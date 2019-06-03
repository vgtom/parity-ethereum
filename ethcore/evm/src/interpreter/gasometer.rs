// Copyright 2015-2019 Parity Technologies (UK) Ltd.
// This file is part of Parity Ethereum.

// Parity Ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Ethereum.  If not, see <http://www.gnu.org/licenses/>.

use std::cmp;
use rug::Integer;
use super::{integer_to_address, integer_to_hash, slice_be_to_integer, U256_MAX};

use vm;
use instructions::{self, Instruction, InstructionInfo};
use interpreter::stack::Stack;
use vm::Schedule;

#[inline]
fn check_overflow(v: Integer) -> vm::Result<Integer> {
	if v > *U256_MAX || 0 > v {
		return Err(vm::Error::OutOfGas);
	}
	Ok(v)
}

enum Request {
	Gas(Integer),
	GasMem(Integer, Integer),
	GasMemProvide(Integer, Integer, Option<Integer>),
	GasMemCopy(Integer, Integer, Integer)
}

pub struct InstructionRequirements {
	pub gas_cost: Integer,
	pub provide_gas: Option<Integer>,
	pub memory_total_gas: Integer,
	pub memory_required_size: usize,
}

pub struct Gasometer {
	pub current_gas: Integer,
	pub current_mem_gas: Integer,
}

impl Gasometer {

	pub fn new(current_gas: Integer) -> Self {
		Gasometer {
			current_gas: current_gas,
			current_mem_gas: Integer::from(0),
		}
	}

	pub fn verify_gas(&self, gas_cost: &Integer) -> vm::Result<()> {
		match &self.current_gas < gas_cost {
			true => Err(vm::Error::OutOfGas),
			false => Ok(())
		}
	}

	/// How much gas is provided to a CALL/CREATE, given that we need to deduct `needed` for this operation
	/// and that we `requested` some.
	pub fn gas_provided(&self, schedule: &Schedule, needed: &Integer, requested: Option<Integer>) -> vm::Result<Integer> {
		match schedule.sub_gas_cap_divisor {
			Some(cap_divisor) if self.current_gas >= *needed => {
				let gas_remaining = self.current_gas.clone() - needed;
				let max_gas_provided = match cap_divisor {
					64 => Integer::from(&gas_remaining - Integer::from(&gas_remaining >> 6)),
					cap_divisor => Integer::from(&gas_remaining - Integer::from(&gas_remaining / Integer::from(cap_divisor))),
				};

				if let Some(r) = requested {
					Ok(cmp::min(r, max_gas_provided))
				} else {
					Ok(max_gas_provided)
				}
			},
			_ => {
				if let Some(r) = requested {
					Ok(r)
				} else if self.current_gas >= *needed {
					Ok(Integer::from(&self.current_gas - needed))
				} else {
					Ok(0.into())
				}
			},
		}
	}

	/// Determine how much gas is used by the given instruction, given the machine's state.
	///
	/// We guarantee that the final element of the returned tuple (`provided`) will be `Some`
	/// iff the `instruction` is one of `CREATE`, or any of the `CALL` variants. In this case,
	/// it will be the amount of gas that the current context provides to the child context.
	pub fn requirements(
		&mut self,
		ext: &vm::Ext,
		instruction: Instruction,
		info: &InstructionInfo,
		stack: &Stack<Integer>,
		current_mem_size: usize,
	) -> vm::Result<InstructionRequirements> {
		let schedule = ext.schedule();
		let tier = info.tier.idx();
		let default_gas = Integer::from(schedule.tier_step_gas[tier]);

		let cost = match instruction {
			instructions::JUMPDEST => {
				Request::Gas(Integer::from(1))
			},
			instructions::SSTORE => {
				let address = integer_to_hash(stack.peek(0));
				let newval = stack.peek(1);
				let val = slice_be_to_integer(&*ext.storage_at(&address)?);

				let gas = if schedule.eip1283 {
					let orig = slice_be_to_integer(&*ext.initial_storage_at(&address)?);
					calculate_eip1283_sstore_gas(schedule, &orig, &val, &newval)
				} else {
					if val == 0 && *newval != 0 {
						schedule.sstore_set_gas
					} else {
						// Refund for below case is added when actually executing sstore
						// &val != 0 && newval == 0
						schedule.sstore_reset_gas
					}
				};
				Request::Gas(Integer::from(gas))
			},
			instructions::SLOAD => {
				Request::Gas(Integer::from(schedule.sload_gas))
			},
			instructions::BALANCE => {
				Request::Gas(Integer::from(schedule.balance_gas))
			},
			instructions::EXTCODESIZE => {
				Request::Gas(Integer::from(schedule.extcodesize_gas))
			},
			instructions::EXTCODEHASH => {
				Request::Gas(Integer::from(schedule.extcodehash_gas))
			},
			instructions::SUICIDE => {
				let mut gas = Integer::from(schedule.suicide_gas);

				let is_value_transfer = ext.origin_balance()? != 0;
				let address = integer_to_address(stack.peek(0));
				if (
					!schedule.no_empty && !ext.exists(&address)?
				) || (
					schedule.no_empty && is_value_transfer && !ext.exists_and_not_null(&address)?
				) {
					gas = check_overflow(gas + Integer::from(schedule.suicide_to_new_account_cost))?;
				}

				Request::Gas(gas)
			},
			instructions::MSTORE | instructions::MLOAD => {
				Request::GasMem(default_gas, mem_needed_const(stack.peek(0), 32)?)
			},
			instructions::MSTORE8 => {
				Request::GasMem(default_gas, mem_needed_const(stack.peek(0), 1)?)
			},
			instructions::RETURN | instructions::REVERT => {
				Request::GasMem(default_gas, mem_needed(stack.peek(0), stack.peek(1))?)
			},
			instructions::SHA3 => {
				let words = to_word_size(stack.peek(1))?;
				let gas = check_overflow(Integer::from(schedule.sha3_gas) + (Integer::from(schedule.sha3_word_gas) *  words))?;
				Request::GasMem(gas, mem_needed(stack.peek(0), stack.peek(1))?)
			},
			instructions::CALLDATACOPY | instructions::CODECOPY | instructions::RETURNDATACOPY => {
				Request::GasMemCopy(default_gas,
									mem_needed(stack.peek(0), stack.peek(2))?,
									Integer::from(stack.peek(2)))
			},
			instructions::EXTCODECOPY => {
				Request::GasMemCopy(Integer::from(schedule.extcodecopy_base_gas),
									mem_needed(stack.peek(1), stack.peek(3))?,
									Integer::from(stack.peek(3)))
			},
			instructions::LOG0 | instructions::LOG1 | instructions::LOG2 | instructions::LOG3 | instructions::LOG4 => {
				let no_of_topics = instruction.log_topics().expect("log_topics always return some for LOG* instructions; qed");
				let log_gas = schedule.log_gas + schedule.log_topic_gas * no_of_topics;

				let data_gas = check_overflow(stack.peek(1) * Integer::from(schedule.log_data_gas))?;
				let gas = check_overflow(data_gas + Integer::from(log_gas))?;
				Request::GasMem(gas, mem_needed(stack.peek(0), stack.peek(1))?)
			},
			instructions::CALL | instructions::CALLCODE => {
				let mut gas = Integer::from(schedule.call_gas);
				let mem = cmp::max(
					mem_needed(stack.peek(5), stack.peek(6))?,
					mem_needed(stack.peek(3), stack.peek(4))?
				);

				let address = integer_to_address(stack.peek(1));
				let is_value_transfer = *stack.peek(2) != 0;

				if instruction == instructions::CALL && (
					(!schedule.no_empty && !ext.exists(&address)?)
					||
					(schedule.no_empty && is_value_transfer && !ext.exists_and_not_null(&address)?)
				) {
					gas = check_overflow(gas + Integer::from(schedule.call_new_account_gas))?;
				}

				if is_value_transfer {
					gas = check_overflow(gas + Integer::from(schedule.call_value_transfer_gas))?;
				}

				let requested = Integer::from(stack.peek(0));

				Request::GasMemProvide(gas, mem, Some(requested))
			},
			instructions::DELEGATECALL | instructions::STATICCALL => {
				let gas = Integer::from(schedule.call_gas);
				let mem = cmp::max(
					mem_needed(stack.peek(4), stack.peek(5))?,
					mem_needed(stack.peek(2), stack.peek(3))?
				);
				let requested = Integer::from(stack.peek(0));

				Request::GasMemProvide(gas, mem, Some(requested))
			},
			instructions::CREATE => {
				let start = stack.peek(1);
				let len = stack.peek(2);

				let gas = Integer::from(schedule.create_gas);
				let mem = mem_needed(start, len)?;

				Request::GasMemProvide(gas, mem, None)
			},
			instructions::CREATE2 => {
				let start = stack.peek(1);
				let len = stack.peek(2);

				let base = Integer::from(schedule.create_gas);
				let word = to_word_size(len)?;
				let word_gas = check_overflow(Integer::from(schedule.sha3_word_gas) * word)?;
				let gas = check_overflow(base + word_gas)?;
				let mem = mem_needed(start, len)?;

				Request::GasMemProvide(gas, mem, None)
			},
			instructions::EXP => {
				let expon = stack.peek(1);
				let bytes = ((expon.significant_bits() + 7) / 8) as usize;
				let gas = Integer::from(schedule.exp_gas + schedule.exp_byte_gas * bytes);
				Request::Gas(gas)
			},
			instructions::BLOCKHASH => {
				Request::Gas(Integer::from(schedule.blockhash_gas))
			},
			_ => Request::Gas(default_gas),
		};

		Ok(match cost {
			Request::Gas(gas) => {
				InstructionRequirements {
					gas_cost: gas,
					provide_gas: None,
					memory_required_size: 0,
					memory_total_gas: self.current_mem_gas.clone(),
				}
			},
			Request::GasMem(gas, mem_size) => {
				let (mem_gas_cost, new_mem_gas, new_mem_size) = self.mem_gas_cost(schedule, current_mem_size, &mem_size)?;
				let gas = check_overflow(gas + mem_gas_cost)?;
				InstructionRequirements {
					gas_cost: gas,
					provide_gas: None,
					memory_required_size: new_mem_size,
					memory_total_gas: new_mem_gas,
				}
			},
			Request::GasMemProvide(gas, mem_size, requested) => {
				let (mem_gas_cost, new_mem_gas, new_mem_size) = self.mem_gas_cost(schedule, current_mem_size, &mem_size)?;
				let gas = check_overflow(gas + mem_gas_cost)?;
				let provided = self.gas_provided(schedule, &gas, requested)?;
				let total_gas = check_overflow(Integer::from(&gas + &provided))?;

				InstructionRequirements {
					gas_cost: total_gas,
					provide_gas: Some(provided),
					memory_required_size: new_mem_size,
					memory_total_gas: new_mem_gas,
				}
			},
			Request::GasMemCopy(gas, mem_size, copy) => {
				let (mem_gas_cost, new_mem_gas, new_mem_size) = self.mem_gas_cost(schedule, current_mem_size, &mem_size)?;
				let copy = to_word_size(&copy)?;
				let copy_gas = check_overflow(Integer::from(schedule.copy_gas) * copy)?;
				let gas = check_overflow(gas + copy_gas)?;
				let gas = check_overflow(gas + mem_gas_cost)?;

				InstructionRequirements {
					gas_cost: gas,
					provide_gas: None,
					memory_required_size: new_mem_size,
					memory_total_gas: new_mem_gas,
				}
			},
		})
	}

	fn mem_gas_cost(&self, schedule: &Schedule, current_mem_size: usize, mem_size: &Integer) -> vm::Result<(Integer, Integer, usize)> {
		let gas_for_mem = |mem_size: &Integer| {
			// Assumption for optimisation of division (shift right by a constant)
			assert_eq!(schedule.quad_coeff_div, 512);
			let s: Integer = Integer::from(mem_size >> 5);
			// s * memory_gas + s * s / quad_coeff_div
			let a = check_overflow(s.clone() * Integer::from(schedule.memory_gas))?;
			// Calculate s*s/quad_coeff_div
			let s_squared = check_overflow(s.square())?;
			check_overflow(a + (s_squared >> 9))
		};

		let current_mem_size = Integer::from(current_mem_size);
		let req_mem_size_rounded: Integer = to_word_size(mem_size)? << 5;

		let (mem_gas_cost, new_mem_gas) = if req_mem_size_rounded > current_mem_size {
			let new_mem_gas = gas_for_mem(&req_mem_size_rounded)?;
			(new_mem_gas.clone() - self.current_mem_gas.clone(), new_mem_gas)
		} else {
			(Integer::from(0), self.current_mem_gas.clone())
		};

		Ok((mem_gas_cost, new_mem_gas, req_mem_size_rounded.to_usize_wrapping()))
	}
}

#[inline]
fn mem_needed_const(mem: &Integer, add: u32) -> vm::Result<Integer> {
	check_overflow(Integer::from(mem + add))
}

#[inline]
fn mem_needed(offset: &Integer, size: &Integer) -> vm::Result<Integer> {
	if *size == 0 {
		return Ok(Integer::from(0));
	}
	check_overflow(Integer::from(offset + size))
}

#[inline]
fn to_word_size(value: &Integer) -> vm::Result<Integer> {
	Ok(check_overflow(Integer::from(value + 31))? >> 5)
}

#[inline]
fn calculate_eip1283_sstore_gas(schedule: &Schedule, original: &Integer, current: &Integer, new: &Integer) -> usize {
	if current == new {
		// 1. If current value equals new value (this is a no-op), 200 gas is deducted.
		schedule.sload_gas
	} else {
		// 2. If current value does not equal new value
		if original == current {
			// 2.1. If original value equals current value (this storage slot has not been changed by the current execution context)
			if *original == 0 {
				// 2.1.1. If original value is 0, 20000 gas is deducted.
				schedule.sstore_set_gas
			} else {
				// 2.1.2. Otherwise, 5000 gas is deducted.
				schedule.sstore_reset_gas

				// 2.1.2.1. If new value is 0, add 15000 gas to refund counter.
			}
		} else {
			// 2.2. If original value does not equal current value (this storage slot is dirty), 200 gas is deducted. Apply both of the following clauses.
			schedule.sload_gas

			// 2.2.1. If original value is not 0
			// 2.2.1.1. If current value is 0 (also means that new value is not 0), remove 15000 gas from refund counter. We can prove that refund counter will never go below 0.
			// 2.2.1.2. If new value is 0 (also means that current value is not 0), add 15000 gas to refund counter.

			// 2.2.2. If original value equals new value (this storage slot is reset)
			// 2.2.2.1. If original value is 0, add 19800 gas to refund counter.
			// 2.2.2.2. Otherwise, add 4800 gas to refund counter.
		}
	}
}

pub fn handle_eip1283_sstore_clears_refund(ext: &mut vm::Ext, original: &Integer, current: &Integer, new: &Integer) {
	let sstore_clears_schedule = ext.schedule().sstore_refund_gas;

	if current == new {
		// 1. If current value equals new value (this is a no-op), 200 gas is deducted.
	} else {
		// 2. If current value does not equal new value
		if original == current {
			// 2.1. If original value equals current value (this storage slot has not been changed by the current execution context)
			if *original == 0 {
				// 2.1.1. If original value is 0, 20000 gas is deducted.
			} else {
				// 2.1.2. Otherwise, 5000 gas is deducted.
				if *new == 0 {
					// 2.1.2.1. If new value is 0, add 15000 gas to refund counter.
					ext.add_sstore_refund(sstore_clears_schedule);
				}
			}
		} else {
			// 2.2. If original value does not equal current value (this storage slot is dirty), 200 gas is deducted. Apply both of the following clauses.

			if *original != 0 {
				// 2.2.1. If original value is not 0
				if *current == 0 {
					// 2.2.1.1. If current value is 0 (also means that new value is not 0), remove 15000 gas from refund counter. We can prove that refund counter will never go below 0.
					ext.sub_sstore_refund(sstore_clears_schedule);
				} else if *new == 0 {
					// 2.2.1.2. If new value is 0 (also means that current value is not 0), add 15000 gas to refund counter.
					ext.add_sstore_refund(sstore_clears_schedule);
				}
			}

			if original == new {
				// 2.2.2. If original value equals new value (this storage slot is reset)
				if *original == 0 {
					// 2.2.2.1. If original value is 0, add 19800 gas to refund counter.
					let refund = ext.schedule().sstore_set_gas - ext.schedule().sload_gas;
					ext.add_sstore_refund(refund);
				} else {
					// 2.2.2.2. Otherwise, add 4800 gas to refund counter.
					let refund = ext.schedule().sstore_reset_gas - ext.schedule().sload_gas;
					ext.add_sstore_refund(refund);
				}
			}
		}
	}
}

#[test]
fn test_mem_gas_cost() {
	// given
	let gasometer = Gasometer::new(Integer::from(0));
	let schedule = Schedule::default();
	let current_mem_size = 5;

	// when
	let result = gasometer.mem_gas_cost(&schedule, current_mem_size, &U256_MAX);

	// then
	if result.is_ok() {
		assert!(false, "Should fail with OutOfGas");
	}
}

#[test]
fn test_calculate_mem_cost() {
	// given
	let gasometer = Gasometer::new(Integer::from(0));
	let schedule = Schedule::default();
	let current_mem_size = 0;
	let mem_size = Integer::from(5);

	// when
	let (mem_cost, new_mem_gas, mem_size) = gasometer.mem_gas_cost(&schedule, current_mem_size, &mem_size).unwrap();

	// then
	assert_eq!(mem_cost, 3);
	assert_eq!(new_mem_gas, 3);
	assert_eq!(mem_size, 32);
}
