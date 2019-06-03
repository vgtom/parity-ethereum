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

//! Rust VM implementation

#[macro_use]
mod informant;
mod gasometer;
mod stack;
mod memory;
mod shared_cache;

use std::{cmp, mem};
use std::sync::Arc;
use hash::keccak;
use bytes::Bytes;
use ethereum_types::{U256, H256, Address};
use rug::{Integer, integer::Order};
use vm::{
	self, ActionParams, ParamsType, ActionValue, CallType, MessageCallResult,
	ContractCreateResult, CreateContractAddress, ReturnData, GasLeft, Schedule,
	TrapKind, TrapError
};

use instructions::{self, Instruction, InstructionInfo};

use self::gasometer::Gasometer;
use self::stack::{Stack, VecStack};
use self::memory::Memory;
pub use self::shared_cache::SharedCache;

use bit_set::BitSet;

#[cfg(target_endian = "big")]
const ENDIANNESS: Order = Order::LsfBe;
#[cfg(not(target_endian = "big"))]
const ENDIANNESS: Order = Order::LsfLe;

const GASOMETER_PROOF: &str = "If gasometer is None, Err is immediately returned in step; this function is only called by step; qed";

lazy_static! {
	/// The unsigned 256-bit integer arithmetic modulus.
	pub static ref U256_MODULUS: Integer = Integer::from(1) << 256;
	/// The maximum unsigned 256-bit integer.
	pub static ref U256_MAX: Integer = (Integer::from(1) << 256) - 1;
}

type ProgramCounter = usize;

/// Abstraction over raw vector of Bytes. Easier state management of PC.
struct CodeReader {
	position: ProgramCounter,
	code: Arc<Bytes>,
}

impl CodeReader {
	/// Create new code reader - starting at position 0.
	fn new(code: Arc<Bytes>) -> Self {
		CodeReader {
			code,
			position: 0,
		}
	}

	/// Gets `num_bytes` from code, converts those to an `Integer` in big-endian order and advances the PC.
	fn read(&mut self, num_bytes: usize) -> Integer {
		let pos = self.position;
		self.position += num_bytes;
		let max = cmp::min(pos + num_bytes, self.code.len());
		Integer::from_digits(&self.code[pos..max], Order::MsfBe)
	}

	fn len(&self) -> usize {
		self.code.len()
	}
}

enum InstructionResult {
	Ok,
	UnusedGas(Integer),
	JumpToPosition(Integer),
	StopExecutionNeedsReturn {
		/// Gas left.
		gas: Integer,
		/// Return data offset.
		init_off: usize,
		/// Return data size.
		init_size: usize,
		/// Apply or revert state changes.
		apply: bool,
	},
	StopExecution,
	Trap(TrapKind),
}

enum Never {}

/// ActionParams without code, so that it can be feed into CodeReader.
#[derive(Debug)]
struct InterpreterParams {
	/// Address of currently executed code.
	pub code_address: Address,
	/// Hash of currently executed code.
	pub code_hash: Option<H256>,
	/// Receive address. Usually equal to code_address,
	/// except when called using CALLCODE.
	pub address: Address,
	/// Sender of current part of the transaction.
	pub sender: Address,
	/// Transaction initiator.
	pub origin: Address,
	/// Gas paid up front for transaction execution
	pub gas: Integer,
	/// Gas price.
	pub gas_price: Integer,
	/// Transaction value.
	pub value: ActionValue,
	/// Input data.
	pub data: Option<Bytes>,
	/// Type of call
	pub call_type: CallType,
	/// Param types encoding
	pub params_type: ParamsType,
}

impl From<ActionParams> for InterpreterParams {
	fn from(params: ActionParams) -> Self {
		InterpreterParams {
			code_address: params.code_address,
			code_hash: params.code_hash,
			address: params.address,
			sender: params.sender,
			origin: params.origin,
			gas: u256_to_integer(&params.gas),
			gas_price: u256_to_integer(&params.gas_price),
			value: params.value,
			data: params.data,
			call_type: params.call_type,
			params_type: params.params_type,
		}
	}
}

/// Stepping result returned by interpreter.
pub enum InterpreterResult {
	/// The VM has already stopped.
	Stopped,
	/// The VM has just finished execution in the current step.
	Done(vm::Result<GasLeft>),
	/// The VM can continue to run.
	Continue,
	Trap(TrapKind),
}

impl From<vm::Error> for InterpreterResult {
	fn from(error: vm::Error) -> InterpreterResult {
		InterpreterResult::Done(Err(error))
	}
}

/// Intepreter EVM implementation
pub struct Interpreter {
	mem: Vec<u8>,
	cache: Arc<SharedCache>,
	params: InterpreterParams,
	reader: CodeReader,
	return_data: ReturnData,
	informant: informant::EvmInformant,
	do_trace: bool,
	done: bool,
	valid_jump_destinations: Option<Arc<BitSet>>,
	gasometer: Option<Gasometer>,
	stack: VecStack<Integer>,
	resume_output_range: Option<(usize, usize)>,
	resume_result: Option<InstructionResult>,
	last_stack_ret_len: usize,
}

impl vm::Exec for Interpreter {
	fn exec(mut self: Box<Self>, ext: &mut vm::Ext) -> vm::ExecTrapResult<GasLeft> {
		loop {
			let result = self.step(ext);
			match result {
				InterpreterResult::Continue => {},
				InterpreterResult::Done(value) => return Ok(value),
				InterpreterResult::Trap(trap) => match trap {
					TrapKind::Call(params) => {
						return Err(TrapError::Call(params, self));
					},
					TrapKind::Create(params, address) => {
						return Err(TrapError::Create(params, address, self));
					},
				},
				InterpreterResult::Stopped => panic!("Attempted to execute an already stopped VM.")
			}
		}
	}
}

impl vm::ResumeCall for Interpreter {
	fn resume_call(mut self: Box<Self>, result: MessageCallResult) -> Box<vm::Exec> {
		{
			let this = &mut *self;
			let (out_off, out_size) = this.resume_output_range.take().expect("Box<ResumeCall> is obtained from a call opcode; resume_output_range is always set after those opcodes are executed; qed");

			match result {
				MessageCallResult::Success(gas_left, data) => {
					let output = this.mem.writeable_slice(out_off, out_size);
					let len = cmp::min(output.len(), data.len());
					(&mut output[..len]).copy_from_slice(&data[..len]);

					this.return_data = data;
					this.stack.push(Integer::from(1));
					this.resume_result = Some(InstructionResult::UnusedGas(gas_left));
				},
				MessageCallResult::Reverted(gas_left, data) => {
					let output = this.mem.writeable_slice(out_off, out_size);
					let len = cmp::min(output.len(), data.len());
					(&mut output[..len]).copy_from_slice(&data[..len]);

					this.return_data = data;
					this.stack.push(Integer::from(0));
					this.resume_result = Some(InstructionResult::UnusedGas(gas_left));
				},
				MessageCallResult::Failed => {
					this.stack.push(Integer::from(0));
					this.resume_result = Some(InstructionResult::Ok);
				},
			}
		}
		self
	}
}

impl vm::ResumeCreate for Interpreter {
	fn resume_create(mut self: Box<Self>, result: ContractCreateResult) -> Box<vm::Exec> {
		match result {
			ContractCreateResult::Created(address, gas_left) => {
				self.stack.push(slice_be_to_integer(&*address));
				self.resume_result = Some(InstructionResult::UnusedGas(gas_left));
			},
			ContractCreateResult::Reverted(gas_left, return_data) => {
				self.stack.push(Integer::from(0));
				self.return_data = return_data;
				self.resume_result = Some(InstructionResult::UnusedGas(gas_left));
			},
			ContractCreateResult::Failed => {
				self.stack.push(Integer::from(0));
				self.resume_result = Some(InstructionResult::Ok);
			},
		}
		self
	}
}

impl Interpreter {
	/// Create a new `Interpreter` instance with shared cache.
	pub fn new(mut params: ActionParams, cache: Arc<SharedCache>, schedule: &Schedule, depth: usize) -> Interpreter {
		let reader = CodeReader::new(params.code.take().expect("VM always called with code; qed"));
		let params = InterpreterParams::from(params);
		let informant = informant::EvmInformant::new(depth);
		let valid_jump_destinations = None;
		let gasometer = Some(Gasometer::new(params.gas.clone()));
		let stack = VecStack::with_capacity(schedule.stack_limit);

		Interpreter {
			cache, params, reader, informant,
			valid_jump_destinations, gasometer, stack,
			done: false,
			do_trace: true,
			mem: Vec::new(),
			return_data: ReturnData::empty(),
			last_stack_ret_len: 0,
			resume_output_range: None,
			resume_result: None,
		}
	}

	/// Execute a single step on the VM.
	#[inline(always)]
	pub fn step(&mut self, ext: &mut vm::Ext) -> InterpreterResult {
		if self.done {
			return InterpreterResult::Stopped;
		}

		let result = if self.gasometer.is_none() {
			InterpreterResult::Done(Err(vm::Error::OutOfGas))
		} else if self.reader.len() == 0 {
			InterpreterResult::Done(Ok(GasLeft::Known(
				self.gasometer.as_ref().expect("Gasometer None case is checked above; qed").current_gas.clone()
			)))
		} else {
			self.step_inner(ext).err().expect("step_inner never returns Ok(()); qed")
		};

		if let &InterpreterResult::Done(_) = &result {
			self.done = true;
			self.informant.done();
		}
		return result;
	}

	/// Inner helper function for step.
	#[inline(always)]
	fn step_inner(&mut self, ext: &mut vm::Ext) -> Result<Never, InterpreterResult> {
		let result = match self.resume_result.take() {
			Some(result) => result,
			None => {
				let opcode = self.reader.code[self.reader.position];
				let instruction = Instruction::from_u8(opcode);
				self.reader.position += 1;

				// TODO: make compile-time removable if too much of a performance hit.
				self.do_trace = self.do_trace && ext.trace_next_instruction(
					self.reader.position - 1, opcode, &self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas,
				);

				let instruction = match instruction {
					Some(i) => i,
					None => return Err(InterpreterResult::Done(Err(vm::Error::BadInstruction {
						instruction: opcode
					}))),
				};

				let info = instruction.info();
				self.last_stack_ret_len = info.ret;
				self.verify_instruction(ext, instruction, info)?;

				// Calculate gas cost
				let requirements = self.gasometer.as_mut().expect(GASOMETER_PROOF).requirements(ext, instruction, info, &self.stack, self.mem.size())?;
				if self.do_trace {
					let store_wr = Self::store_written(instruction, &self.stack);
					ext.trace_prepare_execute(self.reader.position - 1, opcode, &requirements.gas_cost, Self::mem_written(instruction, &self.stack), store_wr);
				}

				self.gasometer.as_mut().expect(GASOMETER_PROOF).verify_gas(&requirements.gas_cost)?;
				self.mem.expand(requirements.memory_required_size);
				self.gasometer.as_mut().expect(GASOMETER_PROOF).current_mem_gas = requirements.memory_total_gas;
				self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas = Integer::from(&self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas - requirements.gas_cost);

				evm_debug!({ self.informant.before_instruction(self.reader.position, instruction, info, &self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas, &self.stack) });

				// Execute instruction
				let current_gas = self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas.clone();
				let result = self.exec_instruction(
					current_gas, ext, instruction, requirements.provide_gas
				)?;

				evm_debug!({ self.informant.after_instruction(instruction) });

				result
			},
		};

		if let InstructionResult::Trap(trap) = result {
			return Err(InterpreterResult::Trap(trap));
		}

		if let InstructionResult::UnusedGas(ref gas) = result {
			self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas =
				Integer::from(&self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas + gas);
		}

		if self.do_trace {
			ext.trace_executed(
				&self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas,
				self.stack.peek_top(self.last_stack_ret_len).iter().cloned().collect::<Vec<Integer>>().as_slice(),
				&self.mem,
			);
		}

		// Advance
		match result {
			InstructionResult::JumpToPosition(position) => {
				if self.valid_jump_destinations.is_none() {
					self.valid_jump_destinations = Some(self.cache.jump_destinations(&self.params.code_hash, &self.reader.code));
				}
				let jump_destinations = self.valid_jump_destinations.as_ref().expect("jump_destinations are initialized on first jump; qed");
				let pos = self.verify_jump(position, jump_destinations)?;
				self.reader.position = pos;
			},
			InstructionResult::StopExecutionNeedsReturn {gas: gas_left, init_off, init_size, apply} => {
				let mem = mem::replace(&mut self.mem, Vec::new());
				return Err(InterpreterResult::Done(Ok(GasLeft::NeedsReturn {
					gas_left,
					data: mem.into_return_data(init_off, init_size),
					apply_state: apply
				})));
			},
			InstructionResult::StopExecution => {
				return Err(InterpreterResult::Done(Ok(GasLeft::Known(
					self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas.clone()
				))));
			},
			_ => {},
		}

		if self.reader.position >= self.reader.len() {
			return Err(InterpreterResult::Done(Ok(GasLeft::Known(
				self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas.clone()
			))));
		}

		Err(InterpreterResult::Continue)
	}

	fn verify_instruction(&self, ext: &vm::Ext, instruction: Instruction, info: &InstructionInfo) -> vm::Result<()> {
		let schedule = ext.schedule();

		if (instruction == instructions::DELEGATECALL && !schedule.have_delegate_call) ||
			(instruction == instructions::CREATE2 && !schedule.have_create2) ||
			(instruction == instructions::STATICCALL && !schedule.have_static_call) ||
			((instruction == instructions::RETURNDATACOPY || instruction == instructions::RETURNDATASIZE) && !schedule.have_return_data) ||
			(instruction == instructions::REVERT && !schedule.have_revert) ||
			((instruction == instructions::SHL || instruction == instructions::SHR || instruction == instructions::SAR) && !schedule.have_bitwise_shifting) ||
			(instruction == instructions::EXTCODEHASH && !schedule.have_extcodehash)
		{
			return Err(vm::Error::BadInstruction {
				instruction: instruction as u8
			});
		}

		if !self.stack.has(info.args) {
			Err(vm::Error::StackUnderflow {
				instruction: info.name,
				wanted: info.args,
				on_stack: self.stack.size()
			})
		} else if self.stack.size() - info.args + info.ret > schedule.stack_limit {
			Err(vm::Error::OutOfStack {
				instruction: info.name,
				wanted: info.ret - info.args,
				limit: schedule.stack_limit
			})
		} else {
			Ok(())
		}
	}

	fn mem_written(
		instruction: Instruction,
		stack: &Stack<Integer>
	) -> Option<(usize, usize)> {
		let read = |pos| stack.peek(pos).to_usize_wrapping();
		let written = match instruction {
			instructions::MSTORE | instructions::MLOAD => Some((read(0), 32)),
			instructions::MSTORE8 => Some((read(0), 1)),
			instructions::CALLDATACOPY | instructions::CODECOPY | instructions::RETURNDATACOPY => Some((read(0), read(2))),
			instructions::EXTCODECOPY => Some((read(1), read(3))),
			instructions::CALL | instructions::CALLCODE => Some((read(5), read(6))),
			instructions::DELEGATECALL | instructions::STATICCALL => Some((read(4), read(5))),
			_ => None,
		};

		match written {
			Some((offset, size)) if !memory::is_valid_range(offset, size) => None,
			written => written,
		}
	}

	fn store_written(
		instruction: Instruction,
		stack: &Stack<Integer>
	) -> Option<(Integer, Integer)> {
		match instruction {
			instructions::SSTORE => Some((stack.peek(0).clone(), stack.peek(1).clone())),
			_ => None,
		}
	}

	fn exec_instruction(
		&mut self,
		gas: Integer,
		ext: &mut vm::Ext,
		instruction: Instruction,
		provided: Option<Integer>
	) -> vm::Result<InstructionResult> {
		match instruction {
			instructions::JUMP => {
				let jump = self.stack.pop_back();
				return Ok(InstructionResult::JumpToPosition(
					jump
				));
			},
			instructions::JUMPI => {
				let jump = self.stack.pop_back();
				let condition = self.stack.pop_back();
				if condition != 0 {
					return Ok(InstructionResult::JumpToPosition(
						jump
					));
				}
			},
			instructions::JUMPDEST => {
				// ignore
			},
			instructions::CREATE | instructions::CREATE2 => {
				let endowment = self.stack.pop_back();
				let init_off = self.stack.pop_back().to_usize_wrapping();
				let init_size = self.stack.pop_back().to_usize_wrapping();
				let address_scheme = match instruction {
					instructions::CREATE => CreateContractAddress::FromSenderAndNonce,
					instructions::CREATE2 => CreateContractAddress::FromSenderSaltAndCodeHash(integer_to_hash(&self.stack.pop_back())),
					_ => unreachable!("instruction can only be CREATE/CREATE2 checked above; qed"),
				};

				let create_gas = provided.expect("`provided` comes through Self::exec from `Gasometer::get_gas_cost_mem`; `gas_gas_mem_cost` guarantees `Some` when instruction is `CALL`/`CALLCODE`/`DELEGATECALL`/`CREATE`; this is `CREATE`; qed");

				if ext.is_static() {
					return Err(vm::Error::MutableCallInStaticContext);
				}

				// clear return data buffer before creating new call frame.
				self.return_data = ReturnData::empty();

				let can_create = ext.balance(&self.params.address)? >= endowment && ext.depth() < ext.schedule().max_depth;
				if !can_create {
					self.stack.push(Integer::from(0));
					return Ok(InstructionResult::UnusedGas(create_gas));
				}

				let contract_code = self.mem.read_slice(init_off, init_size);

				let create_result = ext.create(&create_gas, &endowment, contract_code, address_scheme, true);
				return match create_result {
					Ok(ContractCreateResult::Created(address, gas_left)) => {
						self.stack.push(slice_be_to_integer(&*address));
						Ok(InstructionResult::UnusedGas(gas_left))
					},
					Ok(ContractCreateResult::Reverted(gas_left, return_data)) => {
						self.stack.push(Integer::from(0));
						self.return_data = return_data;
						Ok(InstructionResult::UnusedGas(gas_left))
					},
					Ok(ContractCreateResult::Failed) => {
						self.stack.push(Integer::from(0));
						Ok(InstructionResult::Ok)
					},
					Err(trap) => {
						Ok(InstructionResult::Trap(trap))
					},
				};
			},
			instructions::CALL | instructions::CALLCODE | instructions::DELEGATECALL | instructions::STATICCALL => {
				assert!(ext.schedule().call_value_transfer_gas > ext.schedule().call_stipend, "overflow possible");

				self.stack.pop_back();
				let call_gas = provided.expect("`provided` comes through Self::exec from `Gasometer::get_gas_cost_mem`; `gas_gas_mem_cost` guarantees `Some` when instruction is `CALL`/`CALLCODE`/`DELEGATECALL`/`CREATE`; this is one of `CALL`/`CALLCODE`/`DELEGATECALL`; qed");
				let code_address = self.stack.pop_back();
				let code_address = integer_to_address(&code_address);

				let value = if instruction == instructions::DELEGATECALL {
					None
				} else if instruction == instructions::STATICCALL {
					Some(Integer::from(0))
				} else {
					Some(self.stack.pop_back())
				};

				let in_off = self.stack.pop_back().to_usize_wrapping();
				let in_size = self.stack.pop_back().to_usize_wrapping();
				let out_off = self.stack.pop_back().to_usize_wrapping();
				let out_size = self.stack.pop_back().to_usize_wrapping();

				// Add stipend (only CALL|CALLCODE when value > 0)
				let call_gas = call_gas + (value.as_ref().map_or_else(|| Integer::from(0), |val| if val != &0 {
					Integer::from(ext.schedule().call_stipend)
				} else {
					Integer::from(0)
				}));

				// Get sender & receive addresses, check if we have balance
				let (sender_address, receive_address, has_balance, call_type) = match instruction {
					instructions::CALL => {
						if ext.is_static() && value.as_ref().map_or(false, |v| v != &0) {
							return Err(vm::Error::MutableCallInStaticContext);
						}
						let has_balance = &ext.balance(&self.params.address)? >=
							value.as_ref().expect("value set for all but delegate call; qed");
						(&self.params.address, &code_address, has_balance, CallType::Call)
					},
					instructions::CALLCODE => {
						let has_balance = &ext.balance(&self.params.address)? >=
							value.as_ref().expect("value set for all but delegate call; qed");
						(&self.params.address, &self.params.address, has_balance, CallType::CallCode)
					},
					instructions::DELEGATECALL => (&self.params.sender, &self.params.address, true, CallType::DelegateCall),
					instructions::STATICCALL => (&self.params.address, &code_address, true, CallType::StaticCall),
					_ => panic!(format!("Unexpected instruction {:?} in CALL branch.", instruction))
				};

				// clear return data buffer before creating new call frame.
				self.return_data = ReturnData::empty();

				let can_call = has_balance && ext.depth() < ext.schedule().max_depth;
				if !can_call {
					self.stack.push(Integer::from(0));
					return Ok(InstructionResult::UnusedGas(call_gas));
				}

				let call_result = {
					let input = self.mem.read_slice(in_off, in_size);
					ext.call(&call_gas, sender_address, receive_address, value, input, &code_address, call_type, true)
				};

				self.resume_output_range = Some((out_off, out_size));

				return match call_result {
					Ok(MessageCallResult::Success(gas_left, data)) => {
						let output = self.mem.writeable_slice(out_off, out_size);
						let len = cmp::min(output.len(), data.len());
						(&mut output[..len]).copy_from_slice(&data[..len]);

						self.stack.push(Integer::from(1));
						self.return_data = data;
						Ok(InstructionResult::UnusedGas(gas_left))
					},
					Ok(MessageCallResult::Reverted(gas_left, data)) => {
						let output = self.mem.writeable_slice(out_off, out_size);
						let len = cmp::min(output.len(), data.len());
						(&mut output[..len]).copy_from_slice(&data[..len]);

						self.stack.push(Integer::from(0));
						self.return_data = data;
						Ok(InstructionResult::UnusedGas(gas_left))
					},
					Ok(MessageCallResult::Failed) => {
						self.stack.push(Integer::from(0));
						Ok(InstructionResult::Ok)
					},
					Err(trap) => {
						Ok(InstructionResult::Trap(trap))
					},
				};
			},
			instructions::RETURN => {
				let init_off = self.stack.pop_back().to_usize_wrapping();
				let init_size = self.stack.pop_back().to_usize_wrapping();

				return Ok(InstructionResult::StopExecutionNeedsReturn {gas: gas, init_off: init_off, init_size: init_size, apply: true})
			},
			instructions::REVERT => {
				let init_off = self.stack.pop_back().to_usize_wrapping();
				let init_size = self.stack.pop_back().to_usize_wrapping();

				return Ok(InstructionResult::StopExecutionNeedsReturn {gas: gas, init_off: init_off, init_size: init_size, apply: false})
			},
			instructions::STOP => {
				return Ok(InstructionResult::StopExecution);
			},
			instructions::SUICIDE => {
				let address = self.stack.pop_back();
				ext.suicide(&integer_to_address(&address))?;
				return Ok(InstructionResult::StopExecution);
			},
			instructions::LOG0 | instructions::LOG1 | instructions::LOG2 | instructions::LOG3 | instructions::LOG4 => {
				let no_of_topics = instruction.log_topics().expect("log_topics always return some for LOG* instructions; qed");

				let offset = self.stack.pop_back().to_usize_wrapping();
				let size = self.stack.pop_back().to_usize_wrapping();
				let topics = self.stack.pop_n(no_of_topics)
					.iter()
					.map(integer_to_hash)
					.collect();
				ext.log(topics, self.mem.read_slice(offset, size))?;
			},
			instructions::PUSH1 | instructions::PUSH2 | instructions::PUSH3 | instructions::PUSH4 |
			instructions::PUSH5 | instructions::PUSH6 | instructions::PUSH7 | instructions::PUSH8 |
			instructions::PUSH9 | instructions::PUSH10 | instructions::PUSH11 | instructions::PUSH12 |
			instructions::PUSH13 | instructions::PUSH14 | instructions::PUSH15 | instructions::PUSH16 |
			instructions::PUSH17 | instructions::PUSH18 | instructions::PUSH19 | instructions::PUSH20 |
			instructions::PUSH21 | instructions::PUSH22 | instructions::PUSH23 | instructions::PUSH24 |
			instructions::PUSH25 | instructions::PUSH26 | instructions::PUSH27 | instructions::PUSH28 |
			instructions::PUSH29 | instructions::PUSH30 | instructions::PUSH31 | instructions::PUSH32 => {
				let num_bytes = instruction.push_bytes().expect("push_bytes always return some for PUSH* instructions");
				let val = self.reader.read(num_bytes);
				self.stack.push(val);
			},
			instructions::MLOAD => {
				let offset = self.stack.pop_back().to_usize_wrapping();
				let word = self.mem.read(offset);
				self.stack.push(word);
			},
			instructions::MSTORE => {
				let offset = self.stack.pop_back().to_usize_wrapping();
				let word = self.stack.pop_back();
				Memory::write(&mut self.mem, offset, word);
			},
			instructions::MSTORE8 => {
				let offset = self.stack.pop_back().to_usize_wrapping();
				let byte = self.stack.pop_back().to_u8_wrapping();
				self.mem.write_byte(offset, byte);
			},
			instructions::MSIZE => {
				self.stack.push(Integer::from(self.mem.size()));
			},
			instructions::SHA3 => {
				let offset = self.stack.pop_back().to_usize_wrapping();
				let size = self.stack.pop_back().to_usize_wrapping();
				let k = keccak(self.mem.read_slice(offset, size));
				self.stack.push(slice_be_to_integer(&*k));
			},
			instructions::SLOAD => {
				let key = &integer_to_hash(&self.stack.pop_back());
				let word = ext.storage_at(&key)?;
				self.stack.push(slice_be_to_integer(&*word));
			},
			instructions::SSTORE => {
				let key = integer_to_hash(&self.stack.pop_back());
				let val = self.stack.pop_back();

				let current_val = slice_be_to_integer(&*ext.storage_at(&key)?);
				// Increase refund for clear
				if ext.schedule().eip1283 {
					let original_val = slice_be_to_integer(&*ext.initial_storage_at(&key)?);
					gasometer::handle_eip1283_sstore_clears_refund(ext, &original_val, &current_val, &val);
				} else {
					if current_val != 0 && val == 0 {
						let sstore_clears_schedule = ext.schedule().sstore_refund_gas;
						ext.add_sstore_refund(sstore_clears_schedule);
					}
				}
				ext.set_storage(key, integer_to_hash(&val))?;
			},
			instructions::PC => {
				self.stack.push(Integer::from(self.reader.position - 1));
			},
			instructions::GAS => {
				self.stack.push(gas);
			},
			instructions::ADDRESS => {
				self.stack.push(slice_be_to_integer(&*self.params.address));
			},
			instructions::ORIGIN => {
				self.stack.push(slice_be_to_integer(&*self.params.origin));
			},
			instructions::BALANCE => {
				let address = integer_to_address(&self.stack.pop_back());
				let balance = ext.balance(&address)?;
				self.stack.push(balance);
			},
			instructions::CALLER => {
				self.stack.push(slice_be_to_integer(&*self.params.sender));
			},
			instructions::CALLVALUE => {
				self.stack.push(match &self.params.value {
					ActionValue::Transfer(val) | ActionValue::Apparent(val) => val.clone()
				});
			},
			instructions::CALLDATALOAD => {
				let start = self.stack.pop_back().to_usize_wrapping();
				let end = start + 32;
				if let Some(data) = self.params.data.as_ref() {
					let bound = end.min(data.len());
					if start < bound {
						let mut v = [0u8; 32];
						v[0..bound - start].clone_from_slice(&data[start..bound]);
						self.stack.push(Integer::from_digits(&v[..], Order::MsfBe))
					} else {
						self.stack.push(Integer::from(0))
					}
				} else {
					self.stack.push(Integer::from(0))
				}
			},
			instructions::CALLDATASIZE => {
				self.stack.push(Integer::from(self.params.data.as_ref().map_or(0, |l| l.len())));
			},
			instructions::CODESIZE => {
				self.stack.push(Integer::from(self.reader.len()));
			},
			instructions::RETURNDATASIZE => {
				self.stack.push(Integer::from(self.return_data.len()));
			},
			instructions::EXTCODESIZE => {
				let address = integer_to_address(&self.stack.pop_back());
				let len = ext.extcodesize(&address)?.unwrap_or(0);
				self.stack.push(Integer::from(len));
			},
			instructions::EXTCODEHASH => {
				// FIXME: consider returning an Integer from `ext.extcodehash`.
				let address = integer_to_address(&self.stack.pop_back());
				let hash = ext.extcodehash(&address)?.unwrap_or_else(H256::zero);
				self.stack.push(slice_be_to_integer(&*hash));
			},
			instructions::CALLDATACOPY => {
				Self::copy_data_to_memory(&mut self.mem, &mut self.stack, &self.params.data.as_ref().map_or_else(|| &[] as &[u8], |d| &*d as &[u8]));
			},
			instructions::RETURNDATACOPY => {
				{
					let source_offset = self.stack.peek(1);
					let size = self.stack.peek(2);
					let return_data_len = Integer::from(self.return_data.len());
					if Integer::from(source_offset + size) > return_data_len {
						return Err(vm::Error::OutOfBounds);
					}
				}
				Self::copy_data_to_memory(&mut self.mem, &mut self.stack, &*self.return_data);
			},
			instructions::CODECOPY => {
				Self::copy_data_to_memory(&mut self.mem, &mut self.stack, &self.reader.code);
			},
			instructions::EXTCODECOPY => {
				let address = integer_to_address(&self.stack.pop_back());
				let code = ext.extcode(&address)?;
				Self::copy_data_to_memory(
					&mut self.mem,
					&mut self.stack,
					code.as_ref().map(|c| &(*c)[..]).unwrap_or(&[])
				);
			},
			instructions::GASPRICE => {
				self.stack.push(self.params.gas_price.clone());
			},
			instructions::BLOCKHASH => {
				let block_number = self.stack.pop_back();
				let block_hash = ext.blockhash(&block_number);
				self.stack.push(slice_be_to_integer(&*block_hash));
			},
			instructions::COINBASE => {
				self.stack.push(slice_be_to_integer(&*ext.env_info().author));
			},
			instructions::TIMESTAMP => {
				self.stack.push(Integer::from(ext.env_info().timestamp));
			},
			instructions::NUMBER => {
				self.stack.push(Integer::from(ext.env_info().number));
			},
			instructions::DIFFICULTY => {
				self.stack.push(ext.env_info().difficulty.clone());
			},
			instructions::GASLIMIT => {
				self.stack.push(ext.env_info().gas_limit.clone());
			},

			// Stack instructions

			instructions::DUP1 | instructions::DUP2 | instructions::DUP3 | instructions::DUP4 |
			instructions::DUP5 | instructions::DUP6 | instructions::DUP7 | instructions::DUP8 |
			instructions::DUP9 | instructions::DUP10 | instructions::DUP11 | instructions::DUP12 |
			instructions::DUP13 | instructions::DUP14 | instructions::DUP15 | instructions::DUP16 => {
				let position = instruction.dup_position().expect("dup_position always return some for DUP* instructions");
				let val = self.stack.peek(position).clone();
				self.stack.push(val);
			},
			instructions::SWAP1 | instructions::SWAP2 | instructions::SWAP3 | instructions::SWAP4 |
			instructions::SWAP5 | instructions::SWAP6 | instructions::SWAP7 | instructions::SWAP8 |
			instructions::SWAP9 | instructions::SWAP10 | instructions::SWAP11 | instructions::SWAP12 |
			instructions::SWAP13 | instructions::SWAP14 | instructions::SWAP15 | instructions::SWAP16 => {
				let position = instruction.swap_position().expect("swap_position always return some for SWAP* instructions");
				self.stack.swap_with_top(position)
			},
			instructions::POP => {
				self.stack.pop_back();
			},
			instructions::ADD => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push((a + b).keep_bits(256));
			},
			instructions::MUL => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push((a * b).keep_bits(256));
			},
			instructions::SUB => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				// Perform subtraction, wrapping from 0 down to (1 << 256) - 1. The result is a
				// 256-bit number in two's complement notation.
				let r = a - b;
				let wrapped_r = if r >= 0 {
					r
				} else {
					r + U256_MODULUS.clone()
				};
				self.stack.push(wrapped_r);
			},
			instructions::DIV => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(if b != 0 {
					a / b
				} else {
					Integer::from(0)
				});
			},
			instructions::MOD => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(if b != 0 {
					a % b
				} else {
					Integer::from(0)
				});
			},
			instructions::SDIV => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(if b != 0 {
					apply_rug_signed_2(|a, b| a / b, a, b)
				} else {
					Integer::from(0)
				});
			},
			instructions::SMOD => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(if b != 0 {
					apply_rug_first_signed_2(|a, b| a % b, a, b)
				} else {
					Integer::from(0)
				});
			},
			instructions::EXP => {
				let base = self.stack.pop_back();
				let expon = self.stack.pop_back();
				// FIXME: decide whether to correct the semantics of exponentiation and exponentiate mod 256.
				let res = base.pow_mod(&expon, &U256_MODULUS).expect("Negative exponent is not allowed");
				self.stack.push(res);
			},
			instructions::NOT => {
				let a = self.stack.pop_back();
				self.stack.push(!a);
			},
			instructions::LT => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(Integer::from(a < b));
			},
			instructions::SLT => {
				let (a, neg_a) = get_and_reset_sign(self.stack.pop_back());
				let (b, neg_b) = get_and_reset_sign(self.stack.pop_back());

				let is_positive_lt = a < b && !(neg_a | neg_b);
				let is_negative_lt = a > b && (neg_a & neg_b);
				let has_different_signs = neg_a && !neg_b;

				self.stack.push(Integer::from(is_positive_lt || is_negative_lt || has_different_signs));
			},
			instructions::GT => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(Integer::from(a > b));
			},
			instructions::SGT => {
				let (a, neg_a) = get_and_reset_sign(self.stack.pop_back());
				let (b, neg_b) = get_and_reset_sign(self.stack.pop_back());

				let is_positive_gt = a > b && !(neg_a | neg_b);
				let is_negative_gt = a < b && (neg_a & neg_b);
				let has_different_signs = !neg_a && neg_b;

				self.stack.push(Integer::from(is_positive_gt || is_negative_gt || has_different_signs));
			},
			instructions::EQ => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(Integer::from(a == b));
			},
			instructions::ISZERO => {
				let a = self.stack.pop_back();
				self.stack.push(Integer::from(a == 0));
			},
			instructions::AND => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(a & b);
			},
			instructions::OR => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(a | b);
			},
			instructions::XOR => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				self.stack.push(a ^ b);
			},
			instructions::BYTE => {
				let i = self.stack.pop_back().to_u32_wrapping();
				let a = self.stack.pop_back();
				let byte = if i < 32 {
					(a >> (8 * (31 - i) as u32)).to_u8_wrapping()
				} else {
					0
				};
				self.stack.push(Integer::from(byte));
			},
			instructions::ADDMOD => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				let c = self.stack.pop_back();

				self.stack.push(if c != 0 {
					(a + b) % c
				} else {
					Integer::from(0)
				});
			},
			instructions::MULMOD => {
				let a = self.stack.pop_back();
				let b = self.stack.pop_back();
				let c = self.stack.pop_back();

				self.stack.push(if a != 0 && b != 0 && c != 0 {
					(a * b) % c
				} else {
					Integer::from(0)
				});
			},
			instructions::SIGNEXTEND => {
				let bit = self.stack.pop_back();
				if bit < 32 {
					let number = self.stack.pop_back();
					let bit_position = bit.to_u32_wrapping() * 8 + 7;

					let bit = number.get_bit(bit_position);
					let mask: Integer = (Integer::from(1) << bit_position) - 1;
					self.stack.push(if bit {
						number | !mask
					} else {
						number & mask
					});
				}
			},
			instructions::SHL => {
				let shift = self.stack.pop_back();
				let value = self.stack.pop_back();

				let result = if shift >= 256 {
					Integer::from(0)
				} else {
					(value << shift.to_u32_wrapping()).keep_bits(256)
				};
				self.stack.push(result);
			},
			instructions::SHR => {
				let shift = self.stack.pop_back();
				let value = self.stack.pop_back();

				let result = if shift >= 256 {
					Integer::from(0)
				} else {
					value >> shift.to_u32_wrapping()
				};
				self.stack.push(result);
			},
			instructions::SAR => {
				// We cannot use get_and_reset_sign/set_sign here, because the rounding looks different.
				let shift = self.stack.pop_back().to_u32_wrapping();
				let value = self.stack.pop_back();
				let sign = value.get_bit(255);

				let result = if shift >= 256 {
					if sign {
						U256_MAX.clone()
					} else {
						Integer::from(0)
					}
				} else {
					let mut shifted = value >> shift;
					if sign {
						let mask = U256_MAX.clone() ^ ((Integer::from(1) << (256 - shift)) - 1);
						println!("mask: {:x}", mask);
						shifted = shifted | mask;
					}
					shifted
				};
				self.stack.push(result);
			},
		};
		Ok(InstructionResult::Ok)
	}

	fn copy_data_to_memory(mem: &mut Vec<u8>, stack: &mut Stack<Integer>, source: &[u8]) {
		let dest_offset = stack.pop_back().to_usize_wrapping();
		let source_offset = stack.pop_back().to_usize_wrapping();
		let size = stack.pop_back().to_usize_wrapping();
		let source_size = source.len();

		let output_end = if source_offset > source_size || size > source_size || source_offset + size > source_size {
			let zero_slice = if source_offset > source_size {
				mem.writeable_slice(dest_offset, size)
			} else {
				mem.writeable_slice(dest_offset + source_size - source_offset, source_offset + size - source_size)
			};
			for i in zero_slice.iter_mut() {
				*i = 0;
			}
			source_size
		} else {
			size + source_offset
		};

		if source_offset < source_size {
			let output_begin = source_offset;
			mem.write_slice(dest_offset, &source[output_begin..output_end]);
		}
	}

	fn verify_jump(&self, jump_u: Integer, valid_jump_destinations: &BitSet) -> vm::Result<usize> {
		let jump = jump_u.to_usize_wrapping();

		if valid_jump_destinations.contains(jump) && jump == jump_u {
			Ok(jump)
		} else {
			Err(vm::Error::BadJumpDestination {
				destination: jump
			})
		}
	}
}

/// Truncates the integer to 256 bits and, treating the result in two's complement notation, returns
/// its absolute value and sign.
fn get_and_reset_sign(n: Integer) -> (Integer, bool) {
	let n = n.keep_bits(256);
	let sign = n.get_bit(255);
	let n_abs = if sign {
		U256_MODULUS.clone() - n
	} else {
		n
	};
	(n_abs, sign)
}

/// Converts an integer to a big-endian vector of digits of given `size`.
#[inline]
fn integer_to_digits_be(n: &Integer, size: usize) -> Vec<u8> {
	let n_sized = Integer::from(n.keep_bits_ref(size as u32 * 8));
	n_sized.to_digits::<u8>(Order::MsfBe)
}

/// Converts a variable length `Integer` to a 32-byte long big-endian `H256`. If the argument is
/// longer than 32 bytes, the lower 32 bytes are used.
#[inline]
fn integer_to_hash(n: &Integer) -> H256 {
	const SIZE: usize = 32;
	let mut r = H256::new();
	let digits = integer_to_digits_be(n, SIZE);
	r[SIZE - digits.len() .. SIZE].copy_from_slice(digits.as_slice());
	r
}

/// Converts a variable length `Integer` to a 20-byte long big-endian `Address`. If the argument is
/// longer than 20 bytes, the lower 20 bytes are used.
#[inline]
fn integer_to_address(n: &Integer) -> Address {
	const SIZE: usize = 20;
	let mut r = Address::new();
	let digits = integer_to_digits_be(n, SIZE);
	r[SIZE - digits.len() .. SIZE].copy_from_slice(digits.as_slice());
	r
}

/// Converts a 32-byte long little-endian `U256` to a variable length `Integer`.
#[inline]
fn u256_to_integer(n: &U256) -> Integer {
	let U256(n_u64s) = n;
	Integer::from_digits(n_u64s, ENDIANNESS)
}

/// Converts a big-endian slice to an `Integer`.
///
// FIXME: add tests.
#[inline]
pub fn slice_be_to_integer(slice: &[u8]) -> Integer {
	Integer::from_digits(slice, Order::MsfBe)
}

/// Maps a signed `Integer` to an unsigned integer using two's complement encoding. Assumes the
/// argument is equivalent to a 256-bit integer in two's complement encoding.
#[inline]
fn signed_to_twos_complement(n: Integer) -> Integer {
 	if n < 0 {
		U256_MODULUS.clone() - n.abs()
	} else {
		n
	}
}

/// Applies an `Integer`-valued function to two arguments of type `U256`. The first argument is
/// converted to a signed `Integer`. The second argument is left unsigned.
///
/// Panics if the size of the result of function application is greater than 32 bytes.
#[inline]
fn apply_rug_first_signed_2<F>(f: F, a: Integer, b: Integer) -> Integer
where F: Fn(Integer, Integer) -> Integer {
	let (a, sign_a) = get_and_reset_sign(a);
	let a = if sign_a { a.as_neg().clone() } else { a };
	let r = f(a, b);
	signed_to_twos_complement(r)
}

/// Applies an `Integer`-valued function to two arguments of type `U256` whose highest bit indicates
/// the sign in two's complement encoding.
///
/// Panics if the size of the result of function application is greater than 32 bytes.
#[inline]
fn apply_rug_signed_2<F>(f: F, a: Integer, b: Integer) -> Integer
where F: Fn(Integer, Integer) -> Integer {
	let (a, sign_a) = get_and_reset_sign(a);
	let (b, sign_b) = get_and_reset_sign(b);
	let a = if sign_a { a.as_neg().clone() } else { a };
	let b = if sign_b { b.as_neg().clone() } else { b };
	let r = f(a, b);
	signed_to_twos_complement(r)
}

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use rustc_hex::FromHex;
	use vmtype::VMType;
	use factory::Factory;
	use vm::{self, Exec, ActionParams, ActionValue};
	use vm::tests::{FakeExt, test_finalize};

	fn interpreter(params: ActionParams, ext: &vm::Ext) -> Box<Exec> {
		Factory::new(VMType::Interpreter, 1).create(params, ext.schedule(), ext.depth())
	}

	#[test]
	fn should_not_fail_on_tracing_mem() {
		let code = "7feeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff006000527faaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaa6020526000620f120660406000601773945304eb96065b2a98b57a48a06ae28d285a71b56101f4f1600055".from_hex().unwrap();

		let mut params = ActionParams::default();
		params.address = 5.into();
		params.gas = 300_000.into();
		params.gas_price = 1.into();
		params.value = ActionValue::Transfer(100_000.into());
		params.code = Some(Arc::new(code));
		let mut ext = FakeExt::new();
		ext.balances.insert(5.into(), 1_000_000_000.into());
		ext.tracing = true;

		let gas_left = {
			let vm = interpreter(params, &ext);
			test_finalize(vm.exec(&mut ext).ok().unwrap()).unwrap()
		};

		assert_eq!(ext.calls.len(), 1);
		assert_eq!(gas_left, 248_212);
	}

	#[test]
	fn should_not_overflow_returndata() {
		let code = "6001600160000360003e00".from_hex().unwrap();

		let mut params = ActionParams::default();
		params.address = 5.into();
		params.gas = 300_000.into();
		params.gas_price = 1.into();
		params.code = Some(Arc::new(code));
		let mut ext = FakeExt::new_byzantium();
		ext.balances.insert(5.into(), 1_000_000_000.into());
		ext.tracing = true;

		let err = {
			let vm = interpreter(params, &ext);
			test_finalize(vm.exec(&mut ext).ok().unwrap()).err().unwrap()
		};

		assert_eq!(err, ::vm::Error::OutOfBounds);
	}

	// Source:
	//
	// PUSH32 0x5ed6db9489224124a1a4110ec8bec8b01369c8b549a4b8c4388a1796dc35a937
	// PUSH32 0xb8e0a2b6b1587398c28bf9e9d34ea24ba34df308eec2acedca363b2fce2c25db
	// PUSH32 0xcc2de1f8ec6cc9a24ed2c48b856637f9e45f0a5feee21a196aa42a290ef454ca
	// MULMOD
	// PUSH32 0x1a1aa0d67ab8bfd1d3f4d0f4427cb12137ee1b8fb30ef5bf8a3a625435cdd41f
	// EQ
	// PUSH1 0x8a
	// JUMPI
	// INVALID
	// JUMPDEST
	#[test]
	fn should_compute_mulmod_and_check() {
		let code = "7f5ed6db9489224124a1a4110ec8bec8b01369c8b549a4b8c4388a1796dc35a9377fb8e0a2b6b1587398c28bf9e9d34ea24ba34df308eec2acedca363b2fce2c25db7fcc2de1f8ec6cc9a24ed2c48b856637f9e45f0a5feee21a196aa42a290ef454ca097f1a1aa0d67ab8bfd1d3f4d0f4427cb12137ee1b8fb30ef5bf8a3a625435cdd41f14608a57fe5b".from_hex().unwrap();
		let mut params = ActionParams::default();
		params.address = 5.into();
		params.gas = 300_000.into();
		params.gas_price = 1.into();
		params.code = Some(Arc::new(code));
		let mut ext = FakeExt::new();
		ext.balances.insert(5.into(), 1_000_000_000.into());
		ext.tracing = true;
		let gas_left = {
			let vm = interpreter(params, &ext);
			test_finalize(vm.exec(&mut ext).ok().unwrap()).unwrap()
		};
		assert_eq!(ext.calls.len(), 0);
		assert_eq!(gas_left, 299_963);
	}
}
