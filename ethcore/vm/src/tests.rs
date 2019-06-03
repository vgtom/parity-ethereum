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

use std::sync::Arc;
use std::collections::{HashMap, HashSet};
use rug::Integer;
use ethereum_types::{H256, Address};
use bytes::Bytes;
use {
	CallType, Schedule, EnvInfo,
	ReturnData, Ext, ContractCreateResult, MessageCallResult,
	CreateContractAddress, Result, GasLeft,
};
use hash::keccak;
use error::TrapKind;

pub struct FakeLogEntry {
	pub topics: Vec<H256>,
	pub data: Bytes
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum FakeCallType {
	Call, Create
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct FakeCall {
	pub call_type: FakeCallType,
	pub create_scheme: Option<CreateContractAddress>,
	pub gas: Integer,
	pub sender_address: Option<Address>,
	pub receive_address: Option<Address>,
	pub value: Option<Integer>,
	pub data: Bytes,
	pub code_address: Option<Address>,
}

/// Fake externalities test structure.
///
/// Can't do recursive calls.
#[derive(Default)]
pub struct FakeExt {
	pub store: HashMap<H256, H256>,
	pub suicides: HashSet<Address>,
	pub calls: HashSet<FakeCall>,
	pub sstore_clears: i128,
	pub depth: usize,
	pub blockhashes: HashMap<Integer, H256>,
	pub codes: HashMap<Address, Arc<Bytes>>,
	pub logs: Vec<FakeLogEntry>,
	pub info: EnvInfo,
	pub schedule: Schedule,
	pub balances: HashMap<Address, Integer>,
	pub tracing: bool,
	pub is_static: bool,
}

// similar to the normal `finalize` function, but ignoring NeedsReturn.
pub fn test_finalize(res: Result<GasLeft>) -> Result<Integer> {
	match res {
		Ok(GasLeft::Known(gas)) => Ok(gas),
		Ok(GasLeft::NeedsReturn{..}) => unimplemented!(), // since ret is unimplemented.
		Err(e) => Err(e),
	}
}

impl FakeExt {
	/// New fake externalities
	pub fn new() -> Self {
		FakeExt::default()
	}

	/// New fake externalities with byzantium schedule rules
	pub fn new_byzantium() -> Self {
		let mut ext = FakeExt::default();
		ext.schedule = Schedule::new_byzantium();
		ext
	}

	/// New fake externalities with constantinople schedule rules
	pub fn new_constantinople() -> Self {
		let mut ext = FakeExt::default();
		ext.schedule = Schedule::new_constantinople();
		ext
	}

	/// Alter fake externalities to allow wasm
	pub fn with_wasm(mut self) -> Self {
		self.schedule.wasm = Some(Default::default());
		self
	}
}

impl Ext for FakeExt {
	fn initial_storage_at(&self, _key: &H256) -> Result<H256> {
		Ok(H256::new())
	}

	fn storage_at(&self, key: &H256) -> Result<H256> {
		Ok(self.store.get(key).unwrap_or(&H256::new()).clone())
	}

	fn set_storage(&mut self, key: H256, value: H256) -> Result<()> {
		self.store.insert(key, value);
		Ok(())
	}

	fn exists(&self, address: &Address) -> Result<bool> {
		Ok(self.balances.contains_key(address))
	}

	fn exists_and_not_null(&self, address: &Address) -> Result<bool> {
		Ok(self.balances.get(address).map_or(false, |b| b != &0))
	}

	fn origin_balance(&self) -> Result<Integer> {
		unimplemented!()
	}

	fn balance(&self, address: &Address) -> Result<Integer> {
		Ok(self.balances[address].clone())
	}

	fn blockhash(&mut self, number: &Integer) -> H256 {
		self.blockhashes.get(number).unwrap_or(&H256::new()).clone()
	}

	fn create(
		&mut self,
		gas: &Integer,
		value: &Integer,
		code: &[u8],
		address: CreateContractAddress,
		_trap: bool,
	) -> ::std::result::Result<ContractCreateResult, TrapKind> {
		self.calls.insert(FakeCall {
			call_type: FakeCallType::Create,
			create_scheme: Some(address),
			gas: gas.clone(),
			sender_address: None,
			receive_address: None,
			value: Some(value.clone()),
			data: code.to_vec(),
			code_address: None
		});
		// TODO: support traps in testing.
		Ok(ContractCreateResult::Failed)
	}

	fn call(
		&mut self,
		gas: &Integer,
		sender_address: &Address,
		receive_address: &Address,
		value: Option<Integer>,
		data: &[u8],
		code_address: &Address,
		_call_type: CallType,
		_trap: bool,
	) -> ::std::result::Result<MessageCallResult, TrapKind> {
		self.calls.insert(FakeCall {
			call_type: FakeCallType::Call,
			create_scheme: None,
			gas: gas.clone(),
			sender_address: Some(sender_address.clone()),
			receive_address: Some(receive_address.clone()),
			value: value,
			data: data.to_vec(),
			code_address: Some(code_address.clone())
		});
		// TODO: support traps in testing.
		Ok(MessageCallResult::Success(gas.clone(), ReturnData::empty()))
	}

	fn extcode(&self, address: &Address) -> Result<Option<Arc<Bytes>>> {
		Ok(self.codes.get(address).cloned())
	}

	fn extcodesize(&self, address: &Address) -> Result<Option<usize>> {
		Ok(self.codes.get(address).map(|c| c.len()))
	}

	fn extcodehash(&self, address: &Address) -> Result<Option<H256>> {
		Ok(self.codes.get(address).map(|c| keccak(c.as_ref())))
	}

	fn log(&mut self, topics: Vec<H256>, data: &[u8]) -> Result<()> {
		self.logs.push(FakeLogEntry {
			topics: topics,
			data: data.to_vec()
		});
		Ok(())
	}

	fn ret(self, _gas: &Integer, _data: &ReturnData, _apply_state: bool) -> Result<Integer> {
		unimplemented!();
	}

	fn suicide(&mut self, refund_address: &Address) -> Result<()> {
		self.suicides.insert(refund_address.clone());
		Ok(())
	}

	fn schedule(&self) -> &Schedule {
		&self.schedule
	}

	fn env_info(&self) -> &EnvInfo {
		&self.info
	}

	fn depth(&self) -> usize {
		self.depth
	}

	fn is_static(&self) -> bool {
		self.is_static
	}

	fn add_sstore_refund(&mut self, value: usize) {
		self.sstore_clears += value as i128;
	}

	fn sub_sstore_refund(&mut self, value: usize) {
		self.sstore_clears -= value as i128;
	}

	fn trace_next_instruction(&mut self, _pc: usize, _instruction: u8, _gas: &Integer) -> bool {
		self.tracing
	}
}
