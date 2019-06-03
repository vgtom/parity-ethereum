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

//! Evm interface.

use rug::Integer;
use vm::{Ext, Result, ReturnData, GasLeft, Error};

/// Finalization result. Gas Left: either it is a known value, or it needs to be computed by processing
/// a return instruction.
#[derive(Debug)]
pub struct FinalizationResult {
	/// Final amount of gas left.
	pub gas_left: Integer,
	/// Apply execution state changes or revert them.
	pub apply_state: bool,
	/// Return data buffer.
	pub return_data: ReturnData,
}

/// Types that can be "finalized" using an EVM.
///
/// In practice, this is just used to define an inherent impl on
/// `Reult<GasLeft<'a>>`.
pub trait Finalize {
	/// Consume the externalities, call return if necessary, and produce call result.
	fn finalize<E: Ext>(self, ext: E) -> Result<FinalizationResult>;
}

impl Finalize for Result<GasLeft> {
	fn finalize<E: Ext>(self, ext: E) -> Result<FinalizationResult> {
		match self {
			Ok(GasLeft::Known(gas_left)) => Ok(FinalizationResult { gas_left, apply_state: true, return_data: ReturnData::empty() }),
			Ok(GasLeft::NeedsReturn { gas_left, data, apply_state }) => ext.ret(&gas_left, &data, apply_state).map(|gas_left| FinalizationResult {
				gas_left: gas_left,
				apply_state: apply_state,
				return_data: data,
			}),
			Err(err) => Err(err),
		}
	}
}

impl Finalize for Error {
	fn finalize<E: Ext>(self, _ext: E) -> Result<FinalizationResult> {
		Err(self)
	}
}
