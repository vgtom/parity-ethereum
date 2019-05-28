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

use rug::{Integer, integer::Order};
use vm::ReturnData;

const MAX_RETURN_WASTE_BYTES: usize = 16384;

pub trait Memory {
	/// Retrieve current size of the memory
	fn size(&self) -> usize;
	/// Resize (shrink or expand) the memory to specified size (fills 0)
	fn resize(&mut self, new_size: usize);
	/// Resize the memory only if its smaller
	fn expand(&mut self, new_size: usize);
	/// Write single byte to memory
	fn write_byte(&mut self, offset: usize, value: u8);
	/// Writes a 256-bit word to memory by truncating the given `Integer`. Panics if there is less
	/// than 32 bytes after `offset`.
	fn write(&mut self, offset: usize, value: Integer);
	/// Reads a 256-bit word from memory as an `Integer`.
	fn read(&self, offset: usize) -> Integer;
	/// Writes a slice of bytes to memory. Panics if there is not enough bytes after `offset` to
	/// store the given slice.
	fn write_slice(&mut self, offset: usize, &[u8]);
	/// Retrieve part of the memory between offset and offset + size
	fn read_slice(&self, offset: usize, size: usize) -> &[u8];
	/// Retrieve writeable part of memory
	fn writeable_slice(&mut self, offset: usize, size: usize) -> &mut[u8];
	/// Convert memory into return data.
	fn into_return_data(self, offset: usize, size: usize) -> ReturnData;
}

/// Checks whether offset and size is valid memory range
pub fn is_valid_range(off: usize, size: usize)  -> bool {
	// When size is zero we haven't actually expanded the memory
	let overflow = off.overflowing_add(size).1;
	size > 0 && !overflow
}

impl Memory for Vec<u8> {
	fn size(&self) -> usize {
		self.len()
	}

	fn read_slice(&self, offset: usize, size: usize) -> &[u8] {
		if !is_valid_range(offset, size) {
			&self[0..0]
		} else {
			&self[offset..offset + size]
		}
	}

	fn read(&self, offset: usize) -> Integer {
		Integer::from_digits(&self[offset..offset + 32], Order::MsfLe)
	}

	fn writeable_slice(&mut self, offset: usize, size: usize) -> &mut [u8] {
		if !is_valid_range(offset, size) {
			&mut self[0..0]
		} else {
			&mut self[offset..offset + size]
		}
	}

	fn write_slice(&mut self, offset: usize, slice: &[u8]) {
		if !slice.is_empty() {
			self[offset..offset + slice.len()].copy_from_slice(slice);
		}
	}

	fn write(&mut self, offset: usize, value: Integer) {
		const SIZE: usize = 32;
		// Take the low 32 bytes and write them out to memory in big-endian order.
		let digits = value.keep_bits(SIZE as u32 * 8).to_digits::<u8>(Order::MsfBe);
		let len = digits.len();
		let nel = SIZE - len;
		self[offset + nel..offset + SIZE].copy_from_slice(digits.as_slice());
		if nel > 0 {
			// Fill out the leading zeros.
			for byte in &mut self[offset..offset + nel] {
				*byte = 0;
			}
		}
	}

	fn write_byte(&mut self, offset: usize, value: u8) {
		self[offset] = value;
	}

	fn resize(&mut self, new_size: usize) {
		self.resize(new_size, 0);
	}

	fn expand(&mut self, size: usize) {
		if size > self.len() {
			Memory::resize(self, size)
		}
	}

	fn into_return_data(mut self, offset: usize, size: usize) -> ReturnData {
		if !is_valid_range(offset, size) {
			return ReturnData::empty();
		}
		let corrected_offset = if self.len() - size > MAX_RETURN_WASTE_BYTES {
			if offset == 0 {
				self.truncate(size);
				self.shrink_to_fit();
			} else {
				self = self[offset..offset + size].to_vec();
			}
			0
		} else {
			offset
		};
		ReturnData::new(self, corrected_offset, size)
	}
}

#[cfg(test)]
mod tests {
	use rug::Integer;
	use super::Memory;

	#[test]
	fn test_memory_read_and_write() {
		// given
		let mem: &mut Memory = &mut vec![];
		mem.resize(0x80 + 32);

		// when
		mem.write(0x80, Integer::from(0xabcdef));

		// then
		assert_eq!(mem.read(0x80), Integer::from(0xabcdef));
	}

	#[test]
	fn test_memory_read_and_write_byte() {
		// given
		let mem: &mut Memory = &mut vec![];
		mem.resize(32);

		// when
		mem.write_byte(0x1d, 0xab);
		mem.write_byte(0x1e, 0xcd);
		mem.write_byte(0x1f, 0xef);

		// then
		assert_eq!(mem.read(0x00), Integer::from(0xabcdef));
	}

	#[test]
	fn test_memory_read_slice_and_write_slice() {
		let mem: &mut Memory = &mut vec![];
		mem.resize(32);

		{
			let slice = "abcdefghijklmnopqrstuvwxyz012345".as_bytes();
			mem.write_slice(0, slice);

			assert_eq!(mem.read_slice(0, 32), slice);
		}

		// write again
		{
			let slice = "67890".as_bytes();
			mem.write_slice(1, slice);

			assert_eq!(mem.read_slice(0, 7), "a67890g".as_bytes());
		}

		// write empty slice out of bounds
		{
			let slice = [];
			mem.write_slice(0x1000, &slice);
			assert_eq!(mem.size(), 32);
		}
	}
}
