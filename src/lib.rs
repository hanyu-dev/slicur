//! `slicur` - A library for reading network IO bytes buffer.

#![no_std]
#![cfg_attr(feature = "feat-nightly", feature(cold_path))]
#![cfg_attr(feature = "feat-nightly", feature(slice_as_array))]

#[cfg(feature = "feat-debug-buffer")]
extern crate alloc;

#[cfg(test)]
extern crate std;

use core::fmt;

pub mod error;
#[cfg(feature = "feat-u24")]
mod number;

#[cfg(feature = "feat-u24")]
// re-export the unsigned 24-bit integer type (`u24`)
pub use number::u24;

/// Wrapper over a slice of bytes that allows reading chunks from
/// with the current position state held using a cursor.
///
/// A new reader for a sub section of the buffer can be created
/// using the `sub` function or a section of a certain length can
/// be obtained using the `take` function
pub struct Reader<'a> {
    /// The underlying buffer storing the readers content
    buffer: &'a [u8],
    /// Stores the current reading position for the buffer
    cursor: usize,
}

#[cfg(not(feature = "feat-debug-buffer"))]
impl fmt::Debug for Reader<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Reader")
            .field("buffer", &"...")
            .field("cursor", &self.cursor)
            .finish()
    }
}

#[cfg(feature = "feat-debug-buffer")]
impl fmt::Debug for Reader<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn hex_slice(bytes: &[u8]) -> alloc::string::String {
            let hex_len = bytes.len() * 2;
            let mut hex_string = alloc::string::String::new();

            // Safety: the hex string is guaranteed to be valid UTF-8
            let buf = unsafe { hex_string.as_mut_vec() };

            buf.reserve_exact(hex_len);

            // Safety: has reserved enough space
            unsafe {
                buf.set_len(hex_len);
            }

            // Safety: the len is correct (2 * bytes.len())
            unsafe {
                const_hex::encode_to_slice(bytes, buf).unwrap_unchecked();
            }

            hex_string
        }

        f.debug_struct("Reader")
            .field("buffer", &hex_slice(self.buffer))
            .field("cursor", &self.cursor)
            .finish()
    }
}

impl<'a> Reader<'a> {
    #[inline]
    /// Creates a new [`Reader`] of the provided `bytes` slice with
    /// the initial cursor position of zero.
    ///
    /// Notice: **MUST** be network endian (big endian) encoded bytes.
    pub const fn init(bytes: &'a [u8]) -> Self {
        Reader {
            buffer: bytes,
            cursor: 0,
        }
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Attempts to create a new [`Reader`] on a sub section of this readers
    /// bytes by taking a slice of the provided `length`. Will return `None` if
    /// there is not enough bytes.
    ///
    /// ## Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn sub(&mut self, length: usize) -> Result<Self, error::InsufficientData> {
        match self.take(length) {
            Ok(bytes) => Ok(Reader::init(bytes)),
            Err(e) => Err(e),
        }
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Borrows a slice of all the remaining bytes that appear after the cursor
    /// position, then moves the cursor to the end of the buffer length.
    ///
    /// ## Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn rest(&mut self) -> &'a [u8] {
        let peeked_rest = self.peek_rest();
        self.cursor = self.buffer.len();
        peeked_rest
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.79.0), const))]
    /// Peek the remaining bytes.
    ///
    /// ## Const context
    ///
    /// This function can be used in a const context since Rust 1.79.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn peek_rest(&self) -> &'a [u8] {
        let Some(rest_buffer_len) = self.buffer.len().checked_sub(self.cursor) else {
            #[cfg(feature = "feat-nightly")]
            core::hint::cold_path();

            unreachable!()
        };

        unsafe {
            // Safety: The cursor is guaranteed to be within the bounds of the buffer
            core::slice::from_raw_parts(self.buffer.as_ptr().add(self.cursor), rest_buffer_len)
        }
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Attempts to borrow a slice of bytes from the current cursor position of
    /// `length`. If there is not enough bytes remaining after the cursor to
    /// take the length, then `error::InsufficientData` is returned instead.
    ///
    /// ## Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn take(&mut self, length: usize) -> Result<&'a [u8], error::InsufficientData> {
        let required_length = self.cursor + length;

        match error::InsufficientData::check(required_length, self.buffer.len()) {
            Ok(()) => {
                // Safety: has checked that the cursor + length does not exceed the buffer
                // length
                let ret = unsafe {
                    core::slice::from_raw_parts(self.buffer.as_ptr().add(self.cursor), length)
                };

                self.cursor = required_length;

                Ok(ret)
            }
            Err(e) => Err(e),
        }
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Like [`take`](Self::take), but takes a fixed-size array of `N` bytes.
    pub fn take_n<const N: usize>(&mut self) -> Result<&'a [u8; N], error::InsufficientData> {
        let required_length = self.cursor + N;

        match error::InsufficientData::check(required_length, self.buffer.len()) {
            Ok(()) => {
                // Safety: has checked that the cursor + N does not exceed the buffer length
                let ret = unsafe { &*(self.buffer.as_ptr().add(self.cursor) as *const [u8; N]) };

                self.cursor = required_length;

                Ok(ret)
            }
            Err(e) => Err(e),
        }
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Advances the cursor by the specified `length`.
    pub fn advance(&mut self, length: usize) -> Result<(), error::InsufficientData> {
        match error::InsufficientData::check(self.cursor + length, self.buffer.len()) {
            Ok(()) => {
                self.cursor += length;
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    #[inline]
    /// Used to check whether the reader has any content left after the cursor
    /// (cursor has not reached end of buffer)
    pub const fn any_left(&self) -> bool {
        self.cursor < self.buffer.len()
    }

    #[inline]
    /// Expects that the reader has no content left, or return an error.
    pub const fn expect_empty(&self) -> Result<(), error::TrailingData> {
        match self.any_left() {
            true => Err(error::TrailingData),
            false => Ok(()),
        }
    }

    #[inline]
    /// Returns the cursor position which is also the number of bytes that have
    /// been read from the buffer.
    pub const fn used(&self) -> usize {
        self.cursor
    }

    #[inline]
    /// Returns the number of bytes that are still able to be
    /// read (The number of remaining takes)
    pub const fn left(&self) -> usize {
        self.buffer.len() - self.cursor
    }

    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Reads a single byte from the reader and returns it.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn read_u8(&mut self) -> Result<u8, error::InsufficientData> {
        match self.take_n::<{ (u8::BITS / 8) as usize }>() {
            Ok(&[b0]) => Ok(b0),
            Err(e) => Err(e),
        }
    }

    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Reads a u16 from the reader and returns it.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn read_u16(&mut self) -> Result<u16, error::InsufficientData> {
        match self.take_n::<{ (u16::BITS / 8) as usize }>() {
            Ok(&b) => Ok(u16::from_be_bytes(b)),
            Err(e) => Err(e),
        }
    }

    #[cfg(feature = "feat-u24")]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Reads a u24 from the reader and returns it.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn read_u24(&mut self) -> Result<u24, error::InsufficientData> {
        match self.take_n::<{ (u24::BITS / 8) as usize }>() {
            Ok(&b) => Ok(u24::from_be_bytes(b)),
            Err(e) => Err(e),
        }
    }

    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Reads a u32 from the reader and returns it.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn read_u32(&mut self) -> Result<u32, error::InsufficientData> {
        match self.take_n::<{ (u32::BITS / 8) as usize }>() {
            Ok(&b) => Ok(u32::from_be_bytes(b)),
            Err(e) => Err(e),
        }
    }

    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Reads a u64 from the reader and returns it.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn read_u64(&mut self) -> Result<u64, error::InsufficientData> {
        match self.take_n::<{ (u64::BITS / 8) as usize }>() {
            Ok(&b) => Ok(u64::from_be_bytes(b)),
            Err(e) => Err(e),
        }
    }

    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Reads a u128 from the reader and returns it.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn read_u128(&mut self) -> Result<u128, error::InsufficientData> {
        match self.take_n::<{ (u128::BITS / 8) as usize }>() {
            Ok(&b) => Ok(u128::from_be_bytes(b)),
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reader_init() {
        let data = [1, 2, 3, 4, 5];
        let reader = Reader::init(&data);

        assert_eq!(reader.used(), 0);
        assert_eq!(reader.left(), 5);
        assert!(reader.any_left());
        assert!(reader.expect_empty().is_err());
    }

    #[test]
    fn test_reader_take() {
        let data = [1, 2, 3, 4, 5];
        let mut reader = Reader::init(&data);

        // Take 2 bytes
        let chunk = reader.take(2).unwrap();
        assert_eq!(chunk, &[1, 2]);
        assert_eq!(reader.used(), 2);
        assert_eq!(reader.left(), 3);

        // Take remaining bytes
        let chunk = reader.take(3).unwrap();
        assert_eq!(chunk, &[3, 4, 5]);
        assert_eq!(reader.used(), 5);
        assert_eq!(reader.left(), 0);
        assert!(!reader.any_left());
        assert!(reader.expect_empty().is_ok());

        // Try to take more than available
        assert!(reader.take(1).is_err());
    }

    #[test]
    fn test_reader_take_zero() {
        let data = [1, 2, 3];
        let mut reader = Reader::init(&data);

        let chunk = reader.take(0).unwrap();
        assert_eq!(chunk, &[]);
        assert_eq!(reader.used(), 0);
        assert_eq!(reader.left(), 3);
    }

    #[test]
    fn test_reader_rest() {
        let data = [1, 2, 3, 4, 5];
        let mut reader = Reader::init(&data);

        // Take some bytes first
        reader.take(2).unwrap();

        // Get rest
        let rest = reader.rest();
        assert_eq!(rest, &[3, 4, 5]);
        assert_eq!(reader.used(), 5);
        assert_eq!(reader.left(), 0);
        assert!(!reader.any_left());
    }

    #[test]
    fn test_reader_peek_rest() {
        let data = [1, 2, 3, 4, 5];
        let mut reader = Reader::init(&data);

        // Take some bytes first
        reader.take(2).unwrap();

        // Peek rest (should not advance cursor)
        let rest = reader.peek_rest();
        assert_eq!(rest, &[3, 4, 5]);
        assert_eq!(reader.used(), 2);
        assert_eq!(reader.left(), 3);
        assert!(reader.any_left());

        // Peek again should return same result
        let rest2 = reader.peek_rest();
        assert_eq!(rest2, &[3, 4, 5]);
        assert_eq!(reader.used(), 2);
    }

    #[test]
    fn test_reader_sub() {
        let data = [1, 2, 3, 4, 5];
        let mut reader = Reader::init(&data);

        // Create sub reader
        let mut sub_reader = reader.sub(3).unwrap();
        assert_eq!(reader.used(), 3);
        assert_eq!(reader.left(), 2);

        // Sub reader should have its own state
        assert_eq!(sub_reader.used(), 0);
        assert_eq!(sub_reader.left(), 3);

        let chunk = sub_reader.take(2).unwrap();
        assert_eq!(chunk, &[1, 2]);
        assert_eq!(sub_reader.used(), 2);
        assert_eq!(sub_reader.left(), 1);

        // Original reader should be unaffected by sub reader operations
        assert_eq!(reader.used(), 3);
        assert_eq!(reader.left(), 2);

        // Try to create sub reader with insufficient data
        assert!(reader.sub(3).is_err());
    }

    #[test]
    fn test_reader_advance() {
        let data = [1, 2, 3, 4, 5];
        let mut reader = Reader::init(&data);

        assert!(reader.advance(2).is_ok());
        assert_eq!(reader.used(), 2);
        assert_eq!(reader.left(), 3);

        assert!(reader.advance(3).is_ok());
        assert_eq!(reader.used(), 5);
        assert_eq!(reader.left(), 0);

        // Try to advance beyond buffer
        assert!(reader.advance(1).is_err());
    }

    #[test]
    fn test_reader_read_u8() {
        let data = [0x12, 0x34, 0x56];
        let mut reader = Reader::init(&data);

        assert_eq!(reader.read_u8().unwrap(), 0x12);
        assert_eq!(reader.read_u8().unwrap(), 0x34);
        assert_eq!(reader.read_u8().unwrap(), 0x56);

        // Try to read beyond buffer
        assert!(reader.read_u8().is_err());
    }

    #[test]
    fn test_reader_read_u16() {
        let data = [0x12, 0x34, 0x56, 0x78];
        let mut reader = Reader::init(&data);

        assert_eq!(reader.read_u16().unwrap(), 0x1234);
        assert_eq!(reader.read_u16().unwrap(), 0x5678);

        // Try to read beyond buffer
        assert!(reader.read_u16().is_err());
    }

    #[test]
    fn test_reader_read_u32() {
        let data = [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0];
        let mut reader = Reader::init(&data);

        assert_eq!(reader.read_u32().unwrap(), 0x12345678);
        assert_eq!(reader.read_u32().unwrap(), 0x9ABCDEF0);

        // Try to read beyond buffer
        assert!(reader.read_u32().is_err());
    }

    #[test]
    fn test_reader_read_u64() {
        let data = [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88,
        ];
        let mut reader = Reader::init(&data);

        assert_eq!(reader.read_u64().unwrap(), 0x123456789ABCDEF0);
        assert_eq!(reader.read_u64().unwrap(), 0x1122334455667788);

        // Try to read beyond buffer
        assert!(reader.read_u64().is_err());
    }

    #[test]
    fn test_reader_read_u128() {
        let data = [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88,
        ];
        let mut reader = Reader::init(&data);

        assert_eq!(
            reader.read_u128().unwrap(),
            0x123456789ABCDEF01122334455667788
        );

        // Try to read beyond buffer
        assert!(reader.read_u128().is_err());
    }

    #[cfg(feature = "feat-u24")]
    #[test]
    fn test_reader_read_u24() {
        let data = [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC];
        let mut reader = Reader::init(&data);

        let val1 = reader.read_u24().unwrap();
        assert_eq!(val1.to_u32(), 0x123456);

        let val2 = reader.read_u24().unwrap();
        assert_eq!(val2.to_u32(), 0x789ABC);

        // Try to read beyond buffer
        assert!(reader.read_u24().is_err());
    }

    #[test]
    fn test_reader_insufficient_data() {
        let data = [1];
        let mut reader = Reader::init(&data);

        // u8 should work
        assert!(reader.read_u8().is_ok());

        // Reset
        let mut reader = Reader::init(&data);

        // u16 should fail
        assert!(reader.read_u16().is_err());
        assert!(reader.read_u32().is_err());
        assert!(reader.read_u64().is_err());
        assert!(reader.read_u128().is_err());
    }

    #[test]
    fn test_reader_empty_buffer() {
        let data = [];
        let mut reader = Reader::init(&data);

        assert_eq!(reader.used(), 0);
        assert_eq!(reader.left(), 0);
        assert!(!reader.any_left());
        assert!(reader.expect_empty().is_ok());

        assert!(reader.take(1).is_err());
        assert!(reader.read_u8().is_err());

        let rest = reader.rest();
        assert_eq!(rest, &[]);

        let peek_rest = reader.peek_rest();
        assert_eq!(peek_rest, &[]);
    }
}
