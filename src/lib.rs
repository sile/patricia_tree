//! Memory-efficient data structures based on patricia tree (a.k.a, radix tree).
//!
//! A common prefixes of the keys in a patricia tree are represented by a shared path.
//! So if the prefixes of the key set is highly redundant,
//! the memory usage of the resulting patricia tree will be drastically less than
//! more generic data structures (e.g., `BTreeMap`).
//!
//! See [Radix tree](https://en.wikipedia.org/wiki/Radix_tree) for more details.
//!
//! # Examples
//!
//! ```
//! use patricia_tree::PatriciaMap;
//!
//! let mut map = PatriciaMap::new();
//! map.insert("foo", 1);
//! map.insert("bar", 2);
//! map.insert("baz", 3);
//! assert_eq!(map.len(), 3);
//!
//! assert_eq!(map.get("foo"), Some(&1));
//! assert_eq!(map.get("bar"), Some(&2));
//! assert_eq!(map.get("baz"), Some(&3));
//! ```
#![warn(missing_docs)]
#![allow(clippy::cast_ptr_alignment)]

#[macro_use]
extern crate bitflags;
#[cfg(test)]
extern crate rand;

use std::cmp::Ordering;

pub use map::{GenericPatriciaMap, PatriciaMap, StringPatriciaMap};
pub use set::{GenericPatriciaSet, PatriciaSet, StringPatriciaSet};

pub mod map;
pub mod set;

mod node;
#[cfg(feature = "serde")]
mod serialization;
mod tree;

/// This trait represents a bytes type that can be used as the key type of patricia trees.
pub trait Bytes {
    /// Borrowed type of this type.
    type Borrowed: ?Sized + BorrowedBytes + ToOwned<Owned = Self>;
}

impl Bytes for Vec<u8> {
    type Borrowed = [u8];
}

impl Bytes for String {
    type Borrowed = str;
}

/// Borrowed type of [`Bytes`].
pub trait BorrowedBytes {
    /// Returns the byte representation of this instance.
    fn as_bytes(&self) -> &[u8];

    /// Returns `true` if the given bytes is a valid representation of this type, otherwise `false`.
    fn is_valid_bytes(bytes: &[u8]) -> bool;

    /// Converts the given bytes to an instance of this type.
    ///
    /// Caller can assume that `is_valid_bytes(bytes)` is `true`.
    fn from_bytes(bytes: &[u8]) -> &Self;

    /// Returns a suffix of this instance not containing the common prefix with the given bytes.
    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self;

    /// Same as [`strip_common_prefix()`], but also returns the length of the common prefix.
    fn strip_common_prefix_and_len(&self, bytes: &[u8]) -> (&Self, usize) {
        let next = self.strip_common_prefix(bytes);
        let common_prefix_len = self.as_bytes().len() - next.as_bytes().len();
        (next, common_prefix_len)
    }

    /// Compares the first item of this instance with the first item represented in the the given bytes.
    fn cmp_first_item(&self, bytes: &[u8]) -> Ordering;

    /// Returns `true` if this instance is empty, otherwise `false`.
    fn is_empty(&self) -> bool {
        self.as_bytes().is_empty()
    }

    /// Returns a suffix of this instance not containing the first `n` bytes.
    fn strip_n_prefix(&self, n: usize) -> &Self;
}

impl BorrowedBytes for [u8] {
    fn as_bytes(&self) -> &[u8] {
        self
    }

    fn is_valid_bytes(_bytes: &[u8]) -> bool {
        true
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        bytes
    }

    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self {
        let i = self
            .iter()
            .zip(bytes.iter())
            .take_while(|(a, b)| a == b)
            .count();
        &self[i..]
    }

    fn cmp_first_item(&self, bytes: &[u8]) -> Ordering {
        self.first().cmp(&bytes.first())
    }

    fn strip_n_prefix(&self, n: usize) -> &Self {
        &self[n..]
    }
}

impl BorrowedBytes for str {
    fn as_bytes(&self) -> &[u8] {
        self.as_bytes()
    }

    fn is_valid_bytes(bytes: &[u8]) -> bool {
        std::str::from_utf8(bytes).is_ok()
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        std::str::from_utf8(bytes).expect("unreachable")
    }

    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self {
        for (i, c) in self.char_indices() {
            let n = c.len_utf8();
            if self.as_bytes()[i..i + n]
                .iter()
                .ne(bytes[i..].iter().take(n))
            {
                return &self[i..];
            }
        }
        ""
    }

    fn cmp_first_item(&self, bytes: &[u8]) -> Ordering {
        self.chars()
            .next()
            .cmp(&Self::from_bytes(bytes).chars().next())
    }

    fn strip_n_prefix(&self, n: usize) -> &Self {
        &self[n..]
    }
}
