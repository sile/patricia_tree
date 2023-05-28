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
#![allow(clippy::cast_ptr_alignment, clippy::cast_ref_to_mut)]

#[macro_use]
extern crate bitflags;
#[cfg(test)]
extern crate rand;

pub use map::PatriciaMap;
pub use set::PatriciaSet;

pub mod map;
pub mod set;

mod node;
#[cfg(feature = "serde")]
mod serialization;
mod tree;

/// TODO
pub trait Bytes {
    /// TODO
    type Owned;

    /// TODO
    fn as_bytes(&self) -> &[u8];

    /// TODO
    fn is_valid_bytes(bytes: &[u8]) -> bool;

    /// TODO
    fn from_bytes(bytes: &[u8]) -> &Self;

    /// TODO
    fn from_owned_bytes(bytes: Vec<u8>) -> Self::Owned;

    /// TODO
    fn strip_common_prefix<'a, 'b>(&'a self, bytes: &'b [u8]) -> (&'a Self, &'b [u8]);
}

impl Bytes for [u8] {
    type Owned = Vec<u8>;

    fn as_bytes(&self) -> &[u8] {
        self
    }

    fn is_valid_bytes(_bytes: &[u8]) -> bool {
        true
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        bytes
    }

    fn from_owned_bytes(bytes: Vec<u8>) -> Self::Owned {
        bytes
    }

    fn strip_common_prefix<'a, 'b>(&'a self, bytes: &'b [u8]) -> (&'a Self, &'b [u8]) {
        let i = self
            .iter()
            .zip(bytes.iter())
            .take_while(|(a, b)| a == b)
            .count();
        (&self[..i], &bytes[i..])
    }
}
