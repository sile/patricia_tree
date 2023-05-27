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
#[cfg(feature = "binary-format")]
#[macro_use]
extern crate bytecodec;
#[cfg(test)]
extern crate rand;
#[cfg(feature = "binary-format")]
#[macro_use]
extern crate trackable;

//pub use map::PatriciaMap;
//pub use set::PatriciaSet;

//pub mod map;
pub mod node;
//pub mod set;

#[cfg(feature = "binary-format")]
mod codec;
#[cfg(feature = "serde")]
mod serialization;
mod tree;

/// This trait represents a key type of patricia tree.
pub trait Key: AsRef<[u8]> {
    /// Owned version of the key type.
    type Owned;

    /// TODO
    fn strip_common_prefix<'a, 'b>(&'a self, bytes: &'b [u8]) -> (&'a Self, &'b [u8]);

    /// TODO
    fn from_bytes(bytes: &[u8]) -> &Self;

    /// TODO
    fn from_vec(bytes: Vec<u8>) -> Self::Owned;

    /// TODO
    fn slice(&self, bytes_len: usize) -> &Self {
        Self::from_bytes(&self.as_ref()[..bytes_len])
    }
}

impl Key for [u8] {
    type Owned = Vec<u8>;

    fn strip_common_prefix<'a, 'b>(&'a self, bytes: &'b [u8]) -> (&'a Self, &'b [u8]) {
        let i = self
            .iter()
            .copied()
            .zip(bytes.iter().copied())
            .take_while(|(a, b)| a == b)
            .count();
        (&self[i..], &bytes[i..])
    }

    fn slice(&self, bytes_len: usize) -> &Self {
        &self[..bytes_len]
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        bytes
    }

    fn from_vec(bytes: Vec<u8>) -> Self::Owned {
        bytes
    }
}

// impl Key for str {
//     type Item = char;
//     type Owned = String;

//     fn get_byte(&self, i: usize) -> Option<u8> {
//         self.as_bytes().get(i).copied()
//     }
// }
