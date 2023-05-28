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

pub use map::{BytesPatriciaMap, PatriciaMap};
pub use set::{BytesPatriciaSet, PatriciaSet};

pub mod map;
pub mod set;

mod node;
#[cfg(feature = "serde")]
mod serialization;
mod tree;

/// TODO
pub trait Bytes {
    /// TODO
    fn as_bytes(&self) -> &[u8];

    /// TODO
    fn is_valid_bytes(bytes: &[u8]) -> bool;

    /// TODO
    fn from_bytes(bytes: &[u8]) -> &Self;

    /// TODO
    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self;
}

impl Bytes for [u8] {
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
}

// pub(crate) fn insert_str(&mut self, key: &str, value: V) -> Option<V> {
//     if self.label().get(0) > key.as_bytes().get(0) {
//         let this = Node {
//             ptr: self.ptr,
//             _value: PhantomData,
//         };
//         let node = Node::new(key.as_bytes(), Some(value), None, Some(this));
//         self.ptr = node.ptr;
//         mem::forget(node);
//         return None;
//     }

//     let common_prefix_len = self.skip_str_common_prefix(key);
//     let next = &key[common_prefix_len..];
//     let is_label_matched = common_prefix_len == self.label().len();
//     if next.is_empty() {
//         if is_label_matched {
//             let old = self.take_value();
//             self.set_value(value);
//             old
//         } else {
//             self.split_at(common_prefix_len);
//             self.set_value(value);
//             None
//         }
//     } else if is_label_matched {
//         if let Some(child) = self.child_mut() {
//             return child.insert_str(next, value);
//         }
//         let child = Node::new(next.as_bytes(), Some(value), None, None);
//         self.set_child(child);
//         None
//     } else if common_prefix_len == 0 {
//         if let Some(sibling) = self.sibling_mut() {
//             return sibling.insert_str(next, value);
//         }
//         let sibling = Node::new(next.as_bytes(), Some(value), None, None);
//         self.set_sibling(sibling);
//         None
//     } else {
//         self.split_at(common_prefix_len);
//         assert_some!(self.child_mut()).insert_str(next, value);
//         None
//     }
// }
// fn skip_str_common_prefix(&self, key: &str) -> usize {
//     for (i, c) in key.char_indices() {
//         let n = c.len_utf8();
//         if key.as_bytes()[i..i + n]
//             .iter()
//             .ne(self.label()[i..].iter().take(n))
//         {
//             return i;
//         }
//     }
//     key.len()
// }
