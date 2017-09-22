#[macro_use]
extern crate bitflags;
extern crate libc;

pub use map::PatriciaMap;

pub mod map;
pub mod node;

mod tree;
