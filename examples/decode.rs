//! `cargo run --example decode --features binary-format < INPUT_FILE > OUTPUT_FILE`
extern crate bytecodec;
extern crate patricia_tree;

use bytecodec::io::IoDecodeExt;
use bytecodec::null::NullDecoder;
use patricia_tree::{PatriciaSet, node::NodeDecoder};

fn main() {
    let mut decoder = NodeDecoder::new(NullDecoder);
    let node = decoder.decode_exact(std::io::stdin()).unwrap();
    let set = PatriciaSet::from(node);
    for s in set.iter() {
        println!("{}", std::str::from_utf8(&s).unwrap());
    }
}
