#![feature(test)]
extern crate patricia_tree;
extern crate rand;
extern crate test;

use patricia_tree::PatriciaSet;
use rand::Rng;

#[bench]
fn bench_insertion(b: &mut test::Bencher) {
    let mut set = PatriciaSet::new();
    b.iter(|| {
        set.insert(rand::random::<usize>().to_string().bytes());
    });
}

#[bench]
fn bench_retrieval(b: &mut test::Bencher) {
    const MAX: usize = 1_000_000;

    let mut set = PatriciaSet::new();
    for _ in 0..MAX / 2 {
        set.insert((rand::random::<usize>() % MAX).to_string().bytes());
    }
    b.iter(|| {
        set.contains((rand::random::<usize>() % MAX).to_string().bytes());
    });
}

#[bench]
fn bench_removal(b: &mut test::Bencher) {
    const MAX: usize = 1_000_000;

    let mut set = PatriciaSet::new();
    for i in 0..MAX {
        set.insert(i.to_string().bytes());
    }

    let mut values = (0..MAX).collect::<Vec<_>>();
    rand::thread_rng().shuffle(&mut values[..]);

    let mut values = values.iter().cycle();
    b.iter(|| {
        set.remove(values.next().unwrap().to_string().bytes());
    });
}
