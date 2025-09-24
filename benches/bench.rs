use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use patricia_tree::PatriciaSet;
use rand::{Rng, seq::IndexedRandom};

use std::{
    collections::{BTreeSet, HashSet},
    hint::black_box,
};

fn bench_insertion(c: &mut Criterion) {
    let mut group = c.benchmark_group("insertion");

    group.bench_function("PatriciaSet", |b| {
        let mut set = PatriciaSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.bench_function("HashSet", |b| {
        let mut set = HashSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.bench_function("BTreeSet", |b| {
        let mut set = BTreeSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.finish();
}

fn bench_retrieval(c: &mut Criterion) {
    const MAX: u64 = 1_000_000;
    let mut group = c.benchmark_group("retrieval");
    let mut set = PatriciaSet::new();
    let mut rng = rand::rng();

    // Pre-populate the set
    for _ in 0..MAX / 2 {
        set.insert((rng.random::<u64>() % MAX).to_string());
    }

    group.bench_function("PatriciaSet", |b| {
        b.iter(|| {
            set.contains(black_box((rng.random::<u64>() % MAX).to_string()));
        })
    });

    let mut hash_set = HashSet::new();
    for _ in 0..MAX / 2 {
        hash_set.insert((rng.random::<u64>() % MAX).to_string());
    }
    group.bench_function("HashSet", |b| {
        b.iter(|| {
            hash_set.contains(black_box(&(rng.random::<u64>() % MAX).to_string()));
        })
    });

    let mut btree_set = BTreeSet::new();
    for _ in 0..MAX / 2 {
        btree_set.insert((rng.random::<u64>() % MAX).to_string());
    }
    group.bench_function("BTreeSet", |b| {
        b.iter(|| {
            btree_set.contains(black_box(&(rng.random::<u64>() % MAX).to_string()));
        })
    });
    group.finish();
}

fn bench_removal(c: &mut Criterion) {
    let mut group = c.benchmark_group("removal");
    const MAX: u64 = 100_000;

    let mut values = Vec::with_capacity(MAX as usize);
    for i in 0..MAX {
        values.push(i.to_string());
    }
    let patricia_set: PatriciaSet = values.iter().cloned().collect();
    let hashset: HashSet<String> = values.iter().cloned().collect();
    let btreeset: BTreeSet<String> = values.iter().cloned().collect();

    group.bench_function("PatriciaSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (patricia_set.clone(), val.clone())
            },
            // time removal
            |(set, val)| {
                set.remove(black_box(val));
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("HashSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (hashset.clone(), val.clone())
            },
            |(set, val)| {
                set.remove(black_box(&*val));
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (btreeset.clone(), val.clone())
            },
            |(set, val)| {
                set.remove(black_box(&*val));
            },
            BatchSize::SmallInput,
        )
    });
    group.finish();
}

criterion_group!(benches, bench_insertion, bench_retrieval, bench_removal);
criterion_main!(benches);
