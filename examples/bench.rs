//! Microbenchmarks for the set types (internal development use).
//!
//! Run with: `cargo run --release --example bench`
//!
//! Optional env var `BENCH_REPEATS` (default 30) controls the number of
//! best-of-N samples per case. Each sample auto-scales its inner loop count
//! to land near 100 ms of wall time, so reported numbers stay stable.
//!
//! Uses `std::time::Instant` rather than `criterion` to keep the dev-dependency
//! tree lean. Keys are generated up front with `noprop`, so the measured
//! operations do not include any randomness cost.

use std::collections::{BTreeSet, HashSet};
use std::env;
use std::hint::black_box;
use std::time::{Duration, Instant};

use patricia_tree::PatriciaSet;

const TARGET_DURATION: Duration = Duration::from_millis(100);
const INSERTION_KEYS: u64 = 1_000_000;
const RETRIEVAL_KEYS: u64 = 1_000_000;
const REMOVAL_KEYS: u64 = 100_000;

fn parse_repeats() -> usize {
    env::var("BENCH_REPEATS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(30)
}

fn shuffle<T>(ctx: &mut noprop::TestCaseContext, values: &mut [T]) {
    for i in (1..values.len()).rev() {
        let j = noprop::sample_usize_in(ctx, 0..=i);
        values.swap(i, j);
    }
}

fn make_keys(ctx: &mut noprop::TestCaseContext, max: u64) -> Vec<String> {
    let mut keys = (0..max).map(|i| i.to_string()).collect::<Vec<_>>();
    shuffle(ctx, &mut keys);
    keys
}

fn measure_op<F: FnMut()>(mut op: F) -> f64 {
    for _ in 0..3 {
        op();
    }
    let mut iters: u64 = 1;
    loop {
        let start = Instant::now();
        for _ in 0..iters {
            op();
        }
        let elapsed = start.elapsed();
        if elapsed >= TARGET_DURATION {
            return elapsed.as_nanos() as f64 / iters as f64;
        }
        let factor =
            (TARGET_DURATION.as_nanos() as f64 / elapsed.as_nanos().max(1) as f64).max(2.0);
        iters = (iters as f64 * factor).ceil() as u64;
    }
}

fn measure_batched<S, F, G>(mut setup: G, mut op: F) -> f64
where
    F: FnMut(S) -> S,
    G: FnMut() -> S,
{
    for _ in 0..3 {
        let state = op(setup());
        drop(state);
    }
    let mut iters: u64 = 1;
    loop {
        let start = Instant::now();
        let mut total = Duration::ZERO;
        for _ in 0..iters {
            let state = setup();
            let t = Instant::now();
            let state = op(state);
            total += t.elapsed();
            drop(state);
        }
        let elapsed = start.elapsed();
        if elapsed >= TARGET_DURATION {
            return total.as_nanos() as f64 / iters as f64;
        }
        let factor =
            (TARGET_DURATION.as_nanos() as f64 / elapsed.as_nanos().max(1) as f64).max(2.0);
        iters = (iters as f64 * factor).ceil() as u64;
    }
}

fn best_of<F: FnMut() -> f64>(repeats: usize, mut f: F) -> f64 {
    let mut best = f64::INFINITY;
    for _ in 0..repeats {
        best = best.min(f());
    }
    best
}

struct Row {
    name: &'static str,
    ns_per_op: f64,
}

fn print_rows(rows: &[Row]) {
    let base = rows[0].ns_per_op;
    for row in rows {
        println!(
            "  {:12} {:10.1} ns/op  {:6.2}x",
            row.name,
            row.ns_per_op,
            row.ns_per_op / base,
        );
    }
}

fn bench_insertion(ctx: &mut noprop::TestCaseContext, repeats: usize) {
    let keys = make_keys(ctx, INSERTION_KEYS);

    let patricia = best_of(repeats, || {
        let mut set = PatriciaSet::new();
        let mut i = 0;
        measure_op(|| {
            set.insert(black_box(keys[i].clone()));
            i = (i + 1) % keys.len();
        })
    });

    let hash = best_of(repeats, || {
        let mut set = HashSet::new();
        let mut i = 0;
        measure_op(|| {
            set.insert(black_box(keys[i].clone()));
            i = (i + 1) % keys.len();
        })
    });

    let btree = best_of(repeats, || {
        let mut set = BTreeSet::new();
        let mut i = 0;
        measure_op(|| {
            set.insert(black_box(keys[i].clone()));
            i = (i + 1) % keys.len();
        })
    });

    print_rows(&[
        Row {
            name: "PatriciaSet",
            ns_per_op: patricia,
        },
        Row {
            name: "HashSet",
            ns_per_op: hash,
        },
        Row {
            name: "BTreeSet",
            ns_per_op: btree,
        },
    ]);
}

fn bench_retrieval(ctx: &mut noprop::TestCaseContext, repeats: usize) {
    let keys = make_keys(ctx, RETRIEVAL_KEYS);

    let mut patricia_set = PatriciaSet::new();
    for key in keys.iter().take(RETRIEVAL_KEYS as usize / 2) {
        patricia_set.insert(key.clone());
    }
    let patricia = best_of(repeats, || {
        let mut i = 0;
        measure_op(|| {
            patricia_set.contains(black_box(keys[i].as_str()));
            i = (i + 1) % keys.len();
        })
    });

    let mut hash_set = HashSet::new();
    for key in keys.iter().take(RETRIEVAL_KEYS as usize / 2) {
        hash_set.insert(key.clone());
    }
    let hash = best_of(repeats, || {
        let mut i = 0;
        measure_op(|| {
            hash_set.contains(black_box(keys[i].as_str()));
            i = (i + 1) % keys.len();
        })
    });

    let mut btree_set = BTreeSet::new();
    for key in keys.iter().take(RETRIEVAL_KEYS as usize / 2) {
        btree_set.insert(key.clone());
    }
    let btree = best_of(repeats, || {
        let mut i = 0;
        measure_op(|| {
            btree_set.contains(black_box(keys[i].as_str()));
            i = (i + 1) % keys.len();
        })
    });

    print_rows(&[
        Row {
            name: "PatriciaSet",
            ns_per_op: patricia,
        },
        Row {
            name: "HashSet",
            ns_per_op: hash,
        },
        Row {
            name: "BTreeSet",
            ns_per_op: btree,
        },
    ]);
}

fn bench_removal(ctx: &mut noprop::TestCaseContext, repeats: usize) {
    let keys = make_keys(ctx, REMOVAL_KEYS);

    let patricia_set = keys.iter().cloned().collect::<PatriciaSet>();
    let patricia = best_of(repeats, || {
        let mut i = 0;
        measure_batched(
            || {
                let key = keys[i].clone();
                i = (i + 1) % keys.len();
                (patricia_set.clone(), key)
            },
            |(mut set, key)| {
                set.remove(black_box(&key));
                (set, key)
            },
        )
    });

    let hash_set = keys.iter().cloned().collect::<HashSet<_>>();
    let hash = best_of(repeats, || {
        let mut i = 0;
        measure_batched(
            || {
                let key = keys[i].clone();
                i = (i + 1) % keys.len();
                (hash_set.clone(), key)
            },
            |(mut set, key)| {
                set.remove(black_box(&key));
                (set, key)
            },
        )
    });

    let btree_set = keys.iter().cloned().collect::<BTreeSet<_>>();
    let btree = best_of(repeats, || {
        let mut i = 0;
        measure_batched(
            || {
                let key = keys[i].clone();
                i = (i + 1) % keys.len();
                (btree_set.clone(), key)
            },
            |(mut set, key)| {
                set.remove(black_box(&key));
                (set, key)
            },
        )
    });

    print_rows(&[
        Row {
            name: "PatriciaSet",
            ns_per_op: patricia,
        },
        Row {
            name: "HashSet",
            ns_per_op: hash,
        },
        Row {
            name: "BTreeSet",
            ns_per_op: btree,
        },
    ]);
}

fn main() {
    let repeats = parse_repeats();
    println!("BENCH_REPEATS: {repeats}");
    let mut ctx = noprop::TestCaseContext::new(0xDEAD_BEEF);

    println!("insertion:");
    bench_insertion(&mut ctx, repeats);

    println!("retrieval:");
    bench_retrieval(&mut ctx, repeats);

    println!("removal:");
    bench_removal(&mut ctx, repeats);
}
