//! Property tests comparing `GenericPatriciaMap` against `BTreeMap`.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt::Debug;

use patricia_tree::BorrowedBytes;
use patricia_tree::Bytes;
use patricia_tree::GenericPatriciaMap;

mod helpers_bytes;
mod helpers_string;

use helpers_bytes::sample_byte_key;
use helpers_string::sample_string_key;

const CASES: usize = 256;

#[derive(Default)]
struct MapGates {
    insert_added: Cell<usize>,
    remove_removed: Cell<usize>,
    iter_checked_nonempty: Cell<usize>,
    prefix_queried_nonempty: Cell<usize>,
}

fn common_prefix_len(a: &[u8], b: &[u8]) -> usize {
    a.iter().zip(b.iter()).take_while(|(x, y)| x == y).count()
}

fn byte_lcp(_key: &[u8], lcp: usize) -> usize {
    lcp
}

// String keys are compared at character boundaries, so the returned length is
// always aligned to a character boundary of the query key.
fn char_aligned_lcp(key: &str, lcp: usize) -> usize {
    key.char_indices()
        .map(|(i, c)| i + c.len_utf8())
        .filter(|&n| n <= lcp)
        .max()
        .unwrap_or(0)
}

fn run_map_model_property<K>(
    ctx: &mut noprop::TestCaseContext,
    sample_key: fn(&mut noprop::TestCaseContext) -> K,
    align_lcp: fn(&K::Borrowed, usize) -> usize,
    gates: &MapGates,
) -> noprop::TestResult
where
    K: Bytes + AsRef<K::Borrowed> + Ord + Clone + Debug + 'static,
{
    let mut map = GenericPatriciaMap::<K, u32>::new();
    let mut model = BTreeMap::<K, u32>::new();
    let steps =
        noprop::sample_with_boundaries(ctx, &[1usize, 4, 16], noprop::Ratio::one_nth(8), |_ctx| {
            noprop::sample_usize_in(_ctx, 1..=32)
        });
    let mut insert_added = false;
    let mut remove_removed = false;

    for step in 0..steps {
        match noprop::sample_weighted_index(ctx, &[4, 3, 2, 1, 1, 2]) {
            0 => {
                let key = sample_key(ctx);
                let value = noprop::sample_u32(ctx);
                let expected = model.insert(key.clone(), value);
                let actual = map.insert(key, value);
                assert_eq!(actual, expected, "insert mismatch at step {step}");
                insert_added |= expected.is_none();
            }
            1 => {
                let key = sample_key(ctx);
                let expected = model.remove(&key);
                let actual = map.remove(&key);
                assert_eq!(actual, expected, "remove mismatch at step {step}");
                remove_removed |= expected.is_some();
            }
            2 => {
                let key = sample_key(ctx);
                assert_eq!(
                    map.get(&key),
                    model.get(&key),
                    "get mismatch at step {step}"
                );
                assert_eq!(
                    map.contains_key(&key),
                    model.contains_key(&key),
                    "contains_key mismatch at step {step}",
                );
            }
            3 => {
                assert_eq!(map.len(), model.len(), "len mismatch at step {step}");
                assert_eq!(
                    map.is_empty(),
                    model.is_empty(),
                    "is_empty mismatch at step {step}",
                );
            }
            4 => {
                let expected = model
                    .iter()
                    .map(|(k, v)| (k.clone(), *v))
                    .collect::<Vec<_>>();
                let actual = map.iter().map(|(k, v)| (k, *v)).collect::<Vec<_>>();
                assert_eq!(actual, expected, "iter mismatch at step {step}");
                if !model.is_empty() {
                    gates
                        .iter_checked_nonempty
                        .set(gates.iter_checked_nonempty.get() + 1);
                }
            }
            5 => {
                let key = sample_key(ctx);
                let key_bytes = key.as_ref().as_bytes();

                let expected_lcp_len = model
                    .keys()
                    .map(|k| common_prefix_len(key_bytes, k.as_ref().as_bytes()))
                    .map(|lcp| align_lcp(key.as_ref(), lcp))
                    .max()
                    .unwrap_or(0);
                assert_eq!(
                    map.longest_common_prefix_len(&key),
                    expected_lcp_len,
                    "longest_common_prefix_len mismatch at step {step}: key={key:?} model={model:?}",
                );

                let expected_glcp = model
                    .iter()
                    .filter(|(k, _)| key_bytes.starts_with(k.as_ref().as_bytes()))
                    .max_by_key(|(k, _)| k.as_ref().as_bytes().len())
                    .map(|(k, v)| (k.as_ref().as_bytes(), *v));
                let actual_glcp = map
                    .get_longest_common_prefix(&key)
                    .map(|(k, v)| (k.as_bytes(), *v));
                assert_eq!(
                    actual_glcp, expected_glcp,
                    "get_longest_common_prefix mismatch at step {step}",
                );

                let mut expected_common_prefixes = model
                    .iter()
                    .filter(|(k, _)| key_bytes.starts_with(k.as_ref().as_bytes()))
                    .map(|(k, v)| (k.as_ref().as_bytes().to_vec(), *v))
                    .collect::<Vec<_>>();
                expected_common_prefixes.sort();
                let actual_common_prefixes = map
                    .common_prefixes(&key)
                    .map(|(k, v)| (k.as_bytes().to_vec(), *v))
                    .collect::<Vec<_>>();
                assert_eq!(
                    actual_common_prefixes, expected_common_prefixes,
                    "common_prefixes mismatch at step {step}",
                );

                let expected_iter_prefix = model
                    .iter()
                    .filter(|(k, _)| k.as_ref().as_bytes().starts_with(key_bytes))
                    .map(|(k, v)| (k.clone(), *v))
                    .collect::<Vec<_>>();
                let actual_iter_prefix = map
                    .iter_prefix(key.as_ref())
                    .map(|(k, v)| (k, *v))
                    .collect::<Vec<_>>();
                assert_eq!(
                    actual_iter_prefix, expected_iter_prefix,
                    "iter_prefix mismatch at step {step}",
                );

                if !model.is_empty() {
                    gates
                        .prefix_queried_nonempty
                        .set(gates.prefix_queried_nonempty.get() + 1);
                }
            }
            _ => unreachable!(),
        }
    }

    if insert_added {
        gates.insert_added.set(gates.insert_added.get() + 1);
    }
    if remove_removed {
        gates.remove_removed.set(gates.remove_removed.get() + 1);
    }
    Ok(())
}

#[test]
fn patricia_map_matches_btree_map() -> noprop::TestResult {
    let seed = noprop::seed_from_env_or_time("PATRICIA_TREE_SEED")?;
    let gates = MapGates::default();
    let mut runner = noprop::Runner::new(seed);
    runner.run(CASES, |ctx| {
        run_map_model_property(ctx, sample_byte_key, byte_lcp, &gates)
    })?;

    assert!(
        gates.insert_added.get() > 0,
        "no case inserted a new key\n{runner}",
    );
    assert!(
        gates.remove_removed.get() > 0,
        "no case removed an existing key\n{runner}",
    );
    assert!(
        gates.iter_checked_nonempty.get() > 0,
        "no case iterated a non-empty map\n{runner}",
    );
    assert!(
        gates.prefix_queried_nonempty.get() > 0,
        "no case queried a non-empty map\n{runner}",
    );
    Ok(())
}

#[test]
fn string_patricia_map_matches_btree_map() -> noprop::TestResult {
    let seed = noprop::seed_from_env_or_time("PATRICIA_TREE_SEED")?;
    let gates = MapGates::default();
    let mut runner = noprop::Runner::new(seed);
    runner.run(CASES, |ctx| {
        run_map_model_property(ctx, sample_string_key, char_aligned_lcp, &gates)
    })?;

    assert!(
        gates.insert_added.get() > 0,
        "no case inserted a new key\n{runner}",
    );
    assert!(
        gates.remove_removed.get() > 0,
        "no case removed an existing key\n{runner}",
    );
    assert!(
        gates.iter_checked_nonempty.get() > 0,
        "no case iterated a non-empty map\n{runner}",
    );
    assert!(
        gates.prefix_queried_nonempty.get() > 0,
        "no case queried a non-empty map\n{runner}",
    );
    Ok(())
}
