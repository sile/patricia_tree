//! Property-based tests using noprop.
//!
//! The oracle is the corresponding `BTreeMap` / `BTreeSet` from the standard
//! library. Byte keys stress label splitting on shared prefixes, while Unicode
//! string keys stress character-boundary handling of the `str` implementation.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Debug;

use patricia_tree::BorrowedBytes;
use patricia_tree::Bytes;
use patricia_tree::GenericPatriciaMap;
use patricia_tree::PatriciaSet;

const CASES: usize = 256;

#[derive(Default)]
struct MapGates {
    insert_added: Cell<usize>,
    remove_removed: Cell<usize>,
    iter_checked_nonempty: Cell<usize>,
    prefix_queried_nonempty: Cell<usize>,
}

#[derive(Default)]
struct SplitGates {
    nontrivial_split: Cell<usize>,
}

#[derive(Default)]
struct SetGates {
    insert_added: Cell<usize>,
    remove_removed: Cell<usize>,
    iter_checked_nonempty: Cell<usize>,
}

fn common_prefix_len(a: &[u8], b: &[u8]) -> usize {
    a.iter().zip(b.iter()).take_while(|(x, y)| x == y).count()
}

fn sample_byte_key(ctx: &mut noprop::TestCaseContext) -> Vec<u8> {
    let len = noprop::sample_with_boundaries(
        ctx,
        &[0usize, 1, 2, 8],
        noprop::Ratio::one_nth(8),
        |_ctx| noprop::sample_usize_in(_ctx, 0..=16),
    );
    let mut key = Vec::with_capacity(len);
    for _ in 0..len {
        if noprop::sample_ratio(ctx, noprop::Ratio::one_nth(2)) {
            key.push(noprop::sample_u8(ctx));
        } else {
            key.push(b"abc"[noprop::sample_usize_in(ctx, 0..3)]);
        }
    }
    key
}

fn sample_char(ctx: &mut noprop::TestCaseContext) -> char {
    if noprop::sample_ratio(ctx, noprop::Ratio::one_nth(4)) {
        noprop::sample_char(ctx)
    } else {
        const CHARS: [char; 8] = ['a', 'b', 'z', '0', '-', 'é', '日', '🌏'];
        CHARS[noprop::sample_usize_in(ctx, 0..CHARS.len())]
    }
}

fn sample_string_key(ctx: &mut noprop::TestCaseContext) -> String {
    let len = noprop::sample_with_boundaries(
        ctx,
        &[0usize, 1, 2, 8],
        noprop::Ratio::one_nth(8),
        |_ctx| noprop::sample_usize_in(_ctx, 0..=12),
    );
    (0..len).map(|_| sample_char(ctx)).collect()
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

fn sample_byte_prefix_of_existing(
    ctx: &mut noprop::TestCaseContext,
    model: &BTreeMap<Vec<u8>, u32>,
) -> Vec<u8> {
    let index = noprop::sample_usize_in(ctx, 0..model.len());
    let key = model.keys().nth(index).unwrap();
    let cut = noprop::sample_usize_in(ctx, 0..=key.len());
    key[..cut].to_vec()
}

fn sample_string_prefix_of_existing(
    ctx: &mut noprop::TestCaseContext,
    model: &BTreeMap<String, u32>,
) -> String {
    let index = noprop::sample_usize_in(ctx, 0..model.len());
    let key = model.keys().nth(index).unwrap();
    let cut = noprop::sample_usize_in(ctx, 0..=key.chars().count());
    key.chars().take(cut).collect()
}

fn run_split_model_property<K>(
    ctx: &mut noprop::TestCaseContext,
    sample_key: fn(&mut noprop::TestCaseContext) -> K,
    sample_prefix_of_existing: fn(&mut noprop::TestCaseContext, &BTreeMap<K, u32>) -> K,
    gates: &SplitGates,
) -> noprop::TestResult
where
    K: Bytes + AsRef<K::Borrowed> + Ord + Clone + Debug + 'static,
{
    let mut map = GenericPatriciaMap::<K, u32>::new();
    let mut model = BTreeMap::<K, u32>::new();

    let inserts = noprop::sample_with_boundaries(
        ctx,
        &[0usize, 1, 4, 16],
        noprop::Ratio::one_nth(8),
        |_ctx| noprop::sample_usize_in(_ctx, 0..=24),
    );
    for _ in 0..inserts {
        let key = sample_key(ctx);
        map.insert(key.clone(), 1);
        model.insert(key, 1);
    }

    // Bias the prefix toward existing keys so that non-trivial splits are likely.
    let prefix = if !model.is_empty() && noprop::sample_ratio(ctx, noprop::Ratio::one_nth(2)) {
        sample_prefix_of_existing(ctx, &model)
    } else {
        sample_key(ctx)
    };

    let splitted = map.split_by_prefix(&prefix);
    let prefix_bytes = prefix.as_ref().as_bytes();

    let expected_splitted = model
        .iter()
        .filter(|(k, _)| k.as_ref().as_bytes().starts_with(prefix_bytes))
        .map(|(k, v)| (k.clone(), *v))
        .collect::<Vec<_>>();
    let expected_rest = model
        .iter()
        .filter(|(k, _)| !k.as_ref().as_bytes().starts_with(prefix_bytes))
        .map(|(k, v)| (k.clone(), *v))
        .collect::<Vec<_>>();

    let actual_splitted = splitted.iter().map(|(k, v)| (k, *v)).collect::<Vec<_>>();
    let actual_rest = map.iter().map(|(k, v)| (k, *v)).collect::<Vec<_>>();

    assert_eq!(
        actual_splitted, expected_splitted,
        "splitted entries mismatch"
    );
    assert_eq!(actual_rest, expected_rest, "remaining entries mismatch");
    assert_eq!(
        splitted.len(),
        expected_splitted.len(),
        "splitted len mismatch",
    );
    assert_eq!(map.len(), expected_rest.len(), "remaining len mismatch");

    if !expected_splitted.is_empty() && !expected_rest.is_empty() {
        gates.nontrivial_split.set(gates.nontrivial_split.get() + 1);
    }
    Ok(())
}

#[test]
fn patricia_map_split_by_prefix_matches_model() -> noprop::TestResult {
    let seed = noprop::seed_from_env_or_time("PATRICIA_TREE_SEED")?;
    let gates = SplitGates::default();
    let mut runner = noprop::Runner::new(seed);
    runner.run(CASES, |ctx| {
        run_split_model_property(ctx, sample_byte_key, sample_byte_prefix_of_existing, &gates)
    })?;

    assert!(
        gates.nontrivial_split.get() > 0,
        "no case split a map into two non-empty parts\n{runner}",
    );
    Ok(())
}

#[test]
fn string_patricia_map_split_by_prefix_matches_model() -> noprop::TestResult {
    let seed = noprop::seed_from_env_or_time("PATRICIA_TREE_SEED")?;
    let gates = SplitGates::default();
    let mut runner = noprop::Runner::new(seed);
    runner.run(CASES, |ctx| {
        run_split_model_property(
            ctx,
            sample_string_key,
            sample_string_prefix_of_existing,
            &gates,
        )
    })?;

    assert!(
        gates.nontrivial_split.get() > 0,
        "no case split a map into two non-empty parts\n{runner}",
    );
    Ok(())
}

fn run_set_model_property(
    ctx: &mut noprop::TestCaseContext,
    sample_key: fn(&mut noprop::TestCaseContext) -> Vec<u8>,
    gates: &SetGates,
) -> noprop::TestResult {
    let mut set = PatriciaSet::new();
    let mut model = BTreeSet::new();
    let steps =
        noprop::sample_with_boundaries(ctx, &[1usize, 4, 16], noprop::Ratio::one_nth(8), |_ctx| {
            noprop::sample_usize_in(_ctx, 1..=32)
        });
    let mut insert_added = false;
    let mut remove_removed = false;

    for step in 0..steps {
        match noprop::sample_weighted_index(ctx, &[3, 2, 2]) {
            0 => {
                let value = sample_key(ctx);
                let expected = model.insert(value.clone());
                let actual = set.insert(value);
                assert_eq!(actual, expected, "insert mismatch at step {step}");
                insert_added |= actual;
            }
            1 => {
                let value = sample_key(ctx);
                let expected = model.remove(&value);
                let actual = set.remove(&value);
                assert_eq!(actual, expected, "remove mismatch at step {step}");
                remove_removed |= actual;
            }
            _ => {
                let value = sample_key(ctx);
                assert_eq!(
                    set.contains(&value),
                    model.contains(&value),
                    "contains mismatch at step {step}",
                );
            }
        }
    }

    let expected = model.iter().cloned().collect::<Vec<_>>();
    let actual = set.iter().collect::<Vec<_>>();
    assert_eq!(actual, expected, "iter mismatch");
    assert_eq!(set.len(), model.len(), "len mismatch");

    if !model.is_empty() {
        gates
            .iter_checked_nonempty
            .set(gates.iter_checked_nonempty.get() + 1);
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
fn patricia_set_matches_btree_set() -> noprop::TestResult {
    let seed = noprop::seed_from_env_or_time("PATRICIA_TREE_SEED")?;
    let gates = SetGates::default();
    let mut runner = noprop::Runner::new(seed);
    runner.run(CASES, |ctx| {
        run_set_model_property(ctx, sample_byte_key, &gates)
    })?;

    assert!(
        gates.insert_added.get() > 0,
        "no case inserted a new element\n{runner}",
    );
    assert!(
        gates.remove_removed.get() > 0,
        "no case removed an existing element\n{runner}",
    );
    assert!(
        gates.iter_checked_nonempty.get() > 0,
        "no case iterated a non-empty set\n{runner}",
    );
    Ok(())
}
