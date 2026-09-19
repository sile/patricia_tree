//! Property tests for `GenericPatriciaMap::split_by_prefix`.

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
struct SplitGates {
    nontrivial_split: Cell<usize>,
}

fn sample_byte_prefix_of_existing(
    ctx: &mut noprop::TestCaseContext,
    model: &BTreeMap<Vec<u8>, u32>,
) -> Vec<u8> {
    let index = noprop::sample_usize_in(ctx, 0..model.len());
    let key = model
        .keys()
        .nth(index)
        .expect("index is sampled from 0..model.len()");
    let cut = noprop::sample_usize_in(ctx, 0..=key.len());
    key[..cut].to_vec()
}

fn sample_string_prefix_of_existing(
    ctx: &mut noprop::TestCaseContext,
    model: &BTreeMap<String, u32>,
) -> String {
    let index = noprop::sample_usize_in(ctx, 0..model.len());
    let key = model
        .keys()
        .nth(index)
        .expect("index is sampled from 0..model.len()");
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
