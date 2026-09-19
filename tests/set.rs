//! Property tests comparing `PatriciaSet` against `BTreeSet`.

use std::cell::Cell;
use std::collections::BTreeSet;

use patricia_tree::PatriciaSet;

mod helpers_bytes;

use helpers_bytes::sample_byte_key;

const CASES: usize = 256;

#[derive(Default)]
struct SetGates {
    insert_added: Cell<usize>,
    remove_removed: Cell<usize>,
    iter_checked_nonempty: Cell<usize>,
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
