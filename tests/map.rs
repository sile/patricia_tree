//! Tests for `GenericPatriciaMap`.
//!
//! `patricia_map_matches_btree_map` and
//! `string_patricia_map_matches_btree_map` compare the map against
//! `BTreeMap` over sampled inputs; the remaining tests are worked examples.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt::Debug;

use patricia_tree::BorrowedBytes;
use patricia_tree::Bytes;
use patricia_tree::GenericPatriciaMap;
use patricia_tree::PatriciaMap;
use patricia_tree::StringPatriciaMap;

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

#[test]
fn it_works() {
    let input = [
        ("7", 7),
        ("43", 43),
        ("92", 92),
        ("37", 37),
        ("31", 31),
        ("21", 21),
        ("0", 0),
        ("35", 35),
        ("47", 47),
        ("82", 82),
        ("61", 61),
        ("9", 9),
    ];

    let mut map = PatriciaMap::new();
    for &(ref k, v) in input.iter() {
        assert_eq!(map.insert(k, v), None);
        assert_eq!(map.get(k), Some(&v));
    }
}

#[test]
fn debug_works() {
    let map: PatriciaMap<_> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
        .into_iter()
        .collect();
    assert_eq!(
        format!("{map:?}"),
        "{[98, 97, 114]: 2, [98, 97, 122]: 3, [102, 111, 111]: 1}"
    );
}

#[test]
fn clear_works() {
    let mut map = PatriciaMap::new();
    assert!(map.is_empty());

    map.insert("foo", 1);
    assert!(!map.is_empty());

    map.clear();
    assert!(map.is_empty());
}

#[test]
fn into_iter_works() {
    let map: PatriciaMap<_> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
        .into_iter()
        .collect();
    assert_eq!(
        map.into_iter().collect::<Vec<_>>(),
        [(Vec::from("bar"), 2), ("baz".into(), 3), ("foo".into(), 1)]
    );
}

#[test]
fn iter_mut_works() {
    let mut map: PatriciaMap<_> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
        .into_iter()
        .collect();

    for (_key, x) in map.iter_mut() {
        (*x) *= 2;
    }

    assert_eq!(
        map.into_iter().collect::<Vec<_>>(),
        [(Vec::from("bar"), 4), ("baz".into(), 6), ("foo".into(), 2)]
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn large_map_works() {
    let mut input = (0..10000).map(|i| (i.to_string(), i)).collect::<Vec<_>>();
    let mut ctx = noprop::TestCaseContext::new(0xDEAD_BEEF);
    for i in (1..input.len()).rev() {
        let j = noprop::sample_usize_in(&mut ctx, 0..=i);
        input.swap(i, j);
    }

    // Insert
    let mut map = input.iter().cloned().collect::<PatriciaMap<_>>();
    assert_eq!(map.len(), input.len());

    // Get
    for &(ref k, v) in input.iter() {
        assert_eq!(map.get(k), Some(&v));
    }

    // Remove
    for &(ref k, v) in input.iter().take(input.len() / 2) {
        assert_eq!(map.remove(k), Some(v));
        assert_eq!(map.remove(k), None);
    }
    for (k, _) in input.iter().take(input.len() / 2) {
        assert_eq!(map.get(k), None);
    }
    for &(ref k, v) in input.iter().skip(input.len() / 2) {
        assert_eq!(map.get(k), Some(&v));
    }

    // Insert
    for &(ref k, v) in input.iter().take(input.len() / 2) {
        assert_eq!(map.insert(k, v), None);
    }
    for &(ref k, v) in input.iter().skip(input.len() / 2) {
        assert_eq!(map.insert(k, v), Some(v));
    }

    // Get
    for &(ref k, v) in input.iter() {
        assert_eq!(map.get(k), Some(&v));
    }
}

#[test]
fn test_common_word_prefixes() {
    let mut t = PatriciaMap::new();
    t.insert(".com.foo.", vec!["b"]);
    t.insert(".", vec!["a"]);
    t.insert(".com.foo.bar.", vec!["c"]);
    t.insert("..", vec!["e"]);
    t.insert("x", vec!["d"]);

    let results = t
        .common_prefixes(b".com.foo.bar.baz.")
        .flat_map(|(_, v)| v)
        .cloned()
        .collect::<Vec<_>>();

    assert!(results.iter().eq(vec![&"a", &"b", &"c"].into_iter()));
}

#[test]
fn test_letter_prefixes() {
    let mut t = PatriciaMap::new();
    t.insert("x", vec!["x"]);
    t.insert("a", vec!["a"]);
    t.insert("ab", vec!["b"]);
    t.insert("abc", vec!["c"]);
    t.insert("abcd", vec!["d"]);
    t.insert("abcdf", vec!["f"]);

    let results = t
        .common_prefixes(b"abcde")
        .flat_map(|(_, v)| v)
        .cloned()
        .collect::<Vec<_>>();
    assert!(results.iter().eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
}

#[test]
fn test_common_prefixes() {
    let mut t = PatriciaMap::new();
    t.insert("b", vec!["b"]);
    t.insert("a", vec!["a"]);
    t.insert("c", vec!["c"]);
    t.insert("..", vec!["e"]);
    t.insert("x", vec!["d"]);

    let results = t
        .common_prefixes(b"abc")
        .flat_map(|(_, v)| v)
        .cloned()
        .collect::<Vec<_>>();
    assert!(results.iter().eq(vec![&"a"].into_iter()));

    let mut t = PatriciaMap::new();
    t.insert("ab", vec!["b"]);
    t.insert("a", vec!["a"]);
    t.insert("abc", vec!["c"]);
    t.insert("..", vec!["e"]);
    t.insert("x", vec!["d"]);

    let results = t
        .common_prefixes(b"abcd")
        .flat_map(|(_, v)| v)
        .cloned()
        .collect::<Vec<_>>();

    assert!(results.iter().eq(vec![&"a", &"b", &"c"].into_iter()));

    let mut list = PatriciaMap::new();
    list.insert(b".com.foocatnetworks.".as_ref(), vec![0_u16]);
    list.insert(b".com.foocatnetworks.foo.".as_ref(), vec![1]);
    list.insert(b".com.foocatnetworks.foo.baz.".as_ref(), vec![2]);
    list.insert(b".com.google.".as_ref(), vec![0]);
    list.insert(b".com.cisco.".as_ref(), vec![0]);
    list.insert(b".org.wikipedia.".as_ref(), vec![0]);

    let results = list
        .common_prefixes(b".com.foocatnetworks.foo.baz.")
        .flat_map(|(_, v)| v)
        .cloned()
        .collect::<Vec<_>>();

    assert!(vec![0_u16, 1, 2].into_iter().eq(results.into_iter()));
}

#[test]
fn issue21() {
    let mut map = PatriciaMap::new();
    map.insert("1", 0);
    map.insert("2", 0);
    map.remove("2");
    map.insert("2", 0);
    assert_eq!(map.len(), map.iter().count());
    assert_eq!(map.len(), map.iter_mut().count());
}

#[test]
fn issue35() {
    let mut map = StringPatriciaMap::<u8>::new();
    map.insert("インターポール", 1);
    map.insert("インターポル", 2);
    map.insert("インターリーブ", 3);
    map.insert("インターン", 4);

    assert_eq!(map.get("インターポール"), Some(&1));
    assert_eq!(map.get("インターポル"), Some(&2));
}

#[test]
fn issue42_iter_prefix() {
    let mut map = StringPatriciaMap::new();
    map.insert("a0/b0", 0);
    map.insert("a1/b1", 0);
    let items: Vec<_> = {
        let prefix = "a0".to_owned();
        map.iter_prefix(&prefix).collect()
    };

    assert_eq!(items, vec![("a0/b0".to_owned(), &0)])
}

#[test]
fn issue42_iter_prefix_mut() {
    let mut map = StringPatriciaMap::new();
    map.insert("a0/b0", 0);
    map.insert("a1/b1", 0);
    let items: Vec<_> = {
        let prefix = "a0".to_owned();
        map.iter_prefix_mut(&prefix).collect()
    };

    assert_eq!(items, vec![("a0/b0".to_owned(), &mut 0)])
}

#[test]
fn issue42_common_prefix_values() {
    let mut map = StringPatriciaMap::new();
    map.insert("a0/b0", 0);
    map.insert("a1/b1", 0);
    let items: Vec<_> = {
        let prefix = "a0/b0/c0".to_owned();
        map.common_prefix_values(&prefix).collect()
    };

    assert_eq!(items, vec![&0])
}

#[test]
fn test_owned_impl_iter() {
    struct TestTrie<T> {
        map: GenericPatriciaMap<Vec<u8>, T>,
    }

    impl<T> TestTrie<T> {
        #[expect(dead_code)]
        fn common_prefix_test(&self, domain: &[u8]) -> impl Iterator<Item = &T> {
            let domain = domain.to_vec();
            self.map.common_prefix_values_owned(domain)
        }
    }
}
