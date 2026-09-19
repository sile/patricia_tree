//! Tests for the `serde` feature.

use patricia_tree::PatriciaMap;

#[test]
fn serde_works() {
    let mut input = vec![
        (Vec::from("foo"), 1u32),
        ("bar".into(), 2),
        ("baz".into(), 3),
    ];
    input.sort();

    let map: PatriciaMap<u32> = input.iter().cloned().collect();
    let serialized = serde_json::to_vec(&map).unwrap();
    let map: PatriciaMap<u32> = serde_json::from_slice(serialized.as_slice()).unwrap();

    assert_eq!(map.len(), 3);
    assert_eq!(map.into_iter().collect::<Vec<_>>(), input);
}

#[test]
fn large_serde_works() {
    let mut input = (0..10000u32)
        .map(|i| (i.to_string().into_bytes(), i))
        .collect::<Vec<_>>();
    input.sort();

    let map: PatriciaMap<u32> = input.iter().cloned().collect();
    let serialized = serde_json::to_vec(&map).unwrap();
    let map: PatriciaMap<u32> = serde_json::from_slice(serialized.as_slice()).unwrap();

    assert_eq!(map.len(), 10000);
    assert_eq!(map.into_iter().collect::<Vec<_>>(), input);
}
