//! Regression tests for `String` keys that interact with label splitting.

use patricia_tree::StringPatriciaMap;

// Regression test for issue #59: a `str` key longer than `MAX_LABEL_LEN`
// (255) bytes whose 255th byte falls in the middle of a multi-byte character
// must not corrupt the tree.
#[test]
fn string_key_split_mid_character() {
    let mut map = StringPatriciaMap::new();

    // 254 ASCII bytes followed by a 3-byte character, so byte 255 lands on the
    // second byte of that character.
    let key = "a".repeat(254) + "あの";
    map.insert(key.clone(), 1);

    assert_eq!(map.len(), 1);
    assert_eq!(map.get(&key), Some(&1));

    // Force a split by inserting a sibling that shares the long prefix.
    map.insert("b", 2);
    assert_eq!(map.len(), 2);
    assert_eq!(map.get(&key), Some(&1));
    assert_eq!(map.get("b"), Some(&2));

    let entries = map
        .iter()
        .map(|(k, v)| (k.to_string(), *v))
        .collect::<Vec<_>>();
    assert_eq!(entries, vec![(key, 1), ("b".to_string(), 2)]);
}
