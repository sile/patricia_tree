//! A map based on a patricia tree.
use crate::node::Node;
use crate::tree::{self, PatriciaTree};
use std::alloc::{GlobalAlloc, System};
use std::fmt;
use std::iter::FromIterator;

/// A map based on a patricia tree.
#[derive(Clone)]
pub struct PatriciaMap<V, A: Clone + GlobalAlloc = System> {
    tree: PatriciaTree<V, A>,
}

impl<V> PatriciaMap<V> {
    /// Makes a new empty `PatriciaMap` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert("foo", 10);
    /// assert_eq!(map.len(), 1);
    /// assert_eq!(map.get("foo"), Some(&10));
    ///
    /// map.remove("foo");
    /// assert_eq!(map.get("foo"), None);
    /// ```
    pub fn new() -> Self {
        PatriciaMap {
            tree: PatriciaTree::new(),
        }
    }
}

impl<V, A: Clone + GlobalAlloc> PatriciaMap<V, A> {
    /// Same as `new`, but using a custom [`std::alloc::GlobalAlloc`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::alloc::System;
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new_in(System);
    /// map.insert("foo", 10);
    /// assert_eq!(map.len(), 1);
    /// ```
    ///
    pub fn new_in(allocator: A) -> Self {
        PatriciaMap {
            tree: PatriciaTree::new_in(allocator),
        }
    }

    /// Clears this map, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree.clear();
    }

    /// Returns `true` if this map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// assert!(map.contains_key("foo"));
    /// assert!(!map.contains_key("bar"));
    /// ```
    pub fn contains_key<K: AsRef<[u8]>>(&self, key: K) -> bool {
        self.tree.get(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.get("foo"), Some(&1));
    /// assert_eq!(map.get("bar"), None);
    /// ```
    pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<&V> {
        self.tree.get(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// map.get_mut("foo").map(|v| *v = 2);
    /// assert_eq!(map.get("foo"), Some(&2));
    /// ```
    pub fn get_mut<K: AsRef<[u8]>>(&mut self, key: K) -> Option<&mut V> {
        self.tree.get_mut(key)
    }

    /// Finds the longest common prefix of `key` and the keys in this map,
    /// and returns a reference to the entry whose key matches the prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// map.insert("foobar", 2);
    /// assert_eq!(map.get_longest_common_prefix("fo"), None);
    /// assert_eq!(map.get_longest_common_prefix("foo"), Some(("foo".as_bytes(), &1)));
    /// assert_eq!(map.get_longest_common_prefix("fooba"), Some(("foo".as_bytes(), &1)));
    /// assert_eq!(map.get_longest_common_prefix("foobar"), Some(("foobar".as_bytes(), &2)));
    /// assert_eq!(map.get_longest_common_prefix("foobarbaz"), Some(("foobar".as_bytes(), &2)));
    /// ```
    pub fn get_longest_common_prefix<'a, K>(&self, key: &'a K) -> Option<(&'a [u8], &V)>
    where
        K: AsRef<[u8]> + ?Sized,
    {
        self.tree.get_longest_common_prefix(key.as_ref())
    }

    /// Inserts a key-value pair into this map.
    ///
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// assert_eq!(map.insert("foo", 1), None);
    /// assert_eq!(map.get("foo"), Some(&1));
    /// assert_eq!(map.insert("foo", 2), Some(1));
    /// assert_eq!(map.get("foo"), Some(&2));
    /// ```
    pub fn insert<K: AsRef<[u8]>>(&mut self, key: K, value: V) -> Option<V> {
        self.tree.insert(key, value)
    }

    /// Removes a key from this map, returning the value at the key if the key was previously in it.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.remove("foo"), Some(1));
    /// assert_eq!(map.remove("foo"), None);
    /// ```
    pub fn remove<K: AsRef<[u8]>>(&mut self, key: K) -> Option<V> {
        self.tree.remove(key)
    }

    /// Returns an iterator that collects all entries in the map up to a certain key.
    ///
    /// # Example
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    /// let mut t = PatriciaMap::new();
    /// t.insert("a", vec!["a"]);
    /// t.insert("x", vec!["x"]);
    /// t.insert("ab", vec!["b"]);
    /// t.insert("abc", vec!["c"]);
    /// t.insert("abcd", vec!["d"]);
    /// t.insert("abcdf", vec!["f"]);
    /// assert!(t
    ///     .common_prefixes(b"abcde")
    ///     .map(|(_, v)| v)
    ///     .flatten()
    ///     .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    /// ```
    pub fn common_prefixes<'a, 'b>(
        &'a self,
        key: &'b [u8],
    ) -> impl 'b + Iterator<Item = (&'b [u8], &'a V)>
    where
        'a: 'b,
    {
        self.tree
            .common_prefixes(key)
            .filter_map(move |(prefix_len, n)| n.value().map(|v| (&key[..prefix_len], v)))
    }

    /// Returns an iterator that collects all values of entries in the map up to a certain key.
    ///
    /// # Example
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    /// let mut t = PatriciaMap::new();
    /// t.insert("a", vec!["a"]);
    /// t.insert("x", vec!["x"]);
    /// t.insert("ab", vec!["b"]);
    /// t.insert("abc", vec!["c"]);
    /// t.insert("abcd", vec!["d"]);
    /// t.insert("abcdf", vec!["f"]);
    /// assert!(t
    ///     .common_prefix_values(b"abcde")
    ///     .flatten()
    ///     .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    /// ```
    pub fn common_prefix_values<'a>(&'a self, key: &[u8]) -> impl 'a + Iterator<Item = &'a V> {
        self.tree
            .common_prefixes(key.to_owned())
            .filter_map(|(_, n)| n.value())
    }

    /// Splits the map into two at the given prefix.
    ///
    /// The returned map contains all the entries of which keys are prefixed by `prefix`.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut a = PatriciaMap::new();
    /// a.insert("rust", 1);
    /// a.insert("ruby", 2);
    /// a.insert("bash", 3);
    /// a.insert("erlang", 4);
    /// a.insert("elixir", 5);
    ///
    /// let b = a.split_by_prefix("e");
    /// assert_eq!(a.len(), 3);
    /// assert_eq!(b.len(), 2);
    ///
    /// assert_eq!(a.keys().collect::<Vec<_>>(), [b"bash", b"ruby", b"rust"]);
    /// assert_eq!(b.keys().collect::<Vec<_>>(), [b"elixir", b"erlang"]);
    /// ```
    pub fn split_by_prefix<K: AsRef<[u8]>>(&mut self, prefix: K) -> Self {
        let subtree = self.tree.split_by_prefix(prefix);
        PatriciaMap { tree: subtree }
    }

    /// Returns the number of elements in this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// map.insert("bar", 2);
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns `true` if this map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert("foo", 1);
    /// assert!(!map.is_empty());
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets an iterator over the entries of this map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &2), ("baz".into(), &3), ("foo".into(), &1)],
    ///            map.iter().collect::<Vec<_>>());
    /// ```
    pub fn iter(&self) -> Iter<V, A> {
        Iter::new(self.tree.nodes(), Vec::new())
    }

    /// Gets a mutable iterator over the entries of this map, soretd by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// for (_, v) in map.iter_mut() {
    ///    *v += 10;
    /// }
    /// assert_eq!(map.get("bar"), Some(&12));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<V, A> {
        IterMut {
            nodes: self.tree.nodes(),
            key: Vec::new(),
        }
    }

    /// Gets an iterator over the entries having the given prefix of this map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &2), ("baz".into(), &3)],
    ///            map.iter_prefix(b"ba").collect::<Vec<_>>());
    /// ```
    pub fn iter_prefix<'a, 'b>(
        &'a self,
        prefix: &'b [u8],
    ) -> impl 'a + Iterator<Item = (Vec<u8>, &'a V)>
    where
        'b: 'a,
    {
        self.tree
            .iter_prefix(prefix)
            .into_iter()
            .flat_map(move |(prefix_len, nodes)| Iter::new(nodes, Vec::from(&prefix[..prefix_len])))
    }

    /// Gets an iterator over the keys of this map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![Vec::from("bar"), "baz".into(), "foo".into()],
    ///            map.keys().collect::<Vec<_>>());
    /// ```
    pub fn keys(&self) -> Keys<V, A> {
        Keys(self.iter())
    }

    /// Gets an iterator over the values of this map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![2, 3, 1],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values(&self) -> Values<V, A> {
        Values {
            nodes: self.tree.nodes(),
        }
    }

    /// Gets a mutable iterator over the values of this map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// for v in map.values_mut() {
    ///     *v += 10;
    /// }
    /// assert_eq!(vec![12, 13, 11],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<V, A> {
        ValuesMut {
            nodes: self.tree.nodes(),
        }
    }
}
impl<V: fmt::Debug, A: Clone + GlobalAlloc> fmt::Debug for PatriciaMap<V, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (k, v)) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}: {:?}", k, v)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}
impl<V, A: Clone + GlobalAlloc + Default> Default for PatriciaMap<V, A> {
    fn default() -> Self {
        Self::new_in(Default::default())
    }
}
impl<V, A: Clone + GlobalAlloc> IntoIterator for PatriciaMap<V, A> {
    type Item = (Vec<u8>, V);
    type IntoIter = IntoIter<V, A>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: self.tree.into_nodes(),
            key: Vec::new(),
        }
    }
}
impl<K, V> FromIterator<(K, V)> for PatriciaMap<V>
where
    K: AsRef<[u8]>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut map = PatriciaMap::new();
        for (k, v) in iter {
            map.insert(k, v);
        }
        map
    }
}
impl<K, V, A: Clone + GlobalAlloc> Extend<(K, V)> for PatriciaMap<V, A>
where
    K: AsRef<[u8]>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}
impl<V, A: Clone + GlobalAlloc> From<Node<V, A>> for PatriciaMap<V, A> {
    fn from(f: Node<V, A>) -> Self {
        PatriciaMap { tree: f.into() }
    }
}
impl<V, A: Clone + GlobalAlloc> From<PatriciaMap<V, A>> for Node<V, A> {
    fn from(f: PatriciaMap<V, A>) -> Self {
        f.tree.into_root()
    }
}
impl<V, A: Clone + GlobalAlloc> AsRef<Node<V, A>> for PatriciaMap<V, A> {
    fn as_ref(&self) -> &Node<V, A> {
        self.tree.root()
    }
}

/// An iterator over a `PatriciaMap`'s entries.
#[derive(Debug)]
pub struct Iter<'a, V: 'a, A: Clone + GlobalAlloc> {
    nodes: tree::Nodes<'a, V, A>,
    key: Vec<u8>,
    key_offset: usize,
}
impl<'a, V: 'a, A: Clone + GlobalAlloc> Iter<'a, V, A> {
    fn new(nodes: tree::Nodes<'a, V, A>, key: Vec<u8>) -> Self {
        let key_offset = key.len();
        Self {
            nodes,
            key,
            key_offset,
        }
    }
}
impl<'a, V: 'a, A: Clone + GlobalAlloc> Iterator for Iter<'a, V, A> {
    type Item = (Vec<u8>, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_len, node)) = self.nodes.next() {
            self.key.truncate(self.key_offset + key_len);
            self.key.extend(node.label());
            if let Some(value) = node.value() {
                return Some((self.key.clone(), value));
            }
        }
        None
    }
}

/// An owning iterator over a `PatriciaMap`'s entries.
#[derive(Debug)]
pub struct IntoIter<V, A: Clone + GlobalAlloc> {
    nodes: tree::IntoNodes<V, A>,
    key: Vec<u8>,
}
impl<V, A: Clone + GlobalAlloc> Iterator for IntoIter<V, A> {
    type Item = (Vec<u8>, V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_len, mut node)) = self.nodes.next() {
            self.key.truncate(key_len);
            self.key.extend(node.label());
            if let Some(value) = node.take_value() {
                return Some((self.key.clone(), value));
            }
        }
        None
    }
}

/// A mutable iterator over a `PatriciaMap`'s entries.
#[derive(Debug)]
pub struct IterMut<'a, V: 'a, A: Clone + GlobalAlloc> {
    nodes: tree::Nodes<'a, V, A>,
    key: Vec<u8>,
}
impl<'a, V: 'a, A: Clone + GlobalAlloc> Iterator for IterMut<'a, V, A> {
    type Item = (Vec<u8>, &'a mut V);
    #[allow(mutable_transmutes)]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_len, node)) = self.nodes.next() {
            self.key.truncate(key_len);
            self.key.extend(node.label());

            let node = unsafe { &mut *(node as *const _ as *mut Node<V, A>) };
            if let Some(value) = node.value_mut() {
                return Some((self.key.clone(), value));
            }
        }
        None
    }
}

/// An iterator over a `PatriciaMap`'s keys.
#[derive(Debug)]
pub struct Keys<'a, V: 'a, A: Clone + GlobalAlloc>(Iter<'a, V, A>);
impl<'a, V: 'a, A: Clone + GlobalAlloc> Iterator for Keys<'a, V, A> {
    type Item = Vec<u8>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

/// An iterator over a `PatriciaMap`'s values.
#[derive(Debug)]
pub struct Values<'a, V: 'a, A: Clone + GlobalAlloc> {
    nodes: tree::Nodes<'a, V, A>,
}
impl<'a, V: 'a, A: Clone + GlobalAlloc> Iterator for Values<'a, V, A> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((_, node)) = self.nodes.next() {
            if let Some(value) = node.value() {
                return Some(value);
            }
        }
        None
    }
}

/// A mutable iterator over a `PatriciaMap`'s values.
#[derive(Debug)]
pub struct ValuesMut<'a, V: 'a, A: Clone + GlobalAlloc> {
    nodes: tree::Nodes<'a, V, A>,
}
impl<'a, V: 'a, A: Clone + GlobalAlloc> Iterator for ValuesMut<'a, V, A> {
    type Item = &'a mut V;
    #[allow(mutable_transmutes)]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((_, node)) = self.nodes.next() {
            let node = unsafe { &mut *(node as *const _ as *mut Node<V, A>) };
            if let Some(value) = node.value_mut() {
                return Some(value);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::seq::SliceRandom;

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
            format!("{:?}", map),
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
    #[cfg_attr(miri, ignore)]
    fn large_map_works() {
        let mut input = (0..10000).map(|i| (i.to_string(), i)).collect::<Vec<_>>();
        input.shuffle(&mut rand::thread_rng());

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
        for &(ref k, _) in input.iter().take(input.len() / 2) {
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
            .map(|(_, v)| v)
            .flatten()
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
            .map(|(_, v)| v)
            .flatten()
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
            .map(|(k, v)| {
                unsafe {
                    println!("{:?}", std::str::from_utf8_unchecked(k));
                }
                v
            })
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        dbg!(&results);
        assert!(results.iter().eq(vec![&"a"].into_iter()));

        let mut t = PatriciaMap::new();
        t.insert("ab", vec!["b"]);
        t.insert("a", vec!["a"]);
        t.insert("abc", vec!["c"]);
        t.insert("..", vec!["e"]);
        t.insert("x", vec!["d"]);

        let results = t
            .common_prefixes(b"abcd")
            .map(|(_, v)| v)
            .flatten()
            .cloned()
            .collect::<Vec<_>>();

        assert!(results.iter().eq(vec![&"a", &"b", &"c"].into_iter()));

        let mut list = PatriciaMap::new();
        list.insert(b".com.foocatnetworks.".as_ref(), vec![0 as u16]);
        list.insert(b".com.foocatnetworks.foo.".as_ref(), vec![1]);
        list.insert(b".com.foocatnetworks.foo.baz.".as_ref(), vec![2]);
        list.insert(b".com.google.".as_ref(), vec![0]);
        list.insert(b".com.cisco.".as_ref(), vec![0]);
        list.insert(b".org.wikipedia.".as_ref(), vec![0]);

        let results = list
            .common_prefixes(b".com.foocatnetworks.foo.baz.")
            .map(|(_, v)| v)
            .flatten()
            .cloned()
            .collect::<Vec<_>>();

        assert!(vec![0 as u16, 1, 2].into_iter().eq(results.into_iter()));
    }
}
