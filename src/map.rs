//! A map based on a patricia tree.
use crate::node;
#[cfg(any(test, feature = "serde"))]
use crate::node::Node;
use crate::tree::{self, PatriciaTree};
use crate::{BorrowedBytes, Bytes};
use alloc::borrow::ToOwned;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::iter::FromIterator;
use core::marker::PhantomData;

/// Patricia tree based map with [`Vec<u8>`] as key.
pub type PatriciaMap<V> = GenericPatriciaMap<Vec<u8>, V>;

/// Patricia tree based map with [`String`] as key.
///
/// Keys are compared at character boundaries, and all prefix operations are
/// aligned to character boundaries of the query key.  For example,
/// `longest_common_prefix_len()` never returns a length that splits a
/// multi-byte character.
pub type StringPatriciaMap<V> = GenericPatriciaMap<String, V>;

/// Patricia tree based map.
pub struct GenericPatriciaMap<K, V> {
    tree: PatriciaTree<V>,
    _key: PhantomData<K>,
}

impl<K, V> GenericPatriciaMap<K, V> {
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
        GenericPatriciaMap {
            tree: PatriciaTree::new(),
            _key: PhantomData,
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

    #[cfg(feature = "serde")]
    pub(crate) fn from_node(node: Node<V>) -> Self {
        Self {
            tree: node.into(),
            _key: PhantomData,
        }
    }

    #[cfg(any(test, feature = "serde"))]
    pub(crate) fn as_node(&self) -> &Node<V> {
        self.tree.root()
    }

    #[cfg(test)]
    pub(crate) fn into_node(self) -> Node<V> {
        self.tree.into_root()
    }
}
impl<K: Bytes, V> GenericPatriciaMap<K, V> {
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
    pub fn contains_key<Q: AsRef<K::Borrowed>>(&self, key: Q) -> bool {
        self.tree.get(key.as_ref()).is_some()
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
    pub fn get<Q: AsRef<K::Borrowed>>(&self, key: Q) -> Option<&V> {
        self.tree.get(key.as_ref())
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
    pub fn get_mut<Q: AsRef<K::Borrowed>>(&mut self, key: Q) -> Option<&mut V> {
        self.tree.get_mut(key.as_ref())
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
    pub fn get_longest_common_prefix<'a, Q>(&self, key: &'a Q) -> Option<(&'a K::Borrowed, &V)>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        let (key, value) = self.tree.get_longest_common_prefix(key.as_ref())?;
        Some((K::Borrowed::from_bytes(key), value))
    }

    /// Finds the longest common prefix of `key` and the keys in this map,
    /// and returns a mutable reference to the entry whose key matches the prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// map.insert("foobar", 2);
    /// assert_eq!(map.get_longest_common_prefix_mut("fo"), None);
    /// assert_eq!(map.get_longest_common_prefix_mut("foo"), Some(("foo".as_bytes(), &mut 1)));
    /// *map.get_longest_common_prefix_mut("foo").unwrap().1 = 3;
    /// assert_eq!(map.get_longest_common_prefix_mut("fooba"), Some(("foo".as_bytes(), &mut 3)));
    /// assert_eq!(map.get_longest_common_prefix_mut("foobar"), Some(("foobar".as_bytes(), &mut 2)));
    /// *map.get_longest_common_prefix_mut("foobar").unwrap().1 = 4;
    /// assert_eq!(map.get_longest_common_prefix_mut("foobarbaz"), Some(("foobar".as_bytes(), &mut 4)));
    /// ```
    pub fn get_longest_common_prefix_mut<'a, Q>(
        &mut self,
        key: &'a Q,
    ) -> Option<(&'a K::Borrowed, &mut V)>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        let (key, value) = self.tree.get_longest_common_prefix_mut(key.as_ref())?;
        Some((K::Borrowed::from_bytes(key), value))
    }

    /// Returns the longest common prefix length of `key` and the keys in this map.
    ///
    /// Unlike `get_longest_common_prefix()`, this method does not check if there is a key that matches the prefix in this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo", 1);
    /// map.insert("foobar", 2);
    /// assert_eq!(map.longest_common_prefix_len("fo"), 2);
    /// assert_eq!(map.longest_common_prefix_len("foo"), 3);
    /// assert_eq!(map.longest_common_prefix_len("fooba"), 5);
    /// assert_eq!(map.longest_common_prefix_len("foobar"), 6);
    /// assert_eq!(map.longest_common_prefix_len("foobarbaz"), 6);
    /// assert_eq!(map.longest_common_prefix_len("foba"), 2);
    /// ```
    pub fn longest_common_prefix_len<Q>(&self, key: &Q) -> usize
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        self.tree.longest_common_prefix_len(key.as_ref())
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
    pub fn insert<Q: AsRef<K::Borrowed>>(&mut self, key: Q, value: V) -> Option<V> {
        self.tree.insert(key.as_ref(), value)
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
    pub fn remove<Q: AsRef<K::Borrowed>>(&mut self, key: Q) -> Option<V> {
        self.tree.remove(key.as_ref())
    }

    /// Returns an iterator that collects all entries in the map up to a certain key.
    ///
    /// # Example
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
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
    pub fn common_prefixes<'a, 'b, Q>(
        &'a self,
        key: &'b Q,
    ) -> CommonPrefixesIter<'a, 'b, K::Borrowed, V>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        CommonPrefixesIter {
            key_bytes: key.as_ref().as_bytes(),
            iterator: self.tree.common_prefixes(key.as_ref()),
        }
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
    pub fn common_prefix_values<'a, 'b, Q>(&'a self, key: &'b Q) -> impl Iterator<Item = &'a V>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
        <K as Bytes>::Borrowed: 'b,
    {
        self.tree
            .common_prefixes(key.as_ref())
            .filter_map(|(_, n)| n.value())
    }

    /// Returns an iterator that collects all values of entries in the map up to a certain key.
    /// Takes owned key value so that iterator is not tied to key lifetime
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
    ///     .common_prefix_values_owned(b"abcde".to_vec())
    ///     .flatten()
    ///     .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    /// ```
    pub fn common_prefix_values_owned(&self, key: K) -> impl Iterator<Item = &V>
    where
        K: AsRef<K::Borrowed>,
    {
        self.tree
            .common_prefixes_owned(key)
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
    pub fn split_by_prefix<Q: AsRef<K::Borrowed>>(&mut self, prefix: Q) -> Self {
        let subtree = self.tree.split_by_prefix(prefix.as_ref());
        GenericPatriciaMap {
            tree: subtree,
            _key: PhantomData,
        }
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
    pub fn iter(&self) -> Iter<'_, K, V> {
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
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(self.tree.nodes_mut(), Vec::new())
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
    pub fn keys(&self) -> Keys<'_, K, V> {
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
    pub fn values(&self) -> Values<'_, V> {
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
    pub fn values_mut(&mut self) -> ValuesMut<'_, V> {
        ValuesMut {
            nodes: self.tree.nodes_mut(),
        }
    }
}
impl<K: Bytes, V> GenericPatriciaMap<K, V> {
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
    pub fn iter_prefix<'a>(&'a self, prefix: &K::Borrowed) -> impl Iterator<Item = (K, &'a V)> {
        self.tree
            .iter_prefix(prefix)
            .into_iter()
            .flat_map(move |(prefix_len, nodes)| {
                Iter::<K, V>::new(nodes, Vec::from(&prefix.as_bytes()[..prefix_len]))
            })
    }

    /// Gets a mutable iterator over the entries having the given prefix of this map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map: PatriciaMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &mut 2), ("baz".into(), &mut 3)],
    ///            map.iter_prefix_mut(b"ba").collect::<Vec<_>>());
    /// ```
    pub fn iter_prefix_mut<'a>(
        &'a mut self,
        prefix: &K::Borrowed,
    ) -> impl Iterator<Item = (K, &'a mut V)> {
        self.tree
            .iter_prefix_mut(prefix)
            .into_iter()
            .flat_map(move |(prefix_len, nodes)| {
                IterMut::<K, V>::new(nodes, Vec::from(&prefix.as_bytes()[..prefix_len]))
            })
    }
}
impl<K: Bytes + fmt::Debug, V: fmt::Debug> fmt::Debug for GenericPatriciaMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
impl<K, V: Clone> Clone for GenericPatriciaMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            tree: self.tree.clone(),
            _key: PhantomData,
        }
    }
}
impl<K, V> Default for GenericPatriciaMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K: Bytes, V> IntoIterator for GenericPatriciaMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: self.tree.into_nodes(),
            key_bytes: Vec::new(),
            _key: PhantomData,
        }
    }
}
impl<K, Q, V> FromIterator<(Q, V)> for GenericPatriciaMap<K, V>
where
    K: Bytes,
    Q: AsRef<K::Borrowed>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (Q, V)>,
    {
        let mut map = GenericPatriciaMap::new();
        for (k, v) in iter {
            map.insert(k, v);
        }
        map
    }
}
impl<K, Q, V> Extend<(Q, V)> for GenericPatriciaMap<K, V>
where
    K: Bytes,
    Q: AsRef<K::Borrowed>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (Q, V)>,
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// An iterator over a `PatriciaMap`'s entries.
#[derive(Debug)]
pub struct Iter<'a, K, V: 'a> {
    nodes: tree::Nodes<'a, V>,
    key_bytes: Vec<u8>,
    key_offset: usize,
    _key: PhantomData<K>,
}
impl<'a, K, V: 'a> Iter<'a, K, V> {
    fn new(nodes: tree::Nodes<'a, V>, key: Vec<u8>) -> Self {
        let key_offset = key.len();
        Self {
            nodes,
            key_bytes: key,
            key_offset,
            _key: PhantomData,
        }
    }
}
impl<'a, K: Bytes, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        for (key_len, node) in &mut self.nodes {
            self.key_bytes.truncate(self.key_offset + key_len);
            self.key_bytes.extend(node.label());
            if let Some(value) = node.value() {
                return Some((K::Borrowed::from_bytes(&self.key_bytes).to_owned(), value));
            }
        }
        None
    }
}

/// An owning iterator over a `PatriciaMap`'s entries.
#[derive(Debug)]
pub struct IntoIter<K, V> {
    nodes: tree::IntoNodes<V>,
    key_bytes: Vec<u8>,
    _key: PhantomData<K>,
}
impl<K: Bytes, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        for (key_len, mut node) in &mut self.nodes {
            self.key_bytes.truncate(key_len);
            self.key_bytes.extend(node.label());
            if let Some(value) = node.take_value() {
                return Some((K::Borrowed::from_bytes(&self.key_bytes).to_owned(), value));
            }
        }
        None
    }
}

/// A mutable iterator over a `PatriciaMap`'s entries.
#[derive(Debug)]
pub struct IterMut<'a, K, V: 'a> {
    nodes: tree::NodesMut<'a, V>,
    key_bytes: Vec<u8>,
    key_offset: usize,
    _key: PhantomData<K>,
}
impl<'a, K, V: 'a> IterMut<'a, K, V> {
    fn new(nodes: tree::NodesMut<'a, V>, key: Vec<u8>) -> Self {
        let key_offset = key.len();
        Self {
            nodes,
            key_bytes: key,
            key_offset,
            _key: PhantomData,
        }
    }
}
impl<'a, K: Bytes, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        for (key_len, node) in &mut self.nodes {
            self.key_bytes.truncate(self.key_offset + key_len);
            self.key_bytes.extend(node.label());
            if let Some(value) = node.into_value_mut() {
                return Some((K::Borrowed::from_bytes(&self.key_bytes).to_owned(), value));
            }
        }
        None
    }
}

/// An iterator over a `PatriciaMap`'s keys.
#[derive(Debug)]
pub struct Keys<'a, K, V: 'a>(Iter<'a, K, V>);
impl<'a, K: Bytes, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

/// An iterator over a `PatriciaMap`'s values.
#[derive(Debug)]
pub struct Values<'a, V: 'a> {
    nodes: tree::Nodes<'a, V>,
}
impl<'a, V: 'a> Iterator for Values<'a, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        for (_, node) in &mut self.nodes {
            if let Some(value) = node.value() {
                return Some(value);
            }
        }
        None
    }
}

/// A mutable iterator over a `PatriciaMap`'s values.
#[derive(Debug)]
pub struct ValuesMut<'a, V: 'a> {
    nodes: tree::NodesMut<'a, V>,
}
impl<'a, V: 'a> Iterator for ValuesMut<'a, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        for (_, node) in &mut self.nodes {
            if let Some(value) = node.into_value_mut() {
                return Some(value);
            }
        }
        None
    }
}

/// An iterator over entries in a `PatriciaMap` that share a common prefix with
/// a given key.
#[derive(Debug)]
pub struct CommonPrefixesIter<'a, 'b, K: ?Sized, V> {
    key_bytes: &'b [u8],
    iterator: node::CommonPrefixesIter<'a, 'b, K, V>,
}
impl<'a, 'b, K, V> Iterator for CommonPrefixesIter<'a, 'b, K, V>
where
    K: 'b + ?Sized + BorrowedBytes,
{
    type Item = (&'b K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        for (prefix_len, n) in self.iterator.by_ref() {
            if let Some(v) = n.value() {
                return Some((K::from_bytes(&self.key_bytes[..prefix_len]), v));
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_patricia_map_works() {
        // Insert as bytes.
        let mut t = PatriciaMap::new();
        t.insert("🌏🗻", ()); // [240,159,140,143,240,159,151,187]
        t.insert("🌏🍔", ()); // [240,159,140,143,240,159,141,148]

        let first_label = t.as_node().child().unwrap().label();
        assert!(core::str::from_utf8(first_label).is_err());
        assert_eq!(first_label, [240, 159, 140, 143, 240, 159]);

        // Insert as string.
        let mut t = StringPatriciaMap::new();
        t.insert("🌏🗻", ());
        t.insert("🌏🍔", ());

        let first_label = t.as_node().child().unwrap().label();
        assert_eq!(core::str::from_utf8(first_label).ok(), Some("🌏"));
    }
}
