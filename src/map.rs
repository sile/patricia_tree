use std::iter::FromIterator;

use tree::PatriciaTree;

// TODO: impl
// - Clone
// - IntoIterator
#[derive(Debug, Default, Clone)]
pub struct PatriciaMap<V> {
    tree: PatriciaTree<V>,
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
    /// map.insert("foo".bytes(), 10);
    /// assert_eq!(map.len(), 1);
    /// assert_eq!(map.get("foo".bytes()), Some(&10));
    ///
    /// map.remove("foo".bytes());
    /// assert_eq!(map.get("foo".bytes()), None);
    /// ```
    pub fn new() -> Self {
        PatriciaMap { tree: PatriciaTree::new() }
    }

    /// Clears this map, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo".bytes(), 1);
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
    /// map.insert("foo".bytes(), 1);
    /// assert!(map.contains_key("foo".bytes()));
    /// assert!(!map.contains_key("bar".bytes()));
    /// ```
    pub fn contains_key<K>(&self, key: K) -> bool
    where
        K: Iterator<Item = u8>,
    {
        // TODO: optimize
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
    /// map.insert("foo".bytes(), 1);
    /// assert_eq!(map.get("foo".bytes()), Some(&1));
    /// assert_eq!(map.get("bar".bytes()), None);
    /// ```
    pub fn get<K>(&self, key: K) -> Option<&V>
    where
        K: Iterator<Item = u8>,
    {
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
    /// map.insert("foo".bytes(), 1);
    /// map.get_mut("foo".bytes()).map(|v| *v = 2);
    /// assert_eq!(map.get("foo".bytes()), Some(&2));
    /// ```
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.get_mut(key)
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
    /// assert_eq!(map.insert("foo".bytes(), 1), None);
    /// assert_eq!(map.get("foo".bytes()), Some(&1));
    /// assert_eq!(map.insert("foo".bytes(), 2), Some(1));
    /// assert_eq!(map.get("foo".bytes()), Some(&2));
    /// ```
    pub fn insert<K>(&mut self, key: K, value: V) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.insert(key, value)
    }

    /// Removes a key from this map, returning the value at the key if the key was previously in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo".bytes(), 1);
    /// assert_eq!(map.remove("foo".bytes()), Some(1));
    /// assert_eq!(map.remove("foo".bytes()), None);
    /// ```
    pub fn remove<K>(&mut self, key: K) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.remove(key)
    }

    /// Returns the number of elements in this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map = PatriciaMap::new();
    /// map.insert("foo".bytes(), 1);
    /// map.insert("bar".bytes(), 2);
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
    /// map.insert("foo".bytes(), 1);
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
    // # Examples
    //
    // ```
    // use patricia_tree::PatriciaMap;
    //
    // let map: PatriciaMap<_> =
    //     vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)].into_iter().collect();
    // assert_eq!(vec![(Vec::from("bar"), &2), ("baz".into(), &3), ("foo".into(), &1)],
    //            map.iter().collect::<Vec<_>>());
    // ```
    pub fn iter(&self) -> Iter<V> {
        unimplemented!()
    }
    // TODO:
    // - iter
    // - iter_mut
    // - keys
    // - values
    // - values_mut
    // - nodes (or graph)
    // - from_nodes
}
impl<K, V> FromIterator<(K, V)> for PatriciaMap<V>
where
    K: Iterator<Item = u8>,
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
impl<K, V> Extend<(K, V)> for PatriciaMap<V>
where
    K: Iterator<Item = u8>,
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

#[derive(Debug)]
pub struct Iter<'a, V>(::std::marker::PhantomData<(&'a u8, V)>);
impl<'a, V: 'a> Iterator for Iter<'a, V> {
    type Item = (Vec<u8>, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}
