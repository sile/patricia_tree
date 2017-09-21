use tree::PatriciaTree;

#[derive(Debug)]
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

    /// Returns true if this map contains a value for the specified key.
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

    pub fn len(&self) -> usize {
        self.tree.len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn insert<K>(&mut self, key: K, value: V) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.insert(key, value)
    }
    pub fn remove<K>(&mut self, key: K) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.remove(key)
    }
}
