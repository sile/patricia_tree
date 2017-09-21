use tree::PatriciaTree;

#[derive(Debug)]
pub struct PatriciaMap<V> {
    tree: PatriciaTree<V>,
}
impl<V> PatriciaMap<V> {
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
    pub fn get<K>(&self, key: K) -> Option<&V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.get(key)
    }
    pub fn remove<K>(&mut self, key: K) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        self.tree.remove(key)
    }
}
