use std::fmt;
use std::iter::FromIterator;

use node::Node;
use tree::{self, PatriciaTree};

#[derive(Default, Clone)]
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
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let map: PatriciaMap<_> =
    ///     vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &2), ("baz".into(), &3), ("foo".into(), &1)],
    ///            map.iter().collect::<Vec<_>>());
    /// ```
    pub fn iter(&self) -> Iter<V> {
        Iter {
            nodes: self.tree.nodes(),
            key: Vec::new(),
        }
    }

    /// Gets a mutable iterator over the entries of this map, soretd by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map: PatriciaMap<_> =
    ///     vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)].into_iter().collect();
    /// for (_, v) in map.iter_mut() {
    ///    *v += 10;
    /// }
    /// assert_eq!(map.get("bar".bytes()), Some(&12));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<V> {
        IterMut {
            nodes: self.tree.nodes(),
            key: Vec::new(),
        }
    }

    /// Gets an iterator over the keys of this map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let map: PatriciaMap<_> =
    ///     vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)].into_iter().collect();
    /// assert_eq!(vec![Vec::from("bar"), "baz".into(), "foo".into()],
    ///            map.keys().collect::<Vec<_>>());
    /// ```
    pub fn keys(&self) -> Keys<V> {
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
    ///     vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)].into_iter().collect();
    /// assert_eq!(vec![2, 3, 1],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values(&self) -> Values<V> {
        Values { nodes: self.tree.nodes() }
    }

    /// Gets a mutable iterator over the values of this map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaMap;
    ///
    /// let mut map: PatriciaMap<_> =
    ///     vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)].into_iter().collect();
    /// for v in map.values_mut() {
    ///     *v += 10;
    /// }
    /// assert_eq!(vec![12, 13, 11],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<V> {
        ValuesMut { nodes: self.tree.nodes() }
    }
}
impl<V: fmt::Debug> fmt::Debug for PatriciaMap<V> {
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
impl<V> From<Node<V>> for PatriciaMap<V> {
    fn from(f: Node<V>) -> Self {
        PatriciaMap { tree: f.into() }
    }
}
impl<V> From<PatriciaMap<V>> for Node<V> {
    fn from(f: PatriciaMap<V>) -> Self {
        f.tree.into()
    }
}
impl<V> AsRef<Node<V>> for PatriciaMap<V> {
    fn as_ref(&self) -> &Node<V> {
        self.tree.root()
    }
}

#[derive(Debug)]
pub struct Iter<'a, V: 'a> {
    nodes: tree::Nodes<'a, V>,
    key: Vec<u8>,
}
impl<'a, V: 'a> Iterator for Iter<'a, V> {
    type Item = (Vec<u8>, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_len, node)) = self.nodes.next() {
            self.key.truncate(key_len);
            self.key.extend(node.label());
            if let Some(value) = node.value() {
                return Some((self.key.clone(), value));
            }
        }
        None
    }
}

#[derive(Debug)]
pub struct IterMut<'a, V: 'a> {
    nodes: tree::Nodes<'a, V>,
    key: Vec<u8>,
}
impl<'a, V: 'a> Iterator for IterMut<'a, V> {
    type Item = (Vec<u8>, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_len, node)) = self.nodes.next() {
            self.key.truncate(key_len);
            self.key.extend(node.label());
            if let Some(value) = unsafe { node.value_mut() } {
                return Some((self.key.clone(), value));
            }
        }
        None
    }
}

#[derive(Debug)]
pub struct Keys<'a, V: 'a>(Iter<'a, V>);
impl<'a, V: 'a> Iterator for Keys<'a, V> {
    type Item = Vec<u8>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

#[derive(Debug)]
pub struct Values<'a, V: 'a> {
    nodes: tree::Nodes<'a, V>,
}
impl<'a, V: 'a> Iterator for Values<'a, V> {
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

#[derive(Debug)]
pub struct ValuesMut<'a, V: 'a> {
    nodes: tree::Nodes<'a, V>,
}
impl<'a, V: 'a> Iterator for ValuesMut<'a, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((_, node)) = self.nodes.next() {
            if let Some(value) = unsafe { node.value_mut() } {
                return Some(value);
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn debug_works() {
        let map: PatriciaMap<_> = vec![("foo".bytes(), 1), ("bar".bytes(), 2), ("baz".bytes(), 3)]
            .into_iter()
            .collect();
        assert_eq!(
            format!("{:?}", map),
            "{[98, 97, 114]: 2, [98, 97, 122]: 3, [102, 111, 111]: 1}"
        );
    }
}
