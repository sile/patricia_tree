//! A set based on a patricia tree.
use std::fmt;
use std::iter::FromIterator;

use map::{self, PatriciaMap};
use node::Node;

/// A set based on a patricia tree.
#[derive(Default, Clone)]
pub struct PatriciaSet {
    map: PatriciaMap<()>,
}
impl PatriciaSet {
    /// Makes a new empty `PatriciaSet` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let set = PatriciaSet::new();
    /// assert!(set.is_empty());
    /// ```
    pub fn new() -> Self {
        PatriciaSet { map: PatriciaMap::new() }
    }

    /// Returns the number of elements in this set.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// set.insert("bar");
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if this set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert("foo");
    /// assert!(!set.is_empty());
    ///
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears this set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns `true` if this set contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// assert!(set.contains("foo"));
    /// assert!(!set.contains("bar"));
    /// ```
    pub fn contains<T: AsRef<[u8]>>(&self, value: T) -> bool {
        self.map.get(value).is_some()
    }

    /// Adds a value to this set.
    ///
    /// If the set did not have this value present, `true` is returned.
    /// If the set did have this value present, `false` is returned, and the entry is not updated.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// assert!(set.insert("foo"));
    /// assert!(!set.insert("foo"));
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert<T: AsRef<[u8]>>(&mut self, value: T) -> bool {
        self.map.insert(value, ()).is_none()
    }

    /// Removes a value from the set. Returns `true` is the value was present in this set.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// assert_eq!(set.remove("foo"), true);
    /// assert_eq!(set.remove("foo"), false);
    /// ```
    pub fn remove<T: AsRef<[u8]>>(&mut self, value: T) -> bool {
        self.map.remove(value).is_some()
    }

    /// Gets an iterator over the contents of this set, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// set.insert("bar");
    /// set.insert("baz");
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), [Vec::from("bar"), "baz".into(), "foo".into()]);
    /// ```
    pub fn iter(&self) -> Iter {
        Iter(self.map.keys())
    }
}
impl fmt::Debug for PatriciaSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, t) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", t)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}
impl IntoIterator for PatriciaSet {
    type Item = Vec<u8>;
    type IntoIter = IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.map.into_iter())
    }
}
impl<T: AsRef<[u8]>> FromIterator<T> for PatriciaSet {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = PatriciaSet::new();
        for t in iter {
            set.insert(t);
        }
        set
    }
}
impl<T: AsRef<[u8]>> Extend<T> for PatriciaSet {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for t in iter {
            self.insert(t);
        }
    }
}
impl From<Node<()>> for PatriciaSet {
    fn from(f: Node<()>) -> Self {
        PatriciaSet { map: f.into() }
    }
}
impl From<PatriciaSet> for Node<()> {
    fn from(f: PatriciaSet) -> Self {
        f.map.into()
    }
}
impl AsRef<Node<()>> for PatriciaSet {
    fn as_ref(&self) -> &Node<()> {
        self.map.as_ref()
    }
}

/// An Iterator over a `PatriciaSet`'s items.
#[derive(Debug)]
pub struct Iter<'a>(map::Keys<'a, ()>);
impl<'a> Iterator for Iter<'a> {
    type Item = Vec<u8>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// An owning iterator over a `PatriciaSet`'s items.
#[derive(Debug)]
pub struct IntoIter(map::IntoIter<()>);
impl Iterator for IntoIter {
    type Item = Vec<u8>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn debug_works() {
        let set: PatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        assert_eq!(
            format!("{:?}", set),
            "{[98, 97, 114], [98, 97, 122], [102, 111, 111]}"
        );
    }
}
