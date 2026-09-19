//! A set based on a patricia tree.
use crate::Bytes;
use crate::map::{self, GenericPatriciaMap};
#[cfg(any(feature = "serde", test))]
use crate::node::Node;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::iter::FromIterator;

/// Patricia tree based set with [`Vec<u8>`] as key.
pub type PatriciaSet = GenericPatriciaSet<Vec<u8>>;

/// Patricia tree based set with [`String`] as key.
///
/// Keys are compared at character boundaries, and all prefix operations are
/// aligned to character boundaries of the query value.
pub type StringPatriciaSet = GenericPatriciaSet<String>;

/// Patricia tree based set.
pub struct GenericPatriciaSet<T> {
    map: GenericPatriciaMap<T, ()>,
}
impl<T> GenericPatriciaSet<T> {
    /// Makes a new empty [`GenericPatriciaSet`] instance.
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
        GenericPatriciaSet {
            map: GenericPatriciaMap::new(),
        }
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

    #[cfg(feature = "serde")]
    pub(crate) fn from_node(node: Node<()>) -> Self {
        Self {
            map: GenericPatriciaMap::from_node(node),
        }
    }

    #[cfg(any(test, feature = "serde"))]
    pub(crate) fn as_node(&self) -> &Node<()> {
        self.map.as_node()
    }

    #[cfg(test)]
    pub(crate) fn into_node(self) -> Node<()> {
        self.map.into_node()
    }
}
impl<T: Bytes> GenericPatriciaSet<T> {
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
    pub fn contains<U: AsRef<T::Borrowed>>(&self, value: U) -> bool {
        self.map.get(value).is_some()
    }

    /// Finds the longest common prefix of `value` and the elements in this set.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    ///
    /// set.insert("foo");
    /// set.insert("foobar");
    /// assert_eq!(set.get_longest_common_prefix("fo"), None);
    /// assert_eq!(set.get_longest_common_prefix("foo"), Some("foo".as_bytes()));
    /// assert_eq!(set.get_longest_common_prefix("fooba"), Some("foo".as_bytes()));
    /// assert_eq!(set.get_longest_common_prefix("foobar"), Some("foobar".as_bytes()));
    /// assert_eq!(set.get_longest_common_prefix("foobarbaz"), Some("foobar".as_bytes()));
    /// ```
    pub fn get_longest_common_prefix<'a, U>(&self, value: &'a U) -> Option<&'a T::Borrowed>
    where
        U: ?Sized + AsRef<T::Borrowed>,
    {
        self.map.get_longest_common_prefix(value).map(|x| x.0)
    }

    /// Returns the longest common prefix length of `value` and the elements in this set.
    ///
    /// Unlike `get_longest_common_prefix()`, this method does not check if there is a element that matches the prefix in this set.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// set.insert("foobar");
    /// assert_eq!(set.longest_common_prefix_len("fo"), 2);
    /// assert_eq!(set.longest_common_prefix_len("foo"), 3);
    /// assert_eq!(set.longest_common_prefix_len("fooba"), 5);
    /// assert_eq!(set.longest_common_prefix_len("foobar"), 6);
    /// assert_eq!(set.longest_common_prefix_len("foobarbaz"), 6);
    /// assert_eq!(set.longest_common_prefix_len("foba"), 2);
    /// ```
    pub fn longest_common_prefix_len<U>(&self, value: &U) -> usize
    where
        U: ?Sized + AsRef<T::Borrowed>,
    {
        self.map.longest_common_prefix_len(value)
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
    pub fn insert<U: AsRef<T::Borrowed>>(&mut self, value: U) -> bool {
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
    pub fn remove<U: AsRef<T::Borrowed>>(&mut self, value: U) -> bool {
        self.map.remove(value).is_some()
    }

    /// Splits the set into two at the given prefix.
    ///
    /// The returned set contains all the entries that prefixed by `prefix`.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    ///
    /// let mut a = PatriciaSet::new();
    /// a.insert("rust");
    /// a.insert("ruby");
    /// a.insert("python");
    /// a.insert("erlang");
    ///
    /// let b = a.split_by_prefix("ru");
    ///
    /// assert_eq!(a.iter().collect::<Vec<_>>(), [b"erlang", b"python"]);
    /// assert_eq!(b.iter().collect::<Vec<_>>(), [b"ruby", b"rust"]);
    /// ```
    pub fn split_by_prefix<U: AsRef<T::Borrowed>>(&mut self, prefix: U) -> Self {
        GenericPatriciaSet {
            map: self.map.split_by_prefix(prefix),
        }
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
    pub fn iter(&self) -> Iter<'_, T> {
        Iter(self.map.keys())
    }
}
impl<T: Bytes> GenericPatriciaSet<T> {
    /// Gets an iterator over the contents having the given prefix of this set, in sorted order.
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
    /// assert_eq!(set.iter_prefix(b"ba").collect::<Vec<_>>(), [Vec::from("bar"), "baz".into()]);
    /// ```
    pub fn iter_prefix<'a, 'b>(&'a self, prefix: &'b T::Borrowed) -> impl 'a + Iterator<Item = T>
    where
        'b: 'a,
    {
        self.map.iter_prefix(prefix).map(|(k, _)| k)
    }
}
impl<T: Bytes + fmt::Debug> fmt::Debug for GenericPatriciaSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
impl<T> Clone for GenericPatriciaSet<T> {
    fn clone(&self) -> Self {
        GenericPatriciaSet {
            map: self.map.clone(),
        }
    }
}
impl<T> Default for GenericPatriciaSet<T> {
    fn default() -> Self {
        GenericPatriciaSet::new()
    }
}
impl<T: Bytes> IntoIterator for GenericPatriciaSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.map.into_iter())
    }
}
impl<T: Bytes, U: AsRef<T::Borrowed>> FromIterator<U> for GenericPatriciaSet<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = U>,
    {
        let mut set = GenericPatriciaSet::new();
        for t in iter {
            set.insert(t);
        }
        set
    }
}
impl<T: Bytes, U: AsRef<T::Borrowed>> Extend<U> for GenericPatriciaSet<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = U>,
    {
        for t in iter {
            self.insert(t);
        }
    }
}

/// An Iterator over a `PatriciaSet`'s items.
#[derive(Debug)]
pub struct Iter<'a, T>(map::Keys<'a, T, ()>);
impl<T: Bytes> Iterator for Iter<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// An owning iterator over a `PatriciaSet`'s items.
#[derive(Debug)]
pub struct IntoIter<T>(map::IntoIter<T, ()>);
impl<T: Bytes> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}
