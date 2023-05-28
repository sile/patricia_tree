//! A set based on a patricia tree.
use crate::map::{self, PatriciaMap};
#[cfg(any(feature = "serde", test))]
use crate::node::Node;
use crate::Bytes;
use std::fmt;
use std::iter::FromIterator;

/// TODO
pub type BytesPatriciaSet = PatriciaSet<[u8]>;

/// A set based on a patricia tree.
#[derive(Default, Clone)]
pub struct PatriciaSet<T: ?Sized> {
    map: PatriciaMap<T, ()>,
}

impl<T: ?Sized> PatriciaSet<T> {
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
        PatriciaSet {
            map: PatriciaMap::new(),
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
            map: PatriciaMap::from_node(node),
        }
    }

    #[cfg(feature = "serde")]
    pub(crate) fn as_node(&self) -> &Node<()> {
        self.map.as_node()
    }

    #[cfg(test)]
    pub(crate) fn into_node(self) -> Node<()> {
        self.map.into_node()
    }
}
impl<T: ?Sized + Bytes> PatriciaSet<T> {
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
    pub fn contains<U: AsRef<T>>(&self, value: U) -> bool {
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
    /// set.insert("foo");
    /// set.insert("foobar");
    /// assert_eq!(set.get_longest_common_prefix("fo"), None);
    /// assert_eq!(set.get_longest_common_prefix("foo"), Some("foo".as_bytes()));
    /// assert_eq!(set.get_longest_common_prefix("fooba"), Some("foo".as_bytes()));
    /// assert_eq!(set.get_longest_common_prefix("foobar"), Some("foobar".as_bytes()));
    /// assert_eq!(set.get_longest_common_prefix("foobarbaz"), Some("foobar".as_bytes()));
    /// ```
    pub fn get_longest_common_prefix<'a, U>(&self, value: &'a U) -> Option<&'a T>
    where
        U: AsRef<T> + ?Sized,
    {
        self.map.get_longest_common_prefix(value).map(|x| x.0)
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
    pub fn insert<U: AsRef<T>>(&mut self, value: U) -> bool {
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
    pub fn remove<U: AsRef<T>>(&mut self, value: U) -> bool {
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
    pub fn split_by_prefix<U: AsRef<T>>(&mut self, prefix: U) -> Self {
        PatriciaSet {
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
    pub fn iter(&self) -> Iter<T> {
        Iter(self.map.keys())
    }
}
impl<T: ?Sized + Bytes + ToOwned> PatriciaSet<T> {
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
    pub fn iter_prefix<'a, 'b>(&'a self, prefix: &'b T) -> impl 'a + Iterator<Item = T::Owned>
    where
        'b: 'a,
    {
        self.map.iter_prefix(prefix).map(|(k, _)| k)
    }
}
impl<T> fmt::Debug for PatriciaSet<T>
where
    T: ?Sized + Bytes + ToOwned,
    T::Owned: fmt::Debug,
{
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
impl<T: ?Sized + Bytes + ToOwned> IntoIterator for PatriciaSet<T> {
    type Item = T::Owned;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.map.into_iter())
    }
}
impl<T: ?Sized + Bytes + ToOwned, U: AsRef<T>> FromIterator<U> for PatriciaSet<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = U>,
    {
        let mut set = PatriciaSet::new();
        for t in iter {
            set.insert(t);
        }
        set
    }
}
impl<T: Bytes + ToOwned, U: AsRef<T>> Extend<U> for PatriciaSet<T> {
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
pub struct Iter<'a, T: ?Sized>(map::Keys<'a, T, ()>);
impl<'a, T: ?Sized + Bytes + ToOwned> Iterator for Iter<'a, T> {
    type Item = T::Owned;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// An owning iterator over a `PatriciaSet`'s items.
#[derive(Debug)]
pub struct IntoIter<T: ?Sized>(map::IntoIter<T, ()>);
impl<T: ?Sized + Bytes + ToOwned> Iterator for IntoIter<T> {
    type Item = T::Owned;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debug_works() {
        let set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        assert_eq!(
            format!("{:?}", set),
            "{[98, 97, 114], [98, 97, 122], [102, 111, 111]}"
        );
    }

    #[test]
    fn clear_works() {
        let mut set = BytesPatriciaSet::new();
        set.insert("foo");
        assert!(!set.is_empty());

        set.clear();
        assert!(set.is_empty());
    }

    #[test]
    fn into_iter_works() {
        let set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        assert_eq!(
            set.into_iter().collect::<Vec<_>>(),
            [Vec::from("bar"), "baz".into(), "foo".into()]
        );
    }

    #[test]
    fn split_by_prefix_works() {
        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("");
        assert!(set.is_empty());
        assert_eq!(
            splitted_set.iter().collect::<Vec<_>>(),
            [b"bar", b"baz", b"foo"]
        );

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("f");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"baz"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"foo"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("fo");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"baz"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"foo"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("foo");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"baz"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"foo"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("b");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"foo"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"bar", b"baz"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("ba");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"foo"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"bar", b"baz"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("bar");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"baz", b"foo"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"bar"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let mut splitted_set = set.split_by_prefix("baz");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"foo"]);
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"baz"]);

        splitted_set.insert("aaa");
        assert_eq!(splitted_set.iter().collect::<Vec<_>>(), [b"aaa", b"baz"]);

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("bazz");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"baz", b"foo"]);
        assert!(splitted_set.is_empty());

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("for");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"baz", b"foo"]);
        assert!(splitted_set.is_empty());

        let mut set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let splitted_set = set.split_by_prefix("qux");
        assert_eq!(set.iter().collect::<Vec<_>>(), [b"bar", b"baz", b"foo"]);
        assert!(splitted_set.is_empty());
    }

    #[test]
    fn iter_prefix_works() {
        fn assert_iter_prefix(set: &BytesPatriciaSet, prefix: &str) {
            let actual = set.iter_prefix(prefix.as_bytes()).collect::<Vec<_>>();
            let expected = set
                .iter()
                .filter(|key| key.starts_with(prefix.as_bytes()))
                .collect::<Vec<_>>();
            assert_eq!(actual, expected);
        }

        let set: BytesPatriciaSet = vec!["foo", "bar", "baz"].into_iter().collect();
        let prefixes = [
            "", "a", "b", "ba", "bar", "baz", "bax", "c", "f", "fo", "foo",
        ];
        for prefix in &prefixes {
            assert_iter_prefix(&set, prefix);
        }

        let set: BytesPatriciaSet = vec![
            "JavaScript",
            "Python",
            "Java",
            "C++",
            "Swift",
            "TypeScript",
            "Go",
            "SQL",
            "Ruby",
            "R",
            "PHP",
            "Perl",
            "Kotlin",
            "C#",
            "Rust",
            "Scheme",
            "Erlang",
            "Scala",
            "Elixir",
            "Haskell",
        ]
        .into_iter()
        .collect();
        let prefixes = [
            "", "P", "Py", "J", "Jav", "Java", "JavaS", "Rusti", "E", "El", "H", "S", "Sc",
        ];
        for prefix in &prefixes {
            assert_iter_prefix(&set, prefix);
        }
    }
}
