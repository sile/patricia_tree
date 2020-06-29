//! A node which represents a subtree of a patricia tree.
use std::alloc::{self, Layout};
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::slice;

macro_rules! assert_some {
    ($expr:expr) => {
        if let Some(value) = $expr {
            value
        } else {
            panic!("`{}` must be `Some(..)`", stringify!($expr));
        }
    };
}

#[cfg(feature = "binary-format")]
pub use crate::codec::{NodeDecoder, NodeEncoder};

const MAX_LABEL_LEN: usize = 255;

/// A node which represents a subtree of a patricia tree.
///
/// Note that this is a low level building block.
/// Usually it is recommended to use more high level data structures (e.g., `PatriciaTree`).
#[derive(Debug)]
#[repr(C)]
pub struct Node<V> {
    value: Option<V>,
    child: Option<*mut Node<V>>,
    sibling: Option<*mut Node<V>>,
    label: Vec<u8>,
    _value: PhantomData<V>,
}

unsafe impl<V> Send for Node<V> {}
unsafe impl<V> Sync for Node<V> {}

impl<V> Node<V> {
    /// Makes a new node which represents an empty tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::node::Node;
    ///
    /// let node = Node::<()>::root();
    /// assert!(node.label().is_empty());
    /// assert!(node.value().is_none());
    /// assert!(node.child().is_none());
    /// assert!(node.sibling().is_none());
    /// ```
    pub fn root() -> Self {
        Node::new(b"", None, None, None)
    }

    /// Makes a new node.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::node::Node;
    ///
    /// let node0 = Node::new("foo".as_ref(), Some(3), None, None);
    /// assert_eq!(node0.label(), b"foo");
    /// assert_eq!(node0.value(), Some(&3));
    /// assert_eq!(node0.child().map(|n| n.label()), None);
    /// assert_eq!(node0.sibling().map(|n| n.label()), None);
    ///
    /// let node1 = Node::new("bar".as_ref(), None, None, Some(node0));
    /// assert_eq!(node1.label(), b"bar");
    /// assert_eq!(node1.value(), None);
    /// assert_eq!(node1.child().map(|n| n.label()), None);
    /// assert_eq!(node1.sibling().map(|n| n.label()), Some(&b"foo"[..]));
    ///
    /// // If the length of a label name is longer than 255, it will be splitted to two nodes.
    /// let node2 = Node::new([b'a'; 256].as_ref(), Some(4), Some(node1), None);
    /// assert_eq!(node2.label(), [b'a'; 255].as_ref());
    /// assert_eq!(node2.value(), None);
    /// assert_eq!(node2.child().map(|n| n.label()), Some(&b"a"[..]));
    /// assert_eq!(node2.sibling().map(|n| n.label()), None);
    ///
    /// assert_eq!(node2.child().unwrap().value(), Some(&4));
    /// assert_eq!(node2.child().unwrap().child().unwrap().label(), b"bar");
    /// ```
    pub fn new(
        mut label: &[u8],
        mut value: Option<V>,
        mut child: Option<Self>,
        sibling: Option<Self>,
    ) -> Self {
        if label.len() > MAX_LABEL_LEN {
            child = Some(Node::new(&label[MAX_LABEL_LEN..], value, child, None));
            label = &label[..MAX_LABEL_LEN];
            value = None;
        }

        let child = child.map(|c| Box::into_raw(Box::new(c)));
        let sibling = sibling.map(|c| Box::into_raw(Box::new(c)));
        Node {
            value,
            child,
            sibling,
            label: label.to_vec(),
            _value: PhantomData,
        }
    }

    pub fn new_raw(
        mut label: &[u8],
        mut value: Option<V>,
        mut child: Option<*mut Self>,
        sibling: Option<*mut Self>,
    ) -> Self {
        if label.len() > MAX_LABEL_LEN {
            child = Some(Box::into_raw(Box::new(Node::new_raw(
                &label[MAX_LABEL_LEN..],
                value,
                child,
                None,
            ))));
            label = &label[..MAX_LABEL_LEN];
            value = None;
        }
        Node {
            value,
            child,
            sibling,
            label: label.to_vec(),
            _value: PhantomData,
        }
    }

    pub fn child(&self) -> Option<&Node<V>> {
        self.child.map(|c| unsafe { &*c })
    }

    pub fn sibling(&self) -> Option<&Node<V>> {
        self.sibling.map(|c| unsafe { &*c })
    }

    pub fn label(&self) -> &[u8] {
        &self.label[..self.label.len()]
    }

    pub fn label_mut(&mut self) -> &mut [u8] {
        let len = self.label.len();
        self.label[..len].as_mut()
    }

    pub fn value(&self) -> Option<&V> {
        self.value.as_ref()
    }

    pub fn value_mut(&mut self) -> Option<&mut V> {
        self.value.as_mut()
    }

    pub fn child_mut(&mut self) -> Option<&mut Node<V>> {
        self.child.map(|c| unsafe { &mut *c })
    }

    pub fn sibling_mut(&mut self) -> Option<&mut Node<V>> {
        self.sibling.map(|c| unsafe { &mut *c })
    }

    pub fn take_value(&mut self) -> Option<V> {
        self.value.take()
    }

    pub fn take_child(&mut self) -> Option<Self> {
        self.child.take().map(|c| unsafe { *Box::from_raw(c) })
    }

    pub fn take_sibling(&mut self) -> Option<Self> {
        self.sibling.take().map(|c| unsafe { *Box::from_raw(c) })
    }

    pub fn set_value(&mut self, value: V) {
        self.take_value();
        self.value = Some(value);
    }

    pub fn set_child(&mut self, child: Self) {
        self.take_child();
        self.child = Some(Box::into_raw(Box::new(child)));
    }

    pub fn set_sibling(&mut self, sibling: Self) {
        self.take_sibling();
        self.sibling = Some(Box::into_raw(Box::new(sibling)));
    }

    pub(crate) fn get(&self, key: &[u8]) -> Option<&V> {
        let common_prefix_len = self.skip_common_prefix(key);
        let next = &key[common_prefix_len..];
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                self.value()
            } else {
                self.child().and_then(|child| child.get(next))
            }
        } else if common_prefix_len == 0 && self.label().get(0) <= key.get(0) {
            self.sibling().and_then(|sibling| sibling.get(next))
        } else {
            None
        }
    }

    pub(crate) fn get_mut(&mut self, key: &[u8]) -> Option<&mut V> {
        let common_prefix_len = self.skip_common_prefix(key);
        let next = &key[common_prefix_len..];
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                self.value_mut()
            } else {
                self.child_mut().and_then(|child| child.get_mut(next))
            }
        } else if common_prefix_len == 0 && self.label().get(0) <= key.get(0) {
            self.sibling_mut().and_then(|sibling| sibling.get_mut(next))
        } else {
            None
        }
    }

    pub(crate) fn get_longest_common_prefix(
        &self,
        key: &[u8],
        offset: usize,
    ) -> Option<(usize, &V)> {
        let common_prefix_len = self.skip_common_prefix(key);
        let next = &key[common_prefix_len..];
        if common_prefix_len == self.label().len() {
            let offset = offset + common_prefix_len;
            if next.is_empty() {
                self.value().map(|v| (offset, v))
            } else {
                self.child()
                    .and_then(|child| child.get_longest_common_prefix(next, offset))
                    .or_else(|| self.value().map(|v| (offset, v)))
            }
        } else if common_prefix_len == 0 && self.label().get(0) <= key.get(0) {
            self.sibling()
                .and_then(|sibling| sibling.get_longest_common_prefix(next, offset))
        } else {
            None
        }
    }

    fn skip_common_prefix(&self, key: &[u8]) -> usize {
        self.label()
            .iter()
            .zip(key.iter())
            .take_while(|x| x.0 == x.1)
            .count()
    }

    pub(crate) fn remove(&mut self, key: &[u8]) -> Option<V> {
        let common_prefix_len = self.skip_common_prefix(key);
        let next = &key[common_prefix_len..];
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                self.take_value().map(|old| {
                    self.try_merge_with_child();
                    old
                })
            } else {
                self.child_mut()
                    .and_then(|child| child.remove(next))
                    .map(|old| {
                        self.try_reclaim_child();
                        self.try_merge_with_child();
                        old
                    })
            }
        } else if common_prefix_len == 0 && self.label().get(0) <= key.get(0) {
            self.sibling_mut()
                .and_then(|sibling| sibling.remove(next))
                .map(|old| {
                    self.try_reclaim_sibling();
                    old
                })
        } else {
            None
        }
    }

    pub(crate) fn insert(&mut self, key: &[u8], value: V) -> Option<V> {
        if self.label().get(0) > key.get(0) {
            let mut node = Node::new_raw(key, Some(value), None, Some(self as *mut _));
            mem::swap(self, &mut node);
            self.sibling = Some(Box::into_raw(Box::new(node)));
            return None;
        }

        let common_prefix_len = self.skip_common_prefix(key);
        let next = &key[common_prefix_len..];
        let is_label_matched = common_prefix_len == self.label().len();
        if next.is_empty() {
            if is_label_matched {
                let old = self.take_value();
                self.set_value(value);
                old
            } else {
                self.split_at(common_prefix_len);
                self.set_value(value);
                None
            }
        } else if is_label_matched {
            if let Some(child) = self.child_mut() {
                return child.insert(next, value);
            }
            let child = Node::new(next, Some(value), None, None);
            self.set_child(child);
            None
        } else if common_prefix_len == 0 {
            if let Some(sibling) = self.sibling_mut() {
                return sibling.insert(next, value);
            }
            let sibling = Node::new(next, Some(value), None, None);
            self.set_sibling(sibling);
            None
        } else {
            self.split_at(common_prefix_len);
            assert_some!(self.child_mut()).insert(next, value);
            None
        }
    }
    fn split_at(&mut self, position: usize) {
        debug_assert!(position < self.label_len());
        let value = self.take_value();
        let child = self.take_child();
        let sibling = self.take_sibling();

        let child = Node::new(&self.label()[position..], value, child, None);
        let parent = Node::new(&self.label()[..position], None, Some(child), sibling);
        *self = parent;
    }
    fn label_len(&self) -> usize {
        // self.label_len as usize
        self.label.len()
    }
    pub(crate) fn try_merge_with_child(&mut self) {
        if self.value().is_some() || self.child.is_none() {
            return;
        }

        let child = assert_some!(self.child());
        if child.sibling().is_none() && (self.label_len() + child.label_len()) <= MAX_LABEL_LEN {
            let mut child = assert_some!(self.take_child());
            let sibling = self.take_sibling();
            let value = child.take_value();
            let grandchild = child.take_child();

            let mut label = Vec::with_capacity(self.label_len() + child.label_len());
            label.extend(self.label());
            label.extend(child.label());
            let node = Self::new(&label, value, grandchild, sibling);
            *self = node;
        }
    }
    fn try_reclaim_sibling(&mut self) {
        let sibling = assert_some!(self.sibling());
        if sibling.value().is_some() | sibling.child().is_some() {
            return;
        }
        if let Some(sibling) = self.take_sibling().and_then(|mut n| n.take_sibling()) {
            self.set_sibling(sibling);
        }
    }
    fn try_reclaim_child(&mut self) {
        let child = assert_some!(self.child());
        if child.value().is_some() | child.child().is_some() {
            return;
        }
        if let Some(child) = self.take_child().and_then(|mut n| n.take_sibling()) {
            self.set_child(child);
        }
    }

    /// Gets an iterator which traverses the nodes in this tree, in depth first order.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::PatriciaSet;
    /// use patricia_tree::node::Node;
    ///
    /// let mut set = PatriciaSet::new();
    /// set.insert("foo");
    /// set.insert("bar");
    /// set.insert("baz");
    ///
    /// let node = Node::from(set);
    /// let nodes = node.iter().map(|(level, node)| (level, node.label())).collect::<Vec<_>>();
    /// assert_eq!(nodes,
    ///            [
    ///                (0, "".as_ref()),
    ///                (1, "ba".as_ref()),
    ///                (2, "r".as_ref()),
    ///                (2, "z".as_ref()),
    ///                (1, "foo".as_ref())
    ///            ]);
    /// ```
    pub fn iter(&self) -> Iter<V> {
        Iter {
            stack: vec![(0, self)],
        }
    }

    pub(crate) fn iter_descendant(&self) -> Iter<V> {
        Iter {
            stack: vec![(0, self)],
        }
    }

    pub(crate) fn common_prefixes<'a, K>(&'a self, key: K) -> CommonPrefixesIter<'a, K, V>
    where
        K: AsRef<[u8]>,
    {
        CommonPrefixesIter {
            key,
            stack: vec![(0, self)],
        }
    }

    pub(crate) fn get_prefix_node(&self, key: &[u8], offset: usize) -> Option<(usize, &Self)> {
        let common_prefix_len = self.skip_common_prefix(key);
        let next = &key[common_prefix_len..];
        if next.is_empty() {
            Some((common_prefix_len, self))
        } else if common_prefix_len == self.label().len() {
            let offset = offset + common_prefix_len;
            self.child()
                .and_then(|child| child.get_prefix_node(next, offset))
        } else if common_prefix_len == 0 && self.label().get(0) <= key.get(0) {
            self.sibling()
                .and_then(|sibling| sibling.get_prefix_node(next, offset))
        } else {
            None
        }
    }

    pub(crate) fn split_by_prefix(&mut self, prefix: &[u8]) -> Option<Self> {
        let common_prefix_len = self.skip_common_prefix(prefix);
        if common_prefix_len == prefix.len() {
            let value = self.take_value();
            let child = self.take_child();
            let node = Node::new(&self.label()[common_prefix_len..], value, child, None);
            if let Some(sibling) = self.take_sibling() {
                *self = sibling;
            }
            Some(node)
        } else if common_prefix_len == self.label().len() {
            let next = &prefix[common_prefix_len..];
            self.child_mut()
                .and_then(|child| child.split_by_prefix(next))
                .map(|old| {
                    self.try_reclaim_child();
                    self.try_merge_with_child();
                    old
                })
        } else if common_prefix_len == 0 && self.label().get(0) <= prefix.get(0) {
            let next = &prefix[common_prefix_len..];
            self.sibling_mut()
                .and_then(|sibling| sibling.split_by_prefix(next))
                .map(|old| {
                    self.try_reclaim_sibling();
                    old
                })
        } else {
            None
        }
    }
}

impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        let _ = self.take_value();
        let _ = self.take_child();
        let _ = self.take_sibling();
    }
}

impl<V: Clone> Clone for Node<V> {
    fn clone(&self) -> Self {
        let label = self.label();
        let value = self.value().cloned();
        let child = self.child().cloned();
        let sibling = self.sibling().cloned();
        Node::new(label, value, child, sibling)
    }
}

impl<V> IntoIterator for Node<V> {
    type Item = (usize, Node<V>);
    type IntoIter = IntoIter<V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            stack: vec![(0, self)],
        }
    }
}

/// An iterator which traverses the nodes in a tree, in depth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct Iter<'a, V: 'a> {
    stack: Vec<(usize, &'a Node<V>)>,
}
impl<'a, V: 'a> Iterator for Iter<'a, V> {
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.stack.pop() {
            if level != 0 {
                if let Some(sibling) = node.sibling() {
                    self.stack.push((level, sibling));
                }
            }
            if let Some(child) = node.child() {
                self.stack.push((level + 1, child));
            }
            Some((level, node))
        } else {
            None
        }
    }
}

/// An iterator over entries in that collects all values up to
/// until the key stops matching.
#[derive(Debug)]
pub(crate) struct CommonPrefixesIter<'a, K, V> {
    key: K,
    stack: Vec<(usize, &'a Node<V>)>,
}

impl<'a, K, V> Iterator for CommonPrefixesIter<'a, K, V>
where
    K: AsRef<[u8]>,
{
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((offset, node)) = self.stack.pop() {
            let common_prefix_len = node.skip_common_prefix(&self.key.as_ref()[offset..]);
            if common_prefix_len == 0 && node.label().get(0) <= self.key.as_ref().get(offset) {
                if let Some(sibling) = node.sibling() {
                    self.stack.push((offset, sibling));
                }
            }

            if common_prefix_len == node.label().len() {
                let prefix_len = offset + common_prefix_len;
                if let Some(child) = node.child() {
                    self.stack.push((prefix_len, child));
                }
                return Some((prefix_len, node));
            }
        }
        None
    }
}

/// An owning iterator which traverses the nodes in a tree, in depth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct IntoIter<V> {
    stack: Vec<(usize, Node<V>)>,
}
impl<V> Iterator for IntoIter<V> {
    type Item = (usize, Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, mut node)) = self.stack.pop() {
            if let Some(sibling) = node.take_sibling() {
                self.stack.push((level, sibling));
            }
            if let Some(child) = node.take_child() {
                self.stack.push((level + 1, child));
            }
            Some((level, node))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PatriciaSet;
    use std::str;

    #[test]
    fn long_label_works() {
        let node = Node::new(&[b'a'; 256][..], Some(10), None, None);
        assert_eq!(node.label(), &[b'a'; 255][..]);
        assert_eq!(node.value(), None);
        assert_eq!(node.child().is_some(), true);

        let child = node.child().unwrap();
        assert_eq!(child.label(), b"a");
        assert_eq!(child.value(), Some(&10));
    }

    #[test]
    fn split_at() {
        let mut node = Node::new(&[b'a'; 100][..], Some(10), None, None);
        assert!(node.child().is_none());
        assert_eq!(node.value(), Some(&10));
        node.split_at(50);
        let child = node.child().unwrap();
        assert_eq!(
            child.label(),
            &(0..50).map(|_| b'a').collect::<Vec<_>>()[..]
        );
        assert_eq!(child.value(), Some(&10));
    }

    #[test]
    fn test() {
        let node0 = Node::new("foo".as_ref(), Some(3), None, None);
        assert_eq!(node0.label(), b"foo");
        assert_eq!(node0.value(), Some(&3));
        assert_eq!(node0.child().map(|n| n.label()), None);
        assert_eq!(node0.sibling().map(|n| n.label()), None);

        let node1 = Node::new("bar".as_ref(), None, None, Some(node0));
        assert_eq!(node1.label(), b"bar");
        assert_eq!(node1.value(), None);
        assert_eq!(node1.child().map(|n| n.label()), None);
        assert_eq!(node1.sibling().map(|n| n.label()), Some(&b"foo"[..]));

        // If the length of a label name is longer than 255, it will be splitted to two nodes.
        let node2 = Node::new([b'a'; 256].as_ref(), Some(4), Some(node1), None);
        assert_eq!(node2.label(), [b'a'; 255].as_ref());
        assert_eq!(node2.value(), None);
        assert_eq!(node2.child().map(|n| n.label()), Some(&b"a"[..]));
        assert_eq!(node2.sibling().map(|n| n.label()), None);

        assert_eq!(node2.child().unwrap().value(), Some(&4));
        assert_eq!(node2.child().unwrap().child().unwrap().label(), b"bar");
    }

    #[test]
    fn insert_node() {
        let mut node0 = Node::new("foo".as_ref(), Some(3), None, None);
        node0.insert("fooo".as_ref(), 4);
        node0.insert("x".as_ref(), 5);
        assert_eq!(node0.value(), Some(&3));
        assert_eq!(node0.label(), &b"foo"[..]);
        assert_eq!(node0.child().unwrap().value(), Some(&4));
        assert_eq!(node0.child().unwrap().label(), &b"o"[..]);
    }
    #[test]
    fn insert_node_sibling() {
        let mut node0 = Node::new("foo".as_ref(), Some(3), None, None);
        node0.insert("fooo".as_ref(), 4);
        node0.insert("a".as_ref(), 5); // becomes root node

        assert_eq!(node0.value(), Some(&5));
        assert_eq!(node0.label(), &b"a"[..]);
        assert_eq!(node0.sibling().unwrap().value(), Some(&3));
        assert_eq!(node0.sibling().unwrap().label(), &b"foo"[..]);
    }

    #[test]
    fn get_longest_common_prefix_works() {
        let set = ["123", "123456", "1234_67", "123abc", "123def"]
            .iter()
            .collect::<PatriciaSet>();

        let lcp = |key| set.get_longest_common_prefix(key);
        assert_eq!(lcp(""), None);
        assert_eq!(lcp("12"), None);
        assert_eq!(lcp("123"), Some("123".as_bytes()));
        assert_eq!(lcp("1234"), Some("123".as_bytes()));
        assert_eq!(lcp("123456"), Some("123456".as_bytes()));
        assert_eq!(lcp("1234_6"), Some("123".as_bytes()));
        assert_eq!(lcp("123456789"), Some("123456".as_bytes()));
    }

    #[test]
    fn reclaim_works() {
        let mut set = ["123", "123456", "123abc", "123def"]
            .iter()
            .collect::<PatriciaSet>();
        assert_eq!(
            set_to_labels(&set),
            [(0, ""), (1, "123"), (2, "456"), (2, "abc"), (2, "def")]
        );

        set.remove("123def");
        assert_eq!(set_to_labels(&set), [(0, "123"), (1, "456"), (1, "abc")]);

        set.remove("123456");
        assert_eq!(set_to_labels(&set), [(0, "123"), (1, "abc")]);

        set.remove("123");
        assert_eq!(set_to_labels(&set), [(0, "123abc")]);
    }

    fn set_to_labels(set: &PatriciaSet) -> Vec<(usize, &str)> {
        set.as_ref()
            .iter()
            .map(|(level, n)| (level, str::from_utf8(n.label()).unwrap()))
            .collect()
    }
}
