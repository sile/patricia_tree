use crate::{
    node::{self, Node, NodeMut},
    Bytes,
};

#[derive(Debug, Clone)]
pub struct PatriciaTree<V> {
    root: Node<V>,
    len: usize,
}

impl<V> PatriciaTree<V> {
    pub fn new() -> Self {
        PatriciaTree {
            root: Node::root(),
            len: 0,
        }
    }
    #[cfg(feature = "serde")]
    pub fn root(&self) -> &Node<V> {
        &self.root
    }
    #[cfg(test)]
    pub fn into_root(self) -> Node<V> {
        self.root
    }
    pub fn insert<K: ?Sized + Bytes>(&mut self, key: &K, value: V) -> Option<V> {
        if let Some(old) = self.root.insert(key, value) {
            Some(old)
        } else {
            self.len += 1;
            None
        }
    }
    pub fn get(&self, key: &[u8]) -> Option<&V> {
        self.root.get(key)
    }
    pub fn get_mut(&mut self, key: &[u8]) -> Option<&mut V> {
        self.root.get_mut(key)
    }
    pub fn get_longest_common_prefix<'a>(&self, key: &'a [u8]) -> Option<(&'a [u8], &V)> {
        self.root
            .get_longest_common_prefix(key, 0)
            .map(|(n, v)| (&key[..n], v))
    }
    pub fn iter_prefix<'a, 'b>(&'a self, prefix: &'b [u8]) -> Option<(usize, Nodes<V>)> {
        if let Some((common_prefix_len, node)) = self.root.get_prefix_node(prefix, 0) {
            let nodes = Nodes {
                nodes: node.iter_descendant(),
                label_lens: Vec::new(),
            };
            Some((prefix.len() - common_prefix_len, nodes))
        } else {
            None
        }
    }
    pub fn iter_prefix_mut<'a, 'b>(&'a mut self, prefix: &'b [u8]) -> Option<(usize, NodesMut<V>)> {
        if let Some((common_prefix_len, node)) = self.root.get_prefix_node_mut(prefix, 0) {
            let nodes = NodesMut {
                nodes: node.iter_descendant_mut(),
                label_lens: Vec::new(),
            };
            Some((prefix.len() - common_prefix_len, nodes))
        } else {
            None
        }
    }
    pub(crate) fn common_prefixes<K>(&self, key: K) -> node::CommonPrefixesIter<K, V>
    where
        K: AsRef<[u8]>,
    {
        self.root.common_prefixes(key)
    }
    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        if let Some(old) = self.root.remove(key, 0) {
            self.len -= 1;
            Some(old)
        } else {
            None
        }
    }
    pub fn split_by_prefix(&mut self, prefix: &[u8]) -> Self {
        if let Some(splitted_root) = self.root.split_by_prefix(prefix, 0) {
            let mut splitted_root = Node::new(prefix, None, Some(splitted_root), None);
            splitted_root.try_merge_with_child(1);
            let splitted = Self::from(Node::new(b"", None, Some(splitted_root), None));
            self.len -= splitted.len();
            splitted
        } else {
            Self::new()
        }
    }
    pub fn clear(&mut self) {
        self.root = Node::root();
        self.len = 0;
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn nodes(&self) -> Nodes<V> {
        Nodes {
            nodes: self.root.iter(),
            label_lens: Vec::new(),
        }
    }
    pub fn nodes_mut(&mut self) -> NodesMut<V> {
        NodesMut {
            nodes: self.root.iter_mut(),
            label_lens: Vec::new(),
        }
    }
    pub fn into_nodes(self) -> IntoNodes<V> {
        IntoNodes {
            nodes: self.root.into_iter(),
            label_lens: Vec::new(),
        }
    }
}
impl<V> Default for PatriciaTree<V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<V> From<Node<V>> for PatriciaTree<V> {
    fn from(f: Node<V>) -> Self {
        let mut this = PatriciaTree { root: f, len: 0 };
        let count = this.nodes().filter(|n| n.1.value().is_some()).count();
        this.len = count;
        this
    }
}

#[derive(Debug)]
pub struct Nodes<'a, V: 'a> {
    nodes: node::Iter<'a, V>,
    label_lens: Vec<usize>,
}
impl<'a, V: 'a> Iterator for Nodes<'a, V> {
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.nodes.next() {
            self.label_lens.resize(level + 1, 0);
            self.label_lens[level] = node.label().len();

            let parent_key_len = self.label_lens.iter().take(level).sum();
            Some((parent_key_len, node))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct NodesMut<'a, V: 'a> {
    nodes: node::IterMut<'a, V>,
    label_lens: Vec<usize>,
}
impl<'a, V: 'a> Iterator for NodesMut<'a, V> {
    type Item = (usize, NodeMut<'a, V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.nodes.next() {
            self.label_lens.resize(level + 1, 0);
            self.label_lens[level] = node.label().len();

            let parent_key_len = self.label_lens.iter().take(level).sum();
            Some((parent_key_len, node))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct IntoNodes<V> {
    nodes: node::IntoIter<V>,
    label_lens: Vec<usize>,
}
impl<V> Iterator for IntoNodes<V> {
    type Item = (usize, Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.nodes.next() {
            self.label_lens.resize(level + 1, 0);
            self.label_lens[level] = node.label().len();

            let parent_key_len = self.label_lens.iter().take(level).sum();
            Some((parent_key_len, node))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut tree = PatriciaTree::new();
        assert_eq!(tree.insert("".as_bytes(), 1), None);
        assert_eq!(tree.insert("".as_bytes(), 2), Some(1));

        assert_eq!(tree.insert("foo".as_bytes(), 3), None);
        assert_eq!(tree.insert("foo".as_bytes(), 4), Some(3));

        assert_eq!(tree.insert("foobar".as_bytes(), 5), None);

        assert_eq!(tree.insert("bar".as_bytes(), 6), None);
        assert_eq!(tree.insert("baz".as_bytes(), 7), None);

        assert_eq!(tree.insert("bar".as_bytes(), 7), Some(6));
        assert_eq!(tree.insert("baz".as_bytes(), 8), Some(7));

        assert_eq!(tree.get("".as_bytes()), Some(&2));
        assert_eq!(tree.get("foo".as_bytes()), Some(&4));
        assert_eq!(tree.get("foobar".as_bytes()), Some(&5));
        assert_eq!(tree.get("bar".as_bytes()), Some(&7));
        assert_eq!(tree.get("baz".as_bytes()), Some(&8));
        assert_eq!(tree.get("qux".as_bytes()), None);

        let tree2 = tree.clone();
        assert_eq!(tree2.get("".as_bytes()), Some(&2));
        assert_eq!(tree2.get("foo".as_bytes()), Some(&4));
        assert_eq!(tree2.get("foobar".as_bytes()), Some(&5));
        assert_eq!(tree2.get("bar".as_bytes()), Some(&7));
        assert_eq!(tree2.get("baz".as_bytes()), Some(&8));

        assert_eq!(tree.remove("".as_bytes()), Some(2));
        assert_eq!(tree.remove("foo".as_bytes()), Some(4));
        assert_eq!(tree.remove("foobar".as_bytes()), Some(5));
        assert_eq!(tree.remove("bar".as_bytes()), Some(7));
        assert_eq!(tree.remove("baz".as_bytes()), Some(8));
        assert_eq!(tree.remove("qux".as_bytes()), None);

        assert_eq!(tree.get("".as_bytes()), None);
        assert_eq!(tree.get("foo".as_bytes()), None);
        assert_eq!(tree.get("foobar".as_bytes()), None);
        assert_eq!(tree.get("bar".as_bytes()), None);
        assert_eq!(tree.get("baz".as_bytes()), None);
        assert_eq!(tree.get("qux".as_bytes()), None);

        assert_eq!(tree2.get("".as_bytes()), Some(&2));
        assert_eq!(tree2.get("foo".as_bytes()), Some(&4));
        assert_eq!(tree2.get("foobar".as_bytes()), Some(&5));
        assert_eq!(tree2.get("bar".as_bytes()), Some(&7));
        assert_eq!(tree2.get("baz".as_bytes()), Some(&8));
    }
}
