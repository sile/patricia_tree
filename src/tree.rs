use crate::{
    node::{self, Node, NodeMut},
    Key,
};

#[derive(Debug, Clone)]
pub struct PatriciaTree<K, V> {
    root: Node<K, V>,
    len: usize,
}

impl<K: Key, V> PatriciaTree<K, V> {
    pub fn new() -> Self {
        PatriciaTree {
            root: Node::root(),
            len: 0,
        }
    }
    pub fn into_root(self) -> Node<K, V> {
        self.root
    }
    pub fn root(&self) -> &Node<K, V> {
        &self.root
    }
    pub fn insert<Q: AsRef<K>>(&mut self, key: Q, value: V) -> Option<V> {
        if let Some(old) = self.root.insert(key.as_ref().as_ref(), value) {
            Some(old)
        } else {
            self.len += 1;
            None
        }
    }
    // TODO
    // pub fn insert_str(&mut self, key: &str, value: V) -> Option<V> {
    //     if let Some(old) = self.root.insert_str(key, value) {
    //         Some(old)
    //     } else {
    //         self.len += 1;
    //         None
    //     }
    // }
    pub fn get<Q: AsRef<K>>(&self, key: Q) -> Option<&V> {
        self.root.get(key.as_ref().as_ref())
    }
    pub fn get_mut<Q: AsRef<K>>(&mut self, key: Q) -> Option<&mut V> {
        self.root.get_mut(key.as_ref().as_ref())
    }
    pub fn get_longest_common_prefix<'a>(&self, key: &'a [u8]) -> Option<(&'a [u8], &V)> {
        self.root
            .get_longest_common_prefix(key, 0)
            .map(|(n, v)| (&key[..n], v))
    }
    pub fn iter_prefix<'a, 'b>(&'a self, prefix: &'b [u8]) -> Option<(usize, Nodes<K, V>)> {
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
    pub fn iter_prefix_mut<'a, 'b>(
        &'a mut self,
        prefix: &'b [u8],
    ) -> Option<(usize, NodesMut<K, V>)> {
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
    pub(crate) fn common_prefixes<Q>(&self, key: Q) -> node::CommonPrefixesIter<K, Q, V>
    where
        Q: AsRef<K>,
    {
        self.root.common_prefixes(key)
    }
    pub fn remove<Q: AsRef<K>>(&mut self, key: Q) -> Option<V> {
        if let Some(old) = self.root.remove(key.as_ref().as_ref(), 0) {
            self.len -= 1;
            Some(old)
        } else {
            None
        }
    }
    pub fn split_by_prefix<Q: AsRef<K>>(&mut self, prefix: Q) -> Self {
        if let Some(splitted_root) = self.root.split_by_prefix(prefix.as_ref().as_ref(), 0) {
            let mut splitted_root =
                Node::new(prefix.as_ref().as_ref(), None, Some(splitted_root), None);
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
    pub fn nodes(&self) -> Nodes<K, V> {
        Nodes {
            nodes: self.root.iter(),
            label_lens: Vec::new(),
        }
    }
    pub fn nodes_mut(&mut self) -> NodesMut<K, V> {
        NodesMut {
            nodes: self.root.iter_mut(),
            label_lens: Vec::new(),
        }
    }
    pub fn into_nodes(self) -> IntoNodes<K, V> {
        IntoNodes {
            nodes: self.root.into_iter(),
            label_lens: Vec::new(),
        }
    }
}
impl<K: Key, V> Default for PatriciaTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K: Key, V> From<Node<K, V>> for PatriciaTree<K, V> {
    fn from(f: Node<K, V>) -> Self {
        let mut this = PatriciaTree { root: f, len: 0 };
        let count = this.nodes().filter(|n| n.1.value().is_some()).count();
        this.len = count;
        this
    }
}

#[derive(Debug)]
pub struct Nodes<'a, K, V: 'a> {
    nodes: node::Iter<'a, K, V>,
    label_lens: Vec<usize>,
}
impl<'a, K: Key, V: 'a> Iterator for Nodes<'a, K, V> {
    type Item = (usize, &'a Node<K, V>);
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
pub struct NodesMut<'a, K, V: 'a> {
    nodes: node::IterMut<'a, K, V>,
    label_lens: Vec<usize>,
}
impl<'a, K: Key, V: 'a> Iterator for NodesMut<'a, K, V> {
    type Item = (usize, NodeMut<'a, K, V>);
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
pub struct IntoNodes<K, V> {
    nodes: node::IntoIter<K, V>,
    label_lens: Vec<usize>,
}
impl<K: Key, V> Iterator for IntoNodes<K, V> {
    type Item = (usize, Node<K, V>);
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
        assert_eq!(tree.insert("", 1), None);
        assert_eq!(tree.insert("", 2), Some(1));

        assert_eq!(tree.insert("foo", 3), None);
        assert_eq!(tree.insert("foo", 4), Some(3));

        assert_eq!(tree.insert("foobar", 5), None);

        assert_eq!(tree.insert("bar", 6), None);
        assert_eq!(tree.insert("baz", 7), None);

        assert_eq!(tree.insert("bar", 7), Some(6));
        assert_eq!(tree.insert("baz", 8), Some(7));

        assert_eq!(tree.get(""), Some(&2));
        assert_eq!(tree.get("foo"), Some(&4));
        assert_eq!(tree.get("foobar"), Some(&5));
        assert_eq!(tree.get("bar"), Some(&7));
        assert_eq!(tree.get("baz"), Some(&8));
        assert_eq!(tree.get("qux"), None);

        let tree2 = tree.clone();
        assert_eq!(tree2.get(""), Some(&2));
        assert_eq!(tree2.get("foo"), Some(&4));
        assert_eq!(tree2.get("foobar"), Some(&5));
        assert_eq!(tree2.get("bar"), Some(&7));
        assert_eq!(tree2.get("baz"), Some(&8));

        assert_eq!(tree.remove(""), Some(2));
        assert_eq!(tree.remove("foo"), Some(4));
        assert_eq!(tree.remove("foobar"), Some(5));
        assert_eq!(tree.remove("bar"), Some(7));
        assert_eq!(tree.remove("baz"), Some(8));
        assert_eq!(tree.remove("qux"), None);

        assert_eq!(tree.get(""), None);
        assert_eq!(tree.get("foo"), None);
        assert_eq!(tree.get("foobar"), None);
        assert_eq!(tree.get("bar"), None);
        assert_eq!(tree.get("baz"), None);
        assert_eq!(tree.get("qux"), None);

        assert_eq!(tree2.get(""), Some(&2));
        assert_eq!(tree2.get("foo"), Some(&4));
        assert_eq!(tree2.get("foobar"), Some(&5));
        assert_eq!(tree2.get("bar"), Some(&7));
        assert_eq!(tree2.get("baz"), Some(&8));
    }
}
