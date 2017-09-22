use node::Node;

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
    pub fn root(&self) -> &Node<V> {
        &self.root
    }
    pub fn insert<K>(&mut self, key: K, value: V) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        if let Some(old) = self.root.insert(key.peekable(), value) {
            Some(old)
        } else {
            self.len += 1;
            None
        }
    }
    pub fn get<K>(&self, key: K) -> Option<&V>
    where
        K: Iterator<Item = u8>,
    {
        self.root.get(key.peekable())
    }
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut V>
    where
        K: Iterator<Item = u8>,
    {
        self.root.get_mut(key.peekable())
    }
    pub fn remove<K>(&mut self, key: K) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        if let Some(old) = self.root.remove(key.peekable()) {
            self.len -= 1;
            Some(old)
        } else {
            None
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
            stack: vec![(0, self.root())],
            key_len: 0,
        }
    }
}
impl<V> Default for PatriciaTree<V> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Nodes<'a, V: 'a> {
    stack: Vec<(usize, &'a Node<V>)>,
    key_len: usize,
}
impl<'a, V: 'a> Iterator for Nodes<'a, V> {
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((key_len, node)) = self.stack.pop() {
            self.key_len = key_len;
            if let Some(sibling) = node.sibling() {
                self.stack.push((self.key_len, sibling));
            }

            self.key_len += node.key().len();
            if let Some(child) = node.child() {
                self.stack.push((self.key_len, child));
            }

            Some((key_len, node))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn it_works() {
        let mut tree = PatriciaTree::new();
        assert_eq!(tree.insert("".bytes(), 1), None);
        assert_eq!(tree.insert("".bytes(), 2), Some(1));

        assert_eq!(tree.insert("foo".bytes(), 3), None);
        assert_eq!(tree.insert("foo".bytes(), 4), Some(3));

        assert_eq!(tree.insert("foobar".bytes(), 5), None);

        assert_eq!(tree.insert("bar".bytes(), 6), None);
        assert_eq!(tree.insert("baz".bytes(), 7), None);

        assert_eq!(tree.insert("bar".bytes(), 7), Some(6));
        assert_eq!(tree.insert("baz".bytes(), 8), Some(7));

        assert_eq!(tree.get("".bytes()), Some(&2));
        assert_eq!(tree.get("foo".bytes()), Some(&4));
        assert_eq!(tree.get("foobar".bytes()), Some(&5));
        assert_eq!(tree.get("bar".bytes()), Some(&7));
        assert_eq!(tree.get("baz".bytes()), Some(&8));
        assert_eq!(tree.get("qux".bytes()), None);

        let tree2 = tree.clone();
        assert_eq!(tree2.get("".bytes()), Some(&2));
        assert_eq!(tree2.get("foo".bytes()), Some(&4));
        assert_eq!(tree2.get("foobar".bytes()), Some(&5));
        assert_eq!(tree2.get("bar".bytes()), Some(&7));
        assert_eq!(tree2.get("baz".bytes()), Some(&8));

        assert_eq!(tree.remove("".bytes()), Some(2));
        assert_eq!(tree.remove("foo".bytes()), Some(4));
        assert_eq!(tree.remove("foobar".bytes()), Some(5));
        assert_eq!(tree.remove("bar".bytes()), Some(7));
        assert_eq!(tree.remove("baz".bytes()), Some(8));
        assert_eq!(tree.remove("qux".bytes()), None);

        assert_eq!(tree.get("".bytes()), None);
        assert_eq!(tree.get("foo".bytes()), None);
        assert_eq!(tree.get("foobar".bytes()), None);
        assert_eq!(tree.get("bar".bytes()), None);
        assert_eq!(tree.get("baz".bytes()), None);
        assert_eq!(tree.get("qux".bytes()), None);

        assert_eq!(tree2.get("".bytes()), Some(&2));
        assert_eq!(tree2.get("foo".bytes()), Some(&4));
        assert_eq!(tree2.get("foobar".bytes()), Some(&5));
        assert_eq!(tree2.get("bar".bytes()), Some(&7));
        assert_eq!(tree2.get("baz".bytes()), Some(&8));
    }
}
