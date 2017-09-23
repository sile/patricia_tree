use std::iter::{self, Peekable};
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::slice;
use libc;

macro_rules! assert_some {
    ($expr:expr) => {
        if let Some(value) = $expr {
            value
        } else {
            panic!("`{}` must be `Some(..)`", stringify!($expr));
        }
    }
}

bitflags! {
    struct Flags: u8 {
        const VALUE_ALLOCATED = 0b0000_0001;
        const VALUE_INITIALIZED = 0b0000_0010;
        
        const CHILD_ALLOCATED = 0b0000_0100;
        const CHILD_INITIALIZED = 0b0000_1000;

        const SIBLING_ALLOCATED = 0b0001_0000;
        const SIBLING_INITIALIZED = 0b0010_0000;
    }
}

const FLAGS_OFFSET: isize = 0;
const LABEL_LEN_OFFSET: isize = 1;
const LABEL_OFFSET: isize = 2;

const MAX_LABEL_LEN: usize = 255;

/// A node which represents a subtree of a patricia tree.
///
/// Note that this is a low level building block.
/// Usually it is recommended to use more high level data structures (e.g., `PatriciaTree`).
#[derive(Debug)]
pub struct Node<V> {
    // layout;
    //   - flags: u8
    //   - label_len: u8
    //   - label: [u8; LABEL_LEN]
    //   - value: Option<V>
    //   - child: Option<Node<V>>
    //   - sibling: Option<Node<V>>
    ptr: *mut u8,

    _value: PhantomData<V>,
}
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
        Self::new(iter::empty(), None, None, None)
    }

    /// Makes a new node.
    ///
    /// # Examples
    ///
    /// ```
    /// use patricia_tree::node::Node;
    ///
    /// let node0 = Node::new("foo".bytes(), Some(3), None, None);
    /// assert_eq!(node0.label(), b"foo");
    /// assert_eq!(node0.value(), Some(&3));
    /// assert_eq!(node0.child().map(|n| n.label()), None);
    /// assert_eq!(node0.sibling().map(|n| n.label()), None);
    ///
    /// let node1 = Node::new("bar".bytes(), None, None, Some(node0));
    /// assert_eq!(node1.label(), b"bar");
    /// assert_eq!(node1.value(), None);
    /// assert_eq!(node1.child().map(|n| n.label()), None);
    /// assert_eq!(node1.sibling().map(|n| n.label()), Some(&b"foo"[..]));
    ///
    /// // If the length of a label name is longer than 255, it will be splitted to two nodes.
    /// let node2 = Node::new("a".bytes().cycle().take(256), Some(4), Some(node1), None);
    /// assert_eq!(node2.label(), "a".bytes().cycle().take(255).collect::<Vec<_>>().as_slice());
    /// assert_eq!(node2.value(), None);
    /// assert_eq!(node2.child().map(|n| n.label()), Some(&b"a"[..]));
    /// assert_eq!(node2.sibling().map(|n| n.label()), None);
    ///
    /// assert_eq!(node2.child().unwrap().value(), Some(&4));
    /// assert_eq!(node2.child().unwrap().child().unwrap().label(), b"bar");
    /// ```
    pub fn new<L>(label: L, value: Option<V>, child: Option<Self>, sibling: Option<Self>) -> Self
    where
        L: Iterator<Item = u8>,
    {
        Self::new_with_peekable(label.peekable(), value, child, sibling)
    }

    /// Returns the label of this node.
    pub fn label(&self) -> &[u8] {
        unsafe {
            let label_len = *self.ptr.offset(LABEL_LEN_OFFSET) as usize;
            slice::from_raw_parts(self.ptr.offset(LABEL_OFFSET), label_len)
        }
    }

    /// Returns the reference to the value of this node.
    pub fn value(&self) -> Option<&V> {
        if let Some(offset) = self.value_offset() {
            if self.flags().contains(Flags::VALUE_INITIALIZED) {
                unsafe {
                    let value = self.ptr.offset(offset) as *const V;
                    return Some(&*value);
                }
            }
        }
        None
    }

    /// Returns the mutable reference to the value of this node.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        if let Some(offset) = self.value_offset() {
            if self.flags().contains(Flags::VALUE_INITIALIZED) {
                unsafe {
                    let value = self.ptr.offset(offset) as *mut V;
                    return Some(&mut *value);
                }
            }
        }
        None
    }

    /// Returns the reference to the child of this node.
    pub fn child(&self) -> Option<&Self> {
        if let Some(offset) = self.child_offset() {
            if self.flags().contains(Flags::CHILD_INITIALIZED) {
                unsafe {
                    let child = self.ptr.offset(offset) as *const Self;
                    return Some(&*child);
                }
            }
        }
        None
    }

    /// Returns the mutable reference to the child of this node.
    pub fn child_mut(&mut self) -> Option<&mut Self> {
        if let Some(offset) = self.child_offset() {
            if self.flags().contains(Flags::CHILD_INITIALIZED) {
                unsafe {
                    let child = self.ptr.offset(offset) as *mut Self;
                    return Some(&mut *child);
                }
            }
        }
        None
    }

    /// Returns the reference to the sibling of this node.
    pub fn sibling(&self) -> Option<&Self> {
        if let Some(offset) = self.sibling_offset() {
            if self.flags().contains(Flags::SIBLING_INITIALIZED) {
                unsafe {
                    let sibling = self.ptr.offset(offset) as *const Self;
                    return Some(&*sibling);
                }
            }
        }
        None
    }

    /// Returns the mutable reference to the sibling of this node.
    pub fn sibling_mut(&mut self) -> Option<&mut Self> {
        if let Some(offset) = self.sibling_offset() {
            if self.flags().contains(Flags::SIBLING_INITIALIZED) {
                unsafe {
                    let sibling = self.ptr.offset(offset) as *mut Self;
                    return Some(&mut *sibling);
                }
            }
        }
        None
    }

    /// Takes the value out of this node.
    pub fn take_value(&mut self) -> Option<V> {
        if let Some(offset) = self.value_offset() {
            if self.flags().contains(Flags::VALUE_INITIALIZED) {
                self.set_flags(Flags::VALUE_INITIALIZED, false);
                unsafe {
                    let value = self.ptr.offset(offset) as *const V;
                    return Some(mem::transmute_copy(&*value));
                }
            }
        }
        None
    }

    /// Takes the child out of this node.
    pub fn take_child(&mut self) -> Option<Self> {
        if let Some(offset) = self.child_offset() {
            if self.flags().contains(Flags::CHILD_INITIALIZED) {
                self.set_flags(Flags::CHILD_INITIALIZED, false);
                unsafe {
                    let child = self.ptr.offset(offset) as *mut Self;
                    return Some(mem::transmute_copy(&*child));
                }
            }
        }
        None
    }

    /// Takes the sibling out of this node.
    pub fn take_sibling(&mut self) -> Option<Self> {
        if let Some(offset) = self.sibling_offset() {
            if self.flags().contains(Flags::SIBLING_INITIALIZED) {
                self.set_flags(Flags::SIBLING_INITIALIZED, false);
                unsafe {
                    let sibling = self.ptr.offset(offset) as *mut Self;
                    return Some(mem::transmute_copy(&*sibling));
                }
            }
        }
        None
    }

    /// Sets the value of this node.
    pub fn set_value(&mut self, value: V) {
        self.take_value();
        if let Some(offset) = self.value_offset() {
            self.set_flags(Flags::VALUE_INITIALIZED, true);
            unsafe { ptr::write(self.ptr.offset(offset) as _, value) };
        } else {
            let child = self.take_child();
            let sibling = self.take_sibling();
            let node = Node::new(self.label().iter().cloned(), Some(value), child, sibling);
            *self = node;
        }
    }

    /// Sets the child of this node.
    pub fn set_child(&mut self, child: Self) {
        self.take_child();
        if let Some(offset) = self.child_offset() {
            self.set_flags(Flags::CHILD_INITIALIZED, true);
            unsafe { ptr::write(self.ptr.offset(offset) as _, child) };
        } else {
            let value = self.take_value();
            let sibling = self.take_sibling();
            let node = Node::new(self.label().iter().cloned(), value, Some(child), sibling);
            *self = node;
        }
    }

    /// Sets the sibling of this node.
    pub fn set_sibling(&mut self, sibling: Self) {
        self.take_sibling();
        if let Some(offset) = self.sibling_offset() {
            self.set_flags(Flags::SIBLING_INITIALIZED, true);
            unsafe { ptr::write(self.ptr.offset(offset) as _, sibling) };
        } else {
            let value = self.take_value();
            let child = self.take_child();
            let node = Node::new(self.label().iter().cloned(), value, child, Some(sibling));
            *self = node;
        }
    }
    // TODO: iter, IntoIterator, FromIterator

    fn skip_common_prefix<K>(&self, key: &mut Peekable<K>) -> Option<usize>
    where
        K: Iterator<Item = u8>,
    {
        self.label().iter().position(|b| {
            let matched = Some(b) == key.peek();
            if matched {
                key.next();
            }
            !matched
        })
    }
    // TODO: s/Peekable<K>/&[u8]/
    pub(crate) fn get<K>(&self, mut key: Peekable<K>) -> Option<&V>
    where
        K: Iterator<Item = u8>,
    {
        if self.label().get(0).map_or(false, |b| Some(b) > key.peek()) {
            None
        } else if let Some(common_prefix_len) = self.skip_common_prefix(&mut key) {
            if common_prefix_len == 0 {
                self.sibling().and_then(|sibling| sibling.get(key))
            } else {
                None
            }
        } else if key.peek().is_none() {
            self.value()
        } else {
            self.child().and_then(|child| child.get(key))
        }
    }
    pub(crate) fn get_mut<K>(&mut self, mut key: Peekable<K>) -> Option<&mut V>
    where
        K: Iterator<Item = u8>,
    {
        if self.label().get(0).map_or(false, |b| Some(b) > key.peek()) {
            None
        } else if let Some(common_prefix_len) = self.skip_common_prefix(&mut key) {
            if common_prefix_len == 0 {
                self.sibling_mut().and_then(|sibling| sibling.get_mut(key))
            } else {
                None
            }
        } else if key.peek().is_none() {
            self.value_mut()
        } else {
            self.child_mut().and_then(|child| child.get_mut(key))
        }
    }
    pub(crate) fn remove<K>(&mut self, mut key: Peekable<K>) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        if self.label().get(0).map_or(false, |b| Some(b) > key.peek()) {
            None
        } else if let Some(common_prefix_len) = self.skip_common_prefix(&mut key) {
            if common_prefix_len == 0 {
                let result = self.sibling_mut().and_then(|sibling| sibling.remove(key));
                if result.is_some() {
                    self.try_reclaim_sibling();
                }
                result
            } else {
                None
            }
        } else if key.peek().is_none() {
            self.take_value()
        } else {
            let result = self.child_mut().and_then(|child| child.remove(key));
            if result.is_some() {
                self.try_reclaim_child();
            }
            result
        }
    }
    pub(crate) fn insert<K>(&mut self, mut key: Peekable<K>, value: V) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        if self.label().get(0).map_or(false, |b| Some(b) > key.peek()) {
            let this = Node {
                ptr: self.ptr,
                _value: PhantomData,
            };
            let node = Node::new_with_peekable(key, Some(value), None, Some(this));
            self.ptr = node.ptr;
            mem::forget(node);
            None
        } else if let Some(common_prefix_len) = self.skip_common_prefix(&mut key) {
            if common_prefix_len == 0 {
                if let Some(sibling) = self.sibling_mut() {
                    return sibling.insert(key, value);
                }
                let sibling = Node::new_with_peekable(key, Some(value), None, None);
                self.set_sibling(sibling);
                None
            } else {
                self.split_at(common_prefix_len);
                assert_some!(self.child_mut()).insert(key, value);
                None
            }
        } else if key.peek().is_none() {
            let old = self.take_value();
            self.set_value(value);
            old
        } else {
            if let Some(child) = self.child_mut() {
                return child.insert(key, value);
            }
            let child = Node::new_with_peekable(key, Some(value), None, None);
            self.set_child(child);
            None
        }
    }

    fn new_with_peekable<K>(
        mut label: Peekable<K>,
        mut value: Option<V>,
        mut child: Option<Self>,
        sibling: Option<Self>,
    ) -> Self
    where
        K: Iterator<Item = u8>,
    {
        let mut label_bytes = [0; MAX_LABEL_LEN];
        let mut label_len = 0;
        while let Some(&b) = label.peek() {
            label_bytes[label_len] = b;
            label_len += 1;
            label.next();
            if label_len == label_bytes.len() {
                break;
            }
        }
        if label.peek().is_some() {
            child = Some(Self::new_with_peekable(label, value, child, None));
            value = None;
        }

        let mut flags = Flags::empty();
        let mut block_size = LABEL_OFFSET as usize + label_len;
        if value.is_some() {
            flags.insert(Flags::VALUE_ALLOCATED | Flags::VALUE_INITIALIZED);
            block_size += mem::size_of::<V>();
        }
        if child.is_some() {
            flags.insert(Flags::CHILD_ALLOCATED | Flags::CHILD_INITIALIZED);
            block_size += mem::size_of::<Self>();
        }
        if sibling.is_some() {
            flags.insert(Flags::SIBLING_ALLOCATED | Flags::SIBLING_INITIALIZED);
            block_size += mem::size_of::<Self>();
        }
        let ptr = unsafe { libc::malloc(block_size) } as *mut u8;
        assert_ne!(ptr, ptr::null_mut());

        unsafe {
            ptr::write(ptr.offset(FLAGS_OFFSET), flags.bits() as u8);
            ptr::write(ptr.offset(LABEL_LEN_OFFSET), label_len as u8);
            ptr::copy_nonoverlapping(label_bytes.as_ptr(), ptr.offset(LABEL_OFFSET), label_len);

            let mut offset = LABEL_OFFSET + label_len as isize;
            if let Some(value) = value {
                ptr::write(ptr.offset(offset) as _, value);
                offset += mem::size_of::<V>() as isize;
            }
            if let Some(child) = child {
                ptr::write(ptr.offset(offset) as _, child);
                offset += mem::size_of::<Self>() as isize;
            }
            if let Some(sibling) = sibling {
                ptr::write(ptr.offset(offset) as _, sibling);
            }
        }
        Node {
            ptr,
            _value: PhantomData,
        }
    }
    fn flags(&self) -> Flags {
        Flags::from_bits_truncate(unsafe { *self.ptr })
    }
    fn set_flags(&mut self, other: Flags, value: bool) {
        let mut flags = self.flags();
        flags.set(other, value);
        unsafe { ptr::write(self.ptr, flags.bits() as u8) };
    }
    fn label_len(&self) -> usize {
        unsafe { *self.ptr.offset(LABEL_LEN_OFFSET) as usize }
    }
    fn value_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if flags.contains(Flags::VALUE_ALLOCATED) {
            Some(LABEL_OFFSET + self.label_len() as isize)
        } else {
            None
        }
    }
    fn child_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if flags.contains(Flags::CHILD_ALLOCATED) {
            let mut offset = LABEL_OFFSET + self.label_len() as isize;
            if flags.contains(Flags::VALUE_ALLOCATED) {
                offset += mem::size_of::<V>() as isize;
            }
            Some(offset)
        } else {
            None
        }
    }
    fn sibling_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if flags.contains(Flags::SIBLING_ALLOCATED) {
            let mut offset = LABEL_OFFSET + self.label_len() as isize;
            if flags.contains(Flags::VALUE_ALLOCATED) {
                offset += mem::size_of::<V>() as isize;
            }
            if flags.contains(Flags::CHILD_ALLOCATED) {
                offset += mem::size_of::<usize>() as isize;
            }
            Some(offset)
        } else {
            None
        }
    }
    fn split_at(&mut self, position: usize) {
        debug_assert!(position < self.label_len());
        let value = self.take_value();
        let child = self.take_child();
        let sibling = self.take_sibling();

        let child = Node::new(
            self.label().iter().skip(position).cloned(),
            value,
            child,
            None,
        );
        let parent = Node::new(
            self.label().iter().take(position).cloned(),
            None,
            Some(child),
            sibling,
        );
        *self = parent;
    }
    fn try_reclaim_sibling(&mut self) {
        let flags = assert_some!(self.sibling()).flags();
        if flags.intersects(Flags::VALUE_INITIALIZED | Flags::CHILD_INITIALIZED) {
            return;
        }
        if let Some(sibling) = self.take_sibling().and_then(|mut n| n.take_sibling()) {
            self.set_sibling(sibling);
        }
    }
    fn try_reclaim_child(&mut self) {
        let flags = assert_some!(self.child()).flags();
        if !flags.intersects(Flags::VALUE_INITIALIZED | Flags::CHILD_INITIALIZED) {
            if let Some(child) = self.take_child().and_then(|mut n| n.take_sibling()) {
                self.set_child(child);
            } else {
                return;
            }
        }

        let flags = assert_some!(self.child()).flags();
        if !self.flags().contains(Flags::VALUE_INITIALIZED) &&
            !flags.contains(Flags::SIBLING_INITIALIZED) &&
            (self.label_len() + assert_some!(self.child()).label_len()) <= MAX_LABEL_LEN
        {
            let mut child = assert_some!(self.take_child());
            let sibling = self.take_sibling();
            let value = child.take_value();
            let grandchild = child.take_child();
            let node = Self::new(
                self.label().iter().chain(child.label().iter()).cloned(),
                value,
                grandchild,
                sibling,
            );
            *self = node;
        }
    }
}
impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        unsafe {
            let _ = self.take_value();
            let _ = self.take_child();
            let _ = self.take_sibling();
            libc::free(self.ptr as *mut libc::c_void)
        }
    }
}
impl<V: Clone> Clone for Node<V> {
    fn clone(&self) -> Self {
        let label = self.label();
        let value = self.value().cloned();
        let child = self.child().cloned();
        let sibling = self.sibling().cloned();
        Node::new(label.iter().cloned(), value, child, sibling)
    }
}
