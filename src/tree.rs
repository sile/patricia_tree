use std::iter::{self, Peekable};
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::slice;
use libc;

#[derive(Debug)]
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
    pub fn len(&self) -> usize {
        self.len
    }
}

bitflags! {
    struct Flags: u8 {
        const VALUE_ALLOCATED = 0b0000_0001;
        const VALUE_INITIALIZED = 0b0000_0010;
        const VALUE_EXISTS = Self::VALUE_ALLOCATED.bits
                           | Self::VALUE_INITIALIZED.bits;
        
        const CHILD_ALLOCATED = 0b0000_0100;
        const CHILD_INITIALIZED = 0b0000_1000;
        const CHILD_EXISTS = Self::CHILD_ALLOCATED.bits
                           | Self::CHILD_INITIALIZED.bits;

        const SIBLING_ALLOCATED = 0b0001_0000;
        const SIBLING_INITIALIZED = 0b0010_0000;
        const SIBLING_EXISTS = Self::SIBLING_ALLOCATED.bits
                             | Self::SIBLING_INITIALIZED.bits;
    }
}

// layout:
//   - flags:8
//   - key_len:8
//   - key:KEY_LEN
//   - value: Option<V>
//   - child: Option<usize>
//   - sibling: Option<usize>

// TODO: pack
#[derive(Debug)]
pub struct Node<V> {
    ptr: *mut u8,
    _value: PhantomData<V>,
}
impl<V> Node<V> {
    pub fn root() -> Self {
        Self::new(iter::empty(), None, None, None)
    }
    pub fn new<K>(mut key: K, value: Option<V>, child: Option<Self>, sibling: Option<Self>) -> Self
    where
        K: Iterator<Item = u8>,
    {
        let mut key_bytes = [0; 255];
        let mut key_len = 0;
        while let Some(b) = key.next() {
            key_bytes[key_len] = b;
            key_len += 1;
        }
        if key_len == key_bytes.len() {
            assert!(child.is_none());
            unimplemented!("TODO");
        } else {
            let mut flags = Flags::empty();
            let mut block_size = 1 + 1 + key_len;
            if value.is_some() {
                flags.insert(Flags::VALUE_EXISTS);
                block_size += mem::size_of::<V>();
            }
            if child.is_some() {
                flags.insert(Flags::CHILD_EXISTS);
                block_size += mem::size_of::<usize>();
            }
            if sibling.is_some() {
                flags.insert(Flags::SIBLING_EXISTS);
                block_size += mem::size_of::<usize>();
            }

            let ptr = unsafe { libc::malloc(block_size) } as *mut u8;
            assert_ne!(ptr, ptr::null_mut());

            unsafe {
                let mut offset = 0;
                ptr::write(ptr.offset(offset), flags.bits() as u8);
                offset += 1;

                ptr::write(ptr.offset(offset), key_len as u8);
                offset += 1;

                ptr::copy_nonoverlapping(key_bytes.as_ptr(), ptr.offset(offset), key_len);
                offset += key_len as isize;

                if let Some(value) = value {
                    ptr::write(ptr.offset(offset) as _, value);
                    offset += mem::size_of::<V>() as isize;
                }
                if let Some(child) = child {
                    ptr::write(ptr.offset(offset) as _, child.ptr);
                    mem::forget(child);
                    offset += mem::size_of::<usize>() as isize;
                }
                if let Some(sibling) = sibling {
                    ptr::write(ptr.offset(offset) as _, sibling.ptr);
                    mem::forget(sibling);
                }
            }

            Node {
                ptr,
                _value: PhantomData,
            }
        }
    }

    pub fn key(&self) -> &[u8] {
        unsafe {
            let key_len = *self.ptr.offset(1) as usize;
            slice::from_raw_parts(self.ptr.offset(2), key_len)
        }
    }
    fn from_ptr(ptr: *mut u8) -> Self {
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
    pub fn key_len(&self) -> u8 {
        unsafe { *self.ptr.offset(1) }
    }
    pub fn value_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if flags.contains(Flags::VALUE_ALLOCATED) {
            Some(2 + self.key_len() as isize)
        } else {
            None
        }
    }
    pub fn child_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if flags.contains(Flags::CHILD_ALLOCATED) {
            let mut offset = 2 + self.key_len() as isize;
            if flags.contains(Flags::VALUE_ALLOCATED) {
                offset += mem::size_of::<V>() as isize;
            }
            Some(offset)
        } else {
            None
        }
    }
    pub fn sibling_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if flags.contains(Flags::SIBLING_ALLOCATED) {
            let mut offset = 2 + self.key_len() as isize;
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
    pub fn take_child(&mut self) -> Option<Node<V>> {
        if let Some(offset) = self.child_offset() {
            if self.flags().contains(Flags::CHILD_EXISTS) {
                self.set_flags(Flags::CHILD_INITIALIZED, false);
                let child = unsafe {
                    let ptr: *mut u8 = *(self.ptr.offset(offset) as *mut _);
                    Node::from_ptr(ptr)
                };
                return Some(child);
            }
        }
        None
    }
    pub fn take_sibling(&mut self) -> Option<Node<V>> {
        if let Some(offset) = self.sibling_offset() {
            if self.flags().contains(Flags::SIBLING_EXISTS) {
                self.set_flags(Flags::SIBLING_INITIALIZED, false);
                let sibling = unsafe {
                    let ptr: *mut u8 = *(self.ptr.offset(offset) as *mut _);
                    Node::from_ptr(ptr)
                };
                return Some(sibling);
            }
        }
        None
    }
    pub fn take_value(&mut self) -> Option<V> {
        if let Some(offset) = self.value_offset() {
            if self.flags().contains(Flags::VALUE_EXISTS) {
                self.set_flags(Flags::VALUE_INITIALIZED, false);
                let value = unsafe {
                    mem::replace(
                        mem::transmute(self.ptr.offset(offset)),
                        mem::uninitialized(),
                    )
                };
                return Some(value);
            }
        }
        None
    }
    pub fn value(&self) -> Option<&V> {
        if let Some(offset) = self.value_offset() {
            if self.flags().contains(Flags::VALUE_EXISTS) {
                let value: *const V = unsafe { self.ptr.offset(offset) as _ };
                return Some(unsafe { mem::transmute(value) });
            }
        }
        None
    }
    pub fn child(&self) -> Option<&Node<V>> {
        if let Some(offset) = self.child_offset() {
            if self.flags().contains(Flags::CHILD_EXISTS) {
                let child: *const Node<V> = unsafe { self.ptr.offset(offset) as _ };
                return Some(unsafe { mem::transmute(child) });
            }
        }
        None
    }
    pub fn sibling(&self) -> Option<&Node<V>> {
        if let Some(offset) = self.sibling_offset() {
            if self.flags().contains(Flags::SIBLING_EXISTS) {
                let sibling: *const Node<V> = unsafe { self.ptr.offset(offset) as _ };
                return Some(unsafe { mem::transmute(sibling) });
            }
        }
        None
    }
    pub fn set_value(&mut self, value: V) -> Option<V> {
        let old = self.take_value();
        if let Some(offset) = self.value_offset() {
            self.set_flags(Flags::VALUE_INITIALIZED, true);
            unsafe { ptr::write(self.ptr.offset(offset) as _, value) };
            old
        } else {
            let child = self.take_child();
            let sibling = self.take_sibling();
            let node = Node::new(self.key().iter().cloned(), Some(value), child, sibling);
            *self = node;
            None
        }
    }
    pub fn set_child(&mut self, child: Self) {
        let _ = self.take_child();
        if let Some(offset) = self.child_offset() {
            self.set_flags(Flags::CHILD_INITIALIZED, true);
            unsafe { ptr::write(self.ptr.offset(offset) as _, child.ptr) };
            mem::forget(child);
        } else {
            let value = self.take_value();
            let sibling = self.take_sibling();
            let node = Node::new(self.key().iter().cloned(), value, Some(child), sibling);
            *self = node;
        }
    }
    pub fn set_sibling(&mut self, sibling: Self) {
        let _ = self.take_sibling();
        if let Some(offset) = self.sibling_offset() {
            self.set_flags(Flags::SIBLING_INITIALIZED, true);
            unsafe { ptr::write(self.ptr.offset(offset) as _, sibling.ptr) };
            mem::forget(sibling);
        } else {
            let value = self.take_value();
            let child = self.take_child();
            let node = Node::new(self.key().iter().cloned(), value, child, Some(sibling));
            *self = node;
        }
    }
    fn split_at(&mut self, position: usize) -> Self {
        debug_assert!(position < self.key_len() as usize);
        let value = self.take_value();
        let child = self.take_child();
        let sibling = self.take_sibling();

        let parent = Node::new(
            self.key().iter().take(position).cloned(),
            None,
            None,
            sibling,
        );
        let child = Node::new(
            self.key().iter().skip(position).cloned(),
            value,
            child,
            None,
        );
        *self = parent;
        child
    }
    pub fn get<K>(&self, mut key: Peekable<K>) -> Option<&V>
    where
        K: Iterator<Item = u8>,
    {
        // TODO: 共通化
        let mut common_prefix = 0;
        let node_key_len;
        {
            let node_key = self.key();
            node_key_len = node_key.len();
            while let Some(b) = key.peek().cloned() {
                if common_prefix == node_key.len() {
                    break;
                }
                if node_key[common_prefix] != b {
                    break;
                }
                common_prefix += 1;
                key.next();
            }
        }

        if common_prefix == node_key_len {
            if key.peek().is_none() {
                self.value()
            } else {
                self.child().and_then(|child| child.get(key))
            }
        } else if common_prefix == 0 {
            self.sibling().and_then(|sibling| sibling.get(key))
        } else {
            None
        }
    }
    pub fn remove<K>(&mut self, mut key: Peekable<K>) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        let mut common_prefix = 0;
        let node_key_len;
        {
            let node_key = self.key();
            node_key_len = node_key.len();
            while let Some(b) = key.peek().cloned() {
                if common_prefix == node_key.len() {
                    break;
                }
                if node_key[common_prefix] != b {
                    break;
                }
                common_prefix += 1;
                key.next();
            }
        }

        if common_prefix == node_key_len {
            if key.peek().is_none() {
                // TODO: 不要となったノードの削除・回収
                self.take_value()
            } else if let Some(mut child) = self.take_child() {
                let old = child.remove(key);
                self.set_child(child);
                old
            } else {
                None
            }
        } else if common_prefix == 0 {
            if let Some(mut sibling) = self.take_sibling() {
                let old = sibling.remove(key);
                self.set_sibling(sibling);
                old
            } else {
                None
            }
        } else {
            None
        }
    }
    pub fn insert<K>(&mut self, mut key: Peekable<K>, value: V) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        let mut common_prefix = 0;
        let node_key_len;
        {
            let node_key = self.key();
            node_key_len = node_key.len();
            while let Some(b) = key.peek().cloned() {
                if common_prefix == node_key.len() {
                    break;
                }
                if node_key[common_prefix] != b {
                    break;
                }
                common_prefix += 1;
                key.next();
            }
        }

        if common_prefix == node_key_len {
            if key.peek().is_none() {
                self.set_value(value)
            } else if let Some(mut child) = self.take_child() {
                let old = child.insert(key, value);
                self.set_child(child);
                old
            } else {
                let child = Node::new(key, Some(value), None, None);
                self.set_child(child);
                None
            }
        } else if common_prefix == 0 {
            // TODO: sort by key
            if let Some(mut sibling) = self.take_sibling() {
                let old = sibling.insert(key, value);
                self.set_sibling(sibling);
                old
            } else {
                let sibling = Node::new(key, Some(value), None, None);
                self.set_sibling(sibling);
                None
            }
        } else {
            let mut child = self.split_at(common_prefix);
            child.insert(key, value);
            self.set_child(child);
            None
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
    }
}
