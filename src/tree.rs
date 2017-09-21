use std::iter::{self, Peekable};
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::slice;
use libc;

#[derive(Debug)]
pub struct PatriciaTree<V> {
    root: Node<V>,
}
impl<V> PatriciaTree<V> {
    pub fn new() -> Self {
        PatriciaTree { root: Node::root() }
    }
    pub fn insert<K>(&mut self, key: K, value: V) -> Option<V>
    where
        K: Iterator<Item = u8>,
    {
        self.root.insert(key.peekable(), value)
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
                    println!("#### {}: {}", offset, child.ptr as usize);
                    ptr::write(ptr.offset(offset) as _, child.ptr);
                    offset += mem::size_of::<usize>() as isize;
                }
                if let Some(sibling) = sibling {
                    ptr::write(ptr.offset(offset) as _, sibling.ptr);
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
                println!("# {:?}, {:?}", self.value_offset(), self.child_offset());
                println!("# BEFORE: {:?}", self.flags());
                self.set_flags(Flags::CHILD_INITIALIZED, false);
                println!("# AFTER: {:?}", self.flags());
                let child = unsafe {
                    let ptr: *mut u8 = *(self.ptr.offset(offset) as *mut _);
                    println!("@ {}", ptr as usize);
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
                let sibling = unsafe { Node::from_ptr(self.ptr.offset(offset)) };
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
            println!("### {}: {}", offset, child.ptr as usize);
            unsafe { ptr::write(self.ptr.offset(offset) as _, child.ptr) };
        } else {
            let value = self.take_value();
            let sibling = self.take_sibling();
            let node = Node::new(self.key().iter().cloned(), value, Some(child), sibling);
            *self = node;
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
            } else if let Some(child) = self.take_child() {
                panic!()
            } else {
                let child = Node::new(key, Some(value), None, None);
                self.set_child(child);
                None
            }
        } else {
            panic!("{:?}", (self.key(), common_prefix))
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
    }
}
