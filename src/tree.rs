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

pub const FLAG_HAS_VALUE: u8 = 0x01;
pub const FLAG_HAS_CHILD: u8 = 0x02;
pub const FLAG_HAS_SIBLING: u8 = 0x04;

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
            let mut flags = 0;
            let mut block_size = 1 + 1 + key_len;
            if value.is_some() {
                flags |= FLAG_HAS_VALUE;
                block_size += mem::size_of::<V>();
            }
            if child.is_some() {
                flags |= FLAG_HAS_CHILD;
                block_size += mem::size_of::<usize>();
            }
            if sibling.is_some() {
                flags |= FLAG_HAS_SIBLING;
                block_size += mem::size_of::<usize>();
            }

            let ptr = unsafe { libc::malloc(block_size) } as *mut u8;
            assert_ne!(ptr, ptr::null_mut());

            unsafe {
                let mut offset = 0;
                ptr::write(ptr.offset(offset), flags);
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
    pub fn child(&self) -> Option<Node<V>> {
        self.child_offset()
            .map(|offset| unsafe { self.ptr.offset(offset) })
            .map(Node::from_ptr)
    }
    pub fn sibling(&self) -> Option<Node<V>> {
        self.sibling_offset()
            .map(|offset| unsafe { self.ptr.offset(offset) })
            .map(Node::from_ptr)
    }
    pub fn from_ptr(ptr: *mut u8) -> Self {
        Node {
            ptr,
            _value: PhantomData,
        }
    }

    pub fn flags(&self) -> u8 {
        unsafe { *self.ptr }
    }
    pub fn key_len(&self) -> u8 {
        unsafe { *self.ptr.offset(1) }
    }

    pub fn value_offset(&self) -> Option<isize> {
        if (self.flags() & FLAG_HAS_VALUE) != 0 {
            Some(2 + self.key_len() as isize)
        } else {
            None
        }
    }
    pub fn child_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if (flags & FLAG_HAS_CHILD) != 0 {
            let mut offset = 2 + self.key_len() as isize;
            if (flags & FLAG_HAS_VALUE) != 0 {
                offset += mem::size_of::<V>() as isize;
            }
            Some(offset)
        } else {
            None
        }
    }
    pub fn sibling_offset(&self) -> Option<isize> {
        let flags = self.flags();
        if (flags & FLAG_HAS_SIBLING) != 0 {
            let mut offset = 2 + self.key_len() as isize;
            if (flags & FLAG_HAS_VALUE) != 0 {
                offset += mem::size_of::<V>() as isize;
            }
            if (flags & FLAG_HAS_CHILD) != 0 {
                offset += mem::size_of::<usize>() as isize;
            }
            Some(offset)
        } else {
            None
        }
    }

    pub fn set_value(&mut self, value: V) -> Option<V> {
        if let Some(offset) = self.value_offset() {
            Some(unsafe {
                mem::replace(mem::transmute(self.ptr.offset(offset)), value)
            })
        } else {
            let node = Node::new(
                self.key().iter().cloned(),
                Some(value),
                self.child(),
                self.sibling(),
            );
            self.ptr = node.ptr;
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

        if common_prefix == node_key_len && key.peek().is_none() {
            self.set_value(value)
        } else {
            panic!("{:?}", (self.key(), common_prefix))
        }
    }
}
impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        unsafe { libc::free(self.ptr as *mut libc::c_void) }
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
    }
}
