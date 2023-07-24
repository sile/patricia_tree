use crate::node::{Flags, Node};
use crate::{BorrowedBytes, GenericPatriciaMap, GenericPatriciaSet};
use serde::de::{Error, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::borrow::{Borrow, Cow};
use std::marker::PhantomData;

impl<T> Serialize for GenericPatriciaSet<T> {
    /// In order to serialize a [PatriciaSet], make sure you installed the crate
    /// with the feature `serde`.
    ///
    /// For example, in your `Cargo.toml`:
    /// ```toml
    /// [dependencies]
    /// patricia_tree = { version = "*", features = ["serde"] }
    /// ```
    ///
    /// Read more about serialization / deserialization at the [serde] crate.
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_node().serialize(serializer)
    }
}

impl<K, V: Serialize> Serialize for GenericPatriciaMap<K, V> {
    /// In order to serialize a [PatriciaMap], make sure you installed the crate
    /// with the feature `serde`.
    ///
    /// For example, in your `Cargo.toml`:
    /// ```toml
    /// [dependencies]
    /// patricia_tree = { version = "*", features = ["serde"] }
    /// ```
    ///
    /// Read more about serialization / deserialization at the [serde] crate.
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_node().serialize(serializer)
    }
}

impl<T: Serialize> Serialize for Node<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut tree_bytes = Vec::new();
        let mut values = Vec::new();
        let mut stack = vec![(0u16, self)];
        while let Some((level, node)) = stack.pop() {
            tree_bytes.push(node.flags().bits());
            tree_bytes.push(node.label().len() as u8);
            tree_bytes.push((level >> 8) as u8);
            tree_bytes.push(level as u8);
            tree_bytes.extend(node.label());
            if let Some(value) = node.value() {
                values.push(value);
            }
            if let Some(sibling) = node.sibling() {
                stack.push((level, sibling));
            }
            if let Some(child) = node.child() {
                stack.push((level + 1, child));
            }
        }

        (Bytes(Cow::Owned(tree_bytes)), values).serialize(serializer)
    }
}

impl<'de, T: crate::Bytes> Deserialize<'de> for GenericPatriciaSet<T> {
    /// In order to deserialize a [PatriciaSet], make sure you installed the crate
    /// with the feature `serde`.
    ///
    /// For example, in your `Cargo.toml`:
    /// ```toml
    /// [dependencies]
    /// patricia_tree = { version = "*", features = ["serde"] }
    /// ```
    ///
    /// Read more about serialization / deserialization at the [serde] crate.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        KeyAndNode::<T, ()>::deserialize(deserializer)
            .map(|x| GenericPatriciaSet::from_node(x.node))
    }
}

impl<'de, K: crate::Bytes, V: Deserialize<'de>> Deserialize<'de> for GenericPatriciaMap<K, V> {
    /// In order to serialize a [PatriciaMap], make sure you installed the crate
    /// with the feature `serde`.
    ///
    /// For example, in your `Cargo.toml`:
    /// ```toml
    /// [dependencies]
    /// patricia_tree = { version = "*", features = ["serde"] }
    /// ```
    ///
    /// Read more about serialization / deserialization at the [serde] crate.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        KeyAndNode::<K, V>::deserialize(deserializer).map(|x| GenericPatriciaMap::from_node(x.node))
    }
}

#[derive(Debug)]
struct KeyAndNode<K, V> {
    node: Node<V>,
    _key: PhantomData<K>,
}

impl<'de, K: crate::Bytes, V: Deserialize<'de>> Deserialize<'de> for KeyAndNode<K, V> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (tree_bytes, mut values): (Bytes<'de>, Vec<V>) =
            Deserialize::deserialize(deserializer)?;
        values.reverse();
        let mut tree_bytes = tree_bytes.0.as_ref();

        let mut stack = Vec::new();
        while !tree_bytes.is_empty() {
            if tree_bytes.len() < 4 {
                return Err(D::Error::custom("unexpected EOS"));
            }
            let flags = Flags::from_bits_truncate(tree_bytes[0]);
            let label_len = usize::from(tree_bytes[1]);
            let level = (u16::from(tree_bytes[2]) << 8) | u16::from(tree_bytes[3]);
            tree_bytes = &tree_bytes[4..];

            if tree_bytes.len() < label_len {
                return Err(D::Error::custom("unexpected EOS"));
            }
            let mut node = Node::<V>::new_for_decoding(flags, label_len as u8);
            node.label_mut().copy_from_slice(&tree_bytes[..label_len]);
            if !K::Borrowed::is_valid_bytes(node.label()) {
                return Err(D::Error::custom(&format!(
                    "malformed label bytes: {:?}",
                    node.label()
                )));
            }
            tree_bytes = &tree_bytes[label_len..];

            if flags.contains(Flags::VALUE_INITIALIZED) {
                let value = values
                    .pop()
                    .ok_or_else(|| D::Error::custom("too few values"))?;
                node.set_value(value);
            }

            stack.push((level, node));
            while let Some((level, node)) = stack.pop() {
                let flags = node.flags();
                let has_child_or_sibling = (flags.contains(Flags::CHILD_ALLOCATED)
                    && !flags.contains(Flags::CHILD_INITIALIZED))
                    || (flags.contains(Flags::SIBLING_ALLOCATED)
                        && !flags.contains(Flags::SIBLING_INITIALIZED));
                if has_child_or_sibling {
                    stack.push((level, node));
                    break;
                }

                if let Some((last_level, last_node)) = stack.last_mut() {
                    if level == *last_level {
                        last_node.set_sibling(node);
                    } else if level == *last_level + 1 {
                        last_node.set_child(node);
                    } else {
                        return Err(D::Error::custom("invalid data"));
                    }
                } else if level == 0 {
                    return Ok(KeyAndNode {
                        node,
                        _key: PhantomData,
                    });
                } else {
                    return Err(D::Error::custom("invalid data"));
                }
            }
        }

        Err(D::Error::custom("invalid data"))
    }
}

struct Bytes<'a>(Cow<'a, [u8]>);

impl<'a> Serialize for Bytes<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self.0.borrow())
    }
}

impl<'de> Deserialize<'de> for Bytes<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(BytesVisitor)
    }
}

struct BytesVisitor;

impl<'de> Visitor<'de> for BytesVisitor {
    type Value = Bytes<'de>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a byte string")
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(Bytes(Cow::Borrowed(v)))
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(Bytes(Cow::Owned(v.to_owned())))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut bytes = Vec::new();
        while let Some(byte) = seq.next_element()? {
            bytes.push(byte);
        }
        Ok(Bytes(Cow::Owned(bytes)))
    }
}

#[cfg(test)]
mod tests {
    use crate::PatriciaMap;

    #[test]
    fn serde_works() {
        let mut input = vec![
            (Vec::from("foo"), 1u32),
            ("bar".into(), 2),
            ("baz".into(), 3),
        ];
        input.sort();

        let map: PatriciaMap<u32> = input.iter().cloned().collect();
        let serialized = serde_json::to_vec(&map).unwrap();
        let map: PatriciaMap<u32> = serde_json::from_slice(serialized.as_slice()).unwrap();

        assert_eq!(map.len(), 3);
        assert_eq!(map.into_iter().collect::<Vec<_>>(), input);
    }

    #[test]
    fn large_serde_works() {
        let mut input = (0..10000u32)
            .map(|i| (i.to_string().into_bytes(), i))
            .collect::<Vec<_>>();
        input.sort();

        let map: PatriciaMap<u32> = input.iter().cloned().collect();
        let serialized = serde_json::to_vec(&map).unwrap();
        let map: PatriciaMap<u32> = serde_json::from_slice(serialized.as_slice()).unwrap();

        assert_eq!(map.len(), 10000);
        assert_eq!(map.into_iter().collect::<Vec<_>>(), input);
    }
}
