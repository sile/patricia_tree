use crate::node::{Flags, Node};
use crate::{PatriciaMap, PatriciaSet};
use serde::de::Error;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

impl Serialize for PatriciaSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_ref().serialize(serializer)
    }
}

impl<T: Serialize> Serialize for PatriciaMap<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_ref().serialize(serializer)
    }
}

impl<T: Serialize> Serialize for Node<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        struct Bytes<'a>(&'a [u8]);

        impl<'a> Serialize for Bytes<'a> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serializer.serialize_bytes(self.0)
            }
        }

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

        (Bytes(&tree_bytes), values).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for PatriciaSet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Node::deserialize(deserializer).map(PatriciaSet::from)
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for PatriciaMap<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Node::<T>::deserialize(deserializer).map(PatriciaMap::from)
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for Node<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // let (mut tree_bytes, mut values): (&'de [u8], Vec<T>) =
        //     Deserialize::deserialize(deserializer)?;
        let (tree_bytes, mut values): (Vec<u8>, Vec<T>) = Deserialize::deserialize(deserializer)?;
        values.reverse();
        let mut tree_bytes = &tree_bytes[..];

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
            let mut node = Node::<T>::new_for_decoding(flags, label_len as u8);
            node.label_mut().copy_from_slice(&tree_bytes[..label_len]);
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
                    return Ok(node);
                } else {
                    return Err(D::Error::custom("invalid data"));
                }
            }
        }

        Err(D::Error::custom("invalid data"))
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

        let mut bytes = Vec::new();
        ciborium::ser::into_writer(&map, &mut bytes).unwrap();

        let map: PatriciaMap<u32> = ciborium::de::from_reader(&mut &bytes[..]).unwrap();

        assert_eq!(map.len(), 3);
        assert_eq!(map.into_iter().collect::<Vec<_>>(), input);
    }

    // #[test]
    // fn large_serde_works() {
    //     let mut input = (0..10000)
    //         .map(|i| (i.to_string().into_bytes(), i))
    //         .collect::<Vec<_>>();
    //     input.sort();

    //     let map: PatriciaMap<_> = input.iter().cloned().collect();
    //     let root = Node::from(map);

    //     let mut buf = Vec::new();
    //     let mut encoder = track_try_unwrap!(NodeEncoder::<U32beEncoder>::with_item(root));
    //     track_try_unwrap!(encoder.encode_all(&mut buf));

    //     let mut decoder = NodeDecoder::new(U32beDecoder::new());
    //     let size = track_try_unwrap!(decoder.decode(&buf, Eos::new(true)));
    //     assert_eq!(size, buf.len());

    //     let item = track_try_unwrap!(decoder.finish_decoding());
    //     let map = PatriciaMap::from(item);
    //     assert_eq!(map.len(), 10000);
    //     assert_eq!(map.into_iter().collect::<Vec<_>>(), input);
    // }
}
