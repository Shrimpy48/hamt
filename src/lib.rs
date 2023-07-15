mod hash_seq;
mod simple;

pub use simple::Hamt;

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use proptest::prelude::*;
    use proptest_derive::Arbitrary;

    use super::*;

    #[derive(Debug, Arbitrary)]
    enum Op<K, V> {
        Insert { key: K, value: V },
        Get { key: K },
        Remove { key: K },
    }

    proptest! {
        #[test]
        fn matches_hashmap(ops in prop::collection::vec(any::<Op<u8, u8>>(), prop::collection::SizeRange::default())) {
            let mut hamt: Hamt<u8, u8> = Hamt::new();
            let mut hashmap: HashMap<u8, u8> = HashMap::new();

            for op in ops {
                match op {
                    Op::Insert { key, value } => prop_assert_eq!(hamt.insert(key, value), hashmap.insert(key, value)),
                    Op::Get { key } => prop_assert_eq!(hamt.get(&key), hashmap.get(&key)),
                    Op::Remove { key } => prop_assert_eq!(hamt.remove(&key), hashmap.remove(&key)),
                }
            }
        }
    }
}
