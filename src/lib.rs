mod hash_seq;
mod simple;

pub use simple::Hamt;

#[cfg(test)]
mod tests {
    use std::{
        collections::{hash_map::DefaultHasher, HashMap},
        hash::BuildHasherDefault,
    };

    use proptest::prelude::*;
    use proptest_derive::Arbitrary;

    use super::*;

    #[derive(Debug, Arbitrary)]
    enum Op<K, V> {
        Get { key: K },
        Insert { key: K, value: V },
        Remove { key: K },
    }

    proptest! {
        #[test]
        fn matches_hashmap(ops in prop::collection::vec(any::<Op<u8, u8>>(), prop::collection::SizeRange::default())
        ) {
            // Use a consistent seed so shrinking works.
            let mut hamt: Hamt<u8, u8, BuildHasherDefault<DefaultHasher>> = Hamt::default();
            let mut hashmap: HashMap<u8, u8, BuildHasherDefault<DefaultHasher>> = HashMap::default();

            for op in ops {
                match op {
                    Op::Insert { key, value } => prop_assert_eq!(
                        hamt.insert(key, value),
                        hashmap.insert(key, value),
                        "insert failed key={key}, value={value}, state={hashmap:?}",
                        key = key,
                        value = value,
                        hashmap = hashmap
                    ),
                    Op::Get { key } => prop_assert_eq!(
                        hamt.get(&key),
                        hashmap.get(&key),
                        "get failed key={key}, state={hashmap:?}",
                        key = key,
                        hashmap = hashmap
                    ),
                    Op::Remove { key } => prop_assert_eq!(
                        hamt.remove(&key),
                        hashmap.remove(&key),
                        "remove failed key={key}, state={hashmap:?}",
                        key = key,
                        hashmap = hashmap
                    ),
                }
            }
        }
    }
}
