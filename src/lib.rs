mod hash_seq;
mod simple;

pub use simple::Hamt;

#[cfg(test)]
mod tests {
    use std::{
        collections::{hash_map::DefaultHasher, HashMap, HashSet},
        hash::BuildHasherDefault,
    };

    use proptest::prelude::*;
    use proptest_derive::Arbitrary;

    use super::*;

    #[derive(Debug, Arbitrary)]
    enum Op<K, V> {
        Len,
        Get { key: K },
        Insert { key: K, value: V },
        Remove { key: K },
        Iter,
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

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
                        "insert failed key={key}, value={value}, desired={hashmap:#?}, actual={hamt:#?}",
                        key = key,
                        value = value,
                        hashmap = hashmap,
                        hamt = hamt,
                    ),
                    Op::Get { key } => prop_assert_eq!(
                        hamt.get(&key),
                        hashmap.get(&key),
                        "get failed key={key}, desired={hashmap:#?}, actual={hamt:#?}",
                        key = key,
                        hashmap = hashmap,
                        hamt = hamt,
                    ),
                    Op::Remove { key } => prop_assert_eq!(
                        hamt.remove(&key),
                        hashmap.remove(&key),
                        "remove failed key={key}, desired={hashmap:#?}, actual={hamt:#?}",
                        key = key,
                        hashmap = hashmap,
                        hamt = hamt,
                    ),
                    Op::Iter => prop_assert_eq!(hamt.iter().collect::<HashSet<_>>(), hashmap.iter().collect::<HashSet<_>>(),
                        "iter failed desired={hashmap:#?}, actual={hamt:#?}",
                        hashmap = hashmap,
                        hamt = hamt,
                    ),
                    Op::Len => prop_assert_eq!(hamt.len(), hashmap.len(),
                        "len failed desired={hashmap:#?}, actual={hamt:#?}",
                        hashmap = hashmap,
                        hamt = hamt,
                    ),
                }
        }
    }
    }
}
