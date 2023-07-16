use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::ops::Index;
use std::rc::Rc;
use std::{fmt, iter, mem};

use crate::hash_seq::HashSeq;

mod node;
use node::*;

pub struct Hamt<K, V, S = RandomState> {
    root: IntNode<K, V>,
    hash_builder: S,
    size: usize,
}

impl<K, V, S> Hamt<K, V, S>
where
    S: Default,
{
    pub fn new() -> Self {
        Self::with_hasher(S::default())
    }
}

impl<K, V, S> Hamt<K, V, S> {
    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            root: IntNode::new(),
            hash_builder,
            size: 0,
        }
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self)
    }

    pub fn len(&self) -> usize {
        self.size
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        self.root = IntNode::new();
        self.size = 0;
    }
}

impl<K, V, S> Hamt<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    pub fn get_key_value<Q>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash_seq = HashSeq::new(k, &self.hash_builder);
        self.root
            .search(hash_seq)
            .map(|leaf| (leaf.key(), leaf.value()))
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get_key_value(k).map(|(_, v)| v)
    }

    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get_key_value(k).is_some()
    }
}

impl<K, V, S> Hamt<K, V, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher,
{
    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut hash_seq = HashSeq::new(k, &self.hash_builder);
        let result = self.root.search_mut(&mut hash_seq);
        match result.kind {
            SearchResultKind::Success => {
                let Some(Node::Leaf(leaf)) = result.anchor.get_mut(result.index) else { unreachable!() };
                Some(leaf.value_mut())
            }
            _ => None,
        }
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let key = Rc::new(k);
        let hs_key = Rc::clone(&key);
        let mut hash_seq = HashSeq::new(&*hs_key, &self.hash_builder);
        let result = self.root.search_mut(&mut hash_seq);
        match result.kind {
            SearchResultKind::Success => {
                let Some(Node::Leaf(leaf)) = result.anchor.get_mut(result.index) else { unreachable!() };
                Some(mem::replace(leaf.value_mut(), v))
            }
            SearchResultKind::NotFound => {
                *result.anchor = result
                    .anchor
                    .insert(result.index, Node::Leaf(LeafNode::new(key, Rc::new(v))));
                self.size += 1;
                None
            }
            SearchResultKind::Mismatch => {
                let Some(Node::Leaf(leaf)) = result.anchor.get(result.index) else { unreachable!() };
                let leaf = leaf.clone();
                let other_hash_seq = hash_seq.with_key(leaf.key());
                let paired_seq = hash_seq.zip(other_hash_seq);
                let Some(child) = result.anchor.get_mut(result.index) else { unreachable!() };
                *child = Node::Int(IntNode::make_table(
                    paired_seq,
                    LeafNode::new(key, Rc::new(v)),
                    leaf.clone(),
                ));
                self.size += 1;
                None
            }
        }
    }

    pub fn remove_entry<Q>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash_seq = HashSeq::new(k, &self.hash_builder);
        let result = self.root.remove(hash_seq);
        match result {
            RemoveResult::Success { key, value } | RemoveResult::Gathered { key, value } => {
                self.size -= 1;
                Some((key, value))
            }
            RemoveResult::NotFound => None,
        }
    }

    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.remove_entry(k).map(|(_, v)| v)
    }
}

impl<K, V, S> Hamt<K, V, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    pub fn insert_immut(&self, k: K, v: V) -> Self {
        // Shallow copy
        let mut out = self.clone();
        out.insert(k, v);
        out
    }

    pub fn remove_immut<Q>(&self, k: &Q) -> Self
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // Shallow copy
        let mut out = self.clone();
        out.remove(k);
        out
    }
}

impl<K, V, S> Default for Hamt<K, V, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, S: Clone> Clone for Hamt<K, V, S> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
            hash_builder: self.hash_builder.clone(),
            size: self.size,
        }
    }
}

impl<K, V, S> Extend<(K, V)> for Hamt<K, V, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for Hamt<K, V, S>
where
    K: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(*key, *value);
        }
    }
}

impl<K, V, S> FromIterator<(K, V)> for Hamt<K, V, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut out = Self::default();
        for (key, value) in iter {
            out.insert(key, value);
        }
        out
    }
}

impl<'a, K, V, S> IntoIterator for &'a Hamt<K, V, S> {
    type IntoIter = Iter<'a, K, V>;
    type Item = (&'a K, &'a V);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// Constraining S is more ergonomic for creating map "literals" - see the note on HashMap::from.
impl<K, V, const N: usize> From<[(K, V); N]> for Hamt<K, V, RandomState>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn from(arr: [(K, V); N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<K, V, S> PartialEq for Hamt<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &Hamt<K, V, S>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, S> Eq for Hamt<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, Q, V, S> Index<&Q> for Hamt<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized,
    S: BuildHasher,
{
    type Output = V;

    #[inline]
    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).expect("no entry found for key")
    }
}

impl<K: fmt::Debug, V: fmt::Debug, S> fmt::Debug for Hamt<K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        map.entries(self.iter());
        map.finish()
    }
}

pub struct Iter<'a, K, V> {
    stack: Vec<IterItem<'a, K, V>>,
    len: usize,
}

struct IterItem<'a, K, V> {
    node: &'a IntNode<K, V>,
    child: usize,
}

impl<'a, K, V> IterItem<'a, K, V> {
    fn new(node: &'a IntNode<K, V>) -> Self {
        Self { node, child: 0 }
    }
}

impl<'a, K, V> Iter<'a, K, V> {
    fn new<S>(hamt: &'a Hamt<K, V, S>) -> Self {
        let exp_depth = hamt
            .size
            .checked_ilog(64)
            .map(|d| d as usize + 2)
            .unwrap_or(1);
        let mut stack = Vec::with_capacity(exp_depth);
        stack.push(IterItem::new(&hamt.root));
        Self {
            stack,
            len: hamt.size,
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.last_mut() {
                Some(item) => match item.node.nth_child(item.child) {
                    Some(Node::Int(int)) => self.stack.push(IterItem::new(int)),
                    Some(Node::Leaf(leaf)) => {
                        let res = Some((leaf.key(), leaf.value()));
                        item.child += 1;
                        self.len -= 1;
                        break res;
                    }
                    None => {
                        self.stack.pop();
                        if let Some(item) = self.stack.last_mut() {
                            item.child += 1
                        }
                    }
                },
                None => {
                    break None;
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K, V> iter::FusedIterator for Iter<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

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
