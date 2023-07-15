use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::mem;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

use crate::hash_seq::HashSeq;

pub struct Hamt<K, V, S = RandomState> {
    root: IntNode<K, V>,
    hash_builder: S,
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
        }
    }
}

impl<K, V, S> Hamt<K, V, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
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
            .map(|leaf| (&*leaf.key, &*leaf.value))
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get_key_value(k).map(|(_, v)| v)
    }

    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash_seq = HashSeq::new(k, &self.hash_builder);
        let result = self.root.search_mut(hash_seq);
        match result.kind {
            SearchResultKind::Success => {
                let Some(Node::Leaf(leaf)) = result.anchor.get_mut(result.index) else { unreachable!() };
                Some(Rc::make_mut(&mut leaf.value))
            }
            _ => None,
        }
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let key = Rc::new(k);
        let hs_key = Rc::clone(&key);
        let hash_seq = HashSeq::new(&*hs_key, &self.hash_builder);
        let result = self.root.search_mut(hash_seq.clone());
        match result.kind {
            SearchResultKind::Success => {
                let Some(Node::Leaf(leaf)) = result.anchor.get_mut(result.index) else { unreachable!() };
                Some(mem::replace(Rc::make_mut(&mut leaf.value), v))
            }
            SearchResultKind::NotFound => {
                *result.anchor = result.anchor.insert(
                    result.index,
                    Node::Leaf(LeafNode {
                        key,
                        value: Rc::new(v),
                    }),
                );
                None
            }
            SearchResultKind::Mismatch => {
                let Some(Node::Leaf(leaf)) = result.anchor.get(result.index) else { unreachable!() };
                let leaf = leaf.clone();
                let other_hash_seq = hash_seq.with_key(&leaf.key);
                let paired_seq = hash_seq.zip(other_hash_seq);
                let Some(child) = result.anchor.get_mut(result.index) else { unreachable!() };
                *child = Node::Int(IntNode::make_table(
                    paired_seq,
                    LeafNode {
                        key,
                        value: Rc::new(v),
                    },
                    leaf.clone(),
                ));
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

impl<K, V, S> Default for Hamt<K, V, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
struct IntNode<K, V> {
    bitmap: u64,
    children: Rc<[Node<K, V>]>,
}

impl<K, V> IntNode<K, V> {
    fn new() -> Self {
        Self {
            bitmap: 0,
            children: Rc::new([]),
        }
    }

    fn get(&self, index: usize) -> Option<&Node<K, V>> {
        if self.bitmap & (1 << index) != 0 {
            let dense_idx = (self.bitmap & ((1 << index) - 1)).count_ones();
            Some(self.children.index(dense_idx as usize))
        } else {
            None
        }
    }

    fn get_mut(&mut self, index: usize) -> Option<&mut Node<K, V>> {
        if self.bitmap & (1 << index) != 0 {
            let dense_idx = (self.bitmap & ((1 << index) - 1)).count_ones();
            Some(make_mut_unsized(&mut self.children).index_mut(dense_idx as usize))
        } else {
            None
        }
    }

    fn insert(&self, index: usize, child: Node<K, V>) -> Self {
        let bitmap = self.bitmap | (1 << index);
        debug_assert_ne!(
            bitmap, self.bitmap,
            "Node should not already have child at this index"
        );
        let new_num_children = bitmap.count_ones() as usize;
        let n_before = (self.bitmap & ((1 << index) - 1)).count_ones() as usize;
        let mut children = Vec::with_capacity(new_num_children);
        children.extend_from_slice(&self.children[..n_before]);
        children.push(child);
        children.extend_from_slice(&self.children[n_before..]);

        Self {
            bitmap,
            children: children.into(),
        }
    }

    fn make_table(
        mut paired_seq: impl Iterator<Item = (usize, usize)>,
        left_leaf: LeafNode<K, V>,
        right_leaf: LeafNode<K, V>,
    ) -> Self {
        let Some((left_index, right_index)) = paired_seq.next() else { unreachable!() };
        match left_index.cmp(&right_index) {
            Ordering::Equal => Self {
                bitmap: 1 << left_index,
                children: Rc::new([Node::Int(Self::make_table(
                    paired_seq, left_leaf, right_leaf,
                ))]),
            },
            Ordering::Less => Self {
                bitmap: (1 << left_index) | (1 << right_index),
                children: Rc::new([Node::Leaf(left_leaf), Node::Leaf(right_leaf)]),
            },
            Ordering::Greater => Self {
                bitmap: (1 << left_index) | (1 << right_index),
                children: Rc::new([Node::Leaf(right_leaf), Node::Leaf(left_leaf)]),
            },
        }
    }

    fn remove_child(&self, index: usize) -> Self {
        let bitmap = self.bitmap & !(1 << index);
        let n_before = (self.bitmap & ((1 << index) - 1)).count_ones() as usize;
        let n_after = (self.bitmap & !((1 << (index + 1)) - 1)).count_ones() as usize;
        let mut children = Vec::with_capacity(bitmap.count_ones() as usize);
        children.extend_from_slice(&self.children[..n_before]);
        children.extend_from_slice(&self.children[self.children.len() - n_after..]);

        Self {
            bitmap,
            children: children.into(),
        }
    }
}

impl<K, V> IntNode<K, V>
where
    K: Clone,
    V: Clone,
{
    // Remove without gathering this node.
    fn remove<Q, S>(&mut self, mut hash_seq: HashSeq<'_, Q, S>) -> RemoveResult<K, V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        S: BuildHasher,
    {
        let Some(index) = hash_seq.next() else { unreachable!() };
        match self.get_mut(index) {
            None => RemoveResult::NotFound,
            Some(Node::Leaf(leaf)) => {
                if (*leaf.key).borrow() == hash_seq.key() {
                    let key = (*leaf.key).clone();
                    let value = (*leaf.value).clone();
                    *self = self.remove_child(index);
                    RemoveResult::Success { key, value }
                } else {
                    RemoveResult::NotFound
                }
            }
            Some(node) => {
                let res = node.gather_remove(hash_seq);
                match res {
                    RemoveResult::NotFound | RemoveResult::Success { .. } => res,
                    RemoveResult::Gathered { key, value } => RemoveResult::Success { key, value },
                }
            }
        }
    }
}

fn make_mut_unsized<T>(rc_t: &mut Rc<T>) -> &mut T
where
    T: ?Sized + ToOwned,
    T::Owned: Into<Rc<T>>,
{
    // The semantics of this are slightly different to make_mut:
    // it will clone instead of disassociating weak pointers.
    if Rc::get_mut(rc_t).is_none() {
        let cloned = (**rc_t).to_owned().into();
        *rc_t = cloned;
    }
    // We now hold an exclusive reference to the only Rc.
    let Some(out) = Rc::get_mut(rc_t) else { unreachable!() };
    out
}

impl<K, V> IntNode<K, V>
where
    K: Eq + Hash,
{
    fn search<'a, Q, S>(&'a self, mut hash_seq: HashSeq<'_, Q, S>) -> Option<&'a LeafNode<K, V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        S: BuildHasher,
    {
        let Some(index) = hash_seq.next() else { unreachable!() };
        match self.get(index) {
            None => None,
            Some(Node::Leaf(leaf)) => {
                if (*leaf.key).borrow() == hash_seq.key() {
                    Some(leaf)
                } else {
                    None
                }
            }
            Some(Node::Int(int)) => int.search(hash_seq),
        }
    }

    fn search_mut<'a, Q, S>(
        &'a mut self,
        mut hash_seq: HashSeq<'_, Q, S>,
    ) -> SearchMutResult<'a, K, V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        S: BuildHasher,
    {
        let Some(index) = hash_seq.next() else { unreachable!() };
        match self.get(index) {
            None => SearchMutResult {
                kind: SearchResultKind::NotFound,
                index,
                anchor: self,
            },
            Some(Node::Leaf(leaf)) => {
                if (*leaf.key).borrow() == hash_seq.key() {
                    SearchMutResult {
                        kind: SearchResultKind::Success,
                        index,
                        anchor: self,
                    }
                } else {
                    SearchMutResult {
                        kind: SearchResultKind::Mismatch,
                        index,
                        anchor: self,
                    }
                }
            }
            Some(Node::Int(_)) => {
                // Decouple the lifetime of this branch's borrow from the others.
                let Some(Node::Int(int)) = self.get_mut(index) else { unreachable!() };
                int.search_mut(hash_seq)
            }
        }
    }
}

impl<K, V> Clone for IntNode<K, V> {
    fn clone(&self) -> Self {
        Self {
            bitmap: self.bitmap,
            children: Rc::clone(&self.children),
        }
    }
}

#[derive(Debug)]
struct LeafNode<K, V> {
    key: Rc<K>,
    value: Rc<V>,
}

impl<K, V> Clone for LeafNode<K, V> {
    fn clone(&self) -> Self {
        Self {
            key: Rc::clone(&self.key),
            value: Rc::clone(&self.value),
        }
    }
}

#[derive(Debug)]
enum Node<K, V> {
    Int(IntNode<K, V>),
    Leaf(LeafNode<K, V>),
}

impl<K, V> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    fn gather_remove<Q, S>(&mut self, mut hash_seq: HashSeq<'_, Q, S>) -> RemoveResult<K, V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        S: BuildHasher,
    {
        match self {
            Self::Int(int) => {
                let Some(index) = hash_seq.next() else { unreachable!() };
                match int.get_mut(index) {
                    None => RemoveResult::NotFound,
                    Some(Node::Leaf(leaf)) => {
                        if (*leaf.key).borrow() == hash_seq.key() {
                            let key = (*leaf.key).clone();
                            let value = (*leaf.value).clone();
                            if int.bitmap.count_ones() == 2 {
                                let other_index = (int.bitmap & !(1 << index)).ilog2() as usize;
                                if let Node::Leaf(_) = int.get(other_index).unwrap() {
                                    self.gather(other_index);
                                    RemoveResult::Gathered { key, value }
                                } else {
                                    *int = int.remove_child(index);
                                    RemoveResult::Success { key, value }
                                }
                            } else {
                                *int = int.remove_child(index);
                                RemoveResult::Success { key, value }
                            }
                        } else {
                            RemoveResult::NotFound
                        }
                    }
                    Some(node) => {
                        let res = node.gather_remove(hash_seq);
                        match res {
                            RemoveResult::NotFound | RemoveResult::Success { .. } => res,
                            RemoveResult::Gathered { key, value } => {
                                let Node::Int(int) = node else { unreachable!() };
                                if int.bitmap.count_ones() == 1 {
                                    self.gather(index);
                                    RemoveResult::Gathered { key, value }
                                } else {
                                    RemoveResult::Success { key, value }
                                }
                            }
                        }
                    }
                }
            }
            Self::Leaf(_) => unreachable!(),
        }
    }
}

impl<K, V> Node<K, V> {
    fn gather(&mut self, index: usize) {
        let Self::Int(int) = self else { unreachable!() };
        let Some(leaf@Self::Leaf(_)) = int.get(index) else { unreachable!() };
        *self = leaf.clone()
    }
}

impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Self {
        match self {
            Self::Int(int) => Self::Int(int.clone()),
            Self::Leaf(leaf) => Self::Leaf(leaf.clone()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum SearchResultKind {
    Success,
    Mismatch,
    NotFound,
}

#[derive(Debug)]
struct SearchMutResult<'a, K, V> {
    kind: SearchResultKind,
    anchor: &'a mut IntNode<K, V>,
    index: usize,
}

#[derive(Debug)]
enum RemoveResult<K, V> {
    Success { key: K, value: V },
    Gathered { key: K, value: V },
    NotFound,
}
