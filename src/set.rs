use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::{fmt, iter};

use super::Hamt;

pub struct HamtSet<T, S = RandomState> {
    inner: Hamt<T, (), S>,
}

impl<T, S> HamtSet<T, S> {
    pub fn with_hasher(hasher: S) -> Self {
        Self {
            inner: Hamt::with_hasher(hasher),
        }
    }

    pub fn clear(&mut self) {
        self.inner.clear()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self.inner.iter())
    }
}

impl<T, S> HamtSet<T, S>
where
    S: Default,
{
    pub fn new() -> Self {
        Self { inner: Hamt::new() }
    }
}

impl<T, S> HamtSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.inner.contains_key(value)
    }

    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.inner.get_key_value(value).map(|(k, _)| k)
    }
}

impl<T, S> HamtSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher,
{
    pub fn insert(&mut self, value: T) -> bool {
        self.inner.insert(value, ()).is_none()
    }

    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.inner.remove(value).is_some()
    }

    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.inner.remove_entry(value).map(|(k, _)| k)
    }
}

impl<T, S> Clone for HamtSet<T, S>
where
    S: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T, S> fmt::Debug for HamtSet<T, S>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut set = f.debug_set();
        set.entries(self.iter());
        set.finish()
    }
}

impl<T, S> Default for HamtSet<T, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, S> PartialEq<HamtSet<T, S>> for HamtSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    fn eq(&self, other: &HamtSet<T, S>) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<T, S> Eq for HamtSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

impl<T, S> Extend<T> for HamtSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.inner.extend(iter.into_iter().map(|k| (k, ())))
    }
}

impl<'a, T, S> Extend<&'a T> for HamtSet<T, S>
where
    T: Eq + Hash + Copy,
    S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.inner.extend(iter.into_iter().map(|k| (k, &())))
    }
}

impl<T, const N: usize> From<[T; N]> for HamtSet<T, RandomState>
where
    T: Eq + Hash + Clone,
{
    fn from(value: [T; N]) -> Self {
        Self::from_iter(value)
    }
}

impl<T, S> FromIterator<T> for HamtSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            inner: Hamt::from_iter(iter.into_iter().map(|k| (k, ()))),
        }
    }
}

impl<'a, T, S> IntoIterator for &'a HamtSet<T, S> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct Iter<'a, T> {
    inner: super::simple::Iter<'a, T, ()>,
}

impl<'a, T> Iter<'a, T> {
    fn new(inner: super::simple::Iter<'a, T, ()>) -> Self {
        Self { inner }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> iter::FusedIterator for Iter<'a, T> {}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

#[cfg(test)]
mod tests {
    use std::{
        collections::{hash_map::DefaultHasher, HashSet},
        hash::BuildHasherDefault,
    };

    use proptest::prelude::*;
    use proptest_derive::Arbitrary;

    use super::*;

    #[derive(Debug, Arbitrary)]
    enum Op<T> {
        Len,
        Get { value: T },
        Insert { value: T },
        Remove { value: T },
        Iter,
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn matches_hashset(ops in prop::collection::vec(any::<Op<u8>>(), prop::collection::SizeRange::default())
    ) {
        // Use a consistent seed so shrinking works.
        let mut hamt: HamtSet<u8, BuildHasherDefault<DefaultHasher>> = HamtSet::default();
        let mut hashset: HashSet<u8, BuildHasherDefault<DefaultHasher>> = HashSet::default();

        for op in ops {
            match op {
                    Op::Insert { value } => prop_assert_eq!(
                        hamt.insert(value),
                        hashset.insert(value),
                        "insert failed value={value}, desired={hashset:#?}, actual={hamt:#?}",
                        value = value,
                        hashset = hashset,
                        hamt = hamt,
                    ),
                    Op::Get { value } => prop_assert_eq!(
                        hamt.get(&value),
                        hashset.get(&value),
                        "get failed value={value}, desired={hashset:#?}, actual={hamt:#?}",
                        value=value,
                        hashset = hashset,
                        hamt = hamt,
                    ),
                    Op::Remove { value } => prop_assert_eq!(
                        hamt.remove(&value),
                        hashset.remove(&value),
                        "remove failed value={value}, desired={hashset:#?}, actual={hamt:#?}",
                        value = value,
                        hashset = hashset,
                        hamt = hamt,
                    ),
                    Op::Iter => prop_assert_eq!(hamt.iter().collect::<HashSet<_>>(), hashset.iter().collect::<HashSet<_>>(),
                        "iter failed desired={hashset:#?}, actual={hamt:#?}",
                        hashset = hashset,
                        hamt = hamt,
                    ),
                    Op::Len => prop_assert_eq!(hamt.len(), hashset.len(),
                        "len failed desired={hashset:#?}, actual={hamt:#?}",
                        hashset = hashset,
                        hamt = hamt,
                    ),
                }
        }
    }
    }
}
