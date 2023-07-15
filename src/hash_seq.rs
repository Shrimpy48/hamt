use std::hash::*;
use std::iter::{FusedIterator, Iterator};

// No Copy implementation for the same reason Range doesn't: Iterators with Copy can be confusing.
#[derive(Debug)]
pub struct HashSeq<'a, Q: ?Sized, S> {
    key: &'a Q,
    hash_builder: &'a S,
    hash: u64,
    depth: usize,
    shift: u8,
}

impl<'a, Q: ?Sized, S> Clone for HashSeq<'a, Q, S> {
    fn clone(&self) -> Self {
        Self {
            key: self.key,
            hash_builder: self.hash_builder,
            hash: self.hash,
            depth: self.depth,
            shift: self.shift,
        }
    }
}

impl<'a, Q, S> HashSeq<'a, Q, S>
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    pub fn new(key: &'a Q, hash_builder: &'a S) -> Self {
        let depth: usize = 0;
        let mut hasher = hash_builder.build_hasher();
        depth.hash(&mut hasher);
        key.hash(&mut hasher);
        let hash = hasher.finish();
        Self {
            key,
            hash_builder,
            hash,
            depth,
            shift: 0,
        }
    }

    pub fn key(&self) -> &'a Q {
        self.key
    }

    pub fn with_key(&self, key: &'a Q) -> Self {
        let depth = self.depth;
        let shift = self.shift;
        let hash_builder = self.hash_builder;
        let mut hasher = hash_builder.build_hasher();
        depth.hash(&mut hasher);
        key.hash(&mut hasher);
        let hash = hasher.finish();
        Self {
            key,
            hash_builder,
            hash,
            depth,
            shift,
        }
    }
}

impl<Q, S> Iterator for HashSeq<'_, Q, S>
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let res = (self.hash >> self.shift) & 0b111111;

        // We read the range shift..shift+6, and we are about to increase shift by 6
        if self.shift > 64 - 12 {
            self.shift = 0;
            self.depth += 1;
            let mut hasher = self.hash_builder.build_hasher();
            self.depth.hash(&mut hasher);
            self.key.hash(&mut hasher);
            self.hash = hasher.finish();
        } else {
            self.shift += 6;
        }

        // At most the lowest 6 bits of res can be set, so it definitely fits
        Some(res as usize)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

impl<Q, S> FusedIterator for HashSeq<'_, Q, S>
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
}
