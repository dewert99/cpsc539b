use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use ahash::AHashMap;

#[derive(Default)]
pub struct SemiPersistent<T>(T);

impl<T> Deref for SemiPersistent<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> SemiPersistent<T> {
    pub fn new(data: T) -> Self {
        SemiPersistent(data)
    }
}

pub struct Revert<'a, T, F: FnMut(&mut T)> {
    data: &'a mut SemiPersistent<T>,
    revert: F,
}

impl<'a, T, F: FnMut(&mut T)> Deref for Revert<'a, T, F> {
    type Target = SemiPersistent<T>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<'a, T, F: FnMut(&mut T)> DerefMut for Revert<'a, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<'a, T, F: FnMut(&mut T)> Drop for Revert<'a, T, F> {
    fn drop(&mut self) {
        (self.revert)(&mut self.data.0);
    }
}

impl<'a, K: Hash + Eq + Clone, V> SemiPersistent<AHashMap<K, V>> {
    pub fn insert_sp(
        &mut self,
        key: K,
        val: V,
    ) -> Revert<'_, AHashMap<K, V>, impl FnMut(&mut AHashMap<K, V>)> {
        let mut last_val = self.0.insert(key.clone(), val);
        Revert {
            data: self,
            revert: move |map| {
                match last_val.take() {
                    None => map.remove(&key),
                    Some(val) => map.insert(key.clone(), val),
                };
            },
        }
    }
}

pub type SPHashMap<K, V> = SemiPersistent<AHashMap<K, V>>;