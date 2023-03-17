use ahash::AHashMap;
use std::hash::Hash;
use std::mem;
use std::ops::{Deref, DerefMut};

#[derive(Default, Clone, Debug)]
/// Wrapper for semi persistent data structure
/// Methods mutating inner type return a `Revert` handle which reverts the changes when dropped
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

    pub fn map(self, f: impl FnOnce(&mut T)) -> Self {
        let mut this = self;
        f(&mut this.0);
        this
    }

    /// Use with caution
    /// Requires that `revert` undoes the effect of `d0` when passed it's return value
    pub fn do_and_revert<'a, U>(
        &'a mut self,
        d0: impl FnOnce(&mut T) -> U,
        mut revert: impl FnMut(&mut U, &mut T) + 'a,
    ) -> Revert<'a, T, impl FnMut(&mut T)> {
        let mut val = d0(&mut self.0);
        Revert {
            data: self,
            revert: move |x| revert(&mut val, x),
        }
    }
}

pub enum Either<X, Y> {
    L(X),
    R(Y),
}

impl<X: Deref, Y: Deref<Target = X::Target>> Deref for Either<X, Y> {
    type Target = X::Target;

    fn deref(&self) -> &Self::Target {
        match self {
            Either::L(x) => x,
            Either::R(y) => y,
        }
    }
}

impl<X: DerefMut, Y: DerefMut<Target = X::Target>> DerefMut for Either<X, Y> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Either::L(x) => x,
            Either::R(y) => y,
        }
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

pub type SPHashMap<K, V> = SemiPersistent<AHashMap<K, V>>;

impl<'a, K: Hash + Eq + Clone, V> SPHashMap<K, V> {
    pub fn insert_sp(
        &mut self,
        key: K,
        val: V,
    ) -> Revert<'_, AHashMap<K, V>, impl FnMut(&mut AHashMap<K, V>)> {
        let k2 = key.clone();
        self.do_and_revert(
            |data| data.insert(key, val),
            move |last_val, data| {
                match last_val.take() {
                    None => data.remove(&k2),
                    Some(val) => data.insert(k2.clone(), val),
                };
            },
        )
    }

    pub fn remove_sp(
        &mut self,
        key: K,
    ) -> Revert<'_, AHashMap<K, V>, impl FnMut(&mut AHashMap<K, V>) + '_> {
        let k2 = key.clone();
        self.do_and_revert(
            move |data| data.remove(&key),
            move |last_val, data| {
                match last_val.take() {
                    None => {}
                    Some(val) => {
                        data.insert(k2.clone(), val);
                    }
                };
            },
        )
    }

    pub fn clear(&mut self) -> Revert<'_, AHashMap<K, V>, impl FnMut(&mut AHashMap<K, V>)> {
        self.do_and_revert(mem::take, |last_val, data| *data = mem::take(last_val))
    }
}
