use ahash::AHashMap;
use std::hash::Hash;
use std::marker::PhantomData;
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

/// Use with caution
/// Requires that `revert` undoes the effect of `d0` when passed it's return value
pub trait DoRevert<T> {
    type Revert: RevertFn<T>;

    fn d0(self, t: &mut T) -> Self::Revert;
}

pub trait RevertFn<T> {
    fn revert(&mut self, t: &mut T);
}

impl<T, D1: DoRevert<T>, D2: DoRevert<T>> DoRevert<T> for (D1, D2) {
    type Revert = (D1::Revert, D2::Revert);

    fn d0(self, t: &mut T) -> Self::Revert {
        (self.0.d0(t), self.1.d0(t))
    }
}

impl<T, R1: RevertFn<T>, R2: RevertFn<T>> RevertFn<T> for (R1, R2) {
    fn revert(&mut self, t: &mut T) {
        self.1.revert(t);
        self.0.revert(t);
    }
}

pub struct Shift<D, F, T>(D, F, PhantomData<T>);

// requires f is pure
pub fn shift<D, F, T>(d: D, f: F) -> Shift<D, F, T> {
    Shift(d, f, PhantomData)
}

impl<T, T2, D: DoRevert<T>, F: Fn(&mut T2) -> &mut T> DoRevert<T2> for Shift<D, F, T> {
    type Revert = Shift<D::Revert, F, T>;

    fn d0(self, t: &mut T2) -> Self::Revert {
        let t = (self.1)(t);
        shift(self.0.d0(t), self.1)
    }
}

impl<T, T2, R: RevertFn<T>, F: Fn(&mut T2) -> &mut T> RevertFn<T2> for Shift<R, F, T> {
    fn revert(&mut self, t: &mut T2) {
        self.0.revert((self.1)(t))
    }
}

pub struct DoRevertBase<D, T>(D, PhantomData<T>);

/// Use with caution
/// Requires that `revert` undoes the effect of `d0` when passed it's return value
pub fn do_revert<D, T>(d: D) -> DoRevertBase<D, T> {
    DoRevertBase(d, PhantomData)
}

impl<D: FnOnce(&mut T) -> R, R: FnMut(&mut T), T> DoRevert<T> for DoRevertBase<D, T> {
    type Revert = DoRevertBase<R, T>;

    fn d0(self, t: &mut T) -> Self::Revert {
        do_revert((self.0)(t))
    }
}

impl<R: FnMut(&mut T), T> RevertFn<T> for DoRevertBase<R, T> {
    fn revert(&mut self, t: &mut T) {
        (self.0)(t)
    }
}


// impl <D, R> DoRevert<D, R> {
//     /// Use with caution
//     /// Requires that `revert` undoes the effect of `d0` when passed it's return value
//     pub fn new<'a, T, U>(d0: D, revert: R) -> Self
//     where D: FnOnce(&mut T) -> U, R: FnMut(&mut U, &mut T) + 'a {
//         DoRevert{d0, revert}
//     }
//
//     pub fn shift<'a, T, U, T2>(self, f: impl Fn(&mut T2) -> &mut T) -> DoRevert<impl FnOnce(&mut T2) -> U, impl FnMut(&mut U, &mut T2) + 'a>
//     where D: FnOnce(&mut T) -> U, R: FnMut(&mut U, &mut T) + 'a  {
//         DoRevert{d0: |t2| (self.d0)(f(t2)), revert: |t2| ((self.revert)(f(t2)))}
//     }
// }

impl<T> SemiPersistent<T> {
    pub fn new(data: T) -> Self {
        SemiPersistent(data)
    }

    pub fn map(self, f: impl FnOnce(&mut T)) -> Self {
        let mut this = self;
        f(&mut this.0);
        this
    }

    pub fn do_and_revert<'a, D: DoRevert<T>>(
        &'a mut self,
        dr: D,
    ) -> Revert<'a, T, D::Revert>
        where D::Revert: 'a {
        let rev = dr.d0(&mut self.0);
        Revert {
            data: self,
            revert: rev,
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

pub struct Revert<'a, T, F: RevertFn<T>> {
    data: &'a mut SemiPersistent<T>,
    revert: F,
}

impl<'a, T, F: RevertFn<T>> Deref for Revert<'a, T, F> {
    type Target = SemiPersistent<T>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<'a, T, F: RevertFn<T>> DerefMut for Revert<'a, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<'a, T, F: RevertFn<T>> Drop for Revert<'a, T, F> {
    fn drop(&mut self) {
        self.revert.revert(&mut self.data.0)
    }
}

pub type SPHashMap<K, V> = SemiPersistent<AHashMap<K, V>>;

fn replace_dr<T: Default>(val: T) -> impl DoRevert<T> {
    do_revert(|data: &mut T| {
        let mut old_val = mem::replace(data, val);
        move |data: &mut T| {
            mem::swap(data, &mut old_val)
        }
    })
}

pub fn map_insert_dr<'a, K: Hash + Eq + Clone, V>(key: K, val: V) -> impl DoRevert<AHashMap<K, V>> {
    let k2 = key.clone();
    do_revert(|data: &mut AHashMap<K, V>| {
        let mut last_val = data.insert(key, val);
        move |data: &mut AHashMap<K, V>| {
            match last_val.take() {
                None => data.remove(&k2),
                Some(val) => data.insert(k2.clone(), val),
            };
        }
    })
}

pub fn map_remove_dr<'a, K: Hash + Eq + Clone, V>(key: K) -> impl DoRevert<AHashMap<K, V>> {
    do_revert(|data: &mut AHashMap<K, V>| {
        let mut last_val = data.remove(&key);
        move |data: &mut AHashMap<K, V>| {
            match last_val.take() {
                None => {},
                Some(val) => {
                    data.insert(key.clone(), val);
                },
            };
        }
    })
}

pub fn inc_dr() -> impl DoRevert<u32> {
    do_revert(|data: &mut u32| {
        *data += 1;
        |data: &mut u32| {*data -= 1;}
    })
}

impl<'a, K: Hash + Eq + Clone, V> SPHashMap<K, V> {
    pub fn insert_sp(
        &mut self,
        key: K,
        val: V,
    ) -> impl DerefMut<Target=SPHashMap<K, V>> + '_ {
        self.do_and_revert(map_insert_dr(key, val))
    }
}
