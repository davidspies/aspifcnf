use std::collections::{btree_map::Entry, BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::ops::{Deref, DerefMut};

use derive_where::derive_where;

#[derive(Clone)]
#[derive_where(Default)]
pub struct AssertSet<T>(pub BTreeSet<T>);

impl<T: Debug + Ord> AssertSet<T> {
    pub fn new() -> Self {
        AssertSet(BTreeSet::new())
    }

    #[track_caller]
    pub fn insert(&mut self, value: T) {
        let inserted = self.0.insert(value);
        assert!(inserted, "Value already present in BTreeSet");
    }

    #[track_caller]
    pub fn remove(&mut self, value: &T) {
        let removed = self.0.remove(value);
        assert!(removed, "Value {value:?} not found in BTreeSet");
    }

    pub fn try_insert(&mut self, value: T) -> bool {
        self.0.insert(value)
    }

    pub fn try_remove(&mut self, value: &T) -> bool {
        self.0.remove(value)
    }
}

impl<T: Ord> Deref for AssertSet<T> {
    type Target = BTreeSet<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Ord> DerefMut for AssertSet<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive_where(Default)]
pub struct AssertMap<K: Ord, V>(pub BTreeMap<K, V>);

impl<K: Debug + Ord, V> AssertMap<K, V> {
    #[track_caller]
    pub fn insert(&mut self, key: K, value: V) {
        match self.0.entry(key) {
            Entry::Vacant(vac) => {
                vac.insert(value);
            }
            Entry::Occupied(occ) => {
                panic!("Key {:?} already present in BTreeMap", occ.key());
            }
        }
    }

    #[track_caller]
    pub fn remove(&mut self, key: &K) -> V {
        let removed = self.0.remove(key);
        removed.unwrap_or_else(|| panic!("Key {key:?} not found in BTreeMap"))
    }
}

impl<K: Ord, V> Deref for AssertMap<K, V> {
    type Target = BTreeMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K: Ord, V> DerefMut for AssertMap<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// AssertMultiMap remains the same
#[derive_where(Default)]
pub struct AssertMultiMap<K: Ord, V: Ord>(pub AssertMap<K, AssertSet<V>>);

impl<K: Debug + Ord, V: Debug + Ord> AssertMultiMap<K, V> {
    #[track_caller]
    pub fn insert(&mut self, key: K, value: V) {
        self.0
            .entry(key)
            .or_insert_with(AssertSet::new)
            .insert(value);
    }

    #[track_caller]
    pub fn remove(&mut self, key: K, value: &V) {
        match self.0.entry(key) {
            Entry::Occupied(mut occ) => {
                occ.get_mut().remove(value);
                if occ.get().is_empty() {
                    occ.remove();
                }
            }
            Entry::Vacant(vac) => {
                panic!("Key {:?} not found in MultiMap", vac.key());
            }
        }
    }
}

impl<K: Ord, V: Ord> Deref for AssertMultiMap<K, V> {
    type Target = AssertMap<K, AssertSet<V>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K: Ord, V: Ord> DerefMut for AssertMultiMap<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
