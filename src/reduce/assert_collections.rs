use std::collections::{btree_map::Entry, BTreeMap, BTreeSet};
use std::ops::{Deref, DerefMut};

use derive_where::derive_where;

#[derive(Clone, Default)]
pub struct AssertSet<T: Ord>(pub BTreeSet<T>);

impl<T: Ord> AssertSet<T> {
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
        assert!(removed, "Value not found in BTreeSet");
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

impl<K: Ord, V> AssertMap<K, V> {
    #[track_caller]
    pub fn insert(&mut self, key: K, value: V) {
        let replaced = self.0.insert(key, value);
        assert!(replaced.is_none(), "Key already present in BTreeMap");
    }

    #[track_caller]
    pub fn remove(&mut self, key: &K) -> V {
        let removed = self.0.remove(key);
        removed.expect("Key not found in BTreeMap")
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

impl<K: Ord, V: Ord> AssertMultiMap<K, V> {
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
            Entry::Vacant(_) => {
                panic!("Key not found in MultiMap");
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
