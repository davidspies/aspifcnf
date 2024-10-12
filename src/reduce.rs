#[derive(Debug)]
pub struct Unsatisfiable;

mod assert_collections {
    use std::collections::{hash_map::Entry, HashMap, HashSet};
    use std::hash::Hash;
    use std::ops::{Deref, DerefMut};

    #[derive(Default)]
    pub struct AssertHashSet<T: Eq + Hash>(pub HashSet<T>);

    impl<T: Eq + Hash> AssertHashSet<T> {
        pub fn new() -> Self {
            AssertHashSet(HashSet::new())
        }

        #[track_caller]
        pub fn insert(&mut self, value: T) {
            let inserted = self.0.insert(value);
            assert!(inserted, "Value already present in HashSet");
        }

        #[track_caller]
        pub fn remove(&mut self, value: &T) {
            let removed = self.0.remove(value);
            assert!(removed, "Value not found in HashSet");
        }

        pub fn try_remove(&mut self, value: &T) -> bool {
            self.0.remove(value)
        }
    }

    impl<T: Eq + Hash> Deref for AssertHashSet<T> {
        type Target = HashSet<T>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T: Eq + Hash> DerefMut for AssertHashSet<T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    #[derive(Default)]
    pub struct AssertHashMap<K: Eq + Hash, V>(pub HashMap<K, V>);

    impl<K: Eq + Hash, V> AssertHashMap<K, V> {
        pub fn new() -> Self {
            AssertHashMap(HashMap::new())
        }

        #[track_caller]
        pub fn insert(&mut self, key: K, value: V) {
            let replaced = self.0.insert(key, value);
            assert!(replaced.is_none(), "Key already present in HashMap");
        }

        #[track_caller]
        pub fn remove(&mut self, key: &K) -> V {
            let removed = self.0.remove(key);
            removed.expect("Key not found in HashMap")
        }
    }

    impl<K: Eq + Hash, V> Deref for AssertHashMap<K, V> {
        type Target = HashMap<K, V>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<K: Eq + Hash, V> DerefMut for AssertHashMap<K, V> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    // New AssertMultiMap
    #[derive(Default)]
    pub struct AssertMultiMap<K: Eq + Hash, V: Eq + Hash>(pub AssertHashMap<K, AssertHashSet<V>>);

    impl<K: Eq + Hash, V: Eq + Hash> AssertMultiMap<K, V> {
        pub fn new() -> Self {
            AssertMultiMap(AssertHashMap::new())
        }

        #[track_caller]
        pub fn insert(&mut self, key: K, value: V) {
            self.0
                .entry(key)
                .or_insert_with(AssertHashSet::new)
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

    impl<K: Eq + Hash, V: Eq + Hash> Deref for AssertMultiMap<K, V> {
        type Target = AssertHashMap<K, AssertHashSet<V>>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<K: Eq + Hash, V: Eq + Hash> DerefMut for AssertMultiMap<K, V> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }
}

mod sat_instance {
    use super::assert_collections::{AssertHashMap, AssertHashSet, AssertMultiMap};
    use super::Unsatisfiable;
    use std::collections::HashSet;

    #[derive(Default)]
    pub struct SatInstance {
        // Private fields
        clause_id_to_literals: AssertHashMap<usize, AssertHashSet<isize>>,
        literal_to_clause_ids: AssertMultiMap<isize, usize>,
        clause_length_to_clause_ids: AssertMultiMap<usize, usize>,
        num_clauses_containing_literal_to_literals: AssertMultiMap<usize, isize>,
        redundant_clause_ids: AssertHashSet<usize>,
    }

    impl SatInstance {
        // Public accessors
        /// Returns an immutable reference to the clause ID to literals mapping.
        pub fn clause_id_to_literals(&self) -> &AssertHashMap<usize, AssertHashSet<isize>> {
            &self.clause_id_to_literals
        }

        /// Returns an immutable reference to the literal to clause IDs mapping.
        pub fn literal_to_clause_ids(&self) -> &AssertMultiMap<isize, usize> {
            &self.literal_to_clause_ids
        }

        /// Returns an immutable reference to the clause length to clause IDs mapping.
        pub fn clause_length_to_clause_ids(&self) -> &AssertMultiMap<usize, usize> {
            &self.clause_length_to_clause_ids
        }

        /// Returns an immutable reference to the number of clauses containing literal to literals mapping.
        pub fn num_clauses_containing_literal_to_literals(&self) -> &AssertMultiMap<usize, isize> {
            &self.num_clauses_containing_literal_to_literals
        }

        /// Returns an immutable reference to the set of redundant clause IDs.
        pub fn redundant_clause_ids(&self) -> &AssertHashSet<usize> {
            &self.redundant_clause_ids
        }

        // Primitive methods

        /// Adds a clause to the instance.
        pub fn add_clause(
            &mut self,
            clause_id: usize,
            literals: HashSet<isize>,
        ) -> Result<(), Unsatisfiable> {
            if literals.is_empty() {
                return Err(Unsatisfiable);
            }

            let literals_set = AssertHashSet(literals);
            self.clause_id_to_literals.insert(clause_id, literals_set);

            let clause_len = self.clause_id_to_literals[&clause_id].len();
            self.clause_length_to_clause_ids
                .insert(clause_len, clause_id);

            for &lit in self.clause_id_to_literals[&clause_id].iter() {
                self.literal_to_clause_ids.insert(lit, clause_id);
            }

            // Update num_clauses_containing_literal_to_literals
            for &lit in self.clause_id_to_literals[&clause_id].iter() {
                let count = self.literal_to_clause_ids[&lit].len();
                self.num_clauses_containing_literal_to_literals
                    .insert(count, lit);
                if count > 1 {
                    self.num_clauses_containing_literal_to_literals
                        .remove(count - 1, &lit);
                }
            }

            // Check for redundancy
            let literals = &self.clause_id_to_literals[&clause_id];
            if has_redundancy(literals) {
                self.redundant_clause_ids.insert(clause_id);
            }

            Ok(())
        }

        /// Adds a literal to a clause.
        pub fn add_literal_to_clause(&mut self, clause_id: usize, literal: isize) {
            let literals = self.clause_id_to_literals.get_mut(&clause_id).unwrap();

            // Update clause_length_to_clause_ids
            let old_length = literals.len();
            literals.insert(literal);
            let new_length = literals.len();
            assert_eq!(new_length, old_length + 1);

            self.clause_length_to_clause_ids
                .remove(old_length, &clause_id);
            self.clause_length_to_clause_ids
                .insert(new_length, clause_id);

            // Update literal_to_clause_ids
            self.literal_to_clause_ids.insert(literal, clause_id);

            // Update num_clauses_containing_literal_to_literals
            let count = self.literal_to_clause_ids[&literal].len();
            self.num_clauses_containing_literal_to_literals
                .insert(count, literal);
            if count > 1 {
                self.num_clauses_containing_literal_to_literals
                    .remove(count - 1, &literal);
            }

            // Update redundancy
            if literals.contains(&-literal) {
                self.redundant_clause_ids.insert(clause_id);
            }
        }

        /// Removes a literal from a clause.
        pub fn remove_literal_from_clause(
            &mut self,
            clause_id: usize,
            literal: isize,
        ) -> Result<(), Unsatisfiable> {
            let literals = self.clause_id_to_literals.get_mut(&clause_id).unwrap();

            literals.remove(&literal);

            // Update clause_length_to_clause_ids
            let old_length = literals.len() + 1;
            let new_length = literals.len();

            self.clause_length_to_clause_ids
                .remove(old_length, &clause_id);

            self.clause_length_to_clause_ids
                .insert(new_length, clause_id);

            // Update literal_to_clause_ids
            self.literal_to_clause_ids.remove(literal, &clause_id);

            // Update num_clauses_containing_literal_to_literals
            let new_count = self
                .literal_to_clause_ids
                .get(&literal)
                .map_or(0, |s| s.len());
            let old_count = new_count + 1;
            self.num_clauses_containing_literal_to_literals
                .remove(old_count, &literal);
            if new_count > 0 {
                self.num_clauses_containing_literal_to_literals
                    .insert(new_count, literal);
            }

            // Update redundancy
            if literals.contains(&-literal) {
                if !has_redundancy(literals) {
                    self.redundant_clause_ids.remove(&clause_id);
                }
            }

            // Check if the clause is now empty
            if literals.is_empty() {
                return Err(Unsatisfiable);
            }

            Ok(())
        }

        /// Eliminates a clause from the instance.
        pub fn remove_clause(&mut self, clause_id: usize) {
            let literals = self.clause_id_to_literals.remove(&clause_id);

            // Remove from clause_length_to_clause_ids
            self.clause_length_to_clause_ids
                .remove(literals.len(), &clause_id);

            // Remove from redundant_clause_ids
            self.redundant_clause_ids.try_remove(&clause_id);

            for &lit in literals.iter() {
                // Update literal_to_clause_ids
                self.literal_to_clause_ids.remove(lit, &clause_id);

                // Update num_clauses_containing_literal_to_literals
                let new_count = self.literal_to_clause_ids.get(&lit).map_or(0, |s| s.len());
                let old_count = new_count + 1;
                self.num_clauses_containing_literal_to_literals
                    .remove(old_count, &lit);
                if new_count > 0 {
                    self.num_clauses_containing_literal_to_literals
                        .insert(new_count, lit);
                }
            }
        }
    }

    fn has_redundancy(literals: &AssertHashSet<isize>) -> bool {
        literals.iter().any(|&l| literals.contains(&-l))
    }
}

use std::collections::HashSet;

use self::sat_instance::SatInstance;

impl SatInstance {
    /// Creates a new `SatInstance` from a list of clauses.
    pub fn new(clauses: Vec<Vec<isize>>) -> Result<Self, Unsatisfiable> {
        let mut instance = SatInstance::default();

        for (clause_id, clause) in clauses.into_iter().enumerate() {
            let literals: HashSet<isize> = clause.into_iter().collect();
            instance.add_clause(clause_id, literals)?;
        }

        Ok(instance)
    }

    /// Applies Rule 1: Tautology Elimination.
    pub fn apply_tautology_elimination(&mut self) -> bool {
        let redundant_clause_ids: Vec<_> = self.redundant_clause_ids().iter().copied().collect();
        if redundant_clause_ids.is_empty() {
            return false;
        }
        for cid in redundant_clause_ids {
            self.remove_clause(cid);
        }
        true
    }

    /// Applies Rule 2: Unit Propagation.
    pub fn apply_unit_propagation(&mut self) -> Result<bool, Unsatisfiable> {
        let unit_clause_ids = self.clause_length_to_clause_ids().get(&1);
        let Some(unit_clause_ids) = unit_clause_ids else {
            return Ok(false);
        };
        let unit_clause_ids: Vec<_> = unit_clause_ids.iter().copied().collect();
        for cid in unit_clause_ids {
            let Some(literals) = self.clause_id_to_literals().get(&cid) else {
                // In case the same unit clause occurs twice
                continue;
            };
            let unit_lit = *extract_singleton(literals.iter());
            // Remove clauses containing unit_lit
            if let Some(cids) = self.literal_to_clause_ids().get(&unit_lit) {
                let cids: Vec<_> = cids.iter().copied().collect();
                for cid_to_remove in cids {
                    self.remove_clause(cid_to_remove);
                }
            }
            // Remove -unit_lit from clauses
            if let Some(cids) = self.literal_to_clause_ids().get(&-unit_lit) {
                let cids: Vec<_> = cids.iter().copied().collect();
                for cid_to_modify in cids {
                    self.remove_literal_from_clause(cid_to_modify, -unit_lit)?;
                }
            }
        }
        Ok(true)
    }

    /// Applies Rule 3: Pure Literal Elimination.
    pub fn apply_pure_literal_elimination(&mut self) -> bool {
        let pure_literals: Vec<_> = self
            .literal_to_clause_ids()
            .keys()
            .filter(|&&l| !self.literal_to_clause_ids().contains_key(&-l))
            .cloned()
            .collect();

        if !pure_literals.is_empty() {
            for lit in pure_literals {
                if let Some(cids) = self.literal_to_clause_ids().get(&lit) {
                    let cids: Vec<_> = cids.iter().cloned().collect();
                    for cid in cids {
                        self.remove_clause(cid);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    /// Applies Rule 4: Chain Length Reduction.
    pub fn apply_chain_length_reduction(&mut self) -> bool {
        if let Some(literals_with_one_clause) =
            self.num_clauses_containing_literal_to_literals().get(&1)
        {
            let literals_with_one_clause: Vec<_> =
                literals_with_one_clause.iter().cloned().collect();
            for lit in literals_with_one_clause {
                if let Some(cids) = self.literal_to_clause_ids().get(&lit) {
                    let cid = *cids.iter().next().unwrap();
                    if self.clause_id_to_literals()[&cid].len() == 2 {
                        let other_lit = *self.clause_id_to_literals()[&cid]
                            .iter()
                            .filter(|&&l| l != lit)
                            .next()
                            .unwrap();

                        // Remove the clause
                        self.remove_clause(cid);

                        // Replace -lit with other_lit in all clauses
                        if let Some(cids_neg) = self.literal_to_clause_ids().get(&-lit) {
                            let cids_neg: Vec<_> = cids_neg.iter().cloned().collect();
                            for cid_neg in cids_neg {
                                self.add_literal_to_clause(cid_neg, other_lit);
                                self.remove_literal_from_clause(cid_neg, -lit).unwrap();
                            }
                        }
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Applies Rule 5: Once-Each Reduction.
    pub fn apply_once_each_reduction(&mut self) -> Result<bool, Unsatisfiable> {
        if let Some(literals_with_one_clause) =
            self.num_clauses_containing_literal_to_literals().get(&1)
        {
            let literals_with_one_clause: Vec<_> =
                literals_with_one_clause.iter().cloned().collect();
            for lit in literals_with_one_clause {
                if let Some(cids1) = self.literal_to_clause_ids().get(&lit) {
                    if let Some(cids2) = self.literal_to_clause_ids().get(&-lit) {
                        if cids1.len() == 1 && cids2.len() == 1 {
                            let cid1 = *cids1.iter().next().unwrap();
                            let cid2 = *cids2.iter().next().unwrap();

                            let mut resolvent: HashSet<_> = self.clause_id_to_literals()[&cid1]
                                .iter()
                                .chain(self.clause_id_to_literals()[&cid2].iter())
                                .cloned()
                                .filter(|&l| l != lit && l != -lit)
                                .collect();

                            // Remove both clauses
                            self.remove_clause(cid1);
                            self.remove_clause(cid2);

                            // Add the resolvent clause
                            self.add_clause(cid1, resolvent)?;
                            return Ok(true);
                        }
                    }
                }
            }
        }
        Ok(false)
    }

    /// Applies all reduction rules until a fixed point is reached.
    pub fn reduce_to_fixed_point(&mut self) -> Result<(), Unsatisfiable> {
        loop {
            if self.apply_tautology_elimination() {
                continue;
            }

            if self.apply_unit_propagation()? {
                continue;
            }

            if self.apply_pure_literal_elimination() {
                continue;
            }

            if self.apply_chain_length_reduction() {
                continue;
            }

            if self.apply_once_each_reduction()? {
                continue;
            }

            break;
        }
        Ok(())
    }
}

fn extract_singleton<T>(collection: impl IntoIterator<Item = T>) -> T {
    let mut iter = collection.into_iter();
    let singleton = iter.next().unwrap();
    assert!(iter.next().is_none(), "Expected a singleton collection");
    singleton
}

// Usage Example

fn main() {
    let clauses = vec![
        vec![1, -2],
        vec![2],
        vec![-1, 3],
        vec![1, -3],
        vec![4, -4], // This clause is redundant
    ];

    match SatInstance::new(clauses) {
        Ok(mut sat_instance) => match sat_instance.reduce_to_fixed_point() {
            Ok(()) => {
                let reduced_clauses: Vec<Vec<isize>> = sat_instance
                    .clause_id_to_literals()
                    .values()
                    .map(|literals| literals.iter().cloned().collect())
                    .collect();

                println!("Reduced Clauses: {:?}", reduced_clauses);
            }
            Err(_) => {
                println!("Unsatisfiable");
            }
        },
        Err(_) => {
            println!("Unsatisfiable");
        }
    }
}
