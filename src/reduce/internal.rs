use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::ops::Neg;

use super::assert_collections::{AssertMap, AssertMultiMap, AssertSet};
use super::Unsatisfiable;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct Literal(pub(super) isize);

impl Neg for Literal {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0.abs(), self.0.signum()).cmp(&(other.0.abs(), other.0.signum()))
    }
}

#[derive(Default)]
pub(super) struct SatInstance {
    // Private fields
    clause_id_to_literals: AssertMap<usize, AssertSet<Literal>>,
    literal_to_clause_ids: AssertMap<Literal, AssertSet<usize>>,
    clause_length_to_clause_ids: AssertMultiMap<usize, usize>,
    num_clauses_containing_literal_to_literals: AssertMultiMap<usize, Literal>,
    redundant_clause_ids: AssertSet<usize>,
}

impl SatInstance {
    pub(super) fn new_helper(num_vars: usize) -> Self {
        let mut instance = Self::default();

        // Initialize literal_to_clause_ids with empty sets for all literals
        for var in 1..=num_vars as isize {
            instance
                .literal_to_clause_ids
                .insert(Literal(var), AssertSet::new());
            instance
                .literal_to_clause_ids
                .insert(Literal(-var), AssertSet::new());
        }

        // Initialize num_clauses_containing_literal_to_literals with 0 entry
        for var in 1..=num_vars as isize {
            instance
                .num_clauses_containing_literal_to_literals
                .insert(0, Literal(var));
            instance
                .num_clauses_containing_literal_to_literals
                .insert(0, Literal(-var));
        }
        instance
    }

    // Public accessors
    /// Returns an immutable reference to the clause ID to literals mapping.
    pub(super) fn clause_id_to_literals(&self) -> &AssertMap<usize, AssertSet<Literal>> {
        &self.clause_id_to_literals
    }

    /// Returns an immutable reference to the literal to clause IDs mapping.
    pub(super) fn literal_to_clause_ids(&self) -> &AssertMap<Literal, AssertSet<usize>> {
        &self.literal_to_clause_ids
    }

    /// Returns an immutable reference to the clause length to clause IDs mapping.
    pub(super) fn clause_length_to_clause_ids(&self) -> &AssertMultiMap<usize, usize> {
        &self.clause_length_to_clause_ids
    }

    /// Returns an immutable reference to the number of clauses containing literal to literals mapping.
    pub(super) fn num_clauses_containing_literal_to_literals(
        &self,
    ) -> &AssertMultiMap<usize, Literal> {
        &self.num_clauses_containing_literal_to_literals
    }

    /// Returns an immutable reference to the set of redundant clause IDs.
    pub(super) fn redundant_clause_ids(&self) -> &AssertSet<usize> {
        &self.redundant_clause_ids
    }

    // Primitive methods

    /// Adds a clause to the instance.
    pub(super) fn add_clause(
        &mut self,
        clause_id: usize,
        literals: BTreeSet<Literal>,
    ) -> Result<(), Unsatisfiable> {
        if literals.is_empty() {
            return Err(Unsatisfiable);
        }

        let literals_set = AssertSet(literals);
        self.clause_id_to_literals.insert(clause_id, literals_set);

        let clause_len = self.clause_id_to_literals[&clause_id].len();
        self.clause_length_to_clause_ids
            .insert(clause_len, clause_id);

        for &lit in self.clause_id_to_literals[&clause_id].iter() {
            // Since the key always exists in literal_to_clause_ids, we can get_mut
            let clause_ids_set = self.literal_to_clause_ids.get_mut(&lit).unwrap();

            let old_count = clause_ids_set.len();

            // Remove from old count in num_clauses_containing_literal_to_literals
            self.num_clauses_containing_literal_to_literals
                .remove(old_count, &lit);

            clause_ids_set.insert(clause_id);

            let new_count = old_count + 1;

            self.num_clauses_containing_literal_to_literals
                .insert(new_count, lit);
        }

        // Check for redundancy
        if has_redundancy(&self.clause_id_to_literals[&clause_id]) {
            self.redundant_clause_ids.insert(clause_id);
        }

        Ok(())
    }

    /// Adds a literal to a clause.
    pub(super) fn add_literal_to_clause(&mut self, clause_id: usize, literal: Literal) -> bool {
        let literals = self.clause_id_to_literals.get_mut(&clause_id).unwrap();

        // Update clause_length_to_clause_ids
        let old_length = literals.len();
        let inserted = literals.try_insert(literal);
        if !inserted {
            return false;
        }
        let new_length = literals.len();
        assert_eq!(new_length, old_length + 1);

        self.clause_length_to_clause_ids
            .remove(old_length, &clause_id);
        self.clause_length_to_clause_ids
            .insert(new_length, clause_id);

        // Update literal_to_clause_ids
        let clause_ids_set = self.literal_to_clause_ids.get_mut(&literal).unwrap();

        let old_count = clause_ids_set.len();

        // Remove from old count in num_clauses_containing_literal_to_literals
        self.num_clauses_containing_literal_to_literals
            .remove(old_count, &literal);

        clause_ids_set.insert(clause_id);

        let new_count = old_count + 1;

        self.num_clauses_containing_literal_to_literals
            .insert(new_count, literal);

        // Update redundancy
        if literals.contains(&-literal) {
            self.redundant_clause_ids.try_insert(clause_id);
        }

        true
    }

    /// Removes a literal from a clause.
    pub(super) fn remove_literal_from_clause(
        &mut self,
        clause_id: usize,
        literal: Literal,
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
        let clause_ids_set = self.literal_to_clause_ids.get_mut(&literal).unwrap();

        let old_count = clause_ids_set.len();
        clause_ids_set.remove(&clause_id);

        // Remove from old count in num_clauses_containing_literal_to_literals
        self.num_clauses_containing_literal_to_literals
            .remove(old_count, &literal);

        let new_count = old_count - 1;
        self.num_clauses_containing_literal_to_literals
            .insert(new_count, literal);

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
    pub(super) fn remove_clause(&mut self, clause_id: usize) {
        let literals = self.clause_id_to_literals.remove(&clause_id);

        // Remove from clause_length_to_clause_ids
        self.clause_length_to_clause_ids
            .remove(literals.len(), &clause_id);

        // Remove from redundant_clause_ids
        self.redundant_clause_ids.try_remove(&clause_id);

        for &lit in literals.iter() {
            // Update literal_to_clause_ids
            let clause_ids_set = self.literal_to_clause_ids.get_mut(&lit).unwrap();

            let old_count = clause_ids_set.len();
            clause_ids_set.remove(&clause_id);

            // Remove from old count in num_clauses_containing_literal_to_literals
            self.num_clauses_containing_literal_to_literals
                .remove(old_count, &lit);

            let new_count = old_count - 1;
            self.num_clauses_containing_literal_to_literals
                .insert(new_count, lit);
        }
    }
}

fn has_redundancy(literals: &AssertSet<Literal>) -> bool {
    literals.iter().any(|&l| literals.contains(&-l))
}
