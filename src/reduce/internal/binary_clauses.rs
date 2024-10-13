use crate::reduce::assert_collections::{AssertMultiMap, AssertSet};
use crate::reduce::internal::Literal;

#[derive(Default)]
pub(super) struct BinaryClauses {
    clauses: AssertMultiMap<(Literal, Literal), usize>,
    equalities: AssertSet<(usize, Literal)>,
}

impl BinaryClauses {
    pub(super) fn equalities(&self) -> &AssertSet<(usize, Literal)> {
        &self.equalities
    }

    pub(super) fn try_insert(&mut self, clause_id: usize, clause: &AssertSet<Literal>) -> bool {
        let mut clause = clause.iter();
        let Some(&lit1) = clause.next() else {
            return false;
        };
        let Some(&lit2) = clause.next() else {
            return false;
        };
        if clause.next().is_some() {
            return false;
        }
        if lit1 == -lit2 {
            return false;
        }
        assert!(lit1 < lit2);
        self.clauses.insert((lit1, lit2), clause_id);
        if self.clauses.contains_key(&(-lit1, -lit2)) {
            if lit2.0 < 0 {
                self.equalities.try_insert((-lit2.0 as usize, lit1));
            } else {
                self.equalities.try_insert((lit2.0 as usize, -lit1));
            }
        }
        true
    }

    pub(super) fn try_remove(&mut self, clause_id: usize, clause: &AssertSet<Literal>) -> bool {
        let mut clause = clause.iter();
        let Some(&lit1) = clause.next() else {
            return false;
        };
        let Some(&lit2) = clause.next() else {
            return false;
        };
        if clause.next().is_some() {
            return false;
        }
        if lit1 == -lit2 {
            return false;
        }
        assert!(lit1 < lit2);
        self.clauses.remove((lit1, lit2), &clause_id);
        if !self.clauses.contains_key(&(lit1, lit2)) {
            if lit2.0 < 0 {
                self.equalities.try_remove(&(-lit2.0 as usize, lit1));
            } else {
                self.equalities.try_remove(&(lit2.0 as usize, -lit1));
            }
        }
        true
    }
}
