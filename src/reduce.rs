use std::collections::BTreeSet;

use self::internal::Literal;
use self::internal::SatInstance;

mod assert_collections;
mod internal;

#[derive(Debug)]
pub struct Unsatisfiable;

pub fn apply_reductions(clauses: Vec<Vec<isize>>) -> Result<Vec<Vec<isize>>, Unsatisfiable> {
    let mut instance = SatInstance::new(clauses)?;
    instance.reduce_to_fixed_point()?;
    Ok(instance.to_clauses())
}

impl SatInstance {
    /// Creates a new `SatInstance` with a given number of variables and clauses.
    pub fn new(clauses: Vec<Vec<isize>>) -> Result<Self, Unsatisfiable> {
        // Determine the number of variables (maximum absolute value of literals)
        let num_vars = clauses
            .iter()
            .flatten()
            .map(|&lit| lit.abs() as usize)
            .max()
            .unwrap_or(0);

        let mut instance = Self::new_helper(num_vars);

        // Now add clauses
        for (clause_id, clause) in clauses.into_iter().enumerate() {
            instance.add_clause(clause_id, clause.into_iter().map(Literal).collect())?;
        }

        Ok(instance)
    }

    pub(crate) fn to_clauses(&self) -> Vec<Vec<isize>> {
        self.clause_id_to_literals()
            .iter()
            .map(|(_, literals)| literals.iter().copied().map(|l| l.0).collect())
            .collect()
    }

    /// Applies Rule 1: Tautology Elimination.
    pub fn apply_tautology_elimination(&mut self) -> bool {
        let redundant_clause_ids = self.redundant_clause_ids().clone();
        if redundant_clause_ids.is_empty() {
            return false;
        }
        for &cid in redundant_clause_ids.iter().rev() {
            self.remove_clause(cid);
        }
        true
    }

    /// Applies Rule 2: Unit Propagation.
    pub fn apply_unit_propagation(&mut self) -> Result<bool, Unsatisfiable> {
        let Some(unit_clause_ids) = self.clause_length_to_clause_ids().get(&1) else {
            return Ok(false);
        };
        for cid in unit_clause_ids.clone().iter().rev() {
            let Some(literals) = self.clause_id_to_literals().get(&cid) else {
                // In case the same unit clause occurs twice
                continue;
            };
            let &unit_lit = extract_singleton(literals.iter()).unwrap();
            // Remove clauses containing unit_lit
            if let Some(cids) = self.literal_to_clause_ids().get(&unit_lit) {
                for &cid_to_remove in cids.clone().iter() {
                    self.remove_clause(cid_to_remove);
                }
            }
            // Remove -unit_lit from clauses
            if let Some(cids) = self.literal_to_clause_ids().get(&-unit_lit) {
                for &cid_to_modify in cids.clone().iter() {
                    self.remove_literal_from_clause(cid_to_modify, -unit_lit)?;
                }
            }
        }
        Ok(true)
    }

    /// Applies Rule 3: Pure Literal Elimination.
    pub fn apply_pure_literal_elimination(&mut self) -> bool {
        let zero_count_literals = self.num_clauses_containing_literal_to_literals()[&0].clone();
        let mut changed = false;

        // Iterate over literals with counts of zero
        for &lit in zero_count_literals.iter().rev() {
            for &cid in self.literal_to_clause_ids()[&-lit].clone().iter() {
                self.remove_clause(cid);
                changed = true;
            }
        }

        changed
    }

    pub fn apply_equalities(&mut self) -> bool {
        let mut changed = false;
        for &(atom1, lit2) in self.equalities().clone().iter().rev() {
            let lit1 = Literal(atom1 as isize);
            for &clause_id in self.literal_to_clause_ids()[&lit1].clone().iter() {
                self.add_literal_to_clause(clause_id, lit2);
                self.remove_literal_from_clause(clause_id, lit1).unwrap();
                changed = true;
            }
            let lit1 = Literal(-(atom1 as isize));
            let lit2 = -lit2;
            for &clause_id in self.literal_to_clause_ids()[&lit1].clone().iter() {
                self.add_literal_to_clause(clause_id, lit2);
                self.remove_literal_from_clause(clause_id, lit1).unwrap();
                changed = true;
            }
        }
        changed
    }

    /// Applies Rule 4: Chain Length Reduction.
    pub fn apply_chain_length_reduction(&mut self) -> bool {
        let Some(literals_with_one_clause) =
            self.num_clauses_containing_literal_to_literals().get(&1)
        else {
            return false;
        };
        let mut changed = false;
        for &lit in literals_with_one_clause.clone().iter().rev() {
            let Some(&cid) = extract_singleton(self.literal_to_clause_ids()[&lit].iter()) else {
                continue;
            };
            let Some(&other_lit) = extract_singleton(
                self.clause_id_to_literals()[&cid]
                    .iter()
                    .filter(|&&l| l != lit),
            ) else {
                continue;
            };

            // Remove the clause
            self.remove_clause(cid);
            changed = true;

            // Replace -lit with other_lit in all clauses
            let Some(cids_neg) = self.literal_to_clause_ids().get(&-lit) else {
                continue;
            };
            for &cid_neg in cids_neg.clone().iter() {
                self.add_literal_to_clause(cid_neg, other_lit);
                self.remove_literal_from_clause(cid_neg, -lit).unwrap();
            }
        }
        changed
    }

    /// Applies Rule 5: Once-Each Reduction.
    pub fn apply_once_each_reduction(&mut self) -> Result<bool, Unsatisfiable> {
        let Some(literals_with_one_clause) =
            self.num_clauses_containing_literal_to_literals().get(&1)
        else {
            return Ok(false);
        };
        let mut changed = false;
        for &lit in literals_with_one_clause.clone().iter().rev() {
            let Some(cids1) = self.literal_to_clause_ids().get(&lit) else {
                continue;
            };
            let Some(&cid1) = extract_singleton(cids1.iter()) else {
                continue;
            };
            let Some(cids2) = self.literal_to_clause_ids().get(&-lit) else {
                continue;
            };
            let Some(&cid2) = extract_singleton(cids2.iter()) else {
                continue;
            };
            let resolvent: BTreeSet<_> = self.clause_id_to_literals()[&cid1]
                .iter()
                .chain(self.clause_id_to_literals()[&cid2].iter())
                .copied()
                .filter(|&l| l != lit && l != -lit)
                .collect();

            // Remove both clauses
            self.remove_clause(cid1);
            self.remove_clause(cid2);

            // Add the resolvent clause
            self.add_clause(cid1, resolvent)?;
            changed = true;
        }
        Ok(changed)
    }

    /// Applies all reduction rules until a fixed point is reached.
    pub fn reduce_to_fixed_point(&mut self) -> Result<(), Unsatisfiable> {
        loop {
            if self.apply_tautology_elimination() {
                eprintln!("Tautology Elimination");
                continue;
            }

            if self.apply_unit_propagation()? {
                eprintln!("Unit Propagation");
                continue;
            }

            if self.apply_pure_literal_elimination() {
                eprintln!("Pure Literal Elimination");
                continue;
            }

            if self.apply_equalities() {
                eprintln!("Equality Reduction");
                continue;
            }

            if self.apply_once_each_reduction()? {
                eprintln!("Once-Each Reduction");
                continue;
            }

            if self.apply_chain_length_reduction() {
                eprintln!("Chain Length Reduction");
                continue;
            }

            break;
        }
        Ok(())
    }
}

fn extract_singleton<T>(mut iter: impl Iterator<Item = T>) -> Option<T> {
    let singleton = iter.next()?;
    iter.next().is_none().then_some(singleton)
}
