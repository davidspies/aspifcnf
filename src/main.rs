use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::{env, iter};

mod reduce;

/// Represents a rule in the ASP program.
#[derive(Debug)]
struct Rule {
    head_type: HeadType,
    head_atoms: Vec<usize>,
    body: Body,
}

/// Represents the type of the rule head.
#[derive(Clone, Copy, Debug, PartialEq)]
enum HeadType {
    Disjunction,
    Choice,
}

/// Represents a literal, which can be positive or negative.
type Literal = isize;

/// Represents the body of a rule, which can be normal or a weight body.
#[derive(Debug)]
struct Body {
    lower_bound: usize,
    literals: Vec<(Literal, usize)>, // (literal, weight)
}

/// Manages the mapping between atom names and variable numbers.
struct AtomTable {
    atom_to_var: HashMap<String, usize>,
    var_to_atom: HashMap<usize, String>,
    atoms: HashSet<usize>,
}

impl AtomTable {
    fn new() -> Self {
        Self {
            atom_to_var: HashMap::new(),
            var_to_atom: HashMap::new(),
            atoms: HashSet::new(),
        }
    }

    /// Maps atom name to variable number.
    fn add_atom(&mut self, name: &str, var: usize) {
        self.atom_to_var.insert(name.to_string(), var);
        self.var_to_atom.insert(var, name.to_string());
        self.atoms.insert(var);
    }

    /// Adds a literal's absolute value as an atom.
    fn add_literal(&mut self, lit: isize) {
        self.atoms.insert(lit.abs() as usize);
    }

    /// Retrieves the maximum variable number used in atoms.
    fn max_atom_var(&self) -> usize {
        *self.atoms.iter().max().unwrap_or(&0)
    }
}

/// Variable counter for generating new variables.
#[derive(Clone)]
struct VarCounter(usize);

impl VarCounter {
    fn new(start: usize) -> Self {
        VarCounter(start)
    }

    fn get_new_variable(&mut self) -> usize {
        let var = self.0;
        self.0 += 1;
        var
    }
}

/// Represents the entire ASP program.
struct ASPProgram {
    rules: Vec<Rule>,
    atom_table: AtomTable,
}

struct SatTranslator {
    clauses: Vec<Vec<isize>>,
    atom_rule_vars: HashMap<usize, Vec<usize>>,
    var_counter: VarCounter,
}

impl ASPProgram {
    fn new() -> Self {
        Self {
            rules: Vec::new(),
            atom_table: AtomTable::new(),
        }
    }

    /// Parses the ASPIF input and populates the ASPProgram.
    fn parse_aspif<R: BufRead>(&mut self, reader: R) {
        for line_result in reader.lines() {
            let line = line_result.expect("Failed to read line");
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') || line == "0" {
                continue;
            }

            let tokens: Vec<&str> = line.split_whitespace().collect();
            if tokens.is_empty() {
                continue;
            }

            match tokens[0] {
                "1" => self.parse_rule(&tokens[1..]),
                "4" => self.parse_output(&tokens[1..]),
                _ => {
                    // Other statements are ignored in this implementation
                }
            }
        }
    }

    /// Parses a rule statement from the ASPIF input.
    fn parse_rule(&mut self, tokens: &[&str]) {
        let mut idx = 0;
        let head_type = match tokens[idx].parse::<u8>().unwrap() {
            0 => HeadType::Disjunction,
            1 => HeadType::Choice,
            _ => panic!("Unknown head type"),
        };
        idx += 1;
        let m = tokens[idx].parse::<usize>().unwrap(); // Number of head atoms
        idx += 1;
        let mut head_atoms = Vec::new();
        for _ in 0..m {
            let atom = tokens[idx].parse::<usize>().unwrap();
            self.atom_table.add_literal(atom as isize);
            head_atoms.push(atom);
            idx += 1;
        }
        let body_type = tokens[idx].parse::<u8>().unwrap();
        idx += 1;
        let body = match body_type {
            0 => {
                // Normal body
                let n = tokens[idx].parse::<usize>().unwrap(); // Number of body literals
                idx += 1;
                let mut literals = Vec::new();
                for _ in 0..n {
                    let lit = tokens[idx].parse::<isize>().unwrap();
                    self.atom_table.add_literal(lit);
                    literals.push((lit, 1));
                    idx += 1;
                }
                Body {
                    literals,
                    lower_bound: n,
                }
            }
            1 => {
                // Weight body
                let lower_bound = tokens[idx].parse::<usize>().unwrap();
                idx += 1;
                let n = tokens[idx].parse::<usize>().unwrap(); // Number of body literals
                idx += 1;
                let mut literals = Vec::new();
                for _ in 0..n {
                    let lit = tokens[idx].parse::<isize>().unwrap();
                    idx += 1;
                    let weight = tokens[idx].parse::<usize>().unwrap();
                    idx += 1;
                    self.atom_table.add_literal(lit);
                    literals.push((lit, weight));
                }
                Body {
                    lower_bound,
                    literals,
                }
            }
            _ => {
                panic!("Unsupported body type: {}", body_type);
            }
        };

        let rule = Rule {
            head_type,
            head_atoms,
            body,
        };
        self.rules.push(rule);
    }

    /// Parses an output statement to map atom names to variable numbers.
    fn parse_output(&mut self, tokens: &[&str]) {
        let _m = tokens[0].parse::<usize>().unwrap();
        let s = tokens[1];
        let n = tokens[2].parse::<usize>().unwrap();

        if n == 0 {
            // Unconditional show: Map 's' to a variable not yet mapped
            let all_vars: HashSet<usize> = self
                .rules
                .iter()
                .flat_map(|r| r.head_atoms.iter().cloned())
                .collect();
            let mapped_vars: HashSet<usize> = self.atom_table.var_to_atom.keys().cloned().collect();
            let unmapped_vars: Vec<usize> = all_vars.difference(&mapped_vars).cloned().collect();

            if unmapped_vars.is_empty() {
                panic!("No unmapped variable available for atom '{}'", s);
            }

            let var = unmapped_vars[0];
            self.atom_table.add_atom(s, var);
        } else if n == 1 {
            // Conditional show: Map 's' to l1
            let l = tokens[3].parse::<usize>().unwrap();
            self.atom_table.add_atom(s, l);
        } else {
            panic!(
                "Unsupported number of literals (n={}) in #show directive for atom '{}'",
                n, s
            );
        }
    }
}

impl SatTranslator {
    fn new(var_counter: VarCounter) -> Self {
        Self {
            clauses: Vec::new(),
            atom_rule_vars: HashMap::new(),
            var_counter,
        }
    }

    /// Generates CNF clauses based on the parsed rules.
    fn generate_clauses(&mut self, prog: &ASPProgram) {
        for rule in &prog.rules {
            let rule_var = self.var_counter.get_new_variable();
            self.generate_head_clauses(rule.head_type, &rule.head_atoms, rule_var);
            self.generate_body_clauses(&rule.body, rule_var);
        }

        // Add the atom support clauses
        self.generate_atom_support_clauses();
    }

    fn generate_head_clauses(
        &mut self,
        head_type: HeadType,
        head_atoms: &Vec<usize>,
        rule_var: usize,
    ) {
        if head_type == HeadType::Disjunction {
            self.clauses.push(
                head_atoms
                    .iter()
                    .map(|&a| a as isize)
                    .chain(iter::once(-(rule_var as isize)))
                    .collect(),
            );
        }
        for &head_atom in head_atoms {
            self.atom_rule_vars
                .entry(head_atom)
                .or_insert_with(Vec::new)
                .push(rule_var);
        }
    }

    fn generate_body_clauses(&mut self, body: &Body, rule_var: usize) {
        let Body {
            lower_bound,
            literals,
        } = body;
        // Calculate the total sum of weights
        let total_weight = literals.iter().map(|&(_, w)| w).sum();

        // Special handling when lower_bound == total_weight
        if *lower_bound == total_weight {
            let rule_var = rule_var;
            self.clauses.push(
                iter::once(rule_var as isize)
                    .chain(literals.iter().map(|&(lit, _)| -lit))
                    .collect(),
            );
            for &(lit, _) in literals {
                self.clauses.push(vec![-(rule_var as isize), lit]);
            }
        } else if literals.iter().all(|&(_, w)| w >= *lower_bound) {
            for &(lit, _) in literals {
                self.clauses.push(vec![rule_var as isize, -lit]);
            }
            self.clauses.push(
                iter::once(-(rule_var as isize))
                    .chain(literals.iter().map(|&(lit, _)| lit))
                    .collect(),
            );
        } else {
            // Use the existing approach
            WeightBodyBuilder::new(body, rule_var, self).generate_clauses();
        }
    }

    /// Generates the atom support clauses.
    fn generate_atom_support_clauses(&mut self) {
        for (atom_var, rule_vars) in self.atom_rule_vars.iter() {
            let mut clause = vec![-(*atom_var as isize)];
            for &r_var in rule_vars {
                clause.push(r_var as isize);
            }
            self.clauses.push(clause);
        }
    }
}

/// Struct to handle weight body clause generation.
struct WeightBodyBuilder<'a> {
    body: &'a Body,
    rule_var: usize,
    clause_builder: &'a mut SatTranslator,
    v_vars: Vec<usize>,
    bitstrings: HashMap<isize, Vec<bool>>,
    l_prime_vars: HashMap<isize, usize>,
}

impl<'a> WeightBodyBuilder<'a> {
    fn new(body: &'a Body, rule_var: usize, clause_builder: &'a mut SatTranslator) -> Self {
        // Check conditions
        if body.lower_bound != 2 {
            panic!(
                "Only weight bodies with lower bound 2 are supported. Got rule body {:?}",
                body
            );
        }
        if !body.literals.iter().all(|&(_, w)| w == 1) {
            panic!(
                "Only weight bodies with all weights 1 are supported. Got rule body {:?}",
                body
            );
        }
        let n = body.literals.len();
        let k = (n as f64).log2().ceil() as usize;

        // Create k new variables v0, v1, ..., v(k-1)
        let mut v_vars = Vec::new();
        for _ in 0..k {
            let var = clause_builder.var_counter.get_new_variable();
            v_vars.push(var);
        }

        // Assign bitstrings to literals
        let mut bitstrings: HashMap<isize, Vec<bool>> = HashMap::new();
        for (i, &(lit, _)) in body.literals.iter().enumerate() {
            let bitstring = format!("{:0width$b}", i, width = k);
            let bits: Vec<bool> = bitstring.chars().map(|c| c == '1').collect();
            bitstrings.insert(lit, bits);
        }

        // For each body literal l, create an extra variable l'
        let mut l_prime_vars: HashMap<isize, usize> = HashMap::new();
        for &(lit, _) in &body.literals {
            let l_prime = clause_builder.var_counter.get_new_variable();
            l_prime_vars.insert(lit, l_prime);
        }

        WeightBodyBuilder {
            body,
            rule_var,
            clause_builder,
            v_vars,
            bitstrings,
            l_prime_vars,
        }
    }

    fn generate_clauses(mut self) {
        // Generate clauses for each body literal
        for (lit, _) in self.body.literals.iter() {
            self.generate_body_literal_clauses(*lit);
        }
        // Generate supportedness clauses
        self.generate_supportedness_clauses();
    }

    fn generate_body_literal_clauses(&mut self, lit: Literal) {
        let bits = &self.bitstrings[&lit];
        // Clause: r_i \/ not l'
        self.clause_builder.clauses.push(vec![
            self.rule_var as isize,
            -(self.l_prime_vars[&lit] as isize),
        ]);
        // For each bit position i
        for (i, &bit) in bits.iter().enumerate() {
            let v_i = self.v_vars[i];
            // Clause: not l \/ l' \/ v_i
            let mut clause = vec![-lit, self.l_prime_vars[&lit] as isize];
            if bit {
                clause.push(v_i as isize);
            } else {
                clause.push(-(v_i as isize));
            }
            self.clause_builder.clauses.push(clause);
        }
        // Supportedness constraints:
        // Clause: not l' \/ l
        let l_prime = self.l_prime_vars[&lit];
        self.clause_builder
            .clauses
            .push(vec![-(l_prime as isize), lit]);
        // Clause: not l' \/ (vs don't match l's bitstring)
        let mut vs_clause = vec![-(l_prime as isize)];
        let bits = &self.bitstrings[&lit];
        for (i, &bit) in bits.iter().enumerate() {
            let v_i = self.v_vars[i];
            if bit {
                vs_clause.push(-(v_i as isize));
            } else {
                vs_clause.push(v_i as isize);
            }
        }
        self.clause_builder.clauses.push(vs_clause);
    }

    fn generate_supportedness_clauses(&mut self) {
        // For each bit variable v_i
        for (i, &v_i) in self.v_vars.iter().enumerate() {
            let mut clause1 = vec![-(self.rule_var as isize), v_i as isize];
            let mut clause2 = vec![-(self.rule_var as isize), -(v_i as isize)];
            // Collect literals where bit i is 0 or 1
            let mut literals_with_bit0 = Vec::new();
            let mut literals_with_bit1 = Vec::new();
            for &(lit, _) in &self.body.literals {
                let bits = &self.bitstrings[&lit];
                if bits[i] {
                    literals_with_bit1.push(lit);
                } else {
                    literals_with_bit0.push(lit);
                }
            }
            clause1.extend(literals_with_bit0);
            clause2.extend(literals_with_bit1);
            self.clause_builder.clauses.push(clause1);
            self.clause_builder.clauses.push(clause2);
        }
        // Add clause: not r_i \/ (l' for all body literals)
        let mut l_primes_clause = vec![-(self.rule_var as isize)];
        for &l_prime in self.l_prime_vars.values() {
            l_primes_clause.push(l_prime as isize);
        }
        self.clause_builder.clauses.push(l_primes_clause);
    }
}

fn main() {
    // Read the ASPIF file from command line arguments or stdin
    let args: Vec<String> = env::args().collect();
    let input: Box<dyn BufRead> = if args.len() > 1 {
        let filename = &args[1];
        let file = File::open(filename).expect("Unable to open file");
        Box::new(BufReader::new(file))
    } else {
        Box::new(BufReader::new(io::stdin()))
    };

    let mut program = ASPProgram::new();
    program.parse_aspif(input);
    let max_atom_var = program.atom_table.max_atom_var();
    let var_counter = VarCounter::new(max_atom_var + 1);
    let mut translator = SatTranslator::new(var_counter);
    translator.generate_clauses(&program);
    let clauses = reduce::apply_reductions(translator.clauses).unwrap();
    let mut introduced_vars: Vec<_> = clauses
        .iter()
        .flatten()
        .filter_map(|&lit| {
            let atom = lit.abs() as usize;
            (atom > max_atom_var).then_some(atom)
        })
        .collect();
    introduced_vars.sort_unstable();
    introduced_vars.dedup();
    let total_vars = max_atom_var + introduced_vars.len();
    let mapping: HashMap<_, _> = introduced_vars
        .into_iter()
        .enumerate()
        .map(|(i, v)| (v, max_atom_var + 1 + i))
        .collect();

    // Output DIMACS CNF format
    println!("p cnf {} {}", total_vars, clauses.len());
    for clause in clauses {
        for mut lit in clause {
            if lit.abs() > max_atom_var as isize {
                let var = mapping[&(lit.abs() as usize)];
                lit = var as isize * lit.signum();
            }
            print!("{} ", lit);
        }
        println!("0");
    }
}
