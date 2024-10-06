use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader};

/// Represents a rule in the ASP program.
#[derive(Debug)]
struct Rule {
    head_type: HeadType,
    head_atoms: Vec<usize>,
    body: Body,
    rule_var: Option<usize>,
}

/// Represents the type of the rule head.
#[derive(Debug, PartialEq)]
enum HeadType {
    Disjunction,
    Choice,
}

/// Represents a literal, which can be positive or negative.
type Literal = isize;

/// Represents the body of a rule, which can be normal or a weight body.
#[derive(Debug)]
enum Body {
    Normal(Vec<Literal>),
    Weight {
        lower_bound: isize,
        literals: Vec<(Literal, usize)>, // (literal, weight)
    },
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

    /// Returns a reference to all atoms.
    fn atoms(&self) -> &HashSet<usize> {
        &self.atoms
    }
}

/// Variable counter for generating new variables.
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

    fn current(&self) -> usize {
        self.0 - 1
    }
}

/// Represents the entire ASP program.
struct ASPProgram {
    rules: Vec<Rule>,
    atom_table: AtomTable,
    atom_rule_vars: HashMap<usize, Vec<usize>>,
    var_counter: VarCounter,
}

impl ASPProgram {
    fn new() -> Self {
        Self {
            rules: Vec::new(),
            atom_table: AtomTable::new(),
            atom_rule_vars: HashMap::new(),
            var_counter: VarCounter::new(1), // Initialize with 1 or the appropriate starting value
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
                let mut body_literals = Vec::new();
                for _ in 0..n {
                    let lit = tokens[idx].parse::<isize>().unwrap();
                    self.atom_table.add_literal(lit);
                    body_literals.push(lit);
                    idx += 1;
                }
                Body::Normal(body_literals)
            }
            1 => {
                // Weight body
                let lower_bound = tokens[idx].parse::<isize>().unwrap();
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
                Body::Weight {
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
            rule_var: None,
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

    /// Assigns unique rule variables to rules with non-empty heads and updates mappings.
    fn assign_rule_vars(&mut self) {
        let max_atom_var = self.atom_table.max_atom_var();
        self.var_counter = VarCounter::new(max_atom_var + 1);
        for rule in &mut self.rules {
            if !rule.head_atoms.is_empty() {
                let rule_var = self.var_counter.get_new_variable();
                rule.rule_var = Some(rule_var);
                // Map head atoms to rule variables
                for &atom in &rule.head_atoms {
                    self.atom_rule_vars
                        .entry(atom)
                        .or_insert_with(Vec::new)
                        .push(rule_var);
                }
            }
        }
    }

    /// Generates CNF clauses based on the parsed rules.
    fn generate_clauses(&mut self) -> Vec<Vec<isize>> {
        let mut clauses = Vec::new();

        for rule in &self.rules {
            match &rule.body {
                Body::Normal(body_literals) => {
                    self.generate_normal_rule_clauses(rule, body_literals, &mut clauses);
                }
                Body::Weight {
                    lower_bound,
                    literals,
                } => {
                    // Calculate the total sum of weights
                    let total_weight: isize = literals.iter().map(|(_, w)| *w as isize).sum();

                    // Special handling when lower_bound == total_weight
                    if *lower_bound == total_weight {
                        // Treat as normal body
                        let body_literals: Vec<Literal> =
                            literals.iter().map(|(lit, _)| *lit).collect();
                        self.generate_normal_rule_clauses(rule, &body_literals, &mut clauses);
                    } else {
                        // Use the existing approach
                        let mut builder = WeightBodyBuilder::new(
                            rule,
                            *lower_bound,
                            literals,
                            &mut self.var_counter,
                            &mut clauses,
                        );
                        builder.generate_clauses();
                    }
                }
            }
        }

        // Add the atom support clauses
        self.generate_atom_support_clauses(&mut clauses);

        clauses
    }

    /// Generates clauses for normal rules and constraints.
    fn generate_normal_rule_clauses(
        &self,
        rule: &Rule,
        body_literals: &[Literal],
        clauses: &mut Vec<Vec<isize>>,
    ) {
        if rule.head_type == HeadType::Disjunction && !rule.head_atoms.is_empty() {
            // Basic rule: a :- b, not c, d
            // Encoded as: a \/ not b \/ c \/ not d
            let mut clause: Vec<isize> = rule.head_atoms.iter().map(|&a| a as isize).collect();
            for &lit in body_literals {
                clause.push(-lit);
            }
            clauses.push(clause);
        }
        // Constraints (rules with empty head)
        if rule.head_type == HeadType::Disjunction && rule.head_atoms.is_empty() {
            // Constraint: :- b, not c.
            // Encoded as: not b \/ c
            let clause: Vec<isize> = body_literals.iter().map(|&lit| -lit).collect();
            clauses.push(clause);
        }
        // Supportedness constraints
        if let Some(r_var) = rule.rule_var {
            for &lit in body_literals {
                clauses.push(vec![-(r_var as isize), lit]);
            }
        }
    }

    /// Generates the atom support clauses.
    fn generate_atom_support_clauses(&self, clauses: &mut Vec<Vec<isize>>) {
        for &atom_var in self.atom_table.atoms() {
            if let Some(rule_vars) = self.atom_rule_vars.get(&atom_var) {
                let mut clause = vec![-(atom_var as isize)];
                for &r_var in rule_vars {
                    clause.push(r_var as isize);
                }
                clauses.push(clause);
            }
        }
    }

    /// Retrieves the total number of variables used.
    fn total_variables(&self) -> usize {
        self.var_counter.current()
    }
}

/// Struct to handle weight body clause generation.
struct WeightBodyBuilder<'a> {
    rule: &'a Rule,
    literals: &'a [(Literal, usize)],
    clauses: &'a mut Vec<Vec<isize>>,
    v_vars: Vec<usize>,
    bitstrings: HashMap<isize, Vec<bool>>,
    l_prime_vars: HashMap<isize, usize>,
}

impl<'a> WeightBodyBuilder<'a> {
    fn new(
        rule: &'a Rule,
        lower_bound: isize,
        literals: &'a [(Literal, usize)],
        var_counter: &'a mut VarCounter,
        clauses: &'a mut Vec<Vec<isize>>,
    ) -> Self {
        // Check conditions
        if lower_bound != 2 {
            panic!("Only weight bodies with lower bound 2 are supported. Got rule {:?}", rule);
        }
        if !literals.iter().all(|&(_, w)| w == 1) {
            panic!("Only weight bodies with all weights 1 are supported. Got rule {:?}", rule);
        }
        let n = literals.len();
        let k = (n as f64).log2().ceil() as usize;

        // Create k new variables v0, v1, ..., v(k-1)
        let mut v_vars = Vec::new();
        for _ in 0..k {
            let var = var_counter.get_new_variable();
            v_vars.push(var);
        }

        // Assign bitstrings to literals
        let mut bitstrings: HashMap<isize, Vec<bool>> = HashMap::new();
        for (i, &(lit, _)) in literals.iter().enumerate() {
            let bitstring = format!("{:0width$b}", i, width = k);
            let bits: Vec<bool> = bitstring.chars().map(|c| c == '1').collect();
            bitstrings.insert(lit, bits);
        }

        // For each body literal l, create an extra variable l'
        let mut l_prime_vars: HashMap<isize, usize> = HashMap::new();
        for &(lit, _) in literals {
            let l_prime = var_counter.get_new_variable();
            l_prime_vars.insert(lit, l_prime);
        }

        WeightBodyBuilder {
            rule,
            literals,
            clauses,
            v_vars,
            bitstrings,
            l_prime_vars,
        }
    }

    fn generate_clauses(&mut self) {
        // Generate clauses for each body literal
        for (lit, _) in self.literals.iter() {
            self.generate_body_literal_clauses(*lit);
        }
        // Generate supportedness clauses
        if let Some(r_var) = self.rule.rule_var {
            self.generate_supportedness_clauses(r_var);
        }
    }

    fn generate_body_literal_clauses(&mut self, lit: Literal) {
        let bits = &self.bitstrings[&lit];
        // For each bit position i
        for (i, &bit) in bits.iter().enumerate() {
            let v_i = self.v_vars[i];
            // Clause: a \/ not l \/ v_i or a \/ not l \/ v_i
            let mut clause = Vec::new();
            for &a in &self.rule.head_atoms {
                clause.push(a as isize);
            }
            clause.push(-lit);
            if bit {
                clause.push(v_i as isize);
            } else {
                clause.push(-(v_i as isize));
            }
            self.clauses.push(clause);
        }
        // Supportedness constraints:
        // Clause: not l' \/ l
        let l_prime = self.l_prime_vars[&lit];
        self.clauses.push(vec![-(l_prime as isize), lit]);
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
        self.clauses.push(vs_clause);
    }

    fn generate_supportedness_clauses(&mut self, r_var: usize) {
        // For each bit variable v_i
        for (i, &v_i) in self.v_vars.iter().enumerate() {
            let mut clause1 = vec![-(r_var as isize), v_i as isize];
            let mut clause2 = vec![-(r_var as isize), -(v_i as isize)];
            // Collect literals where bit i is 0 or 1
            let mut literals_with_bit0 = Vec::new();
            let mut literals_with_bit1 = Vec::new();
            for (lit, _) in self.literals {
                let bits = &self.bitstrings[&lit];
                if bits[i] {
                    literals_with_bit1.push(lit);
                } else {
                    literals_with_bit0.push(lit);
                }
            }
            clause1.extend(literals_with_bit0);
            clause2.extend(literals_with_bit1);
            self.clauses.push(clause1);
            self.clauses.push(clause2);
        }
        // Add clause: not r_i \/ (l' for all body literals)
        let mut l_primes_clause = vec![-(r_var as isize)];
        for &l_prime in self.l_prime_vars.values() {
            l_primes_clause.push(l_prime as isize);
        }
        self.clauses.push(l_primes_clause);
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
    program.assign_rule_vars();
    let clauses = program.generate_clauses();
    let total_vars = program.total_variables();

    // Output DIMACS CNF format
    println!("p cnf {} {}", total_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            print!("{} ", lit);
        }
        println!("0");
    }
}
