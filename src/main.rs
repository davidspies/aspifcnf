use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};

/// Represents a rule in the ASP program.
#[derive(Debug)]
struct Rule {
    head_type: HeadType,
    head_atoms: Vec<usize>,
    body_literals: Vec<Literal>,
    rule_var: Option<usize>,
}

/// Represents the type of the rule head.
#[derive(Debug, PartialEq)]
enum HeadType {
    Disjunction,
    Choice,
}

/// Represents a literal, which can be positive or negative.
#[derive(Debug, Clone, Copy)]
struct Literal(isize);

impl Literal {
    fn new(value: isize) -> Self {
        Self(value)
    }

    fn negate(self) -> Self {
        Self(-self.0)
    }

    fn value(self) -> isize {
        self.0
    }
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

    fn add_atom(&mut self, name: &str, var: usize) {
        self.atom_to_var.insert(name.to_string(), var);
        self.var_to_atom.insert(var, name.to_string());
        self.atoms.insert(var);
    }

    fn add_literal(&mut self, lit: isize) {
        self.atoms.insert(lit.abs() as usize);
    }

    fn max_atom_var(&self) -> usize {
        *self.atoms.iter().max().unwrap_or(&0)
    }

    fn atoms(&self) -> &HashSet<usize> {
        &self.atoms
    }
}

/// Represents the entire ASP program.
struct ASPProgram {
    rules: Vec<Rule>,
    atom_table: AtomTable,
    atom_rule_vars: HashMap<usize, Vec<usize>>,
}

impl ASPProgram {
    fn new() -> Self {
        Self {
            rules: Vec::new(),
            atom_table: AtomTable::new(),
            atom_rule_vars: HashMap::new(),
        }
    }

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
        if body_type != 0 {
            panic!("Weight bodies are not supported in this implementation.");
        }
        let n = tokens[idx].parse::<usize>().unwrap(); // Number of body literals
        idx += 1;
        let mut body_literals = Vec::new();
        for _ in 0..n {
            let lit = tokens[idx].parse::<isize>().unwrap();
            self.atom_table.add_literal(lit);
            body_literals.push(Literal::new(lit));
            idx += 1;
        }
        let rule = Rule {
            head_type,
            head_atoms,
            body_literals,
            rule_var: None,
        };
        self.rules.push(rule);
    }

    fn parse_output(&mut self, tokens: &[&str]) {
        let _m = tokens[0].parse::<usize>().unwrap();
        let s = tokens[1];
        let _n = tokens[2].parse::<usize>().unwrap();
        let l = tokens[3].parse::<usize>().unwrap(); // Atom variable number
        self.atom_table.add_atom(s, l);
    }

    fn assign_rule_vars(&mut self) {
        let mut rule_var_counter = self.atom_table.max_atom_var();
        for rule in &mut self.rules {
            if !rule.head_atoms.is_empty() {
                rule_var_counter += 1;
                rule.rule_var = Some(rule_var_counter);
                // Map head atoms to rule variables
                for &atom in &rule.head_atoms {
                    self.atom_rule_vars
                        .entry(atom)
                        .or_insert_with(Vec::new)
                        .push(rule_var_counter);
                }
            }
        }
    }

    fn generate_clauses(&self) -> Vec<Vec<isize>> {
        let mut clauses = Vec::new();

        // Normal constraints
        for rule in &self.rules {
            if rule.head_type == HeadType::Disjunction && !rule.head_atoms.is_empty() {
                let mut clause: Vec<isize> = rule
                    .head_atoms
                    .iter()
                    .map(|&a| a as isize)
                    .collect();
                for &lit in &rule.body_literals {
                    clause.push(-lit.value());
                }
                clauses.push(clause);
            }
        }

        // Constraints (rules with empty head)
        for rule in &self.rules {
            if rule.head_type == HeadType::Disjunction && rule.head_atoms.is_empty() {
                let clause: Vec<isize> = rule
                    .body_literals
                    .iter()
                    .map(|&lit| -lit.value())
                    .collect();
                clauses.push(clause);
            }
        }

        // Supportedness constraints
        for rule in &self.rules {
            if let Some(r_var) = rule.rule_var {
                for &lit in &rule.body_literals {
                    clauses.push(vec![-(r_var as isize), lit.value()]);
                }
                // If the body is empty, no constraints are needed
            }
        }

        // Atom support clauses
        for &atom_var in self.atom_table.atoms() {
            if let Some(rule_vars) = self.atom_rule_vars.get(&atom_var) {
                let mut clause = vec![-(atom_var as isize)];
                for &r_var in rule_vars {
                    clause.push(r_var as isize);
                }
                clauses.push(clause);
            }
        }

        clauses
    }

    fn total_variables(&self) -> usize {
        self.atom_table
            .atoms()
            .iter()
            .chain(self.rules.iter().filter_map(|r| r.rule_var.as_ref()))
            .cloned()
            .max()
            .unwrap_or(0)
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
