use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};

#[derive(Debug)]
struct Rule {
    head_type: u8,       // h ∈ {0, 1}
    head_atoms: Vec<usize>,
    body_literals: Vec<isize>,
    rule_var: Option<usize>,
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

    // Atom mappings
    let mut atom_to_var: HashMap<String, usize> = HashMap::new();
    let mut var_to_atom: HashMap<usize, String> = HashMap::new();

    // Rules
    let mut rules: Vec<Rule> = Vec::new();

    // Map from atom to rule variables that have it in their head
    let mut atom_rule_vars: HashMap<usize, Vec<usize>> = HashMap::new();

    // Set of atoms
    let mut atoms: HashSet<usize> = HashSet::new();

    // Read the ASPIF file line by line
    for line_result in input.lines() {
        let line = line_result.expect("Failed to read line");
        let line = line.trim();
        if line.is_empty() || line.starts_with('%') || line.starts_with('0') {
            continue;
        }

        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        match tokens[0] {
            "1" => {
                // Rule statement
                let mut idx = 1;
                let h = tokens[idx].parse::<u8>().unwrap();
                idx += 1;
                let m = tokens[idx].parse::<usize>().unwrap();
                idx += 1;
                let mut head_atoms = Vec::new();
                for _ in 0..m {
                    let atom = tokens[idx].parse::<usize>().unwrap();
                    atoms.insert(atom);
                    head_atoms.push(atom);
                    idx += 1;
                }
                let body_type = tokens[idx].parse::<u8>().unwrap();
                idx += 1;
                if body_type != 0 {
                    panic!("Weight bodies are not supported in this implementation.");
                }
                let n = tokens[idx].parse::<usize>().unwrap();
                idx += 1;
                let mut body_literals = Vec::new();
                for _ in 0..n {
                    let lit = tokens[idx].parse::<isize>().unwrap();
                    atoms.insert(lit.abs() as usize);
                    body_literals.push(lit);
                    idx += 1;
                }
                let rule = Rule {
                    head_type: h,
                    head_atoms,
                    body_literals,
                    rule_var: None,
                };
                rules.push(rule);
            }
            "4" => {
                // Output statement: atom mapping
                let m = tokens[1].parse::<usize>().unwrap();
                let s = tokens[2];
                let n = tokens[3].parse::<usize>().unwrap();
                let l = tokens[4].parse::<usize>().unwrap(); // The atom's variable number
                atom_to_var.insert(s.to_string(), l);
                var_to_atom.insert(l, s.to_string());
                atoms.insert(l);
            }
            _ => {
                // Other statements are ignored in this implementation
                continue;
            }
        }
    }

    // Total number of atoms (variables corresponding to atoms)
    let max_atom_var = *atoms.iter().max().unwrap_or(&0);

    // Assign rule variables to rules with non-empty head
    let mut rule_var_counter = max_atom_var;
    for rule in &mut rules {
        if !rule.head_atoms.is_empty() {
            rule_var_counter += 1;
            rule.rule_var = Some(rule_var_counter);
            // For each head atom, add this rule variable to the list
            for &atom in &rule.head_atoms {
                atom_rule_vars
                    .entry(atom)
                    .or_insert_with(Vec::new)
                    .push(rule_var_counter);
            }
        }
    }

    // Collect clauses
    let mut clauses: Vec<Vec<isize>> = Vec::new();

    // For each basic rule (h=0, m>0), generate normal constraint clause
    for rule in &rules {
        if rule.head_type == 0 && !rule.head_atoms.is_empty() {
            // Basic rule
            let mut clause: Vec<isize> = rule.head_atoms.iter().map(|&a| a as isize).collect();
            for &lit in &rule.body_literals {
                clause.push(-lit);
            }
            clauses.push(clause);
        }
    }

    // For constraints (rules with empty head), generate clauses ¬body
    for rule in &rules {
        if rule.head_type == 0 && rule.head_atoms.is_empty() {
            // Constraint
            let clause: Vec<isize> = rule
                .body_literals
                .iter()
                .map(|&lit| -lit)
                .collect();
            clauses.push(clause);
        }
    }

    // For supportedness constraints
    // For each rule with non-empty head, add constraints ¬r ∨ l for each body literal l
    for rule in &rules {
        if let Some(r_var) = rule.rule_var {
            for &lit in &rule.body_literals {
                clauses.push(vec![-(r_var as isize), lit]);
            }
            // If the body is empty, we need to ensure the rule variable is not false due to missing body literals
            if rule.body_literals.is_empty() {
                // No body literals, so the rule variable is always true (no constraints needed)
            }
        }
    }

    // For each atom, add clause ¬a ∨ r1 ∨ r2 ∨ ...
    for &atom_var in &atoms {
        if let Some(rule_vars) = atom_rule_vars.get(&atom_var) {
            let mut clause = vec![-(atom_var as isize)];
            for &r_var in rule_vars {
                clause.push(r_var as isize);
            }
            clauses.push(clause);
        }
    }

    // Total variables
    let total_vars = rule_var_counter;

    // Output DIMACS CNF format
    println!("p cnf {} {}", total_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            print!("{} ", lit);
        }
        println!("0");
    }
}
