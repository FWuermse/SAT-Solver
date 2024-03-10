use std::collections::{HashMap, HashSet};

use crate::{dpll::Literal, implication_graph::ImplicationGraph};

pub(crate) fn arbitrary(free_lits: &HashSet<i32>) -> (i32, bool) {
    match free_lits.iter().next() {
        Some(&lit) => (lit, true),
        None => (0, true),
    }
}

// DLIS:  picks the variable that appears in the largest number of unsatisfied clauses,
// aiming to quickly reduce the search space
pub(crate) fn dlis(
    free_lits: &HashSet<i32>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    // Create a map to count the occurrences of each variable in unsatisfied clauses
    let mut var_occurrences: HashMap<i32, usize> = HashMap::new();

    // Iterate over all unsatisfied clauses
    for (clause, _) in unsat_clauses {
        for &var in clause {
            let abs_var = var.abs();
            if free_lits.contains(&abs_var) || free_lits.contains(&-abs_var) {
                // Increment the count for this variable
                *var_occurrences.entry(var).or_insert(0) += 1;
            }
        }
    }

    // Find the variable with the highest occurrence count
    let mut max_var = 0;
    let mut max_count = 0;
    for (&var, &count) in var_occurrences.iter() {
        if count > max_count {
            max_var = var;
            max_count = count;
        }
    }

    // If no variable was found, return a default value
    if max_var == 0 {
        return (*free_lits.iter().next().unwrap(), true);
    }

    // The value to assign is true if the variable appears more often positively
    let val = max_var > 0;
    (max_var.abs(), val)
}

// DLCS: chooses the variable that appears the most in the unsatisfied clauses,
// counting both its positive and negative occurrences.
// It's similar to DLIS but considers both polarities of the variable.
pub(crate) fn dlcs(
    free_lits: &HashSet<i32>,
    _lit_val: &HashMap<u16, Literal>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    let mut var_occurrences: HashMap<i32, usize> = HashMap::new();

    for (clause, _) in unsat_clauses {
        for &var in clause {
            let abs_var = var.abs();
            if free_lits.contains(&abs_var) {
                *var_occurrences.entry(abs_var).or_insert(0) += 1;
            }
        }
    }

    let &max_var = var_occurrences
        .iter()
        .max_by_key(|entry| entry.1)
        .map(|(var, _)| var)
        .unwrap_or(&0);
    if max_var == 0 {
        return (*free_lits.iter().next().unwrap(), true);
    }

    let val = true; // Default assignment
    (max_var, val)
}

// MOM:  selects a variable from the smallest unsatisfied clauses.
// Within these clauses, it picks the variable that occurs the most frequently.
// This heuristic focuses on resolving smaller clauses first, as they are closer to causing conflicts.
pub(crate) fn mom(
    free_lits: &HashSet<i32>,
    _lit_val: &HashMap<u16, Literal>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    let min_clause_size = unsat_clauses
        .iter()
        .map(|(_, size)| *size)
        .min()
        .unwrap_or(0);
    let mut var_occurrences: HashMap<i32, usize> = HashMap::new();

    for (clause, size) in unsat_clauses {
        if *size == min_clause_size {
            for &var in clause {
                if free_lits.contains(&var.abs()) {
                    *var_occurrences.entry(var.abs()).or_insert(0) += 1;
                }
            }
        }
    }

    let &max_var = var_occurrences
        .iter()
        .max_by_key(|entry| entry.1)
        .map(|(var, _)| var)
        .unwrap_or(&0);
    if max_var == 0 {
        return (*free_lits.iter().next().unwrap(), true);
    }

    let val = true; // Default assignment
    (max_var, val)
}

// Boehm: is a variation of MOM.
// It includes a bias term to favor variables appearing in smaller clauses.
// This term is usually a power of the number of occurrences of the variable in small clauses.
pub(crate) fn boehm(
    free_lits: &HashSet<i32>,
    _lit_val: &HashMap<u16, Literal>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    let min_clause_size = unsat_clauses
        .iter()
        .map(|(_, size)| *size)
        .min()
        .unwrap_or(0);
    let mut var_occurrences: HashMap<i32, usize> = HashMap::new();

    for (clause, size) in unsat_clauses {
        if *size == min_clause_size {
            for &var in clause {
                if free_lits.contains(&var.abs()) {
                    *var_occurrences.entry(var.abs()).or_insert(0) +=
                        2usize.pow(min_clause_size as u32); // Bias term
                }
            }
        }
    }

    let &max_var = var_occurrences
        .iter()
        .max_by_key(|entry| entry.1)
        .map(|(var, _)| var)
        .unwrap_or(&0);
    if max_var == 0 {
        return (*free_lits.iter().next().unwrap(), true);
    }

    let val = true; // Default assignment
    (max_var, val)
}

// Jeroslaw-Wang: calculates a score for each variable based on its appearances in the clauses.
// The score of a literal in a clause is 2^(-clause_size).
// The total score for a variable is the sum of the scores of its literals.
pub(crate) fn jeroslaw_wang(
    free_lits: &HashSet<i32>,
    _lit_val: &HashMap<u16, Literal>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    let mut scores: HashMap<i32, f64> = HashMap::new();

    for (clause, size) in unsat_clauses {
        let score = 2f64.powf(-(*size as f64));
        for &var in clause {
            if free_lits.contains(&var.abs()) {
                *scores.entry(var.abs()).or_insert(0.0) += score;
            }
        }
    }

    let &max_var = scores
        .iter()
        .max_by(|a, b| a.1.partial_cmp(b.1).unwrap())
        .map(|(var, _)| var)
        .unwrap_or(&0);
    if max_var == 0 {
        return (*free_lits.iter().next().unwrap(), true);
    }

    let val = true; // Default assignment
    (max_var, val)
}

// VSIDS
pub(crate) fn vsids(
    free_lits: &HashSet<i32>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    let mut scores: HashMap<i32, f64> = HashMap::new();

    for (clause, _) in unsat_clauses {
        for &var in clause {
            if free_lits.contains(&var.abs()) {
                *scores.entry(var.abs()).or_insert(0.0) += 1.0;
            }
        }
    }

    let &max_var = scores
        .iter()
        .max_by(|a, b| a.1.partial_cmp(b.1).unwrap())
        .map(|(var, _)| var)
        .unwrap_or(&0);
    if max_var == 0 {
        return (*free_lits.iter().next().unwrap(), true);
    }

    let val = true; // Default assignment
    (max_var, val)
}

// VMTF: Selects the last variable involved in a conflict
pub(crate) fn vmtf(
    free_lits: &HashSet<i32>,
    learned_clauses: &Vec<Vec<i32>>,
) -> (i32, bool) {
    let mut lit_counters: HashMap<i32, usize> = HashMap::new();

    // Counts only free literals in the learned clauses
    for clause in learned_clauses.iter() {
        for &lit in clause {
            let lit_abs = lit.abs();
            if free_lits.contains(&lit_abs) {
                *lit_counters.entry(lit_abs).or_insert(0) += 1;
            }
        }
    }

    // Sorts the free literals based on their frequency
    let mut sorted_lits: Vec<(i32, usize)> = lit_counters.into_iter().collect();
    sorted_lits.sort_by_key(|k| std::cmp::Reverse(k.1));

    // Selects the first literal in the sorted list
    if let Some((lit, _)) = sorted_lits.first() {
        return (*lit, true);
    }

    //Fallback
    arbitrary(free_lits)
}

// BerkMin: Selects a variable from the most recent unsatisfied clause
pub(crate) fn berkmin(
    implication_graph: &ImplicationGraph,
    free_lits: &HashSet<i32>,
) -> (i32, bool) {
    if let Ok(conflict_node) = implication_graph.get_conflict_node() {
       // Filters only the free predecessors of the conflict node
        let conflict_literals: Vec<i32> = conflict_node.predecessors.iter()
            .filter_map(|&lit| {
                let lit_abs = lit.abs();
                if free_lits.contains(&lit_abs) {
                    Some(lit)
                } else {
                    None
                }
            })
            .collect();

        // Selects the literal with the highest priority
        if let Some(&selected_lit) = conflict_literals.iter().max_by_key(|&lit| {
            implication_graph.0.get(&lit.abs()).map_or(0, |node| node.predecessors.len())
        }) {
            return (selected_lit.abs(), selected_lit > 0);
        }
    }

    // Fallback if no suitable literal is found or there is no conflict
    arbitrary(free_lits)
}



// Custom: Least number of clauses: selects the variable that appears in the smallest number of clauses.
pub(crate) fn custom(
    free_lits: &HashSet<i32>,
    unsat_clauses: &HashSet<(Vec<i32>, u8)>,
) -> (i32, bool) {
    let mut scores: HashMap<i32, usize> = HashMap::new();

    for (clause, _) in unsat_clauses {
        for &var in clause {
            if free_lits.contains(&var.abs()) {
                *scores.entry(var.abs()).or_insert(0) += 1;
            }
        }
    }

    let &min_var = scores
        .iter()
        .min_by(|a, b| a.1.cmp(b.1))
        .map(|(var, _)| var)
        .unwrap_or(&0);
    let val = true; // Default assignment
    (min_var, val)
}
