use std::collections::{HashMap, VecDeque};

type BVar = i32;

#[derive(Debug, Clone)]
enum DIMACSOutput {
    Sat(Vec<i32>),
    Unsat,
}

// Using structs instead of tuples for readability
// Same mem layout as for tuples:
// - https://doc.rust-lang.org/reference/type-layout.html#tuple-layout
// - https://doc.rust-lang.org/reference/types/struct.html#structtype
struct Clause<'a> {
    sat_by_var: BVar,
    vars: &'a Vec<BVar>,
    unassign_vars: u8,
}

struct Variable {
    val: bool,
    is_free: bool,
}

struct Assignment {
    var: BVar,
    val: bool,
    forced: bool,
}

fn solve(input: Vec<Vec<i32>>) -> DIMACSOutput {
    // Using HashMaps due to better get(i) / append complexity, see https://doc.rust-lang.org/std/collections/#sequences
    let mut clauses = HashMap::new();
    let mut neg_occ = HashMap::new();
    let mut pos_occ = HashMap::new();
    let mut lit_val = HashMap::new();
    // Using VecDaque for better push_front complexity
    let mut unit_queue = VecDeque::new();
    let mut assignment_stack: Vec<Assignment> = Vec::new();

    // * read formula
    // Using iterators where possible for better performance
    input.iter().enumerate().for_each(|(c, vars)| {
        let clause = Clause {
            sat_by_var: 0,
            vars: &vars,
            unassign_vars: vars.len() as u8,
        };
        let fist_var = &clause.vars[0];
        clauses.insert(c, clause);
        if vars.len() == 1 {
            unit_queue.push_front(*fist_var);
        }
        vars.iter().for_each(|literal| {
            let lit = literal.abs();
            lit_val.insert(
                lit,
                Variable {
                    val: false,
                    is_free: true,
                },
            );
            match literal.signum() {
                // TODO: Is it neccessary to check whether a variable occurs twice in same pol. in a clause?
                // When not checking clauses like (a \/ -a \/ ...) would not be taken into account.
                1 => pos_occ
                    .entry(lit)
                    .and_modify(|clauses: &mut Vec<usize>| clauses.push(c))
                    .or_insert(vec![c]),
                -1 => neg_occ
                    .entry(lit)
                    .and_modify(|clauses: &mut Vec<usize>| clauses.push(c))
                    .or_insert(vec![c]),
                _ => panic!("0 is not a valid Variable in the DIMACS format"),
            };
        })
    });

    // * unit propagation
    let unsat = unit_prop(
        &mut unit_queue,
        &mut clauses,
        &mut assignment_stack,
        &mut lit_val,
        &mut pos_occ,
        &mut neg_occ,
    );
    if unsat {
        return DIMACSOutput::Unsat;
    }

    loop {
        // * choose literal var
        let (var, val) = choose_literal(
            &mut clauses,
            &mut assignment_stack,
            &mut lit_val,
            &mut unit_queue,
        );
        // * set value var
        set_var(
            var,
            false,
            val,
            &mut unit_queue,
            &mut clauses,
            &mut assignment_stack,
            &mut lit_val,
            &mut pos_occ,
            &mut neg_occ,
        );

        // * unit propagation
        loop {
            let conflict = unit_prop(
                &mut unit_queue,
                &mut clauses,
                &mut assignment_stack,
                &mut lit_val,
                &mut pos_occ,
                &mut neg_occ,
            );
            if !conflict {
                break;
            };

            // * if conflict detected
            let unsat = backtrack(
                &mut clauses,
                &mut assignment_stack,
                &mut lit_val,
                &mut unit_queue,
                &mut pos_occ,
                &mut neg_occ,
            );
            if unsat {
                return DIMACSOutput::Unsat;
            }
        }

        // * if all clauses satisfied
        if clauses.values().fold(true, |i, c| i && c.sat_by_var != 0) {
            return DIMACSOutput::Sat(vec![]);
        }
    }
}

fn backtrack(
    clauses: &mut HashMap<usize, Clause>,
    assignment_stack: &mut Vec<Assignment>,
    lit_val: &mut HashMap<i32, Variable>,
    unit_queue: &mut VecDeque<i32>,
    pos_occ: &mut HashMap<i32, Vec<usize>>,
    neg_occ: &mut HashMap<i32, Vec<usize>>,
) -> bool {
    let mut last_step = assignment_stack.pop();
    while last_step.as_ref().is_some_and(|step| step.forced) {
        unset_var(last_step.unwrap().var, clauses, lit_val, pos_occ, neg_occ);
        last_step = assignment_stack.pop();
    }
    if last_step.is_none() {
        return true;
    }
    let var = last_step.as_ref().unwrap().var;
    let val = last_step.unwrap().val;
    unset_var(var, clauses, lit_val, pos_occ, neg_occ);
    unit_queue.clear();
    set_var(
        var,
        true,
        !val,
        unit_queue,
        clauses,
        assignment_stack,
        lit_val,
        pos_occ,
        neg_occ,
    );
    false
}

// TODO: @Laura hier können die Heuristiken rein. Gerne auch mit enum flag welche an/aus sind.
fn choose_literal(
    clauses: &mut HashMap<usize, Clause>,
    assignment_stack: &mut Vec<Assignment>,
    lit_val: &mut HashMap<i32, Variable>,
    unit_queue: &mut VecDeque<i32>,
) -> (i32, bool) {
    let arbitrary_unset_var = lit_val.iter().find(|v| v.1.is_free);
    (
        *arbitrary_unset_var.unwrap().0,
        arbitrary_unset_var.unwrap().1.val,
    )
}

fn unit_prop(
    unit_queue: &mut VecDeque<i32>,
    clauses: &mut HashMap<usize, Clause>,
    assignment_stack: &mut Vec<Assignment>,
    lit_val: &mut HashMap<i32, Variable>,
    pos_occ: &mut HashMap<i32, Vec<usize>>,
    neg_occ: &mut HashMap<i32, Vec<usize>>,
) -> bool {
    while !unit_queue.is_empty() {
        let forced_lit = unit_queue.pop_back().unwrap();
        // mark all clauses with pos_occ as sat
        let unsat = set_var(
            forced_lit,
            true,
            forced_lit.is_positive(),
            unit_queue,
            clauses,
            assignment_stack,
            lit_val,
            pos_occ,
            neg_occ,
        );
        if unsat {
            return true;
        }
    }
    false
}

fn set_var(
    var: BVar,
    forced: bool,
    val: bool,
    unit_queue: &mut VecDeque<i32>,
    clauses: &mut HashMap<usize, Clause>,
    assignment_stack: &mut Vec<Assignment>,
    lit_val: &mut HashMap<i32, Variable>,
    pos_occ: &mut HashMap<i32, Vec<usize>>,
    neg_occ: &mut HashMap<i32, Vec<usize>>,
) -> bool {
    assignment_stack.push(Assignment { var, val, forced });
    let mut conflict = false;
    let mut lit = lit_val.get_mut(&var.abs()).unwrap();
    lit.is_free = false;
    // -1 true => 1 false
    // -1 false => 1 true
    // 1 true => 1 true
    // 1 false => 1 false
    // <=> var.is_pos == value
    let new_val = val == var.is_positive();
    lit.val = new_val;
    // mark all clauses with pos_occ as sat
    // -1 true => neg_occ is sat
    // -1 false => pos_occ is sat
    // 1 true => pos_occ is sat
    // 1 false => neg_occ is sat
    // <=> var.is_pos == value
    let (mark_sat, mark_unsat) = match new_val {
        true => (pos_occ, neg_occ),
        false => (neg_occ, pos_occ),
    };
    mark_sat
        .get(&var.abs())
        .unwrap()
        .iter()
        .for_each(|c: &usize| {
            clauses.entry(*c).and_modify(|sat_clause| {
                if sat_clause.sat_by_var == 0 {
                    sat_clause.sat_by_var = var;
                }
            });
        });
    for c in mark_unsat.get(&var.abs()).unwrap() {
        let unsat_clause = clauses.get_mut(c).unwrap();
        unsat_clause.unassign_vars = unsat_clause.unassign_vars - 1;
        match unsat_clause.unassign_vars {
            0 => conflict = true,
            1 => {
                if let Some(free_lit) = unsat_clause
                    .vars
                    .iter()
                    .find(|&v| lit_val.get(&v.abs()).unwrap().is_free && !unit_queue.contains(v))
                {
                    unit_queue.push_front(*free_lit);
                }
            }
            _ => continue,
        };
    }
    conflict
}

fn unset_var(
    var: BVar,
    clauses: &mut HashMap<usize, Clause>,
    lit_val: &mut HashMap<i32, Variable>,
    pos_occ: &mut HashMap<i32, Vec<usize>>,
    neg_occ: &mut HashMap<i32, Vec<usize>>,
) {
    let mut lit_var = lit_val.get_mut(&var.abs()).unwrap();
    lit_var.is_free = true;
    // Value of lit_var actually doesn't matter
    let (mark_sat, mark_unsat) = match lit_var.val {
        true => (pos_occ, neg_occ),
        false => (neg_occ, pos_occ),
    };
    mark_sat.get(&var.abs()).unwrap().iter().for_each(|c| {
        clauses.entry(*c).and_modify(|sat_clause| {
            if sat_clause.sat_by_var == var {
                sat_clause.sat_by_var = 0;
            }
        });
    });
    for c in mark_unsat.get(&var.abs()).unwrap() {
        let unsat_clause = clauses.get_mut(c).unwrap();
        unsat_clause.unassign_vars = unsat_clause.unassign_vars + 1;
    }
}

#[test]
fn should_solve_sat_small() {
    let res = solve(vec![vec![1, -2, 3], vec![-1, 2], vec![-1, -2, -3]]);
    if let DIMACSOutput::Unsat = res {
        panic!("Was UNSAT but expected SAT.")
    }
}

#[test]
fn should_solve_sat() {
    let res = solve(vec![
        vec![1, 2, 3],
        vec![1, 2, 4],
        vec![1, 3, 4],
        vec![2, 3, 4],
        vec![-1, -2, -3],
        vec![-1, -2, -4],
        vec![-1, -3, -4],
        vec![-2, -3, -4],
        vec![1, 2, 5],
        vec![1, 2, 6],
        vec![1, 5, 6],
        vec![2, 5, 6],
        vec![-1, -2, -5],
        vec![-1, -2, -6],
        vec![-1, -5, -6],
        vec![-2, -5, -6],
        vec![3, 4, 7],
        vec![3, 4, 8],
        vec![3, 7, 8],
        vec![4, 7, 8],
        vec![-3, -4, -7],
        vec![-3, -4, -8],
        vec![-3, -7, -8],
        vec![-4, -7, -8],
        vec![5, 6, 7],
        vec![5, 6, 8],
        vec![5, 7, 8],
        vec![6, 7, 8],
        vec![-5, -6, -7],
        vec![-5, -6, -8],
        vec![-5, -7, -8],
        vec![-6, -7, -8],
        vec![3, 4],
        vec![1, 2],
        vec![5, 6],
    ]);
    if let DIMACSOutput::Unsat = res {
        panic!("Was UNSAT but expected SAT.")
    }
}

#[test]
fn should_solve_unsat_small() {
    let res = solve(vec![
        vec![1, -2, 3],
        vec![-1, 2],
        vec![-1, -2, -3],
        vec![1],
        vec![2],
        vec![3],
    ]);
    if let DIMACSOutput::Sat(_) = res {
        panic!("Was SAT but expected UNSAT.")
    }
}

#[test]
fn should_solve_unsat() {
    let res = solve(vec![
        vec![1, 2],
        vec![-1, -2],
        vec![3, 4, 5],
        vec![3, 4, 6],
        vec![3, 5, 6],
        vec![4, 5, 6],
        vec![-3, -4, -5],
        vec![-3, -4, -6],
        vec![-3, -5, -6],
        vec![-4, -5, -6],
        vec![3, 4, 7],
        vec![3, 4, 8],
        vec![3, 7, 8],
        vec![4, 7, 8],
        vec![-3, -4, -7],
        vec![-3, -4, -8],
        vec![-3, -7, -8],
        vec![-4, -7, -8],
        vec![5, 6, 9],
        vec![5, 6, 10],
        vec![5, 9, 10],
        vec![6, 9, 10],
        vec![-5, -6, -9],
        vec![-5, -6, -10],
        vec![-5, -9, -10],
        vec![-6, -9, -10],
        vec![1, 2, 9, 10],
        vec![1, 2, 9, 11],
        vec![1, 2, 9, 12],
        vec![1, 2, 10, 11],
        vec![1, 2, 10, 12],
        vec![1, 2, 11, 12],
        vec![1, 9, 10, 11],
        vec![1, 9, 10, 12],
        vec![1, 9, 11, 12],
        vec![1, 10, 11, 12],
        vec![2, 9, 10, 11],
        vec![2, 9, 10, 12],
        vec![2, 9, 11, 12],
        vec![2, 10, 11, 12],
        vec![9, 10, 11, 12],
        vec![-1, -2, -9, -10],
        vec![-1, -2, -9, -11],
        vec![-1, -2, -9, -12],
        vec![-1, -2, -10, -11],
        vec![-1, -2, -10, -12],
        vec![-1, -2, -11, -12],
        vec![-1, -9, -10, -11],
        vec![-1, -9, -10, -12],
        vec![-1, -9, -11, -12],
        vec![-1, -10, -11, -12],
        vec![-2, -9, -10, -11],
        vec![-2, -9, -10, -12],
        vec![-2, -9, -11, -12],
        vec![-2, -10, -11, -12],
        vec![-9, -10, -11, -12],
        vec![7, 8, 11],
        vec![7, 8, 12],
        vec![7, 11, 12],
        vec![8, 11, 12],
        vec![-7, -8, -11],
        vec![-7, -8, -12],
        vec![-7, -11, -12],
        vec![-8, -11, -12],
        vec![-1, -3],
        vec![-1, -4],
        vec![-2, -3],
        vec![-2, -4],
        vec![1, 2],
    ]);
    if let DIMACSOutput::Sat(_) = res {
        panic!("Was SAT but expected UNSAT.")
    }
}
