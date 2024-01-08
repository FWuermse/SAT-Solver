use crate::heuristsics::{arbitrary, boehm, custom, dlcs, dlis, jeroslaw_wang, mom};
use std::collections::{HashMap, HashSet, VecDeque};

type Atom = u16;
type BVar = i32;
type CIdx = usize;

#[derive(Debug, Clone)]
pub enum DIMACSOutput {
    Sat(Vec<i32>),
    Unsat,
}

// Using structs instead of tuples for readability
// Same mem layout as for tuples:
// - https://doc.rust-lang.org/reference/type-layout.html#tuple-layout
// - https://doc.rust-lang.org/reference/types/struct.html#structtype
pub(crate) struct Clause {
    pub(crate) vars: Vec<BVar>,
    pub(crate) watched: BVar,
}

pub(crate) struct Literal {
    pub(crate) val: bool,
    pub(crate) is_free: bool,
}

struct Assignment {
    var: BVar,
    val: bool,
    forced: bool,
}

pub struct CDCL {
    // Using HashMaps due to better get(i) / append complexity, see https://doc.rust-lang.org/std/collections/#sequences
    clauses: HashMap<usize, Clause>,
    history: Vec<Assignment>,
    // Memory allocation in the history is a bottle neck thus the initial unit prop and pure lit elim don't need to expand it
    history_enabled: bool,
    lit_val: HashMap<Atom, Literal>,
    min_depth: u16,
    // Keys don't contain the sign as abs is cheaper than calculating the sign every time
    neg_occ: HashMap<Atom, Vec<CIdx>>,
    pos_occ: HashMap<Atom, Vec<CIdx>>,
    // Using VecDaque for better push_front complexity
    unit_queue: VecDeque<BVar>,
}

impl CDCL {
    pub fn new(
        input: Vec<Vec<i32>>,
        lit_count: usize,
        clause_count: usize,
        heuristic: String,
        show_depth: bool,
    ) -> Self {
        let mut dpll = CDCL {
            clauses: HashMap::with_capacity(clause_count),
            history: Vec::new(),
            history_enabled: false,
            lit_val: HashMap::with_capacity(lit_count),
            min_depth: match show_depth {
                true => u16::MAX,
                false => 0,
            },
            neg_occ: HashMap::with_capacity(lit_count),
            pos_occ: HashMap::with_capacity(lit_count),
            unit_queue: VecDeque::new(),
        };
        // * read formula
        // Using iterators where possible for better performance
        input.into_iter().enumerate().for_each(|(c, vars)| {
            let fist_var = vars.clone()[0];
            let clause = Clause {
                vars: vars.clone(),
                watched: fist_var,
            };
            dpll.clauses.insert(c, clause);
            if vars.len() == 1 && !dpll.unit_queue.contains(&fist_var) {
                dpll.unit_queue.push_front(fist_var);
            }
            vars.iter().for_each(|literal| {
                let lit = literal.abs() as Atom;
                dpll.lit_val.insert(
                    lit,
                    Literal {
                        val: false,
                        is_free: true,
                    },
                );
                match literal.signum() {
                    // TODO: Is it neccessary to check whether a variable occurs twice in same pol. in a clause?
                    // When not checking clauses like (a \/ -a \/ ...) would not be taken into account.
                    1 => dpll
                        .pos_occ
                        .entry(lit)
                        .and_modify(|clauses: &mut Vec<CIdx>| clauses.push(c))
                        .or_insert(vec![c]),
                    -1 => dpll
                        .neg_occ
                        .entry(lit)
                        .and_modify(|clauses: &mut Vec<CIdx>| clauses.push(c))
                        .or_insert(vec![c]),
                    _ => panic!("0 is not a valid Variable in the DIMACS format"),
                };
            })
        });
        dpll
    }

    pub fn solve(&mut self) -> DIMACSOutput {
        // * unit propagation
        let conflict = self.unit_prop();
        if conflict {
            return DIMACSOutput::Unsat;
        }
        if self
            .clauses
            .values()
            .fold(true, |i, c| i && c.sat_by_var != 0)
        {
            let res: Vec<i32> = self
                .lit_val
                .iter()
                .map(|(atom, lit)| match lit.val {
                    true => *atom as BVar,
                    false => -(*atom as BVar),
                })
                .collect();
            return DIMACSOutput::Sat(res);
        }

        // * pure lit elim
        let mut pure_lits = self.get_pure_lits();

        loop {
            // * choose literal var
            let (var, val, forced) = match pure_lits.is_empty() {
                true => {
                    self.history_enabled = true;
                    let (var, val) = self.pick_literal();
                    (var, val, false)
                }
                false => {
                    let lit = pure_lits.pop().unwrap();
                    // As the lit occurs only in one polarity it doesn't make sense to try both assignments
                    (lit, lit.is_positive(), true)
                }
            };
            // * set value var
            self.set_var(forced, val, var);

            // * unit propagation
            loop {
                let conflict = self.unit_prop();
                if !conflict {
                    break;
                };

                // * if conflict detected
                let unsat = self.backtrack();
                if unsat {
                    return DIMACSOutput::Unsat;
                }
            }

            // * if all clauses satisfied
            if self
                .clauses
                .values()
                .fold(true, |i, c| i && c.sat_by_var != 0)
            {
                let res: Vec<i32> = self
                    .lit_val
                    .iter()
                    .map(|(atom, lit)| match lit.val {
                        true => *atom as BVar,
                        false => -(*atom as BVar),
                    })
                    .collect();
                return DIMACSOutput::Sat(res);
            }
        }
    }

    fn get_pure_lits(&self) -> Vec<BVar> {
        let neg_hs = self.neg_occ.keys().collect::<HashSet<&Atom>>();
        let pos_hs = self.pos_occ.keys().collect::<HashSet<&Atom>>();
        // neg_occ \ pos_occ
        let pure = neg_hs.difference(&pos_hs);
        pure.into_iter()
            .map(|&literal| {
                // TODO: is the sign in the unitque important?
                let sign = match neg_hs.get(literal) {
                    Some(_) => 1,
                    None => -1,
                };
                *literal as BVar * sign
            })
            .collect::<Vec<BVar>>()
    }

    fn backtrack(&mut self) -> bool {
        let mut last_step = self.history.pop();
        while last_step.as_ref().is_some_and(|step| step.forced) {
            self.unset_var(last_step.unwrap().var);
            last_step = self.history.pop();
        }
        if self.history.len() as u16 <= self.min_depth {
            self.min_depth = self.history.len() as u16;
            println!("backtracked to depth {}", self.history.len());
        }
        if last_step.is_none() {
            return true;
        }
        let var = last_step.as_ref().unwrap().var;
        let val = last_step.unwrap().val;
        self.unset_var(var);
        self.unit_queue.clear();
        self.set_var(true, !val, var);
        false
    }

    fn unit_prop(&mut self) -> bool {
        while !self.unit_queue.is_empty() {
            let forced_lit = self.unit_queue.pop_back().unwrap();
            // mark all clauses with pos_occ as sat
            let unsat = self.set_var(true, true, forced_lit);
            if unsat {
                return true;
            }
        }
        false
    }

    fn set_var(&mut self, forced: bool, val: bool, var: BVar) -> bool {
        if self.history_enabled {
            self.history.push(Assignment { var, val, forced });
        }
        let mut conflict = false;
        let lit = self.lit_val.get_mut(&(var.abs() as Atom)).unwrap();
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
            true => (&self.pos_occ, &self.neg_occ),
            false => (&self.neg_occ, &self.pos_occ),
        };
        if let Some(occ) = mark_sat.get(&(var.abs() as Atom)) {
            occ.iter().for_each(|c: &CIdx| {
                self.clauses.entry(*c).and_modify(|sat_clause| {
                    if sat_clause.sat_by_var == 0 {
                        sat_clause.sat_by_var = var;
                    }
                });
            });
        }
        if let Some(occ) = mark_unsat.get(&(var.abs() as Atom)) {
            occ.iter().for_each(|c| {
                let unsat_clause = self.clauses.get_mut(c).unwrap();
                unsat_clause.unassign_vars = unsat_clause.unassign_vars - 1;
                match unsat_clause.unassign_vars {
                    0 => conflict = true,
                    1 => {
                        if let Some(free_lit) = unsat_clause.vars.iter().find(|&v| {
                            self.lit_val.get(&(v.abs() as Atom)).unwrap().is_free
                                && !self.unit_queue.contains(v)
                        }) {
                            self.unit_queue.push_front(*free_lit);
                        }
                    }
                    _ => (),
                };
            })
        }
        conflict
    }

    fn unset_var(&mut self, var: BVar) {
        let lit_var = self.lit_val.get_mut(&(var.abs() as Atom)).unwrap();
        lit_var.is_free = true;
        // Value of lit_var actually doesn't matter
        let (mark_sat, mark_unsat) = match lit_var.val {
            true => (&self.pos_occ, &self.neg_occ),
            false => (&self.neg_occ, &self.pos_occ),
        };
        if let Some(occ) = mark_sat.get(&(var.abs() as Atom)) {
            let x = var as u16;
            occ.iter().for_each(|c| {
                self.clauses.entry(*c).and_modify(|sat_clause| {
                    if sat_clause.sat_by_var == var {
                        sat_clause.sat_by_var = 0;
                    }
                });
            })
        };
        if let Some(occ) = mark_unsat.get(&(var.abs() as Atom)) {
            occ.iter().for_each(|c| {
                let unsat_clause = self.clauses.get_mut(c).unwrap();
                unsat_clause.unassign_vars = unsat_clause.unassign_vars + 1;
            })
        }
    }
}

#[test]
fn should_solve_sat_small() {
    let res = CDCL::new(
        vec![vec![1, -2, 3], vec![-1, 2], vec![-1, -2, -3]],
        3,
        3,
        "arbitrary".to_string(),
        true,
    )
    .solve();
    if let DIMACSOutput::Unsat = res {
        panic!("Was UNSAT but expected SAT.")
    }
}

#[test]
fn should_solve_sat() {
    let res = CDCL::new(
        vec![
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
        ],
        8,
        35,
        "arbitrary".to_string(),
        true,
    )
    .solve();
    if let DIMACSOutput::Unsat = res {
        panic!("Was UNSAT but expected SAT.")
    }
}

#[test]
fn should_solve_unsat_small() {
    let res = CDCL::new(
        vec![
            vec![1, -2, 3],
            vec![-1, 2],
            vec![-1, -2, -3],
            vec![1],
            vec![2],
            vec![3],
        ],
        3,
        6,
        "arbitrary".to_string(),
        true,
    )
    .solve();
    if let DIMACSOutput::Sat(_) = res {
        panic!("Was SAT but expected UNSAT.")
    }
}

#[test]
fn should_solve_unsat() {
    let res = CDCL::new(
        vec![
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
        ],
        12,
        68,
        "arbitrary".to_string(),
        true,
    )
    .solve();
    if let DIMACSOutput::Sat(_) = res {
        panic!("Was SAT but expected UNSAT.")
    }
}

#[test]
fn should_parse_and_solve_sat() {
    let (input, v_c, c_c) =
        crate::parse::parse("./dimacs-files/input/sat/aim-50-1_6-yes1-1.cnf").unwrap();
    let res = CDCL::new(input, v_c, c_c, "arbitrary".to_string(), true).solve();
    if let DIMACSOutput::Unsat = res {
        panic!("Was UNSAT but expected SAT.")
    }
}

#[test]
fn should_parse_and_solve_unsat() {
    let (input, v_c, c_c) =
        crate::parse::parse("./dimacs-files/input/unsat/aim-50-1_6-no-1.cnf").unwrap();
    let res = CDCL::new(input, v_c, c_c, "arbitrary".to_string(), true).solve();
    if let DIMACSOutput::Sat(_) = res {
        panic!("Was UNSAT but expected SAT.")
    }
}
