# SAT-Solver

## Running the SAT-Solver

Once built via `cargo build --release` the solver can be executed the following:

`./target/release/sat [MODE] [FILEPATH] [FILEPATH] --heuristic [HEURISTIC] [FLAGS]`

### MODE

* dpll
* cdcl

### HEURISTIC

Supported heuristics are:

- arbitrary
- dlis
- dlcs
- mom
- boehm
- jeroslawwang
- vsids
- custom

### Flags

|short|long|description|
|-|-|-|
|-d|--depth|show progress when using dpll|
|-s|--subsumed_clauses|Use subsumed_clauses preprocessing|
|-f|--flamegraph|Produces a Flamegraph|
|-h|--help|Print help|
|-v|--version|Print version|

## CPU Time Measurement

To measure the CPU time for each `.cnf` file in `src/inputs`, run the `cputime` binary:

`cargo run --bin cputime --time-limit [TIME-LIMIT] --heuristic [HEURISTIC]`

### TIME-LIMIT

Time-Limit arguments:

- true: 60sec execution time frame
- false: measures the duration of the execution without timeout

## Plotting

To create the plots for the existing `.csv` files in `src/cputime`, run the `plot` binary:
`cargo run --bin plot`

## Running the tests

When cloning make sure to also sync the submodule which includes testfiles:

`git submodule update --init --recursive`

Run the tests using cargo:

`cargo test --package sat_solver --lib -- cdcl --nocapture`

# Team Responsibilities

**Noel:**

- [x] Fix issue with Conflict analysis
- [x] Subsumed Clauses
- [x] Restarts
- [ ] Drup logging

**Laura:**

- [x] Implication Graph
- [x] Conflict analysis

**Flo:**

- [x] 2-Watched Literals
- [x] Fix/Update impl. graph while setting vars
- [x] Fix/Rewrite Conflict analysis
- [x] Non-chron backtracking
- [x] Test + Debug non-chronological backtracking
- [x] Check whether unit clauses can occur in conflict analysis
- [x] Check impl for set_var in respect to unit clauses
- [x] Pure literal elimination as preprocessing
- [x] Output valid DIMACS solution
- [ ] VSIDS performance

# Our favourite Implication Graph during debugging

![](graphviz.svg)
