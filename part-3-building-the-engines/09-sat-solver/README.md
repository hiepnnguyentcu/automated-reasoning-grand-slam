# Chapter 9: SAT Solver

Part 3: Building the Engines.

## Objective

Build a competitive CDCL solver in Rust that produces checkable proofs.

## Proof of mastery

Solve SAT Competition benchmarks with every unsatisfiable result confirmed by an independent proof checker.

## Topics

| Topic | Objective |
|---|---|
| [Rust Foundations](rust-foundations/) | Write idiomatic and fast Rust, including ownership, unsafe boundaries and profiling. |
| [Solver Data Structures](solver-data-structures/) | Implement a DIMACS parser, a compact clause arena, watched literals and a decision heap. |
| [CDCL Core](cdcl-core/) | Implement propagation, first-UIP conflict analysis, clause minimization and backjumping. |
| [Heuristics](heuristics/) | Implement and measure VSIDS, phase saving, restarts and clause deletion. |
| [Inprocessing](inprocessing/) | Add variable elimination and subsumption and measure their effect on benchmarks. |
| [Proof Output](proof-output/) | Emit DRAT proofs and validate every unsatisfiable answer with DRAT-trim. |
| [Fuzzing and Testing](fuzzing-and-testing/) | Find solver bugs with fuzzing, delta debugging and comparison against reference solvers. |
| [Benchmarking](benchmarking/) | Compare the solver with MiniSat and CaDiCaL on competition benchmarks under reliable conditions. |

## Main materials

- Eén and Sörensson, An Extensible SAT-solver, SAT 2003.
- [MiniSat source repository.](https://github.com/niklasso/minisat)
- [CaDiCaL source repository.](https://github.com/arminbiere/cadical)
- [Klabnik and Nichols, The Rust Programming Language.](https://doc.rust-lang.org/book/)
