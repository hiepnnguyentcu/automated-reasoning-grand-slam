# Part 3: Building the Engines

## Objective

Turn the concepts from Part 2 into working, tested and benchmarked reasoning tools in Rust and OCaml.

Building begins in this part, and each tool is judged against public benchmarks and existing tools.

## Chapters

| # | Chapter | Objective | Proof of mastery |
|--:|---|---|---|
| 9 | [SAT Solver](09-sat-solver/) | Build a competitive CDCL solver in Rust that produces checkable proofs. | Solve SAT Competition benchmarks with every unsatisfiable result confirmed by an independent proof checker. |
| 10 | [SMT Solver](10-smt-solver/) | Build an SMT solver on top of the SAT solver for equality, linear arithmetic and bit-vectors. | Pass differential testing against Z3 and cvc5 on SMT-LIB benchmarks in the supported logics. |
| 11 | [Model Checker](11-model-checker/) | Build a model checker on the solvers from Chapters 9 and 10, including IC3. | Report verified results on Hardware Model Checking Competition benchmarks. |
