# Chapter 10: SMT Solver

Part 3: Building the Engines.

## Objective

Build an SMT solver on top of the SAT solver for equality, linear arithmetic and bit-vectors.

## Proof of mastery

Pass differential testing against Z3 and cvc5 on SMT-LIB benchmarks in the supported logics.

## Topics

| Topic | Objective |
|---|---|
| [OCaml Foundations](ocaml-foundations/) | Write idiomatic OCaml, including algebraic data types, modules and functors. |
| [SMT-LIB Front End](smt-lib-front-end/) | Parse, type-check and simplify SMT-LIB problems into the solver's internal terms. |
| [E-Graph and EUF](e-graph-and-euf/) | Implement congruence closure with explanations as a theory solver. |
| [Simplex for Linear Arithmetic](simplex-for-linear-arithmetic/) | Implement general simplex with exact arithmetic and conflict explanations. |
| [Bit-Blasting](bit-blasting/) | Translate bit-vector operations to CNF and add word-level rewriting. |
| [DPLL(T) Integration](dpllt-integration/) | Connect the SAT core and theory solvers with theory propagation and backtracking. |
| [Differential Testing](differential-testing/) | Find soundness bugs through differential testing and fuzzing against Z3 and cvc5. |

## Main materials

- Nieuwenhuis, Oliveras and Tinelli, Solving SAT and SAT Modulo Theories: From an abstract Davis-Putnam-Logemann-Loveland procedure to DPLL(T), JACM 2006.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition.
- [SMT-LIB standard and benchmarks.](https://smt-lib.org/)
