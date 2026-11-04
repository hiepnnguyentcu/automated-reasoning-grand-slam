# Chapter 5: SMT

Part 2: Core Reasoning.

## Objective

Explain how SMT solvers combine SAT search with theory reasoning across the theories used in verification.

## Proof of mastery

Trace DPLL(T) and the simplex-based arithmetic procedure by hand on unseen formulas.

## Topics

| Topic | Objective |
|---|---|
| [DPLL(T)](dpllt/) | Trace the interaction between a CDCL core and a theory solver, including theory propagation and conflict explanations. |
| [Equality and Congruence Closure](equality-and-congruence-closure/) | Decide equality with uninterpreted functions by hand using congruence closure. |
| [Arithmetic](arithmetic/) | Trace simplex for linear real arithmetic, branch and bound for integers, and explain the nonlinear case. |
| [Bit-Vectors](bit-vectors/) | Bit-blast bit-vector formulas by hand and explain word-level simplification. |
| [Arrays](arrays/) | Decide array formulas using the read-over-write axioms and lemma instantiation. |
| [Strings](strings/) | Explain the word-equation and length reasoning used in string solvers and where they remain incomplete. |
| [Theory Combination](theory-combination/) | Apply Nelson-Oppen combination by hand and state the conditions it requires. |
| [Quantifiers](quantifiers/) | Explain E-matching and model-based quantifier instantiation and their failure modes. |
| [Interpolation](interpolation/) | Compute Craig interpolants from a refutation and explain their use in verification. |
| [Industrial Solvers](industrial-solvers/) | Use Z3 and cvc5 through SMT-LIB and explain their main architectural choices. |

## Main materials

- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition.
- Bradley and Manna, The Calculus of Computation.
- [Bjørner, de Moura, Nachmanson and Wintersteiger, Programming Z3.](https://theory.stanford.edu/~nikolaj/programmingz3.html)
