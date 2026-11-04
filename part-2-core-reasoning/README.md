# Part 2: Core Reasoning

## Objective

Understand the algorithms behind SAT and SMT solvers, first-order provers, program verifiers and model checkers well enough to trace them by hand.

This part is concepts only, and learning is checked with closed-book proofs and hand traces.

## Chapters

| # | Chapter | Objective | Proof of mastery |
|--:|---|---|---|
| 4 | [SAT](04-sat/) | Explain how modern SAT solvers work and why each major technique improves them. | Trace CDCL by hand on an unseen formula, including conflict analysis and the resulting learned clauses. |
| 5 | [SMT](05-smt/) | Explain how SMT solvers combine SAT search with theory reasoning across the theories used in verification. | Trace DPLL(T) and the simplex-based arithmetic procedure by hand on unseen formulas. |
| 6 | [First-Order Proving](06-first-order-proving/) | Explain how automated provers search for proofs in full first-order logic with equality. | Run saturation by hand on an unseen first-order problem and report the resulting proof. |
| 7 | [Deductive Verification](07-deductive-verification/) | Prove program correctness with program logics and reduce those proofs to solver queries. | Generate verification conditions by hand for an unseen program with loops and prove them correct. |
| 8 | [Model Checking](08-model-checking/) | Decide temporal and safety properties of systems using explicit, symbolic and SAT-based algorithms. | Trace IC3 by hand on a small transition system, including frames, generalization and propagation. |
