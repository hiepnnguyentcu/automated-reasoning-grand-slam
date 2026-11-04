# Chapter 4: SAT

Part 2: Core Reasoning.

## Objective

Explain how modern SAT solvers work and why each major technique improves them.

## Proof of mastery

Trace CDCL by hand on an unseen formula, including conflict analysis and the resulting learned clauses.

## Topics

| Topic | Objective |
|---|---|
| [Encodings](encodings/) | Encode combinatorial and verification problems into CNF, including with the Tseitin transformation and cardinality constraints. |
| [Resolution and DPLL](resolution-and-dpll/) | Trace resolution, Davis-Putnam and DPLL by hand and compare their behavior. |
| [CDCL](cdcl/) | Trace clause learning, implication graphs, first-UIP analysis and backjumping by hand. |
| [Heuristics and Restarts](heuristics-and-restarts/) | Explain watched literals, VSIDS, phase saving, restarts and clause deletion and the evidence for each. |
| [Preprocessing and Inprocessing](preprocessing-and-inprocessing/) | Apply variable elimination, subsumption and blocked clause elimination and state what they preserve. |
| [Proofs and Certificates](proofs-and-certificates/) | Produce and check a DRAT proof for a small unsatisfiable formula by hand. |
| [Local Search](local-search/) | Explain stochastic local search and when it outperforms CDCL. |
| [MaxSAT](maxsat/) | Explain core-guided and linear-search MaxSAT algorithms and trace one on a small instance. |
| [QBF and Model Counting](qbf-and-model-counting/) | Explain how QBF solving and model counting extend SAT and why they are harder. |

## Main materials

- Biere, Heule, van Maaren and Walsh (editors), Handbook of Satisfiability, 2nd edition.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition.
- Knuth, The Art of Computer Programming, Volume 4B, the section on satisfiability.
