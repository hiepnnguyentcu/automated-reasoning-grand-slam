# Chapter 13: Static Analysis

Part 4: Remaining Methods.

## Objective

Design static analyses that are sound by construction and useful on real code.

## Proof of mastery

Build an abstract interpreter and a small symbolic executor and evaluate them on real programs.

## Topics

| Topic | Objective |
|---|---|
| [Dataflow Analysis](dataflow-analysis/) | Formulate and solve dataflow problems as fixed points over lattices. |
| [Abstract Interpretation](abstract-interpretation/) | Prove an analysis sound using Galois connections and apply widening. |
| [Numeric Domains](numeric-domains/) | Implement interval and octagon domains and compare their precision and cost. |
| [Pointer Analysis](pointer-analysis/) | Implement Andersen-style and Steensgaard-style analyses and compare them. |
| [Interprocedural Analysis and Datalog](interprocedural-analysis-and-datalog/) | Solve interprocedural problems using IFDS and Datalog-based analysis. |
| [Compositional Analysis](compositional-analysis/) | Explain bi-abduction and why compositional analysis scales to large codebases. |
| [Symbolic Execution](symbolic-execution/) | Implement a small symbolic executor and explain path explosion and concolic testing. |
| [Industrial Practice](industrial-practice/) | Explain why developers adopt or ignore analyzers and apply those lessons to tool design. |

## Main materials

- [Møller and Schwartzbach, Static Program Analysis.](https://cs.au.dk/~amoeller/spa/)
- Rival and Yi, Introduction to Static Analysis: An Abstract Interpretation Perspective.
- Nielson, Nielson and Hankin, Principles of Program Analysis.
