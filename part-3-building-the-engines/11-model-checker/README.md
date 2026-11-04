# Chapter 11: Model Checker

Part 3: Building the Engines.

## Objective

Build a model checker on the solvers from Chapters 9 and 10, including IC3.

## Proof of mastery

Report verified results on Hardware Model Checking Competition benchmarks.

## Topics

| Topic | Objective |
|---|---|
| [Input Formats](input-formats/) | Parse AIGER and Btor2 models into a transition system representation. |
| [BMC and K-Induction](bmc-and-k-induction/) | Implement incremental bounded model checking and k-induction on your solver. |
| [IC3 Implementation](ic3-implementation/) | Implement IC3 with inductive generalization and counterexample output. |
| [Certificates](certificates/) | Output invariants and counterexamples and validate them independently of the checker. |
| [Benchmarking](benchmarking/) | Compare the checker with ABC on competition benchmarks and explain the differences. |

## Main materials

- Bradley, SAT-Based Model Checking without Unrolling, VMCAI 2011.
- Eén, Mishchenko and Brayton, Efficient implementation of property directed reachability, FMCAD 2011.
- [Hardware Model Checking Competition.](https://hwmcc.github.io/)
