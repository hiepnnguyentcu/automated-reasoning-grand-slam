# Chapter 8: Model Checking

Part 2: Core Reasoning.

## Objective

Decide temporal and safety properties of systems using explicit, symbolic and SAT-based algorithms.

## Proof of mastery

Trace IC3 by hand on a small transition system, including frames, generalization and propagation.

## Topics

| Topic | Objective |
|---|---|
| [Transition Systems and Temporal Logic](transition-systems-and-temporal-logic/) | Model systems as transition systems and express properties in LTL and CTL. |
| [Explicit-State Checking](explicit-state-checking/) | Check LTL properties using Büchi automata and nested depth-first search. |
| [Symbolic Checking with BDDs](symbolic-checking-with-bdds/) | Build reduced ordered BDDs by hand and compute fixed points over them. |
| [Bounded Model Checking](bounded-model-checking/) | Encode reachability up to a bound as SAT and state when the result is conclusive. |
| [K-Induction](k-induction/) | Prove safety with k-induction and strengthen it using invariants. |
| [Abstraction Refinement](abstraction-refinement/) | Run the CEGAR loop by hand with predicate abstraction and spurious counterexample analysis. |
| [Interpolation-Based Checking](interpolation-based-checking/) | Compute reachable-state approximations from interpolants and explain when they converge. |
| [IC3 and PDR](ic3-and-pdr/) | Explain and trace incremental inductive clause learning from memory. |
| [Horn Clauses](horn-clauses/) | Encode program verification as constrained Horn clauses and explain how they are solved. |
| [Software Model Checking](software-model-checking/) | Explain how C programs are translated for bounded checking and where the approach is unsound. |

## Main materials

- Baier and Katoen, Principles of Model Checking.
- Clarke, Henzinger, Veith and Bloem (editors), Handbook of Model Checking.
- Bradley, SAT-Based Model Checking without Unrolling, VMCAI 2011.
