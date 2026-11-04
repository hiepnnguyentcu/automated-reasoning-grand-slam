# Chapter 7: Deductive Verification

Part 2: Core Reasoning.

## Objective

Prove program correctness with program logics and reduce those proofs to solver queries.

## Proof of mastery

Generate verification conditions by hand for an unseen program with loops and prove them correct.

## Topics

| Topic | Objective |
|---|---|
| [Hoare Logic](hoare-logic/) | Prove partial and total correctness of small programs using Hoare logic. |
| [Weakest Preconditions](weakest-preconditions/) | Compute weakest preconditions by hand and relate them to Hoare logic. |
| [Loop Invariants](loop-invariants/) | Find inductive invariants and ranking functions for unseen loops. |
| [Verification Conditions](verification-conditions/) | Explain how verifiers generate compact verification conditions and send them to solvers. |
| [Separation Logic](separation-logic/) | Prove pointer programs correct using the frame rule and inductive heap predicates. |
| [Concurrent Separation Logic](concurrent-separation-logic/) | Reason about shared-memory concurrency with ownership and resource invariants. |

## Main materials

- Bradley and Manna, The Calculus of Computation.
- Winskel, The Formal Semantics of Programming Languages.
- Reynolds, Separation Logic: A Logic for Shared Mutable Data Structures, LICS 2002.
