# Automated Reasoning Grand Slam

## Objective

Become an expert in automated reasoning and meet the technical requirements of the AWS Automated Reasoning Applied Scientist posting.

The program has 7 parts, 20 chapters and 142 topics. No time limits have been applied to it.

## Structure

```
part-1-foundations/
    01-mathematical-logic/
        propositional-logic/
```

Each folder has a README that states its objective and lists helpful materials.

## Parts

| Part | Chapters | Objective |
|---|---|---|
| [Part 1: Foundations](part-1-foundations/) | 1 to 3 | Build the logic, computability and semantics needed to read and prove results in automated reasoning without assistance. |
| [Part 2: Core Reasoning](part-2-core-reasoning/) | 4 to 8 | Understand the algorithms behind SAT and SMT solvers, first-order provers, program verifiers and model checkers well enough to trace them by hand. |
| [Part 3: Building the Engines](part-3-building-the-engines/) | 9 to 11 | Turn the concepts from Part 2 into working, tested and benchmarked reasoning tools in Rust and OCaml. |
| [Part 4: Remaining Methods](part-4-remaining-methods/) | 12 to 14 | Add working depth in proof assistants, static analysis and program synthesis, the remaining methods named in the posting. |
| [Part 5: Real Systems](part-5-real-systems/) | 15 to 16 | Apply formal methods to real cloud, systems and cryptographic software and leave public evidence of that work. |
| [Part 6: AI and Reasoning](part-6-ai-and-reasoning/) | 17 to 19 | Connect machine learning and formal methods in both directions, which is where the posting's newest requirements sit and where your specialty develops. |
| [Part 7: Original Research](part-7-original-research/) | 20 | Produce new results in automated reasoning and become known for them in the community. |

## Roadmap

This roadmap covers year 1 only, and later years will be decided based on how it goes. The research focus is verifying LLM output and agent behavior, built on a strong foundation. The plan assumes about 30 hours a week over 48 weeks.

The 7 parts remain the taxonomy of the field, and topics outside this plan stay available for later.

### Year 1: foundation and solvers

The target is Parts 1 to 3 and one proof assistant.

| Weeks | Focus | Done when |
|--:|---|---|
| 1 to 6 | [Part 1: Foundations](part-1-foundations/), with [Rust Foundations](part-3-building-the-engines/09-sat-solver/rust-foundations/) on the side | You pass the proofs of mastery for Chapters 1 to 3. |
| 7 to 17 | [Part 2: Core Reasoning](part-2-core-reasoning/), with Rust Foundations on the side | You pass the hand traces and proofs for Chapters 4 to 8. |
| 17 to 25 | [SAT Solver](part-3-building-the-engines/09-sat-solver/) | You solve SAT Competition benchmarks with every unsatisfiable result confirmed by an independent proof checker. |
| 25 to 38 | [SMT Solver](part-3-building-the-engines/10-smt-solver/) | You pass differential testing against Z3 and cvc5 on SMT-LIB benchmarks in the supported logics. |
| 38 to 40 | [Lean](part-4-remaining-methods/12-proof-assistants/lean/) | You can prove program and mathematical properties in Lean 4 using tactics and automation. |
| 40 to 47 | [Model Checker](part-3-building-the-engines/11-model-checker/) | You report verified results on Hardware Model Checking Competition benchmarks. |
| 47 to 48 | Buffer | You have absorbed any overruns from earlier stages. |

Check your pace at week 25, because the solver estimates are the least certain part of this plan. If you are well behind, or if a paper needs the time, move the Model Checker to year 2 first.

## Alignment with the posting

| Posting item | Chapters | Evidence |
|---|---|---|
| PhD or equivalent research experience | 18, 20 | Your PhD and its papers. |
| Mathematical logic | 1, 2, 6 | Closed-book proofs. |
| SAT/SMT solving and constraint solving | 4, 5, 9, 10 | Solvers you built. |
| Model checking | 8, 11 | A model checker you built. |
| Mechanical theorem proving, Lean, Dafny, Isabelle and Rocq | 6, 12 | Mechanized proofs and verified programs. |
| Formal verification | 3, 7, 12 | Verified programs. |
| Static analysis and program analysis | 13 | An analyzer you built. |
| Program synthesis | 14 | A synthesizer you built. |
| New decision procedures, heuristics and search strategies | 9, 10, 17, 20 | Benchmark results and a paper. |
| Learned search heuristics and neural approaches to symbolic reasoning | 17 | A heuristic evaluated in your solver. |
| Verifying AI-generated code and guarantees for LLM outputs | 18 | A peer-reviewed paper. |
| Safety of agentic coding systems | 19 | A verified permission model. |
| Formal methods on real-world software, security and systems problems | 15, 16 | Merged contributions. |
| Cloud infrastructure verification and cryptographic assurance | 15, 16 | Merged contributions and a verified primitive. |
| AI safety and formal guarantees for generative AI | 18, 19 | A paper and a permission model. |
| OCaml, Rust or similar languages | 9, 10, 15 | Solvers and contributions. |
| Original research published in peer-reviewed venues | 18, 20 | Papers. |

## What the program cannot fully cover

| Posting item | Position |
|---|---|
| Deployment at Amazon scale | Chapters 15 and 20 approximate it, and the real experience requires an internship or job. |
| Professional software development | Open source work helps, and an internship is stronger evidence. |
| Customer work and cross-organizational influence | These come from years on the job. |
| Mentoring | Teaching assistant and lab work provide a partial start. |

## Status of the materials

The materials were listed from memory, and their citations and links have not been checked.
