# Chapter 17: Machine Learning for Reasoning

Part 6: AI and Reasoning.

## Objective

Use learning to improve solvers and provers, and evaluate those improvements honestly.

## Proof of mastery

Evaluate a learned heuristic inside your own solver on held-out benchmarks against the baseline.

## Topics

| Topic | Objective |
|---|---|
| [Algorithm Selection](algorithm-selection/) | Build a portfolio selector and measure it against the best single solver. |
| [Learned Branching](learned-branching/) | Explain and reproduce a learned or reinforcement-based branching heuristic. |
| [Neural Symbolic Reasoning](neural-symbolic-reasoning/) | Reproduce a graph neural network for SAT and state what it can and cannot guarantee. |
| [Neural Theorem Proving](neural-theorem-proving/) | Explain how models search for proofs in proof assistants and how they are benchmarked. |
| [LLMs for Invariants and Proofs](llms-for-invariants-and-proofs/) | Evaluate LLM-generated invariants with a verifier checking every result. |
| [Heuristic Project](heuristic-project/) | Integrate one learned heuristic into your solver and report its cost and benefit. |

## Main materials

- Bengio, Lodi and Prouvost, Machine learning for combinatorial optimization: A methodological tour d'horizon, European Journal of Operational Research 2021.
- Selsam et al., Learning a SAT Solver from Single-Bit Supervision, ICLR 2019.
- Selsam and Bjørner, Guiding High-Performance SAT Solvers with Unsat-Core Predictions, SAT 2019.
