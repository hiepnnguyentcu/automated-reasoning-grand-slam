# Chapter 19: Agentic Coding Safety

Part 6: AI and Reasoning.

## Objective

Define and prove what a coding agent can and cannot do, regardless of what the model decides.

## Proof of mastery

Build a formally verified permission model for a coding agent and test it against known attacks.

## Topics

| Topic | Objective |
|---|---|
| [Threat Models](threat-models/) | State concrete threat models for coding agents, including their tools, data and failure modes. |
| [Authorization Policies](authorization-policies/) | Express agent permissions in a policy language and prove properties of them with a solver. |
| [Information Flow](information-flow/) | Apply noninterference and taint tracking to the data an agent reads and sends. |
| [Sandboxing](sandboxing/) | Explain the guarantees that operating system sandboxes give and how they can fail. |
| [Runtime Enforcement](runtime-enforcement/) | Identify which policies a runtime monitor can enforce and build one for agent tool calls. |
| [Prompt Injection Defenses](prompt-injection-defenses/) | Compare defenses by what they guarantee and measure them against an attack benchmark. |
| [Verified Permission Model](verified-permission-model/) | Formalize an agent's permission model and mechanically prove its core safety properties. |

## Main materials

- Dalrymple et al., Towards Guaranteed Safe AI: A Framework for Ensuring Robust and Reliable AI Systems, arXiv 2024.
- Debenedetti et al., Defeating Prompt Injections by Design, arXiv 2025.
- Schneider, Enforceable security policies, ACM TISSEC 2000.
