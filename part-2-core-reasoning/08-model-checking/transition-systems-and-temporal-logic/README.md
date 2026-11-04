# Transition Systems and Temporal Logic

Part 2, Chapter 8: Model Checking.

## Objective

Model systems as transition systems and express properties in LTL and CTL.

## Why this matters

Every algorithm in this chapter takes two inputs: a transition system and a property. Explicit-state checking consumes LTL through Büchi automata, BDD-based checking evaluates CTL through fixed points, and BMC, k-induction, interpolation and IC3 use the symbolic form $I(x)$, $T(x, x')$, $P(x)$. In applied work, most of the difficulty lies in stating the model and the property correctly: a wrong abstraction or a vacuous specification produces a proof of nothing. This topic gives you the definitions that the other nine topics assume.

## Prerequisites

- [Propositional Logic](../../../part-1-foundations/01-mathematical-logic/propositional-logic/) for the formulas that label and relate states.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for the fixed-point and inductive arguments.
- [Operational Semantics](../../../part-1-foundations/03-semantics-and-types/operational-semantics/) for the idea that a program denotes a transition relation.

## Lesson

### Transition systems and Kripke structures

A Kripke structure is a tuple $M = (S, S_0, R, AP, L)$, where $S$ is a finite set of states, $S_0 \subseteq S$ is the set of initial states, $R \subseteq S \times S$ is a transition relation, $AP$ is a set of atomic propositions, and $L : S \to 2^{AP}$ labels each state with the propositions true in it. Unless stated otherwise, $R$ is total: every state has at least one successor. A dead end can always be made total by adding a self-loop on a state labeled with a fresh proposition such as `deadlock`.

Some textbooks, including Baier and Katoen, add action labels to the transitions. Actions matter for parallel composition, and they are irrelevant to the temporal logics of this topic, so this chapter suppresses them.

A path from $s$ is an infinite sequence $\pi = s_0 s_1 s_2 \dots$ with $s_0 = s$ and $(s_i, s_{i+1}) \in R$ for all $i$. Write $\pi[i]$ for $s_i$ and $\pi^i$ for the suffix $s_i s_{i+1} \dots$. The trace of $\pi$ is the sequence of labels $L(s_0) L(s_1) \dots$, which is an infinite word over the alphabet $2^{AP}$. A state is reachable if it lies on a finite path from an initial state.

### Modeling a system

A program or circuit gives a Kripke structure as follows. A state assigns a value to each variable, including the program counter. Each atomic step of the system contributes transitions. Parallel composition by interleaving gives a transition for each enabled step of each process, and the number of states is in general exponential in the number of processes and variables. This growth is the state explosion problem that the rest of the chapter attacks.

A symbolic description avoids listing states. Encode each state as a Boolean vector $x = (x_1, \dots, x_n)$, and give two formulas: $I(x)$ for the initial states, and $T(x, x')$ for the transition relation, where $x'$ is a primed copy of the variables representing the next state. A free input is modeled by an extra variable, or by existential quantification over it. A sequential circuit with next-state functions $f_i$ has $T(x, x') = \bigwedge_i (x_i' \leftrightarrow f_i(x, w))$. A safety property is a formula $P(x)$ required to hold in all reachable states.

### Linear-time properties

A linear-time property over $AP$ is a set of infinite words over $2^{AP}$. A structure $M$ satisfies a property $E$ when every trace of a path from an initial state belongs to $E$.

For an infinite word $\sigma$, a finite prefix $\hat\sigma$ is a bad prefix of $E$ if no extension of $\hat\sigma$ belongs to $E$.

- $E$ is a safety property if every word outside $E$ has a bad prefix. A violation is observable after finite time.
- $E$ is a liveness property if every finite word can be extended to a word in $E$. No finite observation refutes it.

An invariant is a safety property of the form "every state satisfies the propositional formula $P$".

Theorem (Alpern and Schneider decomposition). Every linear-time property $E$ is the intersection of a safety property and a liveness property.

Proof. Let $\mathrm{cl}(E)$ be the set of words all of whose finite prefixes are prefixes of some word of $E$. Then $\mathrm{cl}(E)$ is a safety property, because a word outside it has a prefix that extends into no word of $E$, and hence into no word of $\mathrm{cl}(E)$. Let $L = E \cup \overline{\mathrm{cl}(E)}$, where the bar is complement. Clearly $E = \mathrm{cl}(E) \cap L$. To see that $L$ is a liveness property, take a finite word $u$. If $u$ is a prefix of a word in $E$, that word is an extension in $L$. Otherwise, every extension of $u$ lies outside $\mathrm{cl}(E)$, and hence in $L$. $\square$

### LTL

The formulas of linear temporal logic are given by

$$
\varphi ::= p \mid \neg \varphi \mid \varphi \land \varphi \mid \mathbf{X}\, \varphi \mid \varphi\, \mathbf{U}\, \varphi, \qquad p \in AP.
$$

The semantics is over an infinite word $\sigma = A_0 A_1 \dots$, with $\sigma^i$ denoting the suffix from position $i$:

- $\sigma \models p$ iff $p \in A_0$.
- $\sigma \models \neg \varphi$ iff $\sigma \not\models \varphi$.
- $\sigma \models \varphi \land \psi$ iff $\sigma \models \varphi$ and $\sigma \models \psi$.
- $\sigma \models \mathbf{X}\, \varphi$ iff $\sigma^1 \models \varphi$.
- $\sigma \models \varphi\, \mathbf{U}\, \psi$ iff there is $j \geq 0$ with $\sigma^j \models \psi$ and $\sigma^i \models \varphi$ for all $i < j$.

The usual abbreviations are $\mathbf{F}\, \varphi = \top\, \mathbf{U}\, \varphi$ and $\mathbf{G}\, \varphi = \neg \mathbf{F}\, \neg \varphi$. Weak until is $\varphi\, \mathbf{W}\, \psi = (\varphi\, \mathbf{U}\, \psi) \lor \mathbf{G}\, \varphi$, and release is $\varphi\, \mathbf{R}\, \psi = \neg(\neg \varphi\, \mathbf{U}\, \neg \psi)$.

A structure satisfies an LTL formula, written $M \models \varphi$, if every trace from an initial state satisfies it.

The following equivalences are used constantly.

$$
\neg \mathbf{X}\, \varphi \equiv \mathbf{X}\, \neg \varphi, \qquad \varphi\, \mathbf{U}\, \psi \equiv \psi \lor (\varphi \land \mathbf{X}(\varphi\, \mathbf{U}\, \psi)),
$$

$$
\mathbf{F}\, \varphi \equiv \varphi \lor \mathbf{X}\, \mathbf{F}\, \varphi, \qquad \mathbf{G}\, \varphi \equiv \varphi \land \mathbf{X}\, \mathbf{G}\, \varphi.
$$

Common specification patterns are the following.

| Pattern | Formula | Meaning |
|---|---|---|
| Invariant | $\mathbf{G}\, p$ | The proposition $p$ holds in every state of the trace. |
| Response | $\mathbf{G}(r \to \mathbf{F}\, g)$ | Every request is eventually followed by a grant. |
| Infinitely often | $\mathbf{G}\, \mathbf{F}\, p$ | The proposition $p$ recurs without end. |
| Stabilization | $\mathbf{F}\, \mathbf{G}\, p$ | From some point on, $p$ holds forever. |

### CTL

Computation tree logic quantifies over the paths from a state. State formulas are given by

$$
\Phi ::= p \mid \neg \Phi \mid \Phi \land \Phi \mid \mathbf{EX}\, \Phi \mid \mathbf{E}[\Phi\, \mathbf{U}\, \Phi] \mid \mathbf{EG}\, \Phi.
$$

The semantics at a state $s$ is:

- $s \models \mathbf{EX}\, \Phi$ iff some successor of $s$ satisfies $\Phi$.
- $s \models \mathbf{E}[\Phi\, \mathbf{U}\, \Psi]$ iff some path from $s$ satisfies $\Phi\, \mathbf{U}\, \Psi$ at the level of states.
- $s \models \mathbf{EG}\, \Phi$ iff some path from $s$ has $\Phi$ true at every state.

The other operators are defined from these:

$$
\mathbf{EF}\, \Phi = \mathbf{E}[\top\, \mathbf{U}\, \Phi], \quad \mathbf{AX}\, \Phi = \neg \mathbf{EX}\, \neg \Phi, \quad \mathbf{AG}\, \Phi = \neg \mathbf{EF}\, \neg \Phi, \quad \mathbf{AF}\, \Phi = \neg \mathbf{EG}\, \neg \Phi,
$$

$$
\mathbf{A}[\Phi\, \mathbf{U}\, \Psi] = \neg \mathbf{E}[\neg \Psi\, \mathbf{U}\, (\neg \Phi \land \neg \Psi)] \land \neg \mathbf{EG}\, \neg \Psi.
$$

A structure satisfies $\Phi$ when every initial state satisfies it. In CTL, each temporal operator must be immediately preceded by a path quantifier. CTL* lifts that restriction, and it contains both LTL and CTL.

### The fixed-point view of CTL

The CTL operators are fixed points of monotone functions on the subset lattice of $S$. Let $\mathrm{pre}(Z)$ be the set of states with a successor in $Z$. Then

$$
\mathbf{E}[\Phi\, \mathbf{U}\, \Psi] = \mu Z.\, \Psi \cup (\Phi \cap \mathrm{pre}(Z)), \qquad \mathbf{EG}\, \Phi = \nu Z.\, \Phi \cap \mathrm{pre}(Z),
$$

where $\mu$ and $\nu$ denote least and greatest fixed points. The Knaster-Tarski theorem gives the existence of these fixed points, because the functions are monotone. Since $S$ is finite, iteration from $\emptyset$ reaches the least fixed point and iteration from $S$ reaches the greatest within $|S| + 1$ steps.

Theorem. $\mathbf{EG}\, \Phi$ is the greatest fixed point of $G(Z) = \Phi \cap \mathrm{pre}(Z)$.

Proof. Write $W$ for the set of states with a path along which $\Phi$ holds everywhere. First, $W$ is a fixed point: a state of $W$ satisfies $\Phi$ and has a successor in $W$, and conversely a state of $\Phi \cap \mathrm{pre}(W)$ prepends itself to a path of its successor. Next, let $Z$ be any fixed point. From $s \in Z$, the equation gives $s \models \Phi$ and a successor in $Z$. Repeating this constructs an infinite path inside $Z$, on which $\Phi$ holds everywhere, so $s \in W$. Therefore $W$ contains every fixed point. $\square$

This gives the labeling algorithm: process subformulas from the inside out, and attach to each state the subformulas that hold in it. Computing $\mathbf{E}[\Phi\, \mathbf{U}\, \Psi]$ takes a backward search from $\Psi$-states through $\Phi$-states. For $\mathbf{EG}\, \Phi$, restrict the graph to the $\Phi$-states and compute the states that can reach a nontrivial strongly connected component inside it. The whole procedure runs in $O(|\Phi| \cdot (|S| + |R|))$ time. LTL model checking has a worse dependence on the formula: it takes time $O(|M| \cdot 2^{O(|\varphi|)})$ with the automaton construction of [Explicit-State Checking](../explicit-state-checking/), and the problem is PSPACE-complete.

### LTL and CTL are incomparable

- The LTL formula $\mathbf{F}\, \mathbf{G}\, p$ has no equivalent in CTL. In particular, it differs from $\mathbf{AF}\, \mathbf{AG}\, p$, as Example 2 shows.
- The CTL formula $\mathbf{AG}\, \mathbf{EF}\, p$ has no equivalent in LTL, since LTL cannot express the existence of an alternative future. Exercise 7 proves this.
- Properties such as $\mathbf{AG}\, p$ and $\mathbf{G}\, p$ agree.

Satisfaction of an LTL formula is a universal claim over traces, so $M \not\models \varphi$ does not imply $M \models \neg \varphi$. Two traces of the same structure can disagree on $\varphi$.

### Fairness

Interleaving models contain runs that real schedulers exclude, for example a process that is enabled forever and never scheduled. A fairness assumption restricts attention to some paths.

- Unconditional fairness: $\mathbf{G}\, \mathbf{F}\, \psi$.
- Strong fairness: $\mathbf{G}\, \mathbf{F}\, \phi \to \mathbf{G}\, \mathbf{F}\, \psi$.
- Weak fairness: $\mathbf{F}\, \mathbf{G}\, \phi \to \mathbf{G}\, \mathbf{F}\, \psi$.

In LTL, an assumption is a premise: check $\mathrm{fair} \to \varphi$. In CTL, fairness cannot be written as a formula of this kind, so the semantics of the path quantifiers is changed so that they range over fair paths, and the algorithm for $\mathbf{EG}$ is changed to search for fair strongly connected components.

## Worked examples

### Example 1: mutual exclusion with a semaphore

Two processes share a semaphore $y$ that starts at 1. Each process cycles through the local states $n$ (noncritical), $w$ (waiting) and $c$ (critical). Moving from $w$ to $c$ requires $y = 1$ and sets $y := 0$. Moving from $c$ to $n$ sets $y := 1$. A state is a triple $(\ell_1, \ell_2, y)$, and the initial state is $(n, n, 1)$.

Generating the reachable states breadth first gives the following.

```
(n,n,1): (w,n,1), (n,w,1)
(w,n,1): (c,n,0), (w,w,1)
(n,w,1): (w,w,1), (n,c,0)
(c,n,0): (n,n,1), (c,w,0)
(n,c,0): (w,c,0), (n,n,1)
(w,w,1): (c,w,0), (w,c,0)
(c,w,0): (n,w,1)
(w,c,0): (w,n,1)
```

There are eight reachable states out of the $3 \times 3 \times 2 = 18$ syntactically possible ones.

Let $c_1$ mean $\ell_1 = c$, and similarly for the others.

The property $\mathbf{G}\, \neg(c_1 \land c_2)$ holds, since no listed state has both components equal to $c$. The observation that no state has this form also gives the inductive reason: every state with a process in $c$ has $y = 0$, and entry to $c$ requires $y = 1$.

The property $\mathbf{G}(w_1 \to \mathbf{F}\, c_1)$ fails. A counterexample is the lasso

$$
(n,n,1)\ (w,n,1)\ \bigl[(w,w,1)\ (w,c,0)\ (w,n,1)\bigr]^\omega,
$$

where process 1 waits forever while process 2 keeps entering its critical section. This is starvation.

The CTL property $\mathbf{AG}\, \mathbf{EF}\, c_1$ holds. From $(w,c,0)$ one can go to $(w,n,1)$, and then to $(c,n,0)$. Every other state reaches one of these or is itself in $c_1$. Thus process 1 can always reach its critical section, although it need not. The contrast between the $\mathbf{AG}\, \mathbf{EF}\, c_1$ result and the failed response property shows the difference between possibility and inevitability.

The CTL property $\mathbf{AG}(w_1 \to \mathbf{AF}\, c_1)$ also fails, for the same reason. The labeling algorithm computes $\mathbf{EG}\, \neg c_1$, which includes the states $(w,n,1)$, $(w,w,1)$, $(w,c,0)$.

### Example 2: $\mathbf{F}\, \mathbf{G}\, p$ differs from $\mathbf{AF}\, \mathbf{AG}\, p$

Let $S = \{s_0, s_1, s_2\}$ with $S_0 = \{s_0\}$, transitions $s_0 \longrightarrow s_0$, $s_0 \longrightarrow s_1$, $s_1 \longrightarrow s_2$, $s_2 \longrightarrow s_2$, and $L(s_0) = L(s_2) = \{p\}$, $L(s_1) = \emptyset$.

Step 1: LTL. Every path either stays in $s_0$ forever, or leaves $s_0$ and ends in $s_2$ forever. In both cases $p$ eventually holds forever, so $M \models \mathbf{F}\, \mathbf{G}\, p$.

Step 2: compute $\mathbf{AG}\, p = \neg \mathbf{EF}\, \neg p$. The state $s_1$ is the only one with $\neg p$. Backward search gives $\mathbf{EF}\, \neg p = \{s_1, s_0\}$. Therefore $\mathbf{AG}\, p = \{s_2\}$.

Step 3: compute $\mathbf{AF}\, \mathbf{AG}\, p = \neg \mathbf{EG}\, \neg \mathbf{AG}\, p$. The set $\neg \mathbf{AG}\, p$ is $\{s_0, s_1\}$. Iterate $Z_{j+1} = \{s_0, s_1\} \cap \mathrm{pre}(Z_j)$ from $Z_0 = \{s_0, s_1\}$.

```
Z0 = {s0, s1}
pre(Z0) = {s0}          since s0 has successors in Z0, and s1's only successor is s2
Z1 = {s0}
pre(Z1) = {s0}
Z2 = {s0}               fixed point
```

Therefore $\mathbf{EG}\, \neg \mathbf{AG}\, p = \{s_0\}$, and $\mathbf{AF}\, \mathbf{AG}\, p = \{s_1, s_2\}$. The initial state $s_0$ is excluded, so $M \not\models \mathbf{AF}\, \mathbf{AG}\, p$.

The path that stays in $s_0$ forever is the witness. At every position, a branch into $s_1$ is available, so $\mathbf{AG}\, p$ never holds along that path, even though $p$ holds along it.

### Example 3: a counter in symbolic form

A two-bit counter with enable input $e$ has state $(x_1, x_2)$, with $x_1$ as the high bit. The equations are

$$
x_2' \leftrightarrow x_2 \oplus e, \qquad x_1' \leftrightarrow x_1 \oplus (x_2 \land e).
$$

With $I = \neg x_1 \land \neg x_2$ and input $e$ treated as a free variable, the relation is $T = (x_2' \leftrightarrow x_2 \oplus e) \land (x_1' \leftrightarrow x_1 \oplus (x_2 \land e))$. Quantifying out $e$ gives each state two successors: itself ($e = 0$) and its increment ($e = 1$). For example, the state 01 has successors 01 and 10. The formula $\mathbf{G}\, \mathbf{F}\, (x_1 \land x_2)$ fails, because the counter may stall forever at 00, whereas $\mathbf{AG}\, \mathbf{EF}\, (x_1 \land x_2)$ holds, because the increment can always be chosen.

## Common mistakes

- Reading $\mathbf{F}\, p$ as "$p$ holds at some point on some path". It is a claim about one trace, and $M \models \mathbf{F}\, p$ quantifies over all traces. The existential reading is $\mathbf{EF}\, p$.
- Assuming that $M \not\models \varphi$ implies $M \models \neg \varphi$. Two traces can disagree. In Example 3, $\mathbf{G}\, \mathbf{F}(x_1 \land x_2)$ and its negation both fail.
- Translating $\mathbf{F}\, \mathbf{G}\, p$ into $\mathbf{AF}\, \mathbf{AG}\, p$ by inserting quantifiers. Example 2 shows they differ. The implication holds only from $\mathbf{AF}\, \mathbf{AG}\, p$ to $\mathbf{F}\, \mathbf{G}\, p$.
- Distributing $\mathbf{AF}$ over disjunction. $\mathbf{AF}(p \lor q)$ can hold when both $\mathbf{AF}\, p$ and $\mathbf{AF}\, q$ fail, because different paths may satisfy different disjuncts.
- Treating $\mathbf{X}$ as defined at the end of a trace. Paths are infinite here, and a finite trace requires separate semantics, which are not the same as these.
- Writing $\mathbf{G}(r \to \mathbf{X}\, g)$ when you mean response. That formula requires the grant at exactly the next step.
- Calling $p\, \mathbf{U}\, q$ a safety property. It has both components: $p\, \mathbf{W}\, q$ for safety and $\mathbf{F}\, q$ for liveness.
- Forgetting vacuity. $\mathbf{G}(r \to \mathbf{F}\, g)$ holds trivially if $r$ never holds, so a model bug that disables requests makes the check pass.

## Exercises

### Exercise 1

Write the semantics of $\varphi\, \mathbf{U}\, \psi$ and of $\mathbf{EG}\, \Phi$.

<details><summary>Solution</summary>

$\sigma \models \varphi\, \mathbf{U}\, \psi$ iff there is $j \geq 0$ with $\sigma^j \models \psi$ and $\sigma^i \models \varphi$ for all $0 \leq i < j$. $s \models \mathbf{EG}\, \Phi$ iff there is a path $\pi$ from $s$ with $\pi[i] \models \Phi$ for all $i \geq 0$.

</details>

### Exercise 2

Classify each property as safety, liveness or neither: $\mathbf{G}\, p$; $\mathbf{F}\, p$; $\mathbf{G}\, \mathbf{F}\, p$; $p\, \mathbf{U}\, q$; $\mathbf{X}\, p$.

<details><summary>Solution</summary>

$\mathbf{G}\, p$ is safety, with a bad prefix ending in a state without $p$. $\mathbf{F}\, p$ is liveness. $\mathbf{G}\, \mathbf{F}\, p$ is liveness. $p\, \mathbf{U}\, q$ is neither: a prefix that has $\neg p \land \neg q$ before any $q$ is bad, so it is not liveness, and the word $\{p\}^\omega$ violates it with no bad prefix, so it is not safety. $\mathbf{X}\, p$ is safety, since the bad prefix has length two.

</details>

### Exercise 3

Let $\sigma = \{p\}\, \{p\}\, \{q\}\, \emptyset^\omega$. Evaluate $p\, \mathbf{U}\, q$, $\mathbf{X}\, \mathbf{X}\, q$, $\mathbf{G}\, \mathbf{F}\, q$, $\mathbf{F}\, \mathbf{G}\, \neg q$ and $\mathbf{G}(p \to \mathbf{F}\, q)$.

<details><summary>Solution</summary>

$p\, \mathbf{U}\, q$ is true, with $j = 2$. $\mathbf{X}\, \mathbf{X}\, q$ is true. $\mathbf{G}\, \mathbf{F}\, q$ is false, since $q$ does not recur after position 2. $\mathbf{F}\, \mathbf{G}\, \neg q$ is true from position 3. $\mathbf{G}(p \to \mathbf{F}\, q)$ is true, since positions with $p$ are 0 and 1, and $q$ occurs at position 2.

</details>

### Exercise 4

Let $M$ have states $s_0, s_1, s_2, s_3$, transitions $s_0 \longrightarrow s_1$, $s_0 \longrightarrow s_2$, $s_1 \longrightarrow s_1$, $s_1 \longrightarrow s_3$, $s_2 \longrightarrow s_3$, $s_3 \longrightarrow s_3$, and labels $L(s_0) = L(s_1) = \{p\}$, $L(s_2) = \{q\}$, $L(s_3) = \emptyset$. Compute $\mathbf{EG}\, p$, $\mathbf{E}[p\, \mathbf{U}\, q]$, $\mathbf{EF}\, q$, $\mathbf{AF}\, q$ and $\mathbf{AG}\, \neg q$.

<details><summary>Solution</summary>

For $\mathbf{EG}\, p$, start with $Z_0 = \{s_0, s_1\}$. Both have a successor in $Z_0$: $s_0$ to $s_1$ and $s_1$ to itself. So $\mathbf{EG}\, p = \{s_0, s_1\}$.

For $\mathbf{E}[p\, \mathbf{U}\, q]$, start with $\{s_2\}$. Add $p$-states with a successor in it, which adds $s_0$. Then $s_1$ has successors $s_1$ and $s_3$, neither in the set. The result is $\{s_0, s_2\}$.

$\mathbf{EF}\, q$ is the backward closure of $\{s_2\}$, which is $\{s_0, s_2\}$.

$\mathbf{AF}\, q = \neg \mathbf{EG}\, \neg q$. Here $\neg q$ is $\{s_0, s_1, s_3\}$, and $\mathbf{EG}$ of it is $\{s_0, s_1, s_3\}$, so $\mathbf{AF}\, q = \{s_2\}$.

$\mathbf{AG}\, \neg q = \neg \mathbf{EF}\, q = \{s_1, s_3\}$.

</details>

### Exercise 5

Prove the expansion law $\varphi\, \mathbf{U}\, \psi \equiv \psi \lor (\varphi \land \mathbf{X}(\varphi\, \mathbf{U}\, \psi))$.

<details><summary>Solution</summary>

Suppose $\sigma \models \varphi\, \mathbf{U}\, \psi$ with witness $j$. If $j = 0$, the right side holds by its first disjunct. If $j > 0$, then $\sigma \models \varphi$ from the condition at $i = 0$, and $\sigma^1 \models \varphi\, \mathbf{U}\, \psi$ with witness $j - 1$. Conversely, $\sigma \models \psi$ gives witness $j = 0$. If $\sigma \models \varphi$ and $\sigma^1 \models \varphi\, \mathbf{U}\, \psi$ with witness $j$, then $j + 1$ is a witness for $\sigma$, because $\varphi$ holds at position 0 and at positions 1 to $j$ of $\sigma$ before the $\psi$ position. $\square$

</details>

### Exercise 6

Show that if $M \models \mathbf{AF}\, \mathbf{AG}\, p$ then $M \models \mathbf{F}\, \mathbf{G}\, p$, and explain why the converse fails.

<details><summary>Solution</summary>

Take any path $\pi$ from an initial state. By $\mathbf{AF}\, \mathbf{AG}\, p$, some state $\pi[j]$ satisfies $\mathbf{AG}\, p$. Then every state reachable from $\pi[j]$ satisfies $p$, in particular every $\pi[i]$ with $i \geq j$. So $\pi \models \mathbf{F}\, \mathbf{G}\, p$. Example 2 is a structure satisfying $\mathbf{F}\, \mathbf{G}\, p$ and violating $\mathbf{AF}\, \mathbf{AG}\, p$, because $\mathbf{AG}$ quantifies over branches that leave the path.

</details>

### Exercise 7

Prove that $\mathbf{AG}\, \mathbf{EF}\, p$ has no LTL equivalent.

<details><summary>Solution</summary>

Let $M_1$ have an initial state $s$ with $L(s) = \emptyset$, transitions $s \longrightarrow s$ and $s \longrightarrow t$, and a state $t$ with $L(t) = \{p\}$ and transition $t \longrightarrow t$. Let $M_2$ be the restriction of $M_1$ to $s$ with only the self-loop. Then $M_1 \models \mathbf{AG}\, \mathbf{EF}\, p$, whereas $M_2$ does not satisfy it, since $p$ is unreachable in $M_2$. Suppose an LTL formula $\varphi$ were equivalent. Then $M_1 \models \varphi$, so all traces of $M_1$ satisfy $\varphi$. Every trace of $M_2$ is also a trace of $M_1$, so $M_2 \models \varphi$. This contradicts the equivalence on $M_2$. $\square$

</details>

### Exercise 8

Prove that $\mathbf{E}[\Phi\, \mathbf{U}\, \Psi]$ is the least fixed point of $H(Z) = \Psi \cup (\Phi \cap \mathrm{pre}(Z))$.

<details><summary>Solution</summary>

Let $W = \mathbf{E}[\Phi\, \mathbf{U}\, \Psi]$. The expansion law at the level of states shows that $W$ is a fixed point of $H$. Now let $Z$ be any fixed point, and let $s \in W$ with a witness path whose $\Psi$-state is at position $j$. Use induction on $j$. If $j = 0$, then $s \in \Psi \subseteq Z$. If $j > 0$, then $s \models \Phi$ and its path successor has a witness of length $j - 1$, so it lies in $Z$ by the induction hypothesis. Hence $s \in \Phi \cap \mathrm{pre}(Z) \subseteq Z$. Therefore $W \subseteq Z$. $\square$

</details>

### Exercise 9

Write the Alpern and Schneider decomposition of $p\, \mathbf{U}\, q$.

<details><summary>Solution</summary>

The safety part is the closure of $E = p\, \mathbf{U}\, q$. A finite word is a prefix of a word in $E$ iff it has no position with $\neg p \land \neg q$ before the first $q$. Infinite words with this property are exactly those satisfying $p\, \mathbf{W}\, q$. The liveness part can be chosen simply as $\mathbf{F}\, q$: every finite word extends to one containing $q$, and $(p\, \mathbf{W}\, q) \land \mathbf{F}\, q \equiv p\, \mathbf{U}\, q$. The construction in the proof uses the alternative liveness part $E \cup \overline{p\, \mathbf{W}\, q}$, which yields the same intersection.

</details>

### Exercise 10

Model a bounded buffer of capacity 2 with nondeterministic insert and remove, as a Kripke structure with proposition `full` on the state with two items, and propositions for the last operation. Write in LTL the fact that a remove eventually happens if the buffer stays full, and argue whether the model satisfies it. Then state a fairness assumption that makes it true.

<details><summary>Solution</summary>

Take states $(n, a)$, where $n \in \{0, 1, 2\}$ is the number of items and $a \in \{\mathrm{ins}, \mathrm{rem}, \mathrm{idle}\}$ is the last action. An insert is enabled when $n < 2$, a remove is enabled when $n > 0$, and an idle step is always enabled. The formula is $\mathbf{G}(\mathrm{full} \to \mathbf{F}\, \mathrm{rem})$. The model does not satisfy it: the path that fills the buffer and then idles forever is a counterexample. A strong fairness assumption on remove repairs it: $\mathbf{G}\, \mathbf{F}\, (n > 0) \to \mathbf{G}\, \mathbf{F}\, \mathrm{rem}$. Under this premise, a buffer that stays full has $n > 0$ infinitely often, so a remove occurs infinitely often, and in particular after any full state. Weak fairness on remove also suffices here, since remove stays continuously enabled while the buffer stays full.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Give the definition of a Kripke structure, of a path, and of the symbolic pair $I, T$.
- State the semantics of LTL and CTL.
- Distinguish safety and liveness by the bad prefix criterion, and decompose a property into both.
- Compute CTL subformulas by hand with the fixed-point iterations.
- Show that $\mathbf{F}\, \mathbf{G}\, p$ and $\mathbf{AF}\, \mathbf{AG}\, p$ differ, and that $\mathbf{AG}\, \mathbf{EF}\, p$ has no LTL equivalent.
- State one fairness assumption and explain how LTL and CTL handle it differently.

## Materials

- Baier and Katoen, Principles of Model Checking. Read the chapters Modelling Concurrent Systems, Linear-Time Properties, Linear Temporal Logic and Computation Tree Logic for the fullest textbook treatment of this topic, including fairness.
- Huth and Ryan, Logic in Computer Science, 2nd edition. Read Chapter 3, Verification by model checking, especially Sections 3.2 (LTL), 3.4 (CTL), 3.5 (expressive power), 3.6 (algorithms) and 3.7 (fixed-point characterisation), for a shorter and more elementary account.
