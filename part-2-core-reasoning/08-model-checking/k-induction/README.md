# K-Induction

Part 2, Chapter 8: Model Checking.

## Objective

Prove safety with k-induction and strengthen it using invariants.

## Why this matters

BMC finds bugs, and it rarely proves their absence on realistic designs. K-induction adds one more SAT query to each bound and thereby turns BMC into a proof method. It is simple to add to an existing BMC engine, which is why it is widely used, and it is the first step on the path from bounded search to unbounded proof that leads to [IC3 and PDR](../ic3-and-pdr/). The practical skill it trains is reading a failed inductive step: the counterexample to induction says what the property fails to tell you, and that is usually the lemma you need to add. The same skill applies when an automated verifier rejects your loop invariant.

## Prerequisites

- [Bounded Model Checking](../bounded-model-checking/) for path formulas and the recurrence diameter.
- [Loop Invariants](../../07-deductive-verification/loop-invariants/) for inductive invariants in the program setting.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for strong induction, which k-induction resembles.

## Lesson

### Induction on transition systems

A formula $F$ is an inductive invariant if $I \models F$ and $F \land T \models F'$. If additionally $F \models P$, then $P$ holds in every reachable state. Plain induction takes $F = P$. It often fails because $P$ is too weak: a state may satisfy $P$, be unreachable, and step to a violation. Such a state is called a counterexample to induction (CTI).

The idea of k-induction is to assume $P$ on $k$ consecutive states instead of one. Such a longer hypothesis often rules out the unreachable predecessor.

### Definition

Let $k \geq 1$. The two proof obligations are as follows.

Base case: no violation occurs in the first $k$ states of any path from $I$.

$$
\mathrm{Base}_k = I(x^0) \land \bigwedge_{i=0}^{k-2} T(x^i, x^{i+1}) \land \bigvee_{i=0}^{k-1} \neg P(x^i) \quad \text{is unsatisfiable.}
$$

Inductive step: any path of $k$ states satisfying $P$ extends only to a state satisfying $P$.

$$
\mathrm{Step}_k = \bigwedge_{i=0}^{k-1} \bigl(P(x^i) \land T(x^i, x^{i+1})\bigr) \land \neg P(x^k) \quad \text{is unsatisfiable.}
$$

Note that the initial condition is not assumed in the step. The property $P$ is k-inductive if both formulas are unsatisfiable. For $k = 1$, these are the two conditions of ordinary induction for $P$.

Theorem (soundness). If $P$ is k-inductive, then $P$ holds in every reachable state.

Proof. Let $s_0 s_1 \dots$ be a path from $I$. Use strong induction on $j$ to show $s_j \models P$. For $j < k$, this is the base case. For $j \geq k$, the states $s_{j-k}, \dots, s_{j-1}$ satisfy $P$ by the induction hypothesis, and consecutive states are related by $T$, so $\mathrm{Step}_k$ gives $s_j \models P$. $\square$

Theorem (monotonicity of the step). If $\mathrm{Step}_k$ is unsatisfiable, so is $\mathrm{Step}_{k+1}$.

Proof. A model of $\mathrm{Step}_{k+1}$ is a sequence $x^0, \dots, x^{k+1}$. Dropping $x^0$ gives a model of $\mathrm{Step}_k$. $\square$

The base behaves differently. If $\mathrm{Base}_k$ is satisfiable for a total $T$, the model is a genuine counterexample and the property fails. A satisfiable base at some bound stays satisfiable at all larger bounds, since a violation in the first $k$ states also lies in the first $k + 1$.

### The procedure

```
for k := 1, 2, 3, ...:
    if SAT(Base_k):      return counterexample
    if not SAT(Step_k):  return safe
```

Both queries are incremental, since each new bound adds a copy of $T$ and one more instance of $P$.

### Incompleteness and the simple-path restriction

K-induction is not complete as defined above. If some unreachable state $u$ satisfies $P$, has a self-loop, and has a successor violating $P$, then the sequence $u, u, \dots, u, v$ is a model of $\mathrm{Step}_k$ for every $k$.

Sheeran, Singh and Stålmarck restore completeness on finite systems by demanding that the states in the step be pairwise distinct.

$$
\mathrm{SStep}_k = \mathrm{Step}_k \land \bigwedge_{0 \leq i < j \leq k} x^i \neq x^j.
$$

Theorem. Let $S$ be finite. (a) If $\mathrm{Base}_k$ and $\mathrm{SStep}_k$ are unsatisfiable, then $P$ holds in every reachable state. (b) If $P$ holds in every reachable state, there is a $k$ such that both are unsatisfiable.

Proof. (a) Suppose a violation is reachable, and take a shortest path $s_0, \dots, s_n$ to a violating state. It is loop-free, and only its last state violates $P$. If $n < k$, it gives a model of $\mathrm{Base}_k$. If $n \geq k$, its last $k + 1$ states give a model of $\mathrm{SStep}_k$. (b) If $P$ holds in all reachable states, $\mathrm{Base}_k$ is unsatisfiable for all $k$. For $k \geq |S|$, a model of $\mathrm{SStep}_k$ would need $k + 1 > |S|$ distinct states, so it does not exist. $\square$

The bound in (b) is the worst case, and in practice the method finishes much earlier or not at all. The quadratic number of disequalities can be added lazily, only when a candidate model of the step repeats a state.

A complementary constraint is often added: for $i \geq 1$, the state $x^i$ is not initial in a shortest counterexample path. A shortest path from $I$ does not revisit $I$, so the constraint is sound in the step. This gives a dual way of cutting off spurious paths.

### What k-inductive means as an invariant

Theorem. If $P$ is k-inductive, the set

$$
F = \{ s : \text{every path from } s \text{ with at most } k-1 \text{ transitions contains only } P\text{-states} \}
$$

is an inductive invariant with $F \models P$.

Proof. $F \models P$ holds by the empty path. Initiation is the base case. For consecution, let $s \in F$ and $s \longrightarrow t$, and take a path $t = t_0, \dots, t_j$ with $j \leq k - 1$. The path $s, t_0, \dots, t_j$ has $j + 1$ transitions. If $j + 1 \leq k - 1$, then $t_j \models P$ by $s \in F$. If $j = k - 1$, then the $k$ states $s, t_0, \dots, t_{k-2}$ satisfy $P$ by $s \in F$, and $\mathrm{Step}_k$ gives $t_{k-1} \models P$. Thus $t \in F$. $\square$

K-induction is therefore a succinct way of working with an implicit inductive strengthening. Written as a single formula, $F$ is a universally quantified statement over the $k - 1$ further states, so its propositional form can be much larger than the $k$ copies of $T$ in the step query.

### Strengthening with invariants

If $Q$ is known to hold in all reachable states, it may be added as an assumption without changing correctness:

$$
\bigwedge_{i=0}^{k-1} \bigl(P(x^i) \land Q(x^i) \land T(x^i, x^{i+1})\bigr) \land \neg P(x^k).
$$

Theorem. If $\mathrm{Base}_k$ is unsatisfiable, $Q$ holds in all reachable states and the strengthened step is unsatisfiable, then $P$ holds in all reachable states.

Proof. The proof is the same strong induction. The hypothesis on $s_{j-k}, \dots, s_{j-1}$ includes $Q$ because each of them is reachable. $\square$

A related form proves $P \land Q$ together. If $P \land Q$ is k-inductive, then both hold, and neither needs to be established first. This is often the only way, because lemmas can be mutually inductive: neither may be inductive alone.

The practical workflow is:

1. Run the step. If it is satisfiable, read the CTI.
2. Identify what makes the first state of the CTI unreachable, and state a candidate lemma $Q$ that excludes it.
3. Prove $Q$ with k-induction, possibly assuming $P$, or conjoin it to $P$.
4. Repeat.

Generators such as template-based invariant synthesis automate step 2. Bradley's paper on IC3 notes that it could in principle be combined with k-induction and argues against doing so, because k-induction would eliminate only the states that are easiest to generalize. This is one reason why IC3 stays with $k = 1$ and builds the lemmas directly.

### Comparison

| Method | Query | Certificate on success |
|---|---|---|
| BMC | One long path formula per bound. | There is none for safety, without a threshold. |
| K-induction | One long path formula plus one free unrolling per bound. | A k-inductive property. |
| IC3 | Many queries with one copy of $T$. | A 1-inductive clause set. |

## Worked examples

### Example 1: one unreachable predecessor

Let $S = \{a, b, c, d\}$, $I = \{a\}$, with transitions $a \longrightarrow b$, $b \longrightarrow a$, $c \longrightarrow d$, $d \longrightarrow d$, and $P$ true on $\{a, b, c\}$.

For $k = 1$:

- $\mathrm{Base}_1$: $a$ satisfies $P$, so it is unsatisfiable.
- $\mathrm{Step}_1$: the sequence $c, d$ has $P(c)$, $T(c, d)$ and $\neg P(d)$, so it is satisfiable. The CTI is $c$, an unreachable state that satisfies $P$.

For $k = 2$:

- $\mathrm{Base}_2$: the only path from $a$ with two states is $a, b$, and both satisfy $P$. It is unsatisfiable.
- $\mathrm{Step}_2$: we need $x^0, x^1$ in $P$ with $x^1 \longrightarrow x^2$ and $\neg P(x^2)$. The only such state $x^2$ is $d$. Its predecessors are $c$ and $d$, and only $c$ is in $P$, so $x^1 = c$. No state steps to $c$. The formula is unsatisfiable.

Therefore $P$ is 2-inductive. The invariant from the theorem is $F = \{a, b\}$, since $c$ has a path to $d$ with one transition, and it is the reachable set.

### Example 2: a delay chain over the integers mod 4

The state is $(c, d_1, d_2)$ with each component in $\mathbb{Z}_4$, using six bits. The transition is deterministic:

$$
c' = c + 1, \qquad d_1' = c, \qquad d_2' = d_1.
$$

The initial state is $(2, 1, 0)$, and the property is $P : c \neq d_2$. The intent is that $d_2$ always lags $c$ by two. The reachable states are the four states with $d_1 = c - 1$ and $d_2 = c - 2$.

For $k = 1$. $\mathrm{Base}_1$ is unsatisfiable, since $2 \neq 0$. For $\mathrm{Step}_1$, the state $x^0 = (c, d_1, d_2)$ must satisfy $c \neq d_2$, and $x^1 = (c + 1, c, d_1)$ must violate $P$, which requires $c + 1 = d_1$. Choosing $c = 0$, $d_1 = 1$ and $d_2 = 1$ gives the following model.

```
x0 = (0, 1, 1)    c ≠ d2 holds
x1 = (1, 0, 1)    c = d2, so P fails
```

The formula is satisfiable, so the CTI is $(0, 1, 1)$, which is unreachable, because it has $d_1 \neq c - 1$.

For $k = 2$. $\mathrm{Base}_2$ is unsatisfiable: the first two states are $(2, 1, 0)$ and $(3, 2, 1)$, both satisfying $P$. For $\mathrm{Step}_2$, let $x^0 = (c, d_1, d_2)$. Then

```
x1 = (c + 1, c, d1)
x2 = (c + 2, c + 1, c)
```

A violation at $x^2$ needs $c + 2 = c$ in $\mathbb{Z}_4$, which is false. So $\mathrm{Step}_2$ is unsatisfiable, whatever $d_1$ and $d_2$ are, and $P$ is 2-inductive. The argument does not use the $P$ hypotheses at all: two steps wash out the arbitrary initial register values.

The strengthening alternative gives 1-induction. Let $Q : d_1 = c - 1$. The formula $Q$ is 1-inductive, since $d_1' = c = c' - 1$, and $(2, 1, 0)$ satisfies it. Let $R : d_2 = c - 2$. Under $Q$, we have $d_2' = d_1 = c - 1 = c' - 2$. Thus $Q \land R$ is inductive and implies $P$. A proof with $k = 1$ therefore needs two lemmas, whereas k-induction with $k = 2$ needs none.

A brute-force check over all 64 states confirmed the CTI and the result at $k = 2$. With one further register and the property $c \neq d_3$, the smallest working bound is $k = 3$.

### Example 3: a self-loop, and two ways to fix it

Change Example 1 by adding the transition $c \longrightarrow c$, so that $c$ has a self-loop.

Plain k-induction diverges. The sequence $c, c, \dots, c, d$ is a model of $\mathrm{Step}_k$ for every $k$.

Fix 1: the simple-path restriction. $\mathrm{SStep}_1$ is still satisfiable by $c, d$, whose states are distinct. $\mathrm{SStep}_2$ needs distinct $x^0, x^1, x^2$ with $x^2 = d$, $x^1 = c$, and $x^0$ a predecessor of $c$ in $P$ other than $c$. There is no such $x^0$, so it is unsatisfiable. With $\mathrm{Base}_2$ unsatisfiable, the result is proved at $k = 2$.

Fix 2: an invariant. Let $Q$ be the set $\{a, b\}$. Then $a$ is in $Q$ and $Q$ is closed under $T$, so it is 1-inductive. The strengthened step for $k = 1$ needs $x^0 \in Q$ with a successor outside $P$. There is none, so the proof finishes at $k = 1$.

## Common mistakes

- Including $I(x^0)$ in the step. That turns the step into a BMC query, which removes the inductive content and makes the result an unsound proof.
- Omitting the base case. The step alone says nothing about reachable states. For instance, a system whose initial state violates $P$, and whose violating states have no $P$-path into them, can have an unsatisfiable step.
- Assuming that a satisfiable step means that the property is false. A CTI is usually an unreachable state, and a violation is established only by the base query.
- Assuming that k-induction always terminates. Without the simple-path constraint it can diverge, as Example 3 shows.
- Adding an unproved candidate $Q$ as an assumption. Assuming a false $Q$ can make the step vacuous. A lemma must be proved separately or conjoined to the proof goal, so that it is also checked.
- Applying the disequality constraint at the wrong level. The proof requires $x^i \neq x^j$ on full states, including every state variable.
- Thinking that the theorem on $F$ makes k-induction no stronger than 1-induction. It shows that an inductive strengthening exists, but the strengthening is not available as a formula in the query, and writing it down can be far more expensive.

## Exercises

### Exercise 1

Write $\mathrm{Base}_k$ and $\mathrm{Step}_k$.

<details><summary>Solution</summary>

$\mathrm{Base}_k = I(x^0) \land \bigwedge_{i=0}^{k-2} T(x^i, x^{i+1}) \land \bigvee_{i=0}^{k-1} \neg P(x^i)$.

$\mathrm{Step}_k = \bigwedge_{i=0}^{k-1} (P(x^i) \land T(x^i, x^{i+1})) \land \neg P(x^k)$.

</details>

### Exercise 2

Show that a 1-inductive property is $k$-inductive for all $k \geq 1$.

<details><summary>Solution</summary>

$\mathrm{Step}_1$ being unsatisfiable implies that $\mathrm{Step}_k$ is unsatisfiable, by the monotonicity theorem. For the base, 1-induction gives that $P$ holds in all reachable states, so no path from $I$ violates $P$, and $\mathrm{Base}_k$ is unsatisfiable for all $k$.

</details>

### Exercise 3

Find the smallest $k$ for the system with states $i, u, v, w, b$, initial state $i$, transitions $i \longrightarrow i$, $u \longrightarrow v$, $v \longrightarrow w$, $w \longrightarrow b$, $b \longrightarrow b$, and $P$ true on $\{i, u, v, w\}$.

<details><summary>Solution</summary>

The base holds for all $k$, since only $i$ is reachable. The step is satisfiable at $k = 1$ by $w, b$, at $k = 2$ by $v, w, b$, and at $k = 3$ by $u, v, w, b$. At $k = 4$ it would need a $P$-predecessor of $u$, and none exists. So the smallest $k$ is 4.

</details>

### Exercise 4

Using the theorem on $F$, write the inductive invariant for the system in Exercise 3 with $k = 4$, and verify directly that it is inductive.

<details><summary>Solution</summary>

$F$ is the set of states all of whose paths with at most 3 transitions stay in $P$. From $u$, the path $u, v, w, b$ has 3 transitions and ends outside $P$, so $u \notin F$. From $v$ and $w$, the same reasoning applies with shorter paths. From $b$, the empty path fails. Only $i$ remains. So $F = \{i\}$, with $i$ initial and $i$ stepping only to itself, and it is inductive.

</details>

### Exercise 5

Prove that $\mathrm{Step}_k$ can be made unsatisfiable for all large $k$ in an acyclic subgraph of $P$-states: if the states of $P$ induce an acyclic graph, then $P$ is k-inductive for some $k$ whenever $P$ holds in all reachable states.

<details><summary>Solution</summary>

Let $m$ be the number of $P$-states. A model of $\mathrm{Step}_k$ begins with a path through $k$ $P$-states. In an acyclic graph, states on a path are pairwise distinct, so $k \leq m$. Therefore $\mathrm{Step}_{m+1}$ is unsatisfiable. The base is unsatisfiable by assumption, for all $k$. So $k = m + 1$ works. No simple-path constraint is required. $\square$

</details>

### Exercise 6

Show that the following is not a valid proof rule: from an unsatisfiable $\mathrm{Step}_k \land I(x^0)$ and an unsatisfiable $\mathrm{Base}_k$, conclude $P$.

<details><summary>Solution</summary>

$\mathrm{Step}_k \land I(x^0)$ is exactly the check for violations at step $k$ given that the first $k$ states satisfy $P$. So both together say only that no violation exists within $k + 1$ states. Take a line of states $s_0, s_1, s_2, s_3, s_4$, with initial state $s_0$, each stepping to the next, with $s_4$ stepping to itself, and with $P$ false only on $s_4$. At $k = 2$, the rule passes: paths from $s_0$ have no violation within 3 states. But $s_4$ is reachable, so the conclusion is false.

</details>

### Exercise 7

For the delay chain of Example 2 with a third register $d_3$, where $d_3' = d_2$, initial state $(3, 2, 1, 0)$ and $P : c \neq d_3$, find the smallest $k$, and give the step witnesses at $k = 1, 2$.

<details><summary>Solution</summary>

At $k = 1$: let $x^0 = (0, 0, 1, 1)$. Then $x^1 = (1, 0, 0, 1)$ has $c = d_3$, and $x^0$ has $c \neq d_3$. At $k = 2$: let $x^0 = (0, 2, 0, 1)$. Then $x^1 = (1, 0, 2, 0)$ and $x^2 = (2, 1, 0, 2)$, where $c = d_3 = 2$ at $x^2$, and $P$ holds at $x^0$ and $x^1$. At $k = 3$: $x^3$ has $c = c^0 + 3$ and $d_3 = c^0$, and $c^0 + 3 \neq c^0$ in $\mathbb{Z}_4$, so the step is unsatisfiable. The base is unsatisfiable, because the first three states are $(3, 2, 1, 0)$, $(0, 3, 2, 1)$ and $(1, 0, 3, 2)$, each with $c \neq d_3$. The smallest $k$ is 3.

</details>

### Exercise 8

Prove that if $P \land Q$ is 1-inductive, then both $P$ and $Q$ are invariants. Give a system in which neither is 1-inductive alone.

<details><summary>Solution</summary>

The formula $P \land Q$ is an inductive invariant, so it holds in all reachable states, and so do both conjuncts.

For the system, take two bits $(x_1, x_2)$ with $x_1' = x_2$ and $x_2' = x_1$, starting from 00, with $P = \neg x_1$ and $Q = \neg x_2$. The formula $\neg x_1$ fails because 01 satisfies it and steps to 10. The formula $\neg x_2$ fails because 10 satisfies it and steps to 01. The conjunction $\neg x_1 \land \neg x_2$ holds only on 00, which steps to itself.

This is an instance of a pair of mutually inductive lemmas. Here a larger $k$ can replace the lemma. $\mathrm{Step}_1$ for $P$ is satisfiable by 01, 10. $\mathrm{Step}_2$ would need a $P$-predecessor of 01, and the only predecessor of 01 is 10, which violates $P$. So $P$ is 2-inductive.

</details>

### Exercise 9

Design a family of systems where the smallest $k$ is $2^n$, while a one-line lemma gives $k = 1$.

<details><summary>Solution</summary>

Take a bit $o$ and an $n$-bit counter $c$, with $o' = o$ and $c' = c + 1 \bmod 2^n$. The initial state has $o = 0$. Let $P = \neg(o \land c = 2^n - 1)$. All reachable states have $o = 0$, so $P$ holds.

For $o = 1$, the $P$-states have counter values $0, \dots, 2^n - 2$. The sequence of these values followed by $2^n - 1$ is a model of $\mathrm{Step}_{2^n - 1}$. No model exists for $\mathrm{Step}_{2^n}$: extending the path backward would need a $P$-state with counter value $2^n - 1$ and $o = 1$, which is the bad state. With $o = 0$, no bad state is ever entered. So the smallest $k$ is $2^n$. A brute-force check confirmed $k = 4$ for $n = 2$.

The lemma $Q = \neg o$ is 1-inductive, and it immediately implies $P$. This shows that a good lemma can save an exponential amount of unrolling.

</details>

### Exercise 10

Explain the role of each hypothesis in the completeness proof with simple paths, and show that part (b) can fail without finiteness.

<details><summary>Solution</summary>

In (a), the shortest path is loop-free, which guarantees that a real violation always yields a model of the restricted step or of the base, so the restriction loses no real counterexample. In (b), finiteness gives an upper bound on the number of distinct states in a path. Without finiteness, let the states be the integers, with $n \longrightarrow n + 1$, initial state 0, and $P : n \neq -1$. Every reachable state satisfies $P$. For every $k$, the sequence $-1-k, \dots, -2, -1$ is a simple path whose first $k$ states satisfy $P$ and whose last state violates it. So $\mathrm{SStep}_k$ is satisfiable for all $k$, and the procedure does not terminate.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write the two queries and prove soundness by strong induction.
- Run the procedure on a small system, and read off the CTI at each failing bound.
- Explain why plain k-induction is incomplete, and prove that the simple-path variant is complete on finite systems.
- Construct the 1-inductive invariant implied by a k-inductive property.
- Add a lemma correctly, in both forms, and explain mutually inductive lemmas.

## Materials

- Sheeran, Singh and Stålmarck, Checking Safety Properties Using Induction and a SAT-Solver, FMCAD 2000. Read it for the simple-path restriction and the termination argument that make k-induction complete on finite systems.
- Clarke, Henzinger, Veith and Bloem (editors), Handbook of Model Checking. Look in the chapter SAT-Based Model Checking, by Biere and Kröning, for a treatment in context with BMC. The chapter's title was confirmed, and whether it has a dedicated section on k-induction was not.
- Bradley, SAT-Based Model Checking without Unrolling, VMCAI 2011. This entry is added here. Read its related work section for the comparison between k-induction and incremental clause generation.
