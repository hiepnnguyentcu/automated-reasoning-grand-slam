# Bounded Model Checking

Part 2, Chapter 8: Model Checking.

## Objective

Encode reachability up to a bound as SAT and state when the result is conclusive.

## Why this matters

Bounded model checking (BMC) was the first widely adopted way of using a SAT solver for model checking. It finds shallow bugs in designs far larger than BDD methods can handle, since it searches for a path and never represents the set of reachable states. It is also a building block: k-induction adds an inductive step to it, interpolation extracts proofs from its refutations, and the C bounded checker of [Software Model Checking](../software-model-checking/) uses the same unrolling at the level of programs. In applied work, the most important judgment about BMC is the one this topic trains: knowing what an unsatisfiable answer does and does not prove.

## Prerequisites

- [Transition Systems and Temporal Logic](../transition-systems-and-temporal-logic/) for $I$, $T$ and LTL.
- [Encodings](../../04-sat/encodings/) for CNF translation.
- [CDCL](../../04-sat/cdcl/) for the solver behind the encoding.

## Lesson

### The idea

A symbolic transition system over $x$ is given by $I(x)$ and $T(x, x')$. Introduce a fresh copy $x^0, x^1, \dots, x^k$ of the state variables for each time step. A sequence of states is a path of length $k$ from an initial state exactly when it satisfies

$$
\mathrm{Path}_k = I(x^0) \land \bigwedge_{i=0}^{k-1} T(x^i, x^{i+1}).
$$

To search for a violation of an invariant $P$ within $k$ steps, check the satisfiability of

$$
\mathrm{BMC}_k = \mathrm{Path}_k \land \bigvee_{i=0}^{k} \neg P(x^i).
$$

Theorem (soundness of the encoding). Let $T$ be total. Then $\mathrm{BMC}_k$ is satisfiable iff there is a state violating $P$ reachable from an initial state in at most $k$ steps. A model gives the path.

Proof. A model assigns a state to each $x^i$. The conjuncts of $\mathrm{Path}_k$ say that $x^0$ is initial and that consecutive states are related by $T$, and the disjunction gives an index $i$ with a violating state, so the prefix up to $i$ is the required path. Conversely, a violating path of length $j \leq k$ can be extended to length $k$ because $T$ is total, which gives the model. $\square$

A variant checks $\mathrm{Path}_k \land \neg P(x^k)$ for $k = 0, 1, 2, \dots$ in order. The two forms find the same violations when the search runs through every $k$. The second has fewer clauses at each depth, and with a nontotal $T$ it is the correct one.

The formula grows linearly with $k$: its size is $O(|I| + k |T| + k |P|)$, assuming a Tseitin translation to CNF, which adds a linear number of variables. For a circuit, the conjunction $\bigwedge_j (x_j' \leftrightarrow f_j(x, w))$ is translated gate by gate.

### The driver loop

```
for k := 0, 1, 2, ...:
    if SAT(Path_k ∧ ¬P(x^k)): return counterexample of length k
    if k has reached a completeness threshold: return safe
```

Practical solvers keep this incremental. The clauses of $T(x^{k}, x^{k+1})$ are added to the solver as the bound grows, and $\neg P(x^k)$ is added as a temporary assumption. Clauses learned for one bound then remain valid for the next, because they follow from the permanent part of the formula.

Since the search runs in order, a counterexample found this way has minimal length. Short counterexamples are valuable in debugging, and this was one of the original advantages claimed for the method over BDD-based checking.

### What an unsatisfiable answer means

An unsatisfiable $\mathrm{BMC}_k$ shows only that no violation exists within $k$ steps. It says nothing about step $k + 1$. BMC is conclusive for safety only when you know a number $c$ such that any violation, if one exists, has a witness of length at most $c$. Such a number is a completeness threshold. Two candidates are the following.

Define the following quantities for a system with initial states $I$. The initial diameter $d_I$ is the largest, over reachable states $s$, of the length of a shortest path from $I$ to $s$. The recurrence diameter $r_I$ is the largest $n$ such that a path $s_0 \dots s_n$ with $s_0 \in I$ visits pairwise distinct states.

Theorem. If $\mathrm{BMC}_k$ is unsatisfiable for all $k \leq d_I$, then $P$ holds in every reachable state.

Proof. A reachable state violating $P$ would have a shortest path from $I$ of length at most $d_I$, which is a satisfying assignment of some $\mathrm{BMC}_k$ with $k \leq d_I$. $\square$

Theorem. $d_I \leq r_I \leq |S| - 1$.

Proof. A shortest path is loop-free, so its length is at most $r_I$. A loop-free path has at most $|S|$ states. $\square$

The two quantities differ in the cost of computing them.

- The value $r_I$ is decidable by SAT. It is the largest $n$ for which the following formula is satisfiable:

$$
\mathrm{Simple}_n = I(x^0) \land \bigwedge_{i=0}^{n-1} T(x^i, x^{i+1}) \land \bigwedge_{0 \leq i < j \leq n} x^i \neq x^j.
$$

- The value $d_I$ requires a quantifier alternation: for each state reached by a path of length $n + 1$, there must be a shorter path to it. This is a formula of the form $\forall \exists$, which you can solve as a QBF, and a SAT solver alone does not decide it directly.

The gap can be exponential. In a graph with an edge between every pair of states, $d_I = 1$ and $r_I = |S| - 1$. So $r_I$ is computable by SAT, but it can be a very weak threshold.

Knowing $r_I$ gives the simplest complete method for finite systems: increase $k$, and stop when $\mathrm{Simple}_k$ is unsatisfiable. This method and the $k$-induction of [K-Induction](../k-induction/) use the same simple-path constraint, and the quadratic number of disequalities in the formula is the cost of doing so.

A bound can be derived from the design in restricted cases, for example from structural analysis of a system with a known pipeline depth. In general, the true value of $d_I$ can be exponential in the size of the model: an $n$-bit counter has $d_I = 2^n - 1$.

### Bounded semantics for LTL

The original paper applied BMC to full LTL. A finite path can witness an infinite behavior when its last state has a transition back to an earlier state, because that gives a lasso. For an existential question, that is, whether a path satisfies $\neg \varphi$, the encoding has two cases.

Let $L_{l,k} = T(x^k, x^l)$ state that the path can return from position $k$ to position $l$, and let $L_k = \bigvee_{l=0}^{k} L_{l,k}$. The encoding of $\psi = \neg \varphi$ in negation normal form is

$$
\mathrm{Path}_k \land \Bigl( \bigl(\neg L_k \land [\psi]^0_k\bigr) \lor \bigvee_{l=0}^{k} \bigl(L_{l,k} \land {}_l[\psi]^0_k\bigr) \Bigr).
$$

Here $[\psi]^i_k$ translates $\psi$ at position $i$ along a loop-free prefix, and ${}_l[\psi]^i_k$ translates it along a lasso with loop back to $l$. The key recursive rules are as follows.

```
without a loop:
    [p]^i_k         =  p(x^i)
    [X ψ]^i_k       =  [ψ]^(i+1)_k    if i < k, otherwise ⊥
    [G ψ]^i_k       =  ⊥
    [F ψ]^i_k       =  ⋁ (j from i to k) [ψ]^j_k
    [ψ U θ]^i_k     =  ⋁ (j from i to k) ([θ]^j_k ∧ ⋀ (n from i to j-1) [ψ]^n_k)

with a loop back to l:
    l[X ψ]^i_k      =  l[ψ]^succ(i)_k, where succ(i) = i+1 for i < k and succ(k) = l
    l[G ψ]^i_k      =  ⋀ (j from min(i,l) to k) l[ψ]^j_k
    l[F ψ]^i_k      =  ⋁ (j from min(i,l) to k) l[ψ]^j_k
```

The no-loop translation of $\mathbf{G}\, \psi$ is $\bot$, because a finite prefix without a loop cannot guarantee anything for all future positions. Any witness found by either case is a real path, which gives soundness. Completeness for LTL holds at some finite bound: in a finite system, if $M \not\models \varphi$, then $\neg \varphi$ has a witness that is a lasso, whose length is bounded by the size of the product with a Büchi automaton for $\neg \varphi$.

### Limits

- BMC is mostly a bug-finding method on large systems, because the threshold is usually out of reach.
- A formula with a large $k$ can be hard for the solver, even though each copy of $T$ is small.
- A deep bug requires a deep unrolling, and a system such as a counter forces $k$ to be exponential in the size of the description, as Exercise 10 shows.

## Worked examples

### Example 1: a two-bit counter with enable

The state is $(x_1, x_2)$, the input is $e$, and $x_1$ is the high bit.

$$
x_2' \leftrightarrow x_2 \oplus e, \qquad x_1' \leftrightarrow x_1 \oplus (x_2 \land e).
$$

Let $I = \neg x_1 \land \neg x_2$, and let $P = \neg x_1 \lor \neg x_2$. Each state has itself and its increment as successors.

Step 1: write the encoding for $k = 0$. $\mathrm{Path}_0 \land \neg P(x^0)$ is $\neg x_1^0 \land \neg x_2^0 \land x_1^0 \land x_2^0$, which is unsatisfiable by unit propagation.

Step 2: write the encoding for $k = 1$.

$$
\neg x_1^0 \land \neg x_2^0 \land (x_2^1 \leftrightarrow x_2^0 \oplus e^0) \land (x_1^1 \leftrightarrow x_1^0 \oplus (x_2^0 \land e^0)) \land x_1^1 \land x_2^1.
$$

Using the unit literals $\neg x_1^0$ and $\neg x_2^0$, the conjunct $x_2^0 \land e^0$ is false. So the second equivalence reduces to $x_1^1 \leftrightarrow \bot$. Then $x_1^1$ conflicts with this, and the formula is unsatisfiable.

Step 3: write the encoding for $k = 2$. The values at step 1 are constrained by the same reasoning: $x_1^1 = \bot$ and $x_2^1 = e^0$. For step 2:

$$
x_2^2 \leftrightarrow x_2^1 \oplus e^1, \qquad x_1^2 \leftrightarrow \bot \oplus (x_2^1 \land e^1).
$$

The bad state needs $x_1^2 = \top$ and $x_2^2 = \top$. The first requirement forces $x_2^1 = \top$ and $e^1 = \top$, and then $x_2^2 = \top \oplus \top = \bot$, a conflict. The formula is unsatisfiable.

Step 4: write the encoding for $k = 3$. Now $x_1^3 = \top$ and $x_2^3 = \top$ can be obtained. Setting $e^0 = e^1 = e^2 = \top$ gives the path

```
step  x1 x2  e
0     0  0   1
1     0  1   1
2     1  0   1
3     1  1
```

Therefore BMC reports a counterexample of length 3. An SMT solver run of the disjunctive form confirmed that the formula is unsatisfiable for $k = 0, 1, 2$ and satisfiable for $k = 3$, with this model.

The Tseitin encoding of $x_2' \leftrightarrow x_2 \oplus e$ is the four clauses, one for each row of the truth table that the equivalence forbids:

```
(¬x2' ∨ x2 ∨ e)
(¬x2' ∨ ¬x2 ∨ ¬e)
(x2' ∨ ¬x2 ∨ e)
(x2' ∨ x2 ∨ ¬e)
```

Each copy of $T$ produces such a block with its own variables, and the blocks share variables only at the frontier between time steps.

### Example 2: when a result is conclusive

Consider a system with state set $\{a, b, c, d\}$, initial state $a$, and transitions

$$
a \longrightarrow b, \quad a \longrightarrow c, \quad a \longrightarrow d, \quad b \longrightarrow c, \quad b \longrightarrow d, \quad c \longrightarrow d, \quad d \longrightarrow d.
$$

Let $P$ be true on all four states. Every state is at distance at most 1 from $a$, so $d_I = 1$. The longest loop-free path is $a, b, c, d$, so $r_I = 3$.

Running BMC with $k = 0, 1$ gives unsatisfiable answers. Since $d_I = 1$, that is a proof of safety, but only if you know $d_I$. A SAT-only procedure would run the simple-path formula as well.

```
k    Simple_k
0    SAT: a
1    SAT: a, b
2    SAT: a, b, c
3    SAT: a, b, c, d
4    UNSAT: five pairwise distinct states do not exist
```

The procedure with recurrence diameter stops at $k = 4$, having shown $r_I = 3$, and it concludes safety from unsatisfiable $\mathrm{BMC}_k$ for $k$ up to 3. The cost of the SAT-only guarantee is two extra unrollings over the true threshold.

Now change the system by removing all edges except $a \longrightarrow b$, $b \longrightarrow c$, $b \longrightarrow d$, $c \longrightarrow a$ and $d \longrightarrow d$. The distances from $a$ are 0, 1, 2, 2, so $d_I = 2$. The longest simple paths are $a, b, c$ and $a, b, d$, so $r_I = 2$. In this system the two thresholds agree.

### Example 3: a bounded LTL witness

Let a system have states $s_0$, $s_1$, $s_2$, with initial state $s_0$, transitions $s_0 \longrightarrow s_1$, $s_1 \longrightarrow s_2$, $s_1 \longrightarrow s_1$, $s_2 \longrightarrow s_2$, and label $q$ only on $s_2$. The property is $\varphi = \mathbf{F}\, q$. Its negation is $\mathbf{G}\, \neg q$.

No-loop case: $[\mathbf{G}\, \neg q]^0_k = \bot$, so only lassos can be witnesses.

Depth $k = 0$: the only candidate path is $s_0$, which has no self-loop. The disjunct $L_{0,0} = T(x^0, x^0)$ is false for $x^0 = s_0$, so the formula is unsatisfiable.

Depth $k = 1$: the candidate paths of length 1 are $s_0, s_1$. Now $L_{1,1} = T(s_1, s_1)$ is true, and the translation requires $\neg q$ at positions 1 and 0. Both hold, so the formula is satisfiable, with the lasso $s_0\, s_1^\omega$. Thus $\mathbf{F}\, q$ fails, and BMC gives a trace on which the system remains in $s_1$ forever.

## Common mistakes

- Treating unsatisfiable $\mathrm{BMC}_k$ as a safety proof. It proves only that no violation occurs within $k$ steps.
- Using the recurrence diameter as if it were the diameter. Both give a valid threshold, but $r_I$ can be exponentially larger.
- Omitting the total relation assumption. With a nontotal $T$, a violation may have no extension to length $k$. The disjunctive form $\bigvee_i \neg P(x^i)$ then misses a violation at an earlier step, and the check for each exact depth does not.
- Reusing the same variable for an input at different time steps. Each step needs a fresh copy of $e$.
- Encoding the simple-path constraint with $x^i \neq x^j$ only for adjacent steps. It must hold for all pairs $i < j$.
- Reading a counterexample from assignments to Tseitin auxiliaries. Only the state and input variables form the trace.
- Assuming that a small $k$ makes a formula easy. A short unrolling of a multiplier is still a hard SAT instance.
- Believing that BMC finds violations of LTL liveness with a finite prefix alone. A violation of $\mathbf{F}\, q$ needs a lasso, so the loop condition must be encoded.

## Exercises

### Exercise 1

Write $\mathrm{BMC}_k$ from memory, and state what a satisfiable answer and an unsatisfiable answer each imply.

<details><summary>Solution</summary>

$\mathrm{BMC}_k = I(x^0) \land \bigwedge_{i<k} T(x^i, x^{i+1}) \land \bigvee_{i \leq k} \neg P(x^i)$. Satisfiable means that a real counterexample of length at most $k$ exists, and the model gives it. Unsatisfiable means that no violating state is reachable within $k$ steps, and it says nothing about longer paths. These readings assume that $T$ is total.

</details>

### Exercise 2

Give the CNF of $y \leftrightarrow (a \land b)$ and of $y \leftrightarrow (a \lor b)$.

<details><summary>Solution</summary>

$y \leftrightarrow (a \land b)$: $(\neg y \lor a)$, $(\neg y \lor b)$, $(y \lor \neg a \lor \neg b)$.

$y \leftrightarrow (a \lor b)$: $(y \lor \neg a)$, $(y \lor \neg b)$, $(\neg y \lor a \lor b)$.

</details>

### Exercise 3

Write the $k = 1$ encoding for a toggling bit: $x' \leftrightarrow \neg x$, $I = \neg x$, and $P = \neg x$. Decide it.

<details><summary>Solution</summary>

The formula is $\neg x^0 \land (x^1 \leftrightarrow \neg x^0) \land (x^0 \lor x^1)$. From $\neg x^0$, unit propagation gives $x^1$, and the third clause holds. The formula is satisfiable, and the trace is $x^0 = \bot$, $x^1 = \top$. The state after one step violates $P$.

</details>

### Exercise 4

Compute $d_I$ and $r_I$ for the two-bit counter with enable in Example 1, and state the smallest bound at which BMC would be conclusive for each property: (a) $P = \neg x_1 \lor \neg x_2$, and (b) $P = \top$.

<details><summary>Solution</summary>

The reachable states are 00, 01, 10 and 11, at distances 0, 1, 2 and 3, so $d_I = 3$. A loop-free path can visit at most these four states, and 00, 01, 10, 11 is one, so $r_I = 3$. (a) BMC finds a counterexample at $k = 3$, and a counterexample is conclusive by itself. (b) No violation exists, and BMC needs $k$ up to $d_I = 3$, which is both a diameter and a recurrence diameter here.

</details>

### Exercise 5

Prove that iterating $k$ upward with the exact depth formula returns a counterexample of minimal length.

<details><summary>Solution</summary>

Suppose the procedure returns at depth $k$, and suppose there were a counterexample of length $j < k$. Its prefix up to the first violation would give a model of $\mathrm{Path}_j \land \neg P(x^j)$, so the procedure would have returned at depth $j$, a contradiction. $\square$

</details>

### Exercise 6

Show that $\mathrm{Simple}_n$ unsatisfiable implies $\mathrm{Simple}_m$ unsatisfiable for all $m \geq n$, and that it implies $r_I < n$.

<details><summary>Solution</summary>

A model of $\mathrm{Simple}_m$ restricted to the first $n + 1$ states gives a model of $\mathrm{Simple}_n$, since a prefix of a simple path from $I$ is a simple path from $I$. So unsatisfiability for $n$ propagates upward. By definition, $r_I$ is the largest $n$ for which $\mathrm{Simple}_n$ is satisfiable. If $\mathrm{Simple}_n$ is unsatisfiable, all larger values are as well, so $r_I < n$. $\square$

</details>

### Exercise 7

Using Example 3, explain why the depth at which a lasso witness of $\mathbf{G}\, \neg q$ is found is at most $|S| - 1$ when one exists at all.

<details><summary>Solution</summary>

A witness trace of $\mathbf{G}\, \neg q$ is an infinite path through $\neg q$ states. In a finite system, some state repeats on it. Take the first repetition: the path $s_0, \dots, s_l, \dots, s_k$, with $s_k$ having a transition to $s_l$ and with $s_0, \dots, s_k$ pairwise distinct. This is a lasso with at most $|S|$ distinct states, so $k \leq |S| - 1$. It is a witness, because all its states satisfy $\neg q$. For this particular formula the threshold $|S| - 1$ therefore suffices.

</details>

### Exercise 8

Prove that the disjunctive and the exact depth forms find the same counterexamples when $T$ is total and the loop runs through all depths.

<details><summary>Solution</summary>

Suppose $\mathrm{Path}_j \land \neg P(x^j)$ is satisfiable for some $j \leq k$. Since $T$ is total, the path can be extended to length $k$, which gives a model of $\mathrm{BMC}_k$. Conversely, a model of $\mathrm{BMC}_k$ has an index $i \leq k$ with $\neg P(x^i)$, and its prefix up to $i$ gives a model of the exact form at depth $i$. So $\mathrm{BMC}_k$ is satisfiable iff the exact form is satisfiable for some $j \leq k$. $\square$

</details>

### Exercise 9

Give the formula for the initial diameter check as a QBF, and explain why $\mathrm{Simple}_n$ does not need quantifier alternation.

<details><summary>Solution</summary>

The bound $d_I \leq n$ holds iff, for every path of length $n + 1$ from $I$, its endpoint is reachable by a path of length at most $n$:

$$
\forall x^0 \dots x^{n+1}.\ \bigl( I(x^0) \land \bigwedge_{i \leq n} T(x^i, x^{i+1}) \bigr) \to \exists y^0 \dots y^n.\ I(y^0) \land \bigwedge_{i < n} (T(y^i, y^{i+1}) \lor y^i = y^{i+1}) \land y^n = x^{n+1}.
$$

The stuttering disjunct allows paths shorter than $n$. By contrast, $\mathrm{Simple}_n$ asks only for the existence of one path with disequalities among its own states, so it is a purely existential formula and thus a SAT problem.

</details>

### Exercise 10

Design a family of systems, parameterized by $n$, of size $O(n)$, where any counterexample is of length $2^n - 1$. Explain what this shows about BMC, and why the same system is easy for induction with an appropriate property.

<details><summary>Solution</summary>

Take an $n$-bit counter with next-state functions $x_i' \leftrightarrow x_i \oplus (x_{i+1} \land \dots \land x_n)$, starting at 0, with the bad state being all ones. The description has size $O(n^2)$ with flat conjunctions, or $O(n)$ with a chain of intermediate carry signals. Any path from 0 to all ones takes $2^n - 1$ steps, so BMC needs an exponential number of copies of $T$ to find the violation. This shows that the bound can be exponential in the input even though the formula is linear in the bound. For a safe variant with the same structure, such as a counter with the bad state unreachable because of a parity bit that never changes, a one-step inductive argument over the parity bit is immediate, and such a proof needs no deep unrolling.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write $\mathrm{Path}_k$, $\mathrm{BMC}_k$ and $\mathrm{Simple}_n$.
- Encode one transition step of a small circuit as CNF, and decide an unrolling by hand.
- Compute $d_I$ and $r_I$ of a small graph.
- State and prove the completeness theorems for $d_I$ and $r_I$.
- State the bounded LTL encoding, and find a lasso witness for a small system.

## Materials

- Biere, Cimatti, Clarke and Zhu, Symbolic Model Checking without BDDs, TACAS 1999. Read it for the original encoding of LTL with and without loops and for the motivation relative to BDDs.
- Clarke, Henzinger, Veith and Bloem (editors), Handbook of Model Checking. Read the chapter SAT-Based Model Checking, by Biere and Kröning, for a survey that opens with BMC. The chapter's existence and title were confirmed, and its section structure was not.

Baier and Katoen, Principles of Model Checking, is not listed for this topic, because none of its ten chapters is on SAT-based model checking.
