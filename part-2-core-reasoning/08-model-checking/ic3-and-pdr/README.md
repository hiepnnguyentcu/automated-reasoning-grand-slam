# IC3 and PDR

Part 2, Chapter 8: Model Checking.

## Objective

Explain and trace incremental inductive clause learning from memory.

## Why this matters

IC3, also known as property directed reachability (PDR), proves safety of finite-state systems with many small one-step SAT queries, and it needs no unrolling of the transition relation. It became one of the standard engines for hardware model checking, and its structure carries over to software through constrained Horn clause solvers, which you meet in [Horn Clauses](../horn-clauses/). An applied scientist uses the idea constantly: an invariant is built from local lemmas, each justified relative to the lemmas before it. You will implement this algorithm in the build chapters, and a hand trace is the only reliable way to know that you understand each of its invariants before you debug code that breaks them.

## Prerequisites

- [Transition Systems and Temporal Logic](../transition-systems-and-temporal-logic/) for the symbolic formulation $I(x)$, $T(x, x')$, $P(x)$.
- [Bounded Model Checking](../bounded-model-checking/) for counterexample traces as SAT witnesses.
- [K-Induction](../k-induction/) for inductive invariants and strengthening.
- [Interpolation-Based Checking](../interpolation-based-checking/) for the comparison with another method based on over-approximate reachability.
- [CDCL](../../04-sat/cdcl/) for the incremental SAT queries that the algorithm issues.

## Lesson

### The problem, and what IC3 changes

You are given a finite transition system over state variables $x = (x_1, \dots, x_n)$, with initial condition $I(x)$, transition relation $T(x, x')$ and a safety property $P(x)$. The question is whether every reachable state satisfies $P$.

A formula $F$ is an inductive invariant when two conditions hold:

$$
I \models F \qquad \text{(initiation)}, \qquad F \land T \models F' \qquad \text{(consecution)}.
$$

If in addition $F \models P$, then $P$ holds in every reachable state. The property $P$ itself is often not inductive, so the task is to find an inductive strengthening: a formula $F$ with $F \models P$ that is inductive.

Earlier SAT-based methods reach for the strengthening through unrolling. K-induction unrolls to depth $k$, and interpolation extracts an over-approximate image from a $k$-step BMC refutation. Both issue large queries whose size grows with the depth. Bradley's observation is that a strengthening can be assembled from many clauses, each discovered by a query that mentions only one copy of $T$. The cost is paid in the number of queries, and each individual query stays easy.

### Relative induction

A formula $c$ is inductive relative to $G$ when

$$
I \models c \qquad \text{and} \qquad G \land c \land T \models c'.
$$

The assumption $G$ cuts down the set of states from which $c$ must be preserved. A clause that is not inductive on its own may be inductive relative to what you already know. This is exactly the way a person proves a system correct with a sequence of lemmas.

Two consequences matter throughout this topic.

- If $s$ is a full state, then $\neg s$ is a clause. It is inductive relative to $G$ exactly when $s$ is not initial and no $G$-state other than $s$ itself has $s$ as a successor.
- Relative induction is not monotone in the clause. A subclause of an inductive clause may fail to be inductive, and a subclause of a non-inductive clause may be inductive. Exercise 4 shows the second case.

### Frames

IC3 maintains a sequence of formulas $F_0, F_1, \dots, F_k$. Here $F_0 = I$, and for $i \geq 1$ the formula $F_i$ is $P$ conjoined with a set of clauses, written $\mathrm{clauses}(F_i)$. The sequence satisfies four invariants:

1. $I \models F_i$ for all $i$, and $F_0 = I$.
2. $F_i \models F_{i+1}$ for $0 \leq i < k$. For $i \geq 1$ this holds syntactically because $\mathrm{clauses}(F_{i+1}) \subseteq \mathrm{clauses}(F_i)$.
3. $F_i \models P$ for $0 \leq i \leq k$.
4. $F_i \land T \models F_{i+1}'$ for $0 \leq i < k$.

Invariants 1, 2 and 4 together imply that $F_i$ over-approximates the states reachable in at most $i$ steps. Invariant 3 then says that no violation occurs within $k$ steps, provided that the states of $F_k$ are checked one more step ahead, which is the job of the blocking phase.

The termination criterion is immediate from these invariants.

Theorem (convergence yields a proof). If $\mathrm{clauses}(F_i) = \mathrm{clauses}(F_{i+1})$ for some $1 \leq i < k$, then $F_i$ is an inductive strengthening of $P$.

Proof. Initiation is invariant 1. Consecution is invariant 4 together with $F_{i+1} = F_i$: we obtain $F_i \land T \models F_i'$. The implication $F_i \models P$ is invariant 3. $\square$

### The algorithm

The pseudocode below is the simplified recursive form that you should trace by hand. It uses full states as proof obligations, and it adds each learned clause only at the level at which it was requested.

```
prove(I, T, P):
    if SAT(I ∧ ¬P) or SAT(I ∧ T ∧ ¬P'): return counterexample
    F0 := I;  F1 := P;  k := 1
    loop:
        // strengthening phase
        while SAT(Fk ∧ T ∧ ¬P') with witness state s in Fk:
            block(s, k)                 // may report a counterexample
        // propagation phase
        k := k + 1;  Fk := P
        for i := 1 to k - 1:
            for each clause c in clauses(Fi) \ clauses(Fi+1):
                if not SAT(Fi ∧ T ∧ ¬c'): add c to clauses(Fi+1)
            if clauses(Fi) = clauses(Fi+1): return safe, invariant Fi

block(s, i):                            // obligation: remove s from Fi
    if s satisfies I: report counterexample
    while SAT(Fi-1 ∧ ¬s ∧ T ∧ s') with witness state t in Fi-1:
        block(t, i - 1)
    c := generalize(¬s, i - 1)
    add c to clauses(Fj) for j := 1 to i

generalize(c, j):                       // c is inductive relative to Fj
    for each literal l of c, in a fixed order:
        d := c \ {l}
        if d is nonempty and I ⊨ d and not SAT(Fj ∧ d ∧ T ∧ ¬d'):
            c := d
    return c
```

Read a pair $(s, i)$ as a proof obligation: the state $s$ is in $F_i$ and has a path of $k - i + 1$ steps to a violation of $P$, so it must be shown unreachable in $i$ steps. The obligation succeeds at level $i$ when no $F_{i-1}$-state other than $s$ can step into $s$. Each failed query produces a predecessor one level lower, and each predecessor is a further state that can reach the violation.

Three remarks connect this form to the literature.

- In Bradley's original presentation, a state $s$ is generalized relative to the highest $F_i$ that allows it, and the clause is added to $F_1, \dots, F_{i+1}$. A set of states with levels is then pushed upward until the clause reaches the frontier. This variation learns stronger clauses, and it needs more bookkeeping. Bradley's paper states the correctness proof with annotated pseudocode.
- Practical implementations re-enqueue an obligation $(s, i+1)$ after blocking $(s, i)$, in a priority queue ordered by level, because this finds deeper counterexamples and additional clauses early. They also try to push each learned clause forward immediately. The trace in this topic omits both optimizations so that propagation is visible as a separate phase.
- The original paper checks $F_k \land T \land \neg P'$, as above. A common formulation in PDR implementations instead checks $F_k \land \neg P$ directly and starts $F_1$ at $\top$. Both are correct, and only the frame index at which a bad state is seen shifts by one.

### Inductive generalization

Blocking only the single state $s$ would make the algorithm enumerate states. Generalization shrinks $\neg s$ to a subclause, and a shorter clause excludes more states. A subclause $d \subseteq \neg s$ must satisfy initiation and consecution relative to the frame in order to keep invariants 1 and 4. The simple loop in the pseudocode tries to remove each literal once. It always succeeds in returning something, because $\neg s$ itself qualifies when the blocking query is unsatisfiable and $s$ is not initial.

Because relative induction is not monotone, a failed literal removal does not prove that no smaller clause works. Bradley's MIC procedure accounts for this with the down algorithm: given a candidate clause $d$ that fails consecution with witness state $u$, replace $d$ by $d \cap \neg u$, keeping only the literals of $d$ that $u$ falsifies. Each such step removes only literals that no inductive subclause of $d$ can use: a subclause containing a literal true at $u$ holds at $u$, while the successor of $u$ violates all of $d$ and hence that subclause. Iterating gives either the largest inductive subclause of $d$ or a clause that fails initiation, in which case $d$ has no inductive subclause. MIC then removes a literal from the current inductive clause, applies down, and repeats until no literal can be removed. Bradley's implementation stops after three failed attempts on a clause, because the search for an exact minimum costs more than it gains in practice.

Two further techniques are standard in implementations. An unsatisfiable core of the query $F \land c \land T \land \neg c'$ often identifies literals of $c'$ that the refutation does not need, which removes several literals at once. If the reduced clause violates initiation, a literal of the original clause is restored. The later work of Hassan, Bradley and Somenzi on better generalization adds an analysis of counterexamples to generalization, which blocks the states that prevent a literal from being dropped.

### Propagation

Clauses learned at level $i$ say only that their states are unreachable within $i$ steps. Propagation asks whether $c$ can move to $F_{i+1}$, which requires exactly $F_i \land T \models c'$. This single query adds no new reasoning about predecessors, and it is the step that discovers true invariants: a clause that propagates at every level holds forever. Since the frames are monotone and the state space is finite, adjacent frames must eventually coincide if no counterexample exists.

### Correctness

Lemma (adding a clause preserves the invariants). Suppose the invariants hold, that $I \models c$, and that $F_{i-1} \land c \land T \models c'$. Then adding $c$ to $F_1, \dots, F_i$ preserves all four invariants.

Proof. Invariants 1, 2 and 3 hold since $I \models c$, $c$ is added to a prefix of the frames, and frames only become stronger. For invariant 4, the only changed conclusions are $F_j \land T \models c'$ for $0 \leq j < i$. For $j = 0$, we have $I \models F_{i-1}$ and $I \models c$, so $I \land T \models c'$ follows from the hypothesis. For $1 \leq j < i$, the new frame $F_j$ contains $c$ and implies $F_{i-1}$ by invariant 2, so the hypothesis again gives $F_j \land T \models c'$. For $j = i$, the frame $F_i$ only became stronger and $F_{i+1}$ is unchanged. $\square$

Theorem (soundness of counterexamples). If `block` reports a counterexample, then the sequence of obligations from the initial state to the original violation is a real trace of the system.

Proof. Each obligation $(t, i-1)$ arises because a query found a transition from $t$ to the obligation $s$ above it, and each top-level obligation arises because a query found a transition from $s$ to a $\neg P$ state. A counterexample is reported when the bottom state satisfies $I$. Linking these transitions gives a path from an initial state to a violation. $\square$

Theorem (total correctness). For a finite system, the algorithm terminates. It returns a counterexample exactly if $P$ can be violated, and otherwise it returns an inductive strengthening.

Proof sketch. If it returns, the answer is right by the two results above. For termination, each execution of `block` that completes removes $s$ from $F_i$, and only finitely many state and level pairs exist. Recursion depth is at most $i$, since an obligation at level 0 has a state in $F_0 = I$ and is reported immediately. Hence the strengthening phase ends for each $k$. When it ends, $F_k \land T \models P'$ holds, so invariant 4 holds for the new frame $F_{k+1} = P$.

Now suppose propagation at level $k$ does not converge, and take any $i$ from 1 to $k - 1$. There is a clause $c$ in $F_i$ but not in $F_{i+1}$, and since propagation did not move it, $F_i \land T \not\models c'$. By invariant 4 the witness successor is an $F_{i+1}$-state, and it violates $c$, so it lies in $F_{i+1}$ and outside $F_i$. The state sets therefore form a strictly increasing chain $F_1 \subset F_2 \subset \dots \subset F_k$, which is impossible once $k$ exceeds the number of states. This gives Bradley's bound $k \leq 2^n + 1$ on the number of major iterations. $\square$

A useful strengthening fact is that $\neg s$ is always inductive relative to $F_{k-2}$ when $s$ is a state returned by the strengthening query at level $k$. Otherwise some $F_{k-2}$-state steps to $s$, so $s$ would be in $F_{k-1}$, and $s$ has a $\neg P$ successor, which contradicts $F_{k-1} \land T \models F_k' \models P'$. Recursion from a top-level obligation therefore never has to reach below $F_{k-2}$ on its first query, and Exercise 6 asks you to write out the argument.

### Relation to PDR practice

Eén, Mishchenko and Brayton introduced the name property directed reachability together with a simplified implementation. The commonly cited changes are as follows.

- Each clause is stored once, at the highest level at which it is known to hold, and a separate frame holds clauses proved inductive outright.
- A state returned by the SAT solver is enlarged to a cube using ternary simulation, so that a single obligation covers many states with the same successor behaviour.
- A single incremental solver or one solver per frame is reused across queries, with activation literals controlling which clauses are active.

The partial cubes are sound because a cube obtained this way still has every one of its states stepping to the obligation above it. With partial cubes, the check that an obligation is not initial becomes the query $I \land s$, and a clause must also pass initiation after a literal is dropped.

## Worked examples

All traces below were generated by a brute-force implementation in a scratch script, with assertions checking all four frame invariants after each change to a frame and comparing each verdict with explicit reachability. The invariant in Example 1 was also checked independently with an SMT solver.

Conventions for the traces are as follows.

- A state is written as a bit string $x_1 x_2 x_3$.
- Every query answers with the numerically lowest witness. A different choice gives a different valid trace, as Exercise 7 shows.
- Generalization tries the literals in the order $x_1, x_2, x_3$ and makes one pass.
- Each obligation line shows the state and the level from which it must be removed.

### Example 1: a safe system with frames, generalization and propagation

Take state variables $x_1, x_2, x_3$ and one free input $w$, with

$$
x_1' \leftrightarrow x_2 \land \neg x_3, \qquad x_2' \leftrightarrow x_1 \lor w, \qquad x_3' \leftrightarrow x_2 \lor w.
$$

Let $I = \neg x_1 \land \neg x_2 \land \neg x_3$ and $P = \neg x_1 \lor \neg x_2 \lor \neg x_3$, so the only bad state is 111. The transition table, obtained by evaluating the equations for $w = 0$ and $w = 1$, is below.

```
state   successors
000     000, 011
001     000, 011
010     101, 111
011     001, 011
100     010, 011
101     010, 011
110     111
111     011
```

The reachable states are 000, 001 and 011, so $P$ holds. The property is not inductive, because 010 satisfies $P$ and steps to 111. Here is the complete trace.

```
I ∧ ¬P UNSAT and I ∧ T ∧ ¬P' UNSAT; F0 = I, F1 = P, k = 1
    F1 = P   states: {000,001,010,011,100,101,110}

=== strengthen k=1
query F1 ∧ T ∧ ¬P': SAT, F1-states with a bad successor {010,110}, take s=010 (to 111)
obligation (010, 1)
  query F0 ∧ ¬s ∧ T ∧ s' with s=010: UNSAT (no F0-predecessor)
  generalize (x1 ∨ ¬x2 ∨ x3) relative to F0
    try (¬x2 ∨ x3): passes initiation and consecution, keep
    try (x3): fails initiation (000 is initial and violates it)
    try (¬x2): fails consecution, 000 to 011
    result (¬x2 ∨ x3)
  learn (¬x2 ∨ x3), add to F1
    F1 = P ∧ (¬x2 ∨ x3)   states: {000,001,011,100,101}
query F1 ∧ T ∧ ¬P': UNSAT

k := 2, F2 = P
propagate
  F1 ∧ T ⊨ (¬x2 ∨ x3)' fails: 100 to 010; clause stays at level 1
    F1 = P ∧ (¬x2 ∨ x3)   states: {000,001,011,100,101}
    F2 = P                states: {000,001,010,011,100,101,110}
  F1 and F2 differ, so continue

=== strengthen k=2
query F2 ∧ T ∧ ¬P': SAT, F2-states with a bad successor {010,110}, take s=010 (to 111)
obligation (010, 2)
  query F1 ∧ ¬s ∧ T ∧ s' with s=010: SAT, F1-predecessors {100,101}, take t=100
  obligation (100, 1)
    query F0 ∧ ¬s ∧ T ∧ s' with s=100: UNSAT (no F0-predecessor)
    generalize (¬x1 ∨ x2 ∨ x3) relative to F0
      try (x2 ∨ x3): fails initiation (000 is initial and violates it)
      try (¬x1 ∨ x3): passes initiation and consecution, keep
      try (¬x1): passes initiation and consecution, keep
      result (¬x1)
    learn (¬x1), add to F1
      F1 = P ∧ (¬x2 ∨ x3) ∧ (¬x1)   states: {000,001,011}
      F2 = P                         states: {000,001,010,011,100,101,110}
  query F1 ∧ ¬s ∧ T ∧ s' with s=010: UNSAT (no F1-predecessor now)
  generalize (x1 ∨ ¬x2 ∨ x3) relative to F1
    try (¬x2 ∨ x3): passes initiation and consecution, keep
    try (x3): fails initiation (000 is initial and violates it)
    try (¬x2): fails consecution, 000 to 011
    result (¬x2 ∨ x3)
  learn (¬x2 ∨ x3), add to F1 (already present) and F2
      F1 = P ∧ (¬x2 ∨ x3) ∧ (¬x1)   states: {000,001,011}
      F2 = P ∧ (¬x2 ∨ x3)            states: {000,001,011,100,101}
query F2 ∧ T ∧ ¬P': UNSAT

k := 3, F3 = P
propagate
  F1 ∧ T ⊨ (¬x1)' holds: push to F2
  clauses(F1) = clauses(F2): converged
    F1 = P ∧ (¬x2 ∨ x3) ∧ (¬x1)   states: {000,001,011}
    F2 = P ∧ (¬x2 ∨ x3) ∧ (¬x1)   states: {000,001,011}
    F3 = P                         states: {000,001,010,011,100,101,110}

result: SAFE, invariant F1 = P ∧ (¬x2 ∨ x3) ∧ (¬x1)
```

Check the result directly. The invariant has states 000, 001 and 011, which contain the initial state and avoid 111. Their successors are 000, 011, 000, 011, 001, 011, all inside the set. It is therefore inductive, and in this example it equals the reachable set.

Note these points in the trace.

- In the first generalization, $(\neg x_2)$ fails with witness 000 to 011, which is a reachable transition. The literal $x_3$ is needed because 011 is reachable.
- $(\neg x_2 \lor x_3)$ does not propagate at $k = 2$ because of the state 100, which is unreachable but not yet excluded. The clause $(\neg x_1)$ learned at level 1 removes 100, and only then can the same clause be derived again at level 2.
- The learned clause $(\neg x_1)$ is much stronger than $\neg 100$. It also excludes 101, so the obligation for $s = 010$ has no further predecessor and no separate obligation for 101 is needed.

### Example 2: an unsafe system

Take the shift register $x_1' \leftrightarrow x_2$, $x_2' \leftrightarrow x_3$, $x_3' \leftrightarrow w$, with $I = \neg x_1 \land \neg x_2 \land \neg x_3$ and the same $P$ as above. A one on the input moves left, and three ones in a row reach 111.

```
state   successors
000     000, 001
001     010, 011
010     100, 101
011     110, 111
100     000, 001
101     010, 011
110     100, 101
111     110, 111
```

```
I ∧ ¬P UNSAT and I ∧ T ∧ ¬P' UNSAT; F0 = I, F1 = P, k = 1
    F1 = P   states: {000,001,010,011,100,101,110}

=== strengthen k=1
query F1 ∧ T ∧ ¬P': SAT, F1-states with a bad successor {011}, take s=011 (to 111)
obligation (011, 1)
  query F0 ∧ ¬s ∧ T ∧ s' with s=011: UNSAT (no F0-predecessor)
  generalize (x1 ∨ ¬x2 ∨ ¬x3) relative to F0
    try (¬x2 ∨ ¬x3): passes initiation and consecution, keep
    try (¬x3): fails consecution, 000 to 001
    try (¬x2): passes initiation and consecution, keep
    result (¬x2)
  learn (¬x2), add to F1
    F1 = P ∧ (¬x2)   states: {000,001,100,101}
query F1 ∧ T ∧ ¬P': UNSAT

k := 2, F2 = P
propagate
  F1 ∧ T ⊨ (¬x2)' fails: 001 to 010; clause stays at level 1
    F1 = P ∧ (¬x2)   states: {000,001,100,101}
    F2 = P           states: {000,001,010,011,100,101,110}

=== strengthen k=2
query F2 ∧ T ∧ ¬P': SAT, F2-states with a bad successor {011}, take s=011 (to 111)
obligation (011, 2)
  query F1 ∧ ¬s ∧ T ∧ s' with s=011: SAT, F1-predecessors {001,101}, take t=001
  obligation (001, 1)
    query F0 ∧ ¬s ∧ T ∧ s' with s=001: SAT, F0-predecessors {000}, take t=000
    obligation (000, 0)
      000 is initial: counterexample

result: UNSAFE, trace 000 001 011 111
```

Reading the obligations from the bottom gives the input sequence $w = 1, 1, 1$. The learned clause $(\neg x_2)$ is true of states reachable in one step and false of 011, and that is all it claims, so the frame remains sound even though the system is unsafe. Clauses say that states are unreachable within a bounded number of steps, and a counterexample may still pass through them at a larger distance.

## Common mistakes

- Dropping the requirement $I \models d$ during generalization. The clause $(x_3)$ in Example 1 excludes 010 and passes consecution relative to $F_0$ vacuously, yet it excludes the initial state and would make the frames unsound. Always test initiation for every candidate clause.
- Omitting $\neg s$ from the blocking query. Without it, a state with a self-loop is its own predecessor, and the recursion cannot finish. The correct query is $F_{i-1} \land \neg s \land T \land s'$, because consecution assumes the clause $\neg s$ in the pre-state.
- Confusing the levels in a blocking step. A clause inductive relative to $F_j$ may be added up to $F_{j+1}$, and no higher, or invariant 4 can break. To discharge the obligation $(s, i)$ you therefore query relative to $F_{i-1}$, which also makes each predecessor one level lower so that the recursion descends.
- Believing that a learned clause is a true invariant. A clause at level $i$ claims only unreachability within $i$ steps. In Example 2 the clause $(\neg x_2)$ is false of reachable states such as 010.
- Testing convergence of $F_k$ and $F_{k+1}$ before the strengthening phase has ended. Invariant 4 between those two frames is established only once $F_k \land T \models P'$ holds. The standard check is clause set equality after propagation.
- Assuming that $F_k$ must converge first. Convergence may occur at any level, and often at a low one, as in Example 1 and Exercise 8.
- Believing that one failed literal removal rules out smaller inductive clauses. Relative induction is not monotone in the clause, which is the reason for the down algorithm.
- Treating an obligation at level $i$ as a claim that the state is reachable. The obligation claims only that it reaches a violation in $k - i + 1$ steps. Whether it is reachable is what the recursion decides.

## Exercises

### Exercise 1

State the four frame invariants from memory.

<details><summary>Solution</summary>

$I \models F_i$ with $F_0 = I$. $F_i \models F_{i+1}$, syntactically $\mathrm{clauses}(F_{i+1}) \subseteq \mathrm{clauses}(F_i)$ for $i \geq 1$. $F_i \models P$. $F_i \land T \models F_{i+1}'$.

</details>

### Exercise 2

Define when $c$ is inductive relative to $G$, and state the two queries that decide it.

<details><summary>Solution</summary>

$c$ is inductive relative to $G$ when $I \models c$ and $G \land c \land T \models c'$. Equivalently, $I \land \neg c$ and $G \land c \land T \land \neg c'$ are both unsatisfiable.

</details>

### Exercise 3

Using the table of Example 1, show that $(\neg x_1)$ is not inductive, and that it is inductive relative to $(\neg x_2 \lor x_3)$.

<details><summary>Solution</summary>

The states with $\neg x_1$ are 000, 001, 010, 011. State 010 has successor 101, which violates $\neg x_1$, so it is not inductive. Adding the assumption $(\neg x_2 \lor x_3)$ removes 010. The remaining states 000, 001, 011 have successors 000, 011, 001, all with $x_1 = 0$. Initiation holds, since 000 satisfies $\neg x_1$.

</details>

### Exercise 4

Over variables $x_1, x_2$, let $I$ be the single state 11, with the transitions $11 \longrightarrow 11$, $10 \longrightarrow 10$, $01 \longrightarrow 00$, $00 \longrightarrow 00$. Show that $(x_1)$ is inductive and $(x_1 \lor x_2)$ is not. Then apply the down step to $(x_1 \lor x_2)$.

<details><summary>Solution</summary>

The $(x_1)$ states are 10 and 11, whose successors stay in $\{10, 11\}$, and 11 is initial, so $(x_1)$ is inductive. The clause $(x_1 \lor x_2)$ holds on 01, 10, 11, and $01 \longrightarrow 00$ violates it, so consecution fails with witness $u = 01$. The negation of the witness is $\neg u = (x_1 \lor \neg x_2)$. Intersecting literals gives $(x_1 \lor x_2) \cap (x_1 \lor \neg x_2) = (x_1)$, and $(x_1)$ is inductive. This shows that a subclause can be inductive when the larger clause is not.

</details>

### Exercise 5

In the system of Example 1, generalize $\neg s$ for $s = 110$ relative to $F_0$, trying literals in the order $x_1, x_2, x_3$.

<details><summary>Solution</summary>

Start from $(\neg x_1 \lor \neg x_2 \lor x_3)$. Since 110 is not initial and has no predecessor in $I$, this clause is inductive relative to $F_0$.

```
try (¬x2 ∨ x3): passes initiation and consecution, keep
try (x3): fails initiation (000 violates it)
try (¬x2): fails consecution, 000 to 011
result (¬x2 ∨ x3)
```

</details>

### Exercise 6

Show that an $F_k \land T \land \neg P'$ witness $s$ always has $\neg s$ inductive relative to $F_{k-2}$ for $k \geq 2$, assuming the frame invariants, and that $s$ is not initial.

<details><summary>Solution</summary>

Since $s$ has a $\neg P$ successor, $s$ is not in $F_{k-1}$ when $k \geq 2$, by $F_{k-1} \land T \models F_k' \models P'$. If $s$ were initial, it would lie in $F_{k-1}$ by invariant 1, a contradiction, so initiation holds for $\neg s$. If some $F_{k-2}$-state $t \neq s$ stepped to $s$, then by invariant 4, $s$ would lie in $F_{k-1}$, again a contradiction. So $F_{k-2} \land \neg s \land T \land s'$ is unsatisfiable.

</details>

### Exercise 7

Rerun Example 1 with queries returning the numerically highest witness instead of the lowest. Report every step. The invariant you obtain should be logically the same formula.

<details><summary>Solution</summary>

```
=== strengthen k=1
query F1 ∧ T ∧ ¬P': SAT {010,110}, take s=110 (to 111)
obligation (110, 1)
  query F0 ∧ ¬s ∧ T ∧ s': UNSAT
  generalize (¬x1 ∨ ¬x2 ∨ x3) relative to F0
    try (¬x2 ∨ x3): passes, keep
    try (x3): fails initiation
    try (¬x2): fails consecution, 000 to 011
  learn (¬x2 ∨ x3), add to F1
    F1 states: {000,001,011,100,101}
query F1 ∧ T ∧ ¬P': UNSAT

k := 2, F2 = P
propagate
  F1 ∧ T ⊨ (¬x2 ∨ x3)' fails: 100 to 010

=== strengthen k=2
query F2 ∧ T ∧ ¬P': SAT {010,110}, take s=110 (to 111)
obligation (110, 2)
  query F1 ∧ ¬s ∧ T ∧ s': UNSAT
  generalize (¬x1 ∨ ¬x2 ∨ x3) relative to F1
    try (¬x2 ∨ x3): fails consecution, 100 to 010
    try (¬x1 ∨ x3): passes, keep
    try (¬x1): passes, keep
  learn (¬x1), add to F1, F2
    F1 = P ∧ (¬x2 ∨ x3) ∧ (¬x1)   states: {000,001,011}
    F2 = P ∧ (¬x1)                 states: {000,001,010,011}
query F2 ∧ T ∧ ¬P': SAT {010}, take s=010 (to 111)
obligation (010, 2)
  query F1 ∧ ¬s ∧ T ∧ s': UNSAT
  generalize (x1 ∨ ¬x2 ∨ x3) relative to F1
    try (¬x2 ∨ x3): passes, keep
    try (x3): fails initiation
    try (¬x2): fails consecution, 000 to 011
  learn (¬x2 ∨ x3), add to F1 (present) and F2
    F2 = P ∧ (¬x1) ∧ (¬x2 ∨ x3)    states: {000,001,011}
query F2 ∧ T ∧ ¬P': UNSAT

k := 3, F3 = P
propagate
  no clause of F1 is missing from F2, so clauses(F1) = clauses(F2): converged
```

The invariant is $P \land (\neg x_2 \lor x_3) \land (\neg x_1)$, the same as in Example 1, although no recursion was needed on this path. The choice of witness changes the trace and the number of obligations.

</details>

### Exercise 8

Trace IC3 on a token ring: $x_1' \leftrightarrow x_3$, $x_2' \leftrightarrow x_1$, $x_3' \leftrightarrow x_2$, with $I = x_1 \land \neg x_2 \land \neg x_3$ and $P = \neg x_1 \lor \neg x_2$. Use the lowest-witness rule and the literal order $x_1, x_2, x_3$.

<details><summary>Solution</summary>

The system is deterministic. Each state rotates: 100 steps to 010, 010 to 001, 001 to 100, 101 to 110, 110 to 011, 011 to 101, and 000 and 111 are fixed. The bad states are 110 and 111, and the reachable states are 100, 010, 001.

```
F0 = I, F1 = P, k = 1
    F1 states: {000,001,010,011,100,101}

=== strengthen k=1
query F1 ∧ T ∧ ¬P': SAT {101}, take s=101 (to 110)
obligation (101, 1)
  query F0 ∧ ¬s ∧ T ∧ s': UNSAT
  generalize (¬x1 ∨ x2 ∨ ¬x3) relative to F0
    try (x2 ∨ ¬x3): passes, keep
    try (¬x3): passes, keep
    result (¬x3)
  learn (¬x3), add to F1
    F1 states: {000,010,100}
query F1 ∧ T ∧ ¬P': UNSAT

k := 2, F2 = P
propagate
  F1 ∧ T ⊨ (¬x3)' fails: 010 to 001

=== strengthen k=2
query F2 ∧ T ∧ ¬P': SAT {101}, take s=101 (to 110)
obligation (101, 2)
  query F1 ∧ ¬s ∧ T ∧ s': UNSAT
  generalize (¬x1 ∨ x2 ∨ ¬x3) relative to F1
    try (x2 ∨ ¬x3): fails consecution, 010 to 001
    try (¬x1 ∨ ¬x3): passes, keep
    try (¬x1): fails initiation (100 is initial)
    result (¬x1 ∨ ¬x3)
  learn (¬x1 ∨ ¬x3), add to F1, F2
    F1 states: {000,010,100}
    F2 = P ∧ (¬x1 ∨ ¬x3)   states: {000,001,010,011,100}
query F2 ∧ T ∧ ¬P': UNSAT

k := 3, F3 = P
propagate
  F1 ∧ T ⊨ (¬x3)' fails: 010 to 001
  F2 ∧ T ⊨ (¬x1 ∨ ¬x3)' fails: 011 to 101

=== strengthen k=3
query F3 ∧ T ∧ ¬P': SAT {101}, take s=101 (to 110)
obligation (101, 3)
  query F2 ∧ ¬s ∧ T ∧ s': SAT {011}, take t=011
  obligation (011, 2)
    query F1 ∧ ¬s ∧ T ∧ s': UNSAT
    generalize (x1 ∨ ¬x2 ∨ ¬x3) relative to F1
      try (¬x2 ∨ ¬x3): passes, keep
      try (¬x3): fails consecution, 010 to 001
      try (¬x2): fails consecution, 100 to 010
      result (¬x2 ∨ ¬x3)
    learn (¬x2 ∨ ¬x3), add to F1, F2
      F2 = P ∧ (¬x1 ∨ ¬x3) ∧ (¬x2 ∨ ¬x3)   states: {000,001,010,100}
  query F2 ∧ ¬s ∧ T ∧ s': UNSAT
  generalize (¬x1 ∨ x2 ∨ ¬x3) relative to F2
    try (x2 ∨ ¬x3): fails consecution, 010 to 001
    try (¬x1 ∨ ¬x3): passes, keep
    try (¬x1): fails initiation
    result (¬x1 ∨ ¬x3)
  learn (¬x1 ∨ ¬x3), add to F1, F2 (present) and F3
    F3 = P ∧ (¬x1 ∨ ¬x3)   states: {000,001,010,011,100}
query F3 ∧ T ∧ ¬P': UNSAT

k := 4, F4 = P
propagate
  F1 ∧ T ⊨ (¬x3)' fails: 010 to 001
  F2 ∧ T ⊨ (¬x2 ∨ ¬x3)' holds: push to F3
  clauses(F2) = clauses(F3): converged

result: SAFE, invariant F2 = P ∧ (¬x1 ∨ ¬x3) ∧ (¬x2 ∨ ¬x3)
```

The invariant has states 000, 001, 010, 100, which is "at most one token". It is strictly larger than the reachable set, since it contains the unreachable state 000, and this is the expected outcome: IC3 aims for an invariant that is sufficient for $P$, and it does not compute reachability. In $F_1$, the stronger clause $(\neg x_3)$ subsumes $(\neg x_1 \lor \neg x_3)$ and $(\neg x_2 \lor \neg x_3)$, and an implementation would remove the subsumed clauses.

</details>

### Exercise 9

Prove that a state outside $F_i$ is outside $F_j$ for every $j \leq i$. Then prove that when the strengthening phase at level $k$ ends without a counterexample, every state of $F_i$ for $1 \leq i \leq k$ needs at least $k - i + 2$ transitions to reach a violation of $P$.

<details><summary>Solution</summary>

The first claim is invariant 2: $F_j \models F_i$ for $j \leq i$, so a state outside $F_i$ cannot be in $F_j$. For the distance claim, use descending induction on $i$, counting a violating state as distance 0. For $i = k$: $F_k \models P$ gives distance at least 1, and $F_k \land T \models P'$ rules out distance 1, so the distance is at least 2. For the step, suppose $F_{i+1}$-states have distance at least $k - i + 1$. By invariant 4, each successor of an $F_i$-state is an $F_{i+1}$-state, so an $F_i$-state has distance at least $k - i + 2$. In Example 1 at the end of $k = 2$, the state 100 in $F_2$ has distance exactly 2, by the path through 010 to 111, which matches the bound.

</details>

### Exercise 10

Compare IC3, k-induction and interpolation-based checking on the number of copies of $T$ per query and on how each obtains its strengthening. Then explain why IC3 cannot be replaced by plain BMC even if the BMC depth grows.

<details><summary>Solution</summary>

IC3 uses one copy of $T$ per query and builds a strengthening clause by clause from bad states. K-induction uses $k$ copies and strengthens by adding depth or, separately, supplied lemmas. Interpolation uses a $k$-step BMC query per iteration, and it extracts an over-approximate image from the refutation. BMC alone cannot certify safety without an independently justified completeness threshold, since an unsatisfiable answer at depth $k$ says nothing about paths longer than $k$, whereas IC3 can stop with an inductive invariant at a frame count far below the reachable depth. In practice the small queries also stay cheap for large designs, at the price of many queries.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State the four frame invariants and prove that clause set equality of adjacent frames yields an inductive strengthening.
- Trace `prove`, `block`, `generalize` and propagation by hand on a three-bit system from its transition equations.
- Decide relative induction of a given clause against a given frame, with a witness when it fails.
- Explain why a failed literal removal is not final, and execute one step of the down algorithm.
- Explain the difference between Bradley's IC3 and the PDR formulation of Eén, Mishchenko and Brayton.
- State the bound on $k$ and the reason that it holds.

## Materials

- Bradley, SAT-Based Model Checking without Unrolling, VMCAI 2011. Read it for the original algorithm, the annotated correctness proof in its listings, the termination bound and the implementation notes on MIC and unsatisfiable cores.
- Bradley, Understanding IC3, SAT 2012. Read it as the author's tutorial on the ideas behind the algorithm, after you can trace the algorithm yourself.
- Eén, Mishchenko and Brayton, Efficient implementation of property directed reachability, FMCAD 2011. Read it for the PDR formulation and the practical data structures, including frame storage and ternary simulation.
- Hassan, Bradley and Somenzi, Better Generalization in IC3, FMCAD 2013. This entry is added here. Read it for generalization that analyzes counterexamples to generalization.

Baier and Katoen, Principles of Model Checking, is not listed for this topic. It was published in 2008, before IC3 appeared, and none of its ten chapters is on SAT-based model checking.
