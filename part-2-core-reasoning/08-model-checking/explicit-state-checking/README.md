# Explicit-State Checking

Part 2, Chapter 8: Model Checking.

## Objective

Check LTL properties using Büchi automata and nested depth-first search.

## Why this matters

Explicit-state checking enumerates states one at a time and stores them in a table. It is the oldest model checking method, and it remains effective for protocols and concurrent software, where the number of reachable states is modest compared with the number of syntactically possible states, and where partial-order reduction applies. It also gives the standard reduction of LTL model checking to a graph problem, and symbolic methods reuse that automata-theoretic reduction. Liveness bugs such as starvation and livelock are found by this reduction. Build chapters later in the program assume that you know why the seed order of nested search matters.

## Prerequisites

- [Transition Systems and Temporal Logic](../transition-systems-and-temporal-logic/) for Kripke structures and LTL.
- [Space and the Polynomial Hierarchy](../../../part-1-foundations/02-decidability-and-complexity/space-and-the-polynomial-hierarchy/) for the meaning of PSPACE-completeness.

## Lesson

### Safety checking by reachability

For an invariant $\mathbf{G}\, P$, explicit-state checking is graph search. Run breadth-first or depth-first search from the initial states, store visited states in a hash table, and stop when a state violating $P$ is found. The search path is the counterexample, and breadth-first search gives a shortest one. The time is linear in the number of reachable states and transitions. All the difficulty lies in the size of the state set.

A more general safety property reduces to the same computation. Its bad prefixes form a language of finite words, and when this language is regular, a finite automaton can be run in product with the system.

### Büchi automata

Liveness needs infinite words. A nondeterministic Büchi automaton (NBA) is a tuple $A = (Q, \Sigma, \delta, Q_0, F)$ with a finite state set $Q$, an alphabet $\Sigma$, a transition function $\delta : Q \times \Sigma \to 2^Q$, initial states $Q_0 \subseteq Q$ and accepting states $F \subseteq Q$. A run on $\sigma = A_0 A_1 \dots$ is an infinite state sequence $q_0 q_1 \dots$ with $q_0 \in Q_0$ and $q_{i+1} \in \delta(q_i, A_i)$. The run is accepting if some state of $F$ occurs infinitely often. $L(A)$ is the set of words with an accepting run. The languages recognized by NBAs are exactly the $\omega$-regular languages.

Three facts explain the design of the algorithm.

- NBAs are closed under union, intersection and complementation. Complementation is expensive, which is why model checkers build an automaton for the negated formula directly.
- Deterministic Büchi automata are strictly weaker. The language $\mathbf{F}\, \mathbf{G}\, p$ has a two-state NBA and no deterministic Büchi automaton, so nondeterminism cannot be removed in this model.
- $L(A) \neq \emptyset$ iff some accepting state is reachable from an initial state and lies on a cycle. A nonempty language is therefore witnessed by a lasso.

The third fact holds because a run visiting $F$ infinitely often visits some accepting state $q$ twice, and the segment between the two visits is a cycle. The converse pumps the cycle.

### The automata-theoretic reduction

For an LTL formula $\varphi$, let $\mathrm{Words}(\varphi)$ be the set of words over $2^{AP}$ satisfying it.

Theorem (Vardi and Wolper). Let $A_{\neg\varphi}$ be an NBA with $L(A_{\neg\varphi}) = \mathrm{Words}(\neg \varphi)$. Then $M \models \varphi$ iff $\mathrm{Traces}(M) \cap L(A_{\neg\varphi}) = \emptyset$.

The statement is a rewrite: $M \models \varphi$ means every trace is in $\mathrm{Words}(\varphi)$, which means that no trace is in its complement.

The intersection is computed as a product. With the convention that an automaton state records the state after reading the current label,

$$
M \otimes A = (S \times Q,\ \longrightarrow,\ I',\ F'),
$$

where $(s, q) \longrightarrow (s', q')$ iff $s \longrightarrow s'$ in $M$ and $q' \in \delta(q, L(s'))$. The initial states are the pairs $(s_0, q)$ with $s_0 \in S_0$ and $q \in \delta(q_0, L(s_0))$ for some $q_0 \in Q_0$. A pair is accepting if its automaton component is in $F$.

Theorem. $M \not\models \varphi$ iff $M \otimes A_{\neg\varphi}$ has a reachable accepting cycle. A reachable accepting cycle projects to a lasso-shaped trace of $M$ that violates $\varphi$.

### From LTL to automata

The standard construction goes through a generalized Büchi automaton (GBA), whose acceptance is a family $\{F_1, \dots, F_m\}$ of sets, with a run required to visit each $F_j$ infinitely often. The states are elementary sets, which guess in advance what holds at the current position.

Let $\mathrm{cl}(\varphi)$ be the set of subformulas of $\varphi$ and their negations, identifying $\neg\neg\psi$ with $\psi$. A set $B \subseteq \mathrm{cl}(\varphi)$ is elementary if it is

- maximal: for each $\psi$ in the closure, exactly one of $\psi$ and $\neg\psi$ is in $B$;
- propositionally consistent: $\psi_1 \land \psi_2 \in B$ iff $\psi_1 \in B$ and $\psi_2 \in B$, and $\top$ is in $B$ if it is in the closure;
- locally consistent for until: if $\psi_2 \in B$ then $\psi_1\, \mathbf{U}\, \psi_2 \in B$, and if $\psi_1\, \mathbf{U}\, \psi_2 \in B$ and $\psi_2 \notin B$ then $\psi_1 \in B$.

The GBA for $\varphi$ is as follows.

- The states are the elementary sets.
- The initial states are those containing $\varphi$.
- A transition from $B$ on the letter $A$ requires $A = B \cap AP$ and goes to each $B'$ such that $\mathbf{X}\, \psi \in B$ iff $\psi \in B'$, and $\psi_1\, \mathbf{U}\, \psi_2 \in B$ iff $\psi_2 \in B$ or ($\psi_1 \in B$ and $\psi_1\, \mathbf{U}\, \psi_2 \in B'$).
- For each until subformula $\psi_1\, \mathbf{U}\, \psi_2$ in the closure, there is an acceptance set $F_{\psi_1 \mathbf{U} \psi_2} = \{B : \psi_1\, \mathbf{U}\, \psi_2 \notin B \text{ or } \psi_2 \in B\}$.

The expansion law $\psi_1\, \mathbf{U}\, \psi_2 \equiv \psi_2 \lor (\psi_1 \land \mathbf{X}(\psi_1\, \mathbf{U}\, \psi_2))$ is locally enforced by the transitions, but it has two solutions, and only the least one is right. The acceptance sets remove the wrong solution, in which an until is promised forever and never discharged.

Proof sketch of correctness. If $\sigma \models \varphi$, the sets $B_i = \{\psi \in \mathrm{cl}(\varphi) : \sigma^i \models \psi\}$ form an accepting run. Conversely, given an accepting run on $\sigma$ with sets $B_i$, show by structural induction on $\psi$ that $\psi \in B_i$ iff $\sigma^i \models \psi$. The until case with $\psi_1\, \mathbf{U}\, \psi_2 \in B_i$ uses the acceptance condition: if $\psi_2$ never held from $i$ on, the until would propagate forever by the transition rule, which keeps the run out of the acceptance set.

The number of automaton states is $2^{O(|\varphi|)}$, so checking takes $O(|M| \cdot 2^{O(|\varphi|)})$ time. The problem is PSPACE-complete. The upper bound holds because a lasso can be guessed nondeterministically on the fly, with polynomial memory for the current and seed states, so the exponential automaton is never stored.

A GBA with $m$ acceptance sets becomes an NBA by keeping a counter of which set is awaited.

$$
Q' = Q \times \{1, \dots, m\}, \qquad F' = F_1 \times \{1\},
$$

with $(q, i) \longrightarrow (q', j)$ when $q \longrightarrow q'$ in the GBA, where $j = i$ if $q \notin F_i$ and $j = (i \bmod m) + 1$ if $q \in F_i$. Each infinite visit to $F'$ forces a visit to every $F_i$ between returns to the first copy.

### Nested depth-first search

Searching for a reachable accepting cycle by computing strongly connected components works, but nested depth-first search, due to Courcoubetis, Vardi, Wolper and Yannakakis, stores only two bits per state and can find a counterexample on the fly.

```
blue(s):
    mark s blue; push s on the stack
    for each successor t of s:
        if t is not blue: blue(t)
    if s is accepting:
        seed := s
        red(s)
    pop s

red(s):
    mark s red
    for each successor t of s:
        if t = seed: report cycle (the stack up to seed, then the red path back to seed)
        if t is not red: red(t)

main: for each initial state s0: if s0 is not blue: blue(s0)
report no accepting cycle
```

Red marks are kept across all red searches. This sharing is what makes the algorithm linear: each state is expanded at most once in each color. Sharing also requires seeds to be processed in postorder, which is the delicate part.

Theorem. Nested DFS reports a cycle iff a reachable accepting cycle exists.

Proof. If a cycle is reported, the blue stack and the red path give a lasso through the accepting seed.

Conversely, suppose that an accepting state on a cycle is reachable. Blue search visits every reachable state, so it calls `red` on every reachable accepting state, unless it reports earlier. Suppose the algorithm reports nothing. Let $s$ be the first seed, in the order of calls, that lies on a cycle. The red search from $s$ visits every state reachable from $s$ through states that were not already red when it started. It fails to return to $s$, so the cycle through $s$ contains a state $r$ that was already red. Let $q$ be the seed of the earlier red search that marked $r$. Then $q$ was finished by blue before $s$, and $q$ reaches $r$, and $r$ reaches $s$, so $q$ reaches $s$.

We now show that $q$ lies on a cycle, which contradicts the choice of $s$. Consider the state of blue search when $q$ is finished, and recall that $s$ is finished later.

- If $s$ is on the stack at that time, then $s$ reaches $q$ along the stack, and since $q$ reaches $s$, the state $q$ lies on a cycle.
- If $s$ has not yet been visited at that time, take a path from $q$ to $s$, and let $g$ be the first state on it, after $q$, that is not finished. Its predecessor on the path is finished or is $q$, so all successors of that predecessor have been visited, and $g$ is therefore visited and unfinished, which means that $g$ is on the stack. The state $g$ reaches $q$ along the stack, and $q$ reaches $g$ along the path, so $q$ lies on a cycle.
- If $s$ had been finished before $q$, the order assumption would be violated, so this case cannot arise.

In every case, $q$ is a seed on a cycle with a red search earlier than that of $s$, a contradiction. $\square$

The running time is $O(|S'| + |{\longrightarrow}|)$ for the product, because each state is entered at most once per color.

### Reducing the state space

Explicit-state tools rely on reductions, of which SPIN is the classic example.

- Partial-order reduction explores a subset of the interleavings of independent steps while preserving the LTL properties without $\mathbf{X}$.
- Hash compaction and bitstate hashing store a hash of each state, or a few bits, instead of the state. Two distinct states can then collide, so a state may be wrongly treated as visited. Search may miss errors, although any reported error is genuine.
- On-the-fly construction builds the product during the search, so a counterexample can be found before the whole system is expanded.

## Worked examples

### Example 1: a response property on a product

The system has states $s_0$ (label $\emptyset$), $s_1$ (label $\{r\}$), $s_2$ (label $\{g\}$) and $s_3$ (label $\emptyset$), with initial state $s_0$ and transitions

$$
s_0 \longrightarrow s_1, \quad s_1 \longrightarrow s_2, \quad s_1 \longrightarrow s_3, \quad s_3 \longrightarrow s_3, \quad s_3 \longrightarrow s_2, \quad s_2 \longrightarrow s_0.
$$

The property is $\varphi = \mathbf{G}(r \to \mathbf{F}\, g)$. Its negation is $\mathbf{F}(r \land \mathbf{G}\, \neg g)$.

Step 1: an NBA for the negation. Take states $q_0$ (initial) and $q_1$ (accepting), with $q_0 \xrightarrow{\top} q_0$, $q_0 \xrightarrow{r \land \neg g} q_1$ and $q_1 \xrightarrow{\neg g} q_1$. An accepting run must leave $q_0$ on a letter with $r \land \neg g$ and never see $g$ afterwards.

Step 2: the product, with labels read on entering a system state. The initial label at $s_0$ is $\emptyset$, which does not satisfy $r$, so the only initial product state is $(s_0, q_0)$.

```
(s0,q0): (s1,q0), (s1,q1)
(s1,q0): (s2,q0), (s3,q0)
(s1,q1): (s3,q1)           the letter at s2 contains g, which q1 cannot read
(s2,q0): (s0,q0)
(s3,q0): (s3,q0), (s2,q0)
(s3,q1): (s3,q1)           the letter at s2 contains g, which q1 cannot read
```

The accepting product states are $(s_1, q_1)$ and $(s_3, q_1)$.

Step 3: nested DFS, visiting successors in the listed order.

```
blue enter (s0,q0), stack [(s0,q0)]
blue enter (s1,q0), stack [(s0,q0), (s1,q0)]
blue enter (s2,q0), stack [(s0,q0), (s1,q0), (s2,q0)]
   successor (s0,q0) is already blue
blue post  (s2,q0), not accepting
blue enter (s3,q0), stack [(s0,q0), (s1,q0), (s3,q0)]
   successors (s3,q0) and (s2,q0) are already blue
blue post  (s3,q0), not accepting
blue post  (s1,q0), not accepting
blue enter (s1,q1), stack [(s0,q0), (s1,q1)]
blue enter (s3,q1), stack [(s0,q0), (s1,q1), (s3,q1)]
   successor (s3,q1) is already blue
blue post  (s3,q1), accepting, seed := (s3,q1)
   red visit (s3,q1)
   successor (s3,q1) is the seed: cycle found
```

The stack gives the prefix, and the red path gives the cycle. Projecting on the system yields the lasso $s_0\, s_1\, s_3^\omega$: a request at $s_1$ is followed by waiting forever. The property fails.

### Example 2: nested search that fails first, with shared red marks

Consider a product graph with initial state $A$ and accepting states $B$ and $E$, with successors listed in order:

```
A: B, E
B: C
C: D
D: C
E: F
F: C, E
```

```
blue enter A, stack [A]
blue enter B, stack [A, B]
blue enter C, stack [A, B, C]
blue enter D, stack [A, B, C, D]
   successor C is already blue
blue post  D, not accepting
blue post  C, not accepting
blue post  B, accepting, seed := B
   red visit B
   red visit C
   red visit D
   successor C of D is already red
   no successor equals B: no cycle through B; red set is now {B, C, D}
blue enter E, stack [A, E]
blue enter F, stack [A, E, F]
   successor C is already blue; successor E is already blue
blue post  F, not accepting
blue post  E, accepting, seed := E
   red visit E
   red visit F
   successor C of F is already red, so it is not revisited
   successor E of F is the seed: cycle found

Counterexample: prefix A, E; cycle E, F, E.
```

The first seed $B$ reaches the cycle $C\, D\, C$, which contains no accepting state, so no accepting cycle is reported. The shared red mark on $C$ saves work in the second search. The proof above guarantees that skipping $C$ cannot hide a cycle through $E$: any path from $C$ back to $E$ would place the earlier seed $B$ on a cycle, and the search from $B$ would already have reported that cycle.

### Example 3: the GBA of $p\, \mathbf{U}\, q$

The closure of $\varphi = p\, \mathbf{U}\, q$ is $\{p, q, \varphi\}$ with their negations. The elementary sets are determined by the values of $(p, q, \varphi)$ with two restrictions: $q$ forces $\varphi$, and $\neg p \land \neg q$ forces $\neg \varphi$. There are five.

```
B1 = {p, q, φ}
B2 = {¬p, q, φ}
B3 = {p, ¬q, φ}
B4 = {p, ¬q, ¬φ}
B5 = {¬p, ¬q, ¬φ}
```

The transition rule says that $\varphi \in B$ iff $q \in B$ or ($p \in B$ and $\varphi \in B'$). Therefore:

- from $B_1$ and $B_2$, the right side is true, so every $B'$ is allowed;
- from $B_3$, the set $B'$ must contain $\varphi$, so $B'$ is one of $B_1, B_2, B_3$;
- from $B_4$, the set $B'$ must omit $\varphi$, so $B'$ is $B_4$ or $B_5$;
- from $B_5$, the right side is false, so every $B'$ is allowed.

Each state reads exactly the letter $B \cap AP$. The initial states contain $\varphi$: $B_1, B_2, B_3$. The acceptance set is $\{B : \varphi \notin B \text{ or } q \in B\} = \{B_1, B_2, B_4, B_5\}$.

Check three words.

- The word $\{p\}^\omega$ can only use $B_3$ and $B_4$. Starting from $B_3$, it must remain in $B_3$, which is not accepting, so the word is rejected, as required.
- The word $\{p\}\, \{q\}\, \emptyset^\omega$ has the run $B_3\, B_2\, B_5^\omega$, which is accepting.
- The word $\emptyset^\omega$ has only $B_5$ available, and $B_5$ is not initial, so it is rejected.

A brute-force check confirmed that this automaton agrees with the semantics of $p\, \mathbf{U}\, q$ on all lasso words with a prefix of length at most 2 and a period of length at most 2.

## Common mistakes

- Building an automaton for $\varphi$ and testing for a cycle. The search must be for an accepting cycle in the product with $A_{\neg\varphi}$.
- Starting a red search in preorder. Take the graph $A \longrightarrow B$, $B \longrightarrow C$, $C \longrightarrow B$, with $A$ and $B$ accepting. Starting at $A$ in preorder would mark $B$ and $C$ red without finding $A$. The later red search from $B$ would then find its successor $C$ already red and miss the cycle. Postorder processes $B$ first.
- Clearing red marks between red searches in order to be safe. The search remains correct, but it becomes quadratic.
- Assuming that bitstate hashing proves a property. A collision makes the search skip states, so an error-free result does not establish correctness.
- Reporting a counterexample as soon as blue search closes a cycle. A cycle closed by a blue edge may avoid every accepting state, so the accepting seed must lie on the cycle that is reported.
- Using a deterministic Büchi automaton because determinization works for finite automata. It does not work here: some $\omega$-regular languages, such as $\mathbf{F}\, \mathbf{G}\, p$, have no deterministic Büchi automaton.
- Reading the product with inconsistent conventions. Fix whether the automaton reads the label of the source state or of the target state, and apply it to the initial state as well.

## Exercises

### Exercise 1

State the acceptance condition of an NBA and the emptiness criterion in terms of reachability and cycles.

<details><summary>Solution</summary>

A run is accepting if it visits some state of $F$ infinitely often. $L(A)$ is nonempty iff an accepting state is reachable from an initial state and lies on a cycle.

</details>

### Exercise 2

Give an NBA for $\mathbf{F}\, \mathbf{G}\, p$ and explain why it needs nondeterminism.

<details><summary>Solution</summary>

Take states $q_0$ (initial) and $q_1$ (accepting), with $q_0 \xrightarrow{\top} q_0$, $q_0 \xrightarrow{p} q_1$ and $q_1 \xrightarrow{p} q_1$. The automaton guesses the position after which $p$ always holds. Suppose a deterministic automaton accepted this language. Since $\{p\}^\omega$ is accepted, its run reaches an accepting state after some finite block of letters $\{p\}$. After that block and a letter $\emptyset$, the continuation $\{p\}^\omega$ must again be accepted, so another finite block of $\{p\}$ reaches an accepting state. Repeating this builds a word with infinitely many letters $\emptyset$ and infinitely many accepting visits, which is wrongly accepted.

</details>

### Exercise 3

Give an NBA for $\mathbf{G}\, \mathbf{F}\, p$, with a deterministic transition function.

<details><summary>Solution</summary>

Take states $q_0$ (initial) and $q_1$ (accepting). On a letter with $p$, go to $q_1$ from both states. On a letter without $p$, go to $q_0$ from both states. A run visits $q_1$ exactly after each letter with $p$, so it is accepting iff $p$ occurs infinitely often.

</details>

### Exercise 4

Using the GBA of Example 3, give the accepting run on $\{p\}\, \{p, q\}\, \emptyset\, \{q\}^\omega$, and show why the same word has no accepting run from $B_4$.

<details><summary>Solution</summary>

The run is $B_3\, B_1\, B_5\, B_2^\omega$. It starts at an initial state, follows the rules, since $B_3$ may go to $B_1$, $B_1$ to any state and $B_5$ to any state, and it visits $B_2$ infinitely often. $B_4$ is not initial, so it cannot begin a run at all. A run from $B_4$ would also be stuck at the second letter, because $B_4$ allows only $B_4$ and $B_5$, and neither reads a letter containing $q$.

</details>

### Exercise 5

Degeneralize this GBA: states $u, v, w$, all initial, with all transitions between states permitted, where $u$ reads letters with $p$, $v$ reads letters with $q$, and $w$ reads every letter. The acceptance sets are $F_1 = \{u\}$ and $F_2 = \{v\}$. State the language and the resulting NBA.

<details><summary>Solution</summary>

The language is $\mathbf{G}\, \mathbf{F}\, p \land \mathbf{G}\, \mathbf{F}\, q$. A run must use $u$ and $v$ infinitely often, and it can use $w$ at all other positions.

The NBA has states $Q \times \{1, 2\}$. Each state reads the same letters as its first component. The initial states are $(u,1), (v,1), (w,1)$, and the accepting set is $\{(u,1)\}$. From $(u,1)$ every transition goes to copy 2. From $(v,1)$ and $(w,1)$ every transition stays in copy 1. From $(v,2)$ every transition goes to copy 1. From $(u,2)$ and $(w,2)$ every transition stays in copy 2. Every other state is non-accepting. The run visits $(u,1)$ infinitely often iff the original run uses both $u$ and $v$ infinitely often.

</details>

### Exercise 6

Run nested DFS on the graph with initial $A$, accepting states $\{A, B\}$, and edges $A \longrightarrow B$, $B \longrightarrow C$, $C \longrightarrow B$.

<details><summary>Solution</summary>

```
blue enter A, stack [A]
blue enter B, stack [A, B]
blue enter C, stack [A, B, C]
   successor B is already blue
blue post  C, not accepting
blue post  B, accepting, seed := B
   red visit B
   red visit C
   successor B of C is the seed: cycle found
```

The prefix is $A, B$, and the cycle is $B, C, B$. The seed $B$ is processed before $A$, which is precisely why the mistake in the preorder variant does not arise.

</details>

### Exercise 7

Show that the theorem of nested DFS fails if red search treats "already blue" as a stopping condition instead of "already red".

<details><summary>Solution</summary>

Take the graph of Exercise 6. When the seed $B$ is processed, the state $C$ is blue. A red search that stops at blue states would stop immediately at $C$ and report nothing, so the cycle $B, C, B$ is missed. Red search must traverse blue states and stop only at red states.

</details>

### Exercise 8

Check $\mathbf{G}\, \mathbf{F}\, g$ on the system of Example 1 by constructing the product with an automaton for $\mathbf{F}\, \mathbf{G}\, \neg g$, and give the counterexample.

<details><summary>Solution</summary>

Take states $q_0$ (initial) and $q_1$ (accepting), with $q_0 \xrightarrow{\top} q_0$, $q_0 \xrightarrow{\neg g} q_1$ and $q_1 \xrightarrow{\neg g} q_1$. At $s_0$, the label has no $g$, so the initial product states are $(s_0, q_0)$ and $(s_0, q_1)$. The product contains $(s_3, q_1)$ with a self-loop, reachable by $(s_0, q_1), (s_1, q_1), (s_3, q_1)$, since none of $s_0, s_1, s_3$ has $g$ in its label. Thus a reachable accepting cycle exists, and it projects to $s_0\, s_1\, s_3^\omega$, which has no $g$ at all.

</details>

### Exercise 9

Prove that a run of a GBA, lifted to the degeneralized automaton, visits $F' = F_1 \times \{1\}$ infinitely often iff the original run visits every $F_i$ infinitely often.

<details><summary>Solution</summary>

Let a run visit every $F_i$ infinitely often. Its counter advances from $i$ to $i + 1$ at the first visit to $F_i$ after arriving in copy $i$. Since every set is visited infinitely often, the counter cycles through $1, \dots, m$ forever. Each cycle includes a visit to $F_1$ in copy 1, because that is the event that moves the counter out of copy 1. Hence $F_1 \times \{1\}$ is visited infinitely often.

Conversely, let $F_1 \times \{1\}$ be visited infinitely often. Each such visit moves the counter to 2, and returning to copy 1 requires moving through copies $2, \dots, m$, which happens only upon visits to $F_2, \dots, F_m$ in turn. The infinite number of returns gives infinitely many visits to each $F_i$. $\square$

</details>

### Exercise 10

Explain, with a concrete scenario, why partial-order reduction cannot in general preserve properties with $\mathbf{X}$.

<details><summary>Solution</summary>

Two independent assignments $a$ and $b$ commute: both orders reach the same state. Suppose that $a$ alone changes proposition $p$, and $b$ changes no proposition. The orders $a, b$ and $b, a$ differ in when $p$ changes: the first has $p$ at position 1, and the second has it at position 2. The formula $\mathbf{X}\, p$ distinguishes them. The reduction keeps a single representative order, and it can keep the wrong one. Formulas without $\mathbf{X}$ cannot count these steps, so a reduction can preserve them when it maintains a suitable visibility condition.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define an NBA, accepting runs and the product with a Kripke structure.
- State the reduction of LTL model checking to accepting cycle detection.
- Build the elementary sets and the GBA of a small LTL formula, and degeneralize it.
- Trace nested DFS on an unseen graph, and give the counterexample.
- Explain why postorder and shared red marks are both needed, and prove the correctness theorem.
- State what SPIN's reductions give up.

## Materials

- Baier and Katoen, Principles of Model Checking. Read the chapter Regular Properties for Büchi automata and nested depth-first search, the chapter Linear Temporal Logic for the elementary set construction, and the chapter Partial Order Reduction for the reduction. These chapter names were confirmed from the book's table of contents, and specific section numbers were not.
- Holzmann, The Model Checker SPIN, IEEE Transactions on Software Engineering 1997. Read it for how an industrial explicit-state tool combines on-the-fly checking, partial-order reduction and compact state storage.
- [SPIN model checker.](https://spinroot.com/) Use the site for the tool, its documentation and the Promela language when you want to try examples.
