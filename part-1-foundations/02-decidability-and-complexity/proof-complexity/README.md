# Proof Complexity

Part 1, Chapter 2: Decidability and Complexity.

## Objective

Explain why resolution proofs of the pigeonhole principle are exponential and what this means for CDCL solvers.

## Why this matters

NP-completeness says little about why a particular formula defeats a solver. Proof complexity gives a sharper answer: on an unsatisfiable input, a [CDCL solver](../../../part-2-core-reasoning/04-sat/cdcl/) in effect writes down a resolution proof, so its running time cannot be less than the size of the shortest resolution proof. If that size is exponential, then no heuristic, restart policy or implementation effort can save the solver, and you must change the encoding or the proof system. This is the reasoning behind [symmetry breaking and preprocessing](../../../part-2-core-reasoning/04-sat/preprocessing-and-inprocessing/), cardinality reasoning, [proof formats such as DRAT](../../../part-2-core-reasoning/04-sat/proofs-and-certificates/), and new-atom techniques in [DPLL(T)](../../../part-2-core-reasoning/05-smt/dpllt/). As an applied scientist, you will use it to decide whether a timeout calls for a better heuristic or a different formulation.

## Prerequisites

- [Proof Systems](../../01-mathematical-logic/proof-systems/), for resolution.
- [Soundness and Completeness](../../01-mathematical-logic/soundness-and-completeness/), for refutational completeness of resolution.
- [Reductions and NP-Completeness](../reductions-and-np-completeness/), for NP, coNP and the Tseitin encoding.

## Lesson

### Proof systems in general

Cook and Reckhow (1979) gave a definition that covers all propositional proof systems. A proof system for UNSAT is a polynomial-time computable predicate $V(F, \pi)$ such that a CNF $F$ is unsatisfiable if and only if there is a string $\pi$ with $V(F, \pi)$ true. The string $\pi$ is a refutation of $F$. The first condition direction is completeness, and the second is soundness. Polynomial-time checking is what makes a proof a certificate.

A proof system is polynomially bounded if there is a polynomial $q$ such that every unsatisfiable $F$ has a refutation of size at most $q(|F|)$.

Theorem (Cook and Reckhow, 1979). A polynomially bounded proof system exists if and only if $\mathrm{NP} = \mathrm{coNP}$.

Proof. Suppose $V$ is polynomially bounded. Then UNSAT is in NP, with a refutation as the certificate. UNSAT is coNP-complete, so [every coNP language lies in NP](../reductions-and-np-completeness/), which gives $\mathrm{NP} = \mathrm{coNP}$. Conversely, if $\mathrm{NP} = \mathrm{coNP}$, then UNSAT has a polynomial-time verifier with polynomially long certificates, and that verifier is a polynomially bounded proof system. $\square$

This motivates the research program: prove lower bounds for stronger and stronger proof systems, each a step toward $\mathrm{NP} \ne \mathrm{coNP}$. For a practitioner, the results have a direct reading, since each solver architecture corresponds to a proof system.

A system $A$ polynomially simulates a system $B$ if there is a polynomial-time function that translates each $B$-refutation of $F$ into an $A$-refutation of $F$. If $A$ simulates $B$ and $B$ has short proofs of some family, then so does $A$.

### Resolution and its restrictions

The resolution rule derives $C \lor D$ from $C \lor x_1$ and $D \lor \neg x_1$. A resolution refutation of a CNF $F$ is a sequence of clauses ending in the empty clause $\bot$, where each clause is in $F$ or is derived from two earlier clauses. Its size is the number of clauses. Its width is the number of literals in its largest clause.

A refutation has a dependency graph, which is a directed acyclic graph.

- A refutation is tree-like if each derived clause is used at most once. Reuse requires deriving the clause again.
- A refutation is regular if no variable is resolved on twice along a path from a source to the empty clause.
- General resolution has neither restriction.

Exponential separations are known: Ben-Sasson, Impagliazzo and Wigderson (2004) gave formulas with polynomial-size general refutations for which all tree-like refutations have exponential size.

### DPLL corresponds to tree-like resolution

Theorem. If DPLL, with unit propagation treated as branching where one side fails at once, explores a search tree with $L$ leaves on an unsatisfiable $F$, then $F$ has a tree-like resolution refutation with at most $2L - 1$ clauses.

Proof. Each leaf has a partial assignment that falsifies some clause of $F$, and the leaf is labeled by that clause. Process internal nodes bottom-up. Suppose that a node branches on $x_1$, and that its children are labeled $C_1$ and $C_2$, where each label is falsified by the assignment at the child. If $C_1$ does not contain $x_1$ in the falsified polarity, then $C_1$ is already falsified by the parent's assignment, so label the parent with $C_1$. The same applies to $C_2$. Otherwise, $C_1$ contains one literal of $x_1$ and $C_2$ contains the other, so their resolvent is falsified by the parent's assignment, and it labels the parent. The root's assignment is empty, so its label is $\bot$. This has at most one derived clause per internal node, and there are $L - 1$ internal nodes. $\square$

Conversely, a tree-like refutation can be read top-down as a decision procedure of no larger size. So the shortest tree-like refutation and the smallest DPLL tree, under the best possible branching, have essentially the same size.

### CDCL corresponds to general resolution

Conflict analysis is resolution. On a conflict, the solver starts with the falsified clause, and repeatedly resolves it with the reason clause of a literal on the trail, until a stopping condition such as the first unique implication point holds. Each learned clause therefore has a resolution derivation with at most one step for each literal on the trail, and thus at most one step per variable.

Theorem. If a CDCL solver, with any decision heuristic, restart policy or clause deletion policy, ends with UNSAT after $c$ conflicts on a formula with $v$ variables, then $F$ has a resolution refutation with $O(c \cdot v)$ derived clauses.

Proof. Concatenate the derivations of the learned clauses in order, followed by the derivation from the final conflict at decision level 0. Each derivation has at most $v$ steps and uses only earlier clauses. Deleting a clause only reduces what the solver may use, so a deleted clause remains available in the proof. The last derivation ends with $\bot$. $\square$

This is the theorem that makes lower bounds relevant. A lower bound of $S$ on the size of resolution refutations gives a lower bound of $S / v$ on the number of conflicts, for every configuration of a standard CDCL solver. It also covers preprocessing that consists of resolution steps and subsumption, such as bounded variable elimination, as long as no new variables are introduced.

There is a partial converse. Pipatsrisawat and Darwiche (2011) and Atserias, Fichte and Thurley (2011) showed that CDCL with restarts, given suitable nondeterministic decisions, polynomially simulates general resolution. So on any formula with short resolution proofs, some sequence of choices gives a short run, although a practical heuristic need not find it. Atserias and Müller (2019) showed that finding short resolution refutations is NP-hard to approximate in the following sense: resolution is not automatable unless $\mathrm{P} = \mathrm{NP}$. Whether CDCL without restarts polynomially simulates general resolution is, to the extent of the sources listed here, an open question, so check the current literature before relying on it.

### The pigeonhole principle

For $n \ge 1$, the formula $\mathrm{PHP}^{n+1}_n$ says that $n + 1$ pigeons fit into $n$ holes with no shared hole. It has variables $p_{i,j}$, for pigeon $i \in [n + 1]$ and hole $j \in [n]$, meaning that pigeon $i$ sits in hole $j$. It has these clauses.

$$
P_i = \bigvee_{j=1}^{n} p_{i,j} \quad (i \in [n + 1]), \qquad H_{i,i',j} = \neg p_{i,j} \lor \neg p_{i',j} \quad (i < i',\ j \in [n]).
$$

There are $n(n + 1)$ variables and $(n + 1) + n \binom{n+1}{2}$ clauses, so the size is polynomial in $n$.

The formula is unsatisfiable by a one-line counting argument. Resolution cannot count: it only manipulates clauses, and each clause only records a disjunction. This is the intuition, and the theorem below makes it precise.

Theorem (Haken, 1985). Every resolution refutation of $\mathrm{PHP}^{n+1}_n$ has size $2^{\Omega(n)}$. Specifically, for $n \ge 4$, its size is at least $(10/9)^{\lfloor n/4 \rfloor}$.

The proof below follows the simplified restriction argument of Beame and Pitassi (1996), and the constants have been recomputed for this presentation. It has three parts: critical assignments, a lemma stating that a refutation must contain a clause with many positive variables after a monotonization, and a restriction argument that removes such clauses when the refutation is small.

### Critical assignments and monotonization

Fix $m$, and work with $\mathrm{PHP}^{m+1}_m$. An assignment is $i$-critical if it matches the $m$ pigeons other than $i$ one-to-one with the $m$ holes, and sets all other variables to false. In such an assignment, pigeon $i$ has no hole, and every hole holds exactly one pigeon. A critical assignment is one that is $i$-critical for some $i$. It satisfies all clauses of $\mathrm{PHP}^{m+1}_m$, except $P_i$.

For a clause $C$, define the monotonization $C^+$ by replacing each negative literal $\neg p_{i,j}$ by the disjunction $\bigvee_{i' \ne i} p_{i',j}$.

Lemma 1. $C$ and $C^+$ have the same value under each critical assignment.

Proof. In a critical assignment, hole $j$ holds exactly one pigeon. So $p_{i,j}$ is false exactly when some other pigeon is in hole $j$, which is the disjunction above. $\square$

### The width lemma

Lemma 2. Let $m \ge 3$, and let $\pi$ be a sequence of clauses ending in $\bot$, in which each clause is an axiom of $\mathrm{PHP}^{m+1}_m$ or follows from two earlier clauses by a rule that is sound on critical assignments. Then $\pi$ contains a clause $C$ such that $C^+$ has at least $\frac{2}{9}(m + 1)^2$ variables.

Proof. For a clause $C$, define its complexity $\mu(C)$ as the smallest size of a set $S$ of pigeons such that every critical assignment that satisfies all $P_i$ with $i \in S$ also satisfies $C$. The full set $S = [m + 1]$ always qualifies, since no critical assignment satisfies all $P_i$. So $\mu$ is defined.

The measure has these properties.

- $\mu(P_i) \le 1$, since $S = \{i\}$ works.
- $\mu(H_{i,i',j}) = 0$, since each critical assignment satisfies these clauses.
- $\mu(\bot) = m + 1$. If $|S| \le m$, then there is a pigeon $i \notin S$, and an $i$-critical assignment satisfies all $P_{i'}$ with $i' \in S$ and falsifies $\bot$.
- $\mu(C) \le \mu(A) + \mu(B)$ when $C$ follows from $A$ and $B$. The union of sets for $A$ and $B$ forces both premises, and soundness then forces $C$.

Consider the first clause $C$ in $\pi$ with $\mu(C) \ge (m + 1)/3$. It exists because $\mu(\bot) = m + 1$. It is not an axiom, because $(m + 1)/3 > 1$. Its two premises have complexity less than $(m + 1)/3$, so subadditivity gives $s = \mu(C) < \frac{2}{3}(m + 1)$. Let $S$ be a minimum set for $C$, with $|S| = s$.

Fix $i \in S$ and $i' \notin S$. Since $S \setminus \{i\}$ is too small, there is a critical assignment $\alpha$ that satisfies all $P_{i''}$ with $i'' \in S \setminus \{i\}$ and falsifies $C$. Since $S$ forces $C$, $\alpha$ cannot satisfy $P_i$, so $\alpha$ is $i$-critical. Pigeon $i'$ is matched by $\alpha$ to a hole $j$. Let $\alpha'$ be $\alpha$ modified so that pigeon $i$ takes hole $j$ and pigeon $i'$ loses it. Then $\alpha'$ is $i'$-critical. Since $i' \notin S$, it satisfies all $P_{i''}$ with $i'' \in S$, so it satisfies $C$.

By Lemma 1, $C^+$ is false under $\alpha$ and true under $\alpha'$. The two assignments differ only in that $p_{i,j}$ goes from false to true, and $p_{i',j}$ goes from true to false. Since $C^+$ has only positive literals, it contains $p_{i,j}$.

For a fixed $i \in S$, use the same assignment $\alpha$ for all $i' \notin S$. The pigeons $i' \notin S$ occupy different holes in $\alpha$, so $C^+$ contains at least $m + 1 - s$ different variables $p_{i,j}$. Summing over all $i \in S$ gives at least $s(m + 1 - s)$ variables in $C^+$.

The function $s(m + 1 - s)$ is concave in $s$, so on the interval $[\frac{1}{3}(m + 1), \frac{2}{3}(m + 1)]$, it attains its minimum at an endpoint, and both endpoints give $\frac{2}{9}(m + 1)^2$. $\square$

### Removing wide clauses by restriction

Call a clause $C$ wide if $C^+$ has at least $w$ variables, with $w = n(n + 1)/10$ here. The value of $w$ stays fixed during the argument.

A restriction $\rho$ for a pigeon $i_0$ and hole $j_0$ sets $p_{i_0,j_0} = 1$, sets $p_{i_0,j} = 0$ for $j \ne j_0$, and sets $p_{i,j_0} = 0$ for $i \ne i_0$. It removes one pigeon and one hole.

Lemma 3. Restricting $\mathrm{PHP}^{m+1}_m$ with $\rho$ gives exactly $\mathrm{PHP}^{m}_{m-1}$ on the remaining pigeons and holes, after removing satisfied clauses. Restricting a refutation gives a sequence that satisfies the hypothesis of Lemma 2 for the smaller formula. If $C$ survives $\rho$, then $(C \restriction \rho)^+$ is contained in $C^+$.

Proof. The clause $P_{i_0}$ is satisfied. A clause $P_i$ with $i \ne i_0$ loses the literal $p_{i,j_0}$, so it becomes the pigeon clause on the remaining holes. A clause $H$ containing $i_0$ or $j_0$ has a literal $\neg p$ on a variable set to 0, unless that variable is $p_{i_0,j_0}$, and in that case the other literal is $\neg p_{i',j_0}$, which is true. So all such clauses are satisfied. The other clauses $H$ are unchanged.

Restriction is sound, so each restricted clause still follows from its restricted premises, and $\bot$ stays $\bot$. Delete the satisfied clauses from the sequence. If a premise of a clause was satisfied and deleted, then the conclusion follows from the other premise alone or is implied by the restricted formula, and in either case the argument for subadditivity of $\mu$ still holds, since a satisfied premise has complexity 0.

For the containment, a positive literal of $C \restriction \rho$ is a positive literal of $C$, and a negative literal $\neg p_{i,j}$ of $C \restriction \rho$ has monotonization over the remaining pigeons, which is a subset of its monotonization over all pigeons. $\square$

Lemma 4. Let $W$ be a set of clauses over $\mathrm{PHP}^{m+1}_m$ with $m \le n$, each with $C^+$ having at least $w$ variables. Then some restriction satisfies at least one tenth of the clauses of $W$.

Proof. Choose $(i_0, j_0)$ uniformly from the $(m + 1)m$ pairs. If $C \in W$ and $C^+$ contains $p_{i_0,j_0}$, then $\rho$ satisfies $C$. To see this, if $C$ contains $p_{i_0,j_0}$, then it is satisfied directly. Otherwise, $C$ contains $\neg p_{i',j_0}$ for some $i' \ne i_0$, and $\rho$ sets $p_{i',j_0}$ to 0. Since $C^+$ has at least $w$ variables, the probability of this is at least

$$
\frac{w}{(m + 1) m} \ge \frac{n (n + 1) / 10}{(n + 1) n} = \frac{1}{10}.
$$

An averaging argument then gives a pair that satisfies at least one tenth of the clauses of $W$. $\square$

Proof of the theorem. Let $n \ge 4$ and $t = \lfloor n/4 \rfloor$, and suppose that a refutation has fewer than $(10/9)^t$ clauses. Then fewer than $(10/9)^t$ clauses are wide. Apply Lemma 4 repeatedly, $t$ times, each time removing a pigeon and a hole, and keep the set of remaining wide clauses. By Lemma 3, clauses that were not wide stay not wide, so only clauses originally wide can be wide later. After each restriction, at most nine tenths of the wide clauses remain, so at the end, the number of wide clauses is less than $(10/9)^t (9/10)^t = 1$. Hence no clause is wide.

What remains is a refutation in the sense of Lemma 2 for $\mathrm{PHP}^{m+1}_m$, with $m = n - t \ge 3n/4$. So $m \ge 3$, and $m + 1 > 3n/4$. By Lemma 2, a clause exists with at least

$$
\frac{2}{9}(m + 1)^2 > \frac{2}{9} \cdot \frac{9 n^2}{16} = \frac{n^2}{8} \ge \frac{n(n + 1)}{10} = w
$$

variables, where the last inequality holds when $n \ge 4$. That clause is wide, which is a contradiction. $\square$

The argument has a clear structure. Short refutations have few wide clauses, a few restrictions eliminate them all, and every refutation of what is left must contain a wide clause. Note that the bound is exponential in $n$, and the number of variables is about $n^2$, so in terms of the number of variables $v$, it is $2^{\Omega(\sqrt{v})}$.

### What this means for CDCL

Combining this theorem with the theorem on CDCL gives the following.

Corollary. Any CDCL solver that is a standard resolution-based solver, with any heuristics, restarts and clause deletion, needs at least $(10/9)^{\lfloor n/4 \rfloor} / (n(n+1))$ conflicts to refute $\mathrm{PHP}^{n+1}_n$.

The practical meaning is as follows.

- No heuristic fixes this. Tuning VSIDS, phase saving or restarts changes constants and bases, and it cannot remove the exponential growth.
- The barrier is the proof system. A different formulation, or a solver that can produce proofs in a stronger system, can have polynomial runs.
- Similar structure in real problems can have the same effect. Scheduling, resource allocation and register allocation problems often contain a counting argument: too many tasks, too few slots. A solver may then spend exponential effort proving something that a person proves in one line.
- A timeout on a counting-heavy UNSAT instance should therefore make you suspect a proof complexity barrier, rather than a poor search heuristic.
- The upper bound is also exponential. By Exercise 7, general resolution has refutations of $\mathrm{PHP}^{n+1}_n$ of size exactly $n(n + 3) 2^{n-2}$ under one construction, which is far below the $n!$-style behavior of naive tree search but still exponential.

The following table reports counts from a scratch script, which ran a plain DPLL with unit propagation, with the lowest-numbered variable tried true first. These are the leaf counts for that one fixed strategy, and they illustrate growth. They are not a claim about optimal search. The column for the construction in Exercise 7 counts resolution steps.

| $n$ | DPLL leaves, fixed order | Resolution steps, Exercise 7 |
|---|---|---|
| 2 | 2 | 10 |
| 3 | 9 | 36 |
| 4 | 52 | 112 |
| 5 | 375 | 320 |
| 6 | 3246 | 864 |
| 7 | 32781 | 2240 |

The remedies correspond to moving to a stronger proof system or changing the input.

- Cardinality detection and pseudo-Boolean solving use cutting planes, which have polynomial-size proofs of this principle.
- Symmetry breaking adds constraints that are not implied, but that preserve satisfiability. They can give polynomial-size resolution refutations, as Exercise 10 shows.
- Extended resolution adds definitions of new variables, and it has polynomial-size proofs by Cook's construction. Techniques such as bounded variable addition can sometimes rediscover useful definitions.
- Stronger proof formats accept such reasoning in checkable form. DRAT can express extended resolution. Heule, Kiesl and Biere (2017) showed short proofs of the pigeonhole principle without new variables in a system based on propagation redundancy.

### Stronger systems: extended resolution, cutting planes and Frege

Extended resolution (Tseitin, 1968) adds a rule that introduces a new variable $z$ as a definition, $z \leftrightarrow (\ell_1 \land \ell_2)$, in clause form. It preserves satisfiability but not logical equivalence. Cook (1976) used it for a polynomial-size proof of the pigeonhole principle, by reducing $\mathrm{PHP}^{n+1}_n$ to $\mathrm{PHP}^{n}_{n-1}$ with

$$
q_{i,j} \leftrightarrow p_{i,j} \lor (p_{i,n} \land p_{n+1,j}) \qquad (i \le n,\ j \le n - 1).
$$

The meaning is as follows. Remove pigeon $n + 1$ and hole $n$. If pigeon $i$ was in hole $n$, then it moves to the hole of pigeon $n + 1$. Each reduction step derives the clauses of the smaller instance in polynomially many steps, and there are $n$ such steps. Example 4 traces the first step.

Cutting planes works with linear inequalities over integers. A clause becomes an inequality, and the rules are addition, multiplication by a positive integer, and division with rounding. For instance, $x_1 + x_2 + x_3 \le 3/2$ becomes $x_1 + x_2 + x_3 \le 1$ for integers. It has polynomial-size proofs of the pigeonhole principle (Cook, Coullard and Turán, 1987), which appear in Exercise 8. It simulates resolution. It has its own exponential lower bounds, for example on clique-coloring formulas (Pudlák, 1997).

Frege systems are textbook Hilbert-style propositional calculi that manipulate arbitrary formulas. Extended Frege adds definitions, and it is polynomially equivalent to extended resolution. Buss (1987) gave polynomial-size Frege proofs of the pigeonhole principle. No superpolynomial lower bound is known for Frege or extended Frege, and this is a central open problem.

| System | Solver or tool it reflects | Short proofs of the pigeonhole principle |
|---|---|---|
| Tree-like resolution | DPLL. | No. |
| General resolution | CDCL. | No. |
| Cutting planes | Pseudo-Boolean solvers and integer arithmetic reasoning. | Yes. |
| Extended resolution | CDCL with definitions, and DRAT proofs. | Yes. |
| Frege | Formula-based proof calculi. | Yes. |

### Other hard families, and the size-width method

Haken's method started a broad theory. These are the other main hard families for resolution.

- Tseitin formulas on expander graphs (Urquhart, 1987) encode a parity contradiction, in which the sum of all charges disagrees with the sum of edge parities. Gaussian elimination solves them, which is one reason why some solvers add XOR reasoning.
- Random $k$-CNF with a clause density well above the threshold (Chvátal and Szemerédi, 1988). These are almost always unsatisfiable, and their resolution refutations are almost always exponentially large.

Ben-Sasson and Wigderson (2001) gave a general technique that reduces size lower bounds to width lower bounds. Let $w(F)$ be the maximum clause width in $F$, let $w(F \vdash \bot)$ be the smallest width of a refutation, and let $v$ be the number of variables.

$$
S_{\mathrm{tree}}(F) \ge 2^{w(F \vdash \bot) - w(F)}, \qquad S(F) \ge \exp\left( \Omega\left( \frac{(w(F \vdash \bot) - w(F))^2}{v} \right) \right).
$$

So short proofs are narrow. If a refutation must contain a wide clause while the input clauses are narrow, then the refutation is long. For $\mathrm{PHP}^{n+1}_n$, the input clauses $P_i$ are already wide, so the method needs a bounded-degree variant of the formula. Width also has an algorithmic meaning: bounded-width resolution is a polynomial-time algorithm, since there are only polynomially many clauses of bounded width.

### Beyond propositional logic

- QBF. Q-resolution (Kleine Büning, Karpinski and Flögel, 1995) extends resolution with universal reduction, which removes a universal literal from a clause when no existential variable in that clause occurs after it in the prefix. The proof complexity of QBF systems has a character of its own, and it informs the design of [QBF solvers](../../../part-2-core-reasoning/04-sat/qbf-and-model-counting/). Exercise 13 is a small example.
- SMT. The proof system of a lazy SMT solver depends on the atoms it may use. If DPLL(T) can use only atoms from the input, then some formulas need exponentially many theory lemmas, and adding a new atom can give a short proof, as Exercise 11 shows.
- First-order logic. The proof length of a theorem can be very sensitive to the use of lemmas, because a cut can shorten a proof by a large factor. This reappears in lemma generation for [saturation provers](../../../part-2-core-reasoning/06-first-order-proving/saturation-provers/).

## Worked examples

### Example 1: an explicit refutation of $\mathrm{PHP}^3_2$

The formula has 6 variables and 9 clauses.

```
P1: p11 or p12
P2: p21 or p22
P3: p31 or p32
H(1,2,1): not p11 or not p21      H(1,2,2): not p12 or not p22
H(1,3,1): not p11 or not p31      H(1,3,2): not p12 or not p32
H(2,3,1): not p21 or not p31      H(2,3,2): not p22 or not p32
```

The refutation follows the idea in Exercise 7. It first derives clauses that say "pigeon 1 or 2 is in hole $j$", and then uses them to exclude pigeon 3 from each hole.

```
 1. p11 or not p22        from P1 and H(1,2,2), on p12
 2. p11 or p21            from P2 and line 1, on p22
 3. p12 or not p21        from P1 and H(1,2,1), on p11
 4. p12 or p22            from P2 and line 3, on p21
 5. p21 or not p31        from line 2 and H(1,3,1), on p11
 6. not p31               from line 5 and H(2,3,1), on p21
 7. p22 or not p32        from line 4 and H(1,3,2), on p12
 8. not p32               from line 7 and H(2,3,2), on p22
 9. p32                   from P3 and line 6, on p31
10. empty clause          from line 9 and line 8, on p32
```

That is 10 resolution steps, which matches the formula $n(n + 3) 2^{n-2}$ for $n = 2$. A script checked each step.

### Example 2: a CDCL run and its resolution proof

Run CDCL on $\mathrm{PHP}^3_2$, deciding $p_{1,1}$ true first. The solver visits unit clauses in this order.

```
level 1: decide p11
         not p21    reason H(1,2,1)
         not p31    reason H(1,3,1)
         p22        reason P2
         p32        reason P3
         conflict:  H(2,3,2) = not p22 or not p32
```

Conflict analysis resolves backward along the trail, using the reasons, until one literal at the current level remains.

```
start:                 not p22 or not p32
with P3 on p32:        not p22 or p31                 two literals at level 1
with H(1,3,1) on p31:  not p11 or not p22             two literals at level 1
with P2 on p22:        not p11 or p21                 two literals at level 1
with H(1,2,1) on p21:  not p11                        one literal at level 1
```

The solver learns the unit clause $\neg p_{1,1}$ and backjumps to level 0, where propagation runs.

```
level 0: not p11    learned
         p12        reason P1
         not p22    reason H(1,2,2)
         not p32    reason H(1,3,2)
         p21        reason P2
         p31        reason P3
         conflict:  H(2,3,1) = not p21 or not p31
```

A conflict at level 0 means unsatisfiability. Analysis produces the rest of the proof.

```
start:                 not p21 or not p31
with P3 on p31:        not p21 or p32
with H(1,3,2) on p32:  not p12 or not p21
with P2 on p21:        not p12 or p22
with H(1,2,2) on p22:  not p12
with P1 on p12:        p11
with not p11 on p11:   empty clause
```

The run had 2 conflicts and 10 resolution steps, 4 for the learned clause and 6 for the final conflict. So the CDCL trace can be read as a resolution proof, as the theorem says. A script checked each resolution step.

### Example 3: critical assignments and the complexity measure

Take $m = 3$, so $\mathrm{PHP}^4_3$. Consider the clause $D = p_{1,1} \lor p_{1,2} \lor p_{2,1} \lor p_{2,2}$. It says that pigeon 1 or pigeon 2 sits in hole 1 or hole 2.

Monotonization. $D$ has only positive literals, so $D^+ = D$, with 4 variables.

Complexity. Compute $\mu(D)$.

- $S = \emptyset$ fails. Consider the 3-critical assignment with pigeon 1 in hole 3, pigeon 2 in hole 1, pigeon 4 in hole 2. It satisfies $D$, but we need a falsifying one. Since at most one of pigeons 1, 2 can use hole 3, $D$ is falsified only when one of pigeons 1, 2 is the missing pigeon and the other is in hole 3. For example, take pigeon 2 missing, pigeon 1 in hole 3, and pigeons 3, 4 in holes 1, 2. This falsifies $D$.
- $S = \{1\}$ fails, by that same assignment, since pigeon 1 is placed.
- $S = \{2\}$ fails by the symmetric assignment with pigeon 1 missing, and pigeon 2 in hole 3.
- $S = \{3\}$ and $S = \{4\}$ fail, by the same assignment with pigeon 2 missing.
- $S = \{1, 2\}$ works. If both are placed, then they occupy two different holes among three, so at least one is in hole 1 or 2, which satisfies $D$.

So $\mu(D) = 2$. The proof's window is $(m + 1)/3 \le \mu < 2(m + 1)/3$, that is, $4/3 \le \mu < 8/3$, and $\mu(D) = 2$ lies in that window. The lemma's count gives at least $s(m + 1 - s) = 2 \cdot 2 = 4$ variables in $D^+$, and $D^+$ has exactly 4 variables. So the bound is tight here. It also matches the proof's construction: for $i = 1$ and $i' \in \{3, 4\}$, the variables are $p_{1,1}$ and $p_{1,2}$.

A clause with a negative literal. Let $C = \neg p_{1,1} \lor p_{2,2}$. Then $C^+ = p_{2,1} \lor p_{3,1} \lor p_{4,1} \lor p_{2,2}$. Check it under the 4-critical assignment with pigeons 1, 2, 3 in holes 1, 2, 3. $C$ is true, since $p_{2,2}$ is true, and $C^+$ is true. Under the 4-critical assignment with pigeons 1, 2, 3 in holes 1, 3, 2, $C$ is false, since $p_{1,1}$ is true and $p_{2,2}$ is false. $C^+$ is false too: hole 1 is used by pigeon 1, and $p_{2,2}$ is false. On a noncritical assignment, the two may differ: the all-false assignment makes $C$ true and $C^+$ false.

A script confirmed $\mu(D) = 2$, $\mu(C) = 3$, $\mu(\bot) = 4$, and agreement of $C, C^+$ and of $D, D^+$ on all critical assignments.

### Example 4: Cook's extended resolution step for $n = 2$

Reduce $\mathrm{PHP}^3_2$ to $\mathrm{PHP}^2_1$. Remove pigeon 3 and hole 2, and introduce for $i = 1, 2$:

$$
q_{i,1} \leftrightarrow p_{i,1} \lor (p_{i,2} \land p_{3,1}).
$$

The target formula has clauses $q_{1,1}$, $q_{2,1}$ and $\neg q_{1,1} \lor \neg q_{2,1}$. Derive them by case analysis, which translates directly to resolution with the definition clauses.

Clause $q_{1,1}$. From $P_1$, either $p_{1,1}$ holds, and then $q_{1,1}$ holds, or $p_{1,2}$ holds. In the second case, $H_{1,3,2}$ gives $\neg p_{3,2}$, so $P_3$ gives $p_{3,1}$, and then $p_{1,2} \land p_{3,1}$ gives $q_{1,1}$. Clause $q_{2,1}$ is the same, with pigeon 2 and $H_{2,3,2}$.

Clause $\neg q_{1,1} \lor \neg q_{2,1}$. Suppose both hold. There are four cases.

- $p_{1,1}$ and $p_{2,1}$ contradict $H_{1,2,1}$.
- $p_{1,1}$ and $p_{3,1}$, from the second definition branch, contradict $H_{1,3,1}$.
- $p_{3,1}$ and $p_{2,1}$ contradict $H_{2,3,1}$.
- $p_{1,2}$ and $p_{2,2}$ contradict $H_{1,2,2}$.

The smaller formula has an immediate refutation. In general, the same argument has a polynomial number of steps for each level. Pigeon $i$ now appears "virtually" in the smaller problem, so the definition lets the proof remember a choice with a single variable, which resolution with the original variables cannot do. A script checked for $n = 2$ and $n = 3$ that the new clauses follow semantically from the corresponding old clauses, by enumerating assignments.

## Common mistakes

- Thinking that a lower bound on resolution proves $\mathrm{P} \ne \mathrm{NP}$ or $\mathrm{NP} \ne \mathrm{coNP}$. It only rules out one proof system, and stronger systems may still have short proofs.
- Blaming the heuristic for an exponential proof barrier. On a formula with only exponential resolution proofs, every standard CDCL configuration is exponential.
- Concluding that $\mathrm{PHP}$ is hard for all solvers. It is easy for systems with cardinality reasoning or extended variables, and also easy for a solver using symmetry breaking.
- Treating the bound as exponential in the number of variables directly. It is exponential in $n$, and the number of variables is $n(n + 1)$, so the bound is $2^{\Omega(\sqrt{v})}$.
- Confusing tree-like with general resolution. DPLL corresponds to tree-like resolution, and learned clauses are exactly what permits reuse in general resolution.
- Stating that CDCL with no restarts is known to simulate resolution. The known simulation uses restarts, and its decisions are nondeterministic, so it does not describe what a heuristic will do.
- Reading "polynomially simulates" as "runs in polynomial time on all easy formulas". The simulation result says that a short run exists, and finding a short proof is hard in general, by the non-automatability result.
- Assuming that Lemma 1 holds for all assignments. A clause and its monotonization agree only on critical assignments, as the all-false assignment shows.
- Assuming that a symmetry-breaking clause is implied by the formula. It preserves only satisfiability, so a proof using it needs a proof system with suitable redundancy rules, or an accompanying symmetry argument.
- Thinking that a short proof must be easy to find because it exists. Existence of a short proof and the ability to find it are different questions.

## Exercises

### Exercise 1

Define a proof system for UNSAT, polynomially bounded, and polynomial simulation. State why resolution is a proof system under this definition.

<details><summary>Solution</summary>

A proof system is a polynomial-time predicate $V(F, \pi)$ such that $F$ is unsatisfiable if and only if $V(F, \pi)$ holds for some $\pi$. It is polynomially bounded if some polynomial $q$ gives each unsatisfiable $F$ a refutation of size at most $q(|F|)$. System $A$ polynomially simulates $B$ if a polynomial-time function turns $B$-refutations of $F$ into $A$-refutations of $F$.

Resolution qualifies. A checker confirms that each clause is in $F$ or follows by the rule from earlier clauses, which takes polynomial time. Soundness of the rule and refutational completeness give the "if and only if".

</details>

### Exercise 2

Compute the number of variables and clauses of $\mathrm{PHP}^{n+1}_n$ as a function of $n$, and evaluate them at $n = 4$. Express the lower bound of the theorem in terms of the number of variables.

<details><summary>Solution</summary>

There are $n(n + 1)$ variables and $(n + 1) + n \binom{n+1}{2} = (n + 1) + n^2(n + 1)/2$ clauses. At $n = 4$, there are 20 variables and $5 + 4 \cdot 10 = 45$ clauses.

With $v = n(n + 1)$, $n = \Theta(\sqrt{v})$, so the bound is $2^{\Omega(\sqrt{v})}$.

</details>

### Exercise 3

In $\mathrm{PHP}^4_3$, compute $C^+$ for $C = \neg p_{1,2} \lor \neg p_{3,1} \lor p_{4,3}$. Find a critical assignment that falsifies both clauses, and an assignment that is not critical on which they differ.

<details><summary>Solution</summary>

$\neg p_{1,2}$ becomes $p_{2,2} \lor p_{3,2} \lor p_{4,2}$, and $\neg p_{3,1}$ becomes $p_{1,1} \lor p_{2,1} \lor p_{4,1}$. So

$$
C^+ = p_{2,2} \lor p_{3,2} \lor p_{4,2} \lor p_{1,1} \lor p_{2,1} \lor p_{4,1} \lor p_{4,3}.
$$

Critical falsifier. Set pigeon 1 in hole 2 and pigeon 3 in hole 1. Then hole 3 must be taken by pigeon 2, with pigeon 4 missing. Thus $p_{1,2}$ and $p_{3,1}$ are true and $p_{4,3}$ is false, which falsifies $C$. Every variable of $C^+$ is false in this assignment, since hole 2 holds only pigeon 1, hole 1 holds only pigeon 3, and pigeon 4 is missing.

Noncritical difference. The all-false assignment makes $C$ true, since $\neg p_{1,2}$ is true, and it makes $C^+$ false.

</details>

### Exercise 4

Using the theorem's proof, take $m = 8$. Determine the interval for $s$, and compute the minimum of $s(m + 1 - s)$ on this interval. Compare the result with $\frac{2}{9}(m + 1)^2$.

<details><summary>Solution</summary>

Here $m + 1 = 9$. The proof gives $3 \le s < 6$, so $s \in \{3, 4, 5\}$. The values of $s(9 - s)$ are $18, 20, 20$, and the minimum is 18. The formula gives $\frac{2}{9} \cdot 81 = 18$, and it agrees with the minimum. The bound of the lemma is reached at the endpoint $s = 3$.

</details>

### Exercise 5

Apply the restriction that places pigeon 4 in hole 3 to $\mathrm{PHP}^4_3$. Describe what happens to each clause type, and confirm that the result is $\mathrm{PHP}^3_2$.

<details><summary>Solution</summary>

The restriction sets $p_{4,3} = 1$, $p_{4,1} = p_{4,2} = 0$, and $p_{1,3} = p_{2,3} = p_{3,3} = 0$.

- $P_4 = p_{4,1} \lor p_{4,2} \lor p_{4,3}$ is satisfied.
- For $i \le 3$, $P_i = p_{i,1} \lor p_{i,2} \lor p_{i,3}$ loses $p_{i,3}$, so it becomes $p_{i,1} \lor p_{i,2}$.
- Clauses $H_{i,i',3}$ have a literal $\neg p_{i,3}$ for some $i \le 3$, which is true, so they are satisfied.
- Clauses $H_{i,4,j}$ with $j \le 2$ have the literal $\neg p_{4,j}$, which is true, so they are satisfied.
- Clauses $H_{i,i',j}$ with $i, i' \le 3$ and $j \le 2$ are unchanged.

What remains is three pigeon clauses over holes 1, 2 and the six hole clauses for these pigeons and holes, which is exactly $\mathrm{PHP}^3_2$.

</details>

### Exercise 6

The functional onto pigeonhole principle adds to $\mathrm{PHP}^{n+1}_n$ the clauses $\neg p_{i,j} \lor \neg p_{i,j'}$ for $j \ne j'$, meaning that each pigeon has at most one hole, and $\bigvee_i p_{i,j}$ for each $j$, meaning that each hole is occupied. Show that the lower bound proof goes through unchanged. Explain why adding clauses can leave a formula equally hard.

<details><summary>Solution</summary>

Two facts about the new clauses are needed.

Critical assignments satisfy the new clauses. A critical assignment gives each matched pigeon exactly one hole and gives the missing pigeon no hole, so the functional clauses hold. Each hole holds exactly one pigeon, so the onto clauses hold. Therefore, these clauses have $\mu = 0$, and Lemma 2 applies as before.

Restrictions preserve the form. For a restriction $(i_0, j_0)$, a functional clause for pigeon $i_0$ is satisfied, because at most one of its variables is $p_{i_0,j_0}$, and the other variable $p_{i_0,j'}$ is 0, which makes its negative literal true. A functional clause for pigeon $i \ne i_0$ with hole $j_0$ is satisfied, because $p_{i,j_0} = 0$. Other functional clauses are unchanged. The onto clause for $j_0$ is satisfied by $p_{i_0,j_0}$. The onto clause for $j \ne j_0$ loses $p_{i_0,j}$, so it becomes the onto clause on the remaining pigeons. So the restricted formula has the same form.

The rest of the proof uses only these two facts, so the same lower bound holds.

The reason why adding clauses does not help is that new axioms help only if they give new information on the hard assignments. Here, the new clauses are true on all critical assignments, so they cannot help to separate those assignments.

</details>

### Exercise 7

For $S \subseteq [n]$ with $|S| = n - k + 1$, let $D_{k,S} = \bigvee_{i \le k,\ j \in S} p_{i,j}$. Show that $D_{1,[n]} = P_1$, and that $D_{n+1,\emptyset} = \bot$. Give a derivation of $D_{k+1,S'}$ from clauses $D_{k,S' \cup \{j\}}$, and compute the exact total number of resolution steps. Compare this with the lower bound.

<details><summary>Solution</summary>

Base and end. For $k = 1$ and $S = [n]$, the clause is $\bigvee_j p_{1,j} = P_1$. For $k = n + 1$, $|S| = 0$, so the clause is $\bot$.

Step. Let $|S'| = n - k$, so $k$ holes are outside $S'$. Start with the accumulator $A = P_{k+1}$. For each hole $j \notin S'$:

1. Take $D_{k,S' \cup \{j\}}$, and for each $i \le k$, resolve on $p_{i,j}$ with $H_{i,k+1,j} = \neg p_{i,j} \lor \neg p_{k+1,j}$. This takes $k$ steps, and gives $\neg p_{k+1,j} \lor D_{k,S'}^*$, where $D_{k,S'}^* = \bigvee_{i \le k,\ j' \in S'} p_{i,j'}$.
2. Resolve with $A$ on $p_{k+1,j}$. This takes one step, removes $p_{k+1,j}$ from $A$, and adds $D_{k,S'}^*$.

After all $k$ holes, $A = \bigvee_{j' \in S'} p_{k+1,j'} \lor D_{k,S'}^* = D_{k+1,S'}$.

Count. Each target clause takes $k(k + 1)$ steps. There are $\binom{n}{n-k} = \binom{n}{k}$ target clauses at level $k + 1$. The total is

$$
\sum_{k=1}^{n} \binom{n}{k} k (k + 1) = \sum_k \binom{n}{k} k^2 + \sum_k \binom{n}{k} k = n(n + 1) 2^{n-2} + n 2^{n-1} = n(n + 3) 2^{n-2}.
$$

A script built this derivation for $n$ from 2 to 7, checked all steps and confirmed this count.

Comparison. The upper bound is $2^{n + O(\log n)}$ and the lower bound is $(10/9)^{\lfloor n/4 \rfloor}$, so both are exponential in $n$, with different bases. Note that the derivation reuses each clause $D_{k,S}$ in several later derivations, and a tree-like proof must derive it again each time.

</details>

### Exercise 8

Give a polynomial-size cutting planes refutation of $\mathrm{PHP}^{n+1}_n$.

<details><summary>Solution</summary>

Write clauses as inequalities over $0 \le p_{i,j} \le 1$. The pigeon clause is $\sum_j p_{i,j} \ge 1$, and the hole clause is $p_{i,j} + p_{i',j} \le 1$.

Step 1, per hole $j$. Prove by induction on $k$ that $\sum_{i \le k} p_{i,j} \le 1$. The case $k = 2$ is a hole clause. For the step from $k$ to $k + 1$, add $k - 1$ copies of $\sum_{i \le k} p_{i,j} \le 1$ to the $k$ inequalities $p_{i,j} + p_{k+1,j} \le 1$, with $i \le k$. This gives

$$
k \sum_{i \le k + 1} p_{i,j} \le (k - 1) + k = 2 k - 1.
$$

Dividing by $k$ and rounding gives $\sum_{i \le k + 1} p_{i,j} \le \lfloor (2 k - 1)/k \rfloor = 1$.

Step 2. Add over all holes, to get $\sum_{i, j} p_{i,j} \le n$.

Step 3. Add over all pigeons, to get $\sum_{i, j} p_{i,j} \ge n + 1$.

Step 4. Combining the two gives $0 \ge 1$, a contradiction.

Size. There are $O(n)$ holes, $O(n)$ induction steps for each hole, and $O(n)$ additions in each step. All coefficients are polynomial in $n$. So the refutation has polynomial size.

</details>

### Exercise 9

Prove that Cook's definitions yield the pigeon clauses of the smaller instance in general. That is, with $q_{i,j} \leftrightarrow p_{i,j} \lor (p_{i,n} \land p_{n+1,j})$, show from $\mathrm{PHP}^{n+1}_n$ that $\bigvee_{j \le n - 1} q_{i,j}$ holds for each $i \le n$, and that $\neg q_{i,j} \lor \neg q_{i',j}$ holds for $i < i' \le n$ and $j \le n - 1$.

<details><summary>Solution</summary>

Pigeon clause for $i \le n$. By $P_i$, some $p_{i,j}$ holds. If $j \le n - 1$, then $q_{i,j}$ holds. If $j = n$, then $H_{i,n+1,n}$ gives $\neg p_{n+1,n}$. By $P_{n+1}$, there is some $j' \le n - 1$ with $p_{n+1,j'}$. Then $p_{i,n} \land p_{n+1,j'}$ gives $q_{i,j'}$.

Hole clause. Suppose $q_{i,j}$ and $q_{i',j}$ hold. There are four cases.

- $p_{i,j}$ and $p_{i',j}$ contradict $H_{i,i',j}$.
- $p_{i,j}$ and $p_{n+1,j}$ contradict $H_{i,n+1,j}$.
- $p_{n+1,j}$ and $p_{i',j}$ contradict $H_{i',n+1,j}$.
- $p_{i,n}$ and $p_{i',n}$ contradict $H_{i,i',n}$.

Each case analysis has size polynomial in $n$ as a resolution derivation, and there are polynomially many clauses at each level and $n$ levels. Exhaustive enumeration in a script confirmed the entailment for $n = 2$ and $n = 3$.

</details>

### Exercise 10

Add symmetry-breaking clauses $S_{i,j,j'} = \neg p_{i,j} \lor \neg p_{i+1,j'}$ for each $i \le n$ and each $j' \le j$, which say that consecutive pigeons sit in increasing holes. Prove that the new formula has a resolution refutation with $O(n^3)$ steps. Then state why the clauses are safe to add, and what a proof checker must accept to validate this.

<details><summary>Solution</summary>

Let $Q_k = \bigvee_{j \ge k} p_{k,j}$. Note that $Q_1 = P_1$, and $Q_{n+1} = \bot$.

Inductive step, from $Q_k$ to $Q_{k+1}$. Fix $j' \le k$. Resolve $Q_k$ with $S_{k,j,j'}$, for each $j \ge k$, on $p_{k,j}$. This is allowed since $j' \le k \le j$. These $n - k + 1$ steps remove all literals of $Q_k$ and add only $\neg p_{k+1,j'}$, so the result is the unit clause $\neg p_{k+1,j'}$. Do this for each of the $k$ values of $j'$. Then resolve $P_{k+1}$ with these units, in $k$ steps, to obtain $Q_{k+1}$.

Count. The total is $\sum_{k=1}^{n} k(n - k + 2) = n(n + 1)(n + 5)/6$. A script built the derivation for $n$ from 2 to 8, and checked it and the count. For example, $n = 8$ takes 156 steps.

Safety. The clauses are not implied by the formula, but they preserve satisfiability. If a placement of pigeons in holes exists, then renaming pigeons so that holes increase with the pigeon index gives another placement, since the formula is symmetric under permuting pigeons, and this placement satisfies the new clauses.

Checker. A pure resolution checker cannot accept these clauses, since they are not resolvents. It must accept a rule that adds non-implied clauses while preserving satisfiability, such as a proof format that supports symmetry reasoning or redundancy rules. Otherwise, the tool must justify the symmetry-breaking step separately, for example with a proof of the symmetry. Without that, the final result is correct but not fully certified.

</details>

### Exercise 11

Consider the diamond formula over equality logic, with variables $x_0, \dots, x_n$, $y_i$ and $z_i$:

$$
\bigwedge_{i=0}^{n-1} \big( (x_i = y_i \land y_i = x_{i+1}) \lor (x_i = z_i \land z_i = x_{i+1}) \big) \land x_0 \ne x_n.
$$

A lazy SMT solver may use only the atoms in the formula, and must add theory lemmas that rule out theory-inconsistent assignments. Prove that it needs at least $2^n$ theory lemmas. Then show that with the new atoms $x_i = x_{i+1}$, a polynomial number of lemmas suffice.

<details><summary>Solution</summary>

Lower bound. For each $\pi \in \{y, z\}^n$, consider the Boolean assignment $A_\pi$ in which, for each $i$, the atoms on branch $\pi_i$ are true, the atoms on the other branch are false, and $x_0 \ne x_n$ holds. It satisfies the Boolean skeleton, and it is theory-inconsistent. So it must be excluded by a theory lemma.

A theory lemma is a valid clause, whose negation is a theory-inconsistent set $L$ of literals. To block $A_\pi$, $L$ must be contained in $A_\pi$. A subset of literals of $A_\pi$ is inconsistent only if it contains the literal $x_0 \ne x_n$ and positive equalities that connect $x_0$ to $x_n$. In the equality graph of $A_\pi$, each $x_i$ is a cut vertex, so this connection must use the whole chain, that is, all true atoms for each segment. Hence $L$ determines $\pi$, and a lemma blocks only one assignment $A_\pi$. So at least $2^n$ lemmas are needed.

Upper bound with new atoms. For each $i$, add the lemmas $(x_i = y_i \land y_i = x_{i+1}) \to x_i = x_{i+1}$ and $(x_i = z_i \land z_i = x_{i+1}) \to x_i = x_{i+1}$. Together with the Boolean skeleton, they give $x_i = x_{i+1}$ by Boolean reasoning, for each $i$. Add the lemma $\bigwedge_i (x_i = x_{i+1}) \to x_0 = x_n$. The Boolean formula is now unsatisfiable by propagation. This requires $2n + 1$ lemmas.

So the choice of atoms changes the proof system's power, with an exponential gap, in the same way as extension variables in propositional logic.

</details>

### Exercise 12

A customer's scheduling formula has 25 tasks and 24 time slots, with a constraint that no two tasks share a slot, and a large set of side constraints. Their CDCL solver times out on it, and they ask you to tune the heuristics. Write a recommendation, with reasons, using this topic's results. Propose at least three concrete changes.

<details><summary>Solution</summary>

Diagnosis. The conflict may have a hidden pigeonhole core. Any resolution-based solver then needs a number of conflicts growing exponentially with the number of tasks, regardless of heuristic settings, so tuning can only change the constants. First, confirm by extracting the part of the problem that contains only the tasks, slots and exclusivity. If that subproblem alone times out at sizes of this order and scales badly with $n$, then the diagnosis is supported. The lower bound is asymptotic, so this should be tested and not assumed.

Recommendations.

1. Add a preprocessing check: count tasks and slots, and report the conflict directly. This is the shortest proof.
2. Use a pseudo-Boolean or integer arithmetic encoding of the capacity constraints, or a solver with cardinality detection. Cutting planes has polynomial-size proofs of this principle.
3. Break symmetry among identical tasks and identical slots. By Exercise 10, an ordering constraint can yield polynomial-size resolution refutations. Only symmetries that the side constraints preserve may be used.
4. Add auxiliary variables with a sequential counter or similar encoding, which gives the solver new atoms to reason with. It offers a chance of a shorter proof, and it is a heuristic. Measure the effect on your instances.

Certification. If the answer must be certified, select a proof format that can validate the reasoning, because DRAT can express redundancy rules that plain resolution cannot, and a capacity argument may require a separate certificate.

</details>

### Exercise 13

Use Q-resolution to refute $\exists x_1\, \forall y_1\, (x_1 \lor y_1) \land (\neg x_1 \lor y_1)$. Explain why the universal reduction rule is sound for this prefix, and why $\forall y_1\, \exists x_1\, (x_1 \lor y_1) \land (\neg x_1 \lor \neg y_1)$ cannot be refuted, by evaluating it.

<details><summary>Solution</summary>

Refutation. In $x_1 \lor y_1$, the literal $y_1$ is universal, and no existential variable of the clause occurs after it in the prefix, so universal reduction gives $x_1$. In the same way, $\neg x_1 \lor y_1$ reduces to $\neg x_1$. Resolving gives $\bot$.

Soundness for this prefix. If a clause must hold for every value of $y_1$, then it must hold for the value that falsifies the literal $y_1$. Since all other variables in the clause were chosen before $y_1$, they cannot depend on that value. So the clause without $y_1$ must hold.

Second formula. This is $\forall y_1\, \exists x_1$. For $y_1 = \top$, the matrix requires $\neg x_1$, and for $y_1 = \bot$, it requires $x_1$. The strategy $x_1 = \neg y_1$ satisfies both. So the formula is true, and a sound system cannot refute it. Universal reduction does not apply to a clause such as $x_1 \lor y_1$ here, because the existential variable $x_1$ occurs after $y_1$ in the prefix and so may depend on it.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define proof systems and polynomial simulation, and prove the connection with NP and coNP.
- Prove that a DPLL search tree gives a tree-like refutation, and show how a CDCL trace gives a general resolution refutation.
- Write the pigeonhole clauses, and give a refutation for small $n$.
- Define critical assignments and monotonization, and prove their agreement.
- Define the complexity measure $\mu$, state its properties, and prove the width lemma.
- Describe the restriction argument, and derive the final bound with constants.
- State the corollary for CDCL, and explain which solver techniques it does and does not cover.
- Give polynomial-size proofs of the principle in cutting planes and in extended resolution, and explain why symmetry breaking also helps.
- State the size-width relation and name other hard families.
- Explain the corresponding point for DPLL(T) and new atoms.

## Materials

- Haken, The Intractability of Resolution, Theoretical Computer Science 1985. Read it for the original exponential lower bound by the bottleneck counting method.
- Biere, Heule, van Maaren and Walsh (editors), Handbook of Satisfiability, 2nd edition. Read it for the handbook's treatment of proof complexity, the connection between CDCL and resolution, and practical proof formats.
- Cook and Reckhow, The relative efficiency of propositional proof systems, Journal of Symbolic Logic, 1979. Read it for the general definition and the connection with NP and coNP.
- Beame and Pitassi, Simplified and improved resolution lower bounds, FOCS 1996. Read it for the restriction argument adapted in this topic.
- Ben-Sasson and Wigderson, Short proofs are narrow: resolution made simple, Journal of the ACM, 2001. Read it for the size-width relation.
- Ben-Sasson, Impagliazzo and Wigderson, Near optimal separation of tree-like and general resolution, Combinatorica, 2004. Read it for the gap between tree-like and general resolution.
- Cook, A short proof of the pigeon hole principle using extended resolution, SIGACT News, 1976. Read it for the reduction with definitions used in Example 4.
- Cook, Coullard and Turán, On the complexity of cutting-plane proofs, Discrete Applied Mathematics, 1987. Read it for cutting planes proofs of counting principles.
- Buss, Polynomial size proofs of the propositional pigeonhole principle, Journal of Symbolic Logic, 1987. Read it for the Frege upper bound.
- Urquhart, Hard examples for resolution, Journal of the ACM, 1987. Read it for Tseitin formulas on expander graphs.
- Chvátal and Szemerédi, Many hard examples for resolution, Journal of the ACM, 1988. Read it for lower bounds on random formulas.
- Pudlák, Lower bounds for resolution and cutting plane proofs and monotone computations, Journal of Symbolic Logic, 1997. Read it for lower bounds on cutting planes.
- Beame, Kautz and Sabharwal, Towards understanding and harnessing the potential of clause learning, Journal of Artificial Intelligence Research, 2004. Read it for an early formal treatment of clause learning as a proof system.
- Pipatsrisawat and Darwiche, On the power of clause-learning SAT solvers as resolution engines, Artificial Intelligence, 2011. Read it for the simulation of resolution by CDCL with restarts.
- Atserias, Fichte and Thurley, Clause-learning algorithms with many restarts and bounded-width resolution, Journal of Artificial Intelligence Research, 2011. Read it for a related simulation and its width perspective.
- Atserias and Müller, Automating resolution is NP-hard, FOCS 2019. Read it for the non-automatability result.
- Heule, Kiesl and Biere, Short proofs without new variables, CADE 2017. Read it for short proofs of the principle in a proof system with redundancy rules.
- Kleine Büning, Karpinski and Flögel, Resolution for quantified Boolean formulas, Information and Computation, 1995. Read it for Q-resolution.
