# Resolution and DPLL

Part 2, Chapter 4: SAT.

## Objective

Trace resolution, Davis-Putnam and DPLL by hand and compare their behavior.

## Why this matters

Every complete SAT algorithm in use descends from the two procedures in this topic. Davis-Putnam variable elimination returns as [bounded variable elimination](../preprocessing-and-inprocessing/), and DPLL search with learning becomes [CDCL](../cdcl/). The resolution rule is also the language of solver proofs, of [interpolation](../../05-smt/interpolation/) and of [first-order resolution](../../06-first-order-proving/first-order-resolution/). When you judge whether a query is hard for a solver, you are usually reasoning about the size of its resolution proofs.

## Prerequisites

- [Propositional logic](../../../part-1-foundations/01-mathematical-logic/propositional-logic/)
- [Normal forms and Skolemization](../../../part-1-foundations/01-mathematical-logic/normal-forms-and-skolemization/)
- [Proof systems](../../../part-1-foundations/01-mathematical-logic/proof-systems/)
- [Reductions and NP-completeness](../../../part-1-foundations/02-decidability-and-complexity/reductions-and-np-completeness/)

## Lesson

### CNF and notation

A literal is a variable $x_i$ or its negation $\neg x_i$. A clause is a disjunction of literals, treated as a set, so it has no repeated literals. A CNF formula is a conjunction of clauses, treated as a set. The empty clause $\bot$ is unsatisfiable, and the empty formula is valid. A clause is a tautology if it contains a literal and its negation.

A partial assignment $\rho$ is a set of literals containing no complementary pair. The formula $F|_\rho$ is obtained by deleting every clause that contains a literal of $\rho$ and deleting from the remaining clauses every literal whose negation is in $\rho$.

### The resolution rule

For clauses $C \lor x$ and $D \lor \neg x$, the resolution rule derives the resolvent $C \lor D$:

$$\frac{C \lor x \qquad D \lor \neg x}{C \lor D}$$

The variable $x$ is the pivot. A resolution derivation of a clause $E$ from $F$ is a sequence of clauses ending in $E$, in which each clause is in $F$ or is a resolvent of two earlier clauses. A refutation of $F$ is a derivation of $\bot$ from $F$. Write $F \vdash_{\mathrm{Res}} E$ if a derivation exists.

Theorem 1 (soundness). If $F \vdash_{\mathrm{Res}} E$, then $F \models E$.

Proof. It suffices to check one step. Let an assignment satisfy $C \lor x$ and $D \lor \neg x$. If $x$ is true, the second clause forces $D$ to be satisfied. If $x$ is false, the first clause forces $C$ to be satisfied. In both cases $C \lor D$ is satisfied. $\square$

Resolution is not complete for derivation of arbitrary implied clauses, since $(x_1) \models (x_1 \lor x_2)$ has no resolution derivation. It is complete for refutation, which is all a solver needs.

### Variable elimination

Let $F_x$ be the clauses of $F$ containing $x$, let $F_{\neg x}$ be the clauses containing $\neg x$, and let $F_0$ be the remaining clauses. Define

$$\mathrm{DP}_x(F) = F_0 \cup \{ C \lor D : (C \lor x) \in F_x,\ (D \lor \neg x) \in F_{\neg x},\ C \lor D \text{ is not a tautology} \}.$$

Theorem 2 (elimination). $F$ is satisfiable if and only if $\mathrm{DP}_x(F)$ is satisfiable. Moreover, any model of $\mathrm{DP}_x(F)$ extends to a model of $F$ by choosing a value for $x$.

Proof. If $\alpha$ satisfies $F$, then $\alpha$ satisfies each resolvent by Theorem 1, and $\alpha$ restricted to the variables other than $x$ still satisfies them because they do not mention $x$.

Conversely, let $\alpha$ satisfy $\mathrm{DP}_x(F)$ and not assign $x$. Suppose that there is a clause $C \lor x \in F_x$ with $C$ false under $\alpha$ and also a clause $D \lor \neg x \in F_{\neg x}$ with $D$ false under $\alpha$. Then $C \lor D$ is false under $\alpha$, so it is not a tautology, so it is in $\mathrm{DP}_x(F)$, which contradicts $\alpha$ being a model. So at least one side has all its clauses already satisfied. If every clause $C \lor x$ has $C$ true under $\alpha$, set $x$ false, which satisfies $F_{\neg x}$. Otherwise set $x$ true, which satisfies $F_x$, and $F_{\neg x}$ is satisfied by the case analysis. $\square$

Theorem 3 (refutational completeness). If $F$ is unsatisfiable, then $F \vdash_{\mathrm{Res}} \bot$.

Proof. Use induction on the number of variables in $F$. If there are none, $F$ is unsatisfiable only if $F = \{\bot\}$. Otherwise pick a variable $x$. By Theorem 2, $\mathrm{DP}_x(F)$ is unsatisfiable, and it has fewer variables, so it has a refutation. Every clause in it is in $F$ or is a resolvent of clauses in $F$, so prepending those resolutions gives a refutation of $F$. $\square$

### The Davis-Putnam procedure

Davis and Putnam (1960) designed their procedure as the propositional core of a first-order prover. It has three rules, which they named the one-literal rule, the affirmative-negative rule and the rule for eliminating atomic formulas.

```
DP(F):
    while F has clauses:
        if ⊥ is in F: return UNSAT
        if F has a unit clause (l): F := F|{l}                # one-literal rule
        else if a literal l is pure in F: F := F|{l}          # affirmative-negative rule
        else: choose a variable x; F := DP_x(F)               # elimination
    return SAT
```

A literal is pure if its negation does not occur in the formula.

Lemma 4. If $(l) \in F$, then $F$ is equivalent to $\{l\} \land F|_{\{l\}}$, so $F$ and $F|_{\{l\}}$ are equisatisfiable. If $l$ is pure in $F$, then $F$ and $F|_{\{l\}}$ are equisatisfiable, though in general not equivalent.

Proof. The unit case is immediate, because every model of $F$ makes $l$ true. For the pure case, $F|_{\{l\}} \subseteq F$ with literals removed only if they are $\neg l$, and $\neg l$ does not occur, so $F|_{\{l\}}$ is a subset of $F$. Hence a model of $F$ is a model of $F|_{\{l\}}$. Given a model $\alpha$ of $F|_{\{l\}}$, set $l$ true. Clauses with $l$ are satisfied, and the others are in $F|_{\{l\}}$ and do not contain the variable of $l$, so they remain satisfied. $\square$

Elimination can increase the number of clauses, since $|F_x| \cdot |F_{\neg x}|$ can be far larger than $|F_x| + |F_{\neg x}|$. On the machines of that time memory ran out quickly, and it was the limiting resource. The order of elimination has a large effect, as Exercise 9 shows. For a good order, elimination is exponential only in the induced width of the formula's interaction graph, as Rish and Dechter (2000) discuss.

### The DPLL procedure

Davis, Logemann and Loveland (1962) replaced elimination by splitting on a variable. This trades memory for search. The search keeps only the current path in memory, which allowed the method to run on problems that the elimination version could not hold.

```
DPLL(F):
    while F contains a unit clause (l):
        F := F|{l}
    if ⊥ is in F: return UNSAT
    if F is empty: return SAT
    optionally, while a literal l is pure in F: F := F|{l}
    choose a literal l of F
    if DPLL(F|{l}) = SAT: return SAT
    return DPLL(F|{¬l})
```

The correctness follows from Lemma 4 and the fact that $F$ is satisfiable if and only if $F|_{\{l\}}$ or $F|_{\{\neg l\}}$ is satisfiable. Termination follows because each call has fewer variables. Solvers usually drop the pure-literal rule because maintaining it during search is costly relative to its benefit.

### DPLL and tree-like resolution

A refutation is tree-like if each derived clause is used at most once, so that the derivation forms a tree. It is regular if on each path from a leaf to $\bot$ no variable is resolved more than once.

Theorem 5. An UNSAT run of DPLL with $k$ leaves can be converted to a tree-like, regular resolution refutation with $O(k \cdot n)$ steps, and each conflict leaf contributes a clause of $F$.

Proof sketch. Treat each unit propagation as a split on the variable with one branch immediately falsifying the unit clause, so the run is a binary tree in which nodes are labeled by split variables and leaves by clauses of $F$ falsified by the path to them. Label each node $v$ with a clause $C_v$ that is falsified by the partial assignment at $v$. A leaf is labeled with its falsified clause. For an inner node splitting on $x$ with children labeled $C_1$ and $C_2$: if the child with $x$ true has $\neg x \notin C_1$, then $C_1$ is already falsified by the path to $v$, so set $C_v = C_1$ and prune the other subtree, and proceed likewise on the other child. Otherwise $\neg x \in C_1$ and $x \in C_2$, and set $C_v$ to the resolvent. By induction $C_v$ is falsified by the path to $v$. At the root the path is empty, so $C_{\mathrm{root}} = \bot$. Each path splits a variable at most once, so the refutation is regular. A pure-literal step needs no resolution, because $F|_{\{l\}}$ is a subset of $F$ when $l$ is pure. $\square$

The converse holds too. From a tree-like refutation of size $s$ you can read off a DPLL tree of size at most about $s$, by splitting on the pivots from the root downward. So DPLL without learning and tree-like resolution have essentially the same power, up to polynomial factors.

This has an important consequence. Lower bounds on tree-like resolution apply directly to DPLL with any heuristic, whereas general resolution can be exponentially shorter. Some formula families have polynomial-size general refutations and only exponential-size tree-like ones, as described in [Proof complexity](../../../part-1-foundations/02-decidability-and-complexity/proof-complexity/). Clause learning reuses derived clauses, which is how CDCL escapes this bound. Haken (1985) showed that even general resolution needs exponential size on the pigeonhole formulas, so neither method can solve them quickly.

### Comparison

| Aspect | Davis-Putnam | DPLL |
|---|---|---|
| Main operation | It eliminates a variable by adding all non-tautological resolvents. | It splits on a variable and recurses on two restricted formulas. |
| Memory | It can grow exponentially in the worst case. | It uses polynomial space on the current path. |
| Time | It is exponential in the worst case and is governed by clause growth. | It is exponential in the worst case and is governed by the search tree. |
| Proof produced | It yields a refutation that resolves variables in one fixed order. | It yields a tree-like, regular refutation. |
| Model on success | It needs a reconstruction pass in reverse elimination order. | The path gives a model directly, with unassigned variables free. |
| Order sensitivity | The variable order changes clause growth. | The branching order changes the tree size. |

## Worked examples

A script in the scratchpad checked each result in this section by brute force and reproduced the elimination and search steps.

### Example 1: one formula, three methods

Consider the formula

$$F = (x_1 \lor x_2) \land (x_1 \lor \neg x_2 \lor x_3) \land (\neg x_1 \lor x_3) \land (\neg x_3 \lor x_4) \land (\neg x_3 \lor \neg x_4),$$

with clauses named C1 to C5 in that order.

A resolution refutation:

```
C6  = (¬x3)         from C4 and C5 on x4
C7  = (¬x1)         from C3 and C6 on x3
C8  = (x1 ∨ ¬x2)    from C2 and C6 on x3
C9  = (x1)          from C1 and C8 on x2
C10 = ⊥             from C7 and C9 on x1
```

The clause C6 is used twice, so this refutation has 5 steps but is not tree-like.

Davis-Putnam elimination with the order $x_4, x_3, x_2, x_1$, using elimination at every step and skipping the unit and pure rules:

```
Eliminate x4: pos {C4}, neg {C5}
    C4, C5 give (¬x3)
    Result: (x1 ∨ x2), (x1 ∨ ¬x2 ∨ x3), (¬x1 ∨ x3), (¬x3)
Eliminate x3: pos {(x1 ∨ ¬x2 ∨ x3), (¬x1 ∨ x3)}, neg {(¬x3)}
    (x1 ∨ ¬x2 ∨ x3), (¬x3) give (x1 ∨ ¬x2)
    (¬x1 ∨ x3), (¬x3) give (¬x1)
    Result: (x1 ∨ x2), (x1 ∨ ¬x2), (¬x1)
Eliminate x2: pos {(x1 ∨ x2)}, neg {(x1 ∨ ¬x2)}
    They give (x1)
    Result: (¬x1), (x1)
Eliminate x1: they give ⊥
UNSAT
```

DPLL, splitting on the lowest numbered variable with true first:

```
split x1
    C3 is unit: x3
    C4 is unit: x4
    C5 is falsified: conflict
split ¬x1
    C1 is unit: x2
    C2 is unit: x3
    C4 is unit: x4
    C5 is falsified: conflict
UNSAT, with 2 leaves
```

Now apply Theorem 5 to the DPLL tree.

```
Branch x1:
    leaf (¬x3 ∨ ¬x4), resolve with (¬x3 ∨ x4) on x4 gives (¬x3)
    resolve with (¬x1 ∨ x3) on x3 gives (¬x1)
Branch ¬x1:
    leaf (¬x3 ∨ ¬x4), resolve with (¬x3 ∨ x4) on x4 gives (¬x3)
    resolve with (x1 ∨ ¬x2 ∨ x3) on x3 gives (x1 ∨ ¬x2)
    resolve with (x1 ∨ x2) on x2 gives (x1)
Root: resolve (¬x1) and (x1) on x1 gives ⊥
```

This tree-like refutation has 6 steps because it derives $(\neg x_3)$ twice. The general refutation above has 5 steps because it reuses that clause. The saving is small here. On larger families the same idea of reuse gives an exponential difference.

### Example 2: model reconstruction after elimination

Let $F$ be

$$(x_1 \lor x_2 \lor x_3) \land (x_1 \lor \neg x_2) \land (\neg x_1 \lor x_3) \land (\neg x_3 \lor x_4) \land (\neg x_2 \lor \neg x_4).$$

```
Eliminate x4: (¬x3 ∨ x4), (¬x2 ∨ ¬x4) give (¬x2 ∨ ¬x3)
    Result: (x1 ∨ x2 ∨ x3), (x1 ∨ ¬x2), (¬x1 ∨ x3), (¬x2 ∨ ¬x3)
Eliminate x3:
    (x1 ∨ x2 ∨ x3), (¬x2 ∨ ¬x3) give a tautology, so it is discarded
    (¬x1 ∨ x3), (¬x2 ∨ ¬x3) give (¬x1 ∨ ¬x2)
    Result: (x1 ∨ ¬x2), (¬x1 ∨ ¬x2)
Eliminate x2: pos {}, neg {(x1 ∨ ¬x2), (¬x1 ∨ ¬x2)}, so there are no resolvents
    Result: empty formula
Eliminate x1: nothing remains.
SAT
```

To reconstruct a model, assign variables in reverse elimination order, using the clauses that were removed when each variable was eliminated.

```
x1: free. Choose x1 = false.
x2: removed clauses (x1 ∨ ¬x2), (¬x1 ∨ ¬x2). With x1 false, the first forces x2 = false.
x3: removed clauses (x1 ∨ x2 ∨ x3), (¬x1 ∨ x3), (¬x2 ∨ ¬x3).
    With x1, x2 false, the first forces x3 = true.
x4: removed clauses (¬x3 ∨ x4), (¬x2 ∨ ¬x4). With x3 true, the first forces x4 = true.
Model: ¬x1, ¬x2, x3, x4
```

Enumeration shows that this formula has exactly two models, the one above and the same assignment with $x_1$ true.

### Example 3: clause growth on the pigeonhole formula

Three pigeons do not fit into two holes. Let $x_1, x_2$ say that pigeon 1 is in hole 1 or hole 2, let $x_3, x_4$ do the same for pigeon 2, and let $x_5, x_6$ do so for pigeon 3.

```
(x1 ∨ x2)  (x3 ∨ x4)  (x5 ∨ x6)
(¬x1 ∨ ¬x3)  (¬x1 ∨ ¬x5)  (¬x3 ∨ ¬x5)
(¬x2 ∨ ¬x4)  (¬x2 ∨ ¬x6)  (¬x4 ∨ ¬x6)
```

Elimination in the order $x_1, x_2, \dots, x_6$ gives these clause counts, after removing duplicates.

```
start 9, after x1: 8, after x2: 8, after x3: 6, after x4: 4, after x5: 2, after x6: 1 (⊥)
```

For example, eliminating $x_2$ takes two positive clauses, $(x_2 \lor \neg x_3)$ and $(x_2 \lor \neg x_5)$, and two negative clauses, and it produces four resolvents. The total number of resolutions performed is $2 + 4 + 3 + 4 + 2 + 1 = 16$, of which 2 give a tautology.

DPLL with the same variable order has only two leaves:

```
split x1
    (¬x1 ∨ ¬x3) gives ¬x3 and (¬x1 ∨ ¬x5) gives ¬x5
    (x3 ∨ x4) gives x4, and (¬x4 ∨ ¬x6) gives ¬x6
    (x5 ∨ x6) is falsified
split ¬x1
    (x1 ∨ x2) gives x2, then (¬x2 ∨ ¬x4) gives ¬x4 and (¬x2 ∨ ¬x6) gives ¬x6
    (x3 ∨ x4) gives x3, and (¬x3 ∨ ¬x5) gives ¬x5
    (x5 ∨ x6) is falsified
```

Small cases hide the exponential growth, which appears as the number of pigeons rises.

## Common mistakes

- Resolving on two variables at once. From $(x_1 \lor x_2)$ and $(\neg x_1 \lor \neg x_2)$ you may not derive $\bot$. Each of the two possible resolutions gives a tautology, and the two clauses are jointly satisfiable.
- Keeping tautological resolvents. They are valid but useless, and including them inflates the clause count during elimination.
- Forgetting that elimination removes the original clauses. Removing them is what eliminates the variable, and keeping them leaves the variable in the formula.
- Thinking that elimination preserves equivalence. It preserves satisfiability and it preserves the formula's meaning over the remaining variables, namely $\exists x. F$, so the models of the result are the projections of the models of $F$.
- Thinking that the pure-literal rule preserves all models. It keeps at least one model if one exists, which is what SAT needs, and it does not preserve the number of models, which matters for [model counting](../qbf-and-model-counting/).
- Calling DP and DPLL the same algorithm. The names are often confused because of the shared authors, and the first eliminates while the second splits.
- Claiming that DPLL learns. Plain DPLL discards all information on backtracking, and the same subformula can be refuted repeatedly.
- Assuming that the second branch needs testing when the first succeeds. A satisfiable first branch ends the whole search.

## Exercises

### Exercise 1

For each pair, give all non-tautological resolvents: (a) $(x_1 \lor x_2)$ and $(\neg x_1 \lor x_3)$; (b) $(x_1 \lor x_2)$ and $(\neg x_1 \lor \neg x_2)$; (c) $(x_1)$ and $(\neg x_1)$; (d) $(x_1 \lor x_2)$ and $(x_1 \lor x_3)$.

<details><summary>Solution</summary>

(a) $(x_2 \lor x_3)$. (b) None, since resolving on $x_1$ gives $(x_2 \lor \neg x_2)$ and resolving on $x_2$ gives $(x_1 \lor \neg x_1)$. (c) $\bot$. (d) None, since no variable occurs with opposite signs.

</details>

### Exercise 2

Compute $F|_{\{x_1, \neg x_3\}}$ for $F = (x_1 \lor x_2) \land (\neg x_1 \lor x_3 \lor x_4) \land (x_3 \lor \neg x_4) \land (\neg x_2 \lor \neg x_3)$.

<details><summary>Solution</summary>

The first clause contains $x_1$, so it is deleted. The second loses $\neg x_1$ and $x_3$, which gives $(x_4)$. The third loses $x_3$, which gives $(\neg x_4)$. The fourth contains $\neg x_3$, so it is deleted. The result is $(x_4) \land (\neg x_4)$.

</details>

### Exercise 3

Give a resolution refutation of the following formula.

$$(x_1 \lor x_2 \lor x_3) \land (\neg x_1 \lor x_2) \land (\neg x_2 \lor x_3) \land (\neg x_3 \lor x_4) \land (x_1 \lor \neg x_4) \land (\neg x_1 \lor \neg x_3 \lor \neg x_4)$$

<details><summary>Solution</summary>

Name the clauses C1 to C6 in order.

```
C7  = (x1 ∨ ¬x3)      from C4 and C5 on x4
C8  = (¬x1 ∨ ¬x3)     from C4 and C6 on x4
C9  = (¬x3)           from C7 and C8 on x1
C10 = (¬x2)           from C3 and C9 on x3
C11 = (¬x1)           from C2 and C10 on x2
C12 = (x2 ∨ x3)       from C1 and C11 on x1
C13 = (x3)            from C12 and C10 on x2
C14 = ⊥               from C13 and C9 on x3
```

</details>

### Exercise 4

Run Davis-Putnam elimination on the formula of Exercise 3 with the order $x_4, x_1, x_2, x_3$. Use only the elimination rule.

<details><summary>Solution</summary>

```
Eliminate x4: pos {(¬x3 ∨ x4)}, neg {(x1 ∨ ¬x4), (¬x1 ∨ ¬x3 ∨ ¬x4)}
    resolvents: (x1 ∨ ¬x3), (¬x1 ∨ ¬x3)
    Result: (x1 ∨ x2 ∨ x3), (¬x1 ∨ x2), (¬x2 ∨ x3), (x1 ∨ ¬x3), (¬x1 ∨ ¬x3)
Eliminate x1: pos {(x1 ∨ x2 ∨ x3), (x1 ∨ ¬x3)}, neg {(¬x1 ∨ x2), (¬x1 ∨ ¬x3)}
    (x1 ∨ x2 ∨ x3), (¬x1 ∨ x2) give (x2 ∨ x3)
    (x1 ∨ x2 ∨ x3), (¬x1 ∨ ¬x3) give a tautology
    (x1 ∨ ¬x3), (¬x1 ∨ x2) give (x2 ∨ ¬x3)
    (x1 ∨ ¬x3), (¬x1 ∨ ¬x3) give (¬x3)
    Result: (¬x2 ∨ x3), (x2 ∨ x3), (x2 ∨ ¬x3), (¬x3)
Eliminate x2: pos {(x2 ∨ x3), (x2 ∨ ¬x3)}, neg {(¬x2 ∨ x3)}
    (x2 ∨ x3), (¬x2 ∨ x3) give (x3)
    (x2 ∨ ¬x3), (¬x2 ∨ x3) give a tautology
    Result: (¬x3), (x3)
Eliminate x3: they give ⊥. UNSAT.
```

</details>

### Exercise 5

Run DPLL on the following formula, splitting on the lowest numbered variable with true first. Draw the tree and extract a tree-like refutation.

```
C1 = (x1 ∨ x2 ∨ x3)      C2 = (x1 ∨ x2 ∨ ¬x3)
C3 = (x1 ∨ ¬x2 ∨ x3)     C4 = (x1 ∨ ¬x2 ∨ ¬x3)
C5 = (¬x1 ∨ x2 ∨ x3)     C6 = (¬x1 ∨ x2 ∨ ¬x3)
C7 = (¬x1 ∨ ¬x2 ∨ x4)    C8 = (¬x1 ∨ ¬x2 ∨ ¬x4)
```

<details><summary>Solution</summary>

```
split x1
    split x2: C7 gives x4, and C8 is falsified
    split ¬x2: C5 gives x3, and C6 is falsified
split ¬x1
    split x2: C3 gives x3, and C4 is falsified
    split ¬x2: C1 gives x3, and C2 is falsified
UNSAT, with 4 leaves.
```

Refutation:

```
(¬x1 ∨ ¬x2)  from C7 and C8 on x4
(¬x1 ∨ x2)   from C5 and C6 on x3
(¬x1)        from the two lines above on x2
(x1 ∨ ¬x2)   from C3 and C4 on x3
(x1 ∨ x2)    from C1 and C2 on x3
(x1)         from the two lines above on x2
⊥            from (¬x1) and (x1) on x1
```

</details>

### Exercise 6

Using the elimination of Example 2, reconstruct the model obtained if you choose $x_1 = $ true in the first step. Check it against the original formula.

<details><summary>Solution</summary>

With $x_1$ true, the clause $(\neg x_1 \lor \neg x_2)$ forces $x_2$ false. Then $(\neg x_1 \lor x_3)$ forces $x_3$ true, and $(\neg x_3 \lor x_4)$ forces $x_4$ true. The model is $x_1, \neg x_2, x_3, x_4$. Check: $(x_1 \lor x_2 \lor x_3)$ holds by $x_1$. $(x_1 \lor \neg x_2)$ holds by $x_1$. $(\neg x_1 \lor x_3)$ holds by $x_3$. $(\neg x_3 \lor x_4)$ holds by $x_4$. $(\neg x_2 \lor \neg x_4)$ holds by $\neg x_2$.

</details>

### Exercise 7

Prove that resolution decides 2-SAT in polynomial time.

<details><summary>Solution</summary>

A resolvent of two clauses of at most two literals each has at most two literals, because each parent loses its pivot literal. So every derivable clause has at most two literals. Over $n$ variables there are at most $2n + 1$ clauses of size at most one and at most $\binom{2n}{2}$ of size two, which is $O(n^2)$ in total. Repeatedly adding resolvents reaches saturation after $O(n^2)$ additions, with each addition found in polynomial time. By Theorems 1 and 3, $F$ is unsatisfiable if and only if $\bot$ is in the saturated set.

</details>

### Exercise 8

Prove that the pure-literal rule can remove models. Give a formula and a model that is lost, and show that the rule never turns a satisfiable formula into an unsatisfiable one.

<details><summary>Solution</summary>

Take $F = (x_1 \lor x_2)$. The literal $x_1$ is pure, so the rule gives $F|_{\{x_1\}}$, the empty formula, with $x_1$ set true. The model $\neg x_1, x_2$ of $F$ does not have $x_1$ true, so it is lost.

For the second part, Lemma 4 applies. Since $\neg l$ does not occur, $F|_{\{l\}}$ is a subset of $F$, so any model of $F$ satisfies it.

</details>

### Exercise 9

Let $F$ consist of the clauses $(x_0 \lor y_i)$ and $(\neg x_0 \lor z_i)$ for $i = 1, \dots, k$. Compare eliminating $x_0$ first with eliminating all $y_i$ and $z_i$ first.

<details><summary>Solution</summary>

Eliminating $x_0$ first produces $(y_i \lor z_j)$ for all $i, j$, which is $k^2$ clauses in place of $2k$.

Eliminating $y_1$ first has no negative occurrences, so it produces no resolvents and removes $(x_0 \lor y_1)$. Likewise for each $y_i$ and $z_i$. After $2k$ eliminations the formula is empty, and no clause was ever added. The same formula takes quadratic space in one order and no extra space in the other. This illustrates why [bounded variable elimination](../preprocessing-and-inprocessing/) picks variables with few occurrences and limits growth.

</details>

### Exercise 10

Prove that the refutation obtained from DPLL in Theorem 5 is regular, and explain why this does not show that regular resolution is as weak as tree-like resolution.

<details><summary>Solution</summary>

In the DPLL tree, a path from the root to a leaf never splits on the same variable twice, because after a split the variable no longer occurs in the restricted formula. Propagations are splits in the sense of the proof, and they also fix the variable. The resolution steps follow the tree, with pivots equal to the split variables, so each path in the refutation resolves on each variable at most once. So it is regular.

The theorem shows that tree-like DPLL refutations are a subset of regular refutations. It gives no bound in the reverse direction, because a regular refutation need not be a tree. A clause can be reused along several paths. So regular resolution can be much shorter than any tree-like refutation.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State and apply the resolution rule, and spot tautological resolvents.
- Prove soundness, the elimination theorem and refutational completeness.
- Run Davis-Putnam elimination on a small formula with a given order, and reconstruct a model.
- Run DPLL with unit propagation on a small formula and draw its search tree.
- Convert a DPLL tree to a tree-like refutation.
- Explain the trade-off between elimination and splitting, and say which proof system bounds each.

## Materials

- Davis and Putnam, A Computing Procedure for Quantification Theory, JACM 1960. Read it for the original three rules and for the first-order setting that motivated them.
- Davis, Logemann and Loveland, A machine program for theorem-proving, CACM 1962. Read it for the replacement of elimination by splitting and the reasons of memory behind it.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the treatment of propositional procedures for a textbook account of DPLL and resolution.
- Rish and Dechter, Resolution versus Search: Two Strategies for SAT, Journal of Automated Reasoning 2000. Read it for the role of induced width and a comparison of elimination with search.
- Haken, The Intractability of Resolution, Theoretical Computer Science 1985. Read it for the exponential lower bound on pigeonhole formulas.
