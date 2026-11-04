# Loop Invariants

Part 2, Chapter 7: Deductive Verification.

## Objective

Find inductive invariants and ranking functions for unseen loops.

## Why this matters

Everything else in deductive verification can be calculated, and loops are where a human or a search procedure has to supply an idea. A verifier reports that an invariant is not preserved far more often than it reports a real bug, so the daily work of verification engineering is largely invariant repair. Automatic methods attack the same object: [abstract interpretation](../../../part-4-remaining-methods/13-static-analysis/abstract-interpretation/) computes invariants in a fixed domain, [IC3](../../08-model-checking/ic3-and-pdr/) and [Horn clause solving](../../08-model-checking/horn-clauses/) search for them with a solver, and learned approaches try to guess them. Ranking functions play the same role for termination, which matters for liveness properties and for the soundness of recursive specifications.

## Prerequisites

- [Hoare Logic](../hoare-logic/) for the while rules.
- [Weakest Preconditions](../weakest-preconditions/) for backward strengthening and the fixed-point view.
- [Arrays](../../05-smt/arrays/) for read-over-write reasoning in array invariants.

## Lesson

### Invariants, inductive invariants and adequate invariants

Fix a loop $L \equiv \mathtt{while}\ b\ \mathtt{do}\ c$ with precondition $P$ and postcondition $Q$. Three notions need to be kept apart.

- $I$ is an invariant if $I$ holds at the loop head in every state reachable from $P$.
- $I$ is inductive if initiation holds, $\models P \to I$, and consecution holds, $\models I \land b \to \mathrm{wlp}(c, I)$.
- $I$ is adequate if $\models I \land \neg b \to Q$.

The proof obligations of Hoare logic require an inductive and adequate predicate. Every inductive predicate is an invariant, by induction on the number of iterations, but the converse fails. Consider

```
x := 1 ; y := 1 ;
while b do ( y := y + x ; x := x + 1 )
```

The predicate $y \geq 1$ is an invariant. It is not inductive, because consecution quantifies over all states, and $y = 1, x = -5$ satisfies it and leads to $y = -4$. The conjunction $y \geq 1 \land x \geq 0$ is inductive. This is the fundamental phenomenon: a true property often has to be strengthened before it can be proved by induction, in the same way as a theorem in mathematics often needs a stronger induction hypothesis.

### The space of inductive invariants

Let $R$ be the set of states reachable at the loop head from $P$, which is $\mu X.\ P \lor \mathrm{sp}(c, X \land b)$. Let $W \equiv \mathrm{wlp}(L, Q)$.

Theorem. The following hold.

1. $R$ is the strongest inductive predicate: it is inductive, and $\models R \to I$ for every inductive $I$.
2. Inductive predicates are closed under arbitrary conjunction and disjunction.
3. $\models \{P\}\ L\ \{Q\}$ if and only if $R$ is adequate, and if and only if $\models P \to W$.
4. If $I$ is inductive and adequate, then $\models R \to I$ and $\models I \to W$.

Proof. Statement 1 is the least fixed point property, since inductiveness of $I$ says $P \lor \mathrm{sp}(c, I \land b) \to I$. Statement 2: for a conjunction, $\mathrm{wlp}$ is conjunctive, so consecution of each conjunct gives consecution of the conjunction. For a disjunction, a run of $c$ from a state in $I_1 \lor I_2$ with $b$ starts in one disjunct and ends in the same disjunct. Exercise 8 gives the details. Statement 3 follows because exit states of the loop are exactly the states in $R \land \neg b$. Statement 4 combines statement 1 with the theorem in [Weakest Preconditions](../weakest-preconditions/) stating that $W$ is the weakest adequate inductive predicate. $\square$

So a suitable invariant always exists semantically when the triple is valid, and the set of them is a lattice between $R$ and $W$. Being between $R$ and $W$ does not suffice. For $x := 0 ;\ \mathtt{while}\ x < 10\ \mathtt{do}\ x := x + 1$ with $Q \equiv x = 10$, $R$ is $0 \leq x \leq 10$ and $W$ is $x \leq 10$. The set $\{-3\} \cup \{0, \ldots, 10\}$ lies between them and is not inductive, because $-3$ steps to $-2$.

The art of invariant finding is picking a member of this lattice that is simple enough for you and for the solver. Finding one is undecidable in general, since the triple's validity is undecidable.

### Finding an invariant from the postcondition

Furia, Meyer and Velder analyze the invariants of many classical algorithms, and observe that the clauses of a practical invariant separate into two kinds. Essential clauses are a weakening or other mutation of the postcondition. Bounding clauses keep variables in range and ensure that the essential clause is meaningful. They name the common mutations, and these are the first thing to try on an unseen loop.

| Technique | Description | Typical case |
|---|---|---|
| Constant relaxation | Replace a constant in the postcondition by a variable, and use their equality as the exit condition. | Sum or maximum of a prefix up to $i$, with the loop stopping when $i = n$. |
| Uncoupling | Replace one variable by two, and use their equality as the exit condition. | Subtractive gcd, where the result variable is split in two. |
| Term dropping | Remove a conjunct, usually one supplied by the exit condition. | Integer division, where $r < y$ is dropped and returned by $\neg(y \leq r)$. |
| Aging | Replace a variable by an expression for its value at an earlier iteration. | Off-by-one adjustments, such as stating a property of $i - 1$ when $i$ is updated before the check. |
| Backward reasoning | Compute the loop's postcondition from another assertion by backward substitution. | An inner loop whose postcondition is derived from the outer invariant. |

A practical procedure for an unseen loop is the following.

1. Write the postcondition and the negated guard. Ask which conjunct can be replaced by $\neg b$, and which constant can become the loop counter.
2. Tabulate two or three runs by hand, with one row per iteration and one column per variable. Look for relations that hold at all rows.
3. Add bounding clauses for every variable that is an index or a counter, so that the exit condition determines the final value.
4. Attempt consecution. If it fails, examine the failing state and strengthen as described below.
5. Check initiation and adequacy last, since strengthening can break initiation.

### Strengthening by counterexample to induction

Suppose $I$ is adequate and true of reachable states, but consecution fails. Then there is a counterexample to induction, a state with $I \land b$ from which $c$ leaves $I$. This state must be unreachable if $I$ is really an invariant, so the failure reveals a fact that $I$ does not yet state. The candidate fact is computed backward:

$$I' \equiv I \land (b \to \mathrm{wlp}(c, I)).$$

Iterating this operation from $I_0 \equiv \neg b \to Q$ is the $\nu$ iteration for $W$ from the previous topic. In its pure form it is unusable, because the formula grows and may never stabilize. In practice you simplify the added conjunct under the current invariant and the guard, and you often generalize it by hand. Worked Example 2 shows this.

The iteration also gives a refutation test. Since $\models W \to I_k$ for each $k$, a state in $P$ that violates $I_k$ refutes the triple itself: it is a real input from which the loop can exit within $k$ iterations in a state violating $Q$. This is the same reasoning that underlies backward counterexample search in [IC3](../../08-model-checking/ic3-and-pdr/).

### Automated search

You should know the main families of automation.

- Candidate filtering, as in Houdini (Flanagan and Leino, 2001). The search starts from a finite set of candidates and repeatedly removes those not implied, as shown below. It always returns the largest inductive subset, as Exercise 9 proves.
- Abstract interpretation, which computes a fixed point in a restricted domain using widening. See [Abstract Interpretation](../../../part-4-remaining-methods/13-static-analysis/abstract-interpretation/).
- Template-based constraint solving, which fixes a shape such as linear inequalities with unknown coefficients and converts consecution into constraints on the coefficients with Farkas' lemma (Colón, Sankaranarayanan and Sipma, 2003).
- Solver-driven model checking, including [interpolation](../../08-model-checking/interpolation-based-checking/), [IC3](../../08-model-checking/ic3-and-pdr/) and [Horn clauses](../../08-model-checking/horn-clauses/).

```
Houdini(P, b, c, candidates):
    A := { q in candidates : P → q is valid }
    repeat
        changed := false
        for each q in A:
            if (⋀A) ∧ b → wlp(c, q) is not valid:
                remove q from A
                changed := true
    until not changed
    return ⋀A
```

### Arrays and quantified invariants

Invariants for array loops describe a partition of the indices into regions. Each region is described by a universally quantified clause over its index range, and the loop moves the boundaries. Treat array writes as $a := \mathit{store}(a, i, e)$, as explained in [Hoare Logic](../hoare-logic/). When proving a quantified clause for the updated array, split on whether the quantified index equals the written index. If the postcondition also says that the result is a permutation of the input, you need an extra clause, usually written with a ghost multiset, which this topic does not pursue.

### Ranking functions

Definition. A relation $\prec$ on a set $W$ is well-founded if there is no infinite descending chain $w_0 \succ w_1 \succ \cdots$. A ranking function for $L$ under invariant $I$ is a function $t$ from states to $W$ such that

$$\models I \land b \land t = n \to \mathrm{wp}(c, I \land t \prec n).$$

The bound premise of the integer rule of [Hoare Logic](../hoare-logic/) is included in the choice of $W$: the integer case uses $W = \mathbb{N}$, and $t$ only needs to be a natural number when $I \land b$ holds.

Theorem (soundness). If such a $t$ exists, every run of $L$ from a state in $I$ terminates.

Proof. An infinite run would visit states $\sigma_0, \sigma_1, \ldots$ satisfying $I \land b$, and $t(\sigma_0) \succ t(\sigma_1) \succ \cdots$ would be an infinite descending chain. $\square$

Theorem (completeness). Let $c$ be deterministic and suppose every run of $L$ from $I$ terminates. Then a ranking function into $\mathbb{N}$ exists. If $c$ is nondeterministic with finite branching, the same holds. With unbounded nondeterminism, a ranking function into the ordinals exists, and $\mathbb{N}$ may not suffice.

Proof. In the deterministic case, let $t(\sigma)$ be the number of iterations left from $\sigma$. It decreases by exactly one per iteration. In the finitely branching case, the tree of runs from $\sigma$ has only finite paths, so by König's lemma it is finite. Let $t(\sigma)$ be its height. In the general case, the tree is well-founded, and $t(\sigma)$ is its ordinal rank. For the last claim, see Exercise 10. $\square$

The theorem uses the semantic function, which might not be expressible in a simple term, so the theorem does not tell you how to write a ranking function.

Lexicographic ranking. For $\mathbb{N}^k$ with $(a_1, \ldots, a_k) \prec (b_1, \ldots, b_k)$ if at the first index where they differ, $a_i < b_i$, the order is well-founded. To prove this by induction on $k$, note that in any infinite descending chain the first component is nonincreasing, hence eventually constant, and the rest of the tuples then give an infinite descending chain in $\mathbb{N}^{k-1}$. Lexicographic ranking is natural for nested loops and for loops in which one branch resets a counter. The order type of $\mathbb{N}^k$ is $\omega^k$, so these functions can handle cases with no natural-number ranking.

Finding a ranking function usually proceeds in this way:

1. Look for a quantity that the exit condition bounds, such as $n - i$, $hi - lo$ or $r$.
2. If different branches decrease different quantities, try a lexicographic tuple, ordered so that a branch that increases a component also decreases an earlier one.
3. If the decrease needs a fact such as $y > 0$, add the fact to the invariant.

Linear ranking functions for simple linear loops over the rationals can be synthesized in polynomial time via Farkas' lemma (Podelski and Rybalchenko, 2004). Not all terminating loops have one, as Exercise 7 shows.

Transition invariants. Podelski and Rybalchenko (LICS 2004) give a different criterion. A relation $T$ is a transition invariant if it contains the transitive closure of the transition relation restricted to reachable states. It is disjunctively well-founded if it is a finite union $T_1 \cup \cdots \cup T_m$ of well-founded relations.

Theorem. A program terminates if and only if it has a disjunctively well-founded transition invariant.

Proof. If it terminates, the transitive closure of the reachable transition relation is itself well-founded, with $m = 1$. Conversely, suppose there is an infinite run $s_0, s_1, \ldots$. Color each pair $i < j$ by some $k$ with $(s_i, s_j) \in T_k$. By the infinite Ramsey theorem, there is an infinite subset of indices whose pairs all have the same color $k$. This yields an infinite chain in $T_k$, contradicting well-foundedness. $\square$

The transitive closure is essential. The union of well-founded relations is generally not well-founded. Take the transitions $(x, y) \mapsto (x - 1, y + 1)$ and $(x, y) \mapsto (x + 1, y - 1)$ on $\mathbb{N}^2$: every step decreases $x$ or decreases $y$, but the two steps can alternate forever. Their transitive closure contains $(x, y) \mapsto (x, y)$, which is in neither relation.

Termination can be genuinely hard. The loop $\mathtt{while}\ n \neq 1\ \mathtt{do}\ \mathtt{if}\ n\ \mathrm{even}\ \mathtt{then}\ n := n / 2\ \mathtt{else}\ n := 3n + 1$ is the Collatz problem, and no ranking function for it is known.

## Worked examples

### Example 1: integer square root

```
[ n ≥ 0 ]
r := 0 ;
while (r+1)·(r+1) ≤ n do r := r + 1
[ r·r ≤ n ∧ n < (r+1)·(r+1) ]
```

Term dropping: the second conjunct of the postcondition is the negated guard, so try $r^2 \leq n$.

Trial 1. $I_1 \equiv r^2 \leq n$. Initiation is $0 \leq n$, which holds. Consecution needs $(r+1)^2 \leq n$, which is the guard. Adequacy holds. So $I_1$ gives partial correctness.

Termination. The quantity $n - r^2$ is the obvious candidate. After the body it equals $n - r^2 - 2r - 1$, so the decrease requires $2r + 1 > 0$. This fails under $I_1$ alone, which permits $r = -5$ when $n = 30$. So strengthen to $I_2 \equiv r \geq 0 \land r^2 \leq n$, which is still inductive. Now the decrease holds, and the guard gives $n - r^2 \geq 2r + 1 \geq 0$ for the bound. The simpler variant $n - r$ also works under $I_2$, because $r \leq r^2 \leq n$ on integers with $r \geq 0$.

The lesson is that termination proofs often require invariant clauses that partial correctness did not need.

### Example 2: cubes by finite differences, strengthening step by step

```
[ a ≥ 0 ]
n := 0 ; x := 0 ; y := 1 ; z := 6 ;
while n < a do ( n := n + 1 ; x := x + y ; y := y + z ; z := z + 6 )
[ x = a³ ]
```

Constant relaxation on the postcondition gives $x = n^3$, with bounding clause $n \leq a$. This is the first candidate.

```
I0 ≡ n ≤ a ∧ x = n³
```

The body runs $n := n + 1$, then $x := x + y$, then $y := y + z$, then $z := z + 6$, so the backward computation visits them in the opposite order. For the conjunct $x = n^3$, the assignments to $z$ and $y$ do nothing. Then $x := x + y$ gives $x + y = n^3$, and $n := n + 1$ gives $x + y = (n+1)^3$.

So consecution needs $x = n^3 \land n < a \to x + y = (n+1)^3$, which fails with counterexample $n = 0, a = 1, x = 0, y = 170$. Under $x = n^3$, the requirement is equivalent to $y = 3n^2 + 3n + 1$. Add this as a new conjunct, which is the simplified form of the strengthening step.

```
I1 ≡ n ≤ a ∧ x = n³ ∧ y = 3n² + 3n + 1
```

Now the new conjunct has its own consecution obligation. Compute it backward through the body. The assignment $z := z + 6$ does nothing to $y = 3n^2 + 3n + 1$. Then $y := y + z$ gives $y + z = 3n^2 + 3n + 1$. The assignment $x := x + y$ does nothing. Then $n := n + 1$ gives

$$y + z = 3(n+1)^2 + 3(n+1) + 1.$$

Under $y = 3n^2 + 3n + 1$ this is equivalent to $z = 3(2n + 1) + 3 = 6n + 6$. Add it.

```
I2 ≡ n ≤ a ∧ x = n³ ∧ y = 3n² + 3n + 1 ∧ z = 6n + 6
```

Backward through the body, $z = 6n + 6$ becomes $z + 6 = 6(n + 1) + 6$, which is the conjunct itself. The chain has closed, so $I_2$ is inductive. All the checks are now:

```
Initiation (n,x,y,z = 0,0,1,6):  0 ≤ a ∧ 0 = 0 ∧ 1 = 1 ∧ 6 = 6     from a ≥ 0
Consecution, n + 1 ≤ a:          from n < a
Adequacy: I2 ∧ ¬(n < a) gives n = a, so x = a³
Variant:  t ≡ a - n, bound from n < a, and the body decreases t by 1
```

Each strengthening stated what the previous clause required of the next variable. This pattern is typical of programs that compute polynomials incrementally.

### Example 3: binary search, with a quantified invariant

The program computes the first index whose element is at least $k$, for a sorted array.

```
[ n ≥ 0 ∧ ∀i,j. 0 ≤ i ≤ j < n → a[i] ≤ a[j] ]
lo := 0 ; hi := n ;
while lo < hi do
    mid := lo + (hi - lo) div 2 ;
    if a[mid] < k then lo := mid + 1 else hi := mid
[ 0 ≤ lo ≤ n ∧ (∀j. 0 ≤ j < lo → a[j] < k) ∧ (∀j. lo ≤ j < n → a[j] ≥ k) ]
```

Apply double constant relaxation. The postcondition is a partition of $[0, n)$ with one boundary. Replace the single boundary by $lo$ and $hi$, leaving an unknown middle region. The invariant is

$$I \equiv 0 \leq lo \leq hi \leq n \land (\forall j.\ 0 \leq j < lo \to a[j] < k) \land (\forall j.\ hi \leq j < n \to a[j] \geq k).$$

Initiation. At $lo = 0, hi = n$, both ranges are empty and $0 \leq 0 \leq n \leq n$.

Fact about the midpoint. From $lo < hi$, $(hi - lo)\ \mathrm{div}\ 2$ lies in $[0, hi - lo)$, so $lo \leq mid < hi$, and thus $0 \leq mid < n$.

Consecution, then branch. Assume $I$, $lo < hi$ and $a[mid] < k$. The new value of $lo$ is $mid + 1$. The bounds $0 \leq mid + 1 \leq hi$ hold. For the quantified clause, take $j$ with $0 \leq j < mid + 1$. If $j < lo$, the old clause applies. If $lo \leq j \leq mid$, sortedness gives $a[j] \leq a[mid] < k$.

Consecution, else branch. Assume $a[mid] \geq k$. The new value of $hi$ is $mid$. The bounds $lo \leq mid \leq n$ hold. Take $j$ with $mid \leq j < n$. If $j \geq hi$, the old clause applies. If $mid \leq j < hi$, sortedness gives $a[j] \geq a[mid] \geq k$.

Adequacy. $I \land \neg(lo < hi)$ gives $lo = hi$, and substitution gives the postcondition.

Termination. Let $t \equiv hi - lo$. The bound follows from $lo < hi$. In the then branch, $hi - (mid + 1) < hi - lo$ since $mid \geq lo$. In the else branch, $mid - lo < hi - lo$ since $mid < hi$.

The midpoint formula has a further point. Written as $(lo + hi)\ \mathrm{div}\ 2$, it is equal over mathematical integers, but it can overflow on machine integers even when the search range is valid. An integer-based proof does not detect this, and a [bit-vector](../../05-smt/bit-vectors/) model does.

### Example 4: lexicographic ranking and a reset

```
[ x ≥ 0 ∧ y ≥ 0 ]
while x > 0 do
    if y > 0 then y := y - 1
    else ( x := x - 1 ; y := ? )     // ? is any natural number
```

Take $I \equiv x \geq 0 \land y \geq 0$, which is inductive, because the else branch is only taken with $x > 0$. Take $t \equiv (x, y)$ with lexicographic order on $\mathbb{N}^2$.

The then branch leaves $x$ unchanged and decreases $y$, which stays natural since $y > 0$.

The else branch decreases $x$, and the increase in $y$ does not matter, since the first component is strictly smaller.

No function into $\mathbb{N}$ can rank this loop. Suppose $t$ is such a function, and let $m \equiv t(2, 0)$. From state $(2, 0)$, the else branch may choose $y = m + 1$, reaching state $(1, m + 1)$. From there, $m + 1$ iterations of the then branch must follow, and each strictly decreases $t$, so $t(1, m + 1) \geq m + 1 > m$. This contradicts the requirement $t(1, m + 1) < m$. The ordinal function $\omega \cdot x + y$ ranks the loop, and it is the same as the lexicographic order.

The verification conditions in Examples 1 to 3 were checked with an SMT solver, with the array properties encoded in the theory of arrays with quantifiers. All were reported valid, and the weak invariant $I_0$ of Example 2 was reported invalid, as stated.

## Common mistakes

1. Treating a property seen in testing as an invariant ready for proof. It may be true and not inductive, as with $y \geq 1$ above. The proof obligation is for all states satisfying $I \land b$, and these may be unreachable.
2. Omitting bounding clauses. Without $i \leq n$, the condition $\neg(i < n)$ gives $i \geq n$ and not $i = n$, so the postcondition cannot be concluded.
3. Writing an invariant that describes the state only at the end of the body. An invariant must hold at the loop head, before the guard is tested, which includes the moment of exit.
4. Using the guard inside the invariant. If $I$ includes $i < n$, it is false at exit, so initiation or consecution will fail at the last iteration.
5. Strengthening until initiation fails. Each new conjunct needs its own initiation check. If initiation fails for a conjunct that is required by consecution, the program may be incorrect, or the conjunct may be too strong.
6. Forgetting to include facts about values not changed by the loop. A verifier that havocs only the modified variables keeps facts about the others, but a hand proof based on a bare invariant must state any fact from the precondition that consecution uses, such as $y > 0$ in integer division, or use the invariance rule to carry it.
7. Choosing a variant that decreases but is unbounded below. The bound premise is an obligation, and it may need its own invariant clause.
8. Believing that a sum of variants is always the right combination. If a branch decreases $x$ by 1 and increases $y$ by 5, then $x + y$ fails, and $(x, y)$ with lexicographic order or a weighted sum such as $6x + y$ is required.
9. Assuming that disjunctive well-foundedness only needs to cover single steps. It must cover the transitive closure, as shown above.

## Exercises

### Exercise 1

For the loop $x := 1 ;\ y := 1 ;\ \mathtt{while}\ b\ \mathtt{do}\ (y := y + x ;\ x := x + 1)$, show precisely that $y \geq 1$ is an invariant but not inductive, and show that $y \geq 1 \land x \geq 0$ is inductive.

<details><summary>Solution</summary>

Not inductive: from $y = 1, x = -1$, which satisfies $y \geq 1$, the body gives $y = 0$.

Inductive strengthening. Initiation holds at $x = y = 1$. For consecution, assume $y \geq 1$ and $x \geq 0$. The body leaves $y + x \geq 1$ and $x + 1 \geq 0$.

Since the strengthening is inductive, all of its conjuncts hold at every reachable loop head, including $y \geq 1$. This shows that $y \geq 1$ is an invariant.

</details>

### Exercise 2

Find an invariant and a variant, and prove total correctness.

```
[ b ≥ 0 ]
x := 0 ; i := 0 ;
while i < b do ( x := x + a ; i := i + 1 )
[ x = a·b ]
```

<details><summary>Solution</summary>

Constant relaxation of $b$ to $i$ gives $x = a \cdot i$. Add bounding clauses: $I \equiv 0 \leq i \leq b \land x = a \cdot i$. Variant $t \equiv b - i$.

Initiation: $0 = a \cdot 0$ and $0 \leq 0 \leq b$.

Consecution: backward through the body, the requirement is $0 \leq i + 1 \leq b \land x + a = a(i + 1)$. It follows from $I$ and $i < b$.

Adequacy: $i \leq b \land \neg(i < b)$ gives $i = b$, so $x = a \cdot b$.

Variant: bounded by $i < b$, and it decreases by one.

</details>

### Exercise 3

Find an invariant and a variant for Russian peasant multiplication, and prove correctness. Here `div` is integer division and $y \geq 0$ initially.

```
[ B ≥ 0 ]
x := A ; y := B ; z := 0 ;
while y > 0 do
    if y mod 2 = 1 then z := z + x else skip ;
    x := 2·x ;
    y := y div 2
[ z = A·B ]
```

<details><summary>Solution</summary>

Generalize the postcondition. It is equivalent to $z + x \cdot 0 = A \cdot B$, and the constant $0$ can become the variable $y$, which the exit condition returns to $0$. So let $I \equiv z + x y = A B \land y \geq 0$, and $t \equiv y$.

Initiation: $0 + AB = AB$ and $B \geq 0$.

Consecution. Assume $I$ and $y > 0$. If $y$ is odd, write $y = 2y' + 1$. The new values are $z + x$, $2x$ and $y'$, so the left side becomes $z + x + 2x y' = z + x(2y' + 1) = z + xy$. If $y$ is even, write $y = 2y'$. The new values are $z$, $2x$ and $y'$, so the left side becomes $z + 2x y' = z + xy$. In both cases $y' \geq 0$.

Adequacy: $I \land \neg(y > 0)$ gives $y = 0$, so $z = AB$.

Variant: $y \geq 1$ implies $y\ \mathrm{div}\ 2 < y$. This is an example in which the decrease is by more than one and depends on the positivity of $y$.

</details>

### Exercise 4

Find an invariant and a variant for a linear search with an early exit, and prove correctness. Reads out of range are harmless in this model, because arrays are total functions.

```
[ n ≥ 0 ]
i := 0 ;
while i < n ∧ a[i] ≠ k do i := i + 1
[ 0 ≤ i ≤ n ∧ (∀j. 0 ≤ j < i → a[j] ≠ k) ∧ (i = n ∨ a[i] = k) ]
```

<details><summary>Solution</summary>

The last conjunct is what the negated guard supplies, so drop it. Let $I \equiv 0 \leq i \leq n \land \forall j.\ 0 \leq j < i \to a[j] \neq k$, and $t \equiv n - i$.

Initiation: the range is empty at $i = 0$.

Consecution. Assume $I$, $i < n$ and $a[i] \neq k$. The bounds hold for $i + 1$. For $0 \leq j < i + 1$, either $j < i$ and the old clause applies, or $j = i$ and the guard applies.

Adequacy. $\neg(i < n \land a[i] \neq k)$ gives $i \geq n \lor a[i] = k$. With $i \leq n$, the first disjunct becomes $i = n$.

Variant: $i < n$ bounds $t$, and the body decreases it by one.

</details>

### Exercise 5

Find an invariant for this partition loop, and prove the postcondition. It uses a swap $\mathtt{swap}(a, i, j-1)$, which you should model with two array stores. The permutation property is not required.

```
[ n ≥ 0 ]
i := 0 ; j := n ;
while i < j do
    if a[i] ≤ p then i := i + 1
    else ( swap(a, i, j-1) ; j := j - 1 )
[ 0 ≤ i ≤ n ∧ (∀k. 0 ≤ k < i → a[k] ≤ p) ∧ (∀k. i ≤ k < n → a[k] > p) ]
```

<details><summary>Solution</summary>

Double constant relaxation again gives

$$I \equiv 0 \leq i \leq j \leq n \land (\forall k.\ 0 \leq k < i \to a[k] \leq p) \land (\forall k.\ j \leq k < n \to a[k] > p), \qquad t \equiv j - i.$$

Then branch. Assume $i < j$ and $a[i] \leq p$. For $k < i + 1$, either $k < i$ or $k = i$, and the guard covers the second case.

Else branch. Let $a' \equiv \mathit{store}(\mathit{store}(a, i, a[j-1]), j - 1, a[i])$, and note $a[i] > p$ and $i \leq j - 1$. For the left region, take $0 \leq k < i$. Then $k \neq i$ and $k \neq j - 1$, since $k < i \leq j - 1$, so $a'[k] = a[k] \leq p$. For the right region, take $j - 1 \leq k < n$. If $k = j - 1$, then $a'[k] = a[i] > p$. This case also covers $i = j - 1$, since the outer store wins. If $k \geq j$, then $k \neq i$ and $k \neq j - 1$, so $a'[k] = a[k] > p$. The bounds $i \leq j - 1$ and $j - 1 \leq n$ hold.

Adequacy. $i = j$ at exit gives the postcondition by substitution.

Variant. Each branch decreases $j - i$ by one, and $i < j$ bounds it.

</details>

### Exercise 6

Prove termination of the following loop, stating what must be added to the invariant.

```
[ y > 0 ]
while x > 0 do ( x := x - y ; y := y + 1 )
```

<details><summary>Solution</summary>

Take $t \equiv x$, and $I \equiv y > 0$. The bound follows from the guard. The decrease $x - y < x$ needs $y > 0$, which the invariant supplies. Consecution of $I$: $y + 1 > 0$. The clause $y > 0$ is the point of the exercise, because without it the loop diverges from $y = 0$.

</details>

### Exercise 7

Consider $\mathtt{while}\ x > 0\ \mathtt{do}\ (x := x + y ;\ y := y - 1)$ with arbitrary integer initial values.

(a) Prove that it has no linear ranking function $f(x, y) = \alpha x + \beta y + \gamma$ into $\mathbb{N}$, under the trivial invariant $\top$.

(b) Prove that it terminates anyway.

<details><summary>Solution</summary>

(a) Decrease needs $f(x + y, y - 1) < f(x, y)$ for all $x > 0$ and all $y$. Compute the difference: $f(x+y, y-1) - f(x,y) = \alpha y - \beta$. For this to be negative for all integers $y$, we need $\alpha = 0$ and $\beta > 0$. Then $f = \beta y + \gamma$. The bound needs $f \geq 0$ for all $x > 0$ and all $y$, but $\beta y + \gamma$ becomes negative for sufficiently negative $y$. This is a contradiction.

(b) Every iteration decreases $y$ by one, so after finitely many iterations either the loop has already exited, or $y \leq -1$. From that point on, $y \leq -1$ stays true, so each iteration decreases $x$ by at least one. Since the loop requires $x > 0$, it exits after finitely many further iterations. Two phases are enough for the proof, which you can formalize by taking the variant $(\max(y + 1, 0), \max(x, 0))$ with lexicographic order. The first component is strictly decreasing while $y \geq 0$. When it is $0$, $y \leq -1$, and the second component strictly decreases.

</details>

### Exercise 8

Prove that inductive predicates for a loop are closed under arbitrary conjunction and disjunction. Then show that the class of adequate inductive predicates is closed under both as well.

<details><summary>Solution</summary>

Let $\{I_\alpha\}$ be inductive, with a nonempty index set.

Conjunction. Initiation: $P \to I_\alpha$ for all $\alpha$, so $P \to \bigwedge I_\alpha$. Consecution: let $\sigma \models \bigwedge I_\alpha \land b$, and let $\sigma'$ be a final state of $c$ from $\sigma$. For each $\alpha$, $\sigma \models I_\alpha \land b$, so $\sigma' \models I_\alpha$.

Disjunction. Initiation: $P \to I_\beta$ for any $\beta$ implies $P \to \bigvee I_\alpha$. Consecution: let $\sigma \models \bigvee I_\alpha \land b$. Then $\sigma \models I_\beta \land b$ for some $\beta$, so $\sigma' \models I_\beta$, which implies $\bigvee I_\alpha$.

Adequacy. For a conjunction, $\bigwedge I_\alpha \land \neg b$ implies $I_\beta \land \neg b$, which implies $Q$. For a disjunction, each disjunct of $(\bigvee I_\alpha) \land \neg b$ implies $Q$.

</details>

### Exercise 9

Prove that the Houdini algorithm terminates and returns the conjunction of the largest subset $S \subseteq$ candidates such that $\bigwedge S$ is inductive.

<details><summary>Solution</summary>

Termination: $A$ strictly shrinks at each removal, and the candidate set is finite.

Result is inductive. When the loop ends, no removal occurred in the final pass. So for each $q \in A$, $(\bigwedge A) \land b \to \mathrm{wlp}(c, q)$ is valid. By conjunctivity of wlp, $(\bigwedge A) \land b \to \mathrm{wlp}(c, \bigwedge A)$ is valid. Each $q \in A$ passed the initial filter, so $P \to \bigwedge A$.

Maximality. Let $S$ be a set of candidates with $\bigwedge S$ inductive. We show that $S \subseteq A$ at all times. First, for $q \in S$, $P \to \bigwedge S \to q$, so $q$ passes the initial filter. Now suppose $S \subseteq A$ at some moment, and let $q \in S$. Since $S \subseteq A$, $\bigwedge A \to \bigwedge S$. Thus $(\bigwedge A) \land b \to (\bigwedge S) \land b \to \mathrm{wlp}(c, \bigwedge S) \to \mathrm{wlp}(c, q)$, so $q$ is not removed.

Since the result contains every such $S$ and is itself one of them, it is the largest.

</details>

### Exercise 10

Prove that there is no ranking function into $\mathbb{N}$ for this terminating loop, and give a ranking function into the ordinals. As before, `?` chooses any natural number.

```
while b = 0 ∨ (b = 1 ∧ x > 0) do
    if b = 0 then ( x := ? ; b := 1 ) else x := x - 1
```

<details><summary>Solution</summary>

Suppose $t$ maps states satisfying the guard into $\mathbb{N}$ and decreases at each iteration. First, for $v \geq 1$, by induction on $v$, $t(b = 1, x = v) \geq v - 1$. For $v = 1$ this is immediate, since $t \geq 0$. For $v + 1$, the next state is $(b = 1, x = v)$, and so $t(1, v + 1) > t(1, v) \geq v - 1$, which gives $t(1, v + 1) \geq v$.

Let $m \equiv t(b = 0, x)$ for some state with $b = 0$. The body can choose $x = m + 2$, leading to $t(1, m + 2) \geq m + 1 > m$, which contradicts the decrease.

A ranking function into ordinals: $t(b = 0, x) = \omega$ and $t(b = 1, x) = x$ for $x \geq 0$. Choosing $x = v$ moves from $\omega$ to the finite ordinal $v$, which is smaller. Decrementing goes from $x$ to $x - 1$. For negative values of $x$ with $b = 1$ the guard is false, so no decrease is required.

</details>

### Exercise 11

Design and prove the invariant for fast exponentiation.

```
[ B ≥ 0 ]
x := A ; y := B ; z := 1 ;
while y > 0 do
    if y mod 2 = 1 then z := z·x else skip ;
    x := x·x ;
    y := y div 2
[ z = A^B ]
```

<details><summary>Solution</summary>

Generalize the postcondition as in Exercise 3: $I \equiv z \cdot x^y = A^B \land y \geq 0$, and $t \equiv y$. Here $w^0 = 1$ for all $w$, including $w = 0$.

Initiation: $1 \cdot A^B = A^B$.

Consecution, odd case $y = 2y' + 1$: the new left side is $(z x) \cdot (x^2)^{y'} = z \cdot x^{2y' + 1} = z \cdot x^y$.

Consecution, even case $y = 2y'$: the new left side is $z \cdot (x^2)^{y'} = z \cdot x^{y}$.

Adequacy: $y = 0$ gives $z \cdot x^0 = z = A^B$.

Variant: as in Exercise 3.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Define invariant, inductive and adequate, and give a loop with an invariant that is not inductive.
- Explain why the set of adequate inductive predicates lies between $R$ and $W$, and give a predicate between them that is not inductive.
- Apply constant relaxation, uncoupling and term dropping to an unseen postcondition.
- Strengthen a failed invariant by computing wlp through the body, simplifying under the current invariant, and closing the chain.
- Write a quantified partition invariant for an array loop, and prove consecution by cases on the written index.
- Give a natural-number or lexicographic ranking function, including the invariant clauses that the decrease needs.
- Prove soundness of ranking, completeness for deterministic loops, and the failure of natural-number ranking under unbounded choice.
- State the disjunctive well-foundedness theorem, including why the transitive closure is required.

## Materials

- Furia, Meyer and Velder, Loop invariants: Analysis, classification, and examples, ACM Computing Surveys 2014. Read it for essential and bounding invariants, the named generalization techniques and a large catalogue of algorithm invariants. The preprint is [arXiv 1211.4470](https://arxiv.org/abs/1211.4470).
- Bradley and Manna, The Calculus of Computation. Read its material on inductive assertions and termination for ranking functions and for examples with arrays.
- Gries, The Science of Programming, 1981. Read its material on loop development for deriving invariants from postconditions.
- Flanagan and Leino, Houdini, an Annotation Assistant for ESC/Java, FME 2001. Read it for the original candidate filtering algorithm.
- Colón, Sankaranarayanan and Sipma, Linear Invariant Generation Using Non-linear Constraint Solving, CAV 2003. Read it for template-based invariant generation with Farkas' lemma.
- Podelski and Rybalchenko, A Complete Method for the Synthesis of Linear Ranking Functions, VMCAI 2004. Read it for the reduction of linear ranking synthesis to linear programming.
- Podelski and Rybalchenko, Transition Invariants, LICS 2004. Read it for disjunctive well-foundedness and the use of Ramsey's theorem.
