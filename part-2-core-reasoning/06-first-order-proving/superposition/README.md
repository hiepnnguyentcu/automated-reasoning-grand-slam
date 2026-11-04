# Superposition

Part 2, Chapter 6: First-Order Proving.

## Objective

Apply the superposition calculus with term orderings and explain how it handles equality.

## Why this matters

Almost every interesting first-order problem involves equality: software specifications use data structure axioms, and mathematics uses algebraic laws. Superposition is the calculus inside Vampire, E and SPASS, and it is the standard method for first-order logic with equality. It combines the [ordered resolution](../first-order-resolution/) of the previous topics with the [orderings and critical pairs](../term-rewriting/) of completion. The ground case explains what [congruence closure](../../05-smt/equality-and-congruence-closure/) does in SMT, and the nonground case handles quantifiers without the instantiation heuristics of [E-matching](../../05-smt/quantifiers/). Knowing this calculus lets you read prover proofs, choose orderings and judge whether a new encoding of a verification problem will behave well.

## Prerequisites

- [Unification](../unification/) for mgus.
- [First-Order Resolution](../first-order-resolution/) for clauses, ordered inferences, selection, redundancy and the model construction.
- [Term Rewriting](../term-rewriting/) for simplification orderings, critical pairs and completion.

## Lesson

### Equality before superposition

Three older approaches explain the shape of the calculus.

The first adds equality axioms: reflexivity, symmetry, transitivity and one congruence axiom per symbol position. Each is a clause, and resolution can then treat $\approx$ as a predicate. This is sound and complete but impractical, since symmetry and transitivity resolve with almost everything, and the number of derivable clauses explodes.

The second is paramodulation (Robinson and Wos, 1969). It builds in replacement of equals by equals:

$$
\frac{C \lor l \approx r \qquad D[l']}{(C \lor D[r])\sigma}, \qquad \sigma = \mathrm{mgu}(l, l').
$$

This removes the axioms but has no ordering restriction, and it allows replacement into variable positions. The search remains enormous.

The third is Knuth-Bendix completion, which only rewrites a term to a smaller term and only needs overlaps at non-variable positions. It works only for unit equations, and it can fail on unorientable ones.

Superposition combines these ideas. Replacement goes from larger to smaller, only into the larger side of the maximal literal, and never into a variable. Bachmair and Ganzinger proved in 1990 and 1994 that these restrictions preserve refutational completeness for full clauses, with selection and a strong redundancy criterion.

### Setting

All atoms are equations. A literal is $s \approx t$ or $s \not\approx t$, with $\approx$ symmetric. A clause is a multiset of literals. A predicate atom $P(t_1, \ldots, t_n)$ is encoded as the equation $P(t_1, \ldots, t_n) \approx \top$, where $\top$ is a special constant smallest in the ordering, and $P$ is treated as a function symbol into a separate Boolean sort. So $\neg P(t)$ is $P(t) \not\approx \top$.

Fix a reduction ordering $\succ$ on terms that is total on ground terms and has the subterm property, for example [KBO or LPO](../term-rewriting/) with a total precedence. Superposition needs ground totality because the model construction compares arbitrary ground instances.

Extend $\succ$ to literals by mapping each literal to a multiset of terms and using the multiset extension:

$$
s \approx t \mapsto \{s, t\}, \qquad s \not\approx t \mapsto \{s, s, t, t\}.
$$

Extend to clauses by the multiset extension of the literal ordering. As a result, $s \not\approx t \succ s \approx t$. Also, a literal whose largest term is $u$ is greater than any literal built from terms smaller than $u$. The negative literal is doubled so that a clause with $s \not\approx t$ is above a clause that produces the rule for $s$.

On nonground terms $\succ$ is partial. The test $s \not\preceq t$ means that $s$ is neither smaller than nor equal to $t$. It allows the incomparable case, which cannot be excluded because some ground instances may go either way.

A selection function $S$ assigns to each clause a multiset of its negative literals, as in [ordered resolution](../first-order-resolution/).

### The calculus

Let $\sigma$ be an mgu in each rule, and let premises be variable-disjoint.

Superposition right:

$$
\frac{C \lor l \approx r \qquad D \lor s[l'] \approx t}{(C \lor D \lor s[r] \approx t)\sigma}
$$

Superposition left:

$$
\frac{C \lor l \approx r \qquad D \lor s[l'] \not\approx t}{(C \lor D \lor s[r] \not\approx t)\sigma}
$$

Equality resolution:

$$
\frac{D \lor s \not\approx t}{D\sigma}
$$

Equality factoring:

$$
\frac{C \lor s \approx t \lor s' \approx t'}{(C \lor t \not\approx t' \lor s' \approx t')\sigma}
$$

The side conditions are listed below.

For both superposition rules:

1. $\sigma = \mathrm{mgu}(l, l')$.
2. $l'$ is not a variable. This is the key restriction. The term $l$ itself may be a variable, as Example 3 shows.
3. $l\sigma \not\preceq r\sigma$ and $s\sigma \not\preceq t\sigma$. Replacement happens only from the larger side, and only into the larger side.
4. In the left premise, $(l \approx r)\sigma$ is strictly maximal in the premise after $\sigma$, and nothing is selected.

For superposition right:

5. In the right premise, $(s \approx t)\sigma$ is strictly maximal after $\sigma$, and nothing is selected.
6. $(l \approx r)\sigma \not\succeq (s \approx t)\sigma$. This condition is sometimes omitted in presentations, and it only reduces inferences.

For superposition left:

7. In the right premise, $s \not\approx t$ is selected, or nothing is selected and $(s \not\approx t)\sigma$ is maximal after $\sigma$.

For equality resolution:

8. $\sigma = \mathrm{mgu}(s, t)$, and $s \not\approx t$ is selected, or nothing is selected and $(s \not\approx t)\sigma$ is maximal.

For equality factoring:

9. $\sigma = \mathrm{mgu}(s, s')$, $s\sigma \not\preceq t\sigma$, nothing is selected, and $(s \approx t)\sigma$ is maximal.

Each rule is sound. Superposition combines congruence with case analysis: if neither $C\sigma$ nor $D\sigma$ holds, then $l\sigma \approx r\sigma$ and $s[l']\sigma \approx t\sigma$ hold, so $s[r]\sigma \approx t\sigma$ holds. Equality resolution holds because $s\sigma \not\approx s\sigma$ is false. Equality factoring is sound because $s\sigma = s'\sigma$, so $s \approx t$ together with $t \approx t'$ implies $s' \approx t'$.

### What the rules do on special cases

On predicates, superposition with $P(t) \approx \top$ into $P(t') \not\approx \top$ produces $\top \not\approx \top$, which equality resolution removes. The two steps together are ordered resolution. Equality factoring on $P(t) \approx \top \lor P(t') \approx \top$ produces $\top \not\approx \top \lor P(t') \approx \top$, which reduces to $P(t') \approx \top$. This is ordered factoring. So [ordered resolution](../first-order-resolution/) is the fragment of the calculus without genuine equations, and traces below name these two combined steps Res and Fact. A superposition into a Boolean atom, such as $f(a) \approx a$ into $P(f(a))$, works like any other rewriting.

On positive unit equations, superposition right is exactly the deduction of critical pairs in unfailing completion. Rewriting with the unit is demodulation, discussed below. So [Knuth-Bendix completion](../term-rewriting/) is the fragment with only unit equations.

On ground clauses with only positive and negative equational units, superposition computes a convergent ground rewrite system. This is the same result that congruence closure represents by a union-find structure.

### Candidate models

The completeness proof generalizes the [resolution model construction](../first-order-resolution/). The interpretation is now a convergent ground rewrite system $R$, and it makes $s \approx t$ true when $s \downarrow_R t$.

For a set $M$ of ground clauses, process clauses in increasing order. Let $R_C = \bigcup_{D \prec C} E_D$. Let

$$
E_C = \{s \to t\}
$$

if $C = D \lor s \approx t$ meets all of the following, and $E_C = \emptyset$ otherwise.

- $C$ is false in $R_C$.
- $s \approx t$ is strictly maximal in $C$, $s \succ t$, and nothing is selected in $C$.
- $s$ is irreducible by $R_C$.
- $D$ is false in $R_C \cup \{s \to t\}$.

Let $R_\infty = \bigcup_C E_C$. Every rule decreases, so $R_\infty$ terminates. Since a left side is irreducible by all earlier rules, no two rules overlap, so $R_\infty$ has no critical pairs and is convergent.

Theorem (ground model). Let $M$ be a set of ground clauses saturated up to redundancy under the ground rules, with $\bot \notin M$. Then $R_\infty \models M$.

Proof sketch. Let $C$ be a smallest clause false in $R_\infty$. It is not redundant, since smaller clauses are true in $R_\infty$.

Case 1. $C = D \lor s \not\approx t$ with this literal selected or maximal, and $s \succeq t$. Since the literal is false, $s \downarrow t$. If $s = t$, equality resolution gives $D$. It is smaller than $C$ and false, a contradiction. If $s \succ t$, then $s$ is reducible at a position by a rule $l \to r$ produced by a clause $B \lor l \approx r \prec C$. Superposition left gives $B \lor D \lor s[r] \not\approx t$. This conclusion is smaller than $C$. It is false in $R_\infty$, because $B$ and $D$ are false, and $s[r] \downarrow t$ by convergence. This is a contradiction.

Case 2. Nothing is selected, and the maximal literal is positive, say $s \approx t$ with $s \succ t$ (the case $s = t$ makes $C$ true). Three subcases arise.

Subcase a: $s$ is reducible by $R_C$, by a rule $l \to r$ from $B \lor l \approx r$. Superposition right gives a conclusion that is smaller than $C$ and false, a contradiction.

Subcase b: $s$ is irreducible and $s \approx t$ is strictly maximal. The production conditions then hold unless the remainder $D$ of $C$ becomes true in $R_C \cup \{s \to t\}$. If all hold, $C$ produces and is true, a contradiction. If $D$ becomes true, it must contain a literal $s \approx t'$ with $t \downarrow t'$, because only a positive literal with top term $s$ can change value when the rule for $s$ is added. Equality factoring then gives $D' \lor t \not\approx t' \lor s \approx t'$. This conclusion is smaller than $C$. It is false: $t \downarrow t'$ under $R_C$ makes the new negative literal false, and $s \approx t'$ is false in $R_\infty$ since $C$ is false. This is a contradiction.

Subcase c: $s \approx t$ occurs twice. Equality factoring applies with $t = t'$, and the same argument gives a contradiction. $\square$

This is the role of equality factoring: it repairs a clause whose maximal term cannot produce, because a second literal with the same maximal term would become true. The clause set $\{a \approx b \lor a \approx c, b \approx c\}$ in Example 4 shows this.

### Lifting and the absence of variable overlaps

Let $N$ be saturated, and let $M = \mathrm{gnd}(N)$. A ground inference from $M$ lifts to an inference from $N$, as in [resolution](../first-order-resolution/), when the rewrite step is at a position that comes from the non-variable part of the clause. Stability of the ordering guarantees that the conditions hold before instantiation.

Here is the reason that a rewrite below a variable needs no inference. Consider a ground instance $C\theta$ where $x\theta$ is reducible by $R_\infty$. Let $\theta'$ be $\theta$ with $x\theta$ replaced by its normal form. Then $C\theta' \prec C\theta$ by monotonicity, and $C\theta'$ is another ground instance of $C$. By the minimality of the counterexample, $C\theta'$ is true in $R_\infty$. Since $x\theta$ and $x\theta'$ have the same normal form, $C\theta$ is true as well. So only instances with irreducible substitutions are relevant, and the reducible case disappears. This is the same fact as the variable-overlap case in the [critical pair lemma](../term-rewriting/).

Theorem (refutational completeness, Bachmair and Ganzinger). Let $\succ$ be a reduction ordering total on ground terms, and let $S$ be a selection function. If $N$ is saturated up to redundancy under the superposition calculus and $\bot \notin N$, then $N$ is satisfiable. So every fair derivation from an unsatisfiable set produces $\bot$.

### Redundancy and simplification

A ground clause $C$ is redundant with respect to a ground set $M$ if $C$ follows from clauses of $M$ smaller than $C$. An inference with main premise $C_m$ is redundant if its conclusion follows from clauses of $M$ smaller than $C_m$. For a nonground set, the definitions apply to all ground instances. Saturation up to redundancy means that every inference from $N$ is redundant in this sense.

Redundancy is a semantic and ordering-based condition, so it is undecidable in general. Provers use sufficient conditions. The most important are below.

Demodulation. From $l \approx r$ and $C[l\sigma]$, derive $C[r\sigma]$ and delete $C[l\sigma]$. The conditions are that $\sigma$ is a match, $l\sigma \succ r\sigma$, and $C[l\sigma] \succ (l \approx r)\sigma$. The second condition is needed so that $C[l\sigma]$ follows from smaller clauses, namely $C[r\sigma]$ and the unit instance. It is demodulation that lets you keep the set small. Kovács and Voronkov call it rewriting by unit equalities. Because rewriting is performed with a match, the clause being simplified is not instantiated.

Subsumption. As in resolution, $C$ subsumes $D$ if $C\sigma$ is a sub-multiset of $D$, and $D$ can then be deleted. Equality literals are matched modulo symmetry.

Tautology deletion. A clause containing $t \approx t$ or a complementary pair is redundant. Equational tautologies such as $a \not\approx b \lor b \not\approx c \lor a \approx c$ are also redundant, and congruence closure can recognize them.

Deletion of trivial literals. The literal $t \not\approx t$ can be removed, since this is equality resolution with an empty unifier, and the result makes the premise redundant. Duplicates of a literal can be merged.

Subsumption resolution. If $(C \lor A)\sigma$ is contained in $D \lor B$ as sets and $A\sigma = B$, then $D \lor \neg B$ can be replaced by $D$.

### Selection

Selecting a negative literal blocks every inference on positive literals of that clause until the selected literal is resolved away. Selection is an important strategic tool: with all negative literals selected, a clause $\neg A_1 \lor \cdots \lor \neg A_n \lor B$ waits until each antecedent is established. Reger, Suda, Voronkov and Hoder evaluate incomplete selection strategies in Vampire, which fall outside the completeness theorem, as discussed in [saturation provers](../saturation-provers/).

## Worked examples

In traces, `x1` stands for $x_1$, `≈` for $\approx$, `≉` for $\not\approx$, and `·` for a binary function symbol in infix notation. Weights are for KBO with all symbols and variables of weight 1, unless the example says otherwise.

### Example 1: comparing literals

Use LPO with $a \succ b \succ c$, and the clause $a \approx b \lor a \approx c \lor b \not\approx c$.

```
a ≈ b      {a, b}
a ≈ c      {a, c}
b ≉ c      {b, b, c, c}

{a, b} > {a, c}          common a cancels, b > c
{a, c} > {b, b, c, c}    common c cancels, a > b and a > c
```

So the order is $a \approx b \succ a \approx c \succ b \not\approx c$. The literal $a \approx b$ is strictly maximal. A negative literal is above a positive one with the same top term, since $\{s, s, t, t\} \succ \{s, t\}$, but it is below a positive literal with a larger top term.

### Example 2: a group in which every element has order 2 is commutative

Use KBO with $\cdot > a > b > e$. Prove $x_1 \cdot x_1 \approx e$ together with the group axioms entails commutativity. Skolemize the negated goal with constants $a$ and $b$.

```
1. e·x1 ≈ x1
2. x1·x1 ≈ e
3. (x1·x2)·x3 ≈ x1·(x2·x3)
4. a·b ≉ b·a
```

The weight of each side is compared. For instance $(x_1 \cdot x_2) \cdot x_3$ and $x_1 \cdot (x_2 \cdot x_3)$ have the same weight and variables, and the left is larger by the first argument, since $x_1 \cdot x_2 \succ x_1$. The inference steps are as follows.

```
5. x2·(x2·x1) ≈ x1
   Superpose 2 into 3 at position 1 of (x1·x2)·x3.
   Rename 2 as x4·x4 ≈ e, mgu {x1 ↦ x4, x2 ↦ x4}.
   Conclusion: e·x3 ≈ x4·(x4·x3).
   Demodulate e·x3 to x3 with 1, then rename.

6. x1·e ≈ x1
   Superpose 2 into 5 at position 2 of x2·(x2·x1).
   Rename 2 as x4·x4 ≈ e, mgu {x2 ↦ x4, x1 ↦ x4}.
   Conclusion: x4·e ≈ x4.

7. x1·(x2·(x1·x2)) ≈ e
   Superpose 2 into 3 at the root of (x1·x2)·x3.
   Rename 2 as x4·x4 ≈ e, mgu {x4 ↦ x1·x2, x3 ↦ x1·x2}.
   Conclusion: e ≈ x1·(x2·(x1·x2)).

8. x2·(x1·x2) ≈ x1
   Superpose 7 into 5 at position 2 of x2'·(x2'·x1').
   Use 7 in the form x1·(x2·(x1·x2)) ≈ e.
   mgu {x2' ↦ x1, x1' ↦ x2·(x1·x2)}.
   Conclusion: x1·e ≈ x2·(x1·x2).
   Demodulate x1·e to x1 with 6, then rename.

9. x1·x2 ≈ x2·x1
   Superpose 8 into 5 at position 2 of x2'·(x2'·x1').
   Use 8 in the form x2·(x1·x2) ≈ x1.
   mgu {x2' ↦ x2, x1' ↦ x1·x2}.
   Conclusion: x2·x1 ≈ x1·x2.

10. ⊥
   Demodulate 4 with 9. Since a > b, the instance a·b > b·a is decreasing,
   and 4 is larger than the instance, so 4 becomes b·a ≉ b·a.
   Delete the trivial literal to obtain ⊥.
```

Each superposition has a mgu instantiation of its left side that is not smaller than the right side, which is the required orientation test. Clause 9 cannot be oriented as a rule, but superposition does not require that: an unorientable equation is used in both directions on instances, as allowed by ordered rewriting. A short script checked that each step is a logical consequence of its premises and that the input is unsatisfiable.

### Example 3: a superposition from a variable

Use LPO with $e \succ d \succ c \succ b$.

```
1. x1 ≈ b ∨ x1 ≈ c ∨ x1 ≈ d
2. e ≉ b
3. e ≉ c
4. e ≉ d
```

Clause 1 says the domain has at most three elements with these names, and the other clauses say that $e$ is none of them. The variable $x_1$ is allowed on the left of a superposition, since $x_1\sigma \not\preceq d\sigma$ can hold after $\sigma$. The target $e$ in clause 4 is not a variable, so condition 2 is met.

```
5. e ≈ b ∨ e ≈ c
   Superpose x1 ≈ d from 1 into e in 4, with mgu {x1 ↦ e}.
   After σ, e ≈ d is strictly maximal in e ≈ b ∨ e ≈ c ∨ e ≈ d, and e > d.
   Conclusion: e ≈ b ∨ e ≈ c ∨ d ≉ d. Remove the trivial literal.

6. e ≈ b
   Superpose e ≈ c, which is strictly maximal in 5, into e in 3, with the empty mgu.
   Conclusion: e ≈ b ∨ c ≉ c. Remove the trivial literal.

7. ⊥
   Superpose e ≈ b from 6 into e in 2. Conclusion: b ≉ b. Remove it.
```

Note that a simplification ordering cannot orient $x_1 \approx d$ at the clause level, because the two sides are incomparable. Only after applying $\sigma$ is the literal oriented.

### Example 4: why equality factoring exists

Use LPO with $a \succ b \succ c$, no selection, and the satisfiable set $N = \{a \approx b \lor a \approx c,\ b \approx c\}$.

Without equality factoring, $N$ is saturated: $a \approx b$ is strictly maximal in the first clause, $b \approx c$ can only rewrite $b$ inside $a \approx b$, and this is the smaller side of a literal, which is not allowed. The candidate model is built as follows.

```
b ≈ c         false in {}, b irreducible            produce b → c
a ≈ b ∨ a ≈ c false in {b → c}, a ≈ b is maximal    a irreducible
              But adding a → b would make a ≈ c true, since a → b → c.
              So the remainder is not false, and there is no production.
Model: {b → c}, in which the first clause is false.
```

The construction fails, and equality factoring is what repairs it. It applies to $a \approx b \lor a \approx c$ with $s = s' = a$, giving $b \not\approx c \lor a \approx c$. Now consider clauses in increasing order.

```
b ≈ c                 produce b → c
b ≉ c ∨ a ≈ c         false in {b → c}, a ≈ c strictly maximal,
                      remainder b ≉ c false: produce a → c
a ≈ b ∨ a ≈ c         true, since a and b both reduce to c
Model: {b → c, a → c}, which satisfies all clauses.
```

The only remaining allowed inference superposes $a \approx c$ from the new clause into the first clause, and its conclusion $b \not\approx c \lor a \approx c \lor c \approx b$ is a tautology. So the extended set is saturated up to redundancy.

### Example 5: a theory of arrays

This example uses an axiom from [arrays in SMT](../../05-smt/arrays/). Use KBO with $\mathit{sel} > \mathit{st} > a > i > j > v > w$. Prove that writing to $j$ does not disturb a value stored at a different index $i$.

```
1. sel(st(x1,x2,x3), x2) ≈ x3
2. x1 ≈ x2 ∨ sel(st(x3,x1,x4), x2) ≈ sel(x3, x2)
3. i ≉ j
4. sel(st(st(a,i,v), j, w), i) ≉ v
```

In clause 2, the second literal is maximal, because its top term contains all the variables and weighs more.

```
5. j ≈ i ∨ sel(st(a,i,v), i) ≉ v
   Superpose the second literal of 2 into 4 at the root of the left side.
   mgu {x3 ↦ st(a,i,v), x1 ↦ j, x4 ↦ w, x2 ↦ i}.

6. j ≈ i
   Demodulate sel(st(a,i,v), i) to v with 1, giving j ≈ i ∨ v ≉ v.
   Remove the trivial literal.

7. ⊥
   Demodulate 3 with 6. Since i > j, i rewrites to j, giving j ≉ j.
   Remove the trivial literal.
```

## Common mistakes

- Superposing into a variable position. Condition 2 forbids this. Only the term $l'$ of the target must be non-variable, while $l$ itself can be a variable.
- Superposing into the smaller side of an equation. The target must be in $s$ with $s\sigma \not\preceq t\sigma$.
- Comparing before applying $\sigma$. The side conditions are tested on instances, and a literal maximal before $\sigma$ can stop being maximal after it.
- Treating incomparable terms as forbidden. The tests use $\not\preceq$, so incomparable sides are allowed.
- Using the instantiating mgu for demodulation. Demodulation uses matching only, so the clause being simplified keeps its variables.
- Demodulating a clause with a rule when the instance is not smaller than the clause. A unit clause $a \approx b$ with $a \succ b$ cannot be demodulated by itself, because that would delete it.
- Omitting equality factoring in a non-Horn problem. Example 4 shows why the rule is needed.
- Forgetting to treat predicates as Boolean terms when comparing literals. $\neg P(a)$ is $\{P(a), P(a), \top, \top\}$.
- Assuming an ordering that is partial on ground terms. Ground totality is an assumption of the completeness theorem.

## Exercises

1. State the rules of superposition, equality resolution and equality factoring with their side conditions.

<details><summary>Solution</summary>

See the calculus section. The answer must include the mgu, the non-variable condition on $l'$, the orientation conditions $l\sigma \not\preceq r\sigma$ and $s\sigma \not\preceq t\sigma$, strict maximality with no selection for positive premises, the rule for selected or maximal negative literals, and the maximality condition with $s\sigma \not\preceq t\sigma$ in equality factoring.

</details>

2. Use LPO with $f > a > b > c$. Order the literals $f(a) \approx b$, $f(a) \not\approx c$, $a \approx b$, $f(b) \not\approx b$, $P(f(a))$ with $P$ above all function symbols, and $\top$ smallest.

<details><summary>Solution</summary>

Their multisets are as follows.

```
P(f(a))      {P(f(a)), ⊤}
f(a) ≉ c     {f(a), f(a), c, c}
f(a) ≈ b     {f(a), b}
f(b) ≉ b     {f(b), f(b), b, b}
a ≈ b        {a, b}
```

$P(f(a))$ is largest, because $P(f(a)) \succ f(a)$. The literal $f(a) \not\approx c$ is above $f(a) \approx b$, because after cancelling one $f(a)$, the remaining $\{f(a), c, c\}$ dominates $\{b\}$. The literal $f(a) \approx b$ is above $f(b) \not\approx b$, because $f(a) \succ f(b)$ under LPO and $f(a)$ is above both $f(b)$ copies and both $b$ copies. Finally, $f(b) \succ a$ and $f(b) \succ b$, so $f(b) \not\approx b$ is above $a \approx b$. The order is $P(f(a)) \succ f(a) \not\approx c \succ f(a) \approx b \succ f(b) \not\approx b \succ a \approx b$.

</details>

3. Use KBO with $f > c > b$. Refute the following clauses with superposition. Write every inference with its mgu.

$$
f(x_1) \not\approx c \lor f(x_1) \approx b, \qquad f(f(x_1)) \approx x_1, \qquad b \not\approx c.
$$

<details><summary>Solution</summary>

```
1. f(x1) ≉ c ∨ f(x1) ≈ b
2. f(f(x1)) ≈ x1
3. b ≉ c

4. x1 ≉ c ∨ f(f(x1)) ≈ b
   Superpose 2 into the maximal literal f(x1) ≉ c of 1.
   Rename 2 as f(f(x2)) ≈ x2, mgu {x1 ↦ f(x2)}.
   Conclusion: x2 ≉ c ∨ f(f(x2)) ≈ b.

5. x1 ≉ c ∨ x1 ≈ b
   Superpose 2 into f(f(x1)) ≈ b of 4, which is strictly maximal.
   The mgu matches x2 of the renamed 2 with x1.
   Conclusion: x1 ≉ c ∨ x1 ≈ b.

6. c ≈ b
   Equality resolution on x1 ≉ c in 5, with mgu {x1 ↦ c}.
   After σ, c ≉ c is maximal in c ≉ c ∨ c ≈ b.

7. ⊥
   Superpose c ≈ b into c in 3, with b ≉ c read as c ≉ b.
   Conclusion: b ≉ b. Equality resolution gives ⊥.
```

In step 4, $f(x_1) \not\approx c$ is the larger literal of clause 1, because $\{f(x_1), f(x_1), c, c\}$ dominates $\{f(x_1), b\}$. A short script confirmed each step.

</details>

4. Compute the conclusion of equality factoring on $f(x_1) \approx a \lor f(b) \approx c$, and state the side conditions to check. Use KBO with $f > a > b > c$.

<details><summary>Solution</summary>

Take $s \approx t$ as $f(x_1) \approx a$, and $s' \approx t'$ as $f(b) \approx c$. The mgu is $\{x_1 \mapsto b\}$. The conclusion is $a \not\approx c \lor f(b) \approx c$. The checks are that $f(b) \not\preceq a$, which holds, that nothing is selected, which holds, and that $(f(x_1) \approx a)\sigma = f(b) \approx a$ is maximal after $\sigma$, which holds because it is above $f(b) \approx c$, since $a \succ c$.

</details>

5. Let $N = \{c \approx b,\ d \approx c \lor d \approx b,\ d \not\approx b\}$ with LPO and $d > c > b$, and no selection. Find all inferences without equality factoring. Show that each is redundant, so that $N$ is saturated up to redundancy without that rule. Why does this show that the calculus without equality factoring is incomplete?

<details><summary>Solution</summary>

The maximal literal of the second clause is $d \approx c$. It is strictly maximal, and $d \succ c$, so it can superpose into $d$ of $d \not\approx b$, which is maximal in that unit. No superposition into $d \approx c$ from $c \approx b$ is allowed, because $c$ is the smaller side. The rule $c \approx b$ has no other target, the second clause can only use its maximal literal, and a superposition of $d \approx c$ into its own copy is blocked by condition 6. So there is one inference, with conclusion $c \not\approx b \lor d \approx b$.

The main premise is $d \not\approx b$. Compare the multisets: $\{d, d, b, b\}$ is above $\{d, c\}$ and $\{d, b\}$, so the second clause is smaller than $d \not\approx b$. The clause $c \approx b$ is smaller too. The conclusion follows from these two: if $c = b$, the second clause gives $d \approx b$. So the inference is redundant.

Thus $N$ is saturated up to redundancy and does not contain $\bot$. But $N$ is unsatisfiable, since $c \approx b$ and either case of the second clause contradict $d \not\approx b$. So the theorem would be false without equality factoring. With the rule, the same clause $c \not\approx b \lor d \approx b$ is derived from the second clause as main premise. Now only $c \approx b$ is smaller than the main premise, and it does not imply the conclusion, so the inference is not redundant. The refutation follows: $d \approx b$ is strictly maximal in the new clause and superposes into $d \not\approx b$ to give $c \not\approx b$ after removing $b \not\approx b$, and $c \approx b$ superposes into this to give $\bot$.

</details>

6. Prove that demodulation is a redundancy elimination when its conditions hold. Show also that the condition $C[l\sigma] \succ (l \approx r)\sigma$ cannot be dropped, using a unit equation and the clause equal to it.

<details><summary>Solution</summary>

Let $\theta$ make $C[l\sigma]$ ground. The clause $C[l\sigma]\theta$ follows from $C[r\sigma]\theta$ and $(l \approx r)\sigma\theta$ by congruence. Stability gives $l\sigma\theta \succ r\sigma\theta$, so monotonicity gives $C[r\sigma]\theta \prec C[l\sigma]\theta$. Stability also gives $(l \approx r)\sigma\theta \prec C[l\sigma]\theta$. So the original clause follows from smaller ground instances and is redundant, once the conclusion and the unit are in the set.

For the second part, let $a \succ b$ and take the unit $a \approx b$. Applied to itself with no condition, demodulation replaces $a \approx b$ by $b \approx b$, which is a tautology. The information $a \approx b$ is lost. The condition blocks this because $a \approx b$ is not greater than itself.

</details>

7. Explain why ground totality of the ordering is required, and why a nonground ordering cannot be total, even for KBO or LPO.

<details><summary>Solution</summary>

The candidate model processes all ground clauses and assumes that each ground literal has a definite place in the order, so each clause has a unique maximal literal or a repeated one. Without totality, a clause with two incomparable maximal literals would have neither case of the production rule. So the proof fails.

No stable ordering can be total on nonground terms. If $x_1 \succ x_2$ held, then stability under the renaming that swaps them would give $x_2 \succ x_1$, a contradiction. The same holds for $x_1 \cdot x_2$ and $x_2 \cdot x_1$. So incomparable pairs are unavoidable, and the calculus handles them through conditions of the form $\not\preceq$.

</details>

8. Give a selection function on a clause $\neg P(x_1) \lor \neg Q(x_1) \lor R(x_1)$ with no equations, and describe which of the rules can act on it when $P(a)$ is available. Does the choice affect completeness?

<details><summary>Solution</summary>

Let $S$ pick $\neg P(x_1)$, or any negative literal. The clause can then only act through superposition left into this literal. The combined step Res with $P(a)$ produces $\neg Q(a) \lor R(a)$. Positive-literal inferences on $R(x_1)$, and inferences on $\neg Q(x_1)$, are blocked. The choice does not affect refutational completeness, since the completeness theorem holds for any selection function of negative literals. It can have a large effect on the size of the search.

</details>

9. State what the calculus reduces to on problems with only positive unit equations, with a goal consisting of a single negative ground unit. Explain why a solver with this restriction need not use equality factoring or selection.

<details><summary>Solution</summary>

The positive units generate unfailing completion. Superposition right is deduction of critical pairs. Demodulation is simplification with the system. The single goal is rewritten by superposition left, and equality resolution closes it when the two sides normalize to the same term. There is no clause with two positive literals, so equality factoring has no premise. The only negative literal is in a unit, so selection has no effect.

</details>

10. A paramodulation-style prover allows superposition into a variable. Give a concrete example of how this can cause many useless inferences on the clause $P(x_1)$ and a unit equation $a \approx b$, and say why the completeness proof shows they are unnecessary.

<details><summary>Solution</summary>

Superposition into the variable $x_1$ of $P(x_1)$ with $a \approx b$ gives $P(b)$. This is true for any unit equation and any variable occurrence, so each unit can act on every variable position in every clause, without any restriction from a symbol of the target. The result is just an instance of $P(x_1)$, which is already subsumed by it.

The completeness proof handles this through the variable case. A ground instance whose substitution is reducible is above the instance with the normalized substitution, and the latter is true by minimality. So the instance whose variable is rewritten never needs its own inference.

</details>

11. Design: extend the calculus informally to a new theory-specific simplification rule, namely deleting a literal $t \not\approx t'$ when $t$ and $t'$ are equal in a decidable theory. State the two facts you would have to prove to keep completeness.

<details><summary>Solution</summary>

Soundness requires that the conclusion is a consequence of the premise and the theory. Deleting a false literal gives a clause that follows from the original one, modulo the theory, so soundness holds.

Keeping completeness requires redundancy. The original clause must follow from the smaller replacement clause. If the deletion is a removal of a literal, the conclusion is a sub-multiset of the premise, so it is smaller. It also implies the premise, so the premise becomes redundant. The second fact is that the theory itself is available in the semantics, so the argument must be done in a setting that interprets the theory, and not in pure first-order logic with equality. The classical completeness theorem covers only uninterpreted symbols, unless the theory axioms are added as clauses.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write the four rules with all side conditions.
- Compute literal and clause comparisons in KBO and LPO.
- Run superposition on a small nonground problem and write the proof with mgus and orderings.
- Explain the candidate model with rewrite rules and the production condition.
- Explain equality factoring with an example, and explain why inferences into variables are unnecessary.
- State the conditions of demodulation, and show why each condition is needed.

## Materials

- Bachmair and Ganzinger, Rewrite-Based Equational Theorem Proving with Selection and Simplification, Journal of Logic and Computation 1994. Read it for the calculus, the candidate model construction, and the redundancy framework.
- Kovács and Voronkov, First-Order Theorem Proving and Vampire, CAV 2013. Read it for a compact statement of the calculus in the form Vampire uses, and for the definitions of subsumption, demodulation and subsumption resolution. Its equality factoring and demodulation statements differ in form from the ones here, so check side conditions against the Bachmair and Ganzinger paper.
- Nieuwenhuis and Rubio, Paramodulation-Based Theorem Proving, in Handbook of Automated Reasoning, 2001. Read it for an extended treatment of the calculus, its variants and its completeness proofs.
- Robinson and Wos, Paramodulation and Theorem-Proving in First-Order Theories with Equality, Machine Intelligence 4, 1969. Read it for the origin of paramodulation.
