# Unification

Part 2, Chapter 6: First-Order Proving.

## Objective

Compute most general unifiers by hand and prove the algorithm correct.

## Why this matters

Every inference of a first-order prover starts with a unification. Resolution, factoring and superposition all use most general unifiers to perform, in one step, infinitely many ground inferences at once. Without unification a prover would have to guess ground instances, as the earliest Herbrand-style procedures did. The same operation appears in type inference, in logic programming, in the term indexes of [saturation provers](../saturation-provers/) and in the critical pairs of [term rewriting](../term-rewriting/). Matching, the one-sided variant, drives E-matching in [SMT quantifier instantiation](../../05-smt/quantifiers/). An applied scientist who debugs a prover or designs a new rule needs to compute these substitutions by hand and to know exactly what they guarantee.

## Prerequisites

- [First-Order Logic](../../../part-1-foundations/01-mathematical-logic/first-order-logic/) for terms and substitutions.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for structural and well-founded induction.

## Lesson

### Terms and substitutions

Fix a signature of function symbols with arities, where constants have arity 0, and a countably infinite set of variables. Terms are variables, or $f(t_1, \ldots, t_n)$ where $f$ has arity $n$ and each $t_i$ is a term. Write $\mathrm{Var}(t)$ for the variables of $t$.

A substitution is a map $\sigma$ from variables to terms with $x\sigma \neq x$ for only finitely many $x$. Its domain is $\mathrm{dom}(\sigma) = \{x : x\sigma \neq x\}$, and it is written $\{x_1 \mapsto t_1, \ldots, x_n \mapsto t_n\}$. It extends to terms by $f(t_1, \ldots, t_n)\sigma = f(t_1\sigma, \ldots, t_n\sigma)$. All bindings apply simultaneously, so $f(x_1, x_2)\{x_1 \mapsto x_2, x_2 \mapsto x_1\} = f(x_2, x_1)$.

Composition is written left to right: $t(\sigma\tau) = (t\sigma)\tau$. To compute $\sigma\tau$, apply $\tau$ to every right-hand side of $\sigma$, add the bindings of $\tau$ whose variables are outside $\mathrm{dom}(\sigma)$, and delete any binding of the form $x \mapsto x$. Composition is associative and has the empty substitution as identity. It is not commutative.

A renaming is a substitution that is a bijection on variables. A substitution $\sigma$ is idempotent if $\sigma\sigma = \sigma$.

### Unifiers and most general unifiers

A unification problem is a finite set of equations $E = \{s_1 = t_1, \ldots, s_n = t_n\}$. A unifier of $E$ is a substitution $\theta$ with $s_i\theta = t_i\theta$ for every $i$. Here equality means syntactic identity, and no theory is involved.

Define $\sigma \leq \tau$, read as $\sigma$ is more general than $\tau$, if there is a substitution $\rho$ with $\tau = \sigma\rho$. This relation is a preorder. A most general unifier (mgu) of $E$ is a unifier $\sigma$ with $\sigma \leq \theta$ for every unifier $\theta$ of $E$.

The term $f(x_1, x_2)$ and the term $f(x_2, a)$ have the unifier $\{x_1 \mapsto a, x_2 \mapsto a\}$, and this happens to be an mgu. The terms $f(x_1)$ and $f(x_2)$ have unifiers $\{x_1 \mapsto x_2\}$, $\{x_2 \mapsto x_1\}$ and $\{x_1 \mapsto a, x_2 \mapsto a\}$. The first two are most general, and the third is an instance of each.

The reason for wanting an mgu is that it represents all unifiers finitely. A resolution step performed with an mgu covers every ground instance of that step, which is the content of the lifting lemma in [First-Order Resolution](../first-order-resolution/).

### Historical note

Herbrand's 1930 thesis contains an early description of a unification procedure. Robinson's 1965 paper made the most general unifier the centre of automated deduction by building the resolution rule on it. Robinson's original algorithm scans for the first disagreement between two terms and takes exponential time and space in the worst case when terms are represented as trees. Later work reduced this to linear time (Paterson and Wegman, 1978) and to practical near-linear algorithms (Martelli and Montanari, 1982). The rule-based presentation below follows the Martelli and Montanari style, which is the standard way to teach the algorithm because it separates correctness from the choice of data structure.

### The rule-based algorithm

The algorithm rewrites a set of equations by the rules below until no rule applies or a failure rule fires. In each rule, $E$ is the rest of the problem.

| Rule | Equation selected | Result |
|---|---|---|
| Delete | $t = t$ | Remove the equation. |
| Decompose | $f(s_1, \ldots, s_n) = f(t_1, \ldots, t_n)$ | Replace it with $s_1 = t_1, \ldots, s_n = t_n$. |
| Clash | $f(s_1, \ldots, s_n) = g(t_1, \ldots, t_m)$ with $f \neq g$ or $n \neq m$ | Report failure. |
| Orient | $t = x$ with $t$ not a variable | Replace it with $x = t$. |
| Occurs check | $x = t$ with $x \in \mathrm{Var}(t)$ and $x \neq t$ | Report failure. |
| Eliminate | $x = t$ with $x \notin \mathrm{Var}(t)$ and $x$ occurring in $E$ | Keep $x = t$ and replace $E$ by $E\{x \mapsto t\}$. |

A problem is in solved form if it is $\{x_1 = t_1, \ldots, x_n = t_n\}$ where the $x_i$ are pairwise distinct and no $x_i$ occurs in any $t_j$. A solved form determines the substitution $\sigma_E = \{x_1 \mapsto t_1, \ldots, x_n \mapsto t_n\}$.

```
unify(E):
    while some rule applies to an equation in E:
        pick any such equation and rule
        if the rule is Clash or Occurs check:
            return failure
        apply the rule to E
    return the substitution of the solved form E
```

The choice of equation does not affect correctness, by the theorems below. Different choices can produce different mgus, and these differ only by a renaming.

### Correctness

Write $U(E)$ for the set of unifiers of $E$.

Lemma 1. If $x\theta = t\theta$, then $s\{x \mapsto t\}\theta = s\theta$ for every term $s$.

Proof. Use structural induction on $s$. If $s = x$, the left side is $t\theta$ and the right side is $x\theta$, and these are equal by assumption. If $s$ is another variable, both sides are $s\theta$. If $s = f(s_1, \ldots, s_n)$, apply the induction hypothesis to each argument. $\square$

Lemma 2 (preservation). If a non-failure rule transforms $E$ into $E'$, then $U(E) = U(E')$. If a failure rule applies to $E$, then $U(E) = \emptyset$.

Proof. Delete and Orient are immediate. For Decompose, $f(s_1, \ldots, s_n)\theta = f(t_1, \ldots, t_n)\theta$ holds exactly when $s_i\theta = t_i\theta$ for all $i$, by the definition of application and the fact that terms are freely generated. For Eliminate, any $\theta$ that satisfies $x = t$ satisfies $x\theta = t\theta$, and Lemma 1 shows that it unifies an equation of $E$ if and only if it unifies the corresponding equation of $E\{x \mapsto t\}$.

For Clash, the two sides under any $\theta$ have different root symbols or different numbers of arguments, so they differ. For Occurs check, $x$ occurs in $t$ at a non-root position, because $x \neq t$. Then $x\theta$ is a proper subterm of $t\theta$ for every $\theta$, so $x\theta$ is strictly smaller than $t\theta$ and cannot equal it. $\square$

Lemma 3 (termination). Every sequence of rule applications is finite.

Proof. Call $x$ solved in $E$ if $E$ contains an equation $x = t$ and $x$ occurs exactly once in $E$. Define the measure $(n_1, n_2, n_3)$, compared lexicographically, where $n_1$ is the number of unsolved variables of $E$, $n_2$ is the total number of symbol occurrences in $E$, and $n_3$ is the number of equations $t = x$ with $t$ not a variable.

No rule introduces a variable, and a solved variable stays solved. For the last claim, suppose $y = s$ is an equation and $y$ occurs only there. Then $y$ is not the selected equation's left side in Eliminate (because the selected $x$ occurs at least twice) and $y$ does not occur in $t$, so substitution cannot add an occurrence of $y$. Hence $n_1$ never increases.

- Eliminate strictly decreases $n_1$. Before the step $x$ occurs at least twice, so it is unsolved. After the step it occurs exactly once, because $x \notin \mathrm{Var}(t)$.
- Delete and Decompose keep or decrease $n_1$ and strictly decrease $n_2$.
- Orient keeps or decreases $n_1$, keeps $n_2$ and strictly decreases $n_3$.

The lexicographic order on triples of natural numbers is well-founded. $\square$

Lemma 4. If no rule applies to $E$, then $E$ is in solved form. Further, $\sigma_E$ is an idempotent mgu of $E$, and $\theta = \sigma_E\theta$ for every unifier $\theta$ of $E$.

Proof. Take any equation in $E$. It is not $t = t$, by Delete. It does not have two non-variable sides, by Decompose and Clash. It is not of the form $t = x$ with non-variable $t$, by Orient. So it is $x = t$ with $x \neq t$, and $x \notin \mathrm{Var}(t)$ by Occurs check, and $x$ occurs nowhere else by Eliminate. This is the solved form.

Since no $x_i$ occurs in any $t_j$, we have $x_i\sigma_E = t_i = t_i\sigma_E$, so $\sigma_E$ is a unifier, and also $\sigma_E\sigma_E = \sigma_E$. Let $\theta$ be a unifier of $E$. Then $x_i\sigma_E\theta = t_i\theta = x_i\theta$, and for any other variable $y$ we have $y\sigma_E\theta = y\theta$. So $\theta = \sigma_E\theta$, which also shows $\sigma_E \leq \theta$. $\square$

Theorem (correctness of unification). For every finite problem $E$, the algorithm terminates. If it reports failure, then $E$ has no unifier. Otherwise it returns an idempotent mgu of $E$. In particular, every unifiable problem has an mgu.

Proof. Termination is Lemma 3. Failure is correct by Lemma 2, since the current problem has the same unifiers as $E$ and it has none. On success the final problem $E'$ satisfies $U(E') = U(E)$ by Lemma 2, and Lemma 4 applies to $E'$. $\square$

Theorem (uniqueness). If $\sigma$ and $\tau$ are both mgus of $E$, then $\tau = \sigma\rho$ for a substitution $\rho$ that maps the variables of the terms $x\sigma$ injectively to variables. In this sense an mgu is unique up to renaming.

The proof is Exercise 10.

### Complexity and data structures

Applying Eliminate to trees can produce exponentially large terms. Consider

$$
h(x_1, \ldots, x_n) = h(f(x_0, x_0), f(x_1, x_1), \ldots, f(x_{n-1}, x_{n-1})).
$$

The mgu binds $x_k$ to a complete binary tree of $f$ symbols with $2^{k+1} - 1$ nodes. The output itself is exponential when written as a tree, although it has linear size as a directed acyclic graph.

The standard fix keeps terms in a shared graph and represents equalities with a union-find structure. Each class holds nodes that the current problem forces to be equal.

```
close(s, t):
    s := find(s); t := find(t)
    if s == t: return true
    if s and t are both applications:
        if they differ in root symbol or arity: return false
        union(s, t)
        for each argument index i:
            if not close(s.arg(i), t.arg(i)): return false
        return true
    union(s, t), keeping an application as representative if there is one
    return true

unify(s, t):
    if not close(s, t): return failure
    if the graph of classes has a cycle: return failure
    return the substitution read off the class representatives
```

Here the occurs check is postponed to a single cycle check at the end. A class graph has an edge from class $A$ to class $B$ when an application in $A$ has an argument in $B$. Each call to `close` that does not return at once performs a union, so there are at most $n$ such calls on a graph of $n$ nodes, and the running time is almost linear. Provers usually implement unification differently again: Kovács and Voronkov state that Vampire performs all unification-related operations through term indexing.

Many implementations skip the occurs check. Standard Prolog unification omits it by default for speed, and this is unsound as logic. A prover cannot omit it.

### Matching

A substitution $\sigma$ matches a pattern $l$ onto a term $t$ if $l\sigma = t$. Only the variables of $l$ may be bound, and the variables of $t$ act as constants. Matching is simpler than unification and needs no occurs check.

```
match(l, t):
    S := {}
    W := [(l, t)]
    while W is not empty:
        take (u, v) from W
        if u is a variable:
            if S binds u to a term other than v: return failure
            bind u to v in S
        else if v is a variable or the roots or arities differ: return failure
        else add the pairs of corresponding arguments to W
    return S
```

Demodulation and subsumption are based on matching. Superposition and resolution use unification. The difference matters because demodulation replaces a clause by a simpler one, and this replacement is justified only if the clause itself is not instantiated.

### Unification modulo a theory

If equality is taken modulo a theory, the situation changes sharply. Commutative unification has finite complete sets of unifiers and may need more than one. Associative unification can need infinitely many. Second-order syntactic unification is undecidable (Goldfarb, 1981). These results explain why provers do not replace syntactic unification by a general theory-aware variant without careful design. Baader and Snyder's handbook chapter is the standard survey.

## Worked examples

Traces show the problem after each step. In traces, `x1` stands for $x_1$.

### Example 1: a straightforward success

Unify $f(x_1, g(x_2), x_2)$ and $f(g(x_3), x_3, a)$.

```
start        f(x1, g(x2), x2) = f(g(x3), x3, a)
Decompose    x1 = g(x3),  g(x2) = x3,  x2 = a
Orient       x1 = g(x3),  x3 = g(x2),  x2 = a
Eliminate x3 x1 = g(g(x2)),  x3 = g(x2),  x2 = a
Eliminate x2 x1 = g(g(a)),  x3 = g(a),  x2 = a
```

The result is $\sigma = \{x_1 \mapsto g(g(a)), x_2 \mapsto a, x_3 \mapsto g(a)\}$. Checking both sides gives $f(g(g(a)), g(a), a)$ in each case.

### Example 2: variables bound through other variables

Unify $p(x_1, f(x_1), x_3)$ and $p(g(x_2), f(g(a)), h(x_1, x_2))$.

```
start        p(x1, f(x1), x3) = p(g(x2), f(g(a)), h(x1, x2))
Decompose    x1 = g(x2),  f(x1) = f(g(a)),  x3 = h(x1, x2)
Eliminate x1 x1 = g(x2),  f(g(x2)) = f(g(a)),  x3 = h(g(x2), x2)
Decompose    x1 = g(x2),  g(x2) = g(a),  x3 = h(g(x2), x2)
Decompose    x1 = g(x2),  x2 = a,  x3 = h(g(x2), x2)
Eliminate x2 x1 = g(a),  x2 = a,  x3 = h(g(a), a)
```

The result is $\{x_1 \mapsto g(a), x_2 \mapsto a, x_3 \mapsto h(g(a), a)\}$. Both sides become $p(g(a), f(g(a)), h(g(a), a))$.

### Example 3: failure by occurs check after a long chain

Unify $f(x_1, x_1)$ and $f(g(x_2), g(g(x_2)))$.

```
start        f(x1, x1) = f(g(x2), g(g(x2)))
Decompose    x1 = g(x2),  x1 = g(g(x2))
Eliminate x1 x1 = g(x2),  g(x2) = g(g(x2))
Decompose    x1 = g(x2),  x2 = g(x2)
Occurs check on x2 = g(x2): failure
```

The two terms have no unifier. Note that $x_1 = g(x_2)$ and $x_1 = g(g(x_2))$ look harmless, and only elimination reveals the cycle.

### Example 4: a cycle in the graph algorithm

Unify $f(x_1, x_2)$ and $f(x_2, g(x_1))$ with the union-find algorithm.

```
close(f(x1,x2), f(x2,g(x1)))
    union the two f nodes into class A
    close(x1, x2)        union into class B = {x1, x2}
    close(x2, g(x1))     find(x2) is B, union g(x1) into B, representative g(x1)
close returned true
cycle check
    class B contains g(x1), whose argument x1 is in class B
    edge from B to B is a cycle
result: failure
```

The rule-based algorithm reaches the same verdict: Decompose gives $x_1 = x_2, x_2 = g(x_1)$, Eliminate on $x_1$ gives $x_1 = x_2, x_2 = g(x_2)$, and Occurs check fires.

### Example 5: doubling term size

Unify $h(x_1, x_2, x_3, f(x_4, x_4))$ and $h(f(x_2, x_2), f(x_3, x_3), f(x_4, x_4), x_5)$.

```
Decompose    x1 = f(x2,x2),  x2 = f(x3,x3),  x3 = f(x4,x4),  f(x4,x4) = x5
Eliminate x2 x1 = f(f(x3,x3), f(x3,x3)),  x2 = f(x3,x3),  x3 = f(x4,x4),  f(x4,x4) = x5
Eliminate x3 x1 = f(f(f(x4,x4), f(x4,x4)), f(f(x4,x4), f(x4,x4))),
             x2 = f(f(x4,x4), f(x4,x4)),  x3 = f(x4,x4),  f(x4,x4) = x5
Orient       x1 = f(f(f(x4,x4), f(x4,x4)), f(f(x4,x4), f(x4,x4))),
             x2 = f(f(x4,x4), f(x4,x4)),  x3 = f(x4,x4),  x5 = f(x4,x4)
```

The binding of $x_1$ doubles in size with each level. A graph stores each level once.

## Common mistakes

- Unifying clauses without renaming them apart. $P(x_1)$ and $P(f(x_1))$ fail the occurs check if they share $x_1$, but as premises in two clauses they have disjoint variables by convention. Rename one to $P(f(x_2))$, and the mgu is $\{x_1 \mapsto f(x_2)\}$.
- Applying a substitution sequentially instead of simultaneously. $\{x_1 \mapsto x_2, x_2 \mapsto a\}$ sends $x_1$ to $x_2$, and it does not send $x_1$ to $a$. A solved form avoids the issue because its domain variables are absent from its range.
- Composing in the wrong order. In this repository $\sigma\tau$ applies $\sigma$ first.
- Reporting a unifier that is not most general. $\{x_1 \mapsto a, x_2 \mapsto a\}$ unifies $f(x_1)$ and $f(x_2)$, but it is too specific, and using it in resolution loses generality.
- Stopping when the problem looks solved. $x_1 = x_2, x_2 = a$ is not in solved form because $x_2$ occurs in the first equation.
- Treating variables in the subject of a matching problem as bindable. $f(a)$ does not match onto $x_1$, although the two unify.
- Confusing unification with equality modulo a theory. $a + b$ and $b + a$ do not unify syntactically, even if $+$ is commutative in the intended model.
- Dropping the condition that $x$ occurs elsewhere in Eliminate. The rule would then apply forever to a solved equation.

## Exercises

1. State the definition of an mgu, and state one difference between unification and matching.

<details><summary>Solution</summary>

An mgu of $E$ is a unifier $\sigma$ of $E$ such that every unifier $\theta$ of $E$ has the form $\sigma\rho$ for some substitution $\rho$. In matching $l$ onto $t$, only the variables of $l$ may be bound, and the variables of $t$ are treated as constants. In unification, variables on both sides may be bound.

</details>

2. Let $\sigma = \{x_1 \mapsto f(x_2)\}$ and $\tau = \{x_1 \mapsto b, x_2 \mapsto a\}$. Compute $\sigma\tau$ and $\tau\sigma$.

<details><summary>Solution</summary>

For $\sigma\tau$, apply $\tau$ to the right-hand side of $\sigma$ to get $x_1 \mapsto f(a)$, then add the binding $x_2 \mapsto a$ from $\tau$, and discard $x_1 \mapsto b$ because $x_1$ is already in the domain of $\sigma$. So $\sigma\tau = \{x_1 \mapsto f(a), x_2 \mapsto a\}$.

For $\tau\sigma$, applying $\sigma$ to $b$ and $a$ changes nothing, and the binding of $x_1$ in $\sigma$ is discarded. So $\tau\sigma = \{x_1 \mapsto b, x_2 \mapsto a\}$. The two results differ, which shows that composition is not commutative.

</details>

3. Compute an mgu of $f(g(x_1), x_2, h(x_2))$ and $f(x_3, k(x_3), h(k(g(a))))$.

<details><summary>Solution</summary>

```
Decompose    g(x1) = x3,  x2 = k(x3),  h(x2) = h(k(g(a)))
Orient       x3 = g(x1),  x2 = k(x3),  h(x2) = h(k(g(a)))
Eliminate x3 x3 = g(x1),  x2 = k(g(x1)),  h(x2) = h(k(g(a)))
Eliminate x2 x3 = g(x1),  x2 = k(g(x1)),  h(k(g(x1))) = h(k(g(a)))
Decompose    x3 = g(x1),  x2 = k(g(x1)),  k(g(x1)) = k(g(a))
Decompose    x3 = g(x1),  x2 = k(g(x1)),  g(x1) = g(a)
Decompose    x3 = g(x1),  x2 = k(g(x1)),  x1 = a
Eliminate x1 x3 = g(a),  x2 = k(g(a)),  x1 = a
```

The mgu is $\{x_1 \mapsto a, x_2 \mapsto k(g(a)), x_3 \mapsto g(a)\}$, and both terms become $f(g(a), k(g(a)), h(k(g(a))))$.

</details>

4. Compute an mgu of $f(g(x_1, a), x_2)$ and $f(x_2, g(b, x_3))$.

<details><summary>Solution</summary>

```
Decompose    g(x1, a) = x2,  x2 = g(b, x3)
Orient       x2 = g(x1, a),  x2 = g(b, x3)
Eliminate x2 x2 = g(x1, a),  g(x1, a) = g(b, x3)
Decompose    x2 = g(x1, a),  x1 = b,  a = x3
Eliminate x1 x2 = g(b, a),  x1 = b,  a = x3
Orient       x2 = g(b, a),  x1 = b,  x3 = a
```

The mgu is $\{x_1 \mapsto b, x_2 \mapsto g(b, a), x_3 \mapsto a\}$. Both terms become $f(g(b, a), g(b, a))$.

</details>

5. Decide whether $q(x_1, x_2, g(x_1, x_2))$ and $q(f(x_3), f(x_4), g(x_4, f(a)))$ unify. Then do the same for $f(x_1, g(x_2), x_2)$ and $f(a, x_3, h(x_3))$.

<details><summary>Solution</summary>

First pair:

```
Decompose    x1 = f(x3),  x2 = f(x4),  g(x1, x2) = g(x4, f(a))
Eliminate x1 x1 = f(x3),  x2 = f(x4),  g(f(x3), x2) = g(x4, f(a))
Eliminate x2 x1 = f(x3),  x2 = f(x4),  g(f(x3), f(x4)) = g(x4, f(a))
Decompose    x1 = f(x3),  x2 = f(x4),  f(x3) = x4,  f(x4) = f(a)
Orient       x1 = f(x3),  x2 = f(x4),  x4 = f(x3),  f(x4) = f(a)
Eliminate x4 x1 = f(x3),  x2 = f(f(x3)),  x4 = f(x3),  f(f(x3)) = f(a)
Decompose    x1 = f(x3),  x2 = f(f(x3)),  x4 = f(x3),  f(x3) = a
Clash on f(x3) = a: failure
```

Second pair:

```
Decompose    x1 = a,  g(x2) = x3,  x2 = h(x3)
Orient       x1 = a,  x3 = g(x2),  x2 = h(x3)
Eliminate x3 x1 = a,  x3 = g(x2),  x2 = h(g(x2))
Occurs check on x2 = h(g(x2)): failure
```

Neither pair unifies.

</details>

6. Compute an mgu of $f(x_1, x_2, x_3)$ and $f(x_2, x_3, x_1)$, and give the common instance.

<details><summary>Solution</summary>

```
Decompose    x1 = x2,  x2 = x3,  x3 = x1
Eliminate x1 x1 = x2,  x2 = x3,  x3 = x2
Eliminate x2 x1 = x3,  x2 = x3,  x3 = x3
Delete       x1 = x3,  x2 = x3
```

The mgu is $\{x_1 \mapsto x_3, x_2 \mapsto x_3\}$ and the common instance is $f(x_3, x_3, x_3)$.

</details>

7. Show that $\{x_1 \mapsto a, x_2 \mapsto a\}$ is a unifier of $f(x_1, x_2)$ and $f(x_2, x_1)$ but not an mgu. Then decide whether $f(x_1, x_1)$ matches onto $f(a, b)$, whether $f(x_1, a)$ matches onto $f(x_2, a)$, and whether $f(a)$ matches onto $x_1$.

<details><summary>Solution</summary>

Both terms become $f(a, a)$, so the substitution is a unifier. The substitution $\sigma = \{x_1 \mapsto x_2\}$ is also a unifier, and $\{x_1 \mapsto a, x_2 \mapsto a\} = \sigma\{x_2 \mapsto a\}$. The reverse is impossible, because no substitution maps $a$ back to a variable. So the given unifier is not an mgu.

$f(x_1, x_1)$ does not match onto $f(a, b)$, because $x_1$ would need two values. $f(x_1, a)$ matches onto $f(x_2, a)$ with $\{x_1 \mapsto x_2\}$. $f(a)$ does not match onto $x_1$, because a non-variable pattern cannot match a variable.

</details>

8. Show that the mgu returned by the algorithm has the property $\theta = \sigma\theta$ for every unifier $\theta$, and show by example that an arbitrary mgu need not have this property.

<details><summary>Solution</summary>

The first part is Lemma 4. For the second part, let $E = \{x_1 = x_1\}$, whose unifiers are all substitutions. Let $\sigma = \{x_1 \mapsto x_2, x_2 \mapsto x_1\}$. Every $\theta$ can be written as $\sigma(\sigma\theta)$, because $\sigma\sigma$ is the identity, so $\sigma$ is an mgu. Taking $\theta$ as the identity gives $\sigma\theta = \sigma \neq \theta$.

</details>

9. Prove that $\sigma$ is idempotent if and only if no variable of $\mathrm{dom}(\sigma)$ occurs in $x\sigma$ for any $x \in \mathrm{dom}(\sigma)$.

<details><summary>Solution</summary>

Suppose the condition holds. For $x \in \mathrm{dom}(\sigma)$, the term $x\sigma$ has no variable in the domain of $\sigma$, so $x\sigma\sigma = x\sigma$. For $x \notin \mathrm{dom}(\sigma)$, $x\sigma\sigma = x\sigma = x$. Hence $\sigma\sigma = \sigma$.

Conversely, suppose $\sigma\sigma = \sigma$ and that $y \in \mathrm{dom}(\sigma)$ occurs in $x\sigma$ at position $p$. Then $(x\sigma\sigma)|_p = y\sigma$. Since $x\sigma\sigma = x\sigma$, we also have $(x\sigma\sigma)|_p = (x\sigma)|_p = y$. So $y\sigma = y$, which contradicts $y \in \mathrm{dom}(\sigma)$.

</details>

10. Prove the uniqueness theorem for mgus.

<details><summary>Solution</summary>

Since $\sigma$ is an mgu and $\tau$ is a unifier, $\tau = \sigma\rho$ for some $\rho$. Likewise $\sigma = \tau\rho'$ for some $\rho'$. So $\sigma = \sigma\rho\rho'$, which means that for every variable $x$ we have $(x\sigma)\rho\rho' = x\sigma$.

Let $V$ be the set of variables occurring in terms $x\sigma$, and let $y \in V$. The equation above implies $y\rho\rho' = y$. If $y\rho$ were not a variable, then $y\rho\rho'$ would not be a variable either, so $y\rho$ is a variable. If $y_1\rho = y_2\rho$ for $y_1, y_2 \in V$, then applying $\rho'$ gives $y_1 = y_2$. Therefore $\rho$ restricted to $V$ is an injective map from $V$ into the variables. So $\tau$ is $\sigma$ followed by an injective renaming of the variables in its range.

</details>

11. Explain why Eliminate requires that $x$ occurs in $E$, and show that the measure in Lemma 3 would fail without this condition.

<details><summary>Solution</summary>

Without the condition, Eliminate applies to the equation $x_1 = a$ alone, leaves the problem unchanged and can repeat forever. The proof that $n_1$ decreases uses the fact that $x$ occurred at least twice before the step and was therefore unsolved. When $x$ occurs only in $x = t$, it is already solved, and the step changes no component of the measure.

</details>

12. For the family in the complexity section, prove that the mgu binds $x_k$ to a tree with $2^{k+1} - 1$ nodes. Then state what a graph representation stores for this mgu, and what a proof about the algorithm has to add so that union-find gives a correct answer.

<details><summary>Solution</summary>

By induction on $k$, the binding of $x_k$ is obtained by replacing $x_{k-1}$ by its binding in $f(x_{k-1}, x_{k-1})$. Let $s_k$ be the tree size of the binding, with $s_0 = 1$ for the variable $x_0$. Then $s_k = 2 s_{k-1} + 1$, and $s_k = 2^{k+1} - 1$ satisfies this recurrence.

A graph stores one $f$ node per level, with both children pointing to the node of the previous level, so its size is linear in $n$.

Union-find alone computes the finest congruence-like partition that the equations force. Two further facts complete the proof. A class that contains two different root symbols or arities shows failure, which `close` detects. A cycle in the class graph shows that some variable must equal a term properly containing itself, so the Occurs check argument gives failure. If there is no clash and no cycle, reading representatives in topological order yields an idempotent mgu.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define substitution, composition, unifier, more general and mgu.
- Run the rule-based algorithm on an unseen pair of terms and detect clash and occurs-check failures.
- Prove preservation, termination with the measure $(n_1, n_2, n_3)$ and the mgu property of solved forms.
- Compute a match and explain why demodulation uses matching.
- Explain the exponential family, and describe how a graph with union-find avoids the blow-up.

## Materials

- Robinson, A Machine-Oriented Logic Based on the Resolution Principle, JACM 1965. Read it for the original unification algorithm and for the way the mgu lets a single inference stand for many ground instances.
- Baader and Nipkow, Term Rewriting and All That. Read its treatment of syntactic unification for the rule-based algorithm, the correctness proof and the almost-linear graph algorithm.
- Baader and Snyder, Unification Theory, in Handbook of Automated Reasoning, 2001. Read it for a survey of efficient algorithms and of unification modulo theories.
- Martelli and Montanari, An Efficient Unification Algorithm, ACM TOPLAS 1982. Read it for the rule-based style and an efficient implementation.
- Paterson and Wegman, Linear Unification, Journal of Computer and System Sciences 1978. Read it for the linear-time result.
