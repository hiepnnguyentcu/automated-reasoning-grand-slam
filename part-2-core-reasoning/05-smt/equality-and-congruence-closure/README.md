# Equality and Congruence Closure

Part 2, Chapter 5: SMT.

## Objective

Decide equality with uninterpreted functions by hand using congruence closure.

## Why this matters

Uninterpreted functions are the basic abstraction tool of verification. You replace a multiplier, a hash or a whole subroutine with an unconstrained function, and you keep only the fact that equal inputs give equal outputs. The congruence closure data structure, usually called the E-graph, is also the hub of industrial solvers: Z3 describes its core as a SAT and EUF blackboard to which other theories attach, and the E-matching of [Quantifiers](../quantifiers/) searches this structure. You will implement it in [E-Graph and EUF](../../../part-3-building-the-engines/10-smt-solver/e-graph-and-euf/).

## Prerequisites

- [DPLL(T)](../dpllt/), for the interface that a theory solver must provide.
- [First-Order Theories](../../../part-1-foundations/01-mathematical-logic/first-order-theories/), for the axioms of equality.

## Lesson

### The theory

The theory of equality with uninterpreted functions, EUF, has a signature of arbitrary function and constant symbols and the equality predicate. Its axioms are those of a congruence relation:

$$
\begin{aligned}
&\forall x.\ x = x && \text{(reflexivity)} \\
&\forall x, y.\ x = y \to y = x && \text{(symmetry)} \\
&\forall x, y, z.\ x = y \land y = z \to x = z && \text{(transitivity)} \\
&\forall \vec{x}, \vec{y}.\ \textstyle\bigwedge_i x_i = y_i \to f(\vec{x}) = f(\vec{y}) && \text{(congruence, for each } f\text{)}
\end{aligned}
$$

Every first-order structure satisfies these axioms, because $=$ is interpreted as identity. So $T$-satisfiability in EUF is plain first-order satisfiability of a ground formula with equality. A predicate $P(\vec{t})$ can be encoded with a fresh sort-compatible constant $\mathit{tt}$ and a function $f_P$ by the atom $f_P(\vec{t}) = \mathit{tt}$, so we consider only functions.

The word uninterpreted means that $f$ can be any function. Thus if $F$ is unsatisfiable when $f$ is uninterpreted, then it remains unsatisfiable under any intended meaning for $f$. The converse fails, and this is what makes uninterpreted functions an over-approximation. For example, $x \cdot y \ne y \cdot x$ is satisfiable when multiplication is abstracted by an uninterpreted $f$, and false in arithmetic.

The theory solver needs to decide conjunctions of literals, which have the form $E \cup D$ where $E$ is a set of equalities and $D$ is a set of disequalities. We assume ground terms, that is, constants and variables are treated alike as nullary symbols.

### Congruence closure

Let $S$ be the set of all subterms of the terms occurring in $E \cup D$. A relation $\sim$ on $S$ is a congruence on $S$ if it is an equivalence relation, and whenever $f(s_1, \dots, s_n)$ and $f(t_1, \dots, t_n)$ are in $S$ with $s_i \sim t_i$ for each $i$, then $f(\vec{s}) \sim f(\vec{t})$. The congruence closure of $E$ on $S$ is the smallest congruence on $S$ that contains $E$. It exists because the intersection of congruences is a congruence, and the full relation $S \times S$ is one.

Theorem. Let $\sim$ be the congruence closure of $E$ on $S$. Then $E \cup D$ is satisfiable if and only if $s \not\sim t$ for every disequality $s \ne t$ in $D$.

Proof. Suppose $s \sim t$ for some $s \ne t$ in $D$. By induction on the construction of $\sim$, every related pair is provably equal from $E$ with the congruence axioms, so $E \models s = t$, and $E \cup D$ is unsatisfiable.

Conversely, suppose no disequality is violated. Build a structure $\mathcal{A}$. Its domain is the set of equivalence classes $[t]$ for $t \in S$, together with one extra element $\ast$. A domain must be non-empty, and adding $\ast$ handles this when $S$ is empty. Interpret each symbol $f$ by

$$
f^{\mathcal{A}}(c_1, \dots, c_n) =
\begin{cases}
[f(t_1, \dots, t_n)] & \text{if } f(t_1, \dots, t_n) \in S \text{ and } [t_i] = c_i \text{ for all } i, \\
\ast & \text{otherwise.}
\end{cases}
$$

This definition is unambiguous: if two terms $f(\vec{t})$ and $f(\vec{t}')$ in $S$ have arguments in the same classes, the closure property of $\sim$ gives $f(\vec{t}) \sim f(\vec{t}')$. By induction on terms, each $t \in S$ evaluates to $[t]$, since $S$ is subterm-closed. So each equality in $E$ holds, because its sides are related, and each disequality in $D$ holds, because its sides are in different classes. $\square$

The proof gives the model that a solver reports. It also shows why only subterms of the input are needed. New terms cannot create new consequences among old terms, because the model above exists with $S$ alone.

### The algorithm

The naive algorithm starts with singleton classes, merges the pairs in $E$, and repeatedly looks for two terms with the same function symbol and pairwise congruent arguments. It runs in polynomial time and is suitable for a hand trace.

```
congruence_closure(E, D):
    S := all subterms of E and D
    make each term of S its own class
    for each equality s = t in E:
        merge(s, t)
    if some s != t in D has find(s) = find(t): return unsat
    return sat

merge(s, t):
    if find(s) = find(t): return
    let P_s := terms of S having an argument in the class of s
    let P_t := terms of S having an argument in the class of t
    union the classes of s and t
    for each p in P_s and q in P_t:
        if p and q have the same symbol, and their arguments are pairwise in the same class:
            merge(p, q)
```

An efficient implementation uses three structures.

| Structure | Purpose |
|---|---|
| Union-find | It maps each term to a class representative. |
| Use lists | They store, for each class, the terms that have a member of the class as an argument. |
| Signature table | It maps $f(\mathrm{find}(t_1), \dots, \mathrm{find}(t_n))$ to a term with that signature. |

When two classes merge, the terms in the use list of the smaller class get new signatures. Each one either collides in the table, which gives a new merge, or is inserted. Always relabelling the smaller class means each term is relabelled $O(\log n)$ times. This idea, due to Downey, Sethi and Tarjan, gives $O(n \log n)$ expected time with a hash table. Nelson and Oppen, and Shostak, gave the earlier polynomial algorithms.

The conjunctive problem is thus polynomial, whereas EUF with Boolean structure is NP-complete, because it contains SAT.

### Flattening and currying

The Nieuwenhuis and Oliveras algorithm keeps the input simple. Introduce a fresh constant for each compound term, so that all equalities have the form $a = b$ or $f(a_1, \dots, a_n) = a$, with constants $a_i, a$. Further, by currying with one binary function symbol $\cdot$, the term $f(a, b)$ becomes $(f \cdot a) \cdot b$, and all equations are $a = b$ or $a_1 \cdot a_2 = a$. Then the signature table is a map from pairs of representatives to equations, and there is no dependence on arity.

### Explanations with a proof forest

As a DPLL(T) theory solver, congruence closure must explain each conflict and propagation. The explanation of a derived equality $s = t$ must be a subset of the asserted equalities that entails it, and a small one if possible. The union-find structure loses this information, because its links exist for speed and may be compressed. So Nieuwenhuis and Oliveras add a second structure, the proof forest.

The proof forest has one tree for each class, and the nodes of the tree are the members of the class. Each edge carries its justification: either an input equality, or a pair of equations $f(a_1, a_2) = a$, $f(b_1, b_2) = b$ when the edge records a congruence step.

To merge classes through a new edge between $x$ and $y$, take the tree with fewer nodes, reverse all edges on the path from $x$ to its root so that $x$ becomes the root, and add the edge from $x$ to $y$. The reversal touches each node $O(\log n)$ times in total, for the usual smaller-into-larger reason.

```
explain(s, t):
    pending := { (s, t) }
    result := {}
    while pending is not empty:
        take (a, b) from pending
        c := nearest common ancestor of a and b in the proof forest
        for each edge on the paths from a to c and from b to c:
            if its label is an input equation e:
                add e to result
            else its label is the pair of equations for f(a1, a2) = u and f(b1, b2) = v:
                add both equations to result
                add (a1, b1) and (a2, b2) to pending
    return result
```

To avoid visiting the same edge twice, the paper's implementation merges the visited edges in a second union-find structure. An explanation produced this way is often much smaller than the set of all equalities in the class, but it is not guaranteed to be minimal in cardinality. Finding a smallest explanation is known to be hard, so implementations settle for short ones.

### Disequalities and theory propagation

Store each asserted disequality at its two classes. When classes merge, check whether a stored disequality becomes violated. The conflict explanation is then the explanation of $s = t$ together with $s \ne t$ itself.

Theory propagation is natural here. After a merge, any atom $u = v$ in the formula with $u$ and $v$ now in one class is propagated true. Any atom whose sides are separated by an asserted disequality between their classes can be propagated false. Solvers commonly propagate the first kind eagerly and the second kind only in simple cases.

### Backtracking

The union-find must undo merges. If path compression is used, undoing becomes expensive, so backtrackable implementations use union by size alone, which keeps `find` at $O(\log n)$, and record each union, signature change and use-list change on a trail. On backtracking, these are undone in reverse order. This trade is the reason SMT solvers do not use the textbook near-constant-time union-find.

### Ackermann's reduction

An alternative to the theory solver removes all function symbols. For each pair of occurrences $f(s)$ and $f(t)$, replace them with fresh constants $v_s$ and $v_t$, and add the constraint $s = t \to v_s = v_t$, with the arguments themselves rewritten in the same way. The result is equisatisfiable and lies in equality logic. It has quadratically many constraints. A further reduction encodes equality logic to SAT through small-domain or per-constraint encodings. Solvers such as bit-vector solvers use this step, called Ackermannization, to eliminate uninterpreted functions before bit-blasting.

### Convexity of EUF

A theory is convex if whenever a set of literals entails a disjunction of equalities, it entails one of them. Theorem. EUF is convex. The canonical structure above is the reason: it makes exactly the equalities in the closure true, so if none of the disjuncts is in the closure, then the canonical model falsifies all of them. Exercise 9 asks you to write this out. Convexity matters for [Theory Combination](../theory-combination/).

## Worked examples

### Worked example 1: a classic refutation

Decide

$$
f^3(a) = a \land f^5(a) = a \land f(a) \ne a.
$$

Let $t_i$ denote $f^i(a)$, so $t_0 = a$. The set of subterms is $\{t_0, t_1, t_2, t_3, t_4, t_5\}$, and each has the term $f(t_i) = t_{i+1}$ as its parent, for $i \le 4$. Run the naive algorithm.

```
step  action                               classes
0     initial                              {t0} {t1} {t2} {t3} {t4} {t5}
1     merge t3, t0 (input)                 {t0,t3} {t1} {t2} {t4} {t5}
2     f(t0)=t1 and f(t3)=t4 have           {t0,t3} {t1,t4} {t2} {t5}
      congruent arguments: merge t1, t4
3     f(t1)=t2 and f(t4)=t5 have           {t0,t3} {t1,t4} {t2,t5}
      congruent arguments: merge t2, t5
4     merge t5, t0 (input)                 {t0,t2,t3,t5} {t1,t4}
5     f(t2)=t3 and f(t0)=t1 have           {t0,t1,t2,t3,t4,t5}
      congruent arguments: merge t3, t1
```

All terms now lie in one class, so $t_1 \sim t_0$. This violates $f(a) \ne a$, and the verdict is unsat, confirmed by Z3.

### Worked example 2: a satisfiable set and its model

Decide $a = b \land f(a) = c \land f(b) \ne d$.

The subterm set is $S = \{a, b, c, d, f(a), f(b)\}$. Merging $a$ and $b$ makes $f(a)$ and $f(b)$ congruent, so they merge. Merging $f(a)$ with $c$ gives the following classes.

$$
\{a, b\}, \quad \{c, f(a), f(b)\}, \quad \{d\}.
$$

The disequality $f(b) \ne d$ has its sides in different classes, so the verdict is sat.

Now build the model from the proof of the theorem. The domain is $\{A, C, D, \ast\}$, where $A = [a]$, $C = [c]$ and $D = [d]$. Set $a = b = A$, $c = C$, $d = D$. Set $f(A) = C$, since $f(a) \in S$ has its argument in class $A$. Set $f(C) = f(D) = f(\ast) = \ast$, since no term of $S$ applies $f$ to those classes. In this structure $f(a) = C = c$, and $f(b) = C \ne D = d$, so all literals hold. Z3 also reports sat.

### Worked example 3: an explanation with the proof forest

Assert the following equalities in this order, and treat the disequality $h_1 \ne h_2$ as asserted as well.

```
(1) f(a) = d      (2) f(c) = e      (3) g(d) = h1      (4) g(e) = h2
(5) a = b         (6) p = q         (7) b = c
```

Equations (1) to (4) only fill the signature table, with keys $f(a)$, $f(c)$, $g(d)$ and $g(e)$, because no two of them have matching signatures.

Equation (5) merges $a$ and $b$. The proof forest gets the edge $a \to b$ labelled (5). The signature of $f(a)$ becomes $f(b)$ if $b$ is the representative, and there is no collision. Equation (6) adds the edge $p \to q$ labelled (6).

Equation (7) merges $\{a, b\}$ and $\{c\}$. The smaller tree is $\{c\}$, so the edge $c \to b$ labelled (7) is added. Now $f(a)$ and $f(c)$ have the same signature, which is a collision, and so $d$ and $e$ must merge. The forest gets the edge $d \to e$ with the congruence label (1, 2). Then $g(d)$ and $g(e)$ collide, and the forest gets the edge $h_1 \to h_2$ with the congruence label (3, 4). The disequality $h_1 \ne h_2$ is now violated.

The forest at the point of conflict is shown below.

```
a --(5)--> b <--(7)-- c        p --(6)--> q
d --(1,2)--> e
h1 --(3,4)--> h2
```

Now compute $\mathrm{explain}(h_1, h_2)$.

```
pending          edge used           added to result     new pending
(h1, h2)         h1 -> h2, (3,4)     (3), (4)            (d, e)
(d, e)           d -> e, (1,2)       (1), (2)            (a, c)
(a, c)           a -> b, (5)         (5)                 none
                 c -> b, (7)         (7)                 none
```

The result is $\{(1), (2), (3), (4), (5), (7)\}$, and (6) is correctly absent. The conflict clause contains the negations of these six equalities and of $h_1 \ne h_2$. A check with Z3 shows that the seven literals are unsatisfiable, and that removing any one of them makes the set satisfiable, so this explanation is minimal.

## Common mistakes

- Computing the closure over all terms rather than over the subterms of the input. The closure on $S$ is finite and it is sufficient, as the theorem shows, so there is no need to generate further terms such as $f(f(a))$ if they do not occur.
- Forgetting to re-examine parents after a merge. A hand trace often misses a congruence caused by a merge of two argument classes, particularly the chain reaction in Worked example 1.
- Concluding from $f(a) = f(b)$ that $a = b$. Functions are not injective in EUF, so this inference is unsound.
- Assuming that a sat verdict for abstracted functions implies a real counterexample. If the concrete function has properties beyond congruence, then the model may be spurious.
- Using the union-find links as the explanation. Union-find links do not correspond to asserted equalities, and only the proof forest records justifications.
- Explaining a congruence edge without its argument equalities. A label $f(a_1) = u, f(b_1) = v$ needs the recursive explanation of $a_1 = b_1$, or the explanation is not sufficient to entail the result.
- Using path compression with cheap backtracking in mind. Compression changes many links, and each has to be recorded for undoing, which destroys the advantage.
- Believing that disequalities could be checked only once at the end. In DPLL(T) they must be checked after each merge to obtain early pruning.

## Exercises

1. State the four axiom schemes of EUF, and give the difference between the congruence closure on $S$ and the deductive closure of $E$ over all terms.

<details><summary>Solution</summary>

The schemes are reflexivity, symmetry, transitivity and congruence for each function symbol, as stated in the Lesson.

The deductive closure contains every equation between any two terms of the signature that follows from $E$, an infinite set in general. For example, from $a = b$ it contains $f^n(a) = f^n(b)$ for all $n$. The congruence closure on $S$ is the restriction of that relation to the finite set $S$. By the theorem of the Lesson, the restriction is sufficient for deciding the literals, whose terms are all in $S$.

</details>

2. Compute the congruence closure for $a = b$, $f(a) = g(b)$, $g(a) = c$ on its subterms, and decide whether $f(b) = c$ is entailed.

<details><summary>Solution</summary>

Take $S = \{a, b, c, f(a), f(b), g(a), g(b)\}$, which includes $f(b)$ because the question term must be represented.

Merge $a, b$. This makes $f(a) \sim f(b)$ and $g(a) \sim g(b)$. Merge $f(a), g(b)$. This gives the class $\{f(a), f(b), g(a), g(b)\}$. Merge $g(a), c$. This gives the class $\{f(a), f(b), g(a), g(b), c\}$. So $f(b) \sim c$, and the equality is entailed.

</details>

3. Trace the closure for the binary function $f$ on $f(a, b) = a \land f(f(a, b), b) \ne a$, and report the verdict.

<details><summary>Solution</summary>

Let $u = f(a, b)$ and $v = f(u, b)$. The subterms are $a, b, u, v$.

Merging $u$ with $a$ gives classes $\{a, u\}, \{b\}, \{v\}$. The terms $u = f(a, b)$ and $v = f(u, b)$ have arguments that are pairwise congruent, so $u$ and $v$ merge, giving $\{a, u, v\}$. The disequality $v \ne a$ is violated, so the verdict is unsat. This has been confirmed with Z3.

</details>

4. Decide $a = b \land f(a) \ne f(c)$, and if it is satisfiable, build the model from the construction in the theorem.

<details><summary>Solution</summary>

The subterms are $a, b, c, f(a), f(c)$. Merging $a$ and $b$ gives classes $\{a, b\}, \{c\}, \{f(a)\}, \{f(c)\}$. The disequality has its sides in separate classes, so the verdict is sat, confirmed with Z3.

The domain is $\{A, C, U, V, \ast\}$, with $A = [a]$, $C = [c]$, $U = [f(a)]$ and $V = [f(c)]$. Set $a = b = A$, $c = C$, $f(A) = U$, $f(C) = V$, $f(U) = f(V) = f(\ast) = \ast$. Then $f(a) = U \ne V = f(c)$.

</details>

5. Apply Ackermann's reduction to $x = y \land f(x) \ne f(y) \land g(f(x)) = z$, and decide the result.

<details><summary>Solution</summary>

Let $v_x$ replace $f(x)$ and $v_y$ replace $f(y)$. The function $g$ occurs only once, so the fresh constant $w$ replaces $g(f(x))$, with no constraint for $g$. The result is

$$
x = y \land v_x \ne v_y \land w = z \land (x = y \to v_x = v_y).
$$

The implication and $x = y$ give $v_x = v_y$, which contradicts $v_x \ne v_y$. So the formula is unsat, and so is the original.

</details>

6. Using the assertion order $a = b$, $b = c$, $f(a) = u$, $f(c) = v$, $f(v) = w$, $f(u) = z$, draw the proof forest, and give the explanation of $w = z$.

<details><summary>Solution</summary>

The first two equalities give the edges $a \to b$, labelled $a = b$, and $c \to b$, labelled $b = c$, if the smaller tree $\{c\}$ is joined to $\{a, b\}$.

Asserting $f(a) = u$ and $f(c) = v$ gives a collision, because the arguments are in one class. So $u$ and $v$ merge with the edge $u \to v$ labelled by the pair of equations $f(a) = u, f(c) = v$. Asserting $f(v) = w$ fills the table. Asserting $f(u) = z$ then gives a collision, because $u$ and $v$ are in one class. So $w$ and $z$ merge with an edge labelled by the pair $f(v) = w, f(u) = z$.

To explain $w = z$: the pair $f(v) = w, f(u) = z$ is added, and the pending pair is $(v, u)$. Its edge gives $f(a) = u, f(c) = v$, and the pending pair is $(a, c)$. The path through $b$ gives $a = b$ and $b = c$. So all six equations are in the explanation, each of which is needed.

</details>

7. Prove that if $\gcd(m, n) = 1$ with $m, n \ge 1$, then $f^m(a) = a \land f^n(a) = a \models f(a) = a$.

<details><summary>Solution</summary>

First, $f^m(a) = a$ gives $f^{km}(a) = a$ for all $k \ge 0$, by induction: $f^{(k+1)m}(a) = f^{km}(f^m(a)) = f^{km}(a) = a$, where the middle step uses congruence applied $km$ times. In the same way $f^{ln}(a) = a$ for all $l \ge 0$.

Since $\gcd(m, n) = 1$, there are $k, l \ge 0$ with $km = ln + 1$. To see this, $n$ is invertible modulo $m$, so one can choose $l \ge 0$ with $ln \equiv -1 \pmod m$. Then

$$
a = f^{km}(a) = f^{ln + 1}(a) = f(f^{ln}(a)) = f(a).
$$

The last step uses congruence on $f^{ln}(a) = a$. $\square$

Worked example 1 is the case $m = 3, n = 5$.

</details>

8. Show that the encoding of predicates by $f_P(\vec{t}) = \mathit{tt}$ is correct. That is, a set of literals with predicate $P$ is satisfiable if and only if its encoding is satisfiable.

<details><summary>Solution</summary>

From a model of the original set with interpretation $P^{\mathcal{A}}$, extend the domain by adding two new elements, $e_1$ and $e_0$, unless the domain already has two usable elements. Interpret $\mathit{tt}$ as $e_1$, and $f_P(\vec{v})$ as $e_1$ if $\vec{v} \in P^{\mathcal{A}}$ and $e_0$ otherwise. Extend other functions arbitrarily to the new elements. Then each literal $P(\vec{t})$ becomes $f_P(\vec{t}) = \mathit{tt}$ with the same truth value.

From a model of the encoding, define $P^{\mathcal{A}} = \{\vec{v} : f_P(\vec{v}) = \mathit{tt}\}$. Then the original literals have the same truth values as their encodings.

In many-sorted solvers, the two values belong to a separate Boolean sort, so the extension of the domain is not necessary.

</details>

9. Prove that EUF is convex. Then show that the corresponding statement fails for a disjunction of disequalities.

<details><summary>Solution</summary>

Let $\Gamma = E \cup D$ be satisfiable, and suppose $\Gamma \models s_1 = t_1 \lor \dots \lor s_k = t_k$. Add all these terms and their subterms to $S$, and let $\sim$ be the congruence closure of $E$ on $S$. Suppose, for contradiction, that $s_i \not\sim t_i$ for each $i$. By the theorem, the canonical structure satisfies $\Gamma$, and it assigns different classes to $s_i$ and $t_i$, so it falsifies the disjunction. This contradicts the entailment. So $s_i \sim t_i$ for some $i$, and then $E \models s_i = t_i$.

For disequalities, take $\Gamma = \{a \ne b\}$. It entails $c \ne a \lor c \ne b$, since $c$ cannot equal both. But $\Gamma$ entails neither $c \ne a$ nor $c \ne b$. So the analogous statement fails for disequalities.

</details>

10. Design the undo mechanism for a backtrackable congruence closure with proof forest. List what must be recorded on the trail for one merge, and argue that restoration is correct.

<details><summary>Solution</summary>

For a merge of the smaller class $c_1$ into the larger class $c_2$, record the following items:

- The pair of old representatives, and the old size of $c_2$. Without path compression, only the link of the root of $c_1$ and the size of $c_2$ change in the union-find.
- The nodes whose use lists were changed. With a linked representation, concatenating the use list of $c_1$ to that of $c_2$ can be undone by restoring a tail pointer, so a constant number of words suffices.
- Each signature table entry that was inserted or changed during the merge, with the old value.
- The proof forest path that was reversed, identified by the node where the reversal started, and the edge added.
- Any disequality records moved between classes.

On backtracking, process these in reverse. Each action is the inverse of one forward action, and the entries are restored in reverse order, so by induction on the length of the trail, the state after undoing is identical to the state before the corresponding forward action. Thus the invariants of the structure hold again without recomputation. Pending, unprocessed merges are discarded.

Reversing the proof forest path is its own inverse: removing the added edge and re-reversing the same path restores the earlier orientation.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Define the congruence closure on a set of terms, and prove the decision theorem, including the construction of the model.
- Trace the naive algorithm on an unseen conjunction, and give all merges, including those caused by congruence.
- Build a proof forest for a sequence of assertions, and compute an explanation with it.
- Give the reduction of Ackermann, and say when a solver would use it.
- Explain why backtrackable solvers avoid path compression.
- Prove that EUF is convex.

## Materials

- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the chapter on equality and uninterpreted functions for congruence closure, Ackermann's reduction and the role of uninterpreted functions in equivalence checking.
- Bradley and Manna, The Calculus of Computation. Read the material on quantifier-free equality for a careful statement of the DAG-based algorithm and its correctness.
- Nieuwenhuis and Oliveras, Proof-Producing Congruence Closure, RTA 2005. Read it for the flat curried form, the proof forest and explanation generation.
- Downey, Sethi and Tarjan, Variations on the Common Subexpression Problem, JACM 1980. Read it for the $O(n \log n)$ algorithm.
- Nelson and Oppen, Fast Decision Procedures Based on Congruence Closure, JACM 1980. Read it for the classical formulation and its link to list structures.
