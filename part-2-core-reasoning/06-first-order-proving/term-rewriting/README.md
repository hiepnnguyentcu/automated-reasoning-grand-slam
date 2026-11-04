# Term Rewriting

Part 2, Chapter 6: First-Order Proving.

## Objective

Prove termination and confluence of rewrite systems and run Knuth-Bendix completion by hand.

## Why this matters

Rewriting gives equations a direction, so that equational reasoning becomes computation. It supplies the three ideas that make equality tractable in provers: reduction orderings, critical pairs and completion. [Superposition](../superposition/) is completion lifted to clauses, and the demodulation performed by [saturation provers](../saturation-provers/) is rewriting. The same ideas appear in the simplifiers of [proof assistants](../../../part-4-remaining-methods/12-proof-assistants/) and of SMT solvers. An applied scientist who has to show that a set of simplification rules is safe, or who has to choose a term ordering for a prover, needs exactly the results below.

## Prerequisites

- [Unification](../unification/) for most general unifiers and matching.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for well-founded induction.
- [First-Order Theories](../../../part-1-foundations/01-mathematical-logic/first-order-theories/) for equational theories.

## Lesson

### Abstract reduction

An abstract reduction system is a set with a binary relation $\to$. Write $\to^*$ for its reflexive transitive closure, $\to^+$ for its transitive closure and $\leftrightarrow^*$ for its reflexive symmetric transitive closure. An element $x$ is a normal form if no $y$ has $x \to y$. Elements $y$ and $z$ are joinable, written $y \downarrow z$, if $y \to^* w$ and $z \to^* w$ for some $w$.

The relation is

- terminating if it has no infinite chain $x_0 \to x_1 \to \cdots$,
- confluent if $y \leftarrow^* x \to^* z$ implies $y \downarrow z$,
- locally confluent if $y \leftarrow x \to z$ implies $y \downarrow z$,
- Church-Rosser if $y \leftrightarrow^* z$ implies $y \downarrow z$,
- convergent if it is terminating and confluent.

Theorem. A relation is Church-Rosser if and only if it is confluent.

Proof. Church-Rosser clearly implies confluence, since $y \leftarrow^* x \to^* z$ gives $y \leftrightarrow^* z$. Conversely, induct on the length of the zig-zag from $y$ to $z$. The empty case is trivial. Suppose the last step is $z' \to z$. By induction there is $w$ with $y \to^* w$ and $z' \to^* w$. Confluence applied to $w \leftarrow^* z' \to z$ gives $w'$ with $w \to^* w'$ and $z \to^* w'$, so $y \to^* w'$ and $z \to^* w'$. Suppose instead the last step is $z \to z'$. Then $z \to z' \to^* w$, so $w$ is the join. $\square$

Theorem (Newman's lemma). A terminating relation is confluent if and only if it is locally confluent.

Proof. Confluence implies local confluence. For the other direction, $\to^+$ is well-founded, so use well-founded induction on $x$ with the claim that all $y, z$ with $y \leftarrow^* x \to^* z$ are joinable. If $x = y$ or $x = z$ the claim is immediate. Otherwise $x \to y_1 \to^* y$ and $x \to z_1 \to^* z$. Local confluence gives $u$ with $y_1 \to^* u$ and $z_1 \to^* u$. The induction hypothesis on $y_1$ gives $v$ with $y \to^* v$ and $u \to^* v$. The induction hypothesis on $z_1$, applied to $v \leftarrow^* z_1 \to^* z$, gives $w$ with $v \to^* w$ and $z \to^* w$. So $y \to^* w$ and $z \to^* w$. $\square$

Termination is essential. The relation with $b \to a$, $b \to c$, $c \to b$, $c \to d$ is locally confluent but not confluent, because $a$ and $d$ are distinct normal forms of $b$.

In a convergent system, every element has a unique normal form, written $\mathrm{nf}(x)$, and $y \leftrightarrow^* z$ holds if and only if $\mathrm{nf}(y) = \mathrm{nf}(z)$. This is the reason for wanting convergence: it turns an equational question into normalizing and comparing.

### Term rewriting systems

A rewrite rule is a pair $l \to r$ of terms where $l$ is not a variable and $\mathrm{Var}(r) \subseteq \mathrm{Var}(l)$. Both restrictions are needed for termination: a variable left side rewrites every term, and a new variable on the right allows arbitrary terms to appear. A term rewriting system (TRS) is a set $R$ of rules.

The term $s$ rewrites to $t$ with $R$, written $s \to_R t$, if there is a position $p$ in $s$, a rule $l \to r$ and a substitution $\sigma$ such that $s|_p = l\sigma$ and $t = s[r\sigma]_p$. The substitution is found by matching, and the position is called a redex.

For a set of equations $E$, write $s \leftrightarrow_E^* t$ for the equational closure, using equations in either direction.

Theorem (Birkhoff). $E \models s \approx t$ holds if and only if $s \leftrightarrow_E^* t$.

Proof sketch. The right-to-left direction is soundness of replacing equals by equals. For the other direction, let $\mathcal{T}$ be the quotient of the term algebra by $\leftrightarrow_E^*$. This is a congruence, so $\mathcal{T}$ is a well-defined algebra. Closure under substitution makes it a model of $E$. Evaluating $s$ and $t$ under the assignment sending each variable to its own class gives the classes of $s$ and $t$. So $E \models s \approx t$ forces them to be the same class. $\square$

So a finite convergent TRS $R$ with $\leftrightarrow_R^* = \leftrightarrow_E^*$ decides the word problem of $E$. No such system exists in general, since the word problem is undecidable for some finitely presented groups (Novikov, 1955, and Boone, 1958).

### Termination and reduction orderings

Termination of a finite TRS is undecidable (Huet and Lankford, 1978), so we use sufficient conditions.

A rewrite ordering is a strict partial order $\succ$ on terms that is

- closed under contexts: $s \succ t$ implies $u[s]_p \succ u[t]_p$,
- closed under substitutions: $s \succ t$ implies $s\sigma \succ t\sigma$.

A reduction ordering is a well-founded rewrite ordering.

Theorem. $R$ terminates if and only if $R$ is contained in a reduction ordering.

Proof. If $l \succ r$ for all rules, closure gives $s \succ t$ whenever $s \to_R t$, and well-foundedness rules out infinite chains. If $R$ terminates, then $\to_R^+$ is a reduction ordering containing $R$. $\square$

A simplification ordering is a rewrite ordering with the subterm property: $u[t]_p \succ t$ whenever $p$ is not the root. On a finite signature, simplification orderings are well-founded, by Dershowitz's theorem, which uses Kruskal's tree theorem. So proving a rule decreasing in a simplification ordering is enough. This is the class used in provers.

### Lexicographic path ordering

Fix a precedence, a strict partial order $>$ on function symbols. Then $s \succ_{\mathrm{lpo}} t$ holds if one of the following applies.

1. $t$ is a variable occurring in $s$, and $s \neq t$.
2. $s = f(s_1, \ldots, s_m)$, $t = g(t_1, \ldots, t_n)$ and one of these holds:
   - (a) $s_i \succeq_{\mathrm{lpo}} t$ for some $i$,
   - (b) $f > g$ and $s \succ_{\mathrm{lpo}} t_j$ for all $j$,
   - (c) $f = g$, $s \succ_{\mathrm{lpo}} t_j$ for all $j$, and for some $i$ we have $s_1 = t_1, \ldots, s_{i-1} = t_{i-1}$ and $s_i \succ_{\mathrm{lpo}} t_i$.

The ordering compares roots first. A larger root may copy its arguments and call smaller functions, which makes LPO a natural fit for recursive definitions. LPO is a simplification ordering, and it is total on ground terms if the precedence is total. Variables are incomparable with terms that do not contain them.

### Knuth-Bendix ordering

Assign a weight $w(f) \in \mathbb{N}$ to each symbol and fix $w_0 > 0$. Require $w(c) \geq w_0$ for constants, and require that if a unary $f$ has $w(f) = 0$, then $f$ is greatest in the precedence. These are the admissibility conditions. Extend by $w(x) = w_0$ for variables and $w(f(t_1, \ldots, t_n)) = w(f) + \sum_i w(t_i)$. Write $|t|_x$ for the number of occurrences of $x$ in $t$.

Then $s \succ_{\mathrm{kbo}} t$ holds if $|s|_x \geq |t|_x$ for every variable $x$, and one of these applies.

1. $w(s) > w(t)$.
2. $w(s) = w(t)$ and one of these holds:
   - (a) $s = f^k(x)$, $t = x$ for $k \geq 1$, where $f$ is unary with weight 0,
   - (b) $s = f(s_1, \ldots)$, $t = g(t_1, \ldots)$ with $f > g$,
   - (c) $s = f(s_1, \ldots, s_n)$, $t = f(t_1, \ldots, t_n)$, and at the first argument with $s_i \neq t_i$ we have $s_i \succ_{\mathrm{kbo}} t_i$.

The variable condition is what makes KBO stable: duplicating a variable can make the instantiated right side arbitrarily heavy. So KBO cannot orient $x_1 \cdot (x_2 + x_3) \to (x_1 \cdot x_2) + (x_1 \cdot x_3)$, which duplicates $x_1$. LPO can orient it when $\cdot$ is above $+$. KBO is cheap to compute and is a common choice in saturation provers, and Vampire uses it. Both orderings are decidable on individual pairs.

### Polynomial interpretations

Map each $n$-ary symbol $f$ to a polynomial $[f]$ with natural coefficients that is strictly increasing in every argument on a domain $\mathbb{N}_{\geq k}$. A term then evaluates to a polynomial in its variables. If $[l] > [r]$ on the whole domain for each rule, then $R$ terminates, since the values of successive terms form a strictly decreasing sequence of natural numbers.

For distributivity, take $[\cdot](a, b) = ab$ and $[+](a, b) = a + b + 1$ on $\mathbb{N}_{\geq 2}$. Then $[x_1 \cdot (x_2 + x_3)] = x_1 x_2 + x_1 x_3 + x_1$ and $[(x_1 \cdot x_2) + (x_1 \cdot x_3)] = x_1 x_2 + x_1 x_3 + 1$. Since $x_1 \geq 2$, the rule decreases.

### Beyond simplification orderings

The rule $f(f(x_1)) \to f(g(f(x_1)))$ is terminating. Its left side is embedded in its right side, because deleting $g$ from the right side gives the left. So no simplification ordering orients it. Termination follows from a direct argument: terms over $f$ and $g$ are strings, and each step reduces by one the number of adjacent $f f$ pairs. Modern termination tools use dependency pairs for such cases. The class of simplification orderings suffices for the rest of this chapter, because a saturation prover needs a total ordering on ground terms and does not need to orient every rule.

### Critical pairs and confluence

Rules can overlap. Let $l_1 \to r_1$ and $l_2 \to r_2$ be rules with disjoint variables, $p$ a non-variable position of $l_2$, and $\sigma = \mathrm{mgu}(l_1, l_2|_p)$. If $p$ is the root, require that the two rules are not variants of one rule. The term $l_2\sigma$ can rewrite in two ways, and the pair

$$
\langle\, l_2\sigma[r_1\sigma]_p,\; r_2\sigma \,\rangle
$$

is a critical pair of $R$. A finite TRS has finitely many critical pairs up to renaming.

Theorem (critical pair lemma). A TRS is locally confluent if and only if all of its critical pairs are joinable.

Proof sketch. The forward direction holds because a critical pair is a peak. For the reverse direction, take a peak $t_1 \leftarrow s \to t_2$ rewriting with rules $l_1 \to r_1$ at $p_1$ with $\sigma_1$ and $l_2 \to r_2$ at $p_2$ with $\sigma_2$.

Case 1, disjoint positions. Neither position is above the other. The two steps can be swapped, and $t_1$ and $t_2$ have a common successor by applying the other rule.

Case 2, variable overlap. Say $p_1 = p_2 q$ with $q = q_1 q_2$, where $l_2|_{q_1}$ is a variable $x$. The inner redex lies inside $x\sigma_2$. Rewriting every other occurrence of $x$ on the $t_1$ side, and all occurrences of $x$ on the $t_2$ side in $r_2\sigma_2$, gives a common term. No unification is involved.

Case 3, critical overlap. Say $p_1 = p_2 q$ with $q$ a non-variable position of $l_2$. Then $\sigma_1 \cup \sigma_2$ unifies $l_1$ and $l_2|_q$, so it is an instance of the mgu $\sigma$. The peak is an instance, inside a context, of the critical peak. Joinability of the critical pair is preserved by substitution and context. $\square$

Theorem (Knuth-Bendix). A terminating TRS is confluent if and only if all of its critical pairs are joinable. So confluence of a finite terminating TRS is decidable: compute every critical pair and compare normal forms.

Proof. Combine the critical pair lemma with Newman's lemma. $\square$

Without termination, joinable critical pairs are not sufficient. The system $f(x_1, x_1) \to a$, $f(x_1, g(x_1)) \to b$, $c \to g(c)$ has no critical pairs at all. Yet $f(c, c) \to a$ and $f(c, c) \to f(c, g(c)) \to b$, and $a$ and $b$ are different normal forms. For left-linear systems with no critical pairs, called orthogonal systems, confluence does hold without termination.

### Knuth-Bendix completion

Completion takes equations $E$ and a reduction ordering $\succ$, and tries to build a convergent system equivalent to $E$. Knuth and Bendix introduced it in 1970. The standard modern presentation, due to Bachmair, works on pairs $(E, R)$ with the rules below, where $R$ is always contained in $\succ$.

| Rule | From | To | Condition |
|---|---|---|---|
| Delete | $E \cup \{s = s\}, R$ | $E, R$ | It always applies. |
| Compose | $E, R \cup \{s \to t\}$ | $E, R \cup \{s \to u\}$ | It needs $t \to_R u$. |
| Simplify | $E \cup \{s = t\}, R$ | $E \cup \{u = t\}, R$ | It needs $s \to_R u$. |
| Orient | $E \cup \{s = t\}, R$ | $E, R \cup \{s \to t\}$ | It needs $s \succ t$. |
| Collapse | $E, R \cup \{s \to t\}$ | $E \cup \{u = t\}, R$ | It needs $s \to_R u$ using a rule $l \to r$ for which $s$ strictly encompasses $l$. |
| Deduce | $E, R$ | $E \cup \{s = t\}, R$ | It needs a critical pair $\langle s, t \rangle$ of $R$. |

Here $s$ strictly encompasses $l$ if a subterm of $s$ is an instance of $l$ and $l$ is not a variant of $s$. The condition blocks a rule from collapsing its own variant. Compose may use any rule in $R$, since the right side only decreases.

```
complete(E, order):
    R := empty
    loop:
        while E is not empty:
            take an equation s = t from E, usually the smallest
            normalize s and t with R
            if they are equal: delete the equation and continue
            if neither s > t nor t > s: fail
            orient it, add it to R
            collapse and compose existing rules with the new rule
        if some critical pair of R has not been processed:
            add it to E
        else:
            return R
```

A run has three possible outcomes.

- Success: $E$ is empty, all critical pairs are processed, and the final $R$ is convergent and equivalent to the input.
- Failure: an equation cannot be oriented, for example commutativity.
- Divergence: new rules appear forever. In the limit, the persisting rules form a possibly infinite convergent system, so the procedure still gives a semi-decision procedure for the word problem of $E$, as long as it does not fail.

Theorem (correctness of completion). Consider a fair, non-failing run $(E_0, \emptyset) \vdash (E_1, R_1) \vdash \cdots$, where fair means that every critical pair of persisting rules is eventually processed and that $E_\infty$ is empty. Then $R_\infty$, the set of persisting rules, is convergent, and $\leftrightarrow_{R_\infty}^* = \leftrightarrow_{E_0}^*$.

Proof sketch. Each rule keeps $\leftrightarrow_{E \cup R}^*$ unchanged. Termination of $R_\infty$ follows from $R_\infty \subseteq {\succ}$. For confluence, order equational proofs by a well-founded proof ordering, built from the multisets of terms they mention. Each completion step can only replace a proof by a smaller one. A proof that is not a rewrite proof contains a peak or an equation step, so if fairness has processed the corresponding critical pair, it can be replaced by a smaller proof at a later stage. Well-foundedness then says that every equation of the theory eventually has a rewrite proof in the limit. Rewrite proofs in the limit are exactly joinability, so the system is Church-Rosser. $\square$

The proof-ordering argument is the conceptual ancestor of redundancy in superposition. A simplification is safe because it replaces a proof by a smaller one.

For a fixed reduction ordering, if a finite convergent system equivalent to $E$ exists and is interreduced, then it is unique up to renaming. So the result of a successful run does not depend on the order of steps.

### Unfailing completion

Failure was a serious limitation. Unfailing completion, by Hsiang and Rusinowitch and by Bachmair, Dershowitz and Plaisted, allows unorientable equations to remain as equations. They are used for rewriting only in instances that the ordering decreases, called ordered rewriting. This requires an ordering total on ground terms, and critical pairs are computed from equations in both directions when instances may be decreasing.

Unfailing completion is refutationally complete for pure equational problems: to prove $E \models s \approx t$, add Skolem constants for the variables of the goal and complete until the two sides normalize to the same term. The extension of this idea to full clauses is [superposition](../superposition/).

## Worked examples

In traces, `x1` stands for $x_1$ and `·` for the group operation.

### Example 1: LPO proof of associativity

Use the precedence $i > \cdot > e$ and show $(x_1 \cdot x_2) \cdot x_3 \succ_{\mathrm{lpo}} x_1 \cdot (x_2 \cdot x_3)$. Let $s$ be the left side.

```
s > x1·(x2·x3)       same root, use (c)
  s > x1             x1 occurs in s, use 1
  s > x2·x3          same root, use (c)
    s > x2           x2 occurs in s, use 1
    s > x3           x3 occurs in s, use 1
    x1·x2 > x2       first arguments differ, x2 occurs in x1·x2, use 1
  x1·x2 > x1         first arguments differ, x1 occurs in x1·x2, use 1
```

The reverse is not provable. It would need $x_1 \succ x_1 \cdot x_2$ for the first arguments, or a subterm of $x_1 \cdot (x_2 \cdot x_3)$ being at least as large as $s$, and neither holds.

### Example 2: KBO proof of the inverse of a product

Use $i > \cdot > e$, with $w(i) = 0$, $w(\cdot) = w(e) = w_0 = 1$. Compare $s = i(x_1 \cdot x_2)$ with $t = i(x_2) \cdot i(x_1)$. Each side has one occurrence of $x_1$ and of $x_2$, so the variable condition holds. The weights are $w(s) = 0 + 1 + 1 + 1 = 3$ and $w(t) = 1 + 0 + 1 + 0 + 1 = 3$. Since $i > \cdot$, case 2(b) gives $s \succ_{\mathrm{kbo}} t$. The weight-zero unary symbol $i$ is greatest in the precedence, so the choice is admissible.

### Example 3: all critical pairs of associativity

Let $R = \{(x_1 \cdot x_2) \cdot x_3 \to x_1 \cdot (x_2 \cdot x_3)\}$. Overlap a renamed copy $(x_4 \cdot x_5) \cdot x_6 \to x_4 \cdot (x_5 \cdot x_6)$ into the left side at position 1, the subterm $x_1 \cdot x_2$. The mgu is $\{x_1 \mapsto x_4 \cdot x_5, x_2 \mapsto x_6\}$.

```
peak    ((x4·x5)·x6)·x3
inner   (x4·(x5·x6))·x3
outer   (x4·x5)·(x6·x3)
```

Both sides normalize to $x_4 \cdot (x_5 \cdot (x_6 \cdot x_3))$.

```
(x4·(x5·x6))·x3  →  x4·((x5·x6)·x3)  →  x4·(x5·(x6·x3))
(x4·x5)·(x6·x3)  →  x4·(x5·(x6·x3))
```

The root overlap with itself is excluded, and position 2 is a variable. So this is the only critical pair, it is joinable, and associativity alone is convergent.

### Example 4: a small completion

Complete $E = \{f(f(x_1)) = g(x_1)\}$ with LPO and $f > g$.

```
Orient     R1: f(f(x1)) → g(x1)
Deduce     overlap R1 into position 1 of R1
           peak f(f(f(x1)))
           inner f(g(x1))
           outer g(f(x1))
           both are normal forms, so add f(g(x1)) = g(f(x1))
Orient     R2: f(g(x1)) → g(f(x1))      since f > g and f(g(x1)) > f(x1)
Deduce     overlap R1 into position 1 of R2: no match, since g differs from f
Deduce     overlap R2 into position 1 of R1
           peak f(f(g(x1)))
           inner f(g(f(x1)))  →  g(f(f(x1)))  →  g(g(x1))
           outer g(g(x1))
           they are joinable
Deduce     overlaps of R2 with R2: none, since g(x1) and f(x1) have different roots
Stop       all critical pairs are joinable
```

The result is $\{f(f(x_1)) \to g(x_1),\ f(g(x_1)) \to g(f(x_1))\}$. To decide the word problem, take $f(f(f(a)))$ and $g(f(a))$. Normalizing the first gives $f(g(a))$ and then $g(f(a))$, so the two terms are equal in the theory.

### Example 5: completion of group theory

Complete the axioms $e \cdot x_1 = x_1$, $i(x_1) \cdot x_1 = e$, $(x_1 \cdot x_2) \cdot x_3 = x_1 \cdot (x_2 \cdot x_3)$ with LPO and $i > \cdot > e$. At each step take the smallest unprocessed critical pair. Pairs that normalize to the same term are dropped silently. The trace below lists each rule with the peak that produces it.

```
R1   e·x1 → x1                               input
R2   i(x1)·x1 → e                            input
R3   (x1·x2)·x3 → x1·(x2·x3)                 input

R4   i(x1)·(x1·x2) → x2
     R2 into R3 at position 1
     peak (i(x1)·x1)·x2, giving e·x2 and i(x1)·(x1·x2); e·x2 normalizes to x2

R5   i(e)·x1 → x1
     R1 into R4 at position 2
     peak i(e)·(e·x1), giving i(e)·x1 and x1

R6   i(i(x1))·e → x1
     R2 into R4 at position 2
     peak i(i(x1))·(i(x1)·x1), giving i(i(x1))·e and x1

R7   i(i(e))·x1 → x1
     R5 into R4 at position 2
     peak i(i(e))·(i(e)·x1), giving i(i(e))·x1 and x1

R8   i(e) → e
     R2 into R7 at the root
     peak i(i(e))·i(e), giving e and i(e)
     collapse R5: i(e)·x1 becomes e·x1, then x1 = x1, deleted
     collapse R7: i(i(e))·x1 becomes e·x1, then x1 = x1, deleted

R9   i(i(i(x1)))·x1 → e
     R6 into R4 at position 2
     peak i(i(i(x1)))·(i(i(x1))·e), giving i(i(i(x1)))·x1 and e

R10  i(i(x1))·x2 → x1·x2
     R4 into R4 at position 2
     peak i(i(x1))·(i(x1)·(x1·x2)), giving i(i(x1))·x2 and x1·x2
     collapse R6: i(i(x1))·e becomes x1·e, leaving the equation x1·e = x1
     collapse R9: i(i(i(x1)))·x1 becomes i(x1)·x1, then e = e, deleted

R11  x1·e → x1
     orient the equation left by collapsing R6

R12  x1·i(x1) → e
     R2 into R10 at the root
     peak i(i(x1))·i(x1), giving e and x1·i(x1)

R13  i(i(x1)) → x1
     R10 into R11 at the root
     peak i(i(x1))·e, giving x1·e, which is x1, and i(i(x1))
     collapse R10: i(i(x1))·x2 becomes x1·x2, equal to its right side, deleted

R14  x1·(i(x1)·x2) → x2
     R13 into R4 at position 1
     peak i(i(x1))·(i(x1)·x2), giving x1·(i(x1)·x2) and x2

R15  x1·(x2·i(x1·x2)) → e
     R3 into R12 at the root
     peak (x1·x2)·i(x1·x2), giving x1·(x2·i(x1·x2)) and e

R16  x1·i(x2·x1) → i(x2)
     R15 into R4 at position 2
     peak i(x2)·(x2·(x1·i(x2·x1))), giving i(x2)·e, which is i(x2), and x1·i(x2·x1)
     collapse R15: x1·(x2·i(x1·x2)) becomes x1·i(x1), then e = e, deleted

R17  i(x1·x2) → i(x2)·i(x1)
     R16 into R4 at position 2
     peak i(x2)·(x2·i(x1·x2)), giving i(x2)·i(x1) and i(x1·x2)
     collapse R16: x1·i(x2·x1) becomes x1·(i(x1)·i(x2)), then i(x2) = i(x2), deleted
```

The persisting rules are the classic ten.

```
e·x1 → x1                         x1·e → x1
i(x1)·x1 → e                      x1·i(x1) → e
(x1·x2)·x3 → x1·(x2·x3)           i(e) → e
i(x1)·(x1·x2) → x2                i(i(x1)) → x1
x1·(i(x1)·x2) → x2                i(x1·x2) → i(x2)·i(x1)
```

A short script computed the critical pairs of this final system. There are 55 pairs when counted by ordered rule pair and position, and every pair normalizes to a common term. So the system is convergent and decides the word problem for groups. For example, $i(a \cdot i(b)) \cdot a$ normalizes to $b$:

```
i(a·i(b))·a  →  (i(i(b))·i(a))·a  →  (b·i(a))·a  →  b·(i(a)·a)  →  b·e  →  b
```

## Common mistakes

- Reading local confluence as confluence. Newman's lemma needs termination, as the four-element counterexample shows.
- Assuming joinable critical pairs prove confluence for a nonterminating system. The system with $c \to g(c)$ above is a counterexample.
- Allowing superposition into a variable position when computing critical pairs. These overlaps are the variable-overlap case and are always joinable.
- Forgetting to rename the two rules apart. Then the mgu is wrong or missing.
- Excluding non-root self-overlaps. Only the root overlap of a rule with its own variant is trivial.
- Comparing two terms with LPO and forgetting the requirement $s \succ t_j$ for all arguments in cases (b) and (c).
- Ignoring the variable condition of KBO. Weight alone does not decide, since $f(x_1, x_1)$ cannot be above $g(x_1, x_2)$ because of $x_2$, even if it is heavier.
- Giving weight 0 to a unary symbol that is not greatest in the precedence. If $w(g) = 0$ and $f > g$, then $f(x_1) \succ g(f(x_1))$, which breaks the subterm property.
- Treating a nonterminating run as failure. Divergence still gives a semi-decision procedure, while failure means that an equation could not be oriented.
- Believing that success depends on the order of steps in the result. For a fixed ordering, a successful fair run ends with the unique interreduced system. Failure and divergence can depend on the strategy and the ordering.

## Exercises

1. Define confluence, local confluence, Church-Rosser and convergence, and state Newman's lemma.

<details><summary>Solution</summary>

Confluence says that $y \leftarrow^* x \to^* z$ implies $y \downarrow z$. Local confluence says the same for one-step divergences $y \leftarrow x \to z$. Church-Rosser says that $y \leftrightarrow^* z$ implies $y \downarrow z$. Convergence is termination together with confluence. Newman's lemma states that a terminating relation is confluent if and only if it is locally confluent.

</details>

2. Show that $b \to a$, $b \to c$, $c \to b$, $c \to d$ is locally confluent and not confluent. Say which hypothesis of Newman's lemma fails.

<details><summary>Solution</summary>

The peak $a \leftarrow b \to c$ joins at $a$, by $c \to b \to a$. The peak $b \leftarrow c \to d$ joins at $d$, by $b \to c \to d$. So the system is locally confluent. It is not confluent, because $b \to^* a$ and $b \to^* d$, and $a$ and $d$ are distinct normal forms. The hypothesis that fails is termination, since $b \to c \to b$ is a cycle.

</details>

3. Prove termination of the Ackermann rules by LPO with $\mathit{ack} > s > 0$.

$$
\mathit{ack}(0, x_1) \to s(x_1), \quad
\mathit{ack}(s(x_1), 0) \to \mathit{ack}(x_1, s(0)), \quad
\mathit{ack}(s(x_1), s(x_2)) \to \mathit{ack}(x_1, \mathit{ack}(s(x_1), x_2)).
$$

<details><summary>Solution</summary>

Rule 1: since $\mathit{ack} > s$, use case (b). The term $\mathit{ack}(0, x_1)$ is above $x_1$, by the subterm case.

Rule 2: roots are equal, so use case (c). The first arguments have $s(x_1) \succ x_1$. It remains to show that the left side $u$ is above $x_1$, which is by the subterm case, and above $s(0)$. For this, $\mathit{ack} > s$ and $u \succ 0$, using $\mathit{ack} > 0$.

Rule 3: let $u = \mathit{ack}(s(x_1), s(x_2))$. Use case (c). The first arguments have $s(x_1) \succ x_1$. It remains to show that $u$ is above $x_1$ and above $\mathit{ack}(s(x_1), x_2)$. The first is the subterm case. For the second, use case (c) again: the first arguments are equal, the second have $s(x_2) \succ x_2$, and $u$ is above $s(x_1)$ and above $x_2$ by the subterm case.

</details>

4. Decide which of the following hold in KBO with all weights 1 and $w_0 = 1$, and $f > g$: $f(x_1, x_2) \succ g(x_1)$, $f(x_1, x_2) \succ g(x_3)$, $x_1 \cdot (x_2 + x_3) \succ (x_1 \cdot x_2) + (x_1 \cdot x_3)$ with $\cdot > +$.

<details><summary>Solution</summary>

The first holds, since $x_1$ appears once on each side and the weight drops from 3 to 2. The second fails, since $x_3$ occurs on the right only. The third fails, since $x_1$ occurs twice on the right and once on the left.

</details>

5. Find all critical pairs of $f(f(x_1)) \to f(x_1)$. Determine whether this system is convergent.

<details><summary>Solution</summary>

Overlap a renamed copy into position 1 of the left side, with mgu $\{x_1 \mapsto f(x_2)\}$. The peak is $f(f(f(x_2)))$. The inner step gives $f(f(x_2))$. The outer step gives $f(f(x_2))$. The critical pair has equal sides, so it is joinable. The system terminates, since the term size decreases. So it is convergent by the Knuth-Bendix theorem.

</details>

6. Compute the critical pair of $g(b) \to c$ into $f(g(x_1)) \to a$, and decide whether the system is confluent. Then complete it with LPO and $f > g > a > b > c$.

<details><summary>Solution</summary>

Overlap at position 1 of $f(g(x_1))$, with mgu $\{x_1 \mapsto b\}$. The peak is $f(g(b))$, which rewrites to $f(c)$ and to $a$. Both are normal forms and they differ, so the system is not confluent.

For completion, orient $f(c) = a$. The ordering gives $f(c) \succ a$, so the new rule is $f(c) \to a$. It does not overlap with $g(b) \to c$ or with $f(g(x_1)) \to a$, because $f(c)$ and $f(g(x_1))$ do not unify and no rule's left side unifies with a subterm $c$. The three rules form a convergent system.

</details>

7. Complete $\{f(f(f(x_1))) = x_1, f(f(f(f(f(x_1))))) = x_1\}$ with LPO. Interpret the result.

<details><summary>Solution</summary>

```
Orient      R1: f(f(f(x1))) → x1
Simplify    f(f(f(f(f(x1))))) = x1 normalizes to f(f(x1)) = x1
Orient      R2: f(f(x1)) → x1
Collapse    R1 becomes f(x1) = x1, since f(f(f(x1))) rewrites to f(x1) by R2
Orient      R3: f(x1) → x1
Collapse    R2 becomes x1 = x1 by R3 twice, deleted
```

The final system is $\{f(x_1) \to x_1\}$, with no critical pairs because its left side has no non-variable proper subterm. It shows that if $f^3$ and $f^5$ are both the identity, then $f$ is the identity. The reason is that 3 and 5 are coprime.

</details>

8. Let $E = \{f(f(a)) = a, f(a) = b\}$ with LPO and $f > a > b$. Complete $E$ and decide whether $E \models f(f(b)) \approx b$.

<details><summary>Solution</summary>

Orient $f(a) \to b$. The first equation then normalizes to $f(b) = a$, which is oriented as $f(b) \to a$, using $f > a$. The two left sides do not overlap, so the system is convergent. Normalizing $f(f(b))$ gives $f(a)$, then $b$. Normalizing $b$ gives $b$. So the entailment holds.

</details>

9. Run completion on commutativity $x_1 \cdot x_2 = x_2 \cdot x_1$ with any LPO, and explain the result. Then say how ordered rewriting treats this equation for ground terms $a \cdot b$ and $b \cdot a$ with $a > b$.

<details><summary>Solution</summary>

Completion fails at once, because the two sides are permutations of each other, and stability of a reduction ordering would force the opposite comparison after swapping variables. So no reduction ordering orients the equation.

Ordered rewriting keeps the equation and applies it to an instance only if the result decreases. With $a > b$ and LPO we have $a \cdot b \succ b \cdot a$, so $a \cdot b$ rewrites to $b \cdot a$, and $b \cdot a$ is a normal form. Both terms reach the same normal form, so the goal $a \cdot b \approx b \cdot a$ is proved.

</details>

10. Show that completion diverges on $f(g(f(x_1))) = g(f(x_1))$ with LPO and $f > g$. Give the general form of the rules and the persisting limit.

<details><summary>Solution</summary>

Orient $R_1$: $f(g(f(x_1))) \to g(f(x_1))$, which holds because the right side is a subterm of the left. Assume $R_n$: $f(g^n(f(x_1))) \to g^n(f(x_1))$. Overlap $R_1$ into $R_n$ at the position of the inner $f$, using the mgu $\{x_1 \mapsto g(f(x_2))\}$ on the left side of $R_n$.

```
peak    f(g^n(f(g(f(x2)))))
inner   f(g^n(g(f(x2))))  =  f(g^(n+1)(f(x2)))
outer   g^n(f(g(f(x2))))  →  g^n(g(f(x2)))  =  g^(n+1)(f(x2))
```

The inner term is a normal form with respect to $R_1, \ldots, R_n$, because each of those has a left side $f(g^k(f(\cdot)))$ with $k \leq n$ and the only $f$-rooted subterms with $f$ below them have $k = n + 1$. So the new rule is $R_{n+1}$. Completion never stops, and it adds the infinite family $f(g^n(f(x_1))) \to g^n(f(x_1))$ for $n \geq 1$. That family is the persisting limit. It is confluent, and it decides the word problem only in the semi-decision sense unless one recognizes the pattern.

</details>

11. Prove that if $R$ is convergent and $\leftrightarrow_R^* = \leftrightarrow_E^*$, then $E \models s \approx t$ if and only if $\mathrm{nf}(s) = \mathrm{nf}(t)$.

<details><summary>Solution</summary>

By Birkhoff's theorem, $E \models s \approx t$ if and only if $s \leftrightarrow_E^* t$, which by assumption is $s \leftrightarrow_R^* t$. If $\mathrm{nf}(s) = \mathrm{nf}(t)$, this clearly holds. Conversely, $R$ is confluent, so it is Church-Rosser, and $s \downarrow t$. Both sides reduce to some $w$, and $w$ reduces to a normal form. By confluence and termination the normal form is unique, so it equals both $\mathrm{nf}(s)$ and $\mathrm{nf}(t)$.

</details>

12. Prove the variable-overlap case of the critical pair lemma for a rule $l_2 \to r_2$ with variable $x$ in $l_2$ occurring $m$ times on the left and $k$ times on the right, assuming a peak in which $l_1\sigma_1$ rewrites inside one occurrence of $x\sigma_2$.

<details><summary>Solution</summary>

Write $x\sigma_2 = u[l_1\sigma_1]_q$ and $u' = u[r_1\sigma_1]_q$, so $x\sigma_2 \to u'$. The peak has $t_1 = l_2\sigma_2$ with one occurrence of $x\sigma_2$ replaced by $u'$, and $t_2 = r_2\sigma_2$.

Rewriting the remaining $m - 1$ occurrences of $x\sigma_2$ in $t_1$ to $u'$ gives $l_2\sigma_2'$, where $\sigma_2'$ agrees with $\sigma_2$ except that $x\sigma_2' = u'$. This rewrites to $r_2\sigma_2'$ by the rule $l_2 \to r_2$. Rewriting all $k$ occurrences of $x\sigma_2$ in $t_2$ to $u'$ gives $r_2\sigma_2'$ as well. So $t_1$ and $t_2$ are joinable, with no assumption on critical pairs. If $x$ is non-linear, $m - 1$ can be positive, and this is why the case uses several rewrite steps.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State and prove Newman's lemma, and give the counterexample without termination.
- Decide LPO and KBO comparisons on unseen terms by writing the complete derivation.
- Find a polynomial interpretation for a small system.
- Compute all critical pairs of a small TRS and decide its confluence.
- State the completion rules and run completion by hand on a system with a small number of rules, reporting success, failure or divergence.
- Reproduce the first ten rule steps of group completion, or derive each of the ten final rules from a peak.
- Explain how ordered rewriting extends completion and why it needs a ground-total ordering.

## Materials

- Baader and Nipkow, Term Rewriting and All That. Read it as the main reference for abstract reduction, termination orderings, critical pairs and completion.
- [Harrison, Handbook of Practical Logic and Automated Reasoning.](https://www.cl.cam.ac.uk/~jrh13/atp/) Read its material on equality, rewriting and Knuth-Bendix completion for an algorithmic view of the same results.
- Knuth and Bendix, Simple Word Problems in Universal Algebras, in Computational Problems in Abstract Algebra, 1970. Read it for the original procedure and for the group theory example.
- Bachmair, Dershowitz and Plaisted, Completion Without Failure, in Resolution of Equations in Algebraic Structures, 1989. Read it for unfailing completion, which leads to superposition.
