# Induction Principles

Part 1, Chapter 3: Semantics and Types.

## Objective

Prove properties using structural, rule and well-founded induction.

## Why this matters

Almost every theorem in this chapter has the same shape: a language or a judgment is defined inductively, and a property is proved by induction over that definition. Determinism of evaluation, soundness of Hoare logic and type preservation are all rule inductions. Later chapters reuse the same tools: termination of rewriting in [Term Rewriting](../../../part-2-core-reasoning/06-first-order-proving/term-rewriting/) and of loops in [Loop Invariants](../../../part-2-core-reasoning/07-deductive-verification/loop-invariants/) rests on well-founded orders, and proof assistants in [Chapter 12](../../../part-4-remaining-methods/12-proof-assistants/) generate these induction principles automatically from inductive definitions. An applied scientist who can pick the right induction and the right induction hypothesis will finish proofs, by hand or in a prover, that otherwise stall.

## Prerequisites

- [Propositional Logic](../../01-mathematical-logic/propositional-logic/), for structural induction over formulas.
- [Proof Systems](../../01-mathematical-logic/proof-systems/), for derivations built from inference rules.
- [Soundness and Completeness](../../01-mathematical-logic/soundness-and-completeness/), for an example of induction over derivations.

## Lesson

### Well-founded relations

All the principles in this topic are instances of one theorem, so the lesson begins with it.

Definition. A binary relation $\prec$ on a set $A$ is well-founded if there is no infinite descending sequence $a_0 \succ a_1 \succ a_2 \succ \cdots$, where $a \succ b$ means $b \prec a$.

The relation need not be transitive or total, and it need not be an order at all. The successor relation $\{(n, n+1) \mid n \in \mathbb{N}\}$ is well-founded, and so is the immediate-subterm relation on syntax trees. A well-founded relation is irreflexive and has no cycles, since a cycle could be traversed forever. The converse fails: the relation with $n + 1 \prec n$ for all $n \in \mathbb{N}$ has no cycles, yet $0 \succ 1 \succ 2 \succ \cdots$ is an infinite descending sequence for it.

An element $m \in Q$ is $\prec$-minimal in $Q$ if no $b \in Q$ satisfies $b \prec m$.

Proposition 1. The relation $\prec$ is well-founded if and only if every nonempty subset of $A$ has a $\prec$-minimal element.

Proof. Suppose every nonempty subset has a minimal element. The set of elements of an infinite descending sequence would be nonempty with no minimal element, so no such sequence exists. Conversely, suppose $Q \subseteq A$ is nonempty with no minimal element. Choose $a_0 \in Q$. Since $a_i$ is not minimal, there is $a_{i+1} \in Q$ with $a_{i+1} \prec a_i$. This yields an infinite descending sequence. The construction uses the axiom of dependent choice. $\square$

Theorem 2 (well-founded induction). Let $\prec$ be well-founded on $A$ and let $P$ be a property of elements of $A$. If

$$\forall a \in A.\ \bigl(\forall b \prec a.\ P(b)\bigr) \to P(a),$$

then $\forall a \in A.\ P(a)$.

Proof. Suppose the hypothesis holds and $Q = \{a \mid \neg P(a)\}$ is nonempty. Let $m$ be minimal in $Q$. Every $b \prec m$ lies outside $Q$, so $P(b)$ holds. The hypothesis then gives $P(m)$, which contradicts $m \in Q$. $\square$

There is no separate base case. For a $\prec$-minimal element $a$ of $A$ the inner quantifier is vacuous, so the step must prove $P(a)$ with no assumptions. Base cases are the cases of the step in which nothing is smaller.

Theorem 3 (converse). If the conclusion of Theorem 2 holds for every property $P$, then $\prec$ is well-founded.

Proof. Let $P(a)$ say that no infinite descending sequence starts at $a$. If $P(b)$ holds for all $b \prec a$, then $P(a)$ holds, because a sequence $a \succ a_1 \succ \cdots$ would give a sequence starting at $a_1 \prec a$. So the premise of the principle holds, and the principle gives $P(a)$ for all $a$. $\square$

So well-foundedness is exactly the condition under which induction is valid.

### Building well-founded relations

Proving well-foundedness directly is rarely necessary, since a few constructions cover most uses.

| Construction | Definition | Why it is well-founded |
|---|---|---|
| Subrelation | ${\prec'} \subseteq {\prec}$. | Each $\prec'$-descending sequence is $\prec$-descending. |
| Inverse image, or measure | $a \prec_f a'$ iff $f(a) \prec f(a')$, for $f : A \to B$. | A descending sequence in $A$ maps to one in $B$. |
| Transitive closure | ${\prec^{+}}$ is the least transitive relation containing $\prec$. | Each $\prec^{+}$-descending sequence expands to a $\prec$-descending sequence. |
| Lexicographic product | $(a,b) \prec_{\text{lex}} (a',b')$ iff $a \prec_A a'$, or $a = a'$ and $b \prec_B b'$. | See the proof below. |

Proposition 4. If $\prec_A$ and $\prec_B$ are well-founded, then $\prec_{\text{lex}}$ is well-founded on $A \times B$.

Proof. Take a descending sequence $(a_0,b_0) \succ_{\text{lex}} (a_1,b_1) \succ_{\text{lex}} \cdots$. At each step, either $a_{i+1} \prec_A a_i$ or $a_{i+1} = a_i$. Only finitely many steps can be of the first kind, since otherwise deleting repetitions would give an infinite $\prec_A$-descending sequence. So from some index on, the first component is constant, and from there the second component strictly descends forever, which is impossible. Hence the sequence is finite. $\square$

The measure construction is the most common: to prove termination of a process, map each state to a natural number or a tuple of natural numbers that strictly decreases. The multiset ordering of Dershowitz and Manna extends this to measures that are collections of values, and it recurs in term rewriting.

Mathematical induction is Theorem 2 for the successor relation, and course-of-values induction is Theorem 2 for $<$ on $\mathbb{N}$. Exercise 2 carries this out.

### Structural induction

A grammar such as

$$a ::= n \mid x \mid a_1 + a_2 \mid a_1 - a_2 \mid a_1 \times a_2$$

defines a set of finite trees. The immediate-subterm relation on these trees is well-founded, because it is contained in the inverse image of $<$ under the size of a tree. Theorem 2 for this relation is structural induction: to prove $P(a)$ for all $a$, prove $P(n)$ and $P(x)$ for all atoms, and prove $P(a_1 \circ a_2)$ assuming $P(a_1)$ and $P(a_2)$, for each operator $\circ$.

Structural induction has a companion for definitions. A function can be defined on syntax by giving one equation for each production, with recursive calls only on immediate subterms. The function exists and is unique because every tree has a unique top-level form. More generally, well-founded recursion says that for well-founded $\prec$ and any $G$, there is a unique $f$ with $f(a) = G(a, f{\restriction}_{\{b \mid b \prec a\}})$ for all $a$. Uniqueness is Exercise 9. Existence is proved by well-founded induction, by showing that each $a$ has a unique partial solution defined on the elements below it, and gluing these solutions together.

The semantics of arithmetic expressions used throughout this chapter is such a definition. A state is a function $\sigma : \mathrm{Var} \to \mathbb{Z}$, and

$$\mathcal{A}[\![n]\!]\sigma = n, \qquad \mathcal{A}[\![x]\!]\sigma = \sigma(x), \qquad \mathcal{A}[\![a_1 \circ a_2]\!]\sigma = \mathcal{A}[\![a_1]\!]\sigma \circ \mathcal{A}[\![a_2]\!]\sigma.$$

### Inductive definitions by rules

Many sets in semantics are defined by rules: the evaluation relation, the typing relation, the set of theorems of a proof system. Winskel's formulation captures all of them.

Definition. A rule instance is a pair $(X / y)$, where $X$ is a set of premises and $y$ is a conclusion. If $X = \emptyset$, the rule is an axiom. A rule set $R$ is a set of rule instances. A set $Q$ is $R$-closed if, for every $(X/y) \in R$, $X \subseteq Q$ implies $y \in Q$. The set inductively defined by $R$ is

$$I_R = \bigcap \{Q \mid Q \text{ is } R\text{-closed}\}.$$

Define the operator $\hat{R}(Q) = \{y \mid \exists (X/y) \in R.\ X \subseteq Q\}$. It is monotone, and $Q$ is $R$-closed if and only if $\hat{R}(Q) \subseteq Q$.

Theorem 5. The set $I_R$ is $R$-closed, it is contained in every $R$-closed set, and $\hat{R}(I_R) = I_R$. So $I_R$ is the least fixed point of $\hat{R}$.

Proof. If $(X/y) \in R$ and $X \subseteq I_R$, then $X \subseteq Q$ for each closed $Q$, so $y \in Q$ for each closed $Q$, so $y \in I_R$. Thus $I_R$ is closed, and it is contained in every closed set by definition. Closure gives $\hat{R}(I_R) \subseteq I_R$. Applying the monotone $\hat{R}$ gives $\hat{R}(\hat{R}(I_R)) \subseteq \hat{R}(I_R)$, so $\hat{R}(I_R)$ is closed and therefore contains $I_R$. A fixed point of $\hat{R}$ is closed, so it contains $I_R$. $\square$

This is the Knaster–Tarski construction specialized to a powerset. Two consequences are used constantly.

First, the rule induction principle.

Theorem 6 (rule induction). Let $P$ be a property. If for every $(X/y) \in R$,

$$\bigl(X \subseteq I_R \land \forall x \in X.\ P(x)\bigr) \to P(y),$$

then $P(y)$ holds for all $y \in I_R$.

Proof. The set $Q = \{y \in I_R \mid P(y)\}$ is $R$-closed: if $X \subseteq Q$, then $X \subseteq I_R$ and all premises satisfy $P$, so $y \in I_R$ by closure of $I_R$ and $P(y)$ by assumption. Hence $I_R \subseteq Q$. $\square$

Second, the inversion principle. Since $I_R \subseteq \hat{R}(I_R)$, each $y \in I_R$ is the conclusion of some rule whose premises all lie in $I_R$. Theorem 5 therefore says that $I_R$ contains what the rules force and nothing more. Inversion is the reasoning step "this judgment holds, so it must have come from one of these rules". It uses no induction hypothesis.

A derivation of $y$ is a finite tree whose root is $y$, whose nodes are justified by rule instances, and whose leaves are axioms. When every rule has finitely many premises, the stages $\hat{R}^n(\emptyset)$ form an increasing chain, $y \in \hat{R}^n(\emptyset)$ if and only if $y$ has a derivation of height at most $n$, and

$$I_R = \bigcup_{n \in \mathbb{N}} \hat{R}^n(\emptyset).$$

The union is closed because a finite premise set $X$ contained in the union lies in a single stage. Each stage lies in $I_R$ by induction on $n$. It follows that rule induction, induction on derivation height and structural induction on derivation trees prove the same statements. Exercise 8 shows what changes when rules have infinitely many premises.

As a small example, let $\mathrm{Even}$ be defined on $\mathbb{N}$ by the axiom $\mathrm{Even}(0)$ and the rule from $\mathrm{Even}(n)$ to $\mathrm{Even}(n+2)$. Rule induction proves that $\mathrm{Even}(n)$ implies $\exists k.\ n = 2k$. Inversion proves $\neg\mathrm{Even}(1)$ directly: the axiom concludes $0 \neq 1$, and the other rule concludes $n + 2 \neq 1$.

### The least and the greatest fixed point

The least fixed point contains exactly the elements with a finite derivation. A greatest fixed point also exists, and it admits the coinduction principle: if $Q \subseteq \hat{R}(Q)$, then $Q$ is contained in the greatest fixed point. For the single rule $(\{a\}/a)$, the least fixed point is $\emptyset$ and the greatest is $\{a\}$, since $a$ has an infinite but no finite derivation. Coinduction is the right tool for infinite behaviour such as divergence. This chapter needs it only in passing, and the fixed-point theory returns in [Denotational Semantics](../denotational-semantics/).

### Choosing the induction

Three decisions determine whether an inductive proof succeeds.

The first is what to induct on. A property of a judgment should usually be proved by rule induction on that judgment's derivation, even when the judgment mentions syntax. In the [Operational Semantics](../operational-semantics/) topic, one rule for a loop has a premise about the same loop, so structural induction on the command gives no hypothesis there. Rule induction does.

The second is how strong to make the property. An induction hypothesis is also an assumption you get to use, so a stronger statement can be easier to prove. Any variable that changes between the conclusion and the premises of a rule must be universally quantified inside $P$. Exercise 4 shows this, and so does the determinism proof in [Operational Semantics](../operational-semantics/).

The third is how to treat a judgment with a specific shape. Rule induction proves a property of all members of $I_R$, so its form must apply to an arbitrary conclusion. To prove something about all derivations of $\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma\rangle \Downarrow \sigma'$, state $P(c', \sigma, \sigma')$ as "if $c' = \texttt{while}\ b\ \texttt{do}\ c$, then ...". Rules concluding about other commands are then vacuous.

Sets defined by several mutually dependent judgments use a simultaneous induction. Treat the rules as one rule set on a disjoint union, so that the property to prove is a pair of properties, one per judgment. Exercise 10 shows the method.

## Worked examples

### Worked Example 1: a substitution lemma by structural induction

Define substitution by $n[a'/x] = n$, $x[a'/x] = a'$, $y[a'/x] = y$ for $y \neq x$, and $(a_1 \circ a_2)[a'/x] = a_1[a'/x] \circ a_2[a'/x]$. Write $\sigma[x \mapsto v]$ for the state equal to $\sigma$ except that $x$ maps to $v$.

Claim. For all $a, a', x, \sigma$,

$$\mathcal{A}[\![a[a'/x]]\!]\sigma = \mathcal{A}[\![a]\!]\bigl(\sigma[x \mapsto \mathcal{A}[\![a']\!]\sigma]\bigr).$$

Fix $a', x, \sigma$, write $v = \mathcal{A}[\![a']\!]\sigma$ and $\tau = \sigma[x \mapsto v]$, and induct on the structure of $a$.

Case $a = n$. Both sides equal $n$.

Case $a = x$. The left side is $\mathcal{A}[\![a']\!]\sigma = v$, and the right side is $\tau(x) = v$.

Case $a = y$ with $y \neq x$. The left side is $\sigma(y)$, and the right side is $\tau(y) = \sigma(y)$.

Case $a = a_1 \circ a_2$. The left side is

$$\mathcal{A}[\![a_1[a'/x] \circ a_2[a'/x]]\!]\sigma = \mathcal{A}[\![a_1[a'/x]]\!]\sigma \circ \mathcal{A}[\![a_2[a'/x]]\!]\sigma.$$

By the induction hypothesis this equals $\mathcal{A}[\![a_1]\!]\tau \circ \mathcal{A}[\![a_2]\!]\tau = \mathcal{A}[\![a_1 \circ a_2]\!]\tau$, which is the right side. $\square$

This lemma is what makes the assignment axiom of Hoare logic sound, as [Axiomatic Semantics](../axiomatic-semantics/) shows.

### Worked Example 2: transitivity of a closure by rule induction

Let $\to_R$ be a binary relation on a set. Define $\to_R^{\ast}$ by the rules

$$\frac{}{a \to_R^{\ast} a}\ \text{(Refl)} \qquad\qquad \frac{a \to_R b \quad b \to_R^{\ast} c}{a \to_R^{\ast} c}\ \text{(Step)}$$

Claim. If $a \to_R^{\ast} b$ and $b \to_R^{\ast} c$, then $a \to_R^{\ast} c$.

The rules only extend a sequence on the left, so the choice of derivation matters: induct on the derivation of $a \to_R^{\ast} b$. The variable $c$ does not change across the rules, so it could also be fixed in advance. Define

$$P(a, b) \;:=\; \forall c.\ b \to_R^{\ast} c \to a \to_R^{\ast} c.$$

Case Refl. The conclusion is $a \to_R^{\ast} a$, so $b = a$. Then $P(a, a)$ says that $a \to_R^{\ast} c$ implies $a \to_R^{\ast} c$, which is immediate.

Case Step. The conclusion is $a \to_R^{\ast} b$, with premises $a \to_R d$ and $d \to_R^{\ast} b$. The induction hypothesis is $P(d, b)$. Assume $b \to_R^{\ast} c$. Then $P(d, b)$ gives $d \to_R^{\ast} c$. Applying Step to $a \to_R d$ and $d \to_R^{\ast} c$ gives $a \to_R^{\ast} c$. $\square$

An induction on the derivation of $b \to_R^{\ast} c$ stalls. In the Step case the second derivation has conclusion $b \to_R^{\ast} c$ with premises $b \to_R d$ and $d \to_R^{\ast} c$, and the hypothesis speaks about $d$, with $a \to_R^{\ast} d$ required. You have only $a \to_R^{\ast} b$ and $b \to_R d$, and extending a sequence on the right is itself a form of the claim being proved.

### Worked Example 3: totality of Ackermann's function by lexicographic induction

Consider the equations on $\mathbb{N}$:

$$A(0, n) = n + 1, \qquad A(m+1, 0) = A(m, 1), \qquad A(m+1, n+1) = A(m, A(m+1, n)).$$

The inner call can return a very large second argument, so the second component alone cannot serve as a measure. Lexicographic order on $\mathbb{N} \times \mathbb{N}$ handles this, since the first component decreases regardless of how large the second component becomes.

Claim. The equations define a total function: for all $(m, n)$, evaluation by the equations terminates with a unique value.

Let $P(m, n)$ say that this holds for the argument $(m, n)$. Use well-founded induction on $<_{\text{lex}}$, which is well-founded by Proposition 4. Exactly one equation applies to each argument, so uniqueness is immediate once termination is shown.

Case $(0, n)$. The value is $n + 1$ with no recursive call.

Case $(m+1, 0)$. The call is on $(m, 1)$, and $(m, 1) <_{\text{lex}} (m+1, 0)$ because $m < m + 1$. The induction hypothesis gives a value.

Case $(m+1, n+1)$. First, $(m+1, n) <_{\text{lex}} (m+1, n+1)$, because the first components are equal and $n < n + 1$. The hypothesis gives a value $v$. Second, $(m, v) <_{\text{lex}} (m+1, n+1)$ for any $v$, because $m < m + 1$. The hypothesis gives a value of $A(m, v)$. $\square$

Evaluation of $A(1, 1)$, as a check:

```
A(1,1) = A(0, A(1,0))     third equation
       = A(0, A(0,1))     second equation
       = A(0, 2)          first equation
       = 3                first equation
```

## Common mistakes

- Treating well-foundedness as a property of total orders. The immediate-subterm relation is neither total nor transitive, and it supports induction. Correct by checking only for infinite descending sequences.
- Believing that well-founded induction needs a separate base case. Correct by proving the single step for an arbitrary element, and noticing that minimal elements get a vacuous hypothesis.
- Inducting on the syntax of a command when a rule's premise concerns the same command. Correct by inducting on the derivation.
- Fixing a variable before the induction when it changes across rules. The hypothesis is then too weak to apply. Correct by moving the quantifier inside the property, as in Exercise 4.
- Confusing inversion with rule induction. Inversion analyses the last rule of one derivation and gives premises. Rule induction additionally gives the property for those premises. Use inversion when no hypothesis is needed, which keeps the proof shorter.
- Forgetting the extremal clause of an inductive definition. The rules alone do not prove $\neg\mathrm{Even}(1)$. The fact that $I_R$ is the least closed set does, because it justifies inversion.
- Applying rule induction to a judgment with a fixed shape without generalizing it. The conclusion of a rule may have a different shape. Correct by stating the property for arbitrary conclusions, guarded by an equation.
- Assuming that a lexicographic order is well-founded on strings of unbounded length. It is well-founded on pairs and fixed-length tuples, but the dictionary order on all strings over $\{a, b\}$ has the infinite descending sequence $b \succ ab \succ aab \succ \cdots$.

## Exercises

### Exercise 1

Decide which relations are well-founded, and give a descending sequence for each that is not: (a) $<$ on $\mathbb{N}$; (b) $<$ on $\mathbb{Z}$; (c) $<$ on nonnegative rationals; (d) proper subset on finite subsets of $\mathbb{N}$; (e) proper subset on all subsets of $\mathbb{N}$; (f) proper suffix on finite strings; (g) dictionary order on finite strings over $\{a, b\}$.

<details><summary>Solution</summary>

(a) Well-founded. (b) Not well-founded: $0 > -1 > -2 > \cdots$. (c) Not well-founded: $1 > 1/2 > 1/4 > \cdots$. (d) Well-founded, since the cardinality strictly decreases, so this relation is contained in the inverse image of $<$ under cardinality. (e) Not well-founded: $\mathbb{N} \supsetneq \mathbb{N} \setminus \{0\} \supsetneq \mathbb{N} \setminus \{0, 1\} \supsetneq \cdots$. (f) Well-founded, since length strictly decreases. (g) Not well-founded: $b \succ ab \succ aab \succ \cdots$, where each string precedes the one before it in dictionary order.

</details>

### Exercise 2

Derive mathematical induction and course-of-values induction on $\mathbb{N}$ from Theorem 2.

<details><summary>Solution</summary>

For course-of-values induction, take $\prec$ to be $<$ on $\mathbb{N}$, which is well-founded because a descending sequence starting at $n$ has at most $n + 1$ elements. Theorem 2 reads as: if $(\forall m < n.\ P(m)) \to P(n)$ for all $n$, then $\forall n.\ P(n)$.

For mathematical induction, take $m \prec n$ iff $n = m + 1$. This relation is contained in $<$, so it is well-founded. Assume $P(0)$ and $\forall k.\ P(k) \to P(k+1)$. To apply Theorem 2, fix $n$ and assume $P(b)$ for all $b \prec n$. If $n = 0$, the goal $P(0)$ is given. If $n = k + 1$, then $k \prec n$, so $P(k)$ holds, and $P(k+1)$ follows. Thus $\forall n.\ P(n)$.

</details>

### Exercise 3

Binary trees are given by $t ::= \mathrm{leaf} \mid \mathrm{node}(t_1, t_2)$. Let $\ell(t)$ count leaves, $i(t)$ count node constructors, and let $h(\mathrm{leaf}) = 0$ and $h(\mathrm{node}(t_1, t_2)) = 1 + \max(h(t_1), h(t_2))$. Prove that $\ell(t) = i(t) + 1$ and $\ell(t) \le 2^{h(t)}$.

<details><summary>Solution</summary>

Use structural induction on $t$.

Case $\mathrm{leaf}$. Here $\ell = 1$, $i = 0$ and $h = 0$, so $1 = 0 + 1$ and $1 \le 2^0$.

Case $\mathrm{node}(t_1, t_2)$. For the first claim, $\ell(t) = \ell(t_1) + \ell(t_2) = i(t_1) + 1 + i(t_2) + 1 = (i(t_1) + i(t_2) + 1) + 1 = i(t) + 1$. For the second claim, let $h' = \max(h(t_1), h(t_2))$. Then $\ell(t) = \ell(t_1) + \ell(t_2) \le 2^{h(t_1)} + 2^{h(t_2)} \le 2 \cdot 2^{h'} = 2^{h(t)}$.

</details>

### Exercise 4

Define $f(0, s) = s$ and $f(n+1, s) = f(n, s + n + 1)$ on integers $s$ and naturals $n$. Prove that $f(n, 0) = n(n+1)/2$. Explain why a direct induction on this statement fails.

<details><summary>Solution</summary>

A direct induction fails. The step needs $f(n+1, 0) = f(n, n+1)$, but the hypothesis only speaks of $f(n, 0)$, with second argument $0$.

Generalize to $Q(n)$: for all $s$, $f(n, s) = s + n(n+1)/2$.

Case $n = 0$. $f(0, s) = s$.

Case $n + 1$. Fix $s$. Then $f(n+1, s) = f(n, s + n + 1)$. Instantiating $Q(n)$ at $s + n + 1$ gives $s + n + 1 + n(n+1)/2 = s + (n+1)(n+2)/2$.

Setting $s = 0$ gives the claim.

</details>

### Exercise 5

Prove that the inverse image of a well-founded relation is well-founded, and that the transitive closure of a well-founded relation is well-founded.

<details><summary>Solution</summary>

Inverse image. Given $f : A \to B$ and well-founded $\prec$ on $B$, an infinite sequence $a_0 \succ_f a_1 \succ_f \cdots$ gives $f(a_0) \succ f(a_1) \succ \cdots$ in $B$, which is impossible.

Transitive closure. If $a \succ^{+} b$, there is a finite $\prec$-path $a \succ c_1 \succ \cdots \succ c_k \succ b$, where $k \ge 0$. Given an infinite sequence $a_0 \succ^{+} a_1 \succ^{+} \cdots$, concatenate the finite paths for each step. The result is an infinite $\prec$-descending sequence, which is impossible.

</details>

### Exercise 6

Let $S$ be the set of strings over the alphabet of parentheses defined by the rules: $\varepsilon \in S$; if $s \in S$, then $(s) \in S$; if $s, t \in S$, then $st \in S$. Let $h(w)$ be the number of opening parentheses in $w$ minus the number of closing parentheses. Let $G$ be the set of strings $w$ such that $h(w) = 0$ and $h(p) \ge 0$ for each prefix $p$ of $w$. Prove that $S = G$.

<details><summary>Solution</summary>

$S \subseteq G$, by rule induction.

Rule $\varepsilon$. Its only prefix is $\varepsilon$, and $h(\varepsilon) = 0$.

Rule $(s)$ with $s \in G$. The value $h((s)) = 1 + h(s) - 1 = 0$. A prefix is $\varepsilon$, or $(p$ for a prefix $p$ of $s$, where $h = 1 + h(p) \ge 1$, or the whole string, where $h = 0$.

Rule $st$ with $s, t \in G$. The value $h(st) = 0$. A prefix is a prefix of $s$, or $sp$ for a prefix $p$ of $t$, where $h(sp) = h(p) \ge 0$.

$G \subseteq S$, by course-of-values induction on $|w|$. Let $w \in G$. If $w = \varepsilon$, the first rule applies. Otherwise the prefix of length one has $h \ge 0$, so $w$ begins with an opening parenthesis. Let $p$ be the shortest nonempty prefix of $w$ with $h(p) = 0$, which exists because $h(w) = 0$. Its last character reduces $h$ to $0$ from a positive value, so it is a closing parenthesis, and $p = (u)$. Write $w = p w'$.

The string $u$ is in $G$. We have $h(u) = h(p) = 0$. For a prefix $v$ of $u$, the string $(v$ is a nonempty prefix of $w$ shorter than $p$, so $h((v) \ge 0$ and $h((v) \ne 0$ by minimality of $p$. So $h((v) \ge 1$, which gives $h(v) \ge 0$.

The string $w'$ is in $G$. We have $h(w') = h(w) - h(p) = 0$, and for a prefix $v$ of $w'$, $h(v) = h(pv) \ge 0$.

Both are shorter than $w$, so $u, w' \in S$ by the hypothesis. Then $(u) \in S$, and $w = (u) w' \in S$.

A brute-force enumeration confirmed $S = G$ for all strings up to length 10.

</details>

### Exercise 7

Prove termination of the rewrite rules $x \times (y + z) \to (x \times y) + (x \times z)$ and $(y + z) \times x \to (y \times x) + (z \times x)$, applied anywhere inside a term built from the constant $c$, $+$ and $\times$.

<details><summary>Solution</summary>

Use a measure into $\mathbb{N}$. Define $[c] = 2$, $[s + t] = [s] + [t] + 1$ and $[s \times t] = [s] \cdot [t]$. By structural induction, $[t] \ge 2$ for each term $t$.

Both rules decrease the measure at the root. Write $x, y, z$ for the values of the instantiating terms, all at least $2$. For the first rule, the left value is $x(y + z + 1) = xy + xz + x$, and the right value is $xy + xz + 1$. Since $x \ge 2 > 1$, the left is greater. The second rule is symmetric.

The operations are strictly monotone in each argument on values at least $2$: $u + v + 1$ clearly is, and $u \cdot v$ is because the other factor is positive. By induction on the context around the rewritten subterm, a decrease inside a term gives a decrease of the whole term.

So each rewrite step strictly decreases $[t] \in \mathbb{N}$. The rewrite relation is contained in the inverse image of $<$ under $[\cdot]$, so it is well-founded.

</details>

### Exercise 8

Consider the rule set on $\mathbb{N} \cup \{\omega\}$ with the axiom $(\emptyset / 0)$, the rules $(\{n\} / n + 1)$ for $n \in \mathbb{N}$, and the rule $(\mathbb{N} / \omega)$. Compute $\hat{R}^k(\emptyset)$ and $\bigcup_k \hat{R}^k(\emptyset)$. Determine $I_R$. State which parts of the lesson fail and which still hold.

<details><summary>Solution</summary>

By induction on $k$, $\hat{R}^k(\emptyset) = \{0, \dots, k - 1\}$. The rule $(\mathbb{N}/\omega)$ never fires at a finite stage, because no finite stage contains all of $\mathbb{N}$. The union is $\mathbb{N}$.

The set $\mathbb{N}$ is not $R$-closed, because $\mathbb{N} \subseteq \mathbb{N}$ and the rule then requires $\omega$. Any closed set contains $0$ and every successor, so contains $\mathbb{N}$, and so contains $\omega$. Therefore $I_R = \mathbb{N} \cup \{\omega\}$, and $I_R \ne \bigcup_k \hat{R}^k(\emptyset)$.

The equation $I_R = \bigcup_{n} \hat{R}^n(\emptyset)$ fails, because its proof needs each premise set to be finite. The element $\omega$ has a well-founded derivation that is infinitely branching and has no finite height, so derivation height must be measured by ordinals. Theorems 5 and 6 still hold, since their proofs never use finiteness of premises.

</details>

### Exercise 9

Let $\prec$ be well-founded on $A$. Prove that if $f$ and $g$ satisfy $f(a) = G(a, f{\restriction}_{\{b \mid b \prec a\}})$ and $g(a) = G(a, g{\restriction}_{\{b \mid b \prec a\}})$ for all $a$, then $f = g$.

<details><summary>Solution</summary>

Let $P(a)$ say $f(a) = g(a)$. Use Theorem 2. Fix $a$ and assume $f(b) = g(b)$ for all $b \prec a$. The restrictions of $f$ and $g$ to $\{b \mid b \prec a\}$ are then the same function. So $f(a) = G(a, f{\restriction}) = G(a, g{\restriction}) = g(a)$.

</details>

### Exercise 10

Define $\mathrm{Ev}$ and $\mathrm{Od}$ on $\mathbb{N}$ simultaneously: $\mathrm{Ev}(0)$ is an axiom; from $\mathrm{Od}(n)$ infer $\mathrm{Ev}(n+1)$; from $\mathrm{Ev}(n)$ infer $\mathrm{Od}(n+1)$. Prove that $\mathrm{Ev}(n)$ holds if and only if $n$ is even, and $\mathrm{Od}(n)$ holds if and only if $n$ is odd.

<details><summary>Solution</summary>

For the forward direction, use rule induction with the pair of properties $P_{\mathrm{Ev}}(n)$: $n$ is even, and $P_{\mathrm{Od}}(n)$: $n$ is odd. The axiom concludes $\mathrm{Ev}(0)$, and $0$ is even. The rule from $\mathrm{Od}(n)$ has hypothesis $n$ odd, so $n + 1$ is even. The rule from $\mathrm{Ev}(n)$ has hypothesis $n$ even, so $n + 1$ is odd.

For the backward direction, use mathematical induction on $n$ for the statement: if $n$ is even then $\mathrm{Ev}(n)$, and if $n$ is odd then $\mathrm{Od}(n)$. For $n = 0$, the axiom applies, and $0$ is not odd. For $n + 1$ even, $n$ is odd, so $\mathrm{Od}(n)$ holds by the hypothesis, and the rule gives $\mathrm{Ev}(n+1)$. The case of $n + 1$ odd is symmetric.

</details>

### Exercise 11

Define the relation $G(a, b, d)$ on naturals by the axiom $G(a, 0, a)$ and the rule: if $b > 0$ and $G(b, a \bmod b, d)$, then $G(a, b, d)$. Use the convention $\gcd(0, 0) = 0$. Prove that $G$ is the graph of $\gcd$, which requires a rule induction and a well-founded induction. Identify which induction proves which half.

<details><summary>Solution</summary>

Soundness: if $G(a, b, d)$, then $d = \gcd(a, b)$. Use rule induction. For the axiom, $\gcd(a, 0) = a$. For the rule, the hypothesis gives $d = \gcd(b, a \bmod b)$, and $\gcd(b, a \bmod b) = \gcd(a, b)$ because $a$ and $a \bmod b$ differ by a multiple of $b$, so $a, b$ and $b, a \bmod b$ have the same common divisors.

Totality: for all $a, b$ there is $d$ with $G(a, b, d)$. Use course-of-values induction on $b$, with $a$ universally quantified inside the property. If $b = 0$, take $d = a$. If $b > 0$, then $a \bmod b < b$, so the hypothesis at second argument $a \bmod b$, with first argument $b$, gives $d$ with $G(b, a \bmod b, d)$. The rule gives $G(a, b, d)$.

Together, for all $a, b$, the triple $(a, b, d)$ is in $G$ exactly when $d = \gcd(a, b)$: soundness gives one direction, and totality with soundness gives the other.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State the definition of a well-founded relation and prove the well-founded induction theorem.
- Prove that a lexicographic product of well-founded relations is well-founded.
- Define $I_R$, prove that it is the least fixed point of $\hat{R}$, and derive rule induction and inversion from that.
- Explain when to use structural induction, rule induction and inversion.
- Generalize a statement so that its induction goes through, and explain which variables must be universally quantified inside the property.

## Materials

- Winskel, The Formal Semantics of Programming Languages. Read the chapters on principles of induction and on inductive definitions for the rule-set formulation used here.
- Harper, Practical Foundations for Programming Languages. Read the part on judgments and rules for a systematic account of inductive definitions as judgments.
- Pierce, Types and Programming Languages. Read the early chapters for induction on terms and on derivations as used in language metatheory.
- Baader and Nipkow, Term Rewriting and All That. Read the material on termination for well-founded orders and polynomial interpretations applied to rewriting.
- Dershowitz and Manna, Proving Termination with Multiset Orderings, Communications of the ACM 1979. Read it for the multiset ordering.
- Aczel, An Introduction to Inductive Definitions, in Handbook of Mathematical Logic 1977. Read it for the general theory of rule sets, including infinitary rules.
