# First-Order Logic

Part 1, Chapter 1: Mathematical Logic.

## Objective

Formalize statements in first-order logic and evaluate formulas in a given structure.

## Why this matters

First-order logic is the common language of specifications, verification conditions and SMT-LIB. When you write a loop invariant, a policy property or a quantified assertion, you are writing a first-order formula, and when a tool reports a counterexample, it is reporting a structure. The definitions in this topic underlie [First-Order Theories](../first-order-theories/), [Quantifiers in SMT](../../../part-2-core-reasoning/05-smt/quantifiers/), [Unification](../../../part-2-core-reasoning/06-first-order-proving/unification/) and [Verification Conditions](../../../part-2-core-reasoning/07-deductive-verification/verification-conditions/). An applied scientist must be able to read a requirement in English, write it correctly with quantifiers, and check the result against small models, because errors in formalization are a common reason that a verified property turns out to say the wrong thing.

## Prerequisites

- [Propositional Logic](../propositional-logic/)

## Lesson

### Why propositional logic is not enough

The argument "every request is logged; this message is a request; therefore this message is logged" is valid because of its internal structure. In propositional logic, its three sentences can only be treated as three unrelated variables, and the conclusion does not follow. Frege's Begriffsschrift of 1879 introduced quantifiers and variables to capture such structure. The name first-order refers to the restriction that quantifiers range over the elements of a domain, and not over sets or relations of elements. That restriction gives up some expressive power, and in exchange it yields a complete proof calculus and the compactness theorem, as you will see in [First-Order Metatheory](../first-order-metatheory/).

### Syntax

A signature $\sigma$ consists of a set of function symbols and a set of predicate symbols, each with a natural number called its arity. A function symbol of arity $0$ is a constant. We also fix a countably infinite set of variables, written $x, y, z, x_1, x_2, \dots$.

The terms over $\sigma$ are defined inductively.

- Each variable is a term.
- If $f$ is a function symbol of arity $n$ and $t_1, \dots, t_n$ are terms, then $f(t_1, \dots, t_n)$ is a term.

The atomic formulas are $\bot$, $\top$, $P(t_1, \dots, t_n)$ for a predicate symbol $P$ of arity $n$, and $s = t$ for terms $s, t$. We treat $=$ as a logical symbol, and its meaning is fixed below. We abbreviate $\neg(s = t)$ as $s \neq t$.

The formulas are the atomic formulas, closed under the connectives $\neg, \land, \lor, \to, \leftrightarrow$, and under the quantifiers: if $\varphi$ is a formula and $x$ a variable, then $\forall x\, \varphi$ and $\exists x\, \varphi$ are formulas. In this program, quantifiers bind as tightly as $\neg$, so the scope of a quantifier is the smallest formula that follows it. Thus $\forall x\, P(x) \to Q(x)$ means $(\forall x\, P(x)) \to Q(x)$, and you must write $\forall x\, (P(x) \to Q(x))$ if the quantifier should cover the implication.

A ground term contains no variables. The free variables are defined recursively. For a term, $\mathrm{FV}(t)$ is the set of variables in $t$. For an atom, $\mathrm{FV}$ is the union over its terms. Connectives take unions, and

$$
\mathrm{FV}(\forall x\, \varphi) = \mathrm{FV}(\exists x\, \varphi) = \mathrm{FV}(\varphi) \setminus \{x\}.
$$

An occurrence of $x$ within the scope of a quantifier on $x$ is bound, and any other occurrence is free. A formula with no free variables is a sentence. The universal closure of $\varphi$ is the sentence obtained by prefixing $\forall$ for each free variable.

### Substitution

The term $t[u/x]$ replaces each occurrence of $x$ in $t$ by $u$. For formulas, $\varphi[u/x]$ replaces each free occurrence of $x$ by $u$, while avoiding capture of the variables of $u$. For atoms and connectives, substitution goes through the structure. For a quantifier $Q \in \{\forall, \exists\}$:

$$
(Q y\, \varphi)[u/x] =
\begin{cases}
Q y\, \varphi & \text{if } x = y \text{ or } x \notin \mathrm{FV}(\varphi),\\
Q y\, (\varphi[u/x]) & \text{if } x \neq y,\ x \in \mathrm{FV}(\varphi) \text{ and } y \notin \mathrm{FV}(u),\\
Q z\, (\varphi[z/y][u/x]) & \text{otherwise, with } z \text{ fresh}.
\end{cases}
$$

The third case is what prevents capture. Without it, $(\exists y\, x < y)[y/x]$ would become $\exists y\, y < y$, which says something entirely different. Renaming a bound variable to a fresh one gives a formula with the same meaning, and two formulas related by such renaming are called alpha-equivalent. Some presentations, including Enderton's, instead declare a substitution undefined when capture would occur and speak of a term being substitutable for a variable. The two presentations are interchangeable.

### Structures

A $\sigma$-structure $\mathcal{M}$ consists of:

- a nonempty set $M$, the domain;
- for each function symbol $f$ of arity $n$, a function $f^{\mathcal{M}} : M^n \to M$, so that constants denote elements;
- for each predicate symbol $P$ of arity $n$, a relation $P^{\mathcal{M}} \subseteq M^n$.

The domain must be nonempty and each function must be total. This is the standard convention, and it has consequences: $\forall x\, P(x) \to \exists x\, P(x)$ is valid, and every term denotes an element, so partial functions such as division have to be modeled in some other way.

An assignment is a function $s$ from variables to $M$. The notation $s[x \mapsto a]$ means $s$ changed to send $x$ to $a$. The value of a term is defined by $x^{\mathcal{M}, s} = s(x)$ and

$$
f(t_1, \dots, t_n)^{\mathcal{M}, s} = f^{\mathcal{M}}(t_1^{\mathcal{M}, s}, \dots, t_n^{\mathcal{M}, s}).
$$

### Tarski's definition of truth

The satisfaction relation $\mathcal{M}, s \models \varphi$ is defined by recursion on $\varphi$. Tarski gave this form of definition in the 1930s.

$$
\begin{aligned}
\mathcal{M}, s \models \top & \quad\text{always, and } \mathcal{M}, s \models \bot \text{ never},\\
\mathcal{M}, s \models P(t_1, \dots, t_n) &\iff (t_1^{\mathcal{M}, s}, \dots, t_n^{\mathcal{M}, s}) \in P^{\mathcal{M}},\\
\mathcal{M}, s \models t_1 = t_2 &\iff t_1^{\mathcal{M}, s} \text{ and } t_2^{\mathcal{M}, s} \text{ are the same element},\\
\mathcal{M}, s \models \neg \varphi &\iff \text{not } \mathcal{M}, s \models \varphi,\\
\mathcal{M}, s \models \varphi \land \psi &\iff \mathcal{M}, s \models \varphi \text{ and } \mathcal{M}, s \models \psi,\\
\mathcal{M}, s \models \varphi \lor \psi &\iff \mathcal{M}, s \models \varphi \text{ or } \mathcal{M}, s \models \psi,\\
\mathcal{M}, s \models \varphi \to \psi &\iff \text{not } \mathcal{M}, s \models \varphi, \text{ or } \mathcal{M}, s \models \psi,\\
\mathcal{M}, s \models \varphi \leftrightarrow \psi &\iff \mathcal{M}, s \models \varphi \text{ exactly when } \mathcal{M}, s \models \psi,\\
\mathcal{M}, s \models \forall x\, \varphi &\iff \mathcal{M}, s[x \mapsto a] \models \varphi \text{ for every } a \in M,\\
\mathcal{M}, s \models \exists x\, \varphi &\iff \mathcal{M}, s[x \mapsto a] \models \varphi \text{ for some } a \in M.
\end{aligned}
$$

The definition interprets object-level quantifiers by quantifiers of the metalanguage. This is not circular, since it reduces the truth of a formula to mathematical facts about $\mathcal{M}$.

Two lemmas make the definition usable. The proofs are Exercises 7 and 8.

Lemma (coincidence). If $s$ and $s'$ agree on $\mathrm{FV}(\varphi)$, then $\mathcal{M}, s \models \varphi$ if and only if $\mathcal{M}, s' \models \varphi$. In particular, the truth of a sentence does not depend on $s$, and we write $\mathcal{M} \models \varphi$.

Lemma (substitution). $\mathcal{M}, s \models \varphi[u/x]$ if and only if $\mathcal{M}, s[x \mapsto u^{\mathcal{M}, s}] \models \varphi$.

The substitution lemma says that syntactic substitution matches semantic update of the assignment. Every verification condition generator relies on this fact, since a Hoare assignment rule substitutes a term for a program variable.

Isomorphism. An isomorphism from $\mathcal{M}$ to $\mathcal{N}$ is a bijection $h : M \to N$ that preserves all functions and relations, in both directions for relations. Isomorphic structures satisfy the same sentences, by induction on formulas (Exercise 9). So first-order logic cannot separate structures that differ only in the names of their elements.

### Validity and entailment

The definitions lift those of propositional logic.

| Term | Definition |
|---|---|
| $\varphi$ is satisfiable | Some structure and assignment satisfy $\varphi$. |
| $\varphi$ is valid, written $\models \varphi$ | Every structure and every assignment satisfy $\varphi$. |
| $\mathcal{M}$ is a model of sentence $\varphi$ | $\mathcal{M} \models \varphi$ holds. |
| $\Gamma \models \varphi$ | For every $\mathcal{M}$ and $s$, if $\mathcal{M}, s$ satisfies all of $\Gamma$, then $\mathcal{M}, s \models \varphi$. |
| $\varphi \equiv \psi$ | For every $\mathcal{M}$ and $s$, the two formulas have the same truth value. |

So $\varphi$ is valid if and only if its universal closure is valid, and $\varphi$ is satisfiable if and only if its existential closure is satisfiable. The reductions $\Gamma \models \varphi$ iff $\Gamma \cup \{\neg\varphi\}$ is unsatisfiable, and $\Gamma, \varphi \models \psi$ iff $\Gamma \models \varphi \to \psi$, still hold with the definition above, by the same proofs as in the propositional case.

Some texts adopt a different convention: free variables in a premise are read as universally quantified. Then $P(x) \models \forall x\, P(x)$ holds. Under the definition used here, it does not, because a structure and assignment can make $P(x)$ true at one point only. This difference matters only for formulas with free variables, and you should check which convention a source uses.

Validity of a first-order formula quantifies over all structures, so truth tables do not apply. Church and Turing proved in 1936 that the problem is undecidable, as shown in [Undecidability of Logic and Incompleteness](../../02-decidability-and-complexity/undecidability-of-logic-and-incompleteness/). To show validity, argue semantically for an arbitrary structure, or use a proof system. To show non-validity, exhibit one countermodel.

Standard equivalences and non-equivalences. Assume $x \notin \mathrm{FV}(\psi)$ wherever $\psi$ is used.

| Statement | Status |
|---|---|
| $\neg \forall x\, \varphi \equiv \exists x\, \neg \varphi$ | This equivalence holds. |
| $\neg \exists x\, \varphi \equiv \forall x\, \neg \varphi$ | This equivalence holds. |
| $\forall x\, (\varphi_1 \land \varphi_2) \equiv \forall x\, \varphi_1 \land \forall x\, \varphi_2$ | This equivalence holds. |
| $\exists x\, (\varphi_1 \lor \varphi_2) \equiv \exists x\, \varphi_1 \lor \exists x\, \varphi_2$ | This equivalence holds. |
| $\forall x\, \forall y\, \varphi \equiv \forall y\, \forall x\, \varphi$ and $\exists x\, \exists y\, \varphi \equiv \exists y\, \exists x\, \varphi$ | These equivalences hold. |
| $\forall x\, (\psi \lor \varphi) \equiv \psi \lor \forall x\, \varphi$ | This equivalence holds. |
| $\exists x\, (\psi \land \varphi) \equiv \psi \land \exists x\, \varphi$ | This equivalence holds. |
| $\forall x\, \varphi_1 \lor \forall x\, \varphi_2 \models \forall x\, (\varphi_1 \lor \varphi_2)$ | This entailment holds, and its converse fails. |
| $\exists x\, (\varphi_1 \land \varphi_2) \models \exists x\, \varphi_1 \land \exists x\, \varphi_2$ | This entailment holds, and its converse fails. |
| $\exists x\, \forall y\, \varphi \models \forall y\, \exists x\, \varphi$ | This entailment holds, and its converse fails. |

### Formalization patterns

Most formalization errors come from a few patterns, and these are the correct forms. Here $S$ and $T$ are predicates.

| English | Formula |
|---|---|
| All $S$ are $T$. | $\forall x\, (S(x) \to T(x))$ |
| Some $S$ is $T$. | $\exists x\, (S(x) \land T(x))$ |
| No $S$ is $T$. | $\forall x\, (S(x) \to \neg T(x))$ |
| Only $S$ are $T$. | $\forall x\, (T(x) \to S(x))$ |
| There are at least two $S$. | $\exists x\, \exists y\, (x \neq y \land S(x) \land S(y))$ |
| There is at most one $S$. | $\forall x\, \forall y\, (S(x) \land S(y) \to x = y)$ |
| There is exactly one $S$. | $\exists x\, (S(x) \land \forall y\, (S(y) \to y = x))$ |

Universals pair with $\to$, and existentials pair with $\land$. The reason lies in the semantics. A formula $\exists x\, (S(x) \to T(x))$ is made true by any element outside $S$, so it says almost nothing, and $\forall x\, (S(x) \land T(x))$ says that everything is in both $S$ and $T$.

Many-sorted logic. Practical languages partition the domain into sorts, such as `Int` and `Array` in SMT-LIB, with each symbol given a sorted signature. Many-sorted logic reduces to the one-sorted version by adding a unary predicate per sort and guarding each quantifier. So the theorems of this chapter carry over. It is the logic you will actually type into a solver.

### Evaluating a formula in a structure

For a finite structure, the semantics is directly an algorithm:

```text
function HOLDS(M, s, φ):
    case φ of
        ⊤: return true
        ⊥: return false
        P(t1, ..., tn): return (VAL(M, s, t1), ..., VAL(M, s, tn)) ∈ P^M
        t1 = t2: return VAL(M, s, t1) = VAL(M, s, t2)
        ¬ψ: return not HOLDS(M, s, ψ)
        ψ1 ∧ ψ2: return HOLDS(M, s, ψ1) and HOLDS(M, s, ψ2)
        ψ1 ∨ ψ2: return HOLDS(M, s, ψ1) or HOLDS(M, s, ψ2)
        ψ1 → ψ2: return (not HOLDS(M, s, ψ1)) or HOLDS(M, s, ψ2)
        ψ1 ↔ ψ2: return HOLDS(M, s, ψ1) = HOLDS(M, s, ψ2)
        ∀x ψ: return true if HOLDS(M, s[x ↦ a], ψ) for all a in M, otherwise false
        ∃x ψ: return true if HOLDS(M, s[x ↦ a], ψ) for some a in M, otherwise false
```

The cost is polynomial in $|M|$ for a fixed formula, with exponent bounded by the quantifier depth. When the formula is part of the input, the problem is PSPACE-complete, as discussed in [Space and the Polynomial Hierarchy](../../02-decidability-and-complexity/space-and-the-polynomial-hierarchy/).

To evaluate by hand, start with the outermost quantifier and treat it as a game. For $\forall$, you must check each element, and one failing element is a counterexample. For $\exists$, one witness is enough, and showing falsity requires checking each element. In an infinite structure, use mathematical reasoning. There is no general algorithm: truth in $(\mathbb{N}, +, \cdot)$ is undecidable.

## Worked examples

### Example 1: formalizing requirements

Use the signature with unary predicates $\mathit{Req}$ (request), $\mathit{Srv}$ (server) and $\mathit{Adm}$ (administrator), and binary predicates $H(r, s)$ ($s$ handles $r$) and $\mathit{Del}(u, o)$ ($u$ deleted $o$).

"Every request is handled by exactly one server."

$$
\forall r\, \big(\mathit{Req}(r) \to \exists s\, (\mathit{Srv}(s) \land H(r, s) \land \forall t\, (\mathit{Srv}(t) \land H(r, t) \to t = s))\big)
$$

The inner $\forall t$ expresses uniqueness, and it has to lie inside the scope of $s$ so that it can refer to $s$.

"No server handles every request."

$$
\neg \exists s\, \big(\mathit{Srv}(s) \land \forall r\, (\mathit{Req}(r) \to H(r, s))\big)
$$

An equivalent form obtained from the equivalences is $\forall s\, (\mathit{Srv}(s) \to \exists r\, (\mathit{Req}(r) \land \neg H(r, s)))$.

"Only administrators delete anything."

$$
\forall u\, \forall o\, (\mathit{Del}(u, o) \to \mathit{Adm}(u))
$$

A check against small models. To test the third formula, build one structure with an element $u$ that is not an administrator and has no deletions: the formula should hold. Then add one deletion by $u$: the formula should fail. Testing candidate formulas on small structures in this way catches most errors of direction.

### Example 2: evaluating sentences in a finite graph

Let the signature contain a binary predicate $E$. Let $\mathcal{G}$ have domain $\{1, 2, 3\}$ and $E^{\mathcal{G}} = \{(1,2), (2,3), (3,1), (1,3)\}$.

Sentence A: $\forall x\, \exists y\, E(x, y)$. Each element needs a successor.

```text
x = 1: y = 2 works, since (1,2) ∈ E
x = 2: y = 3 works, since (2,3) ∈ E
x = 3: y = 1 works, since (3,1) ∈ E
result: true
```

Sentence B: $\exists y\, \forall x\, E(x, y)$. Some element must have every element, including itself, as a predecessor.

```text
y = 1: x = 1 fails, since (1,1) ∉ E
y = 2: x = 2 fails, since (2,2) ∉ E
y = 3: x = 3 fails, since (3,3) ∉ E
result: false
```

The pair A and B shows that the order of the quantifiers matters. Sentence A is true and sentence B is false in the same structure.

Sentence C: $\forall x\, \forall y\, (E(x, y) \to \exists z\, (E(y, z) \land E(z, x)))$. Every edge lies on a directed triangle. Only pairs with $E(x, y)$ need checking, because the implication holds otherwise.

```text
(x, y) = (1, 2): z = 3 works, since (2,3) ∈ E and (3,1) ∈ E
(x, y) = (2, 3): z = 1 works, since (3,1) ∈ E and (1,2) ∈ E
(x, y) = (3, 1): z = 2 works, since (1,2) ∈ E and (2,3) ∈ E
(x, y) = (1, 3): need z with (3,z) ∈ E and (z,1) ∈ E
    the only z with (3,z) ∈ E is z = 1
    (1,1) ∉ E, so no z works
result: false, with counterexample x = 1, y = 3
```

### Example 3: evaluating in arithmetic

Let $\mathcal{N} = (\mathbb{N}, 0, 1, +, \cdot, <)$ be the standard structure of arithmetic. The relation of divisibility and the set of primes are definable:

$$
x \mid y \;:=\; \exists z\, (x \cdot z = y), \qquad \mathrm{Prime}(x) \;:=\; 1 < x \land \forall y\, (y \mid x \to y = 1 \lor y = x).
$$

The sentence $\forall x\, \exists y\, (x < y \land \mathrm{Prime}(y))$ is true in $\mathcal{N}$. This is Euclid's theorem that the primes are unbounded.

The sentence $\forall x\, \exists y\, (x < y \land \mathrm{Prime}(y) \land \mathrm{Prime}(y + 1 + 1))$ is the twin prime conjecture. It has a definite truth value in $\mathcal{N}$ by Tarski's definition, and it is an open problem. So the definition of truth gives no method of evaluation for infinite structures.

The same sentence can have different values in different structures. Using the signature with $<$ alone:

| Sentence | $(\mathbb{N}, <)$ | $(\mathbb{Z}, <)$ | $(\mathbb{Q}, <)$ |
|---|---|---|---|
| $\forall x\, \exists y\, x < y$ | True | True | True |
| $\forall x\, \exists y\, y < x$ | False | True | True |
| $\exists x\, \forall y\, \neg(y < x)$ | True | False | False |
| $\forall x\, \forall y\, (x < y \to \exists z\, (x < z \land z < y))$ | False | False | True |

### Example 4: capture and its consequence

Let $\varphi(x)$ be $\exists y\, x < y$, which says that $x$ is not maximal. Over $(\mathbb{N}, <)$, $\varphi(x)$ holds of every element. We want to express this of the value of the variable $y$.

The incorrect, capturing replacement gives $\exists y\, y < y$, which is false in $(\mathbb{N}, <)$ under every assignment.

The correct substitution renames first: $\varphi[y/x] = \exists z\, y < z$. This is true in $(\mathbb{N}, <)$ under every assignment, consistent with the substitution lemma: $\mathcal{N}, s \models \exists z\, y < z$ iff $\mathcal{N}, s[x \mapsto s(y)] \models \exists y\, x < y$.

### Example 5: proving validity and refuting it

Claim: $\exists x\, \forall y\, R(x, y) \models \forall y\, \exists x\, R(x, y)$. Let $\mathcal{M}$ satisfy the left side, with witness $a$. So $(a, b) \in R^{\mathcal{M}}$ for all $b \in M$. For any $b$, the element $a$ is a witness for $\exists x\, R(x, b)$. So the right side holds.

The converse fails. Take $M = \{0, 1\}$ with $R^{\mathcal{M}}$ the equality relation. Every $y$ has the witness $x = y$, so $\forall y\, \exists x\, R(x, y)$ is true. No element is related to both $0$ and $1$, so $\exists x\, \forall y\, R(x, y)$ is false.

Claim (drinker formula): $\exists x\, (P(x) \to \forall y\, P(y))$ is valid. This surprises many readers, since it seems to say that someone's drinking causes everyone to drink. Let $\mathcal{M}$ be any structure. If every element is in $P^{\mathcal{M}}$, then pick any element, which exists because domains are nonempty. The consequent is true, so the implication is true. Otherwise, pick $a \notin P^{\mathcal{M}}$. The antecedent is false at $a$, so the implication is true. In both cases a witness exists.

## Common mistakes

- Writing $\exists x\, (S(x) \to T(x))$ for "some $S$ is $T$". This is true whenever some element is outside $S$. Use $\exists x\, (S(x) \land T(x))$.
- Writing $\forall x\, (S(x) \land T(x))$ for "all $S$ are $T$". This requires everything to be both. Use $\forall x\, (S(x) \to T(x))$.
- Swapping quantifiers. The statement $\forall x\, \exists y\, \varphi$ allows $y$ to depend on $x$, and $\exists y\, \forall x\, \varphi$ requires one $y$ for all $x$.
- Reading $\forall x\, P(x) \to Q(x)$ with the wrong scope. In this program, it means $(\forall x\, P(x)) \to Q(x)$, where the last $x$ is free. Some books let a quantifier extend as far to the right as possible, so check the convention of each source, and use parentheses when in doubt.
- Substituting into a formula without renaming, which captures a variable. Check the bound variables of the formula against the variables of the term.
- Confusing a predicate symbol with a relation and a term with an element. A symbol has meaning only relative to a structure. For example, $x + y = y + x$ is not valid, since a structure can interpret $+$ as any binary function. It holds in particular structures and theories.
- Writing a function where a predicate is required, or the reverse. In $P(f(x))$, $f(x)$ is a term and $P(f(x))$ is a formula. The expression $f(P(x))$ is not well formed, and $\neg f(x)$ is not well formed.
- Treating $=$ as an ordinary predicate. With its fixed meaning, $x = x$ is valid. If $=$ were an ordinary binary predicate, it would not be valid, and you would need the equality axioms given in [First-Order Theories](../first-order-theories/).
- Assuming that a satisfying structure must be a natural one. A formula such as $\forall x\, \exists y\, E(x, y)$ is satisfied by a one-element structure with a loop. If you intended more, then your formula must say more.
- Quantifying over sets or functions in a first-order formula, as in "for all subsets". That is second-order. Encode the set as an element of a set sort with a membership predicate, knowing that this only captures sets available in the structure.

## Exercises

### Exercise 1

Compute the free variables of $\forall x\, (P(x, y) \to \exists y\, Q(x, y, z)) \land R(x)$, and mark which occurrences of $x$ and $y$ are free.

<details><summary>Solution</summary>

In the first conjunct, $x$ is bound by $\forall x$. The $y$ in $P(x, y)$ is free. The $y$ in $Q(x, y, z)$ is bound by $\exists y$. The $z$ is free.

In the second conjunct, the $x$ in $R(x)$ is free, since it lies outside the scope of $\forall x$.

So $\mathrm{FV} = \{x, y, z\}$.

</details>

### Exercise 2

Compute: (a) $(\exists y\, P(x, y))[f(y)/x]$; (b) $(\forall x\, P(x, y))[c/x]$; (c) $(P(x) \land \exists x\, Q(x))[c/x]$; (d) $(\exists y\, P(x, y))[f(z)/x]$.

<details><summary>Solution</summary>

(a) The variable $y$ occurs in $f(y)$, so the bound $y$ must be renamed: $\exists z\, P(f(y), z)$ with $z$ fresh.

(b) The variable $x$ is not free, so the formula is unchanged: $\forall x\, P(x, y)$.

(c) Only the free occurrence changes: $P(c) \land \exists x\, Q(x)$.

(d) No capture occurs, since $y$ does not occur in $f(z)$: $\exists y\, P(f(z), y)$.

</details>

### Exercise 3

Formalize, with unary predicates $S$ (student), $C$ (course), and a binary predicate $T(x, y)$ for "$x$ takes $y$":

(a) Every student takes some course. (b) Some course is taken by every student. (c) No student takes every course. (d) Every course is taken by at least two students. (e) Only students take courses.

<details><summary>Solution</summary>

(a) $\forall x\, (S(x) \to \exists y\, (C(y) \land T(x, y)))$.

(b) $\exists y\, (C(y) \land \forall x\, (S(x) \to T(x, y)))$.

(c) $\neg \exists x\, (S(x) \land \forall y\, (C(y) \to T(x, y)))$.

(d) $\forall y\, (C(y) \to \exists x_1\, \exists x_2\, (x_1 \neq x_2 \land S(x_1) \land S(x_2) \land T(x_1, y) \land T(x_2, y)))$.

(e) $\forall x\, \forall y\, (C(y) \land T(x, y) \to S(x))$.

</details>

### Exercise 4

Let $\mathcal{M}$ have domain $\{0, 1, 2\}$, with $f(x) = (x + 1) \bmod 3$ and $P^{\mathcal{M}} = \{0\}$. Evaluate:

(a) $\forall x\, \exists y\, f(y) = x$; (b) $\exists x\, f(x) = x$; (c) $\forall x\, (P(x) \to \neg P(f(x)))$; (d) $\exists x\, \exists y\, (x \neq y \land P(x) \land P(y))$; (e) $\forall x\, (P(f(f(f(x)))) \leftrightarrow P(x))$; (f) $\forall x\, \exists y\, (y \neq x \land f(f(y)) = x)$.

<details><summary>Solution</summary>

(a) True. For $x = 0, 1, 2$, take $y = 2, 0, 1$.

(b) False. We have $f(0) = 1$, $f(1) = 2$, $f(2) = 0$, with no fixed point.

(c) True. The only element of $P$ is $0$, and $f(0) = 1 \notin P$.

(d) False. The set $P$ has one element.

(e) True. Applying $f$ three times gives the identity on this domain.

(f) True. The equation $f(f(y)) = x$ means $y + 2 \equiv x \pmod 3$, which gives $y \equiv x + 1 \pmod 3$. This $y$ differs from $x$.

</details>

### Exercise 5

Write a sentence with $=$ only, whose models are exactly the structures with three elements. Then write a sentence with one unary function symbol $f$, all of whose models are infinite, and prove that it has that property.

<details><summary>Solution</summary>

For exactly three elements:

$$
\exists x\, \exists y\, \exists z\, (x \neq y \land x \neq z \land y \neq z \land \forall w\, (w = x \lor w = y \lor w = z)).
$$

For infinite models, let $f$ be injective and not surjective:

$$
\forall x\, \forall y\, (f(x) = f(y) \to x = y) \land \exists y\, \forall x\, f(x) \neq y.
$$

Suppose a model has a finite domain. An injective function from a finite set to itself is surjective, by the pigeonhole principle, and this contradicts the second conjunct. So every model is infinite. A model exists: $\mathbb{N}$ with $f(n) = n + 1$.

</details>

### Exercise 6

Decide which of the following are valid. Give a proof or a countermodel.

(a) $\forall x\, (P(x) \lor Q(x)) \to \forall x\, P(x) \lor \forall x\, Q(x)$; (b) $\exists x\, P(x) \land \exists x\, Q(x) \to \exists x\, (P(x) \land Q(x))$; (c) $\forall x\, P(x) \to \exists x\, P(x)$; (d) $(\forall x\, (P(x) \to Q(x))) \to (\forall x\, P(x) \to \forall x\, Q(x))$; (e) $(\forall x\, P(x) \to \forall x\, Q(x)) \to \forall x\, (P(x) \to Q(x))$.

<details><summary>Solution</summary>

(a) Not valid. Take $M = \{0, 1\}$, $P = \{0\}$, $Q = \{1\}$. The antecedent holds, and neither disjunct does.

(b) Not valid. The same structure satisfies both existentials and has no element in both.

(c) Valid. The domain has an element $a$, and $\forall x\, P(x)$ gives $a \in P$, so $\exists x\, P(x)$.

(d) Valid. Assume both antecedents and let $a$ be any element. Then $a \in P$, so $a \in Q$.

(e) Not valid. Take $M = \{0, 1\}$, $P = \{0\}$, $Q = \emptyset$. Since $\forall x\, P(x)$ is false, the antecedent holds. But $P(0) \to Q(0)$ is false.

</details>

### Exercise 7

Prove the coincidence lemma.

<details><summary>Solution</summary>

First, for terms: if $s$ and $s'$ agree on the variables of $t$, then $t^{\mathcal{M}, s} = t^{\mathcal{M}, s'}$. This follows by induction on $t$.

Now use induction on $\varphi$, for all $s$ and $s'$ at once. Atoms follow from the term case. Connectives follow from the induction hypothesis, since the free variables of the parts are among those of the whole.

Let $\varphi = \forall x\, \psi$, with $s$ and $s'$ agreeing on $\mathrm{FV}(\psi) \setminus \{x\}$. For any $a$, $s[x \mapsto a]$ and $s'[x \mapsto a]$ agree on $\mathrm{FV}(\psi)$. By the hypothesis, $\mathcal{M}, s[x \mapsto a] \models \psi$ iff $\mathcal{M}, s'[x \mapsto a] \models \psi$. So $\mathcal{M}, s \models \forall x\, \psi$ iff $\mathcal{M}, s' \models \forall x\, \psi$. The case of $\exists$ is the same.

</details>

### Exercise 8

Prove the substitution lemma. Treat terms, atoms, and the quantifier case including renaming.

<details><summary>Solution</summary>

Let $a = u^{\mathcal{M}, s}$ and $s^* = s[x \mapsto a]$.

Terms. We show $t[u/x]^{\mathcal{M}, s} = t^{\mathcal{M}, s^*}$ by induction on $t$. For $t = x$, both are $a$. For a variable $y \neq x$, both are $s(y)$. For $f(t_1, \dots, t_n)$, apply the hypothesis to each argument.

Atoms and connectives follow from the term case and the induction hypothesis.

Quantifier. Use induction on the number of connectives and quantifiers in $\varphi$, for all $s$, $u$ and $x$, since renaming changes the formula but not this number. Let $\varphi = \forall y\, \psi$.

Case 1: $x = y$ or $x \notin \mathrm{FV}(\psi)$. Then $\varphi[u/x] = \varphi$, and $x \notin \mathrm{FV}(\varphi)$. By the coincidence lemma, $\mathcal{M}, s \models \varphi$ iff $\mathcal{M}, s^* \models \varphi$.

Case 2: $x \neq y$, $x \in \mathrm{FV}(\psi)$ and $y \notin \mathrm{FV}(u)$. Let $b \in M$. Since $y$ does not occur in $u$, the value of $u$ under $s[y \mapsto b]$ is $a$. By the hypothesis, $\mathcal{M}, s[y \mapsto b] \models \psi[u/x]$ iff $\mathcal{M}, s[y \mapsto b][x \mapsto a] \models \psi$. Since $x \neq y$, the last assignment is $s^*[y \mapsto b]$. Quantifying over $b$ gives the result.

Case 3: the renaming case, with $\varphi[u/x] = \forall z\, (\psi[z/y][u/x])$ and $z$ fresh. Let $b \in M$. Since $z$ is not in $u$, the value of $u$ under $s[z \mapsto b]$ is $a$. By the hypothesis applied twice,

$$
\mathcal{M}, s[z \mapsto b] \models \psi[z/y][u/x]
\iff \mathcal{M}, s[z \mapsto b][x \mapsto a] \models \psi[z/y]
\iff \mathcal{M}, s[z \mapsto b][x \mapsto a][y \mapsto b] \models \psi.
$$

Since $z$ does not occur in $\psi$, the coincidence lemma removes the update of $z$, which leaves $\mathcal{M}, s^*[y \mapsto b] \models \psi$. Quantifying over $b$ gives the result. The case of $\exists$ is the same.

</details>

### Exercise 9

(a) Prove that if $h$ is an isomorphism from $\mathcal{M}$ to $\mathcal{N}$, then $\mathcal{M}, s \models \varphi$ iff $\mathcal{N}, h \circ s \models \varphi$. (b) Use this to prove that in $(\mathbb{Z}, <)$, the only subsets of $\mathbb{Z}$ definable by a formula with one free variable are $\emptyset$ and $\mathbb{Z}$.

<details><summary>Solution</summary>

(a) For terms, $h(t^{\mathcal{M}, s}) = t^{\mathcal{N}, h \circ s}$, by induction on $t$, since $h$ preserves functions. Atoms follow, since $h$ preserves relations in both directions and is injective, which handles $=$. Connectives are immediate. For $\forall x\, \psi$, the condition for $\mathcal{M}$ is that $\mathcal{M}, s[x \mapsto a] \models \psi$ for every $a \in M$. By the hypothesis this is $\mathcal{N}, (h \circ s)[x \mapsto h(a)] \models \psi$ for every $a$. Since $h$ is surjective, $h(a)$ ranges over all of $N$.

(b) Let $D$ be defined by $\varphi(x)$, and let $a, b \in \mathbb{Z}$. The map $h(n) = n + (b - a)$ is an isomorphism from $(\mathbb{Z}, <)$ to itself, and $h(a) = b$. By (a), $a \in D$ iff $b \in D$. So $D$ contains all integers or none. In particular, the element $0$ cannot be defined in $(\mathbb{Z}, <)$.

</details>

### Exercise 10

Show the following definability facts. (a) In $(\mathbb{N}, +)$, the elements $0$ and $1$ and the relation $<$ are definable. (b) In $(\mathbb{R}, +, \cdot)$, the relation $\leq$ is definable. (c) Use the method of Exercise 9 to show that $<$ is not definable in $(\mathbb{Z}, +)$.

<details><summary>Solution</summary>

(a) The element $0$ is defined by $x + x = x$. The relation $x < y$ is defined by $\exists z\, (\neg(z + z = z) \land x + z = y)$. The element $1$ is the least nonzero element, defined by $\neg(x + x = x) \land \forall y\, (\neg(y + y = y) \to \neg (y < x))$, where $y < x$ is expanded as above.

(b) $x \leq y$ is defined by $\exists z\, (y = x + z \cdot z)$, since nonnegative reals are exactly the squares.

(c) The map $h(n) = -n$ is an isomorphism from $(\mathbb{Z}, +)$ to itself, since $-(a + b) = (-a) + (-b)$. Suppose a formula $\varphi(x, y)$ defines $<$. Since $0 < 1$, part (a) of Exercise 9 gives that $\varphi$ also holds of $h(0) = 0$ and $h(1) = -1$, so $0 < -1$, which is false.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define signature, term, formula, free variable, capture-avoiding substitution, structure and satisfaction.
- State the coincidence and substitution lemmas, and prove them by induction.
- Formalize an English requirement with correct quantifier pairing and test the formula on small structures.
- Evaluate a sentence in a finite structure by a full hand trace, and in an infinite structure by mathematical reasoning.
- Prove a first-order validity semantically, and refute a non-validity with a countermodel.
- Prove that a set or relation is not definable, using an automorphism.

## Materials

- Huth and Ryan, Logic in Computer Science, 2nd edition. Read the predicate logic chapter for the need for a richer language, for the semantics, and for further examples of formalization.
- Enderton, A Mathematical Introduction to Logic, 2nd edition. Read the first-order logic chapter on first-order languages and on truth and models for the rigorous development, including definability in a structure.
