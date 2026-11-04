# Normal Forms and Skolemization

Part 1, Chapter 1: Mathematical Logic.

## Objective

Convert formulas to negation, prenex, conjunctive and Skolem normal forms and state what each conversion preserves.

## Why this matters

Reasoning engines accept restricted input. A SAT solver expects clauses, a first-order prover expects Skolemized clauses, and quantifier instantiation in an SMT solver works on formulas without existential quantifiers in positive positions. So every practical pipeline starts with a normal form conversion, and the choice of conversion affects the size of the problem and the meaning of the answer. If you confuse equivalence with equisatisfiability, you may read a model that means nothing, or claim validity from a transformation that preserves only satisfiability. This topic prepares you for [Encodings](../../../part-2-core-reasoning/04-sat/encodings/), [First-Order Resolution](../../../part-2-core-reasoning/06-first-order-proving/first-order-resolution/) and Herbrand's theorem in [First-Order Metatheory](../first-order-metatheory/).

## Prerequisites

- [Propositional Logic](../propositional-logic/)
- [Proof Systems](../proof-systems/)
- [First-Order Logic](../first-order-logic/)

## Lesson

### What a conversion may preserve

There are four useful levels of preservation, from strongest to weakest. Let $\varphi'$ be the result of converting $\varphi$.

1. Equivalence: $\varphi' \equiv \varphi$, so $\varphi'$ can replace $\varphi$ in any context.
2. Extension of models: every model of $\varphi$ extends to a model of $\varphi'$ by interpreting the new symbols, and every model of $\varphi'$ restricts to a model of $\varphi$.
3. Satisfiability only: $\varphi'$ is satisfiable if and only if $\varphi$ is.
4. Validity only: $\varphi'$ is valid if and only if $\varphi$ is.

Levels 2 and 3 suit refutation-based tools. They let you decide whether $\varphi$ is satisfiable, and level 2 also lets you read a model of $\varphi$ from a model of $\varphi'$. Neither level lets you replace $\varphi$ with $\varphi'$ in a larger formula, and neither preserves validity. To decide whether $\varphi$ is valid, convert $\neg\varphi$ and test for unsatisfiability.

The following table is the summary to remember. The rest of this topic justifies it.

| Conversion | What it preserves | Size |
|---|---|---|
| Negation normal form | It preserves equivalence. | The growth is linear without $\leftrightarrow$, and can be exponential with $\leftrightarrow$ expanded in a tree. |
| CNF or DNF by distribution | It preserves equivalence. | The growth can be exponential. |
| Tseitin transformation | It preserves satisfiability, with a bijection between models. | The growth is linear. |
| Plaisted-Greenbaum transformation | It preserves satisfiability, with every model restricting to a model of the original. | The growth is linear, with fewer clauses than Tseitin. |
| Prenex normal form | It preserves equivalence. | The growth is linear without $\leftrightarrow$. |
| Skolemization | It preserves satisfiability, and the result entails the original. | The growth is small, although Skolem terms may repeat. |
| Herbrandization | It preserves validity, and the original entails the result. | The growth is small, although Herbrand terms may repeat. |
| Clause form of a universal sentence | It preserves equivalence if the clauses are read with universal closure. | The growth can be exponential by distribution. |

### Negation normal form

A formula is in negation normal form (NNF) if it is built from literals, or first-order literals (atoms and negated atoms), and $\top$, $\bot$, using only $\land$, $\lor$, and the quantifiers. So $\to$ and $\leftrightarrow$ do not occur, and negation applies only to atoms.

The conversion has two steps. First eliminate $\to$ and $\leftrightarrow$. Then push negations inward with these equivalences:

$$
\begin{aligned}
\neg\neg\varphi &\equiv \varphi, & \neg(\varphi \land \psi) &\equiv \neg\varphi \lor \neg\psi, & \neg(\varphi \lor \psi) &\equiv \neg\varphi \land \neg\psi,\\
\neg\forall x\, \varphi &\equiv \exists x\, \neg\varphi, & \neg\exists x\, \varphi &\equiv \forall x\, \neg\varphi, & \neg\top &\equiv \bot, \qquad \neg\bot \equiv \top.
\end{aligned}
$$

Each step is an equivalence, so the result is equivalent to the input by the replacement property. The procedure terminates because the total size of the subformulas under negations decreases at each step.

The formula $\varphi \leftrightarrow \psi$ expands into a formula with two copies of each of $\varphi$ and $\psi$, so nested biconditionals can cause exponential growth when written as a tree. The other connectives cause at most linear growth.

Polarity. An occurrence of a subformula is positive if it lies under an even number of negations, counting the antecedent of $\to$ as one negation, and negative if under an odd number. Both sides of $\leftrightarrow$ count as both polarities. NNF makes polarity visible: after conversion, all surviving atoms are positive if unnegated and negative if negated. Polarity reappears below in both Plaisted-Greenbaum and Skolemization.

### Disjunctive and conjunctive normal forms

A term is a conjunction of literals, and a clause is a disjunction of literals. A formula is in disjunctive normal form (DNF) if it is a disjunction of terms, and in conjunctive normal form (CNF) if it is a conjunction of clauses. The empty disjunction is $\bot$, and the empty conjunction is $\top$.

Every propositional formula has both. There are two standard methods.

From a truth table. The DNF has one term for each row with value $1$. The CNF has one clause for each row with value $0$, namely the clause that is false exactly on that row.

By distribution. Convert to NNF, then repeatedly apply:

$$
\varphi \lor (\psi \land \chi) \equiv (\varphi \lor \psi) \land (\varphi \lor \chi).
$$

Distribution duplicates $\varphi$, and the growth can be exponential. The DNF formula

$$
(x_1 \land x_2) \lor (x_3 \land x_4) \lor \dots \lor (x_{2n-1} \land x_{2n})
$$

has $2n$ literals, and its shortest equivalent CNF has $2^n$ clauses (Exercise 8). This is why solvers do not use distribution on large formulas.

Checking validity of a CNF and satisfiability of a DNF are easy. A clause is valid if and only if it contains complementary literals, and a term is satisfiable if and only if it does not. So converting to DNF would solve SAT in linear time in the size of the output, and the difficulty has moved into the conversion. CNF keeps the hard problem, satisfiability, and represents it compactly.

### The Tseitin transformation

Tseitin introduced this transformation in work published in 1968. The idea is to name each subformula with a new variable, in order to avoid duplication.

Let $\varphi$ be a propositional formula. Assume that it is written with $\neg$ and binary connectives. For each non-atomic subformula $\psi$, take a fresh variable $n_\psi$. For an atom $\alpha$, let $n_\alpha$ stand for $\alpha$. Then define

$$
\mathrm{Def}(\psi) =
\begin{cases}
n_\psi \leftrightarrow \neg n_\alpha & \text{if } \psi = \neg\alpha,\\
n_\psi \leftrightarrow (n_\alpha \circ n_\beta) & \text{if } \psi = \alpha \circ \beta,
\end{cases}
$$

and let $T(\varphi)$ be the clauses of all $\mathrm{Def}(\psi)$, together with the unit clause $\{n_\varphi\}$. These are the clause patterns.

| Definition | Clauses |
|---|---|
| $n \leftrightarrow \neg a$ | $\{\neg n, \neg a\}$, $\{n, a\}$ |
| $n \leftrightarrow (a \land b)$ | $\{\neg n, a\}$, $\{\neg n, b\}$, $\{n, \neg a, \neg b\}$ |
| $n \leftrightarrow (a \lor b)$ | $\{\neg n, a, b\}$, $\{n, \neg a\}$, $\{n, \neg b\}$ |
| $n \leftrightarrow (a \to b)$ | $\{\neg n, \neg a, b\}$, $\{n, a\}$, $\{n, \neg b\}$ |
| $n \leftrightarrow (a \leftrightarrow b)$ | $\{\neg n, \neg a, b\}$, $\{\neg n, a, \neg b\}$, $\{n, a, b\}$, $\{n, \neg a, \neg b\}$ |

Theorem. Every assignment $v$ to the variables of $\varphi$ has exactly one extension $v^*$ to the new variables that satisfies all the definitions. It satisfies $v^*(n_\psi) = v(\psi)$ for each subformula $\psi$. So $v^*$ satisfies $T(\varphi)$ if and only if $v$ satisfies $\varphi$, and the models of $T(\varphi)$ are in bijection with the models of $\varphi$.

Proof. Use induction on subformulas. For an atom the claim is immediate. For $\psi = \alpha \circ \beta$, the definition forces $v^*(n_\psi) = v^*(n_\alpha) \circ v^*(n_\beta)$, which is $v(\alpha) \circ v(\beta) = v(\psi)$ by the induction hypothesis. So the extension exists and is unique, and every model of the definitions has this form. Adding $\{n_\varphi\}$ requires that $v(\varphi) = 1$. $\square$

Corollary. $T(\varphi)$ has at most $4 m + 1$ clauses of at most three literals each, where $m$ is the number of connectives in $\varphi$. So the transformation is linear, and it takes SAT for arbitrary formulas to 3-SAT in linear time.

The result is not equivalent to $\varphi$, since it mentions new variables. For example, $x_1 \lor \neg x_1$ is valid, and its transformation is not valid, because setting all variables to false falsifies the unit clause. To check validity, apply the transformation to the negation.

### The Plaisted-Greenbaum transformation

Plaisted and Greenbaum observed in 1986 that half of each definition is often unnecessary. If a subformula occurs only positively, then it is enough to know that $n_\psi$ implies $\psi$. If only negatively, then it is enough to know that $\psi$ implies $n_\psi$. Only the corresponding clauses are generated. For $\leftrightarrow$ both polarities occur, so both directions are kept.

Theorem. $\varphi$ is satisfiable if and only if its Plaisted-Greenbaum transformation $\mathrm{PG}(\varphi)$ is satisfiable. Moreover, every model of $\mathrm{PG}(\varphi)$ restricts to a model of $\varphi$.

The proof is Exercise 10. Unlike Tseitin, the extension of a model is not unique. This does not affect SAT solving, and it does affect model counting, as Example 1 shows.

### Prenex normal form

A first-order formula is in prenex normal form if it has the form $Q_1 x_1 \dots Q_k x_k\, \mu$, where each $Q_i$ is a quantifier and $\mu$, the matrix, is quantifier-free.

To convert, first rectify the formula: rename bound variables so that all quantifiers bind distinct variables, and no variable occurs both free and bound. Eliminate $\leftrightarrow$, which has occurrences of both polarities. Then pull quantifiers outward with the following equivalences, where $x \notin \mathrm{FV}(\psi)$, which rectification guarantees:

$$
\begin{aligned}
(\forall x\, \varphi) \land \psi &\equiv \forall x\, (\varphi \land \psi), & (\exists x\, \varphi) \land \psi &\equiv \exists x\, (\varphi \land \psi),\\
(\forall x\, \varphi) \lor \psi &\equiv \forall x\, (\varphi \lor \psi), & (\exists x\, \varphi) \lor \psi &\equiv \exists x\, (\varphi \lor \psi),\\
(\forall x\, \varphi) \to \psi &\equiv \exists x\, (\varphi \to \psi), & (\exists x\, \varphi) \to \psi &\equiv \forall x\, (\varphi \to \psi),\\
\psi \to \forall x\, \varphi &\equiv \forall x\, (\psi \to \varphi), & \psi \to \exists x\, \varphi &\equiv \exists x\, (\psi \to \varphi),\\
\neg \forall x\, \varphi &\equiv \exists x\, \neg \varphi, & \neg \exists x\, \varphi &\equiv \forall x\, \neg \varphi.
\end{aligned}
$$

A quantifier in the antecedent of $\to$ flips, because the antecedent has negative polarity. Several of these rules rely on nonempty domains. For example, $(\forall x\, \varphi) \land \psi \equiv \forall x\, (\varphi \land \psi)$ would fail over an empty domain when $\psi$ is false.

Prenex form is not unique. In $(\exists x\, P(x)) \land (\forall y\, Q(y))$, you may pull out either quantifier first, getting $\exists x\, \forall y\, (P(x) \land Q(y))$ or $\forall y\, \exists x\, (P(x) \land Q(y))$. Both are correct. The first is better for Skolemization, as it gives a constant in place of a function. The rule of thumb is to pull existentials out first, when you are free to do so.

### Skolemization

Skolemization removes existential quantifiers by replacing each one with a function that gives a witness. It goes back to Skolem's 1920 work on Löwenheim's theorem. Let $\varphi$ be a sentence in prenex form, with outermost existential at position $i$:

$$
\varphi = \forall y_1 \dots \forall y_m\, \exists x\, \psi.
$$

Let $f$ be a fresh function symbol of arity $m$, which is a constant if $m = 0$. The Skolemization step gives

$$
\varphi' = \forall y_1 \dots \forall y_m\, \psi[f(y_1, \dots, y_m)/x].
$$

Repeat until no existential quantifier remains. The result $\mathrm{Sk}(\varphi)$ is a universal sentence, and this is what we mean by Skolem normal form. Older literature also uses the name for a function-free prefix form $\forall^* \exists^*$, which Skolem also studied. Check which meaning a source intends.

Lemma (one step). $\varphi' \models \varphi$, and $\varphi$ is satisfiable if and only if $\varphi'$ is. More precisely, each model of $\varphi$ can be expanded to a model of $\varphi'$ by interpreting $f$.

Proof. Assume $\mathcal{M} \models \varphi'$, and let $a_1, \dots, a_m \in M$. Let $b = f^{\mathcal{M}}(a_1, \dots, a_m)$. By the substitution lemma, $\psi$ holds with $y_i$ as $a_i$ and $x$ as $b$. So $\exists x\, \psi$ holds at $a_1, \dots, a_m$. Hence $\mathcal{M} \models \varphi$.

Conversely, assume $\mathcal{M} \models \varphi$. For each tuple $a_1, \dots, a_m$, choose a witness $b$ for $\exists x\, \psi$, and let $f(a_1, \dots, a_m) = b$. This uses the axiom of choice in general, and it needs no choice if $M$ can be well-ordered, in particular if $M$ is countable. The expansion of $\mathcal{M}$ with this function satisfies $\varphi'$, by the substitution lemma. $\square$

Theorem. Let $\varphi$ be a prenex sentence. Then (a) $\mathrm{Sk}(\varphi) \models \varphi$; (b) $\varphi$ is satisfiable if and only if $\mathrm{Sk}(\varphi)$ is; (c) every model of $\varphi$ expands to a model of $\mathrm{Sk}(\varphi)$; (d) for any sentence $\chi$ over the original signature, $\varphi \models \chi$ if and only if $\mathrm{Sk}(\varphi) \models \chi$.

Parts (a), (b) and (c) follow by iterating the lemma. Part (d), which says that the result is a conservative extension, is Exercise 9.

Skolemization preserves neither equivalence nor validity. The sentence $\exists x\, P(x)$ has a model in which $P$ holds of one element and $c$ names another, so it does not entail $P(c)$. Example 3 gives a valid sentence whose Skolemization is not valid. Skolemization is a tool for satisfiability, which is why provers apply it to the negation of the goal.

Polarity. Skolemization of formulas in NNF does not require prenex form. An existential in NNF can be replaced by a function of only the universally quantified variables that are free in that subformula. This is called inner or optimized Skolemization, and it gives smaller arities, as Example 2 shows. If the formula is not in NNF, an existential quantifier of negative polarity behaves as a universal quantifier, and must not be Skolemized directly.

Herbrandization. The dual operation for validity replaces each universal quantifier by a function of the preceding existential variables. Its result is valid if and only if the original is (Exercise 11).

### The full clause form pipeline

To decide whether a first-order sentence is satisfiable with a resolution prover, or to test $\Gamma \models \varphi$ by refuting $\Gamma \cup \{\neg\varphi\}$, apply these steps in order.

```text
1. Rectify: rename bound variables apart.
2. Eliminate ↔ and →.
3. Convert to negation normal form.
4. Skolemize, working from the outermost existential inward.
5. Drop the universal quantifiers, keeping the convention that clause variables are universal.
6. Convert the quantifier-free matrix to CNF by distribution or by naming.
7. Rename variables apart in each clause.
```

The result is a set of clauses, each read as its universal closure. Step 7 is sound because $\forall x\, (\varphi \land \psi) \equiv \forall x\, \varphi \land \forall x\, \psi$, so each clause has its own quantifier scope.

To avoid exponential growth in step 6, first-order provers use definitional CNF, the analogue of Tseitin. A subformula $\psi$ with free variables $y_1, \dots, y_k$ is named by a fresh predicate $N$ with the definition $\forall y_1 \dots \forall y_k\, (N(y_1, \dots, y_k) \leftrightarrow \psi)$, or only one direction of it, according to polarity. The proof is the same as before, with a choice of $N^{\mathcal{M}}$ in place of a choice of truth value.

## Worked examples

### Example 1: Tseitin and Plaisted-Greenbaum by hand

Convert $\varphi = (x_1 \land x_2) \lor \neg(x_3 \to x_4)$. Name the subformulas:

```text
x5 names x1 ∧ x2           polarity positive
x6 names x3 → x4           polarity negative
x7 names ¬x6               polarity positive
x8 names x5 ∨ x7           polarity positive
```

Tseitin produces all clauses of each definition:

```text
x5 ↔ x1 ∧ x2:   {¬x5, x1}  {¬x5, x2}  {x5, ¬x1, ¬x2}
x6 ↔ x3 → x4:   {¬x6, ¬x3, x4}  {x6, x3}  {x6, ¬x4}
x7 ↔ ¬x6:       {¬x7, ¬x6}  {x7, x6}
x8 ↔ x5 ∨ x7:   {¬x8, x5, x7}  {x8, ¬x5}  {x8, ¬x7}
root:           {x8}
```

This is 12 clauses. Plaisted-Greenbaum keeps only the implications in the direction given by the polarity. A positive name needs $n \to \psi$. A negative name needs $\psi \to n$.

```text
x5 → x1 ∧ x2:   {¬x5, x1}  {¬x5, x2}
(x3 → x4) → x6: {x6, x3}  {x6, ¬x4}
x7 → ¬x6:       {¬x7, ¬x6}
x8 → x5 ∨ x7:   {¬x8, x5, x7}
root:           {x8}
```

This is 7 clauses.

Compare the models. A brute-force count over $x_1, \dots, x_8$ confirms that $\varphi$ has 7 models over $x_1, \dots, x_4$, that the Tseitin clauses have 7 models, and that the Plaisted-Greenbaum clauses have 10 models. All of them restrict to models of $\varphi$. So both are equisatisfiable with $\varphi$, and only Tseitin preserves the number of models.

Compare distribution. By distribution, $\varphi$ first becomes $(x_1 \land x_2) \lor (x_3 \land \neg x_4)$, and then

$$
(x_1 \lor x_3) \land (x_1 \lor \neg x_4) \land (x_2 \lor x_3) \land (x_2 \lor \neg x_4).
$$

For a formula this small, distribution is shorter and needs no new variables. Naming pays off as nesting and size grow, as Exercise 8 shows.

### Example 2: the full first-order pipeline

Convert to clause form:

$$
\varphi = \forall x\, \big(P(x) \to \exists y\, (R(x, y) \land \neg \forall z\, (R(y, z) \to P(z)))\big).
$$

```text
Eliminate →:
    ∀x (¬P(x) ∨ ∃y (R(x, y) ∧ ¬∀z (¬R(y, z) ∨ P(z))))
Push negation inward (negation normal form):
    ∀x (¬P(x) ∨ ∃y (R(x, y) ∧ ∃z (R(y, z) ∧ ¬P(z))))
Prenex form (all bound variables are already distinct):
    ∀x ∃y ∃z (¬P(x) ∨ (R(x, y) ∧ R(y, z) ∧ ¬P(z)))
Skolemize, with y := f(x) and z := g(x), since each is in the scope of ∀x only:
    ∀x (¬P(x) ∨ (R(x, f(x)) ∧ R(f(x), g(x)) ∧ ¬P(g(x))))
Distribute ∨ over ∧ and drop the quantifier:
    {¬P(x), R(x, f(x))}
    {¬P(x), R(f(x), g(x))}
    {¬P(x), ¬P(g(x))}
```

A solver confirms that the prenex form is equivalent to $\varphi$, and that the Skolem form entails $\varphi$.

Inner Skolemization, applied to the NNF, gives a different result. The subformula $\exists z\, (R(y, z) \land \neg P(z))$ has $y$ as its only free variable, so $z$ can be replaced by $g(y)$. After $y$ is replaced by $f(x)$, this gives

$$
\forall x\, (\neg P(x) \lor (R(x, f(x)) \land R(f(x), g(f(x))) \land \neg P(g(f(x))))).
$$

This result is equisatisfiable with $\varphi$ too. Its function $g$ is unary either way, but it depends only on $y$, and in formulas with more universal quantifiers, inner Skolemization gives strictly smaller arities.

### Example 3: Skolemization does not preserve validity

The drinker formula $\exists x\, (P(x) \to \forall y\, P(y))$ is valid, as shown in [First-Order Logic](../first-order-logic/). Its prenex form is $\exists x\, \forall y\, (P(x) \to P(y))$. Its Skolemization is $\forall y\, (P(c) \to P(y))$, with a fresh constant $c$.

This is not valid. Take $M = \{0, 1\}$, $c = 0$ and $P = \{0\}$. At $y = 1$, the implication is false. So the Skolemization of a valid formula need not be valid. It is satisfiable, as (b) of the theorem requires, for example by making $P$ hold of everything.

To prove the drinker formula with a refutation prover, negate it first: $\forall x\, \exists y\, (P(x) \land \neg P(y))$. Skolemizing gives $\forall x\, (P(x) \land \neg P(f(x)))$, which is unsatisfiable. The instances at $x = c$ and $x = f(c)$ contain the conflict between $\neg P(f(c))$ and $P(f(c))$.

### Example 4: order of prenexing affects Skolem functions

Let $\varphi = (\exists x\, P(x)) \land (\forall y\, \exists z\, R(y, z))$.

```text
Pulling ∃x first:
    ∃x ∀y ∃z (P(x) ∧ R(y, z))
    Skolem form: ∀y (P(c) ∧ R(y, f(y)))
Pulling ∀y and ∃z first:
    ∀y ∃z ∃x (P(x) ∧ R(y, z))
    Skolem form: ∀y (P(g(y)) ∧ R(y, f(y)))
```

Both are correct, but the first produces a constant in place of the unary function $g$. Terms with fewer function symbols lead to smaller Herbrand universes and fewer instances.

## Common mistakes

- Skolemizing before negating the goal. To prove $\varphi$, you must Skolemize $\neg\varphi$. Skolemizing $\varphi$ and then negating replaces the wrong quantifiers, and it gives an unsound result.
- Skolemizing a quantifier in a negative position. In $\neg \exists x\, P(x)$, the quantifier is effectively universal, so replacing $x$ with a constant changes the meaning. Convert to NNF first.
- Using a constant for an existential in the scope of a universal. The sentence $\forall x\, \exists y\, R(x, y)$ becomes $\forall x\, R(x, f(x))$. Writing $\forall x\, R(x, c)$ gives something stronger, which is the Skolemization of $\exists y\, \forall x\, R(x, y)$.
- Reusing a Skolem symbol. Each existential quantifier needs its own fresh symbol. A symbol already in the signature would add an unjustified constraint.
- Pulling a quantifier out of an antecedent without flipping it. The formula $(\forall x\, P(x)) \to Q$ is equivalent to $\exists x\, (P(x) \to Q)$ and not to $\forall x\, (P(x) \to Q)$.
- Prenexing without renaming. The formula $\forall x\, P(x) \lor \forall x\, Q(x)$ is not equivalent to $\forall x\, (P(x) \lor Q(x))$. Rename first to get $\forall x\, \forall y\, (P(x) \lor Q(y))$.
- Prenexing through $\leftrightarrow$ directly. The formula $(\forall x\, P(x)) \leftrightarrow Q$ must first be expanded, because the quantifier occurs with both polarities and gives two quantifiers of different kinds.
- Claiming validity from a Tseitin encoding. The encoding preserves satisfiability, and a valid formula's encoding is falsified by assigning the root name false. Encode the negation and test for unsatisfiability.
- Believing that a model of a Plaisted-Greenbaum encoding gives each name the value of its subformula. It need not. The restriction to the original variables is a model, while the name values may not match.
- Assuming that CNF conversion by distribution is always worse. For a small formula with little nesting, it can be shorter, as in Example 1.

## Exercises

### Exercise 1

Convert to negation normal form: (a) $\neg(x_1 \to (x_2 \land \neg x_3))$; (b) $\neg \forall x\, (P(x) \to \exists y\, Q(x, y))$.

<details><summary>Solution</summary>

(a) $\neg(x_1 \to (x_2 \land \neg x_3)) \equiv x_1 \land \neg(x_2 \land \neg x_3) \equiv x_1 \land (\neg x_2 \lor x_3)$.

(b) $\neg \forall x\, (\neg P(x) \lor \exists y\, Q(x, y)) \equiv \exists x\, \neg(\neg P(x) \lor \exists y\, Q(x, y)) \equiv \exists x\, (P(x) \land \forall y\, \neg Q(x, y))$.

</details>

### Exercise 2

Give a CNF and a DNF for $(x_1 \lor x_2) \to x_3$, and confirm the CNF from the truth table.

<details><summary>Solution</summary>

$(x_1 \lor x_2) \to x_3 \equiv \neg(x_1 \lor x_2) \lor x_3 \equiv (\neg x_1 \land \neg x_2) \lor x_3$, which is a DNF.

Distributing gives the CNF $(\neg x_1 \lor x_3) \land (\neg x_2 \lor x_3)$.

From the truth table, the formula is false exactly in the rows with $x_3 = 0$ and at least one of $x_1$, $x_2$ true, namely $(1,0,0)$, $(0,1,0)$ and $(1,1,0)$. The row method gives the three clauses $(\neg x_1 \lor x_2 \lor x_3)$, $(x_1 \lor \neg x_2 \lor x_3)$ and $(\neg x_1 \lor \neg x_2 \lor x_3)$. This CNF is equivalent, and the shorter one follows by resolving pairs: the first and the third resolve on $x_2$ to give $(\neg x_1 \lor x_3)$, and the second and the third resolve on $x_1$ to give $(\neg x_2 \lor x_3)$.

</details>

### Exercise 3

Convert to prenex normal form: $(\exists x\, P(x)) \to \forall y\, \exists z\, R(y, z)$.

<details><summary>Solution</summary>

The bound variables are already distinct. The antecedent quantifier flips:

$$
(\exists x\, P(x)) \to \forall y\, \exists z\, R(y, z) \equiv \forall x\, (P(x) \to \forall y\, \exists z\, R(y, z)) \equiv \forall x\, \forall y\, \exists z\, (P(x) \to R(y, z)).
$$

</details>

### Exercise 4

Skolemize $\exists x\, \forall y\, \exists z\, \forall w\, \exists v\, T(x, y, z, w, v)$.

<details><summary>Solution</summary>

The quantifier $\exists x$ has no universal quantifier before it, so $x$ becomes a constant $c$. The variable $z$ follows $\forall y$, so it becomes $f(y)$. The variable $v$ follows $\forall y$ and $\forall w$, so it becomes $g(y, w)$.

$$
\forall y\, \forall w\, T(c, y, f(y), w, g(y, w)).
$$

</details>

### Exercise 5

Show that $\exists x\, P(x)$ and $P(c)$ are equisatisfiable and not equivalent. Then state which of these two formulas entails the other.

<details><summary>Solution</summary>

Both are satisfiable, for example in a one-element structure with $P$ true of that element and $c$ naming it. So they are equisatisfiable.

They are not equivalent: let $M = \{0, 1\}$, $P = \{0\}$, $c = 1$. Then $\exists x\, P(x)$ is true and $P(c)$ is false.

$P(c) \models \exists x\, P(x)$, with witness the value of $c$. The other direction fails, by the structure just given. This matches part (a) of the Skolemization theorem.

</details>

### Exercise 6

Apply the Tseitin transformation to $x_1 \leftrightarrow (x_2 \land x_3)$. List all clauses, and count them.

<details><summary>Solution</summary>

Let $x_4$ name $x_2 \land x_3$, and let $x_5$ name $x_1 \leftrightarrow x_4$.

```text
x4 ↔ x2 ∧ x3:   {¬x4, x2}  {¬x4, x3}  {x4, ¬x2, ¬x3}
x5 ↔ (x1 ↔ x4): {¬x5, ¬x1, x4}  {¬x5, x1, ¬x4}  {x5, x1, x4}  {x5, ¬x1, ¬x4}
root:           {x5}
```

That is 8 clauses. The formula has 4 models over $x_1, x_2, x_3$, and these clauses have exactly 4 models, one extending each.

</details>

### Exercise 7

Let $\mathrm{Par}_n = x_1 \oplus \dots \oplus x_n$, which is true exactly when an odd number of variables are true. Prove that every CNF equivalent to $\mathrm{Par}_n$ over only these variables has at least $2^{n-1}$ clauses. Then give a Tseitin-style CNF of size linear in $n$.

<details><summary>Solution</summary>

Consider any non-tautological clause $C$ in an equivalent CNF, and suppose that $C$ does not mention $x_i$. There is an assignment $a$ falsifying $C$. Flipping $a$ at $x_i$ also falsifies $C$. These two assignments have different parity, so one of them satisfies $\mathrm{Par}_n$. But that assignment falsifies a clause of the CNF, which is a contradiction.

So each non-tautological clause mentions all $n$ variables, and it is falsified by exactly one assignment. Each of the $2^{n-1}$ assignments of even parity must falsify some clause, and each clause covers only one. So at least $2^{n-1}$ clauses are needed.

Linear encoding. Add variables $s_2, \dots, s_n$ with $s_2 \leftrightarrow (x_1 \oplus x_2)$ and $s_i \leftrightarrow (s_{i-1} \oplus x_i)$ for $i > 2$, and add the unit clause $\{s_n\}$. Each definition uses 4 clauses of 3 literals, as in the table for $\leftrightarrow$ with one literal negated. So the encoding has $4(n-1) + 1$ clauses. By the Tseitin theorem, its models correspond to those of $\mathrm{Par}_n$.

</details>

### Exercise 8

Let $\varphi_n = (x_1 \land x_2) \lor \dots \lor (x_{2n-1} \land x_{2n})$. Prove that every CNF equivalent to $\varphi_n$ over these variables has at least $2^n$ clauses.

<details><summary>Solution</summary>

A transversal $T$ picks one variable from each of the $n$ pairs. There are $2^n$ transversals. Let $a_T$ be the assignment that makes the variables in $T$ false and all the others true. Each pair then has a false variable, so $\varphi_n$ is false at $a_T$. So in an equivalent CNF, some clause $C_T$ is falsified by $a_T$. Thus the positive literals of $C_T$ are all from $T$, and the negative literals of $C_T$ are all from outside $T$.

We show that $C_T$ contains every variable of $T$ as a positive literal. Suppose the variable $t \in T$, from pair $i$, does not occur positively in $C_T$. Let $b$ be $a_T$ with $t$ changed to true. Since $t$ is not a positive literal of $C_T$, and $\neg t$ is not in $C_T$, the clause $C_T$ is still false at $b$. Pair $i$ is now all true, so $\varphi_n$ is true at $b$. This contradicts the equivalence.

So the positive literals of $C_T$ are exactly $T$, and different transversals have different clauses. Hence there are at least $2^n$ clauses.

</details>

### Exercise 9

Prove conservativity: for a prenex sentence $\varphi$ and a sentence $\chi$ over the signature of $\varphi$, $\varphi \models \chi$ if and only if $\mathrm{Sk}(\varphi) \models \chi$.

<details><summary>Solution</summary>

Suppose $\varphi \models \chi$. By part (a) of the theorem, $\mathrm{Sk}(\varphi) \models \varphi$, so $\mathrm{Sk}(\varphi) \models \chi$.

Suppose $\varphi \not\models \chi$. Then there is a model $\mathcal{M}$ of $\varphi$ with $\mathcal{M} \models \neg\chi$. By part (c), $\mathcal{M}$ expands to a model $\mathcal{M}'$ of $\mathrm{Sk}(\varphi)$, with the same domain and the same interpretation of the original symbols. Since $\chi$ does not contain the Skolem symbols, its truth does not change, so $\mathcal{M}' \models \neg\chi$. Hence $\mathrm{Sk}(\varphi) \not\models \chi$.

</details>

### Exercise 10

Prove the Plaisted-Greenbaum theorem. Assume that $\varphi$ uses only $\neg, \land, \lor, \to$ (no $\leftrightarrow$), so that each occurrence of a subformula has one polarity, and treat each occurrence separately.

<details><summary>Solution</summary>

A positive occurrence of $\psi$ gets the clause form of $n_\psi \to \hat\psi$, and a negative occurrence gets the clause form of $\hat\psi \to n_\psi$, where $\hat\psi$ is the connective applied to the names of the immediate parts. The root has the unit clause $\{n_\varphi\}$.

Model of the encoding gives model of $\varphi$. Let $v$ be a model of $\mathrm{PG}(\varphi)$. We show the following by induction on subformula occurrences: if the occurrence of $\psi$ is positive and $v(n_\psi) = 1$, then $v(\psi) = 1$. If it is negative and $v(n_\psi) = 0$, then $v(\psi) = 0$. For atoms, $n_\psi$ is $\psi$.

Positive occurrence of $\alpha \land \beta$ with $v(n_\psi) = 1$: the clause gives $v(n_\alpha) = v(n_\beta) = 1$, both occurrences are positive, and the hypothesis gives $v(\alpha) = v(\beta) = 1$. Positive occurrence of $\alpha \lor \beta$ is similar. Negative occurrence of $\alpha \land \beta$ with $v(n_\psi) = 0$: the clause $\hat\psi \to n_\psi$ gives that $n_\alpha$ or $n_\beta$ is false, each occurrence is negative, and the hypothesis gives that $\alpha$ or $\beta$ is false. For $\neg\alpha$ and $\alpha \to \beta$, the argument is the same, with the polarity of the parts flipped as needed. Positive occurrence of $\alpha \to \beta$ with $v(n_\psi) = 1$: the occurrence of $\alpha$ is negative and $\beta$ is positive, and the clause says that $n_\alpha$ is false or $n_\beta$ is true. So $\alpha$ is false or $\beta$ is true.

Applying this to the root, which is positive with $v(n_\varphi) = 1$, gives $v(\varphi) = 1$.

Model of $\varphi$ gives model of the encoding. Let $v$ be a model of $\varphi$. Extend it by $v^*(n_\psi) = v(\psi)$. This satisfies both directions of each definition, hence every clause of $\mathrm{PG}(\varphi)$, and $\{n_\varphi\}$.

So $\varphi$ and $\mathrm{PG}(\varphi)$ are equisatisfiable, and every model of the encoding restricts to a model of $\varphi$.

</details>

### Exercise 11

For a prenex sentence $\varphi$, the Herbrand form $\mathrm{H}(\varphi)$ replaces each universal variable by a fresh function of the existential variables that precede it, and deletes the universal quantifiers. Prove that $\varphi$ is valid if and only if $\mathrm{H}(\varphi)$ is valid. Then apply this to the drinker formula.

<details><summary>Solution</summary>

Write $\varphi = Q_1 x_1 \dots Q_k x_k\, \mu$. Its negation is equivalent to the prenex sentence $\bar{Q}_1 x_1 \dots \bar{Q}_k x_k\, \neg\mu$, where each quantifier flips. Skolemizing this sentence replaces the existentials of the negation, which are the universals of $\varphi$, by functions of the preceding universals of the negation, which are the existentials of $\varphi$. So

$$
\mathrm{Sk}(\neg\varphi) \equiv \neg \mathrm{H}(\varphi),
$$

up to using the same fresh symbols. Therefore:

$\varphi$ is valid iff $\neg\varphi$ is unsatisfiable iff $\mathrm{Sk}(\neg\varphi)$ is unsatisfiable iff $\neg\mathrm{H}(\varphi)$ is unsatisfiable iff $\mathrm{H}(\varphi)$ is valid.

For the drinker formula $\exists x\, \forall y\, (P(x) \to P(y))$, the universal variable $y$ follows $\exists x$, so it becomes $f(x)$. This gives $\exists x\, (P(x) \to P(f(x)))$, which is valid. In any structure, consider an element $a$. If $a \notin P$, then $x = a$ works. If $a \in P$ and $f(a) \in P$, then $x = a$ works. If $a \in P$ and $f(a) \notin P$, then $x = f(a)$ works, because its antecedent is false.

</details>

### Exercise 12

Show that $\forall x\, (P(x) \to Q(x)) \land \exists x\, P(x) \models \exists x\, Q(x)$ by converting the premises and the negated conclusion to clause form and finding a set of ground instances that is propositionally unsatisfiable.

<details><summary>Solution</summary>

The premises and the negated conclusion are:

$$
\forall x\, (\neg P(x) \lor Q(x)), \qquad \exists x\, P(x), \qquad \forall x\, \neg Q(x).
$$

Skolemizing $\exists x\, P(x)$ gives $P(c)$. The clause form is $\{\neg P(x), Q(x)\}$, $\{P(c)\}$, $\{\neg Q(x)\}$.

Instantiate $x := c$, which gives the ground clauses $\{\neg P(c), Q(c)\}$, $\{P(c)\}$ and $\{\neg Q(c)\}$. Treating $P(c)$ and $Q(c)$ as propositional variables, resolution derives $\{Q(c)\}$ from the first two clauses, and then the empty clause with the third.

So the clause set is unsatisfiable, and the entailment holds. The step of finding a ground instance is justified by Herbrand's theorem in [First-Order Metatheory](../first-order-metatheory/).

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Convert any formula to NNF, CNF and DNF, and any first-order formula to prenex form and Skolem form, by hand.
- Fill in the summary table of what each conversion preserves, and give a counterexample for each property a conversion does not preserve.
- Write the Tseitin clauses for each connective, and prove the Tseitin theorem.
- Prove that one Skolemization step preserves satisfiability, and state where choice is used.
- Explain why provers Skolemize the negation of the goal.
- Prove an exponential lower bound on the size of CNF for a specific formula without new variables.

## Materials

- [Harrison, Handbook of Practical Logic and Automated Reasoning.](https://www.cl.cam.ac.uk/~jrh13/atp/) Read the propositional logic material on definitional CNF and the first-order material on prenex form and Skolemization. The book presents each conversion as a short program, which helps you see the steps precisely.
- Gallier, Logic for Computer Science, 2nd edition. Read the treatment of negation normal form, prenex form and Skolem functions, developed in connection with Herbrand's theorem.
- Tseitin, On the Complexity of Derivation in Propositional Calculus, 1968. Read it as the historical source of the transformation, and as an early study of resolution with named subformulas.
- Plaisted and Greenbaum, A Structure-Preserving Clause Form Translation, Journal of Symbolic Computation, 1986. Read it for the polarity-based optimization.
