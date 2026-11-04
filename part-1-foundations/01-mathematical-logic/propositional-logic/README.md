# Propositional Logic

Part 1, Chapter 1: Mathematical Logic.

## Objective

Define the syntax and semantics of propositional logic and decide validity, satisfiability and entailment by hand.

## Why this matters

Propositional logic is the language of SAT solvers, and it is the Boolean layer of every SMT solver. Later chapters depend directly on what you learn here: [resolution and DPLL](../../../part-2-core-reasoning/04-sat/resolution-and-dpll/), [CDCL](../../../part-2-core-reasoning/04-sat/cdcl/), [DPLL(T)](../../../part-2-core-reasoning/05-smt/dpllt/) and [bounded model checking](../../../part-2-core-reasoning/08-model-checking/bounded-model-checking/) all reduce a question to the satisfiability of a propositional formula. An applied scientist in this field spends much of their time turning validity questions into satisfiability questions, and reading a satisfying assignment as a concrete counterexample. This topic gives you the definitions that make that translation correct.

## Prerequisites

None in this repository, since this is the first topic of the program. You need basic set notation and ordinary mathematical induction. Structural induction is introduced below and treated in general in [Induction Principles](../../03-semantics-and-types/induction-principles/).

## Lesson

### Syntax

Fix a countably infinite set of propositional variables $V = \{x_1, x_2, x_3, \dots\}$. The set of formulas is the smallest set of strings such that:

- $\bot$ and $\top$ are formulas, and every $x_i \in V$ is a formula;
- if $\varphi$ is a formula, then $(\neg \varphi)$ is a formula;
- if $\varphi$ and $\psi$ are formulas, then $(\varphi \land \psi)$, $(\varphi \lor \psi)$, $(\varphi \to \psi)$ and $(\varphi \leftrightarrow \psi)$ are formulas.

An atom is a variable, $\bot$ or $\top$. A literal is a variable $x_i$ or a negated variable $\neg x_i$.

To reduce parentheses, $\neg$ binds tightest, followed in order by $\land$, $\lor$, $\to$ and $\leftrightarrow$, and $\to$ associates to the right. So $\neg x_1 \land x_2 \to x_3 \to x_4$ abbreviates $(((\neg x_1) \land x_2) \to (x_3 \to x_4))$.

The phrase "smallest set" gives a proof principle and a definition principle.

Structural induction. To prove that a property holds of all formulas, prove it for atoms, and prove that it passes from $\varphi$ and $\psi$ to each formula built from them by one connective.

Structural recursion. To define a function on all formulas, give its value on atoms and say how its value on a compound formula is computed from its values on the immediate parts. For example, the set of subformulas is defined by $\mathrm{Sub}(\alpha) = \{\alpha\}$ for an atom $\alpha$, $\mathrm{Sub}(\neg \varphi) = \{\neg \varphi\} \cup \mathrm{Sub}(\varphi)$, and $\mathrm{Sub}(\varphi \circ \psi) = \{\varphi \circ \psi\} \cup \mathrm{Sub}(\varphi) \cup \mathrm{Sub}(\psi)$ for a binary connective $\circ$.

Structural recursion is well defined only if each compound formula is built in exactly one way. That is the content of the next theorem.

Theorem (unique readability). Every formula is exactly one of the following: an atom, $(\neg \varphi)$ for a unique $\varphi$, or $(\varphi \circ \psi)$ for a unique binary connective $\circ$ and unique $\varphi$, $\psi$.

Proof sketch. By structural induction, every formula has equally many left and right parentheses, and every nonempty proper initial segment of a formula has strictly more left than right parentheses. Suppose $(\varphi \circ \psi)$ and $(\varphi' \circ' \psi')$ are the same string with $\varphi \neq \varphi'$. Then one of $\varphi$, $\varphi'$ is a nonempty proper initial segment of the other, so it is a balanced string and an unbalanced string at once, which is impossible. Hence $\varphi = \varphi'$, and then $\circ = \circ'$ and $\psi = \psi'$. The other cases are similar. $\square$

### Semantics

An assignment is a function $v : V \to \{0, 1\}$, where $1$ means true and $0$ means false. It extends to all formulas by structural recursion:

$$
\begin{aligned}
v(\top) &= 1, \qquad v(\bot) = 0,\\
v(\neg \varphi) &= 1 - v(\varphi),\\
v(\varphi \land \psi) &= \min(v(\varphi), v(\psi)),\\
v(\varphi \lor \psi) &= \max(v(\varphi), v(\psi)),\\
v(\varphi \to \psi) &= \max(1 - v(\varphi), v(\psi)),\\
v(\varphi \leftrightarrow \psi) &= 1 \text{ if } v(\varphi) = v(\psi), \text{ and } 0 \text{ otherwise}.
\end{aligned}
$$

If $v(\varphi) = 1$, we say that $v$ satisfies $\varphi$, or that $v$ is a model of $\varphi$. A set $\Gamma$ of formulas is satisfied by $v$ if $v$ satisfies every member of $\Gamma$.

Lemma (coincidence). If $v$ and $w$ agree on the variables occurring in $\varphi$, then $v(\varphi) = w(\varphi)$.

Proof. By structural induction on $\varphi$. Atoms are immediate, and in each compound case the value is computed from the values of the parts, which agree by the induction hypothesis. $\square$

The lemma is what makes truth tables a decision method. A formula with $n$ variables needs only $2^n$ rows, even though there are uncountably many assignments on $V$.

Why implication has this truth table. Implication is defined so that it is truth-functional and supports reasoning. Two requirements force the table. Modus ponens must preserve truth, so $1 \to 0$ must be $0$. The formula $(x_1 \land x_2) \to x_1$ must hold under every assignment, since a conjunction always gives its first conjunct. Taking $x_1 = x_2 = 1$ forces $1 \to 1 = 1$. Taking $x_1 = 1$, $x_2 = 0$ forces $0 \to 1 = 1$. Taking $x_1 = 0$ forces $0 \to 0 = 1$. The result carries no claim of causal connection between antecedent and consequent, and it is the only table meeting these requirements.

Truth tables for propositional logic were introduced in their modern form by Post and by Wittgenstein, both in 1921. Post used them to prove the completeness of the propositional part of Principia Mathematica, which you will meet in [Soundness and Completeness](../soundness-and-completeness/).

### Validity, satisfiability, entailment

Let $\varphi$, $\psi$ be formulas and $\Gamma$ a set of formulas, possibly infinite.

| Term | Definition |
|---|---|
| $\varphi$ is valid, written $\models \varphi$ | Every assignment satisfies $\varphi$. |
| $\varphi$ is satisfiable | At least one assignment satisfies $\varphi$. |
| $\varphi$ is unsatisfiable | No assignment satisfies $\varphi$. |
| $\varphi$ is contingent | Some assignment satisfies $\varphi$ and some assignment falsifies it. |
| $\Gamma$ entails $\varphi$, written $\Gamma \models \varphi$ | Every assignment that satisfies $\Gamma$ also satisfies $\varphi$. |
| $\varphi$ and $\psi$ are equivalent, written $\varphi \equiv \psi$ | Every assignment gives them the same value. |
| $\varphi$ and $\psi$ are equisatisfiable | Both are satisfiable or both are unsatisfiable. |

A valid formula is also called a tautology. The symbols $\models$ and $\equiv$ belong to the language in which you talk about formulas, and they are not connectives. The symbols $\to$ and $\leftrightarrow$ are connectives inside formulas. The following theorem connects the two levels.

Theorem (duality and reduction). For all $\Gamma$, $\varphi$, $\psi$:

1. $\models \varphi$ if and only if $\neg \varphi$ is unsatisfiable.
2. $\Gamma \models \varphi$ if and only if $\Gamma \cup \{\neg \varphi\}$ is unsatisfiable.
3. $\Gamma \cup \{\varphi\} \models \psi$ if and only if $\Gamma \models \varphi \to \psi$ (the semantic deduction theorem).
4. $\{\varphi_1, \dots, \varphi_n\} \models \psi$ if and only if $\models \varphi_1 \land \dots \land \varphi_n \to \psi$.
5. $\varphi \equiv \psi$ if and only if $\models \varphi \leftrightarrow \psi$.
6. If $\Gamma$ is unsatisfiable, then $\Gamma \models \varphi$ for every $\varphi$.

Proof of 2. If $\Gamma \models \varphi$ and $v$ satisfies $\Gamma$, then $v(\varphi) = 1$, so $v(\neg\varphi) = 0$, and no assignment satisfies $\Gamma \cup \{\neg\varphi\}$. Conversely, if that set is unsatisfiable and $v$ satisfies $\Gamma$, then $v(\neg\varphi) = 0$, so $v(\varphi) = 1$. The other parts are proved in the same way or are exercises below. $\square$

Part 2 is the reason SAT solvers can answer entailment questions. You add the negated conclusion to the premises and ask for a model. A model is a counterexample, and the absence of a model is a proof of entailment. Every verification tool in this program uses this reduction.

Entailment has three further structural properties, each immediate from the definition.

- Reflexivity: if $\varphi \in \Gamma$, then $\Gamma \models \varphi$.
- Monotonicity: if $\Gamma \models \varphi$ and $\Gamma \subseteq \Gamma'$, then $\Gamma' \models \varphi$.
- Cut: if $\Gamma \models \varphi$ and $\Gamma \cup \{\varphi\} \models \psi$, then $\Gamma \models \psi$.

### Substitution and replacement

Write $\varphi[\psi / x]$ for the result of replacing every occurrence of the variable $x$ in $\varphi$ by $\psi$. For an assignment $v$ and $b \in \{0, 1\}$, write $v[x \mapsto b]$ for the assignment that sends $x$ to $b$ and agrees with $v$ elsewhere.

Lemma (substitution). $v(\varphi[\psi / x]) = v[x \mapsto v(\psi)](\varphi)$.

The proof is Exercise 7. It has two consequences.

Corollary (validity is closed under substitution). If $\models \varphi$, then $\models \varphi[\psi / x]$. This is why you can treat a valid formula as a schema. Since $x_1 \lor \neg x_1$ is valid, so is $\chi \lor \neg \chi$ for every formula $\chi$.

Corollary (replacement). If $\varphi \equiv \psi$, then $\chi[\varphi / x] \equiv \chi[\psi / x]$. This justifies rewriting a subformula with an equivalent one.

Setting $\psi$ to a constant gives the Shannon expansion, which underlies case splitting:

$$
\varphi \equiv (x \land \varphi[\top / x]) \lor (\neg x \land \varphi[\bot / x]).
$$

### Standard equivalences

You should know these and be able to confirm any of them with a four-row or eight-row table.

| Name | Equivalence |
|---|---|
| Double negation | $\neg \neg x_1 \equiv x_1$ |
| Commutativity | $x_1 \land x_2 \equiv x_2 \land x_1$ and $x_1 \lor x_2 \equiv x_2 \lor x_1$ |
| Associativity | $x_1 \land (x_2 \land x_3) \equiv (x_1 \land x_2) \land x_3$ and likewise for $\lor$ |
| Idempotence | $x_1 \land x_1 \equiv x_1$ and $x_1 \lor x_1 \equiv x_1$ |
| Distributivity of $\land$ over $\lor$ | $x_1 \land (x_2 \lor x_3) \equiv (x_1 \land x_2) \lor (x_1 \land x_3)$ |
| Distributivity of $\lor$ over $\land$ | $x_1 \lor (x_2 \land x_3) \equiv (x_1 \lor x_2) \land (x_1 \lor x_3)$ |
| De Morgan | $\neg (x_1 \land x_2) \equiv \neg x_1 \lor \neg x_2$ and $\neg (x_1 \lor x_2) \equiv \neg x_1 \land \neg x_2$ |
| Absorption | $x_1 \land (x_1 \lor x_2) \equiv x_1$ and $x_1 \lor (x_1 \land x_2) \equiv x_1$ |
| Units | $x_1 \land \top \equiv x_1$ and $x_1 \lor \bot \equiv x_1$ |
| Zeros | $x_1 \land \bot \equiv \bot$ and $x_1 \lor \top \equiv \top$ |
| Complement | $x_1 \land \neg x_1 \equiv \bot$ and $x_1 \lor \neg x_1 \equiv \top$ |
| Material implication | $x_1 \to x_2 \equiv \neg x_1 \lor x_2$ |
| Contraposition | $x_1 \to x_2 \equiv \neg x_2 \to \neg x_1$ |
| Negated implication | $\neg (x_1 \to x_2) \equiv x_1 \land \neg x_2$ |
| Currying | $(x_1 \land x_2) \to x_3 \equiv x_1 \to (x_2 \to x_3)$ |
| Biconditional | $x_1 \leftrightarrow x_2 \equiv (x_1 \to x_2) \land (x_2 \to x_1)$ |
| Biconditional as cases | $x_1 \leftrightarrow x_2 \equiv (x_1 \land x_2) \lor (\neg x_1 \land \neg x_2)$ |

### Functional completeness

An $n$-ary Boolean function is a map $f : \{0, 1\}^n \to \{0, 1\}$. There are $2^{2^n}$ of them. A formula with variables among $x_1, \dots, x_n$ defines one such function. A set of connectives is functionally complete if every Boolean function, for every $n \geq 1$, is defined by a formula using only those connectives.

Theorem. $\{\neg, \land, \lor\}$ is functionally complete.

Proof. Let $f$ be $n$-ary. For each $a \in \{0, 1\}^n$ with $f(a) = 1$, let $t_a$ be the conjunction of the literals $\ell_1, \dots, \ell_n$, where $\ell_i = x_i$ if $a_i = 1$ and $\ell_i = \neg x_i$ if $a_i = 0$. Then $t_a$ is true exactly at $a$, and the disjunction of all such $t_a$ defines $f$. If $f$ is constantly $0$, use $x_1 \land \neg x_1$. $\square$

The formula built here is in disjunctive normal form, covered in [Normal Forms and Skolemization](../normal-forms-and-skolemization/). De Morgan then shows that $\{\neg, \land\}$ and $\{\neg, \lor\}$ are complete, and the identities in Exercise 5 show the same for $\{\to, \bot\}$ and for NAND alone. To show a set of connectives incomplete, find an invariant shared by all formulas over that set which some Boolean function violates. Exercises 8 and 9 use this technique.

### Deciding by hand

All three problems reduce to one another through the reduction theorem, so a single method handles them. You have three methods, in increasing order of cleverness.

Truth tables. List all $2^n$ rows and evaluate. The method is complete and easy to check. It is practical by hand up to about four variables.

Case splitting. Pick a variable, substitute $\top$ and $\bot$, simplify, and recurse. This is the procedure:

```text
function VALID(φ):
    φ := SIMPLIFY(φ)
    if φ is ⊤ then return true
    if φ is ⊥ then return false
    choose a variable x occurring in φ
    return VALID(φ[⊤/x]) and VALID(φ[⊥/x])
```

SIMPLIFY applies the unit and zero laws above, together with $\neg \top \equiv \bot$, $\neg \bot \equiv \top$, $\top \to \psi \equiv \psi$, $\bot \to \psi \equiv \top$, $\psi \to \top \equiv \top$, $\psi \to \bot \equiv \neg \psi$, $\top \leftrightarrow \psi \equiv \psi$ and $\bot \leftrightarrow \psi \equiv \neg \psi$, until none applies. Once all variables have been replaced, simplification reaches $\top$ or $\bot$, so the procedure terminates. Its correctness is the Shannon expansion: $\varphi$ is valid if and only if both $\varphi[\top / x]$ and $\varphi[\bot / x]$ are valid. Changing "and" to "or" and exchanging the base results gives a satisfiability procedure. This is the skeleton of DPLL.

Falsification search. To test validity, assume that the formula is false and work out what that forces. To falsify $\varphi \to \psi$, you need $\varphi$ true and $\psi$ false, and so on inward. If the forced values conflict on every branch, the formula is valid. If some branch completes without conflict, you have a countermodel. This is the idea behind tableaux and sequent calculus, and it is formalized in [Proof Systems](../proof-systems/).

Complexity. Truth tables take time exponential in the number of variables, and no polynomial method is known. Satisfiability is NP-complete by the Cook-Levin theorem, and validity is coNP-complete. See [Reductions and NP-Completeness](../../02-decidability-and-complexity/reductions-and-np-completeness/). Evaluating one formula under one assignment takes linear time, which is why a model is a certificate that can be checked cheaply.

## Worked examples

### Example 1: Peirce's law by truth table

Decide whether $((x_1 \to x_2) \to x_1) \to x_1$ is valid. Evaluate the subformulas from the inside out.

| $x_1$ | $x_2$ | $x_1 \to x_2$ | $(x_1 \to x_2) \to x_1$ | $((x_1 \to x_2) \to x_1) \to x_1$ |
|---|---|---|---|---|
| 0 | 0 | 1 | 0 | 1 |
| 0 | 1 | 1 | 0 | 1 |
| 1 | 0 | 0 | 1 | 1 |
| 1 | 1 | 1 | 1 | 1 |

The last column is all ones, so the formula is valid. Remember this formula, because it contains only $\to$ and yet has no proof in intuitionistic logic, as you will see in [Soundness and Completeness](../soundness-and-completeness/).

### Example 2: case splitting

Decide whether $\varphi = ((x_1 \to x_2) \land (x_2 \to x_3)) \to (x_1 \to x_3)$ is valid. Split on $x_1$, then on $x_2$ and $x_3$ where needed.

```text
x1 := ⊤
    ((⊤ → x2) ∧ (x2 → x3)) → (⊤ → x3)
    simplifies to (x2 ∧ (x2 → x3)) → x3
    x2 := ⊤
        (⊤ ∧ (⊤ → x3)) → x3
        simplifies to x3 → x3
        x3 := ⊤ gives ⊤ → ⊤, which simplifies to ⊤
        x3 := ⊥ gives ⊥ → ⊥, which simplifies to ⊤
    x2 := ⊥
        (⊥ ∧ (⊥ → x3)) → x3
        simplifies to ⊥ → x3, which simplifies to ⊤
x1 := ⊥
    ((⊥ → x2) ∧ (x2 → x3)) → (⊥ → x3)
    ⊥ → x3 simplifies to ⊤, and ψ → ⊤ simplifies to ⊤
```

All four leaves are $\top$, so $\varphi$ is valid. The search visited four leaves, while a truth table has eight rows.

### Example 3: an entailment from a system description

A service has this behavior. Let $x_1$ mean that a deployment starts, $x_2$ that it uses the blue fleet, $x_3$ that it uses the green fleet, $x_4$ that a health check runs, and $x_5$ that the service is in maintenance mode. The rules are:

$$
\Gamma = \{\, x_1 \to (x_2 \lor x_3),\; x_2 \to x_4,\; x_3 \to x_4,\; x_4 \to \neg x_5,\; x_5 \lor \neg x_1 \,\}.
$$

Part (a). Decide whether $\Gamma \models \neg x_1$. By the reduction theorem, this holds if and only if $\Gamma \cup \{x_1\}$ is unsatisfiable. Suppose $v$ satisfies that set, and follow what is forced.

```text
v(x1) = 1                 from the added formula x1
v(x5) = 1                 from x5 ∨ ¬x1, since ¬x1 is false
v(x4) = 0                 from x4 → ¬x5, since ¬x5 is false
v(x2) = 0                 from x2 → x4, since x4 is false
v(x3) = 0                 from x3 → x4, since x4 is false
x1 → (x2 ∨ x3) is false   since x1 is true and x2 ∨ x3 is false
```

Every step was forced and the result is a conflict, so no such $v$ exists. Hence $\Gamma \models \neg x_1$: under these rules, a deployment can never start. The rules contain a design bug, because the last rule requires maintenance mode while the others exclude it.

Part (b). Decide whether $\Gamma \models \neg x_4$. Look for a model of $\Gamma \cup \{x_4\}$. Set $x_4 = 1$. Then $x_4 \to \neg x_5$ forces $x_5 = 0$, and $x_5 \lor \neg x_1$ forces $x_1 = 0$. The rules $x_2 \to x_4$ and $x_3 \to x_4$ now hold for any $x_2$, $x_3$, and $x_1 \to (x_2 \lor x_3)$ holds because $x_1 = 0$. So $v(x_1) = v(x_2) = v(x_3) = v(x_5) = 0$ with $v(x_4) = 1$ is a model of $\Gamma$ that falsifies $\neg x_4$. Hence $\Gamma \not\models \neg x_4$, and this assignment is the counterexample.

### Example 4: falsification search with a countermodel

Decide whether $\varphi = (x_1 \to (x_2 \to x_3)) \to ((x_1 \to x_2) \to x_3)$ is valid. Assume that $\varphi$ is false.

```text
φ false requires:
    x1 → (x2 → x3) true
    (x1 → x2) → x3 false, which requires:
        x1 → x2 true
        x3 false
Branch x1 = 1:
    x1 → x2 true forces x2 = 1
    x1 → (x2 → x3) true forces x2 → x3 true
    with x2 = 1 this forces x3 = 1, which conflicts with x3 false
Branch x1 = 0:
    x1 → x2 true for every x2
    x1 → (x2 → x3) true for every x2, x3
    no conflict
```

The second branch completes, so $\varphi$ is not valid. The countermodels are $v(x_1) = 0$, $v(x_3) = 0$ with $v(x_2)$ arbitrary. Check one of them with $v(x_2) = 0$: the antecedent $0 \to (0 \to 0)$ is $1$, and the consequent $(0 \to 0) \to 0$ is $1 \to 0 = 0$, so $\varphi$ evaluates to $0$.

## Common mistakes

- Treating "not valid" as "unsatisfiable". A contingent formula such as $x_1$ is neither valid nor unsatisfiable. The correct relation is that $\varphi$ is not valid if and only if $\neg\varphi$ is satisfiable.
- Assuming that either $\Gamma \models \varphi$ or $\Gamma \models \neg \varphi$ must hold. With $\Gamma = \emptyset$ and $\varphi = x_1$, neither holds. Entailment leaves undetermined whatever $\Gamma$ does not fix.
- Writing $\models$ inside a formula or $\to$ between claims about formulas. The expression $x_1 \to (x_2 \models x_3)$ is not a formula. Keep the object language and the metalanguage apart.
- Believing that $\neg(x_1 \to x_2) \equiv \neg x_1 \to \neg x_2$. These differ at $x_1 = x_2 = 0$, where the first is $0$ and the second is $1$. The correct equivalence is $\neg(x_1 \to x_2) \equiv x_1 \land \neg x_2$.
- Treating $\to$ as associative. The formulas $(x_1 \to x_2) \to x_3$ and $x_1 \to (x_2 \to x_3)$ differ at $x_1 = x_2 = x_3 = 0$, where the first is $0$ and the second is $1$.
- Reading $x_1 \leftrightarrow x_2 \leftrightarrow x_3$ as "all three have the same value". The connective $\leftrightarrow$ is associative, and the formula is true exactly when an even number of the variables are false, so it is true at $x_1 = 0$, $x_2 = 0$, $x_3 = 1$.
- Thinking that an inconsistent $\Gamma$ entails nothing. It entails everything, by part 6 of the reduction theorem. When a verification condition holds because its assumptions are contradictory, the result is called vacuous, and it is a common source of false confidence in verification.
- Confusing equivalence with equisatisfiability. The formulas $x_1$ and $x_2$ are equisatisfiable and not equivalent. Replacing a formula by an equisatisfiable one preserves the SAT answer, and it may not preserve the set of models.
- Assuming that substitution preserves non-validity. The formula $x_1$ is not valid, and its substitution instance $x_2 \lor \neg x_2$ is valid. Only validity is preserved.

## Exercises

### Exercise 1

Classify each formula as valid, contingent or unsatisfiable: (a) $(x_1 \to x_2) \lor (x_2 \to x_1)$; (b) $(x_1 \land \neg x_1) \to x_2$; (c) $(x_1 \to x_2) \land x_1 \land \neg x_2$; (d) $(x_1 \to x_2) \to (x_2 \to x_1)$; (e) $(x_1 \lor x_2) \land (\neg x_1 \lor x_3) \to x_2 \lor x_3$.

<details><summary>Solution</summary>

(a) Valid. If $v(x_1) = 0$, the first disjunct is true. If $v(x_1) = 1$, the second disjunct is true.

(b) Valid. The antecedent is false under every assignment.

(c) Unsatisfiable. The conjuncts $x_1$ and $\neg x_2$ force $x_1 \to x_2$ to be false.

(d) Contingent. It is true at $x_1 = x_2 = 0$. It is false at $x_1 = 0$, $x_2 = 1$, where $x_1 \to x_2$ is $1$ and $x_2 \to x_1$ is $0$.

(e) Valid. If the antecedent is true and $v(x_1) = 1$, then $\neg x_1 \lor x_3$ gives $x_3$. If $v(x_1) = 0$, then $x_1 \lor x_2$ gives $x_2$. Either way the consequent holds. This is the resolution rule, stated as a formula.

</details>

### Exercise 2

List the subformulas of $(x_1 \land \neg x_2) \to x_1$. State how many distinct subformulas it has, and how many nodes its syntax tree has.

<details><summary>Solution</summary>

The subformulas are $x_1$, $x_2$, $\neg x_2$, $x_1 \land \neg x_2$ and $(x_1 \land \neg x_2) \to x_1$, so there are five distinct subformulas. The syntax tree has six nodes, because $x_1$ occurs twice and each occurrence is its own leaf. This difference between tree size and the number of distinct subformulas is the difference between a tree and a shared DAG representation.

</details>

### Exercise 3

Let $\Gamma = \{x_1 \lor x_2,\; x_1 \to x_3,\; x_2 \to x_4,\; \neg(x_3 \land x_4)\}$. Find all models of $\Gamma$ over $x_1, \dots, x_4$. Then decide whether $\Gamma \models x_1 \leftrightarrow x_3$ and whether $\Gamma \models x_3$.

<details><summary>Solution</summary>

Split on $x_1$.

If $v(x_1) = 1$, then $x_1 \to x_3$ forces $x_3 = 1$, then $\neg(x_3 \land x_4)$ forces $x_4 = 0$, and $x_2 \to x_4$ forces $x_2 = 0$. This gives the model $(x_1, x_2, x_3, x_4) = (1, 0, 1, 0)$.

If $v(x_1) = 0$, then $x_1 \lor x_2$ forces $x_2 = 1$, then $x_2 \to x_4$ forces $x_4 = 1$, and $\neg(x_3 \land x_4)$ forces $x_3 = 0$. This gives the model $(0, 1, 0, 1)$.

These are the only two models. Both give $x_1$ and $x_3$ the same value, so $\Gamma \models x_1 \leftrightarrow x_3$. The second model has $x_3 = 0$, so $\Gamma \not\models x_3$.

</details>

### Exercise 4

State exactly when $(x_1 \leftrightarrow x_2) \leftrightarrow x_3$ is true, and prove that $\leftrightarrow$ is associative.

<details><summary>Solution</summary>

Identify $v(\varphi \leftrightarrow \psi)$ with $1 \oplus v(\varphi) \oplus v(\psi)$, where $\oplus$ is addition modulo 2. This matches the definition: the value is $1$ exactly when the two values are equal.

Then $v((\varphi_1 \leftrightarrow \varphi_2) \leftrightarrow \varphi_3) = 1 \oplus (1 \oplus a \oplus b) \oplus c = a \oplus b \oplus c$, where $a$, $b$, $c$ are the values of $\varphi_1$, $\varphi_2$, $\varphi_3$. In the same way, $v(\varphi_1 \leftrightarrow (\varphi_2 \leftrightarrow \varphi_3)) = 1 \oplus a \oplus (1 \oplus b \oplus c) = a \oplus b \oplus c$. So the two are equivalent.

The formula is true exactly when $a \oplus b \oplus c = 1$, that is, when an odd number of the three variables are true. With three variables this is the same as an even number being false, namely zero or two.

</details>

### Exercise 5

Define $\neg$, $\lor$ and $\land$ using only $\to$ and $\bot$. Then define them using only NAND, where $\varphi \uparrow \psi$ abbreviates $\neg(\varphi \land \psi)$.

<details><summary>Solution</summary>

With $\to$ and $\bot$:

$$
\neg \varphi \equiv \varphi \to \bot, \qquad \varphi \lor \psi \equiv (\varphi \to \bot) \to \psi, \qquad \varphi \land \psi \equiv (\varphi \to (\psi \to \bot)) \to \bot.
$$

With NAND:

$$
\neg \varphi \equiv \varphi \uparrow \varphi, \qquad \varphi \land \psi \equiv (\varphi \uparrow \psi) \uparrow (\varphi \uparrow \psi), \qquad \varphi \lor \psi \equiv (\varphi \uparrow \varphi) \uparrow (\psi \uparrow \psi).
$$

Each equivalence follows from material implication or De Morgan. For example, $(\varphi \to \bot) \to \psi \equiv \neg\neg\varphi \lor \psi \equiv \varphi \lor \psi$.

</details>

### Exercise 6

Prove the semantic deduction theorem: $\Gamma \cup \{\varphi\} \models \psi$ if and only if $\Gamma \models \varphi \to \psi$.

<details><summary>Solution</summary>

Assume $\Gamma \cup \{\varphi\} \models \psi$, and let $v$ satisfy $\Gamma$. If $v(\varphi) = 0$, then $v(\varphi \to \psi) = 1$. If $v(\varphi) = 1$, then $v$ satisfies $\Gamma \cup \{\varphi\}$, so $v(\psi) = 1$ and $v(\varphi \to \psi) = 1$.

Conversely, assume $\Gamma \models \varphi \to \psi$, and let $v$ satisfy $\Gamma \cup \{\varphi\}$. Then $v(\varphi \to \psi) = 1$ and $v(\varphi) = 1$, so $v(\psi) = 1$ by the definition of $\to$.

</details>

### Exercise 7

Prove the substitution lemma $v(\varphi[\psi / x]) = v[x \mapsto v(\psi)](\varphi)$. Deduce that validity is closed under substitution.

<details><summary>Solution</summary>

Let $w = v[x \mapsto v(\psi)]$. Use structural induction on $\varphi$.

Case $\varphi = x$. Then $\varphi[\psi/x] = \psi$, so $v(\varphi[\psi/x]) = v(\psi) = w(x)$.

Case $\varphi$ is an atom other than $x$. Then $\varphi[\psi/x] = \varphi$. Since $w$ and $v$ agree on every variable except $x$ and on the constants, $v(\varphi) = w(\varphi)$.

Case $\varphi = \neg \alpha$. Then $v(\neg \alpha[\psi/x]) = 1 - v(\alpha[\psi/x]) = 1 - w(\alpha) = w(\neg \alpha)$, using the induction hypothesis for $\alpha$.

Case $\varphi = \alpha \circ \beta$. Substitution distributes over $\circ$, the value of $\alpha \circ \beta$ is computed from the values of $\alpha$ and $\beta$, and the induction hypothesis gives $v(\alpha[\psi/x]) = w(\alpha)$ and $v(\beta[\psi/x]) = w(\beta)$. So the two sides are equal.

For the corollary, suppose $\models \varphi$, and let $v$ be any assignment. Then $v(\varphi[\psi/x]) = v[x \mapsto v(\psi)](\varphi) = 1$, because $\varphi$ is true under every assignment, including this one.

</details>

### Exercise 8

Prove that $\{\land, \lor, \to, \leftrightarrow\}$ is not functionally complete. Take the language to have only variables as atoms.

<details><summary>Solution</summary>

Let $v_1$ be the assignment that sends every variable to $1$. By structural induction, $v_1(\varphi) = 1$ for every formula $\varphi$ built from variables with these connectives. Variables satisfy this by definition. In the inductive step, each connective returns $1$ when both arguments are $1$, as its truth table shows.

The unary function $f(0) = 1$, $f(1) = 0$ sends $1$ to $0$. A formula defining $f$ with variable $x_1$ would have value $0$ under $v_1$, which contradicts the invariant. Hence $\neg$ is not definable.

</details>

### Exercise 9

Prove that $\{\neg, \leftrightarrow, \top, \bot\}$ is not functionally complete by showing that $\land$ is not definable.

<details><summary>Solution</summary>

Call a function affine if it has the form $c \oplus a_1 x_1 \oplus \dots \oplus a_n x_n$ with $c, a_i \in \{0, 1\}$ and arithmetic modulo 2. By structural induction, every formula over these connectives defines an affine function. Constants and variables are affine. Also $\neg \varphi$ is $1 \oplus \varphi$, and $\varphi \leftrightarrow \psi$ is $1 \oplus \varphi \oplus \psi$, and each of these preserves the form.

Suppose $x_1 \land x_2$ equals $c \oplus a_1 x_1 \oplus a_2 x_2$ on all four inputs. The input $(0,0)$ gives $c = 0$. The inputs $(1,0)$ and $(0,1)$ give $a_1 = 0$ and $a_2 = 0$. Then the function is constantly $0$, but $1 \land 1 = 1$. This is a contradiction, so $\land$ is not definable.

</details>

### Exercise 10

Prove Craig's interpolation theorem for propositional logic: if $\models \varphi \to \psi$, there is a formula $\chi$ whose variables all occur in both $\varphi$ and $\psi$, such that $\models \varphi \to \chi$ and $\models \chi \to \psi$. Then compute an interpolant for $\varphi = (x_1 \land x_2) \lor (\neg x_1 \land x_3)$ and $\psi = x_2 \lor x_3 \lor x_4$.

<details><summary>Solution</summary>

Use induction on the number $k$ of variables that occur in $\varphi$ and not in $\psi$.

If $k = 0$, take $\chi = \varphi$. Then $\models \varphi \to \varphi$, and $\models \varphi \to \psi$ holds by assumption.

If $k > 0$, pick such a variable $x$ and let $\varphi' = \varphi[\top/x] \lor \varphi[\bot/x]$. The variable $x$ does not occur in $\varphi'$, so $\varphi'$ has $k - 1$ such variables.

First, $\models \varphi \to \varphi'$. If $v(\varphi) = 1$, then by the substitution lemma the disjunct whose constant equals $v(x)$ has the value $v[x \mapsto v(x)](\varphi) = v(\varphi) = 1$.

Second, $\models \varphi' \to \psi$. Suppose $v(\varphi') = 1$. Then $v[x \mapsto b](\varphi) = 1$ for some $b$, by the substitution lemma. Since $\models \varphi \to \psi$, also $v[x \mapsto b](\psi) = 1$. Since $x$ does not occur in $\psi$, the coincidence lemma gives $v(\psi) = 1$.

By the induction hypothesis applied to $\varphi'$ and $\psi$, there is $\chi$ over the shared variables with $\models \varphi' \to \chi$ and $\models \chi \to \psi$. Then $\models \varphi \to \chi$ by transitivity. The constants $\top$ and $\bot$ are needed when no variable is shared.

For the example, $x_1$ is the only variable of $\varphi$ absent from $\psi$. Compute:

$$
\varphi[\top/x_1] \equiv x_2, \qquad \varphi[\bot/x_1] \equiv x_3,
$$

so $\chi = x_2 \lor x_3$. Both $\varphi \to \chi$ and $\chi \to \psi$ are valid, and the only variables of $\chi$ are $x_2$ and $x_3$, which are shared. Interpolants are used to compute reachable-state approximations in [Interpolation-Based Checking](../../../part-2-core-reasoning/08-model-checking/interpolation-based-checking/).

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define formulas, assignments and the value of a formula under an assignment.
- Define validity, satisfiability, entailment, equivalence and equisatisfiability, and give an example separating each pair that is often confused.
- State and prove the reduction of entailment to unsatisfiability and the semantic deduction theorem.
- Decide a formula with up to four variables by truth table, case splitting and falsification search, and extract a countermodel when one exists.
- Prove the functional completeness of $\{\neg, \land, \lor\}$, and prove a set of connectives incomplete using an invariant.
- Prove a statement about all formulas by structural induction.

## Materials

- Huth and Ryan, Logic in Computer Science, 2nd edition. Read the part of the propositional logic chapter on semantics for a second presentation of truth tables, entailment and satisfiability, with many small exercises.
- Gallier, Logic for Computer Science, 2nd edition. Read the propositional logic chapter for a more formal treatment of syntax, unique readability and functional completeness. The second edition is the corrected Dover reprint of 2015.
