# Undecidability of Logic and Incompleteness

Part 1, Chapter 2: Decidability and Complexity.

## Objective

Explain the undecidability of first-order validity and the statements and limits of Gödel's theorems.

## Why this matters

These theorems set the outer limits of the tools in the rest of the program. [Saturation provers](../../../part-2-core-reasoning/06-first-order-proving/saturation-provers/) can run forever on a non-theorem because first-order validity is undecidable. [SMT solvers](../../../part-2-core-reasoning/05-smt/quantifiers/) return `unknown` on quantified formulas and on nonlinear integer arithmetic for the same kind of reason. Gödel's theorems explain why a verifier needs induction schemes and invariants that are not consequences of a fixed set of axioms, and why a [proof assistant](../../../part-4-remaining-methods/) has a trust base it cannot certify from within. As an applied scientist, you will be asked what guarantee a tool can offer, and these results separate real impossibility from a limitation of the current implementation.

## Prerequisites

- [Computability](../computability/), for $\mathrm{HALT}$, PCP and mapping reductions.
- [First-Order Logic](../../01-mathematical-logic/first-order-logic/), for syntax and semantics.
- [Soundness and Completeness](../../01-mathematical-logic/soundness-and-completeness/), for the difference between $\models$ and $\vdash$.
- [First-Order Metatheory](../../01-mathematical-logic/first-order-metatheory/), for Gödel's completeness theorem and compactness.
- [First-Order Theories](../../01-mathematical-logic/first-order-theories/), for theories and axiomatizations.

## Lesson

### Historical setting

In 1928, Hilbert and Ackermann posed the Entscheidungsproblem: find a procedure that decides whether a first-order sentence is valid. Hilbert also hoped for a complete and provably consistent axiomatization of mathematics. In the 1930s, these hopes were resolved in the negative direction. Gödel proved completeness for first-order logic in 1929, and in 1931 he proved incompleteness for arithmetic. Church and Turing independently proved in 1936 that validity is undecidable. To state a negative result about all algorithms, Church and Turing needed a precise definition of algorithm, which is why computability theory and this topic have a common origin.

### Validity is recognizable

By Gödel's completeness theorem, $\models \varphi$ if and only if $\vdash \varphi$ in a suitable proof system. Proofs are finite strings, and checking a proof is decidable. So the following procedure recognizes validity.

```
for n = 0, 1, 2, ...:
    let p be the n-th string
    if p is a correct proof of phi: accept
```

So $\mathrm{VALID}$ is in $\Sigma_1$. Since $\varphi$ is satisfiable exactly when $\neg \varphi$ is not valid, first-order satisfiability is in $\Pi_1$. The procedure does not decide validity, since it runs forever on a non-valid sentence. Resolution provers improve the search strategy, but they cannot change this behavior in general, as the next theorem shows.

### Validity is undecidable

Theorem (Church, Turing, 1936). The set of valid first-order sentences is undecidable, even for a signature with a constant, two unary function symbols and one binary predicate, without equality.

Proof. Reduce PCP over the alphabet $\{0, 1\}$, which is [undecidable](../computability/). Take a signature with a constant $e$, unary function symbols $f_0, f_1$ and a binary predicate $P$. For a string $u = b_1 b_2 \cdots b_l$ and a term $v$, define

$$
f_u(v) = f_{b_l}(\cdots f_{b_2}(f_{b_1}(v)) \cdots),
$$

so that $f_u(v)$ means "$v$ followed by $u$", with $f_\varepsilon(v) = v$. Given an instance $(s_1, t_1), \dots, (s_k, t_k)$, define

$$
\varphi = \Big[ \bigwedge_{i=1}^{k} P(f_{s_i}(e), f_{t_i}(e)) \land \forall v\, \forall w\, \Big( P(v, w) \to \bigwedge_{i=1}^{k} P(f_{s_i}(v), f_{t_i}(w)) \Big) \Big] \to \exists z\, P(z, z).
$$

The map from the instance to $\varphi$ is clearly computable. It remains to prove that $\varphi$ is valid if and only if the instance has a solution.

Suppose $\varphi$ is valid. Consider the structure with universe $\{0, 1\}^*$, with $e$ interpreted as the empty string, $f_b$ as the function that appends the bit $b$, and $P(x, y)$ as the relation "there are $m \ge 1$ and indices $i_1, \dots, i_m$ with $x = s_{i_1} \cdots s_{i_m}$ and $y = t_{i_1} \cdots t_{i_m}$". The hypothesis of $\varphi$ holds in this structure: the first conjunction uses $m = 1$, and the second extends a sequence by one index. So $\exists z\, P(z, z)$ holds, and an element $z$ satisfying $P(z, z)$ gives a solution.

Suppose that $i_1, \dots, i_m$ is a solution, and let $\mathcal{A}$ be a structure in which the hypothesis of $\varphi$ holds. Let $u = s_{i_1} \cdots s_{i_m}$ and $u' = t_{i_1} \cdots t_{i_m}$. By induction on $j \le m$, the hypothesis gives

$$
\mathcal{A} \models P\big(f_{s_{i_1} \cdots s_{i_j}}(e),\ f_{t_{i_1} \cdots t_{i_j}}(e)\big).
$$

The case $j = 1$ is the first conjunction, and the inductive step uses the second conjunction with $f_{s_{i_{j+1}}}(f_{s_{i_1} \cdots s_{i_j}}(e)) = f_{s_{i_1} \cdots s_{i_{j+1}}}(e)$. At $j = m$, since $u = u'$, both arguments are the same term. So $\mathcal{A} \models \exists z\, P(z, z)$. Hence $\varphi$ is valid. $\square$

The undecidability holds in an even smaller vocabulary. Function symbols can be replaced by their graphs as predicates, and a single binary predicate suffices (Kalmár, 1936). The [next topic](../decidable-fragments/) shows that purely monadic signatures are decidable, so the boundary lies between unary and binary predicates.

Corollaries.

- $\mathrm{VALID}$ is $\Sigma_1$-complete, since it is recognizable and PCP, and therefore every recognizable language, reduces to it.
- First-order satisfiability is $\Pi_1$-complete, and hence not recognizable. No procedure can confirm, on every satisfiable sentence, that it is satisfiable.
- A theorem prover that is complete for refutation must fail to terminate on some satisfiable clause set.
- Unsatisfiability of first-order Horn clauses is also undecidable, since $\varphi$ is close to Horn form already. Its negation has clauses of the form $P(\dots)$ and $\neg P(v, w) \lor P(\dots)$, and $\neg P(z, z)$.

### Finite models: Trakhtenbrot's theorem

One might hope to restrict attention to finite structures, since a database or a bounded program is finite. The result is worse in one respect.

Theorem (Trakhtenbrot, 1950). The set of sentences with a finite model is recognizable and undecidable. Therefore, the set of sentences valid in all finite structures is not recognizable.

Proof sketch. Recognizability follows by enumerating finite structures and checking each sentence by evaluating it. For undecidability, reduce from halting on empty input. Given $M$, build a sentence $\tau_M$ that axiomatizes a finite linear order with successor, used for both time and tape positions, with predicates for the tape contents, the head position and the state at each time. The sentence states that a computation starts correctly, follows the transitions and reaches a halting state within the order. The sentence $\tau_M$ has a finite model if and only if $M$ halts. So finite satisfiability is undecidable and recognizable, and its complement, finite validity up to negation, is not recognizable. $\square$

So there is no sound and complete proof calculus for validity over finite structures. This is one reason why tools for finite-domain reasoning, such as finite model finders, search for models and do not try to prove finite validity directly.

| Question | Position | Tool behavior |
|---|---|---|
| Valid in all structures | $\Sigma_1$-complete | A prover confirms it when true, and may run forever otherwise. |
| Satisfiable in some structure | $\Pi_1$-complete | A prover refutes it when false, and may run forever otherwise. |
| Satisfiable in a finite structure | $\Sigma_1$-complete | A finite model finder confirms it when true, and may run forever otherwise. |
| Valid in all finite structures | $\Pi_1$-complete | A finite model finder refutes it when false, and may run forever otherwise. |

There is a gap. A sentence can be satisfiable with only infinite models, as Exercise 4 shows. On such a sentence, a refutation prover does not terminate, since the sentence is satisfiable, and a finite model finder does not terminate, since no finite model exists. Saturation can occasionally report satisfiability if the saturation terminates, but no general guarantee exists.

### Theories, completeness and decidability

A theory is a set of sentences closed under entailment. Let $T$ be a theory.

- $T$ is consistent if it contains no sentence together with its negation.
- $T$ is complete if for every sentence $\varphi$ in its language, $\varphi \in T$ or $\neg \varphi \in T$.
- $T$ is axiomatizable if $T$ is the set of consequences of some decidable set of axioms. Such a theory is recursively enumerable, by enumerating proofs.
- $T$ is decidable if membership in $T$ is decidable.

The word "complete" has two unrelated meanings. A proof system is complete when $\models$ implies $\vdash$, and a theory is complete when it decides every sentence. Gödel's completeness theorem concerns the first meaning, and his incompleteness theorems concern the second.

Theorem. A consistent, complete and axiomatizable theory is decidable.

Proof. Given a sentence $\varphi$, enumerate the theorems of $T$. Since $T$ is complete, either $\varphi$ or $\neg \varphi$ appears in the enumeration. Output the corresponding answer. Consistency makes the answer unique. $\square$

This simple theorem explains the rest of this topic. If $T$ is rich enough to encode an undecidable problem, then it is undecidable, so it cannot be both complete and axiomatizable.

The most useful arithmetic theory for these proofs is Robinson arithmetic $\mathsf{Q}$. Its language has $0, S, +, \cdot$, and it has these finitely many axioms.

$$
\begin{aligned}
&\text{Q1: } \forall x\, (S(x) \ne 0) \qquad &&\text{Q2: } \forall x\, \forall y\, (S(x) = S(y) \to x = y) \\
&\text{Q3: } \forall x\, (x \ne 0 \to \exists y\, x = S(y)) \qquad &&\text{Q4: } \forall x\, (x + 0 = x) \\
&\text{Q5: } \forall x\, \forall y\, (x + S(y) = S(x + y)) \qquad &&\text{Q6: } \forall x\, (x \cdot 0 = 0) \\
&\text{Q7: } \forall x\, \forall y\, (x \cdot S(y) = x \cdot y + x)
\end{aligned}
$$

Peano arithmetic $\mathsf{PA}$ is $\mathsf{Q}$ plus the induction schema for all formulas. Write $\bar{n}$ for the numeral $S^n(0)$.

A sentence is $\Sigma_1$ if it has the form $\exists y\, \theta(y)$, with $\theta$ having only bounded quantifiers. Two facts about $\mathsf{Q}$ drive the theorems, and this topic states them without full proofs.

Fact 1 ($\Sigma_1$-completeness). If a $\Sigma_1$ sentence is true in the natural numbers, then it is provable in $\mathsf{Q}$. The reason is that $\mathsf{Q}$ proves all numeral computations, such as $\bar{2} + \bar{3} = \bar{5}$, and it proves that a bounded quantifier over numerals is a finite conjunction or disjunction.

Fact 2 (representability). Every computable function $g$ is represented in $\mathsf{Q}$ by a formula $D_g(x, y)$, so that for each $n$, $\mathsf{Q} \vdash \forall y\, (D_g(\bar{n}, y) \leftrightarrow y = \overline{g(n)})$. The difficulty lies in encoding sequences, which is needed for recursion. Gödel's $\beta$ function solves this using the Chinese remainder theorem, so that finite sequences are coded by two numbers using only $+$ and $\cdot$.

As a consequence, for each machine $M$ and input $w$, there is a $\Sigma_1$ sentence $H_{M,w}$, which says that a code of a halting computation exists, and which is true exactly when $M$ halts on $w$.

### A computability proof of incompleteness

Theorem. Let $T$ be a consistent, axiomatizable theory in the language of arithmetic that contains $\mathsf{Q}$ and is $\Sigma_1$-sound, meaning that all its $\Sigma_1$ theorems are true. Then $T$ is incomplete.

Proof. Suppose $T$ is complete. Decide $\mathrm{HALT}$ as follows: given $\langle M, w \rangle$, enumerate the theorems of $T$ until $H_{M,w}$ or $\neg H_{M,w}$ appears.

- If $M$ halts on $w$, then $H_{M,w}$ is true, so by Fact 1, $T$ proves it. Consistency excludes a proof of its negation.
- If $M$ does not halt on $w$, then $H_{M,w}$ is false, so $\Sigma_1$-soundness excludes a proof of it, and completeness gives a proof of $\neg H_{M,w}$.

So this procedure decides $\mathrm{HALT}$, which is a contradiction. $\square$

The same argument gives a concrete corollary. Any such $T$ has a machine $M$ and an input $w$ such that $M$ does not halt on $w$ and $T$ does not prove this fact. If this were false, enumerating proofs would recognize $\overline{\mathrm{HALT}}$. So for any fixed sound proof system, some nonterminating program has no proof of nontermination in it, and this applies to every verifier based on a fixed, axiomatized theory.

### Gödel's first theorem and Rosser's refinement

This proof constructs an independent sentence and weakens the assumption on $T$.

Arithmetization. Assign a number $\ulcorner \varphi \urcorner$ to each formula and each proof. If $T$ is axiomatizable, then the relation "$y$ is the code of a $T$-proof of the formula with code $x$" is decidable, so it is represented by a formula $\mathrm{Prf}_T(y, x)$ that behaves correctly on numerals. Let $\mathrm{Prov}_T(x) = \exists y\, \mathrm{Prf}_T(y, x)$.

Lemma (diagonal lemma). For each formula $\psi(x)$ with one free variable, there is a sentence $G$ with $\mathsf{Q} \vdash G \leftrightarrow \psi(\ulcorner G \urcorner)$.

Proof. Define the computable function $\mathrm{diag}$ as follows: if $n$ is the code of a formula $\chi(x)$, then $\mathrm{diag}(n) = \ulcorner \chi(\bar{n}) \urcorner$. Let $D(x, y)$ represent $\mathrm{diag}$ in $\mathsf{Q}$. Let

$$
\theta(x) = \exists y\, (D(x, y) \land \psi(y)), \qquad m = \ulcorner \theta \urcorner, \qquad G = \theta(\bar{m}).
$$

By definition, $\mathrm{diag}(m) = \ulcorner G \urcorner$. So $\mathsf{Q} \vdash \forall y\, (D(\bar{m}, y) \leftrightarrow y = \ulcorner G \urcorner)$. Therefore,

$$
\mathsf{Q} \vdash G \leftrightarrow \exists y\, (y = \ulcorner G \urcorner \land \psi(y)) \leftrightarrow \psi(\ulcorner G \urcorner). \quad \square
$$

The construction mirrors the machine $D$ in the proof of the undecidability of $A_{\mathrm{TM}}$: a formula is applied to its own code.

Theorem (Gödel, 1931). Let $T$ be consistent, axiomatizable and contain $\mathsf{Q}$, and let $G$ be a sentence with $T \vdash G \leftrightarrow \neg \mathrm{Prov}_T(\ulcorner G \urcorner)$. Then $T \nvdash G$. If $T$ is also $\omega$-consistent, then $T \nvdash \neg G$.

Here, $\omega$-consistent means that there is no formula $\chi(y)$ such that $T \vdash \exists y\, \chi(y)$ and $T \vdash \neg \chi(\bar{n})$ for each $n$.

Proof. Suppose $T \vdash G$. Let $p$ be a code of the proof. Then $\mathsf{Q} \vdash \mathrm{Prf}_T(\bar{p}, \ulcorner G \urcorner)$, so $T \vdash \mathrm{Prov}_T(\ulcorner G \urcorner)$. But $T \vdash \neg \mathrm{Prov}_T(\ulcorner G \urcorner)$ by the choice of $G$, and this contradicts consistency.

Suppose $T \vdash \neg G$. Then $T \vdash \exists y\, \mathrm{Prf}_T(y, \ulcorner G \urcorner)$. By the first part, $G$ has no proof, so for each $n$, $T \vdash \neg \mathrm{Prf}_T(\bar{n}, \ulcorner G \urcorner)$. This contradicts $\omega$-consistency. $\square$

If $T$ is sound, then $G$ is true in the natural numbers, since it says of itself that it is not provable, and it is not provable. "Truth" here means truth in the standard model. In a nonstandard model of $T + \neg G$, $\neg G$ holds because a nonstandard element is a "proof code" that corresponds to no real proof.

Theorem (Rosser, 1936). Let $T$ be consistent, axiomatizable and contain $\mathsf{Q}$. Then $T$ is incomplete.

Proof sketch. Write $\mathrm{neg}$ for a term representing the map $\ulcorner \varphi \urcorner \mapsto \ulcorner \neg \varphi \urcorner$. Let

$$
R(x) = \exists y\, \big(\mathrm{Prf}_T(y, x) \land \forall z \le y\, \neg \mathrm{Prf}_T(z, \mathrm{neg}(x))\big),
$$

which says that a proof of $x$ appears before any proof of its negation. By the diagonal lemma, take $B$ with $T \vdash B \leftrightarrow \neg R(\ulcorner B \urcorner)$.

Suppose $T \vdash B$, with proof code $p$. By consistency, $\neg B$ has no proof, so $\mathsf{Q}$ proves $\neg \mathrm{Prf}_T(\bar{n}, \ulcorner \neg B \urcorner)$ for all $n$. Hence $T \vdash R(\ulcorner B \urcorner)$, witnessed by $p$. Then $T \vdash \neg B$, which contradicts consistency.

Suppose $T \vdash \neg B$, with proof code $q$. Then $T \vdash R(\ulcorner B \urcorner)$. By consistency, $B$ has no proof, so $\mathsf{Q}$ refutes $\mathrm{Prf}_T(\bar{n}, \ulcorner B \urcorner)$ for all $n \le q$. For any $y \ge \bar{q}$, the bounded quantifier reaches the proof $q$ of $\neg B$, so the condition in $R$ fails. Since $\mathsf{Q}$ proves $y \le \bar{q} \lor \bar{q} \le y$, this gives $T \vdash \neg R(\ulcorner B \urcorner)$, which contradicts consistency. $\square$

As a corollary, every consistent theory containing $\mathsf{Q}$ is undecidable, whether or not it is axiomatizable, because a decidable consistent theory could be extended to a complete, consistent and axiomatizable one by Lindenbaum's construction. This gives a second proof that first-order validity is undecidable: since $\mathsf{Q}$ is finitely axiomatized, $\varphi$ is a theorem of $\mathsf{Q}$ exactly when $\bigwedge \mathsf{Q} \to \varphi$ is valid.

### Gödel's second theorem

Let $\mathrm{Con}_T = \neg \mathrm{Prov}_T(\ulcorner \bot \urcorner)$. Suppose that $\mathrm{Prov}_T$ satisfies the Hilbert-Bernays-Löb derivability conditions, for all $\varphi, \psi$.

- D1: if $T \vdash \varphi$, then $T \vdash \mathrm{Prov}_T(\ulcorner \varphi \urcorner)$.
- D2: $T \vdash \mathrm{Prov}_T(\ulcorner \varphi \to \psi \urcorner) \to (\mathrm{Prov}_T(\ulcorner \varphi \urcorner) \to \mathrm{Prov}_T(\ulcorner \psi \urcorner))$.
- D3: $T \vdash \mathrm{Prov}_T(\ulcorner \varphi \urcorner) \to \mathrm{Prov}_T(\ulcorner \mathrm{Prov}_T(\ulcorner \varphi \urcorner) \urcorner)$.

These hold for standard definitions of provability in theories containing $\mathsf{PA}$, and in substantially weaker arithmetic.

Theorem (Gödel, 1931). If $T$ is consistent, contains $\mathsf{Q}$ and satisfies D1 to D3, then $T \nvdash \mathrm{Con}_T$.

Proof. Write $\square \varphi$ for $\mathrm{Prov}_T(\ulcorner \varphi \urcorner)$. Let $G$ satisfy $T \vdash G \leftrightarrow \neg \square G$.

1. From $T \vdash G \to \neg \square G$, using D1 and D2, $T \vdash \square G \to \square \neg \square G$.
2. By D3, $T \vdash \square G \to \square \square G$.
3. From $T \vdash \square G \to (\neg \square G \to \bot)$, using D1 and D2, $T \vdash \square \square G \land \square \neg \square G \to \square \bot$. Together with steps 1 and 2, $T \vdash \square G \to \square \bot$.
4. By contraposition, $T \vdash \neg \square \bot \to \neg \square G$, and thus $T \vdash \mathrm{Con}_T \to G$.

If $T \vdash \mathrm{Con}_T$, then $T \vdash G$, which contradicts the first theorem. $\square$

The proof formalizes the first theorem within $T$. Note how the result depends on how $\mathrm{Con}_T$ is expressed. There are nonstandard consistency statements, including Rosser-style ones, that a theory can prove, and that fail D1 to D3. They do not express consistency in the sense the theorem addresses.

### Limits of the theorems

The theorems have precise hypotheses, and each one matters.

| Hypothesis | Example without it | What happens |
|---|---|---|
| The theory is axiomatizable. | True arithmetic, the set of all sentences true in the natural numbers. | It is complete and consistent, and it is not recursively enumerable. |
| The theory can represent computation. | Presburger arithmetic, which has no multiplication. | It is complete and decidable. |
| The theory can represent computation. | Real closed fields, in which the integers are not definable. | It is complete and decidable by Tarski's quantifier elimination. |
| The theory is consistent. | An inconsistent theory. | It proves every sentence, so it is complete and useless. |

Further points.

- Gödel's completeness theorem and his incompleteness theorem do not conflict. An independent sentence $G$ is true in some models of $T$ and false in others, so $T \not\models G$ and $T \nvdash G$ agree.
- The theorems concern fixed formal systems. Adding $G$ as an axiom gives a stronger system, with its own independent sentence.
- Unprovability is not a defect of the mathematical problem in question, and it does not say that a statement is unknowable. $\mathrm{Con}_{\mathsf{PA}}$ is provable in stronger theories, including Gentzen's 1936 proof by transfinite induction up to $\varepsilon_0$.
- Natural mathematical statements can be independent. Goodstein's theorem and the Paris-Harrington theorem are true and unprovable in $\mathsf{PA}$, and the continuum hypothesis is independent of ZFC if ZFC is consistent.
- The theorems do not imply that human reasoning exceeds machines. Such arguments need extra premises, and those premises are disputed.
- Undefinability of truth. Tarski's theorem says that no arithmetic formula defines truth for arithmetic sentences, as Exercise 7 shows. So $\mathrm{Th}(\mathbb{N})$ is not even in the arithmetical hierarchy.

### Hilbert's tenth problem

Theorem (Matiyasevich, 1970, building on Davis, Putnam and Robinson). A set of natural numbers is recursively enumerable if and only if it is Diophantine, that is, of the form $\{a : \exists \bar{x}\, p(a, \bar{x}) = 0\}$ for a polynomial $p$ with integer coefficients.

Hence the solvability of Diophantine equations is undecidable, and this holds with only existential quantifiers. This is the reason why quantifier-free nonlinear integer arithmetic (QF_NIA) is undecidable. It also gives the sharpest form of incompleteness for arithmetic: for each sound axiomatized $T$, there is a polynomial equation with no solutions such that $T$ does not prove it has no solutions.

### Consequences for automated reasoning

- First-order provers. Refutational completeness is possible, and termination on all inputs is not. Practical systems accept incompleteness in finite time, using strategies, timeouts and portfolio runs.
- SMT with quantifiers. Answers include `unknown`, since instantiation techniques cannot be complete for an undecidable theory. Decidable fragments and bounded versions are the way to get a guarantee.
- Inductive theorems. A statement such as commutativity of addition is true for natural numbers, and not a consequence of the recursive definitions alone in first-order logic, as Example 2 shows. An induction principle must be supplied, and the required induction hypothesis may need strengthening, a problem that also appears as [finding a loop invariant](../../../part-2-core-reasoning/07-deductive-verification/loop-invariants/).
- Program logics. Cook's 1978 theorem shows that Hoare logic is complete relative to an oracle for the assertion language. The oracle cannot be replaced by an axiomatized theory for arithmetic assertions, since true arithmetic is not recursively enumerable.
- [Constrained Horn clauses](../../../part-2-core-reasoning/08-model-checking/horn-clauses/). Satisfiability over linear integer arithmetic is undecidable, as Exercise 11 shows, and so a CHC solver must diverge or answer `unknown` on some inputs.
- Proof assistants. A proof assistant whose logic meets the hypotheses cannot prove its own consistency, unless inconsistent. A kernel's correctness proof must rest on additional assumptions or a stronger metatheory. The trust base can be made small and explicit, and it cannot be removed.

## Worked examples

### Example 1: the reduction from PCP on a specific instance

Take the instance $(s_1, t_1) = (0, 01)$ and $(s_2, t_2) = (10, 0)$. The sequence $1, 2$ is a solution, because $0 \cdot 10 = 01 \cdot 0 = 010$.

Terms, with $f_u(v)$ appending the bits of $u$ to $v$ in order:

$$
f_{s_1}(v) = f_0(v), \quad f_{t_1}(v) = f_1(f_0(v)), \quad f_{s_2}(v) = f_0(f_1(v)), \quad f_{t_2}(v) = f_0(v).
$$

The sentence is:

$$
\Big[ P(f_0(e), f_1(f_0(e))) \land P(f_0(f_1(e)), f_0(e)) \land \forall v\, \forall w\, \big(P(v, w) \to P(f_0(v), f_1(f_0(w))) \land P(f_0(f_1(v)), f_0(w))\big) \Big] \to \exists z\, P(z, z).
$$

To confirm validity by refutation, negate and put in clause form. The variables are universally quantified.

```
C1: P(f0(e), f1(f0(e)))
C2: P(f0(f1(e)), f0(e))
C3: not P(v,w) or P(f0(v), f1(f0(w)))
C4: not P(v,w) or P(f0(f1(v)), f0(w))
C5: not P(z,z)
```

Now use the solution $1, 2$ as a resolution proof. Resolve C1 with C4, using the unifier $v := f_0(e)$ and $w := f_1(f_0(e))$:

```
C6: P(f0(f1(f0(e))), f0(f1(f0(e))))
```

Both arguments are the term for the string $010$. Resolve C6 with C5, with $z := f_0(f_1(f_0(e)))$, to get the empty clause. So the solution sequence translates directly to the proof steps, and the matching string translates to the witness for $z$.

Now see what happens with an instance without a solution, $(1, 10)$ and $(10, 01)$ from the [Computability](../computability/) topic. The clause set has only the two ground unit clauses and two rules, which generate infinitely many derived unit clauses $P(u, u')$. Forward derivation from these clauses generates an endless sequence of them with no empty clause. This is the nontermination that the theorem predicts for some inputs, and here it is visible on a specific one.

### Example 2: a nonstandard model of Q

This example proves that $\mathsf{Q} \nvdash \forall x\, (0 + x = x)$, even though $\mathsf{Q} \vdash 0 + \bar{n} = \bar{n}$ for every numeral. It gives a counterexample showing why induction is needed for universally quantified facts.

Let the universe be $\mathbb{N} \cup \{a, b\}$, where $a, b$ are new elements. Define $S$ as usual on $\mathbb{N}$, with $S(a) = a$ and $S(b) = b$.

Define addition by the requirements of Q4 and Q5. For $n \in \mathbb{N}$, these determine $x + n$: $m + n$ is the usual sum, $a + n = a$ and $b + n = b$. For the new elements, set

$$
x + a = b, \qquad x + b = a \qquad \text{for all } x.
$$

Define multiplication as follows, for $n \in \mathbb{N}$:

$$
m \cdot n \text{ is usual}, \quad a \cdot 0 = b \cdot 0 = 0, \quad a \cdot (n + 1) = b, \quad b \cdot (n + 1) = a,
$$

and for the new elements:

$$
m \cdot a = m \cdot b = a, \quad a \cdot a = a \cdot b = b, \quad b \cdot a = b \cdot b = a.
$$

Check all axioms.

- Q1. $S(x) \ne 0$ holds, since $S(a) = a$, $S(b) = b$ and successors of numbers are positive.
- Q2. $S$ is injective on $\mathbb{N}$, it fixes $a$ and $b$, and it maps no number to $a$ or $b$.
- Q3. The nonzero element $n + 1$ has predecessor $n$, and $a = S(a)$, $b = S(b)$.
- Q4. By definition, $x + 0 = x$.
- Q5, with $y \in \mathbb{N}$. For $x \in \mathbb{N}$, this is ordinary arithmetic. For $x = a$, $a + S(y) = a = S(a) = S(a + y)$, and $x = b$ is the same.
- Q5, with $y = a$. Here $x + S(a) = x + a = b$, and $S(x + a) = S(b) = b$. The case $y = b$ is the same, with $a$ in place of $b$.
- Q6. By definition, $x \cdot 0 = 0$.
- Q7, with $y \in \mathbb{N}$. For $x \in \mathbb{N}$, this is ordinary arithmetic. For $x = a$ and $y = 0$: $a \cdot 1 = b$ and $a \cdot 0 + a = 0 + a = b$. For $x = a$ and $y \ge 1$: $a \cdot (y + 1) = b$ and $a \cdot y + a = b + a = b$. For $x = b$ and $y = 0$: $b \cdot 1 = a$ and $0 + b = a$. For $x = b$ and $y \ge 1$: $b \cdot (y + 1) = a$ and $a + b = a$.
- Q7, with $y = a$. The equation is $x \cdot a = x \cdot a + x$, since $S(a) = a$. For $x = m \in \mathbb{N}$: $a = a + m$. For $x = a$: $b = b + a = b$. For $x = b$: $a = a + b = a$. The case $y = b$ gives the same computations, since $x \cdot b = x \cdot a$ for all $x$.

So this is a model of $\mathsf{Q}$. In it, $0 + a = b \ne a$, so $\forall x\, (0 + x = x)$ fails. By soundness, $\mathsf{Q}$ does not prove that sentence. A script verified all the axioms for this model on a window of natural numbers together with $a$ and $b$.

The lesson is general. The numeral instances are all provable, and a first-order theory without induction cannot pass to the universally quantified statement. A verifier with recursive definitions as axioms and no induction faces this exact situation. Note also that $\mathsf{PA}$ does prove this sentence, by induction on $x$.

### Example 3: using completeness to prove decidability, and its contrapositive

Consider dense linear orders without endpoints (DLO), a theory with finitely many axioms. By Cantor's theorem, all countable models of DLO are isomorphic. By the Löwenheim-Skolem theorem, if a sentence were true in one model of DLO and false in another, then it would differ between two countable models, which is impossible. So DLO is complete. The theorem in the lesson then gives decidability, with no algorithm designed by hand.

Now apply the contrapositive to arithmetic. $\mathsf{PA}$ is axiomatizable and it represents all computable functions, so its set of theorems is undecidable. Since it is consistent, it must be incomplete. The two cases show the general pattern: for a consistent axiomatizable theory, completeness implies decidability, so a theory that represents all computable functions cannot be complete.

## Common mistakes

- Confusing the two meanings of "complete". A complete proof system proves all semantic consequences, and a complete theory decides each sentence of its language.
- Stating Gödel's first theorem as "there are true sentences that are not provable" with no hypotheses. The precise statement requires a consistent, axiomatizable theory that represents enough arithmetic.
- Applying incompleteness to Presburger arithmetic or real closed fields. Those theories are complete and decidable, since they cannot represent all computation.
- Reading incompleteness as a failure of first-order logic. Every first-order theory has a complete proof calculus, and $T \nvdash G$ corresponds to the existence of a model of $T$ where $G$ fails.
- Treating undecidability of validity as if it meant that proofs cannot be found. Validity is recognizable, so every valid sentence has a proof that a prover can find in finite time.
- Claiming that "the Gödel sentence is true" without saying where. It is true in the standard model when the theory is sound, and false in some nonstandard models of the theory.
- Assuming that restricting to finite models makes logic easier. Finite validity is not even recognizable.
- Saying that $\mathrm{Con}_T$ being unprovable casts doubt on the theory. Unprovability in $T$ holds for consistent theories, so it provides no evidence of inconsistency, and an inconsistent theory proves $\mathrm{Con}_T$ along with everything else.
- Stating that $\mathsf{PA}$ is decidable because it has axioms that can be listed. Axiomatizable means that the theorems are recursively enumerable, and $\mathsf{PA}$ is undecidable.
- Believing that QF_NIA is decidable because it has no quantifiers. Its free variables are implicitly existential, and Matiyasevich's theorem makes this problem undecidable.

## Exercises

### Exercise 1

State Gödel's completeness theorem and his first incompleteness theorem, each in one sentence, and explain why they do not conflict.

<details><summary>Solution</summary>

Completeness theorem: for first-order logic, $\Gamma \models \varphi$ implies $\Gamma \vdash \varphi$. First incompleteness theorem, in Rosser's form: a consistent, axiomatizable theory containing $\mathsf{Q}$ has a sentence such that neither it nor its negation is a theorem.

They do not conflict because the independent sentence $\varphi$ is true in some models of the theory and false in others. Thus $T \not\models \varphi$ and $T \not\models \neg \varphi$, and completeness then predicts exactly the unprovability that the incompleteness theorem states.

</details>

### Exercise 2

Prove that first-order satisfiability is not recognizable, and state what this says about a tool that claims to certify first-order satisfiability on all inputs.

<details><summary>Solution</summary>

$\mathrm{VALID}$ is recognizable and undecidable, so its complement is not recognizable. The map $\varphi \mapsto \neg \varphi$ reduces the complement of $\mathrm{VALID}$ to satisfiability, since $\varphi$ is not valid if and only if $\neg \varphi$ is satisfiable. If satisfiability were recognizable, then the complement of $\mathrm{VALID}$ would be as well, which is false.

So no tool that always terminates on satisfiable inputs and only accepts satisfiable sentences can exist. A tool can certify satisfiability only for a restricted class of sentences, for example by a finite model or by a terminating saturation, and it must run forever or answer `unknown` on others.

</details>

### Exercise 3

Write the sentence of the reduction for the instance $(1, 10), (10, 01)$, and show directly that it is not valid.

<details><summary>Solution</summary>

The terms are $f_{s_1}(v) = f_1(v)$, $f_{t_1}(v) = f_0(f_1(v))$, $f_{s_2}(v) = f_0(f_1(v))$ and $f_{t_2}(v) = f_1(f_0(v))$. The sentence is:

$$
\Big[ P(f_1(e), f_0(f_1(e))) \land P(f_0(f_1(e)), f_1(f_0(e))) \land \forall v\, \forall w\, \big(P(v, w) \to P(f_1(v), f_0(f_1(w))) \land P(f_0(f_1(v)), f_1(f_0(w)))\big) \Big] \to \exists z\, P(z, z).
$$

Take the structure with universe $\{0, 1\}^*$, $e$ as the empty string, $f_b$ appending $b$, and $P(x, y)$ meaning that $x$ and $y$ are obtained from a sequence of at least one domino index. The hypothesis holds. The conclusion would give a solution, and the [Computability](../computability/) topic shows that this instance has none. So the sentence is false in this structure, and thus it is not valid.

</details>

### Exercise 4

Give a satisfiable first-order sentence with only infinite models, and prove it. Explain what a refutation prover and a finite model finder do on this sentence. Then state its quantifier prefix after conversion to prenex form.

<details><summary>Solution</summary>

Let

$$
\sigma = \forall x\, \neg R(x, x) \land \forall x\, \forall y\, \forall z\, (R(x, y) \land R(y, z) \to R(x, z)) \land \forall x\, \exists y\, R(x, y).
$$

It is satisfied by $(\mathbb{N}, <)$. In a finite model, start from any element and repeatedly take a successor by the third conjunct. By finiteness, an element repeats, so transitivity gives $R(u, u)$ for some $u$, which contradicts the first conjunct. So all models are infinite.

A refutation prover cannot derive the empty clause, because $\sigma$ is satisfiable, and saturation with Skolem function $f(x)$ generates $R(x, f(x))$, $R(x, f(f(x)))$ and so on without an end, unless a suitable ordering and redundancy elimination happen to close the saturation. A finite model finder does not terminate, since no finite model exists. So $\sigma$ lies in the gap between the two methods.

A prenex form is $\forall x_1\, \forall x_2\, \forall x_3\, \exists y\, \psi$, obtained by using $x_1$ in the irreflexivity and successor conjuncts and $x_1, x_2, x_3$ in transitivity. So the class with prefix $\forall^3 \exists$ lacks the finite model property. The [next topic](../decidable-fragments/) explains the significance of this.

</details>

### Exercise 5

Prove that $\mathrm{Th}(\mathbb{N})$, the set of sentences of arithmetic true in the natural numbers, is not recursively enumerable. Explain why this does not contradict the fact that it is complete.

<details><summary>Solution</summary>

Reduce $\overline{\mathrm{HALT}}$ to $\mathrm{Th}(\mathbb{N})$, with $\langle M, w \rangle \mapsto \neg H_{M,w}$. The sentence is true exactly when $M$ does not halt on $w$. Since $\overline{\mathrm{HALT}}$ is not recognizable, $\mathrm{Th}(\mathbb{N})$ is not recognizable.

There is no conflict. The theorem connecting completeness to decidability needs axiomatizability. $\mathrm{Th}(\mathbb{N})$ is complete and consistent, and it is not axiomatizable, since an axiomatizable theory is recursively enumerable.

</details>

### Exercise 6

Using the model of Example 2, show that $\mathsf{Q}$ does not prove $\forall x\, \forall y\, (x + y = y + x)$. Then explain why $\mathsf{Q}$ still proves every instance with numerals.

<details><summary>Solution</summary>

In the model, $a + b = a$ by the definition $x + b = a$, and $b + a = b$ by the definition $x + a = b$. These differ, so the sentence fails in a model of $\mathsf{Q}$, and by soundness it is not provable.

For numerals $\bar{m}, \bar{n}$, the axioms Q4 and Q5 compute $\bar{m} + \bar{n}$ down to the numeral $\overline{m + n}$, in $n$ steps. Since $m + n = n + m$, the two computations end in the same numeral. So $\mathsf{Q} \vdash \bar{m} + \bar{n} = \bar{n} + \bar{m}$. This is a true closed equation, and it is an instance of Fact 1.

</details>

### Exercise 7

Prove Tarski's undefinability theorem. There is no formula $\mathrm{True}(x)$ of arithmetic such that, for all sentences $\varphi$, $\mathbb{N} \models \varphi$ if and only if $\mathbb{N} \models \mathrm{True}(\ulcorner \varphi \urcorner)$.

<details><summary>Solution</summary>

Suppose that such a formula exists. Apply the diagonal lemma to $\psi(x) = \neg \mathrm{True}(x)$, which gives a sentence $L$ with $\mathsf{Q} \vdash L \leftrightarrow \neg \mathrm{True}(\ulcorner L \urcorner)$. The natural numbers are a model of $\mathsf{Q}$, so $\mathbb{N} \models L \leftrightarrow \neg \mathrm{True}(\ulcorner L \urcorner)$. By the assumption on $\mathrm{True}$, $\mathbb{N} \models L \leftrightarrow \neg L$, which is impossible.

This is the liar paradox made precise. The reason it gives a theorem, and not a paradox, is that the assumption of a definable truth predicate is what fails. In contrast, $\mathrm{Prov}_T$ is definable, so truth and provability differ, and this difference gives another proof of incompleteness for sound theories.

</details>

### Exercise 8

Let $T$ be consistent and meet the hypotheses of the second incompleteness theorem. Prove that $T + \neg \mathrm{Con}_T$ is consistent. If $T$ is sound, state whether this new theory is sound, and describe what its models look like.

<details><summary>Solution</summary>

If $T + \neg \mathrm{Con}_T$ were inconsistent, then $T \vdash \neg \neg \mathrm{Con}_T$, so $T \vdash \mathrm{Con}_T$. This contradicts the second theorem. So the new theory is consistent, and by the completeness theorem it has a model.

If $T$ is sound, then $\mathrm{Con}_T$ is true in $\mathbb{N}$, so the new theory has a false axiom and is unsound. Its models are nonstandard. In such a model, $\exists y\, \mathrm{Prf}_T(y, \ulcorner \bot \urcorner)$ holds, with a witness $y$ that is a nonstandard element, not the code of any actual finite proof.

This illustrates that a consistent theory can prove false statements, so consistency alone does not provide soundness.

</details>

### Exercise 9

Prove Löb's theorem: if $T$ meets the hypotheses of the second theorem and $T \vdash \square \varphi \to \varphi$, then $T \vdash \varphi$. Explain what this says about a kernel that adds a reflection rule for its own proofs.

<details><summary>Solution</summary>

By the diagonal lemma, take $L$ with $T \vdash L \leftrightarrow (\square L \to \varphi)$.

1. From $T \vdash L \to (\square L \to \varphi)$, D1 and D2 yield $T \vdash \square L \to \square(\square L \to \varphi)$.
2. D2 yields $T \vdash \square(\square L \to \varphi) \to (\square \square L \to \square \varphi)$.
3. With D3, $T \vdash \square L \to \square \square L$. Together with steps 1 and 2, $T \vdash \square L \to \square \varphi$.
4. With the hypothesis $T \vdash \square \varphi \to \varphi$, $T \vdash \square L \to \varphi$.
5. By the choice of $L$, $T \vdash L$.
6. By D1, $T \vdash \square L$, and by step 4, $T \vdash \varphi$.

Consequence. A theory proves the reflection principle $\square \varphi \to \varphi$ only for sentences $\varphi$ that it already proves. So a system cannot adopt general reflection over itself as a theorem. If it does adopt it as a new axiom schema, then the result is a stronger theory, and the new system cannot in turn prove reflection for itself. Taking $\varphi = \bot$ in Löb's theorem gives the second incompleteness theorem.

</details>

### Exercise 10

Prove that the following problem is undecidable: given a polynomial with integer coefficients, in QF_NIA syntax, is there an integer solution of $p(\bar{x}) = 0$? Use Matiyasevich's theorem, which is stated over natural numbers, and Lagrange's four-square theorem. Then state which restriction makes the problem decidable, and which remains undecidable.

<details><summary>Solution</summary>

Matiyasevich's theorem provides, for each recursively enumerable set, a Diophantine definition with solutions over natural numbers. Take a recursively enumerable, undecidable set $A$ and its polynomial $p(a, \bar{x})$. For each $a \in \mathbb{N}$, consider the polynomial $p(a, \bar{x})$, and substitute for each $x_i$ a sum of four squares, $y_{i,1}^2 + y_{i,2}^2 + y_{i,3}^2 + y_{i,4}^2$. By Lagrange, each natural number is such a sum, and each sum is a natural number. So $a \in A$ if and only if the new polynomial has an integer solution. This is a mapping reduction from $A$.

Restrictions:

- Fixing a bit width makes the problem finite, and QF_BV over $n$-bit machine arithmetic is decidable. It has a different meaning, since it has modular arithmetic.
- Bounding each variable to a finite range makes it decidable.
- Replacing the integers with the reals makes it decidable, by Tarski's theorem. The solvability of polynomial equations over the reals is in PSPACE.
- Restricting to linear polynomials gives QF_LIA, which is NP-complete.
- Allowing arbitrary degree over the integers remains undecidable, and this also holds with a fixed small number of variables, a further refinement of the theorem that this topic does not need.

</details>

### Exercise 11

Show that satisfiability of constrained Horn clauses over linear integer arithmetic is undecidable, by reducing the halting problem for [two-counter machines](../computability/). A CHC set is satisfiable if there is an interpretation of its predicates that makes all clauses valid.

<details><summary>Solution</summary>

Let the machine have locations $1, \dots, L$, with start location $1$, halting location $L$, and counters $c_1, c_2$ initially zero. Use one predicate $\mathrm{Inv}(p, c_1, c_2)$ over integers, or a predicate $\mathrm{Inv}_p$ per location. The clauses are as follows.

Initial clause.

$$
p = 1 \land c_1 = 0 \land c_2 = 0 \to \mathrm{Inv}(p, c_1, c_2).
$$

For an increment instruction at location $l$ for $c_1$, going to location $l'$:

$$
\mathrm{Inv}(l, c_1, c_2) \to \mathrm{Inv}(l', c_1 + 1, c_2).
$$

For a decrement-or-branch instruction at location $l$, which goes to $l'$ on positive and to $l''$ on zero:

$$
\mathrm{Inv}(l, c_1, c_2) \land c_1 > 0 \to \mathrm{Inv}(l', c_1 - 1, c_2),
$$

$$
\mathrm{Inv}(l, c_1, c_2) \land c_1 = 0 \to \mathrm{Inv}(l'', c_1, c_2).
$$

Query clause.

$$
\mathrm{Inv}(L, c_1, c_2) \to \bot.
$$

Correctness. The least interpretation of $\mathrm{Inv}$ for the non-query clauses is exactly the set of reachable configurations, by induction on the length of runs. Every interpretation that satisfies these clauses contains it. So a satisfying interpretation exists if and only if the least one satisfies the query clause, if and only if the location $L$ is not reachable. So the machine does not halt if and only if the CHC set is satisfiable. The map from machines to clauses is computable, and the two-counter halting problem is undecidable, so CHC satisfiability is undecidable.

Unsatisfiability is in $\Sigma_1$, since a finite derivation of the query, which matches a finite counterexample trace, certifies it.

</details>

### Exercise 12

A colleague says: "Gödel's theorem means that we can never formally verify a compiler, since we cannot prove all truths about it." Explain precisely what is correct and incorrect in this claim.

<details><summary>Solution</summary>

Incorrect part. Incompleteness says that some sentences are independent of a fixed theory, and it does not say that any given sentence is independent. Compiler correctness for a specific compiler is a specific statement, and proving it in a strong enough system, such as those used in proof assistants, is an engineering problem. Such proofs exist for realistic compilers. The theorems do not apply as stated to any single statement.

Correct part. For any fixed sound axiomatized theory $T$, there are programs whose properties $T$ cannot establish. For example, there are nonterminating programs whose nontermination $T$ cannot prove. A program that searches for a proof of a contradiction in $T$ does not halt if $T$ is consistent, and $T$ cannot prove that. A compiler whose correctness depends on such a statement could not be verified in $T$. In addition, a verification rests on trust in its foundation, and that foundation cannot prove its own consistency.

So the theorem gives a limit on what a single system can prove about all programs, and it offers no obstacle to proving properties of typical programs. These properties tend to be provable in weak fragments of arithmetic.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Explain why validity is recognizable, and prove its undecidability by reduction from PCP.
- Place validity, satisfiability, finite satisfiability and finite validity in $\Sigma_1$ or $\Pi_1$, and state what a tool can do for each.
- Explain the two meanings of "complete" and prove that a complete axiomatizable consistent theory is decidable.
- State $\Sigma_1$-completeness and representability for $\mathsf{Q}$.
- Give the computability proof of incompleteness.
- Prove the diagonal lemma, Gödel's first theorem, and describe Rosser's construction.
- State the derivability conditions and derive the second incompleteness theorem from them.
- List theories that escape the theorems, and identify the hypothesis each one fails.
- Explain, for a given tool category, the practical consequence of these limits.

## Materials

- Smith, An Introduction to Gödel's Theorems. Read it for a careful, full treatment of arithmetization, the diagonal lemma, both incompleteness theorems and common misreadings of them.
- Enderton, A Mathematical Introduction to Logic, 2nd edition. Read it for a rigorous development of number theories, representability and the undecidability results.
- Huth and Ryan, Logic in Computer Science, 2nd edition. Read it for an accessible proof of the undecidability of validity by reduction from PCP.
- Church, A note on the Entscheidungsproblem, Journal of Symbolic Logic, 1936. Read it for the original undecidability result.
- Gödel, On formally undecidable propositions of Principia Mathematica and related systems I, 1931. Read it for the original incompleteness theorems, in translation.
- Rosser, Extensions of some theorems of Gödel and Church, Journal of Symbolic Logic, 1936. Read it for the removal of the $\omega$-consistency hypothesis.
- Trakhtenbrot, The impossibility of an algorithm for the decision problem in finite classes, 1950. Read it for the original theorem on finite models.
- Matiyasevich, Hilbert's Tenth Problem, MIT Press, 1993. Read it for the theorem on Diophantine sets and its background.
- Cook, Soundness and completeness of an axiom system for program verification, SIAM Journal on Computing, 1978. Read it for relative completeness of Hoare logic.
