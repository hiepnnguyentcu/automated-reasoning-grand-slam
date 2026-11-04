# First-Order Metatheory

Part 1, Chapter 1: Mathematical Logic.

## Objective

State and apply completeness, compactness, Löwenheim-Skolem and Herbrand's theorem.

## Why this matters

These four theorems say what first-order logic can and cannot do. Completeness is why a first-order prover can exist at all, and it implies that validity is semidecidable. Compactness and Löwenheim-Skolem mark the limits of expressiveness, so they tell you when a property such as reachability cannot be written as a first-order specification. Herbrand's theorem reduces first-order unsatisfiability to propositional unsatisfiability of ground instances, which is the foundation of [First-Order Resolution](../../../part-2-core-reasoning/06-first-order-proving/first-order-resolution/), [Saturation Provers](../../../part-2-core-reasoning/06-first-order-proving/saturation-provers/) and quantifier instantiation in [SMT Quantifiers](../../../part-2-core-reasoning/05-smt/quantifiers/). When a solver returns unknown on a quantified problem, this theory explains why.

## Prerequisites

- [Soundness and Completeness](../soundness-and-completeness/)
- [First-Order Logic](../first-order-logic/)
- [Normal Forms and Skolemization](../normal-forms-and-skolemization/)

## Lesson

### A proof system for first-order logic

Extend natural deduction from [Proof Systems](../proof-systems/) with the following rules. All substitutions avoid capture.

$$
\frac{\Gamma \vdash \varphi[y/x]}{\Gamma \vdash \forall x\, \varphi}\ {\forall}\text{I}
\qquad
\frac{\Gamma \vdash \forall x\, \varphi}{\Gamma \vdash \varphi[t/x]}\ {\forall}\text{E}
\qquad
\frac{\Gamma \vdash \varphi[t/x]}{\Gamma \vdash \exists x\, \varphi}\ {\exists}\text{I}
\qquad
\frac{\Gamma \vdash \exists x\, \varphi \quad \Gamma, \varphi[y/x] \vdash \psi}{\Gamma \vdash \psi}\ {\exists}\text{E}
$$

$$
\frac{}{\Gamma \vdash t = t}\ {=}\text{I}
\qquad
\frac{\Gamma \vdash s = t \quad \Gamma \vdash \varphi[s/x]}{\Gamma \vdash \varphi[t/x]}\ {=}\text{E}
$$

Side conditions. In $\forall$I, the variable $y$ must not be free in $\Gamma$ or in $\forall x\, \varphi$. In $\exists$E, the variable $y$ must not be free in $\Gamma$, in $\exists x\, \varphi$ or in $\psi$. The variable $y$ is called the eigenvariable. It stands for an arbitrary element about which nothing else is assumed.

Theorem (soundness). If $\Gamma \vdash \varphi$, then $\Gamma \models \varphi$.

Proof sketch. Use induction on derivations, as in the propositional case. The new cases use the substitution and coincidence lemmas. For $\forall$I, let $\mathcal{M}, s$ satisfy $\Gamma$, and let $a \in M$. Since $y$ is not free in $\Gamma$, the assignment $s[y \mapsto a]$ also satisfies $\Gamma$, so $\mathcal{M}, s[y \mapsto a] \models \varphi[y/x]$. By the substitution lemma, $\mathcal{M}, s[y \mapsto a][x \mapsto a] \models \varphi$, and since $y$ is not free in $\forall x\, \varphi$, this gives $\mathcal{M}, s[x \mapsto a] \models \varphi$. The case of $\exists$E is Exercise 11. $\square$

### Gödel's completeness theorem

Theorem (Gödel, 1929 dissertation, published 1930). If $\Gamma \models \varphi$, then $\Gamma \vdash \varphi$.

Gödel's original proof reduced formulas to a special prefix form. Henkin's 1949 proof is the one now usually taught, and it follows Lemmas 3 to 6 of [Soundness and Completeness](../soundness-and-completeness/), with two additions: a witness must exist for each existential sentence, and the domain of the model must be built from syntax.

As before, it suffices to show that every consistent set has a model. Assume a countable signature. Free variables in $\Gamma$ can be replaced by fresh constants, so we consider a consistent set $\Gamma$ of sentences.

Step 1: add constants. Add countably many new constants $C$ to the signature. $\Gamma$ remains consistent, because any derivation of $\bot$ uses finitely many new constants, and they can be replaced by variables not occurring in the derivation, which gives a derivation in the original signature.

Step 2: add Henkin axioms. Enumerate the sentences of the form $\exists x\, \varphi_n$ over the extended signature. For each $n$, pick a constant $c_n \in C$ that is not in $\Gamma$, $\varphi_0, \dots, \varphi_n$ or $c_0, \dots, c_{n-1}$, and add the Henkin axiom

$$
H_n = \exists x\, \varphi_n \to \varphi_n[c_n/x].
$$

Consistency is preserved. Let $\Theta$ be consistent and suppose $\Theta \cup \{H_n\}$ is inconsistent, with $c_n$ not in $\Theta$ or $\exists x\, \varphi_n$. Then $\Theta \vdash \neg H_n$, and so $\Theta \vdash \exists x\, \varphi_n$ and $\Theta \vdash \neg \varphi_n[c_n/x]$, by classical propositional reasoning. Since $c_n$ does not occur in $\Theta$, it can be replaced throughout the derivation by a fresh variable, and $\forall$I gives $\Theta \vdash \forall x\, \neg\varphi_n$. Together with $\Theta \vdash \exists x\, \varphi_n$, this makes $\Theta$ inconsistent, which is a contradiction.

Step 3: extend to a maximal consistent set. Run the Lindenbaum construction over the sentences of the extended signature, starting from $\Gamma$ plus all Henkin axioms. The union of all these sets is consistent, because a derivation uses finitely many Henkin axioms. The construction gives a maximal consistent set $\Delta$ with the same closure properties as in the propositional case. In addition, $\exists x\, \varphi \in \Delta$ if and only if $\varphi[t/x] \in \Delta$ for some closed term $t$: one direction is $\exists$I and closure, and the other direction uses the Henkin axiom and closure.

Step 4: build the term model. Define $t \sim u$ if $t = u \in \Delta$, on closed terms. Rules $=$I and $=$E show that $\sim$ is an equivalence relation and a congruence. The domain is the set of equivalence classes $[t]$. Interpret symbols by $f([t_1], \dots, [t_n]) = [f(t_1, \dots, t_n)]$, and let $([t_1], \dots, [t_n]) \in P^{\mathcal{M}}$ if and only if $P(t_1, \dots, t_n) \in \Delta$. Congruence makes these well defined. The value of a closed term $t$ is $[t]$.

Step 5: prove the truth lemma. For every sentence $\varphi$, $\mathcal{M} \models \varphi$ if and only if $\varphi \in \Delta$. Use induction on the number of connectives and quantifiers. Atoms hold by definition, and connectives hold by closure. For the existential case:

$$
\mathcal{M} \models \exists x\, \varphi
\iff \mathcal{M} \models \varphi[t/x] \text{ for some closed } t
\iff \varphi[t/x] \in \Delta \text{ for some closed } t
\iff \exists x\, \varphi \in \Delta.
$$

The first equivalence uses the substitution lemma, and the fact that every element is $[t]$ for some closed $t$. The second uses the induction hypothesis, since $\varphi[t/x]$ has fewer connectives and quantifiers. The universal case reduces to this one using $\forall x\, \varphi \equiv \neg\exists x\, \neg\varphi$ inside $\Delta$. $\square$

Consequences. First, a valid sentence has a finite proof, so validity is recursively enumerable: enumerate all derivations and check each. Church and Turing showed that validity is undecidable, so it is semidecidable and no more. Second, satisfiability is not recursively enumerable, since otherwise both validity and non-validity would be, and validity would be decidable. See [Undecidability of Logic and Incompleteness](../../02-decidability-and-complexity/undecidability-of-logic-and-incompleteness/).

The completeness theorem should not be confused with Gödel's incompleteness theorems. Completeness says that the proof calculus captures truth in all models. Incompleteness says that no reasonable set of axioms for arithmetic has as consequences all truths of the one standard model.

### Compactness

Theorem (compactness). A set $\Gamma$ of sentences has a model if and only if every finite subset of $\Gamma$ has a model.

Proof. If $\Gamma$ has no model, then $\Gamma \models \bot$, so $\Gamma \vdash \bot$ by completeness. Derivations are finite, so a finite $\Gamma_0 \subseteq \Gamma$ derives $\bot$, and by soundness $\Gamma_0$ has no model. $\square$

For uncountable signatures the theorem still holds, as Maltsev showed in 1936. The Henkin proof carries over with a well-ordering of the signature in place of an enumeration.

The typical use is the following. To show that a property is not first-order definable, add new constants, write infinitely many sentences that are each harmless, use compactness to get a model of all of them together, and observe that the model violates the property. This is the method of Examples 1 and 2 and Exercises 5 to 7.

Second-order logic with its standard semantics has neither compactness nor a complete proof system. Lindström's theorem of 1969 makes the trade-off precise: first-order logic is the strongest logic, among a broad class of logics, that has both compactness and the downward Löwenheim-Skolem property.

### Löwenheim-Skolem

Theorem (downward). If a set of sentences over a countable signature has a model, then it has a model whose domain is countable (finite or countably infinite).

Proof. A set with a model is consistent by soundness. The term model of the Henkin proof has a countable domain, since there are countably many closed terms. $\square$

A sharper version, due to Skolem, says that every infinite structure over a countable signature has a countable elementary substructure: a substructure satisfying exactly the same formulas at its elements. The proof closes a countable subset under Skolem functions, as in [Normal Forms and Skolemization](../normal-forms-and-skolemization/).

Theorem (upward). If a set $\Gamma$ of sentences has an infinite model, then for every infinite cardinal $\kappa$ at least as large as the signature, $\Gamma$ has a model of cardinality $\kappa$.

Proof sketch. Add $\kappa$ new constants $c_i$, and add the sentences $c_i \neq c_j$ for all $i \neq j$. Any finite subset mentions finitely many new constants, and they can be interpreted by distinct elements of the infinite model. By compactness, the whole set has a model, and that model has at least $\kappa$ elements. The Henkin construction over a signature of size $\kappa$ gives a model of size at most $\kappa$, since it is built from closed terms. $\square$

Consequences. A first-order set of sentences with an infinite model cannot pin down a single infinite structure up to isomorphism. Skolem's paradox illustrates this point: set theory, if consistent, has a countable model, even though it proves that uncountable sets exist. There is no contradiction. The set that the model calls uncountable is countable from the outside, and the model lacks any bijection witnessing this.

The most that can be asked is categoricity in one cardinality, which is discussed in [First-Order Theories](../first-order-theories/).

### Herbrand's theorem

Herbrand's work of 1930 moves from arbitrary structures to a single syntactic structure.

In this section, assume that the signature contains at least one constant, adding one if necessary. Assume that $=$ does not occur. Equality is treated at the end.

- The Herbrand universe $H$ is the set of ground terms.
- The Herbrand base is the set of ground atoms $P(t_1, \dots, t_n)$ with $t_i \in H$.
- A Herbrand structure has domain $H$ and interprets each function symbol by $f^{\mathcal{H}}(t_1, \dots, t_n) = f(t_1, \dots, t_n)$. So each ground term denotes itself.
- A Herbrand structure is determined by the set of ground atoms that it makes true, so Herbrand structures correspond to truth assignments on the Herbrand base.
- A ground instance of a quantifier-free formula $\mu$ with variables $\bar{x}$ is $\mu[\bar{t}/\bar{x}]$ for ground terms $\bar{t}$.

Lemma (Herbrand models). A universal sentence $\forall \bar{x}\, \mu$, with $\mu$ quantifier-free, has a model if and only if it has a Herbrand model.

Proof. Let $\mathcal{M}$ be a model. Define a Herbrand structure $\mathcal{H}$ by letting $P(\bar{t})$ be true if and only if $\mathcal{M} \models P(\bar{t})$. By induction, every ground quantifier-free formula has the same truth value in $\mathcal{H}$ and $\mathcal{M}$. Since the domain of $\mathcal{H}$ is the set of ground terms, the substitution lemma gives that $\mathcal{H} \models \forall \bar{x}\, \mu$ if and only if $\mathcal{H} \models \mu[\bar{t}/\bar{x}]$ for all ground $\bar{t}$. Each such instance holds in $\mathcal{M}$, and so it holds in $\mathcal{H}$. The other direction is trivial. $\square$

The lemma needs the universal form. The sentence $\neg P(c) \land \exists x\, P(x)$ is satisfiable, and over the signature $\{c, P\}$ the only Herbrand domain is $\{c\}$, so it has no Herbrand model. This is the reason to Skolemize first.

Theorem (Herbrand). Let $\varphi = \forall \bar{x}\, \mu$ be a universal sentence without equality, with $\mu$ quantifier-free. Then $\varphi$ is unsatisfiable if and only if some finite set of ground instances of $\mu$ is propositionally unsatisfiable, where distinct ground atoms are treated as distinct propositional variables.

Proof. Suppose a finite set of ground instances is propositionally unsatisfiable, and suppose $\mathcal{M} \models \varphi$. Then $\mathcal{M}$ satisfies each instance. The assignment that sends a ground atom $A$ to its truth value in $\mathcal{M}$ satisfies the set propositionally, which is a contradiction.

Conversely, suppose every finite set of ground instances is propositionally satisfiable. There are countably many ground atoms. By propositional compactness, there is an assignment $v$ of the Herbrand base satisfying all ground instances at once. Let $\mathcal{H}$ be the corresponding Herbrand structure. Then $\mathcal{H}$ satisfies all instances, so $\mathcal{H} \models \varphi$, and $\varphi$ is satisfiable. $\square$

Corollary (validity form). A sentence $\exists \bar{x}\, \theta$ with $\theta$ quantifier-free and without equality is valid if and only if there are finitely many ground tuples $\bar{t}_1, \dots, \bar{t}_k$ such that $\theta[\bar{t}_1/\bar{x}] \lor \dots \lor \theta[\bar{t}_k/\bar{x}]$ is a propositional tautology.

To apply the theorem to an arbitrary sentence $\varphi$: to test validity, Skolemize $\neg\varphi$ to get a universal sentence, then look for an unsatisfiable finite set of instances. Observe that you cannot, in general, bound $k$ in advance. If there were a computable bound, first-order validity would be decidable.

The Gilmore procedure. Herbrand's theorem gives a semidecision procedure directly.

```text
function GILMORE(φ):     // φ is a universal sentence ∀x̄ μ, without equality
    I := empty set
    for n := 0, 1, 2, ...:
        add to I all ground instances of μ using terms of depth at most n
        if I is propositionally unsatisfiable:
            return unsatisfiable
    // if φ is satisfiable, the loop never returns
```

Gilmore's 1960 implementation tested the instances by converting to DNF. Davis and Putnam improved the propositional part in the same year, and that work led to DPLL. Robinson's resolution in 1965 removed the blind enumeration by using unification to delay the choice of instances. Modern instance-based provers and the quantifier instantiation in SMT solvers can still be viewed as refined searches for the Herbrand instances.

Equality. Treat $=$ as an ordinary binary predicate $E$, and add the equality axioms $\mathrm{Eq}(\sigma)$: reflexivity, symmetry, transitivity and the congruence axioms for each symbol. These are universal sentences.

Lemma. $\varphi$ has a model with real equality if and only if $\varphi^E \land \mathrm{Eq}(\sigma)$ has a model with $E$ uninterpreted, where $\varphi^E$ replaces $=$ by $E$.

Proof. Given a model with real equality, interpret $E$ as the identity. Given a model of $\varphi^E \land \mathrm{Eq}(\sigma)$, the relation $E$ is a congruence, and the quotient by $E$ satisfies $\varphi$ with real equality. $\square$

So Herbrand's theorem extends to equality by including instances of the equality axioms. Treating $=$ as uninterpreted without these axioms is wrong: $P(a) \land \neg P(b) \land a = b$ would be declared satisfiable.

## Worked examples

### Example 1: finiteness is not first-order

Claim. If a set $\Gamma$ of sentences has arbitrarily large finite models, then $\Gamma$ has an infinite model. So no set of sentences has exactly the finite structures as its models.

Let $\lambda_n$ be the sentence saying that there are at least $n$ elements:

$$
\lambda_n = \exists x_1 \dots \exists x_n \bigwedge_{i < j} x_i \neq x_j.
$$

Let $\Gamma' = \Gamma \cup \{\lambda_n : n \geq 2\}$. Let $\Gamma_0$ be a finite subset of $\Gamma'$, and let $N$ be the largest $n$ such that $\lambda_n \in \Gamma_0$. By assumption, $\Gamma$ has a finite model with at least $N$ elements, and it is a model of $\Gamma_0$. By compactness, $\Gamma'$ has a model. This model satisfies every $\lambda_n$, so it is infinite.

Note the asymmetry: the set $\{\lambda_n : n \geq 2\}$ axiomatizes the infinite structures, using infinitely many sentences. By the claim, no sentence or set of sentences axiomatizes the finite structures.

### Example 2: a nonstandard model of arithmetic

Let $\mathcal{N} = (\mathbb{N}, 0, 1, +, \cdot, <)$, and let $\mathrm{Th}(\mathcal{N})$ be the set of all sentences true in $\mathcal{N}$. Let $\bar{n}$ be the numeral $1 + \dots + 1$ with $n$ ones, with $\bar{0} = 0$. Add a constant $c$, and let

$$
\Gamma = \mathrm{Th}(\mathcal{N}) \cup \{\bar{n} < c : n \in \mathbb{N}\}.
$$

Any finite subset mentions finitely many sentences $\bar{n} < c$. So it holds in $\mathcal{N}$ if $c$ is interpreted as a number larger than all the mentioned $n$. By compactness, $\Gamma$ has a model $\mathcal{M}$.

$\mathcal{M}$ satisfies every sentence true in $\mathcal{N}$, so it is elementarily equivalent to $\mathcal{N}$. It contains an element larger than every numeral, so it is not isomorphic to $\mathcal{N}$: an isomorphism would have to send each numeral to itself, so $c$ would have no possible image. Hence even all of the true first-order sentences of arithmetic cannot characterize the natural numbers. The second-order induction axiom can do so, but second-order logic has no compactness theorem and no complete proof system.

### Example 3: a Gilmore trace

Test the unsatisfiability of $S = \{P(a),\; \forall x\, (P(x) \to P(f(x))),\; \neg P(f(f(a)))\}$. The sentences combine into one universal sentence, and the Herbrand universe is $\{a, f(a), f(f(a)), \dots\}$. To shorten notation in the trace, write $A_0 = P(a)$, $A_1 = P(f(a))$, $A_2 = P(f(f(a)))$.

```text
Depth 0, terms {a}:
    instances: A0, A0 → A1, ¬A2
    propositionally satisfiable: A0 = 1, A1 = 1, A2 = 0
Depth 1, terms {a, f(a)}:
    new instance: A1 → A2
    I = {A0, A0 → A1, A1 → A2, ¬A2}
    unit propagation: A0 = 1, so A1 = 1, so A2 = 1, which conflicts with ¬A2
    propositionally unsatisfiable
result: S is unsatisfiable
```

The set $\{P(a), P(a) \to P(f(a)), P(f(a)) \to P(f(f(a))), \neg P(f(f(a)))\}$ is the required finite set of instances.

### Example 4: the drinker formula through Herbrand

Prove that $\varphi = \exists x\, \forall y\, (P(x) \to P(y))$ is valid. Its negation is equivalent to $\forall x\, \exists y\, (P(x) \land \neg P(y))$. Skolemizing gives $\forall x\, (P(x) \land \neg P(f(x)))$. The signature has no constant, so add $c$.

```text
Instance x := c:     P(c) ∧ ¬P(f(c))
Instance x := f(c):  P(f(c)) ∧ ¬P(f(f(c)))
Combined: ¬P(f(c)) and P(f(c)) conflict, so the two instances are unsatisfiable
```

Two instances suffice. One instance would not suffice: the instance $x := c$ alone is satisfied by $P(c) = 1$, $P(f(c)) = 0$. Thus the proof requires using the universal hypothesis twice. This small fact is the reason that first-order search cannot be limited to one instance per quantifier.

### Example 5: a first-order derivation and why side conditions matter

Derive $\exists x\, \forall y\, R(x, y) \vdash \forall y\, \exists x\, R(x, y)$. The eigenvariables are $a$ for $\exists$E and $b$ for $\forall$I.

```text
1  ∃x ∀y R(x, y)          premise
2      ∀y R(a, y)         assumption for ∃E, with a fresh
3      R(a, b)            ∀E on 2, with b fresh
4      ∃x R(x, b)         ∃I on 3
5  ∃x R(x, b)             ∃E on 1, 2-4, since a is not free in 1 or 5
6  ∀y ∃x R(x, y)          ∀I on 5, since b is not free in 1
```

Now try the converse $\forall y\, \exists x\, R(x, y) \vdash \exists x\, \forall y\, R(x, y)$. From the premise, get $\exists x\, R(x, b)$, and assume $R(a, b)$ with $a$ fresh. To conclude $\forall y\, R(a, y)$, you would apply $\forall$I to $b$, but $b$ is free in the open assumption $R(a, b)$, so the side condition blocks the step. Soundness shows that no other route works, because the converse has a countermodel.

## Common mistakes

- Confusing completeness and incompleteness. Gödel's completeness theorem concerns logical consequence in all models, and his incompleteness theorem concerns a fixed theory of arithmetic and its standard model. They do not conflict, since a sentence true in $\mathbb{N}$ but unprovable in Peano arithmetic is false in some nonstandard model.
- Concluding from completeness that validity is decidable. Completeness gives an enumeration of valid formulas, which is a semidecision procedure. Nothing halts on a formula that is not valid.
- Applying Herbrand's theorem to a sentence with existential quantifiers. The result holds only for universal sentences. Skolemize first, or the sentence may be satisfiable with no Herbrand model.
- Skolemizing the wrong formula. To test validity of $\varphi$, Skolemize $\neg \varphi$.
- Forgetting a constant. If the signature has no constant, the Herbrand universe would be empty, so add one.
- Forgetting equality axioms. Instances must include those of the equality axioms, or the procedure can miss unsatisfiability.
- Thinking that Herbrand's theorem gives a decision procedure. It does in special cases, such as when the Herbrand universe is finite, which happens when no function symbols remain after Skolemization, as in the Bernays-Schönfinkel fragment of [Decidable Fragments](../../02-decidability-and-complexity/decidable-fragments/). In general, the universe is infinite, and the procedure may not terminate on satisfiable input.
- Reading the upward Löwenheim-Skolem theorem as applying to theories with only finite models. It requires an infinite model. A sentence saying that there are exactly three elements has only models of size three.
- Treating compactness as a statement about finite models. The conclusion does not say that a finite model exists. It says that a model exists, which may be infinite, even when every finite subset has only finite models.
- Using a variable as an eigenvariable when it is free in an open assumption. This is the error that the side conditions on $\forall$I and $\exists$E exist to prevent, and Exercise 11 shows the unsoundness that results.

## Exercises

### Exercise 1

State Gödel's completeness theorem, the compactness theorem, both Löwenheim-Skolem theorems and Herbrand's theorem, with all hypotheses.

<details><summary>Solution</summary>

Completeness: if $\Gamma \models \varphi$, then $\Gamma \vdash \varphi$.

Compactness: a set of sentences has a model if and only if every finite subset has a model.

Downward Löwenheim-Skolem: a set of sentences over a countable signature that has a model has a countable model.

Upward Löwenheim-Skolem: a set of sentences with an infinite model has a model of every infinite cardinality at least the cardinality of the signature.

Herbrand: a universal sentence $\forall \bar{x}\, \mu$ with $\mu$ quantifier-free and without equality, over a signature with at least one constant, is unsatisfiable if and only if a finite set of its ground instances is propositionally unsatisfiable.

</details>

### Exercise 2

For the signature with constant $a$, unary function $f$, unary predicate $P$ and binary predicate $Q$, describe the Herbrand universe and base. List the ground terms of depth at most $1$, and count the ground atoms built from them.

<details><summary>Solution</summary>

The Herbrand universe is $\{f^n(a) : n \geq 0\}$. The base is the set of atoms $P(f^n(a))$ and $Q(f^m(a), f^n(a))$.

The terms of depth at most $1$ are $a$ and $f(a)$. They give $2$ atoms of the form $P(t)$ and $2 \times 2 = 4$ atoms of the form $Q(t, u)$, for $6$ atoms in total.

</details>

### Exercise 3

Show that the set $\{\forall x\, (P(x) \lor Q(f(x))),\; \forall x\, \neg P(x),\; \forall x\, \neg Q(x)\}$ is unsatisfiable by exhibiting an unsatisfiable finite set of ground instances.

<details><summary>Solution</summary>

Add the constant $a$. Use the following instances.

- From the first sentence, with $x := a$: $P(a) \lor Q(f(a))$.
- From the second sentence, with $x := a$: $\neg P(a)$.
- From the third sentence, with $x := f(a)$: $\neg Q(f(a))$.

Treat $P(a)$ and $Q(f(a))$ as propositional variables. The second and third instances force both to be false, and then the first is false. The three instances are therefore unsatisfiable. The three sentences can be merged into one universal sentence by renaming variables apart, so the theorem applies.

</details>

### Exercise 4

(a) Show that a set of sentences with existential quantifiers can be satisfiable and have no Herbrand model, using $\neg P(c) \land \exists x\, P(x)$. (b) Give a satisfiable universal sentence whose signature has no constant, and explain what the Herbrand universe is after a constant is added. (c) Explain why the instance test fails to detect that $P(a) \land \neg P(b) \land a = b$ is unsatisfiable if $=$ is treated as an uninterpreted predicate.

<details><summary>Solution</summary>

(a) Let $M = \{0, 1\}$, $c = 0$ and $P = \{1\}$. This is a model. Over the signature $\{c, P\}$, the only Herbrand domain is $\{c\}$. Then $\neg P(c)$ and $\exists x\, P(x)$ conflict, so there is no Herbrand model.

(b) Take $\forall x\, P(x)$, whose signature has only $P$. Adding $c$ gives the Herbrand universe $\{c\}$. It has a Herbrand model with $P(c)$ true. Adding the constant is harmless, since any model can interpret it by an arbitrary element.

(c) As propositional variables, $P(a)$, $P(b)$ and $E(a, b)$ are independent, so the assignment $1, 0, 1$ satisfies the ground formula. With the congruence axiom $E(x, y) \land P(x) \to P(y)$, the instance $E(a, b) \land P(a) \to P(b)$ gives the conflict.

</details>

### Exercise 5

Prove that connectedness of graphs is not first-order axiomatizable: no set of sentences over the signature $\{E\}$ has as its models exactly the connected undirected graphs.

<details><summary>Solution</summary>

Suppose $T$ is such a set. Add constants $a$ and $b$. Let $\delta_n$ say that there is no path of length at most $n$ from $a$ to $b$:

$$
\delta_n = \bigwedge_{k \leq n} \neg \exists y_0 \dots \exists y_k\, \Big(y_0 = a \land y_k = b \land \bigwedge_{i < k} E(y_i, y_{i+1})\Big).
$$

Let $\Gamma = T \cup \{\delta_n : n \in \mathbb{N}\}$. Consider a finite subset, and let $N$ be the largest $n$ with $\delta_n$ in it. A path graph with $N + 2$ vertices, with $a$ and $b$ at the ends, is connected, so it satisfies $T$, and its ends are at distance $N + 1$, so it satisfies each mentioned $\delta_n$.

By compactness, $\Gamma$ has a model. It is a model of $T$, so it is a connected graph, and $a$ and $b$ are joined by a path of some finite length $n$. But it satisfies $\delta_n$, which is a contradiction.

The same argument shows that reachability in a graph is not first-order definable, which is why model checkers need fixpoints or induction.

</details>

### Exercise 6

Prove that no set of sentences over the signature $\{<\}$ has as its models exactly the well-ordered sets.

<details><summary>Solution</summary>

Suppose $T$ is such a set. The structure $(\mathbb{N}, <)$ is a model of $T$. Add constants $c_0, c_1, c_2, \dots$, and let $\Gamma = T \cup \{c_{n+1} < c_n : n \in \mathbb{N}\}$.

A finite subset mentions finitely many constants, with indices at most $N$. Interpret $c_i$ as $N - i$ in $(\mathbb{N}, <)$, and interpret the other constants as $0$. So each mentioned $c_{n+1} < c_n$ holds, and $T$ holds. By compactness, $\Gamma$ has a model. The sequence of the $c_i$ is an infinite descending chain in that model, so the model is not well-ordered, but it is a model of $T$. This is a contradiction.

</details>

### Exercise 7

(a) Let $\varphi$ be a sentence in the language of rings that holds in every field of characteristic $0$. Prove that there is a number $P$ such that $\varphi$ holds in every field of characteristic $p \geq P$. (b) Deduce that the class of fields of characteristic $0$ is not defined by a single sentence.

<details><summary>Solution</summary>

(a) Let $F$ be the field axioms, and let $\pi_p$ be the sentence $1 + \dots + 1 \neq 0$ with $p$ ones. By assumption, $F \cup \{\pi_p : p \text{ prime}\} \models \varphi$. By compactness or by the finiteness of proofs, a finite subset entails $\varphi$. Let $P$ be larger than all primes $p$ with $\pi_p$ in the subset. A field of characteristic $p \geq P$ satisfies the field axioms and each of those finitely many $\pi_q$, so it satisfies $\varphi$.

(b) Suppose a sentence $\sigma$ has as its models exactly the fields of characteristic $0$. Apply (a) with $\varphi = \sigma$. Then a field of large prime characteristic satisfies $\sigma$, so it has characteristic $0$, which is a contradiction.

</details>

### Exercise 8

(a) Prove that every first-order set of sentences with an infinite model has an uncountable model. (b) Explain Skolem's paradox by stating what the countable model contains.

<details><summary>Solution</summary>

(a) This is the upward theorem. Let $\mathcal{M}$ be an infinite model. Add uncountably many new constants $c_i$, with the sentences $c_i \neq c_j$ for $i \neq j$. Any finite subset mentions finitely many constants, which can be interpreted as distinct elements of $\mathcal{M}$. By compactness in its general form, the whole set has a model. Its elements include uncountably many distinct interpretations of constants.

(b) If set theory has a model, then it has a countable model $\mathcal{M}$. The theory proves that there is an uncountable set, so $\mathcal{M}$ contains an element $u$ that $\mathcal{M}$ regards as uncountable. The set of $\mathcal{M}$-elements of $u$ is countable from outside. There is a bijection between it and $\mathbb{N}$ in the metatheory. However, $\mathcal{M}$ contains no element that it regards as such a bijection. So "uncountable" means different things inside and outside the model.

</details>

### Exercise 9

Let $S$ consist of $\forall x\, \neg R(x, x)$, $\forall x\, \forall y\, \forall z\, (R(x, y) \land R(y, z) \to R(x, z))$ and $\forall x\, R(x, f(x))$. Add a constant $a$. Prove that $S$ has no finite model, exhibit a Herbrand model, and explain what the Gilmore procedure does on $S$.

<details><summary>Solution</summary>

Suppose $\mathcal{M}$ is a model and let $b \in M$. Consider $b, f(b), f(f(b)), \dots$. By the third sentence and transitivity, $R(f^i(b), f^j(b))$ holds for all $i < j$. By irreflexivity, $f^i(b) \neq f^j(b)$. So the domain is infinite.

The Herbrand universe is $\{f^n(a) : n \geq 0\}$. Let $R(f^m(a), f^n(a))$ hold if and only if $m < n$. Irreflexivity and transitivity hold since this is $<$ on exponents, and $R(f^n(a), f^{n+1}(a))$ gives the third sentence.

$S$ is satisfiable, so every finite set of its ground instances is propositionally satisfiable. The Gilmore procedure runs forever. This is consistent with the theorem, since it semidecides unsatisfiability only.

</details>

### Exercise 10

Prove the validity form of Herbrand's theorem: $\exists \bar{x}\, \theta$ is valid if and only if a finite disjunction of ground instances of $\theta$ is a propositional tautology.

<details><summary>Solution</summary>

$\exists \bar{x}\, \theta$ is valid iff $\neg\exists \bar{x}\, \theta$ is unsatisfiable iff $\forall \bar{x}\, \neg\theta$ is unsatisfiable. By Herbrand's theorem, this holds iff finitely many instances $\neg\theta[\bar{t}_1/\bar{x}], \dots, \neg\theta[\bar{t}_k/\bar{x}]$ are propositionally unsatisfiable. That is the same as saying that the negation of their conjunction, which is equivalent to $\theta[\bar{t}_1/\bar{x}] \lor \dots \lor \theta[\bar{t}_k/\bar{x}]$, is a propositional tautology.

</details>

### Exercise 11

(a) Prove that $\exists$E is sound. (b) Show that dropping the condition that $y$ is not free in $\psi$ makes the system unsound, with a derivation of $\exists x\, P(x) \vdash \forall y\, P(y)$. Give the countermodel.

<details><summary>Solution</summary>

(a) Let $\mathcal{M}, s$ satisfy $\Gamma$. By the first premise, there is an $a$ with $\mathcal{M}, s[x \mapsto a] \models \varphi$. Let $s' = s[y \mapsto a]$. Since $y$ is not free in $\Gamma$, the assignment $s'$ satisfies $\Gamma$. Since $y$ is not free in $\exists x\, \varphi$, the substitution lemma gives $\mathcal{M}, s' \models \varphi[y/x]$. The second premise gives $\mathcal{M}, s' \models \psi$. Since $y$ is not free in $\psi$, also $\mathcal{M}, s \models \psi$.

(b) The assumption $P(y)$ gives $P(y)$ by Ax. Without the side condition, $\exists$E with $\psi = P(y)$ concludes $\exists x\, P(x) \vdash P(y)$. Since $y$ is not free in $\exists x\, P(x)$, $\forall$I gives $\exists x\, P(x) \vdash \forall y\, P(y)$. Let $M = \{0, 1\}$ with $P = \{0\}$. The premise is true and the conclusion is false.

</details>

### Exercise 12

Prove that the satisfiable first-order sentences are not recursively enumerable, given Church's theorem that validity is undecidable.

<details><summary>Solution</summary>

By completeness, the valid sentences are recursively enumerable. Suppose the satisfiable sentences are recursively enumerable too. A sentence $\varphi$ is not valid if and only if $\neg\varphi$ is satisfiable. So the non-valid sentences would also be recursively enumerable. A set whose members and non-members are both recursively enumerable is decidable: run both enumerations in parallel until $\varphi$ appears in one of them. This contradicts Church's theorem.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State each of the four theorems with hypotheses.
- Explain the two additions that the Henkin proof requires beyond the propositional proof, and sketch the proof that Henkin axioms preserve consistency.
- Derive compactness from completeness, and use it to prove that a given property is not first-order definable.
- Derive both Löwenheim-Skolem theorems from the Henkin construction and compactness, and explain Skolem's paradox.
- Define the Herbrand universe, base and structure, and prove Herbrand's theorem from propositional compactness.
- Run the Gilmore procedure by hand, and explain how equality must be handled.
- Explain why validity is semidecidable and satisfiability is not.

## Materials

- Enderton, A Mathematical Introduction to Logic, 2nd edition. Read the first-order logic chapter on soundness and completeness and the models of theories for the Henkin proof, compactness and Löwenheim-Skolem.
- [Harrison, Handbook of Practical Logic and Automated Reasoning.](https://www.cl.cam.ac.uk/~jrh13/atp/) Read the first-order logic material on Herbrand's theorem and its mechanization for the procedures of Gilmore and of Davis and Putnam, and the limitations material for the bounds on what is possible.
- Henkin, The Completeness of the First-Order Functional Calculus, Journal of Symbolic Logic, 1949. Read it for the origin of the proof given here.
