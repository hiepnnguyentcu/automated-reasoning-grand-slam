# First-Order Resolution

Part 2, Chapter 6: First-Order Proving.

## Objective

Refute clause sets using resolution and factoring and explain refutational completeness.

## Why this matters

Resolution is the first calculus for full first-order logic that a machine could search effectively, and modern saturation provers remain its direct descendants. [Superposition](../superposition/) extends the same two rules and the same completeness proof to equality, and [saturation provers](../saturation-provers/) organize the search. The model construction taught here is the single most useful proof technique in the area, because it tells you which inferences a calculus can safely omit. When you design a new restriction, or decide whether a heuristic breaks completeness, this is the argument you will use.

## Prerequisites

- [Unification](../unification/) for most general unifiers.
- [Normal Forms and Skolemization](../../../part-1-foundations/01-mathematical-logic/normal-forms-and-skolemization/) for clause form.
- [First-Order Metatheory](../../../part-1-foundations/01-mathematical-logic/first-order-metatheory/) for Herbrand's theorem and compactness.
- [Resolution and DPLL](../../04-sat/resolution-and-dpll/) for propositional resolution.
- [Undecidability of Logic and Incompleteness](../../../part-1-foundations/02-decidability-and-complexity/undecidability-of-logic-and-incompleteness/) for why the search cannot always terminate.

## Lesson

### From formulas to clauses

A prover shows $\Gamma \models \varphi$ by showing that $\Gamma \cup \{\neg\varphi\}$ is unsatisfiable. It converts this set to clauses with negation normal form, Skolemization and conjunctive normal form. Skolemization preserves satisfiability and does not preserve equivalence. That is sufficient, because refutation asks only about satisfiability.

A literal is an atom $A$ or its negation $\neg A$. A clause is a finite multiset of literals, written as a disjunction, and $\bot$ is the empty clause. All variables of a clause are implicitly universally quantified, each clause has its own variables, and premises of an inference are renamed so that they share no variable. In this topic atoms have no equality, or equality is treated as an ordinary predicate with no built-in meaning. The next topics add its meaning.

A ground instance of $C$ is $C\theta$ with $C\theta$ variable-free. Write $\mathrm{gnd}(N)$ for the set of ground instances of the clauses of $N$. If the signature has no constant, add one. A Herbrand interpretation is a set $I$ of ground atoms, namely those it makes true. A set of clauses is satisfiable if and only if it has a Herbrand model, since $N$ holds in $I$ exactly when $\mathrm{gnd}(N)$ holds in $I$, and a model of a clause set induces a Herbrand model.

### Why unification comes in

Herbrand's theorem says that $N$ is unsatisfiable if and only if some finite subset of $\mathrm{gnd}(N)$ is propositionally unsatisfiable. Early procedures enumerated ground instances and called a propositional check, which was hopeless because almost all instances are irrelevant. Robinson's idea in 1965 was to delay the choice of instance: resolve two literals as soon as they can be made complementary, and instantiate only as much as the mgu demands.

### The calculus

Binary resolution:

$$
\frac{C \lor A \qquad D \lor \neg B}{(C \lor D)\sigma}
\qquad \sigma = \mathrm{mgu}(A, B)
$$

Factoring:

$$
\frac{C \lor A \lor B}{(C \lor A)\sigma}
\qquad \sigma = \mathrm{mgu}(A, B)
$$

The conclusion of resolution is called a resolvent, and the conclusion of factoring is called a factor. A refutation of $N$ is a derivation of $\bot$ from $N$.

Theorem (soundness). Each conclusion is a logical consequence of its premises. So if $\bot$ is derivable from $N$, then $N$ is unsatisfiable.

Proof. Let $J$ be a model of the premises and let $\rho$ be any assignment of domain elements to the variables of the conclusion, extended to the other variables arbitrarily. The premise instances $(C \lor A)\sigma$ and $(D \lor \neg B)\sigma$ hold under $\rho$, and $A\sigma = B\sigma$. If this atom is true, then $D\sigma$ must hold. If it is false, then $C\sigma$ must hold. In both cases $(C \lor D)\sigma$ holds. For factoring, $(C \lor A \lor B)\sigma$ and $(C \lor A)\sigma$ contain the same literals as sets. $\square$

### Why factoring is necessary

Binary resolution alone is not complete. The set $\{P(x_1) \lor P(x_2), \neg P(x_3) \lor \neg P(x_4)\}$ is unsatisfiable. Every resolvent of two-literal clauses here has two literals, so $\bot$ is never derived without factoring. The two factors $P(x_1)$ and $\neg P(x_3)$ resolve to $\bot$ immediately.

Resolving on several literals at once is an alternative: Robinson's original rule resolved a set of literals from each premise. Provers use the binary version together with factoring.

### Lifting

The link between ground and first-order inferences is the following lemma.

Lemma (lifting). Let $C$ and $D$ be variable-disjoint clauses with ground instances $C\theta$ and $D\theta$, and let $R$ be a ground resolvent of $C\theta$ and $D\theta$ on an atom $A$. Then factoring steps on $C$ and on $D$ followed by one resolution step produce a clause $R'$ such that $R$ is an instance of $R'$, when clauses are read as sets of literals.

Proof. Regard the ground premises as sets. Let $L_1, \ldots, L_m$ be the literals of $C$ that $\theta$ sends to $A$, and $M_1, \ldots, M_n$ the literals of $D$ that $\theta$ sends to $\neg A$. Here $\theta$ unifies $L_1, \ldots, L_m$, so factoring $C$ with their mgu $m - 1$ times gives a clause $C'$ with a single literal $L$ with $\theta = \tau\theta'$, where $\tau$ is the substitution accumulated in factoring. The same applies to $D$, giving $D'$ and $M$. Since $\theta$ unifies the atoms of $L$ and $M$, they have an mgu $\sigma$ and $\theta$ factors through $\sigma$. The resolvent $R' = (C' \setminus L \cup D' \setminus M)\sigma$ has the property that its literals under the remaining substitution are exactly those of $C\theta$ other than $A$ and those of $D\theta$ other than $\neg A$. $\square$

The lemma explains why factoring is the first-order counterpart of the set semantics of ground clauses. The classic completeness proof combines this lemma with Herbrand's theorem, compactness and propositional completeness. The proof below is shorter, more general and carries over to equality.

### Orderings and selection

Unrestricted resolution generates far too many clauses. The main restrictions use an ordering and a selection function.

An atom ordering is a strict partial order $\succ$ on atoms that is total and well-founded on ground atoms and stable under substitution: $A \succ B$ implies $A\sigma \succ B\sigma$. Precedence-based term orderings from [Term Rewriting](../term-rewriting/) provide such orderings.

On ground literals, extend $\succ$ so that $\neg A \succ A$ and so that any literal on $A$ is greater than any literal on $B$ when $A \succ B$. On ground clauses, use the multiset extension of the literal ordering. A literal is maximal in $C$ if no literal of $C$ is greater than it. It is strictly maximal if it is maximal and occurs once.

A selection function $S$ assigns to each clause a multiset of its negative literals. If $S(C)$ is empty, the inference is controlled by maximality. Otherwise only selected literals can take part.

Ordered resolution with selection is the rule system below, where all conditions apply after applying $\sigma$.

Ordered resolution:

$$
\frac{C \lor A \qquad D \lor \neg B}{(C \lor D)\sigma}
$$

The side conditions are as follows.

- $\sigma = \mathrm{mgu}(A, B)$.
- $A\sigma$ is strictly maximal in $(C \lor A)\sigma$, and $S(C \lor A)$ is empty.
- Either $\neg B$ is selected in $D \lor \neg B$, or $S(D \lor \neg B)$ is empty and $\neg B\sigma$ is maximal in $(D \lor \neg B)\sigma$.

Ordered factoring:

$$
\frac{C \lor A \lor B}{(C \lor A)\sigma}
$$

The side conditions are $\sigma = \mathrm{mgu}(A, B)$, $S(C \lor A \lor B)$ is empty, and $A\sigma$ is maximal in $(C \lor A \lor B)\sigma$.

On nonground clauses, "maximal" means that no other literal of the instantiated clause is greater. Two literals may be incomparable, in which case both are maximal. This is why the ordering must be a partial order that is stable, and why the test comes after $\sigma$.

### Saturation and redundancy

A ground clause $C$ is redundant with respect to a ground set $M$ if $C$ follows from clauses of $M$ that are smaller than $C$. A nonground clause is redundant if all of its ground instances are redundant in $\mathrm{gnd}(N)$. In the ground case, an inference with main premise $C_m$, the premise containing the negative or factored literal, is redundant if its conclusion follows from clauses of $M$ smaller than $C_m$. A conclusion in $M$ is such a case, because it is smaller than $C_m$.

A set $N$ is saturated if every inference from premises in $N$ is redundant, meaning that each ground instance of its conclusion follows from ground instances of clauses of $N$ smaller than the corresponding instance of the main premise. In practice this means that its conclusion is in $N$ or follows from smaller clauses in $N$.

### Model construction

Fix a set $M$ of ground clauses. Build a Herbrand interpretation by processing the clauses in increasing order. For each $C \in M$ define $I_C = \bigcup_{D \prec C} E_D$, and define

$$
E_C = \{A\} \quad \text{if } C = D \lor A \text{, } C \text{ is false in } I_C \text{, } A \text{ is strictly maximal in } C \text{, and } S(C) \text{ is empty.}
$$

Otherwise $E_C = \emptyset$. A clause with nonempty $E_C$ is called productive. The candidate model is $I = \bigcup_{C \in M} E_C$.

Because atoms are produced in increasing order, a literal of a clause $C$ has the same truth value in $I_C$ as in $I$, apart from a strictly maximal atom that $C$ itself produces. Formally, if $C \prec C'$ and $C'$ produces $A'$, then $A'$ is greater than every atom of $C$ or $C$ is already true by $A'$. So an atom smaller than the maximal atom of $C$ has its final truth value in $I_C$. A productive clause is true in $I$, and the rest of the clause, $D$, is false in $I$.

Theorem (ground completeness). Let $M$ be a ground set saturated under ordered resolution with selection and ordered factoring. If $\bot \notin M$, then $I \models M$.

Proof. Suppose not, and let $C$ be the smallest clause of $M$ false in $I$, which exists by well-foundedness. All smaller clauses of $M$ are true in $I$. So $C$ cannot be redundant, since it would follow from true clauses. Also $C \neq \bot$.

Case 1: $C = D \lor \neg A$, with $\neg A$ selected, or with $S(C)$ empty and $\neg A$ maximal. Since $C$ is false, $A \in I$, so some clause $B \lor A \prec C$ produced $A$. This clause has $A$ strictly maximal, empty selection and $B$ false in $I$. Ordered resolution applies to $B \lor A$ and $D \lor \neg A$, with conclusion $B \lor D$. This conclusion is smaller than $C$, because $\neg A$ is replaced by literals smaller than $A$. By saturation it follows from clauses of $M$ smaller than $C$, which are true in $I$. So $B \lor D$ is true in $I$. But $B$ and $D$ are false in $I$, a contradiction.

Case 2: $S(C)$ is empty and the maximal literal of $C$ is a positive literal $A$ occurring more than once, so $C = D \lor A \lor A$. Ordered factoring applies with conclusion $D \lor A$, which is smaller than $C$. By saturation it is true in $I$. But $A$ and $D$ are false in $I$, a contradiction.

Case 3: $S(C)$ is empty and the maximal literal $A$ of $C$ is strictly maximal and positive. Since $C$ is false in $I$, it is false in $I_C$, by the remark on truth values and $I_C \subseteq I$. So the production condition holds, $A \in E_C \subseteq I$, and $C$ is true in $I$, a contradiction. $\square$

### Lifting saturation

The final step transfers saturation from $N$ to $\mathrm{gnd}(N)$.

Lemma. Let $N$ be saturated under the first-order rules. For a ground instance $C\theta$, let its selected literals be the instances of the literals selected in $C$. Then every ordered inference from $\mathrm{gnd}(N)$ is redundant with respect to $\mathrm{gnd}(N)$.

Proof sketch. A ground ordered resolution with premises $(C \lor A)\theta$ and $(D \lor \neg B)\theta$ has $A\theta = B\theta$, so $\theta$ unifies $A$ and $B$. Let $\sigma$ be their mgu, with $\theta = \sigma\theta'$. Because the ordering is stable, $L\sigma \succ L'\sigma$ implies $L\theta \succ L'\theta$. So if $A\theta$ is strictly maximal and unselected in the ground clause, then $A\sigma$ is strictly maximal in the instantiated first-order clause. The first-order inference therefore exists. Its conclusion lies in $N$ or is redundant, and the ground conclusion is an instance of it. The factoring case is analogous. $\square$

Theorem (refutational completeness, Bachmair and Ganzinger form). Let $\succ$ be an atom ordering and $S$ a selection function. If $N$ is unsatisfiable, then every fair saturation of $N$ under ordered resolution with selection and ordered factoring derives $\bot$. In particular, unrestricted binary resolution with factoring is refutationally complete.

Proof. Let $N^*$ be the limit of a fair derivation, that is, the set of persisting clauses. Fairness means that $N^*$ is saturated. If $\bot \notin N^*$, the theorems above give a Herbrand model of $\mathrm{gnd}(N^*)$. Since deleted clauses are redundant, it is also a model of $N$. This is a contradiction, so $\bot$ appears at some finite stage. For unrestricted resolution, take the closure of $N$ under all resolution and factoring steps. This set is saturated under the ordered rules for any ordering, since each ordered inference is an unrestricted one. So it contains $\bot$. $\square$

A consequence is semi-decidability: if $N$ is unsatisfiable, a fair search finds $\bot$ in finite time. Termination cannot be guaranteed in the satisfiable case, by Church's theorem that first-order validity is undecidable. Saturation yields three outcomes: a refutation, a finite saturated set without $\bot$ which proves satisfiability, or an infinite run.

### Redundancy in practice

Two deletions are the most important.

- A tautology contains complementary literals $A$ and $\neg A$. It is redundant in every set, since it follows from the empty set.
- $C$ subsumes $D$ if $C\sigma \subseteq D$ as multisets for some substitution $\sigma$. When $C$ subsumes $D$ and the two are not variants, $D$ can be deleted. If $C\sigma$ is a proper sub-multiset of $D$, each ground instance of $D$ follows from a smaller instance of $C$. If $C\sigma = D$, each ground instance of $D$ is already a ground instance of $C$, so nothing is lost.

Subsumption must be defined on multisets, or be restricted in size, or factoring can go wrong. Under the set reading, $P(x_1) \lor P(a)$ subsumes its own factor $P(a)$, so a prover that deleted $P(a)$ would throw away the useful clause. Under the multiset reading the two-literal clause does not subsume the one-literal clause.

Subsumption resolution combines both ideas: if $C \lor A$ and $D \lor \neg B$ are such that $(C \lor A)\sigma \subseteq D \lor B$ as sets, with $A\sigma = B$, then $D \lor \neg B$ may be replaced by $D$.

### Other restrictions

Several restrictions predate the ordered view, and each has a clear status.

| Strategy | Restriction | Status |
|---|---|---|
| Set of support (Wos, Robinson and Carson, 1965) | Every inference needs a premise derived from a designated set. | It is complete if the complement of the set is satisfiable. |
| Unit resolution | Every inference has a unit premise. | It is complete for Horn clauses and incomplete in general. |
| Positive hyperresolution | Negative literals are resolved away in one macro step with positive clauses. | It is complete, and selecting negative literals one at a time simulates it. |
| Input resolution | Every inference has an input clause as a premise. | It is complete for Horn clauses and is incomplete in general. |

Set of support explains why provers treat the negated goal specially. It is one reason for goal-directed heuristics in clause selection.

## Worked examples

Traces number clauses and give the premises and mgu of each step. In traces, `x1` stands for $x_1$.

### Example 1: the drinker formula

Prove $\exists x_1 (D(x_1) \to \forall x_2\, D(x_2))$.

The negation is $\forall x_1 \neg(D(x_1) \to \forall x_2\, D(x_2))$. Its negation normal form is $\forall x_1 (D(x_1) \land \exists x_2\, \neg D(x_2))$. Skolemizing $x_2$, which depends on $x_1$, gives $\forall x_1 (D(x_1) \land \neg D(f(x_1)))$.

```
1. D(x1)                     input
2. ¬D(f(x2))                 input, with its variable renamed
3. ⊥                         resolve 1 and 2 with {x1 ↦ f(x2)}
```

Note that the two conjuncts become two clauses, each with its own variable, even though they came from one quantifier. This renaming is justified because $\forall$ distributes over $\land$.

### Example 2: a refutation that needs factoring

Prove $\neg \exists x_1 \forall x_2 (S(x_1, x_2) \leftrightarrow \neg S(x_2, x_2))$, the barber statement. Take $x_1$ as the Skolem constant $b$ in the negated goal.

```
1. ¬S(b, x1) ∨ ¬S(x1, x1)    input
2. S(b, x1) ∨ S(x1, x1)      input
3. ¬S(b, b)                  factor 1 with {x1 ↦ b}
4. S(b, b)                   factor 2 with {x1 ↦ b}
5. ⊥                         resolve 3 and 4
```

No binary resolution of 1 and 2 alone reaches $\bot$. Each resolvent has two literals or is a tautology.

### Example 3: a nontrivial refutation

Show that a symmetric, transitive relation in which every element has a successor is reflexive.

$$
\forall x_1 \exists x_2\, R(x_1, x_2), \quad
\forall x_1 \forall x_2 (R(x_1, x_2) \to R(x_2, x_1)), \quad
\forall x_1 \forall x_2 \forall x_3 (R(x_1, x_2) \land R(x_2, x_3) \to R(x_1, x_3))
\models \forall x_1\, R(x_1, x_1).
$$

Skolemize the first axiom with $f$ and the negated goal with $a$.

```
1. R(x1, f(x1))                                input
2. ¬R(x1, x2) ∨ R(x2, x1)                      input
3. ¬R(x1, x2) ∨ ¬R(x2, x3) ∨ R(x1, x3)         input
4. ¬R(a, a)                                    negated goal
5. R(f(x1), x1)                                resolve 1 and 2 on ¬R(x1', x2')
                                               with {x1' ↦ x1, x2' ↦ f(x1)}
6. ¬R(f(x1), x3) ∨ R(x1, x3)                   resolve 1 and 3 on ¬R(x1', x2')
                                               with {x1' ↦ x1, x2' ↦ f(x1)}
7. R(x1, x1)                                   resolve 5 (renamed R(f(x4), x4))
                                               and 6 with {x1 ↦ x4, x3 ↦ x4}
8. ⊥                                           resolve 7 and 4 with {x1 ↦ a}
```

Each mgu instantiates exactly what is needed. In a ground proof you would have to guess the instance $R(a, f(a))$ at the start.

### Example 4: reading a model from a saturated ground set

Take atoms $P \prec Q \prec R$, no selection, and the clauses below in increasing order.

```
1. P ∨ Q
2. ¬P ∨ ¬Q     obtained by ordered resolution from 3 and 4
3. ¬Q ∨ R
4. ¬P ∨ ¬R
```

The inference from 3 and 4 is allowed because $R$ is strictly maximal in 3 and $\neg R$ is maximal in 4, and its conclusion is clause 2. The inference from 1 and 2 on $Q$ gives the tautology $P \lor \neg P$, which is redundant. There are no other allowed inferences. The set is saturated.

```
clause       I before    true?   production
P ∨ Q        {}          no      Q strictly maximal: produce Q
¬P ∨ ¬Q      {Q}         yes     none
¬Q ∨ R       {Q}         no      R strictly maximal: produce R
¬P ∨ ¬R      {Q, R}      yes     none
```

The model is $\{Q, R\}$, and all four clauses hold in it.

### Example 5: an infinite model from a finite saturated set

Take $N = \{P(a), \neg P(x_1) \lor P(f(x_1))\}$ with an ordering in which $P(f(t)) \succ P(t)$ and no selection. In the second clause $P(f(x_1))$ is greater than $\neg P(x_1)$. So $\neg P(x_1)$ is not maximal, and $P(a)$ cannot resolve with it. The only remaining candidate would put $P(f(x_1))$ against a negative literal, and no clause has one that is eligible. So $N$ is saturated and has no $\bot$, which proves it satisfiable.

The candidate model is $\{P(f^n(a)) : n \geq 0\}$. Each ground instance $\neg P(f^n(a)) \lor P(f^{n+1}(a))$ is false when its turn comes and produces its positive atom.

Unrestricted resolution on the same set diverges, generating $P(f(a)), P(f(f(a))), \ldots$ forever. Here the ordering turned divergence into a one-line satisfiability proof.

Now add the goal clause $\neg P(f(f(a)))$. The new clause is a negative unit, so it is eligible.

```
1. P(a)                        input
2. ¬P(x1) ∨ P(f(x1))           input
3. ¬P(f(f(a)))                 negated goal
4. ¬P(f(a))                    resolve 2 and 3 with {x1 ↦ f(a)}
5. ¬P(a)                       resolve 2 and 4 with {x1 ↦ a}
6. ⊥                           resolve 1 and 5
```

## Common mistakes

- Forgetting to rename premises apart. Resolving $P(x_1)$ against $\neg P(f(x_1))$ without renaming falsely fails the occurs check.
- Omitting factoring, which loses completeness, as the example of $P(x_1) \lor P(x_2)$ shows.
- Treating a resolvent of two complementary pairs as the empty clause. Resolving $P \lor Q$ with $\neg P \lor \neg Q$ gives a tautology such as $Q \lor \neg Q$. You may resolve on one pair only.
- Testing the ordering conditions before applying $\sigma$. A literal maximal in $C$ can stop being maximal in $C\sigma$, so the conditions must be tested on the instance.
- Reading "complete" as "terminates". Refutational completeness says only that unsatisfiable sets eventually give $\bot$.
- Concluding satisfiability from a time-out. Only a finished fair saturation without $\bot$ proves satisfiability.
- Reading Skolemization as an equivalence. The Skolemized formula is equisatisfiable with the original, so it can have fewer models.
- Using unit resolution or input resolution on non-Horn clauses and treating failure as satisfiability. Both strategies are incomplete there.
- Selecting positive literals in the sense used here. The completeness theorem above only covers selection of negative literals.
- Deleting a factor because its parent subsumes it under the set reading. Use multiset subsumption, as in the section on redundancy.

## Exercises

1. State the rules of binary resolution and factoring with their side conditions, and state the refutational completeness theorem.

<details><summary>Solution</summary>

Resolution derives $(C \lor D)\sigma$ from $C \lor A$ and $D \lor \neg B$, with variable-disjoint premises and $\sigma = \mathrm{mgu}(A, B)$. Factoring derives $(C \lor A)\sigma$ from $C \lor A \lor B$, with $\sigma = \mathrm{mgu}(A, B)$. The completeness theorem says that if a clause set is unsatisfiable, then $\bot$ is derivable from it using these two rules.

</details>

2. Compute the resolvent of $P(x_1, f(x_1)) \lor Q(x_1)$ and $\neg P(a, x_2) \lor R(x_2)$, and all factors of $P(x_1, a) \lor P(b, x_2) \lor Q(x_1)$.

<details><summary>Solution</summary>

The mgu of $P(x_1, f(x_1))$ and $P(a, x_2)$ is $\{x_1 \mapsto a, x_2 \mapsto f(a)\}$. The resolvent is $Q(a) \lor R(f(a))$.

The mgu of $P(x_1, a)$ and $P(b, x_2)$ is $\{x_1 \mapsto b, x_2 \mapsto a\}$. The only factor is $P(b, a) \lor Q(b)$.

</details>

3. Refute $\{P(x_1) \lor P(x_2), \neg P(x_3) \lor \neg P(x_4)\}$, and prove that no refutation without factoring exists.

<details><summary>Solution</summary>

Factoring the first clause gives $P(x_1)$, factoring the second gives $\neg P(x_3)$, and resolving these gives $\bot$.

Without factoring, every clause derivable from the set has at least two literals. Each resolution step takes two clauses of length at least two and removes exactly one literal from each, so the resolvent has at least two literals, by induction on the derivation. So $\bot$ is not derivable.

</details>

4. Prove by resolution that $\forall x_1 (P(x_1) \to \exists x_2\, Q(x_1, x_2))$, $\forall x_1 \forall x_2 (Q(x_1, x_2) \to R(x_2))$ and $P(a)$ entail $\exists x_1\, R(x_1)$.

<details><summary>Solution</summary>

```
1. ¬P(x1) ∨ Q(x1, s(x1))       axiom, with Skolem function s
2. ¬Q(x1, x2) ∨ R(x2)          axiom
3. P(a)                        axiom
4. ¬R(x1)                      negated goal
5. Q(a, s(a))                  resolve 1 and 3 with {x1 ↦ a}
6. R(s(a))                     resolve 2 and 5 with {x1 ↦ a, x2 ↦ s(a)}
7. ⊥                           resolve 4 and 6 with {x1 ↦ s(a)}
```

</details>

5. Prove by resolution that $\forall x_1 (P(x_1) \lor Q(x_1))$, $\forall x_1 (P(x_1) \to R(x_1))$ and $\forall x_1 (Q(x_1) \to R(x_1))$ entail $\forall x_1\, R(x_1)$. Give one refutation that uses factoring and one that does not.

<details><summary>Solution</summary>

The clauses are $P(x_1) \lor Q(x_1)$, $\neg P(x_1) \lor R(x_1)$, $\neg Q(x_1) \lor R(x_1)$ and $\neg R(c)$, where $c$ is a Skolem constant from the negated goal.

Refutation with factoring:

```
5. Q(x1) ∨ R(x1)       resolve 1 and 2
6. R(x1) ∨ R(x1)       resolve 3 and 5
7. R(x1)               factor 6
8. ⊥                   resolve 4 and 7
```

Refutation without factoring:

```
5. ¬P(c)               resolve 2 and 4
6. ¬Q(c)               resolve 3 and 4
7. Q(c)                resolve 1 and 5
8. ⊥                   resolve 6 and 7
```

</details>

6. Show that unit resolution cannot refute $\{P \lor Q, \neg P \lor Q, P \lor \neg Q, \neg P \lor \neg Q\}$, then give a refutation using unrestricted resolution.

<details><summary>Solution</summary>

The set has no unit clause, so unit resolution derives nothing at all. It is still unsatisfiable. Resolve the first two clauses on $P$ to obtain $Q \lor Q$, and factor to $Q$. Resolve the last two on $P$ to obtain $\neg Q \lor \neg Q$, and factor to $\neg Q$. Resolve $Q$ and $\neg Q$ to obtain $\bot$.

</details>

7. Let $P \prec Q \prec R$ with no selection. Consider $N = \{P \lor R, \neg P \lor Q, \neg Q \lor R\}$. List the ordered inferences, decide whether $N$ is saturated, and construct the candidate model.

<details><summary>Solution</summary>

In $P \lor R$ the maximal literal is $R$. In $\neg P \lor Q$ it is $Q$. In $\neg Q \lor R$ it is $R$. No clause has a maximal negative literal, so no ordered resolution applies. No clause has a repeated maximal literal, so no factoring applies. $N$ is saturated.

The increasing order is $\neg P \lor Q$, then $P \lor R$, then $\neg Q \lor R$. For $\neg P \lor Q$, the empty interpretation makes $\neg P$ true, so nothing is produced. For $P \lor R$, the clause is false and $R$ is strictly maximal, so $R$ is produced. For $\neg Q \lor R$, the clause is true. The model is $\{R\}$, and all three clauses hold in it.

</details>

8. Prove that a tautology is redundant in every set, and that if $C\sigma \subset D$ as multisets (with $C\sigma$ a proper sub-multiset), then $D$ is redundant in any set containing $C$.

<details><summary>Solution</summary>

A ground instance of a tautology is a tautology, so it follows from the empty set of smaller clauses.

Let $D\theta$ be a ground instance. Then $C\sigma\theta$ is a ground instance of $C$ and a proper sub-multiset of $D\theta$. The multiset extension makes a proper sub-multiset smaller, so $C\sigma\theta \prec D\theta$. Also $C\sigma\theta \models D\theta$, since every literal of the former occurs in the latter. So $D\theta$ follows from a smaller ground instance in the set.

</details>

9. Complete Case 1 of the ground completeness proof for a clause in which the maximal literal is a negative literal that occurs twice, so $C = D \lor \neg A \lor \neg A$ with no selection.

<details><summary>Solution</summary>

$\neg A$ is maximal in $C$, and the side condition asks only for maximality, so ordered resolution still applies. Take the productive clause $B \lor A$ with $A$ strictly maximal, and let the resolved occurrence be one copy of $\neg A$. The conclusion is $B \lor D \lor \neg A$. It is smaller than $C$, because one copy of $\neg A$ was replaced by literals of $B$, all smaller than $A$. It is false in $I$, because $B$ and $D$ are false and $A \in I$. By saturation it follows from clauses smaller than $C$, which are true in $I$, so it would be true in $I$. This is a contradiction.

</details>

10. Show that ordered resolution with this selection function is complete on Horn sets, using the theorem above: $S$ selects a negative literal whenever a clause has one. Describe the resulting strategy.

<details><summary>Solution</summary>

$S$ is a valid selection function, so the theorem applies with any atom ordering. In a Horn set each clause has at most one positive literal. A clause with a negative literal can take part only through its selected negative literal, and the other premise of a resolution step must have empty selection, so it has no negative literal. Together with Horn, this means that the other premise is a positive unit clause. Factoring never applies, because no clause has two positive literals. The strategy is therefore positive unit resolution, which propagates facts forward until the negated goal is refuted.

</details>

11. Design: explain precisely how to detect each of the three outcomes of a fair resolution search, and state which one a resource-limited prover can never report honestly after discarding a non-redundant clause.

<details><summary>Solution</summary>

A refutation is detected when $\bot$ is derived. A finite saturation is detected when every inference among kept clauses has been performed and no new unredundant clause results, which proves satisfiability if only redundant clauses were discarded. An infinite run cannot be detected, and in practice it appears as a time-out, which proves nothing.

If a prover discards a non-redundant clause, for example to enforce a weight limit, then its final set is no longer guaranteed to entail the original problem's models. Exhausting the search no longer gives a model of the input. So it cannot honestly report satisfiability, and it must report "unknown". It can still honestly report a refutation, since soundness is unaffected.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Convert a first-order problem to clauses and identify which variables become Skolem functions.
- Compute resolvents and factors with explicit mgus, keeping variables apart.
- Produce a refutation of an unseen clause set and write it as a numbered derivation.
- Apply the side conditions of ordered resolution with selection on a nonground clause.
- State and prove the lifting lemma.
- Run the model construction on a ground saturated set and prove the completeness theorem.
- State the three outcomes of a fair search and what each one proves.

## Materials

- Robinson, A Machine-Oriented Logic Based on the Resolution Principle, JACM 1965. Read it for the original resolution principle, with its multi-literal rule and the lifting argument.
- [Harrison, Handbook of Practical Logic and Automated Reasoning.](https://www.cl.cam.ac.uk/~jrh13/atp/) Read its material on first-order resolution for the Herbrand-based path to completeness and for concrete procedures you can compare with your hand traces.
- Bachmair and Ganzinger, Resolution Theorem Proving, in Handbook of Automated Reasoning, 2001. Read it for the modern account of ordered resolution, selection, redundancy and the model construction.
- Wos, Robinson and Carson, Efficiency and Completeness of the Set of Support Strategy in Theorem Proving, JACM 1965. Read it for the set of support strategy and its completeness condition.
