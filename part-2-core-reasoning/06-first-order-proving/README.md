# Chapter 6: First-Order Proving

Part 2: Core Reasoning.

## Objective

Explain how automated provers search for proofs in full first-order logic with equality.

## Proof of mastery

Run saturation by hand on an unseen first-order problem and report the resulting proof.

## Overview

This chapter builds the method used by provers such as Vampire and E, one layer at a time. Unification computes the least instantiation that makes two terms equal, which lets a single inference stand for infinitely many ground inferences. First-order resolution uses unification to give a refutationally complete calculus, and it introduces the three ideas used in the rest of the chapter: ordering restrictions, redundancy and the construction of a model from a saturated set.

Term rewriting treats equations separately. It supplies reduction orderings, critical pairs and Knuth-Bendix completion. Superposition then merges the two lines: it is ordered resolution with built-in equality, and on unit equations it is unfailing completion. Saturation provers turn the calculus into a search procedure, with the given-clause loop, simplification, clause selection and term indexing.

The chapter is concepts only. You check your learning with proofs and hand traces.

## Study order

1. Study [Unification](unification/) first, because every later inference uses mgus and matching.
2. Study [First-Order Resolution](first-order-resolution/) next, because it presents the model construction in its simplest form, without equality.
3. Study [Term Rewriting](term-rewriting/) third, because superposition needs its orderings and critical pairs.
4. Study [Superposition](superposition/) fourth, because it combines the two previous topics.
5. Study [Saturation Provers](saturation-provers/) last, because the loop operates on the rules, orderings and redundancy notions of the earlier topics.

Topics 2 and 3 are independent of each other, so you can swap them.

## Topics

| Topic | Objective |
|---|---|
| [Unification](unification/) | Compute most general unifiers by hand and prove the algorithm correct. |
| [First-Order Resolution](first-order-resolution/) | Refute clause sets using resolution and factoring and explain refutational completeness. |
| [Term Rewriting](term-rewriting/) | Prove termination and confluence of rewrite systems and run Knuth-Bendix completion by hand. |
| [Superposition](superposition/) | Apply the superposition calculus with term orderings and explain how it handles equality. |
| [Saturation Provers](saturation-provers/) | Explain the given-clause loop and redundancy elimination in Vampire and E. |

## Chapter exam

Take this exam closed-book, with no software. Show every mgu, ordering comparison and inference. In traces, `x1` stands for $x_1$, `≈` and `≉` stand for $\approx$ and $\not\approx$, and `¬` and `∨` stand for $\neg$ and $\lor$.

Question 6 tests the proof of mastery directly. To pass the chapter, you must answer Question 6 correctly in full, with every inference justified, and you must answer at least six of the other seven questions correctly.

### Question 1: unification

Run the rule-based algorithm on each pair, and report an mgu or the reason for failure.

(a) $h(x_1, g(x_1), x_2)$ and $h(f(x_3), x_4, x_3)$.

(b) $f(h(x_1), g(x_2, x_3), x_3)$ and $f(x_4, g(h(x_4), a), x_2)$.

(c) $p(x_1, f(x_2), x_2)$ and $p(f(x_3), x_3, g(x_1))$.

<details><summary>Solution</summary>

(a)

```
Decompose    x1 = f(x3),  g(x1) = x4,  x2 = x3
Eliminate x1 x1 = f(x3),  g(f(x3)) = x4,  x2 = x3
Orient       x1 = f(x3),  x4 = g(f(x3)),  x2 = x3
```

The problem is in solved form. The mgu is $\{x_1 \mapsto f(x_3), x_2 \mapsto x_3, x_4 \mapsto g(f(x_3))\}$, and both terms become $h(f(x_3), g(f(x_3)), x_3)$.

(b)

```
Decompose    h(x1) = x4,  g(x2, x3) = g(h(x4), a),  x3 = x2
Orient       x4 = h(x1),  g(x2, x3) = g(h(x4), a),  x3 = x2
Eliminate x4 x4 = h(x1),  g(x2, x3) = g(h(h(x1)), a),  x3 = x2
Decompose    x4 = h(x1),  x2 = h(h(x1)),  x3 = a,  x3 = x2
Eliminate x2 x4 = h(x1),  x2 = h(h(x1)),  x3 = a,  x3 = h(h(x1))
Eliminate x3 x4 = h(x1),  x2 = h(h(x1)),  x3 = a,  a = h(h(x1))
Clash on a = h(h(x1)): failure
```

(c)

```
Decompose    x1 = f(x3),  f(x2) = x3,  x2 = g(x1)
Eliminate x1 x1 = f(x3),  f(x2) = x3,  x2 = g(f(x3))
Orient       x1 = f(x3),  x3 = f(x2),  x2 = g(f(x3))
Eliminate x3 x1 = f(f(x2)),  x3 = f(x2),  x2 = g(f(f(x2)))
Occurs check on x2 = g(f(f(x2))): failure
```

</details>

### Question 2: resolution

(a) Refute the set below by resolution and factoring.

$$
S(x_1, x_2) \lor S(x_2, x_1), \qquad
\neg S(x_1, x_2) \lor \neg S(x_2, x_1) \lor T(x_1), \qquad
\neg T(x_1).
$$

(b) Refute the set below by resolution and factoring.

$$
P(x_1) \lor Q(x_1) \lor R(x_1, f(x_1)), \quad
\neg P(x_1) \lor Q(x_1), \quad
\neg Q(a), \quad
\neg R(a, x_1) \lor Q(x_1), \quad
\neg Q(f(a)).
$$

<details><summary>Solution</summary>

(a)

```
1. S(x1, x2) ∨ S(x2, x1)                 input
2. ¬S(x1, x2) ∨ ¬S(x2, x1) ∨ T(x1)       input
3. ¬T(x1)                                input
4. S(x1, x1)                             factor 1 with {x2 ↦ x1}
5. ¬S(x1, x1) ∨ T(x1)                    resolve 4 (renamed S(x3, x3)) and 2
                                         on ¬S(x1, x2), with {x1 ↦ x3, x2 ↦ x3}
6. T(x1)                                 resolve 4 and 5
7. ⊥                                     resolve 3 and 6
```

(b)

```
1. P(x1) ∨ Q(x1) ∨ R(x1, f(x1))          input
2. ¬P(x1) ∨ Q(x1)                        input
3. ¬Q(a)                                 input
4. ¬R(a, x1) ∨ Q(x1)                     input
5. ¬Q(f(a))                              input
6. P(a) ∨ Q(a) ∨ Q(f(a))                 resolve 1 and 4, with x1 ↦ a in 1
                                         and x1 ↦ f(a) in 4
7. P(a) ∨ Q(a)                           resolve 5 and 6
8. Q(a) ∨ Q(a)                           resolve 2 and 7, with {x1 ↦ a}
9. Q(a)                                  factor 8
10. ⊥                                    resolve 3 and 9
```

Other refutations are correct if each step is valid.

</details>

### Question 3: orderings

Use all weights equal to 1 with $w_0 = 1$ in KBO.

(a) With the precedence $g > f$, decide $g(f(x_1), x_2) \succ f(g(x_1, x_2))$ in LPO and in KBO. Write the derivation in each case. Decide the reverse comparison too.

(b) With the precedence $h > g$, decide $h(x_1, x_2) \succ g(x_1, x_1)$ in LPO and in KBO.

<details><summary>Solution</summary>

(a) Let $s = g(f(x_1), x_2)$ and $t = f(g(x_1, x_2))$.

LPO. Since $g > f$, it remains to show $s \succ g(x_1, x_2)$. The roots are equal, so use the lexicographic case. The term $s$ is above $x_1$ and $x_2$ because both occur in it. The first arguments give $f(x_1) \succ x_1$. So $s \succ t$.

KBO. Each variable occurs once on both sides. Both sides have weight 4. Since $g > f$, $s \succ t$.

The reverse fails in both orderings. In KBO the weights are equal and $f < g$ at the root. In LPO, $f < g$ rules out the precedence case, and the subterm case would need $g(x_1, x_2) \succeq s$, which fails because $x_1 \not\succeq f(x_1)$.

(b) LPO. Since $h > g$, it remains to show that $h(x_1, x_2)$ is above $x_1$ twice, which holds because $x_1$ occurs in it. So the comparison holds.

KBO. The right side has two occurrences of $x_1$ and the left has one, so the variable condition fails. The comparison does not hold, and the reverse does not hold either because $x_2$ is missing on the left of the reverse. The two terms are incomparable in KBO.

</details>

### Question 4: completion

(a) Run Knuth-Bendix completion on $f(g(f(x_1))) = g(x_1)$ with LPO and $f > g$. Check every critical pair of the final system.

(b) Run completion on $f(f(x_1)) = g(f(x_1))$ with LPO and $f > g$. Show that it diverges, and give the general form of the rules.

<details><summary>Solution</summary>

(a)

```
Orient   R1: f(g(f(x1))) → g(x1)
Deduce   R1 into position 1.1 of R1, with mgu {x1 ↦ g(f(x2))}
         peak  f(g(f(g(f(x2)))))
         inner f(g(g(x2)))
         outer g(g(f(x2)))
         Both are normal forms.
Orient   R2: f(g(g(x1))) → g(g(f(x1)))
```

The orientation holds because $f > g$ and $f(g(g(x_1)))$ is above $g(f(x_1))$, again by $f > g$ and $f(g(g(x_1))) \succ f(x_1)$. The latter follows from the lexicographic case with $g(g(x_1)) \succ x_1$.

The other overlaps are checked as follows.

```
R2 into position 1.1 of R1, with mgu {x1 ↦ g(g(x2))}
    peak   f(g(f(g(g(x2)))))
    inner  f(g(g(g(f(x2)))))  →  g(g(f(g(f(x2)))))  →  g(g(g(x2)))
    outer  g(g(g(x2)))
    These are joinable.
```

The left side of R1 does not unify with $g(g(x_1))$ or $g(x_1)$, so no overlap goes into R2 below the root. R1 and R2 do not unify at the root, because $f(\cdot)$ and $g(\cdot)$ clash at position 1.1. So the system $\{R1, R2\}$ is convergent.

(b)

```
Orient   R1: f(f(x1)) → g(f(x1))
Deduce   R1 into position 1 of R1
         peak f(f(f(x1)))
         inner f(g(f(x1)))
         outer g(f(f(x1))) → g(g(f(x1)))
Orient   R2: f(g(f(x1))) → g(g(f(x1)))
Deduce   R1 into position 1.1 of R2
         peak f(g(f(f(x1))))
         inner f(g(g(f(x1))))
         outer g(g(f(f(x1)))) → g(g(g(f(x1))))
Orient   R3: f(g(g(f(x1)))) → g(g(g(f(x1))))
```

By induction, write $g^n$ for $n$ applications of $g$. The rule $R_{n+1}$ is $f(g^n(f(x_1))) \to g^{n+1}(f(x_1))$. Overlapping R1 at the position of the inner $f$ gives the peak $f(g^n(f(f(x_1))))$. The inner step gives $f(g^{n+1}(f(x_1)))$. The outer step gives $g^{n+1}(f(f(x_1)))$, which reduces to $g^{n+2}(f(x_1))$. The inner term is not reducible by any rule so far, so a new rule $R_{n+2}$ results. Completion never terminates.

</details>

### Question 5: superposition rules

Use LPO with $f > a > b > c$ and no selection. Consider the clauses

$$
C_1 = f(x_1) \approx a \lor f(x_1) \approx b, \qquad C_2 = f(c) \not\approx b.
$$

List every inference of the superposition calculus from these two clauses. For each candidate you exclude, name the condition that rules it out.

<details><summary>Solution</summary>

In $C_1$, the literal $f(x_1) \approx a$ is strictly maximal, because $a \succ b$. It is the only literal in $C_1$ that can act as a positive premise.

Allowed inferences:

- Superposition left of $f(x_1) \approx a$ into $f(c)$ of $C_2$, with mgu $\{x_1 \mapsto c\}$. The conclusion is $f(c) \approx b \lor a \not\approx b$. After $\sigma$, $f(c) \succ a$, $f(c) \succ b$, $f(c) \approx a$ is strictly maximal in its premise, and $f(c) \not\approx b$ is maximal in its premise.
- Equality factoring on $C_1$, with $s = s' = f(x_1)$, $t = a$, $t' = b$ and the empty mgu. The conclusion is $a \not\approx b \lor f(x_1) \approx b$.

Excluded candidates:

- Superposition from $f(x_1) \approx b$ fails strict maximality, because $f(x_1) \approx a$ is greater.
- Superposition of $f(x_1) \approx a$ into a renamed copy of itself at the root is blocked by the condition $(l \approx r)\sigma \not\succeq (s \approx t)\sigma$, since the two literals become equal.
- Superposition of $f(x_1) \approx a$ into $f(x_1) \approx b$ of a renamed copy fails strict maximality in that target.
- Superposition of $f(x_1) \approx a$ into $a$ or into $x_1$ is excluded. The first is not unifiable, and the second is a variable position.
- Equality resolution on $C_2$ fails, since $f(c)$ and $b$ do not unify.

</details>

### Question 6: saturation by hand

This question tests the proof of mastery. Consider the following problem.

$$
\begin{aligned}
A_1 &: \forall x_1\, (A(x_1) \to \exists x_2\, (R(x_1, x_2) \land B(x_2))) \\
A_2 &: \forall x_1 \forall x_2\, (R(x_1, x_2) \land B(x_2) \to C(x_1)) \\
A_3 &: \forall x_1\, (C(x_1) \to f(x_1) \approx x_1) \\
A_4 &: \forall x_1\, g(f(x_1)) \approx h(x_1) \\
A_5 &: \forall x_1\, (A(x_1) \lor D(x_1)) \\
A_6 &: \forall x_1\, (D(x_1) \to f(x_1) \approx x_1) \\
G &: \forall x_1\, g(x_1) \approx h(x_1)
\end{aligned}
$$

Show that $A_1, \ldots, A_6 \models G$.

(a) Convert the axioms and the negated goal to clauses. Name the Skolem function for $x_2$ in $A_1$ as $k$, and the Skolem constant in the negated goal as $c$.

(b) Run the DISCOUNT given-clause loop by hand with this configuration.

- The ordering is KBO with all weights equal to 1 and precedence $A > B > C > D > R > g > h > f > k > c$.
- The selection function selects the heaviest negative literal, with ties broken alphabetically.
- The next given clause is the lightest passive clause, with the oldest first on ties, where weight counts symbol occurrences without $\top$.
- Number the input clauses in the order they appear: the two clauses from $A_1$, then the clauses from $A_2$, $A_3$ and $A_4$, then $A_5$, $A_6$ and the negated goal.

Report each given clause, each simplification and each generated clause.

(c) Report the final proof as the ancestor tree of $\bot$.

(d) State what would change in your conclusion if the run had ended with an empty passive set after a clause was discarded by a weight limit.

<details><summary>Solution</summary>

(a) The negated goal is $\exists x_1\, g(x_1) \not\approx h(x_1)$, which gives a Skolem constant $c$. The axiom $A_1$ gives two clauses after Skolemization and distribution.

```
[1] ¬A(x1) ∨ R(x1, k(x1))         weight 6
[2] ¬A(x1) ∨ B(k(x1))             weight 5
[3] ¬R(x1, x2) ∨ ¬B(x2) ∨ C(x1)   weight 7
[4] ¬C(x1) ∨ f(x1) ≈ x1           weight 5
[5] g(f(x1)) ≈ h(x1)              weight 5
[6] A(x1) ∨ D(x1)                 weight 4
[7] ¬D(x1) ∨ f(x1) ≈ x1           weight 5
[8] g(c) ≉ h(c)                   weight 4
```

(b) Selected literals are $\neg A(x_1)$ in [1] and [2], $\neg R(x_1, x_2)$ in [3], $\neg C(x_1)$ in [4] and $\neg D(x_1)$ in [7].

```
Given [6] A(x1) ∨ D(x1), weight 4.
    A(x1) is strictly maximal, since A > D. Active is otherwise empty.

Given [8] g(c) ≉ h(c), weight 4.
    Nothing is generated.

Given [2] ¬A(x1) ∨ B(k(x1)), weight 5, with ¬A(x1) selected.
    [9] D(x1) ∨ B(k(x1))             Res on [6] and [2], with x1 of [6] ↦ x1.

Given [4] ¬C(x1) ∨ f(x1) ≈ x1, weight 5, with ¬C(x1) selected.
    Nothing is generated, since no active clause has a positive C literal.

Given [5] g(f(x1)) ≈ h(x1), weight 5.
    g(f(x1)) does not unify with g(c), because f(x1) and c clash.
    Clauses with a selected literal block positive inferences, and
    the terms in their selected literals are predicate atoms that do not contain g.
    Nothing is generated.

Given [7] ¬D(x1) ∨ f(x1) ≈ x1, weight 5, with ¬D(x1) selected.
    No active clause has a strictly maximal D literal. In [6], A(x1) is maximal.
    Nothing is generated.

Given [9] D(x1) ∨ B(k(x1)), weight 5.
    B(k(x1)) is strictly maximal, since its weight is 3.
    No active clause has a selected ¬B literal.
    Nothing is generated.

Given [1] ¬A(x1) ∨ R(x1, k(x1)), weight 6, with ¬A(x1) selected.
    [10] D(x1) ∨ R(x1, k(x1))        Res on [6] and [1].

Given [10], weight 6.
    R(x1, k(x1)) is strictly maximal, and no active clause has a selected ¬R literal.
    Nothing is generated.

Given [3] ¬R(x1, x2) ∨ ¬B(x2) ∨ C(x1), weight 7, with ¬R(x1, x2) selected.
    [11] D(x1) ∨ ¬B(k(x1)) ∨ C(x1)   Res on [10] and [3], with mgu {x2 ↦ k(x1)}.

Given [11], weight 7, with ¬B(k(x1)) selected.
    [12] D(x1) ∨ C(x1)               Res on [9] and [11].
                                     The conclusion is D(x1) ∨ D(x1) ∨ C(x1),
                                     and merging the duplicate literal gives [12].

Given [12] D(x1) ∨ C(x1), weight 4.
    Backward subsumption: [12] subsumes [11], which is deleted.
    C(x1) is strictly maximal, since C > D.
    [13] D(x1) ∨ f(x1) ≈ x1          Res on [12] and [4].

Given [13], weight 5.
    D(x1) is strictly maximal, since D(x1) and f(x1) have equal weight and D > f.
    [14] f(x1) ≈ x1                  Res on [13] and [7].
                                     The conclusion is f(x1) ≈ x1 ∨ f(x1) ≈ x1,
                                     and merging the duplicate literal gives [14].

Given [14] f(x1) ≈ x1, weight 3.
    Backward subsumption deletes [4], [7] and [13].
    Backward demodulation of [5]: g(f(x1)) becomes g(x1), giving [15] g(x1) ≈ h(x1).
    The conditions hold, since f(x1) > x1 and [5] is above the unit instance.

Given [15] g(x1) ≈ h(x1), weight 4.
    Backward demodulation of [8], with match {x1 ↦ c}: g(c) > h(c), since g > h,
    and g(c) ≉ h(c) is above g(c) ≈ h(c). This gives h(c) ≉ h(c).
    Removing the trivial literal gives [16] ⊥. Stop.
```

(c)

```
[6]  A(x1) ∨ D(x1)                    input A5
[2]  ¬A(x1) ∨ B(k(x1))                input A1
[9]  D(x1) ∨ B(k(x1))                 Res [6], [2]
[1]  ¬A(x1) ∨ R(x1, k(x1))            input A1
[10] D(x1) ∨ R(x1, k(x1))             Res [6], [1]
[3]  ¬R(x1, x2) ∨ ¬B(x2) ∨ C(x1)      input A2
[11] D(x1) ∨ ¬B(k(x1)) ∨ C(x1)        Res [10], [3]
[12] D(x1) ∨ C(x1)                    Res [9], [11], merging duplicates
[4]  ¬C(x1) ∨ f(x1) ≈ x1              input A3
[13] D(x1) ∨ f(x1) ≈ x1               Res [12], [4]
[7]  ¬D(x1) ∨ f(x1) ≈ x1              input A6
[14] f(x1) ≈ x1                       Res [13], [7], merging duplicates
[5]  g(f(x1)) ≈ h(x1)                 input A4
[15] g(x1) ≈ h(x1)                    demodulation of [5] with [14]
[8]  g(c) ≉ h(c)                      negated goal
[16] ⊥                                demodulation of [8] with [15]
```

Since $\bot$ was derived and all inferences are sound, the clause set is unsatisfiable. Skolemization preserves satisfiability, so $A_1, \ldots, A_6 \models G$.

A different but valid answer is acceptable if it uses a different tie-break for the same stated rule. A short script reproduced this exact trace with an implementation of the loop, and z3 confirmed each proof step and the entailment.

(d) A refutation would stand, because soundness does not depend on completeness. An empty passive set with no $\bot$ after a non-redundant clause was discarded proves nothing, so the correct report is unknown. Without the discarded clause, the active set is not guaranteed to be saturated with respect to the input.

</details>

### Question 7: models from saturated sets

Consider the following clauses with KBO, all weights equal to 1, precedence $P > Q > R > a > b$, and no selection.

$$
P(a), \qquad \neg P(x_1) \lor Q(x_1), \qquad \neg Q(b), \qquad R(b) \lor Q(a).
$$

Saturate the set, then construct the candidate model over the Herbrand universe $\{a, b\}$.

<details><summary>Solution</summary>

In $\neg P(x_1) \lor Q(x_1)$, the literal $\neg P(x_1)$ is maximal, since $P(x_1) \succ Q(x_1)$ by the precedence. So ordered resolution with $P(a)$ gives $Q(a)$. The clause $R(b) \lor Q(a)$ is subsumed by $Q(a)$ and is deleted. There are no further inferences: $Q(a)$ cannot resolve with $\neg Q(b)$, and $\neg P(x_1)$ has only $P(a)$ to resolve with. The saturated set is $\{P(a), \neg P(x_1) \lor Q(x_1), \neg Q(b), Q(a)\}$, and it does not contain $\bot$, so the input is satisfiable.

The ground instances in increasing order, with the atom order $P(a) \succ P(b) \succ Q(a) \succ Q(b)$, are as follows.

```
clause          model before   true?   production
¬Q(b)           {}             yes     none
Q(a)            {}             no      produce Q(a)
¬P(b) ∨ Q(b)    {Q(a)}         yes     none
P(a)            {Q(a)}         no      produce P(a)
¬P(a) ∨ Q(a)    {Q(a), P(a)}   yes     none
```

The model is $\{P(a), Q(a)\}$, with all $R$ atoms false. The deleted clause $R(b) \lor Q(a)$ holds in it because $Q(a)$ is true.

</details>

### Question 8: proofs and explanations

(a) State and prove Newman's lemma.

(b) Prove that equality factoring is sound.

(c) Prove that demodulation with $l \approx r$ makes $C[l\sigma]$ redundant when $l\sigma \succ r\sigma$ and $C[l\sigma] \succ (l \approx r)\sigma$.

(d) Explain why superposition into a variable position is unnecessary.

(e) State one difference between the Otter and DISCOUNT loops, and explain why a time-out proves neither satisfiability nor unsatisfiability.

<details><summary>Solution</summary>

(a) Newman's lemma states that a terminating relation is confluent if and only if it is locally confluent. Confluence clearly implies local confluence. For the converse, use well-founded induction on $x$ with the claim that all $y, z$ with $y \leftarrow^* x \to^* z$ are joinable. The claim is immediate if $x = y$ or $x = z$. Otherwise $x \to y_1 \to^* y$ and $x \to z_1 \to^* z$. Local confluence gives $u$ with $y_1 \to^* u$ and $z_1 \to^* u$. The induction hypothesis on $y_1$ gives $v$ with $y \to^* v$ and $u \to^* v$. The induction hypothesis on $z_1$, applied to $v$ and $z$, gives $w$ with $v \to^* w$ and $z \to^* w$. So $y$ and $z$ are joinable at $w$.

(b) Let the premise be $C \lor s \approx t \lor s' \approx t'$ with $\sigma = \mathrm{mgu}(s, s')$. Take any interpretation and assignment for the instance under $\sigma$. If $C\sigma$ holds, or $(s' \approx t')\sigma$ holds, then the conclusion holds. Otherwise $(s \approx t)\sigma$ holds. If $t\sigma$ and $t'\sigma$ differ in value, the literal $(t \not\approx t')\sigma$ holds. If they are equal, then $s'\sigma = s\sigma$ equals $t\sigma$, which equals $t'\sigma$, so $(s' \approx t')\sigma$ holds. This contradicts the case assumption, so the conclusion holds in all cases.

(c) Let $\theta$ make $C[l\sigma]$ ground. The clause $C[l\sigma]\theta$ follows from $C[r\sigma]\theta$ and $(l \approx r)\sigma\theta$ by congruence. Stability and monotonicity give $C[r\sigma]\theta \prec C[l\sigma]\theta$. Stability also gives $(l \approx r)\sigma\theta \prec C[l\sigma]\theta$. So each ground instance follows from smaller ground instances of clauses in the set, which is the definition of redundancy.

(d) Suppose a ground instance $C\theta$ has a reducible term $x\theta$ at a variable position. Let $\theta'$ replace $x\theta$ with its normal form under the candidate model. Then $C\theta' \prec C\theta$, by monotonicity, and $C\theta'$ is a ground instance of the same clause. By minimality of the counterexample, $C\theta'$ is true in the candidate model. Since $x\theta$ and $x\theta'$ have the same normal form, $C\theta$ is also true. So the reducible case never needs an inference.

(e) The Otter loop simplifies new clauses using active and passive clauses, while the DISCOUNT loop uses only active clauses. A time-out proves nothing because unsatisfiability needs a derived $\bot$, and satisfiability needs a finished fair saturation. A run stopped by a resource limit has neither.

</details>

## Main materials

- [Harrison, Handbook of Practical Logic and Automated Reasoning.](https://www.cl.cam.ac.uk/~jrh13/atp/)
- Baader and Nipkow, Term Rewriting and All That.
