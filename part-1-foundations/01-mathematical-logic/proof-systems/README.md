# Proof Systems

Part 1, Chapter 1: Mathematical Logic.

## Objective

Derive formulas in natural deduction, sequent calculus and resolution and explain how the systems differ.

## Why this matters

A truth table certifies validity by exhausting all cases, and that certificate grows exponentially. A proof system gives a syntactic certificate that a machine can check without knowing why it is correct. Natural deduction is the logic behind proof assistants, sequent calculus is the logic behind tableau-style search and the source of cut elimination, and resolution is the rule that a CDCL solver applies when it learns a clause. You will use these ideas in [Resolution and DPLL](../../../part-2-core-reasoning/04-sat/resolution-and-dpll/), [Proofs and Certificates](../../../part-2-core-reasoning/04-sat/proofs-and-certificates/) and [Proof Complexity](../../02-decidability-and-complexity/proof-complexity/). In practice, an applied scientist relies on proofs whenever a solver's unsatisfiability claim must be checked independently of the solver.

## Prerequisites

- [Propositional Logic](../propositional-logic/)

## Lesson

### What a proof system is

A proof system consists of a set of formal objects called proofs, together with a mechanical check that a given object is a proof of a given formula. Cook and Reckhow gave the standard general definition in 1979: a propositional proof system is a polynomial-time computable function from strings onto the set of tautologies, and a string $w$ is regarded as a proof of the formula it maps to. The definition captures the one property that matters for trust, which is that checking a proof is easy even if finding one is hard.

Three properties of a system are studied. It is sound if everything it proves is valid. It is complete if everything valid can be proved. Its efficiency concerns the size of the smallest proofs. The first two are the subject of [Soundness and Completeness](../soundness-and-completeness/). In this topic you learn to use the systems.

From here on, we work over the connectives $\bot, \neg, \land, \lor, \to$. Treat $\top$ as an abbreviation for $\neg \bot$, and $\varphi \leftrightarrow \psi$ as an abbreviation for $(\varphi \to \psi) \land (\psi \to \varphi)$. Both abbreviations have the semantics given in [Propositional Logic](../propositional-logic/).

### Hilbert systems

Frege's 1879 system and the systems of Hilbert and his school use many axioms and few rules. A standard system for the connectives $\neg$ and $\to$, due to Łukasiewicz, has three axiom schemas

$$
\begin{aligned}
\text{A1:}\quad & \varphi \to (\psi \to \varphi),\\
\text{A2:}\quad & (\varphi \to (\psi \to \chi)) \to ((\varphi \to \psi) \to (\varphi \to \chi)),\\
\text{A3:}\quad & (\neg \psi \to \neg \varphi) \to (\varphi \to \psi),
\end{aligned}
$$

and one rule, modus ponens: from $\varphi$ and $\varphi \to \psi$ infer $\psi$. A derivation from $\Gamma$ is a finite sequence of formulas, each of which is an instance of an axiom schema, a member of $\Gamma$, or the result of modus ponens on two earlier formulas.

Even $\varphi \to \varphi$ needs some ingenuity:

```text
1. φ → ((φ → φ) → φ)                                A1
2. (φ → ((φ → φ) → φ)) → ((φ → (φ → φ)) → (φ → φ))  A2
3. (φ → (φ → φ)) → (φ → φ)                          modus ponens on 1, 2
4. φ → (φ → φ)                                      A1
5. φ → φ                                            modus ponens on 4, 3
```

Hilbert systems are convenient to reason about, since there is only one rule to consider in an induction, and inconvenient to use. The deduction theorem (Exercise 9) recovers the ordinary practice of assuming a hypothesis, and that practice led to the next system.

### Natural deduction

Gentzen and, independently, Jaśkowski introduced natural deduction in 1934 to match how mathematicians argue, with assumptions that are made and later discharged. Each connective has introduction rules, which say how to establish it, and elimination rules, which say how to use it.

The judgment $\Gamma \vdash \varphi$ means that $\varphi$ is derivable from the set of assumptions $\Gamma$. We write $\Gamma, \varphi$ for $\Gamma \cup \{\varphi\}$. A derivation is a finite tree built from these rules:

$$
\frac{\varphi \in \Gamma}{\Gamma \vdash \varphi}\ \text{Ax}
\qquad
\frac{\Gamma \vdash \varphi \quad \Gamma \vdash \psi}{\Gamma \vdash \varphi \land \psi}\ {\land}\text{I}
\qquad
\frac{\Gamma \vdash \varphi \land \psi}{\Gamma \vdash \varphi}\ {\land}\text{E}_1
\qquad
\frac{\Gamma \vdash \varphi \land \psi}{\Gamma \vdash \psi}\ {\land}\text{E}_2
$$

$$
\frac{\Gamma \vdash \varphi}{\Gamma \vdash \varphi \lor \psi}\ {\lor}\text{I}_1
\qquad
\frac{\Gamma \vdash \psi}{\Gamma \vdash \varphi \lor \psi}\ {\lor}\text{I}_2
\qquad
\frac{\Gamma \vdash \varphi \lor \psi \quad \Gamma, \varphi \vdash \chi \quad \Gamma, \psi \vdash \chi}{\Gamma \vdash \chi}\ {\lor}\text{E}
$$

$$
\frac{\Gamma, \varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}\ {\to}\text{I}
\qquad
\frac{\Gamma \vdash \varphi \to \psi \quad \Gamma \vdash \varphi}{\Gamma \vdash \psi}\ {\to}\text{E}
$$

$$
\frac{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg \varphi}\ {\neg}\text{I}
\qquad
\frac{\Gamma \vdash \neg \varphi \quad \Gamma \vdash \varphi}{\Gamma \vdash \bot}\ {\neg}\text{E}
\qquad
\frac{\Gamma \vdash \bot}{\Gamma \vdash \varphi}\ {\bot}\text{E}
\qquad
\frac{\Gamma, \neg \varphi \vdash \bot}{\Gamma \vdash \varphi}\ \text{RAA}
$$

RAA stands for reductio ad absurdum. Compare it with $\neg$I. The rule $\neg$I proves a negation by refuting the unnegated formula, and it is constructively acceptable. RAA proves an arbitrary formula by refuting its negation, and it is the one rule that makes the system classical. Removing RAA gives intuitionistic natural deduction, in which $x_1 \lor \neg x_1$ and Peirce's law have no proof.

Writing proofs. Trees grow wide, so in practice proofs are written as numbered lines with nested scopes, in the style due to Fitch and used by Huth and Ryan. In the traces below, each bar marks a level of scope. An indented block begins with its assumption, and the block closes when the indentation returns. The notation $i\text{-}j$ cites a closed block from line $i$ to line $j$. A line may be used only while it is in scope, which means that no block containing it has closed. The justification "copy" repeats a line that is in scope. It is the rule Ax applied to a formula already derived, and it can always be removed by reusing the earlier derivation.

To find a natural deduction proof, work from both ends. Look at the goal and use its introduction rule, which often adds an assumption. Look at the assumptions and apply elimination rules. If that stalls and the goal has no useful structure, assume its negation and use RAA.

Example: the law of excluded middle. The goal has no direct proof, so the outermost step is RAA.

```text
1  | | ¬(x1 ∨ ¬x1)      assumption
2  | | | x1             assumption
3  | | | x1 ∨ ¬x1       ∨I 2
4  | | | ⊥              ¬E 1, 3
5  | | ¬x1              ¬I 2-4
6  | | x1 ∨ ¬x1         ∨I 5
7  | | ⊥                ¬E 1, 6
8  | x1 ∨ ¬x1           RAA 1-7
```

### Sequent calculus

Gentzen introduced sequent calculus in the same 1934 work in order to prove a normal form theorem for classical logic. A sequent is an expression $\Gamma \Rightarrow \Delta$, where $\Gamma$ (the antecedent) and $\Delta$ (the succedent) are finite multisets of formulas. Its meaning is:

$$
\Gamma \Rightarrow \Delta \text{ is valid if and only if every assignment that satisfies all of } \Gamma \text{ satisfies at least one formula of } \Delta.
$$

So commas on the left behave like conjunction, and commas on the right behave like disjunction. An empty antecedent is true and an empty succedent is false. We use $\Rightarrow$ for the sequent separator, and we keep $\vdash$ for derivability, so that $\vdash_{\mathsf{G}} \Gamma \Rightarrow \Delta$ means that the sequent has a derivation.

We use the system known as G3 (without structural rules), in which every sequent rule has the principal formula removed from its premises. The axioms, with $x$ a variable, are

$$
\Gamma, x \Rightarrow x, \Delta \qquad\qquad \Gamma, \bot \Rightarrow \Delta
$$

and the rules are:

$$
\frac{\Gamma \Rightarrow \varphi, \Delta}{\Gamma, \neg \varphi \Rightarrow \Delta}\ {\neg}\text{L}
\qquad
\frac{\Gamma, \varphi \Rightarrow \Delta}{\Gamma \Rightarrow \neg \varphi, \Delta}\ {\neg}\text{R}
$$

$$
\frac{\Gamma, \varphi, \psi \Rightarrow \Delta}{\Gamma, \varphi \land \psi \Rightarrow \Delta}\ {\land}\text{L}
\qquad
\frac{\Gamma \Rightarrow \varphi, \Delta \quad \Gamma \Rightarrow \psi, \Delta}{\Gamma \Rightarrow \varphi \land \psi, \Delta}\ {\land}\text{R}
$$

$$
\frac{\Gamma, \varphi \Rightarrow \Delta \quad \Gamma, \psi \Rightarrow \Delta}{\Gamma, \varphi \lor \psi \Rightarrow \Delta}\ {\lor}\text{L}
\qquad
\frac{\Gamma \Rightarrow \varphi, \psi, \Delta}{\Gamma \Rightarrow \varphi \lor \psi, \Delta}\ {\lor}\text{R}
$$

$$
\frac{\Gamma \Rightarrow \varphi, \Delta \quad \Gamma, \psi \Rightarrow \Delta}{\Gamma, \varphi \to \psi \Rightarrow \Delta}\ {\to}\text{L}
\qquad
\frac{\Gamma, \varphi \Rightarrow \psi, \Delta}{\Gamma \Rightarrow \varphi \to \psi, \Delta}\ {\to}\text{R}
$$

Read each rule from the bottom up, as a step of proof search. Each step removes one connective, so search terminates. Each rule is also invertible: the conclusion is valid if and only if all its premises are valid. So the order in which you apply rules cannot affect whether a proof exists, and no backtracking is needed. Search ends in leaves containing only atoms. If all leaves are axioms you have a proof. An open leaf with no atom common to both sides and no $\bot$ on the left gives a countermodel: make its left variables true and its other variables false. The proof of all this is in [Soundness and Completeness](../soundness-and-completeness/).

The cut rule is the following additional rule:

$$
\frac{\Gamma \Rightarrow \varphi, \Delta \quad \Gamma, \varphi \Rightarrow \Delta}{\Gamma \Rightarrow \Delta}\ \text{Cut}
$$

Cut is the use of a lemma: first prove $\varphi$, then use it. It is the only rule whose premises mention a formula that may be absent from the conclusion.

Theorem (Gentzen's Hauptsatz, or cut elimination). Any sequent derivable with Cut is derivable without Cut.

Corollary (subformula property). In a cut-free derivation, every formula is a subformula of a formula in the final sequent.

The subformula property is what makes search feasible, since it limits what a search must consider. Cut elimination comes at a cost, because removing cuts can make a proof exponentially larger, as discussed below. For propositional logic, cut elimination also follows from a semantic argument, which is Exercise 8 of the next topic.

In the traces below, a sequent derivation is written from the root downward, with each premise indented two spaces under its conclusion and the rule applied named at the right. The word "axiom" marks a closed leaf and the word "open" marks a failed leaf.

### Resolution

Resolution was introduced as a complete first-order method by Robinson in 1965, and its propositional form appears in the work of Davis and Putnam in 1960. It has no axioms, one rule and a restricted input format.

A clause is a finite set of literals, read as their disjunction. The empty clause, written $\square$ and shown as `{}` in traces, is false under every assignment. A clause set is read as the conjunction of its clauses, which is a formula in conjunctive normal form (see [Normal Forms and Skolemization](../normal-forms-and-skolemization/)).

The resolution rule is:

$$
\frac{C \cup \{x\} \quad D \cup \{\neg x\}}{C \cup D}
$$

The conclusion $C \cup D$ is called the resolvent on $x$. A resolution derivation from a clause set $S$ is a sequence of clauses, each of which is in $S$ or is a resolvent of two earlier clauses. A refutation of $S$ is a derivation that ends in $\square$.

Theorem (preview). A finite clause set $S$ is unsatisfiable if and only if $S$ has a resolution refutation.

To prove $\Gamma \models \varphi$, convert $\Gamma \cup \{\neg\varphi\}$ to clauses and refute them. Resolution is complete only for refutation. It is not complete for deriving consequences directly, since $\{x_1\} \models \{x_1, x_2\}$ holds and yet no resolution step applies to the single clause $\{x_1\}$.

Saturation is a decision procedure:

```text
function RESOLUTION-SAT(S):
    while true:
        for each pair of clauses in S and each clashing variable x:
            let R be the resolvent on x
            if R is the empty clause then return unsatisfiable
        let New be the non-tautological resolvents not already in S
        if New is empty then return satisfiable
        S := S ∪ New
```

Over $n$ variables, there are at most $3^n$ non-tautological clauses, because each variable occurs positively, negatively or not at all. So the procedure terminates. Dropping tautological resolvents is safe, because the completeness proof in the next topic produces refutations that contain no tautological clause. Unrestricted saturation is very expensive, and practical solvers use conflict analysis to choose which resolvents to derive.

Resolution is a restricted form of cut. Write the clause $\{\neg y_1, \dots, \neg y_k, z_1, \dots, z_m\}$ as the sequent $y_1, \dots, y_k \Rightarrow z_1, \dots, z_m$. Then a resolution step is a cut on the atom $x$, followed by contraction of duplicate literals.

### How the systems differ

All three systems are sound and complete for classical propositional logic, so they agree on what is provable. They differ in how proofs are found and how large they must be.

| Aspect | Natural deduction | Sequent calculus (G3) | Resolution |
|---|---|---|---|
| Input | It accepts any formula and any assumptions. | It accepts any sequent of formulas. | It accepts clauses only. |
| Direction of the argument | It argues directly from assumptions to a goal. | It decomposes a goal until only atoms are left. | It refutes the negated goal. |
| Number of rules | It has introduction and elimination rules for each connective. | It has one left rule and one right rule for each connective. | It has one rule. |
| Subformula property | It holds only for normalized proofs, with a small exception for RAA. | It holds for all cut-free proofs. | Every literal comes from the input clauses. |
| Main use | It is the basis of proof assistants and of human-readable proofs. | It is the basis of tableaux and of proof-theoretic analysis. | It is the basis of SAT and first-order provers. |
| Failure of search | A failed attempt tells you nothing. | A completed failed search gives a countermodel. | A saturated clause set with no empty clause is satisfiable. |

Translations. Introduction rules in natural deduction correspond to right rules in sequent calculus. Elimination rules correspond to left rules used together with Cut. Restricting succedents to at most one formula yields Gentzen's intuitionistic calculus, which is why several formulas on the right are the source of classical strength in sequent calculus, in the same way that RAA is in natural deduction.

Efficiency. Hilbert (Frege) systems, natural deduction and sequent calculus with cut polynomially simulate one another, so they are equally efficient up to a polynomial factor. Cut-free sequent proofs can be exponentially larger than proofs with cut. Resolution is polynomially simulated by these systems, and it is strictly weaker: Haken proved in 1985 that the pigeonhole formulas require exponential-size resolution refutations, while Buss proved in 1987 that they have polynomial-size Frege proofs. This gap explains why stronger reasoning in solvers has long been an active research topic, and it is treated in [Proof Complexity](../../02-decidability-and-complexity/proof-complexity/).

## Worked examples

### Example 1: one theorem in all three systems

Prove the constructive dilemma:

$$
((x_1 \to x_2) \land (x_3 \to x_4)) \to ((x_1 \lor x_3) \to (x_2 \lor x_4)).
$$

Natural deduction. Introduce the two implications, then split on the disjunction.

```text
1  | | (x1 → x2) ∧ (x3 → x4)                                 assumption
2  | | | x1 ∨ x3                                             assumption
3  | | | x1 → x2                                             ∧E 1
4  | | | x3 → x4                                             ∧E 1
5  | | | | x1                                                assumption
6  | | | | x2                                                →E 3, 5
7  | | | | x2 ∨ x4                                           ∨I 6
8  | | | | x3                                                assumption
9  | | | | x4                                                →E 4, 8
10 | | | | x2 ∨ x4                                           ∨I 9
11 | | | x2 ∨ x4                                             ∨E 2, 5-7, 8-10
12 | | (x1 ∨ x3) → (x2 ∨ x4)                                 →I 2-11
13 | ((x1 → x2) ∧ (x3 → x4)) → ((x1 ∨ x3) → (x2 ∨ x4))       →I 1-12
```

This proof does not use RAA, so the theorem holds intuitionistically.

Sequent calculus. Apply rules from the root upward. The left rule $\lor$L creates two branches, and each $\to$L creates two more.

```text
⇒ ((x1 → x2) ∧ (x3 → x4)) → ((x1 ∨ x3) → (x2 ∨ x4))        →R
  (x1 → x2) ∧ (x3 → x4) ⇒ (x1 ∨ x3) → (x2 ∨ x4)            ∧L
    x1 → x2, x3 → x4 ⇒ (x1 ∨ x3) → (x2 ∨ x4)               →R
      x1 → x2, x3 → x4, x1 ∨ x3 ⇒ x2 ∨ x4                  ∨R
        x1 → x2, x3 → x4, x1 ∨ x3 ⇒ x2, x4                 ∨L
          x1 → x2, x3 → x4, x1 ⇒ x2, x4                    →L
            x3 → x4, x1 ⇒ x1, x2, x4                       axiom
            x2, x3 → x4, x1 ⇒ x2, x4                       axiom
          x1 → x2, x3 → x4, x3 ⇒ x2, x4                    →L
            x1 → x2, x3 ⇒ x3, x2, x4                       axiom
            x1 → x2, x4, x3 ⇒ x2, x4                       axiom
```

The sequents with an implication at the left that are closed as axioms still contain a compound formula. That is allowed: the axiom only requires a shared variable, and the other formulas are side formulas.

Resolution. Negate the theorem. Its negation is equivalent to the conjunction of $x_1 \to x_2$, $x_3 \to x_4$, $x_1 \lor x_3$, $\neg x_2$ and $\neg x_4$. These give five clauses.

```text
1. {¬x1, x2}     given
2. {¬x3, x4}     given
3. {x1, x3}      given
4. {¬x2}         given
5. {¬x4}         given
6. {¬x1}         resolve 1, 4 on x2
7. {¬x3}         resolve 2, 5 on x4
8. {x3}          resolve 3, 6 on x1
9. {}            resolve 7, 8 on x3
```

Compare the three proofs. The natural deduction proof follows the informal argument. The sequent proof needed no choices. The resolution proof is the shortest, but only because the negation put the formula into a form suited to the rule.

### Example 2: Peirce's law needs classical reasoning

Natural deduction. The goal $x_1$ is a variable with no introduction rule, and the available assumption is an implication whose antecedent is not obviously provable. So use RAA.

```text
1  | | (x1 → x2) → x1       assumption
2  | | | ¬x1                assumption
3  | | | | x1               assumption
4  | | | | ⊥                ¬E 2, 3
5  | | | | x2               ⊥E 4
6  | | | x1 → x2            →I 3-5
7  | | | x1                 →E 1, 6
8  | | | ⊥                  ¬E 2, 7
9  | | x1                   RAA 2-8
10 | ((x1 → x2) → x1) → x1  →I 1-9
```

Sequent calculus. Observe how the second occurrence of $x_1$ on the right, which is possible only with multiple succedents, closes the first branch.

```text
⇒ ((x1 → x2) → x1) → x1       →R
  (x1 → x2) → x1 ⇒ x1         →L
    ⇒ x1 → x2, x1             →R
      x1 ⇒ x2, x1             axiom
    x1 ⇒ x1                   axiom
```

### Example 3: failed search gives a countermodel

Search for a proof of $(x_1 \to x_2) \Rightarrow (x_2 \to x_1)$.

```text
x1 → x2 ⇒ x2 → x1      →R
  x1 → x2, x2 ⇒ x1     →L
    x2 ⇒ x1, x1        open
    x2, x2 ⇒ x1        open
```

Both leaves are atomic and share no variable, so the sequent has no proof. Since the rules are invertible, trying a different order would not help. From an open leaf, make the left variables true and the others false: $v(x_2) = 1$, $v(x_1) = 0$. Check it: $x_1 \to x_2$ is true and $x_2 \to x_1$ is false, so this assignment refutes the original sequent.

### Example 4: a pigeonhole refutation

Refute the claim that three pigeons fit in two holes with no hole shared. Let $x_1, x_2$ say that pigeon 1 is in hole 1 or hole 2, let $x_3, x_4$ say the same for pigeon 2, and let $x_5, x_6$ say the same for pigeon 3. Clauses 1 to 3 place each pigeon in a hole. Clauses 4 to 9 forbid two pigeons in one hole. The refutation first derives that pigeon 3 cannot be in hole 2, and then that pigeon 3 is in hole 1, from which the other two pigeons are forced into hole 2.

```text
1.  {x1, x2}       given
2.  {x3, x4}       given
3.  {x5, x6}       given
4.  {¬x1, ¬x3}     given
5.  {¬x1, ¬x5}     given
6.  {¬x3, ¬x5}     given
7.  {¬x2, ¬x4}     given
8.  {¬x2, ¬x6}     given
9.  {¬x4, ¬x6}     given
10. {x2, ¬x3}      resolve 1, 4 on x1
11. {x2, x4}       resolve 10, 2 on x3
12. {x4, ¬x6}      resolve 11, 8 on x2
13. {¬x6}          resolve 12, 9 on x4
14. {x5}           resolve 3, 13 on x6
15. {¬x1}          resolve 5, 14 on x5
16. {¬x3}          resolve 6, 14 on x5
17. {x2}           resolve 1, 15 on x1
18. {x4}           resolve 2, 16 on x3
19. {¬x4}          resolve 7, 17 on x2
20. {}             resolve 18, 19 on x4
```

This small instance needs only eleven resolution steps. By Haken's theorem, the required number of steps grows exponentially with the number of pigeons, even though the informal counting argument stays short.

## Common mistakes

- Using a line from a closed block. Once a block has closed, its assumption and everything derived under it are out of scope. For example, $x_1 \lor x_2 \vdash x_1$ cannot be proved by assuming $x_1$, closing that block, and copying $x_1$ into the $x_2$ block. Only the closed block as a whole can be cited.
- Confusing $\neg$I with RAA. From $\Gamma, \varphi \vdash \bot$, the rule $\neg$I gives $\neg\varphi$. From $\Gamma, \neg \varphi \vdash \bot$, RAA gives $\varphi$. The second rule is the classical one.
- Resolving on two variables at once. From $\{x_1, x_2\}$ and $\{\neg x_1, \neg x_2\}$, it is wrong to conclude $\square$. These clauses are jointly satisfied by $x_1 = 1$, $x_2 = 0$. Each of the two legal resolvents is a tautology, such as $\{x_2, \neg x_2\}$.
- Forgetting to negate the conclusion before using resolution. Refuting $\Gamma \cup \{\varphi\}$ shows that $\Gamma \models \neg \varphi$, which is a different claim from $\Gamma \models \varphi$.
- Expecting resolution to derive every consequence. It finds $\square$ whenever the set is unsatisfiable, and it need not derive a given implied clause.
- Reading the comma on the right of a sequent as conjunction. The sequent $\Rightarrow x_1, \neg x_1$ is valid because the right side reads as a disjunction.
- Misplacing the premises of $\to$L. The formula $\varphi$ goes to the right of the first premise, since it must be proved. The formula $\psi$ goes to the left of the second premise, since it may be used.
- Concluding non-provability from a failed natural deduction attempt. Natural deduction search has no such guarantee. Use completeness: if a formula has a countermodel, it has no proof, and if it has none, a proof exists even if you have not found it.
- Assuming that cut elimination makes proofs shorter. It makes them analytic, and it can make them exponentially longer.

## Exercises

### Exercise 1

State the rules $\lor$E and RAA. Say which assumptions are discharged in each, and say which rule of natural deduction makes the system classical.

<details><summary>Solution</summary>

The rule $\lor$E says that from $\Gamma \vdash \varphi \lor \psi$, $\Gamma, \varphi \vdash \chi$ and $\Gamma, \psi \vdash \chi$ you may infer $\Gamma \vdash \chi$. It discharges $\varphi$ in the second subderivation and $\psi$ in the third.

The rule RAA says that from $\Gamma, \neg\varphi \vdash \bot$ you may infer $\Gamma \vdash \varphi$. It discharges $\neg\varphi$.

RAA makes the system classical, since removing it leaves intuitionistic natural deduction.

</details>

### Exercise 2

Derive the contrapositive in natural deduction: $x_1 \to x_2 \vdash \neg x_2 \to \neg x_1$.

<details><summary>Solution</summary>

```text
1  | x1 → x2          premise
2  | | ¬x2            assumption
3  | | | x1           assumption
4  | | | x2           →E 1, 3
5  | | | ⊥            ¬E 2, 4
6  | | ¬x1            ¬I 3-5
7  | ¬x2 → ¬x1        →I 2-6
```

The proof does not use RAA. The converse direction, from $\neg x_2 \to \neg x_1$ to $x_1 \to x_2$, requires it.

</details>

### Exercise 3

Derive the classical direction of De Morgan's law in natural deduction: $\neg(x_1 \land x_2) \vdash \neg x_1 \lor \neg x_2$.

<details><summary>Solution</summary>

```text
1  | ¬(x1 ∧ x2)            premise
2  | | ¬(¬x1 ∨ ¬x2)        assumption
3  | | | ¬x1               assumption
4  | | | ¬x1 ∨ ¬x2         ∨I 3
5  | | | ⊥                 ¬E 2, 4
6  | | x1                  RAA 3-5
7  | | | ¬x2               assumption
8  | | | ¬x1 ∨ ¬x2         ∨I 7
9  | | | ⊥                 ¬E 2, 8
10 | | x2                  RAA 7-9
11 | | x1 ∧ x2             ∧I 6, 10
12 | | ⊥                   ¬E 1, 11
13 | ¬x1 ∨ ¬x2             RAA 2-12
```

</details>

### Exercise 4

Derive $(x_1 \to x_2) \lor (x_2 \to x_1)$ in natural deduction.

<details><summary>Solution</summary>

Assume the negation. Under an additional assumption $x_2$, you can obtain $x_1 \to x_2$ and hence a contradiction. That gives $x_2 \to x_1$ by $\bot$E, and so another contradiction.

```text
1  | | ¬((x1 → x2) ∨ (x2 → x1))    assumption
2  | | | x2                        assumption
3  | | | | x1                      assumption
4  | | | | x2                      copy 2
5  | | | x1 → x2                   →I 3-4
6  | | | (x1 → x2) ∨ (x2 → x1)     ∨I 5
7  | | | ⊥                         ¬E 1, 6
8  | | | x1                        ⊥E 7
9  | | x2 → x1                     →I 2-8
10 | | (x1 → x2) ∨ (x2 → x1)       ∨I 9
11 | | ⊥                           ¬E 1, 10
12 | (x1 → x2) ∨ (x2 → x1)         RAA 1-11
```

</details>

### Exercise 5

Give a sequent calculus proof of $\neg(x_1 \land x_2) \Rightarrow \neg x_1 \lor \neg x_2$.

<details><summary>Solution</summary>

```text
¬(x1 ∧ x2) ⇒ ¬x1 ∨ ¬x2       ∨R
  ¬(x1 ∧ x2) ⇒ ¬x1, ¬x2      ¬R
    ¬(x1 ∧ x2), x1 ⇒ ¬x2     ¬R
      ¬(x1 ∧ x2), x1, x2 ⇒   ¬L
        x1, x2 ⇒ x1 ∧ x2     ∧R
          x1, x2 ⇒ x1        axiom
          x1, x2 ⇒ x2        axiom
```

Compared with Exercise 3, the proof involves no ingenuity: each step is determined up to order.

</details>

### Exercise 6

Run sequent search on $x_1 \lor x_2 \Rightarrow x_1 \land x_2$ and read off every countermodel that the open leaves give.

<details><summary>Solution</summary>

```text
x1 ∨ x2 ⇒ x1 ∧ x2       ∧R
  x1 ∨ x2 ⇒ x1          ∨L
    x1 ⇒ x1             axiom
    x2 ⇒ x1             open
  x1 ∨ x2 ⇒ x2          ∨L
    x1 ⇒ x2             open
    x2 ⇒ x2             axiom
```

The leaf $x_2 \Rightarrow x_1$ gives $v(x_2) = 1$, $v(x_1) = 0$. The leaf $x_1 \Rightarrow x_2$ gives $v(x_1) = 1$, $v(x_2) = 0$. Under each assignment, $x_1 \lor x_2$ is true and $x_1 \land x_2$ is false.

</details>

### Exercise 7

Use resolution to show that $\{x_1 \to x_2,\; x_2 \to x_3,\; x_3 \to x_4\} \models x_1 \to x_4$.

<details><summary>Solution</summary>

The negated conclusion $\neg(x_1 \to x_4)$ is equivalent to $x_1 \land \neg x_4$, which yields the unit clauses $\{x_1\}$ and $\{\neg x_4\}$.

```text
1. {¬x1, x2}     given
2. {¬x2, x3}     given
3. {¬x3, x4}     given
4. {x1}          given
5. {¬x4}         given
6. {x2}          resolve 1, 4 on x1
7. {x3}          resolve 2, 6 on x2
8. {x4}          resolve 3, 7 on x3
9. {}            resolve 5, 8 on x4
```

This pattern of resolving with unit clauses is unit propagation.

</details>

### Exercise 8

Prove that the resolution rule is sound: if an assignment satisfies both $C \cup \{x\}$ and $D \cup \{\neg x\}$, it satisfies $C \cup D$. Deduce that if $S$ has a refutation, then $S$ is unsatisfiable.

<details><summary>Solution</summary>

Let $v$ satisfy both premises. If $v(x) = 1$, then $v$ falsifies $\neg x$, so it must satisfy a literal of $D$. If $v(x) = 0$, then $v$ falsifies $x$, so it must satisfy a literal of $C$. Either way, $v$ satisfies a literal of $C \cup D$.

If $v$ satisfied $S$, then by induction on the length of a derivation, $v$ would satisfy each clause of the derivation. The last clause is $\square$, which no assignment satisfies. So no such $v$ exists.

</details>

### Exercise 9

Prove the deduction theorem for the Hilbert system: if $\Gamma, \varphi \vdash \psi$, then $\Gamma \vdash \varphi \to \psi$.

<details><summary>Solution</summary>

Use induction on the length of the derivation of $\psi$ from $\Gamma, \varphi$, considering how its last line is justified.

Case $\psi$ is an axiom instance or a member of $\Gamma$. Then $\Gamma \vdash \psi$ in one line. Also, $\psi \to (\varphi \to \psi)$ is an instance of A1, and modus ponens gives $\Gamma \vdash \varphi \to \psi$.

Case $\psi = \varphi$. The five-line derivation in the lesson gives $\vdash \varphi \to \varphi$.

Case $\psi$ follows by modus ponens from $\chi$ and $\chi \to \psi$. By the induction hypothesis, $\Gamma \vdash \varphi \to \chi$ and $\Gamma \vdash \varphi \to (\chi \to \psi)$. The instance of A2

$$
(\varphi \to (\chi \to \psi)) \to ((\varphi \to \chi) \to (\varphi \to \psi))
$$

and two applications of modus ponens give $\Gamma \vdash \varphi \to \psi$.

The axioms A1 and A2 are exactly what this proof needs, and that explains their form.

</details>

### Exercise 10

Prove that weakening is admissible in cut-free G3: if $\Gamma \Rightarrow \Delta$ has a derivation of height $h$, then for any multisets $\Gamma'$ and $\Delta'$, the sequent $\Gamma, \Gamma' \Rightarrow \Delta, \Delta'$ has a derivation of height at most $h$.

<details><summary>Solution</summary>

Use induction on $h$.

If the sequent is an axiom, it contains a variable on both sides or $\bot$ on the left, and the enlarged sequent contains the same formulas, so it is also an axiom.

Otherwise, the last rule has principal formula $\pi$, and its premises have the same side formulas as the conclusion plus the active formulas. Add $\Gamma'$ and $\Delta'$ to each premise. By the induction hypothesis each enlarged premise has a derivation of height at most $h - 1$. Applying the same rule gives the enlarged conclusion, because the rules place no restriction on side formulas. The height is at most $h$.

</details>

### Exercise 11

Show that RAA can be replaced by the axiom schema $\varphi \lor \neg\varphi$. Use only the intuitionistic rules and this schema to derive RAA.

<details><summary>Solution</summary>

Assume $\Gamma, \neg\varphi \vdash \bot$, and derive $\Gamma \vdash \varphi$ as follows. By the schema, $\Gamma \vdash \varphi \lor \neg\varphi$. Apply $\lor$E with two cases. In the first case, $\Gamma, \varphi \vdash \varphi$ by Ax. In the second case, $\Gamma, \neg\varphi \vdash \bot$ by assumption, so $\Gamma, \neg\varphi \vdash \varphi$ by $\bot$E. Hence $\Gamma \vdash \varphi$.

The other direction is the derivation of excluded middle in the lesson, which uses the same pattern with $x_1$ replaced by any $\varphi$. So the two are interchangeable over the intuitionistic rules.

</details>

### Exercise 12

Prove the subformula property for cut-free G3, and explain why it fails with Cut.

<details><summary>Solution</summary>

Inspect the rules: in each rule of G3, every formula in a premise is either a side formula, which also appears in the conclusion, or an immediate subformula of the principal formula of the conclusion. So every formula in a premise is a subformula of a formula in the conclusion.

By induction on the distance from the root of a derivation, every formula in the derivation is a subformula of some formula in the final sequent, since "subformula of" is transitive.

With Cut, the formula $\varphi$ appears in the premises and may not occur in the conclusion, so the argument fails at this rule. For example, in deriving $x_1 \Rightarrow x_1$ you may cut on the unrelated formula $x_2 \lor \neg x_2$.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State all the rules of natural deduction, the rules of G3 and the resolution rule.
- Derive excluded middle, Peirce's law and both directions of De Morgan's laws in natural deduction.
- Prove a valid sequent by search, and read off a countermodel from an open leaf of an unprovable sequent.
- Convert a small entailment to clauses and refute it by resolution.
- State what cut is, what cut elimination says, and why the subformula property matters for search.
- Compare the three systems on direction of reasoning, input format and proof size, and state the separation between resolution and Frege systems.

## Materials

- Huth and Ryan, Logic in Computer Science, 2nd edition. Read the part of the propositional logic chapter on natural deduction for many worked box-style proofs and exercises. The line format in this topic follows the same idea.
- Gallier, Logic for Computer Science, 2nd edition. Read the treatment of Gentzen systems and cut elimination for a rigorous development of sequent calculus, and the treatment of propositional resolution for its completeness.
- [Harrison, Handbook of Practical Logic and Automated Reasoning.](https://www.cl.cam.ac.uk/~jrh13/atp/) Read the propositional logic material on the Davis-Putnam procedure and the first-order material on resolution and tableaux, to see these systems used as algorithms.
- Cook and Reckhow, The Relative Efficiency of Propositional Proof Systems, Journal of Symbolic Logic, 1979. Read it for the general definition of a proof system and for polynomial simulation.
