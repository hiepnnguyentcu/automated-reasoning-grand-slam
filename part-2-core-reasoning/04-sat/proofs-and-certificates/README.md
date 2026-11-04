# Proofs and Certificates

Part 2, Chapter 4: SAT.

## Objective

Produce and check a DRAT proof for a small unsatisfiable formula by hand.

## Why this matters

A satisfiable answer is easy to trust, since you can evaluate the formula on the model. An unsatisfiable answer needs evidence, and solvers are large programs with subtle bugs. Clausal proofs let a small, separately checked tool confirm the answer, and this is central whenever a solver result supports a verification or security claim. You will emit such proofs in [the Chapter 9 proof output topic](../../../part-3-building-the-engines/09-sat-solver/proof-output/). The same ideas of certificates recur in [model checkers](../../../part-3-building-the-engines/11-model-checker/certificates/) and in SMT.

## Prerequisites

- [CDCL](../cdcl/)
- [Preprocessing and Inprocessing](../preprocessing-and-inprocessing/)
- [Resolution and DPLL](../resolution-and-dpll/)

## Lesson

### Certificates for each answer

For a SAT answer, the certificate is a model, and checking it takes time linear in the formula. Note that the model must be for the original formula, so a solver that simplified the input must first reconstruct it.

For an UNSAT answer, the certificate is a refutation in some proof system. A resolution proof lists each clause with its parents, and it is simple to check. The problem is size and effort, since a solver would have to record every resolution step, including those in clause minimization. Clausal proofs avoid this by listing only the learned clauses, and they leave the checker to rediscover how each one follows.

### Reverse unit propagation

Let $F$ be a clause set and $C = (l_1 \lor \dots \lor l_k)$ a clause. Write $\neg C$ for the assignment $\neg l_1, \dots, \neg l_k$. Clause $C$ has the reverse unit propagation property (RUP) with respect to $F$ if unit propagation on $F$ under $\neg C$ reaches a conflict. The term asymmetric tautology (AT) describes the same property.

Theorem 1. If $C$ has RUP with respect to $F$, then $F \models C$.

Proof. Suppose that a model of $F$ falsifies $C$. Then it agrees with $\neg C$. Unit propagation is sound, so the model satisfies every derived literal. But propagation reaches a falsified clause of $F$, which contradicts the model satisfying $F$. $\square$

The converse fails. A clause can be implied by $F$ without having RUP, as Exercise 3 shows.

Theorem 2. Every clause learned by first-UIP analysis has RUP with respect to the clause database at that moment. This holds also after clause minimization and after dropping level-0 literals.

Proof. Let $C$ be the first-UIP clause, and let $W$ be the literals that $C$ negates. By the definition of the cut, each node on the conflict side has all its antecedents in $W$, in lower levels that are also in $W$, or on the conflict side. So under $\neg C$, which makes all of $W$ true, propagation can assign the conflict-side literals in trail order, and the falsified clause is reached. Propagation may find a conflict sooner, which is also acceptable. If a literal of level 0 was dropped, propagation at the start rederives its negation, since it was propagated without decisions. If a literal $\neg r$ was removed by minimization, then the removed literal $r$ is implied by propagation from the remaining ones, so the argument still applies. $\square$

Goldberg and Novikov (2003) proposed checking solver output in this way, which is the origin of checking clauses with propagation in place of explicit resolution chains.

### Resolution asymmetric tautology

Let $C$ be a clause and $p \in C$ a literal, called the pivot. Clause $C$ has the resolution asymmetric tautology property (RAT) on $p$ with respect to $F$ if, for every clause $D \in F$ with $\neg p \in D$, the resolvent $C \lor (D \setminus \{\neg p\})$ has RUP with respect to $F$ or is a tautology. If no clause contains $\neg p$, the condition holds vacuously.

Theorem 3. If $C$ has RAT on $p$ with respect to $F$, then $F$ and $F \land C$ are satisfiability-equivalent. A model $\tau$ of $F$ that falsifies $C$ turns into a model of $F \land C$ by making $p$ true.

Proof. If $F \land C$ is satisfiable, so is $F$. Conversely, let $\tau$ satisfy $F$ and falsify $C$, and let $\tau'$ be $\tau$ with $p$ true. Then $C$ is satisfied by $\tau'$. Only clauses with $\neg p$ might become false. Take such a clause $D$, and write $D = \neg p \lor D'$. The resolvent $C \lor D'$ is either a tautology or has RUP.

If it has RUP, then $F \models C \lor D'$ by Theorem 1, so $\tau$ satisfies it. Since $\tau$ falsifies $C$, it satisfies some literal of $D'$.

If it is a tautology, then since $C$ and $D$ are not themselves tautologies, there is a literal $k \in C$ with $\neg k \in D'$. Since $\tau$ falsifies $C$, $\neg k$ is true under $\tau$.

In both cases a literal of $D'$ is true under $\tau$. That literal is not on the variable of $p$, assuming $D$ is not a tautology, so it remains true under $\tau'$, and $D$ is satisfied. $\square$

RAT generalizes RUP, in the sense that a clause with RUP and a nonempty set of literals has RAT on any of its literals, since a resolvent contains $C$ and thus also has RUP. It also generalizes blocked clauses, for which every resolvent is a tautology. RAT-based additions are not necessarily implied, so a proof can introduce new variables. This allows RAT proofs to express extended resolution, which is believed to be much stronger than resolution, and to justify the common inprocessing techniques in one format. Järvisalo, Heule and Biere (2012) use this property as the basis of their inprocessing rules.

### DRUP and DRAT proofs

A DRAT proof is a sequence of clause additions and deletions. The checker maintains the current clause set, initially $F$.

```
FORWARD-CHECK(F, proof):
    S := F
    for each step in proof:
        if step deletes clause C:
            remove C from S
        else step adds clause C:
            if C has RUP with respect to S: add C to S
            else if C has RAT on its first literal with respect to S: add C to S
            else: reject
        if C is the empty clause: accept
    reject
```

DRUP is the same format with RUP as the only addition rule. The pivot is the first literal of the clause as written, so the literal order in the file matters. Heule, Hunt and Wetzler (2013) introduced DRUP-trim, and Wetzler, Heule and Hunt (2014) extended the approach to DRAT.

Deletion serves two purposes. It lets the checker keep up with a solver that deleted clauses, so that propagation stays fast. For RAT steps, it also changes the check, because fewer clauses contain $\neg p$.

Theorem 4. If a DRAT proof of $F$ reaches the empty clause under FORWARD-CHECK, then $F$ is unsatisfiable.

Proof. Show by induction that if $F$ is satisfiable, then the current clause set $S$ is satisfiable at each step. Initially $S = F$. A deletion keeps a satisfiable set satisfiable. An addition passes by RUP or RAT, and Theorem 1 or 3 keeps $S$ satisfiable. But the empty clause cannot be in a satisfiable set. $\square$

This proof shows also why DRAT certifies only unsatisfiability. Deletion can make an unsatisfiable set satisfiable, so reaching a state without a conflict says nothing about $F$. So a SAT answer requires a model.

### The file format

The DRAT text format uses DIMACS integers. Each line lists a clause terminated by 0, and a deletion begins with `d`. For the formula of Example 1 below, the input and proof files are the following.

```
c input formula
p cnf 4 8
1 2 -3 0
-1 -2 3 0
2 3 -4 0
-2 -3 4 0
1 3 4 0
-1 -3 -4 0
-1 2 4 0
1 -2 -4 0
```

```
c proof
1 2 0
1 0
2 0
0
```

Solvers usually write a compact binary form of the same content.

### Backward checking and trimming

A forward check tests every lemma, but many lemmas are never used to reach the conflict. A backward check first adds all lemmas without checking them, up to the empty clause. It then walks the proof in reverse and checks only marked lemmas. When checking a clause, it marks the clauses that the propagation actually needed to reach the conflict.

```
BACKWARD-CHECK(F, proof):
    forward pass: apply additions and deletions, without checks, until a conflict by propagation
    mark the clauses involved in that conflict
    for each lemma C in reverse order:
        remove C from the current set
        if C is marked:
            check C by RUP or RAT, and mark the clauses used in the check
    accept
```

The marked input clauses form an unsatisfiable core, and the marked lemmas form a trimmed proof. Heule, Hunt and Wetzler also introduced core-first unit propagation, which prefers already marked clauses during propagation. This tends to keep the marked set small. For a RAT check, the checker must also consider every clause containing the negated pivot, and those clauses are marked as needed, so the order of deletions must be respected.

There is one known discrepancy between theory and practice. In its default mode, DRAT-trim ignores deletions of unit clauses, since a solver deleting a satisfied unit clause does not intend to undo its propagation. Rebola-Pardo and Biere (2018) called the two readings the specified and the operational flavors of DRAT. A proof that relies on such a deletion may pass in one reading and fail in the other. When you compare checkers, check which reading each one uses.

### Verified checkers and hints

A checker is itself a program, so it can have bugs. To reduce trust, the proof pipeline usually has two stages. An efficient unverified tool such as DRAT-trim reads the DRAT proof and produces an annotated form. A small verified checker then checks this form.

The annotated format LRAT (Cruz-Filipe et al., 2017) lists, for each lemma, the clause identifiers in the exact order in which they become unit and then conflict. Checking is then a simple linear scan with no search for unit clauses. Each line has the form `id literals 0 hints 0`, and for Example 1 below the proof is:

```
9  1 2 0  1 3 5 0
10 1 0    9 8 4 5 0
11 2 0    9 7 3 6 0
12 0      10 11 2 4 6 0
```

The first line says that clause 9 is $(x_1 \lor x_2)$, and that under its negation the clauses 1 and 3 become unit in that order and clause 5 is falsified. Other related work includes FRAT (Baek, Carneiro and Heule, 2021), which lets the solver leave hints when it is convenient to do so, and the verified checker cake_lpr (Tan, Heule and Myreen, 2021).

## Worked examples

A small RUP and RAT checker written for this topic confirmed every proof below, and it also checked the LRAT hints above by hand-written propagation order. DRAT-trim itself was not run on these proofs, and you should run it when you reach [the Chapter 9 proof output topic](../../../part-3-building-the-engines/09-sat-solver/proof-output/).

### Example 1: a complete DRUP proof, checked by hand

Rivest's unsatisfiable formula over four variables has eight clauses of three literals.

```
C1 = (x1 ∨ x2 ∨ ¬x3)      C2 = (¬x1 ∨ ¬x2 ∨ x3)
C3 = (x2 ∨ x3 ∨ ¬x4)      C4 = (¬x2 ∨ ¬x3 ∨ x4)
C5 = (x1 ∨ x3 ∨ x4)       C6 = (¬x1 ∨ ¬x3 ∨ ¬x4)
C7 = (¬x1 ∨ x2 ∨ x4)      C8 = (x1 ∨ ¬x2 ∨ ¬x4)
```

The proof is the sequence of lemmas $(x_1 \lor x_2)$, $(x_1)$, $(x_2)$, $\bot$. Each step adds a clause only after the check succeeds.

```
Add L1 = (x1 ∨ x2). Assume ¬x1, ¬x2.
    C1 gives ¬x3.
    C3 gives ¬x4.
    C5 is falsified. RUP holds.

Add L2 = (x1). Assume ¬x1.
    L1 gives x2.
    C8 gives ¬x4.
    C4 gives ¬x3.
    C5 is falsified. RUP holds.

Add L3 = (x2). Assume ¬x2.
    L1 gives x1.
    C7 gives x4.
    C3 gives x3.
    C6 is falsified. RUP holds.

Add ⊥. Assume nothing.
    L2 gives x1, and L3 gives x2.
    C2 gives x3.
    C4 gives x4.
    C6 is falsified. RUP holds.
```

So the formula is unsatisfiable. Enumeration of the 16 assignments confirmed this.

### Example 2: a proof from a CDCL run

The UNSAT run in Example 2 of [CDCL](../cdcl/) learned $C_{14}, C_{15}, C_{16}, C_{17}$. Its DRUP proof is these clauses followed by the empty clause. Here is its check.

```
Add (x5 ∨ x1). Assume ¬x5, ¬x1.
    C4 gives x4.  C5 gives ¬x6.  C8 is falsified.

Add (x1). Assume ¬x1.
    (x5 ∨ x1) gives x5.  C13 gives x3.  C3 gives x2.  C6 gives ¬x4.  C11 is falsified.

Add (¬x4 ∨ x5). Assume x4, ¬x5.
    C5 gives ¬x6.  C8 is falsified.

Add (x2). Assume ¬x2.
    (x1) gives x1.  C12 gives x4.  (¬x4 ∨ x5) gives x5.  C3 gives ¬x3.  C7 is falsified.

Add ⊥.
    (x1) gives x1.  (x2) gives x2.  C1 gives ¬x5.  C2 gives ¬x3.  C5 gives ¬x6.
    C8 gives ¬x4.  C9 is falsified.
```

The propagations correspond to the implication graphs in that run, as Theorem 2 predicts. Note that the check of $(x_2)$ uses the unit $(x_1)$, which is why dropping the level-0 literal $\neg x_1$ from the learned clause was acceptable. A resolution proof would have to record that step.

### Example 3: RAT with and without a valid pivot

Definitions. Let $F = (x_1 \lor x_2) \land (\neg x_1 \lor x_3)$, and add the definition $x_4 \leftrightarrow x_1 \land x_2$ for a fresh variable.

```
Add (x4 ∨ ¬x1 ∨ ¬x2), pivot x4.
    No clause contains ¬x4, so RAT holds vacuously.
Add (¬x4 ∨ x1), pivot ¬x4.
    Clauses containing x4: (x4 ∨ ¬x1 ∨ ¬x2).
    Resolvent: (x1 ∨ ¬x1 ∨ ¬x2), a tautology. RAT holds.
Add (¬x4 ∨ x2), pivot ¬x4.
    Clauses containing x4: (x4 ∨ ¬x1 ∨ ¬x2).
    Resolvent: (x2 ∨ ¬x1 ∨ ¬x2), a tautology. RAT holds.
```

These clauses are not implied by $F$, since $F$ does not mention $x_4$. For instance, the first clause has no RUP. Under $\neg x_4, x_1, x_2$ propagation gives only $x_3$, with no conflict.

Blocked clauses. In Example 3 of [Preprocessing and Inprocessing](../preprocessing-and-inprocessing/), adding $(x_1 \lor x_2)$ to $C_2 \land C_3 \land C_4$ with pivot $x_1$ has resolvents that are all tautologies, so RAT holds. The clause is not implied, because the all-false assignment is a model of the three clauses and falsifies it.

The pivot matters. Let $F = (x_1 \lor x_2) \land (\neg x_1 \lor \neg x_2)$.

```
Add (x3 ∨ x1), pivot x3: no clause contains ¬x3, so RAT holds.
Add (x1 ∨ x3), pivot x1:
    Clause containing ¬x1: (¬x1 ∨ ¬x2).
    Resolvent: (x1 ∨ x3 ∨ ¬x2), which is not a tautology.
    Assume ¬x1, ¬x3, x2: (x1 ∨ x2) and (¬x1 ∨ ¬x2) are satisfied, so no conflict arises.
    The RAT check fails.
```

The same clause passes when written in one order and fails in the other.

### Example 4: backward checking and trimming

Use Rivest's formula with an extended proof containing unnecessary lemmas: $(x_1 \lor x_2)$, $(x_1 \lor x_3)$, $(x_1)$, $(x_2)$, $(x_3)$, $\bot$. All pass a forward check.

```
Conflict at the end: (x1) and (x2) give x1, x2.  C2 gives x3.  C4 gives x4.  C6 is falsified.
Marked: (x1), (x2), C2, C4, C6.

(x3): not marked, so skip it.
(x2): check. Under ¬x2, (x1 ∨ x2) gives x1, C7 gives x4, C3 gives x3, and C6 is falsified.
      Mark (x1 ∨ x2), C7, C3.
(x1): check. Under ¬x1, (x1 ∨ x2) gives x2, C8 gives ¬x4, C4 gives ¬x3, and C5 is falsified.
      Mark C8, C5.
(x1 ∨ x3): not marked, so skip it.
(x1 ∨ x2): check. Under ¬x1, ¬x2, C1 gives ¬x3, C3 gives ¬x4, and C5 is falsified.
      Mark C1.
```

The trimmed proof is $(x_1 \lor x_2)$, $(x_1)$, $(x_2)$, $\bot$, and the core is all eight clauses, which is correct since this formula is minimally unsatisfiable. The marked set could differ under a different choice of unit clause. Core-first propagation would prefer the marked unit $(x_1)$ in the check of $(x_2)$, which could make $(x_1 \lor x_2)$ needless for that lemma, although the check of $(x_1)$ still needs it.

## Common mistakes

- Treating a DRUP check as a resolution proof check. The checker repeats propagation, so it needs no parent clauses in the file, and its cost is correspondingly higher.
- Assuming that every implied clause has RUP. RUP is sufficient for implication, and it is not necessary.
- Assuming that a RAT clause is implied. RAT preserves satisfiability only, and adding a RAT clause can remove models.
- Writing a RAT clause with the wrong first literal. The checker uses the first literal as the pivot.
- Trying to use DRAT to certify a SAT answer. Deletion means a proof step says nothing about the satisfiability of the input, so a model is the certificate.
- Forgetting to log deletions. The proof still checks, but the checker slows down and may time out. For RAT steps the check may even fail, since more clauses contain the negated pivot.
- Omitting preprocessing from the proof. If a solver eliminates variables before search and logs only the learned clauses, a learned clause may no longer have RUP with respect to the input.
- Deleting a clause that is a reason at level 0 and expecting all checkers to undo its propagation. Default DRAT-trim ignores unit deletions, and specified DRAT does not.
- Thinking that a verified checker removes all trust. You still trust the formula given to the checker, including any encoding from the original problem, as well as the specification of the proof format and the compiler or kernel under the verified checker.
- Calling RUP checks cheap. Checking can take as long as solving, and sometimes longer, which is why backward mode and hints exist.

## Exercises

### Exercise 1

Define RUP and RAT, and state what each preserves.

<details><summary>Solution</summary>

$C$ has RUP with respect to $F$ if unit propagation on $F$ under the negation of $C$ reaches a conflict. Then $F \models C$, so adding $C$ preserves equivalence.

$C$ has RAT on $p \in C$ with respect to $F$ if each resolvent of $C$ with a clause containing $\neg p$ is a tautology or has RUP with respect to $F$. Adding $C$ preserves satisfiability, and in general it does not preserve equivalence.

</details>

### Exercise 2

Check the proof $(x_2), \bot$ for $F = (x_1 \lor x_2) \land (\neg x_1 \lor x_2) \land (x_1 \lor \neg x_2) \land (\neg x_1 \lor \neg x_2)$.

<details><summary>Solution</summary>

```
Add (x2). Assume ¬x2.
    (x1 ∨ x2) gives x1.  (¬x1 ∨ x2) is falsified. RUP holds.
Add ⊥.
    (x2) gives x2.  (x1 ∨ ¬x2) gives x1.  (¬x1 ∨ ¬x2) is falsified. RUP holds.
```

</details>

### Exercise 3

Let $F = (x_1 \lor x_2 \lor x_3) \land (x_1 \lor x_2 \lor \neg x_3) \land (\neg x_1 \lor x_2 \lor x_3) \land (\neg x_1 \lor x_2 \lor \neg x_3)$. Show that $F \models (x_2)$ and that $(x_2)$ does not have RUP. Then give a DRUP derivation of $(x_2)$.

<details><summary>Solution</summary>

If $x_2$ is false, the four clauses say all four combinations of $x_1, x_3$ are excluded, so $F$ is false. So $F \models (x_2)$.

Assume $\neg x_2$. Each clause has two open literals, so propagation does nothing, and there is no conflict. So $(x_2)$ has no RUP.

Derivation:

```
Add (x1 ∨ x2). Assume ¬x1, ¬x2.
    (x1 ∨ x2 ∨ x3) gives x3.  (x1 ∨ x2 ∨ ¬x3) is falsified.
Add (x2). Assume ¬x2.
    (x1 ∨ x2) gives x1.  (¬x1 ∨ x2 ∨ x3) gives x3.  (¬x1 ∨ x2 ∨ ¬x3) is falsified.
```

</details>

### Exercise 4

Exercise 6 of [CDCL](../cdcl/) learned $(x_2 \lor \neg x_6)$, $(x_6 \lor x_1)$, $(\neg x_6)$ and $(x_3)$. Write the DRUP proof, and check the last lemma and the empty clause.

<details><summary>Solution</summary>

The proof is $(x_2 \lor \neg x_6)$, $(x_6 \lor x_1)$, $(\neg x_6)$, $(x_3)$, $\bot$.

```
Add (x3). Assume ¬x3.
    (¬x6) gives ¬x6.  (x6 ∨ x1) gives x1.
    C1 (x3 ∨ x4 ∨ x6) gives x4.
    C2 (¬x1 ∨ x3 ∨ ¬x4) is falsified. RUP holds.

Add ⊥.
    (¬x6) gives ¬x6.  (x6 ∨ x1) gives x1.  (x3) gives x3.
    C7 (¬x3 ∨ x5 ∨ x6) gives x5.
    C8 (¬x3 ∨ ¬x5 ∨ x6) is falsified. RUP holds.
```

</details>

### Exercise 5

Let $F = (x_1 \lor x_2) \land (\neg x_1 \lor \neg x_2) \land (\neg x_1 \lor x_3) \land (x_2 \lor \neg x_3)$. Test whether $(x_1 \lor \neg x_3)$ has RAT on $x_1$. Does it have RAT on $\neg x_3$?

<details><summary>Solution</summary>

On $x_1$: the clauses with $\neg x_1$ are $(\neg x_1 \lor \neg x_2)$ and $(\neg x_1 \lor x_3)$. The second gives a tautology. The first gives $(x_1 \lor \neg x_3 \lor \neg x_2)$. Assume $\neg x_1, x_3, x_2$. Then $(x_1 \lor x_2)$ is satisfied, $(\neg x_1 \lor \neg x_2)$ is satisfied, $(\neg x_1 \lor x_3)$ is satisfied, and $(x_2 \lor \neg x_3)$ is satisfied. No conflict arises. So RAT fails on $x_1$.

On $\neg x_3$: the only clause with $x_3$ is $(\neg x_1 \lor x_3)$. The resolvent is $(x_1 \lor \neg x_3 \lor \neg x_1)$, a tautology. So RAT holds on $\neg x_3$, and the clause must be written with $\neg x_3$ first.

</details>

### Exercise 6

Let $F$ be the pigeonhole formula with pigeons 1, 2, 3 and holes 1, 2, using $x_1, x_2$ for pigeon 1, $x_3, x_4$ for pigeon 2, and $x_5, x_6$ for pigeon 3. Following Cook's short extended resolution proof, define $x_7 \leftrightarrow x_1 \lor (x_2 \land x_5)$ and $x_8 \leftrightarrow x_3 \lor (x_4 \land x_5)$. These variables say where pigeons 1 and 2 are after pigeon 3 is taken out of hole 1. Give a proof that adds the definitions and derives $\bot$, and explain each step.

<details><summary>Solution</summary>

Definitions for $x_7$, each with the literal on $x_7$ first:

```
(x7 ∨ ¬x1)           no clause has ¬x7, so RAT holds on x7
(x7 ∨ ¬x2 ∨ ¬x5)     no clause has ¬x7, so RAT holds on x7
(¬x7 ∨ x1 ∨ x2)      resolvents with the two clauses above are tautologies
(¬x7 ∨ x1 ∨ x5)      resolvents with the two clauses above are tautologies
```

The clauses for $x_8$ are similar, with $x_3, x_4$ in place of $x_1, x_2$.

Lemmas:

```
(x7): assume ¬x7. Then ¬x1, then x2, then ¬x4 from (¬x2 ∨ ¬x4), x3 from (x3 ∨ x4),
      ¬x5 from (¬x3 ∨ ¬x5), x6 from (x5 ∨ x6), and (¬x2 ∨ ¬x6) is falsified.
(x8): assume ¬x8. Then ¬x3, then x4, then ¬x2, x1, ¬x5, x6, and (¬x4 ∨ ¬x6) is falsified.
(¬x1 ∨ ¬x8): assume x1, x8. Then ¬x3, x4, ¬x5, x6, ¬x2, and (¬x4 ∨ ¬x6) is falsified.
(¬x7 ∨ ¬x8): assume x7, x8. Then ¬x1, x2, ¬x4, x3, ¬x5, x6, and (¬x2 ∨ ¬x6) is falsified.
⊥: x7 and x8 are units, so (¬x7 ∨ ¬x8) is falsified.
```

The last three lemmas say that the new pigeons 1 and 2 cannot both go into hole 1. The checker accepted all 13 steps.

For this very small formula the checker also found RUP for the definition clauses, since $F$ is so constrained. The justification by RAT is the one that scales. For larger pigeonhole formulas, these definitions are what give a polynomial-size proof, whereas resolution needs exponential size. Proofs without new variables at this size are also short: $(\neg x_2), \bot$ is a valid DRUP proof here.

</details>

### Exercise 7

Show how to log one elimination step of BVE in DRAT, using Example 2 of [Resolution and DPLL](../resolution-and-dpll/), where $x_4$ is eliminated. Explain why the steps pass.

<details><summary>Solution</summary>

Eliminating $x_4$ removes $(\neg x_3 \lor x_4)$ and $(\neg x_2 \lor \neg x_4)$ and adds $(\neg x_2 \lor \neg x_3)$.

```
Add (¬x2 ∨ ¬x3)
d   (¬x3 ∨ x4)
d   (¬x2 ∨ ¬x4)
```

The addition has RUP. Assume $x_2, x_3$. Then $(\neg x_3 \lor x_4)$ gives $x_4$, and $(\neg x_2 \lor \neg x_4)$ is falsified. Every resolvent has RUP in this way. Deletions require no justification. The order matters: resolvents must be added before their parents are deleted.

</details>

### Exercise 8

Prove that the three clauses of the definition $x \leftrightarrow a \land b$, for a fresh variable $x$, can be added by RAT in the order given in Example 3, and that this preserves satisfiability and all models of $F$ up to the choice of $x$.

<details><summary>Solution</summary>

The first clause $(x \lor \neg a \lor \neg b)$ has pivot $x$, and $\neg x$ occurs nowhere because $x$ is fresh, so RAT holds vacuously. The clause $(\neg x \lor a)$ has pivot $\neg x$. The only clause containing $x$ is the first one, and the resolvent is $(a \lor \neg a \lor \neg b)$, a tautology. The clause $(\neg x \lor b)$ is the same, with resolvent $(b \lor \neg a \lor \neg b)$. Note that when checking the third clause, the second clause does not contain $x$, so it is not considered.

By Theorem 3 satisfiability is preserved. For models: given any model $\tau$ of $F$, set $x$ to the value of $a \land b$ under $\tau$. All three clauses hold and $F$ is unaffected, since it does not mention $x$. Conversely any model of the extended formula restricts to a model of $F$. So the models correspond one-to-one, and this is why definitions are safe.

</details>

### Exercise 9

Show by example that deletion breaks a claim of satisfiability, and explain why it does not break Theorem 4.

<details><summary>Solution</summary>

Take $F = (x_1) \land (\neg x_1)$, which is unsatisfiable. Delete $(\neg x_1)$. The set $(x_1)$ is satisfiable, and a checker would see no conflict. So reaching a satisfiable state says nothing about $F$.

Theorem 4 argues in one direction only. If $F$ is satisfiable, every later set is satisfiable, so $\bot$ is never reached. Deleting clauses from a satisfiable set keeps it satisfiable, so the argument is unaffected. The contrapositive gives the conclusion: reaching $\bot$ means $F$ is unsatisfiable.

</details>

### Exercise 10

Design a pipeline to trust the claim that a piece of hardware meets a safety property, based on a SAT solver. Say what each stage checks, and what you must still trust.

<details><summary>Solution</summary>

The stages are as follows.

1. Encode the property and the design as a CNF, with a separate review or a certified encoding tool if possible.
2. Run the solver with proof logging, and write a DRAT proof.
3. Run DRAT-trim in backward mode to check the proof and trim it, and have it write LRAT.
4. Run a verified LRAT checker on the CNF and LRAT file.
5. If the solver returns SAT, map the model back to a counterexample, and simulate it on the design, independently of the solver.

The checker's result lets you stop trusting the solver and DRAT-trim. You still trust the following: the encoding is correct and the CNF given to the checker is the one that was encoded, the safety property expresses what you mean, the design model matches the hardware, and the verified checker's specification and the tools under it (its logic, kernel and compiler) are sound. A bound in bounded model checking also limits the claim, unless the method is complete.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Check a DRUP proof by hand on a small formula, showing each propagation.
- Produce a DRUP proof from the learned clauses of a CDCL run.
- Test RAT on a given pivot, including the case of a tautological resolvent.
- Prove Theorems 1, 3 and 4.
- Run a backward check and read off a trimmed proof and a core.
- Write a proof in the DRAT text format, including a deletion.
- Explain what LRAT hints add and what a verified checker leaves you trusting.

## Materials

- Heule, Hunt and Wetzler, Trimming while checking clausal proofs, FMCAD 2013. Read it for backward checking, core-first propagation and trimming with DRUP.
- [DRAT-trim proof checker.](https://github.com/marijnheule/drat-trim) Use it to run the examples in this topic and to read the format description.
- Wetzler, Heule and Hunt, DRAT-trim: Efficient Checking and Trimming Using Expressive Clausal Proofs, SAT 2014. Read it for the extension to RAT.
- Goldberg and Novikov, Verification of Proofs of Unsatisfiability for CNF Formulas, DATE 2003. Read it for the origin of checking conflict clauses by propagation.
- Järvisalo, Heule and Biere, Inprocessing Rules, IJCAR 2012. Read it for RAT as a redundancy property.
- Rebola-Pardo and Biere, Two Flavors of DRAT, Pragmatics of SAT 2018. Read it for the treatment of unit deletions.
- Cruz-Filipe, Heule, Hunt, Kaufmann and Schneider-Kamp, Efficient Certified RAT Verification, CADE 2017. Read it for LRAT and its verified checker.
- Baek, Carneiro and Heule, A Flexible Proof Format for SAT Solver-Elaborator Communication, TACAS 2021. Read it for FRAT.
- Tan, Heule and Myreen, cake_lpr: Verified Propagation Redundancy Checking in CakeML, TACAS 2021. Read it for a verified checker in practice.
