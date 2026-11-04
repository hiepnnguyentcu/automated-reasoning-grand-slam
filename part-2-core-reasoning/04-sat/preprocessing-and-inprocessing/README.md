# Preprocessing and Inprocessing

Part 2, Chapter 4: SAT.

## Objective

Apply variable elimination, subsumption and blocked clause elimination and state what they preserve.

## Why this matters

Industrial CNF is usually machine-generated, with many definitions and redundant clauses, and rewriting it can make it far easier. Simplification is now a standard part of competitive solvers, and it returns in [the Chapter 9 inprocessing topic](../../../part-3-building-the-engines/09-sat-solver/inprocessing/). The main practical danger is that many of these techniques change the set of models, so a careless pipeline returns wrong models, breaks incremental use, or breaks [model counting](../qbf-and-model-counting/). The formal treatment here also supplies the redundancy notion RAT used in [proofs](../proofs-and-certificates/).

## Prerequisites

- [Resolution and DPLL](../resolution-and-dpll/)
- [CDCL](../cdcl/)
- [Encodings](../encodings/)

## Lesson

### Levels of preservation

A simplification maps a formula $F$ to $F'$. It may preserve one of the following.

- Equivalence: $F$ and $F'$ have the same models over the same variables.
- Projected models: the models of $F'$ are exactly the restrictions of the models of $F$ to the remaining variables.
- Satisfiability: $F'$ is satisfiable if and only if $F$ is, usually with a reconstruction procedure that turns a model of $F'$ into one of $F$.

| Technique | What it preserves | Reconstruction needed |
|---|---|---|
| Subsumption | It preserves equivalence. | None is needed. |
| Self-subsuming resolution | It preserves equivalence. | None is needed. |
| Failed literal probing | It preserves equivalence. | None is needed. |
| Vivification | It preserves equivalence. | None is needed. |
| Bounded variable elimination | It preserves projected models. | Eliminated variables need values. |
| Equivalent literal substitution | It preserves projected models. | Substituted variables need values. |
| Pure literal elimination | It preserves satisfiability. | The pure variable needs its value. |
| Blocked clause elimination | It preserves satisfiability. | Some variables may need flipping. |

None of the last four preserves the number of models in general.

### Subsumption

A clause $C$ subsumes a clause $D$ if $C \subseteq D$. Every model of $C$ is then a model of $D$, so removing $D$ preserves equivalence.

Learned clauses and resolvents often subsume existing clauses. Detection uses one-watch or signature schemes. Eén and Biere (2005) use a 64-bit signature per clause, in which each literal sets a hashed bit, so that most non-subset pairs are excluded by a single bitwise test.

### Self-subsuming resolution

If $C \lor l$ and $D \lor \neg l$ are clauses with $C \subseteq D$, then their resolvent is $C \lor D = D$, which subsumes $D \lor \neg l$. So the clause $D \lor \neg l$ can be replaced by $D$. This is called self-subsuming resolution or strengthening.

Theorem 1. Replacing $D \lor \neg l$ by $D$ under this condition preserves equivalence.

Proof. The clause $D$ is a resolvent of the two clauses, so it is implied by them. Also $D$ implies $D \lor \neg l$. So adding $D$ preserves equivalence, and then $D \lor \neg l$ is subsumed. $\square$

### Bounded variable elimination

Bounded variable elimination (BVE) applies the Davis-Putnam elimination of [Resolution and DPLL](../resolution-and-dpll/) to a chosen variable $x$, when the result is not larger than the original. Replace $F_x \cup F_{\neg x}$ by the non-tautological resolvents, as long as the count of clauses does not grow. This bound is what prevents the blow-up that ended the original Davis-Putnam procedure as a practical method. Solvers order candidates by a cost such as $|F_x| \cdot |F_{\neg x}|$, and they may allow a small increase in later rounds.

Theorem 2. For $x$ occurring in $F$, the models of $\mathrm{DP}_x(F)$ are exactly the restrictions of the models of $F$ to the other variables. In other words, $\mathrm{DP}_x(F) \equiv \exists x. F$.

Proof. This restates the two directions of the elimination theorem in [Resolution and DPLL](../resolution-and-dpll/). A model of $F$ satisfies all resolvents, and the resolvents and $F_0$ do not mention $x$. A model of the result extends to $F$ by the choice of $x$ given in that proof. $\square$

Reconstruction stores the removed clauses of $x$, say on a stack. To give $x$ a value, process eliminations in reverse. Set $x$ false, and if any clause in $F_x$ is falsified then set $x$ true. The proof guarantees that this works.

### Gate definitions in elimination

Suppose that $x$ is defined by a gate within $F$. Eén and Biere observed that most resolvents are then redundant. Split the clauses of $x$ into gate clauses $G_x, G_{\neg x}$ and non-gate clauses $N_x, N_{\neg x}$. Then it is enough to add the resolvents of $G_x$ with $N_{\neg x}$ and of $N_x$ with $G_{\neg x}$. The resolvents of two gate clauses are tautologies, and the resolvents of two non-gate clauses are implied by the others.

Why this holds, in outline: a gate definition means that under any assignment to the other variables, exactly one of $G_x$ or $G_{\neg x}$ forces its literal, so $x$ can be substituted by its definition. The substitution produces exactly the gate-with-non-gate resolvents. This is why BVE can remove many Tseitin variables, in effect inverting part of the encoding.

### Blocked clause elimination

Kullmann (1999) introduced blocked clauses. A clause $C$ is blocked on a literal $l \in C$ with respect to $F$ if for every clause $D \in F$ with $\neg l \in D$, the resolvent of $C$ and $D$ on $l$ is a tautology. If no clause contains $\neg l$, then $l$ is pure and $C$ is blocked vacuously.

Theorem 3. If $C$ is blocked on $l$ with respect to $F$ and $C \in F$, then $F$ and $F \setminus \{C\}$ are satisfiable together. Given a model $\tau$ of $F \setminus \{C\}$, either $\tau$ satisfies $C$, or the assignment that flips $l$ to true in $\tau$ satisfies $F$.

Proof. Let $\tau$ satisfy $F \setminus \{C\}$ and falsify $C$. Let $\tau'$ be $\tau$ with $l$ set true. Then $C$ is satisfied. The only clauses that could become false are those containing $\neg l$. Take such a clause $D$. The resolvent of $C$ and $D$ on $l$ is a tautology, so there is a literal $k \in C$ with $k \ne l$ and $\neg k \in D$. Since $\tau$ falsifies $C$, $k$ is false under $\tau$, so $\neg k$ is true, and since $k$ has a different variable from $l$, $\neg k$ is still true under $\tau'$. So $D$ is satisfied. $\square$

Blocked clause elimination (BCE) removes blocked clauses until no more exist. Removing a clause can only make others blocked, so the order does not matter, as Exercise 9 asks you to prove. Järvisalo, Biere and Heule (2010) showed that BCE on a Tseitin encoding achieves the effects of Plaisted-Greenbaum polarity reduction and cone-of-influence reduction, and that BCE removes more when combined with BVE.

Reconstruction: keep a stack of pairs $(l, C)$ in order of removal. Given a model of the final formula, process the stack in reverse order, and if $C$ is not satisfied then set $l$ true. The inprocessing rules paper gives this as a linear-time algorithm that covers a wide range of techniques.

### Other techniques

Failed literal probing. Assign a literal $l$ at a new decision level and propagate. If a conflict arises, then $F \models \neg l$, and the solver adds the unit clause $(\neg l)$. Probing is costly, so solvers limit it. It often uses the roots of the binary implication graph.

Equivalent literal substitution. The binary clauses of $F$ form an implication graph on literals, with $(a \lor b)$ giving edges $\neg a \to b$ and $\neg b \to a$. A strongly connected component is a set of equivalent literals. Replace each by a single representative. If $x$ and $\neg x$ are in one component, $F$ is unsatisfiable.

Vivification. Take a clause $C = (l_1 \lor \dots \lor l_k)$, assign $\neg l_1, \neg l_2, \dots$ one at a time, and propagate on the rest of $F$. If a conflict arises after some prefix, the prefix gives a shorter implied clause. If some literal $l_j$ is implied true after a prefix, then $(l_1 \lor \dots \lor l_{i} \lor l_j)$ is implied and subsumes $C$ when it is shorter. If some $l_j$ is implied false, remove it. Piette, Hamadi and Saïs (2008) described this idea.

### Why inprocessing, and how to keep it sound

Preprocessing runs once, before search. Inprocessing interleaves simplification with search, so it can use learned clauses, and it can simplify what search has revealed. Järvisalo, Heule and Biere (2012) gave a formal account.

A state is $\varphi\,[\rho]\,\sigma$, where $\varphi$ is the set of irredundant clauses, $\rho$ the set of redundant clauses, and $\sigma$ a sequence of pairs $l : C$ for reconstruction. There are four rules.

- LEARN adds a clause $C$ to $\rho$, provided $\varphi \land \rho$ and $\varphi \land \rho \land C$ are satisfiability-equivalent.
- FORGET removes a clause from $\rho$.
- STRENGTHEN moves a clause from $\rho$ to $\varphi$.
- WEAKEN moves a clause $C$ from $\varphi$ to $\rho$, provided $\varphi$ without $C$ and $\varphi$ with $C$ are satisfiability-equivalent, and it records $l : C$ on $\sigma$ when needed.

The invariant is that $\varphi_i$ and $\varphi_i \land \rho_i$ are both satisfiability-equivalent to the input $F$. The preconditions are stated abstractly, and in concrete use they are instantiated with a redundancy property that can be checked in polynomial time, namely RAT, defined in [Proofs and Certificates](../proofs-and-certificates/).

The separation between $\varphi$ and $\rho$ clarifies some subtle points. Clauses in $\rho$ need not be implied by the input $F$. Redundancy checks for elimination need only $\varphi$, and $\rho$ can still be used for propagation. The paper notes that it is sound to keep learned clauses containing an eliminated variable, while the implementations of that time simply removed them. It also describes a buggy version of a technique that a solver shipped for months without visible failures, and shows how the framework identifies the error. This is a useful warning about relying on testing alone.

The paper reports an experiment with Lingeling on application instances from the 2009 and 2011 SAT Competitions, with a 900-second limit.

| Configuration | Solved, 2009 instances | Solved, 2011 instances |
|---|---|---|
| Original version with preprocessing and inprocessing | 196 instances were solved. | 164 instances were solved. |
| Preprocessing only | 184 instances were solved. | 159 instances were solved. |
| Neither | 170 instances were solved. | 156 instances were solved. |

This is one solver at one point in time, so it shows the direction of the effect and not its size in general. The same paper also reports that, for incremental bounded model checking with Lingeling, inprocessing reached many more bounds.

### Incremental solving and frozen variables

Simplifications that do not preserve equivalence must be adapted when the caller later adds clauses. If $x$ has been eliminated, a new clause that mentions $x$ makes the old answer meaningless. There are two standard approaches. The caller can declare variables frozen, so that they are never eliminated, or the solver can restore the eliminated clauses when needed. The same applies to assumption literals.

## Worked examples

A script in the scratchpad checked each transformation below by enumerating models.

### Example 1: bounded variable elimination with a gate

Let $x_1$ be defined by the gate $x_1 \leftrightarrow x_4 \land x_5$, and let it occur in other clauses too.

```
C1 = (x1 ∨ x2 ∨ x3)          non-gate, positive
C2 = (x1 ∨ x6)               non-gate, positive
C3 = (x1 ∨ ¬x4 ∨ ¬x5)        gate, positive
C4 = (¬x1 ∨ x4)              gate, negative
C5 = (¬x1 ∨ x5)              gate, negative
C6 = (¬x1 ∨ ¬x6 ∨ x2)        non-gate, negative
```

All nine resolvents:

```
C1, C4 give (x2 ∨ x3 ∨ x4)
C1, C5 give (x2 ∨ x3 ∨ x5)
C1, C6 give (x2 ∨ x3 ∨ ¬x6)
C2, C4 give (x6 ∨ x4)
C2, C5 give (x6 ∨ x5)
C2, C6 give a tautology
C3, C4 give a tautology
C3, C5 give a tautology
C3, C6 give (¬x4 ∨ ¬x5 ∨ ¬x6 ∨ x2)
```

The non-tautological total is 6, the same as the 6 clauses removed, so BVE allows it. The gate-based rule keeps only the gate-with-non-gate resolvents:

```
(x2 ∨ x3 ∨ x4)   (x2 ∨ x3 ∨ x5)   (x6 ∨ x4)   (x6 ∨ x5)   (¬x4 ∨ ¬x5 ∨ ¬x6 ∨ x2)
```

That is 5 clauses. It omits $(x_2 \lor x_3 \lor \neg x_6)$, the one non-gate resolvent, which is implied. Resolve $(x_2 \lor x_3 \lor x_4)$ and $(x_2 \lor x_3 \lor x_5)$ against $(\neg x_4 \lor \neg x_5 \lor \neg x_6 \lor x_2)$ on $x_4$ and $x_5$, to obtain it. Enumeration confirmed that this result has exactly the projections of the models of the original to $x_2, \dots, x_6$.

### Example 2: strengthening and subsumption

```
C1 = (x1 ∨ x2)
C2 = (¬x1 ∨ x2 ∨ x3)
C3 = (x1 ∨ x2 ∨ x4)
```

C1 subsumes C3, so C3 is removed. C1 and C2 satisfy the condition for self-subsuming resolution with $l = x_1$ and $C = (x_2)$, because $(x_2) \subseteq (x_2 \lor x_3)$. So C2 is replaced by $(x_2 \lor x_3)$. The result is $(x_1 \lor x_2) \land (x_2 \lor x_3)$. Enumeration confirmed equivalence for the strengthening step.

### Example 3: blocked clause elimination and reconstruction

```
C1 = (x1 ∨ x2)
C2 = (¬x1 ∨ ¬x2 ∨ x3)
C3 = (¬x1 ∨ ¬x2 ∨ ¬x3)
C4 = (¬x3 ∨ x2)
```

Models of $F$, over $x_1, x_2, x_3$: $(\neg x_1, x_2, \neg x_3)$, $(\neg x_1, x_2, x_3)$ and $(x_1, \neg x_2, \neg x_3)$.

Check C1 on $x_1$. The clauses containing $\neg x_1$ are C2 and C3. The resolvent of C1 and C2 on $x_1$ is $(x_2 \lor \neg x_2 \lor x_3)$, a tautology, and the same holds for C3. So C1 is blocked on $x_1$. Removing it gives three clauses with four models, the three above plus $(\neg x_1, \neg x_2, \neg x_3)$. So BCE does not preserve equivalence.

Continue with the remaining formula. Now $\neg x_1$ is pure, so C2 and C3 are blocked on $\neg x_1$. Remove C2. Remove C3. Then $\neg x_3$ is pure in C4, so C4 is blocked on $\neg x_3$. The formula is empty, and BCE has shown satisfiability with no search.

The stack, in order of removal, is $(x_1, C_1)$, $(\neg x_1, C_2)$, $(\neg x_1, C_3)$, $(\neg x_3, C_4)$. Reconstruct from any assignment, in reverse order. First take all variables false.

```
C4 = (¬x3 ∨ x2): satisfied by ¬x3.
C3 = (¬x1 ∨ ¬x2 ∨ ¬x3): satisfied.
C2 = (¬x1 ∨ ¬x2 ∨ x3): satisfied.
C1 = (x1 ∨ x2): falsified, so set x1 true.
Result: x1, ¬x2, ¬x3, a model of F.
```

Now take all variables true.

```
C4 = (¬x3 ∨ x2): satisfied by x2.
C3 = (¬x1 ∨ ¬x2 ∨ ¬x3): falsified, so set ¬x1 true, meaning x1 false.
C2 = (¬x1 ∨ ¬x2 ∨ x3): satisfied.
C1 = (x1 ∨ x2): satisfied by x2.
Result: ¬x1, x2, x3, a model of F.
```

The script confirmed that all eight starting assignments give models of $F$.

### Example 4: failed literals, equivalences and vivification

Failed literal. Let $F = (\neg x_1 \lor x_2) \land (\neg x_1 \lor x_3) \land (\neg x_2 \lor \neg x_3 \lor x_4) \land (\neg x_4 \lor \neg x_1)$. Probe $x_1$. Propagation gives $x_2$, then $x_3$, then $x_4$, and then $(\neg x_4 \lor \neg x_1)$ is falsified. So $(\neg x_1)$ is implied and can be added.

Equivalence. Let $F = (\neg x_1 \lor x_2) \land (\neg x_2 \lor x_3) \land (\neg x_3 \lor x_1) \land (x_1 \lor x_4) \land (\neg x_2 \lor \neg x_4)$. The first three clauses form the cycle of implications $x_1, x_2, x_3$, so these are equivalent. Substituting $x_1$ for the others gives $(x_1 \lor x_4) \land (\neg x_1 \lor \neg x_4)$. Its two models map back to $(x_1, x_2, x_3, \neg x_4)$ and $(\neg x_1, \neg x_2, \neg x_3, x_4)$, which are the two models of $F$.

Vivification. Let $F$ contain $C = (x_1 \lor x_2 \lor x_3)$ together with $(x_1 \lor x_4)$ and $(\neg x_4 \lor x_2)$. Assign $\neg x_1$. Propagation on the other clauses gives $x_4$ and then $x_2$, so $x_2$ is implied. Hence $(x_1 \lor x_2)$ is implied, and it replaces $C$. Enumeration confirmed equivalence.

## Common mistakes

- Treating BVE as preserving equivalence. It removes a variable, so at best it preserves the models over the remaining variables.
- Removing the original clauses of $x$ without keeping them for reconstruction. If a model of the input is needed, the removed clauses are required to assign $x$.
- Checking a resolvent for being empty and not for being tautological in BCE. The condition is that every resolvent on $l$ is a tautology.
- Forgetting that a clause is blocked on a specific literal. The stack must record that literal, because it is the one that may be flipped.
- Processing the reconstruction stack in forward order. The order must be reversed, because later removals were checked against a smaller formula.
- Running BVE or BCE before counting models. Both can change the model count, as can pure literal elimination, so model counters must use count-preserving variants.
- Eliminating variables that an incremental caller will mention later. Such variables must be frozen or restored.
- Assuming that subsumption requires equal clauses. A strict subset subsumes, and the smaller clause is the one kept.
- Applying self-subsuming resolution when $C \not\subseteq D$. The resolvent is then longer than the target minus the literal, and the replacement is not justified.
- Believing that simplification always speeds up solving. Removing clauses can reduce propagation strength, which is why solvers use budgets and bounds and often limit growth.
- Thinking that the failed literal unit comes from the search. It comes from propagation alone, under one assumption, so it is cheap to justify in a proof.

## Exercises

### Exercise 1

For the following clauses, list all subsumption pairs and all self-subsuming resolutions: $(x_1 \lor x_2)$, $(x_1 \lor x_2 \lor x_3)$, $(\neg x_1 \lor x_2 \lor x_4)$, $(x_1 \lor \neg x_2 \lor x_3)$.

<details><summary>Solution</summary>

Subsumption: $(x_1 \lor x_2)$ subsumes $(x_1 \lor x_2 \lor x_3)$.

Self-subsuming resolutions:

- With $(x_1 \lor x_2)$ and $(\neg x_1 \lor x_2 \lor x_4)$ on $x_1$: since $(x_2) \subseteq (x_2 \lor x_4)$, replace the second by $(x_2 \lor x_4)$.
- With $(x_1 \lor x_2)$ and $(x_1 \lor \neg x_2 \lor x_3)$ on $x_2$: since $(x_1) \subseteq (x_1 \lor x_3)$, replace the second by $(x_1 \lor x_3)$.
- With $(x_1 \lor x_2 \lor x_3)$ and $(x_1 \lor \neg x_2 \lor x_3)$ on $x_2$: replace the second by $(x_1 \lor x_3)$, which is the same result.

</details>

### Exercise 2

Variable $x_1$ occurs in $(x_1 \lor x_2)$, $(x_1 \lor x_3)$, $(\neg x_1 \lor x_4)$, $(\neg x_1 \lor x_5)$. Is it eliminated under a no-growth bound? What about a variable occurring in $(x_1 \lor x_2)$, $(x_1 \lor x_3)$, $(x_1 \lor x_6)$, $(\neg x_1 \lor x_4)$, $(\neg x_1 \lor x_5)$, $(\neg x_1 \lor x_7)$?

<details><summary>Solution</summary>

The first case has 4 clauses and $2 \times 2 = 4$ non-tautological resolvents, namely $(x_2 \lor x_4)$, $(x_2 \lor x_5)$, $(x_3 \lor x_4)$ and $(x_3 \lor x_5)$. The count does not grow, so it is eliminated.

The second case has 6 clauses and $3 \times 3 = 9$ non-tautological resolvents, so the count grows by 3, and it is not eliminated under the strict bound.

</details>

### Exercise 3

Check whether each clause in $F$ is blocked, on which literal, and give the result of BCE.

$$F = (x_1 \lor x_2) \land (\neg x_1 \lor x_3) \land (\neg x_2 \lor \neg x_3) \land (\neg x_1 \lor \neg x_3)$$

<details><summary>Solution</summary>

Occurrences: $x_1$ in C1; $\neg x_1$ in C2 and C4; $x_2$ in C1; $\neg x_2$ in C3; $x_3$ in C2; $\neg x_3$ in C3 and C4.

- C1 on $x_1$: resolving with C2 gives $(x_2 \lor x_3)$, which is not a tautology. So it is not blocked on $x_1$. On $x_2$: resolving with C3 gives $(x_1 \lor \neg x_3)$, which is not a tautology. So C1 is not blocked.
- C2 on $\neg x_1$: resolving with C1 gives $(x_3 \lor x_2)$, not a tautology. On $x_3$: resolving with C3 gives $(\neg x_1 \lor \neg x_2)$, not a tautology. So C2 is not blocked.
- C3 on $\neg x_2$: resolving with C1 gives $(\neg x_3 \lor x_1)$, not a tautology. On $\neg x_3$: resolving with C2 gives $(\neg x_2 \lor \neg x_1)$, not a tautology. So C3 is not blocked.
- C4 on $\neg x_1$: resolving with C1 gives $(\neg x_3 \lor x_2)$, not a tautology. On $\neg x_3$: resolving with C2 gives $\neg x_1$, not a tautology. So C4 is not blocked.

BCE removes nothing. A blocked clause is often absent from small dense formulas, and this one is one of them.

</details>

### Exercise 4

Given the BCE in Example 3, reconstruct a model from the starting assignment $(x_1, \neg x_2, x_3)$.

<details><summary>Solution</summary>

```
C4 = (¬x3 ∨ x2): x3 true and x2 false, so it is falsified. Set ¬x3 true, meaning x3 false.
C3 = (¬x1 ∨ ¬x2 ∨ ¬x3): satisfied.
C2 = (¬x1 ∨ ¬x2 ∨ x3): satisfied by ¬x2.
C1 = (x1 ∨ x2): satisfied by x1.
Result: x1, ¬x2, ¬x3.
```

This is a model of $F$.

</details>

### Exercise 5

Prove that failed literal probing preserves equivalence, and that it can produce a clause that a solver's level-0 propagation does not find.

<details><summary>Solution</summary>

If propagation under $l$ reaches a conflict, then $F \land l$ is unsatisfiable, since propagation is sound. So $F \models \neg l$. Adding an implied clause preserves equivalence.

Example 4 shows the second claim. The formula given has no unit clause, so level-0 propagation assigns nothing. Probing $x_1$ gives $(\neg x_1)$.

</details>

### Exercise 6

Show by example that BVE and BCE do not preserve the number of models.

<details><summary>Solution</summary>

BVE: let $F = (x_1 \lor x_2)$, which has 3 models over $x_1, x_2$. Eliminating $x_1$ gives the empty formula, which has 2 models over $x_2$.

BCE: Example 3 has 3 models before removal of C1 and 4 models after it, over the same variables.

</details>

### Exercise 7

An incremental solver runs BVE on $F = (x_1 \lor x_2)$, eliminating $x_1$. The caller then adds $(\neg x_1)$ and $(\neg x_2)$. Explain what goes wrong, and give the fix.

<details><summary>Solution</summary>

The formula with the added clauses is $(x_1 \lor x_2) \land (\neg x_1) \land (\neg x_2)$, which is unsatisfiable. After elimination the database contains no clause from $F$. Adding the two units yields a satisfiable formula, so the solver answers SAT, and this is wrong. The relationship between $x_1$ and $x_2$ is gone.

The fix is to freeze any variable that later clauses may mention, so that it is not eliminated. Alternatively, when a clause mentions an eliminated variable, restore its removed clauses before adding the clause.

</details>

### Exercise 8

Prove that eliminating a variable that defines an AND gate, using only gate-with-non-gate resolvents, gives a formula equivalent to substituting the definition. Take $x \leftrightarrow a \land b$.

<details><summary>Solution</summary>

Let the gate clauses be $(\neg x \lor a)$, $(\neg x \lor b)$ and $(x \lor \neg a \lor \neg b)$. Let the non-gate clauses be $(x \lor P_i)$ and $(\neg x \lor Q_j)$.

Substitution of $a \land b$ for $x$ turns $(x \lor P_i)$ into $(a \land b) \lor P_i$, which is $(a \lor P_i) \land (b \lor P_i)$. These are the resolvents of $(x \lor P_i)$ with $(\neg x \lor a)$ and $(\neg x \lor b)$. It turns $(\neg x \lor Q_j)$ into $\neg a \lor \neg b \lor Q_j$, which is the resolvent of $(\neg x \lor Q_j)$ with $(x \lor \neg a \lor \neg b)$. The gate clauses themselves become tautologies under the substitution.

The two formulas are therefore identical as clause sets. Since $x \leftrightarrow a \land b$ is a definition, $F$ is equivalent to the definition conjoined with the substituted formula. So the substituted formula is $\exists x. F$, which is the correct result of elimination by Theorem 2. Hence the non-gate with non-gate resolvents are implied.

</details>

### Exercise 9

Prove that BCE is confluent: it reaches the same final formula in any order.

<details><summary>Solution</summary>

First, monotonicity: if $C$ is blocked on $l$ with respect to $F$, and $C \in G \subseteq F$, then $C$ is blocked on $l$ with respect to $G$. The condition quantifies over clauses containing $\neg l$, and $G$ has only a subset of those.

Now suppose that two runs of BCE end in $F_1$ and $F_2$. Let the run reaching $F_2$ remove $C_1, C_2, \dots$ in order. Suppose that some $C_i$ remains in $F_1$, and take the least such $i$. Then all earlier clauses $C_1, \dots, C_{i-1}$ are absent from $F_1$. So $F_1$ is a subset of the formula from which $C_i$ was removed in the second run. By monotonicity, $C_i$ is blocked in $F_1$, which contradicts that $F_1$ is a final formula. So $F_1 \subseteq F_2$, and by symmetry the two are equal.

</details>

### Exercise 10

Propose an order for a preprocessing pipeline consisting of unit propagation, subsumption, strengthening, BVE, BCE and probing, and justify it. State what a solver must store.

<details><summary>Solution</summary>

A reasonable order is the following. There is no single correct order, and solvers schedule these in rounds with budgets.

1. Unit propagation comes first, because it is cheap and simplifies all later steps.
2. Subsumption and strengthening come next, since they preserve equivalence and they shrink occurrence lists.
3. BVE follows, since shorter clauses produce fewer and shorter resolvents. New resolvents go back to step 2.
4. BCE follows BVE, since it benefits from removed clauses and can enable further elimination.
5. Probing runs on a budget, since each probe costs a propagation. New units go back to step 1.

The solver must store the removed clauses, with the witness literal for each, on a reconstruction stack, and it must process the stack in reverse order to return a model of the input. If it produces proofs, then it must emit additions and deletions, as shown in [Proofs and Certificates](../proofs-and-certificates/). If it is incremental, it must respect frozen variables.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Apply subsumption, self-subsuming resolution, BVE, BCE, probing and equivalent literal substitution on small formulas.
- State for each technique what it preserves, and give an example where the stronger property fails.
- Prove Theorem 1 and Theorem 3, and explain the reconstruction procedure.
- Explain the gate rule for elimination on an AND gate.
- State the four inprocessing rules, and the invariant.
- Explain why incremental solving needs frozen variables.

## Materials

- Eén and Biere, Effective Preprocessing in SAT Through Variable and Clause Elimination, SAT 2005. Read it for BVE with bounds, gate definitions, subsumption and strengthening.
- Järvisalo, Heule and Biere, Inprocessing Rules, IJCAR 2012. Read it for the abstract rules, RAT-based instantiation and reconstruction.
- Kullmann, On a Generalization of Extended Resolution, Discrete Applied Mathematics 1999. Read it for the origin of blocked clauses.
- Järvisalo, Biere and Heule, Blocked Clause Elimination, TACAS 2010. Read it for confluence and the relation to Plaisted-Greenbaum and cone of influence.
- Piette, Hamadi and Saïs, Vivifying Propositional Clausal Formulae, ECAI 2008. Read it for vivification.
