# DPLL(T)

Part 2, Chapter 5: SMT.

## Objective

Trace the interaction between a CDCL core and a theory solver, including theory propagation and conflict explanations.

## Why this matters

DPLL(T) is the skeleton of nearly every SMT solver, and every other topic in this chapter plugs a component into it. Verification conditions from [Chapter 7](../../07-deductive-verification/), queries from the model checkers of [Chapter 8](../../08-model-checking/) and policy analyses in industry all end up as a CDCL search that consults theory solvers. When a query is slow or returns an unexpected answer, an applied scientist reasons about this loop: which atoms the search decides, how large the explanations are, and how much the theory solver propagates. You will implement the loop in [DPLL(T) Integration](../../../part-3-building-the-engines/10-smt-solver/dpllt-integration/).

## Prerequisites

- [CDCL](../../04-sat/cdcl/), for implication graphs, first-UIP analysis and backjumping.
- [Resolution and DPLL](../../04-sat/resolution-and-dpll/), for the propositional procedure and resolution.
- [Encodings](../../04-sat/encodings/), for the Tseitin transformation.
- [First-Order Theories](../../../part-1-foundations/01-mathematical-logic/first-order-theories/), for satisfiability and validity modulo a theory.

## Lesson

### The SMT problem

A theory $T$ is a set of first-order sentences over a signature $\Sigma$, or equivalently a class of $\Sigma$-structures. A quantifier-free formula $F$ is $T$-satisfiable if some model of $T$, together with an assignment to the free variables and free constants of $F$, satisfies $F$. A set of literals is $T$-consistent if it is $T$-satisfiable. We write $\Gamma \models_T \varphi$ if every model of $T$ that satisfies $\Gamma$ also satisfies $\varphi$. A clause $C$ is a $T$-lemma, or theory lemma, if $\models_T C$.

The SMT problem takes a quantifier-free formula with arbitrary Boolean structure and asks whether it is $T$-satisfiable. A theory solver only needs to handle the easier problem for conjunctions of literals. The whole design of DPLL(T) follows from this division of labour: decision procedures for conjunctions were known from the 1970s and 1980s, and CDCL solvers became very good at Boolean search in the late 1990s, so the natural goal is to combine them without rebuilding either.

Two early families of methods existed. Eager methods translate the whole problem to SAT in one step, using reductions such as Ackermann's for uninterpreted functions and bit-blasting for bit-vectors. Eager translation remains the standard for bit-vectors, as [Bit-Vectors](../bit-vectors/) shows, but for arithmetic it can produce very large encodings. Lazy methods give the SAT solver only the Boolean skeleton and add theory facts as they become needed. The name DPLL(T), and the view of it as a generic engine parameterized by a theory solver, come from the work of Ganzinger, Hagen, Nieuwenhuis, Oliveras and Tinelli, later consolidated in the Nieuwenhuis, Oliveras and Tinelli paper listed under Materials.

### Boolean abstraction

Assign a distinct propositional variable to each distinct theory atom. The Boolean abstraction $\alpha(F)$ replaces each atom in $F$ with its variable. The map $\gamma$ sends the variables back to atoms, and it extends to literals and sets of literals.

Atoms should first be normalized, so that syntactically different forms of one constraint share one variable. For example, $x \le y$ and $y \ge x$ should both become $x - y \le 0$. Without this, the SAT solver treats them as unrelated and the theory solver must rediscover the link.

For $F$ in CNF, a propositional assignment $M$ is a set of literals over the variables of $\alpha(F)$.

Proposition. $F$ is $T$-satisfiable if and only if there is an assignment $M$ such that $M \models \alpha(F)$ propositionally and $\gamma(M)$ is $T$-consistent.

Proof. Suppose a $T$-model $\mathcal{A}$ satisfies $F$. Let $M$ contain each abstraction variable $p$ with the truth value of $\gamma(p)$ in $\mathcal{A}$. Then $M \models \alpha(F)$, since $F$ and $\alpha(F)$ have the same Boolean structure, and $\mathcal{A}$ witnesses that $\gamma(M)$ is $T$-consistent. Conversely, if $M \models \alpha(F)$ and $\mathcal{A}$ is a $T$-model of $\gamma(M)$, then the truth value of each atom in $\mathcal{A}$ agrees with $M$ wherever $M$ is defined, and that is enough to make every clause of $F$ true. $\square$

It is sufficient for $M$ to be partial, provided it satisfies every clause. This is why a solver may stop before assigning all atoms.

### The offline lazy loop

The simplest lazy procedure treats the SAT solver as a black box.

```
offline(F):
    B := alpha(F)
    loop:
        if SAT(B) = unsat: return unsat
        M := model of B
        if T-check(gamma(M)) = consistent: return sat
        let K be a T-inconsistent subset of gamma(M)
        B := B and (the disjunction of the negations of the abstractions of K)
```

The added clause is a blocking clause. It is a $T$-lemma, so adding it preserves $T$-satisfiability of $F$. The loop terminates because the number of assignments to the finite set of abstraction variables is finite and each iteration removes at least the current one.

The quality of $K$ determines how much is removed. If $K$ is all of $\gamma(M)$, the clause removes a single full assignment, and the loop can run exponentially many times. If $K$ is small, the clause removes every assignment extending it. A set $K$ is a minimal conflict set when it is $T$-inconsistent and each of its proper subsets is $T$-consistent.

The offline loop has two weaknesses. It finds theory inconsistencies only after the SAT solver has completed an assignment, so the search wastes effort below an already inconsistent partial assignment. It also restarts its search state from scratch, unless the SAT solver is incremental.

### The online architecture

CDCL(T) integrates the theory solver in the CDCL loop. The theory solver sees literals as they are assigned, and it is called before the assignment is complete. This is called early pruning. The usual interface is the following one, which is close to the interface described by Dutertre and de Moura.

| Operation | Contract |
|---|---|
| `assert(l)` | Adds the theory literal $\gamma(l)$ to the current set, and it may report a conflict using only cheap checks. |
| `check()` | Reports either consistency or a conflict set, and it must be sound and complete at least at the final check. |
| `propagate()` | Returns unassigned literals that are $T$-entailed by the current set, and it need not return all of them. |
| `explain(l)` | Returns a subset of the literals asserted before $l$ that $T$-entails $l$. |
| `backtrack(n)` | Restores the state to an earlier level. |

The solver must be incremental, because literals arrive one at a time, and it must be cheap to backtrack, because CDCL backtracks constantly. These two requirements shaped theory solvers, and they explain why the general simplex procedure of [Arithmetic](../arithmetic/) keeps its tableau fixed and changes only bounds.

```
cdcl_t(F):
    trail := empty; level := 0; B := alpha(F)
    loop:
        conflict := boolean_propagate(B, trail)     # unit propagation
        if conflict is none:
            send new trail literals to the theory solver
            conflict := theory_check()               # returns a clause, or none
        if conflict is not none:
            if conflict has no literal above level 0: return unsat
            let top be the highest level in conflict; backtrack to top
            learned, back := analyze(conflict, trail)
            add learned to B
            backtrack to back; assert the asserting literal of learned
            continue
        if theory_propagate(trail) added a literal: continue
        if every clause is satisfied or all atoms are assigned:
            if final_check() is consistent: return sat
            # final_check may also return a conflict or new lemmas
            continue
        level := level + 1; decide an unassigned literal
```

Solvers schedule these steps in many different ways, so a trace depends on the order. The order above is the one used in the traces below: unit propagation runs to a fixed point, then the theory is checked, then one theory propagation is performed, and unit propagation resumes.

### Theory conflicts

If the theory reports the conflict set $\{l_1, \dots, l_n\}$, the core receives the conflict clause $\neg l_1 \lor \dots \lor \neg l_n$. All its literals are false under the trail, so it behaves exactly like a clause falsified during Boolean propagation, and conflict analysis proceeds as in [CDCL](../../04-sat/cdcl/). This is the central point of the architecture: the Boolean engine does not need any knowledge of what the clause means.

There is one difference from the purely Boolean case. A clause falsified by unit propagation always has a literal at the current decision level, while a theory conflict clause need not. For example, a solver that checks the theory only occasionally may find a conflict among literals of levels 1 and 2 when the current level is 5. The core must first backtrack to the highest level occurring in the clause, and then analyze. If that level contains one literal of the clause, the clause is already asserting.

### Theory propagation

If the current literals $T$-entail an unassigned literal $l$ that occurs in the formula, the theory solver can assign it. Without this, the core might decide $\neg l$, and then a conflict would arise that could have been avoided.

A theory-propagated literal needs a reason clause, because conflict analysis may resolve on it. If $\{l_1, \dots, l_n\} \models_T l$, the reason is the $T$-lemma $\neg l_1 \lor \dots \lor \neg l_n \lor l$. Producing explanations eagerly is expensive, and most are never used, so solvers usually record only that the theory propagated $l$, and they ask for the explanation when analysis first needs it. A lazily produced explanation must only use literals that precede $l$ on the trail, otherwise the implication graph could contain a cycle and analysis might not terminate.

Exhaustive theory propagation is usually not worthwhile. For example, Dutertre and de Moura report a comparison in their solver between no propagation, heuristic propagation and full propagation, and their solver uses a cheap derivation of bounds from tableau rows. In the same way, a congruence closure solver propagates equalities between terms that are already merged, which is cheap, and it does not attempt anything harder.

### The abstract transition system

Nieuwenhuis, Oliveras and Tinelli describe the family of procedures as a transition system on states $M \parallel F$, where $M$ is a sequence of literals, some marked as decision literals $l^d$, and $F$ is a clause set. There is a special state FailState. We write $M \models \neg C$ if the complement of each literal of $C$ appears in $M$, and we consider $M$ as a conjunction when writing $M \models_T l$.

| Rule | Transition | Conditions |
|---|---|---|
| UnitPropagate | $M \parallel F, C \lor l$ becomes $M\, l \parallel F, C \lor l$ | $M \models \neg C$ and $l$ is undefined in $M$. |
| Decide | $M \parallel F$ becomes $M\, l^d \parallel F$ | $l$ or $\neg l$ occurs in $F$ and $l$ is undefined in $M$. |
| Fail | $M \parallel F, C$ becomes FailState | $M \models \neg C$ and $M$ has no decision literal. |
| Restart | $M \parallel F$ becomes $\emptyset \parallel F$ | There is no condition. |
| TheoryPropagate | $M \parallel F$ becomes $M\, l \parallel F$ | $M \models_T l$, $l$ or $\neg l$ occurs in $F$, and $l$ is undefined in $M$. |
| T-Learn | $M \parallel F$ becomes $M \parallel F, C$ | Each atom of $C$ occurs in $F$ or in $M$, and $F \models_T C$. |
| T-Forget | $M \parallel F, C$ becomes $M \parallel F$ | $F \models_T C$. |
| T-Backjump | $M\, l^d\, N \parallel F, C$ becomes $M\, l' \parallel F, C$ | See the condition below. |

T-Backjump requires that $M\, l^d\, N \models \neg C$ and that there is a clause $C' \lor l'$ with $F, C \models_T C' \lor l'$, $M \models \neg C'$, $l'$ undefined in $M$, and $l'$ or $\neg l'$ occurring in $F$ or in $M\, l^d\, N$.

The system separates what is allowed from how a solver schedules it. Conflict analysis does not appear as a rule. It is one way to find the backjump clause $C' \lor l'$, and any learned clause it produces is an instance of T-Learn. Theory conflicts are modeled by T-Learn of the conflict clause, which immediately enables T-Backjump or Fail.

Theorem (correctness of Abstract DPLL Modulo Theories). Let $F_0$ be a finite clause set, and consider derivations from $\emptyset \parallel F_0$ using the rules above, in which Restart is applied with increasing periodicity and T-Learn and T-Forget are applied only finitely often between applications of other rules. Then every derivation is finite. Suppose further that the derivation ends in a state that is final for Decide, Fail, UnitPropagate, TheoryPropagate and T-Backjump, and that if it has the form $M \parallel F$ then $M$ is $T$-consistent. Then:

1. The final state is FailState if and only if $F_0$ is $T$-unsatisfiable.
2. If the final state is $M \parallel F$, then $M$ is a $T$-model of $F_0$, in the sense that $M \models F_0$ propositionally and $M$ is $T$-consistent.

Proof sketch. The following invariants hold along any derivation: $F$ and $F_0$ are $T$-equivalent, because learned clauses are $T$-entailed and forgotten ones are entailed by what remains; and each non-decision literal $l$ of $M$ is $T$-entailed by $F$ together with the decision literals before it.

For termination, write $M = M_0 l_1^d M_1 l_2^d \dots l_k^d M_k$, and map $M$ to the tuple $(|M_0|, |M_1|, \dots, |M_k|)$. There are finitely many atoms, so tuples and lengths are bounded. UnitPropagate and TheoryPropagate increase the last component. Decide appends a new component. T-Backjump cuts the tuple and increases an earlier component. Each of these strictly increases the tuple in the lexicographic order, with a longer tuple counted as larger when it extends a shorter one. The learning rules leave $M$ unchanged and occur finitely often in each phase, and the restart condition ensures that eventually a phase is long enough to reach a final state.

For the verdicts, consider Fail. No decision literals remain, so the invariant says that every literal of $M$ is $T$-entailed by $F$. Since $M \models \neg C$ for some $C \in F$, $F$ is $T$-unsatisfiable, and so is $F_0$. Next consider a final state $M \parallel F$. Decide does not apply, so every literal of $F$ is defined in $M$. If a clause $C$ had $M \models \neg C$, then Fail would apply if $M$ had no decision, and otherwise T-Backjump would apply: taking the last decision $l^d$, the literals before it together with $F$ entail the negation of $l^d$, and this provides a backjump clause. Hence $M \models F$, and since $M$ is $T$-consistent, the Proposition above gives that $F_0$ is $T$-satisfiable. $\square$

The hypothesis on the atoms of T-Learn is what keeps the atom set finite. Some theories need new atoms during search, and this is handled by the splitting-on-demand extension described next.

### Theory-specific case splits

Sometimes a theory solver for a non-convex theory needs a case split. A disequality $x \ne y$ over the reals becomes $x < y \lor x > y$, and an integer variable with a fractional relaxation value leads to $x \le k \lor x \ge k+1$. A theory solver could perform these splits internally, but then it would duplicate the Boolean search. Splitting on demand, by Barrett, Nieuwenhuis, Oliveras and Tinelli, has the theory solver return such a clause as a lemma, possibly with new atoms, and the SAT core does the split. Termination then requires that the theory solver introduce only finitely many atoms, and this is why the transition system's restriction on T-Learn has to be relaxed with care. The branch and bound procedure in [Arithmetic](../arithmetic/) shows a case in which an unrestricted split generator does not terminate.

### Further refinements

Static learning adds theory lemmas about the atoms before search begins. For example, it adds $x \le 1 \to x \le 2$ when both atoms occur. Polarity filtering observes that if an atom occurs only positively in the clauses, then its false assignment constrains nothing, and it need not be sent to the theory solver. Relevancy filtering generalizes this to the structure of the original formula, which Tseitin encoding otherwise hides. Theory-guided decision heuristics choose a phase for atoms that agrees with the theory solver's current model, a technique that many solvers use in order to reduce the number of theory conflicts.

If a theory solver is in NP, then the combined problem is also in NP: guess a Boolean assignment and a certificate for the theory check. The exponential behaviour that remains is the behaviour of CDCL.

## Worked examples

### Worked example 1: offline loop over linear real arithmetic

Let $F$ be

$$
(x \le 0 \lor y \le 0) \land (x \ge 1 \lor y \ge 1) \land (x + y \ge 3).
$$

Abstract the atoms as $p_1: x \le 0$, $p_2: y \le 0$, $p_3: x \ge 1$, $p_4: y \ge 1$ and $p_5: x + y \ge 3$. Then $\alpha(F) = (p_1 \lor p_2) \land (p_3 \lor p_4) \land p_5$.

Iteration 1. Suppose the SAT solver returns $p_1, \neg p_2, p_3, \neg p_4, p_5$. The theory solver receives $x \le 0$, $y > 0$, $x \ge 1$, $y < 1$ and $x + y \ge 3$. This is inconsistent, and $\{x \le 0, x \ge 1\}$ is a minimal conflict set. The blocking clause is $\neg p_1 \lor \neg p_3$.

Iteration 2. Suppose the SAT solver now returns $p_1, \neg p_2, \neg p_3, p_4, p_5$. The theory solver receives $x \le 0$, $y > 0$, $x < 1$, $y \ge 1$ and $x + y \ge 3$. The assignment $x = 0, y = 3$ satisfies these. The verdict is sat, confirmed by Z3.

Using all five literals as the blocking clause would have removed only one assignment, and the solver could have tried further assignments containing both $p_1$ and $p_3$. With $p_5$ fixed, the two-literal clause rules out all four assignments that contain $p_1$ and $p_3$.

### Worked example 2: CDCL(T) over difference constraints with theory propagation

The theory is linear real arithmetic, and all atoms bound a difference of two variables, so you can check every theory claim by adding inequalities. The atoms are

$$
\begin{aligned}
a &: x \le y - 1 & b &: y \le z - 1 & c &: z \le x + 1 & d &: z \le w \\
e &: w \le x & g &: t \ge 0 & n &: t \le -1 & m &: z \le y
\end{aligned}
$$

The clauses are

$$
(a \lor n), \quad (c \lor d), \quad (\neg d \lor e), \quad (g \lor n), \quad (b \lor m).
$$

The decisions, when needed, are taken in the order $a, g, b, d$. The theory solver propagates after unit propagation reaches a fixed point, and it examines the unassigned atoms in the order listed above.

```
step  event     literal  level  reason or explanation
 1    decide    a        1
 2    decide    g        2
 3    T-prop    ¬n       2      (¬n ∨ ¬g)        t >= 0 entails t > -1
 4    decide    b        3
 5    T-prop    ¬c       3      (¬c ∨ ¬a ∨ ¬b)   x <= y-1 and y <= z-1 entail x <= z-2
 6    unit      d        3      (c ∨ d)
 7    unit      e        3      (¬d ∨ e)
 8    T-confl                    core {¬c, d, e}
```

The conflict at step 8 can be checked as follows. The literal $\neg c$ says $z > x + 1$. Adding $d$ and $e$ gives $z \le w \le x$. These give $x + 1 < z \le x$, which is impossible. The set $\{\neg c, d, e\}$ is minimal: removing any one of its elements leaves a consistent set. The conflict clause is $c \lor \neg d \lor \neg e$.

Conflict analysis at level 3 proceeds as follows.

```
start                                   (c ∨ ¬d ∨ ¬e)    three literals at level 3
resolve on e with (¬d ∨ e)              (c ∨ ¬d)         two literals at level 3
resolve on d with (c ∨ d)               (c)              one literal at level 3, stop
```

The learned clause is the unit clause $(c)$. Since it contains no other literal, the backjump level is 0. The solver skips levels 1 and 2, which played no part in the conflict. Note that $(c)$ was derived from clauses of the formula and a theory lemma, so it is $T$-entailed by $F$, although it is not a theory lemma on its own, because $c$ is not valid in the theory.

The search continues as follows.

```
step  event     literal  level  reason or explanation
 9    unit      c        0      (c)
10    decide    a        1
11    T-prop    ¬b       1      (¬b ∨ ¬c ∨ ¬a)   as at step 5, a, b and c are inconsistent
12    unit      m        1      (b ∨ m)
13    decide    g        2
14    T-prop    ¬n       2      (¬n ∨ ¬g)
15    decide    d        3
16    unit      e        3      (¬d ∨ e)
```

All clauses are satisfied, and all atoms are assigned. The final check succeeds with the model $x = 0, y = 1, z = 0, w = 0, t = 0$. You can check each literal: $a$ holds since $0 \le 0$, $\neg b$ since $1 > -1$, $c$ since $0 \le 1$, $m$ since $0 \le 1$, $g$ since $0 \ge 0$, $\neg n$ since $0 > -1$, $d$ since $0 \le 0$, and $e$ since $0 \le 0$. Z3 also reports the formula satisfiable.

### Worked example 3: a two-literal learned clause over equality

Use the theory of equality, with atoms $e_1: p = q$, $e_2: r = s$, $e_3: q = w$, $e_4: w = v$, $e_5: p = v$, and with clauses

$$
(e_1 \lor e_5), \quad (e_2 \lor e_3), \quad (\neg e_3 \lor e_4), \quad (\neg e_5 \lor \neg e_3).
$$

The decision order is $e_1, e_2, e_3, e_4$.

```
step  event     literal  level  reason or explanation
 1    decide    e1       1
 2    decide    e2       2
 3    decide    e3       3
 4    unit      e4       3      (¬e3 ∨ e4)
 5    unit      ¬e5      3      (¬e5 ∨ ¬e3)
 6    T-confl                    core {e1, e3, e4, ¬e5}, since p = q = w = v contradicts p != v
```

The conflict clause is $\neg e_1 \lor \neg e_3 \lor \neg e_4 \lor e_5$. Analysis proceeds as follows.

```
start                                   (¬e1 ∨ ¬e3 ∨ ¬e4 ∨ e5)    e3, e4, e5 at level 3
resolve on e5 with (¬e5 ∨ ¬e3)          (¬e1 ∨ ¬e3 ∨ ¬e4)         e3, e4 at level 3
resolve on e4 with (¬e3 ∨ e4)           (¬e1 ∨ ¬e3)               only e3 at level 3, stop
```

The first UIP is $e_3$. The learned clause $\neg e_1 \lor \neg e_3$ has second-highest level 1, so the solver backjumps to level 1, skipping level 2, and asserts $\neg e_3$. The search continues as follows.

```
step  event     literal  level  reason or explanation
 7    unit      ¬e3      1      (¬e1 ∨ ¬e3)
 8    unit      e2       1      (e2 ∨ e3)
 9    decide    e4       2
10    T-prop    ¬e5      2      (¬e5 ∨ ¬e1 ∨ e3 ∨ ¬e4)
```

The explanation at step 10 deserves a check. It says that $p = q$, $q \ne w$ and $w = v$ entail $p \ne v$. Indeed, if $p = v$ held then $q = p = v = w$, contradicting $q \ne w$. This propagation uses a negative equality, which a real congruence closure solver would also be able to explain through the disequality. The final assignment is $e_1, \neg e_3, e_2, e_4, \neg e_5$, and it is consistent: take $p = q$ as one element, $w = v$ as another, and $r = s$ as any element. The verdict is sat, confirmed by Z3.

Compare the literal $e_2$ here with the literal $e_2$ at level 2 before the backjump. There it was a decision that had no part in the conflict. Now it is implied at level 1, because the learned clause changed the Boolean situation.

## Common mistakes

- Treating a theory conflict clause as if it must have a literal at the current level. A theory conflict may lie entirely below the current level, and the solver must backtrack to the highest level in the clause before it applies first-UIP analysis.
- Treating the learned clause as a theory lemma. The theory conflict clause is $T$-valid, but the result of resolving it with clauses of $F$ is only $T$-entailed by $F$. Worked example 2 learns $(c)$, which is not valid in arithmetic.
- Forgetting that negative literals go to the theory as well. If $p$ abstracts $x \le 0$, then the assignment $\neg p$ means $x > 0$, and the theory solver must take it into account unless polarity filtering has shown that this is unnecessary.
- Assuming that the Boolean abstraction preserves $T$-satisfiability. It only over-approximates: $\alpha(F)$ being satisfiable says nothing about $F$, while $\alpha(F)$ being unsatisfiable does imply that $F$ is $T$-unsatisfiable.
- Explaining a propagated literal with literals that were assigned after it. The explanation must use only earlier trail literals, or the implication graph may be cyclic.
- Reporting sat from early checks alone. Intermediate checks may be incomplete by design, and the verdict sat requires a final check that is complete for the theory.
- Believing that small conflict sets are only an optimization. On a problem with many atoms, full-assignment blocking clauses make the procedure behave like enumeration, and this typically decides whether a query finishes.
- Thinking that theory propagation is needed for correctness. TheoryPropagate is optional, and the procedure remains correct without it, as long as the final assignment is checked.

## Exercises

1. State what it means for a set $K$ to be a minimal conflict set, and give a minimal conflict set in $\{x \le 1, y \le 0, x \ge 2, y \ge -1, z = 3\}$ over the reals.

<details><summary>Solution</summary>

A set $K$ of literals is a minimal conflict set if it is $T$-inconsistent and every proper subset of $K$ is $T$-consistent. In the given set, $\{x \le 1, x \ge 2\}$ is inconsistent, and each singleton is consistent, so it is a minimal conflict set. There are no others, since the remaining literals have no contradiction among them.

</details>

2. Give the Boolean abstraction of $(x \le y \lor f(x) = a) \land (y \ge x \to \neg (a = f(x)))$ after normalization, and say what would go wrong without normalization.

<details><summary>Solution</summary>

Normalize $y \ge x$ to $x \le y$ and $a = f(x)$ to $f(x) = a$. With $p: x \le y$ and $q: f(x) = a$, the formula becomes $(p \lor q) \land (p \to \neg q)$, whose CNF is $(p \lor q) \land (\neg p \lor \neg q)$.

Without normalization there would be four variables, $p, q, p', q'$, and the core could assign $p$ and $p'$ differently. The theory solver would then have to find the conflict between them, and this would cost extra theory calls, although the procedure would remain correct.

</details>

3. Run the offline loop by hand on $(x \le 0 \lor x \ge 2) \land x \ge 1 \land x \le 1$ over the reals, using minimal conflict sets, and report the verdict.

<details><summary>Solution</summary>

Let $p: x \le 0$, $q: x \ge 2$, $r: x \ge 1$, $s: x \le 1$. The abstraction is $(p \lor q) \land r \land s$.

The SAT solver must assign $r$ and $s$. Suppose it returns $p, \neg q, r, s$. The core $\{x \le 0, x \ge 1\}$ gives the blocking clause $\neg p \lor \neg r$.

The clause forces $\neg p$, hence $q$, so the assignment is $\neg p, q, r, s$. The core $\{x \ge 2, x \le 1\}$ gives the blocking clause $\neg q \lor \neg s$.

Unit propagation now gives $r$, $s$, $\neg p$, $\neg q$, which falsifies $p \lor q$. The SAT solver reports unsat, so $F$ is unsatisfiable over the reals. This has been confirmed with Z3.

</details>

4. Explain why it is sound to add the conflict clause of a theory conflict to the clause set, although it is not a logical consequence of $\alpha(F)$.

<details><summary>Solution</summary>

The clause is a theory lemma: its negation is a $T$-inconsistent set of literals, so every $T$-model satisfies it. Hence $F$ and $F$ together with the clause have the same $T$-models. The clause is not entailed by $\alpha(F)$ propositionally, because the abstraction forgets the meaning of the atoms. The point of adding it is exactly to teach the abstraction some of that meaning.

</details>

5. Trace CDCL(T) on the following problem in equality logic with uninterpreted functions. The atoms are $e_1: a = b$, $e_2: b = c$, $e_3: f(a) = f(c)$, $e_4: c = d$, $e_5: f(c) = f(d)$ and $e_6: a = d$. The clauses are $(e_1 \lor e_4)$, $(e_2 \lor e_4)$, $(\neg e_3 \lor e_6)$, $(\neg e_5 \lor \neg e_4 \lor \neg e_6)$, $(\neg e_6 \lor \neg e_4 \lor e_5)$ and $(\neg e_6 \lor \neg e_1)$. Decide $e_1$ first, and use exhaustive theory propagation.

<details><summary>Solution</summary>

```
step  event     literal  level  reason
 1    decide    e1       1
 2    unit      ¬e6      1      (¬e6 ∨ ¬e1)
 3    unit      ¬e3      1      (¬e3 ∨ e6)
 4    T-prop    ¬e2      1      (¬e2 ∨ ¬e1 ∨ e3)
 5    unit      e4       1      (e2 ∨ e4)
 6    T-prop    e5       1      (e5 ∨ ¬e4)
```

Step 4 is justified as follows: from $a = b$ and $b = c$, congruence gives $f(a) = f(c)$, so $e_1$ and $\neg e_3$ entail $\neg e_2$. Step 6 follows from congruence on $c = d$.

The clause $(\neg e_5 \lor \neg e_4 \lor \neg e_6)$ is satisfied by $\neg e_6$, and all the others are satisfied. No conflict occurs. The result is sat, with $a = b$, $c = d$, $a \ne c$, and $f(a) \ne f(c)$. This has been confirmed with Z3.

</details>

6. A solver has this trail, with the decisions marked: $a^d$ at level 1, $g^d$ at level 2, $u^d$ at level 3, and $v^d$ at level 4. The theory solver, called only now, reports the conflict set $\{a, g\}$. Describe exactly what the solver does.

<details><summary>Solution</summary>

The conflict clause is $\neg a \lor \neg g$. Its highest level is 2, which is below the current level 4, so the solver first backtracks to level 2, undoing $u$ and $v$. At level 2, the clause has one literal, $\neg g$, so it is already asserting and no resolution is needed. The second-highest level is 1, so the solver backjumps to level 1 and asserts $\neg g$ with the reason $\neg a \lor \neg g$.

</details>

7. Prove that every clause learned by conflict analysis in CDCL(T) is $T$-entailed by the input formula.

<details><summary>Solution</summary>

Argue by induction on the resolution derivation of the clause, with the invariant that every clause $C$ in the current clause set satisfies $F_0 \models_T C$ when read through $\gamma$.

The clauses of the initial set satisfy this trivially. The theory conflict clauses and theory propagation reasons are $T$-valid, so they are entailed by anything. Conflict analysis starts at a conflict clause and resolves with reason clauses, each of which is either a clause of the clause set or a theory reason. Resolution is sound in propositional logic, so if $\gamma(C_1)$ and $\gamma(C_2)$ are $T$-entailed by $F_0$, so is the resolvent. The learned clause is therefore $T$-entailed, and adding it preserves the invariant.

</details>

8. Suppose an atom $p$ occurs only positively in the clause set. Prove that if $M$ is a total Boolean model of the clauses with $\neg p \in M$, then $M \setminus \{\neg p\}$ still satisfies every clause. Use this to justify not sending $\gamma(\neg p)$ to the theory solver.

<details><summary>Solution</summary>

Take a clause $C$. Since $\neg p \notin C$, by the positive-occurrence hypothesis, the literal of $C$ that $M$ makes true is different from $\neg p$. It remains true in $M \setminus \{\neg p\}$. So the partial assignment satisfies every clause.

Consequently, if $\gamma(M \setminus \{\neg p\})$ is $T$-consistent, the Proposition, in its form for partial assignments, shows that $F$ is $T$-satisfiable. Any $T$-model of that set makes $p$ either true or false, and either value keeps all the clauses true, since $p$ occurs only positively. Thus the theory solver can ignore $\gamma(\neg p)$, and doing so avoids conflicts that are irrelevant to satisfiability.

</details>

9. A theory solver's `explain` is lazy. It stores no reason when it propagates $l$ at trail position 5, and at analysis time it uses the current trail, in which literals at positions 6 and 7 also entail $l$. Explain the failure this causes and the correct rule.

<details><summary>Solution</summary>

An explanation that uses a literal at a position after $l$ creates an edge in the implication graph from a later literal to an earlier one. If the later literal was itself implied using $l$, as is possible since it follows $l$, the graph has a cycle. Conflict analysis, which walks the trail backward and resolves away literals, may then fail to terminate at a UIP, and the derived clause may not be asserting.

The correct rule is that an explanation for $l$ may only use literals earlier than $l$ on the trail. Implementations usually record a timestamp when a fact enters the theory solver and consult the state as of that time. The proof forest of [Equality and Congruence Closure](../equality-and-congruence-closure/) and the bound records in [Arithmetic](../arithmetic/) both support this.

</details>

10. Design a splitting-on-demand treatment for disequalities in linear real arithmetic. State the lemma, the new atoms and a proof that only finitely many are needed.

<details><summary>Solution</summary>

For each literal $s \ne t$, with $s, t$ linear terms, define the term $u = s - t$. The lemma is $(s = t) \lor (u < 0) \lor (u > 0)$. It is $T$-valid by trichotomy, so T-Learn would accept it apart from the condition on atoms, which is why splitting on demand is needed.

Each equality atom in the input and each disequality gives at most two new atoms, $u < 0$ and $u > 0$. The lemma adds no new disequalities, because the negations of the new atoms are non-strict inequalities, $u \ge 0$ and $u \le 0$. Each is a bound on an existing tableau term. So the number of new atoms is at most twice the number of equality atoms in the input, and the atom set remains finite, which is what the termination argument needs.

A practical refinement is to create the lemma only when the current simplex assignment gives $s$ and $t$ equal values, since otherwise the disequality already holds in the candidate model.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- State the Proposition on Boolean abstraction, and prove it.
- List the rules of Abstract DPLL Modulo Theories, with their conditions.
- Trace CDCL(T) on an unseen formula, marking levels, reasons, theory propagations and conflict clauses.
- Perform first-UIP analysis, starting from a theory conflict clause, and report the learned clause and backjump level.
- Handle a theory conflict that lies below the current level.
- Explain why explanations must be small and why they must use only earlier literals.
- Sketch the termination and correctness proof of the abstract system.

## Materials

- Nieuwenhuis, Oliveras and Tinelli, Solving SAT and SAT Modulo Theories: From an abstract Davis-Putnam-Logemann-Loveland procedure to DPLL(T), JACM 2006. Read it for the transition system and its correctness proof.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the material on moving from propositional logic to quantifier-free theories for a textbook account of the lazy procedure.
- Barrett, Sebastiani, Seshia and Tinelli, Satisfiability Modulo Theories, in the Handbook of Satisfiability. Read it for a survey of the eager and lazy approaches and of theory solvers.
- Dutertre and de Moura, A Fast Linear-Arithmetic Solver for DPLL(T), CAV 2006. Read its description of the theory solver interface, which is what a real solver expects.
- Barrett, Nieuwenhuis, Oliveras and Tinelli, Splitting on Demand in SAT Modulo Theories, LPAR 2006. Read it for theory case splits performed through the SAT core.
