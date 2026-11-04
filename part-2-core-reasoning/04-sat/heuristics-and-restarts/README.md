# Heuristics and Restarts

Part 2, Chapter 4: SAT.

## Objective

Explain watched literals, VSIDS, phase saving, restarts and clause deletion and the evidence for each.

## Why this matters

The CDCL loop in [the previous topic](../cdcl/) leaves many choices open: how to detect unit clauses, which variable to decide, which value to give it, when to restart and which learned clauses to keep. These choices separate a teaching solver from an industrial one. You will implement them in [the Chapter 9 heuristics topic](../../../part-3-building-the-engines/09-sat-solver/heuristics/), and they are where [learned heuristics](../../../part-6-ai-and-reasoning/) try to improve on hand-designed rules. Knowing the evidence behind each technique also helps you evaluate claims of improvement, which is a regular part of research and applied work in this field.

## Prerequisites

- [CDCL](../cdcl/)
- [Resolution and DPLL](../resolution-and-dpll/)

## Lesson

### Overview of the techniques

| Technique | Problem it addresses | Main source |
|---|---|---|
| Two watched literals | Propagation dominates run time and must scale to many long clauses. | Moskewicz et al., 2001. |
| VSIDS | Decisions must be cheap to compute and focused on recent conflicts. | Moskewicz et al., 2001. |
| Phase saving | Backjumps and restarts discard useful partial assignments. | Pipatsrisawat and Darwiche, 2007. |
| Restarts | Runs can get stuck in a poor region because of early decisions. | Gomes et al., 1998, and Luby et al., 1993. |
| Clause deletion by LBD | Keeping every learned clause slows propagation. | Audemard and Simon, 2009. |

The techniques interact strongly. Evidence for each one was usually collected with the others present, so a claim about one technique in isolation should be read with its experimental setup in mind.

### Two watched literals

Early solvers kept for each clause a count of false literals, or of true and false literals. Each assignment then required visiting every clause containing the variable, and each backtrack required undoing those updates. Watched literals, introduced in Chaff, avoid most of these visits.

The observation is that a clause can become unit or falsified only after all but one of its literals are false. So it is enough to monitor two non-false literals. As long as both are non-false, the clause cannot be unit or falsified, and assignments to other literals need no attention.

Each clause selects two literal positions to watch. For each literal, the solver stores a list of clauses that watch it. When a literal $l$ becomes true, the solver visits only the clauses watching $\neg l$.

```
PROPAGATE-LITERAL(p):                 # p has just become true, so ¬p is false
    for each clause c in the watch list of ¬p:
        let q be the other watched literal of c
        if q is true:
            keep c on this list; continue
        if c has a non-watched literal r that is not false:
            watch r in place of ¬p       # c moves to the watch list of r
            continue
        if q is false:
            return conflict c
        assign q true with reason c      # c is unit
```

The important invariant is the following.

Theorem 1. Suppose that literals are propagated in trail order, and that propagation of all literals on the trail has finished with no conflict. Then for every clause with watched literals $w_1, w_2$: if $w_1$ is false, then $w_2$ is true, and $w_2$ became true no later than the end of the processing of $\neg w_1$. So no clause is unit or falsified without having been handled. Backtracking to any earlier level preserves this invariant with no change to the watches.

Proof. Consider the moment at which $w_1$ becomes false and the clause is visited. Either the watch moves to a non-false literal, in which case $w_1$ is no longer watched, or the other watch $q$ is true, or $q$ is forced true as a unit. In the last two cases $w_2 = q$ is true when the visit finishes. Later assignments can only falsify unassigned literals, and $q$ stays true until a backtrack. So the invariant holds at the end of propagation.

Now consider a backtrack that removes a suffix of the trail. Suppose that $w_1$ is false after the backtrack. Then its falsification is in the kept prefix. So $\neg w_1$ was processed before the backtrack point and $w_2$ was true at or before that moment in trail order, unless the propagation was interrupted by a conflict, in which case the trail above the unprocessed literals is removed by the backjump, since a backjump always undoes at least the whole conflict level. Hence $w_2$ remains assigned and true. So the invariant still holds, and no watch needs to change.

If every clause meets the invariant, a clause with all literals false would have a false watch $w_1$ and a true $w_2$, which is impossible. A unit clause with its open literal unassigned would likewise have a false watch and a non-true partner, which is also impossible. $\square$

There are two practical consequences. Backtracking costs only the removal of assignments from the trail. Also, clauses can be visited less often when variables are assigned in a heavily conflicting region, because the watch settles on literals that are false late.

MiniSat's descendants add a blocking literal to each watch entry, which is a literal of the clause that can be tested before the clause is loaded. If it is true, the clause is skipped without a memory access to its body. Chu, Harwood and Stuckey (2009) studied this kind of cache-conscious design.

The Chaff paper reports that propagation consumes the major part of solver run time, and that the combination of its propagation and decision methods gives one to two orders of magnitude improvement on difficult benchmarks over GRASP and SATO. That figure applies to the solver as a whole and does not isolate watched literals. A careful reading gives credit for the speedup to the combined engineering.

### VSIDS

DPLL-era heuristics such as DLIS and MOMS count literal occurrences in unsatisfied clauses. They need work on each assignment, and they ignore learned information. Variable State Independent Decaying Sum (VSIDS), from Chaff, does neither.

Chaff's version keeps a counter for each literal, starting at 0. It increments the counter of each literal of a clause when that clause is added to the database, so input clauses set the starting values and learned clauses bump them afterward. Periodically, it divides all counters by a constant. The solver decides the unassigned literal with the highest counter. The term state-independent means that the score does not depend on the current assignment, so unassigning a variable does not change it.

MiniSat's version, often called EVSIDS, works on variables.

```
activity(v) := 0 for all v;   inc := 1;   decay := 0.95
on each conflict:
    for each variable v seen during conflict analysis:
        activity(v) := activity(v) + inc
    inc := inc / decay
    if any activity exceeds a large limit:
        multiply all activities and inc by a small constant
decide: pick the unassigned variable of highest activity, using a heap
```

Theorem 2. The scores of EVSIDS are proportional at all times to the scores of a scheme that multiplies all activities by $f$ after each conflict and always adds 1, where $f$ is the decay.

Proof. Let $B_t$ be the set of variables bumped at conflict $t$, for $t = 1, 2, \dots$. Under the second scheme, after conflict $T$ a variable has score $\sum_{t \le T, v \in B_t} f^{T - t}$, with the convention that the decay of conflict $t$ happens before its bump. Under EVSIDS, it has score $\sum_{t \le T, v \in B_t} f^{-(t-1)}$. The ratio of the first to the second is $f^{T - 1}$, which does not depend on $v$. $\square$

So EVSIDS is an exponential moving average, implemented by growing the increment in place of touching every variable. A variable's contribution from a conflict $k$ conflicts ago is weighted by $f^k$. With MiniSat's default of $f = 0.95$, activity has an effective memory of the order of tens of conflicts. This is why the solver concentrates on the most recent conflict region.

The evidence is mainly empirical. Chaff introduced it as a low overhead strategy within the improvements above. Biere and Fröhlich (2015) compared variants of the scoring scheme, including VMTF, and Liang et al. (2015) studied what VSIDS actually selects. Liang et al. (2016) introduced learning rate based branching as an alternative, and that work belongs to the literature covered in [Part 6](../../../part-6-ai-and-reasoning/). The scheme's exact parameters remain a tuning choice, and no theorem explains why it works so well.

### Phase saving

Once a variable is chosen, a value must be picked. Phase saving, from Pipatsrisawat and Darwiche (2007), stores the last value of each variable when it is unassigned, and reuses that value at the next decision of the variable.

The motivation is that a large formula often has nearly independent parts. A backjump to fix one part wipes out the assignments of other parts, and without phase saving the solver would have to solve those parts again. With phase saving, it restores them almost exactly, so they behave as a cached solution. Audemard and Simon (2009) note that aggressive restart strategies pay particularly when combined with phase saving.

Later solvers extended the idea. Target phases keep the assignment that reached the largest trail without a conflict, and rephasing periodically resets saved phases to give diversification. Cai, Zhang, Fleury and Biere (2022) report that these methods and local search gave a large improvement in SAT Competition 2020, as discussed in [Local Search](../local-search/).

### Restarts

A restart undoes the whole trail back to level 0 and keeps learned clauses, activities and saved phases.

The original motivation came from heavy-tailed behavior. Gomes, Selman and Kautz (1998) observed that randomized complete search has run times with very high variance, so that some runs finish quickly and others take far longer, and that restarts exploit the short runs.

Luby, Sinclair and Zuckerman (1993) analyzed restarts for Las Vegas algorithms with unknown run-time distribution. Their universal sequence is

```
1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, ...
```

defined by $t_i = 2^{k-1}$ if $i = 2^k - 1$, and $t_i = t_{i - 2^{k-1} + 1}$ if $2^{k-1} \le i < 2^k - 1$.

Their result states the following. Let $\ell$ be the expected run time of the best fixed cutoff strategy for an algorithm. The universal sequence, used with independent runs, has expected time $O(\ell \log \ell)$. No universal strategy does better by more than a constant factor in the worst case. This theorem assumes independent runs, and CDCL runs are not independent, since each run inherits clauses, activity and phases. So the theorem motivates the Luby sequence, and does not prove its optimality for CDCL. MiniSat's default is a Luby sequence with unit 100 conflicts.

Restart policies then became more aggressive. Audemard and Simon (2009) remark that the meaning of restarting has shifted from going elsewhere in the search space to something closer to reorganizing the current one, since phase saving returns the search to nearly the same assignment. The aim of a modern restart is then to bring the decisions into line with the current activity order.

Dynamic policies react to the search. Glucose (Audemard and Simon, 2012) restarts when recent learned clauses have worse LBD than the global average, using a test of this form:

$$\text{average LBD of the last 50 learned clauses} \times K > \text{average LBD of all learned clauses so far}, \quad K = 0.8.$$

It also blocks restarts when the trail is unusually long, because a long trail suggests that the solver may be close to a model. Biere and Fröhlich (2015) analyzed such schemes using exponential moving averages.

On the theoretical side, restarts are a component of the known simulation of general resolution by CDCL, described in [CDCL](../cdcl/). Whether CDCL without restarts can polynomially simulate general resolution is a well-known open question at the time of writing.

### Clause deletion

A solver learns a clause per conflict and may produce millions of them. They slow propagation, because watch lists grow, and they use memory. So solvers delete most of them. Deletion is sound, because learned clauses are implied, and a solver can derive a deleted clause again if needed. The one constraint is that a clause currently acting as a reason on the trail is locked and must not be deleted while it is one, since conflict analysis needs it.

MiniSat ranks clauses by an activity similar to VSIDS and by size, and it grows the database limit over time. Audemard and Simon (2009) introduced the literal block distance.

Definition. The literal block distance (LBD) of a clause under the current assignment is the number of distinct decision levels among its literals.

A clause of LBD 2 is called a glue clause. It has one literal of the last level and its other literals in one earlier level. After the literals of that earlier block are all false, it propagates its remaining literal, however long the clause is. So it links one block of propagations to another.

The paper's experiments on the SAT-Race 06 benchmarks with MiniSat, with a 1000-second limit, report the following.

- About 40 percent of the unit propagations on learned clauses came from glue clauses, whereas about 20 percent came from clauses of size 2.
- Half of the learned clauses used in conflict analysis had LBD below 6, whereas size only reached the same half at 13.

Its deletion policy removes half of the learned clauses every $20000 + 500x$ conflicts, where $x$ is the number of previous reductions, keeping those of lowest LBD. The paper's comparison of four MiniSat versions gives 70 solved instances for the original, 74 with aggressive deletion, 79 with LBD ranking and 82 with both. Those are numbers from one benchmark set and one solver version in 2009, so treat them as evidence for the direction of the effect.

A solver can also update a clause's LBD when the clause is used in propagation or analysis, since it can decrease as the search moves. Most later solvers rank clauses by LBD, often with separate tiers for the lowest values.

## Worked examples

A script in the scratchpad reproduced the watched-literal trace and the Luby sequence. The scores in Example 2 are simple sums, which you can recompute.

### Example 1: two watched literals, with backtracking

The watches start on the first two literals of each clause. Each visit is processed in clause order.

```
C1 = (x1 ∨ x2 ∨ x3)     C2 = (¬x1 ∨ x3 ∨ x4)    C3 = (¬x3 ∨ ¬x4 ∨ x5)
C4 = (¬x2 ∨ x5)         C5 = (¬x5 ∨ x6)         C6 = (¬x5 ∨ ¬x6 ∨ ¬x4)

Initial watches:  C1[x1,x2]  C2[¬x1,x3]  C3[¬x3,¬x4]  C4[¬x2,x5]  C5[¬x5,x6]  C6[¬x5,¬x6]

Decide ¬x2. So x2 is false.
    C1 watches x2. Its other literal x3 is unassigned, so move the watch to x3.
    Watches:  C1[x1,x3]  C2[¬x1,x3]  C3[¬x3,¬x4]  C4[¬x2,x5]  C5[¬x5,x6]  C6[¬x5,¬x6]

Decide x1. So ¬x1 is false.
    C2 watches ¬x1. Its other literal x4 is unassigned, so move the watch to x4.
    Watches:  C1[x1,x3]  C2[x3,x4]  C3[¬x3,¬x4]  C4[¬x2,x5]  C5[¬x5,x6]  C6[¬x5,¬x6]

Decide ¬x3. So x3 is false.
    C1 watches x3. The other watch x1 is true, so keep the watch.
    C2 watches x3. The other watch x4 is unassigned. No replacement exists since ¬x1 is false.
        C2 is unit, so assign x4.
Process x4. So ¬x4 is false.
    C3 watches ¬x4. The other watch ¬x3 is true, so keep the watch.
    Trail: ¬x2 x1 ¬x3 x4

Backtrack to level 1. Only the trail changes. Trail: ¬x2
    Watches:  C1[x1,x3]  C2[x3,x4]  C3[¬x3,¬x4]  C4[¬x2,x5]  C5[¬x5,x6]  C6[¬x5,¬x6]

Decide x3. So ¬x3 is false.
    C3 watches ¬x3. Its other literal x5 is unassigned, so move the watch to x5.
    Watches:  C1[x1,x3]  C2[x3,x4]  C3[¬x4,x5]  C4[¬x2,x5]  C5[¬x5,x6]  C6[¬x5,¬x6]
```

Over five assignments the solver made six clause visits and three watch moves. A counter-based solver would have updated all occurrences of each assigned variable and reversed those updates on backtracking. Clauses C4, C5 and C6 were never visited, since their watches stayed non-false.

### Example 2: EVSIDS on a CDCL run

Take Example 2 from [CDCL](../cdcl/), and compute the activity that EVSIDS would have accumulated, using $f = 0.5$ so that the increment doubles and the numbers stay simple. That run used a fixed decision rule, so the scores here show how a score would have evolved and did not guide that run. Variables at level 0 are not bumped, as in MiniSat.

The variables seen in each analysis are read off the resolution steps.

| Conflict | Clauses used | Variables bumped | Increment |
|---|---|---|---|
| 1 | C8, C5, C4 | $x_1, x_4, x_5, x_6$ | 1 |
| 2 | C11, C6, C13, C14 | $x_1, x_3, x_4, x_5$ | 2 |
| 3 | C8, C5 | $x_4, x_5, x_6$ | 4 |
| 4 | C7, C3, C16, C12 | $x_2, x_3, x_4, x_5$ | 8 |

In conflict 4 the variable $x_1$ has level 0, so it gets no bump.

```
             x1   x2   x3   x4   x5   x6
after 1       1    0    0    1    1    1
after 2       3    0    2    3    3    1
after 3       3    0    2    7    7    5
after 4       3    8   10   15   15    5
```

Variable $x_2$ first gets activity in conflict 4, and it immediately overtakes $x_1$, whose bumps are older, and $x_6$. This is the recency effect that distinguishes VSIDS from static counts.

### Example 3: LBD and restart budget

From Example 1 in [CDCL](../cdcl/):

- $C_{10} = (\neg x_4 \lor \neg x_6 \lor \neg x_1)$ has literals at levels 1, 3 and 1, so it has size 3 and LBD 2. It is a glue clause.
- $C_{12} = (\neg x_7 \lor \neg x_8 \lor \neg x_4)$ has literals at levels 2, 3 and 1, so it has size 3 and LBD 3.

Same size, different LBD. Under the LBD policy, $C_{10}$ is kept in preference to $C_{12}$, which a size-based rule cannot distinguish.

With a Luby unit of 100 conflicts, the first eight runs have budgets of 100, 100, 200, 100, 100, 200, 400 and 100 conflicts. The first seven runs together use 1200 conflicts, which is $(2^3 - 1)$ runs and $3 \cdot 2^{2} = 12$ units. In general the first $2^k - 1$ terms sum to $k \cdot 2^{k-1}$, as you check by induction in Exercise 2.

### Example 4: phase saving after a backjump

In the first conflict of Example 1 in [CDCL](../cdcl/), the backjump from level 3 to level 1 undoes $x_2, x_5, x_3, x_6, x_7, x_8, x_9$, with their last values all true. Saved phases then hold these values. Learned clause $C_{10}$ and $C_3$ then fix $\neg x_6$ and $\neg x_3$. The next decision takes $x_2$ with its saved phase true, which reconstructs level 2 exactly as before. Without phase saving and with a default of false, the solver would instead try $\neg x_2$, and it could abandon the work done at that level. In a formula where level 2 belongs to an independent part, this is the difference between keeping and discarding a solved component.

## Common mistakes

- Thinking that the watched literals must be the first two positions. Implementations often keep them there by swapping, and any two positions are correct as long as the invariant holds.
- Restoring watches on backtracking. No restoration is needed, as Theorem 1 shows, and doing so wastes the main benefit.
- Moving a watch to a false literal. The replacement must be non-false, which includes true and unassigned.
- Believing that VSIDS uses the current assignment. It is state-independent by design, and only the choice among unassigned variables looks at the assignment.
- Bumping only the variables of the learned clause and calling this MiniSat's scheme. Chaff bumps the literals of the learned clause, whereas MiniSat bumps all variables seen during analysis.
- Assuming that a decay close to 1 means fast forgetting. A decay near 1 changes scores slowly, so the memory is long.
- Applying Luby's theorem directly to CDCL. It assumes independent runs, and CDCL runs share state.
- Describing a restart as abandoning the search. Learned clauses, activities and saved phases all survive, and the search usually returns to a nearby assignment.
- Calling a clause with LBD 1 a glue clause. Such a clause has all its literals in one level, and the term glue is defined for LBD 2 in the original paper.
- Treating LBD as a fixed property of a clause. It depends on the assignment, and it can be recomputed during search.
- Deleting a clause that is a reason on the trail. Analysis may need that clause, so such clauses are locked.
- Attributing a benchmark difference to one technique when others changed too. Proper evaluation requires an ablation with all else held constant, which is covered in [the Chapter 9 benchmarking topic](../../../part-3-building-the-engines/09-sat-solver/benchmarking/).

## Exercises

### Exercise 1

State why two watched literals suffice, and why backtracking needs no watch updates.

<details><summary>Solution</summary>

A clause can become unit or falsified only after at most one literal is non-false. While two watched literals are both non-false, this has not happened, so no other change in the clause matters. When a watch becomes false, the solver looks for a replacement, and if none exists the clause is unit or falsified, or its other watch is true.

On backtracking, literals only change from assigned to unassigned, so a non-false literal stays non-false. A watch that is false after the backtrack was processed earlier, so its partner was already true by Theorem 1, and that partner remains assigned.

</details>

### Exercise 2

Compute terms 16 to 22 of the Luby sequence. Prove that the first $2^k - 1$ terms sum to $k \cdot 2^{k-1}$.

<details><summary>Solution</summary>

The sequence up to term 31 is $1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 16$. So terms 16 to 22 are $1, 1, 2, 1, 1, 2, 4$.

Let $S_k$ be the sum of the first $2^k - 1$ terms. The structure of the definition is that the first $2^k - 1$ terms consist of the first $2^{k-1} - 1$ terms, repeated once, followed by $2^{k-1}$. So $S_1 = 1$ and $S_k = 2 S_{k-1} + 2^{k-1}$. Assume that $S_{k-1} = (k - 1) 2^{k-2}$. Then $S_k = (k - 1) 2^{k-1} + 2^{k-1} = k \cdot 2^{k-1}$. For $k = 4$ this gives 32, which matches the sum of the first 15 terms.

</details>

### Exercise 3

A clause $(l_1 \lor l_2 \lor l_3 \lor l_4 \lor l_5)$ watches $l_1$ and $l_2$. The literals become false in the order $l_3, l_1, l_4, l_2$. Trace the watches, and count the visits. Compare with a counter-based solver, which updates the clause each time.

<details><summary>Solution</summary>

```
l3 false: l3 is not watched, so there is no visit.          Watches l1, l2.
l1 false: visit. l3 is false, l4 is unassigned, so move.    Watches l4, l2.
l4 false: visit. l5 is unassigned, so move.                 Watches l5, l2.
l2 false: visit. l1, l3 and l4 are false, so no replacement.
          The other watch l5 is unassigned, so the clause is unit: assign l5.
```

There are 3 visits. A counter-based solver updates the clause 4 times on the way down and 4 times on backtracking. The watched scheme does no work on backtracking.

</details>

### Exercise 4

Continue Example 1 from its final state with trail $\neg x_2, x_3$. Decide $x_4$. Trace the propagation with watches until the solver reaches a conflict.

<details><summary>Solution</summary>

```
Decide x4. So ¬x4 is false.
    C3 [¬x4, x5] watches ¬x4. The remaining literal ¬x3 is false.
        So there is no replacement, and x5 is unassigned. C3 is unit: assign x5.
Process x5. So ¬x5 is false.
    C5 [¬x5, x6] watches ¬x5. There is no other literal, and x6 is unassigned. C5 is unit: assign x6.
    C6 [¬x5, ¬x6] watches ¬x5. The other watch ¬x6 is now false.
        The remaining literal ¬x4 is false, so there is no replacement. C6 is falsified: conflict.
```

The trail at the conflict is $\neg x_2, x_3, x_4, x_5, x_6$. Clause C6 is falsified. The queue of unprocessed literals still contains $x_6$, and this does not matter because the conflict stops propagation.

</details>

### Exercise 5

Three conflicts bump $\{x_1, x_2\}$, $\{x_2, x_3\}$ and $\{x_3\}$. Compute the scores under EVSIDS with $f = 0.5$, and under the multiplicative version of Theorem 2. Check the proportion.

<details><summary>Solution</summary>

EVSIDS has increments 1, 2 and 4, so $x_1 = 1$, $x_2 = 1 + 2 = 3$ and $x_3 = 2 + 4 = 6$.

For the multiplicative version, decay then bump by 1 at each conflict:

```
after 1:  x1 = 1,     x2 = 1,     x3 = 0
after 2:  x1 = 0.5,   x2 = 1.5,   x3 = 1
after 3:  x1 = 0.25,  x2 = 0.75,  x3 = 1.5
```

The ratio is $1 : 3 : 6$ in both cases. The factor is $f^{T-1} = 0.25$, as the proof states.

</details>

### Exercise 6

A learned clause has literals at levels 9, 4, 4, 4, 2. Give its size, LBD and backjump level. Suppose that later the same literals have levels 7, 7, 7, 6, 6 under the new trail. What is its LBD now, and is it a glue clause?

<details><summary>Solution</summary>

The size is 5, the LBD is 3 for levels $\{9, 4, 2\}$, and the backjump level is 4. Under the later trail, the levels are $\{7, 6\}$, so the LBD is 2, and it is a glue clause by the definition applied to the current assignment. This is the reason solvers update LBD during search.

</details>

### Exercise 7

Prove in detail the backtracking part of Theorem 1, including the case in which a conflict interrupts propagation.

<details><summary>Solution</summary>

Let the trail be $t_1, \dots, t_m$, and let the propagation have processed up to position $p \le m$. Assume that the invariant holds in this form: for every clause and watch $w_1$ whose negation is at a processed position $j \le p$, the partner $w_2$ is true at a position before the end of the processing of $j$.

If $w_2$ was forced during the processing of $j$, it is appended at a position after $j$. It is then on the trail, and its position may be greater than $j$. It has the same level as $t_j$ or a lower one, because it was assigned while the level was that of $t_p$, the current level, and no decision is made until propagation completes. So it can be removed only together with the level of the propagation. A subtle point follows: $w_2$ may have a higher level than $\neg w_1$ only if $\neg w_1$ was assigned at an earlier level and only processed at the current level. This cannot happen with propagation to fixpoint before each decision, since all literals of earlier levels were processed at their own level.

Now backtrack to level $b$. All literals with level above $b$ are removed. If $w_1$ remains false, then $\neg w_1$ has level at most $b$. Since propagation at each earlier level completed with no conflict, or else the conflict occurred at the current level $d > b$ and only affects literals of level $d$, the literal $\neg w_1$ was processed at its own level, and the partner $w_2$ was then true at that level, so it stays.

If a conflict interrupted the propagation at level $d$, all unprocessed literals have level $d$ and are removed by the backjump, because the backjump goes to level $b < d$. So no unprocessed literal survives, and the invariant holds on the kept prefix. The case of a conflict at level 0 ends the solver, so no backtrack is needed.

</details>

### Exercise 8

Explain why Luby's optimality theorem does not imply that the Luby sequence is the best restart policy for CDCL. Name what evidence you would want instead.

<details><summary>Solution</summary>

The theorem assumes that each run of the algorithm is an independent sample from one run-time distribution. A CDCL run depends on the clauses, activities and phases of earlier runs, so the runs are neither independent nor identically distributed. Also, the theorem compares strategies when the distribution is unknown, and it gives worst-case guarantees over distributions, which may be far from those of real instances.

The evidence should be an empirical comparison of policies in one solver, with only the restart policy changed, on a large set of benchmarks, with enough time limit and variability checks, and reported per family for satisfiable and unsatisfiable instances separately. The results for Glucose-style policies and others suggest that satisfiable and unsatisfiable instances benefit from different frequencies.

</details>

### Exercise 9

Prove that deleting a learned clause that is not a reason keeps CDCL sound. Show by example why deleting a reason is a problem.

<details><summary>Solution</summary>

Soundness: every learned clause is implied by $F$. Removing an implied clause from a database leaves it equivalent to $F$, because the database still contains $F$ and only contains consequences of $F$. So the correctness argument of [CDCL](../cdcl/) applies to the new database.

Deleting a reason: take the trail in Example 1 of [CDCL](../cdcl/), just after the first backjump, where $\neg x_6@1$ has reason $C_{10}$. If $C_{10}$ is deleted and a later conflict needs to resolve on $x_6$, then analysis has no reason clause, and it cannot continue. The solver cannot treat the literal as a decision, because its level already has one. This is why solvers lock reason clauses until they are no longer reasons.

</details>

### Exercise 10

Solvers can avoid undoing the part of the trail that a restart would rebuild anyway. Given decisions $d_1, \dots, d_m$ on the trail and the unassigned variable $v$ of highest activity, design a rule for the level to which a restart should go, and justify it.

<details><summary>Solution</summary>

Go back to the lowest level $j$ such that the decision $d_{j+1}$ has activity less than that of $v$. Keep levels 1 to $j$.

The justification: all of $d_1, \dots, d_j$ have activity at least that of $v$. After a full restart, the solver decides the highest-activity variables first, and if phases are saved these give the same values. So the first decisions would repeat those of levels 1 to $j$, in some order, unless propagation changes things, and $v$ would be reached only after them. The kept prefix is what the solver would most likely build again, and keeping it saves work. This rule is known as reusing the trail, described by van der Tak, Ramos and Heule (2011). It is a heuristic, since the order of decisions can change the propagations.

</details>

### Exercise 11

Design an experiment to determine whether LBD-based deletion helps your solver. State the variables, baseline, benchmarks, and how you report the results.

<details><summary>Solution</summary>

Change only the ranking function, comparing LBD with activity-based ranking, and keep the deletion schedule, restart policy, decision heuristic and all other options fixed. Use a benchmark set from a SAT Competition, so that the instances are public and include many families. Run each configuration on the same machines, with one time limit and memory limit, and run several seeds if the solver has any randomness.

Report solved instances split into satisfiable and unsatisfiable, a PAR-2 score, a cactus plot, and a per-family breakdown, so that one family cannot dominate the result. Also report propagations per second and the average size of the database, which explain the mechanism behind any change. Publish the benchmark list and configuration, so that the result can be reproduced. Check whether differences hold up across seeds before claiming an effect.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Trace two watched literals through assignments and backtracking, and state the invariant.
- Compute EVSIDS scores for a sequence of conflicts, and prove its equivalence with multiplicative decay.
- Explain what phase saving preserves and why it combines well with restarts.
- Write the first 15 terms of the Luby sequence, and state what the theorem assumes.
- Compute LBD, and explain why glue clauses matter.
- Say which clauses may not be deleted, and why.
- Give the source and the limits of the evidence for each technique.

## Materials

- Moskewicz et al., Chaff: Engineering an Efficient SAT Solver, DAC 2001. Read it for two watched literals, VSIDS and the case that engineering matters.
- Eén and Sörensson, An Extensible SAT-solver, SAT 2003. Read it for the MiniSat design, activity heuristics and the assumption interface.
- Audemard and Simon, Predicting Learnt Clauses Quality in Modern SAT Solvers, IJCAI 2009. Read it for LBD, glue clauses and the deletion policy.
- Pipatsrisawat and Darwiche, A Lightweight Component Caching Scheme for Satisfiability Solvers, SAT 2007. Read it for the origin of phase saving.
- Luby, Sinclair and Zuckerman, Optimal Speedup of Las Vegas Algorithms, Information Processing Letters 1993. Read it for the universal sequence and its theorem.
- Gomes, Selman and Kautz, Boosting Combinatorial Search Through Randomization, AAAI 1998. Read it for heavy-tailed run times and randomized restarts.
- Audemard and Simon, Refining Restarts Strategies for SAT and UNSAT, CP 2012. Read it for dynamic restarts and blocking.
- Biere and Fröhlich, Evaluating CDCL Variable Scoring Schemes, SAT 2015. Read it for a comparison of VSIDS variants and VMTF.
- Cai, Zhang, Fleury and Biere, Better Decision Heuristics in CDCL through Local Search and Target Phases, JAIR 2022. Read it for target phases and rephasing.
- Van der Tak, Ramos and Heule, Reusing the Assignment Trail in CDCL Solvers, JSAT 2011. Read it for partial restarts.
