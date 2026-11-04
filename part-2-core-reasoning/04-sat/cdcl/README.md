# CDCL

Part 2, Chapter 4: SAT.

## Objective

Trace clause learning, implication graphs, first-UIP analysis and backjumping by hand.

## Why this matters

Conflict-driven clause learning is the algorithm inside almost every industrial SAT solver, and it is the engine that the later chapters reuse. [DPLL(T)](../../05-smt/dpllt/) wraps it around theory solvers, [bounded model checking](../../08-model-checking/bounded-model-checking/) and [IC3](../../08-model-checking/ic3-and-pdr/) call it incrementally, and [the solver you build in Chapter 9](../../../part-3-building-the-engines/09-sat-solver/cdcl-core/) implements it directly. An applied scientist often has to explain why a solver query is slow or why a proof looks the way it does, and that requires knowing exactly what the solver derives at each conflict. This topic is also the proof of mastery for the chapter.

## Prerequisites

- [Resolution and DPLL](../resolution-and-dpll/)
- [Propositional logic](../../../part-1-foundations/01-mathematical-logic/propositional-logic/)
- [Proof systems](../../../part-1-foundations/01-mathematical-logic/proof-systems/)
- [Proof complexity](../../../part-1-foundations/02-decidability-and-complexity/proof-complexity/)

## Lesson

### From DPLL to CDCL

DPLL reacts to a conflict by flipping the most recent decision that has not been flipped. This has two weaknesses. It forgets why the conflict happened, so the same combination of assignments can fail again in another part of the tree. It also backtracks chronologically, so if the conflict depends only on decisions 1 and 7, the solver still explores every remaining combination of decisions 2 to 6 before it changes decision 1.

CDCL repairs both. At each conflict it analyzes the propagation steps that caused the conflict, derives a new clause by resolution, adds that clause to the formula, and jumps back to the deepest level at which the new clause forces a literal. GRASP (Marques-Silva and Sakallah, conference version 1996, journal version 1999) introduced the implication graph, unique implication points and non-chronological backtracking driven by learned clauses. Relsat (Bayardo and Schrag, 1997) also combined learning with non-chronological backtracking. Zhang, Madigan, Moskewicz and Malik (2001) described learning schemes as cuts of the implication graph and found that the scheme based on the first UIP was the most robust of those they compared.

### Definitions

Fix a CNF formula $F$ over variables $x_1, \dots, x_n$. A CDCL state is a sequence of assignments called the trail, together with a clause database that contains $F$ and all learned clauses.

- The trail is the sequence of literals made true, in the order they were assigned.
- A decision is a literal assigned by choice rather than by propagation.
- The decision level of the state is the number of decisions on the trail. Literals assigned before the first decision have level 0.
- The level of a literal on the trail is the decision level at the moment it was assigned. The notation $x_4@1$ means that $x_4$ is true and was assigned at level 1.
- A clause is unit under the trail if all its literals are false except one, which is unassigned. Unit propagation assigns that remaining literal.
- The antecedent or reason of a propagated literal is the clause that became unit and forced it. Decisions have no reason.
- A conflict occurs when a clause has all its literals false.

### The algorithm

```
CDCL(F):
    db := F;  trail := empty;  level := 0
    loop:
        conflict := PROPAGATE()              # unit propagation to fixpoint
        if conflict exists:
            if level = 0: return UNSAT
            (C, b) := ANALYZE(conflict)      # learned clause, backjump level
            add C to db
            BACKJUMP(b)                      # undo all literals of level > b; level := b
            # C is now unit, and the next PROPAGATE assigns its open literal at level b
        else if all variables are assigned:
            return SAT with the trail as the model
        else:
            level := level + 1
            push a chosen unassigned literal on the trail as a decision
```

### Implication graphs

The implication graph at a conflict is a directed acyclic graph that records why each literal is on the trail.

- It has one node for each literal on the trail, and one extra node $\kappa$ for the conflict.
- For each propagated literal $l$ with reason $(l \lor \neg a_1 \lor \dots \lor \neg a_k)$, it has an edge from each $a_i$ to $l$.
- For the falsified clause $(\neg a_1 \lor \dots \lor \neg a_k)$, it has an edge from each $a_i$ to $\kappa$.

Decisions and literals without incoming edges are the sources. The graph is acyclic because each literal's antecedents were assigned earlier on the trail.

A cut is a partition of the nodes into a reason side, which contains all decisions, and a conflict side, which contains $\kappa$. Let $W$ be the set of reason-side nodes that have an edge into the conflict side. The cut clause is

$$C_W = \bigvee_{l \in W} \neg l.$$

Theorem 1 (cuts give implied clauses). For every cut, $F' \models C_W$, where $F'$ is the current clause database.

Proof. Suppose an assignment satisfies $F'$ and makes every literal of $W$ true. Process the conflict-side nodes in trail order. Each one has all its antecedents either in $W$ or earlier on the conflict side, so its reason clause forces it true. Finally the falsified clause has all its literals false, which contradicts the assignment satisfying $F'$. Hence no such assignment exists, so every model of $F'$ falsifies some literal of $W$ and therefore satisfies $C_W$. $\square$

Since learned clauses are themselves implied by $F$, induction on the order of learning gives $F \models C_W$.

### Unique implication points

Let $d$ be the conflict level and let $x$ be the decision of level $d$. Consider the subgraph on the level-$d$ nodes and $\kappa$.

A unique implication point (UIP) is a level-$d$ node through which every path from $x$ to $\kappa$ passes. The decision itself is always a UIP, because every path starts there, so at least one UIP exists. UIPs lie on a line from $x$ to $\kappa$ and are ordered along it. The first UIP is the one nearest to $\kappa$. Zhang et al. count from the conflict, so "first" means first encountered when walking back from $\kappa$. The decision is the last UIP.

The first-UIP cut places on the conflict side every node of level $d$ that is assigned after the first UIP and has a path to $\kappa$. All else is on the reason side.

### Conflict analysis as resolution

The first-UIP clause can be computed from the trail without building the graph. Start with the falsified clause, and keep resolving it with the reason of the most recently assigned literal whose negation occurs in the current clause, until exactly one literal of the current level remains.

```
ANALYZE(conflict):
    d := current level
    C := conflict clause
    p := last position on the trail
    while C contains more than one literal of level d:
        while the negation of trail[p] is not in C:
            p := p - 1
        l := trail[p]
        C := resolve(C, reason(l)) on the variable of l
        p := p - 1
    remove from C all literals of level 0
    if C has one literal: b := 0
    else: b := the second highest level among the literals of C
    return (C, b)
```

Each intermediate clause is the cut clause for the cut whose conflict side contains the nodes resolved so far. Therefore each clause in the sequence has every literal false under the current trail.

Theorem 2 (the loop stops at the first UIP). Assume that propagation runs to fixpoint before each decision. Then ANALYZE terminates with $C$ containing exactly one level-$d$ literal, and that literal is the negation of the first UIP.

Proof. Let $S$ be the set of level-$d$ nodes whose negations are in the current clause. By construction, each node in $S$ has a path to $\kappa$ whose interior consists only of already resolved nodes. The set $S$ also separates $x$ from $\kappa$. To see this, take any path from $x$ to $\kappa$ and its last unresolved node. Its successor is $\kappa$ or a resolved node, so it is an antecedent of that successor, it entered the clause when the successor was processed, and it has not been removed, so it is in $S$. Every level-$d$ implied node has an antecedent at level $d$, since otherwise propagation would have assigned it at a lower level, so every node in $S$ is reachable from $x$.

Let $u$ be the first UIP. Suppose that before $u$ is reached on the walk, $S$ contains a node $w$ earlier on the trail than $u$. Then $w$ has a path to $\kappa$ through resolved nodes, all later on the trail than $u$, so this path avoids $u$. Joining it to a path from $x$ to $w$ gives a path from $x$ to $\kappa$. That path avoids $u$, because all nodes on the segment from $x$ to $w$ are no later than $w$ and hence earlier than $u$. This contradicts $u$ being a UIP, so every node of $S$ is $u$ or later than $u$. If the loop stopped earlier with $S = \{w\}$ and $w$ later than $u$, then $w$ would separate $x$ from $\kappa$ and would be a UIP nearer to $\kappa$ than $u$, which is impossible. When the walk has passed all nodes later than $u$, every node of $S$ is $u$, and $S$ is not empty because it separates $x$ from $\kappa$. So $S = \{u\}$, and the loop stops. $\square$

### Asserting clauses and backjumping

A clause is asserting at a conflict of level $d$ if all its literals are false under the trail and exactly one of them has level $d$. The first-UIP clause is asserting. So is the clause for any other UIP.

Let $C = (\neg u \lor l_1 \lor \dots \lor l_k)$ be the first-UIP clause, with $\neg u$ its literal of level $d$. Let $b$ be the highest level among $l_1, \dots, l_k$, and let $b = 0$ if $k = 0$. Backjumping to level $b$ keeps every $l_i$ assigned and false and unassigns $u$. The clause is now unit, and propagation assigns $\neg u$ at level $b$. Level $b$ is the lowest level at which this happens. Jumping to any level above $b$ would also make $C$ unit, but the stricter rule gives the smallest search state from which the new literal follows.

Backjumping undoes decisions that played no part in the conflict. Those decisions may have to be made again later. Solvers keep the search close to the old state with phase saving, described in [Heuristics and Restarts](../heuristics-and-restarts/).

### Dropping literals of level 0

Literals of level 0 are false in every model of the database, because unit propagation derives their negations without decisions. A learned clause can drop them and remain implied. In proof terms, you could resolve each of them away against its level-0 reason. Example 2 below shows this step. Proof checkers verify the shorter clause with reverse unit propagation, as described in [Proofs and Certificates](../proofs-and-certificates/).

### Clause minimization

A literal $l$ of the learned clause is redundant if resolving it away against reasons gives only literals already in the clause or literals of level 0. Resolving then yields a subset of the clause. Local minimization checks one resolution step. Recursive minimization, described by Sörensson and Biere (2009), follows reasons as long as needed. The literal at the conflict level is never removed, because it is the UIP. Minimization preserves the asserting property and the backjump level can only stay the same or decrease.

### Correctness

Theorem 3 (soundness and termination). If learned clauses are never deleted and there are no restarts, CDCL terminates, it returns SAT only with a model of $F$, and it returns UNSAT only if $F$ is unsatisfiable.

Proof. Soundness for SAT: the trail assigns every variable and no clause is falsified, so all clauses are satisfied, and $F$ is a subset of the database. Soundness for UNSAT: every learned clause is implied by $F$, by induction with Theorem 1 and the remark on level 0. A conflict at level 0 means that unit propagation alone from the implied database falsifies a clause, so $F$ is unsatisfiable.

Termination: assign to each state the vector $(k_0, k_1, \dots, k_n)$, where $k_i$ is the number of literals of level $i$ on the trail. A propagation increases the entry of the current level. A decision changes the next entry from 0 to 1. A backjump to level $b$ followed by the propagation of the asserted literal keeps $k_0, \dots, k_{b-1}$ and increases $k_b$ by at least 1, and later entries may fall. So each step, with the backjump and its asserted literal taken together, makes the vector larger in lexicographic order. There are finitely many vectors because the entries sum to at most $n$. This argument is due to Nieuwenhuis, Oliveras and Tinelli (2006). $\square$

With restarts and clause deletion the vector can go down, so solvers need a further condition to guarantee termination, for example a restart interval that grows without bound and learned clauses that are kept long enough. Exercise 10 examines this.

An UNSAT run produces a resolution refutation, since every learned clause has a resolution derivation from clauses already present, and the final level-0 conflict resolves to the empty clause. The refutations are in general DAG shaped, which is why CDCL is not limited by the bounds on tree-like resolution that apply to DPLL. Pipatsrisawat and Darwiche (2011) and independently Atserias, Fichte and Thurley (2011) showed that CDCL with restarts polynomially simulates general resolution, under nondeterministic choice of decisions and restarts. Haken's lower bound for the pigeonhole principle therefore also limits CDCL, as explained in [Proof complexity](../../../part-1-foundations/02-decidability-and-complexity/proof-complexity/).

### Other learning schemes

Different cuts give different schemes. The table describes those that Zhang et al. compared.

| Scheme | Cut used |
|---|---|
| Decision | The reason side keeps only decisions, so the clause contains negated decisions alone. |
| Rel_sat | The clause keeps the decision of the current level and literals of lower levels. |
| GRASP | The solver learns more than one clause per conflict. |
| 1UIP | The cut stops at the first UIP of the conflict level and keeps literals of lower levels. |
| All UIP | The cut also moves to the first UIP of each lower level. |

The paper reports that the best new scheme gave at least a twofold speedup over the schemes used in solvers of that time, and it describes the 1UIP scheme as quite robust and effective. The experiments are from 2001 and used zChaff with VSIDS, so they are evidence about that setting. The 1UIP scheme remains the standard choice. One reason appears in the paper on literal block distance: Audemard and Simon cite a result of Jabbour and Sais that the first UIP clause has the lowest literal block distance of the UIP schemes.

### Incremental solving under assumptions

MiniSat (Eén and Sörensson, 2003) popularized the assumption interface, which later topics rely on. The caller passes literals $a_1, \dots, a_m$, and the solver uses them as its first decisions, one level each. If it finds a model, all $a_i$ are true in it. If some $a_i$ is already false when its turn comes, the formula is unsatisfiable under the assumptions. Resolving the reason of $\neg a_i$ back to decisions then gives a clause over negated assumptions, and those assumptions form an unsatisfiable core. Learned clauses stay in the database between calls, because they follow from the clauses alone. Assumption levels are ordinary levels, so a learned clause may contain assumption negations. [MaxSAT](../maxsat/) and [IC3](../../08-model-checking/ic3-and-pdr/) use this interface.

## Worked examples

All traces in this topic follow one set of rules so that you can reproduce them by hand.

- Clauses are numbered, and each learned clause receives the next number.
- After every assignment, if any clause is falsified then the lowest numbered such clause is the conflict. Otherwise the lowest numbered unit clause propagates.
- Each example states its decision rule.
- The suffix `d` marks a decision in a trail display.
- In code blocks, `κ <- a, b [C7]` means that the node has incoming edges from `a` and `b` because of clause C7.

A script in the scratchpad reproduced each trace below. It checked each learned clause for entailment by brute force, it checked the first UIP against a separate path-based computation, and it checked the final answer by enumerating all assignments.

### Example 1: a satisfiable formula with non-chronological backjumping

The decision rule is to choose the lowest numbered unassigned variable and assign it true. The formula is the following.

```
C1 = (¬x1 ∨ x4)
C2 = (¬x2 ∨ x5)
C3 = (¬x3 ∨ ¬x4 ∨ x6)
C4 = (¬x6 ∨ x7)
C5 = (¬x6 ∨ ¬x1 ∨ x8)
C6 = (¬x7 ∨ ¬x8 ∨ x9)
C7 = (¬x7 ∨ ¬x8 ∨ ¬x9 ∨ ¬x4)
C8 = (x3 ∨ ¬x5 ∨ x9)
C9 = (x3 ∨ ¬x5 ∨ ¬x9)
```

Search up to the first conflict:

```
Level 0: no unit clause.
Decide x1@1
    C1 is unit, so x4@1
Decide x2@2
    C2 is unit, so x5@2
Decide x3@3
    C3 is unit, so x6@3
    C4 is unit, so x7@3
    C5 is unit, so x8@3
    C6 is unit, so x9@3
Conflict: C7 is falsified at level 3.
Trail: x1@1d x4@1 x2@2d x5@2 x3@3d x6@3 x7@3 x8@3 x9@3
```

Implication graph at the conflict, with level 3 in full and the older literals as sources:

```
x3 is the decision of level 3
x6 <- x3@3, x4@1          [C3]
x7 <- x6@3                [C4]
x8 <- x6@3, x1@1          [C5]
x9 <- x7@3, x8@3          [C6]
κ  <- x7@3, x8@3, x9@3, x4@1   [C7]

            x4@1 ----------------------------+
              |                              |
              v                              v
 x3@3 ------> x6@3 ---> x7@3 ---+---> x9@3 --> κ
               |                |              ^
               |   x1@1         |              |
               |     |          |              |
               v     v          |              |
               x8@3 ------------+--------------+

(x7 and x8 both have edges to x9 and to κ.)
```

Every path from $x_3$ to $\kappa$ goes through $x_6$, and after $x_6$ the paths split through $x_7$ and $x_8$. Neither $x_7$ nor $x_8$ nor $x_9$ lies on all of them, since the path $x_3, x_6, x_8, \kappa$ avoids $x_7$ and $x_9$ while the path $x_3, x_6, x_7, \kappa$ avoids $x_8$ and $x_9$. So the UIPs of level 3 are $x_3$ and $x_6$, and the first UIP is $x_6$.

First-UIP analysis:

```
start          C7   (¬x7 ∨ ¬x8 ∨ ¬x9 ∨ ¬x4)        three literals at level 3
res on x9 with C6   (¬x7 ∨ ¬x8 ∨ x9)     gives (¬x7 ∨ ¬x8 ∨ ¬x4)          two at level 3
res on x8 with C5   (¬x6 ∨ ¬x1 ∨ x8)     gives (¬x7 ∨ ¬x4 ∨ ¬x6 ∨ ¬x1)    two at level 3
res on x7 with C4   (¬x6 ∨ x7)           gives (¬x4 ∨ ¬x6 ∨ ¬x1)          one at level 3, stop
```

The learned clause is $C_{10} = (\neg x_4 \lor \neg x_6 \lor \neg x_1)$. Its literals have levels 1, 3 and 1, so the backjump level is 1. Level 2 played no part in the conflict and is undone, which is the non-chronological step.

The cuts visited by the analysis are the following.

| Conflict side | Cut clause | Literals of level 3 |
|---|---|---|
| $\{\kappa\}$ | $(\neg x_7 \lor \neg x_8 \lor \neg x_9 \lor \neg x_4)$ | Three. |
| $\{x_9, \kappa\}$ | $(\neg x_7 \lor \neg x_8 \lor \neg x_4)$ | Two. |
| $\{x_8, x_9, \kappa\}$ | $(\neg x_7 \lor \neg x_6 \lor \neg x_1 \lor \neg x_4)$ | Two. |
| $\{x_7, x_8, x_9, \kappa\}$ | $(\neg x_6 \lor \neg x_1 \lor \neg x_4)$ | One, at the first UIP. |
| $\{x_6, x_7, x_8, x_9, \kappa\}$ | $(\neg x_3 \lor \neg x_1 \lor \neg x_4)$ | One, at the decision. |

The clause can also be minimized. The literal $\neg x_4$ has reason $C_1 = (\neg x_1 \lor x_4)$, and resolving gives $(\neg x_6 \lor \neg x_1)$, which is a subset of $C_{10}$. The trace below keeps the unminimized clause so that the mechanism stays visible. Minimization would not change the assignments in this example.

The search continues:

```
After backjump, trail: x1@1d x4@1
    C10 is unit, so ¬x6@1
    C3  (¬x3 ∨ ¬x4 ∨ x6) is unit, so ¬x3@1
Decide x2@2
    C2 is unit, so x5@2
    C8 (x3 ∨ ¬x5 ∨ x9) is unit, so x9@2
Conflict: C9 (x3 ∨ ¬x5 ∨ ¬x9) is falsified at level 2.
Trail: x1@1d x4@1 ¬x6@1 ¬x3@1 x2@2d x5@2 x9@2
Implication graph at level 2:
    x2 is the decision
    x5 <- x2@2             [C2]
    x9 <- ¬x3@1, x5@2      [C8]
    κ  <- ¬x3@1, x5@2, x9@2   [C9]
UIPs: x2, x5. First UIP: x5.
Analysis:
    start           C9  (x3 ∨ ¬x5 ∨ ¬x9)
    res on x9 with  C8  (x3 ∨ ¬x5 ∨ x9)   gives (x3 ∨ ¬x5)
Learn C11 = (x3 ∨ ¬x5), with levels 1 and 2. Backjump to level 1.
After backjump, trail: x1@1d x4@1 ¬x6@1 ¬x3@1
    C11 is unit, so ¬x5@1
    C2  (¬x2 ∨ x5) is unit, so ¬x2@1
Decide x7@2
Decide x8@3
    C6 is unit, so x9@3
Conflict: C7 is falsified at level 3.
Trail: x1@1d x4@1 ¬x6@1 ¬x3@1 ¬x5@1 ¬x2@1 x7@2d x8@3d x9@3
Implication graph at level 3:
    x8 is the decision
    x9 <- x7@2, x8@3       [C6]
    κ  <- x7@2, x8@3, x9@3, x4@1   [C7]
UIPs: x8 only.
Analysis:
    start           C7  (¬x7 ∨ ¬x8 ∨ ¬x9 ∨ ¬x4)
    res on x9 with  C6  (¬x7 ∨ ¬x8 ∨ x9)   gives (¬x7 ∨ ¬x8 ∨ ¬x4)
Learn C12 = (¬x7 ∨ ¬x8 ∨ ¬x4), with levels 2, 3 and 1. Backjump to level 2.
After backjump, trail: x1@1d x4@1 ¬x6@1 ¬x3@1 ¬x5@1 ¬x2@1 x7@2d
    C12 is unit, so ¬x8@2
Decide x9@3
All variables are assigned and no clause is falsified.
SAT: x1, ¬x2, ¬x3, x4, ¬x5, ¬x6, x7, ¬x8, x9
```

You can check the model against each of C1 to C9 directly.

Two features deserve attention. The second analysis produced $x_5$ as first UIP although $x_2$ was the decision, so the clause applies however $x_5$ comes to be true. The third conflict has a decision as its only UIP, which is a common situation when few propagations happen at the conflict level.

### Example 2: a complete run to UNSAT

The decision rule is to choose the lowest numbered unassigned variable and assign it false. The formula is the following.

```
C1  = (¬x1 ∨ ¬x2 ∨ ¬x5)
C2  = (¬x2 ∨ ¬x3 ∨ x5)
C3  = (x2 ∨ ¬x3 ∨ ¬x5)
C4  = (x1 ∨ x4 ∨ x5)
C5  = (x5 ∨ ¬x6)
C6  = (¬x3 ∨ ¬x4 ∨ ¬x5)
C7  = (x2 ∨ x3 ∨ ¬x5)
C8  = (¬x4 ∨ x5 ∨ x6)
C9  = (¬x1 ∨ ¬x2 ∨ x4)
C10 = (x3 ∨ x4 ∨ x6)
C11 = (x1 ∨ ¬x3 ∨ x4)
C12 = (¬x1 ∨ x2 ∨ x4)
C13 = (x3 ∨ ¬x5)
```

```
Level 0: no unit clause.
Decide ¬x1@1
Decide ¬x2@2
Decide ¬x3@3
    C7  (x2 ∨ x3 ∨ ¬x5) is unit, so ¬x5@3
    C4  (x1 ∨ x4 ∨ x5)  is unit, so x4@3
    C5  (x5 ∨ ¬x6)      is unit, so ¬x6@3
Conflict 1: C8 (¬x4 ∨ x5 ∨ x6) is falsified at level 3.
Trail: ¬x1@1d ¬x2@2d ¬x3@3d ¬x5@3 x4@3 ¬x6@3
Implication graph at level 3:
    ¬x3 is the decision
    ¬x5 <- ¬x2@2, ¬x3@3     [C7]
    x4  <- ¬x1@1, ¬x5@3     [C4]
    ¬x6 <- ¬x5@3            [C5]
    κ   <- x4@3, ¬x5@3, ¬x6@3   [C8]
UIPs: ¬x3, ¬x5. First UIP: ¬x5.
Analysis:
    start           C8  (¬x4 ∨ x5 ∨ x6)
    res on x6 with  C5  (x5 ∨ ¬x6)       gives (¬x4 ∨ x5)
    res on x4 with  C4  (x1 ∨ x4 ∨ x5)   gives (x5 ∨ x1)
Learn C14 = (x5 ∨ x1), with levels 3 and 1. Backjump to level 1, skipping level 2.

After backjump, trail: ¬x1@1d
    C14 (x5 ∨ x1)       is unit, so x5@1
    C13 (x3 ∨ ¬x5)      is unit, so x3@1
    C3  (x2 ∨ ¬x3 ∨ ¬x5) is unit, so x2@1
    C6  (¬x3 ∨ ¬x4 ∨ ¬x5) is unit, so ¬x4@1
Conflict 2: C11 (x1 ∨ ¬x3 ∨ x4) is falsified at level 1.
Trail: ¬x1@1d x5@1 x3@1 x2@1 ¬x4@1
Implication graph at level 1:
    ¬x1 is the decision
    x5  <- ¬x1@1            [C14]
    x3  <- x5@1             [C13]
    x2  <- x3@1, x5@1       [C3]
    ¬x4 <- x3@1, x5@1       [C6]
    κ   <- ¬x1@1, x3@1, ¬x4@1   [C11]
UIPs: ¬x1 only, because the edge from ¬x1 to κ bypasses all other nodes.
Analysis:
    start           C11 (x1 ∨ ¬x3 ∨ x4)
    res on x4 with  C6  (¬x3 ∨ ¬x4 ∨ ¬x5)  gives (x1 ∨ ¬x3 ∨ ¬x5)
    res on x3 with  C13 (x3 ∨ ¬x5)         gives (x1 ∨ ¬x5)
    res on x5 with  C14 (x5 ∨ x1)          gives (x1)
Learn C15 = (x1), a unit clause. Backjump to level 0.

After backjump, trail: empty
    C15 (x1) is unit, so x1@0
Decide ¬x2@1
    C12 (¬x1 ∨ x2 ∨ x4) is unit, so x4@1
Decide ¬x3@2
    C7  (x2 ∨ x3 ∨ ¬x5) is unit, so ¬x5@2
    C5  (x5 ∨ ¬x6)      is unit, so ¬x6@2
Conflict 3: C8 (¬x4 ∨ x5 ∨ x6) is falsified at level 2.
Trail: x1@0 ¬x2@1d x4@1 ¬x3@2d ¬x5@2 ¬x6@2
Implication graph at level 2:
    ¬x3 is the decision
    ¬x5 <- ¬x2@1, ¬x3@2     [C7]
    ¬x6 <- ¬x5@2            [C5]
    κ   <- x4@1, ¬x5@2, ¬x6@2   [C8]
UIPs: ¬x3, ¬x5. First UIP: ¬x5.
Analysis:
    start           C8  (¬x4 ∨ x5 ∨ x6)
    res on x6 with  C5  (x5 ∨ ¬x6)       gives (¬x4 ∨ x5)
Learn C16 = (¬x4 ∨ x5), with levels 1 and 2. Backjump to level 1.

After backjump, trail: x1@0 ¬x2@1d x4@1
    C16 (¬x4 ∨ x5)       is unit, so x5@1
    C3  (x2 ∨ ¬x3 ∨ ¬x5) is unit, so ¬x3@1
Conflict 4: C7 (x2 ∨ x3 ∨ ¬x5) is falsified at level 1.
Trail: x1@0 ¬x2@1d x4@1 x5@1 ¬x3@1
Implication graph at level 1:
    ¬x2 is the decision
    x4  <- x1@0, ¬x2@1      [C12]
    x5  <- x4@1             [C16]
    ¬x3 <- ¬x2@1, x5@1      [C3]
    κ   <- ¬x2@1, ¬x3@1, x5@1   [C7]
UIPs: ¬x2 only.
Analysis:
    start           C7  (x2 ∨ x3 ∨ ¬x5)
    res on x3 with  C3  (x2 ∨ ¬x3 ∨ ¬x5)   gives (x2 ∨ ¬x5)
    res on x5 with  C16 (¬x4 ∨ x5)         gives (x2 ∨ ¬x4)
    res on x4 with  C12 (¬x1 ∨ x2 ∨ x4)    gives (x2 ∨ ¬x1)
    drop the level-0 literal ¬x1
Learn C17 = (x2), a unit clause. Backjump to level 0.

After backjump, trail: x1@0
    C17 (x2)             is unit, so x2@0
    C1  (¬x1 ∨ ¬x2 ∨ ¬x5) is unit, so ¬x5@0
    C2  (¬x2 ∨ ¬x3 ∨ x5)  is unit, so ¬x3@0
    C5  (x5 ∨ ¬x6)        is unit, so ¬x6@0
    C8  (¬x4 ∨ x5 ∨ x6)   is unit, so ¬x4@0
Conflict 5: C9 (¬x1 ∨ ¬x2 ∨ x4) is falsified at level 0.
The formula is UNSAT.
```

The final conflict resolves to the empty clause:

```
start           C9   (¬x1 ∨ ¬x2 ∨ x4)
res on x4 with  C8   (¬x4 ∨ x5 ∨ x6)      gives (¬x1 ∨ ¬x2 ∨ x5 ∨ x6)
res on x6 with  C5   (x5 ∨ ¬x6)           gives (¬x1 ∨ ¬x2 ∨ x5)
res on x5 with  C1   (¬x1 ∨ ¬x2 ∨ ¬x5)    gives (¬x1 ∨ ¬x2)
res on x2 with  C17  (x2)                 gives (¬x1)
res on x1 with  C15  (x1)                 gives ⊥
```

Together with the four analyses above, this is a complete resolution refutation of the formula. Note the step on conflict 4 that drops $\neg x_1$: the clause $C_{17}$ follows from $(x_2 \lor \neg x_1)$ and $C_{15}$ by one more resolution, and that is why the drop is sound. Written out this way, the derived clause $C_{15}$ is used twice, so the refutation is DAG shaped and not a tree.

## Common mistakes

- Choosing the first UIP from the decision end. The first UIP is the UIP nearest to the conflict, and the decision is the last UIP.
- Treating lower-level literals as UIP candidates. UIPs are defined only on the conflict level, and lower-level literals enter the learned clause without being resolved.
- Resolving in an order other than reverse trail order. Any resolution on a false literal gives an implied clause, but the stopping argument of Theorem 2 needs reverse trail order, and another order can stop at a clause that is not the first-UIP clause or can skip the UIP.
- Stopping when the clause is short. The stopping test is that exactly one literal of the conflict level remains, whatever the length.
- Backjumping to the level just below the conflict. The target is the second highest level in the learned clause, which may be much lower.
- Backjumping to the level of the first UIP or to the lowest level in the clause. The first leaves the clause falsified, and the second can leave more than one open literal, so the clause does not propagate.
- Forgetting that the asserted literal has the backjump level. In Example 1, $\neg x_6$ has level 1 although $x_6$ was at level 3.
- Reading the learned clause as a statement about the decision alone. It contains the negation of the first UIP, and $x_6$ can become true by any route in later search.
- Putting a decision into the implication graph with incoming edges. Decisions at level $d$ have no reasons, and a node of a lower level is a source in the graph as drawn.
- Assuming learned clauses are always shorter than the clauses they come from. A resolvent can be longer than both parents, and learned clauses of hundreds of literals occur on industrial instances.
- Claiming that a level-0 conflict depends on the last decision. Level 0 has no decisions, so the conflict shows that the database, and hence $F$, is unsatisfiable.

## Exercises

### Exercise 1

Define decision level, reason, UIP and asserting clause without looking at the lesson.

<details><summary>Solution</summary>

The decision level of a state is the number of decisions on the trail. The level of a literal is the decision level at the moment it was assigned. The reason of a propagated literal is the clause that was unit and forced it. A UIP at a conflict of level $d$ is a level-$d$ node of the implication graph through which every path from the decision of level $d$ to the conflict node passes. An asserting clause at that conflict is a clause whose literals are all false under the trail, with exactly one of them at level $d$.

</details>

### Exercise 2

A solver at conflict level 9 derives clauses whose literals have the levels below. For each, say whether it is asserting and give the backjump level if it is: (a) 9, 4, 4, 2; (b) 9; (c) 9, 9, 4; (d) 9, 8, 0.

<details><summary>Solution</summary>

(a) It is asserting, and the backjump level is 4. (b) It is asserting, and the backjump level is 0. (c) It is not asserting, because two literals have level 9, so analysis must continue. (d) It is asserting after the level-0 literal is dropped, and the backjump level is 8.

</details>

### Exercise 3

Consider the following formula, with the decision rule lowest variable, value true.

```
C1 = (¬x1 ∨ x2)    C2 = (¬x2 ∨ x3)    C3 = (¬x2 ∨ x4)
C4 = (¬x3 ∨ ¬x4 ∨ x5)    C5 = (¬x5 ∨ x6)    C6 = (¬x5 ∨ ¬x6)
```

Trace up to the first conflict, list the UIPs, and give the clause that each UIP would produce.

<details><summary>Solution</summary>

```
Decide x1@1
    C1 gives x2@1, C2 gives x3@1, C3 gives x4@1, C4 gives x5@1, C5 gives x6@1
Conflict: C6 (¬x5 ∨ ¬x6) is falsified at level 1.
Graph: x2 <- x1; x3 <- x2; x4 <- x2; x5 <- x3, x4; x6 <- x5; κ <- x5, x6.
```

The UIPs are $x_5$, $x_2$ and $x_1$, in that order from the conflict. The nodes $x_3$ and $x_4$ are not UIPs, because each path can avoid one of them, and $x_6$ is not a UIP because the edge from $x_5$ to $\kappa$ bypasses it.

Resolving C6 with C5 on $x_6$ gives $(\neg x_5)$, the first-UIP clause. Continuing, resolving with C4 on $x_5$ gives $(\neg x_3 \lor \neg x_4)$, then C3 on $x_4$ gives $(\neg x_3 \lor \neg x_2)$, then C2 on $x_3$ gives $(\neg x_2)$, which is the clause for the UIP $x_2$. Resolving with C1 on $x_2$ gives $(\neg x_1)$, the clause for the decision.

</details>

### Exercise 4

Use the formula of Example 1 and make the decisions $x_3$, $x_2$, $x_1$ in that order, each with value true. Trace to the first conflict, and give the first UIP, the learned clause and the backjump level. Compare with Example 1.

<details><summary>Solution</summary>

```
Decide x3@1
Decide x2@2
    C2 gives x5@2
Decide x1@3
    C1 gives x4@3, C3 gives x6@3, C4 gives x7@3, C5 gives x8@3, C6 gives x9@3
Conflict: C7 is falsified at level 3.
Graph at level 3:
    x4 <- x1@3            [C1]
    x6 <- x3@1, x4@3      [C3]
    x7 <- x6@3            [C4]
    x8 <- x6@3, x1@3      [C5]
    x9 <- x7@3, x8@3      [C6]
    κ  <- x7@3, x8@3, x9@3, x4@3   [C7]
Analysis:
    start           C7  (¬x7 ∨ ¬x8 ∨ ¬x9 ∨ ¬x4)
    res on x9 with  C6  gives (¬x7 ∨ ¬x8 ∨ ¬x4)
    res on x8 with  C5  gives (¬x7 ∨ ¬x4 ∨ ¬x6 ∨ ¬x1)
    res on x7 with  C4  gives (¬x4 ∨ ¬x6 ∨ ¬x1)
    res on x6 with  C3  gives (¬x4 ∨ ¬x1 ∨ ¬x3)
    res on x4 with  C1  gives (¬x1 ∨ ¬x3)
Learn (¬x1 ∨ ¬x3), with levels 3 and 1. Backjump to level 1.
```

The first UIP is the decision $x_1$. The node $x_6$ is no longer a UIP, since the path from $x_1$ through $x_4$ to $\kappa$ avoids it, and $x_4$ is not a UIP because the edge from $x_1$ to $x_8$ gives a path that avoids it. The learned clause is shorter than in Example 1 and analysis needs more resolutions. This shows that the same formula gives different graphs under different decision orders, and the clause depends on the search state.

</details>

### Exercise 5

At a conflict, the trail contains $x_1@1$ as a decision, $x_2@1$ with reason $(\neg x_1 \lor x_2)$, and $x_3@1$ with reason $(\neg x_1 \lor \neg x_2 \lor x_3)$. The first-UIP clause is $(\neg x_1 \lor \neg x_3 \lor \neg x_5)$, with $x_5$ at the conflict level. Minimize the clause. State whether local minimization is enough.

<details><summary>Solution</summary>

Resolving on $x_3$ with its reason gives $(\neg x_1 \lor \neg x_2 \lor \neg x_5)$. This contains $\neg x_2$, which is not in the original clause, so one step does not yield a subset and local minimization keeps $\neg x_3$. Resolving on $x_2$ with $(\neg x_1 \lor x_2)$ gives $(\neg x_1 \lor \neg x_5)$, which is a subset. So recursive minimization removes $\neg x_3$ and the result is $(\neg x_1 \lor \neg x_5)$.

</details>

### Exercise 6

Trace CDCL on the formula below with the decision rule lowest variable, value false. Give every implication graph at the conflict level, every analysis, and the refutation of the final conflict.

```
C1  = (x3 ∨ x4 ∨ x6)
C2  = (¬x1 ∨ x3 ∨ ¬x4)
C3  = (¬x5 ∨ ¬x6)
C4  = (¬x2 ∨ ¬x5 ∨ ¬x6)
C5  = (¬x4 ∨ ¬x5)
C6  = (¬x2 ∨ x5)
C7  = (¬x3 ∨ x5 ∨ x6)
C8  = (¬x3 ∨ ¬x5 ∨ x6)
C9  = (x2 ∨ x5 ∨ ¬x6)
C10 = (¬x1 ∨ x3 ∨ ¬x5)
C11 = (x1 ∨ ¬x5 ∨ ¬x6)
C12 = (x1 ∨ x5 ∨ x6)
C13 = (¬x3 ∨ x4 ∨ ¬x6)
```

<details><summary>Solution</summary>

```
Decide ¬x1@1
Decide ¬x2@2
Decide ¬x3@3
Decide ¬x4@4
    C1  (x3 ∨ x4 ∨ x6) is unit, so x6@4
    C3  (¬x5 ∨ ¬x6)    is unit, so ¬x5@4
Conflict 1: C9 (x2 ∨ x5 ∨ ¬x6) is falsified at level 4.
Graph at level 4:
    ¬x4 is the decision
    x6  <- ¬x3@3, ¬x4@4     [C1]
    ¬x5 <- x6@4             [C3]
    κ   <- ¬x2@2, ¬x5@4, x6@4   [C9]
UIPs: ¬x4, x6. First UIP: x6.
Analysis:
    start           C9  (x2 ∨ x5 ∨ ¬x6)
    res on x5 with  C3  (¬x5 ∨ ¬x6)      gives (x2 ∨ ¬x6)
Learn C14 = (x2 ∨ ¬x6), with levels 2 and 4. Backjump to level 2.

After backjump, trail: ¬x1@1d ¬x2@2d
    C14 is unit, so ¬x6@2
    C12 (x1 ∨ x5 ∨ x6) is unit, so x5@2
    C5  (¬x4 ∨ ¬x5)    is unit, so ¬x4@2
    C1  (x3 ∨ x4 ∨ x6) is unit, so x3@2
Conflict 2: C8 (¬x3 ∨ ¬x5 ∨ x6) is falsified at level 2.
Graph at level 2:
    ¬x2 is the decision
    ¬x6 <- ¬x2@2            [C14]
    x5  <- ¬x1@1, ¬x6@2     [C12]
    ¬x4 <- x5@2             [C5]
    x3  <- ¬x4@2, ¬x6@2     [C1]
    κ   <- x3@2, x5@2, ¬x6@2    [C8]
UIPs: ¬x2, ¬x6. First UIP: ¬x6.
Analysis:
    start           C8  (¬x3 ∨ ¬x5 ∨ x6)
    res on x3 with  C1  (x3 ∨ x4 ∨ x6)   gives (¬x5 ∨ x6 ∨ x4)
    res on x4 with  C5  (¬x4 ∨ ¬x5)      gives (¬x5 ∨ x6)
    res on x5 with  C12 (x1 ∨ x5 ∨ x6)   gives (x6 ∨ x1)
Learn C15 = (x6 ∨ x1), with levels 2 and 1. Backjump to level 1.

After backjump, trail: ¬x1@1d
    C15 is unit, so x6@1
    C3  (¬x5 ∨ ¬x6) is unit, so ¬x5@1
    C6  (¬x2 ∨ x5)  is unit, so ¬x2@1
Conflict 3: C9 (x2 ∨ x5 ∨ ¬x6) is falsified at level 1.
Graph at level 1:
    ¬x1 is the decision
    x6  <- ¬x1@1            [C15]
    ¬x5 <- x6@1             [C3]
    ¬x2 <- ¬x5@1            [C6]
    κ   <- ¬x2@1, ¬x5@1, x6@1   [C9]
UIPs: ¬x1, x6. First UIP: x6.
Analysis:
    start           C9  (x2 ∨ x5 ∨ ¬x6)
    res on x2 with  C6  (¬x2 ∨ x5)       gives (x5 ∨ ¬x6)
    res on x5 with  C3  (¬x5 ∨ ¬x6)      gives (¬x6)
Learn C16 = (¬x6), a unit clause. Backjump to level 0.

After backjump, trail: empty
    C16 is unit, so ¬x6@0
    C15 is unit, so x1@0
Decide ¬x2@1
Decide ¬x3@2
    C1  (x3 ∨ x4 ∨ x6) is unit, so x4@2
Conflict 4: C2 (¬x1 ∨ x3 ∨ ¬x4) is falsified at level 2.
Graph at level 2:
    ¬x3 is the decision
    x4  <- ¬x3@2, ¬x6@0     [C1]
    κ   <- x1@0, ¬x3@2, x4@2    [C2]
UIPs: ¬x3 only.
Analysis:
    start           C2  (¬x1 ∨ x3 ∨ ¬x4)
    res on x4 with  C1  (x3 ∨ x4 ∨ x6)   gives (¬x1 ∨ x3 ∨ x6)
    drop the level-0 literals ¬x1 and x6
Learn C17 = (x3), a unit clause. Backjump to level 0.

After backjump, trail: ¬x6@0 x1@0
    C17 is unit, so x3@0
    C7  (¬x3 ∨ x5 ∨ x6) is unit, so x5@0
Conflict 5: C8 (¬x3 ∨ ¬x5 ∨ x6) is falsified at level 0.
The formula is UNSAT.
Final refutation:
    start           C8  (¬x3 ∨ ¬x5 ∨ x6)
    res on x5 with  C7  (¬x3 ∨ x5 ∨ x6)  gives (¬x3 ∨ x6)
    res on x3 with  C17 (x3)             gives (x6)
    res on x6 with  C16 (¬x6)            gives ⊥
```

The jump from level 4 to level 2 at conflict 1 is non-chronological, because level 3 has no literal in the learned clause. The literal $\neg x_3@3$ did reach the graph as an antecedent of $x_6$, but the first UIP is $x_6$, so $\neg x_3$ stays behind the cut and does not enter the clause.

</details>

### Exercise 7

Run the formula of Exercise 3 under the single assumption $x_1$, treating the assumption as the first decision. Continue until the solver reports a result, and give the core.

<details><summary>Solution</summary>

The first conflict gives $C_7 = (\neg x_5)$ and a backjump to level 0, where $\neg x_5@0$ is assigned. The assumption $x_1$ is decided again at level 1.

```
Decide x1@1
    C1 gives x2@1, C2 gives x3@1, C3 gives x4@1
Conflict: C4 (¬x3 ∨ ¬x4 ∨ x5) is falsified at level 1.
Analysis:
    start           C4  (¬x3 ∨ ¬x4 ∨ x5)
    res on x4 with  C3  (¬x2 ∨ x4)    gives (¬x3 ∨ x5 ∨ ¬x2)
    res on x3 with  C2  (¬x2 ∨ x3)    gives (x5 ∨ ¬x2)
    drop the level-0 literal x5
Learn C8 = (¬x2). Backjump to level 0.
    C8 gives ¬x2@0, and C1 (¬x1 ∨ x2) gives ¬x1@0.
```

The assumption $x_1$ is now false at level 0, so the solver reports unsatisfiable under the assumption. The core is $\{x_1\}$. The formula without assumptions is satisfiable, for example with $x_1$ and $x_2$ false, $x_3$ true, $x_4$ false, $x_5$ false and $x_6$ true.

</details>

### Exercise 8

Prove that every clause learned by ANALYZE, including after level-0 literals are dropped, is implied by $F$.

<details><summary>Solution</summary>

Use induction on the number of learned clauses. Suppose that all clauses in the database are implied by $F$. Each step of ANALYZE resolves two clauses of the database or an intermediate clause with a clause of the database. Resolution is sound, so each intermediate clause is implied by $F$.

Now let $l$ be a literal of level 0 in the clause. Its negation $\neg l$ is on the trail at level 0, so unit propagation from the database derives $\neg l$ without any decision. Unit propagation is sound, and the database is implied by $F$, so $F \models \neg l$. If $F \models C \lor l$ and $F \models \neg l$, then $F \models C$. Repeating for every level-0 literal shows that the final clause is implied by $F$.

</details>

### Exercise 9

Prove that if propagation runs to fixpoint before each decision, a first-UIP clause learned at a conflict is not already in the clause database.

<details><summary>Solution</summary>

Let the clause be $C = (\neg u \lor l_1 \lor \dots \lor l_k)$, with $u$ at the conflict level $d$ and each $l_i$ false at a level of at most $b < d$. Suppose that $C$ was already in the database when level $b$ propagation finished. At that point all $l_i$ were false. If $u$ was unassigned at that point, $C$ was unit, so propagation would have assigned $\neg u$ at a level of at most $b$. This contradicts $u$ being true. If $u$ was already assigned at that point, its level is at most $b$, which contradicts level $d > b$. So $C$ was not in the database. The case $k = 0$ is the same with $b = 0$.

</details>

### Exercise 10

Show that CDCL may fail to terminate if it restarts after every conflict and deletes every learned clause at each restart. Give a condition that restores termination.

<details><summary>Solution</summary>

Take a deterministic decision rule, for example lowest variable with a fixed value. Suppose the first conflict occurs after some sequence of decisions and propagations. The solver learns a clause, restarts and deletes it, so its state is identical to the initial state. The deterministic rule repeats the same decisions and the same conflict, and this continues forever on a satisfiable or unsatisfiable formula alike, provided at least one conflict occurs on the first descent. Example 1 has this behavior.

Termination is restored if the number of conflicts allowed between restarts grows without bound and the clauses learned during a run are kept until the next run ends. Then eventually a single run is long enough to finish. A run without restarts or deletion terminates by Theorem 3, and its length is bounded in terms of $n$, since the lexicographic measure is bounded. If the conflict limit exceeds that bound, the run ends with SAT or UNSAT.

Keeping all learned clauses is a second sufficient condition with a fixed interval: each conflict adds a clause that was not in the database by Exercise 9, and there are finitely many clauses over $n$ variables, so only finitely many conflicts can occur.

</details>

### Exercise 11

For the first conflict of Example 1, compare the 1UIP clause with the decision clause $(\neg x_3 \lor \neg x_1 \lor \neg x_4)$. After backjumping to level 1 with each clause, list what propagation derives. Then explain which clause you would rather keep, and give an argument based on the search that follows.

<details><summary>Solution</summary>

With the 1UIP clause $C_{10}$, propagation at level 1 derives $\neg x_6$, and then $\neg x_3$ from $C_3$, as in the trace.

With the decision clause, propagation at level 1 derives $\neg x_3$. Since $C_3 = (\neg x_3 \lor \neg x_4 \lor x_6)$ is then satisfied, nothing forces $x_6$. The literal $\neg x_6$ is not derived, and the solver can decide $x_6$ true at a later level. With $x_6$ true, $C_4$ and $C_5$ force $x_7$ and $x_8$, $C_6$ forces $x_9$, and $C_7$ is falsified, so the same conflict can occur again in a different form.

The 1UIP clause is the better choice in this state. It resolves with $C_3$ on $x_6$ to give the decision clause, so the decision clause is implied by the 1UIP clause together with $C_3$. After the backjump, propagation with the 1UIP clause derives both $\neg x_6$ and $\neg x_3$, whereas propagation with the decision clause derives only $\neg x_3$. The 1UIP clause rules out $x_6$ under $x_1$ and $x_4$ regardless of how $x_6$ comes to be true, whereas the decision clause speaks only of $x_3$.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write the CDCL loop and ANALYZE from memory.
- Build the implication graph for any conflict, including edges from lower levels.
- List all UIPs of the conflict level and identify the first.
- Derive the first-UIP clause by resolution in reverse trail order, and state the backjump level.
- Continue a trace through several conflicts, including learned unit clauses and level-0 literals, until SAT or UNSAT.
- Extract the resolution refutation from an UNSAT run.
- Prove Theorem 1, Theorem 2 and the termination part of Theorem 3.
- Explain why the first-UIP clause is new and why it propagates after the backjump.

## Materials

- Marques-Silva and Sakallah, GRASP: A Search Algorithm for Propositional Satisfiability, IEEE Transactions on Computers 1999. Read it for the original implication graph, UIPs and non-chronological backtracking.
- Biere, Heule, van Maaren and Walsh (editors), Handbook of Satisfiability, 2nd edition. Read the material on conflict-driven clause learning for a standard reference treatment.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the treatment of propositional decision procedures for a textbook presentation of the same algorithm with more examples.
- Zhang, Madigan, Moskewicz and Malik, Efficient Conflict Driven Learning in a Boolean Satisfiability Solver, ICCAD 2001. Read it for learning schemes as cuts and the comparison that favored 1UIP.
- Nieuwenhuis, Oliveras and Tinelli, Solving SAT and SAT Modulo Theories: From an Abstract Davis-Putnam-Logemann-Loveland Procedure to DPLL(T), JACM 2006. Read it for the transition-system view and the termination argument.
- Sörensson and Biere, Minimizing Learned Clauses, SAT 2009. Read it for recursive clause minimization.
- Pipatsrisawat and Darwiche, On the Power of Clause-Learning SAT Solvers as Resolution Engines, Artificial Intelligence 2011. Read it for the simulation of general resolution by CDCL with restarts.
