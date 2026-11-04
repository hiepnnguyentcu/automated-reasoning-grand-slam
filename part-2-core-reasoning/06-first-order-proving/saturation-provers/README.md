# Saturation Provers

Part 2, Chapter 6: First-Order Proving.

## Objective

Explain the given-clause loop and redundancy elimination in Vampire and E.

## Why this matters

A sound and complete calculus is only the start. A prover has to organize a search whose clause set can grow by millions, and most of the engineering of Vampire and E exists to control that growth. Understanding the loop tells you why a proof attempt stalled, why a small change in an encoding can make a problem easy or hopeless, and why a time-out says nothing about satisfiability. The hand trace in this topic is the proof of mastery for the chapter. The same ideas return in [machine learning for reasoning](../../../part-6-ai-and-reasoning/17-machine-learning-for-reasoning/), where learned heuristics choose the given clause, and in [proof assistants](../../../part-4-remaining-methods/12-proof-assistants/), where tools such as Isabelle's Sledgehammer call external saturation provers.

## Prerequisites

- [First-Order Resolution](../first-order-resolution/) for saturation, redundancy and the three outcomes of a fair search.
- [Term Rewriting](../term-rewriting/) for KBO and LPO.
- [Superposition](../superposition/) for the inference rules and for demodulation.

## Lesson

### Pipeline

A prover usually proceeds in three stages. Preprocessing turns the input formulas into clauses. Saturation searches for $\bot$. Output reports the status and, on success, a proof.

Kovács and Voronkov list about twenty preprocessing steps in Vampire, including the optional selection of a relevant subset of formulas, removal of if-then-else and let-in connectives, pure predicate elimination, naming of subformulas, Skolemization and conversion to clause form. Naming is the first-order version of the Tseitin transformation: it replaces a subformula by a new predicate, which prevents exponential growth of clause form. It changes the signature, so the output is equisatisfiable with the input. Relevance selection matters for large theories, and the SInE method by Hoder and Voronkov is a well-known approach.

### Fairness and what a run proves

An inference process is a sequence of clause sets $S_0, S_1, \ldots$ where each step adds the conclusion of an inference, or deletes a clause redundant in the current set. A clause is persistent if it is in every $S_j$ from some point on. The process is fair if every inference with persistent premises is performed at some step.

Theorem (Bachmair and Ganzinger, in the form given by Kovács and Voronkov). Let $S_0, S_1, \ldots$ be a fair superposition process. Then $S_0$ is unsatisfiable if and only if some $S_i$ contains $\bot$.

There are three possible scenarios for a fair run on $S_0$.

| Outcome | What the prover saw | What it proves |
|---|---|---|
| Refutation | $\bot$ was derived. | The input is unsatisfiable. |
| Finite saturation | No unprocessed clause remains and nothing non-redundant was discarded. | The input is satisfiable. |
| Infinite run | The search never finishes. | The input is satisfiable, and this can never be observed. |

In practice the last row is replaced by a time-out or an out-of-memory result, which proves nothing. If a prover discards a non-redundant clause, as it may under a weight limit, a finite saturation also proves nothing, and the honest answer is unknown. As Kovács and Voronkov note, Vampire reports this distinction: it never reports satisfiability after a weight limit has been active.

### The given-clause idea

Given a large set, a prover cannot try all inferences in an arbitrary order and remain fair and efficient. Given-clause algorithms solve this by selecting clauses instead of inferences. The kept clauses split into two sets.

- Active clauses have been selected. All inferences among active clauses have been performed.
- Passive clauses are waiting to be selected. They take no part in generating inferences.

At each step the prover selects a passive clause, called the given clause, moves it to active, and performs all generating inferences between it and the active set, including inferences with itself. The conclusions become new passive clauses.

Invariant. After each iteration, every inference with premises in the active set has been performed, or its premises were later removed as redundant.

This gives a clean criterion: when the passive set is empty, the active set is saturated up to redundancy. If $\bot$ is not derived and no non-redundant clause was discarded, the input is satisfiable. The term "given clause" is due to McCune's Otter, as Kovács and Voronkov note.

### Generating and simplifying inferences

Inferences are of two kinds.

- A generating inference adds a conclusion and keeps its premises. Superposition, equality resolution and equality factoring are generating.
- A simplifying inference makes a premise redundant, so that the prover can replace it. Demodulation, subsumption resolution and deletion of trivial literals are simplifying. Subsumption and tautology deletion are deletion rules.

The principle stated by Kovács and Voronkov is to apply simplifying inferences eagerly and generating inferences lazily. Simplification reduces the search space without any loss. Generating inferences grow it, so they wait for selection.

Simplification occurs in two directions.

- Forward simplification reduces a new clause using existing clauses. A clause that becomes redundant is thrown away at this point.
- Backward simplification reduces existing clauses using a new clause. A changed clause returns to the passive set, because it can now have new inferences.

### The Otter loop

The Otter loop uses all kept clauses for simplification, both active and passive.

```
otter(input):
    active := {}
    passive := {}
    process_new(each input clause)
    while passive is not empty:
        given := select(passive)
        move given from passive to active
        for each conclusion of generating inferences between given and active:
            process_new(conclusion)
    return satisfiable, if nothing non-redundant was discarded, else unknown

process_new(C):
    forward simplify C with active and passive
    if C is empty: return unsatisfiable
    if C is a tautology, or is subsumed by active or passive: discard it
    backward simplify active and passive with C
    add C to passive
```

This keeps all kept clauses inter-reduced, and the price is that simplification cost rises with the size of the passive set. Kovács and Voronkov remark that the number of active clauses can be less than 1% of the number of passive ones, so the simplification cost can dominate.

### The DISCOUNT loop

The DISCOUNT loop keeps passive clauses truly passive. It simplifies only with active clauses.

```
discount(input):
    active := {}
    passive := input
    while passive is not empty:
        given := select(passive)
        remove given from passive
        forward simplify given with active
        if given is empty: return unsatisfiable
        if given is a tautology or is subsumed by active: continue
        for each clause D in active that given subsumes or simplifies:
            remove D from active
            if D was simplified, add the result to passive
        add given to active
        for each conclusion C of generating inferences between given and active:
            cheaply simplify C with active
            if C is empty: return unsatisfiable
            if C is not a tautology, add C to passive
    return satisfiable, if nothing non-redundant was discarded, else unknown
```

| Clause set | Otter loop and limited resource strategy | DISCOUNT loop |
|---|---|---|
| Active | It takes part in generating inferences and simplifies new clauses. | It takes part in generating inferences and simplifies new and reactivated clauses. |
| Passive | It simplifies new clauses. | It takes no part in any inference. |
| New | It is simplified by active and passive clauses. | It is simplified by active clauses. |

The DISCOUNT loop processes clauses faster and needs less memory for indexes. It can miss a useful simplification from a passive clause, and it can repeat a simplification when a clause is finally selected. Kovács and Voronkov report that E and Waldmeister implement the DISCOUNT algorithm, and that Vampire offers all three of Otter, DISCOUNT and limited resource strategy. The E documentation also describes its proof procedure as a DISCOUNT-loop variant.

### Clause selection

The choice of given clause is the most important heuristic. Two criteria appear everywhere.

- Age prefers the oldest clause. Selecting by age alone is a breadth-first search, and it is fair, because any clause waits only for finitely many older clauses.
- Weight prefers the lightest clause, where weight usually counts symbols. Lighter clauses tend to have fewer consequences and are more likely to simplify others. Selecting by weight alone is fair over a finite signature, because only finitely many clauses up to renaming have a given weight. Its behaviour can be poor in practice, because a clause just above a stream of lighter clauses waits a long time.

Vampire mixes the two with two priority queues and an age-weight ratio $(a, w)$. Out of each $a + w$ selections, $a$ come from the age queue and $w$ from the weight queue. E uses clause evaluation heuristics that can combine several parameterized functions with priority schemes, for example preferring clauses derived from the conjecture, in the spirit of the set of support strategy. Its automatic mode picks one of a fixed set of strategies from features of the problem. The E 1.2pre release notes mention about 40 strategies, and this number has probably changed since that release. Learned heuristics such as ENIGMA for E belong to Chapter 17.

### Other heuristic parameters

Three more parameters have a large effect.

- Term ordering. Vampire uses KBO. E supports parameterized KBO and LPO. The precedence can be derived from symbol frequency, arity or order in the input.
- Literal selection. E and Vampire provide many selection functions. Reger, Suda, Voronkov and Hoder introduce lookahead selection, which selects the literal expected to take part in the fewest inferences. They also argue that incomplete selection strategies are useful: experimental evaluation in Vampire shows that lookahead and incomplete selection contribute to solving hard problems unsolved by other methods. A prover that uses such a strategy cannot report satisfiability from an exhausted search.
- Portfolio. Provers often run a schedule of strategies, because no single strategy dominates.

### Limited resource strategy

The limited resource strategy is a variation of the Otter loop that applies when a time limit is set. It estimates how many clauses can be processed before the limit, identifies passive and unprocessed clauses that cannot be reached, and discards them, by adaptively changing a weight limit. It is implemented in Vampire, and Kovács and Voronkov describe it as generally the best saturation algorithm in Vampire at that time.

Such a discarded clause need not be redundant. Unreachability is a different concept from redundancy: it makes sense only relative to a time limit, and it sacrifices completeness for practical power. A search exhausted under this strategy cannot establish satisfiability.

### Term indexing

A prover must quickly answer questions such as these: which active clauses unify with this subterm, which unit equations match this subterm, and which clauses are subsumed by this new clause. Doing this by linear scans would dominate the running time, so all such operations use indexes. A retrieval is called perfect if it returns exactly the matching terms, and non-perfect if it returns a superset that must be checked.

| Index | Query type | Use |
|---|---|---|
| Perfect discrimination tree | It supports matching on a tree of flattened terms. | E uses it for forward rewriting and unit subsumption. |
| Fingerprint index | It is a non-perfect filter based on term samples at chosen positions. | E uses it for backward rewriting and superposition. |
| Feature vector index | It is a non-perfect filter based on clause features. | E uses it for subsumption and contextual literal cutting. |
| Code tree | It compiles a set of terms into an abstract machine for retrieval. | It was developed by Voronkov for Vampire. |

Because subsumption checking is NP-complete, as Kovács and Voronkov note, filtering through an index is essential. E stores terms in a shared term bank so that each distinct term is represented once, and caches rewrite results. Kovács and Voronkov also state that Vampire implements all unification-related operations through term indexing, so it does not run a stand-alone unification algorithm on most clause pairs.

### Reading results

The [TPTP library](https://www.tptp.org/) provides standard benchmark problems and input formats. Provers report results with the SZS status ontology. A status of Theorem means that the conjecture follows from the axioms, Unsatisfiable means that the clause set has no model, Satisfiable and CounterSatisfiable mean that a model exists, and GaveUp or Timeout mean that nothing was established. CASC is the annual competition that evaluates provers on TPTP problems. A saturation proof can be read as a tree: each clause lists its parents and rule, and the proof is short because it contains only the ancestors of $\bot$.

### Comparison with other approaches

Saturation and SMT instantiation have complementary strengths. An SMT solver is strong on ground reasoning with theories, and it handles quantifiers by [instantiation](../../05-smt/quantifiers/). A saturation prover is strong on pure first-order reasoning, because inferences on nonground clauses cover many instances at once, while arithmetic and other theories are harder. Kovács and Voronkov state that standard superposition provers have little support for theory reasoning, and that Vampire added built-in integers, reals and arrays through a mixture of inference support and axiomatization. Reasoning that combines first-order logic with linear arithmetic is highly undecidable in general, so such support cannot be complete. Vampire's AVATAR architecture, by Voronkov, uses a SAT solver to split clauses into variable-disjoint components, which brings the case analysis of SAT solving into saturation.

The theory underlying all of these variants has been made uniform by Waldmann, Tourret, Robillard and Blanchette, whose saturation framework separates the calculus from the loop, and which has been formalized in Isabelle.

## Worked examples

The convention below holds in all traces, unless an example says otherwise.

- The loop is the DISCOUNT loop.
- The ordering is KBO with all weights equal to 1.
- The weight of a clause counts function, predicate and variable occurrences, without counting $\top$.
- Selection takes the lightest passive clause, with the oldest first on ties.
- Trivial literals $t \not\approx t$ and duplicate literals are removed immediately after each inference.
- `x1` stands for $x_1$, `·` is a binary operation, `≈` and `≉` are $\approx$ and $\not\approx$.

A short script checked these traces against an implementation of the loop, and z3 confirmed each proof step and the unsatisfiability of the input where relevant.

### Example 1: a complete run on an equational problem

Prove that in a monoid a left inverse of $a$ equals a right inverse of $a$. Use the precedence $\cdot > a > l > r > e$, with no selection function.

```
Input
[1] e·x1 ≈ x1                         weight 4
[2] x1·e ≈ x1                         weight 4
[3] (x1·x2)·x3 ≈ x1·(x2·x3)           weight 10
[4] l·a ≈ e                           weight 4
[5] a·r ≈ e                           weight 4
[6] l ≉ r                             weight 2
```

The run goes as follows.

```
Given [6] l ≉ r, weight 2
    Active is empty, and nothing is generated.

Given [1] e·x1 ≈ x1, weight 4
    No overlap with [6]. Self-overlap at the root is blocked by condition 6.

Given [2] x1·e ≈ x1, weight 4
    Overlap with [1] at the root is the same literal after the mgu,
    so condition 6 blocks it.

Given [4] l·a ≈ e, weight 4
    No overlap with [1], [2] or [6].

Given [5] a·r ≈ e, weight 4
    No overlap, since a·r does not unify with l·a, e·x1 or x1·e.

Given [3] (x1·x2)·x3 ≈ x1·(x2·x3), weight 10
    Simplification does nothing.
    Generating inferences, all into position 1 of the left side unless noted:
    [7]  x1·x2 ≈ e·(x1·x2)              [1] into [3], mgu {x1 ↦ e}
    [8]  x1·x2 ≈ x1·(x2·e)              [2] into [3] at the root, x3 ↦ e
    [9]  x1·x2 ≈ x1·(e·x2)              [2] into [3], x2 ↦ e
    [10] e·x1 ≈ l·(a·x1)                [4] into [3], x1 ↦ l, x2 ↦ a
    [11] e·x1 ≈ a·(r·x1)                [5] into [3], x1 ↦ a, x2 ↦ r
    [12] (x1·(x2·x3))·x4 ≈ (x1·x2)·(x3·x4)    [3] into [3]

Given [7], weight 8
    Subsumed by [1] with {x1 ↦ x1·x2}. Discard it.

Given [8], weight 8
    Demodulate x2·e with [2] to get x1·x2 ≈ x1·x2, a tautology. Discard it.

Given [9], weight 8
    Demodulate e·x2 with [1] to get x1·x2 ≈ x1·x2, a tautology. Discard it.

Given [10], weight 8
    Demodulate e·x1 with [1] to get [15] x1 ≈ l·(a·x1).
    Generating inferences with active:
    [16] l·a ≈ e                        [2] into [15], x1 ↦ e, position of a·x1
    [17] l·e ≈ r                        [5] into [15], x1 ↦ r, position of a·x1
    [18] x1·x2 ≈ l·((a·x1)·x2)          [15] into [3]

Given [16], weight 4
    Subsumed by [4]. Discard it.

Given [17] l·e ≈ r, weight 4
    Generating inferences with active:
    [19] r ≈ l                          [17] into [2], x1 ↦ l, since l·e ≈ l is above l·e ≈ r
    [20] r·x1 ≈ l·(e·x1)                [17] into [3]

Given [19] r ≈ l, weight 2
    Since l > r in the precedence, this is the rule l → r.
    Backward simplify [6]: l ≉ r becomes r ≉ r, which gives [21] ⊥.
    Backward simplify [4], [15] and [17] as well, and add their results to passive.

Given [21] ⊥
    Stop. The input is unsatisfiable.
```

The proof is the ancestor tree of $\bot$.

```
[4]  l·a ≈ e                           input
[3]  (x1·x2)·x3 ≈ x1·(x2·x3)           input
[10] e·x1 ≈ l·(a·x1)                   superposition of [4] into [3]
[1]  e·x1 ≈ x1                         input
[15] x1 ≈ l·(a·x1)                     demodulation of [10] with [1]
[5]  a·r ≈ e                           input
[17] l·e ≈ r                           superposition of [5] into [15]
[2]  x1·e ≈ x1                         input
[19] r ≈ l                             superposition of [17] into [2]
[6]  l ≉ r                             input
[21] ⊥                                 demodulation of [6] with [19]
```

This trace produced 24 clauses in total. The same problem run with age-only selection took 45, and alternating between weight and age took 31, in the implementation used for checking. These counts illustrate the sensitivity of the search, and they say nothing general about the heuristics.

### Example 2: a Horn problem with selection

Use the precedence $P > Q > h > g > f > a$, and select a negative literal of greatest weight, if the clause has one. Prove the goal $h(g(f(a))) \approx h(f(a))$ from the assumptions in clauses 1 to 3.

```
[1] ¬P(x1) ∨ Q(f(x1))         weight 5
[2] ¬Q(x1) ∨ g(x1) ≈ x1       weight 5
[3] P(a)                      weight 2
[4] h(g(f(a))) ≉ h(f(a))      weight 7
```

The run goes as follows.

```
Given [3] P(a), weight 2.
    Active is empty, and nothing is generated.
Given [1] ¬P(x1) ∨ Q(f(x1)), weight 5, with ¬P(x1) selected.
    [5] Q(f(a))                Res on [3] and [1], mgu {x1 ↦ a}.
Given [5] Q(f(a)), weight 3.
    No inference: [2] is not active yet.
Given [2] ¬Q(x1) ∨ g(x1) ≈ x1, weight 5, with ¬Q(x1) selected.
    [6] g(f(a)) ≈ f(a)         Res on [5] and [2], mgu {x1 ↦ f(a)}.
Given [6] g(f(a)) ≈ f(a), weight 5.
    Backward simplification finds nothing in active.
Given [4], weight 7.
    Demodulate with [6]: g(f(a)) becomes f(a), giving h(f(a)) ≉ h(f(a)).
    Removing the trivial literal gives ⊥. Stop.
```

Selection forces this problem into a forward-chaining style. Without selection the maximal positive literal of each clause would take part first.

### Example 3: saturation that proves satisfiability

Run the loop on $\{f(f(x_1)) \approx f(x_1),\ g(f(x_1)) \approx x_1\}$, with the precedence $g > f$.

```
Given [2] g(f(x1)) ≈ x1, weight 4.
    Nothing is generated.
Given [1] f(f(x1)) ≈ f(x1), weight 5.
    [3] g(f(x1)) ≈ f(x1)       [1] into [2], mgu {x1 ↦ f(x2)}, since g(f(f(x2))) rewrites to
                               g(f(x2)) on the left and x1 = f(x2) on the right.
    A self-overlap gives the tautology f(f(x1)) ≈ f(f(x1)), which is deleted.
Given [3], weight 5.
    Demodulate with [2] to get [4] x1 ≈ f(x1).
    Backward: [2] becomes [5] g(x1) ≈ x1, by demodulating f(x1) to x1.
    Backward: [1] is subsumed by [4].
Given [5] g(x1) ≈ x1, weight 3.
    No inference is possible, since f(x1) and g(x1) do not overlap.
Passive is empty. Stop.
```

The final active set is $\{f(x_1) \approx x_1,\ g(x_1) \approx x_1\}$. Nothing non-redundant was discarded, so the input is satisfiable. The rewrite system $f(x_1) \to x_1$, $g(x_1) \to x_1$ gives the model: over a signature with one added constant, every term reduces to that constant. This is the structure in which $f$ and $g$ are identities, and in fact the run shows that the input forces $f$ and $g$ to be identities.

### Example 4: selection can force nontermination

Take $\{P(a),\ \neg P(x_1) \lor P(f(x_1))\}$. Without selection, in KBO $P(f(x_1))$ is the strictly maximal literal, and no inference is possible, so the set is saturated at once and satisfiable. With selection of $\neg P(x_1)$, the second clause must resolve with each positive unit.

```
Given P(a)
Given ¬P(x1) ∨ P(f(x1)), with ¬P(x1) selected
    P(f(a))
Given P(f(a))
    P(f(f(a)))
Given P(f(f(a)))
    P(f(f(f(a))))
    and so on forever
```

The same problem is thus trivial with one configuration and divergent with the other. Both configurations are refutationally complete, and the second is not a bug. Choosing a selection function is a trade-off that depends on the problem, as this example shows.

## Common mistakes

- Reading a time-out as satisfiability. A time-out proves nothing, and only a fair finished saturation with no discarded non-redundant clause proves satisfiability.
- Counting the active set alone when estimating search size. The passive set is usually much larger.
- Believing that passive clauses are unused in every loop. They simplify in the Otter loop and do not in the DISCOUNT loop.
- Forgetting to return a backward-simplified clause to the passive set. A changed clause can have new inferences, so leaving it active breaks the invariant.
- Performing generating inferences before forward simplification of the given clause. The inferences would use a larger clause than necessary, and a redundant clause might be used.
- Assuming that a completeness-preserving heuristic is always better. Vampire benefits from incomplete selection and limited resource strategy.
- Calling a discarded unreachable clause redundant. Redundancy is defined semantically and preserves completeness, while unreachability depends on a time limit.
- Reporting a proof that includes every generated clause. A proof is only the ancestor tree of $\bot$.
- Treating the clause weight as if it were the KBO weight. The two are different measures with different purposes, even though both count symbols by default.
- Letting an age-weight ratio with $a = 0$ guarantee fairness in all settings. Pure weight selection is fair only if the weight function has finitely many clauses at each value, as in a finite signature with symbol counting.

## Exercises

1. Define active clause, passive clause, given clause, and fair inference process. State the invariant of the given-clause loop.

<details><summary>Solution</summary>

An active clause has been selected and takes part in generating inferences. A passive clause is kept and waiting to be selected. The given clause is the passive clause selected at the current iteration. An inference process is fair if every inference with persistent premises is performed at some step. The invariant states that after each iteration, all inferences among active clauses have been performed, apart from those whose premises were later removed.

</details>

2. State the differences between the Otter and DISCOUNT loops. Say which loop E uses and which saturation algorithms Vampire offers.

<details><summary>Solution</summary>

The Otter loop simplifies new clauses with both active and passive clauses, and it simplifies both sets with each new clause. The DISCOUNT loop uses only active clauses for simplification, and passive clauses take no part until selected. E uses a DISCOUNT-loop variant. Vampire offers Otter, DISCOUNT and the limited resource strategy.

</details>

3. Explain why age-only selection is fair. Then explain why weight-only selection is fair over a finite signature and describe when it can behave badly.

<details><summary>Solution</summary>

With age selection, a clause is selected after all clauses older than it, of which there are finitely many. So each kept persistent clause is eventually selected, and then all inferences with it and earlier active clauses are performed. Inferences with later active clauses are performed when those are selected.

With a finite signature, only finitely many clauses up to renaming have a given weight. A clause of weight $w$ waits for finitely many lighter clauses and ties, so it is eventually selected. In practice, it can wait for a very long time if the search generates many lighter clauses, and a key heavy clause can stay unused for the entire run. This is why provers mix the two with a ratio.

</details>

4. In Example 1, take the active set after the given clause [3] has been processed. State the passive set at that point, and say which of the clauses listed could be deleted without performing any inference.

<details><summary>Solution</summary>

The passive set is $\{[7], [8], [9], [10], [11], [12]\}$. Clause [7] is subsumed by [1], as seen by matching $e \cdot x_1 \approx x_1$ with $x_1 \mapsto x_1 \cdot x_2$. Clauses [8] and [9] demodulate to tautologies, which is a simplification step and no generating inference. These three can therefore be removed by simplification and deletion. Clause [11] stays, and [10] demodulates to [15]. Clause [12] stays until a later given clause, and the run stopped before it was selected.

</details>

5. Run the DISCOUNT loop on the following clauses, with KBO, all weights 1, precedence $P > f > a > b > c$, selection of a negative literal, and lightest-first selection. Report the outcome and describe a model if the outcome is satisfiability.

$$
\neg P(x_1) \lor f(x_1) \approx a, \qquad P(b), \qquad f(b) \not\approx c.
$$

<details><summary>Solution</summary>

```
[1] ¬P(x1) ∨ f(x1) ≈ a      weight 5
[2] P(b)                    weight 2
[3] f(b) ≉ c                weight 3

Given [2]. Nothing is generated.
Given [3]. Nothing is generated.
Given [1], with ¬P(x1) selected.
    [4] f(b) ≈ a            Res on [2] and [1], mgu {x1 ↦ b}.
Given [4], weight 3.
    Backward simplify [3]: f(b) rewrites to a, giving [5] a ≉ c.
    No generating inferences.
Given [5], weight 2.
    No inference is possible, because a and c do not unify.
Passive is empty.
```

The final set is saturated, and nothing non-redundant was discarded, so the input is satisfiable. The candidate model has $P(b)$ true and the rule $f(b) \to a$, with $a$, $b$ and $c$ distinct. Under this interpretation, $a \not\approx c$ holds, and for all other ground terms the instance of the first clause is true because $P$ is false there.

</details>

6. Run the DISCOUNT loop by hand on the following problem, using KBO with precedence $\mathit{sel} > \mathit{st} > a > i > j > v > w$. Report the proof.

$$
\mathit{sel}(\mathit{st}(x_1, x_2, x_3), x_2) \approx x_3, \qquad
x_1 \approx x_2 \lor \mathit{sel}(\mathit{st}(x_3, x_1, x_4), x_2) \approx \mathit{sel}(x_3, x_2),
$$

$$
i \not\approx j, \qquad \mathit{sel}(\mathit{st}(\mathit{st}(a, i, v), j, w), i) \not\approx v.
$$

<details><summary>Solution</summary>

```
[1] sel(st(x1,x2,x3), x2) ≈ x3                      weight 7
[2] x1 ≈ x2 ∨ sel(st(x3,x1,x4), x2) ≈ sel(x3, x2)   weight 11
[3] i ≉ j                                            weight 2
[4] sel(st(st(a,i,v), j, w), i) ≉ v                  weight 10

Given [3]. Nothing is generated.
Given [1]. Nothing is generated, since sel(st(x1,x2,x3),x2) cannot match into [3].
Given [4]. Superposing [1] into [4] requires st(st(a,i,v),j,w) with x2 = i and x2 = j.
    The mgu fails, since i and j differ, so nothing is generated.
Given [2], the strictly maximal literal is the second one.
    [5] j ≈ i ∨ sel(st(a,i,v), i) ≉ v      superposition of [2] into [4],
                                            mgu {x3 ↦ st(a,i,v), x1 ↦ j, x4 ↦ w, x2 ↦ i}
    An overlap between [1] and [2] unifies x1 and x2, so its conclusion contains
    x1 ≈ x1. This is a tautology, and it is deleted.
Given [5], weight 9.
    Forward demodulate with [1] to get j ≈ i ∨ v ≉ v.
    Remove the trivial literal to get [6] j ≈ i.
    Backward simplify [3], which rewrites i to j: j ≉ j, which is [7] ⊥.
Given [7]. Stop.
```

The proof consists of [1], [2], [3], [4], [5], [6] and [7].

</details>

7. Explain what would go wrong if the DISCOUNT loop left a backward-simplified clause in the active set without adding its simplified form to passive.

<details><summary>Solution</summary>

The new form of the clause is different and possibly smaller than the old form. New inferences are possible on it, because its maximal literal or subterms changed. If it stays active with no generating inferences, the invariant that all inferences among active clauses have been performed fails. So the final set might not be saturated, and a report of satisfiability, or a later completeness argument, would be wrong. Returning the clause to passive restores the invariant, since the clause goes through selection and its inferences are performed then.

</details>

8. A prover discards every clause of weight above 30 and then empties its passive set. It has not derived $\bot$. What may it report? Compare this with discarding a subsumed clause of any weight.

<details><summary>Solution</summary>

It must report unknown, or an equivalent status such as GaveUp. A heavy clause may be non-redundant, so the set is not saturated up to redundancy. A subsumed clause is redundant, so its deletion preserves the argument. A prover that deletes only redundant clauses and has an empty passive set may report satisfiability, assuming that the rest of its calculus is a complete one.

</details>

9. Explain how you would make the given-clause loop goal-directed without losing completeness, and how you would check that the change is safe.

<details><summary>Solution</summary>

Change only the selection order. For example, use a separate queue which prefers clauses whose ancestors include the negated goal, and give that queue a share of the selections alongside age. This changes which clause is selected next and does not remove any clause or inference, so the calculus is unchanged. Fairness holds as long as every clause is eventually selected, and including an age queue with a positive ratio gives this. Only an exhausted run or a discarded clause needs special care, and this change introduces neither. Since this restricts neither inferences nor clauses, the completeness theorem applies unchanged.

</details>

10. Design: an encoding of a verification condition uses $n$ axioms of the form $\mathit{cons}(x_1, x_2) \neq \mathit{nil}$ and similar facts. A new encoding replaces functions by predicates, so that $y = f(x)$ becomes $F(x, y)$ with totality and functionality axioms. Predict the effect on a superposition prover, and explain the reasoning.

<details><summary>Solution</summary>

The prediction is that the search becomes harder. In the functional encoding, equality reasoning is handled by oriented rewriting with demodulation, which deletes clauses and keeps terms small. In the relational encoding, functionality is a clause with two negative $F$ literals and one positive equation, $\neg F(x_1, x_2) \lor \neg F(x_1, x_3) \lor x_2 \approx x_3$, and totality is a clause with a Skolem function. These non-unit clauses cannot be used for demodulation, so each replacement must be generated through several resolution steps, and each intermediate clause can take part in further inferences. So a fact that was once one simplification step becomes several generating steps. The prediction should still be checked experimentally on a representative set, because heuristics interact with encoding in unpredictable ways.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write the given-clause loop in both variants, and state the invariant.
- Run the DISCOUNT loop by hand on an unseen problem with a stated ordering, selection function and clause selection rule, reporting each given clause, simplification, generated clause and the final proof.
- Distinguish generating, simplifying and deletion steps, and forward and backward simplification.
- State exactly what a refutation, a finite saturation, and a time-out prove.
- Explain age and weight selection, fairness, the limited resource strategy and the concept of unreachable clauses.
- Name the main term indexes and what each is for.

## Materials

- Kovács and Voronkov, First-Order Theorem Proving and Vampire, CAV 2013. Read it for saturation algorithms, redundancy elimination, clause selection, the limited resource strategy, preprocessing and the comparison of the Otter and DISCOUNT loops.
- Schulz, E - a brainiac theorem prover, AI Communications 2002. Read it for the architecture of E, its calculus and its search control.
- [Vampire prover.](https://vprover.github.io/) Use it to obtain the prover and its current documentation, and to compare your hand traces with real output in later chapters.
- [E prover.](https://www.eprover.org/) Use it to obtain the prover and its manual, which describes the calculus and heuristics as implemented.
- [TPTP problem library.](https://www.tptp.org/) Use it for benchmark problems, input formats and the SZS status ontology.
- Riazanov and Voronkov, Limited Resource Strategy in Resolution Theorem Proving, Journal of Symbolic Computation 2003. Read it for the strategy and its experimental motivation.
- Reger, Suda, Voronkov and Hoder, Selecting the Selection, IJCAR 2016. Read it for lookahead selection and the case for incomplete selection.
- Waldmann, Tourret, Robillard and Blanchette, A Comprehensive Framework for Saturation Theorem Proving, Journal of Automated Reasoning 2022. Read it for a modern, mechanized account of redundancy and the given-clause procedure.
- Voronkov, AVATAR: The Architecture for First-Order Theorem Provers, CAV 2014. Read it for the use of a SAT solver to control clause splitting.
