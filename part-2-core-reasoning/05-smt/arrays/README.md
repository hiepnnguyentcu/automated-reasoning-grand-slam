# Arrays

Part 2, Chapter 5: SMT.

## Objective

Decide array formulas using the read-over-write axioms and lemma instantiation.

## Why this matters

Arrays are how verifiers model memory. A heap, a stack frame, a map from addresses to bytes and a table are all represented by functions updated pointwise, so nearly every verification condition from a heap-manipulating program uses this theory. The array solver is also the cleanest example of a theory solved by reduction: its only job is to generate instances of a few axioms, and the combination with equality does the rest. This topic prepares you for [Quantifiers](../quantifiers/), since the array axioms are themselves universally quantified, and for [Verification Conditions](../../07-deductive-verification/verification-conditions/).

## Prerequisites

- [DPLL(T)](../dpllt/), for lemmas generated during search.
- [Equality and Congruence Closure](../equality-and-congruence-closure/), since instantiation reduces arrays to EUF.
- [First-Order Theories](../../../part-1-foundations/01-mathematical-logic/first-order-theories/), for the idea of an axiomatized theory.

## Lesson

### The theory

The theory of arrays has sorts for indices $\mathcal{I}$, elements $\mathcal{E}$ and arrays $\mathcal{A}$, and two function symbols. The term $\mathrm{read}(a, i)$, also written $a[i]$, is the element of $a$ at position $i$. The term $\mathrm{store}(a, i, v)$ is the array that agrees with $a$ except that position $i$ holds $v$. McCarthy introduced these operations with the following axioms, the first two of which are the read-over-write axioms.

$$
\begin{aligned}
&\forall a, i, v.\ \mathrm{read}(\mathrm{store}(a, i, v), i) = v && \text{(idx)} \\
&\forall a, i, j, v.\ i = j \lor \mathrm{read}(\mathrm{store}(a, i, v), j) = \mathrm{read}(a, j) && \text{(read-over-write)} \\
&\forall a, b.\ (\forall i.\ \mathrm{read}(a, i) = \mathrm{read}(b, i)) \to a = b && \text{(extensionality)}
\end{aligned}
$$

The extensional theory includes the third axiom, and the non-extensional theory omits it. Arrays are total functions from indices to elements, and there is no notion of bounds or of an array's length. A program verifier that needs bounds must add them.

Extensionality matters whenever the formula contains $a \ne b$ or a positive use of array equality. The contrapositive gives the following form, in which the inner quantifier has been Skolemized:

$$
a = b \lor \mathrm{read}(a, k_{ab}) \ne \mathrm{read}(b, k_{ab}),
$$

where $k_{ab}$ is a fresh witness index. This is one of the rare places where a solver introduces a new index term.

### Reasoning by case splitting

Consider a term $\mathrm{read}(\mathrm{store}(a, i, v), j)$. The first two axioms give

$$
\mathrm{read}(\mathrm{store}(a, i, v), j) =
\begin{cases}
v & \text{if } i = j, \\
\mathrm{read}(a, j) & \text{otherwise.}
\end{cases}
$$

So you can eliminate this term by a case split on $i = j$. Doing this repeatedly gives a procedure for the fragment in which reads apply directly to stores and arrays are compared by no equalities. The number of case splits is exponential in the worst case, but it provides the right intuition. Each read chases through a chain of stores until it reaches an index that matches or the base array.

### Reduction to EUF by instantiation

A more general procedure replaces $\mathrm{read}$ and $\mathrm{store}$ by uninterpreted functions, and adds enough instances of the axioms. Uninterpreted $\mathrm{read}$ automatically satisfies the congruence rule: if $a = b$ and $i = j$, then $\mathrm{read}(a, i) = \mathrm{read}(b, j)$. So array theory reasoning needs only the following lemma schemes.

| Name | Applies to | Lemma |
|---|---|---|
| idx | A term $b = \mathrm{store}(a, i, v)$. | $\mathrm{read}(b, i) = v$ |
| down | A term $b = \mathrm{store}(a, i, v)$ and an index $j$ read from an array related to $b$. | $j = i \lor \mathrm{read}(b, j) = \mathrm{read}(a, j)$ |
| up | A term $b = \mathrm{store}(a, i, v)$ and an index $j$ read from an array related to $a$. | $j = i \lor \mathrm{read}(b, j) = \mathrm{read}(a, j)$ |
| ext | A pair of array terms $a, b$ that must be distinguished. | $a = b \lor \mathrm{read}(a, k_{ab}) \ne \mathrm{read}(b, k_{ab})$ |

The down and up lemmas are the same formula. They differ in why the lemma is relevant: down pushes information from a read on the store toward its base, and up pushes information from a read on the base toward the store. This presentation follows the rule-based descriptions in the work of de Moura and Bjørner on generalized array procedures. The lemmas that lazy solvers such as Boolector generate are based on a similar idea.

The upward direction may seem unnecessary, but it is needed when one array is the store of two different bases. Take

$$
b = \mathrm{store}(a, i, v) \land b = \mathrm{store}(c, i, w) \land \mathrm{read}(a, j) \ne \mathrm{read}(c, j) \land i \ne j.
$$

No read is applied to $b$. The formula is unsat only because $a$ and $c$ agree with $b$, and hence with each other, at all positions other than $i$. Instantiating the lemma for both stores at the index $j$ gives $\mathrm{read}(b, j) = \mathrm{read}(a, j)$ and $\mathrm{read}(b, j) = \mathrm{read}(c, j)$. These contradict the third literal. Z3 confirms that the formula is unsat.

### Correctness of eager instantiation

The following theorem gives a complete eager procedure, in the spirit of the reduction of Stump, Barrett, Dill and Levitt. We state it for arrays that are used only as arguments of read, store and equality.

Let $F$ be a conjunction of literals over arrays, in which every store term has a name, written $b = \mathrm{store}(a, i, v)$. Construct $\mathrm{Inst}(F)$ by the following steps.

1. For each pair of array terms $a, b$ related by a disequality in $F$, add a fresh index $k_{ab}$ and the ext lemma.
2. Let $\mathrm{Idx}$ be the set of all index terms occurring in $F$, together with the witnesses.
3. For each store $b = \mathrm{store}(a, i, v)$, add the idx lemma.
4. For each store $b = \mathrm{store}(a, i, v)$ and each $j \in \mathrm{Idx}$, add the lemma $j = i \lor \mathrm{read}(b, j) = \mathrm{read}(a, j)$.

Treat read and store as uninterpreted, and let the index and element sorts be interpreted by their own theories.

Theorem. $F$ is satisfiable in the extensional theory of arrays if and only if $\mathrm{Inst}(F)$ is satisfiable in the combination of EUF with the index and element theories.

Proof. Suppose $F$ has a model in arrays. Then every lemma is an instance of an axiom, with the witnesses interpreted as an index where the arrays differ. So $\mathrm{Inst}(F)$ has a model.

Conversely, suppose $\mathcal{M}$ is a model of $\mathrm{Inst}(F)$. For an array term $a$ and index value $d$ equal to the value of some $j \in \mathrm{Idx}$, the value $\mathcal{M}(\mathrm{read}(a, j))$ is defined, and if $j, j'$ have the same value then their reads agree by congruence. Call two array terms weakly related if they are connected by a chain of asserted equalities and store relations. Choose one default element for each weak relation class. Define an array value for each term $a$ as the function

$$
\hat{a}(d) =
\begin{cases}
\mathcal{M}(\mathrm{read}(a, j)) & \text{if } d = \mathcal{M}(j) \text{ for some } j \in \mathrm{Idx}, \\
\text{the default of the class of } a & \text{otherwise.}
\end{cases}
$$

We check that this interpretation satisfies $F$.

Equalities. If $a$ and $b$ are equal in $\mathcal{M}$, congruence gives the same reads, and they are in one class, so $\hat{a} = \hat{b}$.

Stores. Let $b = \mathrm{store}(a, i, v)$. At $d = \mathcal{M}(i)$, the idx lemma gives $\hat{b}(d) = \mathcal{M}(v)$. At any $d = \mathcal{M}(j) \ne \mathcal{M}(i)$ with $j \in \mathrm{Idx}$, the instantiated lemma gives $\hat{b}(d) = \hat{a}(d)$. At any other $d$, both take the default of the common class. So $\hat{b}$ is the correct update of $\hat{a}$.

Disequalities. If $a \ne b$ is in $F$, then the ext lemma with its witness shows that $\hat{a}$ and $\hat{b}$ differ at $\mathcal{M}(k_{ab})$.

Read literals evaluate as they do in $\mathcal{M}$, because each index that occurs in a read is in $\mathrm{Idx}$. $\square$

The size of $\mathrm{Inst}(F)$ is polynomial, and so the satisfiability problem for conjunctions is in NP if the other theories are in NP. Since the lemmas contain disjunctions, the problem is not obviously polynomial, and the case splits on index equality are the real source of difficulty. The theorem also works for finite index and element sorts, because no new values were required: the argument uses only the interpretations of existing terms and the given witnesses. Exercise 7 explores this.

### Lazy instantiation

Eager instantiation adds $|\mathrm{Stores}| \cdot |\mathrm{Idx}|$ lemmas, and most are irrelevant. Practical solvers instantiate on demand.

```
lemmas_on_demand(F):
    B := F with read and store uninterpreted, plus ext lemmas for disequalities
    loop:
        if B is unsat: return unsat
        M := a candidate model of B
        if M respects all store definitions at relevant indices: return sat
        pick a store b = store(a, i, v) and an index j, where M violates
            j = i or read(b, j) = read(a, j), or violates read(b, i) = v
        B := B and the violated lemma
```

Boolector uses this approach, in a form in which the theory consistency checker examines the current SAT assignment and generates lemmas when reads conflict, and other solvers use related schemes inside their theory solvers. The loop terminates because the lemma instances are finite in number, since Idx is fixed in advance, and each iteration adds one that was not yet present.

A useful way of seeing the relevant set is weak equivalence. Two arrays are weakly equivalent if a chain of stores and equalities connects them, and they may then differ only at the store indices on the chain. Reads that relate to the same weak equivalence class interact, and reads in unconnected classes do not.

### The array property fragment

Quantified array properties, such as sortedness, occur in loop invariants. In general, these are undecidable. Bradley, Manna and Sipma identified a decidable fragment. An array property is a formula of the form

$$
\forall \vec{i}.\ G(\vec{i}) \to V(\vec{i}),
$$

where the index guard $G$ is a Boolean combination of comparisons on quantified and other index terms, with the restriction that quantified variables occur only in simple comparisons such as $i \le j$, $i \le t$, $t \le i$ and $i = j$. The value constraint $V$ uses quantified indices only as read positions, as in $a[i]$, and it contains no nested reads such as $a[a[i]]$. For example, these are array properties:

$$
\forall i, j.\ i \le j \to a[i] \le a[j], \qquad\qquad \forall i.\ 0 \le i \le n \to a[i] = 0.
$$

The decision procedure instantiates the quantifiers over a finite index set.

1. Replace $\mathrm{store}$ terms by fresh arrays with two constraints: $b[i] = v$, and the array property $\forall j.\ j \ne i \to b[j] = a[j]$. The latter is written in guard form by the disjunction $j \le i - 1 \lor i + 1 \le j$.
2. Skolemize the existential quantifiers, including those that result from a negated universal.
3. Let the index set $\mathcal{S}$ contain all terms read with non-quantified index and all terms bounding a quantified variable, or a new constant $\lambda$ if none exists.
4. Replace each universal quantifier by a finite conjunction over $\mathcal{S}$.
5. Decide the resulting quantifier-free formula.

The correctness proof is similar in spirit to that of the theorem above: a model of the instances can be extended to all indices by projecting each index to a nearby element of $\mathcal{S}$. The Bradley, Manna and Sipma paper also studies extensions of the fragment, and it proves several of them undecidable. The MBQI paper of Ge and de Moura states that its fragments subsume this one, which you will see in [Quantifiers](../quantifiers/).

## Worked examples

### Worked example 1: an unsat conjunction, by a single lemma

Decide

$$
\mathrm{store}(a, i, v) = b \land \mathrm{read}(b, j) \ne \mathrm{read}(a, j) \land i \ne j.
$$

Let $s = \mathrm{store}(a, i, v)$. The term $\mathrm{read}(b, j)$ exists, and the equality makes $b$ and $s$ equal. So the down lemma for $j$ applies:

$$
j = i \lor \mathrm{read}(s, j) = \mathrm{read}(a, j).
$$

Since $i \ne j$ is asserted, the second disjunct is propagated. Congruence closure on $b = s$ gives $\mathrm{read}(b, j) = \mathrm{read}(s, j)$, and therefore $\mathrm{read}(b, j) = \mathrm{read}(a, j)$. This contradicts the second literal. The verdict is unsat, which Z3 confirms.

### Worked example 2: commuting updates at different indices

We show that two updates at distinct positions can be performed in either order. Decide

$$
\mathrm{store}(\mathrm{store}(a, i, x), j, y) \ne \mathrm{store}(\mathrm{store}(a, j, y), i, x) \land i \ne j.
$$

Name the terms: $b_1 = \mathrm{store}(a, i, x)$, $c_1 = \mathrm{store}(b_1, j, y)$, $b_2 = \mathrm{store}(a, j, y)$ and $c_2 = \mathrm{store}(b_2, i, x)$.

Since $c_1 \ne c_2$ is asserted, add the ext lemma with the fresh index $k$. Together with the literal $c_1 \ne c_2$, this gives

$$
\mathrm{read}(c_1, k) \ne \mathrm{read}(c_2, k).
$$

The index set is $\{i, j, k\}$. The relevant lemmas are as follows.

```
(L1) read(b1, i) = x                         idx for b1
(L2) read(c1, j) = y                         idx for c1
(L3) read(b2, j) = y                         idx for b2
(L4) read(c2, i) = x                         idx for c2
(L5) k = j  or  read(c1, k) = read(b1, k)    down, c1 to b1
(L6) k = i  or  read(b1, k) = read(a, k)     down, b1 to a
(L7) k = i  or  read(c2, k) = read(b2, k)    down, c2 to b2
(L8) k = j  or  read(b2, k) = read(a, k)     down, b2 to a
```

The core performs a case split on $k = i$ and $k = j$, which are atoms of the lemmas. Since $i \ne j$, at most one holds.

Case $k = i$. Then $k \ne j$. By (L5), $\mathrm{read}(c_1, k) = \mathrm{read}(b_1, k)$, which equals $\mathrm{read}(b_1, i) = x$ by congruence and (L1). By congruence and (L4), $\mathrm{read}(c_2, k) = \mathrm{read}(c_2, i) = x$. So the two reads are equal, a conflict.

Case $k = j$. Then $k \ne i$. By congruence and (L2), $\mathrm{read}(c_1, k) = y$. By (L7), $\mathrm{read}(c_2, k) = \mathrm{read}(b_2, k)$, which equals $\mathrm{read}(b_2, j) = y$ by congruence and (L3). A conflict again.

Case $k \ne i$ and $k \ne j$. All four down lemmas fire, so both reads equal $\mathrm{read}(a, k)$. A conflict again.

All cases close, so the verdict is unsat, which Z3 confirms. Therefore, the two update orders give equal arrays when $i \ne j$.

### Worked example 3: the same index, a satisfiable result, and a model

Remove the hypothesis $i \ne j$, take $j = i$, and require $x \ne y$:

$$
\mathrm{store}(\mathrm{store}(a, i, x), i, y) \ne \mathrm{store}(\mathrm{store}(a, i, y), i, x) \land x \ne y.
$$

Name the inner terms $b_1 = \mathrm{store}(a, i, x)$, $c_1 = \mathrm{store}(b_1, i, y)$, $b_2 = \mathrm{store}(a, i, y)$ and $c_2 = \mathrm{store}(b_2, i, x)$. The idx lemmas give $\mathrm{read}(c_1, i) = y$ and $\mathrm{read}(c_2, i) = x$. So $c_1$ and $c_2$ already differ at $i$.

Take the witness $k = i$, so the ext literal $\mathrm{read}(c_1, k) \ne \mathrm{read}(c_2, k)$ holds because $y \ne x$. The remaining lemmas $k = i \lor \dots$ are satisfied through their first disjunct. Therefore, the candidate model is consistent.

Build the model by the theorem. Let $i = 0$, $x = 1$, $y = 2$, and let the default element of this weak class be 0. Then

- $a$ is 0 everywhere,
- $b_1$ has value 1 at index 0 and 0 elsewhere,
- $c_1$ has value 2 at index 0 and 0 elsewhere,
- $b_2$ has value 2 at index 0 and 0 elsewhere,
- $c_2$ has value 1 at index 0 and 0 elsewhere.

The arrays $c_1$ and $c_2$ differ at index 0. Z3 also reports sat, with a similar model.

### Worked example 4: lemmas on demand

Decide

$$
\mathrm{store}(a, i, v) = b \land \mathrm{read}(b, j) = w \land \mathrm{read}(a, j) \ne w.
$$

Treat read and store as uninterpreted.

Round 1. A candidate model of the abstraction assigns $i, j, v, w$ and the reads arbitrarily, subject to the literals. For example, $i = 0$, $j = 1$, $v = 5$, $w = 7$, $\mathrm{read}(a, 1) = 8$. Check it: the store $b = \mathrm{store}(a, i, v)$ and the index $j$ violate the lemma $j = i \lor \mathrm{read}(b, j) = \mathrm{read}(a, j)$, since $1 \ne 0$ and $7 \ne 8$. Add this lemma.

Round 2. With $\mathrm{read}(b, j) = w$ and $\mathrm{read}(a, j) \ne w$, the second disjunct of the lemma is false, so $j = i$ is propagated. A candidate model has $i = j = 0$, $w = 7$, $v = 5$ and $\mathrm{read}(a, 0) = 8$. Check it: the idx lemma $\mathrm{read}(b, i) = v$ is violated, since congruence gives $\mathrm{read}(b, i) = w = 7 \ne 5$. Add the idx lemma.

Round 3. Now $v = w$ is forced. A candidate model is $i = j = 0$, $v = w = 7$ and $\mathrm{read}(a, 0) = 8$. All lemmas hold at the relevant indices, so the procedure reports sat. The arrays are, say, $a$ with value 8 at 0 and 0 elsewhere, and $b$ with value 7 at 0 and 0 elsewhere. Z3 also reports sat, with $i = j$ and $v = w$.

Two lemmas were enough, whereas an eager procedure would have added all instances over the index set before the search began.

## Common mistakes

- Omitting the case $i = j$ from read-over-write. The two-sided form is what makes the axiom sound, since at $i = j$ the read returns the stored value.
- Assuming $\mathrm{store}(a, i, v) = a$ implies anything beyond $\mathrm{read}(a, i) = v$. This equality holds whenever position $i$ already contains $v$, and nothing else is implied.
- Forgetting the witness when a disequality between arrays occurs. Without the ext lemma, the abstraction can treat $a \ne b$ as satisfied while the two arrays have the same reads at every instantiated index, and the solver would report a wrong model.
- Instantiating only downward. As the example above shows, some unsat formulas have no reads on the store itself, so upward lemmas or eager instantiation are required for completeness.
- Applying array extensionality in the non-extensional theory. Without the axiom, $\mathrm{store}(a, i, \mathrm{read}(a, i)) = a$ is not valid.
- Assuming that arrays have finite length or bounds. The theory has no bounds, so a program's out-of-range access must be modelled by explicit constraints.
- Applying the array property procedure to a formula outside the fragment. If the formula contains something like $a[i + 1]$ under a universal quantifier, then finite instantiation is not known to be complete, and a sat answer from it cannot be trusted.
- Choosing an index set without the bounds of the guards. In the array property fragment, the guard's bounding terms must be in the index set, or instances relevant to refutation may be missing.

## Exercises

1. Simplify $\mathrm{read}(\mathrm{store}(\mathrm{store}(a, 1, 5), 2, 7), 1)$ by the read-over-write axioms over integer indices.

<details><summary>Solution</summary>

Since $1 \ne 2$, the outer store is skipped: the term equals $\mathrm{read}(\mathrm{store}(a, 1, 5), 1)$. By idx, this is 5. Z3 confirms that the negated equality is unsat.

</details>

2. Eliminate reads over stores by case splitting for $\mathrm{read}(\mathrm{store}(a, i, v), j) = \mathrm{read}(a, j)$, and state when the equality holds.

<details><summary>Solution</summary>

If $i = j$, the left side is $v$, so the formula is $v = \mathrm{read}(a, i)$. If $i \ne j$, the left side is $\mathrm{read}(a, j)$, and the equality is true. So the formula is equivalent to

$$
i \ne j \lor v = \mathrm{read}(a, i).
$$

</details>

3. For $b = \mathrm{store}(a, i, v) \land \mathrm{read}(b, j) \ne v \land j = i$, list the index set and the lemmas, and decide the formula.

<details><summary>Solution</summary>

The index set is $\{i, j\}$. The idx lemma is $\mathrm{read}(b, i) = v$. By $j = i$ and congruence, $\mathrm{read}(b, j) = \mathrm{read}(b, i) = v$. This contradicts the literal $\mathrm{read}(b, j) \ne v$. The formula is unsat, which Z3 confirms. The other lemmas, such as $j = i \lor \mathrm{read}(b, j) = \mathrm{read}(a, j)$, are not needed.

</details>

4. Prove that $\mathrm{store}(a, i, \mathrm{read}(a, i)) = a$ is valid in the extensional theory, using the lemma procedure on the negation.

<details><summary>Solution</summary>

Let $s = \mathrm{store}(a, i, \mathrm{read}(a, i))$, and assert $s \ne a$. The ext lemma gives a witness $k$ with $\mathrm{read}(s, k) \ne \mathrm{read}(a, k)$.

The lemmas are $\mathrm{read}(s, i) = \mathrm{read}(a, i)$ by idx, and $k = i \lor \mathrm{read}(s, k) = \mathrm{read}(a, k)$ by read-over-write.

If $k = i$, then congruence makes $\mathrm{read}(s, k) = \mathrm{read}(s, i) = \mathrm{read}(a, i) = \mathrm{read}(a, k)$, a conflict. If $k \ne i$, the lemma directly gives a conflict. So the negation is unsat. Z3 confirms this.

</details>

5. Decide $\mathrm{store}(a, i, x) = \mathrm{store}(a, j, y) \land i \ne j$. If it is satisfiable, give the constraints on $a, x, y$ and a model.

<details><summary>Solution</summary>

Let $b$ be the common array. Then $\mathrm{read}(b, i) = x$ by idx, and $\mathrm{read}(b, i) = \mathrm{read}(a, i)$ by read-over-write for the second store, since $i \ne j$. So $x = \mathrm{read}(a, i)$. In the same way, $y = \mathrm{read}(a, j)$. Under these constraints, both stores change nothing, so both equal $a$.

A model is $i = 0$, $j = 1$, $x = 3$, $y = 5$, and $a$ with value 3 at 0, 5 at 1, and 0 elsewhere. Z3 reports sat with a model of the same form.

</details>

6. Give a structure that shows that $\mathrm{store}(a, i, \mathrm{read}(a, i)) = a$ is not valid in the non-extensional theory.

<details><summary>Solution</summary>

Let an array value be a pair $(f, t)$ of a function $f$ from indices to elements and a tag $t \in \{0, 1\}$. Interpret $\mathrm{read}((f, t), i) = f(i)$, and let $\mathrm{store}((f, t), i, v) = (f[i \mapsto v], 1)$. Both read-over-write axioms hold, because they concern only $f$. In this structure, let $a = (f, 0)$. Then $\mathrm{store}(a, i, \mathrm{read}(a, i))$ has tag 1 and is different from $a$, although every read agrees. So the formula is not valid without extensionality.

</details>

7. Let both index and element sorts be single bits. Use the reduction to show that five pairwise distinct arrays cannot exist, and that four can.

<details><summary>Solution</summary>

The reduction introduces a witness for each pair, and each witness has value 0 or 1. Each array term has its reads at index values 0 and 1, which gives two bits. Hence at most four combinations exist. With five arrays, by the pigeonhole principle, two arrays $a, b$ have equal reads at both index values. Their witness $k_{ab}$ has value 0 or 1, and by congruence the reads at $k_{ab}$ are equal to these, so the ext literal is false. The reduced formula is unsat.

For four arrays, assign the four functions from one bit to one bit. Each pair differs at some index, which serves as its witness. Z3 reports unsat for five `Distinct` arrays and sat for four.

</details>

8. Decide, by array property instantiation, the formula $(\forall i, j.\ i \le j \to a[i] \le a[j]) \land a[x] > a[y] \land x \le y$.

<details><summary>Solution</summary>

The formula is an array property with no stores. The index set contains the read terms: $\mathcal{S} = \{x, y\}$. Instantiating $(i, j)$ over $\mathcal{S} \times \mathcal{S}$ gives four formulas. The relevant one is at $(x, y)$: $x \le y \to a[x] \le a[y]$. Together with $x \le y$, it gives $a[x] \le a[y]$, contradicting $a[x] > a[y]$. So the verdict is unsat. Z3 agrees.

</details>

9. Prove that swapping two array positions twice gives the original array. Let $s$ swap positions $i$ and $j$ in $a$, by $s = \mathrm{store}(\mathrm{store}(a, i, a[j]), j, a[i])$, and let $t$ be the same swap of $s$.

<details><summary>Solution</summary>

First compute $s$ at each position. At $j$, $s[j] = a[i]$ by idx. If $i \ne j$, then $s[i] = a[j]$ by two applications of the axioms. At $k \notin \{i, j\}$, $s[k] = a[k]$. If $i = j$, then $s[i] = a[i]$, so in this case $s$ agrees with $a$ everywhere.

Applying the same reasoning to $t$ with $i \ne j$: $t[j] = s[i] = a[j]$. Also $t[i] = s[j] = a[i]$. And for other $k$, $t[k] = s[k] = a[k]$. If $i = j$, then $t[i] = s[i] = a[i]$, and $t[k] = s[k] = a[k]$ elsewhere.

By extensionality, $t = a$. Z3 confirms that $t \ne a$ is unsat.

</details>

10. Design a lazy array solver inside DPLL(T). Say when it runs, what lemma it chooses for a violated store and why the explanation for its lemmas is needed only implicitly. Then give the example that requires upward propagation.

<details><summary>Solution</summary>

Run at final check, when all Boolean atoms are assigned and the congruence closure and index theory are consistent. Optionally run also at intermediate checks, for early pruning.

From the E-graph, compute array classes and index classes. For each store $b = \mathrm{store}(a, i, v)$ check that $\mathrm{read}(b, i)$ and $v$ are in the same class, if not, add the idx lemma. Then for each read $\mathrm{read}(c, j)$ where $c$ is in the same class as $b$ or $a$, if $j$ and $i$ are in different classes, and the terms $\mathrm{read}(b, j)$ and $\mathrm{read}(a, j)$ are not in one class, add the lemma $j = i \lor \mathrm{read}(b, j) = \mathrm{read}(a, j)$. Create the read terms if they do not exist.

For each asserted disequality between arrays not yet given a witness, add an ext lemma.

Lemmas are $T$-valid clauses, not conflicts relative to the trail, so no explanation is computed for them. The Boolean core treats them as new clauses, and if they are conflicting then conflict analysis proceeds normally. The explanations arise from the E-graph when literals of the lemma become false.

The example requiring upward propagation is the one in the Lesson, with no reads on $b$: $b = \mathrm{store}(a, i, v)$, $b = \mathrm{store}(c, i, w)$, $\mathrm{read}(a, j) \ne \mathrm{read}(c, j)$ and $i \ne j$. A check over reads related to $b$ only would report sat with an incorrect model.

Termination holds because the set of index and array terms is finite, apart from the one witness per array disequality, and each lemma is added at most once.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- State the three axioms, and explain the difference between the extensional and non-extensional theories.
- Eliminate reads over stores by case splits.
- Given a formula, name the store terms, compute the index set, write the relevant lemmas and decide it.
- Prove correctness of the reduction, including the construction of array values from a model.
- Run a lemmas-on-demand loop by hand.
- Give an example in which upward lemmas are required.
- State the form of an array property, and decide a small one by instantiation over the index set.

## Materials

- Stump, Barrett, Dill and Levitt, A Decision Procedure for an Extensional Theory of Arrays, LICS 2001. Read it for the original reduction for extensional arrays.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the chapter on arrays for the reduction and a textbook treatment of the array property approach.
- Bradley, Manna and Sipma, What's Decidable About Arrays?, VMCAI 2006. Read it for the array property fragment and its decision procedure.
- de Moura and Bjørner, Generalized, Efficient Array Decision Procedures, FMCAD 2009. Read it for rule-based lemma instantiation and combinators, such as constant arrays and mapped arrays.
- Brummayer and Biere, Lemmas on Demand for the Extensional Theory of Arrays, Journal on Satisfiability, Boolean Modeling and Computation 2009. Read it for a practical lemmas-on-demand scheme.
- Christ and Hoenicke, Weakly Equivalent Arrays, FroCoS 2015. Read it for the weak equivalence perspective on array solving.
