# Encodings

Part 2, Chapter 4: SAT.

## Objective

Encode combinatorial and verification problems into CNF, including with the Tseitin transformation and cardinality constraints.

## Why this matters

Mainstream SAT solvers read CNF, so almost every application begins with an encoding, and the encoding often decides whether a query takes seconds or never finishes. [Bit-blasting](../../05-smt/bit-vectors/) in SMT solvers, [bounded model checking](../../08-model-checking/bounded-model-checking/) and [MaxSAT](../maxsat/) all reduce to the techniques here. In applied work you will frequently write or inspect encodings, and a bug in one silently gives wrong answers from a correct solver.

## Prerequisites

- [Propositional logic](../../../part-1-foundations/01-mathematical-logic/propositional-logic/)
- [Normal forms and Skolemization](../../../part-1-foundations/01-mathematical-logic/normal-forms-and-skolemization/)
- [Reductions and NP-completeness](../../../part-1-foundations/02-decidability-and-complexity/reductions-and-np-completeness/)

## Lesson

### What an encoding must preserve

An encoding maps a problem instance to a CNF formula $F$, possibly with auxiliary variables. There are several levels of correctness.

- The encoding is equisatisfiable if the instance has a solution exactly when $F$ is satisfiable.
- It is model-preserving if the solutions of the instance are exactly the restrictions of the models of $F$ to the problem variables, so a solution can be read back.
- It is count-preserving if each solution has exactly one extension to a model of $F$.

Equisatisfiability is enough for a yes-or-no answer. Reading a counterexample needs model preservation. [Model counting](../qbf-and-model-counting/) needs count preservation or a projected count.

### Why not distribute

Logical equivalence to CNF can force exponential size. The formula

$$\bigvee_{i=1}^{n} (x_i \land y_i)$$

has $2^n$ clauses in distributed form, one for each way to choose $x_i$ or $y_i$ from each disjunct. None of them can be dropped, because each is a prime implicate. With a fresh variable for each subformula, the same structure takes $O(n)$ clauses.

### The Tseitin transformation

Tseitin (1968) introduced the idea of naming subformulas. Given a formula $\varphi$ built from gates, introduce a fresh variable $t_g$ for each gate $g$, and write clauses that make $t_g$ equivalent to the gate applied to its inputs. Finally assert the variable of the root.

| Gate | Clauses for $t \leftrightarrow$ gate |
|---|---|
| $t \leftrightarrow \neg a$ | $(\neg t \lor \neg a)$ and $(t \lor a)$. |
| $t \leftrightarrow a \land b$ | $(\neg t \lor a)$, $(\neg t \lor b)$ and $(t \lor \neg a \lor \neg b)$. |
| $t \leftrightarrow a \lor b$ | $(t \lor \neg a)$, $(t \lor \neg b)$ and $(\neg t \lor a \lor b)$. |
| $t \leftrightarrow a \oplus b$ | $(\neg t \lor a \lor b)$, $(\neg t \lor \neg a \lor \neg b)$, $(t \lor \neg a \lor b)$ and $(t \lor a \lor \neg b)$. |
| $t \leftrightarrow (a \leftrightarrow b)$ | $(\neg t \lor \neg a \lor b)$, $(\neg t \lor a \lor \neg b)$, $(t \lor a \lor b)$ and $(t \lor \neg a \lor \neg b)$. |
| $t \leftrightarrow (s\ ?\ a : b)$ | $(\neg t \lor \neg s \lor a)$, $(t \lor \neg s \lor \neg a)$, $(\neg t \lor s \lor b)$ and $(t \lor s \lor \neg b)$. |

An $n$-input AND or OR takes $n + 1$ clauses. Negations need no gate in practice, because you can use the negative literal directly.

Theorem 1. Let $T(\varphi)$ be the Tseitin encoding of $\varphi$, with root variable asserted. Every model of $\varphi$ extends in exactly one way to a model of $T(\varphi)$, and every model of $T(\varphi)$ restricts to a model of $\varphi$. The size of $T(\varphi)$ is linear in the size of $\varphi$.

Proof. Let $\alpha$ be an assignment to the variables of $\varphi$. Extend it by setting each $t_g$ to the value of gate $g$ under $\alpha$. This is the only choice that satisfies the definition clauses, as you see by induction from the inputs upward, since each set of clauses is equivalent to $t_g$ being equal to the gate of its inputs. The asserted root clause holds exactly when $\varphi$ is true under $\alpha$. So models of $T(\varphi)$ correspond one-to-one with models of $\varphi$. Each gate contributes a constant number of clauses for fixed fan-in, or $n + 1$ for fan-in $n$, so the size is linear. $\square$

### Polarity: Plaisted-Greenbaum

Plaisted and Greenbaum (1986) observed that only one direction of each definition is needed, depending on the polarity of the gate in the formula. If a subformula occurs only positively, you need the clauses for $t \to$ gate. If it occurs only negatively, you need the clauses for gate $\to t$. This removes about half the clauses.

The result is still equisatisfiable and model-preserving on the original variables, but it is not count-preserving, because an auxiliary variable may be free. Also, unit propagation may do less. Tseitin's full definitions let the solver propagate backward and forward through a gate, and the reduced version gives up some of that. Blocked clause elimination can remove the redundant direction automatically, as described in [Preprocessing and Inprocessing](../preprocessing-and-inprocessing/).

### Cardinality constraints

Many problems state that at most $k$ of the literals $x_1, \dots, x_n$ are true. The table compares standard encodings of at-most-one, written AMO.

| Encoding of AMO | Auxiliary variables | Clauses |
|---|---|---|
| Pairwise | $0$ auxiliary variables are needed. | The count is $\binom{n}{2}$. |
| Sequential | $n - 1$ auxiliary variables are needed. | The count is $3n - 4$. |
| Binary | $\lceil \log_2 n \rceil$ auxiliary variables are needed. | The count is $n \lceil \log_2 n \rceil$. |

The pairwise encoding is the simplest and is usually good for small $n$, because each clause is binary. The binary encoding gives each $x_i$ a distinct code on the bits $b_1, \dots, b_m$, and it adds clauses saying $x_i$ implies each bit of its code. Two true inputs would require two different codes, which is impossible.

For general $k$, the direct encoding uses one clause $(\neg x_{i_1} \lor \dots \lor \neg x_{i_{k+1}})$ for every subset of size $k + 1$, which is $\binom{n}{k+1}$ clauses and no auxiliary variables. It explodes for large $n$ and moderate $k$.

### Sequential counter

Sinz (2005) introduced the following encoding of $\sum_i x_i \le k$. It uses auxiliary variables $s_{i,j}$ for $1 \le i \le n - 1$ and $1 \le j \le k$, meant to say that at least $j$ of $x_1, \dots, x_i$ are true. There are $(n - 1) k$ auxiliary variables.

```
(¬x1 ∨ s1,1)
(¬s1,j)                            for 1 < j ≤ k
for 1 < i < n:
    (¬xi ∨ si,1)
    (¬s(i-1),1 ∨ si,1)
    (¬xi ∨ ¬s(i-1),(j-1) ∨ si,j)   for 1 < j ≤ k
    (¬s(i-1),j ∨ si,j)             for 1 < j ≤ k
    (¬xi ∨ ¬s(i-1),k)
(¬xn ∨ ¬s(n-1),k)
```

The number of clauses is $2nk + n - 3k - 1$.

Theorem 2. The encoding is satisfied by an extension of an assignment to $x_1, \dots, x_n$ exactly when at most $k$ of the $x_i$ are true.

Proof. Suppose that at most $k$ are true. Set $s_{i,j}$ true exactly if at least $j$ of $x_1, \dots, x_i$ are true. Each clause then holds by counting. In particular $(\neg x_i \lor \neg s_{i-1,k})$ can fail only if $k + 1$ of the first $i$ inputs are true.

Conversely, take a model. By induction on $i$, if at least $j$ of $x_1, \dots, x_i$ are true, with $j \le k$, then $s_{i,j}$ is true. The clauses with $s_{i,j}$ positive give exactly the two cases, that $x_i$ supplies the $j$-th true input or that the earlier inputs already reach $j$. Now suppose that $k + 1$ inputs are true, and let $x_i$ be the last of them. Then $k$ of the first $i - 1$ are true, so $s_{i-1,k}$ is true, and this contradicts $(\neg x_i \lor \neg s_{i-1,k})$. $\square$

### Totalizer

Bailleux and Boufkhad (2003) introduced the totalizer, a tree that computes the sum of its inputs in unary. A node with children whose outputs are $a_1, \dots, a_p$ and $b_1, \dots, b_q$ has outputs $r_1, \dots, r_{p+q}$, and the clauses for the direction used in at-most constraints are

$$(\neg a_i \lor \neg b_j \lor r_{i+j}) \quad \text{for } 0 \le i \le p,\ 0 \le j \le q,\ i + j \ge 1,$$

where literals with index 0 are omitted. That is $(p + 1)(q + 1) - 1$ clauses per node. To enforce $\sum x_i \le k$, you add the unit clause $(\neg r_{k+1})$ at the root. The totalizer takes $O(n \log n)$ auxiliary variables and $O(n^2)$ clauses when all outputs are kept. Its strength is that the bound $k$ is only one unit clause or one assumption literal, so a solver can tighten the bound incrementally without re-encoding. This is why [MaxSAT](../maxsat/) solvers such as RC2 rely on it.

### Propagation strength

An encoding of a constraint is arc-consistent under unit propagation if, for any partial assignment of the problem variables, unit propagation assigns every problem literal that the constraint then forces. For example, for AMO, once one input is true, propagation must set all the others false. The pairwise, sequential, binary and totalizer encodings all have this property. Strength matters because solvers do most of their work in propagation, and a weak encoding hides consequences behind search. Compact encodings with weak propagation are often slower than larger ones with strong propagation.

### Encoding verification problems

Three patterns recur in verification.

Bit-blasting. A $w$-bit value becomes $w$ variables. Operations become circuits. A ripple-carry adder uses, for each bit $i$, the sum $s_i = a_i \oplus b_i \oplus c_i$ and the carry $c_{i+1} = (a_i \land b_i) \lor (c_i \land (a_i \oplus b_i))$, and each gate is then Tseitin-encoded. The topic [Bit-vectors](../../05-smt/bit-vectors/) covers this further.

Miters. To check that circuits $A$ and $B$ are equivalent, build both on shared inputs, XOR corresponding outputs, OR the XORs, and assert the result. The circuits are equivalent exactly when the formula is unsatisfiable, and a model is an input that distinguishes them.

Bounded model checking. Given initial states $I$, a transition relation $T$ and bad states $B$, the formula below is satisfiable exactly when a bad state is reachable in exactly $k$ steps. The method comes from Biere, Cimatti, Clarke and Zhu (1999).

$$I(s_0) \land \bigwedge_{t=0}^{k-1} T(s_t, s_{t+1}) \land B(s_k)$$

### Modeling choices

Representing an integer in $\{0, \dots, d - 1\}$ has three common forms.

- The direct or one-hot encoding uses a variable for each value, with exactly-one constraints.
- The order encoding uses variables meaning $v \ge i$, with $(v \ge i + 1) \to (v \ge i)$.
- The log encoding uses $\lceil \log_2 d \rceil$ bits.

The order encoding makes inequalities short. The log encoding is compact, and its propagation is weak. The direct encoding is good for all-different and table constraints.

Redundant constraints, which the formula already implies, can make propagation stronger. Symmetry breaking removes equivalent solutions. For instance, fixing the colors of a triangle in graph coloring removes the factor from permuting color names. Symmetry breaking preserves satisfiability, and it does not preserve the set of models.

### DIMACS CNF

Solvers read the DIMACS format, which is the one place in this chapter that uses integers for literals. A header line `p cnf V C` gives the numbers of variables and clauses. Each clause is a line of nonzero integers, with a negative integer for a negated variable, and a terminating 0.

```
c  (x1 ∨ ¬x2) ∧ (x2 ∨ x3)
p cnf 3 2
1 -2 0
2 3 0
```

## Worked examples

A script in the scratchpad checked each encoding in this section by enumerating assignments and comparing with the intended meaning.

### Example 1: Tseitin and Plaisted-Greenbaum

Encode $\varphi = (x_1 \land x_2) \lor (\neg x_1 \land x_3)$, the multiplexer with selector $x_1$. Name $t_4 \leftrightarrow x_1 \land x_2$, $t_5 \leftrightarrow \neg x_1 \land x_3$ and $t_6 \leftrightarrow t_4 \lor t_5$.

```
t4 ↔ x1 ∧ x2 :  (¬t4 ∨ x1)   (¬t4 ∨ x2)   (t4 ∨ ¬x1 ∨ ¬x2)
t5 ↔ ¬x1 ∧ x3:  (¬t5 ∨ ¬x1)  (¬t5 ∨ x3)   (t5 ∨ x1 ∨ ¬x3)
t6 ↔ t4 ∨ t5 :  (¬t6 ∨ t4 ∨ t5)  (t6 ∨ ¬t4)  (t6 ∨ ¬t5)
root:           (t6)
```

There are 10 clauses. Enumerating all 64 assignments gives 4 models, one for each model of $\varphi$. Those are $x_1, x_2$ with $x_3$ free, and $\neg x_1, x_3$ with $x_2$ free.

All subformulas are positive, so Plaisted-Greenbaum keeps only the implications from each $t$ to its gate:

```
(¬t4 ∨ x1)  (¬t4 ∨ x2)  (¬t5 ∨ ¬x1)  (¬t5 ∨ x3)  (¬t6 ∨ t4 ∨ t5)  (t6)
```

There are 6 clauses, and the restrictions of its models are the same 4 assignments. Here the count also stays 4, since $t_4$ and $t_5$ cannot both be true. Exercise 8 gives a case in which the count changes.

To see the difference in propagation, set $x_1$ and $x_2$ true. The full encoding propagates $t_4$ from $(t_4 \lor \neg x_1 \lor \neg x_2)$. The reduced encoding has no clause with $t_4$ positive except through $t_6$, so propagation gives $\neg t_5$ and then $t_4$ only by way of $(\neg t_6 \lor t_4 \lor t_5)$ and the unit clause $(t_6)$. Without the root unit, the reduced encoding would derive nothing about $t_4$.

### Example 2: sequential counter for at most 2 of 4

Let $n = 4$ and $k = 2$. The auxiliary variables are $s_{1,1}, s_{1,2}, s_{2,1}, s_{2,2}, s_{3,1}, s_{3,2}$. The formula gives $2 \cdot 4 \cdot 2 + 4 - 6 - 1 = 13$ clauses.

```
(¬x1 ∨ s1,1)
(¬s1,2)
i = 2:  (¬x2 ∨ s2,1)  (¬s1,1 ∨ s2,1)  (¬x2 ∨ ¬s1,1 ∨ s2,2)  (¬s1,2 ∨ s2,2)  (¬x2 ∨ ¬s1,2)
i = 3:  (¬x3 ∨ s3,1)  (¬s2,1 ∨ s3,1)  (¬x3 ∨ ¬s2,1 ∨ s3,2)  (¬s2,2 ∨ s3,2)  (¬x3 ∨ ¬s2,2)
(¬x4 ∨ ¬s3,2)
```

Enumeration over all assignments confirms that exactly the 11 input patterns with at most two true inputs have an extension.

Propagation after assigning $x_1$ and $x_3$ true:

```
(¬x1 ∨ s1,1) gives s1,1
(¬s1,2) gives ¬s1,2
(¬s1,1 ∨ s2,1) gives s2,1
(¬x3 ∨ s3,1) gives s3,1
(¬x3 ∨ ¬s2,1 ∨ s3,2) gives s3,2
(¬x3 ∨ ¬s2,2) gives ¬s2,2
(¬x4 ∨ ¬s3,2) gives ¬x4
(¬x2 ∨ ¬s1,1 ∨ s2,2) gives ¬x2
```

Both remaining inputs are forced false, as arc consistency requires. The script confirmed this for all 6 pairs of inputs, and that three true inputs yield a conflict under propagation alone.

### Example 3: graph coloring

Color the graph with vertices 1 to 4 and edges $\{1,2\}, \{1,3\}, \{2,3\}, \{3,4\}$. Let $x_{v,c}$ say that vertex $v$ has color $c$.

```
at least one color:  (xv,1 ∨ ... ∨ xv,k)         for each vertex v
at most one color:   (¬xv,c ∨ ¬xv,d)             for each v and c < d
edge constraint:     (¬xu,c ∨ ¬xv,c)             for each edge {u,v} and each c
```

For $k = 2$ this gives $4 + 4 + 8 = 16$ clauses, and the formula is unsatisfiable, since the triangle $1, 2, 3$ needs three colors. For $k = 3$ this gives $4 + 12 + 12 = 28$ clauses and 12 models. There are 6 ways to color the triangle, and vertex 4 has 2 colors left, which gives $6 \cdot 2 = 12$.

The at-most-one clauses are redundant for deciding colorability, since you can take any color from a vertex with several and keep the edge constraints satisfied. They are needed if the model must give each vertex one color or if you count colorings.

To break symmetry, add the units $x_{1,1}$, $x_{2,2}$ and $x_{3,3}$, because any proper coloring can rename colors so that the triangle uses them in this order. The formula stays satisfiable, and the number of models falls from 12 to 2.

### Example 4: bounded model checking of a counter

A 2-bit counter has state $(a, b)$, with $a$ the high bit. Its next-state functions are $b' = \neg b$ and $a' = a \oplus b$. It starts at $00$. Check whether $11$ is reachable in exactly $k$ steps.

For step $t$, the transition clauses are:

```
b(t+1) ↔ ¬b(t):            (¬b(t+1) ∨ ¬b(t))  (b(t+1) ∨ b(t))
a(t+1) ↔ a(t) ⊕ b(t):      (¬a(t+1) ∨ a(t) ∨ b(t))  (¬a(t+1) ∨ ¬a(t) ∨ ¬b(t))
                           (a(t+1) ∨ ¬a(t) ∨ b(t))  (a(t+1) ∨ a(t) ∨ ¬b(t))
```

Adding the initial units $(\neg a_0)$ and $(\neg b_0)$ and the bad-state units $(a_k)$ and $(b_k)$ gives $6k + 4$ clauses over $2(k + 1)$ variables.

| Bound $k$ | Clauses | Result |
|---|---|---|
| 0 | 4 | The formula is unsatisfiable. |
| 1 | 10 | The formula is unsatisfiable. |
| 2 | 16 | The formula is unsatisfiable. |
| 3 | 22 | The formula has one model, $00, 01, 10, 11$. |
| 4 | 28 | The formula is unsatisfiable. |

The bound $k = 4$ is unsatisfiable because the counter returns to $00$ at step 4. So this encoding answers exact reachability at step $k$, and a result at a larger bound does not subsume a smaller one.

## Common mistakes

- Asserting only the definitions and forgetting the root unit. Without $(t_{\mathrm{root}})$ the formula is trivially satisfiable, since definitions alone can always be satisfied.
- Reusing an auxiliary variable for two different subformulas. Each subformula needs a fresh variable, unless it is the same subformula, in which case sharing is correct and helpful.
- Treating Tseitin output as equivalent to the input. It is equisatisfiable and model-preserving on the original variables. It is not logically equivalent, since it mentions more variables and excludes many assignments to them.
- Using Plaisted-Greenbaum with a subformula under $\leftrightarrow$ or XOR and only one polarity. Such subformulas occur in both polarities, so both directions are needed.
- Counting models of an encoding with free auxiliary variables. Plaisted-Greenbaum and one-sided cardinality encodings may have several extensions per input, so a model count must project.
- Assuming a one-sided cardinality encoding defines its outputs. The clauses in the totalizer above force outputs true when the count is high, and they do not force them false when the count is low. This is enough for at-most constraints only.
- Applying the encoding of $\sum x_i \le k$ with $k = 0$ or $k \ge n$. These are degenerate cases. For $k = 0$, use unit clauses. For $k \ge n$, no clauses are needed.
- Assuming a smaller CNF is easier. Clause count alone does not predict solver time, because propagation strength and structure matter more.
- Reading unsatisfiability of a BMC query as a proof of safety. It shows only that no bad state occurs at the bound checked.

## Exercises

### Exercise 1

Write the Tseitin clauses for $t \leftrightarrow a \lor b \lor c$ and for $t \leftrightarrow a \land b \land c$.

<details><summary>Solution</summary>

For the OR: $(t \lor \neg a)$, $(t \lor \neg b)$, $(t \lor \neg c)$ and $(\neg t \lor a \lor b \lor c)$.

For the AND: $(\neg t \lor a)$, $(\neg t \lor b)$, $(\neg t \lor c)$ and $(t \lor \neg a \lor \neg b \lor \neg c)$.

</details>

### Exercise 2

Encode exactly one of $x_1, x_2, x_3$ with no auxiliary variables, and encode at most 2 of $x_1, x_2, x_3, x_4$ with no auxiliary variables. How many clauses does each take?

<details><summary>Solution</summary>

Exactly one: $(x_1 \lor x_2 \lor x_3)$, $(\neg x_1 \lor \neg x_2)$, $(\neg x_1 \lor \neg x_3)$ and $(\neg x_2 \lor \neg x_3)$, which is 4 clauses.

At most 2 of 4: one clause for each subset of size 3, which is $\binom{4}{3} = 4$ clauses, namely $(\neg x_1 \lor \neg x_2 \lor \neg x_3)$, $(\neg x_1 \lor \neg x_2 \lor \neg x_4)$, $(\neg x_1 \lor \neg x_3 \lor \neg x_4)$ and $(\neg x_2 \lor \neg x_3 \lor \neg x_4)$.

</details>

### Exercise 3

Apply the Tseitin transformation to $(x_1 \leftrightarrow x_2) \lor \neg x_3$, using a literal in place of a gate for the negation. Count the clauses.

<details><summary>Solution</summary>

Let $t_4 \leftrightarrow (x_1 \leftrightarrow x_2)$ and $t_5 \leftrightarrow t_4 \lor \neg x_3$.

```
t4: (¬t4 ∨ ¬x1 ∨ x2)  (¬t4 ∨ x1 ∨ ¬x2)  (t4 ∨ x1 ∨ x2)  (t4 ∨ ¬x1 ∨ ¬x2)
t5: (¬t5 ∨ t4 ∨ ¬x3)  (t5 ∨ ¬t4)  (t5 ∨ x3)
root: (t5)
```

This makes 8 clauses.

</details>

### Exercise 4

Write the 18 clauses of a miter that compares $x_1 \oplus x_2$ with $(x_1 \lor x_2) \land \neg(x_1 \land x_2)$, using an XOR gate for the output comparison. Explain what the result of solving means.

<details><summary>Solution</summary>

Let $g_3 \leftrightarrow x_1 \oplus x_2$, $g_4 \leftrightarrow x_1 \lor x_2$, $g_5 \leftrightarrow x_1 \land x_2$, $g_6 \leftrightarrow g_4 \land \neg g_5$ and $m \leftrightarrow g_3 \oplus g_6$.

```
g3: (¬g3 ∨ x1 ∨ x2)  (¬g3 ∨ ¬x1 ∨ ¬x2)  (g3 ∨ ¬x1 ∨ x2)  (g3 ∨ x1 ∨ ¬x2)
g4: (¬g4 ∨ x1 ∨ x2)  (g4 ∨ ¬x1)  (g4 ∨ ¬x2)
g5: (¬g5 ∨ x1)  (¬g5 ∨ x2)  (g5 ∨ ¬x1 ∨ ¬x2)
g6: (¬g6 ∨ g4)  (¬g6 ∨ ¬g5)  (g6 ∨ ¬g4 ∨ g5)
m:  (¬m ∨ g3 ∨ g6)  (¬m ∨ ¬g3 ∨ ¬g6)  (m ∨ ¬g3 ∨ g6)  (m ∨ g3 ∨ ¬g6)
root: (m)
```

This is 4 + 3 + 3 + 3 + 4 + 1 = 18 clauses. Enumeration finds no model, so the two circuits agree on all inputs. A model would have been an input on which they differ.

</details>

### Exercise 5

Build the totalizer for $x_1, x_2, x_3, x_4$ with leaves paired as $(x_1, x_2)$ and $(x_3, x_4)$. How many clauses does it have, and how do you enforce at most 1?

<details><summary>Solution</summary>

Let $a_1, a_2$ be the outputs for $x_1, x_2$, let $b_1, b_2$ be the outputs for $x_3, x_4$, and let $r_1, \dots, r_4$ be the root outputs.

```
(¬x1 ∨ a1)  (¬x2 ∨ a1)  (¬x1 ∨ ¬x2 ∨ a2)
(¬x3 ∨ b1)  (¬x4 ∨ b1)  (¬x3 ∨ ¬x4 ∨ b2)
(¬a1 ∨ r1)  (¬a2 ∨ r2)
(¬b1 ∨ r1)  (¬b2 ∨ r2)
(¬a1 ∨ ¬b1 ∨ r2)  (¬a1 ∨ ¬b2 ∨ r3)
(¬a2 ∨ ¬b1 ∨ r3)  (¬a2 ∨ ¬b2 ∨ r4)
```

Each leaf node has $(1 + 1)(1 + 1) - 1 = 3$ clauses, and the root has $(2 + 1)(2 + 1) - 1 = 8$, for 14 in total. To enforce at most 1, add the unit $(\neg r_2)$. Enumeration confirmed the bounds $k = 0, 1, 2, 3$ using $(\neg r_{k+1})$.

</details>

### Exercise 6

An integer $u \in \{0, 1, 2, 3\}$ and an integer $v \in \{0, 1, 2, 3\}$ are represented by the order encoding, with variables $u_i$ meaning $u \ge i$ and $v_i$ meaning $v \ge i$ for $i = 1, 2, 3$. Write the clauses for the variables' consistency and for $u \le v$.

<details><summary>Solution</summary>

Consistency: $(\neg u_2 \lor u_1)$, $(\neg u_3 \lor u_2)$, $(\neg v_2 \lor v_1)$ and $(\neg v_3 \lor v_2)$.

For $u \le v$: if $u \ge i$ then $v \ge i$, so $(\neg u_1 \lor v_1)$, $(\neg u_2 \lor v_2)$ and $(\neg u_3 \lor v_3)$. This is correct because $u \le v$ holds exactly when, for every $i$, $u \ge i$ implies $v \ge i$.

</details>

### Exercise 7

The BMC encoding in Example 4 answers reachability at step $k$. Change it so that it answers reachability within $k$ steps. Give two methods.

<details><summary>Solution</summary>

The first method replaces $B(s_k)$ by the disjunction $\bigvee_{t=0}^{k} B(s_t)$. Encode each $B(s_t)$ with a fresh variable $e_t \leftrightarrow (a_t \land b_t)$ and add the clause $(e_0 \lor \dots \lor e_k)$.

The second method adds a self-loop to the transition relation, with a fresh input $h_t$: if $h_t$ is true, the state stays the same, and otherwise it moves as before. Then any state reached in at most $k$ steps can also be reached in exactly $k$ steps, and $B(s_k)$ answers the question. With this change the query is monotone in $k$.

</details>

### Exercise 8

Show that full Tseitin is count-preserving and Plaisted-Greenbaum is not, on $\varphi = (x_1 \land x_2) \lor x_3$.

<details><summary>Solution</summary>

Let $t_4$ name $x_1 \land x_2$ and $t_5$ name $t_4 \lor x_3$. By Theorem 1, the full encoding has one model for each model of $\varphi$.

The Plaisted-Greenbaum encoding is $(\neg t_4 \lor x_1)$, $(\neg t_4 \lor x_2)$, $(\neg t_5 \lor t_4 \lor x_3)$ and $(t_5)$. Under $x_1, x_2, x_3$ all true, $t_5$ must be true, and $t_4$ can be either value, since $(\neg t_5 \lor t_4 \lor x_3)$ is satisfied by $x_3$ and the other two clauses hold because $x_1$ and $x_2$ are true. So this model of $\varphi$ has 2 extensions.

</details>

### Exercise 9

Prove that any CNF over exactly the variables $x_1, \dots, x_n$ that is equivalent to $x_1 \oplus \dots \oplus x_n$ has at least $2^{n-1}$ clauses. Then give an encoding with auxiliary variables and $O(n)$ clauses.

<details><summary>Solution</summary>

Let $F$ be such a CNF, and take a non-tautological clause $C$ of $F$. Suppose that $C$ omits a variable $x_j$. Choose an assignment falsifying $C$, which exists because $C$ is not a tautology. Flipping $x_j$ keeps $C$ false and changes the parity. So one of the two assignments has odd parity and falsifies $F$, which contradicts equivalence. Hence every clause mentions all $n$ variables, and it excludes exactly one assignment. There are $2^{n-1}$ even-parity assignments that must be excluded, so $F$ has at least $2^{n-1}$ clauses.

For the encoding, introduce $t_2 \leftrightarrow x_1 \oplus x_2$ and $t_i \leftrightarrow t_{i-1} \oplus x_i$ for $i = 3, \dots, n$, and assert $(t_n)$. Each XOR takes 4 clauses, so this has $4(n - 1) + 1$ clauses.

</details>

### Exercise 10

Prove that the binary AMO encoding is correct and arc-consistent under unit propagation.

<details><summary>Solution</summary>

Let each $x_i$ have a distinct code $c_i$ over bits $b_1, \dots, b_m$, with clauses saying that $x_i$ implies each bit literal of $c_i$.

Correctness: if two inputs $x_i$ and $x_j$ are true, the bits must match both codes, which differ somewhere, so the clauses are violated. If at most one input is true, say $x_i$, set the bits to $c_i$, or arbitrarily if none is true. All clauses hold, since the clauses of the other inputs have their $\neg x_j$ true.

Arc consistency: suppose $x_i$ is true. Unit propagation sets all bits to $c_i$. For $j \ne i$, the codes differ in some bit, so the clause for $x_j$ and that bit has its bit literal false, and unit propagation gives $\neg x_j$. If no input is true, the constraint forces nothing, so there is nothing to propagate.

</details>

### Exercise 11

Design a CNF for a scheduling problem. Three jobs must be placed in two time slots. Jobs 1 and 2 conflict, and at most two jobs fit in each slot. Write the formula with variables $x_{j,s}$ and decide satisfiability.

<details><summary>Solution</summary>

Each job gets at least one slot: $(x_{1,1} \lor x_{1,2})$, $(x_{2,1} \lor x_{2,2})$ and $(x_{3,1} \lor x_{3,2})$.

Each job gets at most one slot: $(\neg x_{j,1} \lor \neg x_{j,2})$ for $j = 1, 2, 3$.

The conflict: $(\neg x_{1,s} \lor \neg x_{2,s})$ for $s = 1, 2$.

Capacity: at most 2 of the 3 jobs in each slot, so $(\neg x_{1,s} \lor \neg x_{2,s} \lor \neg x_{3,s})$ for $s = 1, 2$. These two clauses are subsumed by the conflict clauses, so you can omit them.

The formula is satisfiable, for example with job 1 and job 3 in slot 1 and job 2 in slot 2.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write the Tseitin clauses for AND, OR, XOR, equivalence and if-then-else gates.
- Prove Theorem 1, and say what Plaisted-Greenbaum gives up.
- State the size of the pairwise, sequential, binary and totalizer encodings.
- Write a sequential counter for small $n$ and $k$, and show its propagation.
- Define arc consistency under unit propagation.
- Encode coloring, a miter and a BMC query for a small transition system.
- Distinguish equisatisfiable, model-preserving and count-preserving encodings.

## Materials

- Biere, Heule, van Maaren and Walsh (editors), Handbook of Satisfiability, 2nd edition. Read the material on CNF encodings for a survey of the options and the trade-offs.
- Knuth, The Art of Computer Programming, Volume 4B, the section on satisfiability. Read it for many worked encodings and exercises.
- Tseitin, On the Complexity of Derivation in Propositional Calculus, 1968. Read it for the origin of naming subformulas.
- Plaisted and Greenbaum, A Structure-Preserving Clause Form Translation, Journal of Symbolic Computation 1986. Read it for polarity-based reduction.
- Sinz, Towards an Optimal CNF Encoding of Boolean Cardinality Constraints, CP 2005. Read it for the sequential counter and its size.
- Bailleux and Boufkhad, Efficient CNF Encoding of Boolean Cardinality Constraints, CP 2003. Read it for the totalizer.
- Biere, Cimatti, Clarke and Zhu, Symbolic Model Checking without BDDs, TACAS 1999. Read it for the original bounded model checking encoding.
