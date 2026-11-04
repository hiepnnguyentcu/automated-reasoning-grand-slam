# Symbolic Checking with BDDs

Part 2, Chapter 8: Model Checking.

## Objective

Build reduced ordered BDDs by hand and compute fixed points over them.

## Why this matters

Symbolic model checking replaced lists of states with Boolean functions over the state bits, so that a single data structure can represent a set far larger than any explicit table. Reduced ordered binary decision diagrams (ROBDDs) were the first representation that made this practical, because they are canonical and support all needed operations. They remain useful where the functions have compact diagrams, for example in control logic. Knowing them also explains why SAT-based methods were a breakthrough: BDD methods fail when no good variable order exists, and BMC and IC3 avoid building the full function. The fixed-point computations you learn here also reappear in [Interpolation-Based Checking](../interpolation-based-checking/) and [IC3 and PDR](../ic3-and-pdr/), in approximate form.

## Prerequisites

- [Propositional Logic](../../../part-1-foundations/01-mathematical-logic/propositional-logic/) for Boolean functions and Shannon expansion.
- [Transition Systems and Temporal Logic](../transition-systems-and-temporal-logic/) for $T(x, x')$ and the fixed-point characterization of CTL.

## Lesson

### Binary decision diagrams

Fix a set of Boolean variables. For a function $f$, the cofactors $f|_{x=0}$ and $f|_{x=1}$ are the functions obtained by fixing $x$. The Shannon expansion is

$$
f = (\neg x \land f|_{x=0}) \lor (x \land f|_{x=1}).
$$

A binary decision diagram (BDD) is a rooted directed acyclic graph with terminal nodes 0 and 1. Each nonterminal node $u$ has a variable $\mathrm{var}(u)$ and two children: $\mathrm{lo}(u)$ for the value 0 and $\mathrm{hi}(u)$ for the value 1. The function $f_u$ at a node is defined recursively: $f_0 = \bot$, $f_1 = \top$, and $f_u = (\neg \mathrm{var}(u) \land f_{\mathrm{lo}(u)}) \lor (\mathrm{var}(u) \land f_{\mathrm{hi}(u)})$.

Given a total order on the variables, a BDD is ordered if variables increase along every path. An ordered BDD is reduced if it has

1. no redundant test: $\mathrm{lo}(u) \neq \mathrm{hi}(u)$ for every nonterminal $u$;
2. no duplicates: no two distinct nonterminal nodes have the same variable and the same two children, and there is one node for each terminal.

Theorem (canonicity, Bryant). For a fixed variable order, each Boolean function has exactly one ROBDD, up to isomorphism.

Proof. Existence follows by Shannon expansion followed by applying the two reduction rules until none applies. For uniqueness, consider any two ROBDDs for the same function, and take the union of their nodes, identifying the terminals. Say that a variable has rank $i$ when it is the $i$-th in the order, and consider a node's variable rank. By descending induction on the rank, we show that nodes representing the same function are isomorphic. Let $u$ and $v$ be nonterminal nodes with $f_u = f_v$, and with variable ranks $i \leq j$.

If $i < j$, then $f_v$ does not depend on $\mathrm{var}(u)$, since all variables in the subgraph of $v$ come later in the order. Therefore $f_{\mathrm{lo}(u)} = f_{\mathrm{hi}(u)}$. These two children have higher rank than $u$, so by the induction hypothesis they are isomorphic, and within one reduced graph this makes them the same node, which contradicts the first reduction rule.

If $i = j$, the cofactors agree: $f_{\mathrm{lo}(u)} = f_{\mathrm{lo}(v)}$ and $f_{\mathrm{hi}(u)} = f_{\mathrm{hi}(v)}$. By the induction hypothesis the children are isomorphic, so $u$ and $v$ are isomorphic. A terminal cannot have the same function as a nonterminal, since the two children of a nonterminal differ by the argument above, and that makes its function nonconstant. $\square$

Canonicity has several immediate consequences for a fixed order. Equivalence of two functions is a pointer comparison when they share one table of nodes. Satisfiability is a comparison with node 0, and validity is a comparison with node 1. Dependency on a variable can be read off the graph, as Exercise 6 shows.

### Algorithms

A shared table called the unique table implements the reduction rules, so that all diagrams are built reduced from the start.

```
mk(x, l, h):
    if l = h: return l                     // rule 1
    if (x, l, h) is in the unique table: return it   // rule 2
    create a new node (x, l, h), record it, return it
```

All binary connectives are computed by one procedure, with a table for results already computed.

```
apply(op, u, v):
    if (u, v) is in the memo table: return the stored result
    if u and v are terminals: r := op(u, v)
    else if var(u) = var(v): r := mk(var(u), apply(op, lo(u), lo(v)), apply(op, hi(u), hi(v)))
    else if var(u) < var(v): r := mk(var(u), apply(op, lo(u), v), apply(op, hi(u), v))
    else:                    r := mk(var(v), apply(op, u, lo(v)), apply(op, u, hi(v)))
    store r in the memo table for (u, v) and return r
```

With the memo table, each pair of nodes is processed at most once, so `apply` takes $O(|u| \cdot |v|)$ time. Without the memo table, the procedure can take exponential time on the same inputs. Shortcuts can be added: for $\land$, if either argument is 0, return 0; if $u = v$, return $u$.

Further operations are as follows.

- Restriction: $f|_{x=b}$ redirects each edge into a node labeled $x$ to the child selected by $b$, and re-applies `mk`.
- Negation: swap the terminals, or use `apply`. Many packages use complement edges to make this constant time.
- Existential quantification: $\exists x.\, f = f|_{x=0} \lor f|_{x=1}$. Quantifying a set of variables one at a time can blow up in intermediate results. It is usual to combine conjunction and quantification in one recursive procedure called relational product.

### The variable order

The size of an ROBDD can vary from linear to exponential with the order, for the same function. For the function $(a_1 \land b_1) \lor \dots \lor (a_n \land b_n)$:

- the order $a_1, b_1, \dots, a_n, b_n$ gives $2n$ nonterminal nodes;
- the order $a_1, \dots, a_n, b_1, \dots, b_n$ gives $2^{n+1} - 2$ nonterminal nodes.

The second order must remember, after reading $a_1, \dots, a_n$, exactly which $a_i$ were true. Each such set of indices gives a different remaining function of the $b_i$, so the diagram needs one node for each.

Finding an optimal order is NP-hard. Practical packages use heuristics based on the structure of the system and dynamic reordering, of which Rudell's sifting is the best known. Some functions have no good order: Bryant showed that the middle bit of integer multiplication needs exponential size for every order. This limits BDDs for arithmetic-heavy systems.

### Symbolic state sets

Encode states with variables $x = (x_1, \dots, x_n)$. A set of states is represented by the ROBDD of its characteristic function, and a transition relation by the ROBDD of $T(x, y)$, where $y$ is a copy of the variables representing the next state. Interleaving the copies, $x_1, y_1, x_2, y_2, \dots$, is the usual starting order, because each $y_i$ tends to depend mostly on nearby variables. Exercise 10 quantifies this.

Set operations become Boolean operations: union is $\lor$, intersection is $\land$, complement is $\neg$, and emptiness is comparison with 0. Successors and predecessors use quantification.

$$
\mathrm{post}(Z)(y) = \exists x.\, Z(x) \land T(x, y), \qquad \mathrm{pre}(Z)(x) = \exists y.\, T(x, y) \land Z(y).
$$

The result of `post` is a function of $y$, and it is renamed to $x$ before being combined with other sets. For an interleaved order, a renaming that keeps relative order costs one pass over the graph.

### Fixed points

Forward reachability is the least fixed point $\mu Z.\, I \lor \mathrm{post}(Z)$.

```
reach(I, T):
    R := I
    repeat:
        Rold := R
        R := R ∨ rename(∃x. R(x) ∧ T(x, y), y to x)
    until R = Rold          // pointer comparison
    return R
```

Termination takes at most $d + 1$ iterations, where $d$ is the largest distance from the initial states to a reachable state, because $R_i$ holds exactly the states reachable within $i$ steps. To check an invariant $P$, test whether $R \land \neg P$ is 0.

CTL is computed by the fixed points of [Transition Systems and Temporal Logic](../transition-systems-and-temporal-logic/):

$$
\mathbf{EX}\, \Phi = \mathrm{pre}(\Phi), \quad \mathbf{E}[\Phi\, \mathbf{U}\, \Psi] = \mu Z.\, \Psi \lor (\Phi \land \mathrm{pre}(Z)), \quad \mathbf{EG}\, \Phi = \nu Z.\, \Phi \land \mathrm{pre}(Z).
$$

The other operators follow by negation, which is free on these functions, and each one is a sequence of `apply` and quantification steps. A reachable counterexample can be extracted by storing the sequence of frontier sets and walking backward through them with `pre`.

Practical checkers use several improvements. Frontier search takes the image of only the newly added states, which can reduce the BDD size. Partitioned transition relations keep $T$ as a conjunction $\bigwedge_i (y_i \leftrightarrow f_i)$ and quantify variables early, which avoids building the monolithic $T$. For hardware with very many reachable states, this class of methods handled designs well beyond explicit enumeration. SAT-based methods largely replaced it on large designs, because a SAT query does not need the canonical form of the reachable set.

## Worked examples

### Example 1: reducing a decision tree

Take $f = (x_1 \land x_2) \lor x_3$ with the order $x_1, x_2, x_3$. The full decision tree tests $x_1$, then $x_2$, then $x_3$, with leaves given by the truth table.

```
x1 x2 x3 | f
0  0  0  | 0
0  0  1  | 1
0  1  0  | 0
0  1  1  | 1
1  0  0  | 0
1  0  1  | 1
1  1  0  | 1
1  1  1  | 1
```

Step 1: compute the $x_3$ level. Each node on that level has two leaves.

- $(x_1, x_2) = (0, 0)$ gives the node $(x_3, 0, 1)$.
- $(0, 1)$ gives $(x_3, 0, 1)$, a duplicate of the above.
- $(1, 0)$ gives $(x_3, 0, 1)$, a duplicate.
- $(1, 1)$ gives $(x_3, 1, 1)$, which is redundant and is replaced by the terminal 1.

After merging duplicates, a single node $n_3 = (x_3, 0, 1)$ remains.

Step 2: compute the $x_2$ level.

- $x_1 = 0$ gives $(x_2, n_3, n_3)$, which is redundant and is replaced by $n_3$.
- $x_1 = 1$ gives $n_2 = (x_2, n_3, 1)$.

Step 3: compute the $x_1$ level. The root is $n_1 = (x_1, n_3, n_2)$.

The result has 3 nonterminal nodes.

```
n1 = (x1, lo = n3, hi = n2)
n2 = (x2, lo = n3, hi = 1)
n3 = (x3, lo = 0,  hi = 1)
```

Read off a path: $x_1 = 1, x_2 = 0, x_3 = 1$ goes from $n_1$ to $n_2$ to $n_3$ to 1, which agrees with the table.

### Example 2: tracing `apply`

Compute $g = (x_1 \lor x_2) \land (\neg x_1 \lor x_3)$ with the order $x_1, x_2, x_3$. The inputs are

```
u1 = (x1, lo = u2, hi = 1)    u2 = (x2, lo = 0, hi = 1)        for x1 ∨ x2
v1 = (x1, lo = 1,  hi = v2)   v2 = (x3, lo = 0, hi = 1)        for ¬x1 ∨ x3
```

The trace of `apply(∧, u1, v1)` is as follows.

```
apply(∧, u1, v1)                  both variables are x1
  lo: apply(∧, u2, 1)             u2 has variable x2, and 1 is a terminal
        lo: apply(∧, 0, 1) = 0
        hi: apply(∧, 1, 1) = 1
        mk(x2, 0, 1) = u2
  hi: apply(∧, 1, v2)             v2 has variable x3
        lo: apply(∧, 1, 0) = 0
        hi: apply(∧, 1, 1) = 1
        mk(x3, 0, 1) = v2
  mk(x1, u2, v2) = new node w
```

The result is $w = (x_1, \mathrm{lo} = u_2, \mathrm{hi} = v_2)$, with three nonterminal nodes. Its satisfying assignments are 010, 011, 101 and 111, which agree with direct evaluation of $g$.

Reusing the existing nodes $u_2$ and $v_2$ shows the benefit of the shared unique table: the result shares structure with its inputs.

### Example 3: reachability over BDDs

Let the state be $(x_1, x_2)$, with the transitions

```
00 to 00, 01
01 to 01, 10
10 to 10
11 to 00
```

and $I = \neg x_1 \land \neg x_2$. Use the order $x_1, y_1, x_2, y_2$. The relation is the disjunction of one cube per transition; its ROBDD has 8 nonterminal nodes in this order. The sets below are given as formulas, and each one corresponds to a small ROBDD.

Iteration 0: $R_0 = \neg x_1 \land \neg x_2$. The ROBDD is $(x_1, (x_2, 1, 0), 0)$ with 2 nodes.

Compute the image. The conjunction with $T$ selects the transitions from 00:

$$
R_0(x) \land T(x, y) = \neg x_1 \land \neg x_2 \land \neg y_1.
$$

Quantifying $x_1$ and $x_2$ gives $\neg y_1$, and renaming gives $\neg x_1$. Therefore

$$
R_1 = R_0 \lor \neg x_1 = \neg x_1,
$$

with ROBDD $(x_1, 1, 0)$ of 1 node. The set has grown, and the diagram has shrunk.

Iteration 1. The conjunction selects the transitions from 00 and 01:

$$
R_1(x) \land T(x, y) = \neg x_1 \land \bigl( (\neg x_2 \land \neg y_1) \lor (x_2 \land ((\neg y_1 \land y_2) \lor (y_1 \land \neg y_2))) \bigr).
$$

Quantifying $x_1$ removes the conjunct $\neg x_1$. Quantifying $x_2$ takes the disjunction of the two cofactors:

$$
\neg y_1 \lor (\neg y_1 \land y_2) \lor (y_1 \land \neg y_2) = \neg y_1 \lor \neg y_2.
$$

Renaming gives $\neg x_1 \lor \neg x_2$. Therefore

$$
R_2 = \neg x_1 \lor \neg x_2,
$$

with ROBDD $(x_1, 1, (x_2, 1, 0))$ of 2 nodes.

Iteration 2. The image of $\{00, 01, 10\}$ is $\{00, 01, 10\}$, so $R_3 = R_2$. The node for $R_3$ is the same as the node for $R_2$, so the pointer comparison stops the loop.

The reachable set is $\{00, 01, 10\}$. The state 11 is excluded, so the invariant $\neg x_1 \lor \neg x_2$ holds. Note that 11 has an outgoing transition, which plays no part because no reachable state leads to it.

## Common mistakes

- Omitting the reduction rule for redundant tests, and producing a diagram that is ordered but not canonical. Check every node for $\mathrm{lo} = \mathrm{hi}$.
- Applying a variable order that changes between operands. `apply` assumes one global order, and diagrams with different orders cannot be combined directly.
- Assuming that the order is an implementation detail. The size can vary between $2n$ and $2^{n+1} - 2$ for the same function.
- Evaluating quantification as a Boolean difference. $\exists x.\, f$ is a disjunction of cofactors, and $\forall x.\, f$ is a conjunction of them.
- Forgetting to rename $y$ back to $x$ before taking a union with the current set, which produces a function with the wrong support.
- Thinking that a large set has a large BDD. In Example 3, the set grows from one to two states as the diagram shrinks from 2 nodes to 1. The full state space has a 1-node ROBDD: the terminal 1, which has no nonterminal nodes at all.
- Believing that BDDs escape the hardness of the problem. Some functions, such as the middle bit of multiplication, have exponential ROBDDs under every order.

## Exercises

### Exercise 1

State the two reduction rules for ROBDDs, and state the theorem they give.

<details><summary>Solution</summary>

No nonterminal has $\mathrm{lo} = \mathrm{hi}$, and no two nonterminals have the same variable and the same children. Theorem: for a fixed variable order, each Boolean function has a unique ROBDD up to isomorphism.

</details>

### Exercise 2

Build the ROBDD of $x_1 \oplus x_2 \oplus x_3$ with the order $x_1, x_2, x_3$, and count the nonterminal nodes.

<details><summary>Solution</summary>

```
n7 = (x3, lo = 0, hi = 1)     the remaining function is x3
n9 = (x3, lo = 1, hi = 0)     the remaining function is ¬x3
a  = (x2, lo = n7, hi = n9)   the remaining function is x2 ⊕ x3
b  = (x2, lo = n9, hi = n7)   the remaining function is ¬(x2 ⊕ x3)
r  = (x1, lo = a, hi = b)
```

There are 5 nonterminal nodes. In general, parity on $n$ variables needs $2n - 1$ nonterminal nodes, and the size does not depend on the order, by the symmetry of the function.

</details>

### Exercise 3

Build the ROBDD of $(a_1 \land b_1) \lor (a_2 \land b_2)$ with the order $a_1, b_1, a_2, b_2$ and then with the order $a_1, a_2, b_1, b_2$.

<details><summary>Solution</summary>

First order:

```
p = (b2, lo = 0, hi = 1)
q = (a2, lo = 0, hi = p)
r = (b1, lo = q, hi = 1)
s = (a1, lo = q, hi = r)
```

This gives 4 nonterminal nodes. Second order:

```
p = (b2, lo = 0, hi = 1)        function b2
t = (b1, lo = p, hi = 1)        function b1 ∨ b2
u = (b1, lo = 0, hi = 1)        function b1
v = (a2, lo = 0, hi = p)        function a2 ∧ b2
w = (a2, lo = u, hi = t)        function b1 ∨ (a2 ∧ b2)
r = (a1, lo = v, hi = w)
```

This gives 6 nonterminal nodes, which matches $2^{n+1} - 2$ for $n = 2$.

</details>

### Exercise 4

Trace `apply(∨, u, v)` where $u$ is the ROBDD of $x_1 \land x_2$ and $v$ is the ROBDD of $x_3 \land x_4$, with the order $x_1, x_2, x_3, x_4$.

<details><summary>Solution</summary>

Let $u_1 = (x_1, 0, u_2)$ and $u_2 = (x_2, 0, 1)$, and let $v_1 = (x_3, 0, v_2)$ and $v_2 = (x_4, 0, 1)$.

```
apply(∨, u1, v1): x1 comes first
  lo: apply(∨, 0, v1) = v1
  hi: apply(∨, u2, v1): x2 comes first
        lo: apply(∨, 0, v1) = v1   (memo table hit)
        hi: apply(∨, 1, v1) = 1
        mk(x2, v1, 1) = new node c
  mk(x1, v1, c) = new node d
```

The result is $d = (x_1, v_1, c)$, $c = (x_2, v_1, 1)$, $v_1 = (x_3, 0, v_2)$, $v_2 = (x_4, 0, 1)$, with 4 nonterminal nodes.

</details>

### Exercise 5

For $f = (x_1 \land x_2) \lor x_3$, compute $f|_{x_2 = 1}$, $f|_{x_2 = 0}$, $\exists x_2.\, f$ and $\forall x_2.\, f$, on the ROBDD of Example 1.

<details><summary>Solution</summary>

$f|_{x_2 = 1}$: redirect the edges into $n_2$ to its high child, the terminal 1. The root becomes $(x_1, n_3, 1)$, which is $x_1 \lor x_3$. $f|_{x_2 = 0}$: redirect those edges to the low child $n_3$. The root becomes $(x_1, n_3, n_3)$, which reduces to $n_3$, the function $x_3$. Then $\exists x_2.\, f = (x_1 \lor x_3) \lor x_3 = x_1 \lor x_3$, and $\forall x_2.\, f = (x_1 \lor x_3) \land x_3 = x_3$.

</details>

### Exercise 6

Prove that a function depends on a variable $x$ iff $x$ labels some node in its ROBDD.

<details><summary>Solution</summary>

If $x$ labels no node, then the graph makes no test on $x$, and the function is independent of $x$. Conversely, let $f$ be independent of $x$, and suppose $x$ labels a node of the ROBDD of $f$. Replacing every node $u$ with variable $x$ by its low child, then reducing, yields a diagram of $f|_{x=0} = f$ with no test on $x$. Its reduced form has no node with variable $x$, and it is an ROBDD of $f$ with the same order, which contradicts uniqueness. $\square$

</details>

### Exercise 7

With the relation of Example 3, compute $\mathrm{pre}(x_1 \land \neg x_2)$ symbolically, and interpret it.

<details><summary>Solution</summary>

We need $\exists y.\, T(x, y) \land y_1 \land \neg y_2$. Only the transitions into 10 are selected, namely $01 \longrightarrow 10$ and $10 \longrightarrow 10$. So the conjunction is $((\neg x_1 \land x_2) \lor (x_1 \land \neg x_2)) \land y_1 \land \neg y_2$. Quantifying $y_1, y_2$ gives $(\neg x_1 \land x_2) \lor (x_1 \land \neg x_2) = x_1 \oplus x_2$. This is the set $\{01, 10\}$ of states with a successor in $\{10\}$.

</details>

### Exercise 8

With the relation of Example 3, compute $\mathbf{EG}\, \neg x_1$ by the fixed-point iteration, and also compute $\mathbf{EF}(x_1 \land \neg x_2)$.

<details><summary>Solution</summary>

For $\mathbf{EG}\, \neg x_1$, let $Z_0 = \neg x_1$, the set $\{00, 01\}$. The states with a successor in $Z_0$ are 00 (itself), 01 (itself) and 11 (to 00), so $\mathrm{pre}(Z_0) = \{00, 01, 11\}$. Then $Z_1 = \neg x_1 \land \mathrm{pre}(Z_0) = \{00, 01\} = Z_0$. The fixed point is $\neg x_1$.

For $\mathbf{EF}(x_1 \land \neg x_2)$, let $W_0 = \{10\}$. Then $W_1 = W_0 \lor \mathrm{pre}(W_0) = \{01, 10\}$. Next, $\mathrm{pre}(\{01, 10\})$ adds 00 (to 01), giving $W_2 = \{00, 01, 10\}$. Then 11 steps to 00, giving $W_3 = \{00, 01, 10, 11\}$. The formula holds in every state, and the result is the terminal 1.

</details>

### Exercise 9

Prove that `reach` needs at most $d + 1$ images, where $d$ is the largest distance from an initial state to a reachable state, and give a system where exactly $d + 1$ images are used.

<details><summary>Solution</summary>

By induction, $R_i$ is the set of states at distance at most $i$. Every reachable state has distance at most $d$, so $R_d$ is the full reachable set, and the image computed from $R_d$ adds nothing. Thus the loop stops after computing $d + 1$ images. Example 3 has $d = 2$ and computes three images, from $R_0$, $R_1$ and $R_2$.

</details>

### Exercise 10

Compute the size of the ROBDD of the identity relation $\bigwedge_{i=1}^{n} (x_i \leftrightarrow y_i)$ under the interleaved order and under the separated order $x_1, \dots, x_n, y_1, \dots, y_n$. Explain what this implies for transition relation encoding.

<details><summary>Solution</summary>

Interleaved order: each pair contributes one node for $x_i$ and two nodes for $y_i$, so the total is $3n$ nonterminal nodes.

Separated order: after reading $x_1, \dots, x_n$, the diagram must remember all of them. This requires $2^i$ nodes at level $x_{i+1}$ for $0 \leq i < n$, for a total of $2^n - 1$. At level $y_i$, the remaining function is determined by the values of $x_i, \dots, x_n$, giving $2^{n-i+1}$ nodes. The sum over $i$ from 1 to $n$ is $2^{n+1} - 2$. The total is $3 \cdot 2^n - 3$. For $n = 2$ this gives 9.

Since many transition relations assign most state bits to themselves or to nearby functions, keeping $x_i$ next to $y_i$ avoids exponential size. This is why the interleaved order is the usual starting point.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Build an ROBDD by hand from a truth table or by repeated cofactoring.
- Trace `mk` and `apply` with the memo table.
- Prove canonicity.
- Explain and demonstrate how the variable order changes the size.
- Write the image and preimage formulas, and iterate a reachability fixed point by hand.
- Compute $\mathbf{EX}$, $\mathbf{EU}$ and $\mathbf{EG}$ as set computations over functions.

## Materials

- Bryant, Graph-Based Algorithms for Boolean Function Manipulation, IEEE Transactions on Computers 1986. Read it for the original canonical form, the reduction and apply algorithms, and their complexity.
- Huth and Ryan, Logic in Computer Science, 2nd edition. Read Sections 6.1 and 6.2 for ROBDDs and their algorithms, Section 6.3 for symbolic model checking, and Section 6.4 for the relational mu-calculus. This is the most direct hand-exercise treatment of the topic.
- Baier and Katoen, Principles of Model Checking. Read the part of the chapter Computation Tree Logic on symbolic CTL model checking for fixed-point computation over switching functions and ROBDDs. The chapter name was confirmed from the book's table of contents, and its section structure was not.
- Burch, Clarke, McMillan, Dill and Hwang, Symbolic Model Checking: $10^{20}$ States and Beyond, LICS 1990. This entry is added here. Read it for the historical result that established BDD-based symbolic model checking.
