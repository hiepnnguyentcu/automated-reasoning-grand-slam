# Reductions and NP-Completeness

Part 1, Chapter 2: Decidability and Complexity.

## Objective

Prove the Cook-Levin theorem and construct polynomial reductions to and from SAT.

## Why this matters

SAT is the common target language of automated reasoning. [Encodings](../../../part-2-core-reasoning/04-sat/encodings/) into SAT and [bit-blasting](../../../part-2-core-reasoning/05-smt/bit-vectors/) are reductions, [bounded model checking](../../../part-2-core-reasoning/08-model-checking/bounded-model-checking/) is a reduction, and the combination of a Boolean search with a theory solver in [DPLL(T)](../../../part-2-core-reasoning/05-smt/dpllt/) reflects a complexity argument about Boolean structure. When you meet a new reasoning problem at work, NP-completeness tells you that a SAT or SMT encoding is a natural algorithm, and a proof of the reduction tells you that your encoding is correct. Hardness proofs in the other direction tell you to stop looking for a worst-case polynomial algorithm.

## Prerequisites

- [Computability](../computability/), for Turing machines and mapping reductions.
- [Propositional Logic](../../01-mathematical-logic/propositional-logic/), for satisfiability and validity.
- [Normal Forms and Skolemization](../../01-mathematical-logic/normal-forms-and-skolemization/), for conjunctive normal form.
- [First-Order Theories](../../01-mathematical-logic/first-order-theories/), for the theory examples.

## Lesson

### Time complexity and the class P

Fix the multi-tape Turing machine as the model. The running time of a decider $M$ is the function $t(n)$ giving the maximum number of steps of $M$ on inputs of length $n$. Define

$$
\mathrm{DTIME}(t(n)) = \{L : L \text{ is decided by a machine running in time } O(t(n))\},
$$

$$
\mathrm{P} = \bigcup_{k \ge 1} \mathrm{DTIME}(n^k).
$$

P is robust: the reasonable deterministic models simulate one another with polynomial overhead, and polynomial-time algorithms compose. Input size matters. A number in binary has length logarithmic in its value, so an algorithm that loops up to a binary input is exponential in the input size. The same issue reappears in the [next topic](../space-and-the-polynomial-hierarchy/), where the unrolling bound of a model checking problem changes the complexity depending on how it is encoded.

### The class NP

A language $L$ is in NP if there is a polynomial $q$ and a polynomial-time machine $V$, the verifier, such that for all $x$,

$$
x \in L \iff \exists y\, \big(|y| \le q(|x|) \land V(x, y) \text{ accepts}\big).
$$

The string $y$ is called a certificate. Equivalently, $L$ is decided by a nondeterministic machine whose every branch halts within polynomial time, where acceptance means that some branch accepts. To see the equivalence, a nondeterministic machine can guess $y$ and run $V$, and conversely a certificate can record the choices along an accepting branch.

The class coNP contains the complements of languages in NP. A coNP language has short certificates for its no-instances.

For reasoning, the following classifications are basic.

- SAT is in NP, with a satisfying assignment as the certificate.
- UNSAT and propositional validity are in coNP, with a falsifying or satisfying assignment as a certificate for the no-instances.
- The question NP = coNP asks whether unsatisfiability always has short certificates. The [Proof Complexity](../proof-complexity/) topic develops that question.

Clearly $\mathrm{P} \subseteq \mathrm{NP} \cap \mathrm{coNP}$. Whether $\mathrm{P} = \mathrm{NP}$ is open.

### Polynomial reductions and completeness

A polynomial-time reduction from $A$ to $B$, written $A \le_p B$, is a function $f$ computable in polynomial time such that $x \in A \iff f(x) \in B$ for all $x$.

Lemma. If $A \le_p B$ and $B \in \mathrm{P}$, then $A \in \mathrm{P}$. If $A \le_p B$ and $B \le_p C$, then $A \le_p C$.

Proof. For the first statement, the output $f(x)$ has length polynomial in $|x|$, because a polynomial-time machine writes only polynomially many symbols. Running a polynomial-time decider on $f(x)$ therefore takes polynomial time in $|x|$, and a polynomial of a polynomial is a polynomial. The second statement follows by composing the functions in the same way. $\square$

A language $B$ is NP-hard if $A \le_p B$ for every $A \in \mathrm{NP}$. It is NP-complete if it is also in NP. To prove that $B$ is NP-complete, show that $B \in \mathrm{NP}$ and reduce a known NP-complete problem to $B$.

### The Cook-Levin theorem

Cook published the theorem in 1971, and Levin obtained the same phenomenon independently, with his paper appearing in 1973. Cook's setting was theorem proving, and his original statement concerned reducibility to the tautology problem under a form of oracle reduction. The next year, Karp showed that 21 combinatorial problems are complete under many-one reductions, which established the importance of the concept.

Theorem (Cook-Levin). CNF-SAT is NP-complete.

Proof. Membership follows from the assignment certificate. For hardness, let $L \in \mathrm{NP}$ be decided by a nondeterministic single-tape machine $N$ with time bound $p(n) \ge n$ for a polynomial $p$. Use these normalizations.

- Moves have directions $d \in \{-1, 0, +1\}$, and $N$ never moves left from cell 1.
- Each halting state has a transition, for each symbol, that stays in place and writes the same symbol. So every computation can be extended to exactly $p(n)$ steps, and acceptance can be read off from the last step.

Let $\Delta$ be the finite list of transitions, where each $\tau \in \Delta$ is a tuple $(q, a, q', b, d)$. Fix an input $w$ of length $n$, and write $p = p(n)$. In $p$ steps from cell 1, the head stays within the cells $1, \dots, p + 1$.

Use the following variables, for times $0 \le t \le p$ and cells $1 \le j \le p + 1$.

| Variable | Intended meaning |
|---|---|
| $S_{t,q}$ | The state at time $t$ is $q$. |
| $H_{t,j}$ | The head at time $t$ is on cell $j$. |
| $C_{t,j,a}$ | Cell $j$ at time $t$ holds symbol $a$. |
| $D_{t,\tau}$ | The transition taken at time $t < p$ is $\tau$. |

The formula $\varphi_w$ is the conjunction of these groups of clauses.

Uniqueness. For each $t$, exactly one $S_{t,q}$ holds and exactly one $H_{t,j}$ holds. For each $t < p$, exactly one $D_{t,\tau}$ holds. For each $t, j$, exactly one $C_{t,j,a}$ holds. Each requirement is one clause saying that at least one holds, and one binary clause $\neg u \lor \neg v$ for each pair.

Initial configuration. The unit clauses are $S_{0,q_0}$, $H_{0,1}$, $C_{0,j,w_j}$ for $j \le n$, and $C_{0,j,\sqcup}$ for $j > n$.

Acceptance. The unit clause is $S_{p,q_{\mathrm{acc}}}$.

Transition. For each $t < p$, each $\tau = (q, a, q', b, d)$ and each cell $j$, include:

$$
\neg D_{t,\tau} \lor S_{t,q}, \qquad \neg D_{t,\tau} \lor S_{t+1,q'},
$$

$$
\neg D_{t,\tau} \lor \neg H_{t,j} \lor C_{t,j,a}, \qquad \neg D_{t,\tau} \lor \neg H_{t,j} \lor C_{t+1,j,b},
$$

$$
\neg D_{t,\tau} \lor \neg H_{t,j} \lor H_{t+1,j+d}.
$$

If $j + d$ is out of range, the last clause is replaced by $\neg D_{t,\tau} \lor \neg H_{t,j}$.

Frame. For each $t < p$, each $j$ and each symbol $a$, include:

$$
H_{t,j} \lor \neg C_{t,j,a} \lor C_{t+1,j,a}.
$$

Correctness. Suppose $N$ accepts $w$. Take an accepting computation, extend it to length $p$ using the halting self-loops, and set the variables according to their intended meaning. All clauses hold.

Conversely, let $\alpha$ be a model of $\varphi_w$. The uniqueness clauses let you read off a configuration $c_t$ and a transition $\tau_t$ at each time. The initial clauses say that $c_0$ is the initial configuration. For the inductive step, consider $\tau_t = (q, a, q', b, d)$ and let $j$ be the head position in $c_t$. The transition clauses say that the state of $c_t$ is $q$ and the scanned symbol is $a$, and that $c_{t+1}$ has state $q'$, symbol $b$ at cell $j$ and head at $j + d$. The frame clauses say that other cells are unchanged. So $c_{t+1}$ is a legal successor of $c_t$. Since $c_p$ has state $q_{\mathrm{acc}}$, this is an accepting computation.

Size. $N$ is fixed, so $|Q|$, $|\Gamma|$ and $|\Delta|$ are constants. There are $O(p^2)$ variables. The largest group is head uniqueness, with $O(p^2)$ binary clauses at each of $O(p)$ times, for $O(p^3)$ clauses. All clauses are generated by simple loops, so $w \mapsto \varphi_w$ is computable in polynomial time. $\square$

The construction is a bounded model checking encoding of a Turing machine. The variables at time $t$ form a state vector, and the transition clauses repeat for each $t$. Whenever you see an unrolled transition relation, you see the proof of Cook-Levin.

### From CNF to 3-CNF: the Tseitin transformation

Converting a formula to CNF by distribution can cause exponential growth, as $\bigvee_{i=1}^{n} (x_i \land y_i)$ becomes $2^n$ clauses. Tseitin's 1968 encoding avoids this by naming subformulas.

Given a formula $\varphi$, assign a new variable $t_\psi$ to each non-variable subformula $\psi$, and write $\ell_\chi$ for $t_\chi$ if $\chi$ is a non-variable subformula and for $\chi$ if it is a variable. Add clauses for the definitions:

$$
t_{\psi \land \chi} \leftrightarrow \ell_\psi \land \ell_\chi: \quad (\neg t \lor \ell_\psi),\ (\neg t \lor \ell_\chi),\ (t \lor \neg \ell_\psi \lor \neg \ell_\chi),
$$

$$
t_{\psi \lor \chi} \leftrightarrow \ell_\psi \lor \ell_\chi: \quad (\neg t \lor \ell_\psi \lor \ell_\chi),\ (t \lor \neg \ell_\psi),\ (t \lor \neg \ell_\chi),
$$

$$
t_{\neg \psi} \leftrightarrow \neg \ell_\psi: \quad (\neg t \lor \neg \ell_\psi),\ (t \lor \ell_\psi).
$$

Finally, add the unit clause $\ell_\varphi$. Negation can also be represented without a new variable by using a negated literal.

Theorem. The resulting CNF has size linear in $|\varphi|$ and at most three literals per clause. Every model of $\varphi$ extends uniquely to a model of the CNF, and every model of the CNF restricts to a model of $\varphi$.

Proof. Size is immediate, since each subformula contributes a bounded number of clauses. The definitions force each $t_\psi$ to equal the truth value of $\psi$ under an assignment of the original variables, by structural induction on $\psi$. So the extension exists and is unique, and the unit clause then holds exactly when $\varphi$ is true. $\square$

The Tseitin form is equisatisfiable with $\varphi$, and generally not logically equivalent to it, since it has new variables. It preserves the number of models, which matters for [model counting](../../../part-2-core-reasoning/04-sat/qbf-and-model-counting/). The Plaisted-Greenbaum refinement keeps only the implication direction required by the polarity of each subformula, which gives fewer clauses and does not preserve the model count in general.

3-SAT is the restriction of CNF-SAT to clauses with exactly three literals. A long clause $(\ell_1 \lor \dots \lor \ell_k)$ is split into

$$
(\ell_1 \lor \ell_2 \lor s_1) \land (\neg s_1 \lor \ell_3 \lor s_2) \land \dots \land (\neg s_{k-3} \lor \ell_{k-1} \lor \ell_k).
$$

Short clauses are padded with new variables, in both polarities. For example, $(\ell)$ becomes the four clauses $(\ell \lor a \lor b)$, $(\ell \lor a \lor \neg b)$, $(\ell \lor \neg a \lor b)$ and $(\ell \lor \neg a \lor \neg b)$. Therefore, 3-SAT is NP-complete.

### Reductions from SAT

A reduction from 3-SAT is usually built from three kinds of parts.

- Choice gadgets, which force a Boolean decision for each variable.
- Satisfaction gadgets, which enforce that each clause has a true literal.
- Consistency constraints, which link the two.

Theorem. Independent Set is NP-complete. An instance is a graph $G$ and a number $k$, and the question is whether $G$ has $k$ pairwise nonadjacent vertices.

Proof. A set of $k$ vertices is a certificate that can be checked in polynomial time. For hardness, let $\varphi$ be a 3-CNF with $m$ clauses. Build $G$ with one vertex per literal occurrence. Connect the three vertices of each clause in a triangle, and connect every pair of vertices labeled with complementary literals. Set $k = m$.

If $\alpha \models \varphi$, choose one true literal occurrence from each clause. Two such vertices are in different triangles, and they are not complementary because both are true under $\alpha$. So they are an independent set of size $m$.

Conversely, an independent set of size $m$ has at most one vertex in each triangle, so exactly one. The labels contain no complementary pair, so you can define $\alpha$ to make all chosen literals true, and assign any other variables arbitrarily. Every clause then has a true literal. $\square$

Clique and Vertex Cover follow directly, since $S$ is independent in $G$ exactly when $S$ is a clique in the complement of $G$ and exactly when $V \setminus S$ is a vertex cover of $G$.

Linear integer arithmetic also inherits hardness. A clause $x_1 \lor x_2 \lor \neg x_3$ becomes $x_1 + x_2 + (1 - x_3) \ge 1$ with $0 \le x_i \le 1$. So even conjunctions of linear integer constraints are NP-hard, which is the reason why [arithmetic solvers](../../../part-2-core-reasoning/05-smt/arithmetic/) need branching for integers.

### Reductions to SAT

Since SAT is NP-complete, every problem in NP reduces to it. Going through the generic Cook-Levin construction is wasteful, because it encodes a Turing machine running the verifier. A direct encoding is usually much smaller and solves faster.

The method has four steps.

1. Identify the certificate of the problem, and represent it using Boolean variables.
2. Write clauses that say the variables represent a well-formed certificate.
3. Write clauses that say the certificate is valid.
4. Prove both directions: each valid certificate gives a model, and each model gives a valid certificate.

Common building blocks include the following.

- At least one of $x_1, \dots, x_n$ is the single clause $x_1 \lor \dots \lor x_n$.
- At most one of $x_1, \dots, x_n$ in the pairwise encoding is $\binom{n}{2}$ binary clauses $\neg x_i \lor \neg x_j$.
- At most one in the sequential encoding uses new variables $s_1, \dots, s_{n-1}$, where $s_i$ means "some $x_j$ with $j \le i$ is true". It uses $3n - 4$ clauses for $n \ge 2$, as shown in Exercise 8.
- Integer arithmetic of fixed width is encoded by circuits. For example, the sum bit is $x_i \oplus y_i \oplus c_i$, and each gate gets a Tseitin definition.

Bounded model checking follows the same method. For a transition system with initial predicate $I$, transition relation $T$ and bad states $B$, a counterexample of length $k$ is a certificate, encoded by

$$
I(s_0) \land \bigwedge_{i=0}^{k-1} T(s_i, s_{i+1}) \land B(s_k).
$$

The formula has size $O(|I| + k|T| + |B|)$, which is polynomial when $k$ is given in unary. The problem is then NP-complete, as Exercise 11 shows. The next topic shows what happens when $k$ is given in binary.

### Tractable cases of SAT

Not every clause restriction is hard, and solver architects exploit this.

Theorem (2-SAT). 2-SAT is solvable in linear time.

Proof. Build the implication graph, which has a vertex for each literal and, for each clause $\ell_1 \lor \ell_2$, edges $\neg \ell_1 \to \ell_2$ and $\neg \ell_2 \to \ell_1$. The formula is unsatisfiable if and only if some variable $x$ has $x$ and $\neg x$ in one strongly connected component.

If $x$ and $\neg x$ are in the same component, a model that sets $x$ true must set $\neg x$ true along the implication path, which is impossible, and setting $x$ false fails in the same way.

Otherwise, process the components in reverse topological order, so that a sink comes first. When a component is reached, make its unassigned literals true and their negations false. The graph is skew-symmetric, meaning that $u \to v$ is an edge exactly when $\neg v \to \neg u$ is an edge, so the negations of the literals in a component also form a component. Each clause holds if no edge leads from a true literal to a false one. Suppose that $u \to v$ had $u$ true and $v$ false, and write $a < b$ when the component of $a$ is processed before the component of $b$. Since $u$ is true, $u < \neg u$. Since $v$ is false, $\neg v < v$. The edge $u \to v$ gives $v \le u$, and the edge $\neg v \to \neg u$ gives $\neg u \le \neg v$. Together these give $u < \neg u \le \neg v < v \le u$, which is a contradiction. Strongly connected components can be computed in linear time. $\square$

Theorem (Horn-SAT). The satisfiability of CNF formulas in which each clause has at most one positive literal is solvable in polynomial time, and in linear time with suitable data structures.

Proof. Start with all variables false. While a clause $\neg x_1 \lor \dots \lor \neg x_k \lor y$ has all $x_i$ true and $y$ false, set $y$ true. If a purely negative clause has all variables true, report unsatisfiable. By induction, each variable set to true is true in every model, so the final assignment is the least model if a model exists, and a violated negative clause proves that no model exists. $\square$

Horn structure reappears in logic programming and in [constrained Horn clauses](../../../part-2-core-reasoning/08-model-checking/horn-clauses/).

XOR-SAT, a conjunction of parity constraints, is a linear system over $\mathbb{F}_2$, so it is solved by Gaussian elimination.

Schaefer's dichotomy theorem (1978) classifies Boolean constraint languages. Satisfiability for a finite set of relations over $\{0, 1\}$ is in P if the relations are all 0-valid, all 1-valid, all Horn, all dual Horn, all affine or all bijunctive, and it is NP-complete otherwise. A Boolean constraint language has no intermediate case.

### SMT theories: Boolean structure on top of conjunctions

An SMT problem has a Boolean skeleton over theory atoms. Let $\mathrm{QF}\_T$ be the satisfiability problem for quantifier-free formulas in theory $T$.

Theorem. If deciding $T$-satisfiability of conjunctions of literals is in NP, then $\mathrm{QF}\_T$ is in NP. If the theory has infinitely many atoms that can take independent truth values, then $\mathrm{QF}\_T$ is NP-hard, even if conjunctions are in P.

Proof. For membership, the certificate is a truth assignment to the atoms that satisfies the Boolean skeleton, together with a certificate for the resulting conjunction of literals. For hardness, translate each propositional variable $x_i$ to a distinct atom $a_i$. For example, in difference logic take $a_i$ to be $u_i - v_i \le 0$ with fresh variables $u_i$ and $v_i$. Each truth assignment to these atoms can be realized in the theory, so $\varphi$ is satisfiable if and only if its translation is $T$-satisfiable. $\square$

This theorem is the complexity-theoretic reason for the architecture of [DPLL(T)](../../../part-2-core-reasoning/05-smt/dpllt/). The SAT solver handles the NP-hard Boolean layer, and the theory solver handles conjunctions, which can be much easier. The table lists standard results, and the [Decidable Fragments](../decidable-fragments/) topic adds the quantified cases.

| Theory | Conjunctions of literals | Quantifier-free formulas |
|---|---|---|
| Equality with uninterpreted functions | In P by congruence closure. | NP-complete. |
| Difference logic | In P by negative cycle detection. | NP-complete. |
| Linear real arithmetic | In P by linear programming. | NP-complete. |
| Linear integer arithmetic | NP-complete. | NP-complete. |
| Bit-vectors, with widths in unary | NP-complete. | NP-complete. |
| Bit-vectors, with widths in binary | NEXPTIME-complete, since one-bit operators can express Boolean structure inside a single literal. | NEXPTIME-complete, by Kovásznai, Fröhlich and Biere. |

Linear programming being in P is Khachiyan's 1979 theorem, although simplex, which has exponential worst cases, is what SMT solvers generally use. Membership of linear integer arithmetic in NP requires a nontrivial argument, because integer solutions must have polynomially many bits when they exist. That argument appears in the [Decidable Fragments](../decidable-fragments/) topic.

### What NP-completeness does and does not say

- It is a worst-case statement about a problem as an infinite family. SAT solvers routinely solve large industrial instances, and small crafted instances can be out of reach.
- It does not rule out subexponential algorithms, unless you assume more. The Exponential Time Hypothesis of Impagliazzo and Paturi says that 3-SAT has no $2^{o(n)}$ algorithm, where $n$ is the number of variables.
- If $\mathrm{P} \ne \mathrm{NP}$, then Ladner's theorem yields languages in NP that are neither in P nor NP-complete. So hardness needs a proof, and failing to find an algorithm is not such a proof.
- A decision procedure gives a search procedure for SAT through self-reducibility, as shown in Exercise 6.

## Worked examples

### Example 1: Tseitin encoding, step by step

Encode $\varphi = (x_1 \land x_2) \lor \neg (x_3 \lor x_1)$.

Name the subformulas with $t_1 \leftrightarrow x_1 \land x_2$, $t_2 \leftrightarrow x_3 \lor x_1$ and $t_3 \leftrightarrow t_1 \lor \neg t_2$. The negation is represented by the literal $\neg t_2$. The clauses are as follows.

```
t1 <-> x1 and x2:      (not t1 or x1), (not t1 or x2), (t1 or not x1 or not x2)
t2 <-> x3 or x1:       (not t2 or x3 or x1), (t2 or not x3), (t2 or not x1)
t3 <-> t1 or not t2:   (not t3 or t1 or not t2), (t3 or not t1), (t3 or t2)
root:                  (t3)
```

That is 10 clauses. Check it by propagation with an assignment $x_1 = \top$, $x_2 = \bot$, $x_3 = \bot$, for which $\varphi$ is false. The clause $(\neg t_1 \lor x_2)$ gives $\neg t_1$. The clause $(t_2 \lor \neg x_1)$ gives $t_2$. Then $(\neg t_3 \lor t_1 \lor \neg t_2)$ becomes $\neg t_3$, which conflicts with the root.

Check the assignment $x_1 = \bot$, $x_2 = \bot$, $x_3 = \bot$, for which $\varphi$ is true. The clause $(\neg t_1 \lor x_1)$ gives $\neg t_1$. The clause $(\neg t_2 \lor x_3 \lor x_1)$ gives $\neg t_2$. Then $(t_3 \lor t_2)$ gives $t_3$, and all clauses hold. Exhaustive enumeration by a script confirmed that the CNF has exactly 4 models, one for each model of $\varphi$, namely the assignments $(x_1, x_2, x_3) \in \{(\bot,\bot,\bot), (\bot,\top,\bot), (\top,\top,\bot), (\top,\top,\top)\}$.

### Example 2: from 3-SAT to Independent Set

Let

$$
\varphi = (x_1 \lor x_2 \lor \neg x_3) \land (\neg x_1 \lor x_2 \lor x_3) \land (\neg x_2 \lor \neg x_3 \lor x_1).
$$

The graph has 9 vertices, written as (clause, literal), and $k = 3$. It has 9 triangle edges, plus these 6 edges between complementary literals in different clauses.

```
(1, x1)     -- (2, not x1)
(1, x2)     -- (3, not x2)
(1, not x3) -- (2, x3)
(2, not x1) -- (3, x1)
(2, x2)     -- (3, not x2)
(2, x3)     -- (3, not x3)
```

From the assignment $x_1 = \bot, x_2 = \bot, x_3 = \bot$, choose the true literals $\neg x_3$ in clause 1, $\neg x_1$ in clause 2, and $\neg x_2$ in clause 3. None of these three vertices are adjacent, so they form an independent set of size 3.

In the other direction, take the independent set $\{(1, x_1), (2, x_2), (3, x_1)\}$. The chosen literals are consistent, so define $x_1 = \top$ and $x_2 = \top$, and assign $x_3$ arbitrarily. Each clause has a true literal. An exhaustive script found 12 independent sets of size 3 in this graph, and each one yields a satisfying assignment.

### Example 3: the Cook-Levin encoding for a small machine

Take the nondeterministic machine that accepts binary strings containing a $1$. Its nonhalting state is $q_0$, and its time bound is $p(n) = n + 1$.

| Name | State | Read | Next state | Write | Move |
|---|---|---|---|---|---|
| $\tau_1$ | $q_0$ | $0$ | $q_0$ | $0$ | $+1$ |
| $\tau_2$ | $q_0$ | $1$ | $q_0$ | $1$ | $+1$ |
| $\tau_3$ | $q_0$ | $1$ | $q_{\mathrm{acc}}$ | $1$ | $0$ |
| $\tau_4$ | $q_0$ | $\sqcup$ | $q_{\mathrm{rej}}$ | $\sqcup$ | $0$ |

In addition, for each of the 3 symbols and each of the 2 halting states, there is one self-loop that stays in place. So $|\Delta| = 10$.

Input $w = 01$. Here $p = 3$, with times $0, \dots, 3$ and cells $1, \dots, 4$. The variable counts are as follows: $S_{t,q}$ has $4 \cdot 3 = 12$, $H_{t,j}$ has $4 \cdot 4 = 16$, $C_{t,j,a}$ has $4 \cdot 4 \cdot 3 = 48$, and $D_{t,\tau}$ has $3 \cdot 10 = 30$, for 106 in total. The clause counts for this encoding, as generated by a script, are:

| Group | Clauses |
|---|---|
| State uniqueness | 16 |
| Head uniqueness | 28 |
| Cell uniqueness | 64 |
| Transition uniqueness | 138 |
| Initial configuration | 6 |
| Acceptance | 1 |
| Transition | 420 |
| Frame | 36 |
| Total | 709 |

An accepting tableau is the following, where each row is a configuration.

```
t=0   state q0    head 1   tape 0 1 _ _    transition tau1
t=1   state q0    head 2   tape 0 1 _ _    transition tau3
t=2   state qacc  head 2   tape 0 1 _ _    transition self-loop of qacc on 1
t=3   state qacc  head 2   tape 0 1 _ _
```

Setting the variables according to these rows satisfies every clause. For example, for $t = 1$ and $\tau_3$, the instance $\neg D_{1,\tau_3} \lor \neg H_{1,2} \lor C_{1,2,1}$ holds because $C_{1,2,1}$ is true, and the instance $\neg D_{1,\tau_3} \lor \neg H_{1,2} \lor H_{2,2}$ holds because $H_{2,2}$ is true. Note that the choice of $\tau_2$ at $t = 1$ would give a run that rejects, and that the formula's models pick out only accepting runs.

Input $w = 00$. Here the formula is unsatisfiable, and unit propagation alone shows it.

```
units from init: S(0,q0), H(0,1), C(0,1,0), C(0,2,0), C(0,3,_), C(0,4,_)
t=0: D(0,tau) requires S(0,q) and C(0,1,a), so only tau1 remains: D(0,tau1)
     S(1,q0), H(1,2), and the frame clause gives C(1,2,0), C(1,3,_), C(1,4,_)
t=1: only tau1 remains: D(1,tau1)
     S(2,q0), H(2,3), and the frame clause gives C(2,3,_), C(2,4,_)
t=2: only tau4 remains: D(2,tau4)
     S(3,qrej)
conflict: S(3,qrej) with the unit S(3,qacc) and state uniqueness
```

A script generated this encoding and solved it for all inputs of length at most 4, and in every case the formula was satisfiable exactly when the input contained a $1$.

### Example 4: an encoding that is unsatisfiable, with a hand proof

Encode 3-colorability of the wheel $W_5$: a hub $v_0$ adjacent to each vertex of the 5-cycle $v_1 v_2 v_3 v_4 v_5$. There are 10 edges and 6 vertices.

The certificate is a coloring. Let $x_{v,c}$ mean that vertex $v$ has color $c \in \{R, G, B\}$.

- At least one color per vertex gives 6 clauses $x_{v,R} \lor x_{v,G} \lor x_{v,B}$.
- At most one color per vertex gives $6 \cdot 3 = 18$ binary clauses.
- For each edge $\{u, v\}$ and color $c$, the clause $\neg x_{u,c} \lor \neg x_{v,c}$ gives $10 \cdot 3 = 30$ clauses.

The formula has 18 variables and 54 clauses. Correctness in both directions is immediate from the definition: a proper coloring sets one variable per vertex and satisfies the clauses, and any model provides a color per vertex with different colors on each edge.

A DPLL search proves unsatisfiability. Decide $x_{v_0, R}$.

```
decide x(v0,R)
propagate: not x(v1,R), not x(v2,R), not x(v3,R), not x(v4,R), not x(v5,R)
decide x(v1,G)
propagate: not x(v1,B), not x(v2,G), so x(v2,B), so not x(v3,B), so x(v3,G),
           so not x(v4,G), so x(v4,B), so not x(v5,B), so x(v5,G)
conflict: edge {v5,v1} with color G
backtrack: not x(v1,G), so x(v1,B)
propagate: not x(v2,B), so x(v2,G), so not x(v3,G), so x(v3,B),
           so not x(v4,B), so x(v4,G), so not x(v5,G), so x(v5,B)
conflict: edge {v5,v1} with color B
```

Hence $\neg x_{v_0, R}$. The color names play symmetric roles, so the same search refutes $x_{v_0, G}$ and $x_{v_0, B}$, and then the at-least-one clause for $v_0$ gives the empty clause. In total, the proof has 6 conflicts. Mathematically, the rim would need a proper 2-coloring of an odd cycle. A script confirmed that the formula is unsatisfiable and that $W_5$ has no proper 3-coloring.

## Common mistakes

- Reducing in the wrong direction for hardness. Reducing your problem to SAT gives an upper bound, and hardness requires reducing SAT, or another hard problem, to your problem.
- Omitting the membership proof when claiming NP-completeness. NP-hardness alone does not place a problem in NP, and many hard problems are believed to lie outside NP.
- Proving only one direction of an encoding. A model that does not decode to a valid certificate shows an unsound encoding, and a certificate with no model shows an incomplete one.
- Treating the Tseitin form as logically equivalent to the original. It is equisatisfiable, and its models restrict to models of the original formula, so a validity check must negate the formula before encoding.
- Using a binary-encoded number as if its value were polynomial in its length. A loop up to a binary number, or an unrolling of that many steps, takes exponential time and produces exponential output.
- Reasoning that NP-hard implies infeasible on the instances you care about. Worst-case hardness says nothing about a given family of instances, so you must measure.
- Assuming that a polynomial encoding is a good encoding. Two polynomial encodings can have very different propagation strength and very different solver performance.
- Claiming that CNF validity or DNF satisfiability is hard. Both are in P, and Exercise 2 explains why normal form matters.
- Stating that linear real arithmetic with Boolean structure is in P. Conjunctions are in P, and Boolean combinations are NP-complete.

## Exercises

### Exercise 1

Give the verifier definition of NP, and state what the certificate is for each of: SAT, Independent Set, and the complement of UNSAT.

<details><summary>Solution</summary>

$L \in \mathrm{NP}$ if there is a polynomial $q$ and a polynomial-time verifier $V$ with $x \in L \iff \exists y\,(|y| \le q(|x|) \land V(x, y) \text{ accepts})$.

For SAT, a certificate is a satisfying assignment. For Independent Set, it is a set of $k$ pairwise nonadjacent vertices. The complement of UNSAT, among well-formed formulas, is SAT, so its certificate is also a satisfying assignment.

</details>

### Exercise 2

Classify each problem as in P, NP-complete or coNP-complete: satisfiability of CNF, validity of CNF, satisfiability of DNF, validity of DNF.

<details><summary>Solution</summary>

- CNF satisfiability is NP-complete by Cook-Levin.
- CNF validity is in P. A conjunction is valid exactly when each clause is valid, and a clause is valid exactly when it contains a complementary pair of literals.
- DNF satisfiability is in P. A disjunction is satisfiable exactly when some term is satisfiable, and a term is satisfiable exactly when it has no complementary pair of literals.
- DNF validity is coNP-complete. It is in coNP, since a falsifying assignment is a certificate. For hardness, $\varphi$ in CNF is unsatisfiable exactly when $\neg \varphi$ is valid, and De Morgan's laws transform $\neg \varphi$ into DNF in linear time. UNSAT for CNF is coNP-complete because SAT for CNF is NP-complete.

</details>

### Exercise 3

Apply the Tseitin encoding to $x_1 \leftrightarrow (x_2 \land \neg x_3)$. Write the clauses.

<details><summary>Solution</summary>

Let $t_1 \leftrightarrow x_2 \land \neg x_3$ and $t_2 \leftrightarrow (x_1 \leftrightarrow t_1)$, and assert $t_2$.

For $t_1$, the clauses are $\neg t_1 \lor x_2$, then $\neg t_1 \lor \neg x_3$, then $t_1 \lor \neg x_2 \lor x_3$.

For $t_2$, the clauses are $\neg t_2 \lor \neg x_1 \lor t_1$, then $\neg t_2 \lor x_1 \lor \neg t_1$, then $t_2 \lor x_1 \lor t_1$, then $t_2 \lor \neg x_1 \lor \neg t_1$.

The root is the unit clause $t_2$. There are 8 clauses, each with at most three literals.

</details>

### Exercise 4

Decide the satisfiability of this 2-CNF by the implication graph method, and show the path you used.

$$
(x_1 \lor x_2) \land (\neg x_1 \lor x_3) \land (\neg x_2 \lor x_3) \land (\neg x_3 \lor x_4) \land (\neg x_4 \lor \neg x_3).
$$

<details><summary>Solution</summary>

The implication edges are:

```
not x1 -> x2       not x2 -> x1
x1 -> x3           not x3 -> not x1
x2 -> x3           not x3 -> not x2
x3 -> x4           not x4 -> not x3
x4 -> not x3       x3 -> not x4
```

There is a path $x_3 \to x_4 \to \neg x_3$, and a path $\neg x_3 \to \neg x_1 \to x_2 \to x_3$. So $x_3$ and $\neg x_3$ are in one strongly connected component, and the formula is unsatisfiable. A brute-force script confirmed that it has no models.

</details>

### Exercise 5

Run the Horn-SAT algorithm on the following formula, and state the result.

$$
x_1 \land (\neg x_1 \lor x_2) \land (\neg x_1 \lor \neg x_2 \lor x_3) \land (\neg x_3 \lor \neg x_4) \land (\neg x_2 \lor x_4 \lor \neg x_5) \land (\neg x_3 \lor x_5 \lor \neg x_1).
$$

<details><summary>Solution</summary>

Start with all variables false.

```
x1 is set true by the unit clause
x2 is set true by (not x1 or x2)
x3 is set true by (not x1 or not x2 or x3)
x5 is set true by (not x3 or x5 or not x1)
x4 is set true by (not x2 or x4 or not x5)
(not x3 or not x4) has all variables true, so report unsatisfiable
```

Each variable was forced in every model, so the negative clause is violated in every model. A brute-force script confirmed that the formula has no models.

</details>

### Exercise 6

Show that if there is a polynomial-time decider for SAT, then a satisfying assignment can be found in polynomial time, and count the calls you make.

<details><summary>Solution</summary>

```
if decide(phi) is no: report unsatisfiable
for i = 1 to n:
    if decide(phi with xi set to true) is yes:
        fix xi to true in phi
    else:
        fix xi to false in phi
```

The invariant is that the current formula is satisfiable. When the true branch fails, the formula is satisfiable and $x_i$ cannot be true in any of its models, so the false branch is satisfiable. After the loop, all variables are fixed and the formula is true. There are $n + 1$ calls on formulas of size no larger than the original, so the total time is polynomial. Modern solvers return models directly, but this pattern is the one used for enumeration and minimization with incremental solving.

</details>

### Exercise 7

Prove that if some NP-complete language is in coNP, then NP = coNP.

<details><summary>Solution</summary>

Let $B$ be NP-complete with $B \in \mathrm{coNP}$. Let $A \in \mathrm{NP}$. Then $A \le_p B$ by a function $f$, so $\overline{A} \le_p \overline{B}$ by the same $f$. Since $\overline{B} \in \mathrm{NP}$, and NP is closed under polynomial reductions, $\overline{A} \in \mathrm{NP}$. So $A \in \mathrm{coNP}$, which proves $\mathrm{NP} \subseteq \mathrm{coNP}$.

For the other inclusion, let $A \in \mathrm{coNP}$. Then $\overline{A} \in \mathrm{NP} \subseteq \mathrm{coNP}$, so $A \in \mathrm{NP}$.

In particular, a polynomial-size proof system for UNSAT would have this consequence. The [Proof Complexity](../proof-complexity/) topic develops the idea.

</details>

### Exercise 8

Consider the sequential encoding of at most one, with new variables $s_1, \dots, s_{n-1}$ and clauses

$$
\neg x_1 \lor s_1, \qquad \neg x_n \lor \neg s_{n-1},
$$

$$
\neg x_i \lor s_i, \quad \neg s_{i-1} \lor s_i, \quad \neg x_i \lor \neg s_{i-1} \qquad (2 \le i \le n - 1).
$$

Count the clauses, and prove that an assignment to $x_1, \dots, x_n$ extends to a model of these clauses if and only if at most one $x_i$ is true.

<details><summary>Solution</summary>

Count. There are 2 clauses in the first line and 3 clauses for each of the $n - 2$ values of $i$, so there are $3(n - 2) + 2 = 3n - 4$ clauses.

If at most one $x_i$ is true. Set $s_i$ true exactly when some $x_j$ with $j \le i$ is true. The clauses $\neg x_i \lor s_i$ and $\neg s_{i-1} \lor s_i$ hold by definition. The clause $\neg x_i \lor \neg s_{i-1}$ could fail only if $x_i$ and an earlier $x_j$ are both true, which is excluded. The final clause $\neg x_n \lor \neg s_{n-1}$ holds for the same reason.

If two are true. Suppose that $x_j$ and $x_k$ are true with $j < k$, and suppose that a model exists. The clauses $\neg x_j \lor s_j$ and $\neg s_{i-1} \lor s_i$ give $s_i$ for all $i$ with $j \le i \le n - 1$. In particular, $s_{k-1}$ is true. The clause $\neg x_k \lor \neg s_{k-1}$ then fails, which is a contradiction.

A script confirmed the clause count and this equivalence exhaustively for $n$ from 2 to 7.

</details>

### Exercise 9

Prove that 3-colorability is NP-complete by reducing from 3-SAT with the following gadgets. A palette triangle has vertices $T$, $F$ and $B$. For each variable $x$, vertices $x$ and $\neg x$ are adjacent to each other and to $B$. An OR gadget with inputs $a, b$ has new vertices $p, q, o$ with edges $a p$, $b q$, $p q$, $p o$ and $q o$. For a clause $\ell_1 \lor \ell_2 \lor \ell_3$, apply one OR gadget to $\ell_1, \ell_2$, giving $o_1$, then another OR gadget to $o_1, \ell_3$, giving $o_2$, and connect $o_2$ to $F$ and to $B$.

<details><summary>Solution</summary>

Membership. A coloring is a certificate that can be checked in polynomial time.

Gadget facts. Consider one OR gadget in a proper coloring.

1. If $a$ and $b$ have the color of $F$, then $p$ and $q$ avoid that color and differ, so they take the other two colors, and $o$ must have the color of $F$.
2. If at least one of $a, b$ has the color of $T$, and the other has the color of $T$ or $F$, then the gadget can be colored with $o$ having the color of $T$. Choose $p, q \in \{F, B\}$ with $p \ne q$. If $a = T$ and $b = F$, take $q = B$ and $p = F$. If $a = T$ and $b = T$, take $q = F$ and $p = B$. If $a = F$ and $b = T$, take $p = B$ and $q = F$. In all cases, $p \ne a$ and $q \ne b$.

Forward direction. From a model, color the palette, and color each literal $T$ if true and $F$ if false. In each clause, color each OR gadget by Fact 2 with output $T$ when an input is true. When both inputs of the first gadget are $F$, use Fact 1 with $p = T$, $q = B$, $o_1 = F$. The clause has a true literal, so $o_2$ can have color $T$. That is compatible with its neighbors $F$ and $B$.

Backward direction. Rename colors so that the palette has colors $T, F, B$. Each literal vertex is adjacent to $B$ and to its complement, so the two literals of a variable have colors $T$ and $F$ in some order, which defines an assignment. If all literals of a clause are false, then Fact 1 gives $o_1 = F$, and it gives $o_2 = F$ too. This contradicts the edge from $o_2$ to $F$. So every clause has a true literal.

A script compared this construction against brute-force satisfiability on 300 random small 3-CNF formulas, and it agreed on each one.

</details>

### Exercise 10

Let $\mathrm{EQ}_{\mathrm{lf}}$ be the following problem. Two loop-free programs over Boolean variables, with no calls, compute one Boolean output from $n$ input bits, and the question is whether they compute the same function on all inputs. Prove that $\mathrm{EQ}_{\mathrm{lf}}$ is coNP-complete. Describe how it is decided with a SAT solver.

<details><summary>Solution</summary>

Membership. The complement has an input on which the outputs differ as a certificate, and each loop-free program runs in time polynomial in its length on a given input.

Hardness. Reduce from UNSAT, which is coNP-complete. Given $\varphi(x_1, \dots, x_n)$, let $P_1$ be a program that evaluates $\varphi$ and returns its value, and let $P_2$ be a program that returns false. They are equivalent if and only if $\varphi$ is unsatisfiable.

Decision procedure. Build a miter: encode each program as a circuit with shared inputs, in static single-assignment form, and assert that the outputs differ. Apply Tseitin and call a SAT solver. The answer "unsatisfiable" means that the programs are equivalent, and a model yields a differing input. Contrast this result with [unrestricted program equivalence](../computability/), which is undecidable.

</details>

### Exercise 11

Let BMC be the following problem: given a transition system over $n$ Boolean state variables, specified by formulas $I, T, B$, and a number $k$ in unary, determine whether a state in $B$ is reachable in exactly $k$ steps from a state in $I$. Prove that BMC is NP-complete.

<details><summary>Solution</summary>

Membership. A certificate is the sequence of states $s_0, \dots, s_k$. It has size $(k + 1)n$, which is polynomial in the input since $k$ is written in unary, and each formula can be evaluated in polynomial time.

Hardness. Reduce SAT. Given $\varphi$ over variables $x_1, \dots, x_n$, take these variables as the state, $I = \top$, $T$ as any formula, $B = \varphi$, and $k = 0$. Then a state in $B$ is reachable in 0 steps from a state in $I$ if and only if $\varphi$ is satisfiable.

The unary encoding of $k$ is what permits the certificate to have polynomial size. With $k$ in binary, a certificate of this kind is exponential, and the problem is harder, as the [next topic](../space-and-the-polynomial-hierarchy/) shows.

</details>

### Exercise 12

Design a SAT encoding of the $k$-Clique problem, and prove it correct in both directions. Count the variables and clauses.

<details><summary>Solution</summary>

Let $G = (V, E)$, with $|V| = n$. The certificate is a list of $k$ distinct, pairwise adjacent vertices. Let $y_{i,v}$ mean that position $i$ of the list holds vertex $v$, for $1 \le i \le k$ and $v \in V$. This gives $kn$ variables.

Clauses:

- For each $i$, the clause $\bigvee_{v} y_{i,v}$ says that position $i$ holds a vertex. There are $k$ such clauses.
- For each $i$ and $u \ne v$, the clause $\neg y_{i,u} \lor \neg y_{i,v}$ says that position $i$ holds at most one vertex. There are $k \binom{n}{2}$ such clauses.
- For each $i < j$ and each ordered pair $(u, v)$, where $u = v$ or $\{u, v\} \notin E$, the clause $\neg y_{i,u} \lor \neg y_{j,v}$ says that two positions cannot hold an equal or nonadjacent pair. There are $\binom{k}{2}\big(n + 2(\binom{n}{2} - |E|)\big)$ such clauses.

Forward direction. Given a clique $v_1, \dots, v_k$, set $y_{i,v_i}$ true, and all other variables false. The first two groups hold by construction. A clause in the third group fails only if $v_i = u$ and $v_j = v$, which would make $v_i$ and $v_j$ equal or nonadjacent, and that is excluded.

Backward direction. Given a model, the first two groups define a unique vertex $v_i$ per position. The third group implies that $v_i \ne v_j$ and that $\{v_i, v_j\} \in E$ for $i < j$. So they form a clique of size $k$.

The encoding is polynomial for all $k \le n$. A symmetry-breaking constraint that orders the positions removes the $k!$ equivalent permutations of each solution, which often matters in practice.

</details>

### Exercise 13

Show that the conjunction fragment of linear integer arithmetic is NP-hard by reducing 3-SAT. Then state why this does not contradict the fact that linear real arithmetic has a polynomial conjunction fragment.

<details><summary>Solution</summary>

Map each variable $x_i$ to an integer variable with constraints $0 \le x_i$ and $x_i \le 1$. Map each clause to an inequality, with a positive literal $x$ becoming $x$ and a negative literal $\neg x$ becoming $1 - x$, and requiring the sum for the clause to be at least 1. Integer solutions correspond exactly to satisfying assignments, because each clause inequality holds if and only if one of its literals has value 1.

There is no contradiction, since integrality is what makes the problem hard. Over the reals, the system usually has a fractional solution, such as $x_i = 1/2$ for all $i$, which satisfies every clause inequality of a 3-CNF. So the relaxation loses all information. This shows why a theory solver for integers uses branching and cuts on top of a relaxation.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define P, NP, coNP and polynomial reductions, and prove their basic properties.
- Write out the Cook-Levin construction, group by group, and prove it correct in both directions.
- State the size of the construction, and explain the connection to bounded model checking.
- Apply the Tseitin transformation and state what it preserves.
- Give the reductions from 3-SAT to Independent Set, Vertex Cover, 3-coloring and integer linear constraints.
- Write a direct SAT encoding of a new NP problem and prove it correct.
- Prove the polynomial-time results for 2-SAT and Horn-SAT.
- State Schaefer's dichotomy, and state the complexity of the standard SMT theories in both their conjunction and Boolean forms.

## Materials

- Sipser, Introduction to the Theory of Computation. Read it for P, NP, a tableau-based proof of Cook-Levin and classic reductions.
- Cook, The complexity of theorem-proving procedures, STOC 1971. Read it for the original theorem and its motivation from theorem proving.
- Levin, Universal sequential search problems, Problems of Information Transmission, 1973. Read it for the independent formulation in terms of search problems.
- Karp, Reducibility Among Combinatorial Problems, 1972. Read it for the 21 reductions that showed the concept's breadth.
- Tseitin, On the complexity of derivation in propositional calculus, 1968. Read it for the definitional encoding and for extended resolution.
- Schaefer, The complexity of satisfiability problems, STOC 1978. Read it for the dichotomy theorem.
- Aspvall, Plass and Tarjan, A linear-time algorithm for testing the truth of certain quantified Boolean formulas, Information Processing Letters, 1979. Read it for the implication graph algorithm for 2-SAT and its quantified extension.
- Sinz, Towards an Optimal CNF Encoding of Boolean Cardinality Constraints, CP 2005. Read it for sequential counter encodings.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read it for encodings of theories into SAT and for the complexity of common theories.
- Kovásznai, Fröhlich and Biere, On the Complexity of Fixed-Size Bit-Vector Logics with Binary Encoded Bit-Width, SMT Workshop 2012. Read it for the effect of width encoding on the complexity of bit-vector logic.
