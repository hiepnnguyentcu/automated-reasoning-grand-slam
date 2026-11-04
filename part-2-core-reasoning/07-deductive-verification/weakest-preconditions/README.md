# Weakest Preconditions

Part 2, Chapter 7: Deductive Verification.

## Objective

Compute weakest preconditions by hand and relate them to Hoare logic.

## Why this matters

A Hoare proof requires you to invent an intermediate assertion at every step, whereas a weakest precondition is calculated. This turns verification of loop-free code into a function from programs to formulas, and that function is the core of [verification condition generation](../verification-conditions/). The same predicate transformer view underlies backward reasoning in [loop invariant strengthening](../loop-invariants/), the fixed-point formulations used in [Horn clause solving](../../08-model-checking/horn-clauses/) and [IC3](../../08-model-checking/ic3-and-pdr/), and the relative completeness of Hoare logic. An applied scientist debugging a verifier output needs to be able to compute by hand what the tool computed.

## Prerequisites

- [Hoare Logic](../hoare-logic/) for triples, soundness and the assignment axiom.
- [Denotational Semantics](../../../part-1-foundations/03-semantics-and-types/denotational-semantics/) for fixed points on complete lattices.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for induction on iteration counts.

## Lesson

### Definitions

Identify a predicate with the set of states that satisfy it. Predicates then form a complete Boolean lattice ordered by validity of implication, with top element $\top$ and bottom element $\bot$. For a command $c$ and a postcondition $Q$:

- The weakest liberal precondition $\mathrm{wlp}(c, Q)$ is the set of $\sigma$ such that every terminating run of $c$ from $\sigma$ ends in a state satisfying $Q$.
- The weakest precondition $\mathrm{wp}(c, Q)$ is the set of $\sigma$ such that every run of $c$ from $\sigma$ terminates without failure and ends in a state satisfying $Q$.

Dijkstra introduced $\mathrm{wp}$ in his 1975 paper in order to give a calculus for deriving programs, and his notation for nondeterministic programs is used below. The term weakest is literal. By the first theorem below, $\mathrm{wlp}(c, Q)$ is implied by every precondition that makes the partial correctness triple valid, so it is the largest such set.

Theorem (characterization). For all $P, c, Q$:

$$\models \{P\}\ c\ \{Q\} \iff\ \models P \to \mathrm{wlp}(c, Q) \qquad\qquad \models [P]\ c\ [Q] \iff\ \models P \to \mathrm{wp}(c, Q).$$

Proof. Both claims are immediate from unfolding the definitions. A state in $P$ satisfies the requirement of the triple exactly when it belongs to the corresponding weakest precondition set. $\square$

Theorem (pairing). $\mathrm{wp}(c, Q) \equiv \mathrm{wp}(c, \top) \land \mathrm{wlp}(c, Q)$.

Proof. $\mathrm{wp}(c, \top)$ says that all runs terminate without failure, and $\mathrm{wlp}(c, Q)$ says that all terminating runs end in $Q$. Their conjunction is the definition of $\mathrm{wp}(c, Q)$. $\square$

### The guarded command language

Dijkstra's language has nondeterministic choice built in, and it uses guards in place of an else branch.

```
S ::= skip | abort | x := e | S ; S
    | if b1 → S1 □ ... □ bn → Sn fi
    | do b1 → S1 □ ... □ bn → Sn od
```

In `if`, any branch with a true guard may be chosen, and the command fails if no guard is true. In `do`, the loop repeats while some guard is true, choosing any enabled branch each time. The IMP conditional and loop are the cases with guards $b$ and $\neg b$, and with one guard $b$, respectively.

### Calculation rules for loop-free commands

Write $BB \equiv b_1 \lor \cdots \lor b_n$.

| Command | $\mathrm{wp}(\cdot, Q)$ | $\mathrm{wlp}(\cdot, Q)$ |
|---|---|---|
| $\mathtt{skip}$ | $Q$ | $Q$ |
| $\mathtt{abort}$ | $\bot$ | $\top$ |
| $x := e$ | $Q[e/x]$ | $Q[e/x]$ |
| $S ; T$ | $\mathrm{wp}(S, \mathrm{wp}(T, Q))$ | $\mathrm{wlp}(S, \mathrm{wlp}(T, Q))$ |
| $\mathtt{if}\ \ldots\ \mathtt{fi}$ | $BB \land \bigwedge_i (b_i \to \mathrm{wp}(S_i, Q))$ | $\bigwedge_i (b_i \to \mathrm{wlp}(S_i, Q))$ |

For the deterministic conditional the rule specializes to

$$\mathrm{wp}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, Q) \equiv (b \to \mathrm{wp}(c_1, Q)) \land (\neg b \to \mathrm{wp}(c_2, Q)),$$

and this is equivalent to $(b \land \mathrm{wp}(c_1, Q)) \lor (\neg b \land \mathrm{wp}(c_2, Q))$.

The correctness of each row against the definition follows by unfolding. The assignment row is the substitution lemma, and the sequence row says that all runs of $S ; T$ are runs of $S$ continued by runs of $T$.

Note what the conditional row does to the size of the result. The postcondition $Q$ appears in both conjuncts, so a sequence of $k$ conditionals produces $2^k$ copies of $Q$ if you expand the formula as text. The [verification conditions](../verification-conditions/) topic resolves this.

### Healthiness conditions

Dijkstra lists these properties of $\mathrm{wp}$ for his language:

1. Law of the excluded miracle: $\mathrm{wp}(S, \bot) \equiv \bot$.
2. Monotonicity: if $\models Q \to R$ then $\models \mathrm{wp}(S, Q) \to \mathrm{wp}(S, R)$.
3. Conjunctivity: $\mathrm{wp}(S, Q) \land \mathrm{wp}(S, R) \equiv \mathrm{wp}(S, Q \land R)$.
4. Disjunctivity: $\mathrm{wp}(S, Q) \lor \mathrm{wp}(S, R) \to \mathrm{wp}(S, Q \lor R)$, with equivalence when $S$ is deterministic.

Each one has a direct semantic reading. Law 1 says that a run from any state must end somewhere, so no state can guarantee an impossible result. Law 3 holds because $\mathrm{wp}$ is a universal statement over runs. Law 4 is only an implication in general, since different runs may satisfy different disjuncts. The statement $\mathtt{assume}\ b$ used by modern verifiers satisfies $\mathrm{wp}(\mathtt{assume}\ b, \bot) \equiv \neg b$, so it violates law 1 on purpose. Such statements are sometimes called miracles, and they are useful as an intermediate encoding.

### Loops as fixed points

Fix $L \equiv \mathtt{while}\ b\ \mathtt{do}\ c$. Unfolding one iteration shows that $\mathrm{wp}(L, Q)$ and $\mathrm{wlp}(L, Q)$ are fixed points of these monotone functions on predicates:

$$F(X) \equiv (b \land \mathrm{wp}(c, X)) \lor (\neg b \land Q) \qquad\qquad G(X) \equiv (b \to \mathrm{wlp}(c, X)) \land (\neg b \to Q).$$

Theorem. $\mathrm{wp}(L, Q)$ is the least fixed point of $F$, and $\mathrm{wlp}(L, Q)$ is the greatest fixed point of $G$.

The intuition is that a total correctness guarantee must be established after finitely many iterations, so it is built from below starting with $\bot$. A partial correctness guarantee may hold forever by divergence, so it is cut down from above starting with $\top$. Dijkstra's definition is the corresponding iteration:

$$H_0 \equiv Q \land \neg BB, \qquad H_{k} \equiv H_0 \lor \mathrm{wp}(\mathtt{if}\ \ldots\ \mathtt{fi}, H_{k-1}), \qquad \mathrm{wp}(\mathtt{do}\ \ldots\ \mathtt{od}, Q) \equiv \exists k \geq 0.\ H_k.$$

Lemma. For IMP, $\sigma \models H_k$ if and only if the loop from $\sigma$ terminates after at most $k$ iterations in a state satisfying $Q$.

Proof. By induction on $k$. For $k = 0$, the loop runs zero iterations exactly when $\sigma \models \neg b$, and then the final state is $\sigma$. For $k + 1$, either $\sigma \models H_0$, or $\sigma \models b$ and $\mathrm{wp}(c, H_k)$ holds. The second case says that $c$ terminates in a state from which at most $k$ further iterations reach $Q$. $\square$

Since every terminating run has some finite number of iterations, $\exists k.\ H_k$ is $\mathrm{wp}(L, Q)$ for deterministic programs. The same holds with bounded nondeterminism, by König's lemma: if every run terminates and each step has finitely many successors, the tree of runs is finite and has a uniform depth bound. With unbounded nondeterminism, such as $x := {?}$ choosing any natural number, the iteration $\exists k.\ H_k$ can fall short of the least fixed point, and the transfinite iteration is needed. Exercise 9 gives the example.

For $\mathrm{wlp}$ the dual iteration is $L_0 \equiv \top$, $L_{k+1} \equiv G(L_k)$, and for IMP $\mathrm{wlp}(L, Q) \equiv \forall k.\ L_k$. Here $\sigma \models L_k$ means that if the loop terminates from $\sigma$ in fewer than $k$ iterations, then the final state satisfies $Q$.

These iterations rarely reach a closed form automatically, because the formula grows with $k$, and no finite $k$ needs to suffice. In general the fixed point may not even have a quantifier-free form. This is the reason verifiers ask for invariants: an invariant is a user-supplied approximation of the fixed point, and checking it needs only one application of the transformer.

Theorem (invariants are post-fixed points). If $\models I \land b \to \mathrm{wlp}(c, I)$ and $\models I \land \neg b \to Q$, then $\models I \to \mathrm{wlp}(L, Q)$. So $\mathrm{wlp}(L, Q)$ is the weakest inductive invariant adequate for $Q$.

Proof. The hypotheses say exactly $\models I \to G(I)$. By the Knaster-Tarski theorem, the greatest fixed point of a monotone function is the join of all its post-fixed points, so $I$ implies it. The second statement holds because $\mathrm{wlp}(L, Q)$ is itself a fixed point of $G$, and thus inductive and adequate. $\square$

Dijkstra's paper gives the same fact in two theorems about the `do` construct. For a predicate $P$ with $\models P \land BB \to \mathrm{wp}(\mathtt{if}\ldots\mathtt{fi}, P)$, it shows $\models P \land \mathrm{wp}(\mathtt{do}\ldots\mathtt{od}, \top) \to \mathrm{wp}(\mathtt{do}\ldots\mathtt{od}, P \land \neg BB)$. If in addition a variant $t$ satisfies $t \geq 0$ under $P \land BB$ and every enabled branch decreases $t$, the conjunct $\mathrm{wp}(\mathtt{do}\ldots\mathtt{od}, \top)$ can be dropped.

### Relative completeness of Hoare logic

The transformer gives a canonical proof of any valid triple.

Theorem. Assume that the assertion language is expressive, so that each $\mathrm{wlp}(c, Q)$ is definable by an assertion, and assume that all valid assertions are available to the consequence rule. Then for all $c$ and $Q$, $\vdash \{\mathrm{wlp}(c, Q)\}\ c\ \{Q\}$. Consequently, $\models \{P\}\ c\ \{Q\}$ implies $\vdash \{P\}\ c\ \{Q\}$.

Proof. By structural induction on $c$, for all $Q$ simultaneously.

- Case skip and assign. These are the axioms, since the wlp is $Q$ and $Q[e/x]$.
- Case $c_1 ; c_2$. By the hypothesis for $c_2$, $\vdash \{\mathrm{wlp}(c_2, Q)\}\ c_2\ \{Q\}$. By the hypothesis for $c_1$ with postcondition $\mathrm{wlp}(c_2, Q)$, $\vdash \{\mathrm{wlp}(c_1, \mathrm{wlp}(c_2, Q))\}\ c_1\ \{\mathrm{wlp}(c_2, Q)\}$. Apply seq.
- Case if. Let $W$ be the wlp of the conditional. Then $W \land b \to \mathrm{wlp}(c_1, Q)$ and $W \land \neg b \to \mathrm{wlp}(c_2, Q)$. Apply the hypotheses, consequence and the if rule.
- Case while. Let $W \equiv \mathrm{wlp}(L, Q)$. Since $W$ is a fixed point of $G$, $\models W \land b \to \mathrm{wlp}(c, W)$ and $\models W \land \neg b \to Q$. The induction hypothesis for $c$ with postcondition $W$ gives $\vdash \{\mathrm{wlp}(c, W)\}\ c\ \{W\}$. Consequence gives $\vdash \{W \land b\}\ c\ \{W\}$. The while rule gives $\vdash \{W\}\ L\ \{W \land \neg b\}$, and consequence gives the postcondition $Q$.

For the last claim, $\models \{P\}\ c\ \{Q\}$ gives $\models P \to \mathrm{wlp}(c, Q)$ by the characterization theorem, and one more use of consequence finishes the proof. $\square$

The statement must quantify over all $Q$, because the while case applies the hypothesis to the new postcondition $W$. The proof uses $W$ as the invariant, which is a formula in arithmetic built with Gödel coding. It proves existence of an invariant and gives no practical way to find a readable one.

### Strongest postconditions

The forward dual is $\mathrm{sp}(c, P) = \{\sigma' : \exists \sigma \models P.\ \langle c, \sigma\rangle \Downarrow \sigma'\}$, the set of states reachable from $P$. Its calculation rules are:

$$\mathrm{sp}(\mathtt{skip}, P) \equiv P \qquad \mathrm{sp}(x := e, P) \equiv \exists x_0.\ P[x_0/x] \land x = e[x_0/x] \qquad \mathrm{sp}(c_1 ; c_2, P) \equiv \mathrm{sp}(c_2, \mathrm{sp}(c_1, P))$$

$$\mathrm{sp}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, P) \equiv \mathrm{sp}(c_1, P \land b) \lor \mathrm{sp}(c_2, P \land \neg b)$$

$$\mathrm{sp}(\mathtt{while}\ b\ \mathtt{do}\ c, P) \equiv \neg b \land \mu X.\ (P \lor \mathrm{sp}(c, X \land b)).$$

Theorem (duality). $\models \mathrm{sp}(c, P) \to Q$ if and only if $\models P \to \mathrm{wlp}(c, Q)$. Both are equivalent to $\models \{P\}\ c\ \{Q\}$.

So $\mathrm{sp}(c, \cdot)$ and $\mathrm{wlp}(c, \cdot)$ form a Galois connection on the lattice of predicates. Forward reasoning corresponds to symbolic execution and to the post-image in model checking. It introduces an existential at each assignment, which a verifier can avoid by renaming variables. Backward reasoning introduces no quantifiers at assignments, at the cost of substitution. The renaming trick and the absence of quantifiers meet in the passive form of the next topic.

## Worked examples

### Example 1: a conditional and an assignment

Compute $\mathrm{wp}(S, Q)$ for

```
if x < y then m := y else m := x ;
z := m + 1
```

with $Q \equiv z > x \land z > y$.

```
wp(z := m + 1, Q)         = m + 1 > x ∧ m + 1 > y                  call this R
wp(m := y, R)             = y + 1 > x ∧ y + 1 > y  ≡  y + 1 > x
wp(m := x, R)             = x + 1 > x ∧ x + 1 > y  ≡  x + 1 > y
wp(if ..., R)             = (x < y → y + 1 > x) ∧ (¬(x < y) → x + 1 > y)
```

The first implication is valid, because $x < y$ gives $y + 1 > x$. The second is valid, because $x \geq y$ gives $x + 1 > y$. So $\mathrm{wp}(S, Q) \equiv \top$, and the program establishes $Q$ from every state.

### Example 2: wp and wlp of a loop by iteration

Let $L \equiv \mathtt{while}\ x \neq 0\ \mathtt{do}\ x := x - 1$.

For $Q \equiv x = 0$:

```
H0 = x = 0 ∧ ¬(x ≠ 0)                         ≡ x = 0
H1 = H0 ∨ (x ≠ 0 ∧ H0[x-1/x])
   = x = 0 ∨ (x ≠ 0 ∧ x - 1 = 0)              ≡ x = 0 ∨ x = 1
H2 = H0 ∨ (x ≠ 0 ∧ (x - 1 = 0 ∨ x - 1 = 1))   ≡ 0 ≤ x ≤ 2
```

The pattern is $H_k \equiv 0 \leq x \leq k$. To prove this, assume it for $k$. Then $H_{k+1} \equiv x = 0 \lor (x \neq 0 \land 0 \leq x - 1 \leq k) \equiv 0 \leq x \leq k + 1$. Therefore

$$\mathrm{wp}(L, x = 0) \equiv \exists k \geq 0.\ 0 \leq x \leq k \equiv x \geq 0.$$

For the liberal version, start from $\top$:

```
L0 = ⊤
L1 = (x ≠ 0 → ⊤[x-1/x]) ∧ (x = 0 → x = 0)     ≡ ⊤
```

The iteration has converged at once, so $\mathrm{wlp}(L, x = 0) \equiv \top$. This agrees with the reading of the loop: when it terminates, it has $x = 0$, whatever the initial state.

The pairing theorem can be checked here. For $Q \equiv \top$ the same iteration gives $H_0 \equiv x = 0$ and thus $\mathrm{wp}(L, \top) \equiv x \geq 0$. Then $\mathrm{wp}(L, \top) \land \mathrm{wlp}(L, x = 0) \equiv x \geq 0$, as computed.

For a postcondition that the loop can never establish, take $Q \equiv x = 5$. Then $H_0 \equiv x = 0 \land x = 5 \equiv \bot$, and all $H_k \equiv \bot$, so $\mathrm{wp}(L, x = 5) \equiv \bot$. The liberal iteration gives:

```
L0 = ⊤
L1 = (x ≠ 0 → ⊤) ∧ (x = 0 → x = 5)                ≡ x ≠ 0
L2 = (x ≠ 0 → x - 1 ≠ 0) ∧ (x = 0 → x = 5)        ≡ x ≠ 0 ∧ x ≠ 1
Lk ≡ x ∉ {0, ..., k-1}
```

The intersection over all $k$ is $x < 0$. Thus $\mathrm{wlp}(L, x = 5) \equiv x < 0$, which is the set of states from which the loop diverges and the triple holds vacuously.

### Example 3: subtractive gcd with nondeterministic guards

Let the program be

```
do x > y → x := x - y
 □ y > x → y := y - x
od
```

and let $P \equiv x > 0 \land y > 0 \land \gcd(x, y) = G$, with $G$ a logical variable. The goal is $P \to \mathrm{wp}(\mathtt{do}\ldots\mathtt{od}, x = G)$. Use Dijkstra's variant theorem with $t \equiv x + y$. Compute the one-step transformer, where $BB \equiv x > y \lor y > x$:

```
wp(IF, P) = BB
          ∧ (x > y → x - y > 0 ∧ y > 0 ∧ gcd(x - y, y) = G)
          ∧ (y > x → x > 0 ∧ y - x > 0 ∧ gcd(x, y - x) = G)
```

Show that $P \land BB$ implies each part. $BB$ is a conjunct of the assumption. For the first implication, $x > y$ gives $x - y > 0$, and $\gcd(x - y, y) = \gcd(x, y)$, because a number $d$ divides both $x$ and $y$ if and only if it divides both $x - y$ and $y$. The second implication is symmetric.

For the variant, the requirement is that each branch decreases $t$ whenever $P \land BB$ holds. Let $t_0$ be the value of $t$ before the step:

```
wp(IF, x + y < t0) = BB
                   ∧ (x > y → (x - y) + y < t0)
                   ∧ (y > x → x + (y - x) < t0)
                   ≡ BB ∧ (x > y → x < t0) ∧ (y > x → y < t0)
```

With $t_0 = x + y$ and $x, y > 0$ this holds. Also $t \geq 0$ under $P$.

The theorem gives $P \to \mathrm{wp}(\mathtt{do}\ldots\mathtt{od}, P \land \neg BB)$. Finally $P \land \neg BB$ gives $x = y$, so $G = \gcd(x, x) = x$, and monotonicity yields the goal.

The example also shows the nondeterministic form at work. The guards are mutually exclusive, so this program happens to be deterministic, but adding a third branch such as $x = y \to \mathtt{skip}$ would add a conjunct to the calculation without changing the method, and termination would then fail, as the variant condition on that branch would show.

The implications in Examples 1 to 3 were checked with an SMT solver or by exhaustive runs over a finite range of integers.

## Common mistakes

1. Confusing $\mathrm{wp}$ and $\mathrm{wlp}$. For $\mathtt{while}\ \top\ \mathtt{do}\ \mathtt{skip}$, $\mathrm{wlp}(\cdot, \bot) \equiv \top$ and $\mathrm{wp}(\cdot, \top) \equiv \bot$.
2. Writing the wp of a guarded `if` without the $BB$ conjunct. If no guard holds the command fails, so $\mathrm{wp}(\mathtt{if}\ x > 0 \to \mathtt{skip}\ \mathtt{fi}, \top) \equiv x > 0$ and the result is not $\top$.
3. Substituting in the wrong order in a sequence. $\mathrm{wp}(S;T, Q)$ first transforms $Q$ by $T$, the last command, and then by $S$.
4. Applying a simultaneous substitution in place of a sequential one. For $x := y ;\ y := x$, the wp of $y = 1$ is first $x = 1$ and then $y = 1$, and the swap reading would give a different answer.
5. Assuming the wlp of a loop can always be computed by iterating to convergence. The iteration usually does not converge in finitely many steps, as in the second part of Example 2.
6. Expecting $\exists k.\ H_k$ to be correct under unbounded nondeterminism. See Exercise 9.
7. Assuming that the weakest precondition is the invariant you should write down. The wlp of a loop is the weakest adequate invariant, and in practice it is usually much more complicated than some stronger invariant that is simple to state.
8. Thinking $\mathrm{wp}$ needs a quantifier at assignments. Backward substitution needs none. Quantifiers enter the wp at havoc statements, in the rule for procedure calls and in array postconditions.

## Exercises

### Exercise 1

Compute and simplify over the integers.

(a) $\mathrm{wp}(x := x + 1,\ x > 0)$

(b) $\mathrm{wp}(\mathtt{if}\ x > 0\ \mathtt{then}\ y := x\ \mathtt{else}\ y := -x,\ y > 3)$

(c) $\mathrm{wp}(\mathtt{abort}, \top)$ and $\mathrm{wlp}(\mathtt{abort}, \bot)$

<details><summary>Solution</summary>

(a) $x + 1 > 0$, which is $x \geq 0$.

(b) $(x > 0 \to x > 3) \land (x \leq 0 \to -x > 3)$. On the integers this is equivalent to $x > 3 \lor x < -3$.

(c) $\bot$ and $\top$ respectively. The first says that abort never succeeds, and the second says that it has no terminating runs to violate anything.

</details>

### Exercise 2

Compute $\mathrm{wp}(x := x + y ;\ y := x - y ;\ x := x - y,\ x = A \land y = B)$.

<details><summary>Solution</summary>

```
after last assignment:   x - y = A ∧ y = B
after second assignment: x - (x - y) = A ∧ x - y = B   ≡  y = A ∧ x - y = B
after first assignment:  y = A ∧ (x + y) - y = B       ≡  y = A ∧ x = B
```

</details>

### Exercise 3

Let $c \equiv x := 1 ;\ \mathtt{if}\ y > 0\ \mathtt{then}\ x := x + y\ \mathtt{else}\ \mathtt{skip}$. Compute $\mathrm{wp}(c, x > 2)$, and find the weakest $P$ such that $[P]\ c\ [x > 2]$ holds.

<details><summary>Solution</summary>

The conditional gives $(y > 0 \to x + y > 2) \land (y \leq 0 \to x > 2)$. Substituting $x := 1$ gives $(y > 0 \to 1 + y > 2) \land (y \leq 0 \to 1 > 2)$, which simplifies to $(y > 0 \to y > 1) \land y > 0$, and then to $y > 1$. So $P \equiv y > 1$, by the characterization theorem.

</details>

### Exercise 4

Let $L \equiv \mathtt{while}\ x \neq 1\ \mathtt{do}\ x := x - 2$. Compute $\mathrm{wp}(L, \top)$ with the iteration $H_k$, and compute $\mathrm{wlp}(L, \top)$.

<details><summary>Solution</summary>

$H_0 \equiv \top \land \neg(x \neq 1) \equiv x = 1$.

$H_{k+1} \equiv x = 1 \lor (x \neq 1 \land H_k[x - 2/x])$.

So $H_1 \equiv x \in \{1, 3\}$, and by induction $H_k \equiv x \in \{1, 3, \ldots, 2k + 1\}$. Therefore $\mathrm{wp}(L, \top) \equiv \exists k \geq 0.\ x = 2k + 1$, which says that $x$ is odd and positive.

$\mathrm{wlp}(L, \top) \equiv \top$ for every command, since every terminating run ends in a state satisfying $\top$.

</details>

### Exercise 5

Using the semantic definitions:

(a) Prove conjunctivity and monotonicity of $\mathrm{wp}$ for IMP.

(b) Prove disjunctivity with equivalence for IMP.

(c) Show that the implication in disjunctivity cannot be reversed for nondeterministic programs.

<details><summary>Solution</summary>

(a) For conjunctivity, a state satisfies $\mathrm{wp}(c, Q) \land \mathrm{wp}(c, R)$ when all runs terminate and end in $Q$, and all runs terminate and end in $R$. This is the same as all runs terminating and ending in $Q \land R$. For monotonicity, if $\models Q \to R$, then a run ending in $Q$ also ends in $R$.

(b) In IMP there is at most one run. So $\sigma \models \mathrm{wp}(c, Q \lor R)$ means that the unique run terminates in $\sigma'$ with $\sigma' \models Q$ or $\sigma' \models R$. This is $\sigma \models \mathrm{wp}(c, Q)$ or $\sigma \models \mathrm{wp}(c, R)$.

(c) Let $S \equiv \mathtt{if}\ \top \to x := 1\ \square\ \top \to x := 2\ \mathtt{fi}$, with $Q \equiv x = 1$ and $R \equiv x = 2$. Then $\mathrm{wp}(S, Q \lor R) \equiv \top$, since both runs land in $Q \lor R$. But $\mathrm{wp}(S, Q) \equiv \bot$ and $\mathrm{wp}(S, R) \equiv \bot$, because in each case one run misses the target.

</details>

### Exercise 6

(a) Compute $\mathrm{sp}(x := x + 1,\ x > 0)$ and eliminate the quantifier.

(b) Prove the duality theorem.

<details><summary>Solution</summary>

(a) $\exists x_0.\ x_0 > 0 \land x = x_0 + 1$. Eliminating $x_0 = x - 1$ gives $x - 1 > 0$, which is $x > 1$.

(b) Assume $\models \mathrm{sp}(c, P) \to Q$. Let $\sigma \models P$ with $\langle c,\sigma\rangle \Downarrow \sigma'$. Then $\sigma' \in \mathrm{sp}(c, P)$, so $\sigma' \models Q$. This shows $\sigma \models \mathrm{wlp}(c, Q)$.

Conversely, assume $\models P \to \mathrm{wlp}(c, Q)$. Let $\sigma' \in \mathrm{sp}(c, P)$. By definition there is $\sigma \models P$ with $\langle c,\sigma\rangle \Downarrow \sigma'$. Then $\sigma \models \mathrm{wlp}(c, Q)$, so $\sigma' \models Q$.

</details>

### Exercise 7

Prove directly from the semantic definition, with no appeal to Knaster-Tarski, that $W \equiv \mathrm{wlp}(L, Q)$ is the weakest predicate $X$ satisfying $\models X \land b \to \mathrm{wlp}(c, X)$ and $\models X \land \neg b \to Q$.

<details><summary>Solution</summary>

First, $W$ satisfies both. Suppose $\sigma \models W \land \neg b$. The loop terminates at $\sigma$ at once, so $\sigma \models Q$. Suppose $\sigma \models W \land b$, and $\langle c,\sigma\rangle \Downarrow \sigma''$. To show $\sigma'' \models W$, let $\langle L,\sigma''\rangle \Downarrow \sigma'$. Then $\langle L,\sigma\rangle \Downarrow \sigma'$ by the true-guard rule, so $\sigma' \models Q$. Hence $\sigma'' \models W$, and $\sigma \models \mathrm{wlp}(c, W)$.

Second, let $X$ satisfy both, and let $\sigma \models X$. Take any terminating run $\langle L,\sigma\rangle \Downarrow \sigma'$, and proceed by induction on its derivation. If $\sigma \models \neg b$ then $\sigma' = \sigma$, and $X \land \neg b \to Q$ gives $\sigma' \models Q$. If $\sigma \models b$, then the run factors through $\sigma''$ with $\langle c,\sigma\rangle \Downarrow \sigma''$, and $\sigma'' \models X$ since $\sigma \models \mathrm{wlp}(c, X)$. The induction hypothesis on the shorter run gives $\sigma' \models Q$. So $\sigma \models W$.

</details>

### Exercise 8

Use wp to derive code. An integer square root program maintains $r \geq 0 \land r^2 \leq n \land s = (r+1)^2$ and has this form:

```
r := 0 ; s := 1 ;
while s ≤ n do ( s := s + E ; r := r + 1 )
```

Find the expression $E$, and show that the invariant is preserved and that it yields $r^2 \leq n < (r+1)^2$ at exit. Assume $n \geq 0$.

<details><summary>Solution</summary>

Compute the wp of the conjunct that constrains $s$:

$$\mathrm{wp}(s := s + E ;\ r := r + 1,\ s = (r+1)^2) \equiv s + E = (r+2)^2.$$

Under $s = (r+1)^2$ this requires $E = (r+2)^2 - (r+1)^2 = 2r + 3$.

The other conjuncts transform to $r + 1 \geq 0$ and $(r+1)^2 \leq n$. The first follows from $r \geq 0$. The second follows from the guard $s \leq n$ with $s = (r+1)^2$.

Initiation: at $r = 0, s = 1$ we have $0 \leq n$ and $1 = (0+1)^2$.

Exit: $\neg(s \leq n)$ with $s = (r+1)^2$ gives $n < (r+1)^2$, and $r^2 \leq n$ comes from the invariant.

</details>

### Exercise 9

Add the unbounded choice $x := {?}$, which assigns any natural number, with $\mathrm{wp}(x := {?}, Q) \equiv \forall v \geq 0.\ Q[v/x]$. Consider

```
do b = 0 → x := ? ; b := 1
 □ b = 1 ∧ x > 0 → x := x - 1
od
```

Show that every run from $b = 0$ terminates, and that $\exists k.\ H_k$ for $Q \equiv \top$ is false at $b = 0$. Conclude that the iteration is incomplete for this language.

<details><summary>Solution</summary>

From $b = 0$, the first step sets $b := 1$ and chooses $v \geq 0$ for $x$. Then $x$ decreases to $0$ after $v$ steps, and at that point no guard is true. So every run terminates, though with no uniform bound on its length.

Compute the iteration. $\neg BB \equiv b \neq 0 \land (b \neq 1 \lor x \leq 0)$. So at $b = 1$, $H_0$ means $x \leq 0$, and at $b = 0$, $H_0$ is false.

By induction, for all $k$, $H_k$ at $b = 1$ means $x \leq k$. The step at $b = 1$ with $x > 0$ requires $x - 1 \leq k - 1$.

For $k \geq 1$, $H_k$ at $b = 0$ requires $\forall v \geq 0.\ H_{k-1}[1/b, v/x]$, which is $\forall v \geq 0.\ v \leq k - 1$, and this is false. So at $b = 0$, $H_k$ is false for every $k$, and $\exists k.\ H_k$ is false, even though all runs terminate. The true wp is the least fixed point, which requires iteration to the ordinal $\omega + 1$ or beyond.

</details>

### Exercise 10

Show that the rule $\mathrm{wp}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, Q) \equiv \mathrm{wp}(c_1, Q) \land \mathrm{wp}(c_2, Q)$ is wrong, and show exactly how the two forms of the correct rule are equivalent.

<details><summary>Solution</summary>

For a counterexample, take $c_1 \equiv x := 1$, $c_2 \equiv x := 2$, $b \equiv y > 0$ and $Q \equiv x = 1$. The wrong rule yields $\bot$, since $\mathrm{wp}(c_2, Q) \equiv \bot$. The true wp is $y > 0$.

For the equivalence, let $A \equiv \mathrm{wp}(c_1, Q)$ and $B \equiv \mathrm{wp}(c_2, Q)$. Case on $b$. If $b$ is true, then $(b \to A) \land (\neg b \to B)$ reduces to $A$, and $(b \land A) \lor (\neg b \land B)$ also reduces to $A$. If $b$ is false, both reduce to $B$. Since the formulas agree in both cases, they are equivalent.

The wrong rule is the one that applies to an assume-based choice with no guard conditions in the branches. In [Verification Conditions](../verification-conditions/) the guards appear as $\mathtt{assume}\ b$ inside each branch, and that is why a plain conjunction is correct there.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Define $\mathrm{wp}$, $\mathrm{wlp}$ and $\mathrm{sp}$ semantically and state how each relates to a triple.
- Write the calculation table from memory, including abort and guarded `if`.
- Compute wp through a sequence of assignments and conditionals, with simplification.
- Compute $H_k$ for a simple loop, conjecture a closed form and prove it by induction.
- Give the least and greatest fixed-point characterizations, and explain which is which.
- Prove the relative completeness theorem by structural induction, including the while case.
- Give an example separating wp from wlp, and an example showing that disjunctivity fails for nondeterminism.

## Materials

- Dijkstra, Guarded Commands, Nondeterminacy and Formal Derivation of Programs, CACM 1975. Read it for the original definitions of $\mathrm{wp}$, the healthiness properties, the $H_k$ iteration and the invariance theorems for `do`. A [transcription as EWD472](https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD472.html) is available online.
- Bradley and Manna, The Calculus of Computation. Read its program correctness material for wp and sp in a form aimed at automation, with verification conditions over first-order theories.
- Dijkstra, A Discipline of Programming, 1976. Read it for the extended development of program derivation from predicate transformers.
- Gries, The Science of Programming, 1981. Read it for many graded exercises in calculating with wp and deriving programs.
- Dijkstra and Scholten, Predicate Calculus and Program Semantics, 1990. Read it for the lattice-theoretic treatment of predicate transformers and the role of unbounded nondeterminism.
