# Axiomatic Semantics

Part 1, Chapter 3: Semantics and Types.

## Objective

Relate Hoare-style program logics to operational semantics through soundness.

## Why this matters

An axiomatic semantics defines the meaning of a program by what can be proved about it. Every deductive verifier rests on such a logic, and this topic establishes why trusting that logic is justified. [Chapter 7](../../../part-2-core-reasoning/07-deductive-verification/) teaches you to use [Hoare Logic](../../../part-2-core-reasoning/07-deductive-verification/hoare-logic/) and [Weakest Preconditions](../../../part-2-core-reasoning/07-deductive-verification/weakest-preconditions/) at scale. Here the focus is on the metatheory: soundness against the operational semantics and relative completeness. An applied scientist who extends a verifier with a new language feature must extend its logic, and each such extension requires a soundness argument of the kind developed here.

## Prerequisites

- [Operational Semantics](../operational-semantics/), for the big-step judgment that defines validity.
- [Induction Principles](../induction-principles/), for rule induction.
- [First-Order Logic](../../01-mathematical-logic/first-order-logic/), for the assertion language and its semantics.
- [Soundness and Completeness](../../01-mathematical-logic/soundness-and-completeness/), for the distinction between $\vdash$ and $\models$.
- [Undecidability of Logic and Incompleteness](../../02-decidability-and-complexity/undecidability-of-logic-and-incompleteness/), for the limits on completeness.

## Lesson

### Assertions and triples

Assertions are first-order formulas over the integers, built from IMP arithmetic expressions:

$$P ::= \top \mid \bot \mid a_1 = a_2 \mid a_1 \le a_2 \mid \neg P \mid P_1 \land P_2 \mid P_1 \lor P_2 \mid P_1 \to P_2 \mid \forall z.\ P \mid \exists z.\ P$$

The relation $\sigma \models P$ is the usual first-order satisfaction relation over $\mathbb{Z}$, with the state supplying the values of free variables. So $\sigma \models \forall z.\ P$ iff $\sigma[z \mapsto v] \models P$ for all $v \in \mathbb{Z}$. An assertion $P$ is valid, written $\models P$, if $\sigma \models P$ for all $\sigma$.

A variable that the program does not mention is called a logical variable. Since validity quantifies over all states, logical variables behave like universally quantified parameters. The triple $\{x = u\}\ x := x + 1\ \{x = u + 1\}$ relates the final value of $x$ to its initial value through $u$.

Definition. The partial correctness triple $\{P\}\,c\,\{Q\}$ is valid, written $\models \{P\}\,c\,\{Q\}$, if

$$\forall \sigma, \sigma'.\ \sigma \models P \land \langle c, \sigma\rangle \Downarrow \sigma' \to \sigma' \models Q.$$

The total correctness triple $[P]\,c\,[Q]$ is valid if

$$\forall \sigma.\ \sigma \models P \to \exists \sigma'.\ \langle c, \sigma\rangle \Downarrow \sigma' \land \sigma' \models Q.$$

A partial correctness triple says nothing about runs that diverge. Validity is a semantic notion that depends on the operational semantics. Derivability, defined next, is a syntactic notion, and the theorems of this topic relate the two.

### Hoare logic

The judgment $\vdash \{P\}\,c\,\{Q\}$ is defined inductively by the following rules.

$$\frac{}{\vdash \{Q\}\ \texttt{skip}\ \{Q\}}\ \text{(H-Skip)} \qquad \frac{}{\vdash \{Q[a/x]\}\ x := a\ \{Q\}}\ \text{(H-Assign)}$$

$$\frac{\vdash \{P\}\,c_1\,\{R\} \quad \vdash \{R\}\,c_2\,\{Q\}}{\vdash \{P\}\,c_1 ; c_2\,\{Q\}}\ \text{(H-Seq)}$$

$$\frac{\vdash \{P \land b\}\,c_1\,\{Q\} \quad \vdash \{P \land \neg b\}\,c_2\,\{Q\}}{\vdash \{P\}\ \texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2\ \{Q\}}\ \text{(H-If)}$$

$$\frac{\vdash \{I \land b\}\,c\,\{I\}}{\vdash \{I\}\ \texttt{while}\ b\ \texttt{do}\ c\ \{I \land \neg b\}}\ \text{(H-While)}$$

$$\frac{\models P \to P' \quad \vdash \{P'\}\,c\,\{Q'\} \quad \models Q' \to Q}{\vdash \{P\}\,c\,\{Q\}}\ \text{(H-Cons)}$$

Boolean expressions are read as assertions in the evident way, so $\sigma \models b$ iff $\mathcal{B}[\![b]\!]\sigma = \mathrm{tt}$. The substitution $Q[a/x]$ replaces free occurrences of $x$ by $a$, renaming bound variables to avoid capture.

The assignment rule looks backwards on first reading. The reason is that $Q[a/x]$ says of the initial state exactly what $Q$ says of the final state, as the next lemma shows. This relies on the fact that expressions have no side effects, are total, and that distinct variables do not alias.

The rule H-Cons refers to semantic validity of assertions. The logic therefore has an oracle for arithmetic built in, and a practical system would replace it by a theorem prover or an SMT solver. This separates program reasoning, handled by the Hoare rules, from data reasoning, handled by the oracle.

Hoare introduced this style in 1969, building on Floyd's 1967 method of attaching assertions to flowcharts.

### Soundness

Lemma 1 (substitution). For all $P, a, x, \sigma$,

$$\sigma \models P[a/x] \quad \text{iff} \quad \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma] \models P.$$

Proof. Use structural induction on $P$, with $\sigma$ universally quantified. For atomic formulas, this follows from the substitution lemma for arithmetic expressions proved in [Induction Principles](../induction-principles/). The connectives are immediate from the hypothesis.

Consider $P = \forall z.\ P_0$. If $z = x$, the substitution has no effect and $x$ is not free in $P$, so the two states agree on the free variables of $P$. Otherwise, rename so that $z$ does not occur in $a$. Then

$$\sigma \models (\forall z.\ P_0)[a/x] \iff \forall v.\ \sigma[z \mapsto v] \models P_0[a/x] \iff \forall v.\ \sigma[z \mapsto v][x \mapsto \mathcal{A}[\![a]\!](\sigma[z \mapsto v])] \models P_0.$$

Because $z$ is not in $a$, $\mathcal{A}[\![a]\!](\sigma[z \mapsto v]) = \mathcal{A}[\![a]\!]\sigma$. Because $z \ne x$, the two updates commute. So the last condition is $\forall v.\ \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma][z \mapsto v] \models P_0$, which is $\sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma] \models \forall z.\ P_0$. The other quantifier is analogous. $\square$

Theorem 2 (soundness). If $\vdash \{P\}\,c\,\{Q\}$, then $\models \{P\}\,c\,\{Q\}$.

Proof. Use rule induction on the derivation of the triple.

Case H-Skip. If $\sigma \models Q$ and $\langle \texttt{skip}, \sigma\rangle \Downarrow \sigma'$, inversion gives $\sigma' = \sigma$.

Case H-Assign. If $\sigma \models Q[a/x]$ and $\langle x := a, \sigma\rangle \Downarrow \sigma'$, inversion gives $\sigma' = \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]$. Lemma 1 gives $\sigma' \models Q$.

Case H-Seq. If $\sigma \models P$ and $\langle c_1 ; c_2, \sigma\rangle \Downarrow \sigma''$, inversion gives $\sigma'$ with $\langle c_1, \sigma\rangle \Downarrow \sigma'$ and $\langle c_2, \sigma'\rangle \Downarrow \sigma''$. The hypothesis for $c_1$ gives $\sigma' \models R$, and the hypothesis for $c_2$ gives $\sigma'' \models Q$.

Case H-If. If $\sigma \models P$, invert the big-step derivation. If B-IfT was used, then $\sigma \models P \land b$ and $\langle c_1, \sigma\rangle \Downarrow \sigma'$, and the first hypothesis applies. B-IfF is symmetric.

Case H-Cons. If $\sigma \models P$, then $\sigma \models P'$. If $\langle c, \sigma\rangle \Downarrow \sigma'$, the hypothesis gives $\sigma' \models Q'$, and so $\sigma' \models Q$.

Case H-While. The hypothesis is $\models \{I \land b\}\,c\,\{I\}$. We prove by an inner rule induction on the big-step derivation that for every derivable $\langle c', \sigma\rangle \Downarrow \sigma'$, if $c' = \texttt{while}\ b\ \texttt{do}\ c$ and $\sigma \models I$, then $\sigma' \models I \land \neg b$. Rules that conclude about other commands are vacuous.

For B-WhileF, $\sigma' = \sigma$ and the guard is false, so $\sigma' \models I \land \neg b$.

For B-WhileT, the guard is true at $\sigma$, with $\langle c, \sigma\rangle \Downarrow \tau$ and $\langle \texttt{while}\ b\ \texttt{do}\ c, \tau\rangle \Downarrow \sigma'$. Since $\sigma \models I \land b$, the outer hypothesis gives $\tau \models I$. The inner hypothesis for the second premise gives $\sigma' \models I \land \neg b$. $\square$

The two inductions in this proof have different roles. The outer one is on the proof of the triple, and the inner one is on the execution. A denotational proof of the while case by fixed-point induction is Exercise 7 of [Denotational Semantics](../denotational-semantics/).

### Total correctness

The partial rule says nothing about termination. For total correctness, H-While is replaced by a rule with a variant $t$, an integer expression, and with $z$ a logical variable that occurs in none of $I$, $b$, $c$ and $t$:

$$\frac{\vdash [I \land b \land t = z]\,c\,[I \land t < z] \quad \models I \land b \to t \ge 0}{\vdash [I]\ \texttt{while}\ b\ \texttt{do}\ c\ [I \land \neg b]}\ \text{(H-WhileT)}$$

The other rules are the same, with brackets in place of braces.

Theorem 3. The rule H-WhileT preserves validity of total correctness triples.

Proof. Assume both premises are valid. Since $z$ does not occur in $c$, the command does not change $z$, and runs of $c$ from states that differ only at $z$ correspond. Hence a triple about $c$ may be applied to $\sigma[z \mapsto k]$ for any $k$.

We prove by course-of-values induction on $k \in \mathbb{N}$ that if $\sigma \models I$, $\sigma \models b$ and $\mathcal{A}[\![t]\!]\sigma = k$, then there is $\sigma'$ with $\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma\rangle \Downarrow \sigma'$ and $\sigma' \models I \land \neg b$.

Applying the first premise at $\sigma[z \mapsto k]$ gives a terminating run of $c$ whose result satisfies $I$ and $t < k$. Because $z$ does not occur in $c$, $I$, $b$ or $t$, restoring the value of $z$ gives $\tau$ with $\langle c, \sigma\rangle \Downarrow \tau$, $\tau \models I$ and $\mathcal{A}[\![t]\!]\tau < k$. If $\tau \models \neg b$, then B-WhileF gives $\langle W, \tau\rangle \Downarrow \tau$ for the loop $W$. If $\tau \models b$, the second premise gives $\mathcal{A}[\![t]\!]\tau \ge 0$, and the hypothesis at the smaller value gives a result for $W$ from $\tau$. In both cases B-WhileT concludes.

Finally, let $\sigma \models I$. If $\sigma \models \neg b$, B-WhileF applies. Otherwise, the second premise gives $\mathcal{A}[\![t]\!]\sigma \in \mathbb{N}$, and the claim applies. $\square$

The induction is well-founded induction with the measure $t$, and this is the role of ranking functions in [Loop Invariants](../../../part-2-core-reasoning/07-deductive-verification/loop-invariants/). Natural numbers suffice for IMP. Languages with unbounded nondeterminism can require ordinal-valued variants.

### Weakest liberal preconditions

Definition. For a command $c$ and an assertion $Q$, the weakest liberal precondition is the set of states

$$\mathrm{wlp}(c, Q) = \{\sigma \mid \forall \sigma'.\ \langle c, \sigma\rangle \Downarrow \sigma' \to \sigma' \models Q\}.$$

Directly from the definitions, $\models \{P\}\,c\,\{Q\}$ iff every state satisfying $P$ lies in $\mathrm{wlp}(c, Q)$. So $\mathrm{wlp}(c, Q)$ is the weakest $P$ making the triple valid.

The following equations hold, with the assertions on the right read as sets of states, and they are proved by inversion on the big-step rules.

$$\mathrm{wlp}(\texttt{skip}, Q) = Q, \qquad \mathrm{wlp}(x := a, Q) = Q[a/x], \qquad \mathrm{wlp}(c_1 ; c_2, Q) = \mathrm{wlp}(c_1, \mathrm{wlp}(c_2, Q)),$$

$$\mathrm{wlp}(\texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2, Q) = (b \to \mathrm{wlp}(c_1, Q)) \land (\neg b \to \mathrm{wlp}(c_2, Q)).$$

For loops, the equation is recursive. Let $\Phi(X) = (b \to \mathrm{wlp}(c, X)) \land (\neg b \to Q)$ on sets of states. Then $\mathrm{wlp}(\texttt{while}\ b\ \texttt{do}\ c, Q)$ is the greatest fixed point of the monotone $\Phi$. It is a fixed point because of the unfolding equivalence of [Operational Semantics](../operational-semantics/). It is the greatest because, if $X \subseteq \Phi(X)$, then $X$ is an invariant with $\models \{X \land b\}\,c\,\{X\}$ and $X \land \neg b \subseteq Q$. The while-case argument of Theorem 2 then shows that $X \subseteq \mathrm{wlp}(\texttt{while}\ b\ \texttt{do}\ c, Q)$.

The weakest precondition for total correctness, $\mathrm{wp}(c, Q)$, requires termination as well, and $\mathrm{wp}(\texttt{while}\ b\ \texttt{do}\ c, Q)$ is the least fixed point of the corresponding functional, because termination is witnessed by a finite number of iterations. Dijkstra's predicate transformers of 1975 made this calculus central to program derivation.

A loop-free $\mathrm{wlp}$ is a simple syntactic computation. For a loop, no such recursion exists on syntax, and the greatest fixed point is the reason invariants must be supplied or discovered.

### Relative completeness

Definition. The assertion language is expressive for IMP if for every $c$ and $Q$, there is an assertion $W(c, Q)$ whose models are exactly $\mathrm{wlp}(c, Q)$.

Theorem 4. First-order arithmetic with addition and multiplication is expressive for IMP.

Proof sketch. For each $c$ with variables among $\vec{x}$, define by structural recursion a formula $T_c(\vec{x}, \vec{y})$ meaning $\langle c, \vec{x}\rangle \Downarrow \vec{y}$. The only difficult case is the loop, where $T$ must say that there is a finite sequence of states from $\vec{x}$ to $\vec{y}$, consecutive states being related by $T_{c_0}$ under a true guard, with the guard false at the end. Gödel's $\beta$ function encodes a finite sequence of integers by a pair of numbers using only addition and multiplication, so this quantification over sequences can be expressed. Then $W(c, Q)$ is $\forall \vec{y}.\ T_c(\vec{x}, \vec{y}) \to Q[\vec{y}/\vec{x}]$. $\square$

Theorem 5 (Cook's relative completeness, for IMP). If the assertion language is expressive and $\models \{P\}\,c\,\{Q\}$, then $\vdash \{P\}\,c\,\{Q\}$, where H-Cons may use all valid assertions.

Proof. It suffices to prove $\vdash \{W(c, Q)\}\,c\,\{Q\}$ for all $c$ and $Q$, since validity of the triple gives $\models P \to W(c, Q)$, and H-Cons concludes. Use structural induction on $c$ for all $Q$.

Case $\texttt{skip}$. H-Skip gives $\{Q\}\,\texttt{skip}\,\{Q\}$. Since $\models W(\texttt{skip}, Q) \leftrightarrow Q$, H-Cons concludes.

Case assignment. Similarly, using $\models W(x := a, Q) \leftrightarrow Q[a/x]$.

Case $c_1 ; c_2$. The hypothesis gives $\vdash \{W(c_2, Q)\}\,c_2\,\{Q\}$ and $\vdash \{W(c_1, W(c_2, Q))\}\,c_1\,\{W(c_2, Q)\}$. H-Seq and the sequence equation, with H-Cons, conclude.

Case conditional. The equation gives $\models W(\texttt{if}\ldots, Q) \land b \to W(c_1, Q)$ and $\models W(\texttt{if}\ldots, Q) \land \neg b \to W(c_2, Q)$. The hypotheses, H-Cons and H-If conclude.

Case $W_0 = \texttt{while}\ b\ \texttt{do}\ c$. Let $I = W(W_0, Q)$. First, $\models I \land b \to W(c, I)$. Let $\sigma \models I \land b$ and $\langle c, \sigma\rangle \Downarrow \sigma'$. To show $\sigma' \models I$, let $\langle W_0, \sigma'\rangle \Downarrow \sigma''$. B-WhileT gives $\langle W_0, \sigma\rangle \Downarrow \sigma''$, so $\sigma'' \models Q$. Second, $\models I \land \neg b \to Q$, by B-WhileF. The hypothesis gives $\vdash \{W(c, I)\}\,c\,\{I\}$, H-Cons gives $\vdash \{I \land b\}\,c\,\{I\}$, H-While gives $\vdash \{I\}\,W_0\,\{I \land \neg b\}$, and H-Cons gives $\vdash \{I\}\,W_0\,\{Q\}$. $\square$

The loop case shows that the weakest liberal precondition is itself always an invariant, although it may be a complicated formula.

Absolute completeness is impossible for any proof system with a computably enumerable set of theorems, for two independent reasons.

First, $\models \{\top\}\ \texttt{skip}\ \{P\}$ holds iff $\models P$, so deciding valid triples includes first-order arithmetic truth, which is not computably enumerable by Gödel's incompleteness theorem.

Second, $\models \{\top\}\,c\,\{\bot\}$ holds iff $c$ diverges from all states. Given a Turing machine $M$ and input $w$, one can compute an IMP command that ignores its initial state and simulates $M$ on $w$. Such a command diverges everywhere iff $M$ does not halt on $w$, and non-halting is not computably enumerable.

Relative completeness therefore states the best possible result: the Hoare rules lose nothing, and any incompleteness comes from reasoning about the assertions.

### The denotational reading and variations

With the denotational semantics, partial correctness has a simple reading: $\models \{P\}\,c\,\{Q\}$ iff $\mathcal{C}[\![c]\!](\{\sigma \mid \sigma \models P\}) \subseteq \{\sigma \mid \sigma \models Q\}$, where the function is applied to a set of states. Theorem 3 of [Denotational Semantics](../denotational-semantics/) and Theorem 2 above connect the three styles of semantics.

Hoare triples over-approximate the set of final states. Incorrectness logic, introduced by O'Hearn in 2020, uses triples that under-approximate it, requiring that each state satisfying the postcondition is reachable from a state satisfying the precondition. It is aimed at proving the presence of bugs. The same soundness method applies, using a different validity definition.

## Worked examples

### Worked Example 1: partial correctness of a summation

Let $c$ be $s := 0 ; \texttt{while}\ 1 \le x\ \texttt{do}\ (s := s + x ; x := x - 1)$. We prove

$$\vdash \{x = n \land n \ge 0\}\ c\ \{2s = n(n+1)\}.$$

Here $n$ is a logical variable. The invariant is $I := 2s + x(x+1) = n(n+1) \land x \ge 0$. It expresses that the current sum plus the sum still to be added equals the total.

The proof outline is as follows. Each pair of adjacent assertions without a command between them is an H-Cons step.

```
{ x = n  and  n >= 0 }
{ 2*0 + x*(x+1) = n*(n+1)  and  x >= 0 }                      (V1)
s := 0;
{ I }
while 1 <= x do
    { I  and  1 <= x }
    { 2*(s+x) + (x-1)*x = n*(n+1)  and  x-1 >= 0 }            (V2)
    s := s + x;
    { 2*s + (x-1)*x = n*(n+1)  and  x-1 >= 0 }
    x := x - 1
    { I }
{ I  and  not (1 <= x) }
{ 2*s = n*(n+1) }                                             (V3)
```

The assignment steps are instances of H-Assign, read from bottom to top. For $x := x - 1$, the substitution $I[x-1/x]$ gives $2s + (x-1)((x-1)+1) = n(n+1) \land x - 1 \ge 0$, and $(x-1)((x-1)+1) = (x-1)x$. For $s := s + x$, the substitution replaces $s$ by $s + x$.

The three side conditions are valid arithmetic facts.

(V1). If $x = n$ and $n \ge 0$, then $2 \cdot 0 + x(x+1) = n(n+1)$, and $x \ge 0$.

(V2). Assume $2s + x(x+1) = n(n+1)$, $x \ge 0$ and $1 \le x$. Then $2(s + x) + (x-1)x = 2s + 2x + x^2 - x = 2s + x^2 + x = 2s + x(x+1) = n(n+1)$, and $x - 1 \ge 0$.

(V3). If $x \ge 0$ and $\neg(1 \le x)$, then $x = 0$. So $2s + 0 = n(n+1)$.

Soundness in action. Theorem 2 predicts that $I$ holds at each loop head. For $n = 2$, the concrete run gives the following values.

```
loop head     x    s    2s + x(x+1)    n(n+1)
1st test      2    0    0 + 6 = 6      6
2nd test      1    2    4 + 2 = 6      6
3rd test      0    3    6 + 0 = 6      6
```

At the third test the guard fails, and $2s = 6 = n(n+1)$. A scratch script confirmed the triple and the inductiveness of $I$ on finite ranges of integers.

### Worked Example 2: partial and total correctness differ

Let $W = \texttt{while}\ \neg(x = 0)\ \texttt{do}\ x := x - 1$.

Partial correctness. We claim $\models \{\top\}\ W\ \{x = 0\}$. Take the invariant $I = \top$. The premise of H-While, $\{\top \land \neg(x = 0)\}\ x := x - 1\ \{\top\}$, follows from H-Assign and H-Cons, because $\top[x-1/x]$ is $\top$. H-While gives $\{\top\}\ W\ \{\top \land \neg\neg(x = 0)\}$, and H-Cons gives the claim.

So $\mathrm{wlp}(W, x = 0)$ is the set of all states. The states with $x < 0$ satisfy it vacuously, because $W$ diverges from them.

Total correctness. The triple $[\top]\ W\ [x = 0]$ is invalid, since a state with $x = -1$ diverges. In fact $\mathrm{wp}(W, x = 0)$ is exactly $x \ge 0$. A derivation for that precondition uses $I := x \ge 0$ and variant $t := x$.

First, $\models I \land \neg(x = 0) \to x \ge 0$. Second, we need $[x \ge 0 \land \neg(x = 0) \land x = z]\ x := x - 1\ [x \ge 0 \land x < z]$. H-Assign gives the precondition $x - 1 \ge 0 \land x - 1 < z$, and the implication $x \ge 0 \land x \ne 0 \land x = z \to x - 1 \ge 0 \land x - 1 < z$ holds over the integers. H-WhileT gives $[x \ge 0]\ W\ [x \ge 0 \land \neg\neg(x = 0)]$, and H-Cons gives $[x \ge 0]\ W\ [x = 0]$.

### Worked Example 3: computing wlp for a loop-free program

Compute $\mathrm{wlp}$ of the program $x := x + 1 ; \texttt{if}\ x \le 0\ \texttt{then}\ y := 0 - x\ \texttt{else}\ y := x$ with postcondition $y \ge 2$.

```
wlp(y := 0-x, y>=2)   =  0-x >= 2
wlp(y := x,   y>=2)   =  x >= 2
wlp(if ..., y>=2)     =  (x<=0 -> 0-x >= 2) and (not x<=0 -> x >= 2)
                      =  x <= -2  or  x >= 2             over the integers
wlp(x := x+1, above)  =  x+1 <= -2  or  x+1 >= 2
                      =  x <= -3  or  x >= 1
```

To check the result, consider $x = 0$: then $x$ becomes $1$, the program sets $y$ to $1$, and $y \ge 2$ fails, which matches the fact that $x = 0$ is outside the computed set. For $x = 1$: $x$ becomes $2$ and $y$ becomes $2$. For $x = -3$: $x$ becomes $-2$ and $y$ becomes $2$. For $x = -2$: $x$ becomes $-1$ and $y$ becomes $1$, which is excluded.

## Common mistakes

- Using a forward version of the assignment axiom, $\{Q\}\ x := a\ \{Q[a/x]\}$. For $Q$ being $x = 0$ and $a$ being $1$, it yields $\{x = 0\}\ x := 1\ \{1 = 0\}$, whose postcondition is false in the final state. Correct by substituting into the postcondition to get the precondition.
- Reading partial correctness as a termination claim. The triple $\{\top\}\ \texttt{while}\ \texttt{true}\ \texttt{do}\ \texttt{skip}\ \{\bot\}$ is valid. Use total correctness when termination matters.
- Choosing an invariant that is true at the loop head but not preserved by the body. An invariant must be inductive: $I \land b$ must imply that $I$ holds after $c$. Correct by strengthening it, as $x \ge 0$ was added in Worked Example 1, which is needed to conclude $x = 0$ at exit.
- Omitting the guard in the premise or the conclusion of H-While. The premise needs $b$ for the body, and the conclusion's $\neg b$ is what gives the postcondition its strength.
- Confusing $\vdash$ and $\models$. Soundness and completeness are theorems relating them. They do not hold by definition.
- Stating that Hoare logic is complete without qualification. It is relatively complete, given an expressive assertion language and an oracle for valid assertions.
- Performing naive substitution with binders. The assertion $(\forall y.\ x \le y)[y/x]$ is not $\forall y.\ y \le y$. The bound variable has to be renamed first.
- Applying the assignment axiom when expressions can fail or have side effects, or when two names can alias. Each such feature invalidates Lemma 1 for the extended language, and it requires a modified rule, as with separation logic for pointers.
- Forgetting that a variant must be bounded only when the guard holds. The side condition is $I \land b \to t \ge 0$, and $t$ may be negative at exit.

## Exercises

### Exercise 1

Classify each triple as valid or invalid, for both partial and total correctness: (a) $x = 1$, $x := x + 1$, $x = 2$; (b) $\top$, $\texttt{while}\ \texttt{true}\ \texttt{do}\ \texttt{skip}$, $\bot$; (c) $\bot$, $c$ for any $c$, $Q$ for any $Q$; (d) $\top$, $x := x + 1$, $x > 0$; (e) $x = u$, $x := x + 1$, $x = u + 1$.

<details><summary>Solution</summary>

(a) Valid in both senses, since assignment always terminates and the result is $2$.

(b) Valid for partial correctness, since no run terminates. Invalid for total correctness, since the program does not terminate.

(c) Valid in both senses, since no state satisfies $\bot$.

(d) Invalid in both senses. From $x = -5$, the result is $x = -4$, which is not positive.

(e) Valid in both senses, for each value of the logical variable $u$.

</details>

### Exercise 2

Compute $\mathrm{wlp}(x := x + 1 ; y := 2 \times x, y > x)$ and $\mathrm{wlp}(\texttt{if}\ x \le 0\ \texttt{then}\ y := 0 - x\ \texttt{else}\ y := x, y \ge 1)$. Simplify over the integers.

<details><summary>Solution</summary>

First program. Substituting $2 \times x$ for $y$ gives $2x > x$. Substituting $x + 1$ for $x$ gives $2(x + 1) > x + 1$, which simplifies to $x + 1 > 0$, that is, $x \ge 0$.

Second program. The conditional equation gives $(x \le 0 \to 0 - x \ge 1) \land (\neg(x \le 0) \to x \ge 1)$. The second conjunct is valid over the integers. The first says $x \le 0 \to x \le -1$, which is equivalent to $x \ne 0$. So the result is $x \ne 0$.

</details>

### Exercise 3

Prove $\{x = u \land y = v\}\ x := x + y ; y := x - y ; x := x - y\ \{x = v \land y = u\}$ with a proof outline.

<details><summary>Solution</summary>

Work backwards.

```
{ x = u  and  y = v }
{ y = v  and  (x+y) - y = u }                 H-Cons, valid
x := x + y;
{ y = v  and  x - y = u }                     simplifying x-(x-y) to y, also valid by H-Cons
{ x - (x - y) = v  and  x - y = u }
y := x - y;
{ x - y = v  and  y = u }
x := x - y
{ x = v  and  y = u }
```

Each adjacent pair of assertions is an equivalence over the integers, and each assignment step is an instance of H-Assign.

</details>

### Exercise 4

Let $c$ be $q := 0 ; r := x ; \texttt{while}\ y \le r\ \texttt{do}\ (r := r - y ; q := q + 1)$. Prove $[x \ge 0 \land y > 0]\ c\ [x = qy + r \land 0 \le r \land r < y]$.

<details><summary>Solution</summary>

Take the invariant $I := x = qy + r \land r \ge 0 \land y > 0$ and the variant $t := r$.

Initialization. H-Assign gives the precondition $x = 0 \cdot y + x \land x \ge 0 \land y > 0$ for the two assignments, which follows from the precondition of the program.

Bound. $\models I \land y \le r \to r \ge 0$, which is immediate from $I$.

Body. We need $[I \land y \le r \land r = z]\ r := r - y ; q := q + 1\ [I \land r < z]$. Two applications of H-Assign give the precondition

$$x = (q + 1)y + (r - y) \land r - y \ge 0 \land y > 0 \land r - y < z.$$

We have $(q+1)y + (r - y) = qy + r = x$. Also, $y \le r$ gives $r - y \ge 0$, and $y > 0$ with $r = z$ gives $r - y < z$. So the implication holds.

Exit. H-WhileT gives $[I]\ \ldots\ [I \land \neg(y \le r)]$. Then $x = qy + r$, $r \ge 0$ and $r < y$. H-Cons concludes.

A scratch script confirmed the triple and the variant on a finite range of values.

</details>

### Exercise 5

Using the big-step rules for $\texttt{repeat}$ from Exercise 4 of [Operational Semantics](../operational-semantics/), prove that the following rule is sound: from $\models \{P\}\,c\,\{Q\}$ and $\models Q \land \neg b \to P$, infer $\models \{P\}\ \texttt{repeat}\ c\ \texttt{until}\ b\ \{Q \land b\}$.

<details><summary>Solution</summary>

Use rule induction on the big-step derivation for the repeat command $R$, with the property: if $\sigma \models P$, then $\sigma' \models Q \land b$.

Case R1. We have $\langle c, \sigma\rangle \Downarrow \sigma'$ and $\mathcal{B}[\![b]\!]\sigma' = \mathrm{tt}$. The first premise gives $\sigma' \models Q$, so $\sigma' \models Q \land b$.

Case R2. We have $\langle c, \sigma\rangle \Downarrow \tau$, $\mathcal{B}[\![b]\!]\tau = \mathrm{ff}$ and $\langle R, \tau\rangle \Downarrow \sigma'$. The first premise gives $\tau \models Q$, and with $\neg b$, the second premise gives $\tau \models P$. The induction hypothesis gives $\sigma' \models Q \land b$.

</details>

### Exercise 6

Prove that Floyd's forward assignment rule is sound: $\models \{P\}\ x := a\ \{\exists v.\ x = a[v/x] \land P[v/x]\}$, where $v$ is a variable occurring in neither $a$ nor $P$, and different from $x$.

<details><summary>Solution</summary>

Let $\sigma \models P$ and $\sigma' = \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]$. Choose the witness $v_0 = \sigma(x)$, and let $\rho = \sigma'[v \mapsto v_0]$. We show $\rho$ satisfies both conjuncts.

Observe that $\rho[x \mapsto \rho(v)] = \rho[x \mapsto v_0] = \sigma[v \mapsto v_0]$, since $\sigma(x) = v_0$.

First conjunct. The left side has value $\rho(x) = \mathcal{A}[\![a]\!]\sigma$. By the substitution lemma for expressions, $\mathcal{A}[\![a[v/x]]\!]\rho = \mathcal{A}[\![a]\!](\rho[x \mapsto v_0]) = \mathcal{A}[\![a]\!](\sigma[v \mapsto v_0]) = \mathcal{A}[\![a]\!]\sigma$, where the last step uses that $v$ does not occur in $a$.

Second conjunct. By Lemma 1, $\rho \models P[v/x]$ iff $\rho[x \mapsto v_0] \models P$, that is, iff $\sigma[v \mapsto v_0] \models P$. This is equivalent to $\sigma \models P$, because $v$ is not free in $P$.

</details>

### Exercise 7

Prove the constancy rule: if $\models \{P\}\,c\,\{Q\}$ and no variable free in $R$ is assigned in $c$, then $\models \{P \land R\}\,c\,\{Q \land R\}$. Show that the side condition cannot be dropped.

<details><summary>Solution</summary>

First prove a lemma: if $\langle c, \sigma\rangle \Downarrow \sigma'$ and $x$ is not on the left of any assignment in $c$, then $\sigma'(x) = \sigma(x)$. Use rule induction on the big-step derivation. B-Skip and B-WhileF do not change the state. B-Assign changes only the assigned variable, which is different from $x$. For the rules B-Seq, B-IfT, B-IfF and B-WhileT, the commands in the premises have assignments only among those of the conclusion, so the hypotheses apply, and equalities compose.

Now let $\sigma \models P \land R$ and $\langle c, \sigma\rangle \Downarrow \sigma'$. The validity of the given triple gives $\sigma' \models Q$. By the lemma, $\sigma$ and $\sigma'$ agree on the free variables of $R$. The truth of a formula depends only on the values of its free variables, so $\sigma' \models R$.

Side condition. We have $\models \{\top\}\ x := 1\ \{\top\}$. With $R$ being $x = 0$, the conclusion would be $\{x = 0\}\ x := 1\ \{x = 0\}$, which is invalid.

</details>

### Exercise 8

Prove total correctness of Euclid's algorithm by subtraction: $[x = u \land y = v \land u \ge 1 \land v \ge 1]\ \texttt{while}\ \neg(x = y)\ \texttt{do}\ (\texttt{if}\ x \le y\ \texttt{then}\ y := y - x\ \texttt{else}\ x := x - y)\ [x = \gcd(u, v)]$. Assume that $\gcd$ is available in the assertion language, as Theorem 4 permits.

<details><summary>Solution</summary>

Take $I := \gcd(x, y) = \gcd(u, v) \land x \ge 1 \land y \ge 1$ and the variant $t := x + y$.

Initialization. The precondition implies $I$ directly.

Bound. $I \land \neg(x = y) \to x + y \ge 0$, since $x, y \ge 1$.

Body. Assume $I$, $x \ne y$ and $x + y = z$.

If $x \le y$, then $x < y$, and the assignment yields $y' = y - x \ge 1$. We have $\gcd(x, y - x) = \gcd(x, y)$, because common divisors of $x$ and $y$ are exactly the common divisors of $x$ and $y - x$. The variant becomes $x + (y - x) = y < x + y = z$, since $x \ge 1$.

The other branch is symmetric.

Exit. $I \land \neg\neg(x = y)$ gives $x = y$, so $\gcd(x, y) = x$ because $x \ge 1$, and therefore $x = \gcd(u, v)$.

A scratch script confirmed the invariant and variant for $1 \le u, v < 20$.

</details>

### Exercise 9

Show that the set of valid total correctness triples of the form $[\top]\,c\,[\top]$ is not computably enumerable. You may use the fact that IMP can simulate a Turing machine.

<details><summary>Solution</summary>

The triple $[\top]\,c\,[\top]$ is valid iff $c$ terminates from every state. We reduce the non-halting problem, which is not computably enumerable, to this set.

Given a machine $M$ and an input $w$, compute a command $c_{M,w}$ that reads the initial value of a variable $x$, replaces it by its absolute value $k$, and simulates $M$ on $w$ for $k$ steps. If $M$ has halted within $k$ steps, $c_{M,w}$ enters $\texttt{while}\ \texttt{true}\ \texttt{do}\ \texttt{skip}$. Otherwise it stops.

If $M$ does not halt on $w$, each run stops after the simulation, so the triple is valid. If $M$ halts on $w$ in $h$ steps, then the initial state with $x = h$ gives a divergent run, so the triple is invalid.

Therefore $M$ does not halt on $w$ iff $[\top]\,c_{M,w}\,[\top]$ is valid. If the set were computably enumerable, so would be non-halting, which is a contradiction.

</details>

### Exercise 10

Add $\texttt{assert}\ b$. Define a semantics with the additional judgment $\langle c, \sigma\rangle \Downarrow \mathsf{err}$ in which a false assertion faults, and faults propagate. Define a validity notion that excludes faults. Give a rule for $\texttt{assert}$, and prove it sound. Then describe what changes in the proof of the sequence rule.

<details><summary>Solution</summary>

Semantics. Add the rules: $\langle \texttt{assert}\ b, \sigma\rangle \Downarrow \sigma$ if $\mathcal{B}[\![b]\!]\sigma = \mathrm{tt}$, and $\langle \texttt{assert}\ b, \sigma\rangle \Downarrow \mathsf{err}$ if $\mathcal{B}[\![b]\!]\sigma = \mathrm{ff}$. For propagation: from $\langle c_1, \sigma\rangle \Downarrow \mathsf{err}$ infer $\langle c_1 ; c_2, \sigma\rangle \Downarrow \mathsf{err}$; from $\langle c_1, \sigma\rangle \Downarrow \sigma'$ and $\langle c_2, \sigma'\rangle \Downarrow \mathsf{err}$ infer $\langle c_1 ; c_2, \sigma\rangle \Downarrow \mathsf{err}$; and analogously for the branches of a conditional and for the body and later iterations of a loop.

Validity. $\models \{P\}\,c\,\{Q\}$ holds if for all $\sigma \models P$: it is not the case that $\langle c, \sigma\rangle \Downarrow \mathsf{err}$, and if $\langle c, \sigma\rangle \Downarrow \sigma'$, then $\sigma' \models Q$.

Rule. $\vdash \{b \land Q\}\ \texttt{assert}\ b\ \{Q\}$.

Soundness. Let $\sigma \models b \land Q$. Since the guard is true, the fault rule does not apply, so the command does not fault. The only result is $\sigma$, and $\sigma \models Q$.

Sequence rule. The proof gains one obligation. Let $\sigma \models P$. By the first premise, $c_1$ does not fault from $\sigma$. If $\langle c_1, \sigma\rangle \Downarrow \sigma'$, then $\sigma' \models R$, so by the second premise, $c_2$ does not fault from $\sigma'$. So neither propagation rule applies, and $c_1 ; c_2$ does not fault. The result claim is proved as before.

A fault-avoiding reading of triples is the form used in [Separation Logic](../../../part-2-core-reasoning/07-deductive-verification/separation-logic/), where a triple also guarantees the absence of memory faults.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State the definitions of partial and total correctness validity.
- Write the Hoare rules from memory, and explain why the assignment rule substitutes into the postcondition.
- Prove Lemma 1 and Theorem 2, including the quantifier case and the while case.
- Prove the soundness of H-WhileT by well-founded induction on the variant.
- Find an invariant, and give a complete proof outline with side conditions, for a small loop.
- Prove relative completeness, given expressiveness, and explain why absolute completeness is impossible.

## Materials

- Winskel, The Formal Semantics of Programming Languages. Read the chapter on the axiomatic semantics of IMP for soundness, and the chapter on completeness of the Hoare rules for weakest preconditions, expressiveness and the link to Gödel's theorem.
- Nielson and Nielson, Semantics with Applications. Read the axiomatic program verification chapters for a second treatment of the partial and total correctness rules.
- Hoare, An Axiomatic Basis for Computer Programming, Communications of the ACM 12, 1969. Read it as the founding paper.
- Floyd, Assigning Meanings to Programs, Proceedings of Symposia in Applied Mathematics 19, 1967. Read it for the origin of inductive assertions.
- Cook, Soundness and Completeness of an Axiom System for Program Verification, SIAM Journal on Computing 7(1), 1978. Read it for the origin of relative completeness.
- Dijkstra, Guarded Commands, Nondeterminacy and Formal Derivation of Programs, Communications of the ACM 18(8), 1975. Read it for the weakest precondition calculus.
- Apt, Ten Years of Hoare's Logic: A Survey, Part I, ACM Transactions on Programming Languages and Systems 3(4), 1981. Read it for a survey of the early metatheory.
- O'Hearn, Incorrectness Logic, POPL 2020. Read it to see how the validity definition can be changed to suit bug-finding.
