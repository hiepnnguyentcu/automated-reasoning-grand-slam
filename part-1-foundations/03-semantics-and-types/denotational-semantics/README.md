# Denotational Semantics

Part 1, Chapter 3: Semantics and Types.

## Objective

Define the meaning of programs with domains and fixed points and relate it to operational semantics.

## Why this matters

Denotational semantics assigns each program a mathematical object, and it computes that object from the objects of the program's parts. Fixed points are the key tool, and they reappear throughout the program. [Abstract Interpretation](../../../part-4-remaining-methods/13-static-analysis/abstract-interpretation/) computes approximations of the fixed points defined here, [Symbolic Model Checking](../../../part-2-core-reasoning/08-model-checking/symbolic-checking-with-bdds/) computes reachable states as a least fixed point, and [Datalog-based analyses](../../../part-4-remaining-methods/13-static-analysis/interprocedural-analysis-and-datalog/) define their answers the same way. Compositionality is also a practical concern for an applied scientist, since a modular verifier must be able to reason about a component independently of its context.

## Prerequisites

- [Induction Principles](../induction-principles/), for rule induction and the fixed-point characterization of inductive sets.
- [Operational Semantics](../operational-semantics/), for IMP and its big-step semantics.

## Lesson

### Why a compositional meaning needs fixed points

Operational semantics defines meaning through execution. The meaning of $c$ is obtained by running rules on $c$, and the rule for a loop mentions the loop again. Denotational semantics, developed by Strachey and Scott from the late 1960s, instead asks for a function $\mathcal{C}[\![\cdot]\!]$ from commands to mathematical objects that is compositional: the meaning of a compound command is determined by the meanings of its immediate parts.

Commands may diverge, so the appropriate object is a partial function on states, $\mathcal{C}[\![c]\!] : \Sigma \rightharpoonup \Sigma$. Most clauses are immediate. For $\texttt{while}$, the unfolding of a loop suggests an equation. With $w = \mathcal{C}[\![\texttt{while}\ b\ \texttt{do}\ c]\!]$,

$$w(\sigma) = \begin{cases} w(\mathcal{C}[\![c]\!]\sigma) & \text{if } \mathcal{B}[\![b]\!]\sigma = \mathrm{tt}, \\ \sigma & \text{if } \mathcal{B}[\![b]\!]\sigma = \mathrm{ff}. \end{cases}$$

This equation is not a definition, because $w$ occurs on both sides and its argument need not decrease. It may have many solutions. For $\texttt{while}\ \texttt{true}\ \texttt{do}\ \texttt{skip}$, the equation reads $w(\sigma) = w(\sigma)$, and every partial function satisfies it. The program diverges everywhere, so the intended solution is the everywhere-undefined function. In general, the intended solution is the one that contains only what the equation forces. Domain theory makes this precise.

### Complete partial orders

Definition. A partial order $(D, \sqsubseteq)$ is a reflexive, antisymmetric and transitive relation on $D$. An $\omega$-chain is a sequence $d_0 \sqsubseteq d_1 \sqsubseteq d_2 \sqsubseteq \cdots$. A complete partial order, or cpo, is a partial order in which every $\omega$-chain has a least upper bound, written $\bigsqcup_n d_n$. A cpo is pointed if it has a least element $\bot$.

The relation $d \sqsubseteq e$ is read as "$e$ has at least as much information as $d$". The element $\bot$ carries no information. In this topic it is the least element of a cpo, and it represents an undefined result, with no connection to logical falsity.

Definition. A function $f : D \to E$ between cpos is monotone if $d \sqsubseteq d'$ implies $f(d) \sqsubseteq f(d')$. It is continuous if it is monotone and, for every $\omega$-chain, $f(\bigsqcup_n d_n) = \bigsqcup_n f(d_n)$.

Continuity says that a finite amount of output information depends on only a finite amount of input information, in the sense of a stage of the chain. The right side is well-defined because monotonicity makes $f(d_n)$ a chain.

| Cpo | Elements | Order | Pointed |
|---|---|---|---|
| Partial functions $\Sigma \rightharpoonup \Sigma$ | The elements are sets of pairs that are functional. | The order is inclusion of graphs. | Its least element is the empty function. |
| Flat domain $\mathbb{Z}_\bot$ | The elements are integers and a new element $\bot$. | The only strict relations are $\bot \sqsubset n$. | Its least element is $\bot$. |
| Powerset $\mathcal{P}(X)$ | The elements are subsets of $X$. | The order is inclusion. | Its least element is $\emptyset$. |
| Function space $[D \to E]$ | The elements are continuous functions. | The order is pointwise. | It is pointed when $E$ is pointed. |

The partial functions form a cpo because the union of a chain of functional graphs is functional: if $(\sigma, \tau_1) \in g_i$ and $(\sigma, \tau_2) \in g_j$ with $i \le j$, both pairs lie in $g_j$, so $\tau_1 = \tau_2$. This cpo is isomorphic to $[\Sigma \to \Sigma_\bot]$, with $\Sigma$ discretely ordered.

### Kleene's fixed-point theorem

Theorem 1 (Kleene). Let $D$ be a pointed cpo and $f : D \to D$ continuous. Then

$$\mathrm{fix}(f) = \bigsqcup_{n \in \mathbb{N}} f^n(\bot)$$

is the least fixed point of $f$. Moreover, it is the least pre-fixed point: if $f(x) \sqsubseteq x$, then $\mathrm{fix}(f) \sqsubseteq x$.

Proof. The sequence is a chain: $\bot \sqsubseteq f(\bot)$ since $\bot$ is least, and applying the monotone $f$ repeatedly gives $f^n(\bot) \sqsubseteq f^{n+1}(\bot)$. So the least upper bound exists.

It is a fixed point. By continuity,

$$f\Bigl(\bigsqcup_n f^n(\bot)\Bigr) = \bigsqcup_n f^{n+1}(\bot) = \bigsqcup_n f^n(\bot).$$

The last equality holds because removing the first element $\bot$ of a chain does not change its upper bounds.

It is the least pre-fixed point. Let $f(x) \sqsubseteq x$. Then $f^n(\bot) \sqsubseteq x$ for all $n$, by induction: $\bot \sqsubseteq x$, and if $f^n(\bot) \sqsubseteq x$, then $f^{n+1}(\bot) \sqsubseteq f(x) \sqsubseteq x$. So $x$ is an upper bound of the chain, and $\mathrm{fix}(f) \sqsubseteq x$. A fixed point is a pre-fixed point, so $\mathrm{fix}(f)$ is also the least fixed point. $\square$

Compare with the Knaster–Tarski theorem, which applies to monotone functions on a complete lattice and gives the least fixed point as the meet of the pre-fixed points. Kleene's theorem assumes less of the space and more of the function, and it gives an iterative construction. Exercise 5 shows that monotonicity alone does not make the iteration reach a fixed point.

### The denotational semantics of IMP

Write $g \circ h$ for composition of partial functions, undefined when either stage is undefined, and $\mathrm{cond}(p, g_1, g_2)$ for the function that behaves as $g_1$ on states where $p$ is tt and as $g_2$ where $p$ is ff. By structural recursion on $c$:

$$\mathcal{C}[\![\texttt{skip}]\!] = \mathrm{id}$$

$$\mathcal{C}[\![x := a]\!]\sigma = \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]$$

$$\mathcal{C}[\![c_1 ; c_2]\!] = \mathcal{C}[\![c_2]\!] \circ \mathcal{C}[\![c_1]\!]$$

$$\mathcal{C}[\![\texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2]\!] = \mathrm{cond}(\mathcal{B}[\![b]\!], \mathcal{C}[\![c_1]\!], \mathcal{C}[\![c_2]\!])$$

$$\mathcal{C}[\![\texttt{while}\ b\ \texttt{do}\ c]\!] = \mathrm{fix}(F_{b,c}), \quad \text{where } F_{b,c}(g) = \mathrm{cond}(\mathcal{B}[\![b]\!], g \circ \mathcal{C}[\![c]\!], \mathrm{id}).$$

The definition of $F_{b,c}$ uses only $\mathcal{C}[\![c]\!]$, where $c$ is an immediate subterm, so this is a legitimate structural recursion. The approximant $F_{b,c}^n(\bot)$ has an operational reading: it is the loop restricted to runs that evaluate the guard at most $n$ times, and it is undefined on any state that needs more.

Lemma 2. The function $F_{b,c}$ is continuous on $\Sigma \rightharpoonup \Sigma$.

Proof. Viewing partial functions as graphs,

$$F_{b,c}(g) = \{(\sigma, \tau) \mid \mathcal{B}[\![b]\!]\sigma = \mathrm{tt} \land \exists \sigma'.\ \mathcal{C}[\![c]\!]\sigma = \sigma' \land (\sigma', \tau) \in g\} \cup \{(\sigma, \sigma) \mid \mathcal{B}[\![b]\!]\sigma = \mathrm{ff}\}.$$

Monotonicity is immediate. For a chain $(g_n)$, whether $(\sigma, \tau) \in F_{b,c}(\bigcup_n g_n)$ depends on the membership of one pair $(\sigma', \tau)$ in $\bigcup_n g_n$, and that pair lies in some $g_n$. So $F_{b,c}(\bigcup_n g_n) = \bigcup_n F_{b,c}(g_n)$. $\square$

By Theorem 1, $\mathcal{C}[\![\texttt{while}\ b\ \texttt{do}\ c]\!]$ exists and satisfies the unfolding equation that motivated it. It follows that a loop and its unfolding have the same denotation, with no further proof.

### Relating the semantics

Theorem 3 (equivalence). For all $c, \sigma, \sigma'$, we have $\mathcal{C}[\![c]\!]\sigma = \sigma'$ if and only if $\langle c, \sigma\rangle \Downarrow \sigma'$.

Proof, backward direction. Use rule induction on the big-step derivation.

Cases B-Skip, B-Assign, B-IfT and B-IfF follow directly from the clauses, using the hypothesis for the branch taken.

Case B-Seq. The hypotheses give $\mathcal{C}[\![c_1]\!]\sigma = \sigma'$ and $\mathcal{C}[\![c_2]\!]\sigma' = \sigma''$, so the composition maps $\sigma$ to $\sigma''$.

Case B-WhileF. The guard is false, and the fixed-point equation gives $w(\sigma) = \mathrm{id}(\sigma) = \sigma$.

Case B-WhileT. The guard is true, the hypotheses give $\mathcal{C}[\![c]\!]\sigma = \sigma'$ and $w(\sigma') = \sigma''$, and the fixed-point equation gives $w(\sigma) = w(\sigma') = \sigma''$.

Proof, forward direction. Use structural induction on $c$, with the property that for all $\sigma, \sigma'$, $\mathcal{C}[\![c]\!]\sigma = \sigma'$ implies $\langle c, \sigma\rangle \Downarrow \sigma'$.

Cases $\texttt{skip}$ and assignment are immediate from the rules.

Case $c_1; c_2$. If the composition maps $\sigma$ to $\sigma''$, there is $\sigma'$ with $\mathcal{C}[\![c_1]\!]\sigma = \sigma'$ and $\mathcal{C}[\![c_2]\!]\sigma' = \sigma''$. The hypotheses and B-Seq conclude.

Case conditional. Split on the value of the guard, and apply the hypothesis and the corresponding rule.

Case $W = \texttt{while}\ b\ \texttt{do}\ c$. Write $F = F_{b,c}$. Since $\mathcal{C}[\![W]\!] = \bigcup_n F^n(\bot)$, it suffices to prove by induction on $n$ that for all $\sigma, \sigma'$, $F^n(\bot)\sigma = \sigma'$ implies $\langle W, \sigma\rangle \Downarrow \sigma'$. For $n = 0$, the function is empty. For $n + 1$, consider the guard at $\sigma$. If it is false, then $\sigma' = \sigma$, and B-WhileF applies. If it is true, there is $\tau = \mathcal{C}[\![c]\!]\sigma$ with $F^n(\bot)\tau = \sigma'$. The structural hypothesis for $c$ gives $\langle c, \sigma\rangle \Downarrow \tau$, the inner hypothesis gives $\langle W, \tau\rangle \Downarrow \sigma'$, and B-WhileT concludes. $\square$

The proof uses both kinds of induction, and that is typical: operational-to-denotational is by rule induction, and denotational-to-operational is by induction on syntax, with an inner induction on approximants for loops.

Two consequences follow. First, $c_1 \sim c_2$ if and only if $\mathcal{C}[\![c_1]\!] = \mathcal{C}[\![c_2]\!]$. Second, $\sim$ is a congruence, immediately from the compositionality of the definition. Compare this with the derivation-based proof in Exercise 8 of [Operational Semantics](../operational-semantics/).

### Fixed-point induction

Definition. A subset $P$ of a pointed cpo is admissible if $\bot \in P$ and $P$ is closed under least upper bounds of $\omega$-chains.

Theorem 4 (fixed-point induction, due to Scott). Let $f : D \to D$ be continuous on a pointed cpo and $P$ be admissible. If $f(P) \subseteq P$, then $\mathrm{fix}(f) \in P$.

Proof. By induction on $n$, $f^n(\bot) \in P$. The chain's least upper bound is in $P$ by admissibility. $\square$

Admissibility has to be checked, and it can fail. On $\Sigma \rightharpoonup \Sigma$, any property of the form "for all $(\sigma, \tau) \in g$, $R(\sigma, \tau)$" is admissible, since it holds of the empty function and of a union of graphs if it holds of each one. Partial correctness properties have this form, which is why [Axiomatic Semantics](../axiomatic-semantics/) can use this principle. In contrast, the property of being undefined on some state is not admissible, because a chain of partial functions can have a total union. Exercise 10 gives an instance.

### Higher-order languages

For a language with functions, types denote cpos. The function space $[D \to E]$ with the pointwise order is a cpo, with least upper bounds taken pointwise (Exercise 8), and $\mathrm{fix} : [D \to D] \to D$ is itself continuous (Exercise 9). These facts allow the language PCF, a typed lambda calculus with naturals and a fixed-point operator, to be given a meaning: base types denote flat domains, $[\![\tau \to \tau']\!] = [[\![\tau]\!] \to [\![\tau']\!]]$, and $[\![\mathrm{fix}\ t]\!] = \mathrm{fix}([\![t]\!])$. You will see the syntax of such languages in [Lambda Calculus](../lambda-calculus/) and [Type Systems](../type-systems/).

For the untyped lambda calculus, a model needs a set $D$ with $D \cong (D \to D)$. By Cantor's theorem, this is impossible for all set-theoretic functions, except for the trivial one-element $D$. Scott's insight, around 1969, was that it is possible with continuous functions: there is a nontrivial cpo $D_\infty$ with $D_\infty \cong [D_\infty \to D_\infty]$. This gave the first mathematical model of the untyped lambda calculus.

### Adequacy and full abstraction

Let $t$ and $t'$ be closed terms of a typed language, and let contextual equivalence mean that $C[t]$ and $C[t']$ have the same observable result for every context $C$ of base type.

A denotational semantics is adequate if, for closed terms of base type, $[\![t]\!] = [\![v]\!]$ with $v$ a value holds iff $t$ evaluates to $v$. Adequacy implies that equal denotations give contextual equivalence: if $[\![t]\!] = [\![t']\!]$, then compositionality gives $[\![C[t]]\!] = [\![C[t']]\!]$, and adequacy turns this into equal observations.

A semantics is fully abstract if the converse also holds, so that denotational equality coincides with contextual equivalence.

Theorem 3 gives adequacy for IMP. For PCF, a proof by simple induction fails on the $\mathrm{fix}$ and application cases. Plotkin's 1977 paper proved adequacy of the standard cpo model using a type-indexed relation. The same paper showed that the model is not fully abstract: it contains the parallel-or function, with $\mathrm{por}(\mathrm{tt}, \bot) = \mathrm{tt}$, $\mathrm{por}(\bot, \mathrm{tt}) = \mathrm{tt}$ and $\mathrm{por}(\mathrm{ff}, \mathrm{ff}) = \mathrm{ff}$, which no sequential PCF term can define. Two PCF functionals that agree on all definable arguments and differ on parallel-or are therefore contextually equivalent and have different denotations. Adding parallel-or to the language restores full abstraction. The search for a fully abstract model of PCF by more semantic means led to the game semantics of the 1990s.

## Worked examples

### Worked Example 1: the factorial loop by Kleene iteration

Let $W = \texttt{while}\ 1 \le x\ \texttt{do}\ (y := y \times x ; x := x - 1)$ and $F = F_{b,c}$ for this loop, with $x$ and $y$ the only relevant variables. The body's denotation maps a state $[x, y]$ to $[x - 1, y \cdot x]$.

The first iterates are as follows.

```
F^0(bot) [x,y] : undefined everywhere
F^1(bot) [x,y] : x <= 0  gives [x,y]
                 x >= 1  undefined
F^2(bot) [x,y] : x <= 0  gives [x,y]
                 x  = 1  gives F^1(bot)[0, y]     = [0, y]
                 x >= 2  undefined
F^3(bot) [x,y] : x <= 0  gives [x,y]
                 x  = 1  gives F^2(bot)[0, y]     = [0, y]
                 x  = 2  gives F^2(bot)[1, 2y]    = [0, 2y]
                 x >= 3  undefined
```

Claim. For $n \ge 1$,

$$F^n(\bot)[x, y] = \begin{cases} [x, y] & \text{if } x \le 0, \\ [0, y \cdot x!] & \text{if } 1 \le x < n, \\ \text{undefined} & \text{if } x \ge n. \end{cases}$$

Proof by induction on $n$. For $n = 1$, the second case is empty, and $F^1(\bot)$ matches the table. For the step, let $n \ge 1$, and compute $F^{n+1}(\bot)[x, y]$.

If $x \le 0$, the guard is false, and the result is $[x, y]$.

If $x \ge 1$, the result is $F^n(\bot)[x - 1, y \cdot x]$. If $x = 1$, then the first case of the hypothesis gives $[0, y \cdot 1] = [0, y \cdot 1!]$. If $2 \le x < n + 1$, then $1 \le x - 1 < n$, and the second case gives $[0, y \cdot x \cdot (x-1)!] = [0, y \cdot x!]$. If $x \ge n + 1$, then $x - 1 \ge n$, and the result is undefined. $\square$

Taking the union over $n$, every state is eventually defined:

$$\mathcal{C}[\![W]\!][x, y] = \begin{cases} [x, y] & \text{if } x \le 0, \\ [0, y \cdot x!] & \text{if } x \ge 1. \end{cases}$$

For $[2, 1]$ this gives $[0, 2]$, which agrees with the trace in [Operational Semantics](../operational-semantics/). The closed form of $F^n(\bot)$ was confirmed on a finite range of states by a scratch script.

### Worked Example 2: a loop with many fixed points

Let $W = \texttt{while}\ \neg(x = 0)\ \texttt{do}\ \texttt{skip}$. The equation $g = F(g)$ says:

$$g(\sigma) = \sigma \text{ if } \sigma(x) = 0, \qquad g(\sigma) = g(\sigma) \text{ if } \sigma(x) \ne 0.$$

So the fixed points are exactly the partial functions that act as the identity on states with $x = 0$, with arbitrary behaviour on the rest. Examples are the identity on all states, and the function that sets $x$ to $0$ everywhere.

The iteration gives $F^0(\bot) = \emptyset$, and for all $n \ge 1$, $F^n(\bot)$ is the identity restricted to $\{\sigma \mid \sigma(x) = 0\}$. So the chain is constant from $n = 1$, and the least fixed point is this restriction. It is undefined on states with $x \ne 0$, which are exactly the states from which the program diverges. Theorem 3 guarantees this agreement, and any larger fixed point would attribute results to runs that do not produce them.

### Worked Example 3: a loop is idempotent, by fixed-point induction

Let $W = \texttt{while}\ b\ \texttt{do}\ c$ and $w = \mathcal{C}[\![W]\!] = \mathrm{fix}(F)$. We prove $W ; W \sim W$.

Step 1. Whenever $w(\sigma) = \tau$, we have $\mathcal{B}[\![b]\!]\tau = \mathrm{ff}$. Let $P = \{g \mid \forall (\sigma, \tau) \in g.\ \mathcal{B}[\![b]\!]\tau = \mathrm{ff}\}$. This set has the admissible form described above. To show $F(P) \subseteq P$, let $g \in P$ and $(\sigma, \tau) \in F(g)$. If the guard is false at $\sigma$, then $\tau = \sigma$, so the guard is false at $\tau$. If the guard is true at $\sigma$, then $(\sigma', \tau) \in g$ for $\sigma' = \mathcal{C}[\![c]\!]\sigma$, and $g \in P$ gives the claim. By Theorem 4, $w \in P$.

Step 2. If the guard is false at $\tau$, then $w(\tau) = \tau$, by the fixed-point equation.

Step 3. The denotation of $W ; W$ is $w \circ w$. If $w(\sigma) = \tau$, then Step 1 and Step 2 give $w(\tau) = \tau$, so $(w \circ w)(\sigma) = \tau$. Conversely, if $(w \circ w)(\sigma) = \tau$, there is $\rho$ with $w(\sigma) = \rho$ and $w(\rho) = \tau$. Steps 1 and 2 give $w(\rho) = \rho$, so $\tau = \rho$ and $w(\sigma) = \tau$. So $w \circ w = w$. $\square$

By Theorem 3 this transfers to the operational semantics. A scratch brute-force comparison on small random loops found no counterexample to this equivalence.

## Common mistakes

- Reading $\bot$ as an error value that a program can test for. It stands for no information and represents divergence. Since divergence cannot be detected, continuity and monotonicity forbid functions that behave differently on $\bot$ in a way that would decide it.
- Thinking the order $\sqsubseteq$ compares magnitude. In $\mathbb{Z}_\bot$, the integers $3$ and $5$ are incomparable, because neither contains more information than the other.
- Assuming the fixed-point equation of a loop has one solution. Worked Example 2 has many. The meaning is the least one, and that choice is justified by Theorem 3.
- Assuming that $\mathcal{C}[\![\texttt{while}\ b\ \texttt{do}\ c]\!]$ is defined by a recursion on the loop. The clause recurses only on $c$, and it then takes a fixed point. The unfolding equation follows as a consequence.
- Equating monotone and continuous. A monotone function need not preserve limits, as Exercise 5 shows, and then the Kleene chain need not reach a fixed point.
- Applying fixed-point induction without checking admissibility. Exercise 10 shows that the principle proves a false statement for a non-admissible predicate.
- Treating adequacy and full abstraction as the same. Adequacy gives one implication between denotational equality and contextual equivalence. Full abstraction requires both.
- Interpreting the approximant $F^n(\bot)$ as the state after $n$ iterations. It is a function, the loop's behaviour on inputs that need at most $n$ evaluations of the guard.

## Exercises

### Exercise 1

Decide which of the following are cpos, and which are pointed: (a) $(\mathbb{N}, \le)$; (b) $(\mathbb{N} \cup \{\omega\}, \le)$, with $\omega$ greatest; (c) $(\mathcal{P}(\mathbb{N}), \subseteq)$; (d) finite subsets of $\mathbb{N}$ under $\subseteq$; (e) $\mathbb{Z}$ ordered by equality; (f) $\mathbb{Z}_\bot$.

<details><summary>Solution</summary>

(a) Not a cpo, because $0 \le 1 \le 2 \le \cdots$ has no upper bound. (b) A cpo, since each chain has a maximum or has limit $\omega$, and it is pointed with least element $0$. (c) A cpo, with union as the least upper bound, and it is pointed with least element $\emptyset$. (d) Not a cpo, because $\{0\} \subseteq \{0, 1\} \subseteq \cdots$ has no finite upper bound. (e) A cpo, since each chain is constant, and it is not pointed. (f) A cpo, since each chain has at most two distinct elements, and it is pointed.

</details>

### Exercise 2

For $W = \texttt{while}\ x \le 2\ \texttt{do}\ x := x + 1$, compute $F^n(\bot)$ for $n = 0, 1, 2, 3$, give a closed form for all $n$, and compute $\mathcal{C}[\![W]\!]$.

<details><summary>Solution</summary>

Consider only the value of $x$.

```
F^0(bot) x : undefined
F^1(bot) x : x >= 3  gives x ; otherwise undefined
F^2(bot) x : x >= 3  gives x ; x = 2  gives F^1(bot)(3) = 3 ; otherwise undefined
F^3(bot) x : x >= 3  gives x ; x = 2  gives 3 ; x = 1  gives F^2(bot)(2) = 3 ; otherwise undefined
```

For $n \ge 1$, $F^n(\bot)(x)$ is defined iff $x \ge 4 - n$, and then equals $\max(x, 3)$. The proof is by induction on $n$. If $x \ge 3$, the guard is false, and the result is $x$. If $x \le 2$, then $F^{n+1}(\bot)(x) = F^n(\bot)(x + 1)$, which is defined iff $x + 1 \ge 4 - n$, that is, $x \ge 4 - (n + 1)$, and its value is $\max(x + 1, 3) = 3 = \max(x, 3)$.

The union is the total function $\mathcal{C}[\![W]\!]\sigma = \sigma[x \mapsto \max(\sigma(x), 3)]$. The closed form was confirmed on a finite range by a scratch script.

</details>

### Exercise 3

Describe all fixed points of $F$ for $\texttt{while}\ \neg(x = 0)\ \texttt{do}\ x := x - 1$, and identify the least.

<details><summary>Solution</summary>

A fixed point $g$ satisfies $g(\sigma) = \sigma$ when $\sigma(x) = 0$, and $g(\sigma) = g(\sigma[x \mapsto \sigma(x) - 1])$ otherwise. Here "equal" includes both sides being undefined.

For $\sigma(x) = k > 0$, the equation repeated $k$ times gives $g(\sigma) = g(\sigma[x \mapsto 0]) = \sigma[x \mapsto 0]$, so $g$ is determined.

For $\sigma(x) < 0$, the equation says that $g$ takes the same value (or is undefined) at all states on the descending ray $\{\sigma[x \mapsto k] \mid k < 0\}$, for the ray determined by the values of the other variables. Each such ray can independently be assigned any fixed result, or be left undefined.

So fixed points correspond to these choices. The least fixed point leaves all rays undefined:

$$\mathcal{C}[\![W]\!]\sigma = \sigma[x \mapsto 0] \text{ if } \sigma(x) \ge 0, \quad \text{undefined otherwise.}$$

The iterates confirm this: $F^n(\bot)$ is defined exactly when $0 \le \sigma(x) < n$. The program diverges on negative $x$.

</details>

### Exercise 4

Suppose that for every $\omega$-chain $(d_n)$, the least upper bound of the set $\{f(d_n) \mid n \in \mathbb{N}\}$ exists and equals $f(\bigsqcup_n d_n)$. Prove that $f$ is monotone.

<details><summary>Solution</summary>

Let $d \sqsubseteq d'$. The sequence $d, d', d', d', \dots$ is an $\omega$-chain with least upper bound $d'$. Preservation gives that $f(d')$ is the least upper bound of $\{f(d), f(d')\}$. In particular $f(d)$ is below it, so $f(d) \sqsubseteq f(d')$.

</details>

### Exercise 5

(a) On $D = \mathbb{N} \cup \{\omega\}$, define $f(n) = 0$ for $n \in \mathbb{N}$ and $f(\omega) = 1$. Show that $f$ is monotone and not continuous. (b) On $E = \mathbb{N} \cup \{\omega, \omega + 1\}$, ordered in the obvious way, define $g(n) = n + 1$, $g(\omega) = \omega + 1$, and $g(\omega + 1) = \omega + 1$. Show that $g$ is monotone, that $\bigsqcup_n g^n(\bot)$ is not a fixed point, and find the least fixed point.

<details><summary>Solution</summary>

(a) Monotone: for $n \le m$, $0 \le 0$, and $f(n) = 0 \le 1 = f(\omega)$. Not continuous: for the chain $0 \le 1 \le 2 \le \cdots$, we have $\bigsqcup_n n = \omega$, so $f(\bigsqcup_n n) = 1$, whereas $\bigsqcup_n f(n) = 0$.

(b) Monotone: the function is strictly increasing on $\mathbb{N}$, and $g(n) = n + 1 \le \omega + 1$, and it is constant on $\{\omega, \omega + 1\}$. With $\bot = 0$, $g^n(0) = n$, so $\bigsqcup_n g^n(0) = \omega$. Since $g(\omega) = \omega + 1 \ne \omega$, this is not a fixed point. The only fixed point is $\omega + 1$, since $g(n) \ne n$ for $n \in \mathbb{N}$ and $g(\omega) \ne \omega$. So the least fixed point requires going past stage $\omega$.

</details>

### Exercise 6

Let $R = \texttt{repeat}\ c\ \texttt{until}\ b$. Define $\mathcal{C}[\![R]\!] = \mathrm{fix}(G)$, where $G(g) = \mathrm{cond}(\mathcal{B}[\![b]\!], \mathrm{id}, g) \circ \mathcal{C}[\![c]\!]$. Prove that $\mathcal{C}[\![R]\!] = \mathcal{C}[\![c ; \texttt{while}\ \neg b\ \texttt{do}\ c]\!]$.

<details><summary>Solution</summary>

Write $C = \mathcal{C}[\![c]\!]$, and let $F(g) = \mathrm{cond}(\mathcal{B}[\![\neg b]\!], g \circ C, \mathrm{id})$ be the functional of the while loop.

Claim: $G^n(\bot) = F^n(\bot) \circ C$ for all $n$. For $n = 0$, both sides are empty. For the step,

$$G(F^n(\bot) \circ C) = \mathrm{cond}(\mathcal{B}[\![b]\!], \mathrm{id}, F^n(\bot) \circ C) \circ C,$$

$$F^{n+1}(\bot) \circ C = \mathrm{cond}(\mathcal{B}[\![\neg b]\!], F^n(\bot) \circ C, \mathrm{id}) \circ C.$$

These are equal because the two conditionals choose the same branch at each state.

Taking unions and using the fact that precomposition distributes over union,

$$\mathrm{fix}(G) = \bigcup_n (F^n(\bot) \circ C) = \Bigl(\bigcup_n F^n(\bot)\Bigr) \circ C = \mathcal{C}[\![\texttt{while}\ \neg b\ \texttt{do}\ c]\!] \circ C,$$

which is the denotation of the sequential composition.

</details>

### Exercise 7

Let $P$ and $Q$ be sets of states. Suppose $\mathcal{C}[\![c]\!]$ maps $P \cap \{\sigma \mid \mathcal{B}[\![b]\!]\sigma = \mathrm{tt}\}$ into $P$. Prove by fixed-point induction that $w = \mathcal{C}[\![\texttt{while}\ b\ \texttt{do}\ c]\!]$ maps $P$ into $P \cap \{\sigma \mid \mathcal{B}[\![b]\!]\sigma = \mathrm{ff}\}$.

<details><summary>Solution</summary>

Let $A = \{g \mid \forall (\sigma, \tau) \in g.\ \sigma \in P \to (\tau \in P \land \mathcal{B}[\![b]\!]\tau = \mathrm{ff})\}$. This has the universal form $\forall (\sigma, \tau) \in g.\ R(\sigma, \tau)$, so it contains the empty function and is closed under chain unions. So it is admissible.

Assume $g \in A$, and let $(\sigma, \tau) \in F(g)$ with $\sigma \in P$. If the guard is false at $\sigma$, then $\tau = \sigma \in P$, and the guard is false at $\tau$. If the guard is true at $\sigma$, then $\sigma' = \mathcal{C}[\![c]\!]\sigma$ exists with $(\sigma', \tau) \in g$. The assumption about $c$ gives $\sigma' \in P$, and $g \in A$ gives the claim for $\tau$. So $F(A) \subseteq A$, and Theorem 4 gives $w \in A$.

This is the semantic content of the Hoare rule for loops.

</details>

### Exercise 8

Prove that for a chain of continuous functions $f_0 \sqsubseteq f_1 \sqsubseteq \cdots$ in $[D \to E]$, the pointwise least upper bound $f(d) = \bigsqcup_i f_i(d)$ is continuous.

<details><summary>Solution</summary>

Each $f_i(d)$ forms a chain in $i$, since the order is pointwise, so $f$ is well-defined. It is monotone, since each $f_i$ is. For a chain $(d_m)$,

$$f\Bigl(\bigsqcup_m d_m\Bigr) = \bigsqcup_i f_i\Bigl(\bigsqcup_m d_m\Bigr) = \bigsqcup_i \bigsqcup_m f_i(d_m) = \bigsqcup_m \bigsqcup_i f_i(d_m) = \bigsqcup_m f(d_m).$$

The third equality is the exchange of least upper bounds. For a doubly indexed family monotone in both indices, both iterated least upper bounds are least upper bounds of the whole family, because each is an upper bound of all $a_{i,m}$, and any upper bound of the family is above each iterated one.

It is the least upper bound in $[D \to E]$, since any continuous upper bound $h$ satisfies $f_i(d) \sqsubseteq h(d)$ for all $i$, so $f(d) \sqsubseteq h(d)$.

</details>

### Exercise 9

Prove that $\mathrm{fix} : [D \to D] \to D$ is continuous for pointed $D$.

<details><summary>Solution</summary>

Monotone: if $f \sqsubseteq g$, then $f^n(\bot) \sqsubseteq g^n(\bot)$ by induction on $n$, using monotonicity of $g$ and the pointwise order, so $\mathrm{fix}(f) \sqsubseteq \mathrm{fix}(g)$.

Continuous: let $(f_i)$ be a chain with $f = \bigsqcup_i f_i$. First, $f^n(\bot) = \bigsqcup_i f_i^n(\bot)$ for all $n$. For $n = 0$, both sides are $\bot$. For the step,

$$f^{n+1}(\bot) = f\Bigl(\bigsqcup_j f_j^n(\bot)\Bigr) = \bigsqcup_i \bigsqcup_j f_i(f_j^n(\bot)) = \bigsqcup_k f_k(f_k^n(\bot)) = \bigsqcup_k f_k^{n+1}(\bot).$$

The third equality is the diagonal property of a family monotone in both indices: each $a_{i,j}$ is below $a_{k,k}$ for $k = \max(i, j)$.

Now exchange the least upper bounds:

$$\mathrm{fix}(f) = \bigsqcup_n f^n(\bot) = \bigsqcup_n \bigsqcup_i f_i^n(\bot) = \bigsqcup_i \bigsqcup_n f_i^n(\bot) = \bigsqcup_i \mathrm{fix}(f_i).$$

</details>

### Exercise 10

Let $W = \texttt{while}\ 1 \le x\ \texttt{do}\ x := x - 1$, with functional $F$. Let $P$ be the set of partial functions that are undefined on at least one state $\sigma$ with $\sigma(x) \ge 1$. Show that $\bot \in P$ and $F(P) \subseteq P$, and that $\mathrm{fix}(F) \notin P$. State which hypothesis of Theorem 4 fails.

<details><summary>Solution</summary>

The empty function is undefined on every state, so $\bot \in P$.

Let $g \in P$ be undefined on $\sigma$ with $\sigma(x) \ge 1$. Let $\sigma' = \sigma[x \mapsto \sigma(x) + 1]$. Then $\sigma'(x) \ge 1$, the guard is true at $\sigma'$, and $F(g)(\sigma') = g(\sigma)$, which is undefined. So $F(g) \in P$.

The function $F^0(\bot)$ is empty, and for $n \ge 1$, $F^n(\bot)$ is defined exactly on the states with $\sigma(x) < n$. The union is the total function that maps $\sigma$ to itself if $\sigma(x) \le 0$ and to $\sigma[x \mapsto 0]$ otherwise. So $\mathrm{fix}(F) \notin P$.

All the iterates lie in $P$, and their least upper bound does not. So $P$ is not closed under least upper bounds of chains, and it is not admissible. That is the only hypothesis that fails, and it shows that the check cannot be omitted.

</details>

### Exercise 11

Add $c_1\ \texttt{or}\ c_2$. Replace partial functions by relations, $\mathcal{C}[\![c]\!] \subseteq \Sigma \times \Sigma$, with union for $\texttt{or}$ and relational composition for sequencing. Define the meaning of loops, and explain why continuity still holds. Then show that $\texttt{skip}$ and $\texttt{skip}\ \texttt{or}\ W_\infty$ have the same denotation, and explain what this semantics fails to observe. Here $W_\infty = \texttt{while}\ \texttt{true}\ \texttt{do}\ \texttt{skip}$.

<details><summary>Solution</summary>

Use the pointed cpo $\mathcal{P}(\Sigma \times \Sigma)$ with inclusion. Let $\mathcal{C}[\![c_1\ \texttt{or}\ c_2]\!] = \mathcal{C}[\![c_1]\!] \cup \mathcal{C}[\![c_2]\!]$, and let $\mathcal{C}[\![\texttt{while}\ b\ \texttt{do}\ c]\!] = \mathrm{fix}(F)$ with

$$F(g) = \{(\sigma, \tau) \mid \mathcal{B}[\![b]\!]\sigma = \mathrm{tt} \land \exists \sigma'.\ (\sigma, \sigma') \in \mathcal{C}[\![c]\!] \land (\sigma', \tau) \in g\} \cup \{(\sigma, \sigma) \mid \mathcal{B}[\![b]\!]\sigma = \mathrm{ff}\}.$$

Continuity holds as in Lemma 2, since membership of a pair in $F(g)$ depends on a single pair of $g$, and $F$ distributes over union.

We have $\mathcal{C}[\![W_\infty]\!] = \emptyset$, since its functional is $F(g) = g$. So $\mathcal{C}[\![\texttt{skip}\ \texttt{or}\ W_\infty]\!] = \mathrm{id} \cup \emptyset = \mathcal{C}[\![\texttt{skip}]\!]$.

The denotation records only which results are reachable, which corresponds to the big-step semantics of Exercise 10 in [Operational Semantics](../operational-semantics/). It cannot see that the second program may diverge, so it is unsuitable for total correctness. A semantics that distinguishes them must record a possible divergence as well, for example by using sets of outcomes in $\Sigma_\bot$. Powerdomains are the general construction for this.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define cpo, continuous function and least fixed point, and prove Kleene's theorem.
- Write the denotational semantics of IMP, and show that the loop functional is continuous.
- Compute the approximants of a given loop, and find its denotation in closed form.
- Prove the equivalence of the denotational and big-step semantics for IMP.
- Apply fixed-point induction, checking admissibility.
- Define adequacy and full abstraction, and explain the role of parallel-or for PCF.

## Materials

- Winskel, The Formal Semantics of Programming Languages. Read the chapter on the denotational semantics of IMP for this topic's core, and the later chapters on domain theory and recursion equations for the extension to higher-order languages.
- Nielson and Nielson, Semantics with Applications. Read the denotational semantics chapters for a second treatment of the fixed-point semantics of While and its equivalence with operational semantics.
- Plotkin, LCF Considered as a Programming Language, Theoretical Computer Science 5(3), 1977. Read it for PCF, adequacy and the failure of full abstraction.
- Scott and Strachey, Toward a Mathematical Semantics for Computer Languages, Oxford Programming Research Group monograph PRG-6, 1971. Read it for the historical motivation.
- Gunter, Semantics of Programming Languages, MIT Press 1992. Read it for a textbook development of domains and PCF.
- Abramsky and Jung, Domain Theory, in Handbook of Logic in Computer Science, volume 3, 1994. Read it as the reference for the general theory.
