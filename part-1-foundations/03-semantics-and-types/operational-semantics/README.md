# Operational Semantics

Part 1, Chapter 3: Semantics and Types.

## Objective

Write big-step and small-step semantics for a small language and prove them equivalent.

## Why this matters

An operational semantics is the ground truth against which other claims about a program are judged. Hoare logic in [Axiomatic Semantics](../axiomatic-semantics/) is sound relative to it, type safety in [Type Systems](../type-systems/) is stated in terms of it, and the transition systems of [Chapter 8](../../../part-2-core-reasoning/08-model-checking/transition-systems-and-temporal-logic/) are small-step semantics under another name. When an applied scientist builds a verifier for a real language, the first hard question is what the language means, and the answer is usually written in this style, so that the verifier's soundness has something to be sound against.

## Prerequisites

- [Induction Principles](../induction-principles/), for rule induction, inversion and the substitution lemma for arithmetic expressions.
- [First-Order Logic](../../01-mathematical-logic/first-order-logic/), for reading the side conditions and the statements of theorems.

## Lesson

### The language IMP

IMP is a small imperative language with integer variables. Its syntax is

$$a ::= n \mid x \mid a_1 + a_2 \mid a_1 - a_2 \mid a_1 \times a_2$$

$$b ::= \texttt{true} \mid \texttt{false} \mid a_1 = a_2 \mid a_1 \le a_2 \mid \neg b \mid b_1 \land b_2$$

$$c ::= \texttt{skip} \mid x := a \mid c_1 ; c_2 \mid \texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2 \mid \texttt{while}\ b\ \texttt{do}\ c$$

A state is a total function $\sigma : \mathrm{Var} \to \mathbb{Z}$, and $\Sigma$ is the set of states. The notation $\sigma[x \mapsto v]$ denotes the state that maps $x$ to $v$ and agrees with $\sigma$ elsewhere.

Expressions have no side effects and always terminate, so their meaning is given by total functions defined by structural recursion: $\mathcal{A}[\![a]\!] : \Sigma \to \mathbb{Z}$ as in [Induction Principles](../induction-principles/), and $\mathcal{B}[\![b]\!] : \Sigma \to \{\mathrm{tt}, \mathrm{ff}\}$ with the obvious clauses, such as $\mathcal{B}[\![a_1 \le a_2]\!]\sigma = \mathrm{tt}$ iff $\mathcal{A}[\![a_1]\!]\sigma \le \mathcal{A}[\![a_2]\!]\sigma$.

Commands are where termination becomes an issue, so they get the relational treatment below.

### Big-step semantics

Big-step semantics, also called natural semantics, defines a judgment $\langle c, \sigma\rangle \Downarrow \sigma'$, read as "command $c$ started in $\sigma$ terminates in $\sigma'$". It relates a command directly to its final result.

$$\frac{}{\langle \texttt{skip}, \sigma\rangle \Downarrow \sigma}\ \text{(B-Skip)} \qquad \frac{}{\langle x := a, \sigma\rangle \Downarrow \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]}\ \text{(B-Assign)}$$

$$\frac{\langle c_1, \sigma\rangle \Downarrow \sigma' \quad \langle c_2, \sigma'\rangle \Downarrow \sigma''}{\langle c_1 ; c_2, \sigma\rangle \Downarrow \sigma''}\ \text{(B-Seq)}$$

$$\frac{\mathcal{B}[\![b]\!]\sigma = \mathrm{tt} \quad \langle c_1, \sigma\rangle \Downarrow \sigma'}{\langle \texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2, \sigma\rangle \Downarrow \sigma'}\ \text{(B-IfT)} \qquad \frac{\mathcal{B}[\![b]\!]\sigma = \mathrm{ff} \quad \langle c_2, \sigma\rangle \Downarrow \sigma'}{\langle \texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2, \sigma\rangle \Downarrow \sigma'}\ \text{(B-IfF)}$$

$$\frac{\mathcal{B}[\![b]\!]\sigma = \mathrm{ff}}{\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma\rangle \Downarrow \sigma}\ \text{(B-WhileF)}$$

$$\frac{\mathcal{B}[\![b]\!]\sigma = \mathrm{tt} \quad \langle c, \sigma\rangle \Downarrow \sigma' \quad \langle \texttt{while}\ b\ \texttt{do}\ c, \sigma'\rangle \Downarrow \sigma''}{\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma\rangle \Downarrow \sigma''}\ \text{(B-WhileT)}$$

The relation is the set inductively defined by these rules, so it consists of exactly the triples with a finite derivation. The rule B-WhileT has a premise about the same command as its conclusion, which is why proofs about this relation use rule induction and cannot use structural induction on $c$.

Theorem 1 (determinism of big-step). If $\langle c, \sigma\rangle \Downarrow \sigma_1$ and $\langle c, \sigma\rangle \Downarrow \sigma_2$, then $\sigma_1 = \sigma_2$.

Proof. Use rule induction on the first derivation with the property $P(c, \sigma, \sigma_1) := \forall \sigma_2.\ \langle c, \sigma\rangle \Downarrow \sigma_2 \to \sigma_2 = \sigma_1$. The universal quantifier is needed because the intermediate states differ between premises and conclusion.

Case B-Skip and case B-Assign. Only one rule concludes about this command, and it gives a single result, so inversion on the second derivation gives $\sigma_2 = \sigma_1$.

Case B-Seq, with $c = c_1; c_2$, premises $\langle c_1, \sigma\rangle \Downarrow \sigma'$ and $\langle c_2, \sigma'\rangle \Downarrow \sigma_1$. Inversion on the second derivation gives $\tau$ with $\langle c_1, \sigma\rangle \Downarrow \tau$ and $\langle c_2, \tau\rangle \Downarrow \sigma_2$. The hypothesis for $c_1$ gives $\tau = \sigma'$. Then the hypothesis for $c_2$ at $\sigma'$ gives $\sigma_2 = \sigma_1$.

Case B-IfT. Then $\mathcal{B}[\![b]\!]\sigma = \mathrm{tt}$, so inversion excludes B-IfF, and the second derivation ends with B-IfT with premise $\langle c_1, \sigma\rangle \Downarrow \sigma_2$. The hypothesis gives $\sigma_2 = \sigma_1$. Case B-IfF is symmetric.

Case B-WhileF. Then $\mathcal{B}[\![b]\!]\sigma = \mathrm{ff}$, so the second derivation also ends with B-WhileF, and $\sigma_2 = \sigma = \sigma_1$.

Case B-WhileT, with premises $\langle c, \sigma\rangle \Downarrow \sigma'$ and $\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma'\rangle \Downarrow \sigma_1$. The guard is true, so the second derivation also ends with B-WhileT, with premises $\langle c, \sigma\rangle \Downarrow \tau$ and $\langle \texttt{while}\ b\ \texttt{do}\ c, \tau\rangle \Downarrow \sigma_2$. The hypothesis gives $\tau = \sigma'$, and then $\sigma_2 = \sigma_1$. $\square$

### Small-step semantics

Small-step semantics, also called structural operational semantics, defines a transition relation $\langle c, \sigma\rangle \longrightarrow \langle c', \sigma'\rangle$ on configurations. It describes one step of computation, and $c'$ is what remains to be done.

$$\frac{}{\langle x := a, \sigma\rangle \longrightarrow \langle \texttt{skip}, \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]\rangle}\ \text{(S-Assign)}$$

$$\frac{\langle c_1, \sigma\rangle \longrightarrow \langle c_1', \sigma'\rangle}{\langle c_1 ; c_2, \sigma\rangle \longrightarrow \langle c_1' ; c_2, \sigma'\rangle}\ \text{(S-Seq)} \qquad \frac{}{\langle \texttt{skip} ; c_2, \sigma\rangle \longrightarrow \langle c_2, \sigma\rangle}\ \text{(S-SeqSkip)}$$

$$\frac{\mathcal{B}[\![b]\!]\sigma = \mathrm{tt}}{\langle \texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2, \sigma\rangle \longrightarrow \langle c_1, \sigma\rangle}\ \text{(S-IfT)} \qquad \frac{\mathcal{B}[\![b]\!]\sigma = \mathrm{ff}}{\langle \texttt{if}\ b\ \texttt{then}\ c_1\ \texttt{else}\ c_2, \sigma\rangle \longrightarrow \langle c_2, \sigma\rangle}\ \text{(S-IfF)}$$

$$\frac{}{\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma\rangle \longrightarrow \langle \texttt{if}\ b\ \texttt{then}\ (c ; \texttt{while}\ b\ \texttt{do}\ c)\ \texttt{else}\ \texttt{skip}, \sigma\rangle}\ \text{(S-While)}$$

The command $\texttt{skip}$ has no transition, and a configuration $\langle \texttt{skip}, \sigma\rangle$ is terminal. Write $\longrightarrow^{\ast}$ for the reflexive transitive closure and $\longrightarrow^{k}$ for exactly $k$ steps.

The rule S-While is the only one that grows the command. It is the reason a loop can run forever, and it also makes clear that a structural measure on commands does not decrease.

Proposition 2 (properties of small-step). (a) Determinism: each configuration has at most one successor. (b) Progress: each configuration with $c \ne \texttt{skip}$ has a successor.

Proof. Part (a) is by rule induction on the first step. All rule conclusions have different top-level forms, except for S-Seq and S-SeqSkip and the two conditional rules. S-Seq requires $c_1$ to step, and S-SeqSkip requires $c_1 = \texttt{skip}$, which has no step, so they are exclusive. The conditional rules are exclusive by the guard. In the S-Seq case the hypothesis gives a unique successor for $c_1$. Part (b) is by structural induction on $c$. In the case $c_1; c_2$, either $c_1 = \texttt{skip}$, and S-SeqSkip applies, or the hypothesis gives a step of $c_1$, and S-Seq applies. All other non-skip forms have a rule that applies unconditionally or by the value of the guard. $\square$

### The equivalence theorem

Theorem 3. For all $c, \sigma, \sigma'$,

$$\langle c, \sigma\rangle \Downarrow \sigma' \quad \text{if and only if} \quad \langle c, \sigma\rangle \longrightarrow^{\ast} \langle \texttt{skip}, \sigma'\rangle.$$

The proof uses two lemmas.

Lemma A (sequencing). If $\langle c_1, \sigma\rangle \longrightarrow^{\ast} \langle c_1', \sigma'\rangle$, then $\langle c_1 ; c_2, \sigma\rangle \longrightarrow^{\ast} \langle c_1' ; c_2, \sigma'\rangle$.

Proof. Induct on the number of steps, applying S-Seq to each step. $\square$

Lemma B (expansion). If $\langle c, \sigma\rangle \longrightarrow \langle c', \sigma'\rangle$ and $\langle c', \sigma'\rangle \Downarrow \sigma''$, then $\langle c, \sigma\rangle \Downarrow \sigma''$.

Proof. Use rule induction on the small step, with $\sigma''$ universally quantified.

Case S-Assign. Here $c' = \texttt{skip}$ and $\sigma' = \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]$. Inversion on $\langle \texttt{skip}, \sigma'\rangle \Downarrow \sigma''$ gives $\sigma'' = \sigma'$, and B-Assign concludes.

Case S-Seq. Here $c = c_1; c_2$ and $c' = c_1'; c_2$. Inversion on the big-step gives $\tau$ with $\langle c_1', \sigma'\rangle \Downarrow \tau$ and $\langle c_2, \tau\rangle \Downarrow \sigma''$. The hypothesis gives $\langle c_1, \sigma\rangle \Downarrow \tau$, and B-Seq concludes.

Case S-SeqSkip. Here $c = \texttt{skip}; c_2$, $c' = c_2$ and $\sigma' = \sigma$. B-Skip gives $\langle \texttt{skip}, \sigma\rangle \Downarrow \sigma$. B-Seq with the assumption concludes.

Case S-IfT. Here $c' = c_1$, $\sigma' = \sigma$, and the guard is true. B-IfT concludes. Case S-IfF is symmetric.

Case S-While. Write $W = \texttt{while}\ b\ \texttt{do}\ c_0$. The assumption is $\langle \texttt{if}\ b\ \texttt{then}\ (c_0; W)\ \texttt{else}\ \texttt{skip}, \sigma\rangle \Downarrow \sigma''$. Invert it. If the guard is true, then $\langle c_0; W, \sigma\rangle \Downarrow \sigma''$, and inverting again gives $\langle c_0, \sigma\rangle \Downarrow \tau$ and $\langle W, \tau\rangle \Downarrow \sigma''$, so B-WhileT concludes. If the guard is false, then $\langle \texttt{skip}, \sigma\rangle \Downarrow \sigma''$, so $\sigma'' = \sigma$, and B-WhileF concludes. $\square$

Proof of Theorem 3. For the forward direction, use rule induction on the big-step derivation.

Case B-Skip. Zero steps suffice.

Case B-Assign. One step by S-Assign suffices.

Case B-Seq. The hypotheses give $\langle c_1, \sigma\rangle \longrightarrow^{\ast} \langle \texttt{skip}, \sigma'\rangle$ and $\langle c_2, \sigma'\rangle \longrightarrow^{\ast} \langle \texttt{skip}, \sigma''\rangle$. Lemma A gives $\langle c_1; c_2, \sigma\rangle \longrightarrow^{\ast} \langle \texttt{skip}; c_2, \sigma'\rangle$. One S-SeqSkip step gives $\langle c_2, \sigma'\rangle$, and the second sequence finishes.

Case B-IfT. One S-IfT step, followed by the hypothesis, suffices. Case B-IfF is symmetric.

Case B-WhileF. S-While followed by S-IfF reaches $\langle \texttt{skip}, \sigma\rangle$.

Case B-WhileT. S-While followed by S-IfT reaches $\langle c; W, \sigma\rangle$. The hypothesis for $c$ with Lemma A reaches $\langle \texttt{skip}; W, \sigma'\rangle$. S-SeqSkip reaches $\langle W, \sigma'\rangle$, and the hypothesis for $W$ finishes.

For the backward direction, use induction on the number $k$ of steps. If $k = 0$, then $c = \texttt{skip}$ and $\sigma' = \sigma$, so B-Skip applies. If $k > 0$, the sequence starts with a step to some $\langle c_1, \sigma_1\rangle$, from which $\langle \texttt{skip}, \sigma'\rangle$ is reached in $k - 1$ steps. The hypothesis gives $\langle c_1, \sigma_1\rangle \Downarrow \sigma'$, and Lemma B gives $\langle c, \sigma\rangle \Downarrow \sigma'$. $\square$

Corollary 4. The following are equivalent: there is no $\sigma'$ with $\langle c, \sigma\rangle \Downarrow \sigma'$; the small-step sequence from $\langle c, \sigma\rangle$ is infinite.

Proof. By determinism, the sequence from a configuration is unique. By progress, it ends only at a $\texttt{skip}$ configuration. So it is either infinite or reaches $\langle \texttt{skip}, \sigma'\rangle$ for some $\sigma'$, and Theorem 3 identifies the second alternative with the existence of a big-step derivation. $\square$

Corollary 4 relies on determinism and progress, and it fails when either is lost, as Exercises 9 and 10 show.

### Choosing between the styles

| Question | Big-step | Small-step |
|---|---|---|
| What does a judgment describe? | It describes a complete terminating run. | It describes one step of a run. |
| How does divergence appear? | Divergence appears as the absence of a derivation. | Divergence appears as an infinite sequence. |
| How does a stuck program appear? | A stuck program also appears as the absence of a derivation. | A stuck program appears as a nonterminal configuration with no successor. |
| Which proofs does it suit? | It suits proofs about terminating runs, such as compiler correctness and Hoare logic soundness. | It suits proofs about intermediate states, such as type safety and invariants. |
| How does it treat concurrency? | It handles interleaving poorly. | It models interleaving directly. |

The third row explains why type soundness uses small-step semantics: a statement that a well-typed program does not get stuck cannot be expressed if stuck and divergent programs look alike. The last row is the subject of Exercise 11.

### Program equivalence

Commands $c_1$ and $c_2$ are equivalent, written $c_1 \sim c_2$, if $\langle c_1, \sigma\rangle \Downarrow \sigma'$ and $\langle c_2, \sigma\rangle \Downarrow \sigma'$ hold for the same triples, that is, for all $\sigma, \sigma'$, one holds iff the other does. Because $\sim$ is a congruence, replacing a subcommand by an equivalent subcommand gives an equivalent program, which justifies compiler optimizations. Exercise 8 proves the only nontrivial case.

### Evaluation contexts

Small-step rules like S-Seq only say where the next step happens. An alternative is to separate this into a grammar of evaluation contexts, here $E ::= [\,] \mid E ; c$, with one rule that lifts a computation step $\langle c, \sigma\rangle \rightsquigarrow \langle c', \sigma'\rangle$ to $\langle E[c], \sigma\rangle \longrightarrow \langle E[c'], \sigma'\rangle$. For IMP the two formulations define the same relation. Wright and Felleisen's soundness method in [Type Systems](../type-systems/) uses this style.

### History

Before structural operational semantics, operational definitions were often given by abstract machines, such as Landin's SECD machine, whose details tended to obscure the language. Plotkin's 1981 Aarhus lecture notes showed that transitions could be defined by induction on program syntax, which gave proofs a uniform structure. Kahn's 1987 paper on natural semantics presented the big-step style as a system of inference rules relating programs directly to results.

## Worked examples

### Worked Example 1: a factorial program in both semantics

Let $B$ be $y := y \times x ; x := x - 1$, let $W$ be $\texttt{while}\ 1 \le x\ \texttt{do}\ B$, and let the program be $y := 1 ; W$. Let the initial state have $x = 2$ and $y = 0$. States are written as `[x,y]`, and `IF` abbreviates `if 1<=x then (B; W) else skip`.

Small-step trace. The trace was checked by an interpreter in a scratch script.

```
 0  < y:=1; W                 , [2,0] >
 1  < skip; W                 , [2,1] >   S-Seq(S-Assign)
 2  < W                       , [2,1] >   S-SeqSkip
 3  < IF                      , [2,1] >   S-While
 4  < (y:=y*x; x:=x-1); W     , [2,1] >   S-IfT, since 1<=2
 5  < (skip; x:=x-1); W       , [2,2] >   S-Seq(S-Seq(S-Assign))
 6  < x:=x-1; W               , [2,2] >   S-Seq(S-SeqSkip)
 7  < skip; W                 , [1,2] >   S-Seq(S-Assign)
 8  < W                       , [1,2] >   S-SeqSkip
 9  < IF                      , [1,2] >   S-While
10  < (y:=y*x; x:=x-1); W     , [1,2] >   S-IfT, since 1<=1
11  < (skip; x:=x-1); W       , [1,2] >   S-Seq(S-Seq(S-Assign))
12  < x:=x-1; W               , [1,2] >   S-Seq(S-SeqSkip)
13  < skip; W                 , [0,2] >   S-Seq(S-Assign)
14  < W                       , [0,2] >   S-SeqSkip
15  < IF                      , [0,2] >   S-While
16  < skip                    , [0,2] >   S-IfF, since not 1<=0
```

The program takes 16 steps and ends with $x = 0$ and $y = 2 = 2!$.

Big-step derivation. Each line names the rule and its premises.

```
D1: <y:=y*x, [2,1]> ⇓ [2,2]                 B-Assign
D2: <x:=x-1, [2,2]> ⇓ [1,2]                 B-Assign
D3: <B, [2,1]> ⇓ [1,2]                      B-Seq from D1, D2
D4: <y:=y*x, [1,2]> ⇓ [1,2]                 B-Assign
D5: <x:=x-1, [1,2]> ⇓ [0,2]                 B-Assign
D6: <B, [1,2]> ⇓ [0,2]                      B-Seq from D4, D5
D7: <W, [0,2]> ⇓ [0,2]                      B-WhileF, since not 1<=0
D8: <W, [1,2]> ⇓ [0,2]                      B-WhileT from 1<=1, D6, D7
D9: <W, [2,1]> ⇓ [0,2]                      B-WhileT from 1<=2, D3, D8
D10: <y:=1, [2,0]> ⇓ [2,1]                  B-Assign
D11: <y:=1; W, [2,0]> ⇓ [0,2]               B-Seq from D10, D9
```

Both semantics give the same final state, as Theorem 3 requires.

### Worked Example 2: a divergent loop

Let $W_\infty = \texttt{while}\ \texttt{true}\ \texttt{do}\ \texttt{skip}$. The small-step sequence from any $\sigma$ is periodic with period 3:

```
< while true do skip                                   , s >
< if true then (skip; while true do skip) else skip    , s >   S-While
< skip; while true do skip                             , s >   S-IfT
< while true do skip                                   , s >   S-SeqSkip
```

Claim. There is no derivation of $\langle W_\infty, \sigma\rangle \Downarrow \sigma'$. This is a consequence of Corollary 4, and a direct proof shows how to generalize a judgment with a fixed shape.

Prove by rule induction the property $P(c, \sigma, \sigma') := c \ne W_\infty$ for every derivable $\langle c, \sigma\rangle \Downarrow \sigma'$.

For all rules whose conclusion is not a while command, the property is immediate. For B-WhileF, the conclusion's command is $\texttt{while}\ b\ \texttt{do}\ c_0$ with $\mathcal{B}[\![b]\!]\sigma = \mathrm{ff}$. Since $\mathcal{B}[\![\texttt{true}]\!]\sigma = \mathrm{tt}$, we have $b \ne \texttt{true}$, so the command is not $W_\infty$. For B-WhileT, the third premise is about the same command as the conclusion, and the hypothesis says that this command is not $W_\infty$. $\square$

### Worked Example 3: loop unfolding

Claim. $\texttt{while}\ b\ \texttt{do}\ c \sim \texttt{if}\ b\ \texttt{then}\ (c ; \texttt{while}\ b\ \texttt{do}\ c)\ \texttt{else}\ \texttt{skip}$.

Write $W$ for the loop and $U$ for the conditional. No induction is needed, because the derivations differ only at their last few rules.

Assume $\langle W, \sigma\rangle \Downarrow \sigma'$. Invert. If B-WhileF was used, then the guard is false and $\sigma' = \sigma$. So B-Skip and B-IfF give $\langle U, \sigma\rangle \Downarrow \sigma$. If B-WhileT was used, then the guard is true and there is $\tau$ with $\langle c, \sigma\rangle \Downarrow \tau$ and $\langle W, \tau\rangle \Downarrow \sigma'$. B-Seq gives $\langle c ; W, \sigma\rangle \Downarrow \sigma'$, and B-IfT gives $\langle U, \sigma\rangle \Downarrow \sigma'$.

Assume $\langle U, \sigma\rangle \Downarrow \sigma'$. Invert. If B-IfT was used, then the guard is true and $\langle c; W, \sigma\rangle \Downarrow \sigma'$. Inverting B-Seq gives the premises of B-WhileT. If B-IfF was used, then the guard is false and $\langle \texttt{skip}, \sigma\rangle \Downarrow \sigma'$, so $\sigma' = \sigma$, and B-WhileF applies. $\square$

## Common mistakes

- Inducting on the structure of $c$ for a claim about $\langle c, \sigma\rangle \Downarrow \sigma'$. The while case then has no usable hypothesis. Correct by inducting on the derivation.
- Forgetting to quantify over the other state in determinism. The intermediate states differ between the two derivations, so the hypothesis must hold for all results. Correct by writing $\forall \sigma_2$ inside the property.
- Treating the absence of a big-step derivation as proof of divergence in every language. It is true for IMP by Corollary 4, and it fails once programs can get stuck or behave nondeterministically. Correct by checking determinism and progress first.
- Adding a small-step transition for $\texttt{skip}$. That destroys the terminal status of $\texttt{skip}$ and invalidates the statement of Theorem 3. Correct by keeping $\texttt{skip}$ terminal.
- Writing S-While as a rule whose premises mention the guard's value and then forgetting the false case. Both forms exist in the literature, and either is correct if the rules cover both values of the guard. Correct by checking progress for each new rule.
- Proving the backward direction of Theorem 3 by rule induction on small-step derivations of a sequence. The closure $\longrightarrow^{\ast}$ is the natural object of induction, and the argument needs Lemma B. Correct by inducting on the number of steps.
- Assuming that $c_1 \sim c_2$ means their traces are the same. Equivalence as defined here is about final states only, so $\texttt{skip}$ and $\texttt{skip} ; \texttt{skip}$ are equivalent, even though their small-step traces differ.

## Exercises

### Exercise 1

State the rules S-Seq and S-SeqSkip. Explain why $\langle \texttt{skip}, \sigma\rangle$ has no successor, and give all steps from $\langle \texttt{skip} ; \texttt{skip}, \sigma\rangle$.

<details><summary>Solution</summary>

The rules appear in the lesson. No rule has a conclusion with command $\texttt{skip}$ on the left of the transition, and the relation is the least one closed under the rules, so inversion shows that there is no successor. The sequence is one step, $\langle \texttt{skip} ; \texttt{skip}, \sigma\rangle \longrightarrow \langle \texttt{skip}, \sigma\rangle$, by S-SeqSkip. S-Seq cannot apply because its premise would be a step from $\texttt{skip}$.

</details>

### Exercise 2

Give the full small-step trace of $x := 1 ; \texttt{while}\ x \le 2\ \texttt{do}\ x := x + x$ from a state with $x = 0$.

<details><summary>Solution</summary>

Let `W` be the loop, and let `IF` be `if x<=2 then (x:=x+x; W) else skip`. The state is the value of $x$.

```
 0  < x:=1; W      , 0 >
 1  < skip; W      , 1 >   S-Seq(S-Assign)
 2  < W            , 1 >   S-SeqSkip
 3  < IF           , 1 >   S-While
 4  < x:=x+x; W    , 1 >   S-IfT, since 1<=2
 5  < skip; W      , 2 >   S-Seq(S-Assign)
 6  < W            , 2 >   S-SeqSkip
 7  < IF           , 2 >   S-While
 8  < x:=x+x; W    , 2 >   S-IfT, since 2<=2
 9  < skip; W      , 4 >   S-Seq(S-Assign)
10  < W            , 4 >   S-SeqSkip
11  < IF           , 4 >   S-While
12  < skip         , 4 >   S-IfF, since not 4<=2
```

</details>

### Exercise 3

Prove that $(c_1 ; c_2) ; c_3 \sim c_1 ; (c_2 ; c_3)$ and that $\texttt{if}\ b\ \texttt{then}\ c\ \texttt{else}\ c \sim c$.

<details><summary>Solution</summary>

Associativity. Assume $\langle (c_1; c_2); c_3, \sigma\rangle \Downarrow \sigma'$. Inverting B-Seq twice gives $\tau, \tau'$ with $\langle c_1, \sigma\rangle \Downarrow \tau$, $\langle c_2, \tau\rangle \Downarrow \tau'$ and $\langle c_3, \tau'\rangle \Downarrow \sigma'$. Applying B-Seq to the last two, and then to the first with the result, gives $\langle c_1; (c_2; c_3), \sigma\rangle \Downarrow \sigma'$. The converse is the same argument in reverse.

Conditional. Assume $\langle \texttt{if}\ b\ \texttt{then}\ c\ \texttt{else}\ c, \sigma\rangle \Downarrow \sigma'$. Inversion by either rule gives $\langle c, \sigma\rangle \Downarrow \sigma'$. Conversely, assume $\langle c, \sigma\rangle \Downarrow \sigma'$. The value $\mathcal{B}[\![b]\!]\sigma$ is tt or ff, since $\mathcal{B}$ is total. In the first case B-IfT applies and in the second case B-IfF applies.

</details>

### Exercise 4

Add the command $\texttt{repeat}\ c\ \texttt{until}\ b$, which executes $c$ and then stops if $b$ holds, otherwise repeating. Give big-step and small-step rules, and prove that it is equivalent to $c ; \texttt{while}\ \neg b\ \texttt{do}\ c$.

<details><summary>Solution</summary>

Write $R$ for $\texttt{repeat}\ c\ \texttt{until}\ b$ and $W$ for $\texttt{while}\ \neg b\ \texttt{do}\ c$.

Big-step rules:

$$\frac{\langle c, \sigma\rangle \Downarrow \sigma' \quad \mathcal{B}[\![b]\!]\sigma' = \mathrm{tt}}{\langle R, \sigma\rangle \Downarrow \sigma'}\ \text{(R1)} \qquad \frac{\langle c, \sigma\rangle \Downarrow \sigma' \quad \mathcal{B}[\![b]\!]\sigma' = \mathrm{ff} \quad \langle R, \sigma'\rangle \Downarrow \sigma''}{\langle R, \sigma\rangle \Downarrow \sigma''}\ \text{(R2)}$$

Small-step rule: $\langle R, \sigma\rangle \longrightarrow \langle c ; \texttt{if}\ b\ \texttt{then}\ \texttt{skip}\ \texttt{else}\ R, \sigma\rangle$.

From $R$ to $c ; W$. Use rule induction on the derivation for $R$, with the property: the command is $R$ implies $\langle c; W, \sigma\rangle \Downarrow \sigma''$.

Case R1. The guard $\neg b$ is false at $\sigma'$, so B-WhileF gives $\langle W, \sigma'\rangle \Downarrow \sigma'$. B-Seq concludes.

Case R2. The hypothesis gives $\langle c; W, \sigma'\rangle \Downarrow \sigma''$. Inverting gives $\tau$ with $\langle c, \sigma'\rangle \Downarrow \tau$ and $\langle W, \tau\rangle \Downarrow \sigma''$. The guard $\neg b$ is true at $\sigma'$, so B-WhileT gives $\langle W, \sigma'\rangle \Downarrow \sigma''$. B-Seq with $\langle c, \sigma\rangle \Downarrow \sigma'$ concludes.

From $c ; W$ to $R$. Inversion gives $\langle c, \sigma\rangle \Downarrow \tau$ and $\langle W, \tau\rangle \Downarrow \sigma''$. So it suffices to prove the lemma: for every derivation of $\langle W, \tau\rangle \Downarrow \sigma''$ and every $\sigma_0$ with $\langle c, \sigma_0\rangle \Downarrow \tau$, we have $\langle R, \sigma_0\rangle \Downarrow \sigma''$. Use rule induction on the derivation for $W$, with the appropriate guard on shape.

Case B-WhileF. The guard $\neg b$ is false at $\tau$, so $\mathcal{B}[\![b]\!]\tau = \mathrm{tt}$ and $\sigma'' = \tau$. R1 concludes.

Case B-WhileT. The guard $\neg b$ is true at $\tau$, with $\langle c, \tau\rangle \Downarrow \tau'$ and $\langle W, \tau'\rangle \Downarrow \sigma''$. The hypothesis, with $\sigma_0 := \tau$, gives $\langle R, \tau\rangle \Downarrow \sigma''$. R2 with $\langle c, \sigma_0\rangle \Downarrow \tau$ and $\mathcal{B}[\![b]\!]\tau = \mathrm{ff}$ concludes.

</details>

### Exercise 5

Prove that if $\langle \texttt{while}\ b\ \texttt{do}\ c, \sigma\rangle \Downarrow \sigma'$, then $\mathcal{B}[\![b]\!]\sigma' = \mathrm{ff}$.

<details><summary>Solution</summary>

Use rule induction with the property $P(c', \sigma, \sigma')$: if $c' = \texttt{while}\ b\ \texttt{do}\ c$, then $\mathcal{B}[\![b]\!]\sigma' = \mathrm{ff}$. Rules that conclude about other command forms satisfy it vacuously.

Case B-WhileF. Then $\sigma' = \sigma$ and the rule's premise is $\mathcal{B}[\![b]\!]\sigma = \mathrm{ff}$.

Case B-WhileT. The third premise is $\langle \texttt{while}\ b\ \texttt{do}\ c, \tau\rangle \Downarrow \sigma'$, with the same command. The hypothesis gives $\mathcal{B}[\![b]\!]\sigma' = \mathrm{ff}$.

</details>

### Exercise 6

Prove that $x := a ; x := a' \sim x := a'[a/x]$, where $a'[a/x]$ is the substitution from [Induction Principles](../induction-principles/).

<details><summary>Solution</summary>

From the left, inversion gives a single result: $\tau = \sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]$ after the first assignment, and $\tau[x \mapsto \mathcal{A}[\![a']\!]\tau] = \sigma[x \mapsto \mathcal{A}[\![a']\!]\tau]$ after the second.

From the right, the result is $\sigma[x \mapsto \mathcal{A}[\![a'[a/x]]\!]\sigma]$. The substitution lemma says $\mathcal{A}[\![a'[a/x]]\!]\sigma = \mathcal{A}[\![a']\!](\sigma[x \mapsto \mathcal{A}[\![a]\!]\sigma]) = \mathcal{A}[\![a']\!]\tau$.

So both commands relate $\sigma$ to exactly the state $\sigma[x \mapsto \mathcal{A}[\![a']\!]\tau]$.

</details>

### Exercise 7

Prove the following. If $\langle c_1; c_2, \sigma\rangle \longrightarrow^{k} \langle \texttt{skip}, \sigma''\rangle$, then there are $\sigma'$, $k_1$ and $k_2$ with $\langle c_1, \sigma\rangle \longrightarrow^{k_1} \langle \texttt{skip}, \sigma'\rangle$, $\langle c_2, \sigma'\rangle \longrightarrow^{k_2} \langle \texttt{skip}, \sigma''\rangle$, and $k_1 + k_2 + 1 = k$.

<details><summary>Solution</summary>

Use course-of-values induction on $k$, with $c_1$ and $\sigma$ universally quantified. Since $c_1; c_2 \ne \texttt{skip}$, we have $k \ge 1$. Examine the first step, which by inversion uses one of two rules.

Case S-SeqSkip. Then $c_1 = \texttt{skip}$, and the next configuration is $\langle c_2, \sigma\rangle$. Take $\sigma' = \sigma$, $k_1 = 0$ and $k_2 = k - 1$.

Case S-Seq. The first step is $\langle c_1', \sigma_1\rangle$ with $\langle c_1, \sigma\rangle \longrightarrow \langle c_1', \sigma_1\rangle$, followed by $\langle c_1'; c_2, \sigma_1\rangle \longrightarrow^{k-1} \langle \texttt{skip}, \sigma''\rangle$. The hypothesis gives $\sigma'$, $k_1'$ and $k_2$ with $k_1' + k_2 + 1 = k - 1$, $\langle c_1', \sigma_1\rangle \longrightarrow^{k_1'} \langle \texttt{skip}, \sigma'\rangle$ and the sequence for $c_2$. Take $k_1 = k_1' + 1$.

</details>

### Exercise 8

Prove that if $c \sim c'$, then $\texttt{while}\ b\ \texttt{do}\ c \sim \texttt{while}\ b\ \texttt{do}\ c'$.

<details><summary>Solution</summary>

By symmetry, it suffices to prove one direction. Write $W$ and $W'$ for the two loops. Use rule induction with the property: if the command is $W$, then $\langle W', \sigma\rangle \Downarrow \sigma'$.

Case B-WhileF. The guard is false at $\sigma$, and $\sigma' = \sigma$. B-WhileF applies to $W'$.

Case B-WhileT. The guard is true, $\langle c, \sigma\rangle \Downarrow \tau$ and $\langle W, \tau\rangle \Downarrow \sigma'$. Since $c \sim c'$, we have $\langle c', \sigma\rangle \Downarrow \tau$. The hypothesis gives $\langle W', \tau\rangle \Downarrow \sigma'$. B-WhileT applies to $W'$.

Structural induction on $c$ would not help, because the relation between $W$ and $W'$ is established per derivation.

</details>

### Exercise 9

Add a command $\texttt{abort}$ with no rules at all, in either semantics. Determine which of Theorems 1 and 3, Proposition 2 and Corollary 4 still hold. Explain what the two semantics say about $\texttt{abort}$ and $W_\infty$.

<details><summary>Solution</summary>

Theorem 1 holds, since no new rules or cases arise. Proposition 2(a) holds for the same reason. Proposition 2(b) fails, because $\texttt{abort}$ is not $\texttt{skip}$ and has no successor. Theorem 3 holds, since no case of the proof involves a new rule. Corollary 4 fails: $\langle \texttt{abort}, \sigma\rangle$ has no big-step derivation and its small-step sequence is finite, ending at a stuck configuration.

In the big-step semantics, $\texttt{abort} \sim W_\infty$, because neither has any derivation. In the small-step semantics they are distinguishable: the first is stuck immediately, and the second runs forever. This is why safety theorems are stated with small steps.

</details>

### Exercise 10

Add nondeterministic choice $c_1 \ \texttt{or}\ c_2$, with big-step rules that derive $\langle c_1 \ \texttt{or}\ c_2, \sigma\rangle \Downarrow \sigma'$ from either $\langle c_1, \sigma\rangle \Downarrow \sigma'$ or $\langle c_2, \sigma\rangle \Downarrow \sigma'$, and small-step rules $\langle c_1 \ \texttt{or}\ c_2, \sigma\rangle \longrightarrow \langle c_i, \sigma\rangle$ for $i \in \{1, 2\}$. Decide which results survive, and find a program that shows Corollary 4 failing.

<details><summary>Solution</summary>

Determinism fails in both semantics: $x := 0 \ \texttt{or}\ x := 1$ has two outcomes. Progress survives, since the new form always has a step.

Theorem 3 survives. Its proof uses neither determinism nor progress, and there are only new cases. Forward: one step to the chosen $c_i$, followed by the hypothesis. Lemma B: for a choice step to $c_i$ with $\langle c_i, \sigma\rangle \Downarrow \sigma''$, the big-step rule for that branch applies.

Corollary 4 fails. The program $\texttt{skip} \ \texttt{or}\ W_\infty$ has the big-step derivation with $\sigma' = \sigma$, and it also has an infinite small-step run. So the existence of a derivation no longer rules out divergence. The big-step semantics only records may-termination.

</details>

### Exercise 11

Add parallel composition $c_1 \parallel c_2$ with interleaving. Give the small-step rules. Compute the final values of $x$ for $x := 1 \parallel (x := 2 ; x := x + x)$, and compare them with those of $x := 1 \parallel x := 4$. Explain what this shows about big-step semantics.

<details><summary>Solution</summary>

Rules: from $\langle c_1, \sigma\rangle \longrightarrow \langle c_1', \sigma'\rangle$, infer $\langle c_1 \parallel c_2, \sigma\rangle \longrightarrow \langle c_1' \parallel c_2, \sigma'\rangle$; symmetrically for $c_2$; and $\langle \texttt{skip} \parallel c, \sigma\rangle \longrightarrow \langle c, \sigma\rangle$ and $\langle c \parallel \texttt{skip}, \sigma\rangle \longrightarrow \langle c, \sigma\rangle$.

For the first program, the assignment $x := 1$ can occur in three positions relative to the two assignments of the other side.

```
x:=1, x:=2, x:=x+x    final x = 4
x:=2, x:=1, x:=x+x    final x = 2
x:=2, x:=x+x, x:=1    final x = 1
```

For the second program, the final values are $1$ and $4$.

The commands $x := 2 ; x := x + x$ and $x := 4$ are equivalent under $\sim$, since both map each state to the same result, yet in parallel context they produce different sets of outcomes. So a semantics that records only initial and final states cannot be compositional for parallel composition: it discards the intermediate state at which the other thread can interfere. Small-step semantics retains that state.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Write the big-step and small-step rules for IMP from memory.
- Prove determinism of big-step semantics, including the while case.
- Prove the equivalence theorem, including both lemmas.
- Trace a small program by hand in both semantics.
- Explain with an example how stuck programs, divergence and nondeterminism are seen by each style.

## Materials

- Winskel, The Formal Semantics of Programming Languages. Read the introduction to operational semantics for IMP, which uses big-step rules and defines expression evaluation by rules as well.
- Nielson and Nielson, Semantics with Applications. Read the operational semantics chapters for natural semantics, structural operational semantics and their equivalence for the While language.
- Plotkin, A Structural Approach to Operational Semantics, Aarhus University report DAIMI FN-19, 1981, reprinted in the Journal of Logic and Algebraic Programming 60-61, 2004. Read it as the source of the small-step style.
- Kahn, Natural Semantics, STACS 1987. Read it as the source of the term and method of natural semantics.
- Nipkow and Klein, Concrete Semantics with Isabelle/HOL, Springer 2014. Read it to see the same material mechanized once you reach [Chapter 12](../../../part-4-remaining-methods/12-proof-assistants/).
