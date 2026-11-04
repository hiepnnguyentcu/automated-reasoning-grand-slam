# Computability

Part 1, Chapter 2: Decidability and Complexity.

## Objective

Prove undecidability results using Turing machines, the halting problem and Rice's theorem.

## Why this matters

Every reasoning tool has a question it cannot answer in general, and computability tells you which question that is. A tool for [quantified SMT](../../../part-2-core-reasoning/05-smt/quantifiers/), a [software model checker](../../../part-2-core-reasoning/08-model-checking/software-model-checking/) or a verifier that needs [loop invariants](../../../part-2-core-reasoning/07-deductive-verification/loop-invariants/) must give up one of three things: soundness, completeness or termination. As an applied scientist you will decide which one to give up, and you will need to recognize quickly when a customer's request is undecidable as stated and what restriction makes it decidable. The next topics in this chapter also reuse the reductions built here.

## Prerequisites

- [Propositional Logic](../../01-mathematical-logic/propositional-logic/), for the idea of a formula as a finite object that a machine can process.
- [First-Order Logic](../../01-mathematical-logic/first-order-logic/), for the examples about validity and theories.

## Lesson

### Decision problems and encodings

A decision problem is a set of yes-instances. To make this precise, fix a finite alphabet $\Sigma$ and represent every instance as a string in $\Sigma^*$. A decision problem is then a language $L \subseteq \Sigma^*$, and solving it means determining, for an input $x$, whether $x \in L$.

You will write $\langle X \rangle$ for the encoding of an object $X$, such as a formula, a program or a machine. The choice of reasonable encoding does not affect decidability, because a machine can translate between reasonable encodings. Malformed strings are treated as no-instances, and checking well-formedness is decidable, so proofs may ignore them.

Examples from automated reasoning are the following languages.

$$
\mathrm{SAT} = \{\langle \varphi \rangle : \varphi \text{ is a satisfiable propositional formula}\}
$$

$$
\mathrm{VALID} = \{\langle \varphi \rangle : \varphi \text{ is a valid first-order sentence}\}
$$

### Turing machines

Turing introduced his machine in 1936 to give a precise meaning to "mechanical procedure" and to settle Hilbert's decision problem for first-order logic. The model was designed to capture what a person with pencil and paper can do by following fixed rules: finite memory of the current step, attention to one symbol at a time, and unbounded paper.

A Turing machine is a tuple $M = (Q, \Sigma, \Gamma, \delta, q_0, q_{\mathrm{acc}}, q_{\mathrm{rej}})$ where:

- $Q$ is a finite set of states,
- $\Sigma$ is the input alphabet, and it does not contain the blank symbol $\sqcup$,
- $\Gamma \supseteq \Sigma \cup \{\sqcup\}$ is the finite tape alphabet,
- $q_0 \in Q$ is the start state,
- $q_{\mathrm{acc}} \ne q_{\mathrm{rej}}$ are the halting states,
- $\delta : (Q \setminus \{q_{\mathrm{acc}}, q_{\mathrm{rej}}\}) \times \Gamma \to Q \times \Gamma \times \{L, R\}$ is the transition function.

The tape is infinite to the right and has a leftmost cell. The input starts in the leftmost cell, the remaining cells hold $\sqcup$, and the head starts on the leftmost cell. A left move on the leftmost cell leaves the head in place.

A configuration records the state, the tape contents and the head position. This topic writes a configuration as `u[q]v`, meaning that the tape holds $uv$ followed by blanks, the state is $q$, and the head reads the first symbol of $v$. The relation "yields" between configurations is defined by one application of $\delta$. On input $x$, the machine either reaches $q_{\mathrm{acc}}$ and accepts, reaches $q_{\mathrm{rej}}$ and rejects, or runs forever and loops.

Definitions:

- $L(M) = \{x : M \text{ accepts } x\}$ is the language recognized by $M$.
- $M$ is a decider if it halts on every input.
- A language is decidable if some decider recognizes it.
- A language is recognizable, also called recursively enumerable, if some Turing machine recognizes it.
- A language is co-recognizable if its complement is recognizable.

Multi-tape machines, nondeterministic machines and random-access machines recognize the same languages as this basic model. A nondeterministic machine is simulated by breadth-first search over its tree of configurations. These simulations may cost time, and complexity theory cares about that cost, but they do not change what is computable.

The Church-Turing thesis says that every effective procedure can be carried out by a Turing machine. It is a claim relating an informal notion to a formal one, so it cannot be proved as a theorem. It is supported by the equivalence of all proposed models, including the lambda calculus and general recursive functions. In practice, it allows you to describe machines as programs, and this topic does so from here on.

A machine can be encoded as a string, so a machine can take another machine as input. There is a universal machine $U$ which, on input $\langle M, x \rangle$, simulates $M$ on $x$. This fact is the source of both the power and the limits of computation.

### Recognizable and decidable

Theorem. A language $L$ is decidable if and only if $L$ and $\overline{L}$ are both recognizable.

Proof. If a decider $D$ recognizes $L$, then $D$ recognizes $L$, and $D$ with its answers swapped recognizes $\overline{L}$. Conversely, let $M_1$ recognize $L$ and $M_2$ recognize $\overline{L}$. On input $x$, run both machines in alternation, one step each. Every $x$ belongs to exactly one of the two languages, so one of the machines eventually accepts. Accept if $M_1$ accepts, and reject if $M_2$ accepts. $\square$

The technique of alternating steps among computations is called dovetailing. A portfolio SAT solver that runs a local search engine for models and CDCL for refutations follows the same pattern, although each of its engines already terminates or is cut off by a budget. The theorem also explains first-order reasoning: validity is recognizable through enumeration of proofs, and it fails to be decidable because its complement is not recognizable.

### The halting problem

Define

$$
A_{\mathrm{TM}} = \{\langle M, w \rangle : M \text{ accepts } w\}, \qquad
\mathrm{HALT} = \{\langle M, w \rangle : M \text{ halts on } w\}.
$$

Both languages are recognizable, by simulation.

Theorem (Turing). $A_{\mathrm{TM}}$ is undecidable.

Proof. Assume a decider $H$ exists for $A_{\mathrm{TM}}$. Define the machine $D$ as follows.

```
D on input <M>:
    run H on <M, <M>>
    if H accepts, reject
    if H rejects, accept
```

$D$ halts on every input, since $H$ does. Now consider $D$ on $\langle D \rangle$. By the definition of $D$, it accepts $\langle D \rangle$ exactly when $H$ rejects $\langle D, \langle D \rangle \rangle$, and by the correctness of $H$, that happens exactly when $D$ does not accept $\langle D \rangle$. This is a contradiction. $\square$

The proof is Cantor's diagonal argument. List all machines as rows and all machine encodings as columns, and let each entry say whether the row machine accepts the column string. The machine $D$ differs from every row on the diagonal, so it cannot be one of the rows.

Corollary. $\overline{A_{\mathrm{TM}}}$ is not recognizable, since otherwise $A_{\mathrm{TM}}$ would be decidable by the previous theorem.

### Reductions

A mapping reduction from $A$ to $B$, written $A \le_m B$, is a total computable function $f$ such that for all $x$,

$$
x \in A \iff f(x) \in B.
$$

Lemma. Suppose $A \le_m B$. If $B$ is decidable, then $A$ is decidable. If $B$ is recognizable, then $A$ is recognizable.

Proof. To test $x \in A$, compute $f(x)$ and run the machine for $B$ on it. $\square$

The contrapositive is the tool you will use. To prove $B$ undecidable, reduce a known undecidable $A$ to $B$. The direction matters. The reduction transforms instances of the known hard problem into instances of the new problem. Also note that $A \le_m B$ if and only if $\overline{A} \le_m \overline{B}$, with the same function $f$.

A Turing reduction $A \le_T B$ is an algorithm for $A$ that may call a decider for $B$ as a subroutine. It is more permissive, since any language is Turing-reducible to its complement. Turing reductions transfer decidability, and they do not transfer recognizability. To show that a language is not recognizable, use a mapping reduction.

Theorem. $A_{\mathrm{TM}} \le_m \mathrm{HALT}$, so $\mathrm{HALT}$ is undecidable.

Proof. Map $\langle M, w \rangle$ to $\langle M', w \rangle$, where $M'$ simulates $M$ and enters an infinite loop whenever $M$ would reject. Then $M'$ halts on $w$ exactly when $M$ accepts $w$. The map only rewrites the description of $M$, so it is computable. $\square$

Every undecidability proof by mapping reduction has the same structure.

1. Choose a known undecidable language $A$.
2. Describe $f$, and observe that $f$ only constructs a description and never runs the input machine.
3. Prove both directions of $x \in A \iff f(x) \in B$.

### Rice's theorem

A language property is a set $P$ of recognizable languages. The associated machine language is

$$
L_P = \{\langle M \rangle : L(M) \in P\}.
$$

Membership of $\langle M \rangle$ in $L_P$ depends only on the language of $M$, so two machines with the same language receive the same answer. $P$ is nontrivial if at least one recognizable language lies in $P$ and at least one lies outside $P$.

Theorem (Rice, 1953). If $P$ is a nontrivial property of recognizable languages, then $L_P$ is undecidable.

Proof. The property $P$ is either a set containing $\emptyset$ or a set omitting it. Assume first that $\emptyset \notin P$. Since $P$ is nontrivial, pick $L_0 \in P$ and a machine $M_0$ recognizing $L_0$. Reduce $A_{\mathrm{TM}}$ to $L_P$ by mapping $\langle M, w \rangle$ to $\langle M' \rangle$, where $M'$ is the following machine.

```
M' on input x:
    simulate M on w
    if M rejects, reject
    if M accepts, run M0 on x and return its answer
```

If $M$ accepts $w$, then $L(M') = L_0 \in P$. If $M$ does not accept $w$, then $L(M') = \emptyset \notin P$. So $\langle M, w \rangle \in A_{\mathrm{TM}}$ if and only if $\langle M' \rangle \in L_P$.

If instead $\emptyset \in P$, apply the argument to the complement property $P'$, the set of recognizable languages outside $P$. It omits $\emptyset$ and is nontrivial, so $L_{P'}$ is undecidable. Since $L_{P'}$ and $L_P$ are complementary among well-formed encodings, $L_P$ is undecidable too. $\square$

To apply Rice's theorem, you must check two conditions: the property depends only on the input and output behavior of the program, and it is nontrivial. These syntactic or resource properties fall outside its scope: "$M$ has at most ten states" and "$M$ halts on the empty input within 100 steps". Both are decidable. A property may also fall outside the theorem and still be undecidable, as with "$M$ enters state $q$ on input $w$".

For verification, the consequence is direct. Whether a program computes a given function, whether it refines a specification and whether it is correct on all inputs are all nontrivial semantic properties. An analyzer that terminates on every program therefore must err on some program, either by rejecting a correct one or by accepting an incorrect one. Static analyzers normally choose the first error, which yields false alarms. Bug finders choose the second, which yields missed bugs. Deductive verifiers keep soundness and require human annotations, and they may also fail to terminate.

### Post's correspondence problem

An instance of Post's correspondence problem (PCP) is a finite list of dominoes $(s_1, t_1), \dots, (s_k, t_k)$, where each $s_i$ and $t_i$ is a nonempty string over a finite alphabet. A solution is a sequence $i_1, \dots, i_m$ with $m \ge 1$ such that

$$
s_{i_1} s_{i_2} \cdots s_{i_m} = t_{i_1} t_{i_2} \cdots t_{i_m}.
$$

PCP has no reference to machines, which makes it a convenient source for reductions to logic. The [next stage of this chapter](../undecidability-of-logic-and-incompleteness/) reduces PCP to first-order validity.

Theorem (Post, 1946). PCP is undecidable, including over the alphabet $\{0, 1\}$.

Proof sketch. The proof has two reductions. Let MPCP be the variant in which the solution must begin with domino 1.

From $A_{\mathrm{TM}}$ to MPCP. Assume without loss of generality that $M$ never attempts to move left from the leftmost cell. Build dominoes that force the matching string to be an accepting computation history, written as `#c0#c1#...#`. The first domino is $(\#, \# q_0 w \#)$, which places the initial configuration on the bottom. The bottom is then one configuration ahead of the top, and adding dominoes to match it writes the next configuration on the bottom.

- For $\delta(q, a) = (r, b, R)$, add $(qa, br)$.
- For $\delta(q, a) = (r, b, L)$ and each $c \in \Gamma$, add $(cqa, rcb)$.
- For each $a \in \Gamma$, add $(a, a)$ to copy tape cells.
- Add $(\#, \#)$, and add $(\#, \sqcup \#)$ to extend the tape when the head reaches the right end.
- For each $a \in \Gamma$, add $(a q_{\mathrm{acc}}, q_{\mathrm{acc}})$ and $(q_{\mathrm{acc}} a, q_{\mathrm{acc}})$. These let the top catch up by erasing symbols after acceptance.
- Add $(q_{\mathrm{acc}} \# \#, \#)$ to finish the match.

The top can catch up with the bottom only after $q_{\mathrm{acc}}$ appears, so a match exists exactly when $M$ accepts $w$.

From MPCP to PCP. For a string $u = u_1 \cdots u_n$, write $\star u = \star u_1 \star u_2 \cdots \star u_n$ and $u \star = u_1 \star u_2 \star \cdots u_n \star$. Replace each domino $(s_i, t_i)$ with $(\star s_i, t_i \star)$, add $(\star s_1, \star t_1 \star)$, and add $(\star \diamond, \diamond)$. A match must start with the added first domino, since it is the only one whose two strings begin with the same symbol.

To obtain the binary alphabet, encode each of the finitely many symbols as a binary block of one fixed length. Both sides of a match are then sequences of blocks of that length, so two encoded strings are equal exactly when the original strings are equal. $\square$

### Counter machines

A two-counter machine has a finite program and two registers holding natural numbers. Its instructions increment a counter, decrement a counter if it is positive, and branch on whether a counter is zero.

Theorem (Minsky, 1961). The halting problem for two-counter machines with both counters initially zero is undecidable.

Proof sketch. Two stacks simulate a tape, with one stack for the cells to the left of the head and one for the cells to the right. A stack over a finite alphabet can be represented by a number in a suitable base, and pushing or popping becomes multiplication or division by the base. Four counters suffice to hold two stacks and a scratch value for these operations. The four values $a, b, c, d$ can be packed into a single number $2^a 3^b 5^c 7^d$, and a second counter serves as scratch space for multiplying or dividing that number by a small prime. $\square$

This theorem is the shortest route to undecidability in infinite-state verification. A program with two unbounded integer variables and zero tests is already out of reach of any complete procedure, and an [encoding with Horn clauses](../../../part-2-core-reasoning/08-model-checking/horn-clauses/) inherits the problem.

### The arithmetical hierarchy, briefly

Recognizable languages are those of the form $\{x : \exists y\, R(x, y)\}$ with $R$ decidable, where $y$ encodes a finite accepting computation. This class is called $\Sigma_1$. Its complement class $\Pi_1$ consists of languages of the form $\{x : \forall y\, R(x, y)\}$. Adding alternations gives the classes $\Sigma_n$ and $\Pi_n$, which form the arithmetical hierarchy. Decidable languages are exactly $\Sigma_1 \cap \Pi_1$.

The level tells you which kind of evidence can exist.

| Problem | Level | What this means for a tool |
|---|---|---|
| A program halts on a given input. | $\Sigma_1$-complete | A finite trace is a certificate for a yes-answer. |
| A program never violates an assertion on any input. | $\Pi_1$-complete | A finite trace is a certificate for a no-answer. |
| A first-order sentence is valid. | $\Sigma_1$-complete | A finite proof is a certificate for a yes-answer. |
| A program halts on every input. | $\Pi_2$-complete | Neither a yes-answer nor a no-answer has a general finite certificate. |
| Two programs compute the same partial function. | $\Pi_2$-complete | Neither a yes-answer nor a no-answer has a general finite certificate. |

Safety being $\Pi_1$ explains why testing can find bugs and cannot in general establish their absence. Universal termination being $\Pi_2$ explains why termination tools search for richer objects, such as ranking functions, that exist only for some terminating programs.

### What undecidability does and does not say

Undecidability is a statement about a uniform algorithm for an infinite class of instances. It has these consequences and limits.

- Any finite set of instances is decidable, since a table of answers is an algorithm.
- A specific program may be easy to verify, and most programs that people write have reasons for being correct that a tool can find.
- Restricting the class can restore decidability. Finite-state programs have decidable safety, because their configuration graph is finite. [Bounded model checking](../../../part-2-core-reasoning/08-model-checking/bounded-model-checking/) restricts the length of executions.
- Weakening the guarantee can restore termination. A tool may answer "safe", "unsafe" or "unknown", as an SMT solver does when it returns `unknown` on quantified nonlinear formulas.

## Worked examples

### Example 1: a full Turing machine trace

The following machine decides $\{0^n 1^n : n \ge 0\}$. It repeatedly marks a leftmost $0$ as $X$, moves right to mark the first $1$ as $Y$, and returns. When no $0$ remains, it checks that only $Y$ symbols remain.

| State | Read | Write | Move | Next state |
|---|---|---|---|---|
| $q_0$ | $0$ | $X$ | R | $q_1$ |
| $q_0$ | $Y$ | $Y$ | R | $q_3$ |
| $q_0$ | $\sqcup$ | $\sqcup$ | R | $q_{\mathrm{acc}}$ |
| $q_1$ | $0$ | $0$ | R | $q_1$ |
| $q_1$ | $Y$ | $Y$ | R | $q_1$ |
| $q_1$ | $1$ | $Y$ | L | $q_2$ |
| $q_2$ | $0$ | $0$ | L | $q_2$ |
| $q_2$ | $Y$ | $Y$ | L | $q_2$ |
| $q_2$ | $X$ | $X$ | R | $q_0$ |
| $q_3$ | $Y$ | $Y$ | R | $q_3$ |
| $q_3$ | $\sqcup$ | $\sqcup$ | R | $q_{\mathrm{acc}}$ |

Every pair not listed moves right, leaves the symbol unchanged and enters $q_{\mathrm{rej}}$.

The trace on input $0011$ takes 13 steps and accepts. The symbol `_` stands for a blank.

```
[q0]0011_
X[q1]011_
X0[q1]11_
X[q2]0Y1_
[q2]X0Y1_
X[q0]0Y1_
XX[q1]Y1_
XXY[q1]1_
XX[q2]YY_
X[q2]XYY_
XX[q0]YY_
XXY[q3]Y_
XXYY[q3]_
XXYY_[qacc]_
```

The trace on input $001$ takes 8 steps and rejects.

```
[q0]001_
X[q1]01_
X0[q1]1_
X[q2]0Y_
[q2]X0Y_
X[q0]0Y_
XX[q1]Y_
XXY[q1]_
XXY_[qrej]_
```

The machine halts on every input, because each pass through $q_1$ and $q_2$ marks a new $0$, and the other states only move right until a blank or a rejection. A script that simulated this table confirmed these traces and confirmed the correct answer on all binary strings of length at most 8.

### Example 2: assertion reachability

Let $\mathrm{VIOL}$ be the set of programs that have an input on which an `assert false` statement is executed. This example proves that $\mathrm{VIOL}$ is undecidable and recognizable.

Reduction from $\mathrm{HALT}$. Given $\langle M, w \rangle$, construct the program $P_{M,w}$.

```
P on any input:
    simulate M on w
    assert false
```

The construction only writes down text, so it is computable. It never runs $M$.

- If $M$ halts on $w$, the simulation ends and the assertion is executed, so $P_{M,w} \in \mathrm{VIOL}$.
- If $M$ does not halt on $w$, the simulation never ends and the assertion is never reached, so $P_{M,w} \notin \mathrm{VIOL}$.

So $\mathrm{HALT} \le_m \mathrm{VIOL}$, and $\mathrm{VIOL}$ is undecidable.

Recognizability. Dovetail over all pairs of an input and a step bound. Accept if some run reaches the assertion within its bound. Consequently, $\overline{\mathrm{VIOL}}$, the set of safe programs, is not recognizable: if it were, then $\mathrm{VIOL}$ would be decidable. No sound and complete proof system with mechanically checkable proofs can cover all safe programs in this language. This is the computational reason why every program logic with effectively checkable proofs must be incomplete for full safety, unless it has oracles for the assertion language.

Note that Rice's theorem would not apply as stated to $\mathrm{VIOL}$ on machines, since "an assertion statement is executed" refers to a statement in the text. The direct reduction is what you need.

### Example 3: program equivalence has no one-sided certificate

Let $\mathrm{EQ}_{\mathrm{TM}} = \{\langle M_1, M_2 \rangle : L(M_1) = L(M_2)\}$. Translation validation and regression verification face this problem if stated for unrestricted programs. This example proves that it is neither recognizable nor co-recognizable.

Let $M_{\mathrm{all}}$ be a machine that accepts every input, and let $M_{\mathrm{none}}$ be a machine that rejects every input. Given $\langle M, w \rangle$, let $N_{M,w}$ be the machine that, on any input, ignores it, simulates $M$ on $w$, and accepts if $M$ accepts. Thus

$$
L(N_{M,w}) = \Sigma^* \text{ if } M \text{ accepts } w, \qquad L(N_{M,w}) = \emptyset \text{ otherwise.}
$$

First reduction. Map $\langle M, w \rangle$ to $\langle M_{\mathrm{all}}, N_{M,w} \rangle$. The two languages are equal if and only if $M$ accepts $w$, so $A_{\mathrm{TM}} \le_m \mathrm{EQ}_{\mathrm{TM}}$. Taking complements gives $\overline{A_{\mathrm{TM}}} \le_m \overline{\mathrm{EQ}_{\mathrm{TM}}}$. Since $\overline{A_{\mathrm{TM}}}$ is not recognizable, $\overline{\mathrm{EQ}_{\mathrm{TM}}}$ is not recognizable, so $\mathrm{EQ}_{\mathrm{TM}}$ is not co-recognizable.

Second reduction. Map $\langle M, w \rangle$ to $\langle M_{\mathrm{none}}, N_{M,w} \rangle$. The two languages are equal if and only if $M$ does not accept $w$, so $\overline{A_{\mathrm{TM}}} \le_m \mathrm{EQ}_{\mathrm{TM}}$. Since $\overline{A_{\mathrm{TM}}}$ is not recognizable, $\mathrm{EQ}_{\mathrm{TM}}$ is not recognizable.

For a tool, this means that a differing input can be checked if you can bound the running time, and that the full problem has no finite certificate in either direction. Practical equivalence checkers therefore restrict the problem, for example to loop-free code of fixed width, which is [decidable and much cheaper](../reductions-and-np-completeness/).

### Example 4: a search for a PCP solution

Consider the dominoes $d_1 = (1, 101)$, $d_2 = (10, 00)$ and $d_3 = (011, 11)$. Each row shows the top string, the bottom string and the unmatched part. At each step, a domino is usable only if the two new strings remain prefixes of one another.

The first domino must be $d_1$, since $d_2$ and $d_3$ disagree in their first symbol.

```
sequence       top          bottom       unmatched
d1             1            101          bottom has 01
d1 d3          1011         10111        bottom has 1
d1 d3 d2       101110       1011100      bottom has 0
d1 d3 d2 d3    101110011    101110011    none
```

Two choices require explanation. After $d_1$, the unmatched part $01$ must be matched by a top string compatible with it, and only $011$ qualifies. After $d_1 d_3$, both $d_1$ and $d_2$ have tops compatible with the unmatched $1$, and the table follows $d_2$. The sequence $d_1, d_3, d_2, d_3$ is a solution, with common string $101110011$. A breadth-first script confirmed this solution.

The search branches and has no general bound on the required length. That missing bound is exactly what undecidability expresses, since a computable bound on the length of the shortest solution would give a decision procedure.

## Common mistakes

- Reducing in the wrong direction. To prove $B$ undecidable, you must transform instances of a known undecidable problem into instances of $B$, so that a decider for $B$ would solve the known problem.
- Running the input machine inside the reduction. The reduction must always terminate, so it may only write down a machine that would simulate the input machine when later executed.
- Applying Rice's theorem to syntactic or resource properties. The theorem covers only properties of the recognized language, so a question about state counts or step bounds needs separate analysis.
- Concluding that a property is decidable because Rice's theorem does not apply. "$M$ enters state $q$ on input $w$" is outside the theorem and is still undecidable.
- Treating undecidable as meaning that no instance can be solved. Undecidability only excludes a single algorithm that is correct on all instances and always terminates.
- Treating recognizable as meaning decidable. A recognizer may loop on no-instances, and a first-order prover that has not finished yet tells you nothing about the answer.
- Believing that every finite-state abstraction preserves the answer. Safety of finite-state systems is decidable, and a finite abstraction of an infinite-state program is only an over-approximation or under-approximation unless proved exact.
- Assuming that all reasonable reduction notions are interchangeable. Turing reductions do not transfer recognizability, so proofs of non-recognizability need mapping reductions.

## Exercises

### Exercise 1

State the difference between a decider and a recognizer, and give a language that has a recognizer and no decider.

<details><summary>Solution</summary>

A recognizer must accept exactly the strings of its language, and it may reject or loop on other strings. A decider recognizes its language and also halts on every input. The language $A_{\mathrm{TM}}$ has a recognizer, namely the universal machine, and it has no decider by Turing's theorem.

</details>

### Exercise 2

Trace the machine of Example 1 on input $010$. Give the final answer and the number of steps.

<details><summary>Solution</summary>

```
[q0]010_
X[q1]10_
[q2]XY0_
X[q0]Y0_
XY[q3]0_
XY0[qrej]_
```

The machine rejects after 5 steps. In the second-to-last configuration, state $q_3$ reads $0$, and that pair has no listed transition, so it moves right and enters $q_{\mathrm{rej}}$.

</details>

### Exercise 3

Prove that the decidable languages are closed under complement. Prove that the recognizable languages are closed under union and are not closed under complement.

<details><summary>Solution</summary>

Complement of decidable. Swap the accept and reject answers of a decider. The new machine still halts on every input and recognizes the complement.

Union of recognizable. Given recognizers $M_1$ and $M_2$, on input $x$ run them in alternation, one step each, and accept if either accepts. If $x$ belongs to the union, then one of them accepts in finite time, and the alternation reaches that step. If $x$ does not belong, neither accepts, so the new machine does not accept.

Complement. $A_{\mathrm{TM}}$ is recognizable, and $\overline{A_{\mathrm{TM}}}$ is not recognizable, so the class is not closed under complement.

</details>

### Exercise 4

For each language, state whether Rice's theorem applies, and whether the language is decidable.

1. $\{\langle M \rangle : L(M) = \emptyset\}$.
2. $\{\langle M \rangle : M \text{ has at least 10 states}\}$.
3. $\{\langle M \rangle : M \text{ halts on } \varepsilon \text{ within 100 steps}\}$.
4. $\{\langle M \rangle : L(M) \text{ is finite}\}$.
5. $\{\langle M, w, q \rangle : M \text{ enters state } q \text{ on input } w\}$.

<details><summary>Solution</summary>

1. Rice's theorem applies, since the property depends on $L(M)$ and is nontrivial. The language is undecidable.
2. Rice's theorem does not apply, since two machines with the same language can have different state counts. The language is decidable by reading the description.
3. Rice's theorem does not apply, since it is a resource property. The language is decidable by simulating 100 steps.
4. Rice's theorem applies, since finite and infinite recognizable languages both exist. The language is undecidable.
5. Rice's theorem does not apply, since the question depends on the machine's internal states. The language is undecidable, because the map from $\langle M, w \rangle$ to $\langle M, w, q_{\mathrm{acc}} \rangle$ is a reduction from $A_{\mathrm{TM}}$.

</details>

### Exercise 5

Prove by a mapping reduction that $\{\langle M \rangle : M \text{ accepts } \varepsilon\}$ is undecidable, without using Rice's theorem.

<details><summary>Solution</summary>

Map $\langle M, w \rangle$ to $\langle M_w \rangle$, where $M_w$ erases its input, writes $w$ on the tape, and runs $M$. This is computable, since it writes a fixed preamble that contains $w$ and then appends the transition table of $M$. For every input, including $\varepsilon$, $M_w$ behaves as $M$ does on $w$. So $M_w$ accepts $\varepsilon$ if and only if $M$ accepts $w$, and this is a mapping reduction from $A_{\mathrm{TM}}$.

</details>

### Exercise 6

Prove that $L$ is recognizable if and only if $L \le_m A_{\mathrm{TM}}$.

<details><summary>Solution</summary>

Suppose $L \le_m A_{\mathrm{TM}}$. Since $A_{\mathrm{TM}}$ is recognizable, the lemma on reductions shows that $L$ is recognizable.

Suppose $L$ is recognized by $M$. The map $x \mapsto \langle M, x \rangle$ is computable, and $x \in L$ if and only if $M$ accepts $x$ if and only if $\langle M, x \rangle \in A_{\mathrm{TM}}$. So it is a mapping reduction.

</details>

### Exercise 7

Show that the PCP instance $(1, 10), (10, 01)$ has no solution.

<details><summary>Solution</summary>

A solution cannot begin with $(10, 01)$, since the first symbols $1$ and $0$ differ. So it begins with $(1, 10)$, which leaves the top as $1$ and the bottom as $10$. The bottom has an unmatched $0$, so the next domino must have a top that begins with $0$. Both dominoes have tops that begin with $1$. Hence the sequence cannot be continued, and the single-domino sequence is not a match since $1 \ne 10$. There is no solution.

</details>

### Exercise 8

Prove that $\mathrm{HALT}$ is recognizable and that $\overline{\mathrm{HALT}}$ is not recognizable. State what this says about a tool that tries to certify nontermination of arbitrary programs.

<details><summary>Solution</summary>

Simulate $M$ on $w$ and accept when it halts. This recognizes $\mathrm{HALT}$. If $\overline{\mathrm{HALT}}$ were recognizable, then $\mathrm{HALT}$ and its complement would both be recognizable, and $\mathrm{HALT}$ would be decidable, which contradicts the theorem.

A tool that outputs mechanically checkable certificates of nontermination cannot be complete. If every nonterminating run had a certificate that a machine could check, then enumerating and checking certificates would recognize $\overline{\mathrm{HALT}}$. Such a tool must look for restricted forms of evidence, for example a lasso in a finite-state abstraction or a recurrent set of a chosen shape, and it must answer "unknown" on other programs.

</details>

### Exercise 9

Let $\mathrm{TOTAL} = \{\langle M \rangle : M \text{ halts on every input}\}$. Prove that $\mathrm{TOTAL}$ is neither recognizable nor co-recognizable.

<details><summary>Solution</summary>

Not co-recognizable. Reduce $\mathrm{HALT}$ to $\mathrm{TOTAL}$ by mapping $\langle M, w \rangle$ to a machine that ignores its input and simulates $M$ on $w$. It halts on every input if and only if $M$ halts on $w$. If $\mathrm{TOTAL}$ were co-recognizable, then $\mathrm{HALT}$ would be co-recognizable as well, since $\overline{\mathrm{HALT}} \le_m \overline{\mathrm{TOTAL}}$. Then $\mathrm{HALT}$ would be decidable, which is false.

Not recognizable. Reduce $\overline{\mathrm{HALT}}$ to $\mathrm{TOTAL}$ by mapping $\langle M, w \rangle$ to the machine $K_{M,w}$.

```
K on input x:
    simulate M on w for |x| steps
    if M has halted within those steps, loop forever
    otherwise, accept
```

If $M$ does not halt on $w$, then $K_{M,w}$ accepts every input, so it is total. If $M$ halts on $w$ after $s$ steps, then $K_{M,w}$ loops on every input of length at least $s$, so it is not total. Since $\overline{\mathrm{HALT}}$ is not recognizable, $\mathrm{TOTAL}$ is not recognizable.

</details>

### Exercise 10

A finite-state program has finitely many variables over finite domains and no heap or recursion. Prove that its assertion reachability problem is decidable. Explain why this does not contradict Rice's theorem, and why it gives only limited comfort in practice.

<details><summary>Solution</summary>

Let $N$ be the number of configurations, which is finite and computable from the program text: control locations times the product of the variable domain sizes. Build the graph of configurations with an edge for each possible step. Search from every initial configuration for a configuration at an assertion failure. The search visits each configuration at most once, so it terminates, and it is correct since each execution is a path in this graph.

There is no contradiction, because Rice's theorem concerns all Turing machines. Finite-state programs form a proper subclass of them, and that subclass does not even recognize all recognizable languages.

The comfort is limited because $N$ is exponential in the number of bits. A program with 64 bits of state already has $2^{64}$ configurations, and the [space and hierarchy topic](../space-and-the-polynomial-hierarchy/) shows that the problem is PSPACE-complete when the program is the input.

</details>

### Exercise 11

Prove that no algorithm decides, given a Turing machine $M$, whether $M$ is a correct SAT solver. A correct SAT solver is a machine that halts on all inputs, accepts encodings of satisfiable formulas, and rejects every other string.

<details><summary>Solution</summary>

Rice's theorem does not immediately apply as stated, since the requirement that $M$ halts on all inputs depends on more than $L(M)$. Use a direct reduction from $\overline{\mathrm{HALT}}$ instead. Fix a correct SAT solver $S$, which exists since SAT is decidable by truth tables. Map $\langle N, w \rangle$ to the machine $S_{N,w}$.

```
S' on input x:
    simulate N on w for |x| steps
    if N has halted within those steps, reject x if x encodes a satisfiable formula, and accept otherwise
    otherwise, return the answer of S on x
```

If $N$ does not halt on $w$, then $S_{N,w}$ behaves exactly as $S$, so it is correct. If $N$ halts on $w$ after $s$ steps, then $S_{N,w}$ gives the wrong answer on every input of length at least $s$, so it is incorrect. Hence $\overline{\mathrm{HALT}}$ reduces to the problem, so the problem is undecidable, and in fact not recognizable.

This does not prevent you from verifying a specific solver, and it does not prevent checking individual runs. A proof checker that verifies a [DRAT certificate](../../../part-2-core-reasoning/04-sat/proofs-and-certificates/) validates one answer at a time. That is one reason why certificates are used in practice.

</details>

### Exercise 12

Consider a program analyzer $A$ that terminates on every program in a Turing-complete language and answers either "safe" or "unknown". It is sound, meaning that "safe" is returned only for programs that do not violate assertions. Prove that there is a safe program on which $A$ answers "unknown". Then design a bounded variant of the problem for which a sound, complete and terminating analyzer exists, and state the guarantee it gives.

<details><summary>Solution</summary>

Suppose that $A$ answers "safe" on every safe program. Together with soundness, this means $A$ answers "safe" exactly on the safe programs. Since $A$ terminates, it decides safety, which contradicts Example 2. So some safe program receives "unknown".

Bounded variant. Take as input a program, an initial state with a finite input domain, an integer width $w$ and a step bound $k$ given in unary. Ask whether an assertion can fail within $k$ steps when all variables are limited to $w$ bits. The set of runs of length at most $k$ is finite, and each can be enumerated or encoded in a propositional formula, so the question is decidable. The analyzer is sound and complete for that bounded question. The guarantee is that no violation exists within the bound. It gives no information about longer runs or wider values, unless a separate argument, such as a completeness threshold for finite-state systems or an inductive invariant, extends it.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define Turing machines, configurations, deciders and recognizers, and trace a machine by hand.
- Prove that a language is decidable exactly when it and its complement are recognizable.
- Prove the undecidability of $A_{\mathrm{TM}}$ by diagonalization.
- Define mapping reductions, state their transfer properties, and construct one in the correct direction.
- State and prove Rice's theorem, and decide whether it applies to a given property.
- Prove that a program problem such as assertion reachability, equivalence or totality is undecidable.
- Describe the construction that reduces machine acceptance to PCP.
- Place a verification problem in $\Sigma_1$, $\Pi_1$ or $\Pi_2$, and state what certificates that level allows.

## Materials

- Sipser, Introduction to the Theory of Computation. Read it for Turing machines, the diagonal argument, reductions and the full construction for Post's correspondence problem.
- Turing, On Computable Numbers, with an Application to the Entscheidungsproblem, Proceedings of the London Mathematical Society, 1936 to 1937. Read it for the original motivation of the machine model and the link to first-order logic.
- Rice, Classes of Recursively Enumerable Sets and Their Decision Problems, Transactions of the American Mathematical Society, 1953. Read it for the original statement of Rice's theorem.
- Post, A Variant of a Recursively Unsolvable Problem, Bulletin of the American Mathematical Society, 1946. Read it for the original correspondence problem.
- Minsky, Computation: Finite and Infinite Machines, 1967. Read it for counter machines and their universality.
