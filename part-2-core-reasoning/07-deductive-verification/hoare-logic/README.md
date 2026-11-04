# Hoare Logic

Part 2, Chapter 7: Deductive Verification.

## Objective

Prove partial and total correctness of small programs using Hoare logic.

## Why this matters

Every deductive verifier, including Dafny, Boogie, Viper and the Rust verifiers, is an engineered form of the proof system in this topic. When a verifier rejects a program, the failed obligation corresponds to a premise of a Hoare rule, usually the preservation premise of the while rule. You can only diagnose such a failure if you know what the premise says. The later topics in this chapter compute Hoare proofs mechanically (weakest preconditions and verification conditions) or extend the logic to the heap and to concurrency (separation logic). An applied scientist working on verification reads and writes specifications in this form daily, and has to judge whether a specification says what the customer needs.

## Prerequisites

- [Operational Semantics](../../../part-1-foundations/03-semantics-and-types/operational-semantics/) for big-step execution.
- [Axiomatic Semantics](../../../part-1-foundations/03-semantics-and-types/axiomatic-semantics/) for the idea of relating a logic to a semantics.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for rule induction and well-founded induction.
- [First-Order Theories](../../../part-1-foundations/01-mathematical-logic/first-order-theories/) for the assertion language.
- [Undecidability of Logic and Incompleteness](../../../part-1-foundations/02-decidability-and-complexity/undecidability-of-logic-and-incompleteness/) for the limits of completeness.

## Lesson

### The programming language

The language is the usual small imperative language, called IMP here. Expressions are integer terms $e$ built from variables, constants, $+$, $-$ and $\times$. Boolean expressions $b$ are built from comparisons of integer terms with $\land$, $\lor$ and $\neg$. Expression evaluation is total and has no side effects.

```
c ::= skip | x := e | c ; c | if b then c else c | while b do c
```

A state $\sigma$ maps every variable to an integer. Write $[\![e]\!]\sigma$ for the value of $e$ in $\sigma$, and $\sigma[x \mapsto v]$ for the state that agrees with $\sigma$ except that $x$ maps to $v$. The big-step relation $\langle c, \sigma \rangle \Downarrow \sigma'$ is the least relation closed under these rules.

$$\frac{}{\langle \mathtt{skip}, \sigma\rangle \Downarrow \sigma} \qquad \frac{}{\langle x := e, \sigma\rangle \Downarrow \sigma[x \mapsto [\![e]\!]\sigma]} \qquad \frac{\langle c_1,\sigma\rangle \Downarrow \sigma'' \quad \langle c_2,\sigma''\rangle \Downarrow \sigma'}{\langle c_1 ; c_2,\sigma\rangle \Downarrow \sigma'}$$

$$\frac{\sigma \models b \quad \langle c_1,\sigma\rangle \Downarrow \sigma'}{\langle \mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2,\sigma\rangle \Downarrow \sigma'} \qquad \frac{\sigma \models \neg b \quad \langle c_2,\sigma\rangle \Downarrow \sigma'}{\langle \mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2,\sigma\rangle \Downarrow \sigma'}$$

$$\frac{\sigma \models \neg b}{\langle \mathtt{while}\ b\ \mathtt{do}\ c,\sigma\rangle \Downarrow \sigma} \qquad \frac{\sigma \models b \quad \langle c,\sigma\rangle \Downarrow \sigma'' \quad \langle \mathtt{while}\ b\ \mathtt{do}\ c,\sigma''\rangle \Downarrow \sigma'}{\langle \mathtt{while}\ b\ \mathtt{do}\ c,\sigma\rangle \Downarrow \sigma'}$$

IMP is deterministic: for given $c$ and $\sigma$ there is at most one $\sigma'$. Nontermination appears as the absence of any $\sigma'$.

### Assertions and logical variables

Assertions $P, Q, I$ are first-order formulas over the integers. They may mention program variables and also logical variables, which no program assigns. Logical variables record initial values and connect a precondition to a postcondition, as in $\{x = A \land y = B\}\ \ldots\ \{x = B \land y = A\}$. They are also called ghost or auxiliary variables, although in later topics ghost variables can be assigned by ghost code.

### Triples

A partial correctness triple says that terminating runs from $P$ end in $Q$.

$$\models \{P\}\ c\ \{Q\} \quad\text{iff}\quad \text{for all } \sigma, \sigma': \text{ if } \sigma \models P \text{ and } \langle c,\sigma\rangle \Downarrow \sigma' \text{ then } \sigma' \models Q.$$

A total correctness triple adds termination.

$$\models [P]\ c\ [Q] \quad\text{iff}\quad \text{for all } \sigma \models P \text{ there is } \sigma' \text{ with } \langle c,\sigma\rangle \Downarrow \sigma' \text{ and } \sigma' \models Q.$$

The split exists for a practical reason. Termination arguments and invariance arguments use different ideas, and they compose better when kept apart. The approach goes back to Floyd's 1967 method of attaching assertions to flowchart edges, with a variant measure for termination. Hoare's 1969 paper recast it as a logic of triples over program text, and it treats partial correctness only.

### The rules of partial correctness

$$\frac{}{\{P\}\ \mathtt{skip}\ \{P\}}\ \text{(skip)} \qquad \frac{}{\{Q[e/x]\}\ x := e\ \{Q\}}\ \text{(assign)} \qquad \frac{\{P\}\ c_1\ \{R\} \quad \{R\}\ c_2\ \{Q\}}{\{P\}\ c_1 ; c_2\ \{Q\}}\ \text{(seq)}$$

$$\frac{\{P \land b\}\ c_1\ \{Q\} \quad \{P \land \neg b\}\ c_2\ \{Q\}}{\{P\}\ \mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\ \{Q\}}\ \text{(if)} \qquad \frac{\{I \land b\}\ c\ \{I\}}{\{I\}\ \mathtt{while}\ b\ \mathtt{do}\ c\ \{I \land \neg b\}}\ \text{(while)}$$

$$\frac{\models P \to P' \quad \{P'\}\ c\ \{Q'\} \quad \models Q' \to Q}{\{P\}\ c\ \{Q\}}\ \text{(consequence)}$$

Write $\vdash \{P\}\ c\ \{Q\}$ when the triple is derivable. The consequence rule is the interface between program reasoning and mathematics. Its side conditions are validity questions in the assertion theory, and these are what a solver eventually receives.

The assignment axiom looks backwards at first. Its justification is the substitution lemma.

Lemma (substitution). $\sigma \models Q[e/x]$ if and only if $\sigma[x \mapsto [\![e]\!]\sigma] \models Q$.

The proof is by induction on $Q$, with capture-avoiding substitution, after first proving $[\![t[e/x]]\!]\sigma = [\![t]\!](\sigma[x \mapsto [\![e]\!]\sigma])$ for terms $t$ by induction on $t$. The lemma says that $Q[e/x]$ describes exactly the states in which the assignment will make $Q$ true, which is why the axiom is stated in the backward direction. A forward form needs an existential over the overwritten value, as Floyd's rule shows:

$$\{P\}\ x := e\ \{\exists x_0.\ P[x_0/x] \land x = e[x_0/x]\}.$$

### Soundness

Theorem (soundness). If $\vdash \{P\}\ c\ \{Q\}$ then $\models \{P\}\ c\ \{Q\}$.

Proof. The proof is by induction on the derivation.

- Case skip. The only run leaves $\sigma$ unchanged.
- Case assign. Suppose $\sigma \models Q[e/x]$. The only final state is $\sigma[x \mapsto [\![e]\!]\sigma]$, which satisfies $Q$ by the substitution lemma.
- Case seq. A run of $c_1;c_2$ passes through some $\sigma''$. The first induction hypothesis gives $\sigma'' \models R$, and the second gives $\sigma' \models Q$.
- Case if. The run takes the branch selected by $b$, and that branch's premise applies because $\sigma \models P \land b$ or $\sigma \models P \land \neg b$.
- Case consequence. If $\sigma \models P$ then $\sigma \models P'$. The induction hypothesis gives $\sigma' \models Q'$, hence $\sigma' \models Q$.
- Case while. The induction hypothesis says $\models \{I \land b\}\ c\ \{I\}$. It remains to show that if $\langle \mathtt{while}\ b\ \mathtt{do}\ c, \sigma\rangle \Downarrow \sigma'$ and $\sigma \models I$ then $\sigma' \models I \land \neg b$. Use a nested induction on the big-step derivation. If the last rule is the false-guard rule, then $\sigma' = \sigma$ and $\sigma \models \neg b$. If it is the true-guard rule, then $\sigma \models I \land b$ and $\langle c,\sigma\rangle \Downarrow \sigma''$, so $\sigma'' \models I$ by the outer hypothesis. The nested hypothesis applied to the shorter derivation from $\sigma''$ gives the claim. $\square$

The nested induction is on the run, and it would have nothing to work on if the loop diverged. This is exactly why the while rule says nothing about termination.

### Derived forms and proof outlines

Combining while with consequence gives the form used in practice. To prove $\{P\}\ \mathtt{while}\ b\ \mathtt{do}\ c\ \{Q\}$, choose $I$ and establish three facts:

1. Initiation: $\models P \to I$.
2. Preservation: $\vdash \{I \land b\}\ c\ \{I\}$.
3. Exit: $\models I \land \neg b \to Q$.

A proof outline writes the program with assertions between commands. It is a compact notation for a derivation in which adjacent assertions are linked by consequence. In this chapter, outlines read from top to bottom, and two consecutive assertions mean that the first implies the second.

### Total correctness

For total correctness, replace the while rule by the following rule, and keep the other rules with square brackets.

$$\frac{[I \land b \land t = n]\ c\ [I \land t < n] \qquad \models I \land b \to t \geq 0}{[I]\ \mathtt{while}\ b\ \mathtt{do}\ c\ [I \land \neg b]}\ \text{(while-total)}$$

Here $t$ is an integer term called the variant or ranking function, and $n$ is a logical variable that does not occur in $I$, $b$, $c$ or $t$.

Theorem. The rule while-total is sound.

Proof. Assume the premises are valid. By strong induction on $m \in \mathbb{N}$, show the following claim: every $\sigma \models I$ such that either $\sigma \models \neg b$ or $[\![t]\!]\sigma = m$ has a terminating run of the loop ending in $I \land \neg b$. If $\sigma \models \neg b$, the loop stops at once. Otherwise $\sigma \models I \land b$, so $[\![t]\!]\sigma \geq 0$ and $[\![t]\!]\sigma = m$. Since $n$ does not occur in $I, b, c, t$, we may assume $\sigma(n) = m$ without changing the run on the other variables. The first premise gives a run of $c$ to some $\sigma''$ with $\sigma'' \models I$ and $[\![t]\!]\sigma'' < m$. If $\sigma'' \models \neg b$ the loop stops. Otherwise $[\![t]\!]\sigma'' \geq 0$ by the second premise, so the induction hypothesis applies to the natural number $[\![t]\!]\sigma''$. Every $\sigma \models I$ falls under the claim, either because $b$ is false or by taking $m = [\![t]\!]\sigma$. $\square$

Termination is treated in more depth, with well-founded orders and lexicographic measures, in [Loop Invariants](../loop-invariants/).

### Structural rules

These rules are admissible or derivable for IMP, and they matter once specifications are reused.

$$\frac{\{P_1\}\ c\ \{Q_1\} \quad \{P_2\}\ c\ \{Q_2\}}{\{P_1 \land P_2\}\ c\ \{Q_1 \land Q_2\}}\ \text{(conjunction)} \qquad \frac{\{P_1\}\ c\ \{Q_1\} \quad \{P_2\}\ c\ \{Q_2\}}{\{P_1 \lor P_2\}\ c\ \{Q_1 \lor Q_2\}}\ \text{(disjunction)}$$

$$\frac{\{P\}\ c\ \{Q\}}{\{\exists y.\ P\}\ c\ \{\exists y.\ Q\}}\ \text{(}y \text{ not in } c\text{)} \qquad \frac{\{P\}\ c\ \{Q\}}{\{P \land R\}\ c\ \{Q \land R\}}\ \text{(invariance: } c \text{ assigns no free variable of } R\text{)}$$

The invariance rule, also called the rule of constancy, is what makes it possible to reason about part of the state and keep facts about the rest. On the heap it fails, and its repair is the frame rule of [Separation Logic](../separation-logic/).

### Completeness and its limits

Full completeness is impossible for any effective proof system when assertions are interpreted in the integers.

Theorem. There is no sound and complete proof system for partial correctness over the standard integers whose set of derivable triples is recursively enumerable.

Proof. The triple $\{\top\}\ c\ \{\bot\}$ is valid if and only if $c$ diverges on every initial state. IMP is Turing-complete, and the set of programs that diverge on every input is not recursively enumerable, since its complement is recursively enumerable and undecidable. A sound and complete effective system would enumerate this set. $\square$

The source of the incompleteness is the assertion theory, whose valid formulas are not recursively enumerable by Gödel's first incompleteness theorem. Cook's 1978 theorem separates this source from the program rules. Say that the assertion language is expressive for IMP if for every $c$ and $Q$ there is an assertion that defines the weakest liberal precondition of $c$ and $Q$.

Theorem (Cook, relative completeness). If the assertion language is expressive, and all valid assertions are available as axioms for the consequence rule, then $\models \{P\}\ c\ \{Q\}$ implies $\vdash \{P\}\ c\ \{Q\}$.

First-order arithmetic is expressive for IMP, because Gödel's $\beta$ function can encode finite execution sequences. The proof of the theorem appears in [Weakest Preconditions](../weakest-preconditions/). The theorem says that the program rules lose nothing, and all the difficulty is in the assertion logic. It does not extend to every language: Clarke showed in 1979 that certain combinations of features, such as recursive procedures with procedure parameters, static scope and global variables, admit no sound and relatively complete Hoare system in this sense.

### Arrays and aliasing

The assignment axiom relies on the fact that distinct variable names denote distinct locations. Applying it to $a[i] := e$ by treating $a[i]$ as a name is unsound, since $\{a[j] = 1\}\ a[i] := 2\ \{a[j] = 1\}$ would follow by syntactic substitution and it is false when $i = j$. The standard repair treats the whole array as a variable holding a function, so that the command becomes $a := \mathit{store}(a, i, e)$ and the axiom gives

$$\{Q[\mathit{store}(a,i,e)/a]\}\ a[i] := e\ \{Q\}.$$

Reasoning then uses the read-over-write laws of [the theory of arrays](../../05-smt/arrays/). This works, but pointer programs written this way produce heavy case analysis on aliasing, and that cost motivates separation logic.

## Worked examples

### Example 1: a conditional, as a full derivation

Prove $\{\top\}\ \mathtt{if}\ x < 0\ \mathtt{then}\ y := -x\ \mathtt{else}\ y := x\ \{Q\}$ where $Q \equiv y \geq 0 \land (y = x \lor y = -x)$.

```
1. { -x ≥ 0 ∧ (-x = x ∨ -x = -x) }  y := -x  { Q }          assign
2. ⊨ ⊤ ∧ x < 0 → -x ≥ 0 ∧ (-x = x ∨ -x = -x)                arithmetic
3. { ⊤ ∧ x < 0 }  y := -x  { Q }                            consequence 2, 1
4. { x ≥ 0 ∧ (x = x ∨ x = -x) }  y := x  { Q }              assign
5. ⊨ ⊤ ∧ ¬(x < 0) → x ≥ 0 ∧ (x = x ∨ x = -x)                arithmetic
6. { ⊤ ∧ ¬(x < 0) }  y := x  { Q }                          consequence 5, 4
7. { ⊤ }  if x < 0 then y := -x else y := x  { Q }          if 3, 6
```

### Example 2: integer division, partial correctness

This is the program Hoare used in his 1969 paper, where the proof has precondition $\top$ and postcondition $\neg(y \leq r) \land x = r + y \times q$. Here the goal is stronger.

```
{ x ≥ 0 }
q := 0 ; r := x ;
while y ≤ r do ( r := r - y ; q := q + 1 )
{ x = q·y + r ∧ 0 ≤ r ∧ r < y }
```

The postcondition suggests the invariant, by dropping the conjunct $r < y$, which the exit condition will supply: $I \equiv x = q \cdot y + r \land r \geq 0$.

```
 1. { x = (q+1)·y + r ∧ r ≥ 0 }  q := q + 1  { I }                     assign
 2. { x = (q+1)·y + (r-y) ∧ r-y ≥ 0 }  r := r - y
    { x = (q+1)·y + r ∧ r ≥ 0 }                                        assign
 3. { x = (q+1)·y + (r-y) ∧ r-y ≥ 0 }  r := r - y ; q := q + 1  { I }  seq 2, 1
 4. ⊨ I ∧ y ≤ r → x = (q+1)·y + (r-y) ∧ r-y ≥ 0                        arithmetic
 5. { I ∧ y ≤ r }  r := r - y ; q := q + 1  { I }                      consequence 4, 3
 6. { I }  while y ≤ r do (...)  { I ∧ ¬(y ≤ r) }                      while 5
 7. { x = q·y + x ∧ x ≥ 0 }  r := x  { I }                             assign
 8. { x = 0·y + x ∧ x ≥ 0 }  q := 0  { x = q·y + x ∧ x ≥ 0 }           assign
 9. { x = 0·y + x ∧ x ≥ 0 }  q := 0 ; r := x  { I }                    seq 8, 7
10. ⊨ x ≥ 0 → x = 0·y + x ∧ x ≥ 0                                      arithmetic
11. ⊨ I ∧ ¬(y ≤ r) → x = q·y + r ∧ 0 ≤ r ∧ r < y                       arithmetic
12. { x ≥ 0 }  whole program  { x = q·y + r ∧ 0 ≤ r ∧ r < y }          seq 9, 6 and consequence 10, 11
```

Line 4 is the only step with content. Its arithmetic is $(q+1)y + (r - y) = qy + r = x$ and $r - y \geq 0$ from $y \leq r$.

The precondition does not mention $y$. When $y \leq 0$ the guard stays true because $r \geq 0 \geq y$, so the loop diverges and the triple holds vacuously. Partial correctness permits this, and the total correctness proof below has to rule it out.

The same proof as an outline is shorter:

```
{ x ≥ 0 }
{ x = 0·y + x ∧ x ≥ 0 }
q := 0 ;
{ x = q·y + x ∧ x ≥ 0 }
r := x ;
{ I }
while y ≤ r do
    { I ∧ y ≤ r }
    { x = (q+1)·y + (r-y) ∧ r-y ≥ 0 }
    r := r - y ;
    { x = (q+1)·y + r ∧ r ≥ 0 }
    q := q + 1
    { I }
{ I ∧ ¬(y ≤ r) }
{ x = q·y + r ∧ 0 ≤ r ∧ r < y }
```

### Example 3: integer division, total correctness

Strengthen the precondition to $x \geq 0 \land y > 0$, let $I' \equiv x = q \cdot y + r \land r \geq 0 \land y > 0$, and take the variant $t \equiv r$. The new obligations are as follows.

The bound premise is $I' \land y \leq r \to r \geq 0$, which is immediate.

For the decrease premise, compute backward from $I' \land r < n$ through the body:

```
[ I' ∧ y ≤ r ∧ r = n ]
[ x = (q+1)·y + (r-y) ∧ r-y ≥ 0 ∧ y > 0 ∧ r-y < n ]
r := r - y ;
[ x = (q+1)·y + r ∧ r ≥ 0 ∧ y > 0 ∧ r < n ]
q := q + 1
[ I' ∧ r < n ]
```

The first implication needs $r - y < n$. Since $n = r$ this is $r - y < r$, which holds exactly because $y > 0$. Initiation gives $I'$ from the precondition as in Example 2, with the extra conjunct $y > 0$ carried by the invariance rule since neither $q := 0$ nor $r := x$ assigns $y$. The exit implication is unchanged.

The verification conditions of Examples 1 to 3 were checked with an SMT solver over integer arithmetic, and all were reported valid.

## Common mistakes

1. Reading $\{P\}\ c\ \{Q\}$ as a claim about termination. The triple $\{\top\}\ \mathtt{while}\ \top\ \mathtt{do}\ \mathtt{skip}\ \{\bot\}$ is valid, because there are no terminating runs to check.
2. Applying the assignment axiom forward by writing $\{P\}\ x := e\ \{P[e/x]\}$. For $\{x = 0\}\ x := 1\ \{1 = 0\}$ this gives a false triple. Use the backward axiom, or Floyd's rule with an existential.
3. Using an invariant that is true of all runs but cannot be proved preserved in isolation. The premise quantifies over every state satisfying $I \land b$, including unreachable ones, so $I$ has to carry all the facts that preservation needs.
4. Omitting the bound premise of while-total. With $I \equiv \top$ and $t \equiv x$, the loop $\mathtt{while}\ x \neq 0\ \mathtt{do}\ x := x - 1$ decreases $t$ on every iteration and still diverges from $x = -1$.
5. Using a logical variable $n$ in the variant rule that also occurs in the program. Exercise 8 shows that this makes the rule unsound.
6. Forgetting that a logical variable in a specification is implicitly universally quantified over the whole triple. Writing $\{x = A\}\ c\ \{x = A + 1\}$ means the same $A$ before and after.
7. Treating a precondition as something the program checks. A triple says nothing about states outside $P$, so a program can behave arbitrarily there.
8. Believing that relative completeness makes proofs automatic. It only says that a derivation exists, given an oracle for assertions and given invariants that nothing in the theorem helps you find.

## Exercises

### Exercise 1

Classify each triple as valid or invalid for partial correctness, and say whether it is also valid as a total correctness triple. All variables range over the integers.

(a) $\{x = 1\}\ \mathtt{while}\ x > 0\ \mathtt{do}\ x := x + 1\ \{x = 0\}$

(b) $\{\top\}\ x := x + 1\ \{x > 0\}$

(c) $\{\bot\}\ c\ \{Q\}$ for arbitrary $c$ and $Q$

(d) $\{x \geq 0\}\ y := x \times x\ \{y \geq x\}$

<details><summary>Solution</summary>

(a) Valid for partial correctness, because the loop diverges from $x = 1$ and there is no final state. Invalid for total correctness.

(b) Invalid in both senses. From $x = -5$ the final value is $-4$.

(c) Valid for partial correctness, and valid for total correctness as well, because no state satisfies $\bot$.

(d) Valid in both senses. For $x \geq 0$ on the integers, either $x = 0$ and $x^2 = x$, or $x \geq 1$ and $x^2 \geq x$. The command always terminates.

</details>

### Exercise 2

Use the assignment axiom and the sequencing rule to compute a precondition, and simplify it over the integers.

(a) $\{?\}\ x := x + y\ \{x = 2y\}$

(b) $\{?\}\ y := x + 1 ;\ x := 2y\ \{x > y\}$

<details><summary>Solution</summary>

(a) The axiom gives $x + y = 2y$, which simplifies to $x = y$.

(b) Working backward, $x := 2y$ turns $x > y$ into $2y > y$, which is $y > 0$. Then $y := x + 1$ turns it into $x + 1 > 0$, which is $x \geq 0$ over the integers.

</details>

### Exercise 3

Give a full proof outline for the exchange without a temporary variable.

$$\{x = A \land y = B\}\ x := x + y ;\ y := x - y ;\ x := x - y\ \{x = B \land y = A\}$$

<details><summary>Solution</summary>

Compute backward from the postcondition.

```
{ x = A ∧ y = B }
{ y = B ∧ x = A }                       same as the next line after simplification
{ (x+y) - ((x+y) - y) = B ∧ (x+y) - y = A }
x := x + y ;
{ x - (x - y) = B ∧ x - y = A }
y := x - y ;
{ x - y = B ∧ y = A }
x := x - y
{ x = B ∧ y = A }
```

The arithmetic is $(x+y) - ((x+y) - y) = y$ and $(x+y) - y = x$, so the third assertion simplifies to $y = B \land x = A$, which the precondition states. Over mathematical integers no overflow can occur. On machine integers with wrapping arithmetic the same identities hold modulo $2^w$.

</details>

### Exercise 4

Prove total correctness of the following program, with invariant and variant stated explicitly.

```
[ n ≥ 0 ]
i := 0 ; s := 0 ;
while i < n do ( i := i + 1 ; s := s + i )
[ 2·s = n·(n+1) ]
```

<details><summary>Solution</summary>

Take $I \equiv 0 \leq i \leq n \land 2s = i(i+1)$ and $t \equiv n - i$.

Initiation. With $i = s = 0$ the invariant becomes $0 \leq 0 \leq n \land 0 = 0$, which follows from $n \geq 0$.

Preservation. Backward through the body, $I$ becomes $0 \leq i+1 \leq n \land 2(s + i + 1) = (i+1)(i+2)$. From $I$ and $i < n$ we get $0 \leq i + 1 \leq n$. Also $2(s + i + 1) = i(i+1) + 2(i+1) = (i+1)(i+2)$.

Exit. $I \land \neg(i < n)$ gives $i = n$, so $2s = n(n+1)$.

Bound. $I \land i < n \to n - i \geq 0$.

Decrease. Backward through the body, $n - i < m$ becomes $n - (i+1) < m$. With $m = n - i$ this holds.

</details>

### Exercise 5

(a) Show that Floyd's forward assignment rule is derivable from the backward axiom and consequence.

(b) Show that it is strongest in this sense: if $\models \{P\}\ x := e\ \{Q\}$ then $\models (\exists x_0.\ P[x_0/x] \land x = e[x_0/x]) \to Q$.

<details><summary>Solution</summary>

Let $F \equiv \exists x_0.\ P[x_0/x] \land x = e[x_0/x]$ with $x_0$ fresh.

(a) The axiom gives $\{F[e/x]\}\ x := e\ \{F\}$, where $F[e/x] \equiv \exists x_0.\ P[x_0/x] \land e = e[x_0/x]$, since $x$ does not occur in $P[x_0/x]$ or in $e[x_0/x]$. Then $P \to F[e/x]$ is valid, using the witness $x_0 := x$, because $P[x/x]$ is $P$ and $e[x/x]$ is $e$. Consequence gives the rule.

(b) Assume $\sigma' \models F$. Let $v$ be a witness for $x_0$, and let $\sigma = \sigma'[x \mapsto v]$. Then $\sigma \models P$ by the substitution lemma, and $\sigma'(x) = [\![e[x_0/x]]\!]\sigma'[x_0 \mapsto v] = [\![e]\!]\sigma$. So $\sigma'$ is the result of running $x := e$ from $\sigma$ on the program variables, and the assumed triple gives $\sigma' \models Q$. The fresh $x_0$ is not free in $Q$, so its value does not matter.

</details>

### Exercise 6

The command $\mathtt{repeat}\ c\ \mathtt{until}\ b$ means $c ;\ \mathtt{while}\ \neg b\ \mathtt{do}\ c$. Derive the following rule from the rules of partial correctness.

$$\frac{\{P\}\ c\ \{Q\} \quad \models Q \land \neg b \to P}{\{P\}\ \mathtt{repeat}\ c\ \mathtt{until}\ b\ \{Q \land b\}}$$

<details><summary>Solution</summary>

Take $Q$ as the invariant of the while loop.

```
1. { P } c { Q }                                premise
2. ⊨ Q ∧ ¬b → P                                 premise
3. { Q ∧ ¬b } c { Q }                           consequence 2, 1
4. { Q } while ¬b do c { Q ∧ ¬¬b }              while 3
5. ⊨ Q ∧ ¬¬b → Q ∧ b                            logic
6. { Q } while ¬b do c { Q ∧ b }                consequence 4, 5
7. { P } c ; while ¬b do c { Q ∧ b }            seq 1, 6
```

</details>

### Exercise 7

(a) Prove the following lemma: if $\langle c,\sigma\rangle \Downarrow \sigma'$ and $c$ does not assign $x$, then $\sigma'(x) = \sigma(x)$.

(b) Use it to prove that the invariance rule is sound.

(c) Show that the side condition of the invariance rule cannot be dropped.

<details><summary>Solution</summary>

(a) By induction on the big-step derivation. Skip does not change the state. An assignment to $y \neq x$ does not change $x$. The remaining rules compose smaller runs of subcommands that also do not assign $x$, so the claim follows from the induction hypotheses.

(b) Assume $\models \{P\}\ c\ \{Q\}$, and let $\sigma \models P \land R$ with $\langle c,\sigma\rangle \Downarrow \sigma'$. Then $\sigma' \models Q$. By part (a), $\sigma$ and $\sigma'$ agree on the free variables of $R$. The truth of a formula depends only on its free variables, so $\sigma' \models R$.

(c) From $\{\top\}\ x := 1\ \{\top\}$ with $R \equiv x = 0$, the rule without its side condition would give $\{x = 0\}\ x := 1\ \{x = 0\}$, which is false.

</details>

### Exercise 8

Show that the rule while-total becomes unsound if $n$ is allowed to occur in the loop body.

<details><summary>Solution</summary>

Take $I \equiv y \geq 0$, $b \equiv \top$, $t \equiv y$, and let the body be $c \equiv n := y + 1$.

The first premise reads $[y \geq 0 \land \top \land y = n]\ n := y + 1\ [y \geq 0 \land y < n]$. It is valid, since afterwards $n = y + 1 > y$. The second premise $y \geq 0 \land \top \to y \geq 0$ is valid.

The conclusion would be $[y \geq 0]\ \mathtt{while}\ \top\ \mathtt{do}\ n := y + 1\ [y \geq 0 \land \bot]$, which claims termination of a loop that never terminates. The variant never changes, and the body moves the comparison value instead. The side condition guarantees that $n$ stays a fixed record of the initial value of $t$.

</details>

### Exercise 9

Prove total correctness of $\mathtt{while}\ x \neq 0\ \mathtt{do}\ x := x - 1$ from precondition $x \geq 0$ to postcondition $x = 0$. Then explain why the invariant $\top$ does not work for the same variant.

<details><summary>Solution</summary>

Take $I \equiv x \geq 0$ and $t \equiv x$.

Decrease: $[x \geq 0 \land x \neq 0 \land x = n]\ x := x - 1\ [x \geq 0 \land x < n]$. Backward, the postcondition becomes $x - 1 \geq 0 \land x - 1 < n$. From $x \geq 0$ and $x \neq 0$ we get $x \geq 1$, and $x - 1 < x = n$.

Bound: $x \geq 0 \land x \neq 0 \to x \geq 0$.

Exit: $x \geq 0 \land \neg(x \neq 0) \to x = 0$.

With $I \equiv \top$ the bound premise becomes $x \neq 0 \to x \geq 0$, which fails at $x = -1$. That failure is real, since the loop diverges from $x = -1$. The invariant has to exclude the states from which the variant is not bounded.

</details>

### Exercise 10

Let $\mathtt{for}\ i := a\ \mathtt{to}\ b\ \mathtt{do}\ c$ abbreviate $i := a ;\ \mathtt{while}\ i \leq b\ \mathtt{do}\ (c ;\ i := i + 1)$, where $a, b$ are expressions and $c$ assigns neither $i$ nor any variable of $a$ or $b$, and $i$ does not occur in $a$ or $b$. Design a rule whose premise concerns $c$ only, and derive it.

<details><summary>Solution</summary>

The rule is

$$\frac{\{I \land a \leq i \leq b\}\ c\ \{I[i+1/i]\}}{\{I[a/i] \land a \leq b + 1\}\ \mathtt{for}\ i := a\ \mathtt{to}\ b\ \mathtt{do}\ c\ \{I[b+1/i]\}}$$

Derivation. Use the while invariant $J \equiv I \land a \leq i \leq b + 1$.

Initiation: the assignment axiom for $i := a$ needs $J[a/i] \equiv I[a/i] \land a \leq a \leq b + 1$, which follows from the rule's precondition.

Preservation: from $J \land i \leq b$ we have $I \land a \leq i \leq b$. Let $R \equiv a \leq i \leq b$. Since $c$ assigns no variable of $R$, the invariance rule applied to the premise gives $\{I \land R\}\ c\ \{I[i+1/i] \land R\}$. The assignment axiom gives $\{J[i+1/i]\}\ i := i + 1\ \{J\}$, where $J[i+1/i] \equiv I[i+1/i] \land a \leq i + 1 \leq b + 1$. This follows from $I[i+1/i] \land R$.

Exit: $J \land \neg(i \leq b)$ gives $i = b + 1$, so $I$ becomes $I[b+1/i]$.

The side condition $a \leq b + 1$ is needed because an empty range with $a > b + 1$ would otherwise claim $I[b+1/i]$ from $I[a/i]$ with no iterations.

</details>

### Exercise 11

Prove that for every sound proof system for partial correctness over the integers whose derivable triples are recursively enumerable, some valid triple is not derivable. Then explain why Cook's theorem is consistent with this fact.

<details><summary>Solution</summary>

Let $D = \{c : \models \{\top\}\ c\ \{\bot\}\}$, the set of programs that diverge from every initial state. Its complement is recursively enumerable, because you can dovetail over initial states and step counts until a run halts. If $D$ were also recursively enumerable, it would be decidable. By a reduction from the halting problem it is not: from a program $p$ with no inputs, build $c_p$ that ignores its initial state and simulates $p$, so $c_p \in D$ if and only if $p$ diverges.

If a sound system derived all valid triples and its theorems were recursively enumerable, then enumerating its derivable triples of the form $\{\top\}\ c\ \{\bot\}$ would enumerate exactly $D$, which is a contradiction.

Cook's theorem is consistent with this because its proof system takes every valid assertion of arithmetic as an axiom. That set is not recursively enumerable, so the system in Cook's theorem is not effective.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- State the definitions of partial and total correctness in terms of big-step semantics.
- Write all the rules from memory, including while-total with its side condition on $n$.
- Prove soundness of the assignment axiom from the substitution lemma, and of the while rule by nested induction.
- Produce a full derivation and a proof outline for a program with one loop, given the invariant.
- Find the invariant and variant yourself for loops of the size of integer division.
- Give a counterexample for each dropped side condition: forward assignment, invariance, the bound premise and the freshness of $n$.
- State Cook's relative completeness theorem, and prove that no effective sound and complete system exists.

## Materials

- Hoare, An Axiomatic Basis for Computer Programming, CACM 1969. Read it for the original rules, the division proof and Hoare's discussion of why axioms help language design.
- Winskel, The Formal Semantics of Programming Languages. Read its treatment of Hoare rules for IMP for the soundness proof against operational semantics and the relative completeness proof.
- Huth and Ryan, Logic in Computer Science, 2nd edition. Read its program verification material for a gentle treatment of proof outlines with many small examples.
- Floyd, Assigning Meanings to Programs, 1967. Read it for the flowchart origin of invariants and of well-founded termination arguments.
- Cook, Soundness and Completeness of an Axiom System for Program Verification, SIAM Journal on Computing 1978. Read it for the definition of expressiveness and the relative completeness theorem.
- Clarke, Programming Language Constructs for Which It Is Impossible to Obtain Good Hoare Axiom Systems, JACM 1979. Read it for the limits of relative completeness.
- Apt, de Boer and Olderog, Verification of Sequential and Concurrent Programs, 3rd edition. Read it for a careful textbook development of proof outlines, total correctness and completeness.
