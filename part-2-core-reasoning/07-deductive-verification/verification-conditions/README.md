# Verification Conditions

Part 2, Chapter 7: Deductive Verification.

## Objective

Explain how verifiers generate compact verification conditions and send them to solvers.

## Why this matters

A verifier is a compiler from annotated programs to solver queries. Whether a proof succeeds in seconds, times out or fails unpredictably depends strongly on the shape of the formula this compiler emits. Dafny, Boogie and the Viper backend based on verification condition generation all use the ideas in this topic. If you work on such tools, you will read generated verification conditions, change their encoding and debug their quantifier instantiation. This topic connects [Weakest Preconditions](../weakest-preconditions/) to [DPLL(T)](../../05-smt/dpllt/), [Arrays](../../05-smt/arrays/) and [Quantifiers](../../05-smt/quantifiers/), and it prepares you for the program verifiers in [Dafny](../../../part-4-remaining-methods/12-proof-assistants/dafny/).

## Prerequisites

- [Weakest Preconditions](../weakest-preconditions/) for the calculation rules.
- [Loop Invariants](../loop-invariants/) for inductive invariants and ranking functions.
- [DPLL(T)](../../05-smt/dpllt/) for how a solver processes the result.
- [Arrays](../../05-smt/arrays/) for read-over-write reasoning.
- [Quantifiers](../../05-smt/quantifiers/) for instantiation by matching.

## Lesson

### The task

A verification condition (VC) is a formula whose validity implies that a program meets its specification. A VC generator takes an annotated program, meaning a program with loop invariants, procedure contracts and assertions, and produces the formula. Soundness is the essential requirement: if the VC is valid, then the program is correct. The converse is not expected. An invalid VC may reflect a real bug, an invariant that is too weak, or a contract that says too little.

The architecture described by Barnett and Leino for the Spec# verifier is a pipeline, and the sections below follow it from the source language to the solver.

```
annotated source
    → unstructured intermediate program           (control-flow graph)
    → reducible control-flow graph                (only if needed)
    → acyclic program                             (cut the back edges using invariants)
    → dynamic single assignment form              (fresh incarnations)
    → passive program                             (assignments become assumes)
    → weakest precondition with block equations   (the VC)
    → negation sent to an SMT solver
```

### Classical VC generation for structured programs

This simple form is good for hand work and for understanding. Annotate each loop with an invariant, written $\mathtt{while}\ b\ \mathtt{inv}\ I\ \mathtt{do}\ c$. Define $\mathrm{pre}(c, Q)$, an assertion, and $\mathrm{VC}(c, Q)$, a set of side conditions, by recursion on $c$:

| Command $c$ | $\mathrm{pre}(c, Q)$ | $\mathrm{VC}(c, Q)$ |
|---|---|---|
| $\mathtt{skip}$ | $Q$ | $\emptyset$ |
| $x := e$ | $Q[e/x]$ | $\emptyset$ |
| $c_1 ; c_2$ | $\mathrm{pre}(c_1, \mathrm{pre}(c_2, Q))$ | $\mathrm{VC}(c_1, \mathrm{pre}(c_2, Q)) \cup \mathrm{VC}(c_2, Q)$ |
| $\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ | $(b \to \mathrm{pre}(c_1, Q)) \land (\neg b \to \mathrm{pre}(c_2, Q))$ | $\mathrm{VC}(c_1, Q) \cup \mathrm{VC}(c_2, Q)$ |
| $\mathtt{while}\ b\ \mathtt{inv}\ I\ \mathtt{do}\ c'$ | $I$ | $\{I \land b \to \mathrm{pre}(c', I),\ I \land \neg b \to Q\} \cup \mathrm{VC}(c', I)$ |

To verify $\{P\}\ c\ \{Q\}$, check that $P \to \mathrm{pre}(c, Q)$ and every formula in $\mathrm{VC}(c, Q)$ are valid.

Theorem (soundness). If all formulas in $\mathrm{VC}(c, Q)$ are valid, then $\vdash \{\mathrm{pre}(c, Q)\}\ c\ \{Q\}$ in Hoare logic, with consequence available for valid formulas. Hence if $P \to \mathrm{pre}(c, Q)$ is also valid, then $\models \{P\}\ c\ \{Q\}$.

Proof. By structural induction on $c$, for all $Q$. Skip and assignment are axioms. For sequence, apply the hypotheses to $c_2$ with $Q$, and to $c_1$ with $\mathrm{pre}(c_2, Q)$, and then use seq. For the conditional, the hypotheses give triples for each branch, and $\mathrm{pre} \land b \to \mathrm{pre}(c_1, Q)$ and $\mathrm{pre} \land \neg b \to \mathrm{pre}(c_2, Q)$ are propositional tautologies. For the loop, the hypothesis gives $\vdash \{\mathrm{pre}(c', I)\}\ c'\ \{I\}$. The first VC and consequence give $\vdash \{I \land b\}\ c'\ \{I\}$. The while rule gives $\vdash \{I\}\ \mathtt{while}\ b\ \mathtt{do}\ c'\ \{I \land \neg b\}$. The second VC and consequence give the postcondition $Q$. $\square$

This is a mechanical construction of the Hoare derivation in which the invariants are the only creative input.

### The intermediate language

Modern verifiers first compile to a small language in which all control and specification constructs are expressed with a few statements. It is a variant of the guarded commands of [Weakest Preconditions](../weakest-preconditions/).

```
S ::= x := e | havoc x | assert P | assume P | S ; S | S □ S
```

An execution of `assert P` goes wrong if $P$ is false. An execution of `assume P` is simply discarded if $P$ is false, and such a run is called infeasible or blocking. A program is correct if no execution goes wrong. The rules follow from these meanings.

| Statement | $\mathrm{wp}(\cdot, Q)$ | $\mathrm{wlp}(\cdot, Q)$ |
|---|---|---|
| $x := e$ | $Q[e/x]$ | $Q[e/x]$ |
| $\mathtt{havoc}\ x$ | $\forall x.\ Q$ | $\forall x.\ Q$ |
| $\mathtt{assert}\ P$ | $P \land Q$ | $P \to Q$ |
| $\mathtt{assume}\ P$ | $P \to Q$ | $P \to Q$ |
| $S ; T$ | $\mathrm{wp}(S, \mathrm{wp}(T, Q))$ | $\mathrm{wlp}(S, \mathrm{wlp}(T, Q))$ |
| $S \mathbin{\square} T$ | $\mathrm{wp}(S, Q) \land \mathrm{wp}(T, Q)$ | $\mathrm{wlp}(S, Q) \land \mathrm{wlp}(T, Q)$ |

The VC of a program $S$ is $\mathrm{wp}(S, \top)$. A postcondition is an assert at the end, and a precondition is an assume at the start. In this language $\mathrm{wlp}$ allows going wrong and only constrains normal termination. This follows the usage in Leino's account, and it is the reason that $\mathrm{wlp}(\mathtt{assert}\ P, Q)$ is $P \to Q$.

The source constructs compile as follows.

$$\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2 \quad\text{becomes}\quad (\mathtt{assume}\ b ;\ c_1) \mathbin{\square} (\mathtt{assume}\ \neg b ;\ c_2).$$

A loop is cut so that the back edge disappears. Let $x_1, \ldots, x_m$ be the variables assigned in the body $c$, called the loop targets.

```
assert I ;                     // initiation
havoc x1 ; ... ; havoc xm ;    // jump to an arbitrary iteration
assume I ;
(   assume b ; c ; assert I ; assume ⊥   // preservation; this path stops here
  □ assume ¬b )                          // exit; continue with the rest of the program
```

Running this acyclic program checks initiation at the first assert, and checks preservation from an arbitrary state satisfying $I \land b$ in the first branch. In the second branch, the code following the loop continues from an arbitrary state satisfying $I \land \neg b$. The havoc makes the program an over-approximation, because it forgets everything about the targets except $I$, and facts about other variables survive automatically. Exercise 7 proves soundness. A nested loop is cut first, from the inside out.

Barnett and Leino state this on control-flow graphs. A back edge is an edge whose target dominates its source. For each loop header they add a copy of the invariant's asserts to each predecessor of the header, they turn the original asserts in the header into assumes, they insert havocs of the loop targets at the start of the header, and then they remove the back edges. Control-flow graphs that are not reducible are first made reducible by duplicating code.

A procedure call is replaced by its contract, which is the basis of modular verification. For a procedure with precondition $\mathit{Pre}$, postcondition $\mathit{Post}$ and modified variables $g$, a call is compiled to the following.

```
assert Pre ;                  // with actual arguments substituted
old_g := g ;                  // the value before the call
havoc g ; havoc result ;
assume Post                   // with arguments, result and old(g) = old_g substituted
```

Each procedure body is verified once, as `assume Pre ; body ; assert Post`. The caller's proof never mentions the callee's body, so the VC of a procedure depends only on its own code and on the contracts of what it calls.

### Why naive wp explodes

There are two independent sources of exponential growth, if formulas are expanded as text.

Branching. In $\mathrm{wp}(S \mathbin{\square} T, Q) \equiv \mathrm{wp}(S, Q) \land \mathrm{wp}(T, Q)$ the postcondition is copied. A sequence of $k$ conditionals produces $2^k$ copies of the final postcondition, one per path.

Substitution. Each assignment replaces all occurrences of a variable by an expression. A sequence of $k$ assignments $x := x + x$ takes $Q(x)$ to $Q(2^k x)$ written with $2^k$ occurrences of $x$.

Sharing subterms in a graph avoids the size problem, but Leino points out that size is not the whole issue. A prover that proves a conjunction by proving each conjunct will treat a duplicated obligation repeatedly, even when the branch taken does not affect it. The encoding has to avoid the case split in the prover, and sharing alone in the term does not do that.

### Passive form

The main idea of Flanagan and Saxe is to remove assignments first. Convert the acyclic program to a dynamic single assignment form, where each variable is assigned at most once on any execution, and then replace each assignment by an assume.

Rules for an acyclic program, processed in topological order:

1. Each variable $x$ has a current incarnation, initially $x_0$.
2. Every read of $x$ uses its current incarnation.
3. The statement $x := e$ becomes $\mathtt{assume}\ x_{i} = e'$, where $x_i$ is fresh and $e'$ is $e$ with its current incarnations. Then $x_i$ becomes current.
4. The statement $\mathtt{havoc}\ x$ makes a fresh $x_i$ current and emits nothing.
5. At a join, if predecessors disagree on the current incarnation of $x$, choose a fresh $x_j$ and add $\mathtt{assume}\ x_j = x_{\text{pred}}$ at the end of each predecessor.

The assumption is harmless, because $x_i$ is not used before its definition. In logical terms, the one-point rule says $Q[e/x] \equiv \forall x'.\ x' = e \to Q[x'/x]$ for fresh $x'$, so the statement $x := e$ and the sequence "choose $x'$, assume $x' = e$" have the same wp, up to renaming. Validity of the VC treats fresh incarnations as implicitly universally quantified at the top.

A passive program contains only assert, assume, sequence and choice. Assignments and havocs are gone, and with them the substitution problem. No variable changes value during a run, so all assertions are predicates over one fixed state.

### The property of passive statements

Theorem. For every passive $S$ and all $Q$:

$$\mathrm{wlp}(S, Q) \equiv \mathrm{wlp}(S, \bot) \lor Q \qquad\text{and thus}\qquad \mathrm{wp}(S, Q) \equiv \mathrm{wp}(S, \top) \land (\mathrm{wlp}(S, \bot) \lor Q).$$

The second equation follows from the first using the pairing theorem. Exercise 5 proves the first. Intuitively, in a passive statement the state does not change, so if $Q$ holds at the start it also holds at the end of any normal termination. So it does not matter when you check it.

Flanagan and Saxe define this calculation with two functions, $N$ and $W$, and Leino identifies them as $\neg N(S) \equiv \mathrm{wlp}(S, \bot)$ and $\neg W(S) \equiv \mathrm{wp}(S, \top)$. Write $\mathrm{nrm}(S) \equiv \neg\mathrm{wlp}(S, \bot)$, meaning that $S$ can terminate normally from this state, and $\mathrm{ok}(S) \equiv \mathrm{wp}(S, \top)$, meaning that $S$ cannot go wrong.

| Statement | $\mathrm{ok}$ | $\mathrm{nrm}$ |
|---|---|---|
| $\mathtt{assert}\ P$ | $P$ | $P$ |
| $\mathtt{assume}\ P$ | $\top$ | $P$ |
| $S ; T$ | $\mathrm{ok}(S) \land (\mathrm{nrm}(S) \to \mathrm{ok}(T))$ | $\mathrm{nrm}(S) \land \mathrm{nrm}(T)$ |
| $S \mathbin{\square} T$ | $\mathrm{ok}(S) \land \mathrm{ok}(T)$ | $\mathrm{nrm}(S) \lor \mathrm{nrm}(T)$ |

The downstream obligation $\mathrm{ok}(T)$ occurs once, regardless of the branching in $S$, and the prover needs to consider it only once. The price is a copy of $\mathrm{nrm}(S)$ at each sequence node, and each copy has linear size, so the VC is quadratic in the size of the passive program. Flanagan and Saxe's result is a VC that is worst-case quadratic in the source size and, as they report, close to linear in practice.

The property fails for statements that change state. For $x := 1$, $\mathrm{wlp}(x := 1, \bot) \equiv \bot$, so the formula on the right of the theorem would be $Q$ itself, whereas $\mathrm{wp}(x := 1, x = 2) \equiv \bot$.

### Block equations for unstructured programs

Barnett and Leino obtain a linear VC, and also handle arbitrary control-flow graphs. For each block $A : S ;\ \mathtt{goto}\ B_1, \ldots, B_m$ of a passive program, introduce a Boolean variable $A_{\mathit{ok}}$ with the block equation

$$A_{\mathit{ok}} \equiv \mathrm{wp}\Big(S,\ \bigwedge_{i} (B_i)_{\mathit{ok}}\Big).$$

Let $R$ be the conjunction of all block equations. The VC is

$$R \to \mathit{Start}_{\mathit{ok}}.$$

The variable $A_{\mathit{ok}}$ means that all executions from $A$ in the current state are correct. Since $\mathrm{wp}$ of assert and assume mentions its second argument exactly once, each equation has size linear in its block, and the VC is linear in the size of the passive program. This improves the bound of the previous section because the prover can name downstream obligations using a Boolean atom. A case split on one atom does not duplicate the formula behind it.

Theorem. If the VC of a passive acyclic program is valid, then the program is correct.

Proof. The program is acyclic, so the block equations can be read as definitions of the auxiliary variables in reverse topological order. Every state of the program variables has a unique extension to the auxiliary variables that satisfies $R$. In this extension, an induction in reverse topological order shows that $A_{\mathit{ok}}$ has the same truth value as the textual expansion of the wp of the subgraph from $A$. The VC is thus valid exactly when $\mathrm{wp}$ of the whole program is valid. $\square$

The paper proves a more general form: any passive program, even with cycles, is correct if its VC is valid. The block equations then need not be definitions, so Tarski's theorem provides a solution for the auxiliary variables.

The passive program may itself be larger than the source. Each join may add one assume for each variable on each incoming edge, which gives a bound of order (number of edges) $\times$ (number of variables) in the worst case. The paper also gives a technique for reducing the number of incarnations created at joins.

### Heap, arrays and frames

A verifier models memory as maps in the [theory of arrays](../../05-smt/arrays/), or as a heap map from object and field pairs to values. A field update $o.f := v$ becomes $H := \mathit{store}(H, (o, f), v)$. Then a contract's modifies clause compiles to `havoc H` followed by an assumption stating that all locations outside the modifies set are unchanged:

$$\forall o, f.\ (o, f) \notin \mathit{mod} \to H[(o, f)] = H_{\mathit{old}}[(o, f)].$$

This quantified frame axiom is one source of the cost that [Separation Logic](../separation-logic/) tries to reduce by making framing structural.

### Sending the VC to a solver

The formula passed to an SMT solver is the negation of the VC, together with background axioms for the source language's types and functions.

$$\text{background axioms} \land R \land \neg \mathit{Start}_{\mathit{ok}}.$$

An answer of unsat means that the VC is valid. An answer of sat comes with a model, a candidate counterexample. An answer of unknown or a timeout means that nothing has been established.

A model must be read with care. In the loop-cut program the havocked values are arbitrary states that satisfy $I$, so a model may show an unreachable state. It proves only that the VC is invalid, which may mean a weak invariant. To localize a failure, follow the false $\mathit{ok}$ variables: $\mathit{Start}_{\mathit{ok}}$ is false, so some assert in it is false or some successor's $\mathit{ok}$ is false, and following these yields a path to a failing assert. Tools build error traces in similar ways. For example, Leino, Millstein and Saxe describe labelling subformulas to recover traces.

Quantifiers are usually instantiated by E-matching. Each quantifier is associated with a trigger, which is a set of patterns. When the solver's equivalence classes contain a term matching the pattern, it adds the corresponding instance. This technique was developed in the Simplify prover (Detlefs, Nelson and Saxe). It is efficient and incomplete, and it shapes how specifications must be written.

- If a trigger is too restrictive, a needed instance is never generated, and the proof fails with unknown or with a spurious model. The user often repairs this by mentioning a term in an assertion, so that the pattern finds a match.
- If a trigger is too permissive, it can produce a matching loop, where each instance creates a new term that matches again.

Solver behavior can also vary greatly under small changes to the formula, because heuristics depend on term order and random seeds. Verification engineers refer to this as proof brittleness. Common mitigations are splitting a VC into smaller queries, hiding definitions until they are needed, and keeping specifications out of nonlinear arithmetic where possible.

Vacuity is the corresponding risk from soundness. A VC with inconsistent assumptions is valid and proves nothing. A smoke test inserts `assert ⊥` at chosen locations and expects each to fail. If such an assert is proved, that location is unreachable under the current assumptions, and the assumptions need to be examined.

## Worked examples

### Example 1: counting the explosion

Let $S_k$ be $k$ conditionals in sequence, each of the form $\mathtt{if}\ b_i\ \mathtt{then}\ x := x + 1\ \mathtt{else}\ \mathtt{skip}$, and $Q \equiv x \geq 0$. For $k = 2$, naive wp gives

```
wp(if b2 ..., Q)  =  (b2 → x + 1 ≥ 0) ∧ (¬b2 → x ≥ 0)                     2 copies of Q

wp(if b1 ..., that)
  =  (b1 → (b2 → x + 1 + 1 ≥ 0) ∧ (¬b2 → x + 1 ≥ 0))
   ∧ (¬b1 → (b2 → x + 1 ≥ 0) ∧ (¬b2 → x ≥ 0))                             4 copies of Q
```

In general there are $2^k$ copies, one for each path.

Now use the pipeline for $k = 2$. Each join gets a fresh incarnation.

```
Start:  goto T1, E1
T1:     assume b1 ; assume x1 = x0 + 1 ; assume x2 = x1 ; goto J1
E1:     assume ¬b1 ; assume x2 = x0 ; goto J1
J1:     goto T2, E2
T2:     assume b2 ; assume x3 = x2 + 1 ; assume x4 = x3 ; goto End
E2:     assume ¬b2 ; assume x4 = x2 ; goto End
End:    assert x4 ≥ 0
```

The block equations are as follows, and $Q$ occurs once.

```
End_ok   ≡ x4 ≥ 0
E2_ok    ≡ ¬b2 → x4 = x2 → End_ok
T2_ok    ≡ b2 → x3 = x2 + 1 → x4 = x3 → End_ok
J1_ok    ≡ T2_ok ∧ E2_ok
E1_ok    ≡ ¬b1 → x2 = x0 → J1_ok
T1_ok    ≡ b1 → x1 = x0 + 1 → x2 = x1 → J1_ok
Start_ok ≡ T1_ok ∧ E1_ok
```

This VC is invalid unless a precondition such as $x_0 \geq 0$ is assumed, and that is the expected result, since the program can start with negative $x$. The important point is the size. Each new conditional adds a constant number of equations, and the size grows linearly in $k$.

### Example 2: the full pipeline on a loop

```
assume n ≥ 0 ;
i := 0 ; s := 0 ;
while i < n
    invariant I(i, s) ≡ 0 ≤ i ∧ i ≤ n ∧ 2·s = i·(i+1)
do ( i := i + 1 ; s := s + i ) ;
assert 2·s = n·(n+1)
```

Step 1: the control-flow graph, with the back edge cut. The loop targets are $i$ and $s$.

```
Start:  assume n ≥ 0 ; i := 0 ; s := 0 ; assert I(i, s) ; goto Head
Head:   havoc i ; havoc s ; assume I(i, s) ; goto Body, After
Body:   assume i < n ; i := i + 1 ; s := s + i ; assert I(i, s) ; goto
After:  assume ¬(i < n) ; assert 2·s = n·(n+1) ; goto
```

The `goto` with no target in `Body` is the removed back edge, which has the same effect as `assume ⊥` for what follows.

Step 2: dynamic single assignment and passive form. The variable $n$ is never assigned, so it has only the incarnation $n_0$. The havocs of $i$ and $s$ introduce new incarnations $i_1$ and $s_1$.

```
Start:  assume n0 ≥ 0 ; assume i0 = 0 ; assume s0 = 0 ; assert I(i0, s0) ; goto Head
Head:   assume I(i1, s1) ; goto Body, After
Body:   assume i1 < n0 ; assume i2 = i1 + 1 ; assume s2 = s1 + i2 ; assert I(i2, s2) ; goto
After:  assume ¬(i1 < n0) ; assert 2·s1 = n0·(n0+1) ; goto
```

Step 3: block equations.

```
Start_ok ≡ n0 ≥ 0 → i0 = 0 → s0 = 0 → ( I(i0, s0) ∧ Head_ok )
Head_ok  ≡ I(i1, s1) → ( Body_ok ∧ After_ok )
Body_ok  ≡ i1 < n0 → i2 = i1 + 1 → s2 = s1 + i2 → I(i2, s2)
After_ok ≡ ¬(i1 < n0) → 2·s1 = n0·(n0+1)
```

Step 4: prove the VC by hand. After unfolding, three facts remain.

Initiation. With $i_0 = s_0 = 0$ and $n_0 \geq 0$, $I(0, 0)$ reduces to $0 \leq 0 \land 0 \leq n_0 \land 0 = 0$.

Preservation. Assume $0 \leq i_1 \leq n_0$, $2s_1 = i_1(i_1 + 1)$, $i_1 < n_0$, $i_2 = i_1 + 1$, $s_2 = s_1 + i_2$. Then $0 \leq i_2 \leq n_0$, and $2s_2 = 2s_1 + 2i_2 = i_1(i_1 + 1) + 2(i_1 + 1) = (i_1 + 1)(i_1 + 2) = i_2(i_2 + 1)$.

Exit. From $i_1 \leq n_0$ and $\neg(i_1 < n_0)$, $i_1 = n_0$, so $2s_1 = n_0(n_0 + 1)$.

Step 5: a failed proof. Replace the invariant by the weaker $I'(i, s) \equiv 0 \leq i \land 2s = i(i+1)$, dropping $i \leq n$. A solver returns sat for the negated VC, with this model:

```
n0 = 0, i1 = 1, s1 = 1
Start_ok = false, Head_ok = false, After_ok = false
```

Reading the $\mathit{ok}$ variables gives the path `Start`, `Head`, `After`. The failing assert is $2 s_1 = n_0(n_0 + 1)$, which reads $2 = 0$. The state $i = 1, n = 0$ is not reachable by the program, because $i$ never exceeds $n$. So the correct conclusion is that the invariant is too weak, and there is no bug in the program. Adding back $i \leq n$ repairs the proof.

### Example 3: an array loop and E-matching

```
assume n ≥ 0 ;
i := 0 ;
while i < n
    invariant 0 ≤ i ≤ n ∧ ∀k. 0 ≤ k < i → a[k] = 0
do ( a[i] := 0 ; i := i + 1 ) ;
assert ∀k. 0 ≤ k < n → a[k] = 0
```

The targets are $i$ and $a$. The update is $a := \mathit{store}(a, i, 0)$. Consider the preservation part of the VC after passification:

$$0 \leq i_1 \leq n \land (\forall k.\ 0 \leq k < i_1 \to a_1[k] = 0) \land i_1 < n \land a_2 = \mathit{store}(a_1, i_1, 0) \land i_2 = i_1 + 1 \to 0 \leq i_2 \leq n \land \forall k.\ 0 \leq k < i_2 \to a_2[k] = 0.$$

The bounds on $i_2$ are easy linear arithmetic, so focus on the quantifier. Negate and Skolemize the conclusion with a fresh constant $k_0$. Use trigger $a_1[k]$ for the hypothesis.

```
Literals asserted:
  L1  0 ≤ k0
  L2  k0 < i2
  L3  a2[k0] ≠ 0
  L4  a2 = store(a1, i1, 0)
  L5  i2 = i1 + 1

Theory of arrays, read over write on store(a1, i1, 0)[k0]
(using L4 and congruence to relate a2[k0]):
  (k0 = i1  ∧ a2[k0] = 0)  ∨  (k0 ≠ i1 ∧ a2[k0] = a1[k0])

Case split:
  Case k0 = i1:  a2[k0] = 0 contradicts L3.  Learn k0 ≠ i1.
  Case k0 ≠ i1:  a2[k0] = a1[k0].  The new term a1[k0] matches the trigger a1[k] with k := k0.

E-matching adds the instance:
  L6  0 ≤ k0 ∧ k0 < i1 → a1[k0] = 0

Linear arithmetic:
  L2, L5 give k0 < i1 + 1.  With k0 ≠ i1 this gives k0 < i1.
  L1 and this fact satisfy the antecedent of L6, so a1[k0] = 0.
  a2[k0] = a1[k0] = 0 contradicts L3.

Result: unsat, so the VC is valid.
```

The trigger is what makes this automatic. The term $a_1[k_0]$ appears only after the array case split, and this produces the only instance that the proof requires.

The VCs of Examples 2 and 3 were checked with an SMT solver, and the model in Step 5 was the one returned by the solver. The identities for $\mathrm{ok}$, $\mathrm{nrm}$ and block equations were tested on random passive programs by exhaustive evaluation over Boolean states.

## Common mistakes

1. Concluding a bug from a sat answer. A model of the negated VC may be an unreachable state allowed by a weak invariant, as in Step 5 of Example 2.
2. Concluding correctness from an unsat answer without checking the assumptions. Inconsistent contracts or assumes make everything provable, so run a smoke test.
3. Forgetting that `assume` is unchecked. A manually added assume is a trusted claim, and an error there is a soundness error in your proof.
4. Havocking too little when cutting a loop. All variables assigned in the body, including in nested loops and through callees' modifies clauses, must be targets, or the cut is unsound.
5. Restating too much in invariants. Variables that are not targets keep their values across a cut, so a verifier does not need them in the invariant. Conversely, omitting a fact about a target loses it, however obvious it was before the loop.
6. Treating a passive program's variables as state variables. In the VC they are universally quantified constants, one for each incarnation, and nothing is updated.
7. Believing that passivity alone gives a compact VC. The VC is also compact because of the wp formulation used on it. Expanding the textual wp of a passive program still duplicates $Q$ at every choice.
8. Believing that term sharing alone solves the problem. Sharing reduces size, but a prover may still do repeated work on shared obligations, as Leino explains. The formula's logical structure matters.
9. Applying the identity $\mathrm{wp}(S, Q) \equiv \mathrm{wp}(S, \top) \land (\mathrm{wlp}(S, \bot) \lor Q)$ to statements with assignments. It fails, as the counterexample above shows.
10. Writing a quantified axiom without considering its trigger. For example, a trigger that matches a term created by the axiom's own instance creates a matching loop.

## Exercises

### Exercise 1

Compute $\mathrm{wp}(S, \top)$ and say whether the result is valid.

(a) $\mathtt{assert}\ x > 0 ;\ \mathtt{assume}\ y = x ;\ \mathtt{assert}\ y \geq 1$

(b) $\mathtt{havoc}\ x ;\ \mathtt{assume}\ x > y ;\ \mathtt{assert}\ x \geq y$

(c) $\mathtt{assume}\ x > 0 ;\ \mathtt{assume}\ x < 0 ;\ \mathtt{assert}\ 1 = 2$

<details><summary>Solution</summary>

(a) $x > 0 \land (y = x \to y \geq 1)$. It is not valid, because the first conjunct fails at $x = 0$. The assertion is an obligation on callers of this code.

(b) $\forall x.\ x > y \to x \geq y$. It is valid.

(c) $x > 0 \to (x < 0 \to 1 = 2)$. It is valid, vacuously, since the assumptions are inconsistent.

</details>

### Exercise 2

Use the classical generator to produce all VCs for this program, and state each one simplified. Do not prove them.

```
{ x ≥ 0 }
q := 0 ; r := x ;
while y ≤ r inv x = q·y + r ∧ r ≥ 0 do ( r := r - y ; q := q + 1 )
{ x = q·y + r ∧ 0 ≤ r ∧ r < y }
```

<details><summary>Solution</summary>

Let $I \equiv x = qy + r \land r \geq 0$ and $Q$ be the postcondition.

The precondition of the loop is $I$. Then $\mathrm{pre}(q := 0 ;\ r := x, I) \equiv x = 0 \cdot y + x \land x \geq 0$.

The VCs are:

1. $x \geq 0 \to x = 0 \cdot y + x \land x \geq 0$.
2. $I \land y \leq r \to x = (q + 1) y + (r - y) \land r - y \geq 0$.
3. $I \land \neg(y \leq r) \to Q$.

</details>

### Exercise 3

Convert the following to passive form, write the block equations, and prove the VC.

```
if x > 0 then y := x else y := -x ;
z := y + 1 ;
assert z > 0
```

<details><summary>Solution</summary>

```
Start:  goto T, E
T:      assume x0 > 0 ;    assume y1 = x0 ;  assume y3 = y1 ; goto J
E:      assume ¬(x0 > 0) ; assume y2 = -x0 ; assume y3 = y2 ; goto J
J:      assume z1 = y3 + 1 ; assert z1 > 0
```

```
J_ok     ≡ z1 = y3 + 1 → z1 > 0
T_ok     ≡ x0 > 0 → y1 = x0 → y3 = y1 → J_ok
E_ok     ≡ ¬(x0 > 0) → y2 = -x0 → y3 = y2 → J_ok
Start_ok ≡ T_ok ∧ E_ok
```

Proof of $\mathit{Start}_{\mathit{ok}}$, given the equations. For $T_{\mathit{ok}}$, assume $x_0 > 0$, $y_1 = x_0$ and $y_3 = y_1$. Then $y_3 > 0$, so if $z_1 = y_3 + 1$, then $z_1 > 0$. For $E_{\mathit{ok}}$, assume $x_0 \leq 0$, $y_2 = -x_0$ and $y_3 = y_2$. Then $y_3 \geq 0$, so $z_1 = y_3 + 1 \geq 1 > 0$.

</details>

### Exercise 4

Let $S \equiv ((\mathtt{assume}\ a ;\ \mathtt{assert}\ b) \mathbin{\square} (\mathtt{assume}\ \neg a ;\ \mathtt{assert}\ c)) ;\ \mathtt{assert}\ d$. Compute $\mathrm{ok}(S)$ and $\mathrm{nrm}(S)$ and compare with the naive wp.

<details><summary>Solution</summary>

Let $S_1$ and $S_2$ be the two branches.

$\mathrm{ok}(S_1) \equiv \top \land (a \to b) \equiv a \to b$, and $\mathrm{nrm}(S_1) \equiv a \land b$.

$\mathrm{ok}(S_2) \equiv \neg a \to c$, and $\mathrm{nrm}(S_2) \equiv \neg a \land c$.

The choice has $\mathrm{ok} \equiv (a \to b) \land (\neg a \to c)$ and $\mathrm{nrm} \equiv (a \land b) \lor (\neg a \land c)$.

The sequence gives

$$\mathrm{ok}(S) \equiv (a \to b) \land (\neg a \to c) \land \big(((a \land b) \lor (\neg a \land c)) \to d\big), \qquad \mathrm{nrm}(S) \equiv ((a \land b) \lor (\neg a \land c)) \land d.$$

The naive wp is $(a \to b \land d) \land (\neg a \to c \land d)$. The two are equivalent, but $d$ occurs twice in the naive form and once in $\mathrm{ok}(S)$. If $d$ is a large downstream formula and there are many such choices, the difference is exponential.

</details>

### Exercise 5

Prove that $\mathrm{wlp}(S, Q) \equiv \mathrm{wlp}(S, \bot) \lor Q$ for every passive $S$ and every $Q$.

<details><summary>Solution</summary>

By structural induction on $S$, for all $Q$.

Case $\mathtt{assert}\ P$ or $\mathtt{assume}\ P$. Both have wlp $P \to Q$, which is $\neg P \lor Q$. Also $\mathrm{wlp}(\cdot, \bot) \equiv \neg P$.

Case $S ; T$.

$$\mathrm{wlp}(S ; T, Q) \equiv \mathrm{wlp}(S, \mathrm{wlp}(T, Q)) \equiv \mathrm{wlp}(S, \mathrm{wlp}(T, \bot) \lor Q) \equiv \mathrm{wlp}(S, \bot) \lor \mathrm{wlp}(T, \bot) \lor Q.$$

The second step uses the hypothesis for $T$. The third uses the hypothesis for $S$ with postcondition $\mathrm{wlp}(T, \bot) \lor Q$. Taking $Q \equiv \bot$ in the same calculation gives $\mathrm{wlp}(S ; T, \bot) \equiv \mathrm{wlp}(S, \bot) \lor \mathrm{wlp}(T, \bot)$, which proves the claim.

Case $S \mathbin{\square} T$.

$$\mathrm{wlp}(S \mathbin{\square} T, Q) \equiv (\mathrm{wlp}(S, \bot) \lor Q) \land (\mathrm{wlp}(T, \bot) \lor Q) \equiv (\mathrm{wlp}(S, \bot) \land \mathrm{wlp}(T, \bot)) \lor Q,$$

and $\mathrm{wlp}(S \mathbin{\square} T, \bot) \equiv \mathrm{wlp}(S, \bot) \land \mathrm{wlp}(T, \bot)$.

</details>

### Exercise 6

Show that the same identity fails for $\mathtt{havoc}\ x$, and explain how passification avoids the problem.

<details><summary>Solution</summary>

$\mathrm{wlp}(\mathtt{havoc}\ x, \bot) \equiv \forall x.\ \bot \equiv \bot$. So the identity would claim $\mathrm{wlp}(\mathtt{havoc}\ x, Q) \equiv Q$. But with $Q \equiv x = 1$, the left side is $\forall x.\ x = 1$, which is false, while $Q$ is not false.

Passification removes the havoc by making a fresh incarnation current. Every later occurrence of $x$ in $Q$ refers to the fresh constant $x_i$, which is free in the VC and is therefore effectively universally quantified. Since $x_i$ was not referred to earlier, the quantifier can be moved to the outside of the whole formula.

</details>

### Exercise 7

Prove that the loop cut is sound. Let $E$ be the cut program for $\mathtt{while}\ b\ \mathtt{inv}\ I\ \mathtt{do}\ c$ with $c$ loop-free and targets $\bar{x}$. Assume that $P \to \mathrm{wp}(E, Q)$ is valid. Prove $\models \{P\}\ \mathtt{while}\ b\ \mathtt{do}\ c\ \{Q\}$.

<details><summary>Solution</summary>

Compute. Since $\mathrm{wp}(\mathtt{assume}\ \bot, X) \equiv \top$, the first branch has wp equal to $b \to \mathrm{wp}(c, I \land \top) \equiv b \to \mathrm{wp}(c, I)$. So

$$\mathrm{wp}(E, Q) \equiv I \land Z, \quad\text{where } Z \equiv \forall \bar{x}.\ \big(I \to (b \to \mathrm{wp}(c, I)) \land (\neg b \to Q)\big).$$

$Z$ has no free targets, so no execution of $c$ changes its truth value, by the lemma on unassigned variables. Let $J \equiv I \land Z$.

Initiation: $P \to J$ by assumption.

Preservation: let $\sigma \models J \land b$. Instantiate $Z$ with the current values of $\bar{x}$, and get $\sigma \models \mathrm{wp}(c, I)$. So all runs of $c$ end in $I$, and $Z$ is unchanged, so they end in $J$.

Exit: if $\sigma \models J \land \neg b$, instantiating $Z$ gives $\sigma \models Q$.

The while rule, with soundness, yields the triple. The use of $Z$ is the formal reason that facts about non-targets survive a cut without being mentioned in $I$.

</details>

### Exercise 8

Let `inc` have the contract: requires $x \geq 0$, modifies $g$, ensures $r = x + 1 \land g = \mathrm{old}(g) + r$. Compile the caller below, compute its VC and prove it.

```
assume a ≥ 0 ;
save := g ;
b := inc(a) ;
assert b > a ∧ g > save
```

<details><summary>Solution</summary>

```
assume a ≥ 0 ;
save := g ;
assert a ≥ 0 ;
old_g := g ;
havoc g ; havoc b ;
assume b = a + 1 ∧ g = old_g + b ;
assert b > a ∧ g > save
```

Compute the wp backward, with no substitution needed for $a$:

$$a \geq 0 \to \Big(a \geq 0 \land \forall g', b'.\ \big(b' = a + 1 \land g' = g + b' \to b' > a \land g' > g\big)\Big).$$

Here $g$ on the right is the initial value, since both $\mathit{save}$ and $\mathit{old\_g}$ receive it by substitution. Assume $a \geq 0$. The first conjunct is immediate. For the second, $b' = a + 1 > a$, and $g' = g + b' = g + a + 1 > g$, because $a + 1 > 0$.

The proof uses only the contract. A property of `inc` that is not in the contract, such as whether it writes to a log, is not available to the caller.

</details>

### Exercise 9

Explain what the verifier reports for a procedure with an unsatisfiable precondition, and design a check that detects this. Then explain why the same check detects dead code.

<details><summary>Solution</summary>

The body is verified as `assume Pre ; body ; assert Post`. If $\mathit{Pre}$ is unsatisfiable, the VC $\mathit{Pre} \to \ldots$ is valid for every body and postcondition, and the verifier reports success. The callers then have to establish $\mathit{Pre}$ at each call site, which is impossible, so the problem will surface there unless the procedure is never called.

To detect it, check whether the verifier proves the program `assume Pre ; assert ⊥`. If it does, $\mathit{Pre}$ is unsatisfiable, assuming the background axioms are consistent. To detect dead code, insert `assert ⊥` at the start of each block, one at a time. The verifier proves that assert exactly when no feasible execution reaches the block under the given assumptions. Since the verifier over-approximates at loop cuts and calls, a failed assert does not prove that the block is reachable in the real program.

</details>

### Exercise 10

Consider the axiom $\forall x.\ f(x) = f(g(x))$.

(a) Trace E-matching with trigger $f(x)$, starting from the ground term $f(a)$.

(b) Choose a better trigger, and show how the goal $f(a) = f(g(a))$ is proved with it.

<details><summary>Solution</summary>

(a) The term $f(a)$ matches with $x := a$, giving $f(a) = f(g(a))$. This introduces $f(g(a))$, which matches with $x := g(a)$, giving $f(g(a)) = f(g(g(a)))$, and the process continues forever. This is a matching loop.

(b) Use the trigger $f(g(x))$. The negated goal $f(a) \neq f(g(a))$ contains the term $f(g(a))$, which matches with $x := a$, giving $f(a) = f(g(a))$. This contradicts the negated goal at once. The instance introduces no new term of the form $f(g(\cdot))$, so instantiation stops. With $f(a)$ alone and no $f(g(\cdot))$ term, this trigger would produce nothing, and that is the trade-off.

</details>

### Exercise 11

Prove that the block-equation VC for a passive program is linear in the size of the program, under the assumption that an assertion is counted with its size and that a block with $m$ successors has size at least $m$.

<details><summary>Solution</summary>

Let a block have body $S_1 ; \ldots ; S_p$ and successors $B_1, \ldots, B_m$, and let $X \equiv \bigwedge_i (B_i)_{\mathit{ok}}$. Computing backward, $\mathrm{wp}(\mathtt{assert}\ P, Y) \equiv P \land Y$ and $\mathrm{wp}(\mathtt{assume}\ P, Y) \equiv P \to Y$. Each adds one copy of $P$ and a constant number of symbols, and it keeps exactly one occurrence of $Y$. So by induction on $p$, the right side of the block equation has size $O(|S_1| + \cdots + |S_p| + m)$, and $X$ occurs once in it. The left side and equivalence add a constant. Summing over all blocks, the total is linear in the size of the program. The final implication and $\mathit{Start}_{\mathit{ok}}$ add a constant.

</details>

### Exercise 12

Extend the loop cut to prove termination with a variant $t$. State exactly where the new statements go, and give the resulting VCs for the body.

<details><summary>Solution</summary>

Change the first branch as follows, where $t_0$ is a fresh variable, not assigned in the body.

```
assume b ;
t0 := t ;
assert t0 ≥ 0 ;
c ;
assert I ;
assert t < t0 ;
assume ⊥
```

The assignment records the value of $t$ at the start of the iteration, and the two asserts encode the bound and the decrease. For an invariant $I$, the VCs for this branch are

$$I \land b \to t \geq 0 \qquad\text{and}\qquad I \land b \land t = t_0 \to \mathrm{wp}(c, I \land t < t_0).$$

These are the premises of the rule while-total from [Hoare Logic](../hoare-logic/). Since nested loops are cut first, an inner loop must be proved to terminate by its own variant, and an outer variant must decrease over a whole iteration, using only what the inner invariant and exit condition provide.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Produce the classical VCs for an annotated structured program with loops, and prove the generator sound.
- Write wp and wlp for assert, assume, havoc, sequence and choice.
- Cut a loop with assert, havoc and assume, and prove the cut sound.
- Compile a procedure call using its contract, including the handling of old values.
- Convert an acyclic program to passive form, including the copies at joins.
- State the property of passive statements, prove it and give a counterexample for assignments.
- Compute $\mathrm{ok}$ and $\mathrm{nrm}$, and write block equations.
- Explain how many copies of the postcondition each encoding produces, and why sharing does not settle the question.
- Read a model of the negated VC and decide between a program bug and a weak invariant.
- Explain triggers, trace E-matching on a small example and recognize a matching loop.

## Materials

- Flanagan and Saxe, Avoiding exponential explosion: generating compact verification conditions, POPL 2001. Read it for passive form, the $N$ and $W$ functions and the quadratic bound.
- Barnett and Leino, Weakest-precondition of unstructured programs, PASTE 2005. Read it for loop cutting on control-flow graphs, block equations and the linear bound.
- [Boogie source repository.](https://github.com/boogie-org/boogie) Use it to see these encodings in an industrial intermediate verification language, and read its examples after this topic.
- Leino, Efficient weakest preconditions, Information Processing Letters 2005. Read it for the short explanation of the Flanagan and Saxe technique in terms of wp and wlp.
- Barnett, Chang, DeLine, Jacobs and Leino, Boogie: A Modular Reusable Verifier for Object-Oriented Programs, FMCO 2005. Read it for the architecture around the VC generator.
- Detlefs, Nelson and Saxe, Simplify: A Theorem Prover for Program Checking, JACM 2005. Read it for E-matching and the design of an SMT solver for verification.
- Leino, Millstein and Saxe, Generating error traces from verification-condition counterexamples, Science of Computer Programming 2005. Read it for how labels and models are turned into error traces.
- Leino, Dafny: An Automatic Program Verifier for Functional Correctness, LPAR 2010. Read it to see how a source-level language compiles down to this pipeline.
