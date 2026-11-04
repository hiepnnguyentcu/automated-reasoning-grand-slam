# Separation Logic

Part 2, Chapter 7: Deductive Verification.

## Objective

Prove pointer programs correct using the frame rule and inductive heap predicates.

## Why this matters

Most systems code manipulates a heap, and in such code the question of which writes can affect which reads dominates verification. Separation logic made this question part of the assertion language, so that a proof only mentions the memory a command uses. This idea underlies concurrent reasoning in [Concurrent Separation Logic](../concurrent-separation-logic/), the ownership-based verifiers built on Viper, the verification of Rust through its ownership discipline, and static analyzers such as Infer. An applied scientist working on systems software will encounter these specifications, and needs to be able to read them, write them and tell why a proof fails to go through.

## Prerequisites

- [Hoare Logic](../hoare-logic/) for triples, the invariance rule and the problem of aliasing.
- [Weakest Preconditions](../weakest-preconditions/) for backward reasoning.
- [Loop Invariants](../loop-invariants/) for invariant design.
- [Induction Principles](../../../part-1-foundations/03-semantics-and-types/induction-principles/) for inductive definitions.

## Lesson

### The problem of aliasing

Consider a language with pointers. The rule of constancy in [Hoare Logic](../hoare-logic/) would give

$$\frac{\{x \mapsto -\}\ [x] := 4\ \{x \mapsto 4\}}{\{x \mapsto - \land y \mapsto 3\}\ [x] := 4\ \{x \mapsto 4 \land y \mapsto 3\}}$$

and the conclusion is false when $x = y$. In traditional Hoare logic, a proof must state that every pair of pointers that might alias does not alias, or else treat the whole heap as one array variable and carry the facts through every update. For a data structure of $n$ cells, the number of disequalities grows quadratically, and every procedure specification has to say what it leaves unchanged.

Burstall pointed out in 1972 that reasoning about list-like structures benefits from describing disjoint pieces. Reynolds, Ishtiaq and O'Hearn developed the idea into a logic around 2000. Ishtiaq and O'Hearn related it to the logic of bunched implications, and O'Hearn, Reynolds and Yang introduced the frame rule in its modern form with a local semantics. Reynolds's 2002 survey is the standard presentation.

### The programming language

Add these commands to IMP. Expressions depend only on the store, so reads of the heap are separate commands.

```
c ::= ...
    | x := [e]                 lookup
    | [e] := e'                mutation
    | x := cons(e1, ..., en)   allocate n consecutive cells
    | dispose e                free one cell
```

A state is a pair of a store and a heap. The store $s$ maps variables to integers. The heap $h$ is a finite partial function from locations to integers. Locations are positive integers, and $\mathit{nil}$ is $0$, so $\mathit{nil}$ is never a location.

A lookup, mutation or disposal of an address outside $\mathrm{dom}(h)$ causes the execution to abort, which is called a memory fault. Allocation chooses any free block of $n$ consecutive locations, so it is nondeterministic. The semantics has an outcome $\mathit{abort}$ in addition to final states.

### Assertions

The assertion language extends first-order logic with four forms. Write $h_1 \perp h_2$ when the two heaps have disjoint domains, and $h_1 \cdot h_2$ for their union in that case.

$$s, h \models \mathsf{emp} \iff \mathrm{dom}(h) = \emptyset$$

$$s, h \models e \mapsto e' \iff \mathrm{dom}(h) = \{[\![e]\!]s\} \text{ and } h([\![e]\!]s) = [\![e']\!]s$$

$$s, h \models p * q \iff \exists h_1, h_2.\ h_1 \perp h_2,\ h = h_1 \cdot h_2,\ s, h_1 \models p,\ s, h_2 \models q$$

$$s, h \models p \mathbin{-\!\!*} q \iff \forall h'.\ \text{if } h' \perp h \text{ and } s, h' \models p \text{ then } s, h \cdot h' \models q$$

The connectives $\land, \lor, \neg, \to, \forall, \exists$ have their usual meaning on a fixed state. A pure assertion, one built with no heap forms, depends only on the store. It holds of any heap.

Abbreviations:

$$e \mapsto - \ \equiv\ \exists v.\ e \mapsto v, \qquad e \hookrightarrow e' \ \equiv\ (e \mapsto e') * \top, \qquad e \mapsto e_1, \ldots, e_n \ \equiv\ e \mapsto e_1 * \cdots * (e + n - 1) \mapsto e_n.$$

The points-to assertion $e \mapsto e'$ is exact: it says that the heap is that one cell. The assertion $e \hookrightarrow e'$ says that the heap contains at least that cell. Reading an assertion as a claim to own the described cells is the most useful intuition: $p * q$ says that the two claims are on separate memory.

The separating conjunction is commutative and associative with unit $\mathsf{emp}$. It distributes in one direction over conjunction and in both over disjunction and existentials:

$$(p_1 \lor p_2) * q \leftrightarrow (p_1 * q) \lor (p_2 * q), \qquad (\exists v.\ p) * q \leftrightarrow \exists v.\ (p * q) \text{ when } v \text{ is not free in } q, \qquad (p_1 \land p_2) * q \to (p_1 * q) \land (p_2 * q).$$

Separation also gives the monotonicity rule: from $p_1 \to p_2$ and $q_1 \to q_2$, conclude $p_1 * q_1 \to p_2 * q_2$. The separating implication satisfies the adjunction: $p * q \to r$ is valid if and only if $p \to (q \mathbin{-\!\!*} r)$ is valid. Two consequences are $p * (p \mathbin{-\!\!*} q) \to q$ and $q \to p \mathbin{-\!\!*} (p * q)$.

For pure $b$, $(p \land b) * q \leftrightarrow (p * q) \land b$, which moves pure facts in and out of a separating conjunction. If $b_1$ and $b_2$ are both pure, then $b_1 \land b_2$ and $b_1 * b_2$ are equivalent.

Several familiar laws fail. The following are all invalid in general: $p * q \to p$, $p \to p * p$ and $p \land q \to p * q$. The proposition $x \mapsto 1 * x \mapsto 1$ is unsatisfiable, and this is how separation rules out aliasing: from $x \mapsto 1 * y \mapsto 2$ you may conclude $x \neq y$.

Some semantically defined classes are important.

- $p$ is pure if its truth does not depend on the heap.
- $p$ is precise if for each state $(s, h)$ there is at most one subheap $h' \subseteq h$ with $s, h' \models p$.
- $p$ is intuitionistic if it is preserved under extension of the heap.

The assertions $\mathsf{emp}$, $e \mapsto e'$ and $e \mapsto -$ are precise, and $*$ preserves preciseness. The assertions $\top$ and $\mathsf{emp} \lor (x \mapsto -)$ are not precise. Precision is the property that the concurrent logic needs.

Decidability is sharply limited. Reynolds summarizes the following results for classical separation logic without arithmetic: with quantifiers, validity is not recursively enumerable, while without quantifiers and with the characteristic operations it is decidable. Tools therefore use restricted fragments such as symbolic heaps, which are separating conjunctions of points-to and list facts with some pure facts and no separating implication.

### Triples and fault avoidance

The meaning of a triple includes the absence of faults.

$\{p\}\ c\ \{q\}$ holds if, for all $(s, h)$ with $s, h \models p$: the execution of $c$ from $(s, h)$ does not abort, and every terminating execution ends in a state satisfying $q$. For $[p]\ c\ [q]$, it must also always terminate.

In Reynolds's paraphrase of a saying by O'Hearn, itself after Milner, well-specified programs do not go wrong. Fault avoidance is the key to the design of the logic. Since $\{p\}\ c\ \{q\}$ guarantees no faults, any cell $c$ accesses must be either allocated by $c$ or guaranteed by $p$. So the precondition is a complete description of what the command may touch, called its footprint.

### The rules

All rules of Hoare logic for the sequential commands stay sound, with the assignment axiom applying only to store assignments. The rule of constancy does not. It is replaced by the frame rule, and the heap commands get small axioms.

$$\frac{\{p\}\ c\ \{q\}}{\{p * r\}\ c\ \{q * r\}}\ \text{(frame: no variable free in } r \text{ is modified by } c\text{)}$$

$$\{e \mapsto -\}\ [e] := e'\ \{e \mapsto e'\} \qquad \{e \mapsto -\}\ \mathtt{dispose}\ e\ \{\mathsf{emp}\}$$

$$\{\mathsf{emp}\}\ x := \mathtt{cons}(\bar{e})\ \{x \mapsto \bar{e}\}\ \ (x \text{ not free in } \bar{e})$$

$$\{e \mapsto v\}\ x := [e]\ \{x = v \land e \mapsto v\}\ \ (x \text{ not free in } e, v).$$

If $x$ occurs in $e$ or $\bar{e}$, the versions with a saved old value apply, where $x'$ is a fresh logical variable and $e'$ denotes $e[x'/x]$:

$$\{x = x' \land \mathsf{emp}\}\ x := \mathtt{cons}(\bar{e})\ \{x \mapsto \bar{e}'\} \qquad \{x = x' \land e \mapsto v\}\ x := [e]\ \{x = v \land e' \mapsto v\}\ \ (x \neq v).$$

The auxiliary variable rule from Hoare logic, $\{p\}\ c\ \{q\}$ implies $\{\exists y.\ p\}\ c\ \{\exists y.\ q\}$ for $y$ not in $c$, stays sound and is used constantly to manage existentials.

### Soundness of the frame rule

The soundness of the frame rule depends on two semantic facts about all commands of this language, as stated by Reynolds. Let $h_0 \subseteq h$ with $h = h_0 \cdot h_1$.

1. Safety monotonicity. If $c$ from $(s, h)$ can abort, then $c$ from $(s, h_0)$ can abort.
2. Frame property. If $c$ from $(s, h)$ can terminate in $(s', h')$, then either $c$ from $(s, h_0)$ can abort, or $c$ from $(s, h_0)$ can terminate in $(s', h_0')$ with $h_0' \perp h_1$ and $h' = h_0' \cdot h_1$.

Both are proved by induction on the execution. The idea is that a command that does not fault with a small heap uses only that heap, and a larger heap makes no difference.

Theorem. The frame rule is sound.

Proof. Assume $\{p\}\ c\ \{q\}$, and let $s, h \models p * r$. There are $h_0, h_1$ with $h = h_0 \cdot h_1$, $s, h_0 \models p$ and $s, h_1 \models r$. If $c$ from $(s, h)$ could abort, then by safety monotonicity $c$ from $(s, h_0)$ could abort, which contradicts the assumption. Now suppose $c$ from $(s, h)$ terminates in $(s', h')$. By the frame property, and since aborting from $(s, h_0)$ is impossible, $c$ from $(s, h_0)$ terminates in $(s', h_0')$, where $h' = h_0' \cdot h_1$. The assumption gives $s', h_0' \models q$. Since $c$ modifies no free variable of $r$, $s$ and $s'$ agree on those variables, and thus $s', h_1 \models r$. Therefore $s', h' \models q * r$. $\square$

The frame rule is valid exactly because every specification is tight: there is no way to prove a triple about a command that needs a cell not in its precondition. Yang also proved a completeness result in this sense: if the only thing known about a command is that $\{p\}\ c\ \{q\}$ is valid, all consequences of this fact can be derived with frame, consequence, auxiliary variable elimination and substitution.

### Global and backward forms

The frame rule converts small axioms to global forms. For mutation:

$$\{(e \mapsto -) * r\}\ [e] := e'\ \{(e \mapsto e') * r\}.$$

Taking $r \equiv (e \mapsto e') \mathbin{-\!\!*} q$ and using $(e \mapsto e') * ((e \mapsto e') \mathbin{-\!\!*} q) \to q$ gives a backward rule, which provides a weakest precondition:

$$\{(e \mapsto -) * ((e \mapsto e') \mathbin{-\!\!*} q)\}\ [e] := e'\ \{q\}.$$

The backward rules for the other commands, as given by Reynolds, are

$$\{(e \mapsto -) * r\}\ \mathtt{dispose}\ e\ \{r\}$$

$$\{\forall x'.\ (x' \mapsto \bar{e}) \mathbin{-\!\!*} q[x'/x]\}\ x := \mathtt{cons}(\bar{e})\ \{q\}$$

$$\{\exists v.\ (e \hookrightarrow v) \land q[v/x]\}\ x := [e]\ \{q\},$$

where $x'$ and $v$ are chosen fresh. The separating implication is mainly useful in this role. Most hand proofs and tools use only forward symbolic execution with $*$, as in the examples below.

### Inductive heap predicates

Data structures are described by inductive definitions over mathematical values. Reynolds's list segment predicate relates a sequence $\alpha$ to a chain of two-cell records, where the first cell holds a value and the second holds the next pointer.

$$\mathsf{list}\ \epsilon\ (i, j) \ \equiv\ \mathsf{emp} \land i = j \qquad \mathsf{list}\ (a \cdot \alpha)\ (i, k) \ \equiv\ \exists j.\ i \mapsto a, j * \mathsf{list}\ \alpha\ (j, k).$$

The important lemmas, proved by induction on $\alpha$, are:

$$\mathsf{list}\ (\alpha \cdot \beta)\ (i, k) \leftrightarrow \exists j.\ \mathsf{list}\ \alpha\ (i, j) * \mathsf{list}\ \beta\ (j, k)$$

$$\mathsf{list}\ (\alpha \cdot b)\ (i, k) \leftrightarrow \exists j.\ \mathsf{list}\ \alpha\ (i, j) * j \mapsto b, k$$

$$\mathsf{list}\ \alpha\ (i, j) \to (i = \mathit{nil} \to (\alpha = \epsilon \land j = \mathit{nil})) \qquad \mathsf{list}\ \alpha\ (i, j) \to (i \neq j \to \alpha \neq \epsilon).$$

Note that $i = j$ does not imply $\alpha = \epsilon$, because the segment may be cyclic: $\mathsf{list}\ \alpha\ (i, i)$ can hold for a nonempty $\alpha$. When the end is $\mathit{nil}$ this cannot happen, so $\mathsf{list}\ \alpha\ (i, \mathit{nil}) \land i = \mathit{nil}$ implies $\alpha = \epsilon$, and $i \neq \mathit{nil}$ implies that the sequence is nonempty.

Binary trees are defined similarly over tree values:

$$\mathsf{tree}\ \mathit{leaf}\ (i) \ \equiv\ \mathsf{emp} \land i = \mathit{nil} \qquad \mathsf{tree}\ (\mathit{node}\ \tau_1\ \tau_2)\ (i) \ \equiv\ \exists l, r.\ i \mapsto l, r * \mathsf{tree}\ \tau_1\ (l) * \mathsf{tree}\ \tau_2\ (r).$$

The separating conjunction automatically says that subtrees do not share cells and that the structure is acyclic. Expressing this with ordinary first-order assertions over a heap map takes reachability and many quantifiers.

### Automation

A symbolic execution engine for separation logic keeps a symbolic heap and steps over commands. It needs a frame inference query: given a current heap $p$ and a required precondition $q$, find a frame $F$ with $p \vdash q * F$. The Smallfoot tool of Berdine, Calcagno and O'Hearn checked annotated programs this way. Calcagno, Distefano, O'Hearn and Yang added bi-abduction, the problem of solving $A * p \vdash q * F$ for both a missing precondition $A$ and a frame $F$, in order to infer specifications bottom-up. O'Hearn's 2019 review describes how this leads to the Infer static analyzer. The technique is used at scale because each procedure can be analyzed independently, and the frame rule is what permits this.

## Worked examples

### Example 1: swapping through pointers, with explicit frames

Prove

```
{ x ↦ A ∗ y ↦ B }
a := [x] ; b := [y] ; [x] := b ; [y] := a
{ x ↦ B ∗ y ↦ A }
```

Each line uses a small axiom, with the rest of the assertion as frame.

```
{ x ↦ A ∗ y ↦ B }
a := [x]            lookup on x ↦ A, frame y ↦ B
{ (a = A ∧ x ↦ A) ∗ y ↦ B }
{ a = A ∧ (x ↦ A ∗ y ↦ B) }
b := [y]            lookup on y ↦ B, frame (a = A ∧ x ↦ A)
{ a = A ∧ b = B ∧ (x ↦ A ∗ y ↦ B) }
[x] := b            mutation on x ↦ -, frame (a = A ∧ b = B ∧ y ↦ B)
{ a = A ∧ b = B ∧ (x ↦ b ∗ y ↦ B) }
[y] := a            mutation on y ↦ -, frame (a = A ∧ b = B ∧ x ↦ b)
{ a = A ∧ b = B ∧ (x ↦ b ∗ y ↦ a) }
{ x ↦ B ∗ y ↦ A }
```

The side conditions hold. Lookup into $a$ has a frame with no $a$, and the second lookup's frame has $a$ but the command modifies only $b$. The mutations modify no variables.

The precondition rules out $x = y$. This matches reality here, because for the program as written, $x = y$ and $A \ne B$ is impossible, as a single cell cannot hold both values. The case of aliased pointers with one value would need the separate proof of $\{x \mapsto A \land x = y\}\ \ldots\ \{x \mapsto A\}$.

### Example 2: in-place list reversal

This is Reynolds's motivating example. The program is

```
j := nil ;
while i ≠ nil do ( k := [i + 1] ; [i + 1] := j ; j := i ; i := k )
```

The specification is $\{\mathsf{list}\ \alpha_0\ (i, \mathit{nil})\}\ \ldots\ \{\mathsf{list}\ \alpha_0^{\dagger}\ (j, \mathit{nil})\}$, where $\alpha^{\dagger}$ is the reversal of $\alpha$.

At any moment, $i$ points to the part yet to be reversed, and $j$ to the part already reversed. The invariant is

$$I \ \equiv\ \exists \alpha, \beta.\ (\mathsf{list}\ \alpha\ (i, \mathit{nil}) * \mathsf{list}\ \beta\ (j, \mathit{nil})) \land \alpha_0^{\dagger} = \alpha^{\dagger} \cdot \beta.$$

Note how much the separating conjunction does. With $\land$ in its place, you would have to add a clause saying that the two lists are disjoint in their reachable cells, and a clause saying that any other list in the program is also disjoint from them.

Initiation. After $j := \mathit{nil}$, take $\alpha := \alpha_0$ and $\beta := \epsilon$. Then $\mathsf{list}\ \epsilon\ (\mathit{nil}, \mathit{nil})$ is $\mathsf{emp}$, and $\alpha_0^{\dagger} = \alpha_0^{\dagger} \cdot \epsilon$.

Preservation.

```
{ ∃α,β. (list α (i, nil) ∗ list β (j, nil)) ∧ α0† = α†·β ∧ i ≠ nil }

    Since i ≠ nil, the sequence is nonempty, so write it as a·α. Unfold list:

{ ∃a,α,β,k'. (i ↦ a,k' ∗ list α (k', nil) ∗ list β (j, nil)) ∧ α0† = (a·α)†·β }

k := [i + 1] ;         lookup on i+1 ↦ k', frame everything else

{ ∃a,α,β. (i ↦ a,k ∗ list α (k, nil) ∗ list β (j, nil)) ∧ α0† = (a·α)†·β }

[i + 1] := j ;         mutation on i+1 ↦ -, frame everything else

{ ∃a,α,β. (i ↦ a,j ∗ list α (k, nil) ∗ list β (j, nil)) ∧ α0† = (a·α)†·β }

    Fold list using i ↦ a,j ∗ list β (j, nil) → list (a·β) (i, nil).
    Use (a·α)† = α†·a, so (a·α)†·β = α†·(a·β):

{ ∃a,α,β. (list α (k, nil) ∗ list (a·β) (i, nil)) ∧ α0† = α†·(a·β) }

    Rename a·β to β, using ∃:

{ ∃α,β. (list α (k, nil) ∗ list β (i, nil)) ∧ α0† = α†·β }

j := i ; i := k        assignment axiom twice

{ ∃α,β. (list α (i, nil) ∗ list β (j, nil)) ∧ α0† = α†·β }
```

The renaming step in the last implication drops information deliberately. The resulting assertion mentions $k$ only until it is replaced.

Adequacy. $I \land i = \mathit{nil}$ gives $\alpha = \epsilon$ by the list lemma, so $\mathsf{list}\ \alpha\ (i, \mathit{nil})$ is $\mathsf{emp}$. Then $\alpha_0^{\dagger} = \epsilon \cdot \beta = \beta$, and thus $\mathsf{list}\ \alpha_0^{\dagger}\ (j, \mathit{nil})$.

Termination. The variant is the length of $\alpha$, which decreases by one in each iteration. It is well-defined as a logical quantity because in the heap satisfying the invariant, the list from $i$ to $\mathit{nil}$ determines the sequence's length. Formally, $\alpha$ can be replaced by a function of the state, or the rule can be applied with the bound stated as $|\alpha| = n$ inside the existential.

The frame rule also yields a property for free. If another list satisfies $\mathsf{list}\ \gamma\ (x, \mathit{nil})$ separately, then $\{\mathsf{list}\ \alpha_0\ (i, \mathit{nil}) * \mathsf{list}\ \gamma\ (x, \mathit{nil})\}\ \ldots\ \{\mathsf{list}\ \alpha_0^{\dagger}\ (j, \mathit{nil}) * \mathsf{list}\ \gamma\ (x, \mathit{nil})\}$ follows with no further proof, provided that the program does not modify $x$.

### Example 3: disposing a tree recursively

Let `disposeTree` be the recursive procedure below, in which $l$ and $r$ are local to each call.

```
procedure disposeTree(i):
    if i ≠ nil then
        l := [i] ;
        r := [i + 1] ;
        disposeTree(l) ;
        disposeTree(r) ;
        dispose i ;
        dispose (i + 1)
```

The specification, for every tree value $\tau$, is $\{\mathsf{tree}\ \tau\ (i)\}\ \mathtt{disposeTree}(i)\ \{\mathsf{emp}\}$. The proof uses the usual rule for recursive procedures, and it assumes the specification for the calls while proving the body. For total correctness you do the induction explicitly on $\tau$.

If $i = \mathit{nil}$: since $i$ is not a location, $\tau = \mathit{leaf}$, and the heap is empty. The implicit else branch is skip, and the postcondition holds.

If $i \neq \mathit{nil}$: since $\mathsf{tree}\ \mathit{leaf}\ (i)$ requires $i = \mathit{nil}$, $\tau = \mathit{node}\ \tau_1\ \tau_2$.

```
{ tree (node τ1 τ2) (i) ∧ i ≠ nil }
{ ∃l',r'. i ↦ l',r' ∗ tree τ1 (l') ∗ tree τ2 (r') }
l := [i] ;
r := [i + 1] ;
{ i ↦ l,r ∗ tree τ1 (l) ∗ tree τ2 (r) }
disposeTree(l) ;     hypothesis on tree τ1 (l), frame  i ↦ l,r ∗ tree τ2 (r)
{ i ↦ l,r ∗ emp ∗ tree τ2 (r) }
disposeTree(r) ;     hypothesis on tree τ2 (r), frame  i ↦ l,r
{ i ↦ l,r }
dispose i ;          small axiom, frame i+1 ↦ r
{ i+1 ↦ r }
dispose (i + 1)
{ emp }
```

The frame rule applies to the calls because the local variables $l$ and $r$ in the frame belong to the caller, and because a call modifies only its own locals. In a classical proof, the first recursive call's specification would need to state that it leaves the right subtree alone. Here that statement is unnecessary, since no such cell appears in its precondition.

The executions of the list programs in these examples, and the laws of the Assertions section, were tested on concrete heaps and by exhaustive enumeration over small heaps, respectively. The hand proofs themselves were not mechanically checked.

## Common mistakes

1. Reading $x \mapsto 3$ as a claim that the heap contains that cell among others. It says the heap is exactly one cell. Use $x \hookrightarrow 3$ for the weaker meaning. A precondition written with $\mapsto$ does not exclude larger global heaps, because the frame rule adds them.
2. Assuming $p * q \to p$ because it holds for $\land$. If it held, you could silently discard memory and lose track of a leak. In classical separation logic it fails. So $\{x \mapsto -\}\ \mathtt{skip}\ \{\mathsf{emp}\}$ is false.
3. Applying the frame rule when the command modifies a variable free in the frame. From $\{\mathsf{emp}\}\ x := 1\ \{\mathsf{emp}\}$ you cannot frame $x = 0$.
4. Trying to read a cell through a precondition that does not own it. $\{x = y\}\ z := [x]\ \{\ldots\}$ fails fault avoidance. You need $x \mapsto v$ or $x \hookrightarrow v$ in the precondition.
5. Using $\land$ for two heap facts when you mean $*$. $x \mapsto 1 \land y \mapsto 2$ is true only of a one-cell heap, so it forces $x = y$ and $1 = 2$, which is a contradiction.
6. Assuming that $\mathsf{list}\ \alpha\ (i, i)$ means an empty list. A cyclic segment also satisfies it.
7. Forgetting existentials on an unfolded predicate. After unfolding, the next pointer is a new existential variable, and it has to be matched to a program variable by a lookup.
8. Believing every assertion is precise. Precision fails for $\top$ and for $\mathsf{emp} \lor x \mapsto -$, and even $x \hookrightarrow v$ is not precise. Precision matters for [Concurrent Separation Logic](../concurrent-separation-logic/).
9. Assuming the logic proves total correctness because it proves fault avoidance. A triple in curly brackets still allows divergence.

## Exercises

### Exercise 1

Let $s(x) = 1$ and $s(y) = 2$, and let $h = \{1 \mapsto 2,\ 2 \mapsto 1\}$. For each assertion, decide whether $s, h$ satisfies it.

(a) $x \mapsto y * y \mapsto x$

(b) $x \mapsto y$

(c) $x \hookrightarrow y \land y \hookrightarrow x$

(d) $x \mapsto y \land y \mapsto x$

(e) $x \mapsto y, x$

(f) $x \mapsto - * x \mapsto -$

(g) $\top * x \mapsto y$

<details><summary>Solution</summary>

(a) True. Split into $\{1 \mapsto 2\}$ and $\{2 \mapsto 1\}$.

(b) False. The heap has two cells.

(c) True. Each contains the required cell, with the other cell in the $\top$ part.

(d) False. Each conjunct demands a one-cell heap, and the two disagree on the location.

(e) True. It abbreviates $x \mapsto y * (x + 1) \mapsto x$, and $x + 1 = 2$, which holds $1 = x$.

(f) False. Two disjoint heaps cannot both have location $1$ in their domain.

(g) True. Split into $\{2 \mapsto 1\}$ for $\top$ and $\{1 \mapsto 2\}$ for $x \mapsto y$.

</details>

### Exercise 2

Decide which are valid. Give a proof or a counterexample.

(a) $p * q \to p$

(b) $x \mapsto 1 * y \mapsto 2 \to x \neq y$

(c) $p \land q \to p * q$

(d) $p * (p \mathbin{-\!\!*} q) \to q$

(e) $q \to p \mathbin{-\!\!*} (p * q)$

(f) $\mathsf{emp} * p \leftrightarrow p$

<details><summary>Solution</summary>

(a) Invalid. Take $p \equiv \mathsf{emp}$ and $q \equiv x \mapsto 1$. A one-cell heap satisfies $p * q$ and does not satisfy $p$.

(b) Valid. The two parts have disjoint domains $\{[\![x]\!]s\}$ and $\{[\![y]\!]s\}$, so the addresses differ. In addition, for this example, their stored values differ, but only the domains are needed.

(c) Invalid. Take $p \equiv q \equiv x \mapsto 1$. The one-cell heap satisfies $p \land q$. But $p * q$ is unsatisfiable.

(d) Valid. Let $h = h_1 \cdot h_2$ with $s, h_1 \models p$ and $s, h_2 \models p \mathbin{-\!\!*} q$. Applying the wand on $h_2$ to the extension $h_1$ gives $s, h_2 \cdot h_1 \models q$.

(e) Valid. Let $s, h \models q$, and let $h' \perp h$ with $s, h' \models p$. Then $h \cdot h'$ splits as required for $p * q$.

(f) Valid. $h_1$ must be empty, so $h_2 = h$.

</details>

### Exercise 3

(a) Show why the rule of constancy fails on the heap, using $\{x \mapsto -\}\ [x] := 4\ \{x \mapsto 4\}$.

(b) Show how the frame rule avoids the problem.

(c) Show why the side condition on variables is needed.

<details><summary>Solution</summary>

(a) Using it with $r \equiv y \mapsto 3$ would give $\{x \mapsto - \land y \mapsto 3\}\ [x] := 4\ \{x \mapsto 4 \land y \mapsto 3\}$. The precondition forces $x = y$ and the value $3$ in the single cell. After the command, $y \mapsto 4$ holds and $y \mapsto 3$ fails.

(b) The frame rule gives $\{x \mapsto - * y \mapsto 3\}\ [x] := 4\ \{x \mapsto 4 * y \mapsto 3\}$. The separating conjunction in the precondition excludes $x = y$, so the triple is valid.

(c) From $\{\mathsf{emp}\}\ x := 1\ \{\mathsf{emp}\}$, framing $x = 0$ would give $\{x = 0\}\ x := 1\ \{x = 0\}$, which is false. The separating conjunction only separates heaps. Store variables are not separated by it, so the side condition handles them.

</details>

### Exercise 4

(a) Derive the global mutation rule from the small axiom.

(b) Derive the backward rule for mutation.

(c) Derive the small axiom from the backward rule.

<details><summary>Solution</summary>

(a) Apply the frame rule with frame $r$. Mutation modifies no variables, so the side condition is trivial.

(b) In (a) take $r \equiv (e \mapsto e') \mathbin{-\!\!*} q$. The rule gives $\{(e \mapsto -) * r\}\ [e] := e'\ \{(e \mapsto e') * r\}$. Since $(e \mapsto e') * ((e \mapsto e') \mathbin{-\!\!*} q) \to q$ is valid, consequence gives $\{(e \mapsto -) * r\}\ [e] := e'\ \{q\}$.

(c) Take $q \equiv e \mapsto e'$ in the backward rule. The precondition is $(e \mapsto -) * ((e \mapsto e') \mathbin{-\!\!*} (e \mapsto e'))$. Since $\mathsf{emp} \to ((e \mapsto e') \mathbin{-\!\!*} (e \mapsto e'))$ is valid, by the adjunction, $(e \mapsto -) \to (e \mapsto -) * \mathsf{emp}$ gives $(e \mapsto -) \to$ the precondition, by monotonicity. Consequence gives the small axiom.

</details>

### Exercise 5

Prove the following specification for deleting the first node of a list, where the program variable $i$ initially points to the list and $j$ is fresh.

```
{ list (a·α) (i, k) }
j := [i + 1] ;
dispose i ;
dispose (i + 1) ;
i := j
{ list α (i, k) }
```

<details><summary>Solution</summary>

```
{ list (a·α) (i, k) }
{ ∃j'. i ↦ a,j' ∗ list α (j', k) }
{ ∃j'. i ↦ a ∗ i+1 ↦ j' ∗ list α (j', k) }
j := [i + 1] ;        lookup, frame i ↦ a ∗ list α (j', k)
{ i ↦ a ∗ i+1 ↦ j ∗ list α (j, k) }
dispose i ;           small axiom, frame i+1 ↦ j ∗ list α (j, k)
{ i+1 ↦ j ∗ list α (j, k) }
dispose (i + 1) ;     small axiom, frame list α (j, k)
{ list α (j, k) }
i := j
{ list α (i, k) }
```

The existential over $j'$ is removed by the auxiliary variable rule with the lookup's result, since $j = j'$ holds afterwards and $j$ is not free in the frame. This assumes that $k$ is distinct from $j$ and $i$.

</details>

### Exercise 6

Prove by induction on $\alpha$: $\mathsf{list}\ (\alpha \cdot \beta)\ (i, k) \leftrightarrow \exists j.\ \mathsf{list}\ \alpha\ (i, j) * \mathsf{list}\ \beta\ (j, k)$.

<details><summary>Solution</summary>

Case $\alpha = \epsilon$. The right side is $\exists j.\ (\mathsf{emp} \land i = j) * \mathsf{list}\ \beta\ (j, k)$. This is $\exists j.\ i = j \land \mathsf{list}\ \beta\ (j, k)$, using the law for pure facts and $\mathsf{emp}$ as unit, and equality elimination gives $\mathsf{list}\ \beta\ (i, k)$, the left side.

Case $\alpha = a \cdot \alpha'$. The left side unfolds:

$$\mathsf{list}\ (a \cdot \alpha' \cdot \beta)\ (i, k) \leftrightarrow \exists m.\ i \mapsto a, m * \mathsf{list}\ (\alpha' \cdot \beta)\ (m, k).$$

By the induction hypothesis on $\alpha'$, this is equivalent to

$$\exists m.\ i \mapsto a, m * \exists j.\ \mathsf{list}\ \alpha'\ (m, j) * \mathsf{list}\ \beta\ (j, k).$$

Moving the existential out, using associativity and folding gives

$$\exists j.\ \big(\exists m.\ i \mapsto a, m * \mathsf{list}\ \alpha'\ (m, j)\big) * \mathsf{list}\ \beta\ (j, k) \ \leftrightarrow\ \exists j.\ \mathsf{list}\ (a \cdot \alpha')\ (i, j) * \mathsf{list}\ \beta\ (j, k).$$

</details>

### Exercise 7

Find an invariant and prove this in-place list append, in which the first list is nonempty.

```
{ list (a0·α0) (x, nil) ∗ list β (y, nil) }
t := x ;
k := [t + 1] ;
while k ≠ nil do ( t := k ; k := [t + 1] ) ;
[t + 1] := y
{ list (a0·α0·β) (x, nil) }
```

<details><summary>Solution</summary>

The loop walks along the list, and $t$ is the last node seen, with $k$ its successor. Let $\sigma \equiv a_0 \cdot \alpha_0$. The invariant is

$$I \ \equiv\ \exists \alpha_1, a, \alpha_2.\ \sigma = \alpha_1 \cdot a \cdot \alpha_2 \land \mathsf{list}\ \alpha_1\ (x, t) * t \mapsto a, k * \mathsf{list}\ \alpha_2\ (k, \mathit{nil}) * \mathsf{list}\ \beta\ (y, \mathit{nil}).$$

Initiation. After $t := x$, unfold the first list: $\exists k'.\ t \mapsto a_0, k' * \mathsf{list}\ \alpha_0\ (k', \mathit{nil})$. The lookup sets $k = k'$. Take $\alpha_1 := \epsilon$, $a := a_0$, $\alpha_2 := \alpha_0$, with $\mathsf{list}\ \epsilon\ (x, t)$ true since $x = t$ and $\mathsf{emp}$.

Preservation. From $I$ and $k \neq \mathit{nil}$, the sequence $\alpha_2$ is nonempty. Write $\alpha_2 = b \cdot \alpha_2'$, and unfold:

```
{ σ = α1·a·b·α2' ∧ list α1 (x, t) ∗ t ↦ a,k ∗ k ↦ b,k' ∗ list α2' (k', nil) ∗ list β (y, nil) }

  Fold with the lemma list (α·b) (i, k) ↔ ∃j. list α (i, j) ∗ j ↦ b, k:
  list α1 (x, t) ∗ t ↦ a,k  →  list (α1·a) (x, k)

{ σ = (α1·a)·b·α2' ∧ list (α1·a) (x, k) ∗ k ↦ b,k' ∗ list α2' (k', nil) ∗ list β (y, nil) }
t := k ;
{ σ = (α1·a)·b·α2' ∧ list (α1·a) (x, t) ∗ t ↦ b,k' ∗ list α2' (k', nil) ∗ list β (y, nil) }
k := [t + 1]
{ σ = (α1·a)·b·α2' ∧ list (α1·a) (x, t) ∗ t ↦ b,k ∗ list α2' (k, nil) ∗ list β (y, nil) }
```

This is $I$ with $\alpha_1 := \alpha_1 \cdot a$, $a := b$ and $\alpha_2 := \alpha_2'$.

Exit. $I \land k = \mathit{nil}$ gives $\alpha_2 = \epsilon$ and the list from $k$ is $\mathsf{emp}$. So $\sigma = \alpha_1 \cdot a$.

```
{ σ = α1·a ∧ list α1 (x, t) ∗ t ↦ a,nil ∗ list β (y, nil) }
[t + 1] := y
{ σ = α1·a ∧ list α1 (x, t) ∗ t ↦ a,y ∗ list β (y, nil) }
{ list (α1·a) (x, y) ∗ list β (y, nil) }     fold with the lemma
{ list (σ·β) (x, nil) }                      composition lemma
```

</details>

### Exercise 8

Prove partial and total correctness of list disposal.

```
{ list α (i, nil) }
while i ≠ nil do ( k := [i + 1] ; dispose i ; dispose (i + 1) ; i := k )
{ emp }
```

<details><summary>Solution</summary>

Take the invariant $I \equiv \exists \alpha.\ \mathsf{list}\ \alpha\ (i, \mathit{nil})$, which contains no heap other than the list.

Preservation.

```
{ ∃α. list α (i, nil) ∧ i ≠ nil }
{ ∃a,α',k'. i ↦ a ∗ i+1 ↦ k' ∗ list α' (k', nil) }
k := [i + 1] ;
{ ∃a,α'. i ↦ a ∗ i+1 ↦ k ∗ list α' (k, nil) }
dispose i ;
{ ∃α'. i+1 ↦ k ∗ list α' (k, nil) }
dispose (i + 1) ;
{ ∃α'. list α' (k, nil) }
i := k
{ ∃α'. list α' (i, nil) }
```

Exit. $i = \mathit{nil}$ forces the list to be empty, by the lemma, and so $\mathsf{emp}$.

Termination. Since the specification should show termination for a particular $\alpha$, use the invariant $\exists \alpha.\ \mathsf{list}\ \alpha\ (i, \mathit{nil}) \land |\alpha| = m$ with the logical variable $m$, and let the variant be $m$. Each iteration moves from length $m$ to length $m - 1$. For a precise presentation, the loop rule needs the variant as a function of the state, so define $t$ as the length of the unique list from $i$ to $\mathit{nil}$ in the current heap. The list predicate ensures it exists and is unique.

</details>

### Exercise 9

(a) Show that $(p_1 * q) \land (p_2 * q) \to (p_1 \land p_2) * q$ fails for imprecise $q$.

(b) Prove it for precise $q$.

<details><summary>Solution</summary>

(a) Take $q \equiv \top$, $p_1 \equiv 1 \mapsto 1$ and $p_2 \equiv 2 \mapsto 1$. The heap $\{1 \mapsto 1,\ 2 \mapsto 1\}$ satisfies both $p_1 * \top$ and $p_2 * \top$. But $p_1 \land p_2$ is unsatisfiable, so the right side is false.

(b) Assume $s, h \models (p_1 * q) \land (p_2 * q)$. There are splits $h = h_1 \cdot h_1'$ with $s, h_1 \models p_1$ and $s, h_1' \models q$, and $h = h_2 \cdot h_2'$ with $s, h_2 \models p_2$ and $s, h_2' \models q$. Both $h_1'$ and $h_2'$ are subheaps of $h$ satisfying $q$. By precision they are equal, so $h_1 = h_2$, since each is the complement in $h$ of the same subheap. So $s, h_1 \models p_1 \land p_2$, and $h = h_1 \cdot h_1'$ satisfies $(p_1 \land p_2) * q$.

</details>

### Exercise 10

Extend the language with a test `x := allocated(e)`, setting $x$ to $1$ if $[\![e]\!]s \in \mathrm{dom}(h)$ and to $0$ otherwise, without faulting. Show that the frame rule becomes unsound. Identify which semantic property fails.

<details><summary>Solution</summary>

From $\{\mathsf{emp}\}\ x := \mathtt{allocated}(10)\ \{x = 0 \land \mathsf{emp}\}$, which is valid, framing with $10 \mapsto -$ would give $\{10 \mapsto -\}\ x := \mathtt{allocated}(10)\ \{(x = 0 \land \mathsf{emp}) * 10 \mapsto -\}$. This is false, since the command then sets $x = 1$. The frame $10 \mapsto -$ has no occurrence of $x$, so the side condition does not block the rule.

The failing property is the frame property. From the larger heap, the command reaches the final store with $x = 1$, while from the smaller heap it cannot abort and it cannot terminate in a state with $x = 1$. So the larger-heap behavior is not explained by a run on the smaller heap. The command observes the absence of a cell, which is outside its footprint.

</details>

### Exercise 11

Solve the frame and bi-abduction problems below, giving the least-informative answer that works in each case.

(a) Find $F$ with $x \mapsto 1 * y \mapsto 2 * z \mapsto 3 \vdash y \mapsto 2 * F$.

(b) Find $A$ and $F$ with $A * (x \mapsto 1) \vdash (x \mapsto - * y \mapsto -) * F$.

(c) A procedure has the specification $\{a \mapsto -\}\ \mathtt{p}(a)\ \{\mathsf{emp}\}$. A caller's state is $u \mapsto 7$, and it calls $\mathtt{p}(v)$ with $u$ and $v$ distinct. State the $A$ and $F$ that an analysis infers.

<details><summary>Solution</summary>

(a) $F \equiv x \mapsto 1 * z \mapsto 3$.

(b) $A \equiv y \mapsto -$ and $F \equiv \mathsf{emp}$. The pre-state has $x \mapsto 1$, which implies $x \mapsto -$, and $y \mapsto -$ must come from $A$.

(c) The call needs $v \mapsto -$. The current state has only $u \mapsto 7$. With distinct $u$ and $v$, the missing piece is $A \equiv v \mapsto -$, and the frame is $F \equiv u \mapsto 7$. The analysis adds $A$ to the inferred precondition of the caller and continues with state $\mathsf{emp} * u \mapsto 7$.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Give the semantics of $\mathsf{emp}$, $\mapsto$, $*$ and $\mathbin{-\!\!*}$, and evaluate assertions on a concrete heap.
- State which laws of $\land$ fail for $*$, with counterexamples.
- Define fault avoidance, and explain its connection to the frame rule.
- Write the frame rule with its side condition and the small axioms from memory.
- Prove the frame rule sound from safety monotonicity and the frame property.
- Define $\mathsf{list}$ and $\mathsf{tree}$, and prove the list composition lemma by induction.
- Give the invariant and proof outline for in-place reversal and for list append with no notes.
- Prove a recursive procedure on trees by framing out the sibling subtree.
- Define precise assertions and give examples and non-examples.

## Materials

- Reynolds, Separation Logic: A Logic for Shared Mutable Data Structures, LICS 2002. Read it for the semantics, the inference rules, the list and tree examples and the decidability summary.
- O'Hearn, Separation logic, CACM 2019. Read it for a survey of the developments since 2002, including concurrency and industrial use.
- O'Hearn, Reynolds and Yang, Local Reasoning about Programs that Alter Data Structures, CSL 2001. Read it for small axioms, the frame rule and the local semantics.
- Ishtiaq and O'Hearn, BI as an Assertion Language for Mutable Data Structures, POPL 2001. Read it for the connection with bunched implications and for the backward rules.
- Burstall, Some Techniques for Proving Correctness of Programs Which Alter Data Structures, Machine Intelligence 1972. Read it for the historical origin of the idea of disjoint pieces.
- Berdine, Calcagno and O'Hearn, Smallfoot: Modular Automatic Assertion Checking with Separation Logic, FMCO 2005. Read it for frame inference and symbolic execution.
- Calcagno, Distefano, O'Hearn and Yang, Compositional Shape Analysis by Means of Bi-Abduction, POPL 2009. Read it for how specifications are inferred bottom-up.
