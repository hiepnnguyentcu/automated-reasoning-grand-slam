# Decidable Fragments

Part 1, Chapter 2: Decidability and Complexity.

## Objective

Identify decidable logical fragments, including Presburger arithmetic and effectively propositional logic, and their complexity.

## Why this matters

Since first-order validity is undecidable, practical reasoning tools succeed by recognizing or engineering a formula in a decidable fragment. The [SMT theories](../../../part-2-core-reasoning/05-smt/) for [arithmetic](../../../part-2-core-reasoning/05-smt/arithmetic/), [arrays](../../../part-2-core-reasoning/05-smt/arrays/), [bit-vectors](../../../part-2-core-reasoning/05-smt/bit-vectors/) and [strings](../../../part-2-core-reasoning/05-smt/strings/) are all defined by such boundaries, and protocol verifiers keep their verification conditions in effectively propositional logic so that a solver can always answer. An applied scientist must be able to look at a specification language and say whether it stays inside a decidable fragment, what the worst-case cost is, and what small change would break that guarantee.

## Prerequisites

- [Undecidability of Logic and Incompleteness](../undecidability-of-logic-and-incompleteness/), for the outer limits.
- [Normal Forms and Skolemization](../../01-mathematical-logic/normal-forms-and-skolemization/), for prenex form and Skolem functions.
- [First-Order Metatheory](../../01-mathematical-logic/first-order-metatheory/), for Herbrand's theorem.
- [First-Order Theories](../../01-mathematical-logic/first-order-theories/), for theories and quantifier elimination.
- [Reductions and NP-Completeness](../reductions-and-np-completeness/) and [Space and the Polynomial Hierarchy](../space-and-the-polynomial-hierarchy/), for complexity classes.

## Lesson

### Ways to obtain decidability

Four standard techniques establish decidability, and each suggests a kind of algorithm.

- Finite model property. If each satisfiable sentence in a class has a finite model, then the class is decidable, as shown below. The algorithm is a search for a model, which can be turned into grounding and SAT solving.
- Quantifier elimination. If each formula is equivalent to a quantifier-free one, and quantifier-free sentences can be evaluated, then the theory is decidable. Cooper's algorithm and cylindrical algebraic decomposition are of this kind.
- Reduction to automata. The models of a formula are encoded as words or trees, and the formula becomes an automaton. Presburger arithmetic and monadic second-order logic of one successor can be treated this way.
- Bounded instantiation. A universal quantifier needs only finitely many instances. EPR and the array property fragment work this way.

Theorem. Let $\mathcal{C}$ be a decidable class of first-order sentences with the finite model property. Then satisfiability for $\mathcal{C}$ is decidable.

Proof. Run two searches in alternation on input $\sigma \in \mathcal{C}$. One enumerates finite structures for the signature of $\sigma$ and checks each with direct evaluation. The other enumerates proofs of $\neg \sigma$. If $\sigma$ is satisfiable, then the first search succeeds by the finite model property. If it is unsatisfiable, then the second search succeeds by Gödel's completeness theorem. $\square$

A bound on model size gives more: the sentence can be decided in a known time bound by guessing a structure of bounded size. The bound often yields the exact complexity.

### Effectively propositional logic

Effectively propositional logic (EPR), also called the Bernays-Schönfinkel-Ramsey class, consists of sentences of the form

$$
\exists y_1 \cdots \exists y_m\, \forall x_1 \cdots \forall x_k\, \psi,
$$

where $\psi$ is quantifier-free and the signature has only relation symbols and constants, with no function symbols of positive arity. Equality is allowed.

Why it is named so: Skolemizing the prefix replaces each $y_i$ by a constant, and it introduces no function. The Herbrand universe is then the finite set of constants, so grounding yields a finite propositional problem.

Theorem. An EPR sentence with $m \ge 1$ existential variables and $c$ constants is satisfiable if and only if it has a model with at most $m + c$ elements. If $m + c = 0$, one element suffices.

Proof. Let $\mathcal{A} \models \sigma$. Choose witnesses $a_1, \dots, a_m$ for the existential variables, and let $B$ be the set containing these witnesses and the constants' interpretations, or a single element if that set would be empty. Let $\mathcal{B}$ be the substructure of $\mathcal{A}$ on $B$. There are no functions, so $B$ is closed under the signature. The quantifier-free part of $\psi$ has the same truth value in $\mathcal{A}$ and $\mathcal{B}$ on elements of $B$, and universal statements are preserved by passing to a substructure. So $\mathcal{B} \models \forall \bar{x}\, \psi[\bar{y} := \bar{a}]$, and thus $\mathcal{B} \models \sigma$. $\square$

Decision procedure for a sentence without equality.

```
replace y1, ..., ym by new constants, and let U be the set of all constants
    (if U is empty, add one constant)
for each tuple (u1, ..., uk) in U^k:
    add the clauses of psi[x1 := u1, ..., xk := uk]
call a SAT solver with each ground atom as a propositional variable
```

The number of ground instances is $|U|^k$. That is exponential in $k$, which is the cost of the fragment. With equality, ground atoms $u = v$ are handled as well by equality axioms over the finite set, by congruence closure, or with an SMT solver.

Theorem (Lewis, 1980). EPR satisfiability is NEXPTIME-complete.

Membership. Guess a structure on at most $m + c$ elements, with a table for each relation. The table for a relation of arity $r$ has $(m + c)^r$ entries, which is at most exponential in the input. Check all $(m + c)^{k}$ assignments to the universal variables, which takes exponential time in the input.

Hardness proof sketch. Reduce from the square tiling problem. An instance has a finite set $C$ of tile types, horizontal and vertical compatibility relations $H, V \subseteq C \times C$, a row prefix $w$ and a number $n$ in unary. The question is whether a square of side $2^n$ has a tiling with $w$ at the start of the first row, and this problem is NEXPTIME-complete. Use two constants for bits, $\mathsf{0}$ and $\mathsf{1}$, with $\mathsf{0} \ne \mathsf{1}$. For each tile $c$, use a predicate $T_c(\bar{x}, \bar{y})$ with $2n$ arguments, where $\bar{x}$ and $\bar{y}$ are $n$-bit coordinates. All universal variables are guarded by the predicate $x = \mathsf{0} \lor x = \mathsf{1}$, so that models with extra elements do not matter. The sentence has one existential block and states the following, for all coordinates.

- Each position has exactly one tile.
- If $\mathrm{Succ}(\bar{x}, \bar{x}')$, then the tiles at $(\bar{x}, \bar{y})$ and $(\bar{x}', \bar{y})$ are in $H$.
- If $\mathrm{Succ}(\bar{y}, \bar{y}')$, then the tiles at $(\bar{x}, \bar{y})$ and $(\bar{x}, \bar{y}')$ are in $V$.
- The prefix tiles are given as ground atoms.

Here $\mathrm{Succ}$ is a polynomial-size quantifier-free formula for binary increment. It says that for some bit position $i$, higher bits agree, bit $i$ changes from $\mathsf{0}$ to $\mathsf{1}$, and all lower bits change from $\mathsf{1}$ to $\mathsf{0}$. The sentence has polynomial size, and a model on the bits is a tiling. $\square$

The direction of a query matters. Validity of a sentence of the form $\forall^* \exists^*$ reduces to unsatisfiability of its negation, which is in $\exists^* \forall^*$. So $\forall^* \exists^*$ validity is decidable, and it is coNEXPTIME-complete.

EPR is used in protocol verification. A candidate invariant in universal form, $\mathit{Inv}$, and a transition relation in $\exists^* \forall^*$ form, give a verification condition $\mathit{Inv}(s) \land T(s, s') \land \neg \mathit{Inv}(s')$ in EPR. Tools in the style of Ivy rely on this: the check always terminates, and failures come with finite counterexamples that a person can inspect. Many-sorted EPR extends the fragment by allowing functions between sorts, provided the graph of sorts has no cycle, because then the set of ground terms remains finite. Exercise 12 works through this approach.

A single function symbol can break the fragment. The clause set in the [PCP reduction](../undecidability-of-logic-and-incompleteness/) has only universal variables and unary functions, and it encodes an undecidable problem.

### The monadic class

The monadic class allows only unary relation symbols, with no functions, and arbitrary quantifier prefixes. It is the logic of Aristotelian syllogisms.

Theorem (Löwenheim, 1915). A monadic sentence without equality, with $k$ predicates, that is satisfiable has a model with at most $2^k$ elements.

Proof. Let $\mathcal{A} \models \sigma$. The type of an element $a$ is the set of predicates it satisfies, so there are at most $2^k$ types. Define $\mathcal{B}$ with one element for each realized type, where the element satisfies exactly the predicates in its type. Let $h : A \to B$ map each element to its type. Prove by induction on $\chi$ that, for each assignment $\beta$ into $A$, $\mathcal{A}, \beta \models \chi$ if and only if $\mathcal{B}, h \circ \beta \models \chi$. Atoms hold by definition. Boolean cases are immediate. For $\exists x\, \chi$, a witness in $A$ maps to a witness in $B$ by $h$, and each element of $B$ has a preimage in $A$, since it is a realized type. $\square$

With equality, an element can be distinguished from others by counting. The bound becomes $q \cdot 2^k$, where $q$ is the number of variables in the sentence, because a sentence with $q$ variables can distinguish multiplicities only up to $q$. The monadic class is NEXPTIME-complete, by Lewis (1980).

A binary predicate brings undecidability, by Kalmár's result. The boundary between monadic and dyadic logic is sharp.

### Prefix classes and other fragments

The classical classification by Börger, Grädel and Gurevich resolves the decision problem for classes defined by prefix and signature. The following table lists the classes most relevant to automated reasoning, for relational signatures.

| Class | Prefix or restriction | Decidability | Complexity |
|---|---|---|---|
| EPR | $\exists^* \forall^*$, with equality | Decidable. | NEXPTIME-complete. |
| Ackermann | $\exists^* \forall \exists^*$ | Decidable. | EXPTIME-complete. |
| Gödel-Kalmár-Schütte | $\exists^* \forall^2 \exists^*$, without equality | Decidable. | NEXPTIME-complete. |
| Gödel with equality | $\forall^2 \exists$, with equality | Undecidable, by Goldfarb. | Not applicable. |
| Kahr-Moore-Wang | $\forall \exists \forall$ | Undecidable. | Not applicable. |
| Surányi | $\forall^3 \exists$ | Undecidable. | Not applicable. |
| Monadic | Unary predicates, with equality | Decidable. | NEXPTIME-complete. |
| Two-variable logic FO$^2$ | Any formula using only two variables, with equality | Decidable, with the finite model property. | NEXPTIME-complete, by Grädel, Kolaitis and Vardi. |
| Three-variable logic FO$^3$ | Any formula using only three variables | Undecidable. | Not applicable. |
| Guarded fragment | Quantifiers relativized by a guard atom | Decidable, with the finite model property. | 2EXPTIME-complete in general, by Grädel. |
| Modal logic K | The propositional modal language | Decidable. | PSPACE-complete, by Ladner. |
| Description logic ALC | Concept satisfiability with no axioms | Decidable. | PSPACE-complete. |

Three points deserve attention.

The two-variable logic can translate modal logic, so it gives a first-order explanation for why modal logics are decidable. The standard translation sends a modal formula to a formula with one free variable, by $\mathrm{ST}_x(\square \varphi) = \forall y\, (R(x, y) \to \mathrm{ST}_y(\varphi))$, and variables can be reused to keep only $x$ and $y$. Transitivity needs three variables, and the sentence with only infinite models in the previous topic uses that.

The guarded fragment explains why adding bounded quantification to modal logic remains decidable. In it, a quantifier has the form $\forall \bar{y}\, (\alpha(\bar{x}, \bar{y}) \to \varphi)$, where the guard $\alpha$ is an atom containing all free variables of $\varphi$. Verification conditions rarely fit the guarded fragment directly, but the principle of a bounded search through related elements reappears in decision procedures.

The prefix results mean that the same predicate language can be decidable or not, depending only on quantifier order. This is why you should compute the prefix after Skolemization when you check a query against a fragment.

### Presburger arithmetic

Presburger arithmetic is the first-order theory of $(\mathbb{N}, 0, 1, +, =, <)$, or of the same structure over $\mathbb{Z}$. Multiplication by a constant is available as repeated addition, and multiplication of two variables is not. In 1929, Presburger proved that the theory is complete and decidable, by quantifier elimination.

Elimination requires additional predicates. The formula $\exists x\, (2x = y)$ has no quantifier-free equivalent in the language without divisibility, since it defines the even numbers. Add a predicate $k \mid t$ for each positive integer constant $k$.

Cooper's algorithm (1972) eliminates a single $\exists x$ from a quantifier-free formula, working over $\mathbb{Z}$.

Step 1. Put the formula in negation normal form, and rewrite all atoms to use only $<$ and divisibility.

$$
s \le t \mapsto s < t + 1, \quad s = t \mapsto s < t + 1 \land t < s + 1, \quad \neg (s < t) \mapsto t < s + 1,
$$

$$
\neg (k \mid t) \mapsto \bigvee_{i=1}^{k-1} k \mid t + i.
$$

Step 2. Collect the coefficient of $x$ in each atom, so that each atom has one of the forms $c x < a$, $b < c x$ or $k \mid c x + t$, with $c > 0$ and with $a, b, t$ free of $x$.

Step 3. Let $\delta$ be the least common multiple of all coefficients $c$. Multiply each atom so that the coefficient of $x$ is $\delta$. A divisibility atom $k \mid c x + t$ becomes $k (\delta / c) \mid \delta x + (\delta / c) t$. Replace $\delta x$ by a new variable $x'$, and add the conjunct $\delta \mid x'$. The result is $\varphi(x')$, whose atoms have the forms $x' < a$, $b < x'$ and $k \mid x' + t$.

Step 4. Let $m$ be the least common multiple of the divisors $k$ in $\varphi$. Let $B$ be the set of terms $b$ that occur in lower-bound atoms $b < x'$. Let $\varphi_{-\infty}$ be $\varphi$ with each $x' < a$ replaced by $\top$ and each $b < x'$ replaced by $\bot$. The result is

$$
\exists x'\, \varphi(x') \iff \bigvee_{j=1}^{m} \varphi_{-\infty}[j] \lor \bigvee_{j=1}^{m} \bigvee_{b \in B} \varphi[b + j].
$$

Theorem (correctness of the last step). The displayed equivalence holds over $\mathbb{Z}$.

Proof. Right to left. Each disjunct $\varphi[b + j]$ directly provides a witness. For a disjunct $\varphi_{-\infty}[j]$, note that $\varphi_{-\infty}$ contains only divisibility atoms in $x'$, so its truth value is periodic in $x'$ with period $m$. For a sufficiently large $l$, $x' = j - l m$ lies below all terms $a$ and $b$, so that $\varphi$ and $\varphi_{-\infty}$ agree at this value. So $\varphi[j - l m]$ holds.

Left to right. Suppose $\varphi[x_0]$ holds. If $\varphi[x_0 - l m]$ holds for all $l \ge 0$, then for a large $l$, $\varphi_{-\infty}[x_0 - l m]$ holds as well, and by periodicity, $\varphi_{-\infty}[j]$ holds for the $j \in \{1, \dots, m\}$ that is congruent to $x_0$ modulo $m$.

Otherwise, there is $x_1$ with $\varphi[x_1]$ true and $\varphi[x_1 - m]$ false. Since $\varphi$ is in negation normal form, it is monotone in its atoms. So some atom true at $x_1$ is false at $x_1 - m$. Divisibility atoms have the same value at both points, and an atom $x' < a$ true at $x_1$ remains true at $x_1 - m$. So the atom is $b < x'$, with $b < x_1$ and $x_1 - m \le b$. Thus $x_1 = b + j$ with $1 \le j \le m$, and the disjunct $\varphi[b + j]$ holds. $\square$

To decide a sentence, eliminate quantifiers from the innermost outward, with $\forall$ treated as $\neg \exists \neg$, and evaluate the resulting closed formula. Exact divisibility and arithmetic on numerals are trivial.

Complexity.

- Upper bound. Oppen (1978) showed that Cooper's procedure runs in deterministic time $2^{2^{2^{O(n)}}}$.
- Lower bound. Fischer and Rabin (1974) showed that any decision procedure needs nondeterministic time $2^{2^{\Omega(n)}}$ on infinitely many inputs.
- Exact classification. Berman (1980) showed that the theory is complete for alternating Turing machines with time $2^{2^{n^{O(1)}}}$ and $O(n)$ alternations.

Existential fragment. The existential fragment is the same as quantifier-free linear integer arithmetic (QF_LIA) satisfiability. It is NP-complete. Hardness is the [reduction from 3-SAT](../reductions-and-np-completeness/). Membership follows from a small-solution theorem: if a system $A x \le b$ of linear integer constraints has an integer solution, then it has one in which each entry has a number of bits polynomial in the size of the system. This goes back to Borosh and Treybig (1976) and Papadimitriou (1981). So a solution can be guessed and verified. Applying Cooper's procedure to existential sentences would not give this bound, and it would use far more resources in the worst case.

The automata-based view. Represent numbers in binary, and read tuples of bits, one column at a time, as letters. Each atom $a_1 x_1 + \dots + a_n x_n \le b$ is recognized by a finite automaton whose state is a bounded carry. Conjunction, disjunction and negation are product and complement, and $\exists$ is projection, with subset construction. This gives an algorithm with a different practical profile, and it was used in tools for arithmetic with bit-level reasoning.

Boundaries. The following extensions are undecidable.

- Adding multiplication of two variables gives true arithmetic, and [its existential fragment is already undecidable](../undecidability-of-logic-and-incompleteness/).
- Adding uninterpreted unary predicates to Presburger arithmetic gives a $\Pi^1_1$-complete validity problem, by Halpern (1991), which is not even recursively enumerable. So quantified LIA with uninterpreted functions has no complete proof procedure at all.

### Real arithmetic

Tarski proved that the first-order theory of the reals with $+, \cdot, <$, real closed fields, has quantifier elimination, and hence that it is decidable. The practical algorithm is cylindrical algebraic decomposition (CAD), by Collins (1975), which takes time doubly exponential in the number of variables. Davenport and Heintz showed that doubly exponential behavior is unavoidable for quantifier elimination. The existential fragment is in PSPACE, by Canny (1988). Its exact class has the name $\exists\mathbb{R}$, which contains NP and lies within PSPACE.

Why reals are easier than integers: the integers are not definable in this structure. Real closed fields cannot represent computation, so Gödel's theorems do not apply. Linear real arithmetic has quantifier elimination by the Fourier-Motzkin method or by Loos-Weispfenning substitution, and it requires at least nondeterministic exponential time, by Fischer and Rabin.

### Quantified fragments with arrays

The theory of arrays with quantifiers becomes undecidable quickly, because arrays with integer indices can encode functions, and thus can encode computations. The array property fragment (Bradley, Manna and Sipma, 2006) keeps the formula decidable, for the common idiom "all indices in this range satisfy this condition."

An array property has the form

$$
\forall i_1 \cdots \forall i_k\, \big(G(\bar{i}) \to V(\bar{i})\big),
$$

where the guard $G$ is a Boolean combination, by conjunction and disjunction, of comparisons between index variables and terms not containing index variables, and the value constraint $V$ uses index variables only as direct reads $a[i_j]$, and never as an array index nested in another read or in arithmetic. The fragment is formed by Boolean combinations of quantifier-free formulas and array properties, in which universal quantifiers occur in positive positions.

The decision procedure removes array writes, picks a finite index set $I$ of all relevant ground index terms, and replaces each universal quantifier with a finite conjunction over $I$. The result is a quantifier-free formula in arrays, index theory and element theory. The instantiation is exponential in the number of quantified variables, and the procedure is in the same spirit as EPR. The restrictions are tight, since without them the formula can force infinite chains. For example, $\forall i\, (a[i] < a[i + 1])$ uses index arithmetic, and no finite instantiation reproduces the requirement for unbounded chains.

### The SMT landscape

The following table summarizes the complexity of standard theories, including both quantifier-free and quantified problems.

| Theory | Quantifier-free satisfiability | With quantifiers |
|---|---|---|
| Equality and uninterpreted functions | NP-complete. | Undecidable, since it contains first-order logic. |
| Difference logic | NP-complete. | Contained in linear arithmetic. |
| Linear real arithmetic | NP-complete. | Decidable by quantifier elimination. |
| Linear integer arithmetic | NP-complete. | Decidable, with a doubly exponential lower bound. |
| Nonlinear real arithmetic | In PSPACE, and $\exists\mathbb{R}$-complete. | Decidable by CAD, with doubly exponential cost. |
| Nonlinear integer arithmetic | Undecidable. | Undecidable. |
| Arrays | NP-complete. | Undecidable in general, with decidable fragments such as array properties. |
| Bit-vectors, with widths in unary | NP-complete. | PSPACE-complete. |
| Bit-vectors, with widths in binary | NEXPTIME-complete. | Decidable, and harder still. |
| Word equations | Decidable, in PSPACE by Plandowski. | Undecidable. |

For strings, a long-standing open problem asks whether word equations with linear length constraints are decidable, and some extensions, such as unrestricted `replaceAll`, are undecidable. So the [strings](../../../part-2-core-reasoning/05-smt/strings/) theory in real solvers has no single complexity class. Before relying on a specific claim, read the current literature for the exact combination of operators.

### Using the classification

| If your problem is | You should expect | A natural algorithm is |
|---|---|---|
| A universal invariant check over relations | Decidability in EPR. | Grounding, or model-based instantiation. |
| Linear integer constraints with Boolean structure | NP-completeness. | DPLL(T) with branch and cut. |
| Linear integer constraints with many alternations | Doubly exponential worst cases. | Cooper's algorithm, or automata, after looking for simplification. |
| Polynomials over the reals with quantifiers | Doubly exponential cost in the number of variables. | CAD, or a method such as virtual substitution when the degree is low. |
| Polynomials over the integers | Undecidability. | Incomplete methods, such as bounding or linearization, or bit-blasting. |
| Fixed-width machine arithmetic | NP-completeness, or PSPACE-completeness with alternation. | Bit-blasting and SAT, or a QBF or counterexample-guided loop. |
| Full first-order logic with functions | Undecidability. | Saturation or instantiation, with a time limit and honest `unknown` results. |

A fragment membership check on a query should come before the choice of engine. Sometimes a change of encoding, such as replacing a function by a relation or a sorted function with an acyclic sort graph, restores a guarantee without weakening the question.

## Worked examples

### Example 1: EPR by grounding

Decide the validity of

$$
\psi = \forall a\, \forall b\, \exists x\, \exists y\, \Big[ \big(P(a) \land \neg P(b) \land \neg R(b, a)\big) \to \big( \neg (R(x, y) \lor R(y, x)) \lor (R(x, y) \land P(x) \land \neg P(y)) \big) \Big].
$$

The prefix is $\forall^* \exists^*$, and there are no functions. So the negation is in EPR.

Step 1. Negate and move the negation in.

$$
\exists a\, \exists b\, \forall x\, \forall y\, \Big[ P(a) \land \neg P(b) \land \neg R(b, a) \land (R(x, y) \lor R(y, x)) \land (\neg R(x, y) \lor \neg P(x) \lor P(y)) \Big].
$$

Step 2. Skolemize. The variables $a, b$ become constants. The Herbrand universe is $\{a, b\}$.

Step 3. Ground. The four instances of $(x, y)$ produce the following clauses, in addition to the units.

```
units:  P(a), not P(b), not R(b,a)
(a,a):  R(a,a) or R(a,a);  not R(a,a) or not P(a) or P(a)
(a,b):  R(a,b) or R(b,a);  not R(a,b) or not P(a) or P(b)
(b,a):  R(b,a) or R(a,b);  not R(b,a) or not P(b) or P(a)
(b,b):  R(b,b) or R(b,b);  not R(b,b) or not P(b) or P(b)
```

Step 4. Solve by unit propagation.

```
R(a,b) or R(b,a), with not R(b,a), gives R(a,b)
not R(a,b) or not P(a) or P(b), with R(a,b), P(a) and not P(b), gives the empty clause
```

So the negation is unsatisfiable and $\psi$ is valid.

Step 5. Show what happens without the requirement $\neg R(b, a)$. A SAT call now finds the model with $P(a)$ true, $P(b)$ false, $R(a, a)$, $R(b, a)$ and $R(b, b)$ true, and $R(a, b)$ false. Read as a structure on two elements, this is a model of the weakened EPR sentence, so the corresponding implication is not valid, and the structure is a finite counterexample. A script enumerated all ground assignments in both cases, and found no models with the unit $\neg R(b, a)$ and exactly this one model without it.

### Example 2: Cooper's algorithm on a parametric formula

Eliminate $x$ from

$$
\exists x\, \big(3 x > y \land 2 x < y + 4 \land 2 \mid x + 1\big).
$$

Step 1. The atoms are $y < 3 x$, $2 x < y + 4$ and $2 \mid x + 1$. They are already in the required form, with no negation.

Step 2. The coefficients of $x$ are 3, 2 and 1.

Step 3. Here $\delta = 6$. Scale each atom to obtain coefficient 6.

- $y < 3 x$ becomes $2 y < 6 x$.
- $2 x < y + 4$ becomes $6 x < 3 y + 12$.
- $2 \mid x + 1$ becomes $12 \mid 6 x + 6$.

Set $x' = 6 x$ and add $6 \mid x'$:

$$
\varphi(x') = 2 y < x' \land x' < 3 y + 12 \land 12 \mid x' + 6 \land 6 \mid x'.
$$

Step 4. The divisors are 12 and 6, so $m = 12$. The lower bound set is $B = \{2 y\}$. The formula $\varphi_{-\infty}$ replaces $2 y < x'$ by $\bot$. Since this is a conjunction, $\varphi_{-\infty}$ is $\bot$, and the first disjunction vanishes.

Step 5. The result is

$$
\bigvee_{j=1}^{12} \big( 2 y < 2 y + j \land 2 y + j < 3 y + 12 \land 12 \mid 2 y + j + 6 \land 6 \mid 2 y + j \big).
$$

Step 6. Simplify. The first atom is true for all $j \ge 1$. The second is equivalent to $j - 12 < y$. The atom $12 \mid 2 y + j + 6$ requires $j$ to be even, so let $j = 2 l$, with $1 \le l \le 6$. Dividing by 2 gives $6 \mid y + l + 3$. This implies $3 \mid y + l$, which is equivalent to $6 \mid 2 y + 2 l$, so the last atom is redundant. The result is

$$
\bigvee_{l=1}^{6} \big( 6 \mid y + l + 3 \land y > 2 l - 12 \big).
$$

Check by hand.

- For $y = 0$, $6 \mid l + 3$ gives $l = 3$. The condition is $0 > -6$, which is true. The witness is $x' = 2 y + 2 l = 6$, so $x = 1$. Check: $3 > 0$, $2 < 4$, and $2 \mid 2$.
- For $y = -4$, $6 \mid l - 1$ gives $l = 1$. The condition is $-4 > -10$, which is true. The witness is $x' = -6$, so $x = -1$. Check: $-3 > -4$, $-2 < 0$, and $2 \mid 0$.
- For $y = -3$, $6 \mid l$ gives $l = 6$. The condition is $-3 > 0$, which is false. So the formula is false, and indeed there is no such odd $x$: $x > -1$ with $2 x < 1$ forces $x = 0$, which is even.

A script compared the original formula, by brute-force search for $x$, with the final formula, for all $y$ from $-200$ to $199$, and the two agreed.

### Example 3: the monadic class by types

Decide the satisfiability of

$$
\sigma = \forall x\, (A(x) \to B(x)) \land \forall x\, (B(x) \to C(x)) \land \exists x\, (A(x) \land \neg C(x)).
$$

There are three predicates, so a model needs at most $2^3 = 8$ types. List the types allowed by the universal parts, where a type is written as the triple of truth values $(A, B, C)$.

```
allowed by A -> B and B -> C:
(0,0,0), (0,0,1), (0,1,1), (1,1,1)
```

The existential conjunct requires a type with $A = 1$ and $C = 0$, and no allowed type has this. So $\sigma$ is unsatisfiable, which corresponds to the syllogism: $A$ implies $C$. This is a finite computation, performed on types instead of elements, and in fact this approach is an algorithm for the monadic class. Each universally quantified conjunct restricts the allowed set of types, and each existential conjunct requires an allowed type with some property. For sentences that are not simple conjunctions of this kind, prenex and normal form transformations yield a similar computation.

## Common mistakes

- Taking EPR by the prefix of the wrong formula. A validity question should be negated first, since the fragment applies to satisfiability, so $\forall^* \exists^*$ queries are the EPR case for validity.
- Ignoring function symbols. An $\exists^* \forall^*$ sentence with a unary function has an infinite Herbrand universe and may encode undecidable problems.
- Ignoring Skolem functions hidden in the middle of a formula. A $\forall\exists$ pattern nested inside a formula gives a Skolem function, so you must compute the prenex shape with the polarity of each quantifier.
- Assuming that decidable means fast. EPR is NEXPTIME-complete, Presburger arithmetic has a doubly exponential lower bound, and these limits are real on adversarial inputs.
- Concluding that Presburger arithmetic has a quantifier-free form without divisibility. The formula $\exists x\, (2 x = y)$ shows that divisibility predicates are required.
- Thinking that Presburger arithmetic allows $x \cdot y$. It allows multiplication only by constants, and a product of two variables breaks decidability.
- Treating real and integer arithmetic alike. Nonlinear real arithmetic is decidable, while nonlinear integer arithmetic is undecidable, and the reason is that the integers are not definable in the real structure.
- Assuming that a fragment is closed under Boolean combination. EPR is not closed under negation, because the negation of an $\exists^* \forall^*$ sentence is $\forall^* \exists^*$.
- Using Cooper's algorithm for a purely existential problem. The existential fragment is in NP, and SMT methods are much more efficient on it.
- Assuming that the array property fragment allows arithmetic on quantified index variables. The restriction on index terms is needed for a finite index set.

## Exercises

### Exercise 1

For each sentence, state whether its satisfiability problem is in EPR, and whether its validity problem reduces to EPR. Assume that no other function symbols are present.

1. $\exists x\, \forall y\, R(x, y)$.
2. $\forall x\, \exists y\, R(x, y)$.
3. $\forall x\, P(f(x))$.
4. $\forall x\, \forall y\, (x = y \lor R(x, y))$.
5. $\forall x\, \exists y\, \forall z\, R(x, y, z)$.

<details><summary>Solution</summary>

1. The sentence has prefix $\exists \forall$, so its satisfiability is in EPR. Its validity reduces to the unsatisfiability of $\forall x\, \exists y\, \neg R(x, y)$, which is not in EPR.
2. The prefix $\forall \exists$ is not EPR for satisfiability. Its validity reduces to the unsatisfiability of $\exists x\, \forall y\, \neg R(x, y)$, which is in EPR.
3. The function symbol $f$ means that it is not in EPR for satisfiability. For validity, the negation is $\exists x\, \neg P(f(x))$, which also contains $f$, so it is not EPR as written. This specific formula is easy, but it is outside the fragment.
4. The prefix $\forall \forall$ has no existential block, and it has no functions, so its satisfiability is in EPR. Its validity reduces to the unsatisfiability of $\exists x\, \exists y\, (x \ne y \land \neg R(x, y))$, which is also in EPR.
5. The prefix $\forall \exists \forall$ is neither EPR nor the negation of EPR. Its satisfiability lies in the class $\forall \exists \forall$, which is undecidable for a suitable signature. The negation has prefix $\exists \forall \exists$, which is in the Ackermann class, so validity of this sentence is decidable. Thus, it is decidable whether this sentence is valid, and the satisfiability class in general is undecidable.

</details>

### Exercise 2

Use grounding to show that the following EPR sentence is unsatisfiable: there are constants $a, b, c$ with $R(a, b)$, $R(b, c)$, $R(c, a)$, the relation $R$ is transitive, and $R$ is irreflexive. Give the number of ground instances before propagation, and the derivation.

<details><summary>Solution</summary>

The Herbrand universe is $\{a, b, c\}$. Transitivity has three universal variables, so it has $3^3 = 27$ ground instances. Irreflexivity has 3 ground instances. There are 3 units, for 33 clauses in total.

Derivation by unit propagation:

```
R(a,b), R(b,c), and transitivity with (a,b,c) give R(a,c)
R(a,c), R(c,a), and transitivity with (a,c,a) give R(a,a)
R(a,a) and irreflexivity give the empty clause
```

A brute-force enumeration over all $2^9$ assignments to the ground atoms of $R$ found no model.

</details>

### Exercise 3

Eliminate the quantifier with Cooper's algorithm: $\exists x\, (2 x = y \land 3 \mid x + 1)$. Show each step.

<details><summary>Solution</summary>

Rewrite the equality: $y < 2 x + 1$ and $2 x < y + 1$, so $y - 1 < 2 x$ and $2 x < y + 1$.

The coefficients of $x$ are 2, 2 and 1, so $\delta = 2$. The divisibility becomes $6 \mid 2 x + 2$. Set $x' = 2 x$ and add $2 \mid x'$.

$$
\varphi(x') = y - 1 < x' \land x' < y + 1 \land 6 \mid x' + 2 \land 2 \mid x'.
$$

Here $m = 6$ and $B = \{y - 1\}$. The formula $\varphi_{-\infty}$ is $\bot$, since it contains a lower bound as a conjunct.

The result is $\bigvee_{j=1}^{6} \varphi[y - 1 + j]$. The term $y - 1 + j$ satisfies $x' < y + 1$ only when $j = 1$, so the disjunction simplifies to $\varphi[y]$:

$$
6 \mid y + 2 \land 2 \mid y.
$$

Since $6 \mid y + 2$ implies that $y$ is even, the result is $6 \mid y + 2$. Check: $y = 4$ has $x = 2$, and $3 \mid 3$. A script confirmed this on $[-100, 99]$.

</details>

### Exercise 4

Eliminate the quantifier: $\exists x\, (y < 2 x \land 2 x < z)$. Explain why divisibility appears.

<details><summary>Solution</summary>

Set $x' = 2 x$ with $2 \mid x'$. The formula is $y < x' \land x' < z \land 2 \mid x'$. Here $m = 2$, $B = \{y\}$, and $\varphi_{-\infty}$ is $\bot$. The result is

$$
(y + 1 < z \land 2 \mid y + 1) \lor (y + 2 < z \land 2 \mid y + 2).
$$

Divisibility appears since the question involves even numbers: the question is whether an even number lies strictly between $y$ and $z$. The first even number above $y$ is $y + 1$ or $y + 2$, depending on the parity of $y$. A script confirmed the result for $y, z$ in $[-30, 29]$.

</details>

### Exercise 5

Prove that a subset of $\mathbb{N}$ definable in Presburger arithmetic is ultimately periodic. Conclude that multiplication of two variables is not definable in Presburger arithmetic.

<details><summary>Solution</summary>

Let $\varphi(x)$ define the set. By quantifier elimination, $\varphi(x)$ is equivalent to a Boolean combination of atoms $c x < d$, $c x > d$ and $k \mid c x + d$, with integer constants. Each atom $c x < d$ or $c x > d$, for $c \ne 0$, has a constant truth value for all $x$ above some bound. Each divisibility atom is periodic in $x$ with period $k$. So, let $N$ exceed all these bounds, and let $M$ be the least common multiple of all the divisors. For $x \ge N$, the truth value of each atom depends only on $x \bmod M$, so the truth value of $\varphi(x)$ does as well. This is ultimate periodicity.

The set of perfect squares is not ultimately periodic, since the gaps between consecutive squares are unbounded while an infinite ultimately periodic set has bounded gaps. If multiplication were definable, say by $\mu(x, y, z)$, then squares would be defined by $\exists y\, \mu(y, y, x)$. So multiplication is not definable.

</details>

### Exercise 6

The small-solution theorem says that a system of linear integer constraints with an integer solution has a solution of polynomial bit length. Use it to prove that QF_LIA satisfiability is in NP, including Boolean structure. Then explain why the theorem does not extend to one quantifier alternation.

<details><summary>Solution</summary>

Membership. The certificate has a truth assignment to the atoms and integer values for the variables. Evaluating is polynomial, so it remains to bound the values. If $\varphi$ is satisfiable, then the set of atoms true in a model forms a conjunction of literals. Negated atoms are also linear constraints, because $\neg (s \le t)$ is $s \ge t + 1$, and a negated equality becomes a choice of strict inequality that is picked by the certificate. The system has size bounded by the size of $\varphi$. By the theorem, it has a solution of polynomial bit length.

No extension to alternation. For the sentence $\exists x\, \forall y\, \psi$, a certificate for $x$ can have polynomial length or longer, depending on the formula, and the $\forall y$ part would need to be checked over all integers, which is not a single polynomial evaluation. The theorem provides a bound for a conjunction of linear constraints only. Moreover, the known lower bounds show that general Presburger sentences have no such short certificates. Certificates for full Presburger arithmetic are necessarily much larger.

</details>

### Exercise 7

Prove that each monadic sentence with equality using $q$ variables and $k$ predicates has a model of size at most $q \cdot 2^k$ if it is satisfiable, assuming the following claim: in a structure, keeping at most $q$ elements from each type preserves truth of sentences with $q$ variables. Then prove the claim for $q = 1$ in the case of one predicate.

<details><summary>Solution</summary>

Size bound. There are at most $2^k$ types. By the claim, keeping at most $q$ elements of each type gives a structure with at most $q \cdot 2^k$ elements that satisfies the same sentences with $q$ variables.

Case $q = 1$, $k = 1$. A sentence with one variable and one predicate $P$ is a Boolean combination of $\exists x\, \chi(x)$ forms, where $\chi$ is built from $P(x)$ and $x = x$. Each such form is equivalent to one of: true, false, "there is an element with $P$" or "there is an element with $\neg P$". Keeping one element per realized type preserves whether each type is realized. So the truth of all such sentences is preserved, and the resulting structure has at most two elements.

</details>

### Exercise 8

Translate the modal formula $\square \lozenge p$ to two-variable first-order logic using the standard translation, and evaluate the result on the structure with worlds $w_1, w_2$, edges $w_1 \to w_2$ and $w_2 \to w_2$, and $p$ true only at $w_2$, at world $w_1$.

<details><summary>Solution</summary>

$\mathrm{ST}_x(\square \lozenge p) = \forall y\, (R(x, y) \to \mathrm{ST}_y(\lozenge p))$, and $\mathrm{ST}_y(\lozenge p) = \exists x\, (R(y, x) \land P(x))$. Thus

$$
\mathrm{ST}_x(\square \lozenge p) = \forall y\, \big(R(x, y) \to \exists x\, (R(y, x) \land P(x))\big).
$$

The inner $\exists x$ rebinds $x$, so only two variables are used.

Evaluation at $x = w_1$. The only $y$ with $R(w_1, y)$ is $y = w_2$. The inner existential at $y = w_2$ has the witness $x = w_2$, since $R(w_2, w_2)$ and $P(w_2)$ hold. So the formula is true at $w_1$.

</details>

### Exercise 9

Using the array property approach, show that this formula is unsatisfiable: the array $a$ is sorted on $[0, n]$, $0 \le l \le u \le n$, and $a[l] > a[u]$. Formally,

$$
\forall i\, \forall j\, (0 \le i \land i \le j \land j \le n \to a[i] \le a[j]) \land 0 \le l \land l \le u \land u \le n \land a[l] > a[u].
$$

Identify the index set you use and which instance you need.

<details><summary>Solution</summary>

The formula is an array property: the guard uses only comparisons between index variables and ground index terms, and the value constraint has direct reads only.

The ground index terms are $0, n, l, u$. So the index set is $I = \{0, n, l, u\}$, and the procedure's full instantiation uses $4^2 = 16$ pairs. In the case of this formula, one instance is enough: $i = l$ and $j = u$ give

$$
0 \le l \land l \le u \land u \le n \to a[l] \le a[u].
$$

The other conjuncts make the premise true, so $a[l] \le a[u]$, which contradicts $a[l] > a[u]$. So the quantifier-free formula is unsatisfiable.

</details>

### Exercise 10

Show that the sentence $\sigma$ from the [previous topic](../undecidability-of-logic-and-incompleteness/), which has only infinite models, has a prefix outside EPR. Explain why any class containing $\sigma$ cannot be decided by the finite model approach. Then state what can still be done with such a class if it is decidable by another method.

<details><summary>Solution</summary>

$\sigma$ has prefix $\forall^3 \exists$. It has an existential quantifier following universal quantifiers, so it is not in $\exists^* \forall^*$. Skolemization produces a function, which makes the Herbrand universe infinite.

A class containing $\sigma$ lacks the finite model property, since $\sigma$ is satisfiable and has no finite model. So the theorem based on finite model search does not apply: the search for a finite model never ends on $\sigma$, and the search for a refutation also never ends.

If a class with some infinite-only sentences is decidable, you need a method that represents infinite models finitely. Examples include automata-based representations, or saturation that terminates on that class. In this particular case, however, the class $\forall^3 \exists$ is undecidable by Surányi's result.

</details>

### Exercise 11

For $n = 2$, write the formula $\mathrm{Succ}(x_2 x_1, x'_2 x'_1)$ used in the proof that EPR is NEXPTIME-hard. Verify it on all pairs of 2-bit numbers.

<details><summary>Solution</summary>

Treat $x_2$ as the high bit. The formula has one disjunct for each position of the changing bit.

$$
\mathrm{Succ} = (x_1 = \mathsf{0} \land x'_1 = \mathsf{1} \land x_2 = x'_2) \lor (x_1 = \mathsf{1} \land x'_1 = \mathsf{0} \land x_2 = \mathsf{0} \land x'_2 = \mathsf{1}).
$$

Check on all values. For $x = 00$, the first disjunct holds only for $x' = 01$. For $x = 01$, the second disjunct holds only for $x' = 10$. For $x = 10$, the first holds only for $x' = 11$. For $x = 11$, the first disjunct needs $x_1 = \mathsf{0}$, and the second needs $x_2 = \mathsf{0}$, so neither holds, and the top value has no successor, as required. All other pairs make both disjuncts false.

The formula is quantifier-free and has size $O(n^2)$ for $n$ bits, so it fits in the polynomial-size reduction.

</details>

### Exercise 12

Consider protocol verification with relations. A candidate invariant is $\mathit{Inv} = \forall \bar{x}\, \alpha$, and a transition relation is $T = \exists \bar{y}\, \forall \bar{z}\, \beta$, both with quantifier-free $\alpha, \beta$ and with no functions. Prove that the check of consecution, $\mathit{Inv}(s) \land T(s, s') \to \mathit{Inv}(s')$, is decidable. Then add a quorum intersection axiom $\forall q_1\, \forall q_2\, \exists n\, (M(n, q_1) \land M(n, q_2))$ with two sorts, nodes and quorums. Explain what happens to the fragment and how a sort discipline saves decidability.

<details><summary>Solution</summary>

Consecution holds if and only if $\mathit{Inv}(s) \land T(s, s') \land \neg \mathit{Inv}(s')$ is unsatisfiable. The conjuncts have these forms.

- $\mathit{Inv}(s)$ has the form $\forall \bar{x}\, \alpha$.
- $T(s, s')$ has the form $\exists \bar{y}\, \forall \bar{z}\, \beta$.
- $\neg \mathit{Inv}(s')$ has the form $\exists \bar{x}'\, \neg \alpha'$.

Moving all existential quantifiers to the front gives an $\exists^* \forall^*$ sentence, since their subformulas do not share variables. So this is EPR, which is decidable, and a failure has a finite counterexample.

With the axiom, the prefix has $\forall \exists$, which Skolemizes to a function $f$ from pairs of quorums to nodes. In one-sorted logic, $f$ applied to its own results would generate infinitely many terms, so the Herbrand universe is infinite.

With two sorts, $f : \mathrm{quorum} \times \mathrm{quorum} \to \mathrm{node}$. If no function goes from nodes back to quorums, then the sort graph is acyclic, and the set of ground terms is finite: the quorum constants $Q$, then the node terms, at most $|Q|^2$ plus node constants. So the Herbrand universe remains finite, grounding still terminates, and the finite model property holds. The discipline is to verify that the sort dependency graph has no cycle. If another axiom introduces $g : \mathrm{node} \to \mathrm{quorum}$, then the graph has a cycle, and the guarantee is lost.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Prove that the finite model property makes a recursively presented class decidable.
- Define EPR, prove its small-model property, and decide an EPR sentence by grounding.
- Give the complexity of EPR and explain the source of both the upper and the lower bound.
- Prove the $2^k$ bound for the monadic class without equality.
- State which prefix classes are decidable and which are undecidable, and describe two-variable logic and the guarded fragment.
- Apply Cooper's algorithm by hand, and prove its correctness.
- State the complexity of Presburger arithmetic and of its existential fragment.
- Contrast real and integer arithmetic, with and without nonlinear terms.
- State the array property fragment's restrictions and give an example outside it.
- Given a new formula class, decide which technique, if any, gives decidability, and what the cost is.

## Materials

- Börger, Grädel and Gurevich, The Classical Decision Problem. Read it for the complete classification of prefix-vocabulary classes, the finite model property and complexity results.
- Bradley and Manna, The Calculus of Computation. Read it for quantifier elimination for Presburger arithmetic, the theory of arrays, and the array property fragment.
- Cooper, Theorem proving in arithmetic without multiplication, Machine Intelligence 7, 1972. Read it for the algorithm in its original form.
- Fischer and Rabin, Super-exponential complexity of Presburger arithmetic, 1974. Read it for the lower bounds for Presburger arithmetic and for the reals with addition.
- Oppen, A $2^{2^{2^{pn}}}$ upper bound on the complexity of Presburger arithmetic, Journal of Computer and System Sciences, 1978. Read it for the upper bound on Cooper's procedure.
- Lewis, Complexity results for classes of quantificational formulas, Journal of Computer and System Sciences, 1980. Read it for the NEXPTIME completeness results.
- Grädel, Kolaitis and Vardi, On the decision problem for two-variable first-order logic, Bulletin of Symbolic Logic, 1997. Read it for the small model property of FO$^2$.
- Bradley, Manna and Sipma, What's decidable about arrays, VMCAI 2006. Read it for the array property fragment.
- Padon, McMillan, Panda, Sagiv and Shoham, Ivy: Safety Verification by Interactive Generalization, PLDI 2016. Read it for the use of EPR in practical protocol verification.
