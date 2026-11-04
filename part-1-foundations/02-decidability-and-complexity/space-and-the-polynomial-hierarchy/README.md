# Space and the Polynomial Hierarchy

Part 1, Chapter 2: Decidability and Complexity.

## Objective

Place QBF, model checking and related problems in PSPACE and the polynomial hierarchy.

## Why this matters

Many reasoning problems are harder than SAT, and their complexity explains the shape of the tools built for them. [QBF solving](../../../part-2-core-reasoning/04-sat/qbf-and-model-counting/) has alternation, which a single SAT call cannot express unless NP equals the relevant class. [Model checking](../../../part-2-core-reasoning/08-model-checking/transition-systems-and-temporal-logic/) of a finite system given as a circuit is PSPACE-complete, which is why [BDDs](../../../part-2-core-reasoning/08-model-checking/symbolic-checking-with-bdds/), [bounded model checking](../../../part-2-core-reasoning/08-model-checking/bounded-model-checking/) and [IC3](../../../part-2-core-reasoning/08-model-checking/ic3-and-pdr/) all fail on some instances and do well on others. Questions of the form "there exists a design such that for all inputs" sit at the second level of the polynomial hierarchy, and counterexample-guided loops are the standard way to solve them. An applied scientist uses these classifications to decide how many solver calls an approach needs and which guarantee each call can provide.

## Prerequisites

- [Reductions and NP-Completeness](../reductions-and-np-completeness/), for NP, reductions and the Cook-Levin construction.
- [Computability](../computability/), for Turing machines and configurations.
- [Propositional Logic](../../01-mathematical-logic/propositional-logic/), for semantics of formulas.

## Lesson

### Space complexity

To define sublinear space, use a Turing machine with a read-only input tape and a separate read-write work tape. Space usage is the number of work tape cells visited. For $s(n) \ge \log n$:

- $\mathrm{SPACE}(s)$ is the class of languages decided by a deterministic machine using $O(s(n))$ space.
- $\mathrm{NSPACE}(s)$ is the corresponding class for nondeterministic machines, with the bound holding on all branches.

The standard classes are as follows.

$$
\mathrm{L} = \mathrm{SPACE}(\log n), \quad \mathrm{NL} = \mathrm{NSPACE}(\log n), \quad \mathrm{PSPACE} = \bigcup_k \mathrm{SPACE}(n^k), \quad \mathrm{NPSPACE} = \bigcup_k \mathrm{NSPACE}(n^k).
$$

Space can be reused and time cannot, and this asymmetry explains most of the results below.

A machine with $s(n) \ge \log n$ space has at most $|Q| \cdot n \cdot s(n) \cdot |\Gamma|^{s(n)} = 2^{O(s(n))}$ configurations, since a configuration is determined by the state, the input head position, the work head position and the work tape contents. A halting deterministic machine cannot repeat a configuration, so $\mathrm{SPACE}(s) \subseteq \mathrm{DTIME}(2^{O(s)})$. A nondeterministic machine has a graph of that size, and searching it is also within this time bound. So the following chain holds:

$$
\mathrm{L} \subseteq \mathrm{NL} \subseteq \mathrm{P} \subseteq \mathrm{NP} \subseteq \mathrm{PH} \subseteq \mathrm{PSPACE} \subseteq \mathrm{EXPTIME} \subseteq \mathrm{NEXPTIME}.
$$

The hierarchy theorems give $\mathrm{NL} \subsetneq \mathrm{PSPACE}$ and $\mathrm{P} \subsetneq \mathrm{EXPTIME}$. It is unknown which of the intermediate inclusions are strict.

### Savitch's theorem

Theorem (Savitch, 1970). For $s(n) \ge \log n$, $\mathrm{NSPACE}(s) \subseteq \mathrm{SPACE}(s^2)$. In particular, $\mathrm{NPSPACE} = \mathrm{PSPACE}$.

Proof. Let $N$ use space $s$. Its configurations have length $O(s)$, and it accepts within $t = 2^{O(s)}$ steps if it accepts at all. Assume a unique accepting configuration, by clearing the tape before accepting. Decide whether one configuration reaches another by recursing on the midpoint.

```
CANYIELD(c1, c2, t):
    if t = 1:
        return c1 = c2 or c1 yields c2 in one step
    for each configuration m of length O(s):
        if CANYIELD(c1, m, t/2) and CANYIELD(m, c2, t/2):
            return true
    return false
```

Call this procedure on the initial configuration, the accepting configuration and $t$ rounded up to a power of 2. The recursion depth is $\log t = O(s)$, and each stack frame stores $O(s)$ bits, namely the configurations $c_1, c_2, m$ and the value $t$. The total space is $O(s^2)$. If $s$ is not known in advance, try $s = 1, 2, \dots$ and check whether $N$ can reach a configuration that uses one more cell, as textbooks describe. $\square$

The running time of this procedure is roughly $2^{O(s^2)}$, far more than the time of a graph search. It reuses the space used by the first recursive call when making the second. The same midpoint idea underlies iterative squaring in model checking.

### Graph reachability and NL

The problem $\mathrm{PATH}$ asks whether a directed graph has a path from $u$ to $v$. It is in NL: guess the path one vertex at a time and keep a step counter. It is NL-complete under logspace reductions, since the configuration graph of a logspace nondeterministic machine has polynomial size and can be constructed in logspace.

Theorem (Immerman, Szelepcsényi, 1987 and 1988). $\mathrm{NL} = \mathrm{coNL}$.

This is stated here without proof. Its proof uses inductive counting of reachable vertices. It implies that non-reachability is also in NL, and one consequence is that 2-SAT is in NL, as Exercise 7 shows.

Model checking in its most basic form is $\mathrm{PATH}$. Checking a safety property on an explicit state graph means checking whether a bad state is reachable, so it is NL-complete. Everything that makes model checking hard in practice comes from the fact that the graph is not given explicitly.

### Quantified Boolean formulas

A quantified Boolean formula (QBF) in prenex form is

$$
Q_1 x_1\, Q_2 x_2 \cdots Q_n x_n\, \varphi(x_1, \dots, x_n), \qquad Q_i \in \{\exists, \forall\},
$$

where $\varphi$, the matrix, is a propositional formula. Semantics is by expansion: $\exists x\, \psi$ means $\psi[x := \top] \lor \psi[x := \bot]$, and $\forall x\, \psi$ means $\psi[x := \top] \land \psi[x := \bot]$. TQBF is the language of true closed QBFs.

There is a useful game view. Player $\exists$ picks values for existential variables, and player $\forall$ picks values for universal variables, in prefix order. The formula is true exactly when $\exists$ has a winning strategy, which makes $\varphi$ true. A winning strategy gives each existential variable a function of the universal variables to its left. Those functions are the Skolem functions of the QBF, which appear in the certificates that QBF solvers produce.

Theorem (Stockmeyer and Meyer, 1973). TQBF is PSPACE-complete.

Proof of membership. Evaluate recursively.

```
EVAL(Q1 x1 ... Qn xn phi, assignment):
    if n = 0: return value of phi under assignment
    a = EVAL(rest, assignment + {x1 = true})
    b = EVAL(rest, assignment + {x1 = false})
    if Q1 is exists: return a or b
    if Q1 is forall: return a and b
```

The depth is $n$, and each frame needs constant additional space beyond the shared assignment, so the space is polynomial. Time is exponential. The second call reuses the space of the first.

Proof of hardness. Let $L \in \mathrm{PSPACE}$ be decided by a machine $M$ with space $s(n)$ polynomial. Fix an input $w$. Assume a unique accepting configuration $c_{\mathrm{acc}}$, and let $c_0$ be the initial configuration. Represent a configuration by $O(s)$ Boolean variables. For configuration variable vectors $c, c'$ and for $k \ge 0$, define $\Phi_k(c, c')$ to mean that $c$ reaches $c'$ in at most $2^k$ steps.

Base case. $\Phi_0(c, c')$ says that $c = c'$ or $c$ yields $c'$ in one step. As in the [Cook-Levin proof](../reductions-and-np-completeness/), this is expressed by a propositional formula of size polynomial in $s$, using local checks on each cell.

Recursive case. The naive definition

$$
\Phi_{k+1}(c, c') = \exists m\, \big(\Phi_k(c, m) \land \Phi_k(m, c')\big)
$$

is correct, but it doubles the formula size at each level, and $k$ is polynomial in $s$. So the total size would be exponential. To reuse a single copy of $\Phi_k$, use a universal quantifier to pick which of the two pairs to check.

$$
\Phi_{k+1}(c, c') = \exists m\, \forall a\, \forall b\, \Big[ \big((a = c \land b = m) \lor (a = m \land b = c')\big) \to \Phi_k(a, b) \Big].
$$

The bracketed condition on $a, b$ holds for exactly the two pairs $(c, m)$ and $(m, c')$, so the formula says the same as the naive form.

Each level adds $O(s)$ symbols, so with $T = O(s)$, chosen so that $2^T$ exceeds the number of configurations, $|\Phi_T| = O(s \cdot T + |\Phi_0|)$, which is polynomial. The final sentence $\Phi_T(c_0, c_{\mathrm{acc}})$, with the configuration constants substituted, is true if and only if $M$ accepts $w$. Moving quantifiers outward gives prenex form, since all bound variables can be renamed apart. $\square$

Note the method. In SAT, each repeated use of a sub-formula requires a copy. Universal quantification lets one sub-formula be used many times. This is exactly the sense in which QBF encodings are more succinct than SAT encodings, and it is why QBF is studied for model checking and synthesis.

To put the matrix in CNF, apply Tseitin to the matrix and quantify the new variables existentially at the innermost level. The extra innermost $\exists$ block does not change the truth value, since those variables are functionally determined by the outer variables. So TQBF restricted to prenex CNF remains PSPACE-complete.

### The polynomial hierarchy

The hierarchy classifies problems by the number of quantifier alternations with polynomially long certificates. For $k \ge 1$, a language $L$ is in $\Sigma_k^p$ if there is a polynomial $q$ and a polynomial-time predicate $R$ with

$$
x \in L \iff \exists y_1\, \forall y_2\, \exists y_3 \cdots Q_k y_k\ R(x, y_1, \dots, y_k),
$$

where all $|y_i| \le q(|x|)$, and $Q_k$ is $\exists$ when $k$ is odd and $\forall$ when $k$ is even. $\Pi_k^p$ is the class of complements of languages in $\Sigma_k^p$, so it has the same form with the quantifiers starting from $\forall$. Thus $\Sigma_1^p = \mathrm{NP}$, $\Pi_1^p = \mathrm{coNP}$, and

$$
\mathrm{PH} = \bigcup_{k \ge 1} \Sigma_k^p.
$$

There is an equivalent characterization by oracle machines. An oracle machine may ask whether a string belongs to a fixed language and receive the answer in one step. With this, $\Sigma_{k+1}^p = \mathrm{NP}^{\Sigma_k^p}$ and $\Delta_{k+1}^p = \mathrm{P}^{\Sigma_k^p}$. So $\Delta_2^p = \mathrm{P}^{\mathrm{NP}}$ is the class of problems solved by polynomially many adaptive calls to a SAT solver, and $\Sigma_2^p = \mathrm{NP}^{\mathrm{NP}}$ is the class solved by guessing and then calling a SAT solver polynomially often.

Proof sketch of the equivalence for $k = 2$. For the forward inclusion, $\exists y_1 \forall y_2\, R$ is decided by guessing $y_1$ and asking an NP oracle whether $\exists y_2\, \neg R$. For the reverse inclusion, an $\mathrm{NP}^{\mathrm{NP}}$ machine accepts if there is a branch with oracle answers that are correct. Existentially guess the branch, the oracle answers, and a certificate for each query with a yes-answer. Then universally check that each query with a no-answer has no certificate. This has the required form. $\square$

Theorem. $\mathrm{PH} \subseteq \mathrm{PSPACE}$, and if $\Sigma_k^p = \Pi_k^p$ for some $k$, then $\mathrm{PH} = \Sigma_k^p$.

Proof. The polynomial-space recursion on the quantifiers proves the inclusion, as with TQBF. The collapse is Exercise 11. $\square$

If PH does not collapse, as is widely believed, then no problem complete for $\Sigma_2^p$ can be reduced in polynomial time to SAT. If PH were to equal PSPACE, then PH would collapse, because a PSPACE-complete problem would be in some level of the hierarchy.

### Complete problems: the role of the matrix

Let $\Sigma_k\mathrm{SAT}$ be the set of true sentences $\exists X_1 \forall X_2 \cdots Q_k X_k\, \varphi$ with $k$ blocks.

Theorem (Stockmeyer, Wrathall, 1976). $\Sigma_k\mathrm{SAT}$ is $\Sigma_k^p$-complete, and $\Pi_k\mathrm{SAT}$ is $\Pi_k^p$-complete. Hardness holds with the matrix in 3-CNF when the innermost quantifier is $\exists$, and with the matrix in 3-DNF when the innermost quantifier is $\forall$.

Proof sketch. Membership is immediate, by evaluating the matrix. For hardness, apply the Cook-Levin construction to $R$ with the $y_i$ fixed as inputs. This gives a CNF formula with auxiliary variables $z$ such that $R$ holds exactly when $\exists z$ makes the CNF true. If the innermost quantifier is $\exists$, then $z$ joins that block. If the innermost quantifier is $\forall$, apply the construction to $\neg R$, which yields $\neg R \iff \exists z\, \mathrm{CNF}$, and thus $R \iff \forall z\, \neg \mathrm{CNF}$. Here $\neg \mathrm{CNF}$ is a DNF, and $z$ joins the innermost $\forall$ block. $\square$

The restriction to DNF matters.

Theorem. The problem $\exists X \forall Y\, \varphi$ with $\varphi$ in CNF is in NP, and it is NP-complete.

Proof. A universal quantifier distributes over a conjunction, so the sentence holds exactly when $\exists X \bigwedge_C \forall Y\, C$. For a clause $C$, split it into its $X$-part and its $Y$-part. If the $Y$-part contains a complementary pair, then $\forall Y\, C$ is true. Otherwise, the adversary can falsify the $Y$-part, so $\forall Y\, C$ is equivalent to the $X$-part of $C$. The result is an ordinary SAT problem over $X$. When $Y$ is empty, this is SAT, which gives hardness. $\square$

So if you write a 2QBF solver and encode the matrix naively in CNF with Tseitin variables, the Tseitin variables must be placed innermost and existential. You then have an $\exists\forall\exists$ prefix, which is exactly what the hardness theorem expects.

### Problems at each level

| Problem | Class | Reason |
|---|---|---|
| Is a CNF satisfiable? | NP-complete | A model is a certificate. |
| Is a CNF unsatisfiable? | coNP-complete | It is the complement of SAT. |
| Is a clause set minimally unsatisfiable? | DP-complete | It conjoins one coNP check with polynomially many NP checks, and hardness is due to Papadimitriou and Wolfe. |
| Is the lexicographically least model's last bit 1? | $\Delta_2^p$-complete | The model is found by adaptive SAT calls, and this is the standard complete problem for the class. |
| Is $\exists X \forall Y\, \varphi$ true, with $\varphi$ in DNF? | $\Sigma_2^p$-complete | This is 2QBF. |
| Is there a formula with at most $k$ symbols that is equivalent to a given formula? | $\Sigma_2^p$-complete under Turing reductions | Membership guesses the formula and checks equivalence, and hardness is due to Buchfuhrer and Umans. |
| Is $\forall X \exists Y\, \varphi$ true, with $\varphi$ in CNF? | $\Pi_2^p$-complete | This is 2QBF with the quantifier order reversed. |
| Is a QBF true? | PSPACE-complete | Unbounded alternation matches polynomial space. |
| Is a dependency QBF true? | NEXPTIME-complete | A certificate is an exponentially large table for Skolem functions, as shown by Peterson, Reif and Azhar. |

DP is the class of languages of the form $A \cap B$ with $A \in \mathrm{NP}$ and $B \in \mathrm{coNP}$. It contains NP and coNP, and it lies within $\Delta_2^p$. In a CNF $F$, minimal unsatisfiability asks that $F$ is unsatisfiable and that each $F \setminus \{C\}$ is satisfiable. A combination of those satisfiable subformulas makes an NP check. The [MaxSAT](../../../part-2-core-reasoning/04-sat/maxsat/) decision problem "are $k$ clauses simultaneously satisfiable?" is NP-complete, while computing the optimal value lies in the function class $\mathrm{FP}^{\mathrm{NP}}$, computed by a binary search over $k$ using SAT calls.

Counting has its own hierarchy. Counting models is #P-complete (Valiant, 1979), and Toda's theorem gives $\mathrm{PH} \subseteq \mathrm{P}^{\#\mathrm{P}}$. A counting oracle is therefore at least as powerful as every level of the hierarchy.

The practical reading of the table is a count of solver calls. A problem in NP needs one SAT call in principle. A problem in $\Delta_2^p$ needs polynomially many calls with no alternation. A $\Sigma_2^p$-complete problem cannot, unless the hierarchy collapses, be expressed as one polynomial-size SAT call, so tools use counterexample-guided loops, which may require exponentially many calls in the worst case.

### Solving 2QBF: counterexample-guided refinement

The following algorithm is the standard loop for $\exists X \forall Y\, \varphi(X, Y)$. It has the same structure as counterexample-guided inductive synthesis, where $X$ is a program encoding and $Y$ is an input.

```
Omega = empty set of Y-values
repeat:
    find X-value a such that phi(a, y) holds for all y in Omega    (SAT call)
    if none exists: return false
    find Y-value b such that not phi(a, b)                         (SAT call)
    if none exists: return true, with witness a
    add b to Omega
```

The loop terminates, because every iteration adds a new $b$ to $\Omega$, and there are finitely many values. It is correct, because a false answer means that a subset of the universal instances already eliminates every $X$-value, and a true answer means that $a$ has no counterexample. The first SAT call has a formula that grows with each iteration, since it instantiates $\varphi$ once for each element of $\Omega$. In the worst case, $|\Omega|$ becomes exponential, which matches the hardness of the problem.

### Model checking complexity

A Kripke structure $M = (S, S_0, R, \lambda)$ has a set of states, initial states, a total transition relation and a labeling $\lambda : S \to 2^{AP}$. LTL formulas describe paths, and CTL formulas describe the computation tree. The formal definitions appear in the [temporal logic topic](../../../part-2-core-reasoning/08-model-checking/transition-systems-and-temporal-logic/). The complexity depends on three things: the logic, whether the structure is explicit or symbolic, and which parameter is treated as input.

Theorem (explicit CTL). CTL model checking can be done in time $O(|M| \cdot |\varphi|)$ (Clarke, Emerson and Sistla, 1986).

Proof sketch. Label states with subformulas, innermost first. Atoms and Boolean connectives are direct. For $\mathsf{EX}\,\psi$, label the predecessors of $\psi$-states. For $\mathsf{E}[\psi_1\, \mathsf{U}\, \psi_2]$, search backward from $\psi_2$-states through $\psi_1$-states. For $\mathsf{EG}\,\psi$, restrict the graph to $\psi$-states and search backward from nontrivial strongly connected components. Each subformula takes $O(|M|)$ time. $\square$

The problem is P-complete. CTL is cheap because a state's label summarizes the whole future behavior for each subformula. The formula is evaluated once per state.

Theorem (explicit LTL, Sistla and Clarke, 1985). LTL model checking is PSPACE-complete in the size of the formula.

Membership proof sketch. To check $M \models \varphi$, look for a counterexample, a path satisfying $\neg \varphi$. There is a Büchi automaton for $\neg \varphi$ with $2^{O(|\varphi|)}$ states, in which each state is a set of subformulas. The product with $M$ has an accepting lasso exactly when a counterexample exists. Guess the lasso on the fly, storing only the current product state, the guessed loop state and a binary counter. This takes polynomial space nondeterministically, so PSPACE by Savitch's theorem and closure under complement. The deterministic algorithm runs in time $O(|M| \cdot 2^{O(|\varphi|)})$, and it is linear in $|M|$, which is why model checkers tolerate moderately sized LTL formulas on large structures.

Hardness proof sketch. Let $M_0$ be a deterministic machine that uses at most $p = p(n)$ cells on input $w$. Encode a computation as an infinite word over symbols from $\Gamma \cup (Q \times \Gamma) \cup \{\#\}$, with each configuration taking $p + 1$ symbols. Let the Kripke structure be the complete graph over these symbols, with each state labeled by its symbol, so that its paths include every word. The formula $\psi$ states:

- The first block is the initial configuration. This takes $p + 1$ nested uses of $\mathsf{X}$.
- For each symbol position, the symbol $p + 1$ positions later is determined by the symbol and its two neighbors. For each triple $a b c$ and the symbol $d$ it forces, write $\mathsf{G}\big((a \land \mathsf{X} b \land \mathsf{X}\mathsf{X} c) \to \mathsf{X}^{p+2} d\big)$, which has polynomial size. The $\#$ positions are constrained in the same way.
- Eventually a block has state $q_{\mathrm{acc}}$. This is $\mathsf{F}\, q_{\mathrm{acc}}$, with $q_{\mathrm{acc}}$ standing for the disjunction of the labels that contain that state. Assume that a halting configuration repeats forever, so that every run gives an infinite word.

The machine accepts $w$ if and only if some path satisfies $\psi$, that is, $M \not\models \neg \psi$. PSPACE is closed under complement, so LTL model checking is PSPACE-hard. $\square$

Now consider symbolic input. A symbolic transition system has $n$ Boolean state variables and formulas $I(s)$, $T(s, s')$ and $B(s)$. This is the form of hardware designs and of programs with bounded data, and its state space has $2^n$ states.

Theorem. Symbolic safety is PSPACE-complete. The problem is: given $I, T, B$, is a state in $B$ reachable from a state in $I$?

Proof. Membership: by nondeterministic search, keeping the current state ($n$ bits) and a counter up to $2^n$ ($n$ bits). This is in NPSPACE, so in PSPACE by Savitch's theorem.

Hardness: Let $M_0$ be a machine with polynomial space $p$, with input $w$. Use variables for the state, the head position and each of the $p$ cell contents. Let $I$ describe the initial configuration, $T$ the local update rule, and $B$ the accepting state. Reachability of $B$ holds exactly when $M_0$ accepts $w$. All formulas have polynomial size. $\square$

The following table summarizes these and related results, as surveyed by Schnoebelen.

| Problem | Input form | Complexity |
|---|---|---|
| Safety on a finite graph | Explicit | NL-complete. |
| CTL model checking | Explicit | P-complete, and $O(\lvert M \rvert \cdot \lvert \varphi \rvert)$. |
| LTL model checking | Explicit | PSPACE-complete, and $O(\lvert M \rvert \cdot 2^{O(\lvert \varphi \rvert)})$. |
| Modal $\mu$-calculus model checking | Explicit | In NP $\cap$ coNP, and membership in P is open. |
| Safety, bounded length in unary | Symbolic | NP-complete, since this is bounded model checking. |
| Safety, unbounded | Symbolic | PSPACE-complete. |
| CTL and LTL model checking | Symbolic | PSPACE-complete. |
| Safety of a pushdown system | Explicit control and stack alphabet | In P. |
| Safety with two unbounded stacks or counters | Explicit | Undecidable. |

The last two rows mark the boundary for software. One stack, modeling recursion, retains decidability, and two stacks can simulate a Turing machine tape, as the [Computability](../computability/) topic explains.

### How the classifications relate

There is a direct line from these theorems to engineering choices.

- SAT encodes a fixed-length bounded path, which is NP.
- Iterative squaring encodes the reachability of paths of exponential length within a polynomial-size QBF. In practice, that encoding has not displaced SAT-based unrolling, since QBF solving is harder in practice, but it shows what quantifiers buy.
- Solving a PSPACE-complete problem with SAT calls requires superpolynomially many calls in general, unless $\mathrm{PSPACE} = \Delta_2^p$. [IC3](../../../part-2-core-reasoning/08-model-checking/ic3-and-pdr/) makes many small SAT queries and does not need to represent long paths explicitly.
- Checking a candidate inductive invariant has lower complexity than finding one. It is one validity check, and thus coNP-complete, and this is why a proof-producing model checker gives a much more cheaply verifiable result.

## Worked examples

### Example 1: evaluating a QBF by recursion

Evaluate

$$
\forall x_1\, \exists x_2\, \forall x_3\, (x_1 \lor x_2 \lor x_3) \land (x_1 \lor x_2 \lor \neg x_3) \land (\neg x_1 \lor \neg x_2 \lor x_3) \land (\neg x_1 \lor \neg x_2 \lor \neg x_3).
$$

The recursion tries $x_i = \bot$ first and short-circuits.

```
forall x1:
  x1 = false: exists x2:
    x2 = false: forall x3:
      x3 = false: clause 1 false: matrix false
      result false, stop this forall
    x2 = true: forall x3:
      x3 = false: all clauses true: matrix true
      x3 = true:  all clauses true: matrix true
      result true
    result true, x2 = true is a witness
  x1 = true: exists x2:
    x2 = false: forall x3:
      x3 = false: all clauses true: matrix true
      x3 = true:  all clauses true: matrix true
      result true
    result true, x2 = false is a witness
result true
```

The formula is true, and the Skolem function is $x_2 = \neg x_1$. The stack never holds more than one partial assignment and the current position in the prefix, which is the source of the polynomial space bound. Brute-force evaluation by a script gave the same result.

### Example 2: Savitch's recursion

Take the graph with edges $s \to a$, $a \to b$ and $b \to t$. Trace $\mathrm{CANYIELD}(s, t, 4)$, with midpoints tried in the order $s, a, b, t$. A false first subcall skips the second subcall. Each line at $t = 1$ checks equality or an edge.

```
can(s,t,4)
  can(s,s,2)
    can(s,s,1) = true
    can(s,s,1) = true
    midpoint s succeeds, so can(s,s,2) = true
  can(s,t,2)
    can(s,s,1) = true
    can(s,t,1) = false
    can(s,a,1) = true
    can(a,t,1) = false
    can(s,b,1) = false
    can(s,t,1) = false
    no midpoint succeeds, so can(s,t,2) = false
  can(s,a,2)
    can(s,s,1) = true
    can(s,a,1) = true
    midpoint s succeeds, so can(s,a,2) = true
  can(a,t,2)
    can(a,s,1) = false
    can(a,a,1) = true
    can(a,t,1) = false
    can(a,b,1) = true
    can(b,t,1) = true
    midpoint b succeeds, so can(a,t,2) = true
  midpoint a succeeds, so can(s,t,4) = true
```

There are 20 calls. At no point does the stack hold more than 3 frames, which is $1 + \log_2 4$. A script generated this trace.

### Example 3: iterative squaring for a counter

Consider a 2-bit counter with state $c \in \{0, 1, 2, 3\}$, written in binary, transition relation $R(c, c') : c' = c + 1 \bmod 4$, initial state $0$ and bad state $3$. Determine the smallest $k$ with $\Phi_k(0, 3)$ true.

Define $\Phi_0(c, c') = (c = c') \lor R(c, c')$ and

$$
\Phi_{k+1}(c, c') = \exists m\, \forall a\, \forall b\, \big[ ((a = c \land b = m) \lor (a = m \land b = c')) \to \Phi_k(a, b) \big].
$$

Level 0. $\Phi_0(0, c')$ holds for $c' \in \{0, 1\}$, so $\Phi_0(0, 3)$ is false.

Level 1. Consider $\Phi_1(0, 3)$. The inner premise is true for exactly the pairs $(0, m)$ and $(m, 3)$, so $\Phi_1(0, 3)$ is equivalent to $\exists m\, (\Phi_0(0, m) \land \Phi_0(m, 3))$. The first conjunct requires $m \in \{0, 1\}$. The second requires $m \in \{2, 3\}$. There is no such $m$, so $\Phi_1(0, 3)$ is false.

Level 2. $\Phi_2(0, 3)$ is equivalent to $\exists m\, (\Phi_1(0, m) \land \Phi_1(m, 3))$. Take $m = 1$. For $\Phi_1(0, 1)$, take $m' = 0$, with $\Phi_0(0, 0)$ and $\Phi_0(0, 1)$. For $\Phi_1(1, 3)$, take $m' = 2$, with $\Phi_0(1, 2)$ and $\Phi_0(2, 3)$. So $\Phi_2(0, 3)$ is true, and the bad state is reachable within $2^2 = 4$ steps.

Size. Each level adds three quantified 2-bit vectors and a premise of constant size per bit, so the size is $O(k \cdot n + |R|)$ for an $n$-bit system. The naive form would contain $2^k$ copies of $R$. For a system with $n$ bits, you need $k = n$ to cover all possible distances, so the QBF has polynomial size, while a SAT unrolling that covers the same distance would have $2^n$ copies of the transition relation. A script evaluated these quantifiers and confirmed the results for $k = 0, 1, 2$.

### Example 4: a counterexample-guided run on 2QBF

Decide $\exists x_1 \exists x_2 \forall y_1 \forall y_2\, \varphi$, with

$$
\varphi = (x_1 \land y_1) \lor (x_2 \land \neg y_1) \lor (\neg x_1 \land \neg x_2 \land y_2).
$$

The matrix is in DNF, as the complete form of the problem expects. The first SAT call of each iteration chooses the smallest $(x_1, x_2)$ in lexicographic order that satisfies the constraints, and the second chooses the smallest counterexample $(y_1, y_2)$.

```
iteration 1
  constraints: none
  candidate:   (x1, x2) = (0, 0)
  residual:    phi(0, 0, y) = y2
  counterexample: (y1, y2) = (0, 0)
  add constraint: phi(x, 0, 0) = x2
iteration 2
  constraints: x2
  candidate:   (x1, x2) = (0, 1)
  residual:    phi(0, 1, y) = not y1
  counterexample: (y1, y2) = (1, 0)
  add constraint: phi(x, 1, 0) = x1
iteration 3
  constraints: x2, x1
  candidate:   (x1, x2) = (1, 1)
  residual:    phi(1, 1, y) = y1 or not y1, which is valid
  no counterexample
result: true, with witness (x1, x2) = (1, 1)
```

Two instances of the universal quantifier were enough, out of the four possible. A script reproduced this trace and confirmed the result by brute force.

### Example 5: classifying a reasoning problem

Classify this problem: given a symbolic system $(I, T, B)$ and a candidate formula $\mathit{Inv}$, determine whether $\mathit{Inv}$ is an inductive invariant that proves safety. That means $I \to \mathit{Inv}$, $\mathit{Inv}(s) \land T(s, s') \to \mathit{Inv}(s')$ and $\mathit{Inv} \to \neg B$ are all valid.

Upper bound. The problem asks for three validity checks. Each is in coNP, and coNP is closed under intersection, since a falsifying assignment for any one of them is a certificate for the complement. So the problem is in coNP.

Lower bound. Reduce from UNSAT. Given $\varphi$ over variables $x$, take state variables $x$, with $I = \bot$, $T = \bot$, $B = \varphi$ and $\mathit{Inv} = \top$. The first two conditions hold vacuously. The third, $\top \to \neg \varphi$, is valid if and only if $\varphi$ is unsatisfiable. So the problem is coNP-hard, and hence coNP-complete.

Reading the result. Checking a safety proof takes one SAT call. Finding one solves a PSPACE-complete problem. This difference is what allows a certificate-checking pipeline with a small trusted base to validate the output of a much more elaborate tool.

## Common mistakes

- Assuming that PSPACE-complete means exponential space. PSPACE-complete problems use polynomial space, and they may use exponential time.
- Writing the QBF recursion with two copies of the subformula. That formula is correct and exponentially large, so it is useless as a reduction, and the universal quantifier trick is required.
- Stating that $\exists\forall$ with a CNF matrix is $\Sigma_2^p$-complete. With a CNF matrix, it is in NP, and the complete form uses a DNF matrix or an additional innermost $\exists$ block.
- Placing Tseitin variables in the wrong quantifier block. In prenex QBF, they must be existential and innermost, since their values depend on all other variables.
- Treating the complexity of model checking as one number. The answer depends on the logic, on whether the system is explicit or symbolic, and on whether you measure in the size of the system, the formula or both.
- Claiming that LTL is harder than CTL on all counts. On explicit structures, LTL is exponential in the formula and linear in the system, and many real properties are short, so LTL is often practical.
- Concluding that a PSPACE-complete problem cannot be attacked with SAT. It can be attacked by many SAT calls, as in IC3, and only a single polynomial-size call is ruled out, under the usual assumptions.
- Thinking that the order of quantifiers within a block matters. Within a block of one quantifier type, order does not change truth, and only the order between blocks matters.
- Assuming that a bound on proof length is a bound on counterexample length. A safe system's inductive invariant may be small even if the diameter of the system is exponential, and an unsafe system may have only counterexamples of exponential length.

## Exercises

### Exercise 1

Write the known chain of inclusions from L to NEXPTIME, and state two separations between classes in the chain that are known.

<details><summary>Solution</summary>

$\mathrm{L} \subseteq \mathrm{NL} \subseteq \mathrm{P} \subseteq \mathrm{NP} \subseteq \mathrm{PH} \subseteq \mathrm{PSPACE} \subseteq \mathrm{EXPTIME} \subseteq \mathrm{NEXPTIME}$.

The hierarchy theorems give $\mathrm{NL} \subsetneq \mathrm{PSPACE}$ and $\mathrm{P} \subsetneq \mathrm{EXPTIME}$. So at least one inclusion in each span is strict, and it is not known which.

</details>

### Exercise 2

Let $\varphi = (x_1 \lor x_2 \lor x_3) \land (\neg x_1 \lor \neg x_2 \lor x_3) \land (x_1 \lor \neg x_2 \lor \neg x_3) \land (\neg x_1 \lor x_2 \lor \neg x_3)$. Evaluate $\forall x_1 \forall x_2 \exists x_3\, \varphi$ and $\exists x_1 \exists x_3 \forall x_2\, \varphi$.

<details><summary>Solution</summary>

First, compute the models. The formula is satisfied exactly by the assignments with $x_1 \oplus x_2 \oplus x_3 = 1$: $(0,0,1), (0,1,0), (1,0,0), (1,1,1)$.

For $\forall x_1 \forall x_2 \exists x_3\, \varphi$, any $x_1, x_2$ can be completed by $x_3 = 1 \oplus x_1 \oplus x_2$. So it is true.

For $\exists x_1 \exists x_3 \forall x_2\, \varphi$, after fixing $x_1, x_3$, exactly one value of $x_2$ gives odd parity, so the other value of $x_2$ falsifies $\varphi$. So it is false.

Thus changing the prefix order between blocks changes the answer. A script confirmed the models and both values.

</details>

### Exercise 3

Using the proof in the lesson, reduce the following sentence to a SAT problem and decide it.

$$
\exists x_1 \exists x_2 \forall y_1 \forall y_2\, (x_1 \lor y_1) \land (\neg x_1 \lor x_2 \lor y_2) \land (y_1 \lor \neg y_1 \lor x_2).
$$

<details><summary>Solution</summary>

For each clause, remove the $Y$-part unless it has a complementary pair.

- $x_1 \lor y_1$ has $Y$-part $y_1$, so it becomes $x_1$.
- $\neg x_1 \lor x_2 \lor y_2$ has $Y$-part $y_2$, so it becomes $\neg x_1 \lor x_2$.
- $y_1 \lor \neg y_1 \lor x_2$ has a complementary pair in its $Y$-part, so it is true, and it disappears.

The SAT problem is $x_1 \land (\neg x_1 \lor x_2)$. It has the unique model $x_1 = \top$, $x_2 = \top$. So the sentence is true. A brute-force script confirmed that this is the only $X$-value that works.

</details>

### Exercise 4

Let $S(k)$ be the size of the naive recursive formula, and let $S'(k)$ be the size of the formula with a universal quantifier. Write their recurrences and solutions, and evaluate them for $n$-bit configurations with $k = n$.

<details><summary>Solution</summary>

Let $c$ be the size of the quantifier and comparison text at one level, which is $O(n)$, and let $S(0) = S'(0) = r$ be the size of the one-step formula.

The naive formula satisfies $S(k + 1) = 2 S(k) + c$, so $S(k) = 2^k r + (2^k - 1) c$.

The other formula satisfies $S'(k + 1) = S'(k) + c$, so $S'(k) = r + k c$.

With $k = n$, the naive form has size $\Theta(2^n (r + n))$, and the other form has size $r + O(n^2)$. Only the second is a polynomial-time reduction.

</details>

### Exercise 5

Show that a QBF with only existential quantifiers is SAT, one with only universal quantifiers is validity, and that the class of $\exists$-then-$\forall$-then-$\exists$ sentences with a CNF matrix is $\Sigma_3^p$-complete according to the theorem in the lesson. What is the class of $\forall$-then-$\exists$ sentences with a CNF matrix?

<details><summary>Solution</summary>

$\exists X\, \varphi$ is true if and only if $\varphi$ is satisfiable, by the definition of $\exists$. $\forall X\, \varphi$ is true if and only if $\varphi$ is true under all assignments, which is validity.

An $\exists\forall\exists$ sentence has $k = 3$ blocks with an innermost $\exists$, so the theorem says that CNF suffices for $\Sigma_3^p$-completeness.

A $\forall\exists$ sentence with a CNF matrix has $k = 2$ blocks with an innermost $\exists$, starting with $\forall$. This is $\Pi_2\mathrm{SAT}$, and it is $\Pi_2^p$-complete. Its complement is $\exists\forall$ with a DNF matrix, which is the case from the lesson.

</details>

### Exercise 6

Prove that the minimally unsatisfiable set recognition problem is in DP.

<details><summary>Solution</summary>

Let $F = \{C_1, \dots, C_m\}$ be a set of clauses. It is minimally unsatisfiable when $F$ is unsatisfiable and each $F \setminus \{C_i\}$ is satisfiable.

Let $A$ be the language of clause sets for which each $F \setminus \{C_i\}$ is satisfiable. A list of $m$ assignments, one per subset, is a certificate that can be checked in polynomial time, so $A \in \mathrm{NP}$.

Let $B$ be the language of unsatisfiable clause sets. Then $B \in \mathrm{coNP}$.

The target language is $A \cap B$, so it is in DP.

</details>

### Exercise 7

Prove that 2-SAT is NL-complete. Use $\mathrm{NL} = \mathrm{coNL}$ for membership, and for hardness, reduce the complement of $\mathrm{PATH}$ to 2-SAT.

<details><summary>Solution</summary>

Membership. A 2-CNF is unsatisfiable exactly when some variable $x$ has a path $x \to^* \neg x$ and a path $\neg x \to^* x$ in the implication graph. A logspace nondeterministic machine can guess $x$ and verify both paths, keeping only the current vertex and a counter. So 2-UNSAT is in NL, and so 2-SAT is in coNL, which equals NL.

Hardness. $\mathrm{PATH}$ is NL-complete, so its complement is coNL-complete, and hence NL-complete. Given $G, s, t$, construct a 2-CNF with a variable $x_v$ for each vertex $v$. Add the clause $\neg x_u \lor x_v$ for each edge $u \to v$, the unit clause $x_s$ and the unit clause $\neg x_t$. The formula is unsatisfiable exactly when there is a path from $s$ to $t$: if a path exists, unit propagation along it derives a contradiction, and otherwise, setting $x_v$ true exactly for the vertices reachable from $s$ is a model. Hence $\overline{\mathrm{PATH}}$ reduces to 2-SAT in logarithmic space.

</details>

### Exercise 8

Prove that CTL model checking for a symbolic system $(I, T)$ with $n$ Boolean state variables is in PSPACE.

<details><summary>Solution</summary>

Define a procedure $\mathrm{HOLDS}(s, \psi)$ for a state $s$ of $n$ bits and a subformula $\psi$.

- For atoms and Boolean connectives, evaluate directly, with recursive calls on the subformulas.
- For $\mathsf{EX}\,\psi$, loop over all $2^n$ states $s'$ with a counter, and check $T(s, s')$ and $\mathrm{HOLDS}(s', \psi)$.
- For $\mathsf{E}[\psi_1\, \mathsf{U}\, \psi_2]$, use a nondeterministic search through states that satisfy $\psi_1$ to a state satisfying $\psi_2$, with a counter up to $2^n$.
- For $\mathsf{EG}\,\psi$, nondeterministically guess a path through $\psi$-states to a state on a cycle through $\psi$-states, with the same counters.

Each recursive step stores $O(n)$ bits, and the recursion depth is at most $|\varphi|$. Nondeterministic oracle calls inside a recursion are handled by determinizing each search, by Savitch's theorem, which keeps the total space polynomial. The top level checks all initial states with a counter. So the space is polynomial in $n + |\varphi|$ plus the space to evaluate $I$ and $T$.

</details>

### Exercise 9

Let $\mathrm{BMC}_{\mathrm{bin}}$ be: given a symbolic system, and $k$ in binary, is a bad state reachable in exactly $k$ steps? Prove that $\mathrm{BMC}_{\mathrm{bin}}$ is PSPACE-complete, and compare with the unary case.

<details><summary>Solution</summary>

Membership. Search nondeterministically, storing the current state and a step counter. The counter fits in $|k|$ bits, which is at most the input length. So it is in NPSPACE, hence in PSPACE.

Hardness. Reduce from symbolic safety. Given $(I, T, B)$ over $n$ variables, build a system $T'$ that also has the transitions allowing a state in $B$ to stay in place. Take $k = 2^n$, written in $n + 1$ bits. If $B$ is reachable, then it is reachable within $2^n - 1$ steps, because the shortest path has no repeated state, and staying in $B$ extends that path to exactly $2^n$ steps. If $B$ is not reachable, then there is no path to $B$ of any length.

Comparison. With $k$ in unary, the certificate is a polynomial-size trace, and the problem is NP-complete. The two problems differ only in how a number is written, and this one change moves the problem from NP to PSPACE, under standard assumptions.

</details>

### Exercise 10

A completeness threshold for symbolic safety would be a number $K$ such that if a bad state is reachable, then it is reachable within $K$ steps. Show that an $n$-bit counter system needs $K = 2^n - 1$. Then prove that if a polynomial $K$ in the size of the input were always available, NP would equal PSPACE.

<details><summary>Solution</summary>

Counter. Take $I : s = 0$, $T : s' = s + 1 \bmod 2^n$ and $B : s = 2^n - 1$, with the state a binary number. The system is deterministic and the first visit to $B$ is at step $2^n - 1$. So $K \ge 2^n - 1$, and $T$ has polynomial size.

Collapse. Suppose that $K$ is bounded by a polynomial in the size of the input for each system. Then a sequence of at most $K + 1$ states would be a polynomial-size certificate for reachability, checked in polynomial time. So symbolic safety violation would be in NP. It is PSPACE-complete, and PSPACE is closed under complement, so $\mathrm{PSPACE} \subseteq \mathrm{NP}$. Together with $\mathrm{NP} \subseteq \mathrm{PSPACE}$, this yields equality.

So bounded model checking alone cannot be a complete polynomial-size method unless NP equals PSPACE. Completeness requires other methods, such as [k-induction](../../../part-2-core-reasoning/08-model-checking/k-induction/) or interpolation.

</details>

### Exercise 11

Prove that if $\Sigma_k^p = \Pi_k^p$, then $\Sigma_{k+1}^p = \Sigma_k^p$, and conclude that $\mathrm{PH} = \Sigma_k^p$.

<details><summary>Solution</summary>

Let $L \in \Sigma_{k+1}^p$. Then $x \in L \iff \exists y\, (x, y) \in A$, with $|y|$ polynomial and $A \in \Pi_k^p$, because after the leading $\exists$, the remaining $k$ alternating blocks define a $\Pi_k^p$ language. By assumption, $A \in \Sigma_k^p$, so

$$
(x, y) \in A \iff \exists z_1\, \forall z_2 \cdots Q z_k\ R(x, y, z_1, \dots, z_k).
$$

Merging $\exists y$ with $\exists z_1$ gives a $\Sigma_k^p$ form for $L$. So $\Sigma_{k+1}^p \subseteq \Sigma_k^p$, and the other inclusion is immediate. Applying complements gives $\Pi_{k+1}^p = \Pi_k^p = \Sigma_k^p$.

By induction, for every $j \ge k$, $\Sigma_{j+1}^p = \Sigma_k^p$: the inductive hypothesis gives $\Sigma_j^p = \Pi_j^p = \Sigma_k^p$, and then the first part applies to level $j$. Therefore, $\mathrm{PH} = \Sigma_k^p$.

</details>

### Exercise 12

For each problem, give the smallest class among NP, coNP, $\Sigma_2^p$ and $\Pi_2^p$ that you can prove it belongs to, and sketch the argument. The inputs are propositional.

1. Given a formula $F$ and a number $k$ in unary, is there an unsatisfiable subset of at most $k$ clauses?
2. Given a formula and a truth assignment, is the assignment a minimal model, under set inclusion of true variables?
3. Given an integer $k$ in unary, a set of Boolean inputs and an output function given by a formula, is there a circuit with at most $k$ gates that computes the same function?
4. Given a formula $F$ and a clause $C$, is $C$ implied by $F$?

Then state how a counterexample-guided loop solves problem 3.

<details><summary>Solution</summary>

1. $\Sigma_2^p$: exists a subset of at most $k$ clauses such that for all assignments, the subset is falsified.
2. coNP: the assignment must be a model, which takes polynomial time to check, and every assignment whose true variables form a proper subset must fail the formula. A smaller model is a certificate for the complement.
3. $\Sigma_2^p$: exists a circuit of at most $k$ gates, such that for all inputs, the outputs agree. A circuit with at most $k$ gates has a polynomial-size description when $k$ is in unary.
4. coNP: an assignment that satisfies $F$ and falsifies $C$ is a certificate for the complement.

For problem 3, the loop keeps a finite set of inputs $\Omega$. One SAT call finds a circuit, described by selector variables, which agrees with the specification on $\Omega$. A second SAT call looks for an input on which the found circuit and the specification differ. If there is none, the circuit is correct. If there is one, it is added to $\Omega$. If the first call becomes unsatisfiable, then no circuit of the size exists. This is counterexample-guided inductive synthesis in its Boolean form.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- Define the space classes, and derive $\mathrm{SPACE}(s) \subseteq \mathrm{DTIME}(2^{O(s)})$ from the configuration count.
- Prove Savitch's theorem and trace its recursion.
- Prove that TQBF is PSPACE-complete, with the universal quantifier trick explained.
- Define the polynomial hierarchy by quantifiers and by oracles, and explain their equivalence.
- State the complete problems at each level, including the effect of CNF and DNF matrices.
- Prove that $\exists\forall$ over a CNF matrix is in NP.
- Trace a counterexample-guided 2QBF loop.
- Give the complexity of model checking for CTL and LTL, for explicit and symbolic inputs, and prove the PSPACE-completeness of symbolic safety.
- Classify a new problem, including checking a certificate versus finding it.

## Materials

- Sipser, Introduction to the Theory of Computation. Read it for space complexity, Savitch's theorem and the PSPACE-completeness of TQBF.
- [Arora and Barak, Computational Complexity: A Modern Approach.](https://theory.cs.princeton.edu/complexity/) Read it for the polynomial hierarchy, oracle characterizations, Toda's theorem and the alternation point of view.
- Savitch, Relationships between nondeterministic and deterministic tape complexities, Journal of Computer and System Sciences, 1970. Read it for the original midpoint recursion.
- Stockmeyer, The polynomial-time hierarchy, Theoretical Computer Science, 1976. Read it for the definition of the hierarchy and its complete problems.
- Sistla and Clarke, The complexity of propositional linear temporal logics, Journal of the ACM, 1985. Read it for the PSPACE-completeness of LTL model checking.
- Clarke, Emerson and Sistla, Automatic verification of finite-state concurrent systems using temporal logic specifications, ACM Transactions on Programming Languages and Systems, 1986. Read it for the labeling algorithm for CTL.
- Schnoebelen, The Complexity of Temporal Logic Model Checking, Advances in Modal Logic, 2002. Read it for a survey of model checking complexity across logics and input forms.
- Papadimitriou and Wolfe, The complexity of facets resolved, Journal of Computer and System Sciences, 1988. Read it for the DP-completeness of recognizing minimally unsatisfiable formulas.
- Buchfuhrer and Umans, The complexity of Boolean formula minimization, Journal of Computer and System Sciences, 2011. Read it for the $\Sigma_2^p$-completeness of formula minimization.
- Peterson, Reif and Azhar, Lower bounds for multiplayer noncooperative games of incomplete information, Computers and Mathematics with Applications, 2001. Read it for the origin of the NEXPTIME-completeness result for dependency QBF.
