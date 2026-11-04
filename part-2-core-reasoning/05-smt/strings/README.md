# Strings

Part 2, Chapter 5: SMT.

## Objective

Explain the word-equation and length reasoning used in string solvers and where they remain incomplete.

## Why this matters

Strings appear wherever software meets the outside world: URLs, resource names, SQL queries, access policies and web input. Security analyses ask whether a sanitized string can still contain an attack, and access-policy tools reduce questions about wildcards and names to string constraints, as you will see in [Access Policy Reasoning](../../../part-5-real-systems/15-cloud-and-systems/access-policy-reasoning/). This theory also teaches a different lesson from the rest of the chapter. Here the decision problem for the natural language has unknown status, so the practical question is what a solver can still guarantee when it cannot be complete.

## Prerequisites

- [DPLL(T)](../dpllt/), for the architecture.
- [Equality and Congruence Closure](../equality-and-congruence-closure/), because string solvers extend congruence closure.
- [Arithmetic](../arithmetic/), because lengths are integers.
- [Decidable Fragments](../../../part-1-foundations/02-decidability-and-complexity/decidable-fragments/), for the idea of carving out decidable subsets.

## Lesson

### The theory

Fix a finite alphabet $A$. The sort of strings is interpreted as the set $A^*$ of finite words, and $\epsilon$ is the empty word. The core operations are concatenation, written $x \cdot y$ or by juxtaposition, and length, written $|x|$, which has integer sort. A regular expression denotes a subset of $A^*$, and membership $x \in R$ is an atom.

The SMT-LIB theory of Unicode strings has a very large alphabet, with 196608 characters, and many further functions. Each is total, so each has a defined value on unusual inputs.

| Function | Meaning |
|---|---|
| `str.at(x, i)` | The result is the character at position $i$, or $\epsilon$ if $i$ is out of range. |
| `str.substr(x, i, n)` | The result is the longest substring from $i$ with at most $n$ characters, or $\epsilon$ if $i$ is out of range or $n \le 0$. |
| `str.contains(x, y)` | The atom holds if $y$ occurs in $x$ as a contiguous factor. |
| `str.indexof(x, y, i)` | The result is the first position at least $i$ where $y$ occurs, or $-1$ if there is none. |
| `str.replace(x, y, z)` | The result replaces the first occurrence of $y$ in $x$ with $z$. |
| `str.replace_all(x, y, z)` | The result replaces all occurrences of $y$ in $x$ with $z$. |
| `str.to_int(x)` | The result is the value of $x$ as a decimal numeral, or $-1$ if $x$ is not one. |

### Word equations

A word equation is an equation $s = t$ in which $s$ and $t$ are concatenations of variables and constants. A solution assigns a word to each variable and makes the two sides identical.

Makanin proved in 1977 that satisfiability of word equations is decidable, a difficult result with an impractical algorithm. Plandowski later placed the problem in PSPACE, and Jeż gave a simpler algorithm through his recompression technique. The problem is NP-hard, and whether it is in NP remains a long-standing open question in the literature.

The most basic tool is the following lemma.

Lemma (Levi). If $u \cdot v = x \cdot y$ in $A^*$, then there is a word $t$ such that either $u = x \cdot t$ and $y = t \cdot v$, or $x = u \cdot t$ and $v = t \cdot y$.

Proof. Both $u$ and $x$ are prefixes of one word. Two prefixes of one word are comparable. If $|u| \ge |x|$, then $x$ is a prefix of $u$, so write $u = x \cdot t$. Cancelling $x$ on the left gives $t \cdot v = y$. The other case is symmetric. $\square$

Levi's lemma gives a search procedure. To solve $x \cdot s = c \cdot t$, where $x$ is a variable and $c$ is a character, split into the cases $x = \epsilon$ and $x = c \cdot x'$ for a fresh $x'$. Then substitute and cancel. Similarly, $x \cdot s = y \cdot t$ splits into $x = y$, $x = y \cdot z$ and $y = x \cdot z$. This is close to the classical Nielsen transformation. It can run forever, as Worked example 3 shows, because a variable can reproduce itself under substitution.

### Adding lengths

Most useful properties combine word equations with lengths. Real programs compare lengths and index into strings, and length reasoning prunes the search dramatically.

Each word equation yields a linear integer consequence. Applying $|{\cdot}|$ gives

$$
|x \cdot y| = |x| + |y|, \qquad |c_1 \dots c_n| = n, \qquad |x| \ge 0.
$$

The linear abstraction of the input is a sound over-approximation: if it is unsat in LIA, then the string problem is unsat. For example, $x \cdot y = abc \land |x| = |y|$ gives $2|x| = 3$, which has no integer solution.

The converse direction runs from arithmetic to strings: once arithmetic entails $|u| = |v|$ for two terms that sit at the same position in the two sides of an equation, the solver knows $u = v$ without any split. This is the most valuable inference in the theory.

Whether word equations with linear length constraints are decidable is an open question, according to Ganesh and coauthors and to Liang and coauthors. Natural fragments are decidable, and this is an active field, so you should check the current state of knowledge if you need a precise boundary.

### The Liang et al. calculus

The solver in Liang, Reynolds, Tinelli, Barrett and Deters is a modular extension of congruence closure, combined with an arithmetic solver through equalities over length terms. It is described by a nondeterministic calculus with rules for a configuration, which holds string constraints, arithmetic constraints and regular constraints as well as flat forms, normal forms and buckets. The following table lists the main ideas, using the rule names of the paper.

| Rule | Idea |
|---|---|
| A-Prop and S-Prop | Entailed length equalities are exchanged between the string and arithmetic solvers. |
| Len | An equality $x = t$ yields the arithmetic fact $|x| = |t|$. |
| Len-Split | Each variable is split into $x = \epsilon$ and $|x| > 0$. |
| L-Split | The solver splits on whether two variables have equal length, if this is not known. |
| F-Form and N-Form | Terms get flat forms, as tuples of atomic terms, and each class gets a normal form. |
| F-Unify | If two equal terms have flat forms with a common prefix, followed by $u$ and $v$ with $|u| = |v|$ entailed, then $u = v$ is added. |
| F-Split | If $|u| \ne |v|$ is entailed instead, then the solver branches on $u = v \cdot z$ or $v = u \cdot z$. |
| F-Loop | A reasoning loop is broken by introducing a constraint with a star. |
| D-Base, D-Add and D-Split | These rules arrange classes into buckets, so that distinct classes get different strings. |
| Card | A bucket with too many classes for its length forces that length to grow, since $A$ is finite. |
| R-Star | A non-empty member of a starred language is unfolded by one iteration. |

Flat forms and normal forms are the central notion. A flat form writes a concatenation as a tuple of atomic terms, each one being a variable or constant. The tuple uses the normal forms of the subterms, so a term $x \cdot y$ with $y$ normalized to $a \cdot z$ gets the flat form $(x, a, z)$. When a class has several non-variable terms, their flat forms must describe the same word, which is what forces the equalities above. A solver stops when all classes have a normal form and when all classes can be given different words by the bucket assignment.

The Card rule is the part that a pure congruence closure lacks. For a bucket $B$ of classes that share a length, the rule adds

$$
\mathrm{len}\ B > \lfloor \log_{|A|}(|B| - 1) \rfloor,
$$

because $|B|$ different words of length $n$ exist only if $|A|^n \ge |B|$.

The paper states soundness in two forms. A solver is refutation sound if its unsat answers are correct, and solution sound if its sat answers come with assignments that do satisfy the constraints. Its calculus has both properties, and it is not terminating in general. So incompleteness shows up as non-termination or as the answer unknown, and never as a wrong verdict, subject to bugs in the implementation.

### Regular membership

Regular constraints can be handled in several ways.

Unfolding is the simplest. A constraint $s \in R^*$ with $s \ne \epsilon$ becomes $s = t \cdot z$ with $t \in R$ and $z \in R^*$. This can diverge on its own. The CVC4 paper describes its 2014 treatment of regular constraints as fairly naive, and it uses this kind of unrolling.

Automata can decide emptiness, intersection and complement for membership in one variable. This is the classic method, and tools such as Norn, Trau and OSTRICH are built on automata reasoning, in various combinations with length abstraction. The set of lengths of a regular language is semilinear, so it can be expressed in LIA.

Derivatives work lazily. The derivative of a regular expression with respect to a character gives the language of remaining suffixes. Instead of building the automaton, the solver computes derivatives on demand, and this handles complement and intersection well. Stanford and coauthors describe a symbolic version, which they implemented in Z3.

### Extended functions

Solvers usually remove extended functions by reduction, with the reductions applied lazily.

$$
\mathrm{contains}(x, y) \;\Longleftrightarrow\; \exists u, v.\ x = u \cdot y \cdot v.
$$

The positive case introduces fresh variables, which is easy. The negative case gives a universal statement: for all positions $i$ up to $|x| - |y|$, the substring of $x$ at $i$ with length $|y|$ differs from $y$. This is a bounded quantifier over integers. Bounded quantifiers are expanded on demand, so they are expensive when lengths are large.

The reduction of $y = \mathrm{substr}(x, i, n)$, in the normal range $0 \le i < |x|$ and $n > 0$, is

$$
x = u \cdot y \cdot v \land |u| = i \land |y| = \min(n, |x| - i).
$$

The other cases set $y = \epsilon$. Reynolds and coauthors showed that simplifying extended functions under the current context, before reducing them, helps significantly in practice.

### Where the solvers remain incomplete

| Source | What happens |
|---|---|
| Word equations with lengths | The decidability of this combination is open, so no complete algorithm is known to exist. |
| Self-reproducing equations | Levi splitting can repeat forever on equations like $a \cdot x = x \cdot b$, unless a rule such as F-Loop applies. |
| Negated containment | The expansion has a bounded universal quantifier over a possibly unbounded length. |
| Conversions between strings and integers | A conversion such as `str.to_int` relates a string's value to an integer in a nonlinear way, and it is handled heuristically. |
| Replace-all and similar functions | Their semantics are recursive, so they do not reduce to a finite quantifier-free formula in general. |

Known decidable fragments avoid some of these features. The straight-line fragment of Lin and Barceló, for example, restricts the formula so that each string variable is defined once, from earlier variables, as in a program without loops. In such a formula the constraints can be evaluated in a forward direction. Separately, the bounded approach limits all string lengths: tools such as Hampi reduce fixed-size constraints to bit-vectors. It can find models, but a report of unsat under a bound does not imply unsat in general.

## Worked examples

### Worked example 1: a word equation refuted with lengths

Decide

$$
x \cdot ab = ab \cdot y \land |x| = 1.
$$

The length rule gives $|x| + 2 = 2 + |y|$, so LIA entails $|y| = |x| = 1$.

The two sides have the flat forms $(x, a, b)$ and $(a, b, y)$, with the constant split into characters. They have an empty common prefix, and the next components are $x$ and $a$. Since $|x| = 1 = |a|$ is entailed, F-Unify adds $x = a$.

Now $x$ normalizes to $a$. The flat forms are $(a, a, b)$ and $(a, b, y)$. The common prefix is $a$, and the next components are the distinct constants $a$ and $b$, which have equal length. The two sides cannot be equal, so this is a conflict. The verdict is unsat. Both Z3 and cvc5 return unsat.

If you change the length constraint to $|x| = 2$, then the same reasoning gives $x = ab$ and $y = ab$, which is a model. Z3 returns this model.

### Worked example 2: an example from the paper

The following constraint set is Example 1 of the Liang et al. paper, with $l_1 = a$ and $l_2 = b$:

$$
|x| = |y| \land x \ne \epsilon \land z \ne \epsilon \land x \cdot a \cdot z = y \cdot b \cdot z.
$$

The steps are as follows.

```
1. Len and Len-Split apply to each variable. Branches with an empty variable
   close, because x and z are non-empty and |x| = |y|.
2. In the remaining branch, the classes are {x}, {y}, {z}, {a}, {b}, {ε} and
   {x·a·z, y·b·z}. Normal forms of the first classes are themselves.
3. Flat forms: (x, a, z) and (y, b, z).
4. F-Unify: |x| = |y| is entailed, so add x = y.
5. Reset. Now x and y share a class with representative x.
6. New flat forms: (x, a, z) and (x, b, z). The common prefix is (x).
7. F-Unify: |a| = |b| is entailed, so add a = b.
8. S-Conflict: a and b are distinct constants, so the branch closes.
```

The verdict is unsat. Z3 and cvc5 agree.

### Worked example 3: a loop and its resolution

Decide $a \cdot x = x \cdot b$, where $a, b$ are distinct characters.

Plain Levi splitting does not terminate.

```
Case x = ε:             a = b           conflict
Case x = a · x1:        a·a·x1 = a·x1·b, which cancels to a·x1 = x1·b
    Case x1 = ε:        a = b           conflict
    Case x1 = a · x2:   a·x2 = x2·b
        ...
```

Every recursive case has the same form as the original equation, and lengths do not help, because both sides have length $|x| + 1$ for each $x$.

A simple argument refutes the equation: the left side has one more $a$ than $x$ has, while the right side has the same number of $a$ as $x$ has. Solvers do not generally count characters, so they need another mechanism.

The F-Loop rule applies when a variable occurs first on one side and also later on the other side. Write the sides as $F_s = (x, b)$ and $F_t = (a, x)$. In the rule's notation, $w$ is empty, $u_1 = (b)$, $v = a$, and $v_1$ and $v_2$ are empty. The rule adds fresh variables $z, z_1, z_2$ and the constraints

$$
x = z_2 \cdot z, \qquad a = z_2 \cdot z_1, \qquad b = z_1 \cdot z_2, \qquad z \in (z_1 \cdot z_2)^*.
$$

This reflects the general solution of $u \cdot x = x \cdot w$: the words $u = p q$ and $w = q p$ are conjugates, and $x = p (q p)^n$.

Now $a = z_2 \cdot z_1$ and $a$ is a single character, so $(z_2, z_1)$ is either $(a, \epsilon)$ or $(\epsilon, a)$. In both cases $z_1 \cdot z_2 = a$, so $b = a$, a conflict. The verdict is unsat. Both Z3 and cvc5 return unsat on this equation.

By contrast, $a \cdot x = x \cdot a$ has solutions $x = a^n$, and with $|x| = 3$ Z3 returns $x = aaa$.

### Worked example 4: extended functions and regular membership

Decide $\mathrm{substr}(x, 1, 2) = ab \land |x| = 2$.

The range conditions $0 \le 1 < |x|$ and $2 > 0$ hold, so the reduction applies, with $y = ab$:

$$
x = u \cdot y \cdot v \land |u| = 1 \land |y| = \min(2, 2 - 1) = 1.
$$

The constant gives $|y| = 2$, which contradicts $|y| = 1$. The verdict is unsat. Both solvers agree.

Next, decide $x \in (ab)^* \land |x| = 3$. Since $|x| > 0$, $x \ne \epsilon$, so R-Star gives $x = ab \cdot z$ with $z \in (ab)^*$. The length rule gives $|z| = 1$. Again $z \ne \epsilon$, so $z = ab \cdot z'$ with $|z'| = -1$. This contradicts $|z'| \ge 0$. The verdict is unsat, and both solvers agree. The result reflects the fact that the length set of $(ab)^*$ is the set of even numbers.

### Worked example 5: a case that exposes incompleteness in practice

Decide $x \cdot y = y \cdot z \land |x| = 1 \land x \ne z$.

A hand proof shows the formula is unsat. Lengths give $|z| = |x| = 1$. If $y = \epsilon$, then $x = z$, a contradiction. If $y$ is non-empty, compare the two sides position by position. The first character of $y$ equals $x$, because the right side starts with $y$ and the left starts with $x$. The next character of $y$ equals the previous one, because the left side is $y$ shifted by one, and so on. So every character of $y$ is $x$, and the last character of the left side, which is a character of $y$, equals the last character of the right side, namely $z$. Hence $x = z$, a contradiction.

The same reasoning, as a solver sees it, requires an induction on $|y|$. On this query, Z3 5.3.3 returned unsat, and cvc5, called through its Python package, had not answered after 10 seconds in a test made for this topic. This is a snapshot of two tool versions and a default configuration, and you should expect it to change. The general lesson does not change: a string solver's silence says nothing about the status of the query.

## Common mistakes

- Assuming that a length-consistent formula is satisfiable. The linear abstraction is only an over-approximation, as $a \cdot x = x \cdot b$ shows.
- Assuming that a bounded solver's unsat verdict is final. If lengths were restricted during search, then the answer holds only under the restriction.
- Treating $x \cdot y = y \cdot x$ as implying $x = y$. It implies only that $x$ and $y$ are powers of one word, for example $x = ab$ and $y = abab$.
- Forgetting that SMT-LIB functions are total. For example, `str.at` at an out-of-range position gives $\epsilon$, and a property can be falsified exactly there.
- Assuming that the alphabet is small. With the SMT-LIB alphabet, the Card rule rarely forces anything, so three distinct characters are available without trouble unless regular constraints restrict them.
- Confusing a Levi split with a case split on lengths. A Levi split introduces a fresh variable and an equation, whereas a length split adds only an arithmetic fact.
- Believing that negative containment is as cheap as positive containment. The positive case is existential, and the negative case is a bounded universal.
- Treating the decidability of word equations as covering everything. Makanin's theorem says nothing about length constraints or extended functions.

## Exercises

1. Evaluate, by the SMT-LIB semantics: $\mathrm{substr}(hello, 1, 10)$, $\mathrm{at}(abc, 5)$, $\mathrm{indexof}(abab, b, 2)$, $\mathrm{replace}(aaa, a, b)$ and $\mathrm{replace}(abc, x, y)$.

<details><summary>Solution</summary>

The values are $ello$, because at most the remaining characters are returned; $\epsilon$, because the position is out of range; 3, the first occurrence at position at least 2; $baa$, because only the first occurrence is replaced; and $abc$, because the pattern does not occur. These values have been checked with Z3.

</details>

2. Use Levi's lemma to find all solutions of $x \cdot c = ab \cdot y$, in terms of a free word $t$.

<details><summary>Solution</summary>

Apply the lemma to $x \cdot c$ and $ab \cdot y$.

If $x$ is shorter than $ab$, then $x$ is a proper prefix of $ab$. If $x = \epsilon$, then $c = ab \cdot y$, and the sides begin with different characters. If $x = a$, then $a \cdot c = ab \cdot y$, so $c = b \cdot y$, which is a conflict. There are no solutions in these cases.

Otherwise $x = ab \cdot t$ for some word $t$. Cancelling $ab$ gives $t \cdot c = y$. So all solutions are $x = ab \cdot t$, $y = t \cdot c$. Z3 finds an instance, $x = abd$ and $y = dc$, when asked additionally that the third character of $x$ is $d$.

</details>

3. Show by length reasoning alone that $x \cdot y = abc \land |x| = |y|$ is unsat. Then give a formula that the length abstraction cannot refute, although it is unsat.

<details><summary>Solution</summary>

The length rule gives $|x| + |y| = 3$, so $2|x| = 3$, which has no integer solution.

The formula $x \cdot a = b \cdot x$ is unsat, and its abstraction $|x| + 1 = 1 + |x|$ is valid, so the abstraction does not refute it. Worked example 3 gives the refutation.

</details>

4. Trace the calculus on $x \cdot c \cdot y = ab \cdot z \land x = b$, and report the verdict.

<details><summary>Solution</summary>

From $x = b$, $x$ has the normal form $b$. The flat forms are $(b, c, y)$ and $(a, b, z)$. The first components are constants of the same length, and they are distinct. So this is a conflict, and the verdict is unsat. Z3 and cvc5 both return unsat with the additional redundant constraint $|x| = 1$.

</details>

5. Prove the Lyndon-Schützenberger commutation theorem for two words: if $x \cdot y = y \cdot x$, then there is a word $w$ with $x = w^i$ and $y = w^j$ for some $i, j \ge 0$.

<details><summary>Solution</summary>

Use induction on $|x| + |y|$. If $x = \epsilon$, take $w = y$, with $i = 0$ and $j = 1$. Symmetrically for $y = \epsilon$. These cases cover the base case.

Otherwise, assume without loss of generality that $1 \le |x| \le |y|$. Since $x \cdot y = y \cdot x$, the word $x$ is a prefix of $y$, so $y = x \cdot t$. Substitute: $x \cdot x \cdot t = x \cdot t \cdot x$. Cancelling $x$ gives $x \cdot t = t \cdot x$. Since $|x| + |t| < |x| + |y|$, the induction hypothesis gives $x = w^i$ and $t = w^j$. Then $y = w^{i + j}$. $\square$

</details>

6. Using exercise 5, decide $x \cdot y = y \cdot x \land x = ab \land |y| = 3$, and decide the same with $y = abab$.

<details><summary>Solution</summary>

The word $x = ab$ has no shorter period, so $x = w^i$ forces $w = ab$ and $i = 1$, as $ab$ is not a power of a character. Then $y = (ab)^j$ has even length, contradicting $|y| = 3$. So the first formula is unsat.

With $y = abab = (ab)^2$, both sides equal $ababab$, so the second is sat. Z3 and cvc5 agree on both.

</details>

7. Prove that $x \cdot y = y \cdot z$ with $|x| = 1$ implies $x = z$, by induction on $|y|$. Compare with the argument in Worked example 5.

<details><summary>Solution</summary>

Lengths give $|z| = 1$.

If $|y| = 0$, then $x = z$. Suppose $|y| = n + 1$. The first character of the right side is the first character of $y$, and the first character of the left side is $x$. So $y = x \cdot y'$, with $|y'| = n$. Substituting gives $x \cdot x \cdot y' = x \cdot y' \cdot z$. Cancelling gives $x \cdot y' = y' \cdot z$. The induction hypothesis gives $x = z$. $\square$

This is the same argument as in the worked example, and the induction variable is exactly what a Levi-based solver lacks: each split gives another instance of the same equation with a fresh variable, so it needs a loop-breaking rule or a more general lemma to stop.

</details>

8. Use the Card rule with a two-letter alphabet to refute that three pairwise distinct strings of length 1 exist.

<details><summary>Solution</summary>

All three classes share length 1, and they are pairwise distinct, so they are in one bucket $B$ with $|B| = 3$. Card adds

$$
\mathrm{len}\ B > \lfloor \log_2(3 - 1) \rfloor = 1.
$$

This contradicts length 1, and the verdict is unsat. Z3 and cvc5 both return unsat when the three variables are constrained to the character range from $a$ to $b$.

</details>

9. Give the reduction of $\neg \mathrm{contains}(x, y)$, and explain why it is more expensive than the reduction of $\mathrm{contains}(x, y)$.

<details><summary>Solution</summary>

The formula $\mathrm{contains}(x, y)$ reduces to $x = u \cdot y \cdot v$, with fresh $u, v$, which is a single equation.

The negation reduces to

$$
|y| > |x| \;\lor\; \forall i.\ 0 \le i \le |x| - |y| \to \mathrm{substr}(x, i, |y|) \ne y.
$$

It is a universal quantifier over a bounded integer range whose bound is not constant. A solver instantiates it on demand. Each instance adds a substring term and a disequality, and the number of instances can grow with $|x|$. If the length of $x$ is not bounded by the other constraints, then this instantiation may fail to terminate.

</details>

10. Design a bounded-length string solver based on a SAT or bit-vector encoding. State the encoding, the meaning of its answers and how you would increase the bound. Explain precisely when it can report unsat for the unbounded problem.

<details><summary>Solution</summary>

Encoding. Fix a bound $k$. Represent each string variable $x$ by a length vector $|x| \le k$ and an array of $k$ character vectors. Concatenation $z = x \cdot y$ is encoded by a case split on $|x|$, with position-wise equalities $z[i] = x[i]$ for $i < |x|$ and $z[i + |x|] = y[i]$ for the remainder. Regular membership unfolds an automaton for $k$ steps.

Answers. A model of the encoding gives a real solution, by construction, so the answer sat is correct. Unsat under the bound means only that no solution of this size exists.

Increasing the bound. Run with $k = 2, 4, 8, \dots$. Assert the bound as an assumption literal, so that the core tells you whether it was needed. This is an incremental scheme.

Reporting unsat. If the unsat core does not contain the bound assumption, then the refutation did not use it. This means that the encoding's remaining clauses, which are valid in the unbounded theory only if they hold without the bound, are contradictory. This requires an encoding whose clauses without the assumption are sound for arbitrary lengths, which is rarely the case for direct position encodings. In practice, you would first check the length abstraction in LIA, and use it to compute an upper bound on lengths. If LIA entails a finite bound on all lengths and $k$ reaches that bound, then unsat is final. Otherwise, the solver must answer unknown.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- State and prove Levi's lemma, and apply it to a word equation.
- Trace a length-aware procedure on a small equation, with flat forms and with F-Unify, F-Split and a conflict.
- Show why a self-reproducing equation makes naive splitting diverge, and resolve it by F-Loop.
- Reduce `substr` and `contains`, and explain the cost of the negative case.
- Unfold a star membership constraint by hand.
- List the sources of incompleteness, and state what can be guaranteed regarding verdicts.
- State the decidability results of Makanin and Plandowski, and state which combination remains open.

## Materials

- Liang et al., A DPLL(T) Theory Solver for a Theory of Strings and Regular Expressions, CAV 2014. Read it for the calculus, the combination with arithmetic and its worked examples.
- Reynolds, Woo, Barrett, Brumley, Liang and Tinelli, Scaling Up DPLL(T) String Solvers Using Context-Dependent Simplification, CAV 2017. Read it for the treatment of extended functions.
- Ganesh, Minnes, Solar-Lezama and Rinard, Word Equations with Length Constraints: What's Decidable?, HVC 2012. Read it for the status of the combination with lengths.
- Plandowski, Satisfiability of Word Equations with Constants Is in PSPACE, JACM 2004. Read it for the complexity upper bound.
- Lin and Barceló, String Solving with Word Equations and Transducers: Towards a Logic for Analysing Mutation XSS, POPL 2016. Read it for the straight-line fragment.
- Stanford, Veanes and Bjørner, Symbolic Boolean Derivatives for Efficiently Solving Extended Regular Expression Constraints, PLDI 2021. Read it for the use of derivatives in a solver.
