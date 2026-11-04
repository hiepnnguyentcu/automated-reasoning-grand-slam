# Bit-Vectors

Part 2, Chapter 5: SMT.

## Objective

Bit-blast bit-vector formulas by hand and explain word-level simplification.

## Why this matters

Machine integers are bit-vectors. Reasoning about overflow, masks, shifts, cryptographic code or compiled binaries requires modular arithmetic at a fixed width, and treating these as mathematical integers gives wrong answers. The dominant procedure translates a formula into SAT, so it exercises everything from [Chapter 4](../../04-sat/). It also shows a theme that appears across solver engineering: most of the performance comes from what happens before the SAT solver starts. You will implement it in [Bit-Blasting](../../../part-3-building-the-engines/10-smt-solver/bit-blasting/), and it underlies the cryptographic work of [Chapter 16](../../../part-5-real-systems/16-cryptographic-assurance/).

## Prerequisites

- [Encodings](../../04-sat/encodings/), for the Tseitin transformation.
- [CDCL](../../04-sat/cdcl/), for what the back end does with the result.
- [DPLL(T)](../dpllt/), for the alternative lazy architecture.

## Lesson

### Syntax and semantics

A bit-vector of width $n$ is a sequence of $n$ bits $x_{n-1} \dots x_1 x_0$, where $x_0$ is the least significant. Its unsigned value and its signed (two's complement) value are

$$
\langle x \rangle_u = \sum_{i=0}^{n-1} x_i 2^i, \qquad\qquad \langle x \rangle_s = -x_{n-1} 2^{n-1} + \sum_{i=0}^{n-2} x_i 2^i.
$$

Both views share the same bit patterns. The operations addition, subtraction and multiplication are the same for signed and unsigned values, because they are arithmetic modulo $2^n$. Order, division, remainder and right shift are different for the two views, so SMT-LIB has separate operators, such as `bvult` and `bvslt`.

| Operation | Meaning |
|---|---|
| $x + y$, $x - y$, $x \cdot y$ | The result is the value modulo $2^n$. |
| $-x$ | The result is $2^n - \langle x \rangle_u$ modulo $2^n$, which equals $\sim x + 1$. |
| $x \,\&\, y$, $x \mid y$, $x \oplus y$, $\sim x$ | The operation applies to each bit independently. |
| $x[j:i]$ | Extraction yields the bits from position $j$ down to position $i$. |
| $x \circ y$ | Concatenation places $x$ in the more significant positions. |
| Zero and sign extension | Extension adds high bits that are 0 or that copy the sign bit. |
| $x \ll y$, logical and arithmetic $x \gg y$ | The shift amount is the unsigned value of $y$, and shifting by at least $n$ gives all zeros or all sign bits. |

Division by zero needs a definition, because every function in the logic is total. SMT-LIB defines `bvudiv` by zero to give the all-ones vector and `bvurem` by zero to give the dividend. Z3 evaluates `bvudiv` of 5 by 0 at width 8 to 255, and `bvurem` of 5 by 0 to 5.

Familiar laws of the integers often fail. For example, $x + 1 >_s x$ is not valid, because at the largest signed value the addition wraps around: at width 4, $x = 7$ gives $x + 1 = -8$. The mathematical implication $a \le b \to a + c \le b + c$ fails also. This is why a program verifier that models integers as unbounded misses real bugs.

### Decidability and the eager approach

With a fixed width, each variable has finitely many values, so the theory is decidable, and with widths written in unary the quantifier-free problem is NP-complete, since a formula over width 1 vectors is exactly a propositional formula. The two main routes are as follows.

Eager bit-blasting translates all operators into a single CNF, which is then given to a SAT solver. Solvers normally do this after extensive word-level simplification.

Lazy bit-blasting keeps a DPLL(T) core for the Boolean skeleton and word-level atoms, and it bit-blasts the asserted atoms in a subordinate SAT solver. cvc5 implements both modes, and its paper notes that the eager mode allows more simplification because all constraints go to one SAT solver.

### Bit-blasting by circuits

Each term $t$ of width $n$ gets a vector of propositional literals $[t]_{n-1}, \dots, [t]_0$. For each operator, we write a circuit that defines the result bits in terms of the argument bits, and we use the Tseitin transformation to obtain clauses. Terms are shared as in a DAG, so a repeated subterm costs only once.

Bitwise operators. For $z = x \,\&\, y$, add for each $i$ the definition $z_i \leftrightarrow x_i \land y_i$, which gives the three clauses $(\neg z_i \lor x_i)$, $(\neg z_i \lor y_i)$ and $(z_i \lor \neg x_i \lor \neg y_i)$. Other bitwise operators are similar. Extraction and concatenation use no new variables at all, because they only rename existing literals.

Equality. The atom $x = y$ defines a literal $e$ with $e \leftrightarrow \bigwedge_i (x_i \leftrightarrow y_i)$. This needs one auxiliary literal for each bit and one for the conjunction.

Addition. A ripple-carry adder uses, for $i = 0, \dots, n-1$ with $c_0 = \bot$,

$$
s_i \leftrightarrow x_i \oplus y_i \oplus c_i, \qquad\qquad c_{i+1} \leftrightarrow \mathrm{maj}(x_i, y_i, c_i),
$$

where $\mathrm{maj}(a, b, c) = (a \land b) \lor (a \land c) \lor (b \land c)$. Direct CNF for the three-input XOR has 8 clauses, and direct CNF for the majority has 6 clauses, so a full adder has 14 clauses and an adder is linear in $n$. Subtraction is $x + \sim y + 1$, that is, the adder with $\sim y$ and $c_0 = \top$.

Unsigned comparison. A comparator can be read as the carry chain of a subtraction. Define $l_0 = \bot$ and, for $i = 0, \dots, n-1$,

$$
l_{i+1} \leftrightarrow \mathrm{maj}(\neg a_i, b_i, l_i).
$$

Then $a <_u b$ holds if and only if $l_n$ is true. The value $l_{i+1}$ says that the low $i + 1$ bits of $a$ are less than those of $b$: the relation is decided by bit $i$ if the bits differ, and by $l_i$ if the bits are equal. Signed comparison reduces to unsigned by flipping the sign bits: $a <_s b$ if and only if $(a \oplus 2^{n-1}) <_u (b \oplus 2^{n-1})$.

Shifts. A variable shift uses a barrel shifter. For $n = 2^k$, it has $k$ stages. Stage $j$ conditionally shifts by $2^j$ according to bit $j$ of the shift amount, using one multiplexer for each bit. Any higher bits of the amount, if set, force the result to zero, or to the sign in the arithmetic case. This costs $O(n \log n)$ multiplexers. A check with Z3 confirmed this construction at width 4.

Multiplication. The product has the shift-and-add form

$$
x \cdot y = \sum_{i=0}^{n-1} y_i \cdot 2^i \cdot x \pmod{2^n},
$$

which is $n$ partial products and $n - 1$ adders. Thus the size is $O(n^2)$. Multipliers are the hard case for SAT solvers. A miter that asks whether $x \cdot y \ne y \cdot x$ at the bit level is a well-known hard family for CDCL. In contrast, Z3 5.3.3 answered the same question at widths 8, 10 and 12 in under a millisecond in a test made for this topic, which is consistent with word-level normalization rewriting both sides to one term before any bit-blasting occurs.

Division. Express it as a constraint rather than a circuit. For unsigned $q = a / b$ and $r = a \bmod b$ with $b \ne 0$, introduce fresh $q$ and $r$ and require that

$$
\langle q \rangle_u \cdot \langle b \rangle_u + \langle r \rangle_u = \langle a \rangle_u \text{ with no overflow}, \qquad\qquad r <_u b.
$$

The arithmetic is computed in width $2n$, or with an explicit overflow check. Add the case $b = 0$ according to the SMT-LIB definition. This uses an inverted multiplier, which helps the solver propagate in both directions.

### Word-level simplification

Bit-blasting loses the word structure, and a CDCL solver cannot rediscover much of it within a reasonable time. So solvers work first at the word level.

Rewriting and normalization. Simple rules include constant folding, $x \,\&\, 0 = 0$, $x - x = 0$, $x \oplus x = 0$, and the distribution of extraction over concatenation and bitwise operators. Arithmetic normalization rewrites sums to a canonical order with collected coefficients, so that $x + y + x$ and $2x + y$ become one term. Boolector's paper describes rewriting at three levels: basic rules during construction, global term substitutions together with static analysis, and arithmetic normalization.

Equational solving. If an equation can be solved for a variable, it can be eliminated. For linear equations modulo $2^n$, the following result is the basis of this.

Proposition. The equation $a x = b$ at width $n$, with nonzero $a = 2^k a'$ and $a'$ odd, has a solution if and only if $2^k \mid b$. When solvable, it has exactly $2^k$ solutions, namely

$$
x \equiv (a')^{-1} \cdot (b / 2^k) \pmod{2^{n-k}}.
$$

Proof. An odd number is invertible modulo a power of 2. If $a x \equiv b \pmod{2^n}$, then $2^k$ divides $b$, since it divides both $a x$ and $2^n$. Dividing by $2^k$ gives the equivalent equation $a' x \equiv b/2^k \pmod{2^{n-k}}$. Multiply by the inverse of $a'$ modulo $2^{n-k}$. The solution is unique modulo $2^{n-k}$, which gives $2^k$ values modulo $2^n$. $\square$

Thus any occurrence of an odd coefficient allows a solved form, and the variable disappears.

Unconstrained variables. If a variable occurs only once in the formula, then some operators can be replaced by fresh variables. For example, if $x$ occurs only in the term $x + t$, then $x + t$ takes every value as $x$ varies, regardless of $t$. So one can replace $x + t$ with a fresh variable, and that may make $t$ itself irrelevant. In a similar way, a variable bit extracted once can be replaced. To output a model, the solver must keep a record to compute $x$ from the new variable.

Slicing. If a variable is always used through extractions on fixed ranges, split it into independent parts. This reduces coupling.

Abstraction and refinement. A solver can replace an expensive term, such as a multiplier, by a fresh variable, solve, and add the definition only if the candidate model fails. In the reverse direction, under-approximation restricts variables, for example by fixing high bits, to find models faster, as Boolector supports at the CNF level. If the restricted formula is sat, so is the original. If not, the restriction is relaxed.

Other methods. Propagation-based local search works at the word level by choosing values for inputs to satisfy a target output. Int-blasting translates bit-vector constraints to integer arithmetic, and cvc5's paper notes that it implements this technique alongside bit-blasting.

## Worked examples

### Worked example 1: bit-blast $x + 1 <_u x$ at width 2

We decide whether there is a 2-bit $x$ with $x + 1 <_u x$.

Let $x = x_1 x_0$. The sum $s = x + 1$ is the adder with $y = 01$ and $c_0 = \bot$. For bit 0, the inputs are $x_0$, $\top$ and $\bot$. For bit 1, the inputs are $x_1$, $\bot$ and $c_1$. Simplifying the gates gives

$$
s_0 \leftrightarrow \neg x_0, \qquad c_1 \leftrightarrow x_0, \qquad s_1 \leftrightarrow x_1 \oplus c_1.
$$

The comparator with $a = s$, $b = x$ is $l_1 \leftrightarrow \mathrm{maj}(\neg s_0, x_0, \bot) = \neg s_0 \land x_0$, and $l_2 \leftrightarrow \mathrm{maj}(\neg s_1, x_1, l_1)$. The top-level assertion is the unit clause $l_2$.

The Tseitin clauses are the following.

```
s0 <-> ¬x0:           (s0 ∨ x0) (¬s0 ∨ ¬x0)
c1 <-> x0:            (¬c1 ∨ x0) (c1 ∨ ¬x0)
s1 <-> x1 xor c1:     (¬s1 ∨ x1 ∨ c1) (¬s1 ∨ ¬x1 ∨ ¬c1) (s1 ∨ ¬x1 ∨ c1) (s1 ∨ x1 ∨ ¬c1)
l1 <-> ¬s0 and x0:    (¬l1 ∨ ¬s0) (¬l1 ∨ x0) (l1 ∨ s0 ∨ ¬x0)
l2 <-> maj(¬s1,x1,l1): (s1 ∨ ¬x1 ∨ l2) (s1 ∨ ¬l1 ∨ l2) (¬x1 ∨ ¬l1 ∨ l2)
                       (¬s1 ∨ x1 ∨ ¬l2) (¬s1 ∨ l1 ∨ ¬l2) (x1 ∨ l1 ∨ ¬l2)
assertion:            (l2)
```

Now run CDCL by hand. Unit propagation gives $l_2$. The clauses of $l_2$ reduce to $(\neg s_1 \lor x_1)$, $(\neg s_1 \lor l_1)$ and $(x_1 \lor l_1)$. There are no more unit clauses. Decide $x_0 = \bot$ at level 1.

```
step  literal  level  reason
 1    l2       0      (l2)
 2    ¬x0      1      decision
 3    s0       1      (s0 ∨ x0)
 4    ¬c1      1      (¬c1 ∨ x0)
 5    ¬l1      1      (¬l1 ∨ x0)
 6    ¬s1      1      (¬s1 ∨ l1 ∨ ¬l2)
 7    x1       1      (x1 ∨ l1 ∨ ¬l2)
 8    conflict        (s1 ∨ ¬x1 ∨ c1) is falsified
```

Analysis resolves the conflict clause with the reasons in reverse order.

```
start                               (s1 ∨ ¬x1 ∨ c1)
resolve on x1 with (x1 ∨ l1 ∨ ¬l2)  (s1 ∨ c1 ∨ l1 ∨ ¬l2)
resolve on s1 with (¬s1 ∨ l1 ∨ ¬l2) (c1 ∨ l1 ∨ ¬l2)
resolve on l1 with (¬l1 ∨ x0)       (c1 ∨ x0 ∨ ¬l2)
resolve on c1 with (¬c1 ∨ x0)       (x0 ∨ ¬l2)
```

The clause $(x_0 \lor \neg l_2)$ has one literal at level 1, so analysis stops. The solver backjumps to level 0 and asserts $x_0$. The following propagations result.

```
step  literal  level  reason
 9    x0       0      (x0 ∨ ¬l2)
10    ¬s0      0      (¬s0 ∨ ¬x0)
11    c1       0      (c1 ∨ ¬x0)
12    l1       0      (l1 ∨ s0 ∨ ¬x0)
```

The remaining clauses reduce to $(\neg s_1 \lor \neg x_1)$, $(s_1 \lor x_1)$ and $(\neg s_1 \lor x_1)$. Resolving the first and third gives $\neg s_1$, and then the second gives $x_1$. So the model is $x_1 = \top$, $x_0 = \top$, that is, $x = 3$. Then $s = 0$, and $0 <_u 3$. A brute-force enumeration confirmed $x = 3$ is the unique solution. Z3 likewise gives 3 at width 2, 7 at width 3 and 15 at width 4.

### Worked example 2: word-level solving before bit-blasting

Decide at width 4: $3x + 2 = 7 \land x <_u y$.

The term $3x + 2 = 7$ normalizes to $3x = 5$. The coefficient 3 is odd, and its inverse modulo 16 is 11, since $3 \cdot 11 = 33 \equiv 1 \pmod{16}$. So $x = 11 \cdot 5 = 55 \equiv 7 \pmod{16}$. Check: $3 \cdot 7 + 2 = 23 \equiv 7 \pmod{16}$.

The solver substitutes $x = 7$. What remains is $7 <_u y$, with $y$ otherwise unconstrained. The comparator with a constant needs only a few simplified gates, whereas bit-blasting $3x$ as a multiplier would have created adders for no benefit. Any value such as $y = 8$ gives a model. Z3 reports sat with $x = 7$.

Now consider the even coefficient case $6x = 4$ at width 4. Here $a' = 3$ and $k = 1$, and $2 \mid 4$. Dividing gives $3x \equiv 2 \pmod 8$. The inverse of 3 modulo 8 is 3, so $x \equiv 6 \pmod 8$. The solutions are $x \in \{6, 14\}$, as an enumeration confirms.

### Worked example 3: a 2-bit multiplier by hand

Find 2-bit $x, y$ with $x \cdot y = 2$ and $x <_u y$.

The product of 2-bit values modulo 4 is

$$
p_0 \leftrightarrow x_0 \land y_0, \qquad p_1 \leftrightarrow (x_1 \land y_0) \oplus (x_0 \land y_1),
$$

since the partial product $x \cdot y_0$ contributes $x_1 x_0$, and $2 \cdot x \cdot y_1$ contributes $x_0$ in position 1. The bits above position 1 fall away by the modulus.

Require $p_1 = \top$ and $p_0 = \bot$. From $p_0 = \bot$, at least one of $x_0, y_0$ is false. Consider cases.

- If $x_0 = \bot$ and $y_0 = \bot$, then both products in $p_1$ are false. So $p_1 = \bot$, a contradiction.
- If $x_0 = \bot$ and $y_0 = \top$, then $p_1 = x_1$. So $x_1 = \top$ and $x = 2$, while $y = y_1 1$ is 1 or 3.
- If $x_0 = \top$ and $y_0 = \bot$, then $p_1 = y_1$. So $y_1 = \top$ and $y = 2$, while $x$ is 1 or 3.

The solution set is $(x, y) \in \{(2, 1), (2, 3), (1, 2), (3, 2)\}$, which an enumeration confirms. The constraint $x <_u y$ leaves $(2, 3)$ and $(1, 2)$. Z3 returns one of these, $(2, 3)$.

## Common mistakes

- Confusing signed and unsigned comparison. The vector $1000$ at width 4 is 8 as an unsigned value and $-8$ as a signed value, so $1000 <_s 0001$ holds while $1000 <_u 0001$ fails.
- Assuming integer laws for bit-vectors. Cancellation $x \cdot z = y \cdot z \to x = y$ fails, even for $z \ne 0$, when $z$ is even.
- Computing the wrong bit positions. Extraction $x[j:i]$ has width $j - i + 1$, and position 0 is the least significant bit, which is the rightmost.
- Forgetting the width of the multiplication result. The operator `bvmul` truncates, so a detection of overflow needs a wider multiplication or a dedicated check.
- Handling shift amounts by their low bits only. A shift amount of at least the width gives zero or the sign fill, which differs from the behaviour of many processors, and from C, where the operation is undefined.
- Forgetting the SMT-LIB definition of division by zero. It is a total function with fixed results, and a solver gives no error for it. A property about division may be falsified exactly at $b = 0$.
- Thinking that eager bit-blasting is the whole solver. The rewriting phase often determines whether a problem is solved at all.
- Treating an even coefficient as invertible. The equation $2x = 1$ has no solution at any width, and $4x = 8$ at width 4 has four solutions.

## Exercises

1. At width 4, give the unsigned and signed value of $1011$ and $0111$. Compute $0111 + 0001$, and say whether signed overflow occurred.

<details><summary>Solution</summary>

The vector $1011$ has unsigned value 11 and signed value $-8 + 3 = -5$. The vector $0111$ has unsigned and signed value 7. The sum $0111 + 0001 = 1000$ has signed value $-8$. Two positive numbers gave a negative result, so signed overflow occurred. Unsigned overflow did not occur, since $7 + 1 = 8 < 16$.

</details>

2. Compute $10110100[5:2]$, $10 \circ 011$, and the zero and sign extensions by 2 of $101$.

<details><summary>Solution</summary>

Position numbering from the right gives $10110100[5:2] = 1101$, which has value 13. The concatenation is $10011$, which has value 19. The zero extension is $00101$, with value 5. The sign extension is $11101$, which has unsigned value 29 and signed value $-3$. These have been evaluated by Z3.

</details>

3. Write the CNF for a full adder, and verify that the XOR has 8 clauses and the majority has 6 clauses.

<details><summary>Solution</summary>

For $s \leftrightarrow a \oplus b \oplus c$, the eight clauses are one for each row of the truth table of $(a, b, c)$:

$$
\begin{aligned}
&(\neg a \lor \neg b \lor \neg c \lor s), \quad (\neg a \lor \neg b \lor c \lor \neg s), \quad (\neg a \lor b \lor \neg c \lor \neg s), \quad (\neg a \lor b \lor c \lor s), \\
&(a \lor \neg b \lor \neg c \lor \neg s), \quad (a \lor \neg b \lor c \lor s), \quad (a \lor b \lor \neg c \lor s), \quad (a \lor b \lor c \lor \neg s).
\end{aligned}
$$

For $d \leftrightarrow \mathrm{maj}(a, b, c)$, the six clauses are:

$$
(\neg a \lor \neg b \lor d), \quad (\neg a \lor \neg c \lor d), \quad (\neg b \lor \neg c \lor d), \quad (a \lor b \lor \neg d), \quad (a \lor c \lor \neg d), \quad (b \lor c \lor \neg d).
$$

The first three say that if two inputs are true then $d$ is true. The last three say that if two inputs are false then $d$ is false. Any three Boolean inputs contain two that agree, so at least one of the two groups applies, and $d$ is determined.

</details>

4. Solve $5x + 3 = 1$ at width 8. Then solve $4x = 8$ at width 4, and show that $2x = 1$ has no solution.

<details><summary>Solution</summary>

The first equation is $5x = -2 \equiv 254 \pmod{256}$. The inverse of 5 is 205, since $5 \cdot 205 = 1025 \equiv 1 \pmod{256}$. So $x = 205 \cdot 254 = 52070 \equiv 102 \pmod{256}$. Check: $5 \cdot 102 + 3 = 513 \equiv 1 \pmod{256}$.

For $4x = 8$ at width 4, $k = 2$ and $a' = 1$, and $4 \mid 8$. Dividing gives $x \equiv 2 \pmod 4$, so $x \in \{2, 6, 10, 14\}$.

For $2x = 1$, $k = 1$ and 2 does not divide 1. Directly, $2x$ modulo $2^n$ is always even, so it cannot equal 1. These have been confirmed by enumeration.

</details>

5. Prove the comparator recurrence: if $l_0 = \bot$ and $l_{i+1} \leftrightarrow \mathrm{maj}(\neg a_i, b_i, l_i)$, then $l_i$ is true if and only if the low $i$ bits of $a$ are less, as an unsigned value, than the low $i$ bits of $b$.

<details><summary>Solution</summary>

By induction on $i$. For $i = 0$, both are empty and neither is less, so $l_0 = \bot$ is correct.

Assume the claim for $i$. Consider the bits $a_i, b_i$.

If $a_i = 0$ and $b_i = 1$, the majority has two true inputs, so $l_{i+1}$ is true. And the low $i + 1$ bits of $a$ are less, since the top bit dominates the sum of all lower terms.

If $a_i = 1$ and $b_i = 0$, the majority has two false inputs, so $l_{i+1}$ is false. And the low $i + 1$ bits of $a$ are greater.

If $a_i = b_i$, then $\neg a_i$ and $b_i$ have opposite values, so the majority equals $l_i$. And the comparison is decided by the lower $i$ bits, which is correct by the hypothesis. $\square$

A check confirmed this recurrence for all pairs at widths 2, 3 and 4.

</details>

6. Prove that $a <_s b$ if and only if $(a \oplus 2^{n-1}) <_u (b \oplus 2^{n-1})$.

<details><summary>Solution</summary>

Flipping the sign bit gives $\langle a \oplus 2^{n-1} \rangle_u = \langle a \rangle_s + 2^{n-1}$. To see this, if $a_{n-1} = 0$, the signed value is $\langle a \rangle_u$, and flipping adds $2^{n-1}$. If $a_{n-1} = 1$, the signed value is $\langle a \rangle_u - 2^n$, and flipping subtracts $2^{n-1}$ from the unsigned value, giving $\langle a \rangle_u - 2^{n-1} = \langle a \rangle_s + 2^{n-1}$.

So the map from signed values to these unsigned values is the translation by $2^{n-1}$, which preserves the order, and the statement follows. $\square$

</details>

7. Prove that $x + y = (x \oplus y) + 2 \cdot (x \,\&\, y)$ for bit-vectors at any width. Then explain why a word-level rewriter wants such a rule.

<details><summary>Solution</summary>

For one bit, $x_i + y_i = (x_i \oplus y_i) + 2(x_i \land y_i)$ as integers: check the four cases $0 + 0$, $0 + 1$, $1 + 0$ and $1 + 1$. Multiply by $2^i$ and sum over $i$ to obtain

$$
\langle x \rangle_u + \langle y \rangle_u = \langle x \oplus y \rangle_u + 2 \langle x \,\&\, y \rangle_u
$$

over the integers. Since no carries remain in this bit-independent form, taking both sides modulo $2^n$ gives the identity. A check with Z3 at width 4 confirmed it.

Bit-blasting the two sides gives two structurally different adders, and a SAT solver has to prove their equivalence with no structural hint, so these equivalences are hard to detect after translation. A rule or a normalization that recognises this form at the word level removes the problem before it arises. This occurs in optimized and obfuscated code.

</details>

8. Build a barrel shifter for a left shift at width 4, with the shift amount a 4-bit vector $s$. Give the stages and the handling of large amounts.

<details><summary>Solution</summary>

Let $z^{(0)} = x$. Stage 0 defines $z^{(1)}$ by, for each bit $i$, $z^{(1)}_i \leftrightarrow \text{if } s_0 \text{ then } z^{(0)}_{i-1} \text{ else } z^{(0)}_i$, where $z^{(0)}_{-1} = \bot$. Stage 1 defines $z^{(2)}$ by, for each bit $i$, $z^{(2)}_i \leftrightarrow \text{if } s_1 \text{ then } z^{(1)}_{i-2} \text{ else } z^{(1)}_i$, where negative positions give $\bot$.

The remaining bits $s_2, s_3$ correspond to shifts of at least 4, so the result is zero if either is set. The final bit is $z_i \leftrightarrow \neg s_2 \land \neg s_3 \land z^{(2)}_i$. A check with Z3 confirmed this equals $x \ll s$ at width 4 for all inputs.

The cost is $n$ multiplexers per stage, with $\log_2 n$ stages, which is 8 multiplexers and 4 final conjunctions here.

</details>

9. Consider the formula $F$ over $x$, $y$ at width 8 given by $(x \oplus y) \cdot y >_u 3$, where $x$ occurs only once. Apply the unconstrained variable idea. Report what remains, and explain how to recover a model.

<details><summary>Solution</summary>

Let $u = x \oplus y$. Since XOR with a fixed $y$ is a bijection on $x$, $u$ can take every value whatever $y$ is. So replace $u$ by a fresh variable. The formula is $u \cdot y >_u 3$. Multiplication is not a bijection on $u$ for all $y$, so the process stops there. The result removes the XOR circuit and removes the variable $x$.

Solve the result, for instance with $u = 4, y = 1$. To recover the model, keep the record $x := u \oplus y$, so that $x = 5$, and check $(5 \oplus 1) \cdot 1 = 4 >_u 3$.

</details>

10. Design an abstraction-refinement loop for multiplication at large width. State the abstraction, the check and how you would refine, and argue that it is sound and terminates.

<details><summary>Solution</summary>

Abstraction. Replace each multiplication $x \cdot y$ with a fresh vector $m_{xy}$, so the abstract formula has no multiplier circuits.

Check. Solve the abstract formula. If it is unsat, the original is unsat, since the abstraction has only removed constraints. If it is sat with a model $M$, evaluate each multiplication with the values $M(x)$ and $M(y)$. If each one matches $M(m_{xy})$, then $M$ is a model of the original.

Refinement. For a failing multiplication, add a lemma that excludes the current spurious value. Options in increasing strength are:

- the instance lemma $x = M(x) \land y = M(y) \to m_{xy} = M(x) \cdot M(y)$;
- simple valid lemmas, such as the one that links the low bits: $(x \cdot y)[0:0] = x[0:0] \,\&\, y[0:0]$;
- the full multiplier definition for that one term.

Soundness. Each lemma is valid for the true product, so every model of the original extends to the refined abstraction, and unsat is sound. The sat answer is checked by evaluation, so it is sound as well.

Termination. Each refinement excludes at least one candidate for the abstract variables. There are finitely many values at a fixed width, and the worst case is bounded by adding the full definitions.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Give the signed and unsigned values of a vector, and state which operators differ between the two views.
- Write bit-blasting circuits for addition, comparison, variable shift and multiplication, and produce Tseitin clauses for each.
- Bit-blast a small formula by hand, run CDCL on the clauses and read a model off the result.
- Solve linear equations modulo $2^n$, including the case of an even coefficient.
- Explain why word-level simplification matters, with examples of rewriting, solving and unconstrained-variable elimination.
- State the SMT-LIB definitions for division by zero and for large shifts.

## Materials

- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the chapter on bit vectors for flattening and the construction of arithmetic circuits.
- Brummayer and Biere, Boolector: An Efficient SMT Solver for Bit-Vectors and Arrays, TACAS 2009. Read it for how term rewriting, bit-blasting, under-approximation and lemmas on demand are organized in one tool.
- Ganesh and Dill, A Decision Procedure for Bit-Vectors and Arrays, CAV 2007. Read it for word-level solving and refinement in the STP solver.
- [SMT-LIB theory of fixed-size bit-vectors.](https://smt-lib.org/theories-FixedSizeBitVectors.shtml) Read it for the exact semantics of each operator.
