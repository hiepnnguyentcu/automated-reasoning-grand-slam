# Arithmetic

Part 2, Chapter 5: SMT.

## Objective

Trace simplex for linear real arithmetic, branch and bound for integers, and explain the nonlinear case.

## Why this matters

Almost every verification query contains arithmetic, from array bounds and loop counters to the cost models of resource analyses. The simplex-based procedure in this topic is the most commonly used arithmetic theory solver, and tracing it by hand is half of the proof of mastery for this chapter. Understanding it tells you why integer queries are harder than real ones, why strict inequalities need special treatment, and why adding a nonlinear term can change a query that takes milliseconds into one that times out. You will implement the procedure in [Simplex for Linear Arithmetic](../../../part-3-building-the-engines/10-smt-solver/simplex-for-linear-arithmetic/).

## Prerequisites

- [DPLL(T)](../dpllt/), for what a theory solver must provide.
- [Decidable Fragments](../../../part-1-foundations/02-decidability-and-complexity/decidable-fragments/), for Presburger arithmetic.
- [Undecidability of Logic and Incompleteness](../../../part-1-foundations/02-decidability-and-complexity/undecidability-of-logic-and-incompleteness/), for the limits of arithmetic.

## Lesson

### The landscape

| Fragment | Atoms and domain | Status of the conjunction problem |
|---|---|---|
| LRA | Linear constraints over the rationals or reals. | It is decidable in polynomial time, by Khachiyan's ellipsoid result. |
| LIA | Linear constraints over the integers. | It is NP-complete. |
| IDL and RDL | Constraints $x - y \le c$ over integers or reals. | It is decidable in polynomial time by negative-cycle detection. |
| NRA | Polynomial constraints over the reals. | It is decidable, as Tarski showed, and CAD has doubly exponential worst-case cost in the number of variables. |
| NIA | Polynomial constraints over the integers. | It is undecidable, by Matiyasevich's solution of Hilbert's tenth problem. |

Practical LRA solvers use simplex, although it has exponential worst-case behaviour, because it is fast in practice and easy to make incremental and backtrackable.

### General form

The procedure of Dutertre and de Moura separates the problem into two parts. The linear equations never change, and only bounds are asserted and retracted. This matches what DPLL(T) wants, because backtracking becomes removal of bounds.

For each distinct linear form $\sum_j a_j x_j$ occurring in an atom with at least two variables, introduce a slack variable $s$ with the definition $s = \sum_j a_j x_j$. Each atom then becomes a bound on one variable:

$$
\sum_j a_j x_j \le c \quad \text{becomes} \quad s \le c, \qquad\qquad \sum_j a_j x_j \ge c \quad \text{becomes} \quad s \ge c.
$$

Forms that differ by a constant factor should share one slack variable. For example, $2x + 2y \le 3$ is normalized to $x + y \le 3/2$ first. An atom on one variable, such as $x \le 3$, needs no slack variable. A negated atom is also a bound: $\neg(s \le c)$ is $s > c$.

The problem is now to decide the system

$$
Ax = 0, \qquad l_i \le x_i \le u_i \text{ for all } i,
$$

where $A$ is a fixed matrix and some bounds may be infinite. The definitions are the rows of the initial tableau, and the slack variables are its initial basic variables.

### The tableau and the invariants

A tableau partitions the variables into basic variables $\mathcal{B}$ and nonbasic variables $\mathcal{N}$, with one row for each basic variable:

$$
x_i = \sum_{x_j \in \mathcal{N}} a_{ij} x_j \qquad (x_i \in \mathcal{B}).
$$

All tableaux that arise are equivalent systems of linear equations. The solver also keeps a current assignment $\beta$. It maintains the following invariants at all times.

1. The assignment $\beta$ satisfies all rows.
2. Each nonbasic variable satisfies its bounds: $l_j \le \beta(x_j) \le u_j$.

Only basic variables may violate their bounds. Since the row values of the basic variables are determined by the nonbasic values, the assignment is determined by the values of the nonbasic variables.

### The procedures

Variables are totally ordered, and the order is fixed. The following is the procedure of the paper, written in a compact form.

```
assert_upper(x_i <= c):
    if c >= u_i: return ok                  # the bound is redundant
    if c < l_i: return conflict {x_i <= c, x_i >= l_i}
    u_i := c
    if x_i is nonbasic and beta(x_i) > c: update(x_i, c)
    return ok

assert_lower(x_i >= c):                     # symmetric to assert_upper
    if c <= l_i: return ok
    if c > u_i: return conflict {x_i >= c, x_i <= u_i}
    l_i := c
    if x_i is nonbasic and beta(x_i) < c: update(x_i, c)
    return ok

update(x_j, v):                             # x_j is nonbasic
    for each basic x_k: beta(x_k) += a_kj * (v - beta(x_j))
    beta(x_j) := v

check():
    loop:
        x_i := the smallest basic variable with beta(x_i) < l_i or beta(x_i) > u_i
        if there is none: return sat
        if beta(x_i) < l_i:
            x_j := the smallest nonbasic variable with
                   (a_ij > 0 and beta(x_j) < u_j) or (a_ij < 0 and beta(x_j) > l_j)
            if there is none:
                return conflict {x_i >= l_i}
                    union {x_j <= u_j : a_ij > 0} union {x_j >= l_j : a_ij < 0}
            pivot_and_update(x_i, x_j, l_i)
        else:
            x_j := the smallest nonbasic variable with
                   (a_ij < 0 and beta(x_j) < u_j) or (a_ij > 0 and beta(x_j) > l_j)
            if there is none:
                return conflict {x_i <= u_i}
                    union {x_j >= l_j : a_ij > 0} union {x_j <= u_j : a_ij < 0}
            pivot_and_update(x_i, x_j, u_i)

pivot_and_update(x_i, x_j, v):
    theta := (v - beta(x_i)) / a_ij
    beta(x_i) := v
    beta(x_j) := beta(x_j) + theta
    for each other basic x_k: beta(x_k) += a_kj * theta
    pivot(x_i, x_j)     # solve the row of x_i for x_j and substitute it in the other rows
```

The pivot makes $x_j$ basic and $x_i$ nonbasic, and $x_i$ sits exactly at the violated bound, so invariant 2 holds for it. Because $x_j$ becomes basic, it may now violate its own bounds, and this is why the loop continues. In the row of $x_i$ with entering $x_j$ and coefficient $a$, the replacement is

$$
x_j = \frac{1}{a} x_i - \sum_{k \ne j} \frac{a_{ik}}{a} x_k.
$$

The candidate condition says that $x_j$ can move in the direction that pushes $x_i$ toward its bound. For a row with $x_i$ below its lower bound, $x_i$ must increase, so a positive coefficient needs $x_j$ to increase and a negative coefficient needs $x_j$ to decrease.

### Why a conflict is a proof

Suppose $\beta(x_i) < l_i$ and no candidate exists. Each $x_j$ with $a_{ij} > 0$ has $\beta(x_j) = u_j$, and each $x_j$ with $a_{ij} < 0$ has $\beta(x_j) = l_j$, since invariant 2 keeps values within bounds. Then for any assignment satisfying the bounds and the row,

$$
x_i = \sum_{a_{ij} > 0} a_{ij} x_j + \sum_{a_{ij} < 0} a_{ij} x_j \le \sum_{a_{ij} > 0} a_{ij} u_j + \sum_{a_{ij} < 0} a_{ij} l_j = \beta(x_i) < l_i.
$$

So the explanation set is inconsistent. The row is $x_i$ equal to the maximum value it could possibly attain. The upper-bound case is symmetric.

The same row provides a Farkas certificate. Farkas' lemma says that a system of linear inequalities is infeasible exactly when a non-negative combination of them yields $0 \le c$ for some $c < 0$. Here the multipliers are 1 for the bound on $x_i$ and $|a_{ij}|$ for the other bounds. So a simplex conflict can be checked by simple rational arithmetic, independently of the solver, and this is what proof-producing solvers do.

Proposition (minimality). The explanation set of a row conflict is minimal.

Proof. All bounds in the explanation refer to variables of one row, and all these coefficients are nonzero. Other rows only define further basic variables, and these have no bounds in the set, so they impose no constraint. Remove the bound on some nonbasic $x_k$ in the row. Assign every other nonbasic variable of the row the value of its retained bound. Now $x_k$ is free in the direction needed, so there is a value of $x_k$ for which the row gives $x_i = l_i$. Remove instead the bound on $x_i$. Then the nonbasic variables at their bounds, with $x_i$ computed from the row, satisfy the remaining set. $\square$

### Termination

Theorem. The procedure check terminates.

Proof. Bounds do not change during check. A nonbasic variable changes its value only by leaving the basis, when it moves to a bound, or by entering the basis. So each nonbasic value is either the value it had when check started or a bound. The assignment is determined by the basis and the nonbasic values, and hence there are finitely many states. If check does not terminate, a state repeats, and the sequence between the repetitions is a cycle.

Let $V$ be the set of variables that enter or leave the basis during the cycle, and let $x_t$ be the largest variable in $V$. In the cycle there is a moment $A$ when $x_t$ leaves the basis, and a later moment $B$, with no pivot of $x_t$ in between, when $x_t$ enters the basis. Assume that at $A$, $x_t$ is below its lower bound $l_t$. The other case is symmetric. By the rule for selecting the leaving variable, at $A$ all basic variables smaller than $x_t$ are within their bounds. Nonbasic variables are always within bounds, and so all variables in $V$ other than $x_t$ are within bounds at $A$.

After $A$, $x_t$ is nonbasic with the value $l_t$, and it keeps this value until $B$. At $B$ let $x_i$ be the leaving variable, so $i < t$. Consider the case in which $x_i$ is below $l_i$. Since $x_t$ is a candidate with the value $l_t$, its coefficient in the row $x_i = \sum_j a_{ij} x_j$ at $B$ is positive. Since $x_t$ is the smallest candidate, every smaller nonbasic variable in the row is blocked: if $a_{ij} > 0$ then $\beta_B(x_j) = u_j$, and if $a_{ij} < 0$ then $\beta_B(x_j) = l_j$.

The row holds for every assignment that satisfies the tableau, including both $\beta_A$ and $\beta_B$, so

$$
\beta_A(x_i) - \beta_B(x_i) = \sum_j a_{ij} (\beta_A(x_j) - \beta_B(x_j)).
$$

Terms for $x_j \notin V$ vanish, since such a nonbasic variable keeps its value throughout the cycle. Terms for $x_j \in V$ with $j < t$ are at most zero, because $\beta_A(x_j)$ is within bounds and $\beta_B(x_j)$ is at the blocking bound. The term for $x_t$ is $a_{it}(\beta_A(x_t) - l_t)$, which is negative. Hence $\beta_A(x_i) < \beta_B(x_i) < l_i$, so $x_i$ is below its bound at $A$. This contradicts the fact that, at $A$, all variables in $V$ smaller than $x_t$ are within bounds. The case in which $x_i$ is above its upper bound is symmetric. $\square$

This is why the pivot rule is not a matter of taste. Without Bland's rule, or some other device, simplex can cycle.

### Backtracking and theory propagation

Backtracking restores the old bounds from a stack, and it does not touch the tableau. The assignment left by the last successful check satisfies the old, weaker bounds, so it can continue to be used, and only that one assignment must be saved. This is much cheaper than designs in which atoms add rows.

Bound propagation gives cheap theory propagation. For the row $x_i = \sum_j a_{ij} x_j$, if every $x_j$ with $a_{ij} > 0$ has a finite upper bound and every $x_j$ with $a_{ij} < 0$ has a finite lower bound, then

$$
x_i \le \sum_{a_{ij} > 0} a_{ij} u_j + \sum_{a_{ij} < 0} a_{ij} l_j.
$$

Any unassigned atom $x_i \le c$ with $c$ at least this value is entailed, and its explanation is the set of bounds that were used. Similarly, the atom $x_i \ge c'$ with $c'$ strictly greater than this value is entailed false.

Bounds on one variable also entail each other: $x \le 3$ entails $x \le 5$ and $\neg (x \ge 4)$. Solvers record these relations in order to propagate them directly.

### Strict inequalities

An inequality $x < c$ is treated by a symbolic infinitesimal. Let $\mathbb{Q}_\delta$ be the set of pairs $(c, k)$ of rationals, written $c + k\delta$, with componentwise addition and scalar multiplication, and with the lexicographic order. The atoms become

$$
x < c \quad\text{becomes}\quad x \le c - \delta, \qquad\qquad x > c \quad\text{becomes}\quad x \ge c + \delta.
$$

The algorithm needs only addition, scalar multiplication and comparison, so nothing else has to change.

Lemma. A set of bounds and rows has a rational solution if and only if the $\delta$-version has a solution in $\mathbb{Q}_\delta$. Moreover, a concrete rational $\varepsilon > 0$ can be computed from a $\mathbb{Q}_\delta$ solution, such that substituting $\varepsilon$ for $\delta$ gives a rational solution.

Proof of the second part. The rows are linear and homogeneous, so substituting any $\varepsilon$ preserves them. Each bound has the form $(c, k) \le (d, h)$, which means $c < d$, or $c = d$ and $k \le h$. In the second case, $c + k\varepsilon \le d + h\varepsilon$ for all $\varepsilon > 0$. In the first case with $k \le h$, the inequality also holds for all $\varepsilon > 0$. In the first case with $k > h$, it holds when $\varepsilon \le (d - c)/(k - h)$. Take $\varepsilon$ to be the minimum of these finitely many positive values, or 1 if there are none. Strictness holds because the bound $x \le c - \delta$ with $x$ assigned $c' + k'\delta$ gives, after substitution, $c' + k'\varepsilon \le c - \varepsilon < c$. Similarly for lower bounds. The first part follows: if rows and bounds have a rational solution, then with a small enough infinitesimal coefficient it gives a $\mathbb{Q}_\delta$ solution, because each strict inequality has positive slack in the rationals. $\square$

### Integers: branch and bound

For LIA, first solve the rational relaxation. If it is infeasible, the integer problem is infeasible and the same explanation works. If the solution has integer values on all integer variables, we are done. Otherwise, let $x$ be an integer variable with a non-integer value $v$, and split:

$$
x \le \lfloor v \rfloor \quad \lor \quad x \ge \lceil v \rceil.
$$

In DPLL(T) this is a splitting-on-demand lemma with new atoms, and the SAT core performs the case split.

Branch and bound is sound, since the clause is valid in the integers. It may fail to terminate on unbounded problems. For example, consider

$$
1 \le 3x - 3y \le 2.
$$

The relaxation is satisfiable, while the integer problem is not, because $3x - 3y$ is a multiple of 3. Each branch can move the relaxation solution to larger values, with no end. For bounded problems, the search tree is finite. In theory, one can compute finite bounds from the constraints: if a system of linear constraints has an integer solution, it has one whose size is bounded by a polynomial in the size of the input (Papadimitriou's result), and this also gives membership in NP. These bounds are too large to help in practice, so solvers combine other techniques.

Normalization and tightening. An atom $\sum_j a_j x_j \le c$ with integer coefficients and integer variables is equivalent, with $g = \gcd(a_1, \dots, a_n)$, to $\sum_j (a_j / g) x_j \le \lfloor c / g \rfloor$. The example above becomes $1 \le x - y \le 0$ after tightening, because $\lceil 1/3 \rceil = 1$ and $\lfloor 2/3 \rfloor = 0$. This is an immediate conflict. This one rule resolves many cases. For an equation $\sum_j a_j x_j = c$, the GCD test reports infeasibility when $g$ does not divide $c$.

Cuts. A cutting plane is a linear constraint that every integer solution satisfies, but that the current relaxation solution violates. The following is the pure-integer Gomory cut for a tableau.

Theorem. Suppose the row of a basic integer variable can be written as

$$
x_i = \beta_i + \sum_{j} a_j s_j,
$$

where each $s_j$ is an integer-valued variable with $s_j \ge 0$, $\beta_i$ is not an integer, and all $s_j$ have value 0 in the current assignment. Let $f_0 = \beta_i - \lfloor \beta_i \rfloor$, and let $f_j$ be the fractional part of $-a_j$. Then every integer solution satisfies $\sum_j f_j s_j \ge f_0$.

Proof. Rewrite the row as $x_i + \sum_j (-a_j) s_j = \beta_i$, then split each number into integer and fractional parts:

$$
x_i + \sum_j \lfloor -a_j \rfloor s_j + \sum_j f_j s_j = \lfloor \beta_i \rfloor + f_0.
$$

Rearranging shows that $\sum_j f_j s_j - f_0$ is an integer. Since $f_j, s_j \ge 0$, this integer is at least $-f_0 > -1$, so it is at least 0. $\square$

In a tableau whose nonbasic variables are all at bounds, take $s_j = x_j - l_j$ for a variable at its lower bound, and $s_j = u_j - x_j$ for a variable at its upper bound, with the sign of $a_j$ adjusted. This requires integer bounds. All $s_j$ being 0 at the current point, the current point has left side 0, which is less than $f_0$, so the cut separates it. Gomory's general version allows real variables as well. Solvers apply cuts together with branching. Other techniques include the Omega test of Pugh, which eliminates variables for integers, and Hermite normal form cuts.

### Nonlinear arithmetic

Nonlinear real arithmetic is decidable, but the first practical complete method, Collins' cylindrical algebraic decomposition (CAD), is doubly exponential in the number of variables in the worst case. Nonlinear integer arithmetic is undecidable, so all solvers are incomplete on it. Three methods are important.

Incremental linearization. Treat each product $x \cdot y$ as a fresh variable $m_{xy}$ and solve the linear abstraction. If the model is consistent with the real product, finish. Otherwise add lemmas that exclude this model and are valid for multiplication. Typical lemmas are as follows.

- Sign lemmas: $x > 0 \land y > 0 \to m_{xy} > 0$, with the corresponding statements for other signs.
- Zero lemmas: $x = 0 \lor y = 0 \leftrightarrow m_{xy} = 0$.
- Monotonicity lemmas: $|x| \le |x'| \land |y| \le |y'| \to |m_{xy}| \le |m_{x'y'}|$.
- Tangent lemmas at a point $(a, b)$: $(x - a)(y - b) \ge 0$ when $x \ge a \land y \ge b$ or $x \le a \land y \le b$, which reads $m_{xy} \ge b x + a y - ab$ after expanding, with the opposite inequality when the two conditions have opposite direction.

This procedure is sound for unsat, and it finds models only when the linear model happens to match or can be repaired. It may run forever.

Model-constructing satisfiability. The NLSAT method of Jovanović and de Moura constructs a real model one variable at a time, alongside the Boolean assignment. Given values for $x_1, \dots, x_{k-1}$, each polynomial constraint involving $x_k$ becomes a univariate constraint, whose feasible set is a finite union of intervals with algebraic endpoints. If the intersection is non-empty, pick a value and continue. If it is empty, the method uses CAD-style projection locally, around the current assignment, to generate a clause that explains why this region of values of $x_1, \dots, x_{k-1}$ is impossible. This clause is then used as in conflict analysis. So the CAD machinery runs only on the parts of the space that the search reaches. Z3's documentation describes NLSat as the solver used for the QF_NRA fragment. cvc5's TACAS paper describes a new procedure for nonlinear arithmetic, based on cylindrical algebraic coverings.

Reduction and other methods. Bounded NIA problems can be reduced by bit-blasting to SAT, which is a practical way to find integer models. Algebraic methods such as Gröbner bases can refute systems of polynomial equations.

## Worked examples

### Worked example 1: simplex with a satisfiable result

Decide the conjunction

$$
x + y \le 4 \land 2x - y \ge 2 \land -x + 2y \ge 2
$$

over the reals. Let $s_1 = x + y$, $s_2 = 2x - y$ and $s_3 = -x + 2y$. The order is $x < y < s_1 < s_2 < s_3$. Bounds are asserted one at a time, each followed by a check.

```
Initial tableau                    basic: s1, s2, s3     nonbasic: x, y
  s1 = x + y
  s2 = 2x - y
  s3 = -x + 2y
  beta: x=0 y=0 s1=0 s2=0 s3=0
```

Assert $s_1 \le 4$. Since $\beta(s_1) = 0 \le 4$, the check succeeds without a pivot.

Assert $s_2 \ge 2$. Since $\beta(s_2) = 0 < 2$, the row $s_2 = 2x - y$ is examined. The candidates are $x$, because its coefficient is positive and it has no upper bound, and $y$, because its coefficient is negative and it has no lower bound. Bland's rule picks $x$. Here $\theta = (2 - 0)/2 = 1$.

```
After pivot s2 with x
  x  = 1/2 y + 1/2 s2
  s1 = 3/2 y + 1/2 s2
  s3 = 3/2 y - 1/2 s2
  beta: x=1 y=0 s1=1 s2=2 s3=-1
```

All bounds now hold, since $s_1 = 1 \le 4$ and $s_2 = 2 \ge 2$, so this check succeeds.

Assert $s_3 \ge 2$. Since $\beta(s_3) = -1 < 2$, the row $s_3 = \frac{3}{2} y - \frac{1}{2} s_2$ is examined. The variable $y$ is a candidate, since its coefficient is positive and it has no upper bound. The variable $s_2$ is not a candidate, since its coefficient is negative and it sits at its lower bound 2. So the pivot is $s_3$ with $y$, with $\theta = (2 - (-1))/(3/2) = 2$.

```
After pivot s3 with y
  x  = 2/3 s2 + 1/3 s3
  y  = 1/3 s2 + 2/3 s3
  s1 = s2 + s3
  beta: x=2 y=2 s1=4 s2=2 s3=2
```

All bounds hold, since $s_1 = 4 \le 4$. The result is sat with $x = 2, y = 2$. Check: $2 + 2 = 4 \le 4$, $4 - 2 = 2 \ge 2$, $-2 + 4 = 2 \ge 2$. Z3 also returns $x = 2, y = 2$.

### Worked example 2: simplex with a conflict and its certificate

Decide

$$
x \le 1 \land y \ge -5 \land x + y \ge 3 \land x - y \ge 1.
$$

Let $s_1 = x + y$ and $s_2 = x - y$, with the order $x < y < s_1 < s_2$. Assert the bounds in the order given. The bounds $x \le 1$ and $y \ge -5$ are satisfied by $x = y = 0$, so no pivot is needed.

Assert $s_1 \ge 3$. Now $\beta(s_1) = 0 < 3$. The candidates in $s_1 = x + y$ are $x$, which has value 0 below its upper bound 1, and $y$. Bland's rule picks $x$, with $\theta = 3$.

```
After pivot s1 with x
  x  = -y + s1
  s2 = -2y + s1
  beta: x=3 y=0 s1=3 s2=3
```

Now $x = 3 > 1$, and $x$ is the smallest violated variable. In the row $x = -y + s_1$, $x$ must decrease. The variable $y$ has a negative coefficient and no upper bound, so it is a candidate. The variable $s_1$ has a positive coefficient and it is at its lower bound 3, so it is not. Pivot $x$ with $y$, with target value 1, and $\theta = (1 - 3)/(-1) = 2$.

```
After pivot x with y
  y  = -x + s1
  s2 = 2x - s1
  beta: x=1 y=2 s1=3 s2=-1
```

All bounds hold, because $s_2$ has no bound yet, and $y = 2 \ge -5$, so this check succeeds.

Assert $s_2 \ge 1$. Now $\beta(s_2) = -1 < 1$. In the row $s_2 = 2x - s_1$, $x$ has a positive coefficient and it is at its upper bound 1, and $s_1$ has a negative coefficient and it is at its lower bound 3. There is no candidate. The result is a conflict.

The explanation is $\{s_2 \ge 1, x \le 1, s_1 \ge 3\}$, which in original terms is $\{x - y \ge 1, x \le 1, x + y \ge 3\}$. The bound $y \ge -5$ is correctly absent. The clause sent to the core negates these three literals.

The certificate uses multipliers from the row: 1 for $s_2 \ge 1$, 2 for $x \le 1$, and 1 for $s_1 \ge 3$. Writing all as lower bounds, the combination is

$$
(x - y) + (x + y) + 2(-x) \ge 1 + 3 + 2(-1),
$$

which simplifies to $0 \ge 2$, a contradiction. Z3 agrees that the system is unsat.

### Worked example 3: strict inequalities

Decide $x < 1 \land y < 1 \land x + y > 1$ and produce a rational model.

Let $s = x + y$, with the order $x < y < s$. The bounds are $x \le 1 - \delta$, $y \le 1 - \delta$ and $s \ge 1 + \delta$. The first two are satisfied by $0$. Assert the third. Then $\beta(s) = 0 < 1 + \delta$, and $x$ is the first candidate, with target value $1 + \delta$.

```
After pivot s with x
  x = -y + s
  beta: x = 1 + delta, y = 0, s = 1 + delta
```

Now $x = 1 + \delta > 1 - \delta$. In the row $x = -y + s$, the candidate is $y$, which has a negative coefficient and can still increase, because $\beta(y) = 0 < 1 - \delta$. The variable $s$ is at its lower bound, so it cannot decrease. Pivot $x$ with $y$, with target value $1 - \delta$.

```
After pivot x with y
  y = -x + s
  beta: x = 1 - delta, y = 2 delta, s = 1 + delta
```

All bounds hold: $2\delta \le 1 - \delta$ holds in the lexicographic order, since $0 < 1$. So the result is sat.

Compute $\varepsilon$. The only constraint with a limit is $y \le 1 - \delta$, which is the pair $(0, 2) \le (1, -1)$, giving $\varepsilon \le (1 - 0)/(2 - (-1)) = 1/3$. The bounds on $x$ and $s$ are met exactly, which gives no limit. With $\varepsilon = 1/3$, the model is $x = 2/3$, $y = 2/3$, and $s = 4/3$. Check: both are below 1, and their sum is above 1.

### Worked example 4: branch and bound and a cut

Let $x, y$ be integers. Decide

$$
4 \le 3x + 3y \le 5 \land 0 \le x \le 2 \land 0 \le y \le 2.
$$

Let $s = 3x + 3y$, with the order $x < y < s$. Each node runs simplex on the relaxation with all bounds, including the branch bounds. A node that has a fractional value branches on the smallest such variable, trying the lower branch first. Each explanation below can be checked by evaluating the row at the bounds.

```
node  added bounds             relaxation result               action
1     none                     x=4/3, y=0, s=4                 branch on x
2     x<=1                     x=1, y=1/3, s=4                 branch on y
3     x<=1, y<=0               conflict {x<=1, y<=0, s>=4}     close
4     x<=1, y>=1               x=1/3, y=1, s=4                 branch on x
5     x<=0, y>=1               x=0, y=4/3, s=4                 branch on y
6     x<=0, y<=1               conflict {s>=4, x<=0, y<=1}     close
7     x<=0, y>=2               conflict {s<=5, x>=0, y>=2}     close
8     x>=1, x<=1, y>=1         conflict {s<=5, x>=1, y>=1}     close
9     x>=2                     conflict {s<=5, x>=2, y>=0}     close
```

Here node 5 is the $x \le 0$ child of node 4, and node 8 is its $x \ge 1$ child. All nodes close, so the problem is unsat. Z3 confirms that it is unsat over the integers and sat over the reals, with $x = 4/3, y = 0$.

The example also shows how much stronger other reasoning is. By tightening, $3x + 3y \ge 4$ becomes $x + y \ge 2$, and $3x + 3y \le 5$ becomes $x + y \le 1$. These two contradict each other immediately.

A Gomory cut works as well. At node 1 the tableau row is $x = -y + \frac{1}{3} s$, with $\beta(x) = 4/3$, $y$ at its lower bound 0, and $s$ at its lower bound 4. Since $s$ is an integer in every integer solution, set $s_y = y$ and $s_s = s - 4$. The row is

$$
x = \frac{4}{3} - s_y + \frac{1}{3} s_s.
$$

Then $f_0 = 1/3$. The fractional part of $-(-1) = 1$ is 0, and the fractional part of $-1/3$ is $2/3$. The cut is $\frac{2}{3} s_s \ge \frac{1}{3}$, and so $s_s \ge \frac{1}{2}$, which by integrality means $s \ge 5$. This excludes the current point, which has $s = 4$, and no integer point is lost.

### Worked example 5: a nonlinear query by incremental linearization

Decide over the reals

$$
x \ge 2 \land y \ge 3 \land x \cdot y \le 5.
$$

Replace $x \cdot y$ by $m$. The abstraction $x \ge 2, y \ge 3, m \le 5$ is sat with $x = 2, y = 3, m = 0$, which Z3 reports. The real product is 6, so the model is spurious.

Take the tangent lemma at the point $(2, 3)$. Since $x \ge 2$ and $y \ge 3$, we have $(x - 2)(y - 3) \ge 0$, and therefore

$$
m \ge 3x + 2y - 6.
$$

Adding this lemma gives $m \ge 6 + 6 - 6 = 6$, which contradicts $m \le 5$. So the problem is unsat, and Z3 confirms this for both the linearized query and the original query.

## Common mistakes

- Assigning a new value to a nonbasic variable that violates its bounds. This breaks the invariant on which conflict explanations depend. Only basic variables may be out of bounds.
- Choosing a candidate by sign alone. A positive coefficient for a row below its bound is usable only if $x_j$ is strictly below its upper bound.
- Using the wrong bound in an explanation. For a row below its lower bound, a positive coefficient contributes the upper bound of $x_j$, and a negative coefficient contributes its lower bound. The upper-bound case swaps these.
- Treating $\delta$ as a small number chosen in advance. It is symbolic, and a concrete value is computed only at the end, from the final assignment.
- Concluding integer unsatisfiability from a failed branch alone. All branches must close.
- Trusting branch and bound to terminate on an unbounded problem. The example $1 \le 3x - 3y \le 2$ can diverge, so solvers need cuts or tightening.
- Applying the Gomory cut when a nonbasic variable is real or has a non-integer bound. The pure-integer proof needs all $s_j$ integer-valued, and the general case needs the mixed-integer form.
- Assuming that nonlinear models from a linear abstraction are real models. The abstract variable for a product has no connection to the product until lemmas add it.
- Writing a strict bound into the integer case with $\delta$. Over the integers, $x < c$ is simply $x \le c - 1$.

## Exercises

1. Put $2x - 3y \le 5 \land x + y > 1 \land x \ge 0$ into general form, with $\delta$ where needed.

<details><summary>Solution</summary>

Define $s_1 = 2x - 3y$ and $s_2 = x + y$. The bounds are $s_1 \le 5$, $s_2 \ge 1 + \delta$ and $x \ge 0$. The atom $x \ge 0$ needs no slack variable, and it is a direct bound on $x$. The initial basic variables are $s_1, s_2$.

</details>

2. Give the current simplex status of the row $x_1 = 2x_2 - x_3$ under $\beta(x_1) = 0$, $\beta(x_2) = 1$, $\beta(x_3) = 2$, and the bounds $x_1 \ge 3$, $x_2 \le 5$, $x_3 \ge 2$. Name the variable selected to enter the basis, with order $x_1 < x_2 < x_3$, and give the new values after the pivot.

<details><summary>Solution</summary>

$x_1$ is below its lower bound by 3. The candidates are $x_2$, with positive coefficient and $1 < 5$, and not $x_3$, since it has a negative coefficient and is at its lower bound. So $x_2$ enters. Then $\theta = (3 - 0)/2 = 3/2$, $\beta(x_2) = 5/2$, $\beta(x_1) = 3$, $\beta(x_3) = 2$. The new row is $x_2 = \frac{1}{2} x_1 + \frac{1}{2} x_3$. Check: $\frac{3}{2} + 1 = \frac{5}{2}$.

</details>

3. Trace simplex with the order $x < y < s_1 < s_2$ on $x \le 3$, $x + 2y \ge 6$, $x - y \ge 3$, in that order, and give the explanation and the Farkas certificate.

<details><summary>Solution</summary>

Let $s_1 = x + 2y$ and $s_2 = x - y$.

Asserting $x \le 3$ requires no change. Asserting $s_1 \ge 6$ selects $s_1$ with value 0, and $x$ is the first candidate, so pivot with target 6.

```
x  = -2y + s1
s2 = -3y + s1
beta: x=6 y=0 s1=6 s2=6
```

Now $x = 6 > 3$. In the row $x = -2y + s_1$, $y$ is a candidate, because it has a negative coefficient and no upper bound. Pivot with target 3, and $\theta = (3 - 6)/(-2) = 3/2$.

```
y  = -1/2 x + 1/2 s1
s2 = 3/2 x - 1/2 s1
beta: x=3 y=3/2 s1=6 s2=3/2
```

This check succeeds. Asserting $s_2 \ge 3$ gives $\beta(s_2) = 3/2 < 3$. In the row $s_2 = \frac{3}{2} x - \frac{1}{2} s_1$, $x$ is at its upper bound and $s_1$ is at its lower bound, so there is no candidate.

The explanation is $\{s_2 \ge 3, x \le 3, s_1 \ge 6\}$. With multipliers 1, $\frac{3}{2}$ and $\frac{1}{2}$,

$$
(x - y) + \frac{1}{2}(x + 2y) - \frac{3}{2} x \ge 3 + 3 - \frac{9}{2},
$$

and this reduces to $0 \ge \frac{3}{2}$, a contradiction.

</details>

4. Given $\beta(x) = \delta$, $\beta(y) = 2\delta$ and $s = y - x$, with the bounds $x \ge \delta$, $x \le 1 - \delta$, $y \le 1 - \delta$, $s \ge \delta$, compute a suitable $\varepsilon$ and give the model.

<details><summary>Solution</summary>

The pairs are as follows. For $x \ge \delta$, the pair $(0, 1) \le (0, 1)$ gives no limit. For $x \le 1 - \delta$, the pair $(0, 1) \le (1, -1)$ gives $\varepsilon \le 1/2$. For $y \le 1 - \delta$, the pair $(0, 2) \le (1, -1)$ gives $\varepsilon \le 1/3$. For $s \ge \delta$, $\beta(s) = \delta$ gives no limit. So take $\varepsilon = 1/3$. The model is $x = 1/3$, $y = 2/3$, with $s = 1/3$, and it satisfies $0 < x < 1$, $y < 1$, $y > x$.

</details>

5. A row is $s = 2x - y$, with $x \le 3$ and $y \ge 1$ currently asserted. Atoms $s \le 6$ and $s \ge 7$ occur in the formula and are unassigned. Derive the theory propagations and their reasons.

<details><summary>Solution</summary>

The row gives $s \le 2 \cdot 3 - 1 = 5$. Thus $s \le 6$ is entailed, with the reason clause $\neg (x \le 3) \lor \neg (y \ge 1) \lor s \le 6$. The atom $s \ge 7$ is entailed false, with the reason clause $\neg (x \le 3) \lor \neg (y \ge 1) \lor \neg (s \ge 7)$.

</details>

6. Show that branch and bound can diverge on $1 \le 3x - 3y \le 2$, and show how a single rule refutes the problem.

<details><summary>Solution</summary>

Let the relaxation produce $x = 1/3$, $y = 0$. Branching on $x$ gives the two branches $x \le 0$ and $x \ge 1$. In the branch $x \ge 1$, the relaxation can give $x = 1$, $y = 1/3$, since $3 - 1 = 2$. Now branch on $y$, with the branches $y \le 0$ and $y \ge 1$. In the branch $y \ge 1$, the relaxation gives $x = 4/3$, $y = 1$, and so on. Each new branch has a shifted solution of the same shape, with $3x - 3y \in [1, 2]$, so a solver that always follows such a branch does not terminate.

The tightening rule resolves it: the GCD of the coefficients is 3, so $3x - 3y \ge 1$ becomes $x - y \ge 1$, and $3x - 3y \le 2$ becomes $x - y \le 0$. These are immediately inconsistent.

</details>

7. Prove that LRA is convex: if a satisfiable conjunction $\Gamma$ of non-strict linear constraints entails $\bigvee_i e_i$, where each $e_i$ is an equality, then $\Gamma$ entails some $e_i$. Then show that LIA is not convex.

<details><summary>Solution</summary>

The solution set $P$ of $\Gamma$ is a non-empty convex set. Each $e_i$ defines a hyperplane $H_i$, and the entailment says $P \subseteq \bigcup_i H_i$. Suppose $P \not\subseteq H_i$ for each $i$. Let $p \in P$ lie outside as many hyperplanes as possible. If $p \in H_i$, pick $q \in P \setminus H_i$. The points $(1 - t)p + tq$ with $t \in (0, 1]$ lie in $P$ by convexity. For each $j$ with $p \notin H_j$, at most one value of $t$ gives a point on $H_j$. So for all but finitely many $t$, the point lies outside $H_i$ and outside all $H_j$ that exclude $p$. That point is outside more hyperplanes than $p$, a contradiction, unless $p$ lies outside all of them. Such a $p$ contradicts the entailment. So $P \subseteq H_i$ for some $i$, and thus $\Gamma \models e_i$.

For LIA, take $\Gamma = \{1 \le x, x \le 2\}$. Then $\Gamma \models x = 1 \lor x = 2$ over the integers, while it entails neither disjunct alone.

</details>

8. Prove the proposition on minimality for the case of a conflict with $\beta(x_i) > u_i$.

<details><summary>Solution</summary>

The explanation is $\{x_i \le u_i\} \cup \{x_j \ge l_j : a_{ij} > 0\} \cup \{x_j \le u_j : a_{ij} < 0\}$, with all $a_{ij}$ nonzero. Only these variables have bounds in the set, and other rows only define unbounded basic variables.

Remove $x_i \le u_i$. Set each $x_j$ at its bound, and let $x_i$ be given by the row. Then the set is satisfied.

Remove the bound of some $x_k$. Set each other $x_j$ at its retained bound, and pick $x_i = u_i$. The row then determines a value for $x_k$, since $a_{ik} \ne 0$, and $x_k$ has no remaining bound in the set. All remaining literals are satisfied.

So each proper subset is consistent. $\square$

</details>

9. Let integer variables $x, y$ have the row $x = \frac{5}{2} + \frac{1}{2} s_1 - \frac{3}{2} s_2$, where $s_1 = y - 1$ and $s_2 = 4 - y'$ are slacks at their bounds, for integer variables $y, y'$. Derive the Gomory cut, and write it in terms of $y$ and $y'$.

<details><summary>Solution</summary>

Here $\beta_i = 5/2$, so $f_0 = 1/2$. For $s_1$, the coefficient is $a_1 = 1/2$, and the fractional part of $-1/2$ is $1/2$. For $s_2$, the coefficient is $a_2 = -3/2$, and the fractional part of $3/2$ is $1/2$. The cut is

$$
\frac{1}{2} s_1 + \frac{1}{2} s_2 \ge \frac{1}{2},
$$

that is, $s_1 + s_2 \ge 1$. In terms of the variables, $y - 1 + 4 - y' \ge 1$, which is $y - y' \ge -2$. At the current point, $y = 1$ and $y' = 4$, giving $y - y' = -3$, so the cut excludes it.

</details>

10. Trace a local NLSAT-style explanation by hand for $x^2 + y^2 \le 1 \land x \ge 2$, in the variable order $x, y$. Give the value chosen for $x$, the empty feasible set, and a valid clause that explains it.

<details><summary>Solution</summary>

First, $x \ge 2$ gives the feasible set $[2, \infty)$ for $x$, so choose $x = 2$. Then the first constraint becomes $4 + y^2 \le 1$, which is $y^2 \le -3$, and this has an empty solution set.

The explanation must exclude more than the point $x = 2$. Projecting $x^2 + y^2 \le 1$ onto $x$ gives the interval $[-1, 1]$. The clause

$$
\neg (x^2 + y^2 \le 1) \lor x \le 1
$$

is valid, because $y^2 \ge 0$ means $x^2 \le 1$, and so $x \le 1$. Since $x^2 + y^2 \le 1$ is asserted, this clause propagates $x \le 1$, which contradicts $x \ge 2$. The formula is unsat, and this has been confirmed by Z3.

</details>

11. Design a theory solver interface for integer difference constraints that is simpler than simplex. Give the data structure, the conflict criterion, the explanation and the complexity of one assertion.

<details><summary>Solution</summary>

Represent the set of constraints $x - y \le c$ as a weighted directed graph, with an edge from $y$ to $x$ with weight $c$. The set is consistent if and only if the graph has no negative cycle. A potential function $\pi$ with $\pi(x) - \pi(y) \le c$ for every edge is exactly a model.

To assert a new edge, repair $\pi$ with a Dijkstra-style incremental relaxation over reduced costs $\pi(y) + c - \pi(x) \ge 0$, starting at the head of the new edge. This takes $O(m + n \log n)$ time per assertion. If the relaxation reaches the tail of the new edge with a strictly improved value, a negative cycle exists.

The conflict is the set of constraints on the cycle, found by following parent pointers. The sum of the cycle weights is negative, which is a certificate. Backtracking removes edges and keeps $\pi$ as it was at the last consistent state, because removing an edge preserves the validity of a potential.

Integers need no special treatment, since integer weights give an integer potential.

</details>

## Self-check

Before moving on, you should be able to do the following closed-book.

- Convert a conjunction of linear constraints with strict inequalities to general form.
- Trace check, pivot by pivot, with Bland's rule, on an unseen system, and maintain the full tableau and assignment.
- Extract the explanation and the Farkas certificate from a row conflict, and verify it by arithmetic.
- Prove that check terminates, and prove that the explanation is minimal.
- Compute $\varepsilon$ from a $\mathbb{Q}_\delta$ model.
- Run branch and bound by hand on a bounded integer problem, and apply tightening and a Gomory cut.
- Give an example in which branch and bound does not terminate.
- Explain incremental linearization and NLSAT, and state the decidability status of NRA and NIA.

## Materials

- Dutertre and de Moura, A Fast Linear-Arithmetic Solver for DPLL(T), CAV 2006. Read it for the general form, the check procedure, the treatment of explanations and backtracking, and the handling of strict bounds.
- Kroening and Strichman, Decision Procedures: An Algorithmic Point of View, 2nd edition. Read the chapter on linear arithmetic for general simplex, branch and bound, and Omega-style methods.
- Jovanović and de Moura, Solving Non-linear Arithmetic, IJCAR 2012. Read it for the model-constructing NLSAT procedure.
- Cimatti, Griggio, Irfan, Roveri and Sebastiani, Incremental Linearization for Satisfiability and Verification Modulo Nonlinear Arithmetic and Transcendental Functions, ACM Transactions on Computational Logic 2018. Read it for the lemma families used in incremental linearization.
- Collins, Quantifier Elimination for Real Closed Fields by Cylindrical Algebraic Decomposition, 1975. Read it for the origin of CAD.
- Schrijver, Theory of Linear and Integer Programming. Read it for Farkas' lemma and cutting planes.
