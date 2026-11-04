# Soundness and Completeness

Part 1, Chapter 1: Mathematical Logic.

## Objective

Prove the soundness and completeness of a propositional proof system from memory.

## Why this matters

Soundness and completeness are the two theorems that make a proof system usable: soundness says that a proof can be trusted, and completeness says that a proof always exists when the claim is true. This pair of questions recurs throughout the field. A SAT solver must never report a false unsatisfiability result and must always find a refutation for an unsatisfiable input, and an SMT theory solver and a program logic are judged in the same terms. The maximal consistent set construction you learn here is the propositional version of the Henkin proof in [First-Order Metatheory](../first-order-metatheory/), and the resolution completeness proof is the core of [Resolution and DPLL](../../../part-2-core-reasoning/04-sat/resolution-and-dpll/). This topic is also the proof of mastery for the chapter, so you should be able to write the main proof without notes.

## Prerequisites

- [Propositional Logic](../propositional-logic/)
- [Proof Systems](../proof-systems/)

## Lesson

### The two theorems

Let $\vdash$ be derivability in a proof system and $\models$ be semantic entailment.

- Soundness: if $\Gamma \vdash \varphi$, then $\Gamma \models \varphi$.
- Strong completeness: if $\Gamma \models \varphi$, then $\Gamma \vdash \varphi$, for every set $\Gamma$, finite or infinite.
- Weak completeness: if $\models \varphi$, then $\vdash \varphi$.

Soundness is proved by induction on derivations, and it is a routine check of each rule. Completeness is harder, since it asserts the existence of a proof. Post proved the completeness of the propositional system of Principia Mathematica in 1921. Kalmár gave a proof in 1935 that turns a truth table into a derivation. Henkin's 1949 method for first-order logic, adapted to the propositional case, is the proof given first below.

This topic proves completeness in four different ways, because each one teaches something different.

| Proof | System | Idea | What you get from it |
|---|---|---|---|
| Henkin | Natural deduction | Build a model from a maximal consistent set. | It proves strong completeness and generalizes to first-order logic. |
| Kalmár | Natural deduction | Derive each line of the truth table and combine the lines. | It gives an explicit method for producing a proof. |
| Search | Sequent calculus | Run proof search and read a countermodel from any failure. | It gives a decision procedure as well as completeness. |
| Restriction | Resolution | Split on a variable and lift the two refutations. | It gives the basis of DPLL and clause learning. |

### Natural deduction, recalled

We use the system of [Proof Systems](../proof-systems/) over $\bot, \neg, \land, \lor, \to$, with rules Ax, $\land$I, $\land$E, $\lor$I, $\lor$E, $\to$I, $\to$E, $\neg$I, $\neg$E, $\bot$E and RAA. The set $V$ of variables is countable. A set $\Gamma$ may be infinite. The judgment $\Gamma \vdash \varphi$ holds if and only if there is a finite derivation tree for it.

### Soundness of natural deduction

Theorem (soundness). If $\Gamma \vdash \varphi$, then $\Gamma \models \varphi$.

Proof. Use induction on the derivation of $\Gamma \vdash \varphi$. In each case, let $v$ be an assignment satisfying $\Gamma$, and show that $v(\varphi) = 1$. The induction hypothesis says that each premise of the rule is semantically correct.

- Ax: $\varphi \in \Gamma$, so $v(\varphi) = 1$.
- $\land$I: by the hypothesis, $v(\varphi) = 1$ and $v(\psi) = 1$, so $v(\varphi \land \psi) = 1$.
- $\land$E: by the hypothesis, $v(\varphi \land \psi) = 1$, so each conjunct has the value $1$.
- $\lor$I: by the hypothesis, one disjunct has the value $1$, so the disjunction does.
- $\lor$E: by the hypothesis, $v(\varphi \lor \psi) = 1$. If $v(\varphi) = 1$, then $v$ satisfies $\Gamma, \varphi$, so $v(\chi) = 1$ by the hypothesis for the second premise. If $v(\psi) = 1$, the third premise gives $v(\chi) = 1$ in the same way.
- $\to$I: if $v(\varphi) = 0$, then $v(\varphi \to \psi) = 1$. If $v(\varphi) = 1$, then $v$ satisfies $\Gamma, \varphi$, so $v(\psi) = 1$ by the hypothesis, and $v(\varphi \to \psi) = 1$.
- $\to$E: by the hypothesis, $v(\varphi \to \psi) = 1$ and $v(\varphi) = 1$, so $v(\psi) = 1$.
- $\neg$I: the hypothesis is $\Gamma, \varphi \models \bot$. If $v(\varphi) = 1$, then $v(\bot) = 1$, which is impossible. So $v(\varphi) = 0$ and $v(\neg \varphi) = 1$.
- $\neg$E: the hypothesis would give $v(\neg\varphi) = 1$ and $v(\varphi) = 1$, which is impossible. So no $v$ satisfies $\Gamma$, and the conclusion $\Gamma \models \bot$ holds vacuously.
- $\bot$E: the hypothesis is $\Gamma \models \bot$, so no $v$ satisfies $\Gamma$, and $\Gamma \models \varphi$ holds vacuously.
- RAA: the hypothesis is $\Gamma, \neg\varphi \models \bot$. If $v(\varphi) = 0$, then $v$ satisfies $\Gamma, \neg\varphi$, so $v(\bot) = 1$, which is impossible. So $v(\varphi) = 1$. $\square$

Soundness gives you the standard way to show that something is not derivable: find an assignment that satisfies $\Gamma$ and falsifies $\varphi$.

### Completeness of natural deduction, the Henkin proof

Theorem (strong completeness). If $\Gamma \models \varphi$, then $\Gamma \vdash \varphi$.

Here is the plan. We prove the contrapositive. Assuming $\Gamma \nvdash \varphi$, we must produce an assignment satisfying $\Gamma$ and falsifying $\varphi$. The only material available is syntax, so we build a set of formulas that decides every formula and read an assignment from it.

Definition. A set $\Gamma$ is consistent if $\Gamma \nvdash \bot$. A set $\Delta$ is maximal consistent if it is consistent and no proper superset of $\Delta$ is consistent.

The proof has the following parts: two structural lemmas, the reduction to consistency, Lindenbaum's lemma, the closure properties, the truth lemma, and the conclusion.

Lemma 1 (weakening). If $\Gamma \vdash \varphi$ and $\Gamma \subseteq \Gamma'$, then $\Gamma' \vdash \varphi$.

Proof. Use induction on the derivation, for all $\Gamma'$ at once. For Ax, $\varphi \in \Gamma \subseteq \Gamma'$. For a rule that discharges an assumption, such as $\to$I with premise $\Gamma, \alpha \vdash \beta$, we have $\Gamma \cup \{\alpha\} \subseteq \Gamma' \cup \{\alpha\}$, so the hypothesis gives $\Gamma', \alpha \vdash \beta$, and the same rule applies. The other rules are similar. $\square$

Lemma 2 (finiteness). If $\Gamma \vdash \varphi$, then $\Gamma_0 \vdash \varphi$ for some finite $\Gamma_0 \subseteq \Gamma$.

Proof. Use induction on the derivation. For Ax, take $\Gamma_0 = \{\varphi\}$. For a rule with several premises, take the union of the finite sets from each premise and use Lemma 1 to bring the premises to a common set. For a rule that discharges $\alpha$, the hypothesis gives a finite $\Gamma_1 \subseteq \Gamma \cup \{\alpha\}$ for that premise. Take $\Gamma_0 = \Gamma_1 \setminus \{\alpha\}$. By Lemma 1, the premise holds with $\Gamma_0 \cup \{\alpha\}$, and then the rule applies. $\square$

Lemma 3 (reduction). If $\Gamma \nvdash \varphi$, then $\Gamma \cup \{\neg \varphi\}$ is consistent.

Proof. If $\Gamma, \neg \varphi \vdash \bot$, then $\Gamma \vdash \varphi$ by RAA. $\square$

Lemma 4 (Lindenbaum). Every consistent set is contained in a maximal consistent set.

Proof. Let $\Gamma$ be consistent. The set of formulas is countable, since $V$ is countable and each formula is a finite string. Let $\varphi_0, \varphi_1, \varphi_2, \dots$ enumerate all formulas. Define

$$
\Gamma_0 = \Gamma, \qquad
\Gamma_{n+1} =
\begin{cases}
\Gamma_n \cup \{\varphi_n\} & \text{if this set is consistent,}\\
\Gamma_n & \text{otherwise,}
\end{cases}
\qquad
\Delta = \bigcup_{n} \Gamma_n.
$$

Each $\Gamma_n$ is consistent, by induction on $n$.

$\Delta$ is consistent. Suppose $\Delta \vdash \bot$. By Lemma 2, a finite subset of $\Delta$ derives $\bot$. Each member of this subset lies in some $\Gamma_n$, and the $\Gamma_n$ form an increasing chain, so the whole subset lies in one $\Gamma_n$. By Lemma 1, $\Gamma_n \vdash \bot$, which is a contradiction.

$\Delta$ is maximal. Let $\varphi_n \notin \Delta$. Then $\varphi_n$ was not added at stage $n$, so $\Gamma_n \cup \{\varphi_n\}$ is inconsistent. Since $\Gamma_n \subseteq \Delta$, Lemma 1 gives that $\Delta \cup \{\varphi_n\}$ is inconsistent. So every proper superset of $\Delta$ is inconsistent, again by Lemma 1. $\square$

Lemma 5 (closure properties). Let $\Delta$ be maximal consistent. Then:

1. If $\Delta \vdash \varphi$, then $\varphi \in \Delta$.
2. $\bot \notin \Delta$.
3. $\neg \varphi \in \Delta$ if and only if $\varphi \notin \Delta$.
4. $\varphi \land \psi \in \Delta$ if and only if $\varphi \in \Delta$ and $\psi \in \Delta$.
5. $\varphi \lor \psi \in \Delta$ if and only if $\varphi \in \Delta$ or $\psi \in \Delta$.
6. $\varphi \to \psi \in \Delta$ if and only if $\varphi \notin \Delta$ or $\psi \in \Delta$.

Proof.

Part 1. Assume $\Delta \vdash \varphi$. If $\Delta \cup \{\varphi\}$ were inconsistent, then $\Delta, \varphi \vdash \bot$, so $\Delta \vdash \neg\varphi$ by $\neg$I, and $\Delta \vdash \bot$ by $\neg$E, which is a contradiction. So $\Delta \cup \{\varphi\}$ is consistent, and maximality gives $\varphi \in \Delta$.

Part 2. If $\bot \in \Delta$, then $\Delta \vdash \bot$ by Ax.

Part 3. If both $\varphi$ and $\neg \varphi$ are in $\Delta$, then $\Delta \vdash \bot$ by $\neg$E, so at most one is in $\Delta$. If $\varphi \notin \Delta$, then $\Delta \cup \{\varphi\}$ is inconsistent by maximality, so $\Delta \vdash \neg\varphi$ by $\neg$I, and $\neg\varphi \in \Delta$ by part 1.

Part 4. If $\varphi \land \psi \in \Delta$, then $\land$E and part 1 give both conjuncts. If both conjuncts are in $\Delta$, then $\land$I and part 1 give the conjunction.

Part 5. If $\varphi \in \Delta$ or $\psi \in \Delta$, then $\lor$I and part 1 give $\varphi \lor \psi \in \Delta$. Conversely, let $\varphi \lor \psi \in \Delta$ and suppose $\varphi \notin \Delta$ and $\psi \notin \Delta$. By part 3, $\neg\varphi, \neg\psi \in \Delta$. Then $\Delta, \varphi \vdash \bot$ and $\Delta, \psi \vdash \bot$ by Lemma 1 and $\neg$E, so $\Delta \vdash \bot$ by $\lor$E, which is a contradiction.

Part 6. Let $\varphi \to \psi \in \Delta$. If $\varphi \in \Delta$, then $\to$E and part 1 give $\psi \in \Delta$. For the converse, there are two cases. If $\psi \in \Delta$, then $\Delta, \varphi \vdash \psi$ by Ax, so $\Delta \vdash \varphi \to \psi$ by $\to$I. If $\varphi \notin \Delta$, then $\neg\varphi \in \Delta$ by part 3, so $\Delta, \varphi \vdash \bot$ by $\neg$E, then $\Delta, \varphi \vdash \psi$ by $\bot$E, and $\Delta \vdash \varphi \to \psi$ by $\to$I. In both cases, part 1 gives $\varphi \to \psi \in \Delta$. $\square$

Lemma 6 (truth lemma). Let $\Delta$ be maximal consistent, and define the assignment $v_\Delta$ by $v_\Delta(x) = 1$ if and only if $x \in \Delta$. Then for every formula $\varphi$, $v_\Delta(\varphi) = 1$ if and only if $\varphi \in \Delta$.

Proof. Use structural induction on $\varphi$. Write $v$ for $v_\Delta$.

- $\varphi = x$: this is the definition of $v$.
- $\varphi = \bot$: $v(\bot) = 0$, and $\bot \notin \Delta$ by part 2.
- $\varphi = \neg\alpha$: $v(\neg\alpha) = 1$ iff $v(\alpha) = 0$ iff $\alpha \notin \Delta$ (by the hypothesis) iff $\neg\alpha \in \Delta$ (by part 3).
- $\varphi = \alpha \land \beta$: $v(\alpha \land \beta) = 1$ iff $v(\alpha) = 1$ and $v(\beta) = 1$ iff $\alpha \in \Delta$ and $\beta \in \Delta$ (by the hypothesis) iff $\alpha \land \beta \in \Delta$ (by part 4).
- $\varphi = \alpha \lor \beta$: the same argument with part 5.
- $\varphi = \alpha \to \beta$: $v(\alpha \to \beta) = 1$ iff $v(\alpha) = 0$ or $v(\beta) = 1$ iff $\alpha \notin \Delta$ or $\beta \in \Delta$ (by the hypothesis) iff $\alpha \to \beta \in \Delta$ (by part 6). $\square$

Proof of the theorem. Suppose $\Gamma \nvdash \varphi$. By Lemma 3, $\Gamma \cup \{\neg\varphi\}$ is consistent. By Lemma 4, it is contained in a maximal consistent set $\Delta$. By Lemma 6, $v_\Delta$ satisfies every member of $\Delta$. So $v_\Delta$ satisfies $\Gamma$ and $\neg\varphi$, which gives $v_\Delta(\varphi) = 0$. Hence $\Gamma \not\models \varphi$. $\square$

Where classical logic enters. RAA is used only in Lemma 3. All of Lemmas 1, 2, 4, 5 and 6 go through with the intuitionistic rules alone. So the proof shows more: a set that is intuitionistically consistent is classically satisfiable, and a set is classically refutable if and only if it is intuitionistically refutable. Without RAA, the reduction from non-derivability to consistency fails, because $\nvdash x_1 \lor \neg x_1$ holds in intuitionistic logic while $\neg(x_1 \lor \neg x_1)$ is inconsistent. Exercise 6 proves this non-derivability.

To remember the proof, keep this outline: not derivable gives consistent with the negation (RAA), consistent extends to maximal consistent (enumeration and finiteness), maximal consistent sets behave like truth (one clause for each connective), and truth in $\Delta$ defines the model.

### Completeness of natural deduction, the Kalmár proof

Kalmár's proof is constructive and gives only weak completeness (and hence completeness for finite $\Gamma$).

Fix an assignment $v$ and a formula $\varphi$ with variables among $x_1, \dots, x_n$. Define $x_i^v = x_i$ if $v(x_i) = 1$ and $x_i^v = \neg x_i$ otherwise. Define $\varphi^v = \varphi$ if $v(\varphi) = 1$ and $\varphi^v = \neg \varphi$ otherwise. Let $\Gamma_v = \{x_1^v, \dots, x_n^v\}$.

Lemma (a line of the truth table). $\Gamma_v \vdash \varphi^v$.

Proof. Use structural induction on $\varphi$.

- $\varphi = x_i$: this is Ax.
- $\varphi = \bot$: the goal is $\neg\bot$, which follows from $\bot \vdash \bot$ by $\neg$I.
- $\varphi = \neg\alpha$: if $v(\alpha) = 0$, the goal $\neg\alpha$ is $\alpha^v$. If $v(\alpha) = 1$, the goal is $\neg\neg\alpha$. By the hypothesis $\Gamma_v \vdash \alpha$, so $\Gamma_v, \neg\alpha \vdash \bot$ by $\neg$E, and $\neg$I gives the goal.
- $\varphi = \alpha \land \beta$: if both are true, use $\land$I. If one conjunct is false, say $\alpha$, then $\Gamma_v \vdash \neg\alpha$. Assume $\alpha \land \beta$, derive $\alpha$ and hence $\bot$, and conclude $\neg(\alpha \land \beta)$ by $\neg$I.
- $\varphi = \alpha \lor \beta$: if one disjunct is true, use $\lor$I. If both are false, then $\Gamma_v \vdash \neg\alpha$ and $\Gamma_v \vdash \neg\beta$. Assume $\alpha \lor \beta$, derive $\bot$ in each case by $\lor$E, and conclude by $\neg$I.
- $\varphi = \alpha \to \beta$: if $v(\beta) = 1$, then $\Gamma_v \vdash \beta$, so $\to$I gives the goal. If $v(\alpha) = 0$, then $\Gamma_v \vdash \neg\alpha$, so $\Gamma_v, \alpha \vdash \bot$, $\bot$E gives $\beta$, and $\to$I gives the goal. If $v(\alpha) = 1$ and $v(\beta) = 0$, then $\Gamma_v \vdash \alpha$ and $\Gamma_v \vdash \neg\beta$. Assume $\alpha \to \beta$, derive $\beta$ and hence $\bot$, and conclude by $\neg$I. $\square$

Theorem (weak completeness). If $\models \varphi$, then $\vdash \varphi$.

Proof. Since $\varphi$ is valid, $\varphi^v = \varphi$ for every $v$, so $\Gamma_v \vdash \varphi$ for every $v$. Now remove the variables one at a time. For each choice of literals $\Lambda$ over $x_1, \dots, x_{n-1}$, we have $\Lambda, x_n \vdash \varphi$ and $\Lambda, \neg x_n \vdash \varphi$. Since $\vdash x_n \lor \neg x_n$, $\lor$E gives $\Lambda \vdash \varphi$. After $n$ rounds, $\vdash \varphi$. $\square$

For finite $\Gamma = \{\gamma_1, \dots, \gamma_k\}$ with $\Gamma \models \psi$, the formula $\gamma_1 \to (\gamma_2 \to \dots \to (\gamma_k \to \psi))$ is valid, so it is derivable. Then $\to$E and Lemma 1 give $\Gamma \vdash \psi$.

The proof is an algorithm that produces a derivation of size roughly $2^n$ times the size of $\varphi$. This is the sense in which a truth table is already a proof. The only classical step is the use of excluded middle.

### Completeness of sequent calculus, by proof search

Use G3 from [Proof Systems](../proof-systems/). Say that an assignment $v$ falsifies a sequent $\Gamma \Rightarrow \Delta$ if $v$ satisfies every formula of $\Gamma$ and falsifies every formula of $\Delta$. So a sequent is valid if and only if no assignment falsifies it.

Lemma (exact preservation). For each rule of G3 and each assignment $v$, $v$ falsifies the conclusion if and only if $v$ falsifies at least one premise.

Proof. Go through the rules. For $\land$R: $v$ falsifies $\Gamma \Rightarrow \varphi \land \psi, \Delta$ iff $v$ satisfies $\Gamma$, falsifies $\Delta$, and falsifies $\varphi$ or $\psi$, which is exactly the condition that $v$ falsifies one of the two premises. For $\to$L: $v$ falsifies $\Gamma, \varphi \to \psi \Rightarrow \Delta$ iff $v$ satisfies $\Gamma$, falsifies $\Delta$, and either falsifies $\varphi$ or satisfies $\psi$, which again is one of the two premises. For $\neg$L: $v$ satisfies $\neg\varphi$ iff $v$ falsifies $\varphi$, which moves $\varphi$ to the right. The rules $\neg$R, $\land$L, $\lor$L, $\lor$R and $\to$R are checked in the same way. $\square$

Theorem. A sequent is derivable in G3 if and only if it is valid.

Proof. Soundness. Axioms are valid: $\Gamma, x \Rightarrow x, \Delta$ cannot be falsified because $x$ would have to be both true and false, and $\Gamma, \bot \Rightarrow \Delta$ cannot be falsified because $\bot$ cannot be true. If all premises of a rule are valid, the lemma shows that the conclusion is valid. Induction on the derivation finishes the argument.

Completeness. Use induction on the number $c$ of occurrences of the connectives $\neg, \land, \lor, \to$ in the sequent. Let $\Gamma \Rightarrow \Delta$ be valid.

If $c = 0$, all formulas are variables or $\bot$. If $\bot$ is on the left or a variable is on both sides, the sequent is an axiom. Otherwise, define $v(x) = 1$ for the variables on the left and $v(x) = 0$ for all others. This $v$ satisfies every formula on the left. It falsifies every formula on the right, since each is $\bot$ or a variable not on the left. So $v$ falsifies the sequent, which contradicts validity.

If $c > 0$, choose any compound formula and apply its rule from the bottom up. By the lemma, all premises are valid, and each has fewer connectives. By the induction hypothesis, each premise is derivable, and the rule gives the sequent. $\square$

The proof contains more than completeness. It gives an algorithm that decides validity, its choice of formula does not matter (all rules are invertible), and every open leaf is a countermodel. It also never uses Cut, so it shows that cut is unnecessary for completeness, as Exercise 8 makes precise.

### Completeness of resolution

Let $S$ be a finite set of clauses. For a variable $x$, define the restrictions:

- $S|_{x=1}$: delete each clause containing the literal $x$, and delete $\neg x$ from the remaining clauses.
- $S|_{x=0}$: delete each clause containing the literal $\neg x$, and delete $x$ from the remaining clauses.

Neither restriction contains the variable $x$.

Lemma (restriction). If $S$ is unsatisfiable, then $S|_{x=1}$ and $S|_{x=0}$ are unsatisfiable.

Proof. Suppose $v$ satisfies $S|_{x=1}$. Consider $v' = v[x \mapsto 1]$. A clause of $S$ containing $x$ is satisfied by $v'$. Any other clause $C$ of $S$ has $C \setminus \{\neg x\} \in S|_{x=1}$, and $v'$ satisfies that clause, since it does not mention $x$ and $v$ satisfies it. So $v'$ satisfies $S$, which is a contradiction. The case $x = 0$ is symmetric. $\square$

Lemma (lifting). If $S|_{x=1}$ has a resolution derivation of a clause $C$, then $S$ has a resolution derivation of $C$ or of $C \cup \{\neg x\}$. Symmetrically, a derivation of $C$ from $S|_{x=0}$ gives a derivation of $C$ or of $C \cup \{x\}$ from $S$.

Proof. Go through the derivation from $S|_{x=1}$ and transform each clause. An input clause $C$ of $S|_{x=1}$ is the result of restricting $C$ or $C \cup \{\neg x\}$ in $S$, so use that clause of $S$. For a step that resolves two clauses on a variable $y$, we have $y \neq x$, since $x$ does not occur in $S|_{x=1}$. Resolve their transformed versions on $y$. The resolvent is the original resolvent, possibly with $\neg x$ added. $\square$

Theorem. A finite clause set $S$ is unsatisfiable if and only if $S$ has a resolution refutation.

Proof. If $S$ has a refutation, then $S$ is unsatisfiable, since resolution is sound (Exercise 8 of [Proof Systems](../proof-systems/)).

For the converse, use induction on the number of variables in $S$. If there are none, the only possible clause is $\square$, and an unsatisfiable $S$ must contain it, so $S$ has the one-line refutation $\square$.

Otherwise, pick a variable $x$ in $S$. By the restriction lemma and the induction hypothesis, $S|_{x=1}$ and $S|_{x=0}$ each have refutations. By the lifting lemma with $C = \square$, $S$ derives $\square$ or $\{\neg x\}$, and $S$ derives $\square$ or $\{x\}$. If $\square$ is derived in either case, we are done. Otherwise, resolving $\{x\}$ and $\{\neg x\}$ gives $\square$. $\square$

Remark. If $S$ has no tautological clause, neither do its restrictions, and the transformed clauses in the lifting lemma add at most one literal on a variable absent from the original clause. So the refutation produced contains no tautological clause. This justifies dropping tautological resolvents in the saturation procedure.

The recursion in this proof has the shape of the DPLL search, and the lifted clauses are resolution consequences of the kind that clause learning records. See [Resolution and DPLL](../../../part-2-core-reasoning/04-sat/resolution-and-dpll/) and [CDCL](../../../part-2-core-reasoning/04-sat/cdcl/).

### Compactness

Theorem (compactness). A set $\Gamma$ of formulas is satisfiable if and only if every finite subset of $\Gamma$ is satisfiable. Equivalently, $\Gamma \models \varphi$ if and only if $\Gamma_0 \models \varphi$ for some finite $\Gamma_0 \subseteq \Gamma$.

Proof. One direction is immediate. For the other, suppose $\Gamma$ is unsatisfiable. Then $\Gamma \models \bot$, so $\Gamma \vdash \bot$ by completeness. By Lemma 2, $\Gamma_0 \vdash \bot$ for a finite $\Gamma_0 \subseteq \Gamma$, and by soundness, $\Gamma_0$ is unsatisfiable.

For the second form, $\Gamma \models \varphi$ iff $\Gamma \cup \{\neg\varphi\}$ is unsatisfiable, and then a finite subset of it is unsatisfiable, which gives the finite $\Gamma_0$. $\square$

The theorem is purely semantic, while this proof goes through derivations, using the fact that proofs are finite. Direct proofs exist as well, through König's lemma (Exercise 11) or through the compactness of the product space $\{0,1\}^V$. If $V$ is uncountable, the Henkin proof needs Zorn's lemma in place of the enumeration, and the result still holds.

## Worked examples

### Example 1: the Lindenbaum construction on a concrete set

Let $\Gamma = \{x_1 \lor x_2,\; \neg x_1\}$ and $\varphi = x_2 \land x_3$. We know $\Gamma \nvdash \varphi$, since the assignment below falsifies the entailment. Follow the completeness proof. Start with $\Gamma_0 = \Gamma \cup \{\neg(x_2 \land x_3)\}$, and suppose the enumeration begins with $x_1, x_2, x_3$.

```text
stage 0, candidate x1:
    Γ0 ∪ {x1} contains x1 and ¬x1, so it derives ⊥ by ¬E
    inconsistent, so x1 is not added
stage 1, candidate x2:
    Γ0 ∪ {x2} is satisfied by x1 = 0, x2 = 1, x3 = 0
    consistent by soundness, so x2 is added
stage 2, candidate x3:
    Γ0 ∪ {x2, x3} derives x2 ∧ x3 by ∧I
    with ¬(x2 ∧ x3) this derives ⊥ by ¬E
    inconsistent, so x3 is not added
all later stages:
    a candidate over x1, x2, x3 is added exactly when it is true under these values
    each later variable is decided by the stage at which it first becomes a candidate
```

The assignment read from $\Delta$ has $v(x_1) = 0$, $v(x_2) = 1$, $v(x_3) = 0$. Check the truth lemma on the input: $x_1 \lor x_2$ evaluates to $1$, $\neg x_1$ evaluates to $1$, and $x_2 \land x_3$ evaluates to $0$. So this $v$ is the countermodel promised by the theorem.

### Example 2: Kalmár's proof on a small formula

Take $\varphi = x_1 \to (x_2 \to x_1)$, which is valid. The method derives $\varphi$ under each of the four sets of literals and then eliminates the variables.

Case $v(x_1) = 1$, for either value of $x_2$. Here $\Gamma_v$ contains $x_1$. The subformula $x_2 \to x_1$ has a true consequent, so $\Gamma_v, x_2 \vdash x_1$ by Ax, and $\Gamma_v \vdash x_2 \to x_1$ by $\to$I. The formula $\varphi$ has a true consequent, so $\Gamma_v \vdash \varphi$ by Lemma 1 and $\to$I.

Case $v(x_1) = 0$, for either value of $x_2$. Here $\Gamma_v$ contains $\neg x_1$, and the antecedent of $\varphi$ is false. So $\Gamma_v, x_1 \vdash \bot$ by $\neg$E, $\Gamma_v, x_1 \vdash x_2 \to x_1$ by $\bot$E, and $\Gamma_v \vdash \varphi$ by $\to$I.

Eliminate $x_2$. For each value of $x_1$, we have the two derivations with $x_2$ and $\neg x_2$ in the assumptions. Applying $\lor$E to $x_2 \lor \neg x_2$ gives $x_1 \vdash \varphi$ and $\neg x_1 \vdash \varphi$.

Eliminate $x_1$. Applying $\lor$E to $x_1 \lor \neg x_1$ gives $\vdash \varphi$.

The resulting proof is correct but longer than necessary, since $\varphi$ also has a short direct proof that does not use excluded middle. The method guarantees existence, and it does not aim at short proofs.

### Example 3: extracting a refutation from the resolution proof

Let $S = \{\{x_1, x_2\},\; \{\neg x_1, x_3\},\; \{\neg x_2, x_3\},\; \{\neg x_3\}\}$. Follow the proof, branching on $x_1$.

$S|_{x_1=1}$ deletes $\{x_1, x_2\}$ and shortens $\{\neg x_1, x_3\}$ to $\{x_3\}$. This gives $\{\{x_3\}, \{\neg x_2, x_3\}, \{\neg x_3\}\}$. A refutation resolves $\{x_3\}$ with $\{\neg x_3\}$. To lift it, use the original clause $\{\neg x_1, x_3\}$ in place of $\{x_3\}$, so the result is $\{\neg x_1\}$.

$S|_{x_1=0}$ deletes $\{\neg x_1, x_3\}$ and shortens $\{x_1, x_2\}$ to $\{x_2\}$. This gives $\{\{x_2\}, \{\neg x_2, x_3\}, \{\neg x_3\}\}$. A refutation resolves $\{x_2\}$ with $\{\neg x_2, x_3\}$ to get $\{x_3\}$, and then with $\{\neg x_3\}$ to get the empty clause. To lift it, use $\{x_1, x_2\}$ in place of $\{x_2\}$, so the results are $\{x_1, x_3\}$ and then $\{x_1\}$.

Resolving the two lifted results gives the empty clause. The whole refutation is:

```text
1. {x1, x2}     given
2. {¬x1, x3}    given
3. {¬x2, x3}    given
4. {¬x3}        given
5. {¬x1}        resolve 2, 4 on x3
6. {x1, x3}     resolve 1, 3 on x2
7. {x1}         resolve 6, 4 on x3
8. {}           resolve 5, 7 on x1
```

### Example 4: compactness applied to graph coloring

Claim (a case of the de Bruijn-Erdős theorem). A countable graph $G = (W, E)$ is 3-colorable if and only if every finite subgraph of $G$ is 3-colorable.

One direction holds because a coloring of $G$ restricts to any subgraph. For the other, introduce variables $x_{w,c}$ for each $w \in W$ and $c \in \{1,2,3\}$, meaning that vertex $w$ gets color $c$. There are countably many such variables. Let $\Gamma$ contain:

- $x_{w,1} \lor x_{w,2} \lor x_{w,3}$ for each $w \in W$, and
- $\neg x_{u,c} \lor \neg x_{w,c}$ for each edge $\{u, w\} \in E$ and each color $c$.

Let $\Gamma_0 \subseteq \Gamma$ be finite. It mentions finitely many vertices, so they induce a finite subgraph, which has a 3-coloring by assumption. Assign $x_{w,c} = 1$ exactly when $w$ is in this subgraph and has color $c$. Each formula of $\Gamma_0$ is satisfied, so $\Gamma_0$ is satisfiable.

By compactness, $\Gamma$ has a model $v$. Color each vertex $w$ with the least $c$ such that $v(x_{w,c}) = 1$, which exists by the first kind of formula. The second kind ensures that adjacent vertices never share a color. So $G$ is 3-colorable.

## Common mistakes

- Stating completeness as the converse of the wrong thing. Soundness is the implication from $\vdash$ to $\models$, and completeness is the implication from $\models$ to $\vdash$. A quick check is that soundness has an easy proof by induction on derivations, and that is the direction whose hypothesis gives you a derivation to induct on.
- Defining the Lindenbaum sequence as adding $\varphi_n$ or $\neg\varphi_n$ without showing that one of them is consistent. The version above avoids this, since it adds $\varphi_n$ only if that keeps the set consistent, and it derives the negation property afterward. If you use the other version, you must prove that $\Gamma_n \cup \{\varphi_n\}$ and $\Gamma_n \cup \{\neg \varphi_n\}$ are not both inconsistent, which itself uses RAA.
- Omitting the finiteness argument when proving that $\Delta$ is consistent. The union of consistent sets is consistent only because each derivation uses finitely many assumptions and the sets form a chain. This step is easy to omit, and the proof is incomplete without it.
- Trying to prove the truth lemma in one direction only. The induction needs both directions, because the case for $\neg$ and the antecedent of $\to$ flip them.
- Forgetting $\bot$ in the truth lemma or the base case. If your language has $\bot$, you must show that $\bot \notin \Delta$.
- Using completeness inside its own proof. For example, Lemma 5 must use derivations only. You may not justify a step by saying that a formula is a semantic consequence.
- Believing that weak completeness implies strong completeness on its own. The step requires compactness, as shown in Exercise 5.
- Thinking that completeness makes proof search easy. It says only that a proof exists. The smallest proof may have exponential size.
- Applying the closure properties to a set that is consistent and not maximal. The set $\{x_1 \lor x_2\}$ is consistent and contains neither $x_1$ nor $x_2$, so part 5 of Lemma 5 fails for it. Maximality is what makes membership behave like truth.

## Exercises

### Exercise 1

State soundness and strong completeness for a proof system. For each direction, name the proof technique, and state what the theorem lets you conclude from a countermodel and from a derivation.

<details><summary>Solution</summary>

Soundness says that $\Gamma \vdash \varphi$ implies $\Gamma \models \varphi$. It is proved by induction on derivations. It lets you conclude from a derivation that an entailment holds, and from a countermodel that no derivation exists.

Strong completeness says that $\Gamma \models \varphi$ implies $\Gamma \vdash \varphi$. It is proved by contraposition, building a model from a maximal consistent set, or by the other methods in the lesson. It lets you conclude from the absence of a countermodel that a derivation exists.

</details>

### Exercise 2

(a) Write the cases of the soundness proof for $\lor$E and RAA without looking at the lesson. (b) A student proposes the rule "from $\Gamma, \varphi \vdash \psi$ infer $\Gamma \vdash \psi$." Show that the rule is unsound.

<details><summary>Solution</summary>

(a) Let $v$ satisfy $\Gamma$. For $\lor$E, the first premise gives $v(\varphi \lor \psi) = 1$. If $v(\varphi) = 1$, then $v$ satisfies $\Gamma, \varphi$, and the second premise gives $v(\chi) = 1$. If $v(\psi) = 1$, the third premise gives $v(\chi) = 1$ in the same way.

For RAA, suppose $v(\varphi) = 0$. Then $v$ satisfies $\Gamma, \neg\varphi$, so the premise gives $v(\bot) = 1$, which is impossible. Hence $v(\varphi) = 1$.

(b) Take $\Gamma = \emptyset$ and $\varphi = \psi = x_1$. Then $x_1 \vdash x_1$ by Ax, so the rule gives $\vdash x_1$. The formula $x_1$ is not valid, so the rule is unsound. A rule may discharge an assumption only if it records the assumption in the conclusion, as $\to$I does.

</details>

### Exercise 3

Prove that a set $\Delta$ is maximal consistent if and only if $\Delta = \{\varphi : v(\varphi) = 1\}$ for some assignment $v$, and that $v$ is then unique.

<details><summary>Solution</summary>

Suppose $\Delta$ is maximal consistent. By the truth lemma, $\Delta = \{\varphi : v_\Delta(\varphi) = 1\}$.

Conversely, let $\Delta_v = \{\varphi : v(\varphi) = 1\}$. It is consistent: if $\Delta_v \vdash \bot$, soundness gives $\Delta_v \models \bot$, but $v$ satisfies $\Delta_v$ and falsifies $\bot$. It is maximal: if $\varphi \notin \Delta_v$, then $v(\varphi) = 0$, so $\neg\varphi \in \Delta_v$. Then $\Delta_v \cup \{\varphi\}$ derives $\bot$ by $\neg$E, so it is inconsistent.

For uniqueness, if $\Delta_v = \Delta_w$, then $v(x) = 1$ iff $x \in \Delta_v$ iff $x \in \Delta_w$ iff $w(x) = 1$, for every variable $x$. So $v = w$.

This identifies maximal consistent sets with assignments. Lindenbaum's lemma can be seen as making a sequence of greedy decisions, with no guess ever being undone.

</details>

### Exercise 4

Let $\Gamma = \{x_1 \to x_2\}$. Run Lindenbaum's construction with an enumeration starting $x_1, x_2$. Run it again with an enumeration starting $\neg x_2, x_1$. State the values that the resulting assignments give to $x_1$ and $x_2$.

<details><summary>Solution</summary>

First enumeration. The set $\Gamma \cup \{x_1\}$ is satisfied by $x_1 = x_2 = 1$, so it is consistent, and $x_1$ is added. Then $\Gamma \cup \{x_1, x_2\}$ is satisfied by the same assignment, so $x_2$ is added. The result has $v(x_1) = v(x_2) = 1$.

Second enumeration. The set $\Gamma \cup \{\neg x_2\}$ is satisfied by $x_1 = x_2 = 0$, so $\neg x_2$ is added. Then $\Gamma \cup \{\neg x_2, x_1\}$ derives $x_2$ by $\to$E and $\bot$ by $\neg$E, so it is inconsistent, and $x_1$ is not added. The result has $v(x_1) = v(x_2) = 0$.

Different enumerations give different maximal consistent sets, and each gives a model of $\Gamma$.

</details>

### Exercise 5

Derive strong completeness from weak completeness and compactness, using only the semantic deduction theorem and rules of natural deduction.

<details><summary>Solution</summary>

Assume $\Gamma \models \varphi$. By compactness, there is a finite $\{\gamma_1, \dots, \gamma_k\} \subseteq \Gamma$ that entails $\varphi$. Applying the semantic deduction theorem $k$ times gives $\models \gamma_1 \to (\gamma_2 \to \dots \to (\gamma_k \to \varphi))$. By weak completeness, this formula is derivable with no assumptions. By Lemma 1, it is derivable from $\Gamma$. Since each $\gamma_i \in \Gamma$, we have $\Gamma \vdash \gamma_i$ by Ax, and applying $\to$E $k$ times gives $\Gamma \vdash \varphi$.

</details>

### Exercise 6

Prove that RAA is independent of the other rules: without RAA, neither $x_1 \lor \neg x_1$ nor $((x_1 \to x_2) \to x_1) \to x_1$ is derivable. Use the three-element chain $0 < \tfrac{1}{2} < 1$ with $\land$ as minimum, $\lor$ as maximum, $\bot$ as $0$, $a \to b = 1$ if $a \leq b$ and $a \to b = b$ otherwise, and $\neg a = a \to 0$. Define the semantic relation by requiring $\inf_{\gamma \in \Gamma} v(\gamma) \leq v(\varphi)$ under every assignment to the chain, where the infimum of the empty set is $1$.

<details><summary>Solution</summary>

Prove by induction on derivations that the rules other than RAA preserve the relation. Fix $v$. Let $g$ be the infimum of the values of $\Gamma$, and let $a$, $b$, $c$ be the values of $\varphi$, $\psi$, $\chi$. In a rule whose premise adds $\varphi$ to $\Gamma$, the infimum for the premise is $\min(g, a)$.

- Ax: $\varphi \in \Gamma$ gives $g \leq a$.
- $\land$I and $\land$E: $g \leq a$ and $g \leq b$ hold if and only if $g \leq \min(a, b)$.
- $\lor$I: $g \leq a$ gives $g \leq \max(a, b)$.
- $\lor$E: from $g \leq \max(a, b)$, $\min(g, a) \leq c$ and $\min(g, b) \leq c$, the chain is distributive, so $g = \min(g, \max(a,b)) = \max(\min(g, a), \min(g, b)) \leq c$.
- $\to$I: assume $\min(g, a) \leq b$. If $a \leq b$, then $a \to b = 1 \geq g$. Otherwise, $a > b$ forces $g \leq b$, because $\min(g, a) \leq b < a$, and $a \to b = b$, so $g \leq a \to b$.
- $\to$E: assume $g \leq a \to b$ and $g \leq a$. If $a \leq b$, then $g \leq a \leq b$. Otherwise, $a \to b = b$, so $g \leq b$.
- $\neg$I and $\neg$E: these are the cases $b = 0$ of $\to$I and $\to$E, since $\neg a = a \to 0$.
- $\bot$E: $g \leq 0$ implies $g \leq a$.

So every formula derivable from no assumptions has value $1$ under every assignment, since the empty infimum is $1$.

Let $v(x_1) = \tfrac{1}{2}$. Then $\neg x_1$ has the value $\tfrac{1}{2} \to 0 = 0$, so $x_1 \lor \neg x_1$ has the value $\tfrac{1}{2}$.

Let $v(x_1) = \tfrac{1}{2}$ and $v(x_2) = 0$. Then $x_1 \to x_2 = 0$, so $(x_1 \to x_2) \to x_1 = 0 \to \tfrac{1}{2} = 1$, and Peirce's law has the value $1 \to \tfrac{1}{2} = \tfrac{1}{2}$.

Neither value is $1$, so neither formula is derivable without RAA. RAA itself fails in this structure, as it must. Take $\Gamma = \{\neg\neg x_1\}$ and $\varphi = x_1$. The premise holds under every assignment, because $\neg a$ and $\neg\neg a$ are never both nonzero. The conclusion fails at $v(x_1) = \tfrac{1}{2}$, where $\neg\neg x_1$ has the value $1$ and $x_1$ has the value $\tfrac{1}{2}$.

</details>

### Exercise 7

Prove that natural deduction is Post-complete for schemas: if $\varphi$ is not valid, and all substitution instances of $\varphi$ are added as axioms, then the system derives $\bot$.

<details><summary>Solution</summary>

Since $\varphi$ is not valid, some assignment $w$ falsifies it. Let $\sigma$ replace each variable $x$ of $\varphi$ by $\top$ if $w(x) = 1$ and by $\bot$ if $w(x) = 0$. The instance $\sigma\varphi$ contains no variables. By the substitution lemma, every assignment gives $\sigma\varphi$ the value $w(\varphi) = 0$. So $\neg\sigma\varphi$ is valid, and by completeness, $\vdash \neg\sigma\varphi$ in the original system. The new axiom gives $\vdash \sigma\varphi$. Then $\neg$E gives $\vdash \bot$.

So any proper strengthening of the system by a schema is inconsistent, which is another way of saying that classical propositional logic is as strong as a consistent logic with these rules can be.

</details>

### Exercise 8

Prove semantically that Cut is admissible in G3: if a sequent has a derivation using Cut, then it has a derivation without Cut.

<details><summary>Solution</summary>

First, Cut is sound. Suppose $v$ falsifies $\Gamma \Rightarrow \Delta$. If $v(\varphi) = 1$, then $v$ falsifies the premise $\Gamma, \varphi \Rightarrow \Delta$. If $v(\varphi) = 0$, then $v$ falsifies the premise $\Gamma \Rightarrow \varphi, \Delta$. So if both premises are valid, the conclusion is valid.

Together with the soundness of the other rules, this shows that every sequent derivable with Cut is valid. By the completeness theorem for cut-free G3, every valid sequent has a cut-free derivation.

This is much shorter than Gentzen's syntactic proof. It gives no algorithm for removing cuts from a given derivation, and no bound on the size of the result.

</details>

### Exercise 9

Apply the resolution completeness proof to $S = \{\{x_1, x_2\}, \{x_1, \neg x_2\}, \{\neg x_1, x_2\}, \{\neg x_1, \neg x_2\}\}$, branching first on $x_1$, and write the refutation.

<details><summary>Solution</summary>

$S|_{x_1=1}$ is $\{\{x_2\}, \{\neg x_2\}\}$. Its refutation lifts, using the original clauses $\{\neg x_1, x_2\}$ and $\{\neg x_1, \neg x_2\}$, to a derivation of $\{\neg x_1\}$.

$S|_{x_1=0}$ is $\{\{x_2\}, \{\neg x_2\}\}$. Its refutation lifts, using $\{x_1, x_2\}$ and $\{x_1, \neg x_2\}$, to a derivation of $\{x_1\}$.

```text
1. {x1, x2}     given
2. {x1, ¬x2}    given
3. {¬x1, x2}    given
4. {¬x1, ¬x2}   given
5. {¬x1}        resolve 3, 4 on x2
6. {x1}         resolve 1, 2 on x2
7. {}           resolve 5, 6 on x1
```

</details>

### Exercise 10

Prove the correctness of Davis-Putnam variable elimination. Let $S$ be a tautology-free clause set and $x$ a variable. Let $S'$ consist of the clauses of $S$ not mentioning $x$, together with all non-tautological resolvents of clauses of $S$ on $x$. Prove that $S$ is satisfiable if and only if $S'$ is satisfiable.

<details><summary>Solution</summary>

If $v$ satisfies $S$, then $v$ satisfies $S'$, since resolution is sound.

Suppose $v$ satisfies $S'$. By the coincidence lemma, $v(x)$ does not matter for $S'$. Define $v'$ from $v$ as follows.

Case 1: for every clause $C \cup \{x\} \in S$ with $x \notin C$, $v$ satisfies $C$. Set $v' = v[x \mapsto 0]$. Clauses containing $\neg x$ are satisfied by $\neg x$. Clauses containing $x$ are satisfied by $C$. Clauses not mentioning $x$ are in $S'$.

Case 2: some clause $C_0 \cup \{x\} \in S$ has every literal of $C_0$ false under $v$. Set $v' = v[x \mapsto 1]$. Clauses containing $x$ are satisfied by $x$. Clauses not mentioning $x$ are in $S'$. Let $D \cup \{\neg x\} \in S$ with $x, \neg x \notin D$ (this holds since $S$ is tautology-free). If $C_0 \cup D$ is not a tautology, it is in $S'$. Then $v$ satisfies it, and since $C_0$ is false, $v$ satisfies $D$. If $C_0 \cup D$ is a tautology, there is a literal $\ell \in C_0$ with $\neg\ell \in D$, because neither $C_0$ nor $D$ is a tautology. Since $\ell$ is false under $v$, the literal $\neg\ell$ is true under $v$, so $v$ satisfies $D$.

In either case, $v'$ satisfies $S$.

</details>

### Exercise 11

Prove the compactness theorem directly, using König's lemma and no proof system. König's lemma states that an infinite tree in which every node has finitely many children has an infinite branch. Assume that $\Gamma = \{\gamma_1, \gamma_2, \dots\}$ is countable.

<details><summary>Solution</summary>

Assume that every finite subset of $\Gamma$ is satisfiable. Build a tree whose nodes at level $n$ are the strings $a \in \{0,1\}^n$, read as values of $x_1, \dots, x_n$, satisfying the following condition: $a$ falsifies none of the formulas among $\gamma_1, \dots, \gamma_n$ whose variables all lie in $\{x_1, \dots, x_n\}$. Order the nodes by the prefix relation.

The set of nodes is closed under taking prefixes. Let $a$ be a node at level $n$ and let $a'$ be its prefix at level $n - 1$. A formula $\gamma_i$ with $i \leq n - 1$ and variables in $\{x_1, \dots, x_{n-1}\}$ has the same value under $a$ and $a'$ by the coincidence lemma, so $a'$ does not falsify it. So the nodes do form a tree.

The tree is infinite. For each $n$, the set $\{\gamma_1, \dots, \gamma_n\}$ has a model, and the restriction of this model to $x_1, \dots, x_n$ is a node at level $n$.

Each node has at most two children, so König's lemma gives an infinite branch, which defines an assignment $v$. For any $\gamma_i$, choose $n \geq i$ such that all its variables lie in $\{x_1, \dots, x_n\}$. The node of the branch at level $n$ does not falsify $\gamma_i$. So $v(\gamma_i) = 1$.

</details>

### Exercise 12

Prove the strong completeness of the Hilbert system with axioms A1, A2, A3 and modus ponens from [Proof Systems](../proof-systems/). Here the language has only $\neg$ and $\to$. Call a set inconsistent if it derives both some $\chi$ and $\neg\chi$. You may use the deduction theorem and the finiteness of derivations.

<details><summary>Solution</summary>

Soundness is the check that the axioms are valid and that modus ponens preserves truth. For completeness, first establish these facts.

Fact 1: $\neg\varphi, \varphi \vdash \psi$. By A1, $\neg\varphi \to (\neg\psi \to \neg\varphi)$, so $\neg\varphi \vdash \neg\psi \to \neg\varphi$. By A3, $\neg\varphi \vdash \varphi \to \psi$. Then modus ponens with $\varphi$ gives $\psi$. Hence an inconsistent set derives every formula.

Fact 2: if $\Gamma, \neg\varphi$ is inconsistent, then $\Gamma \vdash \varphi$. Let $\tau = \varphi \to \varphi$, which is derivable. By Fact 1, $\Gamma, \neg\varphi \vdash \neg\tau$. By the deduction theorem, $\Gamma \vdash \neg\varphi \to \neg\tau$. A3 gives $\Gamma \vdash \tau \to \varphi$, and modus ponens with $\tau$ gives $\Gamma \vdash \varphi$.

Fact 3: $\neg\neg\varphi \vdash \varphi$. The set $\{\neg\neg\varphi, \neg\varphi\}$ is inconsistent, so Fact 2 applies.

Fact 4: if $\Gamma, \varphi$ is inconsistent, then $\Gamma \vdash \neg\varphi$. Since $\Gamma, \varphi$ derives everything and $\neg\neg\varphi \vdash \varphi$, the set $\Gamma, \neg\neg\varphi$ derives everything, so it is inconsistent. Fact 2 applied with $\neg\varphi$ in place of $\varphi$ gives $\Gamma \vdash \neg\varphi$.

Now suppose $\Gamma \nvdash \varphi$. By Fact 2, $\Gamma \cup \{\neg\varphi\}$ is consistent. The Lindenbaum construction gives a maximal consistent $\Delta$ containing it, with the same proof as Lemma 4, using the finiteness of derivations.

Closure. If $\Delta \vdash \alpha$, then $\alpha \in \Delta$: otherwise $\Delta, \alpha$ is inconsistent by maximality, so $\Delta \vdash \neg\alpha$ by Fact 4, and $\Delta$ is inconsistent.

Negation. $\neg\alpha \in \Delta$ iff $\alpha \notin \Delta$. Both cannot hold, by consistency. If $\alpha \notin \Delta$, then $\Delta, \alpha$ is inconsistent, so Fact 4 and closure give $\neg\alpha \in \Delta$.

Implication. $\alpha \to \beta \in \Delta$ iff $\alpha \notin \Delta$ or $\beta \in \Delta$. If $\alpha \to \beta \in \Delta$ and $\alpha \in \Delta$, then modus ponens gives $\beta \in \Delta$. If $\beta \in \Delta$, then A1 and modus ponens give $\alpha \to \beta \in \Delta$. If $\alpha \notin \Delta$, then $\neg\alpha \in \Delta$, and Fact 1 with the deduction theorem gives $\Delta \vdash \alpha \to \beta$.

The truth lemma follows by structural induction, with these two clauses. So $v_\Delta$ satisfies $\Gamma$ and $\neg\varphi$, which gives $\Gamma \not\models \varphi$.

</details>

## Self-check

Before moving on, you must be able to do the following closed-book.

- State soundness, weak completeness, strong completeness and compactness.
- Write the full soundness proof for natural deduction, with all rules.
- Write the full Henkin completeness proof, including weakening, finiteness, the reduction lemma, Lindenbaum's lemma, all closure properties and the truth lemma, and state where RAA is used.
- Prove the completeness of G3 by search, and prove the completeness of resolution by restriction and lifting.
- Sketch Kalmár's proof, and derive compactness from completeness.
- Apply compactness to a concrete problem, such as the coloring of infinite graphs.

## Materials

- Enderton, A Mathematical Introduction to Logic, 2nd edition. Read the sentential logic chapter for its direct semantic proof of compactness, and the first-order chapter's proof of soundness and completeness as the model for the Henkin construction. The sentential logic chapter is purely semantic, so it does not contain the proof of completeness for a propositional proof system.
- Huth and Ryan, Logic in Computer Science, 2nd edition. Read the propositional logic chapter's sections on soundness and completeness for natural deduction. Its completeness proof proceeds through lines of the truth table, in the same spirit as the Kalmár proof given here.
