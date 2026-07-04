# The carrier of two: the shared gcd divides 2

<!--navtop-->
[← 01. The Engine (EPMI)](01_EPMI.md) · [Table of contents](00_Overview.md) · [03. Preservation of Two →](03_TwoGap.md)
<!--/navtop-->



In the previous chapter, [01. The Engine (EPMI)](01_EPMI.md), we built the programme's central object — Euclid's perpetual engine — and established that its local impossibility rests on a strictly decreasing height resource.

Before descending along the chain of links, we need to understand exactly what in a twin pair stays unchanged under descent and what separates its sides.

The present chapter isolates this invariant in a pure, elementarily checkable form: the difference of the sides equals two, and the entire arithmetic of how the sides interact with prime divisors is governed by this number.

## Setting

We work with the centres of twin pairs. To each pair of twin primes corresponds an integer $m \ge 1$ for which both sides

$$
6m - 1 \qquad \text{and} \qquad 6m + 1
$$

are candidates for primality. The form $6m \pm 1$ is no accident: every prime $p > 3$ lies in one of the residue classes $\pm 1 \pmod 6$, so a twin pair with difference $2$, both of whose members exceed $3$, is inevitably centred at a multiple of six. We call the number $m$ the **centre**, and the expressions $6m-1$, $6m+1$ the **sides** of the centre.

> **Note.** The condition $m \ge 1$ carries a double load here. First, it excludes the degenerate case $m=0$, in which the "side" $6m-1$ becomes $-1$ and loses meaning in natural-number arithmetic. Second — and this matters more for the formalisation — when working in $\mathbb{N}$ subtraction is truncated ($6m-1$ at $m=0$ would give $0$, not $-1$), so the premise $1 \le m$ guarantees that $6m-1$ is the honest predecessor of $6m$, and the identity $6m+1 = (6m-1)+2$ holds as an equality of natural numbers.

The chapter's question is utterly concrete: how does a common divisor of the two sides relate to their difference, and what does that entail for primes "sitting" on both sides at once?

## Two as the difference of the sides

We begin with the observation from which everything else grows. The sides stand exactly $2$ apart:

$$
(6m+1) - (6m-1) = 2 . \tag{2.1}
$$

It is natural to conjecture that precisely this fixed difference governs all joint divisibility of the sides. Let us formalise this.

**Definition 2.1** (common divisor of the sides). A prime (or, in the general formulation, any natural number) $p$ is called a *common divisor of the sides* of the centre $m$ if simultaneously
$$
p \mid (6m-1) \qquad \text{and} \qquad p \mid (6m+1).
$$

The chapter's first theorem asserts that every such $p$ is forced to divide two.

> **Theorem 2.2** (`twin_sides_shared_dvd_two`). Let $m \ge 1$, and let $p \mid (6m+1)$ and $p \mid (6m-1)$. Then $p \mid 2$.

The meaning of the statement: a common divisor of the sides cannot be larger than their difference permits. The proof is transparent and rests on one identity and one divisibility property.

*Anatomy of the proof.* The key step is to rewrite the larger side through the smaller one:
$$
6m + 1 = (6m - 1) + 2 . \tag{2.2}
$$
In Lean this equality is closed by the tactic `omega` (linear arithmetic over $\mathbb{N}$, accounting for truncated subtraction under $m \ge 1$). After the substitution, the hypothesis $p \mid (6m+1)$ turns into
$$
p \mid \big((6m-1) + 2\big).
$$
Now a basic divisibility property applies: if $p$ divides a sum and divides one of the summands, it divides the other as well. In the Lean 4 kernel this is `Nat.dvd_add_right`: from $p \mid (6m-1)$ follows the equivalence $p \mid \big((6m-1)+2\big) \iff p \mid 2$, and the left-hand side is already in our hands. Hence $p \mid 2$. $\qquad\blacksquare$

> **Note.** Neither of the numbers $6m\pm1$ enters this proof in any essential way — only their *difference* does the work. The same reasoning would give: any common divisor of two numbers divides their difference, and therefore $\gcd(6m-1, 6m+1) \mid 2$. The formulation via $p \mid 2$ is chosen because what interests us later is precisely the behaviour of prime divisors rather than the numerical value of the $\gcd$; but in substance the theorem is exactly the statement $\gcd(6m-1,\,6m+1) \mid 2$.

## Exclusivity: a large prime divides at most one side

From divisibility of two an informative consequence follows at once. Two is small: its only natural divisors are $1$ and $2$. So if a common divisor of the sides is nontrivial at all, it equals $2$; and no prime $p > 2$ can be a common divisor.

> **Theorem 2.3** (`no_large_shared_divisor`). Let $m \ge 1$ and $p > 2$. Then it is impossible to have $p \mid (6m+1)$ and $p \mid (6m-1)$ simultaneously.

In other words (and this is **exclusivity**): *a prime $p > 2$ divides at most one of the two sides.* It is free to divide $6m-1$, free to divide $6m+1$, but not both at once — both could be occupied only by a divisor of two, and $p>2$ is no such thing.

*Anatomy of the proof.* The reasoning is a short chain from the previous theorem to a contradiction. From the assumption that $p$ divides both sides, Theorem 2.2 (`twin_sides_shared_dvd_two`) yields $p \mid 2$. Next we use: a divisor of a positive number does not exceed it — in Lean this is `Nat.le_of_dvd` (the positivity $2 > 0$ is checked by `decide`), whence $p \le 2$. But by hypothesis $2 < p$. The inequalities $p \le 2$ and $2 < p$ are incompatible; the contradiction is closed by the tactic `omega`. $\qquad\blacksquare$

> **Note.** Both theorems of the file `Engine/Carrier.lean` are proven in the bare Lean 4 kernel — without `mathlib`, on three primitives: the identity (`omega`), moving a summand across (`Nat.dvd_add_right`), and the divisor bound (`Nat.le_of_dvd`). This makes the result part of the programme's strictly verified, self-contained foundation: there is no reduction to anything unproven here, no hidden hypothesis — only elementary divisibility.

## What this means for the programme: two as the carrier

Now let us assemble the meaning. A twin pair has a *unique* divisor shared by both sides — and it is two (when it is present at all; for odd sides the common divisor is trivial, $\gcd = 1$). All nontrivial prime divisors of the sides are **exclusive**: each belongs to exactly one side. It is precisely this partition of the primes into two sets, disjoint over the large primes, that constitutes the structural fact we will exploit during descent.

In the terminology of the Lean comment this is "shared active gcd $= 0$": no *active* prime $p > A \ge 2$ divides both sides, so the shared-active class is empty.

Two is removed from the active layer as a prime known to be small, and at the active level the sides are divisibility-independent.

This is exactly the independence needed by the rank-$(3,3)$ determinant law of [05. Irreversibility](05_Irreversibility.md): factoring $6m-1 = abv$ and $6m+1 = qrs$ into products of active primes, we are entitled to treat all six factors $a,b,v,q,r,s$ as *distinct* — exclusivity forbids a divisor from coinciding across the sides.

Hence the metaphor of the **carrier**. Two is what, throughout the entire programme, *separates* the sides (guaranteeing the exclusivity of large primes) and at the same time is *carried along* under descent: when an active factor is removed, the descended centre inherits the same difference $2$ between its own sides. Descent changes the scale of the centre and reshuffles the factorisations, but does not touch the quantity separating $6m'-1$ from $6m'+1$. Two is invariant under descent — it is the descent's load-bearing frame.

> **Observation.** It is useful to see in this a discrete analogue of a "conserved quantity". The height $H$ from chapter [01. The Engine (EPMI)](01_EPMI.md) strictly decreases and thereby forbids perpetual motion; the difference $2$, by contrast, is strictly *conserved* and thereby fixes the geometry of every link. A decreasing resource and a conserved carrier are two sides of one mechanism: the first drives the descent to the bottom, the second makes sure that at every step the object remains a twin pair with the same gap.

## Bridge to the next chapter

We have established that two separates the sides and that large primes are exclusive.

It remains to verify the claim that so far has sounded only as a promise: that the difference $2$ genuinely *survives* the descent operation rather than being restored by coincidence at every step.

In the next chapter, [03. Preservation of Two](03_TwoGap.md), we formalise the preservation of two under descend — we show that after the removal of an active factor the new pair of sides again stands exactly $2$ apart — and thereby turn the carrier from an observation into an invariant on which the infinite descent can rest.

<!--navbot-->

---

[← 01. The Engine (EPMI)](01_EPMI.md) · [Table of contents](00_Overview.md) · [03. Preservation of Two →](03_TwoGap.md)
<!--/navbot-->
