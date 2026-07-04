# No backward move on two points

<!--navtop-->
[← 05. Irreversibility](05_Irreversibility.md) · [Table of contents](00_Overview.md) · [07. The short train →](07_Squeeze.md)
<!--/navtop-->



> Lean source: `Engine/NoBackward.lean` (`exclusive_diag_zero`, `exclusive_no_backward`).

## Where we are

In [chapter 05](05_Irreversibility.md) we established the irreversibility of Euclid's engine — that infinite strictly descending chain, the programme's central forbidden object (see the [glossary](GLOSSARY.md)): the height `H` strictly decreases along the descent (`StrictAnti H`), time cannot be reversed, and a perpetual engine is impossible. The arrow of time fixes a direction on *one* coordinate — the height of the centre.

Now we ask a subtler question: what happens when the engine is viewed on *two* points at once — on the left side `6m-1` and on the right side `6m+1`. It turns out there is a prohibition on moving backward here too, and it is purely arithmetic in nature. This very prohibition will become the source of the negative association later exploited by the four-corner ([chapter 12](12_FourCorner.md)).

## The starting observation: the exclusivity of two

Recall a fact from [chapter 02](02_Carrier.md) (Carrier). The two sides of a twin differ by `2`:
$$(6m+1)-(6m-1)=2.$$
Hence any common divisor of both sides divides their difference, whence
$$\gcd(6m-1,\,6m+1)\mid 2.$$
The corollary, recorded in Lean as `Carrier.no_large_shared_divisor`: **a prime `p>2` does not divide both sides at once** — it divides at most one of them. Let us call this property *exclusivity*: at each odd prime, exactly one of the two outcomes (or neither), but never both simultaneously.

**Definition 6.1** (indicators, ranks, exclusivity). For a prime $p$ of index $i$ from a finite set $s$, define indicator weights $X, Y : \iota \to \mathbb{N}$ by
$$X_p=\mathbf{1}[\,p\mid 6m-1\,],\qquad Y_p=\mathbf{1}[\,p\mid 6m+1\,]$$
— the "contribution on the left" and the "contribution on the right". The ranks (numbers of prime divisors of each side):
$$r_-=\sum_{p\in s}X_p,\qquad r_+=\sum_{p\in s}Y_p.$$
The *exclusivity* condition — the hypothesis `hexcl` in Lean:
$$X_p\cdot Y_p=0\quad\text{for every }p\in s.$$

> **Note.** In Lean this condition is factored out into the hypothesis `hexcl : ∀ i ∈ s, X i * Y i = 0`. The quantities `X, Y : ι → ℕ` live in the natural numbers, not strictly in `{0,1}`: the proofs below use only `X_p·Y_p=0`, and so hold for *any* nonnegative weights with vanishing product. This makes the result an abstract algebraic lemma rather than a statement tied to specific indicators.

## The diagonal vanishes

The first statement is simple but load-bearing. It says that the sum of "self" terms, where one and the same prime sits on both sides, equals zero.

**Theorem 6.2** (`exclusive_diag_zero`). For a finite set $s$ and weights $X, Y : \iota \to \mathbb{N}$, if $X_p \cdot Y_p = 0$ for all $p \in s$, then
$$\sum_{p\in s}X_p\cdot Y_p=0. \tag{6.1}$$

The Lean proof is a single line (`Finset.sum_eq_zero hexcl`): a sum of zeros is zero. But the substantive meaning matters more than the brevity. The quantity `\sum_p X_p Y_p` is the *diagonal*: it counts the cases where a prime `p` divides both the left and the right side — that is, a "backward move on one point", a self-transition in which the engine at that prime returns into itself, touching both sides simultaneously. Exclusivity erases this diagonal completely: `\text{DIAG}=0`.

> **Note.** The diagonal here is not a metaphor but a concrete term of a decomposition. In matrix language, if `N_{ij}` is the count of centres with ranks `(r_-,r_+)=(i,j)`, then nonzero diagonal contributions at the level of primes would correspond to the "both divide" correlation. Exclusivity annihilates them pointwise, before any summation over centres.

## The engine does not run backward on two points

The second statement is the main one. It turns the pointwise vanishing of the diagonal into a structural property of the *product of ranks*.

**Theorem 6.3** (`exclusive_no_backward`). For a finite set $s$ with decidable equality of indices $[\mathrm{DecidableEq}\; \iota]$ and weights $X, Y : \iota \to \mathbb{N}$, under the exclusivity $X_p \cdot Y_p = 0$ for all $p \in s$,
$$\Bigl(\sum_{i\in s}X_i\Bigr)\cdot\Bigl(\sum_{j\in s}Y_j\Bigr)=\sum_{i\in s}\ \sum_{j\in s\setminus\{i\}}X_i\cdot Y_j. \tag{6.2}$$

That is, the product of ranks `r_-\cdot r_+` is entirely *off-diagonal*: the double sum contains no terms with `i=j`; only the pairs `i\neq j` remain.

*Why this is true.* Expand the product of sums. Distributivity (`Finset.sum_mul`, then `Finset.mul_sum`) gives
$$\Bigl(\sum_i X_i\Bigr)\Bigl(\sum_j Y_j\Bigr)=\sum_{i\in s}\sum_{j\in s}X_i\,Y_j.$$
Split the inner sum over `j\in s` by extracting the term `j=i` (the lemma `Finset.add_sum_erase`):
$$\sum_{j\in s}X_i\,Y_j=X_i\,Y_i+\sum_{j\in s\setminus\{i\}}X_i\,Y_j.$$
The extracted term `X_i Y_i` is exactly `X_i\cdot Y_i`, and by exclusivity `X_i\cdot Y_i=0` for `i\in s` (`hexcl i hi`). After `zero_add`, only the off-diagonal part survives. Summing over `i` completes the proof.

Structurally, this is precisely "no backward move on two points". The product `(\sum X)(\sum Y)` describes the joint behaviour of the engine on the left and right side. The diagonal `i=j` would correspond to a simultaneous move "into itself" on both points — the self-transition `2\to 2`. Exclusivity forbids it at each prime, and therefore forbids it in the whole sum: only the cross transitions `i\neq j` remain, where the left divisor and the right divisor are different primes.

> **Note.** The requirement `[DecidableEq ι]` is needed only technically: so that `s.erase i` is defined (one must be able to decide `j=i`). It carries no mathematical content — for finite sets of primes, equality is always decidable.

## What this means: the source of the negative association

Let us put the two facts together. Decompose the covariance of the ranks. For the joint distribution of `(r_-,r_+)` over centres,
$$\mathrm{Cov}(r_-,r_+)=\underbrace{\text{CROSS}}_{\text{off-diagonal coupling}}-\underbrace{\text{DIAG}}_{\sum_p P_p^-P_p^+}, \tag{6.3}$$
where $\text{DIAG}$ gathers the "both divide at one prime" contributions.

Theorem 6.2 (`exclusive_diag_zero`) annihilates the pointwise diagonal, and Theorem 6.3 (`exclusive_no_backward`) shows that the entire structure of the product of ranks is off-diagonal. This is exactly where the sign comes from: the vanished diagonal is the "heat" removed by irreversibility, and it shifts the association of `(r_-,r_+)` toward the negative.

The numerical reconnaissance (`tools/RESULTS_rank2.md`) confirms this robustly: the count matrix `N_{ij}` is close to rank 1 (the ranks are almost independent, `sv_2/sv_1\approx 0.001`), while the sign of the rank-2 correction — the very one the four-corner sees — is *negative at all scales tested*, because `\mathrm{Cov}(r_-,r_+)<0` everywhere.

**Conclusion.** The source of this sign is neither the density of primes nor statistics, but *exact arithmetic exclusivity*: a prime divides at most one side (`shared gcd ∣ 2`).

> **Note.** Let us underline the honesty boundary. Theorem 6.3 (`exclusive_no_backward`) proves the *structure* (the product of ranks is off-diagonal) and the vanishing of $\text{DIAG}$ as a pointwise term (equation (6.1)). This is NOT yet the sign $\mathrm{Cov}(r_-,r_+)<0$ itself for the real counts: there the competing term $\text{CROSS}$ (finite-range correlation) is present, and one needs $\text{DIAG}>\text{CROSS}$.
> Exclusivity gives us the first summand of decomposition (6.3) — a necessary but not sufficient part. The inequality $\text{DIAG}>\text{CROSS}$ itself (equivalently $D=N_{03}N_{30}-N_{00}N_{33}>0$) remains an open node of the programme.

**Conjecture 6.4** (negative association of ranks). The ranks $(r_-, r_+)$ are negatively associated at all scales:
$$N_{00}N_{33}\le N_{03}N_{30}, \tag{6.4}$$
equivalently $\text{DIAG}\ge\text{CROSS}$.

**Closing plan.** Exclusivity (`Carrier.no_large_shared_divisor`, Theorem 6.2 (`exclusive_diag_zero`)) gives the pointwise structure "a per-prime product with no cross $xy$ term" — this is exactly the product CRT model $\prod_p(c_p+a_p x+b_p y)$ without the $xy$ term ([chapter 12](12_FourCorner.md)). For such a model, negative association is provable elementarily (Maclaurin).

What remains is the control of the model→reality remainder: showing that the real `\text{CROSS}` does not exceed `\text{DIAG}`. This is a distribution-free candidate, but numerically `1-R_{fc}\to 0` (knife-edge), which points to proximity to the parity wall. None of the available techniques yields a distribution-independent closure so far; hence the node here is declared open, not closed (on node statuses, see the [glossary](GLOSSARY.md)).

## Bridge to the next chapter

We have obtained the prohibition on moving backward on two points — an arithmetic mechanism that annihilates the diagonal and makes the joint structure of the ranks purely off-diagonal. This constraint acts on the *width* of the engine's move (the joint behaviour of the sides).

In the [next chapter, 07](07_Squeeze.md) we turn to the constraint on the *length* of the move: the algebraic cubic squeeze `12(h+6h^2)<A\Rightarrow 72h^2<A`, that is `h<\sqrt{A/72}`, shows that the valid segment of a train — the number of actually reachable centres along the affine line — is short, even when the line itself and the `+1` fuel are infinite.

**Section takeaway.** Irreversibility in height, the backward prohibition in width, and the short train in length together squeeze the engine from all sides.

<!--navbot-->

---

[← 05. Irreversibility](05_Irreversibility.md) · [Table of contents](00_Overview.md) · [07. The short train →](07_Squeeze.md)
<!--/navbot-->
