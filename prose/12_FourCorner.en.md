# 12. Negative association and the four-corner

<!--navtop-->
[← 11. The block core](11_TwoTransport.md) · [Table of contents](00_Overview.md) · [13. The fractal layer →](13_FractalLayer.md)
<!--/navtop-->



In the previous chapter [11](11_TwoTransport.md) we built the block bridge `twin_prime_conjecture_of_blocks`:
the infinitude of twins follows if at every scale `N` there is a carrier with a survivor,
and the "bad" part is strictly smaller than the carrier. With that, the entire content of the
problem was compressed into a single block inequality of cardinalities.

The present chapter takes that inequality and translates it into the language of *tallies by
side ranks* of $6m\pm1$, where it assumes the form of a *four-corner* relation. We
will show that the required direction `N_{33}<N_{00}` is not a density fact but a **symmetry** fact: it
is forced by the negative association of the two ranks, which in turn is a shadow of the exclusive
(per-prime) structure of the two.

## Tallies by rank and the matrix $N_{ij}$

Fix a block of candidate centers `m` (indices of the survivor class at scale `A`).

**Definition 12.1** (side ranks). To each center `m` assign the pair of side ranks
$$r_-(m)=\bigl\lvert\{p\le A: p\mid 6m-1\}\bigr\rvert,\qquad r_+(m)=\bigl\lvert\{p\le A: p\mid 6m+1\}\bigr\rvert,\tag{12.1}$$
— the number of small prime divisors of the left and the right side respectively. A center is a twin
center if and only if both sides are free of small divisors, that is, `r_-=r_+=0` (after the
sieve-to-the-root this entails the primality of both sides; see [10](10_NonCover.md)).

> **Note.** The rank here counts precisely the **small** divisors $p\le A$; the completeness of the
> rank (that zero rank entails primality) is guaranteed by the sides lying below `A^2` — this is the
> same sieve-to-the-root mechanism `prime_of_no_small_prime_factor` from [10](10_NonCover.md).

Coarsen the ranks to the binary feature "zero / nonzero" and introduce the $2\times2$ tally matrix over
the pair $(\,[r_-{>}0]\,,[r_+{>}0]\,)$:

$$
\begin{array}{c|cc}
 & r_+=0 & r_+>0\\\hline
 r_-=0 & N_{00} & N_{03}\\
 r_->0 & N_{30} & N_{33}
\end{array}
$$

Here $N_{00}$ is the number of centers with both sides clean (**these are exactly the twin centers**), $N_{33}$ —
the centers whose both sides are "spoiled" by a small divisor, and $N_{03},N_{30}$ are the mixed ones
(one side clean, the other not). The indexing `0/3` is a legacy of the rank scale `0..3` in the sources;
the digit `3` encodes "nonzero rank".

Our goal in this chapter is to compare the corner tallies: to prove that the **diagonal** `N_{33}` (both
spoiled) is outweighed by the opposite corner `N_{00}` (both clean). This is exactly what yields the lower
bound on twin centers within a block.

## The rank-1 approximation and the sign of the rank-2 correction

It is natural to assume that, to first approximation, the spoilage indicators of the left and right sides
are *independent*. If the probabilities $\Pr[r_->0]=\pi_-$ and $\Pr[r_+>0]=\pi_+$ were independent, the tally
matrix $N_{ij}$ would have **rank 1**:

$$
N_{ij}\ \approx\ T\cdot u_i\, v_j,\qquad u=(1-\pi_-,\ \pi_-),\quad v=(1-\pi_+,\ \pi_+),
$$

where `T` is the total number of centers. For a rank-1 matrix all four $2\times2$ minors vanish; in
particular, the exact equality holds
$$N_{00}\,N_{33}\ =\ N_{03}\,N_{30}.\tag{12.2}$$

The observation: the real tally matrix is not of rank 1 — there is a **rank-2 correction**, and the whole
question is its *sign*.

**Definition 12.2** (four-corner defect). Set
$$\boxed{\ \Delta_{\mathrm{fc}}\ :=\ N_{03}\,N_{30}-N_{00}\,N_{33}\ }\tag{12.3}$$
— this is (up to normalization) the determinant of the tally matrix, that is, the amplitude of its rank-2 part.
The sign of $\Delta_{\mathrm{fc}}$ is the sign of the covariance of the binary ranks:
$$\mathrm{sgn}\,\Delta_{\mathrm{fc}}\ =\ -\,\mathrm{sgn}\,\mathrm{Cov}\big([r_-{>}0],[r_+{>}0]\big).$$

The condition $\Delta_{\mathrm{fc}}\ge0$, that is,
$$N_{00}\,N_{33}\ \le\ N_{03}\,N_{30},\tag{12.4}$$
is called the **four-corner inequality** and is equivalent to the **negative association** of the ranks:
the spoilage of one side makes the spoilage of the other *less* likely. It is precisely this sign that we
need, and precisely this sign that is not accidental.

## Why the sign is negative: the exclusive structure of the two

Negative association is not postulated here — it flows from the already proven
**exclusivity** of divisors (see [02](02_Carrier.md), `no_large_shared_divisor`): a prime `p>2` cannot divide
both sides at once, for $\gcd(6m-1,6m+1)\mid 2$. Hence at every prime the contribution to the two ranks is
exclusive: `p` divides either `6m-1`, or `6m+1`, or nothing — but *never both*.

From this the per-prime generating function of the ranks is a **product over primes with no cross
term**:

$$
\prod_{2<p\le A}\big(c_p+a_p\,x+b_p\,y\big),\qquad a_p=b_p\ (\pm\text{ symmetry}),\ \textbf{no term }xy,
$$

where `x` marks the contribution to `r_-`, `y` — to `r_+`, and the absence of `xy` is a direct consequence
of "both at once" being forbidden.

Expanding such a product yields at every prime
$$\mathrm{Cov}\big(\mathbf 1_{p\mid-},\mathbf 1_{p\mid+}\big)=0-a_pb_p=-a_pb_p<0,$$
and summation over the primes of the layer preserves the sign:
$$\mathrm{Cov}(r_-,r_+)=\sum_{p}(-a_pb_p)<0.$$
The negative covariance of the ranks is exactly the four-corner.

**Conclusion.** The sign is forced by the exclusive structure of the two, not by the density of primes.

> **Note.** In the CRT model the same inequality is derived purely by symmetry — via Maclaurin's
> inequality on elementary symmetric polynomials: $R_{\mathrm{CRT}}=20\,e_6/e_3^2\le 20\binom{s}{6}/\binom{s}{3}^2<1$.
> This confirms that the four-corner is a property of the *shape* of the product `c+ax+by`, not of analytic prime-counting estimates.

## The algebra of the passage: four-corner + side-corner ⟹ $N_{33}<N_{00}$

The four-corner inequality by itself compares the diagonal `N_{00}N_{33}` with the mixed product
`N_{03}N_{30}`. To obtain the desired `N_{33}<N_{00}`, a second, *lateral* ingredient is needed —
the **side-corner**:
$$N_{03}\,N_{30}\ \le\ N_{00}^{\,2}.\tag{12.5}$$
It says that the mixed corners are small compared with the clean one: low rank is markedly more likely
than high rank (the same survivor recursion $q\to q-2$), so the clean corner `N_{00}` dominates. Formally
we have formalized precisely the *algebra of the passage* — that these two inequalities together force the conclusion.

The non-strict passage is the lemma:

**Theorem 12.3** (`N33_le_N00_of_four_corner`). Let $N_{00},N_{03},N_{30},N_{33}\in\mathbb N$. If $0<N_{00}$, the four-corner $N_{00}\,N_{33}\le N_{03}\,N_{30}$ and the side-corner $N_{03}\,N_{30}\le N_{00}^{2}$ hold, then $N_{33}\le N_{00}$. 🟢

The proof is elementary: the chain $N_{00}N_{33}\le N_{03}N_{30}\le N_{00}\cdot N_{00}$ gives
$N_{00}N_{33}\le N_{00}N_{00}$, whence cancelling the positive factor `N_{00}`
(`Nat.le_of_mul_le_mul_left`) yields $N_{33}\le N_{00}$.

The strict form — what we actually need (a strict gap `B_5>0`, that is, *more* clean
centers than fully spoiled ones) — is given by the lemma:

**Theorem 12.4** (`N33_lt_N00_of_four_corner`). Let $N_{00},N_{03},N_{30},N_{33}\in\mathbb N$. If $0<N_{00}$, the **strict** four-corner $N_{00}\,N_{33}<N_{03}\,N_{30}$ and the side-corner $N_{03}\,N_{30}\le N_{00}^{2}$ hold, then $N_{33}<N_{00}$. 🟢

Here the strict inequality $N_{00}N_{33}<N_{03}N_{30}$ is threaded through the side-corner up to
$N_{00}N_{33}<N_{00}N_{00}$, and `lt_of_mul_lt_mul_left` cancels `N_{00}` on the left, giving the strict conclusion.

Finally, the $\pm$ symmetry of the sides substantially simplifies the side-corner. Since the left and right sides
enter the product symmetrically ($a_p=b_p$), the mixed corners are equal: $N_{03}=N_{30}$. The lemma
`side_corner_of_le` records this simplification:

**Theorem 12.5** (`side_corner_of_le`). Let $N_{00},N_{03},N_{30}\in\mathbb N$. If $N_{03}=N_{30}$ and $N_{03}\le N_{00}$, then the side-corner $N_{03}\,N_{30}\le N_{00}^{2}$ holds. 🟢

Substituting the symmetry reduces the quadratic inequality $N_{03}N_{30}\le N_{00}^2$ to a product of two
identical factors $N_{03}\cdot N_{03}\le N_{00}\cdot N_{00}$, each of which is majorized via
$N_{03}\le N_{00}$ (`Nat.mul_le_mul`). Thus the entire lateral node rests on a single linear
fact: there are no more mixed centers than purely twin centers.

> **Note.** All three lemmas `N33_le_N00_of_four_corner`, `N33_lt_N00_of_four_corner`,
> `side_corner_of_le` are over $\mathbb N$, machine-checked, and use no `sorry`. They
> formalize the **algebra of the passage**, not the corner inequalities themselves.

## Numerical background and magnitudes

Denote the corner ratios
$$R_{\mathrm{fc}}=\frac{N_{00}N_{33}}{N_{03}N_{30}},\qquad R_{\mathrm{sc}}=\frac{N_{03}N_{30}}{N_{00}^{2}}.$$
Then the proportion of fully-spoiled to clean factorizes:
$$\frac{N_{33}}{N_{00}}=R_{\mathrm{fc}}\cdot R_{\mathrm{sc}}.$$

Numerically (`tools/RESULTS_fourcorner.md`) the direction holds on all blocks: $R_{\mathrm{fc}}<1$
everywhere, and as the layer grows $R_{\mathrm{fc}}$ rises toward 1 from below ($0.876\to0.977$ over $k=21\dots28$), while
the lateral ratio remains steadily small, $R_{\mathrm{sc}}\approx0.014$. Hence
$$\frac{N_{33}}{N_{00}}\le(1+o(1))\cdot0.014\ll1,$$
and for the strict `N_{33}<N_{00}` no four-corner *margin* is needed — the **direction** itself,
$R_{\mathrm{fc}}\le1$, plus the smallness of $R_{\mathrm{sc}}$ suffice.

> **Note.** That $R_{\mathrm{fc}}\to1$ from below, rather than bouncing off 1, is structural too:
> the pairwise correlations are small ($a_pb_p\sim p^{-2}$), their sum over the layer $(A,A^2]$ tends to zero, and the ranks
> become asymptotically independent. Exclusivity forbids crossing the mark 1, so the limit
> is attained strictly from below. But it is precisely this tightness near 1 that hides the parity problem — see below.

## Where the node is open: the conjecture and the closing plan

The three formalized lemmas give the **passage**, but not the corner inequalities themselves for the *real*
tallies. The honest boundary — in the house sense of an honestly named open node (see the [glossary](GLOSSARY.md)) — runs here.

**Conjecture 12.6** (the real four-corner). For the real CRT tallies of the survivor block at scale `A`,
the strict $N_{00}N_{33}<N_{03}N_{30}$ and the side-corner $N_{03}N_{30}\le N_{00}^2$ hold. 🟡

**Closing plan (distribution-free).** The model inequality for the product `c+ax+by` is provable
elementarily (Maclaurin / negative association). One step **model→reality** remains:
to show that the exact CRT tallies coincide with this product to an order that does not flip the sign of
the rank-2 correction. Formally this is worked out in [14](14_RealFourCorner.md) via the exact decomposition of the remainder
$N_{ij}^{\text{real}}=N_{ij}^{\text{model}}+e_{ij}$; the task is to bound `e_{ij}` so that
$\mathrm{sgn}\Delta_{\mathrm{fc}}$ is preserved.

**Section takeaway.** We do *not* pass the reduction off as a proof: so far
only the algebra of the passage and the model sign are proven; control of the remainder `e_{ij}` is an open front, but
the candidate is distribution-free, not density-based.

## A bridge to the next chapter

With that, the content of the problem has once again localized — now into **one correlational fact**:
the negative association of the ranks $(r_-,r_+)$ on the real tallies. We have already seen that its root is
the exclusive per-prime structure of the two: the product `c+ax+by` *without* the term `xy`.

In the next chapter [13](13_FractalLayer.md)
we lift this observation to the level of the **fractal layer of the engine**: we show that the same two
organizes the self-similar recursion of survivors upward through the primes ($q\to q-2$) and the finite blocker
collapse downward in scale, and that it is precisely this fractal exclusivity that is the common source both of the direction
$R_{\mathrm{fc}}\le1$ and of the finiteness of the descent depth (EPMI — the impossibility of a perpetual engine,
see the [glossary](GLOSSARY.md)).

<!--navbot-->

---

[← 11. The block core](11_TwoTransport.md) · [Table of contents](00_Overview.md) · [13. The fractal layer →](13_FractalLayer.md)
<!--/navbot-->
