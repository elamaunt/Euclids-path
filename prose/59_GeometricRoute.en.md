# 59. The geometric route: Segre defect, the exact diagonal, and an honest reduction

<!--navtop-->
[← 58. The profinite skeleton](58_ProfiniteSkeleton.md) · [Contents](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricSegreDefect.lean` (`statePoly`, `segre_decomposition`,
> `exterior_algebra_identity`), `Engine/GeometricPrimeProjector.lean`
> (`signed_card_sum`, `softProjector`, `softProjector_bounds`),
> `Engine/GeometricFactorBox.lean` (`factorBox_volume`, `anisotropy2_eq_cosh`),
> `Engine/GeometricTwinShellFourier.lean` (`twin_defect_law`,
> `hodge_even_kills_odd_modes`, `logDivisor_fourier`),
> `Engine/GeometricDiagonalCovariance.lean` (`diag_energy_zero`,
> `diag_cov_period_exact`, `wing_marginal_minus`, `wing_marginal_plus`),
> `Engine/GeometricReduction.lean` (`twinCenter_of_window`, `ReductionHolds`,
> `twinCenters_cofinal_of_reduction`), `Engine/GeometricRouteClassification.lean`
> (`GeometricMixingTarget`, `twins_of_geometricMixingTarget`,
> `mixing_forces_fourCorner`).

This chapter opens the repository's second major route — the **geometric** one. Its founding
intuition is simple: a twin is a *coincidence* of two events ("$6m-1$ is prime" and "$6m+1$
is prime"), and the coincidence of two events is governed by their **covariance**. The route
translates the twin question into bilinear algebra (the Segre decomposition), builds an exact
multiplicative primality projector, computes the diagonal part of the covariance **exactly**
— and stops honestly at the same place every route of this book stops: the off-diagonal
part, which is precisely the parity wall ([12](12_FourCorner.md),
[32](32_RankParityUnity.md)). Nothing is renamed: the route's conditional summit is called
conditional, and its wall is the same wall.

## 1. The Segre defect: covariance as an algebraic object

The state of a pair of indicators at one center is described by four masses: $T$ (both
zero), $U$, $V$ (exactly one), $Q$ (both one).

> **Definition 59.1** (state polynomial). The state polynomial
> $F(x,y) = T + U\,y + V\,x + Q\,xy$ (Lean: `statePoly`) with total mass $A = T+U+V+Q$
> (`Adet`), left factor $L(x) = (T+U) + (V+Q)x$ (`Lfac`), right factor
> $R(y) = (T+V) + (U+Q)y$ (`Rfac`), and **Segre defect** $\Delta = TQ - UV$ (`segreDelta`).

> **Theorem 59.2** (`segre_decomposition`). In any commutative ring,
>
> $$
> A\cdot F(x,y) \;=\; L(x)\,R(y) \;+\; \Delta\,(1-x)(1-y). \tag{59.1}
> $$
>
> The state splits into a product of marginals plus a single rank-one term with coefficient
> $\Delta$: the pair of indicators is independent exactly when its Segre defect vanishes. 🟢

The defect is the (unnormalized) covariance: for $A \ne 0$ one has
$Q/A - \frac{(V+Q)}{A}\cdot\frac{(U+Q)}{A} = \Delta/A^2$ (`cov_eq_delta_div_Asq`).
Its energy form is an exterior-algebra identity:

> **Theorem 59.3** (`exterior_algebra_identity`). For any weights $w$ and fields $x, y$ on a
> finite set $s$,
>
> $$
> 2\Bigl(\sum_k w_k \sum_k w_k x_k y_k - \sum_k w_k x_k \sum_k w_k y_k\Bigr)
>   = \sum_{k,l} w_k w_l\,(x_k - x_l)(y_k - y_l). \tag{59.2}
> $$
>
> Covariance is a sum of pairwise "areas" $(x_k-x_l)(y_k-y_l)$: a bilinear 2-vector living
> in the exterior square. 🟢

## 2. The primality projector and its soft version

To speak of the covariance of primality indicators one needs the indicator itself in
algebraic form.

> **Theorem 59.4** (`signed_card_sum`). For a finite set of "witness divisors" $P$, the
> signed sum $\sum_{S \subseteq P} (-1)^{|S|}$ equals $1$ when $P = \varnothing$ and $0$
> otherwise: inclusion–exclusion is the exact projector onto the event "no witnesses". 🟢

The hard projector does not deform; the route's reduction works with its **soft** version.

> **Definition 59.5** (soft projector). $Q_t(n) = t^{\,\Omega(n)-1}$ (Lean: `softProjector`)
> — a geometric weight in the number of prime factors with multiplicity: on primes
> $Q_t = 1$ for every $t$, on composites it decays in powers of $t$.

> **Theorem 59.6** (`softProjector_bounds`). For $0 \le t \le 1$ and $n \ge 2$, the soft
> projector sandwiches the primality indicator to within $t$:
>
> $$
> \mathbf{1}_{\mathbb P}(n) \;\le\; t^{\,\Omega(n)-1} \;\le\; \mathbf{1}_{\mathbb P}(n) + t. \tag{59.3}
> $$
>
> This is the engine of the reduction skeleton: the covariance of indicators can be replaced
> by the covariance of smooth multiplicative weights at a controlled cost $t$. 🟢

## 3. The factor box and anisotropy

The geometry of a number's divisor distribution is encoded by its "factor box"
$B_n = \prod_i [0, 1/q_i]$ over the factor list $q_i$.

> **Theorem 59.7** (`factorBox_volume`). $\prod_i q_i^{-1} = \bigl(\prod_i q_i\bigr)^{-1}$:
> the volume of the factor box of $n$ equals $1/n$ — volume does not see **how** the mass is
> split among factors, only their product. All information about the shape of the splitting
> sits in the box's anisotropy. 🟢

> **Theorem 59.8** (`anisotropy2_eq_cosh`). For a semiprime box with sides $p, q > 0$, the
> anisotropy $\alpha_2 = \frac{p+q}{2\sqrt{pq}}$ equals the hyperbolic cosine of half the
> logarithmic distance between the factors:
>
> $$
> \alpha_2(p,q) = \cosh\Bigl(\tfrac12 \log\tfrac{p}{q}\Bigr). \tag{59.4}
> $$
>
> Semiprimes are the route's "hyperbolic points": their shape is governed by a single
> hyperbolic angle. 🟢

## 4. The twin's Fourier shell

The local combinatorics between adjacent twins and its frequency image.

> **Theorem 59.9** (`twin_defect_law`). Between adjacent twin centers with gap $g$,
> $N = 2 + S$ prime-occupied centers and $E = (g-1) - S$ empty ones, the exact balance
> $E = g + 1 - N$ holds: the emptiness defect is rigidly tied to the gap. 🟢

> **Theorem 59.10** (`hodge_even_kills_odd_modes`). If the support is symmetric under an
> involution $i \mapsto \bar i$, the weight is even ($\rho_{\bar i} = \rho_i$) and the phase
> is odd ($X_{\bar i} = -X_i$), then $\sum_i \rho_i \sin(\xi X_i) = 0$: the even (under the
> Hodge reflection `hodge_reflection`) averaging kills **all** odd modes. The module's honest
> caveat: the surviving even modes $\prod\cos(\xi\log p/2)$ form a positive-type kernel with
> no mutual cancellation — this **sharpens** the target, it does not break the parity
> wall. 🟢

> **Theorem 59.11** (`logDivisor_fourier`). The centered log-divisor Fourier sum of a
> squarefree number factors into a product of per-prime cosines:
>
> $$
> \prod_{i\in P} \cos\Bigl(\frac{\xi\,\theta_i}{2}\Bigr)
>   = 2^{-|P|} \sum_{T \subseteq P}
>     \cos\Bigl(\frac{\xi}{2}\Bigl(2\sum_{i\in T}\theta_i - \sum_{i\in P}\theta_i\Bigr)\Bigr). \tag{59.5}
> $$
>
> The exact Fourier image of the "Rubik hypercube" of factorization choices. 🟢

## 5. The exact diagonal: $-1/p^2$ at every prime

The route's central computation. Let $D_-^{(p)}(k)$ and $D_+^{(p)}(k)$ be the wing
divisibility indicators: $p \mid 6k-1$ and $p \mid 6k+1$ (Lean: `Dminus`, `Dplus`).

> **Theorem 59.12** (`diag_energy_zero`). For $p \ge 5$ the product $D_-^{(p)} D_+^{(p)}$ is
> identically zero: one prime cannot divide both wings at once
> ($p \mid (6k+1)-(6k-1) = 2$ is impossible). The diagonal energy of every single prime
> vanishes. 🟢

> **Theorem 59.13** (`diag_cov_period_exact`). The marginals are exact:
> $\frac1p\sum_k D_\pm^{(p)}(k) = \frac1p$ (`wing_marginal_minus`, `wing_marginal_plus`),
> and hence the single-prime covariance **over the full period** equals exactly
>
> $$
> \operatorname{cov}_p\bigl(D_-^{(p)}, D_+^{(p)}\bigr) \;=\; -\,\frac{1}{p^2}. \tag{59.6}
> $$
>
> Every prime contributes a strictly negative, exactly computed amount. 🟢

The sum $\sum_p 1/p^2$ telescopes (`inv_sq_le_telescope`): the **diagonal** part of the twin
covariance is summable and fully under control. The entire content of the problem sits in
the **off-diagonal** part — correlations *between distinct* primes on *short* windows. That
is the parity wall: chapter [12](12_FourCorner.md) in four-corner form, chapter
[32](32_RankParityUnity.md) in rank form.

## 6. The honest reduction and where the routes meet

The route ends at a green-conditional summit: an exact statement of *which* input is
missing.

> **Definition 59.14** (geometric reduction). `ReductionHolds`: beyond every horizon $N$
> there is a finite window $I$, weights $w \ge 0$ with $\sum w = 1$, levels $c \in (0,1]$,
> $t \in [0,1]$ with $2t + t^2 < c^2/2$, such that both primality marginals on the window
> are $\ge c$ and the covariance defect of the soft projectors is $\le c^2/4$.

> **Theorem 59.15** (`twinCenter_of_window`). On a **finite** window, the conditions of
> Definition 59.14 force a twin inside the window: there is $m \in I$ with both $6m\pm1$
> prime. The proof is finite and unconditional — a window with good marginals and small
> covariance must contain a coincidence. 🟢

> **Theorem 59.16** (`twins_of_geometricMixingTarget`). If `GeometricMixingTarget`
> (= `ReductionHolds`) holds, twin centers are cofinal
> (via `twinCenters_cofinal_of_reduction`). The hypothesis is strictly stronger than the
> conclusion and does **not** assume the twin conjecture; a one-directional sufficiency —
> a green conditional theorem with a named hypothesis. 🟢

Where does this conditional summit meet the rest of the book?

> **Theorem 59.17** (`mixing_forces_fourCorner`). A strictly negative connected defect
> $N_{00}N_{33} < N_{03}N_{30}$ together with the side bound $N_{03}N_{30} \le N_{00}^2$
> forces $N_{33} < N_{00}$ — **exactly** the named open input of the combinatorial route
> (`N33_lt_N00_of_four_corner`, chapter [12](12_FourCorner.md)). Forward only: the converse
> implication is unproved and not claimed. 🟢

**Chapter summary.** The geometric route proved: covariance is a bilinear object with an
exact Segre decomposition (59.1–59.2); the soft projector sandwiches primality to within $t$
(59.3); the diagonal is computed exactly and is summable (59.6); the finite-window reduction
is unconditional (Theorem 59.15), while its cofinal version is honestly conditional
(Theorem 59.16). The route's wall — the off-diagonal short-window correlation — coincides
with the wall of every other route and is not renamed. The following chapters walk through
the assault on that wall: the systematic Type II map, the twin variety and short windows,
the dilation ladder, the Brun track, and the composite-modulus core.
