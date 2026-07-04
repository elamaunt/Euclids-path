# 51. Numerical evidence

<!--navtop-->
[← 50. Coda](50_Coda.md) · [Table of contents](00_Overview.md) · [52. Discrete model of a fluid →](52_DyadicModel.md)
<!--/navtop-->



> Data sources: `f:/Primes/twin_stats_21_27.csv`, `f:/Primes/twin_stats_28_detail.csv` (originals,
> never edited) and the harnesses `tools/*_harness.py` with protocols `tools/RESULTS_*.md`. This
> chapter has no Lean counterpart: it is **data**, not claims. The numbers are given here as a
> reference point and a stress test of the laws before formalisation — not as a proof.

## What we check, and why

The programme rests on a series of exact Diophantine laws (the carrier of two, the sign law, height
drop) and on one target balance inequality `B₅ = N₀₀ − N₃₃ > 0` (there are no fewer twins than
"double composites"). The formal proofs of these laws live in `Engine/*`; here we show that on real
data they hold — and *with what margin*.

All checks run in exact integer arithmetic and pointwise, on every block and node, not on average. A
law that holds on average is of no use to us: we need a law that is never violated even once.

The numerical evidence never crosses the red line (no probabilities, no distribution of primes). It
measures already-defined integer quantities rather than postulating their density.

## 1. The balance `N₀₀ − N₃₃` and four-corner (blocks `N = 2^k`)

Centres `6m±1` are classified by the pair of side ranks, coarsened to `{0,3}` (prime side /
richly composite side): `N₀₀` (twin), `N₃₃` (both richly composite), `N₀₃, N₃₀` (mixed). The target
is `B₅ = N₀₀ − N₃₃ > 0`; the four-corner ratio `R_fc = N₀₀N₃₃/(N₀₃N₃₀) < 1` encodes the negative
correlation of the side ranks.

| k | N₀₀ | N₃₃ | N₃₃/N₀₀ | R_fc = N₀₀N₃₃/(N₀₃N₃₀) | Γ/M |
|---:|---:|---:|---:|---:|---:|
| 21 | 59 382 | 745 | 0.0125 | 0.876 | 0.671 |
| 22 | 109 168 | 1 213 | 0.0111 | 0.918 | 0.675 |
| 23 | 202 492 | 2 816 | 0.0139 | 0.920 | 0.682 |
| 24 | 375 236 | 4 796 | 0.0128 | 0.976 | 0.682 |
| 25 | 698 496 | 9 596 | 0.0137 | 0.951 | 0.687 |
| 26 | 1 302 736 | 18 721 | 0.0144 | 0.962 | 0.688 |
| 27 | 2 435 911 | 33 386 | 0.0137 | 0.972 | 0.686 |
| 28 | 4 566 323 | 72 230 | 0.0158 | 0.977 | 0.695 |

(The columns `N₀₀,N₃₃,Γ/M` come from the `GLOBAL` rows of the CSV; `R_fc` from
`tools/RESULTS_fourcorner.md`, exact sieve, old-free version. `Γ = N₃₀ + 4N₃₃`, `M` is the mass
scale.)

What we see:

- **`B₅ = N₀₀ − N₃₃ > 0` with a wide margin.** `N₃₃` is only ~1.1–1.6 % of `N₀₀` and never comes
  close to it. The ratio is roughly stable rather than falling to zero (it is important not to
  confuse `N₃₃` with the neighbouring `N₃₁,N₃₂`). This is direct numerical support for
  [16. By contradiction](16_FiniteContradiction.md).
- **`R_fc < 1` on every block** (`0.876 → 0.977`). The four-corner negative association holds
  pointwise, exactly as required by [12. Four-corner](12_FourCorner.md), [14. Remainder decomposition](14_RealFourCorner.md).
- **`Γ/M ≈ 0.67 → 0.70`** — a stable structural constant (carrier dispersion of ~70 % of the mass).
  There is no "clock monopolist", consistent with the exclusivity forcing argument of
  [06. No way back](06_NoBackward.md).

> **Note (the parity wall is visible in the numbers).** `R_fc` **rises monotonically toward 1**
> with the block, i.e. the margin `1 − R_fc → 0⁺`. This is precisely the "margin-to-zero wall" of
> [16. By contradiction](16_FiniteContradiction.md): the inequality holds on all the data, yet its
> margin melts away, which is why the estimate must be uniform rather than per-block. This is
> exactly what makes the twin node a *distributional* one, kin to the estimate of `L(x)` in
> [32. Rank-parity node](32_RankParityUnity.md).

## 2. Where exactly the symmetry breaks (an exploratory margin estimate)

The exploratory harness `symmetry_break_harness.py` (this is not a proof step but a "what-if"
estimate) fits the margin series `1 − R_fc` at `κ = 4.0` with a power law:

$$1 - R_{\mathrm{fc}} \;\sim\; 12.12 \cdot A^{-1.161}.$$

The exponent `α = 1.161 > 0` means `margin → 0⁺` as `A → ∞`, but smoothly, without vanishing.

The harness's conclusion: **there is no finite size at which the symmetry suddenly breaks.** For the
twins to run out, the margin would have to jump off the smooth law and change sign — and nothing of
the kind is observed in the data. This is indirect support for the wall being a knife-edge rather
than a cliff (see [16. By contradiction](16_FiniteContradiction.md)).

## 3. Old-peel: three laws at 100 % (3000 real catches, `A = 200`)

The harness `oldpeel_harness.py` on **3000 real rank-1 catches** (`6n+ε = a` prime `> A`, `6n−ε`
composite, caught by a small `p ≤ A`, unfolding `6n−ε = p(6t+δ)`):

| law | result |
|---|---|
| sign law `δ = −π·ε` (`p ≡ π mod 6`) | **3000 / 3000 = 1.0000** |
| height drop `t < n/5` | **3000 / 3000 = 1.0000** |
| regeneration `t > 0` (the flow continues) | **3000 / 3000 = 1.0000** |

Both algebraic laws (`old_peel_sign`, `old_peel_height_drop`) and the closure core (infinite strict
descent ⟹ `False`) are proven in Lean ([19. Old-peel](19_OldPeel.md)). The numbers confirm that the
mechanism is real at every node checked, not hypothetical. The observed descent `t < n/5` is even
sharper than the proven soft bound `t < n`.

## 4. The clean graph and the global absorber (fan-in)

The numbers for the clean graph and the global absorber (`tools/RESULTS_clean_graph.md`, `tools/RESULTS_global_absorber.md`):

- **The "sink-is-clean" gap.** `178/300 = 59.3 %` of clean centres have all their active edges in
  the boundary. This is precisely the fact that the clean graph is not self-sufficient and requires
  boundary regeneration ([23. Clean graph](23_CleanGraph.md)): 59 % of the apparent "stops" are in
  fact boundary exits.
- **Fan-in is real.** A single absorber centre collects up to 570 lineages (`570/2000 = 28.5 %` of
  the endpoint shares); small centres (`≤ 50`) absorb the mass of the descent. This is the numerical
  form of the single remaining node `GlobalOldAbsorption` ([24. Boundary decomposition](24_BoundaryDecomp.md), [29. The last link](29_CarrierBridge.md)):
  the fan-in `570 → 1` exists, but turning it into an engine — a pigeonhole over the fibre
  (Hall capacity) — is exactly the irreducible gap.

> **Note.** The numbers here measure the open node itself, not its closure. They show that the
> absorber and the fan-in are not an artefact but a real structure; yet the reality of the fan-in is
> not the same as its reducibility to an engine. We record this honestly: the data confirm the
> *existence* of the wall to which the whole programme has been reduced, and say nothing about its
> *conquest*.

## 5. Rank is bounded and squeezed (product-core)

The harnesses `rank2_harness.py`, `cov_harness.py` (k=24, κ=4):

- **The rank range `1 ≤ r ≤ 4`.** On the legal layer the product of factors `> A` is pinched
  between `(A+1)⁵` and `6X_A+1 < A⁵`, which gives `r ≤ 4` (`factor_rank_le_four`,
  [28. MkNode](28_MkNode.md)); the data confirm this.
- **The singular spectrum of the rank-2 covariance:** `[764953, 733, 224, 98]`, `sv₂/sv₁ = 0.001` —
  rank 1 explains 99.9999 % of the energy. In other words, the structure of the centres is almost
  one-dimensional: a single clean mode dominates, and higher-rank corrections are negligible. This
  supports the cubic squeeze and the shortness of repeat trains
  ([07. The short train](07_Squeeze.md), [08. The bounded cycle](08_BK.md)).

## 6. The separating scale is reachable with exponential headroom

A numerical run (`tools/RESULTS_separating_scale.md`): the condition `P_A > 6X_A + 1` (with
`X_A ≈ A^{4.5}`) already holds for small `A` and only strengthens further, since
`log P_A ~ A/ln 10` (Chebyshev) outruns `4.5·log₁₀ A`:

| A | log₁₀ P_A | log₁₀(6·A^{4.5}) | `P_A > 6X_A`? |
|---:|---:|---:|:---:|
| 50 | 17.0 | 8.4 | ✓ |
| 200 | 81.1 | 11.1 | ✓ |
| 1000 | 414.5 | 14.3 | ✓ |

This is the numerical evidence beneath `legal_lift_lt_primorial` / `no_productHall`
([26. Separating scale](26_SeparatingScale.md)): on the legal domain `a < P_A`, so the coarsened
passport `a mod P_A` is already exact and injective — the node `ProductHall` is closed
constructively, without `Classical.choice`.

## 7. The Riemann branch: where the numbers are, and where only theory so far

The identity `λ(n) = (−1)^{Ω(n)} = (−1)^{rank(n)}` and the flip `λ(p·m) = −λ(m)` are proven in Lean
([31. Riemann via Liouville](31_RiemannLiouville.md)) — this is not empirics but a consequence of
`liouville_apply`/`cardFactors_mul` from mathlib.

The estimate `|L(x)| = O(√x · x^ε)` (`LiouvilleBound`) remains an arithmetic input. We have no
separate numerical harness for `L(x)/√x` yet, and we do not hide this.

The only numerical support for the Riemann branch at present is indirect. `L(x)` is the rank-parity
imbalance — the same object as `N₀₀−N₃₃` in §1 — and §1 shows that the balance of ranks holds with a
margin (see [32. Rank-parity node](32_RankParityUnity.md)).

## What matters

Numerical stability **does not close** any of the open nodes. Both the target twin balance
([16. By contradiction](16_FiniteContradiction.md), §1) and the estimate of `L(x)`
([31. Riemann via Liouville](31_RiemannLiouville.md), §7) are needed uniformly and asymptotically,
not at specific `k ≤ 28` / `A ≤ 1000`.

The data are consistent with the hypothesis and confirm that the mechanisms (old-peel, fan-in,
rank ≤ 4, separating scale) are real; but confirmation on a finite segment is a reference point, not
a conclusion. The single irreducible node — `GlobalOldAbsorption` (§4) — is made *visible* by the
data, but not *closed*.

<!--navbot-->

---

[← 50. Coda](50_Coda.md) · [Table of contents](00_Overview.md) · [52. Discrete model of a fluid →](52_DyadicModel.md)
<!--/navbot-->
