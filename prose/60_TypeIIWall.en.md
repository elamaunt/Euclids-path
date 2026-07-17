# 60. The Type II wall up close: the local spectrum, the S₂/S₄ threshold, and the named targets

<!--navtop-->
[← 59. The geometric route](59_GeometricRoute.md) · [Contents](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricTypeIINoGo.lean` (`mixed_mode_parity_scale`, `zEnergy_is_gain`),
> `Engine/GeometricTypeIIProjection.lean` (`two_row_cov`, `two_row_summability`,
> `Zrow_mean_zero`), `Engine/GeometricTypeIIGram.lean` (`gram_diag`, `gram_off`,
> `zero_sum_isometry`), `Engine/GeometricTypeIISpectrum.lean` (`survivorOp_const`,
> `survivorOp_meanzero`, `centeredSurvivorOp_meanzero`, `zEnergy_eq_schatten`),
> `Engine/GeometricTypeIIQuartic.lean` (`zEnergy_S4`, `pythagoras_of_orthogonal`),
> `Engine/GeometricTypeIIChaos.lean` (`schatten_S2_lower`, `schatten_S4_bounded`),
> `Engine/GeometricTypeIIFixedPoint.lean` (`one_defect_fixed_point`),
> `Engine/GeometricTypeIIForest.lean` (`forest_telescope`, `local_rigidity`),
> `Engine/GeometricTypeIIMap.lean` (`CRE`, `twins_of_typeII`),
> `Engine/GeometricTypeIILiouville.lean` (`OneWingTarget`, `twins_of_oneWing`),
> `Engine/GeometricTypeIIRoots.lean` (`LowFreqRootCoherence`, `root_S4_bounded`),
> `Engine/GeometricTypeIIWallMap.lean` (`SemiprimeShortRestriction`,
> `HigherConductorDispersion`, `twins_of_final_package`),
> `Engine/GeometricTypeIIBilinear.lean` (`bilinear_block_bound`),
> `Engine/GeometricTypeIIWindow.lean` (`twin_sieve_window_identity`),
> `Engine/GeometricTypeIICompletion.lean` (`interval_completion`, `interval_parseval`),
> `Engine/GeometricTypeIIIncomplete.lean` (`incomplete_kloos_bound`).

Chapter [59](59_GeometricRoute.md) ended at the off-diagonal short-window correlation. The
Type II line is a systematic **study of the wall**: the exact local spectrum of the
residual, machine-checked verdicts on what *is* a gain versus what is mere renaming, and
the named open targets to which everything else reduces. The house rule: only an event
under one of three criteria (§110) counts as progress — **A** (annihilation), **B**
(summability gain), **C** (dimension reduction); everything else is cartography. The
anti-renaming gate — the machine predicate `zEnergy_is_gain` — is part of this line.

## 1. The wall in local form

> **Theorem 60.1** (`mixed_mode_parity_scale`). The local energy of the quadratic ($S_2$)
> residual at a prime $p$ is bounded below: $\tfrac{1}{2p} \le$ `zEnergy` $1\,p$. The sum
> $\sum_p 1/p$ diverges: the quadratic level is **parity-divergent** — the exact local form
> of the wall. 🟢

## 2. The exact local spectrum

The single-prime residual is not a small object but one with an exactly computed spectrum.

> **Theorem 60.2** (`two_row_cov`). The covariance of two distinct rows of the wing
> indicator equals exactly $-1/p^2$; in the surviving normalization, $-1/(p-1)^2$
> (`two_row_cov_survival`), and that series is summable (`two_row_summability`). The pure
> nonprincipal residual has zero full mean (`Zrow_mean_zero`) — exact annihilation over the
> full CRT period, criterion A. 🟢

> **Theorem 60.3** (`zero_sum_isometry`). The Gram matrix of the residuals is exact: the
> diagonal is $p(p-2)/(p-1)^3$ (`gram_diag`), the off-diagonal $-p/(p-1)^3$ (`gram_off`);
> on the subspace $\sum c_a = 0$,
>
> $$
> \Bigl\|\sum_a c_a Z_a\Bigr\|^2 \;=\; \frac{p}{(p-1)^2} \sum_a c_a^2. \tag{60.1}
> $$
>
> The local parity component is an **isometry with weight $p/(p-1)^2$**, not a small
> perturbation. 🟢

> **Theorem 60.4** (`zEnergy_eq_schatten`). The survivor-operator spectrum: $T_p$ has
> eigenvalue $(q-1)/q$ on constants (`survivorOp_const`) and $-1/q$ on mean-zero
> (`survivorOp_meanzero`); the centered version carries the parity eigenvalue $-1/(q-1)$
> (`centeredSurvivorOp_meanzero`). The `zEnergy` functionals are exactly the Schatten
> $2k$-energies $\operatorname{Tr}|Z|^{2k}$. 🟢

## 3. The threshold between S₂ and S₄

> **Theorem 60.5** (`zEnergy_S4`, `schatten_S2_lower`, `schatten_S4_bounded`). The fourth
> moment delivers the $1/p \to 1/p^3$ transition: `zEnergy` $2\,p \le 1/(p-1)^3$ —
> criterion B, a machine-checked summability gain (`zEnergy_is_gain`). At the level of the
> chaos decomposition:
>
> $$
> 1 + \sum_{p} \frac{1}{p-2} \;\le\; \prod_p \Bigl(1 + \frac{1}{p-2}\Bigr)
> \qquad\text{(diverges)}, \qquad
> \prod_p \Bigl(1 + \frac{1}{(p-2)^3}\Bigr) \;\le\; e^{1/2}
> \quad\text{(uniformly bounded)}. \tag{60.2}
> $$
>
> The quadratic level sits on the parity boundary; the quartic has a summable budget. The
> root variant is bounded the same way: $\prod_p(1 + 6/p^3) \le e^6$
> (`root_S4_bounded`). 🟢

The orthogonal support structure makes the budget additive: families with pairwise disjoint
supports obey the "Pythagorean" law $\sum(\sum_i f_i)^2 = \sum\sum_i f_i^2$
(`pythagoras_of_orthogonal`).

## 4. The fixed point: why higher moments alone do not break through

> **Theorem 60.6** (`one_defect_fixed_point`). The one-defect sector reproduces the parity
> eigenvalue at **every** even moment:
>
> $$
> \sum_\chi \lambda(\chi)^{2k-1}\,\lambda(\chi\theta)
>   \;=\; -\frac{1}{m}\sum_\chi |\lambda(\chi)|^{2k}. \tag{60.3}
> $$
>
> Raising the moment $S_4, S_6, S_8,\dots$ alone does not destroy the sign: the wall
> reproduces itself at all levels. 🟢

The forest recursion (`forest_telescope`) telescopes the main term exactly, and the
rigidity statement (`local_rigidity`) shows the unique normalized hard annihilator is
$(p-1)/(p-2)$: there is no freedom of choice.

## 5. The named targets: exactly where it is open

All routes of this line converge onto a finite list of named `Prop`s — open, with no
`sorry` and no axioms. This is the map of the wall.

> **Definition 60.7** (cross-modulus energy). `CRE`: the residual energy $\mathfrak{E}$
> satisfies $\mathfrak{E}(x) \ll_B x^2 (\log x)^{-B}$ for every $B$. The single unproven
> analytic input of the bundled Type-II program. 🔴

> **Definition 60.8** (one-wing target). `OneWingTarget`: beyond every horizon there is a
> window whose twin count takes the semiprime-corner form $A - B_- - B_+ + C$ with
> $C \ge 0$ and jointly negative Liouville wing bias $L_- + L_+ < 0$. 🔴

The remaining three faces are CRE-shaped residuals: **C** — `SemiprimeShortRestriction`
(the short restriction of the semiprime conductor), **D** — `HigherConductorDispersion`
(multilinear dispersion of conductors with $\omega(c) \ge 3$), **E** —
`LowFreqRootCoherence` (low-frequency coherence of CRT roots across incommensurable
moduli). All 🔴; all are forms of the same question about the signs of $\mu$ on short
windows.

> **Theorem 60.9** (`twins_of_typeII`). The bundled Type-II program — `CRE` together with
> the named Ford–Maynard chain — implies cofinality of twin centers. One-directional; the
> hypothesis is strictly stronger than the conclusion. 🟢

> **Theorem 60.10** (`twins_of_oneWing`, `twins_of_final_package`). Closing
> `OneWingTarget` yields twins — the second explicit route, parallel to CRE; the final
> package assembles it with no hidden bridges. Both are green conditional theorems with
> named hypotheses. 🟢

## 6. The ambient assault and the first unconditional sub-period

The assault on the wall's center was executed in its formalizable part — **ambient
throughout**, with the honest refrain: ambient S₄ does not transfer to the short
rectangle.

> **Theorem 60.11** (`bilinear_block_bound`). The two-variable Type-II block for
> $7 \le p$, $p \le R$, $p \le L$ is bounded: $|B_p| \le 3RL/(p-1)$ — and the relative
> gain $(B/RL)^2 \le 9/(p-1)^2$ telescopes: criterion B at the bilinear level. The period
> hypotheses are load-bearing: special coefficients are easy even without them
> (`bilinear_v_one_elementary` in `GeometricTypeIISpecial.lean` — the warning that guards
> the wall). 🟢

> **Theorem 60.12** (`twin_sieve_window_identity`). The literal wall formula: the twin
> count of a critical-range window equals the exact alternating Möbius–CRT double sum
> $\sum_{S,T}(-1)^{|S|+|T|}N_{S,T}$ with real strike counts. 🟢

> **Theorem 60.13** (`interval_completion`, `interval_parseval`). The completion apparatus
> is exact at every modulus: the short sum $= \frac1q\sum_h W_M(h)\,\widehat F(h)$ for all
> $M$; and $\sum_h \|W_M(h)\|^2 = qM$ exactly for $M \le q$. 🟢

> **Theorem 60.14** (`incomplete_kloos_bound`). The first unconditional sub-period gain:
> for $a \ne 0$,
>
> $$
> \Bigl\|\sum_{m < M} \psi\bigl(a\,m^{-1} + b\,m\bigr)\Bigr\|
>   \;\le\; 2^{1/4} p^{3/4}\Bigl(\frac{M}{p} + 1 + \log p\Bigr), \tag{60.4}
> $$
>
> nontrivial for $M \gg p^{3/4}\log p$. The exponent $3/4$ is fourth-moment strength
> (`kloos_norm_le`), not full Weil $1/2$ — and is declared as such. 🟢

**Chapter summary.** The local spectrum of the residual is computed exactly (60.1–60.4);
the fourth moment is machine-certified as a genuine gain (criterion B) while the quadratic
level is the parity boundary (60.2, 60.5); the fixed point explains why higher moments
alone do not break through (60.3); the open content is collected into five named 🔴
targets (CRE, `OneWingTarget`, C/D/E), and every conditional route to twins is stated
one-directionally. The wall is not renamed — it is named.
