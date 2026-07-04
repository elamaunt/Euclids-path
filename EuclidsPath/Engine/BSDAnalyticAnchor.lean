/-
  BSDAnalyticAnchor — the CONTENTFUL gate of the BSD analytic rank:
  a data anchor of the analytic continuation of the L-series + the GENUINE
  mathlib order of zero.

  ┌─────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER. WHAT IS RED, WHAT IS GREEN, AND WHERE THE CONTRAST.  │
  └─────────────────────────────────────────────────────────────────────────┘

  BACKGROUND. The old gate `AnalyticRank` (BSDFront §3) is a citation marker:
  it merely references the real `WeierstrassCurve.LSeries` and is FREELY
  SATISFIABLE at any rank (`analyticRank_gate_satisfiable`, BSDEpistemic §2),
  so that `WeakBSD` provably reduces to a bare equality
  (`weakBSD_reduces_to_bare_equality`). This module builds a CONTENTFUL
  replacement: the analytic rank = the genuine mathlib order of zero
  `analyticOrderAt`
  (`Mathlib/Analysis/Analytic/Order.lean`, `analyticOrderAt f z₀ : ℕ∞`)
  of the continuation function at the point `s = 1`.

  🔴 RED DATA ANCHOR (named, derived from nowhere):
   · `ContinuedLFunction W` — the DATA of the analytic continuation of the
     curve's L-series: a function `Lambda : ℂ → ℂ` that agrees with
     `WeierstrassCurve.LSeries W` everywhere the Dirichlet series is absolutely
     summable (`agreement`, via `LSeriesSummable`), and is analytic at `s = 1`
     (`analyticAtOne`).

  🟢 GREEN (machine, std triple of axioms):
   · `dirichletCoeffs_def` / `weierstrassLSeries_eq_LSeries_coeffs` —
     rfl citation audits: the coefficients and the series are EXACTLY the
     mathlib objects `WeierstrassCurve.LFunction` / `WeierstrassCurve.LSeries`,
     with no substitution;
   · `analyticRankOf L = analyticOrderAt L.Lambda 1` — the CONTENTFUL rank:
     the order of zero is a genuine mathlib notion, not a free parameter;
   · `weakBSDContentful_iff_analyticOrderAt` — a renaming audit: the new gate
     is UNFOLDED machine-wise into an equality of mathlib orders (`Iff.rfl`);
   · `contentfulGate_pins_rank` / `contentfulGate_not_free_at_two_ranks` —
     the new gate holds at NO MORE than one rank for a given anchor;
   · `oldGate_free_at_every_rank` + `gate_contrast` — the CONTRAST machine-wise:
     the old gate is satisfiable for free at ALL ranks at once (reuse of
     `analyticRank_gate_satisfiable`), the new one requires DATA and pins the
     rank;
   · `analytic_order_realizes_every_rank` — non-vacuity of the NOTION of rank
     ITSELF: for each n there is a function analytic at 1 with order exactly n
     (centered monomial, `analyticOrderAt_centeredMonomial`);
   · `skeletonOfNowhereSummable` + `analyticRankOf_skeleton` — non-vacuity of
     the data TYPE: a skeleton with `Lambda = const 1` (order 0), HONESTLY
     labelled "skeleton, NOT a genuine L" and conditional on the nowhere-
     summability of the series.

  WHAT MATHEMATICS MUST SUPPLY FOR A GENUINE ANCHOR (and what is NOT in mathlib
  v4.31, neither as a theorem nor as a `proof_wanted`):
   1. Analytic continuation of `WeierstrassCurve.LSeries W` to `s = 1`. For
      K = ℚ this is modularity (Wiles–Taylor 1995, BCDT 2001) + continuation
      of the L-functions of modular forms. mathlib gives analyticity of
      L-series ONLY in the open half-plane of absolute convergence:
      `LSeries_analyticOnNhd f : AnalyticOnNhd ℂ (LSeries f)
        {s | LSeries.abscissaOfAbsConv f < s.re}` — and the point 1 does not
      land in it by any cheap means (see item 2).
   2. Coefficient estimates for `WeierstrassCurve.LFunction` (the Hasse bound
      `|aₚ| ≤ 2√p` — absent in mathlib), giving
      `LSeries.abscissaOfAbsConv (dirichletCoeffs W) ≤ 3/2`. IMPORTANT: even
      with Hasse `re 1 = 1 < 3/2`, i.e. `s = 1` lies STRICTLY OUTSIDE the
      half-plane of absolute convergence — the continuation is genuinely
      necessary, convergence cannot replace it. The anchor is not "laziness"
      but an honest junction point.

  HONESTY. We assert NOTHING about the genuine L-function: neither the
  existence of the continuation nor the value of the order. `ContinuedLFunction`
  is a named input for external data; the skeleton is a degenerate inhabitant
  of the type under the counterfactual (for genuine curves) assumption of
  nowhere-summability, which mathlib v4.31 can neither prove nor refute (no
  coefficient estimates, neither from above nor from below). THIS IS NOT A
  SOLUTION OF BSD AND NOT GÖDEL. If external mathematics supplies a genuine
  anchor `L`, the gate `WeakBSDContentful L r` becomes the contentful equality
  "algebraic rank = order of zero of the continuation at 1".

  No `sorry`, no `admit`, no `native_decide`, no new axiom; the quarantine
  (CausalClosureAxiom) is NOT imported. The green load-bearing declarations use
  the standard triple `propext` / `Classical.choice` / `Quot.sound`. The
  repository's toll (taint 47) is NOT changed by this file.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BSDAnalyticAnchor.lean
    → zero errors.

  Kinship: EuclidsPath/Engine/BSDFront.lean (`AnalyticRank`, `WeakBSD`);
    EuclidsPath/Engine/BSDEpistemic.lean (`analyticRank_gate_satisfiable`,
    `weakBSD_reduces_to_bare_equality`); mirror of the renaming audit:
    EuclidsPath/Engine/BoundedGapsAnchor.lean (`boundedGaps_two_iff_twins`).
-/
import Mathlib
import EuclidsPath.Engine.BSDFront
import EuclidsPath.Engine.BSDEpistemic

set_option autoImplicit false

namespace EuclidsPath.BSDFront.AnalyticAnchor

variable {K : Type*} [Field K] [NumberField K]

/-! ### 🟢 Named citation of the coefficients (rfl audits) -/

/-- **🟢 The curve's Dirichlet-series coefficients — a named citation.**
    EXACTLY `(↑) ∘ W.LFunction` from the mathlib definition
    `WeierstrassCurve.LSeries` (rfl audit `dirichletCoeffs_def`). A separate name
    serves two purposes: an honest citation point AND a def-barrier for the
    unifier — the raw `(↑) ∘ W.LFunction` in repeated signatures blows up
    `isDefEq` (beneath the coefficients lies a gigantic Euler product over
    `HeightOneSpectrum (𝓞 K)` with adic completions). -/
noncomputable def dirichletCoeffs (W : WeierstrassCurve K) : ℕ → ℂ :=
  (↑) ∘ W.LFunction

/-- **🟢 rfl citation audit (proved):** `dirichletCoeffs` is literally the
    coefficients from mathlib, with no substitution. -/
theorem dirichletCoeffs_def (W : WeierstrassCurve K) :
    dirichletCoeffs W = (↑) ∘ W.LFunction :=
  rfl

/-- **🟢 rfl series audit (proved):** the real `WeierstrassCurve.LSeries W` is
    `LSeries (dirichletCoeffs W)`, by the mathlib definition. -/
theorem weierstrassLSeries_eq_LSeries_coeffs (W : WeierstrassCurve K) (s : ℂ) :
    WeierstrassCurve.LSeries W s = LSeries (dirichletCoeffs W) s :=
  rfl

/-! ### 🔴 Red data anchor: the data of the analytic continuation -/

/-- **🔴 RED DATA ANCHOR — the data of the L-series analytic continuation.**

    Fields: `Lambda` — the candidate continuation; `agreement` — agreement with
    the real `WeierstrassCurve.LSeries W` everywhere the Dirichlet series is
    absolutely summable (stated via `LSeriesSummable (dirichletCoeffs W) s` —
    exactly the region where the mathlib value of `LSeries` is the honest sum of
    the series, not the junk value `0` from `tsum`); `analyticAtOne` —
    analyticity at `s = 1`.

    WHAT IS NOT IN MATHLIB v4.31 (which is why this is data, not a theorem): the
    continuation of `WeierstrassCurve.LSeries` beyond the half-plane of absolute
    convergence (mathlib gives only `LSeries_analyticOnNhd` INSIDE the half-plane
    `LSeries.abscissaOfAbsConv f < s.re`); modularity; the functional equation;
    even the Hasse bound `|aₚ| ≤ 2√p` for the coefficients
    `WeierstrassCurve.LFunction`. And even with Hasse `s = 1` lies OUTSIDE the
    half-plane (`1 < 3/2`) — the continuation is genuinely necessary.

    We do NOT claim that such data exists — we only NAME the input. -/
structure ContinuedLFunction (W : WeierstrassCurve K) where
  /-- The candidate continuation of the curve's L-series. -/
  Lambda : ℂ → ℂ
  /-- Agreement with the REAL `WeierstrassCurve.LSeries W` on the region of
      absolute summability of the Dirichlet series. Unfolding: `LSeriesSummable
      f s` = `Summable (LSeries.term f s)` — where the series is defined as an
      honest sum; outside this region `LSeries` returns junk `0`, and we
      honestly do NOT require agreement. -/
  agreement : ∀ s : ℂ, LSeriesSummable (dirichletCoeffs W) s →
    Lambda s = WeierstrassCurve.LSeries W s
  /-- Analyticity of the continuation at `s = 1` — what mathlib does NOT give for
      any curve (neither the continuation nor `1` landing in the half-plane of
      convergence). It is precisely this field that makes the anchor DATA. -/
  analyticAtOne : AnalyticAt ℂ Lambda 1

/-- **🟢 Plumbing (proved):** the `agreement` field is consumable — given any
    witness of summability of the series at a point `s`, the anchor's data must
    coincide with the real mathlib sum `WeierstrassCurve.LSeries W s`. -/
theorem lambda_agrees_on_summable {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) {s : ℂ}
    (hs : LSeriesSummable (dirichletCoeffs W) s) :
    L.Lambda s = WeierstrassCurve.LSeries W s :=
  L.agreement s hs

/-! ### 🟢 Contentful analytic rank: the genuine mathlib order of zero -/

/-- **🟢 The CONTENTFUL analytic rank of a given anchor:** the order of zero
    `analyticOrderAt L.Lambda 1 : ℕ∞` — a GENUINE mathlib notion
    (`Mathlib/Analysis/Analytic/Order.lean`): `⊤` if `Lambda` is locally
    identically zero at `1`, otherwise the unique `n` with a local expansion
    `Lambda z = (z − 1) ^ n • g z`, with `g` analytic and `g 1 ≠ 0`
    (`AnalyticAt.analyticOrderAt_eq_natCast`). Unlike the old gate
    `AnalyticRank` (a free parameter `aRank`), this number is COMPUTED from the
    anchor's data, not postulated. -/
noncomputable def analyticRankOf {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) : ℕ∞ :=
  analyticOrderAt L.Lambda 1

/-- **🟢 Non-vacuity of the NOTION of rank (proved):** the mathlib order of zero
    at `1` realizes EVERY `n : ℕ` — the witness `(· − 1) ^ n`, analytic at `1`,
    with order exactly `n` (`analyticOrderAt_centeredMonomial`). The notion
    distinguishes all ranks — in maximal contrast to the old gate, free at all
    ranks at once. -/
theorem analytic_order_realizes_every_rank (n : ℕ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 1 ∧ analyticOrderAt f 1 = (n : ℕ∞) :=
  ⟨(· - 1) ^ n, by fun_prop, analyticOrderAt_centeredMonomial⟩

/-! ### 🟢 Non-vacuity of the data TYPE: a skeleton inhabitant (NOT a genuine L) -/

/-- **🟢 The order of the constant `1` at the point `1` equals zero (proved):**
    the constant does not vanish, `analyticOrderAt_eq_zero` yields `0` for free.
    A brick of the skeleton. -/
theorem analyticOrderAt_const_one_at_one :
    analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 1 = 0 :=
  analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)

/-- **⚠️ SKELETON, NOT A GENUINE L (honest label).** An inhabitant of the type
    `ContinuedLFunction W` with `Lambda = const 1` UNDER THE CONDITION that the
    curve's Dirichlet series is nowhere summable: then `agreement` is vacuously
    true, and analyticity of the constant is free (`analyticAt_const`).

    DOUBLE HONESTY: (1) this is NOT data about the genuine L-function — the
    constant continues nothing; (2) the assumption `h` for genuine elliptic
    curves is COUNTERFACTUAL (by Hasse the series converges for `re s > 3/2`),
    but mathlib v4.31 can neither prove nor refute it — there are NO estimates
    for the coefficients `WeierstrassCurve.LFunction`. The skeleton exists only
    to witness machine-wise: the data TYPE is nonempty, the constructor is
    consumable, and even a degenerate inhabitant pins the rank
    (`analyticRankOf_skeleton`). Honest `agreement` has NO unconditional
    inhabitant — and this is not a defect but the very CONTENT of the gate: it
    requires data. -/
noncomputable def skeletonOfNowhereSummable (W : WeierstrassCurve K)
    (h : ∀ s : ℂ, ¬ LSeriesSummable (dirichletCoeffs W) s) :
    ContinuedLFunction W where
  Lambda := fun _ => 1
  agreement := fun s hs => absurd hs (h s)
  analyticAtOne := analyticAt_const

/-- **🟢 The skeleton's rank equals zero (proved):** even a degenerate
    inhabitant is consumed contentfully — `analyticOrderAt (const 1) 1 = 0`, no
    freedom of rank choice (cf. the old gate, free at ANY rank). -/
theorem analyticRankOf_skeleton (W : WeierstrassCurve K)
    (h : ∀ s : ℂ, ¬ LSeriesSummable (dirichletCoeffs W) s) :
    analyticRankOf (skeletonOfNowhereSummable W h) = 0 := by
  show analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 1 = 0
  exact analyticOrderAt_const_one_at_one

/-! ### 🔴→🟢 The contentful gate WeakBSDContentful and the contrast audit -/

/-- **The CONTENTFUL gate of weak BSD at a given anchor:** the algebraic rank
    `algRank` equals the order of zero of the continuation at `1`. Unlike the old
    `WeakBSD` (BSDFront §3), where the analytic conjunct is freely satisfiable
    and everything reduces to a bare equality of two free ℕ parameters
    (`weakBSD_reduces_to_bare_equality`), here the right-hand side is COMPUTED
    from the data `L` by the genuine mathlib notion `analyticOrderAt`. The
    predicate is honestly OPEN: we neither prove nor refute it for any genuine
    anchor (there are no genuine anchors in mathlib — see `ContinuedLFunction`).
    -/
def WeakBSDContentful {W : WeierstrassCurve K} (L : ContinuedLFunction W)
    (algRank : ℕ) : Prop :=
  analyticRankOf L = algRank

/-- **🟢 GOAL-RENAMING AUDIT (proved; mirror of
    `offCriticalBridge_iff_RH` / `boundedGaps_two_iff_twins`):** the new gate is
    machine-wise UNFOLDED (`Iff.rfl`) into the equality `analyticOrderAt
    L.Lambda 1 = algRank` — a pure mathlib statement about the order of zero,
    WITHOUT mentioning BSD. The gate does not hide the goal under a new name: to
    accept it is to accept exactly this equality of orders, no more and no less.
    -/
theorem weakBSDContentful_iff_analyticOrderAt {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) (algRank : ℕ) :
    WeakBSDContentful L algRank ↔ analyticOrderAt L.Lambda 1 = (algRank : ℕ∞) :=
  Iff.rfl

/-- **🟢 The new gate PINS the rank (proved):** on a single anchor `L` the gate
    holds at no more than one rank — `analyticOrderAt` is a function of the data,
    and injectivity of the cast ℕ → ℕ∞ finishes the job. Cf. the old gate:
    satisfiable at all ranks AT ONCE (`oldGate_free_at_every_rank`). -/
theorem contentfulGate_pins_rank {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) {r₁ r₂ : ℕ}
    (h₁ : WeakBSDContentful L r₁) (h₂ : WeakBSDContentful L r₂) :
    r₁ = r₂ := by
  have e₁ : analyticRankOf L = (r₁ : ℕ∞) := h₁
  have e₂ : analyticRankOf L = (r₂ : ℕ∞) := h₂
  exact_mod_cast e₁.symm.trans e₂

/-- **🟢 The new gate is NOT free (proved):** no anchor admits two different
    ranks — concretely, `0` and `1` are impossible simultaneously. A contrast
    with the old gate, where `AnalyticRank W 0 ∧ AnalyticRank W 1` is provable
    for free (see `gate_contrast`). -/
theorem contentfulGate_not_free_at_two_ranks {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) :
    ¬ (WeakBSDContentful L 0 ∧ WeakBSDContentful L 1) :=
  fun ⟨h0, h1⟩ => zero_ne_one (contentfulGate_pins_rank L h0 h1)

/-- **🟢 The old gate is satisfiable for free (reuse, proved):** a direct
    citation of `analyticRank_gate_satisfiable` (BSDEpistemic §2) —
    `AnalyticRank W aRank` holds at ANY `aRank` without any data. This is the
    honesty lemma of the old layer; here it is needed as one leg of the machine
    contrast. -/
theorem oldGate_free_at_every_rank (W : WeierstrassCurve K) (aRank : ℕ) :
    AnalyticRank W aRank :=
  Epistemic.analyticRank_gate_satisfiable W aRank

/-- **🟢 MACHINE CONTRAST OLD/NEW (proved, one theorem):** the old gate holds at
    ALL ranks simultaneously (free satisfiability, reuse of
    `analyticRank_gate_satisfiable`), the new one — at no more than ONE rank per
    anchor. "The old is satisfiable for free, the new requires data and pins the
    rank" — not a comment, but a conjunction of two proved legs. -/
theorem gate_contrast (W : WeierstrassCurve K) :
    (∀ r : ℕ, AnalyticRank W r) ∧
      ∀ L : ContinuedLFunction W, ∀ r₁ r₂ : ℕ,
        WeakBSDContentful L r₁ → WeakBSDContentful L r₂ → r₁ = r₂ :=
  ⟨fun r => Epistemic.analyticRank_gate_satisfiable W r,
   fun L _ _ h₁ h₂ => contentfulGate_pins_rank L h₁ h₂⟩

/-- **🟢 The old front closes under the anchor — but PAID FOR BY THE FREEDOM OF
    THE OLD GATE (proved, with an honest label):** from `WeakBSDContentful L
    algRank` follows `WeakBSD W algRank algRank`. THE HONESTY IS MACHINE-VISIBLE:
    the hypothesis `_h` in the proof is NOT CONSUMED (an underscored variable) —
    the old front closes for free for any diagonal pair, since its analytic
    conjunct is free (`analyticRank_gate_satisfiable`). There is NO transfer of
    content from the new gate to the old; the arrow exists only as an audit of
    the degeneracy of the old layer. -/
theorem weakBSD_of_contentful {W : WeierstrassCurve K}
    (L : ContinuedLFunction W) (algRank : ℕ)
    (_h : WeakBSDContentful L algRank) :
    WeakBSD W algRank algRank :=
  ⟨Epistemic.analyticRank_gate_satisfiable W algRank, rfl⟩

/-- **🟢 The skeleton pins rank 0 (proved, conditional on the skeleton
    assumption):** the degenerate inhabitant passes the new gate ONLY at
    `algRank = 0` — even it gives no freedom of choice. NOT a statement about the
    genuine L: the constant `1` continues nothing, and the nowhere-summability
    assumption is counterfactual for genuine curves (see
    `skeletonOfNowhereSummable`). -/
theorem skeleton_contentful_zero (W : WeierstrassCurve K)
    (h : ∀ s : ℂ, ¬ LSeriesSummable (dirichletCoeffs W) s) :
    WeakBSDContentful (skeletonOfNowhereSummable W h) 0 := by
  show analyticRankOf (skeletonOfNowhereSummable W h) = ((0 : ℕ) : ℕ∞)
  simpa using analyticRankOf_skeleton W h

/-! ################################################################################
    SUMMARY (LOUD HONEST)
    ################################################################################

  🔴 RED DATA ANCHOR: `ContinuedLFunction W` — the data of the continuation
     (`Lambda`, `agreement` on the region `LSeriesSummable`, `analyticAtOne`).
     In mathlib v4.31 there is no such data for any curve: no continuation of
     `WeierstrassCurve.LSeries` beyond the half-plane `abscissaOfAbsConv < re s`
     (only `LSeries_analyticOnNhd` inside it), no modularity, no functional
     equation, no Hasse bound; and even with Hasse `s = 1` lies outside the
     half-plane — the continuation is genuinely necessary.

  🟢 MACHINE-WISE, IN THIS FILE:
     · `dirichletCoeffs_def`, `weierstrassLSeries_eq_LSeries_coeffs` —
       rfl audits: EXACTLY the mathlib objects are cited, with no substitution;
     · `analyticRankOf` — the contentful rank: mathlib `analyticOrderAt` at `1`;
     · `weakBSDContentful_iff_analyticOrderAt` — an audit: the gate = a pure
       equality of orders, `Iff.rfl`, WITHOUT hidden goal renaming;
     · `contentfulGate_pins_rank`, `contentfulGate_not_free_at_two_ranks`,
       `gate_contrast` — the new gate requires data and pins the rank;
       the old one (`oldGate_free_at_every_rank`, reuse of
       `analyticRank_gate_satisfiable`) is satisfiable for free at all ranks;
     · `analytic_order_realizes_every_rank` — the notion of order realizes
       every n (centered monomial);
     · `skeletonOfNowhereSummable`, `analyticRankOf_skeleton`,
       `skeleton_contentful_zero` — the data type is nonempty (a skeleton, NOT a
       genuine L, conditional on counterfactual nowhere-summability), and even
       the skeleton is pinned to rank 0;
     · `weakBSD_of_contentful` — the old front closes under the anchor, but is
       paid for by the freedom of the old gate (the hypothesis is not consumed —
       visible to the machine).

  🟢 REUSED (cited, NOT re-derived):
     `AnalyticRank`, `WeakBSD` (BSDFront); `analyticRank_gate_satisfiable`
     (BSDEpistemic); mathlib: `analyticOrderAt`, `analyticOrderAt_eq_zero`,
     `analyticOrderAt_centeredMonomial`, `analyticAt_const`, `LSeriesSummable`,
     `WeierstrassCurve.LFunction` / `WeierstrassCurve.LSeries`.

  🔴 HONESTLY OPEN (and NOT touched): the existence of the genuine continuation,
     its order at 1, BSD itself. We assert NOTHING about the genuine L-function.
     THIS IS NOT A PROOF OF BSD AND NOT GÖDEL.

  No `sorry`, no new axiom, no `native_decide`; the quarantine is not imported;
  taint 47 is not changed.
-/

#print axioms dirichletCoeffs
#print axioms dirichletCoeffs_def
#print axioms weierstrassLSeries_eq_LSeries_coeffs
#print axioms ContinuedLFunction
#print axioms lambda_agrees_on_summable
#print axioms analyticRankOf
#print axioms analytic_order_realizes_every_rank
#print axioms analyticOrderAt_const_one_at_one
#print axioms skeletonOfNowhereSummable
#print axioms analyticRankOf_skeleton
#print axioms WeakBSDContentful
#print axioms weakBSDContentful_iff_analyticOrderAt
#print axioms contentfulGate_pins_rank
#print axioms contentfulGate_not_free_at_two_ranks
#print axioms oldGate_free_at_every_rank
#print axioms gate_contrast
#print axioms weakBSD_of_contentful
#print axioms skeleton_contentful_zero

end EuclidsPath.BSDFront.AnalyticAnchor
