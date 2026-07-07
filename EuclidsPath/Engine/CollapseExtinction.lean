/-
  CollapseExtinction — finite-time EXTINCTION for a sublinear inward drive.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS HERE AND WHAT IS NOT.                          │
  └───────────────────────────────────────────────────────────────────────────┘

  WHAT IS PROVEN (green, no sorry/axiom/native_decide):
    • COLLAPSE CORE (`sublinear_collapse_extinction`) — the EXACT DUAL of
      `DyadicBlowup.superlinear_blowup_sq`. Where the cascade blows UP
      (`y → ∞` via `y' ≥ C·y²`), a collapse runs DOWN to `r = 0` in FINITE time
      via a sublinear inward drive `r' ≤ -C·r^α` (`C>0`, `0 ≤ α < 1`). Proof:
      the auxiliary `v t := (r t)^(1-α) + (1-α)C·t` is non-increasing on `[0,∞)`
      (`v' ≤ 0`, because `(r t)^α·(r t)^{-α} = 1`), hence bounded above by
      `r0^(1-α)`, while `v T ≥ (1-α)C·T` — a contradiction for large `T`.
      Extinction no later than `T = r0^(1-α)/((1-α)C)`. Mechanism, as for the
      blow-up core: `antitoneOn_of_deriv_nonpos` (mathlib MVT) + the rpow chain
      rule `HasDerivAt.rpow_const`.
    • NON-VACUITY (`sublinear_collapse_example`) — the drive is REALLY satisfiable:
      the linear witness `r t = r0 - C·t` on `[0, r0/C)` has `r' = -C = -C·r^0`
      exactly. The core theorem is NOT vacuously true.

  WHAT IS NOT HERE (honest scope):
    • This is the abstract ODE core only — the finite-time-singularity fact shared
      by turbulent blow-up and gravitational collapse. It is SELF-CONTAINED and
      does NOT touch the first cause `step00FirstCause` (no yellow layer here).
    • The "collapse / supernova / Chandrasekhar limit / Big-Bang" readings are
      METAPHOR (prose ch. 52), not theorems; the blow-up↔collapse "duality" is a
      shared ODE mechanism, not a duality theorem.
    • Deriving the inward drive `r' ≤ -C·r^α` from a physical self-gravity law
      (Euler–Poisson / Larson–Penston self-similar collapse) is a NAMED analytic
      input, rigorous in the literature but far beyond `mathlib` — NOT done here.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.CollapseExtinction

open scoped Topology

/--
**`sublinear_collapse_extinction` — PROVEN (collapse core, dual of `superlinear_blowup_sq`).**

There does NOT exist a global positive C¹ function `r : [0,∞) → ℝ` satisfying the
sublinear inward drive `r'(t) ≤ -C·r(t)^α` with `C > 0`, `0 ≤ α < 1`, `r 0 = r0 > 0`.

Meaning: a sublinear inward drive drives `r` to `0` in FINITE time — collapse to a
point singularity. The dual of the cascade blow-up: there the magnitude runs to `∞`,
here the radius runs to `0`, both at a finite time.

Proof: with `p := 1 - α > 0` and `K := p·C > 0`, the auxiliary
`v t := (r t)^p + K·t` is monotonically NON-INCREASING on `[0,∞)`, because
`v'(t) = r'(t)·p·(r t)^{p-1} + K ≤ -K + K = 0`
(using `r'(t) ≤ -C·(r t)^α` and `(r t)^α·(r t)^{p-1} = (r t)^0 = 1`). Hence
`v T ≤ v 0 = r0^p`, but `v T = (r T)^p + K·T ≥ K·T`, so `K·T ≤ r0^p`,
contradicted at `T := r0^p / K + 1`. -/
theorem sublinear_collapse_extinction
    (r : ℝ → ℝ) (r' : ℝ → ℝ) (C r0 α : ℝ)
    (hC : 0 < C) (hα0 : 0 ≤ α) (hα1 : α < 1) (hr0 : 0 < r0) (hInit : r 0 = r0)
    (hpos : ∀ t, 0 ≤ t → 0 < r t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt r (r' t) t)
    (hdrive : ∀ t, 0 ≤ t → r' t ≤ -C * (r t) ^ α) : False := by
  set p : ℝ := 1 - α with hp
  have hppos : 0 < p := by rw [hp]; linarith
  set K : ℝ := p * C with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  -- v t := (r t)^p + K·t  has derivative  r' t * (p * (r t)^(p-1)) + K
  have hvderiv : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (r s) ^ p + K * s)
        (r' t * p * (r t) ^ (p - 1) + K) t := by
    intro t ht
    have hrne : r t ≠ 0 := ne_of_gt (hpos t ht)
    have h1 : HasDerivAt (fun s => (r s) ^ p) (r' t * p * (r t) ^ (p - 1)) t :=
      (hderiv t ht).rpow_const (Or.inl hrne)
    have h2 : HasDerivAt (fun s : ℝ => K * s) K t := by
      simpa using (hasDerivAt_id t).const_mul K
    exact h1.add h2
  -- the derivative of v on (0,∞) is non-positive
  have hvnonpos : ∀ t, 0 < t → deriv (fun s => (r s) ^ p + K * s) t ≤ 0 := by
    intro t ht
    have hle := ht.le
    have hderivEq : deriv (fun s => (r s) ^ p + K * s) t
        = r' t * p * (r t) ^ (p - 1) + K := (hvderiv t hle).deriv
    rw [hderivEq]
    have hrpos := hpos t hle
    have hdr := hdrive t hle
    -- (r t)^α · (r t)^(p-1) = 1
    have hexp : (r t) ^ α * (r t) ^ (p - 1) = 1 := by
      rw [← Real.rpow_add hrpos]
      have hsum : α + (p - 1) = 0 := by rw [hp]; ring
      rw [hsum, Real.rpow_zero]
    -- p · (r t)^(p-1) > 0
    have hfac : 0 < p * (r t) ^ (p - 1) := by
      have := Real.rpow_pos_of_pos hrpos (p - 1)
      positivity
    -- r' t · (p·(r t)^(p-1)) ≤ -K
    have hmul : r' t * (p * (r t) ^ (p - 1))
        ≤ (-C * (r t) ^ α) * (p * (r t) ^ (p - 1)) :=
      mul_le_mul_of_nonneg_right hdr (le_of_lt hfac)
    have hrhs : (-C * (r t) ^ α) * (p * (r t) ^ (p - 1)) = -K := by
      rw [hK]
      have hcalc : (-C * (r t) ^ α) * (p * (r t) ^ (p - 1))
          = -(p * C) * ((r t) ^ α * (r t) ^ (p - 1)) := by ring
      rw [hcalc, hexp]; ring
    have hbound : r' t * p * (r t) ^ (p - 1) ≤ -K := by
      calc r' t * p * (r t) ^ (p - 1)
            = r' t * (p * (r t) ^ (p - 1)) := by ring
        _ ≤ (-C * (r t) ^ α) * (p * (r t) ^ (p - 1)) := hmul
        _ = -K := hrhs
    linarith [hbound]
  -- monotonicity: deriv ≤ 0 on interior ⟹ AntitoneOn
  have hcont : ContinuousOn (fun s => (r s) ^ p + K * s) (Set.Ici 0) := fun x hx =>
    (hvderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (r s) ^ p + K * s)
      (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    intro x hx
    exact ((hvderiv x (le_of_lt hx)).differentiableAt).differentiableWithinAt
  have hnp : ∀ x ∈ interior (Set.Ici (0:ℝ)),
      deriv (fun s => (r s) ^ p + K * s) x ≤ 0 := by
    rw [interior_Ici]; intro x hx; exact hvnonpos x hx
  have hanti : AntitoneOn (fun s => (r s) ^ p + K * s) (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff hnp
  -- a sufficiently large T yields a contradiction
  have hr0p : 0 < r0 ^ p := Real.rpow_pos_of_pos hr0 p
  set T : ℝ := r0 ^ p / K + 1 with hT
  have hTpos : 0 < T := by
    rw [hT]; have := div_nonneg hr0p.le hKpos.le; linarith
  have hle : (fun s => (r s) ^ p + K * s) T ≤ (fun s => (r s) ^ p + K * s) 0 :=
    hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr hTpos.le) hTpos.le
  simp only at hle
  have hv0 : (r (0:ℝ)) ^ p + K * 0 = r0 ^ p := by rw [hInit]; ring
  have hCTval : K * T = r0 ^ p + K := by rw [hT]; field_simp
  have hrTp : 0 < (r T) ^ p := Real.rpow_pos_of_pos (hpos T hTpos.le) p
  rw [hv0] at hle
  rw [hCTval] at hle
  linarith

/--
**`sublinear_collapse_example` — PROVEN (non-vacuity of the drive).**

The linear witness `r t = r0 - C·t` on `[0, r0/C)` (with `C>0`, `r0>0`) is positive
and satisfies the collapse drive `r'(t) = -C = -C·r(t)^0` with equality (the `α = 0`
case). Hence the hypotheses of `sublinear_collapse_extinction` (minus globality) are
REALLY satisfiable — the core theorem is not vacuously true; only GLOBAL positivity
fails, which is exactly finite-time collapse. -/
theorem sublinear_collapse_example (C r0 : ℝ) (hC : 0 < C) (hr0 : 0 < r0) :
    ∃ (r r' : ℝ → ℝ), r 0 = r0 ∧
      (∀ t, HasDerivAt r (r' t) t) ∧
      (∀ t, 0 ≤ t → t < r0 / C → 0 < r t) ∧
      (∀ t, r' t = -C * (r t) ^ (0 : ℝ)) := by
  refine ⟨fun t => r0 - C * t, fun _ => -C, by ring, ?_, ?_, ?_⟩
  · intro t
    have h2 : HasDerivAt (fun s : ℝ => C * s) C t := by
      simpa using (hasDerivAt_id t).const_mul C
    simpa using h2.const_sub r0
  · intro t _ht htC
    have hlt : t * C < r0 := (lt_div_iff₀ hC).mp htC
    show 0 < r0 - C * t
    nlinarith [hlt]
  · intro t
    simp [Real.rpow_zero]

end EuclidsPath.CollapseExtinction
