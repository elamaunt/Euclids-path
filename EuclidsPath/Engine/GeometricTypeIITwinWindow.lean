/-
  GeometricTypeIITwinWindow — the SHORT-WINDOW consequence of the twin-variety fourth
  moment: completion of the two-wing incomplete sum onto the `twinV` family, the
  weighted double Cauchy–Schwarz in FOURTH-POWER form, and the good-pair theorem —
  joint two-wing cancellation on short windows for all wing-frequency pairs outside an
  explicitly counted exceptional set.

  ORIGIN.  Idea-generation session (two-axes program, wave 1a, part 2).  This is the
  crossing module welding `GeometricTypeIITwinVariety` (the pure complete-sum moment)
  to the completion×kernel engine of `GeometricTypeIIIncomplete`.  Blueprint:
  `incomplete_kloos_bound`'s assembly, with the pointwise Weil input replaced by the
  FAMILY fourth moment through a weighted double Cauchy–Schwarz.

  THE MECHANISM.  Completion turns the two-wing short sum
  `S(b₁,b₂) = Σ_{m<M} ψ(b₁·m⁻¹ + b₂·(m+2)⁻¹)` (both poles guarded) into
  `(1/ℓ)Σ_h W_M(h)·V(h,b₁,b₂)` — the completion frequency `h` lands EXACTLY on the
  linear slot of the twin family (the incomplete sum is the `a = 0` member).  The
  L¹ weight budget is `Σ_h ‖W‖/ℓ ≤ M/ℓ + 1 + log ℓ` (M-uniform).  A single
  L¹×L∞ Hölder against a pointwise bound on `V` would need Weil input and yields
  only the `ℓ^{3/4}` threshold; instead the DOUBLE Cauchy–Schwarz re-uses the weight
  inside the moment:

      (Σ w‖V‖)⁴ ≤ (Σ w)³ · (Σ w‖V‖⁴) ≤ (Σ w)³ · (max w) · (Σ_h ‖V‖⁴)

  — everything on the right is exact module data: the weight budget, the trivial
  weight bound `max w ≤ M/ℓ`, and the `a`-averaged family moment, which by
  `twinV_markov` is `≤ Kℓ³` outside `≤ 2ℓ²/K` bad pairs `(b₁,b₂)`.  Net:

      ‖S(b₁,b₂)‖⁴ ≤ (M/ℓ + 1 + log ℓ)³ · K·M·ℓ²   (good pairs)

  THE THRESHOLD READING (prose only — the theorem is the finite inequality).  For
  `M ≤ ℓ` the first factor is `≤ (2 + log ℓ)³`, so `‖S‖⁴/M⁴ ≤ (2+log ℓ)³Kℓ²/M³`:
  the bound is `o(M⁴)` exactly when `M ≫ K^{1/3}ℓ^{2/3}(2+log ℓ)` — the `ℓ^{2/3+ε}`
  regime, strictly below the engine's `ℓ^{3/4}` threshold.  The wave-1 pre-pass
  verified this chain adversarially and CORRECTED the naive L¹×L∞ route (which gives
  only `ℓ^{3/4}·log ℓ`): the double Cauchy–Schwarz is load-bearing, not cosmetic.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twin_transform_eq_twinV` — the guarded full transform IS the twin family
      member at linear frequency `h` (the house guard pattern; the shift lands on
      the ONE named parameter `a`);
    * `twin_short_completion` — `S(b₁,b₂) = (1/ℓ)Σ_h W_M(h)·V(h,b₁,b₂)`, EXACT for
      all `M` (no `M ≤ ℓ` needed — `interval_completion` is exact for all `M`);
    * `weighted_cs_fourth` (private) — `(Σ wU)⁴ ≤ (Σw)³(Σ wU⁴)` for `w ≥ 0`: two
      Cauchy–Schwarz steps in squared form, NO real roots or rpow anywhere;
    * `twin_short_fourth_bound` — **THE GOOD-PAIR WINDOW BOUND**: if
      `Σ_a ‖V(a,b₁,b₂)‖⁴ ≤ Kℓ³` then `‖S(b₁,b₂)‖⁴ ≤ (M/ℓ+1+log ℓ)³·K·M·ℓ²`;
    * `twin_short_good_pairs` — **THE HEADLINE**: for every `K > 0` there is an
      explicit bad set of `≤ 2ℓ²/K` wing-frequency pairs outside which the good-pair
      window bound holds — joint two-wing short-window cancellation, almost all pairs.

  DISCLOSURES (mandatory reading before quoting):
    * CROSSING MODULE: imports `GeometricTypeIIIncomplete`, hence transitively the
      Step00 kernel line (`Step00LargeSieve`, `Step00KloostermanMoment`) — it leaves
      the pure TypeII identity chain, exactly as `GeometricTypeIIIncomplete` does.
    * ALMOST ALL, NOT ALL.  The good-pair set depends on `K`; an all-pairs statement
      at exponent `2/3` via this route would be FALSE to state.  All-pairs needs
      genuinely pointwise input (Weil/Salié — a possible future upgrade, at `ℓ^{3/4}`
      via the engine or `ℓ^{1/2}` via non-elementary input; neither is claimed here).
    * ONE PRIME MODULUS; UNSIGNED PHASES.  The window sum carries additive characters
      only — the μ-SIGNED aggregation over composite conductors (the wall's core) is
      untouched.  Nothing here is a bound on any registered target: NOT a §110 event.
      The wall stands at SemiprimeShortRestriction / HigherConductorDispersion /
      LowFreqRootCoherence / CRE / OneWingTarget exactly as before.
    * The window starts at 0 (`Finset.range M`), matching the engine's house form;
      arbitrary starting points would phase-shift the weight, not the mechanism.
    * ZERO NEW OPEN PROPS.  `twinShort` is a named structural object, NOT a target.
      The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIITwinVariety
import EuclidsPath.Engine.GeometricTypeIIIncomplete

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### The guarded two-wing short sum and its completion -/

/-- **The two-wing short window sum**: `S(b₁,b₂) = Σ_{m<M} ψ(b₁m⁻¹ + b₂(m+2)⁻¹)` with
    both poles guarded by the twin-domain indicator.  A named structural object, NOT
    a target. -/
noncomputable def twinShort (ℓ : ℕ) [NeZero ℓ] (b₁ b₂ : ZMod ℓ) (M : ℕ) : ℂ :=
  ∑ m ∈ Finset.range M,
    if ((m : ZMod ℓ)) ∈ twinDom ℓ
    then ZMod.stdAddChar (b₁ * ((m : ZMod ℓ))⁻¹ + b₂ * (((m : ZMod ℓ)) + 2)⁻¹)
    else 0

theorem twinShort_apply {ℓ : ℕ} [NeZero ℓ] (b₁ b₂ : ZMod ℓ) (M : ℕ) :
    twinShort ℓ b₁ b₂ M
      = ∑ m ∈ Finset.range M,
          if ((m : ZMod ℓ)) ∈ twinDom ℓ
          then ZMod.stdAddChar (b₁ * ((m : ZMod ℓ))⁻¹ + b₂ * (((m : ZMod ℓ)) + 2)⁻¹)
          else 0 := rfl

/-- The guarded full transform IS the twin family member at linear frequency `h`:
    `Σ_n [n ∈ D]·ψ(b₁n⁻¹ + b₂(n+2)⁻¹)·ψ(hn) = V(h, b₁, b₂)`.  The completion
    frequency lands on the ONE named linear slot of the family (house guard pattern:
    `incomplete_transform_eq_kloos`, twin poles version). -/
theorem twin_transform_eq_twinV {ℓ : ℕ} [NeZero ℓ] (b₁ b₂ h : ZMod ℓ) :
    ∑ n : ZMod ℓ,
      (if n ∈ twinDom ℓ
        then ZMod.stdAddChar (b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0)
        * ZMod.stdAddChar (h * n)
      = twinV ℓ h b₁ b₂ := by
  rw [twinV_apply]
  have hguard : ∀ n : ZMod ℓ,
      (if n ∈ twinDom ℓ
        then ZMod.stdAddChar (b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0)
        * ZMod.stdAddChar (h * n)
      = if n ∈ twinDom ℓ
        then ZMod.stdAddChar (h * n + b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0 := by
    intro n
    by_cases hn : n ∈ twinDom ℓ
    · rw [if_pos hn, if_pos hn, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · rw [if_neg hn, if_neg hn, zero_mul]
  rw [Finset.sum_congr rfl fun n _ => hguard n]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **THE COMPLETION IDENTITY OF THE TWO-WING WINDOW**:
    `S(b₁,b₂) = (1/ℓ)·Σ_h W_M(h)·V(h,b₁,b₂)` — exact for ALL `M`.  The incomplete
    two-wing sum is the `a = 0` slice of the twin family; completion spreads it over
    the full linear-frequency line with the interval weight. -/
theorem twin_short_completion {ℓ : ℕ} [Fact ℓ.Prime] (b₁ b₂ : ZMod ℓ) (M : ℕ) :
    twinShort ℓ b₁ b₂ M
      = (ℓ : ℂ)⁻¹ * ∑ h : ZMod ℓ, intervalWeight ℓ M h * twinV ℓ h b₁ b₂ := by
  rw [twinShort_apply,
    interval_completion ℓ M (fun n =>
      if n ∈ twinDom ℓ
      then ZMod.stdAddChar (b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0)]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [twin_transform_eq_twinV]

/-! ### The weighted double Cauchy–Schwarz, fourth-power form (no roots) -/

/-- One weighted Cauchy–Schwarz step in squared form:
    `(Σ wU)² ≤ (Σw)(Σ wU²)` for `w ≥ 0` — via `√w·(√w·U)`. -/
private theorem weighted_cs_sq {ι : Type*} (s : Finset ι) (w U : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * U i) ^ 2
      ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * U i ^ 2) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * U i)
  have e1 : ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * U i)
      = ∑ i ∈ s, w i * U i :=
    Finset.sum_congr rfl fun i hi => by
      rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have e2 : ∑ i ∈ s, Real.sqrt (w i) ^ 2 = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have e3 : ∑ i ∈ s, (Real.sqrt (w i) * U i) ^ 2 = ∑ i ∈ s, w i * U i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [e1, e2, e3] at key
  exact key

/-- **The weighted double Cauchy–Schwarz, fourth-power form**:
    `(Σ wU)⁴ ≤ (Σw)³·(Σ wU⁴)` for `w ≥ 0` — two squared CS steps chained; no real
    roots or `rpow` anywhere (the whole chain lives in ℝ-polynomials). -/
private theorem weighted_cs_fourth {ι : Type*} (s : Finset ι) (w U : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * U i) ^ 4
      ≤ (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * U i ^ 4) := by
  have h1 := weighted_cs_sq s w U hw
  have h2 := weighted_cs_sq s w (fun i => U i ^ 2) hw
  have e4 : ∑ i ∈ s, w i * (U i ^ 2) ^ 2 = ∑ i ∈ s, w i * U i ^ 4 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e4] at h2
  have hB : (0 : ℝ) ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hC : (0 : ℝ) ≤ ∑ i ∈ s, w i * U i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  calc (∑ i ∈ s, w i * U i) ^ 4
      = ((∑ i ∈ s, w i * U i) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * U i ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (∑ i ∈ s, w i) ^ 2 * (∑ i ∈ s, w i * U i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i ∈ s, w i) ^ 2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * U i ^ 4)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * U i ^ 4) := by ring

/-! ### The good-pair window bound and the headline -/

/-- **THE GOOD-PAIR WINDOW BOUND**: if the `a`-averaged family moment at `(b₁,b₂)` is
    `≤ Kℓ³`, then `‖S(b₁,b₂)‖⁴ ≤ (M/ℓ + 1 + log ℓ)³·K·M·ℓ²`.  Fourth-power form —
    the `2/3`-threshold inequality with no roots.  Valid for ALL `M` (the reading is
    nontrivial for `M` above `≈ K^{1/3}ℓ^{2/3}log ℓ`; below it the trivial bound `M⁴`
    is better — disclosed in the header). -/
theorem twin_short_fourth_bound {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (b₁ b₂ : ZMod ℓ) (M : ℕ) {K : ℝ}
    (hgood : ∑ a : ZMod ℓ, ‖twinV ℓ a b₁ b₂‖ ^ 4 ≤ K * (ℓ : ℝ) ^ 3) :
    ‖twinShort ℓ b₁ b₂ M‖ ^ 4
      ≤ ((M : ℝ) / ℓ + 1 + Real.log ℓ) ^ 3 * (K * M * (ℓ : ℝ) ^ 2) := by
  have hl0 : (0 : ℝ) < (ℓ : ℝ) := by
    have h0 : 0 < ℓ := by omega
    exact_mod_cast h0
  have hl3 : (0 : ℝ) < (ℓ : ℝ) ^ 3 := pow_pos hl0 3
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ K * (ℓ : ℝ) ^ 3 :=
      le_trans (Finset.sum_nonneg fun a _ => by positivity) hgood
    nlinarith [hl3]
  -- the normalized weight
  set w : ZMod ℓ → ℝ := fun h => ‖intervalWeight ℓ M h‖ / ℓ with hw_def
  have hw0 : ∀ h : ZMod ℓ, 0 ≤ w h := fun h => by positivity
  -- ‖S‖ ≤ Σ_h w(h)·‖V(h)‖
  have hS : ‖twinShort ℓ b₁ b₂ M‖
      ≤ ∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖ := by
    rw [twin_short_completion b₁ b₂ M]
    calc ‖(ℓ : ℂ)⁻¹ * ∑ h : ZMod ℓ, intervalWeight ℓ M h * twinV ℓ h b₁ b₂‖
        = ‖(ℓ : ℂ)⁻¹‖ * ‖∑ h : ZMod ℓ, intervalWeight ℓ M h * twinV ℓ h b₁ b₂‖ :=
          norm_mul _ _
      _ ≤ ‖(ℓ : ℂ)⁻¹‖ * ∑ h : ZMod ℓ, ‖intervalWeight ℓ M h * twinV ℓ h b₁ b₂‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = ∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [norm_mul, norm_inv, Complex.norm_natCast, hw_def]
          field_simp
  -- the weight budget: Σ w ≤ M/ℓ + 1 + log ℓ
  have hL1 : ∑ h : ZMod ℓ, w h ≤ (M : ℝ) / ℓ + 1 + Real.log ℓ := by
    have hsplit : ∑ h : ZMod ℓ, w h
        = w 0 + ∑ h ∈ Finset.univ.erase (0 : ZMod ℓ), w h :=
      (Finset.add_sum_erase Finset.univ w (Finset.mem_univ 0)).symm
    have hw0v : w 0 = (M : ℝ) / ℓ := by
      rw [hw_def]
      show ‖intervalWeight ℓ M 0‖ / ℓ = (M : ℝ) / ℓ
      rw [intervalWeight_zero_freq, Complex.norm_natCast]
    have htail : ∑ h ∈ Finset.univ.erase (0 : ZMod ℓ), w h ≤ 1 + Real.log ℓ := by
      have hsum : ∑ h ∈ Finset.univ.erase (0 : ZMod ℓ), w h
          = (∑ h ∈ Finset.univ.erase (0 : ZMod ℓ), ‖intervalWeight ℓ M h‖) / ℓ := by
        rw [Finset.sum_div]
      rw [hsum, div_le_iff₀ hl0]
      calc ∑ h ∈ Finset.univ.erase (0 : ZMod ℓ), ‖intervalWeight ℓ M h‖
          ≤ (ℓ : ℝ) * (1 + Real.log ℓ) := intervalWeight_L1 h2 M
        _ = (1 + Real.log ℓ) * ℓ := by ring
    rw [hsplit, hw0v]
    linarith
  -- the trivial weight bound: max w ≤ M/ℓ
  have hmax : ∀ h : ZMod ℓ, w h ≤ (M : ℝ) / ℓ := by
    intro h
    show ‖intervalWeight ℓ M h‖ / ℓ ≤ (M : ℝ) / ℓ
    gcongr
    exact interval_weight_trivial ℓ M h
  -- Σ w‖V‖⁴ ≤ (M/ℓ)·Kℓ³ = K·M·ℓ²
  have hwv4 : ∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖ ^ 4
      ≤ K * M * (ℓ : ℝ) ^ 2 := by
    have hstep : ∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖ ^ 4
        ≤ ∑ h : ZMod ℓ, ((M : ℝ) / ℓ) * ‖twinV ℓ h b₁ b₂‖ ^ 4 :=
      Finset.sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_right (hmax h) (by positivity)
    have hfinal : ((M : ℝ) / ℓ) * (K * (ℓ : ℝ) ^ 3) = K * M * (ℓ : ℝ) ^ 2 := by
      field_simp
    calc ∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖ ^ 4
        ≤ ∑ h : ZMod ℓ, ((M : ℝ) / ℓ) * ‖twinV ℓ h b₁ b₂‖ ^ 4 := hstep
      _ = ((M : ℝ) / ℓ) * ∑ h : ZMod ℓ, ‖twinV ℓ h b₁ b₂‖ ^ 4 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ((M : ℝ) / ℓ) * (K * (ℓ : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hgood (by positivity)
      _ = K * M * (ℓ : ℝ) ^ 2 := hfinal
  -- assemble the fourth-power chain
  have hcs := weighted_cs_fourth Finset.univ w (fun h => ‖twinV ℓ h b₁ b₂‖)
    (fun h _ => hw0 h)
  have hsumw0 : (0 : ℝ) ≤ ∑ h : ZMod ℓ, w h := Finset.sum_nonneg fun h _ => hw0 h
  have hlogl : (0 : ℝ) ≤ Real.log ℓ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ ℓ))
  have hMl : (0 : ℝ) ≤ (M : ℝ) / ℓ := by positivity
  have hbudget : (0 : ℝ) ≤ (M : ℝ) / ℓ + 1 + Real.log ℓ := by linarith
  calc ‖twinShort ℓ b₁ b₂ M‖ ^ 4
      ≤ (∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) hS 4
    _ ≤ (∑ h : ZMod ℓ, w h) ^ 3
          * (∑ h : ZMod ℓ, w h * ‖twinV ℓ h b₁ b₂‖ ^ 4) := hcs
    _ ≤ ((M : ℝ) / ℓ + 1 + Real.log ℓ) ^ 3 * (K * M * (ℓ : ℝ) ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ hsumw0 hL1 3) hwv4
          (Finset.sum_nonneg fun h _ => mul_nonneg (hw0 h) (by positivity))
          (pow_nonneg hbudget 3)

/-- **THE HEADLINE — joint two-wing short-window cancellation for almost all wing
    pairs**: for every `K > 0` there is an EXPLICIT bad set of at most `2ℓ²/K`
    wing-frequency pairs `(b₁,b₂)` outside which
    `‖S(b₁,b₂)‖⁴ ≤ (M/ℓ + 1 + log ℓ)³·K·M·ℓ²` — the `ℓ^{2/3}`-regime window bound
    (see the header for the threshold reading and for what this does NOT claim). -/
theorem twin_short_good_pairs {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    {K : ℝ} (hK : 0 < K) (M : ℕ) :
    ∃ Bad : Finset (ZMod ℓ × ZMod ℓ),
      (Bad.card : ℝ) ≤ 2 * (ℓ : ℝ) ^ 2 / K
        ∧ ∀ bb : ZMod ℓ × ZMod ℓ, bb ∉ Bad →
          ‖twinShort ℓ bb.1 bb.2 M‖ ^ 4
            ≤ ((M : ℝ) / ℓ + 1 + Real.log ℓ) ^ 3 * (K * M * (ℓ : ℝ) ^ 2) := by
  refine ⟨Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
    K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4),
    twinV_markov h2 hK, ?_⟩
  intro bb hbb
  have hgood : ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4 ≤ K * (ℓ : ℝ) ^ 3 := by
    by_contra hcon
    exact hbb (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, le_of_lt (not_le.mp hcon)⟩)
  exact twin_short_fourth_bound h2 bb.1 bb.2 M hgood

/-! ### Axiom audit -/

#print axioms twin_transform_eq_twinV
#print axioms twin_short_completion
#print axioms twin_short_fourth_bound
#print axioms twin_short_good_pairs

end TypeII
end Geometric
end EuclidsPath
