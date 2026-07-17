/-
  GeometricTypeIITwinWindowU — THE SHORT WINDOW LEAVES THE PRIME LINE: the
  wave-1 two-wing short-window machinery (completion → weighted double
  Cauchy–Schwarz → good-pair count) ported to EVERY modulus on the UNIT
  domain, and instantiated at semiprimes:

      for all K > 0 there are ≤ 4q²/K bad pairs (b₁,b₂) mod q = ℓ₁ℓ₂
      outside which  ‖S_U(b₁,b₂)‖⁴ ≤ (M/q + 1 + log q)³ · K·M·q².

  ORIGIN.  Autonomous continuation (wave 5c): the named follow-up of wave 5b
  — the completion engine (`interval_completion`, `interval_weight_trivial`,
  `intervalWeight_zero_freq`) was ALREADY general `[NeZero q]`; the kernel L¹
  bound (`intervalWeight_L1`) was stated at primes but its proof uses NO
  primality (harmonic halves + `tmin` — all `[NeZero]` facts): it generalizes
  by hypothesis change alone.  The only genuinely prime-line inputs of wave 1
  were `twinV` and `twinV_markov` — replaced by `twinVU` (wave 5a) and
  `twinVU_markov_general`/`_semiprime` (wave 5b).  Numerical pre-pass (this
  session): the completion identity on the UNIT domain at q = 35 verified for
  five (b₁,b₂,M) triples including M > q, worst error 1.8e−15.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `intervalWeight_L1_general` — `Σ_{h≠0}‖W_M(h)‖ ≤ q(1+log q)` at EVERY
      modulus (the prime hypothesis of the wave-1 lemma was inessential);
    * `twinShortU` + `twinShortU_eq_twinShort` — the unit-guarded two-wing
      window sum; at primes it IS the wave-1 object (total reuse);
    * `twin_short_completion_U` — `S_U(b₁,b₂) = (1/q)Σ_h W_M(h)·V_U(h,b₁,b₂)`
      EXACT for all `M`, all moduli;
    * `twin_short_fourth_bound_U` — the good-pair window bound at every
      modulus: moment ≤ Kq³ ⟹ ‖S_U‖⁴ ≤ (M/q + 1 + log q)³·K·M·q²;
    * `twin_short_good_pairs_U` — the general headline: bad set ≤ N4U(q)/K;
    * `twin_short_good_pairs_semiprime` — **THE SEMIPRIME HEADLINE** displayed
      above: joint two-wing short-window cancellation at a COMPOSITE modulus,
      almost all wing-frequency pairs, the `q^{2/3}`-regime reading.

  DISCLOSURES.
    * The threshold reading is prose, not Lean: for `M ≤ q` the bound is
      `o(M⁴)` exactly when `M ≫ K^{1/3}q^{2/3}(2+log q)` — same exponent as
      the prime line; the constant worsens 2 → 4.
    * This puts the SHORT-WINDOW LANGUAGE at composite moduli; it does NOT
      touch face E's actual content — the μ-SIGNED aggregation across
      INCOMMENSURABLE moduli.  A single composite modulus is still ONE
      modulus; the wall's faces (CRE / OneWingTarget / LowFreqRootCoherence /
      SemiprimeShortRestriction / HigherConductorDispersion) are UNTOUCHED.
    * No pointwise extraction exists for this family (wave-1 disclosure
      stands); the averaged good-pair count is the entire cash value.
    * NOT a §110 event.  The twin sorry (`twin_prime_conjecture`) is
      untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIITwinWindow
import EuclidsPath.Engine.GeometricTypeIITwinVarietyCRTMarkov

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 1: the kernel L¹ bound at every modulus (the prime hypothesis
of the wave-1 lemma was inessential — hypothesis change, same proof) -/

private theorem sum_inv_tmin_le_general {q : ℕ} [NeZero q] (hq2 : 2 < q) :
    ∑ h ∈ Finset.univ.erase (0 : ZMod q), (1 : ℝ) / (tmin h)
      ≤ 2 * (1 + Real.log q) := by
  have hq0 : 0 < q := by omega
  have hpt : ∀ h ∈ Finset.univ.erase (0 : ZMod q),
      (1 : ℝ) / (tmin h) ≤ 1 / (h.val : ℝ) + 1 / ((q - h.val : ℕ) : ℝ) := by
    intro h hmem
    have hh : h ≠ 0 := Finset.ne_of_mem_erase hmem
    have hv1 : 1 ≤ h.val := by
      have := tmin_pos (p := q) hh
      unfold tmin at this
      omega
    have hvq : h.val < q := ZMod.val_lt h
    have h1 : (0 : ℝ) < (h.val : ℝ) := by exact_mod_cast hv1
    have h2 : (0 : ℝ) < ((q - h.val : ℕ) : ℝ) := by
      have : 0 < q - h.val := by omega
      exact_mod_cast this
    unfold tmin
    rcases min_cases h.val (q - h.val) with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]
      have : (0 : ℝ) ≤ 1 / ((q - h.val : ℕ) : ℝ) := by positivity
      linarith
    · rw [hmin]
      have : (0 : ℝ) ≤ 1 / (h.val : ℝ) := by positivity
      linarith
  have hstep := Finset.sum_le_sum hpt
  have hbij : ∑ h ∈ Finset.univ.erase (0 : ZMod q),
      ((1 : ℝ) / (h.val : ℝ) + 1 / ((q - h.val : ℕ) : ℝ))
      = ∑ v ∈ Finset.Icc 1 (q - 1), ((1 : ℝ) / (v : ℝ) + 1 / ((q - v : ℕ) : ℝ)) := by
    apply Finset.sum_nbij' (fun h : ZMod q => h.val) (fun v : ℕ => (v : ZMod q))
    · intro h hmem
      have hh : h ≠ 0 := Finset.ne_of_mem_erase hmem
      have hv1 : 1 ≤ h.val := by
        have := tmin_pos (p := q) hh
        unfold tmin at this
        omega
      have hvq : h.val < q := ZMod.val_lt h
      simp only [Finset.mem_Icc]
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro hc
      have hmod : v % q = 0 % q :=
        (ZMod.natCast_eq_natCast_iff v 0 q).mp (by simpa using hc)
      have hvq : v < q := by omega
      rw [Nat.mod_eq_of_lt hvq, Nat.zero_mod] at hmod
      omega
    · intro h _
      exact ZMod.natCast_rightInverse h
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      exact ZMod.val_cast_of_lt (by omega)
    · intro h _
      rfl
  have hsplit : ∑ v ∈ Finset.Icc 1 (q - 1),
      ((1 : ℝ) / (v : ℝ) + 1 / ((q - v : ℕ) : ℝ))
      = (∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (v : ℝ))
        + ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((q - v : ℕ) : ℝ) :=
    Finset.sum_add_distrib
  have hrefl : ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((q - v : ℕ) : ℝ)
      = ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (v : ℝ) := by
    apply Finset.sum_nbij' (fun v : ℕ => q - v) (fun v : ℕ => q - v)
    · intro v hv
      simp only [Finset.mem_Icc] at hv ⊢
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv ⊢
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      omega
    · intro v hv
      rfl
  have hharm : ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (v : ℝ)
      ≤ 1 + Real.log q := by
    have heq : ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (v : ℝ)
        = ((harmonic (q - 1) : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [one_div]
    rw [heq]
    calc ((harmonic (q - 1) : ℚ) : ℝ)
        ≤ 1 + Real.log (q - 1 : ℕ) := harmonic_le_one_add_log _
      _ ≤ 1 + Real.log q := by
          have h1 : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
            have : 0 < q - 1 := by omega
            exact_mod_cast this
          have h2 : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
            have : q - 1 ≤ q := by omega
            exact_mod_cast this
          have := Real.log_le_log h1 h2
          linarith
  calc ∑ h ∈ Finset.univ.erase (0 : ZMod q), (1 : ℝ) / (tmin h)
      ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod q),
          ((1 : ℝ) / (h.val : ℝ) + 1 / ((q - h.val : ℕ) : ℝ)) := hstep
    _ = ∑ v ∈ Finset.Icc 1 (q - 1),
          ((1 : ℝ) / (v : ℝ) + 1 / ((q - v : ℕ) : ℝ)) := hbij
    _ = (∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (v : ℝ))
        + ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / ((q - v : ℕ) : ℝ) := hsplit
    _ = 2 * ∑ v ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / (v : ℝ) := by rw [hrefl]; ring
    _ ≤ 2 * (1 + Real.log q) := by linarith [hharm]

/-- **The kernel L¹ bound at EVERY modulus**: `Σ_{h≠0}‖W_M(h)‖ ≤ q(1+log q)`,
uniformly in `M` — the wave-1 prime hypothesis was inessential. -/
theorem intervalWeight_L1_general {q : ℕ} [NeZero q] (hq2 : 2 < q) (M : ℕ) :
    ∑ h ∈ Finset.univ.erase (0 : ZMod q), ‖intervalWeight q M h‖
      ≤ (q : ℝ) * (1 + Real.log q) := by
  have hq0 : 0 < q := by omega
  have hstep : ∀ h ∈ Finset.univ.erase (0 : ZMod q),
      ‖intervalWeight q M h‖ ≤ ((q : ℝ) / 2) * ((1 : ℝ) / (tmin h)) := by
    intro h hmem
    have hh : h ≠ 0 := Finset.ne_of_mem_erase hmem
    have := intervalWeight_norm_le_tmin hq0 M hh
    have htm : (0 : ℝ) < (tmin h : ℝ) := by exact_mod_cast tmin_pos hh
    calc ‖intervalWeight q M h‖ ≤ (q : ℝ) / (2 * tmin h) := this
      _ = ((q : ℝ) / 2) * ((1 : ℝ) / (tmin h)) := by
          field_simp
  calc ∑ h ∈ Finset.univ.erase (0 : ZMod q), ‖intervalWeight q M h‖
      ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod q),
          ((q : ℝ) / 2) * ((1 : ℝ) / (tmin h)) :=
        Finset.sum_le_sum hstep
    _ = ((q : ℝ) / 2) * ∑ h ∈ Finset.univ.erase (0 : ZMod q),
          (1 : ℝ) / (tmin h) := by
        rw [Finset.mul_sum]
    _ ≤ ((q : ℝ) / 2) * (2 * (1 + Real.log q)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_tmin_le_general hq2) (by positivity)
    _ = (q : ℝ) * (1 + Real.log q) := by ring

/-! ### Layer 2: the unit two-wing short window and its completion -/

/-- **The unit two-wing short window sum**: the wave-1 object with the
unit-domain guard — the correct guard off the prime line (wave-5a lesson). -/
noncomputable def twinShortU (q : ℕ) [NeZero q] (b₁ b₂ : ZMod q) (M : ℕ) : ℂ :=
  ∑ m ∈ Finset.range M,
    if ((m : ZMod q)) ∈ twinDomU q
    then ZMod.stdAddChar (b₁ * ((m : ZMod q))⁻¹ + b₂ * (((m : ZMod q)) + 2)⁻¹)
    else 0

theorem twinShortU_apply {q : ℕ} [NeZero q] (b₁ b₂ : ZMod q) (M : ℕ) :
    twinShortU q b₁ b₂ M
      = ∑ m ∈ Finset.range M,
          if ((m : ZMod q)) ∈ twinDomU q
          then ZMod.stdAddChar (b₁ * ((m : ZMod q))⁻¹ + b₂ * (((m : ZMod q)) + 2)⁻¹)
          else 0 := rfl

/-- At primes the unit window IS the wave-1 window (total reuse). -/
theorem twinShortU_eq_twinShort {ℓ : ℕ} [Fact ℓ.Prime] (b₁ b₂ : ZMod ℓ) (M : ℕ) :
    twinShortU ℓ b₁ b₂ M = twinShort ℓ b₁ b₂ M := by
  rw [twinShortU_apply, twinShort_apply]
  simp only [twinDomU_eq_twinDom]

/-- The guarded full transform IS the unit twin family member at linear
frequency `h` (house guard pattern, every modulus). -/
theorem twinU_transform_eq_twinVU {q : ℕ} [NeZero q] (b₁ b₂ h : ZMod q) :
    ∑ n : ZMod q,
      (if n ∈ twinDomU q
        then ZMod.stdAddChar (b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0)
        * ZMod.stdAddChar (h * n)
      = twinVU q h b₁ b₂ := by
  rw [twinVU_apply]
  have hguard : ∀ n : ZMod q,
      (if n ∈ twinDomU q
        then ZMod.stdAddChar (b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0)
        * ZMod.stdAddChar (h * n)
      = if n ∈ twinDomU q
        then ZMod.stdAddChar (h * n + b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0 := by
    intro n
    by_cases hn : n ∈ twinDomU q
    · rw [if_pos hn, if_pos hn, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · rw [if_neg hn, if_neg hn, zero_mul]
  rw [Finset.sum_congr rfl fun n _ => hguard n]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **THE COMPLETION IDENTITY AT EVERY MODULUS**:
`S_U(b₁,b₂) = (1/q)·Σ_h W_M(h)·V_U(h,b₁,b₂)` — exact for ALL `M`.
(Numerically verified on the unit domain at q = 35, worst error 1.8e−15.) -/
theorem twin_short_completion_U {q : ℕ} [NeZero q] (b₁ b₂ : ZMod q) (M : ℕ) :
    twinShortU q b₁ b₂ M
      = (q : ℂ)⁻¹ * ∑ h : ZMod q, intervalWeight q M h * twinVU q h b₁ b₂ := by
  rw [twinShortU_apply,
    interval_completion q M (fun n =>
      if n ∈ twinDomU q
      then ZMod.stdAddChar (b₁ * n⁻¹ + b₂ * (n + 2)⁻¹) else 0)]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [twinU_transform_eq_twinVU]

/-! ### Layer 3: the weighted double Cauchy–Schwarz (fourth-power, no roots) -/

private theorem weighted_cs_sq' {ι : Type*} (s : Finset ι) (w U : ι → ℝ)
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

private theorem weighted_cs_fourth' {ι : Type*} (s : Finset ι) (w U : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * U i) ^ 4
      ≤ (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * U i ^ 4) := by
  have h1 := weighted_cs_sq' s w U hw
  have h2 := weighted_cs_sq' s w (fun i => U i ^ 2) hw
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

/-! ### Layer 4: the good-pair window bound and the headlines -/

/-- **THE GOOD-PAIR WINDOW BOUND AT EVERY MODULUS**: if the a-averaged family
moment at `(b₁,b₂)` is `≤ Kq³` then
`‖S_U(b₁,b₂)‖⁴ ≤ (M/q + 1 + log q)³·K·M·q²`. -/
theorem twin_short_fourth_bound_U {q : ℕ} [NeZero q] (hq2 : 2 < q)
    (b₁ b₂ : ZMod q) (M : ℕ) {K : ℝ}
    (hgood : ∑ a : ZMod q, ‖twinVU q a b₁ b₂‖ ^ 4 ≤ K * (q : ℝ) ^ 3) :
    ‖twinShortU q b₁ b₂ M‖ ^ 4
      ≤ ((M : ℝ) / q + 1 + Real.log q) ^ 3 * (K * M * (q : ℝ) ^ 2) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have h0 : 0 < q := by omega
    exact_mod_cast h0
  have hq3 : (0 : ℝ) < (q : ℝ) ^ 3 := pow_pos hq0 3
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ K * (q : ℝ) ^ 3 :=
      le_trans (Finset.sum_nonneg fun a _ => by positivity) hgood
    nlinarith [hq3]
  set w : ZMod q → ℝ := fun h => ‖intervalWeight q M h‖ / q with hw_def
  have hw0 : ∀ h : ZMod q, 0 ≤ w h := fun h => by positivity
  have hS : ‖twinShortU q b₁ b₂ M‖
      ≤ ∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖ := by
    rw [twin_short_completion_U b₁ b₂ M]
    calc ‖(q : ℂ)⁻¹ * ∑ h : ZMod q, intervalWeight q M h * twinVU q h b₁ b₂‖
        = ‖(q : ℂ)⁻¹‖ * ‖∑ h : ZMod q, intervalWeight q M h * twinVU q h b₁ b₂‖ :=
          norm_mul _ _
      _ ≤ ‖(q : ℂ)⁻¹‖ * ∑ h : ZMod q, ‖intervalWeight q M h * twinVU q h b₁ b₂‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = ∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [norm_mul, norm_inv, Complex.norm_natCast, hw_def]
          field_simp
  have hL1 : ∑ h : ZMod q, w h ≤ (M : ℝ) / q + 1 + Real.log q := by
    have hsplit : ∑ h : ZMod q, w h
        = w 0 + ∑ h ∈ Finset.univ.erase (0 : ZMod q), w h :=
      (Finset.add_sum_erase Finset.univ w (Finset.mem_univ 0)).symm
    have hw0v : w 0 = (M : ℝ) / q := by
      rw [hw_def]
      show ‖intervalWeight q M 0‖ / q = (M : ℝ) / q
      rw [intervalWeight_zero_freq, Complex.norm_natCast]
    have htail : ∑ h ∈ Finset.univ.erase (0 : ZMod q), w h ≤ 1 + Real.log q := by
      have hsum : ∑ h ∈ Finset.univ.erase (0 : ZMod q), w h
          = (∑ h ∈ Finset.univ.erase (0 : ZMod q), ‖intervalWeight q M h‖) / q := by
        rw [Finset.sum_div]
      rw [hsum, div_le_iff₀ hq0]
      calc ∑ h ∈ Finset.univ.erase (0 : ZMod q), ‖intervalWeight q M h‖
          ≤ (q : ℝ) * (1 + Real.log q) := intervalWeight_L1_general hq2 M
        _ = (1 + Real.log q) * q := by ring
    rw [hsplit, hw0v]
    linarith
  have hmax : ∀ h : ZMod q, w h ≤ (M : ℝ) / q := by
    intro h
    show ‖intervalWeight q M h‖ / q ≤ (M : ℝ) / q
    gcongr
    exact interval_weight_trivial q M h
  have hwv4 : ∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖ ^ 4
      ≤ K * M * (q : ℝ) ^ 2 := by
    have hstep : ∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖ ^ 4
        ≤ ∑ h : ZMod q, ((M : ℝ) / q) * ‖twinVU q h b₁ b₂‖ ^ 4 :=
      Finset.sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_right (hmax h) (by positivity)
    have hfinal : ((M : ℝ) / q) * (K * (q : ℝ) ^ 3) = K * M * (q : ℝ) ^ 2 := by
      field_simp
    calc ∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖ ^ 4
        ≤ ∑ h : ZMod q, ((M : ℝ) / q) * ‖twinVU q h b₁ b₂‖ ^ 4 := hstep
      _ = ((M : ℝ) / q) * ∑ h : ZMod q, ‖twinVU q h b₁ b₂‖ ^ 4 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ((M : ℝ) / q) * (K * (q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hgood (by positivity)
      _ = K * M * (q : ℝ) ^ 2 := hfinal
  have hcs := weighted_cs_fourth' Finset.univ w (fun h => ‖twinVU q h b₁ b₂‖)
    (fun h _ => hw0 h)
  have hsumw0 : (0 : ℝ) ≤ ∑ h : ZMod q, w h := Finset.sum_nonneg fun h _ => hw0 h
  have hlogq : (0 : ℝ) ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hMq : (0 : ℝ) ≤ (M : ℝ) / q := by positivity
  have hbudget : (0 : ℝ) ≤ (M : ℝ) / q + 1 + Real.log q := by linarith
  calc ‖twinShortU q b₁ b₂ M‖ ^ 4
      ≤ (∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) hS 4
    _ ≤ (∑ h : ZMod q, w h) ^ 3
          * (∑ h : ZMod q, w h * ‖twinVU q h b₁ b₂‖ ^ 4) := hcs
    _ ≤ ((M : ℝ) / q + 1 + Real.log q) ^ 3 * (K * M * (q : ℝ) ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ hsumw0 hL1 3) hwv4
          (Finset.sum_nonneg fun h _ => mul_nonneg (hw0 h) (by positivity))
          (pow_nonneg hbudget 3)

/-- **The general good-pair headline**: at EVERY modulus, for every `K > 0`
there is an explicit bad set of ≤ N4U(q)/K wing pairs outside which the
window bound holds. -/
theorem twin_short_good_pairs_U {q : ℕ} [NeZero q] (hq2 : 2 < q)
    {K : ℝ} (hK : 0 < K) (M : ℕ) :
    ∃ Bad : Finset (ZMod q × ZMod q),
      (Bad.card : ℝ) ≤ ((twinN4U q).card : ℝ) / K
        ∧ ∀ bb : ZMod q × ZMod q, bb ∉ Bad →
          ‖twinShortU q bb.1 bb.2 M‖ ^ 4
            ≤ ((M : ℝ) / q + 1 + Real.log q) ^ 3 * (K * M * (q : ℝ) ^ 2) := by
  refine ⟨Finset.univ.filter (fun bb : ZMod q × ZMod q =>
    K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4),
    twinVU_markov_general hK, ?_⟩
  intro bb hbb
  have hgood : ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4 ≤ K * (q : ℝ) ^ 3 := by
    by_contra hcon
    exact hbb (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, le_of_lt (not_le.mp hcon)⟩)
  exact twin_short_fourth_bound_U hq2 bb.1 bb.2 M hgood

/-- **THE SEMIPRIME HEADLINE — the short window leaves the prime line**: at
`q = ℓ₁ℓ₂` there are ≤ 4q²/K bad wing pairs outside which
`‖S_U(b₁,b₂)‖⁴ ≤ (M/q + 1 + log q)³·K·M·q²` — joint two-wing short-window
cancellation at a COMPOSITE modulus, almost all pairs, the `q^{2/3}` regime
(see the header for the reading and for what this does NOT claim). -/
theorem twin_short_good_pairs_semiprime {ℓ₁ ℓ₂ : ℕ}
    [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) {K : ℝ} (hK : 0 < K) (M : ℕ) :
    ∃ Bad : Finset (ZMod (ℓ₁ * ℓ₂) × ZMod (ℓ₁ * ℓ₂)),
      (Bad.card : ℝ) ≤ 4 * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 2 / K
        ∧ ∀ bb : ZMod (ℓ₁ * ℓ₂) × ZMod (ℓ₁ * ℓ₂), bb ∉ Bad →
          ‖twinShortU (ℓ₁ * ℓ₂) bb.1 bb.2 M‖ ^ 4
            ≤ ((M : ℝ) / (ℓ₁ * ℓ₂ : ℕ) + 1 + Real.log (ℓ₁ * ℓ₂ : ℕ)) ^ 3
              * (K * M * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 2) := by
  have hq2 : 2 < ℓ₁ * ℓ₂ := by
    have h9 : 9 ≤ ℓ₁ * ℓ₂ :=
      Nat.mul_le_mul (by omega : 3 ≤ ℓ₁) (by omega : 3 ≤ ℓ₂)
    omega
  refine ⟨Finset.univ.filter (fun bb : ZMod (ℓ₁ * ℓ₂) × ZMod (ℓ₁ * ℓ₂) =>
    K * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 3 ≤ ∑ a : ZMod (ℓ₁ * ℓ₂),
      ‖twinVU (ℓ₁ * ℓ₂) a bb.1 bb.2‖ ^ 4),
    twinVU_markov_semiprime h₁ h₂ hne hK, ?_⟩
  intro bb hbb
  have hgood : ∑ a : ZMod (ℓ₁ * ℓ₂), ‖twinVU (ℓ₁ * ℓ₂) a bb.1 bb.2‖ ^ 4
      ≤ K * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 3 := by
    by_contra hcon
    exact hbb (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, le_of_lt (not_le.mp hcon)⟩)
  exact twin_short_fourth_bound_U hq2 bb.1 bb.2 M hgood

end TypeII
end Geometric
end EuclidsPath
