/-
  Analytic/PrimePiAP — the π-WING of stage P: PNT in progressions in
  COUNTING FORM — the exact landing contract of stage L.

  `apCount a X` counts primes `p ≤ X` with `p % 6 = a` (the landing's
  spelling).  The chain: the θ-form mod 6 (P-C3/C4) transfers to the
  `%`-spelling, the Abel bridge mirrors the pin's
  `primeCounting_eq_theta_div_log_add_integral` with the class indicator
  carried through `sum_mul_eq_sub_integral_mul₁`, and the correction
  integral is dominated by the pin's global
  `integral_theta_div_log_sq_isLittleO`.  Deliverable:

    `apCount_mul_log_div_tendsto : a ∈ {1, 5} →
       Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
         atTop (nhds 1)`

  — the named hypothesis `hAP` of the stage-L wing-sign theorems,
  DISCHARGED.

  DISCLOSURES.
    * π-in-AP machinery; no face of the parity wall is touched, and no
      §110 event is claimed.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Analytic.PNTCorollaries

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex ArithmeticFunction Filter MeasureTheory Set Finset
open scoped LSeries.notation

/-- The landing's prime counter: primes `p ≤ X` with `p % 6 = a`. -/
def apCount (a X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun n => n.Prime ∧ n % 6 = a).card

/-- The `%`-spelled class θ. -/
noncomputable def thetaMod (a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 6 = a),
    Real.log p

/-- The class indicator weighted by `log` — the Abel-summation
coefficient. -/
noncomputable def apIndicator (a : ℕ) : ℕ → ℝ :=
  Set.indicator {n : ℕ | n.Prime ∧ n % 6 = a} (fun n => Real.log n)

theorem apIndicator_zero (a : ℕ) : apIndicator a 0 = 0 := by
  simp [apIndicator, Nat.not_prime_zero]

theorem apIndicator_one (a : ℕ) : apIndicator a 1 = 0 := by
  simp [apIndicator, Nat.not_prime_one]

theorem apIndicator_sum (a : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apIndicator a k = thetaMod a t := by
  unfold thetaMod
  rw [show Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp), apIndicator_zero, zero_add,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _ => by
    simp [apIndicator, Set.indicator_apply]

/-- The `%`-spelling matches the `ZMod`-spelling. -/
theorem thetaMod_eq_thetaRes {a : ℕ} (ha : a < 6) (x : ℝ) :
    thetaMod a x = thetaRes ((a : ℕ) : ZMod 6) x := by
  unfold thetaMod thetaRes
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, and_congr_right_iff]
  intro _ _
  rw [ZMod.natCast_eq_natCast_iff]
  show p % 6 = a ↔ p % 6 = a % 6
  rw [Nat.mod_eq_of_lt ha]

theorem thetaMod_div_tendsto {a : ℕ} (ha : a = 1 ∨ a = 5) :
    Tendsto (fun x : ℝ => thetaMod a x / x) atTop (nhds (1 / 2 : ℝ)) := by
  rcases ha with rfl | rfl
  · refine thetaRes_six_one.congr fun x => ?_
    rw [thetaMod_eq_thetaRes (by norm_num)]
    norm_num
  · refine thetaRes_six_five.congr fun x => ?_
    rw [thetaMod_eq_thetaRes (by norm_num)]
    norm_num

theorem thetaMod_nonneg (a : ℕ) (x : ℝ) : 0 ≤ thetaMod a x := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact Real.log_nonneg (by exact_mod_cast hp1)

theorem thetaMod_le_theta (a : ℕ) (x : ℝ) :
    thetaMod a x ≤ Chebyshev.theta x := by
  unfold thetaMod Chebyshev.theta
  rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp _
    have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact Real.log_nonneg (by exact_mod_cast hp1)

/-! ### The Abel bridge (mirror of the pin's `primeCounting` identity) -/

theorem apCount_eq_thetaMod_div_log_add_integral {a : ℕ} {x : ℝ}
    (hx : 2 ≤ x) :
    (apCount a ⌊x⌋₊ : ℝ)
      = thetaMod a x / Real.log x
        + ∫ t in (2 : ℝ)..x, thetaMod a t / (t * Real.log t ^ 2) := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t := by
    intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hlz : Real.log z ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [hz.1])
        (by linarith [hz.1])
    fun_prop
  have hint : IntegrableOn (deriv (fun u : ℝ => (Real.log u)⁻¹))
      (Set.Icc 2 x) := by
    refine ContinuousOn.integrableOn_Icc fun z hz =>
      ContinuousWithinAt.congr ?_ (fun _ _ => Real.deriv_inv_log) Real.deriv_inv_log
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have h2 : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2
      (Real.log_ne_zero_of_pos_of_ne_one (by linarith [hz.1])
        (by linarith [hz.1]))
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hcount : (apCount a ⌊x⌋₊ : ℝ)
      = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log k)⁻¹ * apIndicator a k := by
    unfold apCount
    rw [Finset.card_filter]
    push_cast
    rw [show Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    rw [apIndicator_zero, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hc : k.Prime ∧ k % 6 = a
    · rw [if_pos hc]
      have hk2 : 2 ≤ k := hc.1.two_le
      have hlk : Real.log k ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hc.1.pos)
          (by exact_mod_cast hc.1.ne_one)
      rw [show apIndicator a k = Real.log k by
        simp [apIndicator, hc]]
      rw [inv_mul_cancel₀ hlk]
    · rw [if_neg hc]
      rw [show apIndicator a k = 0 by
        simp [apIndicator, hc]]
      rw [mul_zero]
  rw [hcount, sum_mul_eq_sub_integral_mul₁ (apIndicator a)
    (apIndicator_zero a) (apIndicator_one a) x hdiff hint,
    apIndicator_sum a x]
  have hIoc : ∫ t in Set.Ioc (2 : ℝ) x,
      deriv (fun u : ℝ => (Real.log u)⁻¹) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apIndicator a k
      = -∫ t in (2 : ℝ)..x, thetaMod a t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_of_le hx, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [apIndicator_sum a t, Real.deriv_inv_log]
    have ht0 : t ≠ 0 := by
      have := ht.1
      linarith
    have hlt : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
        (by linarith [ht.1])
    field_simp
  rw [hIoc]
  ring

/-! ### The tendsto assembly -/

theorem log_mul_integral_div_tendsto_zero {a : ℕ} :
    Tendsto (fun x : ℝ => Real.log x
      * (∫ t in (2 : ℝ)..x, thetaMod a t / (t * Real.log t ^ 2)) / x)
      atTop (nhds 0) := by
  -- dominated by the pin's global little-o
  have hglobal := Chebyshev.integral_theta_div_log_sq_isLittleO
  have hg0 : Tendsto (fun x : ℝ => Real.log x
      * (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) / x)
      atTop (nhds 0) := by
    have h2 := (Asymptotics.isLittleO_iff_tendsto' ?_).mp hglobal
    · apply h2.congr'
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : 0 < Real.log x := Real.log_pos hx
      have hxpos : (0 : ℝ) < x := by linarith
      field_simp
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx h0
      exfalso
      have hlog : 0 < Real.log x := Real.log_pos hx
      have hxpos : (0 : ℝ) < x := by linarith
      have : x / Real.log x ≠ 0 := by positivity
      exact this h0
  have hclass_int : ∀ y : ℝ, IntegrableOn
      (fun t => thetaMod a t / (t * Real.log t ^ 2)) (Set.Icc 2 y) := by
    intro y
    have hrw : (fun t : ℝ => thetaMod a t / (t * Real.log t ^ 2))
        = fun t : ℝ => (t * Real.log t ^ 2)⁻¹
            * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apIndicator a k := by
      funext t
      rw [apIndicator_sum, div_eq_mul_inv, mul_comm]
    rw [hrw]
    refine integrableOn_mul_sum_Icc (c := apIndicator a) (by norm_num) ?_
    refine ContinuousOn.integrableOn_Icc fun z hz => ?_
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have h2 : z * Real.log z ^ 2 ≠ 0 := mul_ne_zero hz0 (pow_ne_zero 2
      (Real.log_ne_zero_of_pos_of_ne_one (by linarith [hz.1])
        (by linarith [hz.1])))
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  apply squeeze_zero_norm' ?_ hg0
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hci : IntervalIntegrable
      (fun t => thetaMod a t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (hclass_int x).mono_set Set.Ioc_subset_Icc_self
  have hgi : IntervalIntegrable
      (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      Set.Ioc_subset_Icc_self
  have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..x,
      thetaMod a t / (t * Real.log t ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have hden : 0 < t * Real.log t ^ 2 := by
      have : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      positivity
    exact div_nonneg (thetaMod_nonneg a t) hden.le
  have hmono : (∫ t in (2 : ℝ)..x, thetaMod a t / (t * Real.log t ^ 2))
      ≤ ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    apply intervalIntegral.integral_mono_on hx hci hgi
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have hden : 0 < t * Real.log t ^ 2 := by
      have : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      positivity
    exact (div_le_div_iff_of_pos_right hden).mpr (thetaMod_le_theta a t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr

/-- **PNT in progressions, counting form** (real variable):
`apCount(a, ⌊x⌋)·log x/x → 1/2` for `a ∈ {1, 5}`. -/
theorem apCount_mul_log_div_tendsto_real {a : ℕ} (ha : a = 1 ∨ a = 5) :
    Tendsto (fun x : ℝ => (apCount a ⌊x⌋₊ : ℝ) * Real.log x / x) atTop
      (nhds (1 / 2 : ℝ)) := by
  have hθ := thetaMod_div_tendsto ha
  have hcorr := log_mul_integral_div_tendsto_zero (a := a)
  have hsum := hθ.add hcorr
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [apCount_eq_thetaMod_div_log_add_integral hx]
  have hlog : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  field_simp

/-- **THE LANDING CONTRACT, DISCHARGED**: for `a ∈ {1, 5}`,
`apCount(a, n)·2·log n/n → 1` — the named hypothesis `hAP` of the
stage-L wing-sign theorems. -/
theorem apCount_mul_log_div_tendsto {a : ℕ} (ha : a = 1 ∨ a = 5) :
    Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
      atTop (nhds 1) := by
  have h := (apCount_mul_log_div_tendsto_real ha).comp
    tendsto_natCast_atTop_atTop
  have h2 := h.const_mul (2 : ℝ)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
  apply h2.congr
  intro n
  simp only [Function.comp_apply, Nat.floor_natCast]
  ring

end Analytic
end EuclidsPath
