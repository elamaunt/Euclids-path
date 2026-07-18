/-
  Analytic/PNTCorollaries — STAGES P-C3/C4 of the Tauberian campaign:
  THE PRIME NUMBER THEOREM and its mod-6 forms, ψ and θ level.

  All are instantiations of the single Newman application (P-C2):
    * `psi_div_tendsto_one` — **PNT, ψ-form**: `ψ(x)/x → 1` (q = 1);
    * `psiRes_six_one` / `psiRes_six_five` — PNT in the progressions
      `1, 5 mod 6` (ψ-form, limit `1/2` each);
    * `thetaRes` and `thetaRes_div_tendsto` — the θ-wing: per-class
      prime-power pruning against the pin's `|ψ − θ| ≤ 2√x·log x`;
    * `theta_div_tendsto_one` — θ-form of PNT.

  The π-form (`apCount`-shape, the landing contract of stage L) is the
  separate Abel-summation module.

  DISCLOSURES.
    * PNT corollaries; no face of the parity wall is touched, and no
      §110 event is claimed (the wall does not move by PNT).
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Analytic.NewmanPsiAP

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Analytic

open Complex ArithmeticFunction Filter MeasureTheory Set
open scoped LSeries.notation

/-! ### C3: the Prime Number Theorem -/

theorem residueClass_zmod_one (n : ℕ) :
    vonMangoldt.residueClass (0 : ZMod 1) n = Λ n := by
  unfold vonMangoldt.residueClass
  rw [Set.indicator_of_mem]
  exact Subsingleton.elim _ _

theorem psiRes_zmod_one (x : ℝ) :
    psiRes (0 : ZMod 1) x = Chebyshev.psi x := by
  unfold psiRes Chebyshev.psi
  rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
  exact Finset.sum_congr rfl fun n _ => residueClass_zmod_one n

/-- **THE PRIME NUMBER THEOREM, ψ-form** (unconditional):
`ψ(x)/x → 1`. -/
theorem psi_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
  have h := psiRes_div_tendsto (q := 1) (a := 0)
    (by exact isUnit_of_subsingleton _)
  simp only [Nat.totient_one, Nat.cast_one, inv_one] at h
  refine h.congr fun x => ?_
  rw [psiRes_zmod_one]

/-! ### C4: PNT mod 6, ψ-form -/

theorem psiRes_six_one :
    Tendsto (fun x : ℝ => psiRes (1 : ZMod 6) x / x) atTop
      (nhds (1 / 2 : ℝ)) := by
  have h := psiRes_div_tendsto (q := 6) (a := 1) (by decide)
  rw [show Nat.totient 6 = 2 from by decide] at h
  norm_num at h
  exact h

theorem psiRes_six_five :
    Tendsto (fun x : ℝ => psiRes (5 : ZMod 6) x / x) atTop
      (nhds (1 / 2 : ℝ)) := by
  have h := psiRes_div_tendsto (q := 6) (a := 5) (by decide)
  rw [show Nat.totient 6 = 2 from by decide] at h
  norm_num at h
  exact h

/-! ### The θ-wing: per-class prime sums -/

/-- The class-restricted Chebyshev θ: `Σ_{p ≤ x prime, p ≡ a} log p`. -/
noncomputable def thetaRes {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
    (fun p => p.Prime ∧ ((p : ℕ) : ZMod q) = a), Real.log p

theorem thetaRes_nonneg {q : ℕ} (a : ZMod q) (x : ℝ) : 0 ≤ thetaRes a x := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact Real.log_nonneg (by exact_mod_cast hp1)

theorem thetaRes_le_psiRes {q : ℕ} (a : ZMod q) (x : ℝ) :
    thetaRes a x ≤ psiRes a x := by
  unfold thetaRes psiRes
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hc : n.Prime ∧ ((n : ℕ) : ZMod q) = a
  · rw [if_pos hc]
    unfold vonMangoldt.residueClass
    rw [Set.indicator_of_mem (by exact hc.2)]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hc.1]
  · rw [if_neg hc]
    exact vonMangoldt.residueClass_nonneg a n

/-- Per-class prime-power pruning: `psiRes − thetaRes ≤ ψ − θ`. -/
theorem psiRes_sub_thetaRes_le {q : ℕ} (a : ZMod q) (x : ℝ) :
    psiRes a x - thetaRes a x ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
    unfold Chebyshev.psi
    rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
  have htheta : Chebyshev.theta x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (if n.Prime then Real.log n else 0) := by
    unfold Chebyshev.theta
    rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega,
      Finset.sum_filter]
  have hth1 : thetaRes a x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (if n.Prime ∧ ((n : ℕ) : ZMod q) = a then Real.log n else 0) := by
    unfold thetaRes
    rw [Finset.sum_filter]
  rw [hpsi, hth1, htheta, psiRes, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hnp : n.Prime
  · by_cases hna : ((n : ℕ) : ZMod q) = a
    · rw [if_pos ⟨hnp, hna⟩, if_pos hnp]
      have h1 := vonMangoldt.residueClass_le a n
      linarith
    · rw [if_neg (fun h => hna h.2), if_pos hnp]
      have h0 : vonMangoldt.residueClass a n = 0 := by
        unfold vonMangoldt.residueClass
        rw [Set.indicator_of_notMem (by exact hna)]
      have hΛ : Λ n = Real.log n :=
        ArithmeticFunction.vonMangoldt_apply_prime hnp
      rw [h0, hΛ]
      simp
  · rw [if_neg (fun h => hnp h.1), if_neg hnp]
    have h1 := vonMangoldt.residueClass_le a n
    linarith

/-- The global comparison dies: `(ψ − θ)/x → 0`. -/
theorem psi_sub_theta_div_tendsto_zero :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x)
      atTop (nhds 0) := by
  apply squeeze_zero_norm'
    (a := fun x : ℝ => 2 * Real.log x / Real.sqrt x)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hsq : Real.sqrt x * Real.sqrt x = x :=
      Real.mul_self_sqrt hxpos.le
    have hsqpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hxpos]
    have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
    rw [div_le_div_iff₀ hxpos hsqpos]
    calc |Chebyshev.psi x - Chebyshev.theta x| * Real.sqrt x
        ≤ (2 * Real.sqrt x * Real.log x) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_right hbound hsqpos.le
      _ = 2 * Real.log x * x := by
          rw [show (2 * Real.sqrt x * Real.log x) * Real.sqrt x
            = 2 * Real.log x * (Real.sqrt x * Real.sqrt x) by ring, hsq]
  · have h := (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => 2 * (Real.log x / x ^ (1 / 2 : ℝ)))
        atTop (nhds 0) := by
      simpa using h.const_mul 2
    apply h2.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow]
    ring

/-- θ-form of PNT in progressions: `thetaRes(a,x)/x → 1/φ(q)`. -/
theorem thetaRes_div_tendsto {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto (fun x : ℝ => thetaRes a x / x) atTop
      (nhds ((Nat.totient q : ℝ)⁻¹)) := by
  have hmid : Tendsto (fun x : ℝ => (psiRes a x - thetaRes a x) / x)
      atTop (nhds 0) := by
    apply squeeze_zero' ?_ ?_ psi_sub_theta_div_tendsto_zero
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (by linarith [thetaRes_le_psiRes a x]) hx.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (div_le_div_iff_of_pos_right hx).mpr
        (psiRes_sub_thetaRes_le a x)
  have h := (psiRes_div_tendsto ha).sub hmid
  rw [sub_zero] at h
  refine h.congr fun x => ?_
  ring

/-- **PNT, θ-form**: `θ(x)/x → 1`. -/
theorem theta_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
  have h := psi_div_tendsto_one.sub psi_sub_theta_div_tendsto_zero
  rw [sub_zero] at h
  refine h.congr fun x => ?_
  ring

theorem thetaRes_six_one :
    Tendsto (fun x : ℝ => thetaRes (1 : ZMod 6) x / x) atTop
      (nhds (1 / 2 : ℝ)) := by
  have h := thetaRes_div_tendsto (q := 6) (a := 1) (by decide)
  rw [show Nat.totient 6 = 2 from by decide] at h
  norm_num at h
  exact h

theorem thetaRes_six_five :
    Tendsto (fun x : ℝ => thetaRes (5 : ZMod 6) x / x) atTop
      (nhds (1 / 2 : ℝ)) := by
  have h := thetaRes_div_tendsto (q := 6) (a := 5) (by decide)
  rw [show Nat.totient 6 = 2 from by decide] at h
  norm_num at h
  exact h

end Analytic
end EuclidsPath
