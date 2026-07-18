/-
  Engine/GeometricTypeIIWingSignSharp — the SHARP-CONSTANT pass on the
  wing sign crowns: `log 4` → `1 + ε`.

  The M3/plus crowns capped the slice Mertens sums by the pin's
  unconditional Chebyshev constant `log 4 ≈ 1.386`.  The campaign's own
  PNT (`theta_div_tendsto_one`, stage P-C3) gives the EVENTUAL cap
  `θ(u) ≤ (1+ε)·u` on every slice window — the SAME parametric M2
  machinery instantiated at `c = 1+ε` sharpens the margin constant from
  `wingK ≤ 0.925` (log-4 grade) to the PURE RATIONAL
  `wingKSharp = Σ_i 80/((49−2i)(14+i)) ≤ 0.668`, and the crowns from
  `−(1/40)·X/log X` to

      Σ_{window} λ(6m±1)  ≤  −(1/8)·X/log X.

  This DISCHARGES the "sharper constants are named, unclaimed work"
  item of the M3 disclosures — for the CHEBYSHEV grade of the constant.
  The true first-order constant `log((1−θ)/θ)` per θ-slice (a genuinely
  two-sided Mertens asymptotic with exact slicing limits) remains
  unclaimed, as does any second-order refinement.

  DISCLOSURES (the campaign frame, verbatim):
    * OneWingTarget is NOT discharged, NOT premise-shrunk, NOT
      reweighted (twin-strength by pigeonhole; three bridges refuted);
      the surviving open core is the PAIR-rough two-wing coupling.
    * EVENTUAL, NOT EFFECTIVE.  NOT a §110 event.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTypeIIPlusWing
import EuclidsPath.Analytic.PNTCorollaries

set_option maxHeartbeats 3200000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction Filter
open EuclidsPath.Analytic (apCount)

/-! ### The eventual Chebyshev cap from the campaign's PNT -/

theorem theta_cap_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ (1 + ε) * x := by
  have hev := Metric.tendsto_nhds.mp
    EuclidsPath.Analytic.theta_div_tendsto_one ε hε
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.dist_eq, abs_lt] at hx
  have h1 : Chebyshev.theta x / x < 1 + ε := by linarith [hx.2]
  calc Chebyshev.theta x = (Chebyshev.theta x / x) * x := by
        field_simp
    _ ≤ (1 + ε) * x := mul_le_mul_of_nonneg_right h1.le hx0.le

/-! ### The sharp slice Mertens cap -/

/-- The sharp slice cap: any eventual Chebyshev cap `θ(u) ≤ c·u` above
the slice floor `X^{14/40}` caps slice `i` by `c/(14+i)` plus the
boundary term — the parametric M2 difference at `c` instead of `log 4`. -/
theorem slice_inv_sum_le_sharp {X z i : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hXbig : 2 ^ 80 ≤ X) (_hi : i < 6)
    (hθ : ∀ u : ℝ, (X : ℝ) ^ ((14 : ℝ) / 40) ≤ u →
      Chebyshev.theta u ≤ c * u) :
    ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹
      ≤ c * (1 / (14 + i : ℝ))
        + 2 * c * (40 / ((14 + i : ℝ) * Real.log X)) := by
  have hX : 2 ≤ X := le_trans (by norm_num) hXbig
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
    have h2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogX : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast hX)
  set s : ℝ := (X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40) with hsdef
  set t : ℝ := (X : ℝ) ^ (((15 + i : ℕ) : ℝ) / 40) with htdef
  have hlogs : Real.log s = ((14 + i : ℕ) : ℝ) / 40 * Real.log X := by
    rw [hsdef, Real.log_rpow hX0]
  have hlogt : Real.log t = ((15 + i : ℕ) : ℝ) / 40 * Real.log X := by
    rw [htdef, Real.log_rpow hX0]
  have h280 : ((2 : ℝ) ^ (80 : ℝ)) = ((2 ^ 80 : ℕ) : ℝ) := by
    rw [show (80 : ℝ) = ((80 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num
  have hs2 : (2 : ℝ) ≤ s := by
    rw [hsdef]
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((80 : ℝ) * (((14 + i : ℕ) : ℝ) / 40)) := by
          apply (Real.rpow_le_rpow_left_iff (by norm_num)).mpr
          have h14 : (14 : ℝ) ≤ ((14 + i : ℕ) : ℝ) := by push_cast; linarith
          nlinarith
      _ = ((2 : ℝ) ^ (80 : ℝ)) ^ (((14 + i : ℕ) : ℝ) / 40) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (X : ℝ) ^ (((14 + i : ℕ) : ℝ) / 40) := by
          apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [h280]
          exact_mod_cast hXbig
  have hst : s ≤ t := by
    rw [hsdef, htdef]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have : ((14 + i : ℕ) : ℝ) ≤ ((15 + i : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hfloor_s : (X : ℝ) ^ ((14 : ℝ) / 40) ≤ s := by
    rw [hsdef]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have : (14 : ℝ) ≤ ((14 + i : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hsub := slice_subset_Ioc (X := X) (z := z) (i := i) hX
  have hmono : ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹
      ≤ ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => by positivity)
  have hM2 := sum_inv_primes_Ioc_le hs2 hst hc0
    (fun u hu _ => hθ u (le_trans hfloor_s hu))
  have hratio : Real.log t / Real.log s
      = ((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ) := by
    rw [hlogs, hlogt]
    have h14 : ((14 + i : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
    field_simp
  have hlog_ratio : Real.log (Real.log t / Real.log s) ≤ 1 / (14 + i : ℝ) := by
    rw [hratio]
    have h14pos : (0 : ℝ) < ((14 + i : ℕ) : ℝ) := by push_cast; linarith
    have hratpos : (0 : ℝ) < ((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ) := by
      positivity
    calc Real.log (((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ))
        ≤ ((15 + i : ℕ) : ℝ) / ((14 + i : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hratpos
      _ = 1 / ((14 + i : ℕ) : ℝ) := by
          field_simp
          push_cast
          ring
      _ = 1 / (14 + i : ℝ) := by push_cast; ring
  have hlogs_inv : 2 * c / Real.log s
      = 2 * c * (40 / (((14 + i : ℕ) : ℝ) * Real.log X)) := by
    rw [hlogs]
    have h14 : ((14 + i : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
    field_simp
  calc ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹
      ≤ ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹ := hmono
    _ ≤ c * Real.log (Real.log t / Real.log s) + 2 * c / Real.log s := hM2
    _ ≤ c * (1 / (14 + i : ℝ))
        + 2 * c * (40 / ((14 + i : ℝ) * Real.log X)) := by
        have h1 := mul_le_mul_of_nonneg_left hlog_ratio hc0
        rw [hlogs_inv]
        have hpush : (((14 + i : ℕ) : ℝ)) = (14 + i : ℝ) := by push_cast; ring
        rw [hpush]
        linarith

/-! ### The sharp margin constant (pure rational) -/

/-- The sharp wing margin constant: `Σ_{i<6} 80/((49−2i)(14+i)) ≈ 0.667`
— NO Chebyshev inflation, no logarithms. -/
noncomputable def wingKSharp : ℝ :=
  ∑ i ∈ Finset.range 6, (80 / (49 - 2 * (i : ℝ))) * (1 / (14 + (i : ℝ)))

theorem wingKSharp_nonneg : 0 ≤ wingKSharp := by
  unfold wingKSharp
  apply Finset.sum_nonneg
  intro i hi
  have hi5 : (i : ℝ) ≤ 5 := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h49 : (0 : ℝ) < 49 - 2 * (i : ℝ) := by linarith
  apply mul_nonneg (div_nonneg (by norm_num) h49.le)
  positivity

theorem wingKSharp_le : wingKSharp ≤ 0.668 := by
  unfold wingKSharp
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

/-! ### The sharp rung-sum cap -/

theorem rung_sum_le_sharp {X z : ℕ} {ε c : ℝ} (cf : ℕ → ℕ)
    (hcf : ∀ p : ℕ, cf p = 1 ∨ cf p = 5)
    (hε : 0 < ε) (hc0 : 0 ≤ c) (hXbig : 2 ^ 80 ≤ X)
    (h14 : X ^ 14 ≤ z ^ 40)
    (hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + ε) * m)
    (hθ : ∀ u : ℝ, (X : ℝ) ^ ((14 : ℝ) / 40) ≤ u →
      Chebyshev.theta u ≤ c * u) :
    ∑ p ∈ rungPrimes X z, (apCount (cf p) (X / p) : ℝ)
      ≤ (1 + ε) * ((X : ℝ) / (2 * Real.log X)) * (c * wingKSharp)
          * (1 + 80 / Real.log X) := by
  have hX : 2 ≤ X := le_trans (by norm_num) hXbig
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hdisj : (↑(Finset.range 6) : Set ℕ).PairwiseDisjoint
      (fun i => rungSlice X z i) := by
    intro i hi j hj hij
    exact slices_disjoint hX i (Finset.mem_coe.mp hi) j
      (Finset.mem_coe.mp hj) hij
  rw [rungPrimes_eq_biUnion_slices hX h14, Finset.sum_biUnion hdisj]
  have hper : ∀ i ∈ Finset.range 6,
      ∑ p ∈ rungSlice X z i, (apCount (cf p) (X / p) : ℝ)
        ≤ ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * c
              * (1 + 80 / Real.log X))
            * ((80 / (49 - 2 * (i : ℝ))) * (1 / (14 + (i : ℝ)))) := by
    intro i hi
    have hi6 : i < 6 := Finset.mem_range.mp hi
    have hi5 : (i : ℝ) ≤ 5 := by exact_mod_cast Nat.lt_succ_iff.mp hi6
    have h49 : (0 : ℝ) < 49 - 2 * (i : ℝ) := by linarith
    have hstep1 : ∑ p ∈ rungSlice X z i, (apCount (cf p) (X / p) : ℝ)
        ≤ ∑ p ∈ rungSlice X z i, (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
            * ((X : ℝ) / ((p : ℝ) * (2 * Real.log X))) :=
      Finset.sum_le_sum fun p hp =>
        slice_apCount_le hε hXbig hi6 (hcf p) hup hp
    have hstep2 : ∑ p ∈ rungSlice X z i, (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
          * ((X : ℝ) / ((p : ℝ) * (2 * Real.log X)))
        = ((1 + ε) * (80 / (49 - 2 * (i : ℝ)))
            * ((X : ℝ) / (2 * Real.log X)))
          * ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    have hD0 : (0 : ℝ) ≤ (1 + ε) * (80 / (49 - 2 * (i : ℝ)))
        * ((X : ℝ) / (2 * Real.log X)) := by
      apply mul_nonneg (mul_nonneg (by linarith)
        (div_nonneg (by norm_num) h49.le))
      positivity
    have hstep3 := slice_inv_sum_le_sharp (X := X) (z := z) (i := i)
      hc0 hXbig hi6 hθ
    calc ∑ p ∈ rungSlice X z i, (apCount (cf p) (X / p) : ℝ)
        ≤ ((1 + ε) * (80 / (49 - 2 * (i : ℝ)))
              * ((X : ℝ) / (2 * Real.log X)))
            * ∑ p ∈ rungSlice X z i, ((p : ℝ))⁻¹ := by
          rw [← hstep2]
          exact hstep1
      _ ≤ ((1 + ε) * (80 / (49 - 2 * (i : ℝ)))
              * ((X : ℝ) / (2 * Real.log X)))
            * (c * (1 / (14 + i : ℝ))
                + 2 * c * (40 / ((14 + i : ℝ) * Real.log X))) :=
          mul_le_mul_of_nonneg_left hstep3 hD0
      _ = ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * c
              * (1 + 80 / Real.log X))
            * ((80 / (49 - 2 * (i : ℝ))) * (1 / (14 + (i : ℝ)))) := by
          have h14ne : (14 + (i : ℝ)) ≠ 0 := by positivity
          field_simp [h49.ne', hlogX.ne']
          ring
  calc ∑ i ∈ Finset.range 6, ∑ p ∈ rungSlice X z i,
        (apCount (cf p) (X / p) : ℝ)
      ≤ ∑ i ∈ Finset.range 6,
          ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * c
              * (1 + 80 / Real.log X))
            * ((80 / (49 - 2 * (i : ℝ))) * (1 / (14 + (i : ℝ)))) :=
        Finset.sum_le_sum hper
    _ = ((1 + ε) * ((X : ℝ) / (2 * Real.log X)) * c
          * (1 + 80 / Real.log X)) * wingKSharp := by
        rw [← Finset.mul_sum]
        rfl
    _ = (1 + ε) * ((X : ℝ) / (2 * Real.log X)) * (c * wingKSharp)
          * (1 + 80 / Real.log X) := by ring

/-! ### THE SHARP CROWNS -/

/-- **THE SHARP MINUS CROWN (unconditional)**: the wing sign with the
PNT-grade constant — `Σλ ≤ −(1/8)·X/log X` (five times the `log 4`
margin of `minus_wing_sign`). -/
theorem minus_wing_sign_sharp :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ minusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
        ≤ -(1 / 8) * X / Real.log X := by
  have hAP : ∀ a : ℕ, a = 1 ∨ a = 5 →
      Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
        atTop (nhds 1) := fun _ ha =>
    EuclidsPath.Analytic.apCount_mul_log_div_tendsto ha
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (interface_bounds (hAP 1 (Or.inl rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp
    (interface_bounds (hAP 5 (Or.inr rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp
    (theta_cap_eventually (by norm_num : (0 : ℝ) < 1 / 1000))
  have hlogT : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hUev : ∀ᶠ X : ℕ in atTop, U₀ ≤ (X : ℝ) ^ ((14 : ℝ) / 40) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 14 / 40)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop U₀
  have hzsm : ∀ᶠ n : ℕ in atTop,
      Real.log n / (n : ℝ) ^ ((11 : ℝ) / 20) ≤ 1 / 200 := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ((11 : ℝ) / 20))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.comp tendsto_natCast_atTop_atTop
    have h3 := Metric.tendsto_nhds.mp h2 (1 / 200) (by norm_num)
    filter_upwards [h3] with n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hn
    exact hn.2.le
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (2 ^ 80),
    eventually_ge_atTop N₅, eventually_ge_atTop ((max N₁ N₅ + 2) ^ 3),
    hlogT.eventually_ge_atTop 8000, hzsm, hUev]
    with X h2X hbig hN5X hNc h8000 hzs hU14
  intro z h7 h9
  obtain ⟨hz2, hXz3, hzzX, h14⟩ := z_facts h2X h7 h9
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast h2X)
  have hzN : max N₁ N₅ + 2 ≤ z := by
    have h1 : (max N₁ N₅ + 2) ^ 20 ≤ z ^ 20 := by
      calc (max N₁ N₅ + 2) ^ 20
          ≤ (max N₁ N₅ + 2) ^ 21 :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ = ((max N₁ N₅ + 2) ^ 3) ^ 7 := by ring
        _ ≤ X ^ 7 := Nat.pow_le_pow_left hNc 7
        _ ≤ z ^ 20 := h7
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + 1 / 1000) * m := by
    intro a ha m hzm
    rcases ha with rfl | rfl
    · exact (hN₁ m (by have := le_max_left N₁ N₅; omega)).2
    · exact (hN₅ m (by have := le_max_right N₁ N₅; omega)).2
  have hθcap : ∀ u : ℝ, (X : ℝ) ^ ((14 : ℝ) / 40) ≤ u →
      Chebyshev.theta u ≤ (1 + 1 / 1000) * u :=
    fun u hu => hU₀ u (le_trans hU14 hu)
  have hsum := minusWindow_liouville_eq (X := X) (z := z) (by omega) hXz3
  have hsumR : ((∑ m ∈ minusRoughWindow X z,
        ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
      = (wingS X z : ℝ) - (wingP X z : ℝ) := by
    rw [hsum]
    push_cast
    ring
  have hzX : z ≤ X := by
    calc z = z * 1 := by ring
      _ ≤ z * z := Nat.mul_le_mul_left z (by omega)
      _ ≤ X := hzzX
  have hPcast : (wingP X z : ℝ) = (apCount 5 X : ℝ) - (apCount 5 z : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (wingP_add_apCount (X := X) (z := z) hzX)
    push_cast at h
    linarith
  have hP5X : (1 - 1 / 1000) * X / (2 * Real.log X) ≤ (apCount 5 X : ℝ) :=
    apCount_lower_of_bound (hN₅ X hN5X).1 h2X
  have hz_apc : (apCount 5 z : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast apCount_le 5 z
  have hzrpow : (z : ℝ) ≤ (X : ℝ) ^ ((9 : ℝ) / 20) := by
    have h40 : ((X : ℝ) ^ ((9 : ℝ) / 20)) ^ (20 : ℕ) = (X : ℝ) ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ ((9 : ℝ) / 20)) 20,
        ← Real.rpow_mul hX0.le,
        show (((20 : ℕ) : ℝ)) = (20 : ℝ) from by norm_num,
        div_mul_cancel₀ _ (by norm_num : (20 : ℝ) ≠ 0),
        show ((9 : ℝ)) = (((9 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast]
    have hc : ((z : ℝ)) ^ (20 : ℕ) ≤ ((X : ℝ)) ^ (9 : ℕ) := by
      exact_mod_cast h9
    rw [← h40] at hc
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hX0.le _) hc
  have hzterm : (z : ℝ) ≤ (1 / 100) * ((X : ℝ) / (2 * Real.log X)) := by
    have hrp : (0 : ℝ) < (X : ℝ) ^ ((11 : ℝ) / 20) := by positivity
    have h200 : 200 * Real.log X ≤ (X : ℝ) ^ ((11 : ℝ) / 20) := by
      rw [div_le_iff₀ hrp] at hzs
      linarith
    have hsplit : (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20)
        = (X : ℝ) := by
      rw [← Real.rpow_add hX0,
        show (9 : ℝ) / 20 + 11 / 20 = 1 from by norm_num, Real.rpow_one]
    have hmul : (z : ℝ) * (200 * Real.log X) ≤ (X : ℝ) := by
      calc (z : ℝ) * (200 * Real.log X)
          ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (200 * Real.log X) :=
            mul_le_mul_of_nonneg_right hzrpow (by positivity)
        _ ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20) :=
            mul_le_mul_of_nonneg_left h200 (by positivity)
        _ = (X : ℝ) := hsplit
    rw [show (1 / 100 : ℝ) * ((X : ℝ) / (2 * Real.log X))
      = (X : ℝ) / (200 * Real.log X) from by ring]
    rw [le_div_iff₀ (by positivity)]
    exact hmul
  have hScast : (wingS X z : ℝ)
      ≤ ∑ p ∈ rungPrimes X z, (apCount (rungClass p) (X / p) : ℝ) := by
    have h := wingS_le_rung_sum (X := X) (z := z)
    calc (wingS X z : ℝ)
        ≤ ((∑ p ∈ rungPrimes X z, apCount (rungClass p) (X / p) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = ∑ p ∈ rungPrimes X z, (apCount (rungClass p) (X / p) : ℝ) := by
          push_cast
          rfl
  have hSup := rung_sum_le_sharp (X := X) (z := z) rungClass rungClass_or
    (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000) hbig h14 hup hθcap
  have h80 : 80 / Real.log X ≤ 1 / 100 := by
    rw [div_le_iff₀ hlogX]
    linarith
  have h80pos : (0 : ℝ) ≤ 80 / Real.log X := by positivity
  have hprod : (1 + 1 / 1000)
      * (((1 + 1 / 1000) * wingKSharp) * (1 + 80 / Real.log X)) ≤ 0.68 := by
    have hb1 : ((1 + 1 / 1000) * wingKSharp) * (1 + 80 / Real.log X)
        ≤ ((1 + 1 / 1000) * 0.668) * (1 + 1 / 100) := by
      apply mul_le_mul
      · have := wingKSharp_le
        nlinarith
      · linarith
      · linarith
      · nlinarith [wingKSharp_nonneg]
    nlinarith
  have hA0 : (0 : ℝ) ≤ (X : ℝ) / (2 * Real.log X) := by positivity
  have hSfinal : (wingS X z : ℝ)
      ≤ 0.68 * ((X : ℝ) / (2 * Real.log X)) := by
    calc (wingS X z : ℝ)
        ≤ (1 + 1 / 1000) * ((X : ℝ) / (2 * Real.log X))
            * ((1 + 1 / 1000) * wingKSharp)
            * (1 + 80 / Real.log X) := hScast.trans hSup
      _ = ((X : ℝ) / (2 * Real.log X))
            * ((1 + 1 / 1000)
              * (((1 + 1 / 1000) * wingKSharp) * (1 + 80 / Real.log X))) := by
          ring
      _ ≤ ((X : ℝ) / (2 * Real.log X)) * 0.68 :=
          mul_le_mul_of_nonneg_left hprod hA0
      _ = 0.68 * ((X : ℝ) / (2 * Real.log X)) := by ring
  have hPfinal : 0.989 * ((X : ℝ) / (2 * Real.log X)) ≤ (wingP X z : ℝ) := by
    have h999 : (1 - 1 / 1000) * X / (2 * Real.log X)
        = 0.999 * ((X : ℝ) / (2 * Real.log X)) := by ring
    rw [hPcast]
    rw [h999] at hP5X
    linarith
  rw [hsumR]
  have hfin : (wingS X z : ℝ) - (wingP X z : ℝ)
      ≤ -(1 / 4) * ((X : ℝ) / (2 * Real.log X)) := by linarith
  calc (wingS X z : ℝ) - (wingP X z : ℝ)
      ≤ -(1 / 4) * ((X : ℝ) / (2 * Real.log X)) := hfin
    _ = -(1 / 8) * X / Real.log X := by ring

/-- **THE SHARP PLUS CROWN (unconditional)** — the `6m+1` mirror. -/
theorem plus_wing_sign_sharp :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ plusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
        ≤ -(1 / 8) * X / Real.log X := by
  have hAP : ∀ a : ℕ, a = 1 ∨ a = 5 →
      Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
        atTop (nhds 1) := fun _ ha =>
    EuclidsPath.Analytic.apCount_mul_log_div_tendsto ha
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (interface_bounds (hAP 1 (Or.inl rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp
    (interface_bounds (hAP 5 (Or.inr rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp
    (theta_cap_eventually (by norm_num : (0 : ℝ) < 1 / 1000))
  have hlogT : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hUev : ∀ᶠ X : ℕ in atTop, U₀ ≤ (X : ℝ) ^ ((14 : ℝ) / 40) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 14 / 40)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop U₀
  have hzsm : ∀ᶠ n : ℕ in atTop,
      Real.log n / (n : ℝ) ^ ((11 : ℝ) / 20) ≤ 1 / 200 := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ((11 : ℝ) / 20))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.comp tendsto_natCast_atTop_atTop
    have h3 := Metric.tendsto_nhds.mp h2 (1 / 200) (by norm_num)
    filter_upwards [h3] with n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hn
    exact hn.2.le
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (2 ^ 80),
    eventually_ge_atTop N₁, eventually_ge_atTop ((max N₁ N₅ + 2) ^ 3),
    hlogT.eventually_ge_atTop 8000, hzsm, hUev]
    with X h2X hbig hN1X hNc h8000 hzs hU14
  intro z h7 h9
  obtain ⟨hz2, hXz3, hzzX, h14⟩ := z_facts h2X h7 h9
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast h2X)
  have hzN : max N₁ N₅ + 2 ≤ z := by
    have h1 : (max N₁ N₅ + 2) ^ 20 ≤ z ^ 20 := by
      calc (max N₁ N₅ + 2) ^ 20
          ≤ (max N₁ N₅ + 2) ^ 21 :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ = ((max N₁ N₅ + 2) ^ 3) ^ 7 := by ring
        _ ≤ X ^ 7 := Nat.pow_le_pow_left hNc 7
        _ ≤ z ^ 20 := h7
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + 1 / 1000) * m := by
    intro a ha m hzm
    rcases ha with rfl | rfl
    · exact (hN₁ m (by have := le_max_left N₁ N₅; omega)).2
    · exact (hN₅ m (by have := le_max_right N₁ N₅; omega)).2
  have hθcap : ∀ u : ℝ, (X : ℝ) ^ ((14 : ℝ) / 40) ≤ u →
      Chebyshev.theta u ≤ (1 + 1 / 1000) * u :=
    fun u hu => hU₀ u (le_trans hU14 hu)
  have hsum := plusWindow_liouville_eq (X := X) (z := z) (by omega) hXz3
  have hsumR : ((∑ m ∈ plusRoughWindow X z,
        ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
      = (plusWingS X z : ℝ) - (plusWingP X z : ℝ) := by
    rw [hsum]
    push_cast
    ring
  have hzX : z ≤ X := by
    calc z = z * 1 := by ring
      _ ≤ z * z := Nat.mul_le_mul_left z (by omega)
      _ ≤ X := hzzX
  have hPcast : (plusWingP X z : ℝ)
      = (apCount 1 X : ℝ) - (apCount 1 z : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (plusWingP_add_apCount (X := X) (z := z) hzX)
    push_cast at h
    linarith
  have hP1X : (1 - 1 / 1000) * X / (2 * Real.log X) ≤ (apCount 1 X : ℝ) :=
    apCount_lower_of_bound (hN₁ X hN1X).1 h2X
  have hz_apc : (apCount 1 z : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast apCount_le 1 z
  have hzrpow : (z : ℝ) ≤ (X : ℝ) ^ ((9 : ℝ) / 20) := by
    have h40 : ((X : ℝ) ^ ((9 : ℝ) / 20)) ^ (20 : ℕ) = (X : ℝ) ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ ((9 : ℝ) / 20)) 20,
        ← Real.rpow_mul hX0.le,
        show (((20 : ℕ) : ℝ)) = (20 : ℝ) from by norm_num,
        div_mul_cancel₀ _ (by norm_num : (20 : ℝ) ≠ 0),
        show ((9 : ℝ)) = (((9 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast]
    have hc : ((z : ℝ)) ^ (20 : ℕ) ≤ ((X : ℝ)) ^ (9 : ℕ) := by
      exact_mod_cast h9
    rw [← h40] at hc
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hX0.le _) hc
  have hzterm : (z : ℝ) ≤ (1 / 100) * ((X : ℝ) / (2 * Real.log X)) := by
    have hrp : (0 : ℝ) < (X : ℝ) ^ ((11 : ℝ) / 20) := by positivity
    have h200 : 200 * Real.log X ≤ (X : ℝ) ^ ((11 : ℝ) / 20) := by
      rw [div_le_iff₀ hrp] at hzs
      linarith
    have hsplit : (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20)
        = (X : ℝ) := by
      rw [← Real.rpow_add hX0,
        show (9 : ℝ) / 20 + 11 / 20 = 1 from by norm_num, Real.rpow_one]
    have hmul : (z : ℝ) * (200 * Real.log X) ≤ (X : ℝ) := by
      calc (z : ℝ) * (200 * Real.log X)
          ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (200 * Real.log X) :=
            mul_le_mul_of_nonneg_right hzrpow (by positivity)
        _ ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20) :=
            mul_le_mul_of_nonneg_left h200 (by positivity)
        _ = (X : ℝ) := hsplit
    rw [show (1 / 100 : ℝ) * ((X : ℝ) / (2 * Real.log X))
      = (X : ℝ) / (200 * Real.log X) from by ring]
    rw [le_div_iff₀ (by positivity)]
    exact hmul
  have hScast : (plusWingS X z : ℝ)
      ≤ ∑ p ∈ rungPrimes X z, (apCount (plusRungClass p) (X / p) : ℝ) := by
    have h := plusWingS_le_rung_sum (X := X) (z := z)
    calc (plusWingS X z : ℝ)
        ≤ ((∑ p ∈ rungPrimes X z,
            apCount (plusRungClass p) (X / p) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = ∑ p ∈ rungPrimes X z, (apCount (plusRungClass p) (X / p) : ℝ) := by
          push_cast
          rfl
  have hSup := rung_sum_le_sharp (X := X) (z := z) plusRungClass
    plusRungClass_or (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000) hbig h14 hup hθcap
  have h80 : 80 / Real.log X ≤ 1 / 100 := by
    rw [div_le_iff₀ hlogX]
    linarith
  have h80pos : (0 : ℝ) ≤ 80 / Real.log X := by positivity
  have hprod : (1 + 1 / 1000)
      * (((1 + 1 / 1000) * wingKSharp) * (1 + 80 / Real.log X)) ≤ 0.68 := by
    have hb1 : ((1 + 1 / 1000) * wingKSharp) * (1 + 80 / Real.log X)
        ≤ ((1 + 1 / 1000) * 0.668) * (1 + 1 / 100) := by
      apply mul_le_mul
      · have := wingKSharp_le
        nlinarith
      · linarith
      · linarith
      · nlinarith [wingKSharp_nonneg]
    nlinarith
  have hA0 : (0 : ℝ) ≤ (X : ℝ) / (2 * Real.log X) := by positivity
  have hSfinal : (plusWingS X z : ℝ)
      ≤ 0.68 * ((X : ℝ) / (2 * Real.log X)) := by
    calc (plusWingS X z : ℝ)
        ≤ (1 + 1 / 1000) * ((X : ℝ) / (2 * Real.log X))
            * ((1 + 1 / 1000) * wingKSharp)
            * (1 + 80 / Real.log X) := hScast.trans hSup
      _ = ((X : ℝ) / (2 * Real.log X))
            * ((1 + 1 / 1000)
              * (((1 + 1 / 1000) * wingKSharp) * (1 + 80 / Real.log X))) := by
          ring
      _ ≤ ((X : ℝ) / (2 * Real.log X)) * 0.68 :=
          mul_le_mul_of_nonneg_left hprod hA0
      _ = 0.68 * ((X : ℝ) / (2 * Real.log X)) := by ring
  have hPfinal : 0.989 * ((X : ℝ) / (2 * Real.log X))
      ≤ (plusWingP X z : ℝ) := by
    have h999 : (1 - 1 / 1000) * X / (2 * Real.log X)
        = 0.999 * ((X : ℝ) / (2 * Real.log X)) := by ring
    rw [hPcast]
    rw [h999] at hP1X
    linarith
  rw [hsumR]
  have hfin : (plusWingS X z : ℝ) - (plusWingP X z : ℝ)
      ≤ -(1 / 4) * ((X : ℝ) / (2 * Real.log X)) := by linarith
  calc (plusWingS X z : ℝ) - (plusWingP X z : ℝ)
      ≤ -(1 / 4) * ((X : ℝ) / (2 * Real.log X)) := hfin
    _ = -(1 / 8) * X / Real.log X := by ring

/-- The sharp two-wing display.  DISCLOSURE: different `m`-sets per
wing — NOT the OneWingTarget form (pair-rough coupling open). -/
theorem two_wing_sign_sharp :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ minusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
        ≤ -(1 / 8) * X / Real.log X
      ∧ ((∑ m ∈ plusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
        ≤ -(1 / 8) * X / Real.log X := by
  filter_upwards [minus_wing_sign_sharp, plus_wing_sign_sharp] with X h1 h2
  intro z h7 h9
  exact ⟨h1 z h7 h9, h2 z h7 h9⟩

end TypeII
end Geometric
end EuclidsPath
