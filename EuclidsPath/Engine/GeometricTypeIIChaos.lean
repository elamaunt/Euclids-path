/-
  GeometricTypeIIChaos — the prime-chaos decomposition and the critical S₂/S₄ threshold.

  ORIGIN (parity_wall Prime-Chaos session dossier §18 / §19 / §20 / §21). The global survivor
  operator is a CRT tensor product `T_Q = ⊗_p T_p`; decomposing each local space as
  `ℂ·𝟙 ⊕ H_p⁰` gives the prime-chaos layers `H_S` (`S ⊆ 𝒫`) with `dim H_S = ∏_{p∈S}(p−2)` and
  relative eigenvalue `θ_S = (−1)^{|S|}/∏_{p∈S}(p−2)`.  The Schatten `r`-mass is the exact
  subset-sum-to-product identity `Σ_S dim H_S |θ_S|^r = ∏_{p|Q}(1 + (p−2)^{-(r−1)})`.  At the
  parity level `r = 2` this is `∏(1 + 1/(p−2))`, which is UNBOUNDED (dominates the divergent
  `Σ 1/(p−2)`); at `r = 4` it is `∏(1 + 1/(p−2)³)`, which is UNIFORMLY BOUNDED.  So the quadratic
  level sits exactly on the parity boundary and the fourth moment has a summable local budget.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `schatten_powerset` — the decomposition identity `∏(1 + a_p) = Σ_{S} ∏_{p∈S} a_p` (§19/§20);
    * `dim_theta_sq` / `dim_theta_fourth` — `dim H_S · θ_S^{2},θ_S^{4}` factor per prime;
    * `schatten_S2_spectral` / `schatten_S4_spectral` — the spectral sums equal the products (§21);
    * `schatten_S2_lower` — `1 + Σ 1/(p−2) ≤ ∏(1 + 1/(p−2))`: S₂ dominates the divergent partial
      sum, hence is UNBOUNDED (§21);
    * `schatten_S4_bounded` — `∏(1 + 1/(p−2)³) ≤ exp(1/2)`: S₄ is UNIFORMLY BOUNDED (§21).

  DISCLOSURE. The threshold is a wall marker: the quadratic (parity) level does not close, the
  quartic level does — but neither breaks the wall by itself (§27). twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The prime-chaos decomposition identity (§19/§20) -/

/-- **Prime-chaos decomposition (§19/§20).** `∏_{p∈P} (1 + a_p) = Σ_{S ⊆ P} ∏_{p∈S} a_p`. -/
theorem schatten_powerset (P : Finset ℕ) (a : ℕ → ℝ) :
    ∏ p ∈ P, (1 + a p) = ∑ S ∈ P.powerset, ∏ p ∈ S, a p := by
  rw [Finset.prod_congr rfl (fun p _ => add_comm (1 : ℝ) (a p)),
    Finset.prod_add a (fun _ => (1 : ℝ)) P]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_const_one, mul_one]

/-! ## Layer dimensions and eigenvalues (§19) -/

/-- The prime-chaos layer dimension `dim H_S = ∏_{p∈S}(p−2)`. -/
noncomputable def dimHS (S : Finset ℕ) : ℝ := ∏ p ∈ S, ((p : ℝ) - 2)

/-- The relative layer eigenvalue `θ_S = (−1)^{|S|}/∏_{p∈S}(p−2)`. -/
noncomputable def thetaS (S : Finset ℕ) : ℝ := (-1) ^ (S.card) / ∏ p ∈ S, ((p : ℝ) - 2)

private theorem prod_sub_two_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, 5 ≤ p) :
    ∏ p ∈ S, ((p : ℝ) - 2) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hS p hp
  intro h; linarith

/-- `dim H_S · θ_S² = ∏_{p∈S} 1/(p−2)`. -/
theorem dim_theta_sq {S : Finset ℕ} (hS : ∀ p ∈ S, 5 ≤ p) :
    dimHS S * (thetaS S) ^ 2 = ∏ p ∈ S, 1 / ((p : ℝ) - 2) := by
  have hne := prod_sub_two_ne_zero hS
  have hsq : ((-1 : ℝ) ^ (S.card)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold dimHS thetaS
  rw [Finset.prod_div_distrib, Finset.prod_const_one, div_pow, hsq,
    mul_one_div, pow_two, ← div_div, div_self hne]

/-- `dim H_S · θ_S⁴ = ∏_{p∈S} 1/(p−2)³`. -/
theorem dim_theta_fourth {S : Finset ℕ} (hS : ∀ p ∈ S, 5 ≤ p) :
    dimHS S * (thetaS S) ^ 4 = ∏ p ∈ S, 1 / ((p : ℝ) - 2) ^ 3 := by
  have hne := prod_sub_two_ne_zero hS
  unfold dimHS thetaS
  rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow, div_pow]
  have h1 : ((-1 : ℝ) ^ (S.card)) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h1]
  field_simp

/-! ## The spectral sums are the products (§21) -/

/-- **S₂ spectral identity (§21).** `Σ_S dim H_S θ_S² = ∏(1 + 1/(p−2))`. -/
theorem schatten_S2_spectral {P : Finset ℕ} (hP : ∀ p ∈ P, 5 ≤ p) :
    ∑ S ∈ P.powerset, dimHS S * (thetaS S) ^ 2 = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2)) := by
  rw [Finset.sum_congr rfl
    (fun S hS => dim_theta_sq (fun p hp => hP p (Finset.mem_powerset.mp hS hp)))]
  exact (schatten_powerset P (fun p => 1 / ((p : ℝ) - 2))).symm

/-- **S₄ spectral identity (§21).** `Σ_S dim H_S θ_S⁴ = ∏(1 + 1/(p−2)³)`. -/
theorem schatten_S4_spectral {P : Finset ℕ} (hP : ∀ p ∈ P, 5 ≤ p) :
    ∑ S ∈ P.powerset, dimHS S * (thetaS S) ^ 4 = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2) ^ 3) := by
  rw [Finset.sum_congr rfl
    (fun S hS => dim_theta_fourth (fun p hp => hP p (Finset.mem_powerset.mp hS hp)))]
  exact (schatten_powerset P (fun p => 1 / ((p : ℝ) - 2) ^ 3)).symm

/-! ## S₂ is unbounded (§21) -/

private theorem one_add_sum_le_prod {P : Finset ℕ} (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 ≤ a p) :
    1 + ∑ p ∈ P, a p ≤ ∏ p ∈ P, (1 + a p) := by
  induction P using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hax : 0 ≤ a x := ha x (Finset.mem_insert_self x s)
    have hsum : 0 ≤ ∑ p ∈ s, a p :=
      Finset.sum_nonneg (fun p hp => ha p (Finset.mem_insert_of_mem hp))
    have ihs := ih (fun p hp => ha p (Finset.mem_insert_of_mem hp))
    have hmul := mul_le_mul_of_nonneg_left ihs (show (0 : ℝ) ≤ 1 + a x by linarith)
    nlinarith [hmul, mul_nonneg hax hsum]

/-- **S₂ is unbounded (§21).** The `S₂` mass dominates `1 + Σ 1/(p−2)`; since `Σ 1/(p−2)` diverges
    over the primes, `∏(1 + 1/(p−2))` grows without bound. -/
theorem schatten_S2_lower {P : Finset ℕ} (hP : ∀ p ∈ P, 5 ≤ p) :
    1 + ∑ p ∈ P, 1 / ((p : ℝ) - 2) ≤ ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2)) := by
  apply one_add_sum_le_prod
  intro p hp
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hP p hp
  exact div_nonneg (by norm_num) (by linarith)

/-! ## S₄ is uniformly bounded (§21) -/

private theorem telescope_sum_Icc {N : ℕ} (hN : 5 ≤ N) :
    ∑ n ∈ Finset.Icc 5 N, (1 / ((n : ℝ) - 3) - 1 / ((n : ℝ) - 2)) = 1 / 2 - 1 / ((N : ℝ) - 2) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Finset.Icc_self]
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hN0 : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast
    have h1 : (N : ℝ) - 2 ≠ 0 := by linarith
    have h2 : (N : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (N : ℝ) + 1 - 3 ≠ 0 := by linarith
    have h5 : (N : ℝ) + 1 - 2 ≠ 0 := by linarith
    field_simp
    ring

private theorem sum_inv_cube_le_half {P : Finset ℕ} (hP : ∀ p ∈ P, 5 ≤ p) :
    ∑ p ∈ P, 1 / ((p : ℝ) - 2) ^ 3 ≤ 1 / 2 := by
  have hterm : ∀ p ∈ P, 1 / ((p : ℝ) - 2) ^ 3 ≤ 1 / ((p : ℝ) - 3) - 1 / ((p : ℝ) - 2) := by
    intro p hp
    have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hP p hp
    have hp3 : (p : ℝ) - 3 ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    have key : 1 / ((p : ℝ) - 3) - 1 / ((p : ℝ) - 2) = 1 / (((p : ℝ) - 3) * ((p : ℝ) - 2)) := by
      field_simp; ring
    rw [key]
    have hApos : (0 : ℝ) < ((p : ℝ) - 3) * ((p : ℝ) - 2) := by apply mul_pos <;> linarith
    have hAB : ((p : ℝ) - 3) * ((p : ℝ) - 2) ≤ ((p : ℝ) - 2) ^ 3 := by
      have hb : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 5 * (p : ℝ) + 7 := by nlinarith [sq_nonneg ((p : ℝ) - 3)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (p : ℝ) - 2 by linarith) hb]
    exact one_div_le_one_div_of_le hApos hAB
  have hstep1 : ∑ p ∈ P, 1 / ((p : ℝ) - 2) ^ 3
      ≤ ∑ p ∈ P, (1 / ((p : ℝ) - 3) - 1 / ((p : ℝ) - 2)) := Finset.sum_le_sum hterm
  rcases P.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]; norm_num
  · set N := P.max' hne with hNdef
    have hN5 : 5 ≤ N := hP _ (P.max'_mem hne)
    have hsub : P ⊆ Finset.Icc 5 N := by
      intro p hp
      simp only [Finset.mem_Icc]
      exact ⟨hP p hp, Finset.le_max' P p hp⟩
    have hnn : ∀ n ∈ Finset.Icc 5 N, n ∉ P →
        0 ≤ 1 / ((n : ℝ) - 3) - 1 / ((n : ℝ) - 2) := by
      intro n hn _
      simp only [Finset.mem_Icc] at hn
      have h5 : (5 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hle : 1 / ((n : ℝ) - 2) ≤ 1 / ((n : ℝ) - 3) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
    have hstep2 : ∑ p ∈ P, (1 / ((p : ℝ) - 3) - 1 / ((p : ℝ) - 2))
        ≤ ∑ n ∈ Finset.Icc 5 N, (1 / ((n : ℝ) - 3) - 1 / ((n : ℝ) - 2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have hstep3 := telescope_sum_Icc hN5
    have hN2pos : 0 < 1 / ((N : ℝ) - 2) := by
      have : (5 : ℝ) ≤ N := by exact_mod_cast hN5
      have : (0 : ℝ) < (N : ℝ) - 2 := by linarith
      positivity
    linarith [hstep1, hstep2, hstep3, hN2pos]

/-- **S₄ is uniformly bounded (§21).** `∏(1 + 1/(p−2)³) ≤ exp(1/2)` — a fixed constant independent
    of `Q`.  The fourth moment has a summable local budget. -/
theorem schatten_S4_bounded {P : Finset ℕ} (hP : ∀ p ∈ P, 5 ≤ p) :
    ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2) ^ 3) ≤ Real.exp (1 / 2) := by
  have h1 : ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2) ^ 3)
      ≤ ∏ p ∈ P, Real.exp (1 / ((p : ℝ) - 2) ^ 3) := by
    apply Finset.prod_le_prod
    · intro p hp
      have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hP p hp
      have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      positivity
    · intro p hp
      have := Real.add_one_le_exp (1 / ((p : ℝ) - 2) ^ 3)
      linarith
  rw [← Real.exp_sum] at h1
  calc ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2) ^ 3)
      ≤ Real.exp (∑ p ∈ P, 1 / ((p : ℝ) - 2) ^ 3) := h1
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (sum_inv_cube_le_half hP)

end TypeII
end Geometric
end EuclidsPath
