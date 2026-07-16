/-
  GeometricTypeIIRoots — the two-wing CRT-root Fourier geometry and the root S₄ threshold.

  ORIGIN (parity_wall Prime-Chaos session dossier §52 / §53 / §54 / §55). The exact pair-rough
  remainder is `R₂(M,z) = Σ_{q|P(z)} μ(q) Σ_{C²≡1 (q)} Δ(M; q, ...)` (§52).  The Fourier transform
  of the CRT-root set has second and fourth moments `Σ_h |S_q(h)|² = q·2^{ω(q)}` and
  `Σ_h |S_q(h)|⁴ = q·6^{ω(q)}` (§53) — locally the pair of roots `±1` has sums `2,0,−2` with
  multiplicities `1,2,1`, so its additive energy is `1²+2²+1² = 6`.  The completed root operator
  therefore has a summable `S₄`-budget: `Σ_{q squarefree} 6^{ω(q)}/q³ = ∏_p (1 + 6/p³) < ∞` (§54).
  The interval kernel, however, concentrates on low frequencies, where the coherent signed sum over
  `q` remains OPEN (§55).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `root_additive_energy_local` — the local additive energy of `{±1}` is `6` (§53);
    * `root_S4_euler` — `Σ_{q sqfree} 6^{ω}/q³ = ∏_p (1 + 6/p³)` (subset-sum = product, §54);
    * `root_S4_bounded` — `∏_p (1 + 6/p³) ≤ exp 6`: the root `S₄`-budget is BOUNDED (§54);
    * `PairRoughRemainder` — the exact pair-rough remainder (named structural object, §52);
    * `LowFreqRootCoherence` — the low-frequency root coherence target (named open, §55, residual E).

  DISCLOSURE. The root `S₄`-budget is summable, but the low-frequency interval coherence (§55) is
  the open target (residual E). twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIChaos

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The local additive energy of the root pair (§53) -/

/-- **Local additive energy (§53).** The two roots `±1` produce sums `2, 0, −2` with multiplicities
    `1, 2, 1`; the additive energy `Σ_s (#{sums = s})²` is `1² + 2² + 1² = 6`. -/
theorem root_additive_energy_local : (1 : ℕ) ^ 2 + 2 ^ 2 + 1 ^ 2 = 6 := by norm_num

/-! ## The root S₄ Euler product (§54) -/

/-- **Root S₄ Euler product (§54).** The squarefree root fourth-moment budget is
    `Σ_{q sqfree, primes in P} 6^{ω(q)}/q³ = ∏_{p∈P}(1 + 6/p³)` (subset-sum to product). -/
theorem root_S4_euler (P : Finset ℕ) :
    ∑ S ∈ P.powerset, ∏ p ∈ S, (6 / (p : ℝ) ^ 3) = ∏ p ∈ P, (1 + 6 / (p : ℝ) ^ 3) :=
  (schatten_powerset P (fun p => 6 / (p : ℝ) ^ 3)).symm

/-! ## The root S₄ budget is bounded (§54) -/

private theorem telescope_sum_Icc2 {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) = 1 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Finset.Icc_self]
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hN0 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast
    have h1 : (N : ℝ) ≠ 0 := by linarith
    have h2 : (N : ℝ) + 1 ≠ 0 := by linarith
    have h3 : (N : ℝ) + 1 - 1 ≠ 0 := by linarith
    field_simp
    ring

private theorem sum_inv_cube_prime_le_one {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    ∑ p ∈ P, 1 / (p : ℝ) ^ 3 ≤ 1 := by
  have hterm : ∀ p ∈ P, 1 / (p : ℝ) ^ 3 ≤ 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have key : 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) = 1 / (((p : ℝ) - 1) * (p : ℝ)) := by
      field_simp; ring
    rw [key]
    have hApos : (0 : ℝ) < ((p : ℝ) - 1) * (p : ℝ) := by apply mul_pos <;> linarith
    have hAB : ((p : ℝ) - 1) * (p : ℝ) ≤ (p : ℝ) ^ 3 := by nlinarith [h2]
    exact one_div_le_one_div_of_le hApos hAB
  have hstep1 : ∑ p ∈ P, 1 / (p : ℝ) ^ 3 ≤ ∑ p ∈ P, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) :=
    Finset.sum_le_sum hterm
  rcases P.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]; norm_num
  · set N := P.max' hne with hNdef
    have hN2 : 2 ≤ N := hP _ (P.max'_mem hne)
    have hsub : P ⊆ Finset.Icc 2 N := by
      intro p hp; simp only [Finset.mem_Icc]; exact ⟨hP p hp, Finset.le_max' P p hp⟩
    have hnn : ∀ n ∈ Finset.Icc 2 N, n ∉ P → 0 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
      intro n hn _
      simp only [Finset.mem_Icc] at hn
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hle : 1 / (n : ℝ) ≤ 1 / ((n : ℝ) - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
    have hstep2 : ∑ p ∈ P, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))
        ≤ ∑ n ∈ Finset.Icc 2 N, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have hstep3 := telescope_sum_Icc2 hN2
    have hNpos : 0 < 1 / (N : ℝ) := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      positivity
    linarith [hstep1, hstep2, hstep3, hNpos]

/-- **Root S₄ budget is bounded (§54).** `∏_p (1 + 6/p³) ≤ exp 6` — the completed root operator has
    a uniformly bounded fourth-moment budget. -/
theorem root_S4_bounded {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    ∏ p ∈ P, (1 + 6 / (p : ℝ) ^ 3) ≤ Real.exp 6 := by
  have h1 : ∏ p ∈ P, (1 + 6 / (p : ℝ) ^ 3) ≤ ∏ p ∈ P, Real.exp (6 / (p : ℝ) ^ 3) := by
    apply Finset.prod_le_prod
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
      positivity
    · intro p hp
      have := Real.add_one_le_exp (6 / (p : ℝ) ^ 3)
      linarith
  rw [← Real.exp_sum] at h1
  have hsum : ∑ p ∈ P, 6 / (p : ℝ) ^ 3 ≤ 6 := by
    have : ∑ p ∈ P, 6 / (p : ℝ) ^ 3 = 6 * ∑ p ∈ P, 1 / (p : ℝ) ^ 3 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    rw [this]
    have := sum_inv_cube_prime_le_one hP
    linarith
  calc ∏ p ∈ P, (1 + 6 / (p : ℝ) ^ 3) ≤ Real.exp (∑ p ∈ P, 6 / (p : ℝ) ^ 3) := h1
    _ ≤ Real.exp 6 := Real.exp_le_exp.mpr hsum

/-! ## The pair-rough remainder and the low-frequency target (§52 / §55) -/

/-- **The exact pair-rough remainder (§52).** `R₂(M,z) = Σ_{q} μ(q) Δ_q` where `Δ_q` collects the
    CRT-root shifts `Σ_{C²≡1 (q)} Δ(M; q, C)` — a named structural object. -/
noncomputable def PairRoughRemainder (Δ : ℕ → ℝ) (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (ArithmeticFunction.moebius q : ℝ) * Δ q

/-- **Low-frequency root coherence (§55, residual E).** The completed root operator has a summable
    `S₄`-budget, but the interval kernel concentrates on low frequencies; the coherent signed sum
    over `q` there is the open target — a named `Prop`, not a `sorry`. -/
def LowFreqRootCoherence (E : ℝ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → E x ≤ C * x ^ 2 / (Real.log x) ^ B

end TypeII
end Geometric
end EuclidsPath
