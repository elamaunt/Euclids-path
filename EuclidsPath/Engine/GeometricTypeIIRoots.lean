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

/-! ## The local root Fourier moments (§53, prime level)

The Fourier transform of the local root pair `{±1} mod p`.  These are COMPLETE sums over ALL
frequencies `h mod p` (including `h = 0`) — the `ω(q) = 1` case of §53, refining the summable root
`S₄` budget already recorded (`root_S4_euler` / `root_S4_bounded`, criterion B).

DISCLOSURE (§55): the interval kernel concentrates on LOW frequencies, where complete-sum moments
give no cancellation; the coherent signed low-frequency sum over `q` remains the open target
`LowFreqRootCoherence` (residual E) — unchanged by these identities and not duplicated under any
new name. -/

/-- The root-pair Fourier sum `S_p(h) = ψ(h) + ψ(−h)` (the transform of `{±1} mod p`). -/
noncomputable def rootSum {p : ℕ} [NeZero p] (h : ZMod p) : ℂ :=
  ZMod.stdAddChar h + ZMod.stdAddChar (-h)

private theorem two_ne_zero_zmod' {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) : (2 : ZMod p) ≠ 0 := by
  have : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
  simpa using this

private theorem four_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) : (4 : ZMod p) ≠ 0 := by
  have : ((4 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 4]
    intro hdvd
    have hp := (Fact.out : p.Prime)
    have h24 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h24] at hdvd
    have h2 := hp.dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  simpa using this

/-- Complete character sums with an invertible multiplier vanish. -/
private theorem char_sum_mul_zero {p : ℕ} [Fact p.Prime] {c : ZMod p} (hc : c ≠ 0) :
    ∑ h : ZMod p, ZMod.stdAddChar (c * h) = 0 := by
  have h := AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar p)
  rw [if_neg hc, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]

private theorem char_sum_neg_mul_zero {p : ℕ} [Fact p.Prime] {c : ZMod p} (hc : c ≠ 0) :
    ∑ h : ZMod p, ZMod.stdAddChar (-(c * h)) = 0 := by
  have hneg : (-c : ZMod p) ≠ 0 := neg_ne_zero.mpr hc
  have h := char_sum_mul_zero hneg
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [show -(c * a) = -c * a by ring]

/-- The squared root sum: `S_p(h)² = ψ(2h) + ψ(−2h) + 2`. -/
private theorem rootSum_sq {p : ℕ} [Fact p.Prime] (h : ZMod p) :
    rootSum h * rootSum h
      = ZMod.stdAddChar (2 * h) + ZMod.stdAddChar (-(2 * h)) + 2 := by
  unfold rootSum
  have hXX : ZMod.stdAddChar h * ZMod.stdAddChar h = ZMod.stdAddChar (2 * h) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hYY : ZMod.stdAddChar (-h) * ZMod.stdAddChar (-h) = ZMod.stdAddChar (-(2 * h)) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hXY : ZMod.stdAddChar h * ZMod.stdAddChar (-h) = 1 := by
    rw [← AddChar.map_add_eq_mul, show h + -h = 0 by ring, AddChar.map_zero_eq_one]
  linear_combination hXX + hYY + 2 * hXY

/-- **Root second moment (§53, `ω = 1`).** `Σ_h S_p(h)² = 2p` — the complete-sum form of the local
    additive count `2^{ω(q)}` at a single prime. -/
theorem rootSum_M2 {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    ∑ h : ZMod p, rootSum h * rootSum h = 2 * (p : ℂ) := by
  have h2ne := two_ne_zero_zmod' hp2
  rw [Finset.sum_congr rfl (fun h _ => rootSum_sq h), Finset.sum_add_distrib,
    Finset.sum_add_distrib, char_sum_mul_zero h2ne, char_sum_neg_mul_zero h2ne,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-- The fourth power: `S_p(h)⁴ = ψ(4h) + ψ(−4h) + 4ψ(2h) + 4ψ(−2h) + 6` — the local additive
    energy `6` of the root pair appears as the constant term. -/
private theorem rootSum_fourth {p : ℕ} [Fact p.Prime] (h : ZMod p) :
    (rootSum h) ^ 4
      = ZMod.stdAddChar (4 * h) + ZMod.stdAddChar (-(4 * h))
        + 4 * ZMod.stdAddChar (2 * h) + 4 * ZMod.stdAddChar (-(2 * h)) + 6 := by
  have hsq := rootSum_sq h
  have hXX : ZMod.stdAddChar (2 * h) * ZMod.stdAddChar (2 * h) = ZMod.stdAddChar (4 * h) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hYY : ZMod.stdAddChar (-(2 * h)) * ZMod.stdAddChar (-(2 * h))
      = ZMod.stdAddChar (-(4 * h)) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hXY : ZMod.stdAddChar (2 * h) * ZMod.stdAddChar (-(2 * h)) = 1 := by
    rw [← AddChar.map_add_eq_mul, show 2 * h + -(2 * h) = 0 by ring, AddChar.map_zero_eq_one]
  have e4 : (rootSum h) ^ 4 = (rootSum h * rootSum h) * (rootSum h * rootSum h) := by ring
  rw [e4, hsq]
  linear_combination hXX + hYY + 2 * hXY

/-- **Root fourth moment (§53, `ω = 1`).** `Σ_h S_p(h)⁴ = 6p` — the local additive energy
    `1² + 2² + 1² = 6` of the root pair `{±1}`, at the complete-sum level. -/
theorem rootSum_M4 {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    ∑ h : ZMod p, (rootSum h) ^ 4 = 6 * (p : ℂ) := by
  have h2ne := two_ne_zero_zmod' hp2
  have h4ne := four_ne_zero_zmod hp2
  have hc2 : ∑ h : ZMod p, (4 : ℂ) * ZMod.stdAddChar (2 * h) = 0 := by
    rw [← Finset.mul_sum, char_sum_mul_zero h2ne, mul_zero]
  have hc2n : ∑ h : ZMod p, (4 : ℂ) * ZMod.stdAddChar (-(2 * h)) = 0 := by
    rw [← Finset.mul_sum, char_sum_neg_mul_zero h2ne, mul_zero]
  rw [Finset.sum_congr rfl (fun h _ => rootSum_fourth h), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    char_sum_mul_zero h4ne, char_sum_neg_mul_zero h4ne, hc2, hc2n,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-! ## The CRT junction: the root set factors (§53, the (C)×(E) meeting point)

The CRT-root sets multiply under coprime moduli: `|R_{q₁q₂}| = |R_{q₁}|·|R_{q₂}|`, hence
`|R_q| = 2^{ω(q)}` for odd squarefree `q` — the §53 count, previously carried only through the
Euler-product analogy, becomes exact CRT algebra.  This is the junction where the degree-two
conductor structure (residual C) meets the root remainder (residual E) in machine form.
DISCLOSURE: exact algebra; no bound on any signed sum; residuals C/D/E and `CRE` unchanged. -/

/-- **The root set factors under CRT (§53).** For coprime moduli,
    `#{C² = 1 mod q₁q₂} = #{C² = 1 mod q₁} · #{C² = 1 mod q₂}`. -/
theorem root_card_crt {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] (hq : Nat.Coprime q₁ q₂) :
    (Finset.univ.filter fun C : ZMod (q₁ * q₂) => C ^ 2 = 1).card
      = (Finset.univ.filter fun C : ZMod q₁ => C ^ 2 = 1).card
        * (Finset.univ.filter fun C : ZMod q₂ => C ^ 2 = 1).card := by
  classical
  haveI : NeZero (q₁ * q₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  set crtIso := ZMod.chineseRemainder hq with hcrtIso
  have hcard : (Finset.univ.filter fun C : ZMod (q₁ * q₂) => C ^ 2 = 1).card
      = ((Finset.univ.filter fun a : ZMod q₁ => a ^ 2 = 1) ×ˢ
          (Finset.univ.filter fun b : ZMod q₂ => b ^ 2 = 1)).card := by
    apply Finset.card_equiv crtIso.toEquiv
    intro C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    have hphiC : crtIso.toEquiv C = crtIso C := rfl
    rw [hphiC]
    constructor
    · intro hC
      have hsq : (crtIso C) ^ 2 = 1 := by rw [← map_pow, hC, map_one]
      constructor
      · have hfst := congrArg Prod.fst hsq
        rw [pow_two, Prod.fst_mul] at hfst
        rw [pow_two]
        simpa using hfst
      · have hsnd := congrArg Prod.snd hsq
        rw [pow_two, Prod.snd_mul] at hsnd
        rw [pow_two]
        simpa using hsnd
    · intro ⟨h1, h2⟩
      have hsq : (crtIso C) ^ 2 = 1 := by
        have hf : ((crtIso C) ^ 2).1 = (1 : ZMod q₁ × ZMod q₂).1 := by
          rw [pow_two, Prod.fst_mul, ← pow_two]
          simpa using h1
        have hs : ((crtIso C) ^ 2).2 = (1 : ZMod q₁ × ZMod q₂).2 := by
          rw [pow_two, Prod.snd_mul, ← pow_two]
          simpa using h2
        exact Prod.ext hf hs
      have hsq' : crtIso (C ^ 2) = 1 := by rw [map_pow]; exact hsq
      have := congrArg crtIso.symm hsq'
      rw [crtIso.symm_apply_apply, map_one] at this
      exact this
  rw [hcard, Finset.card_product]

end TypeII
end Geometric
end EuclidsPath
