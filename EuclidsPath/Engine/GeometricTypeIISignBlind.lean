/-
  GeometricTypeIISignBlind — THREE MACHINE NO-GOS that harden the wall map on the
  sign side: (1) SIGN-EATING — the Möbius sign at a prime conductor is EXACTLY
  annihilated by the parity eigenvalue `−1/(q−2)`, so μ-telescoping across the
  one-defect tower is impossible and the tower dominates the divergent S₂ mass;
  (2) SPECTRAL BLINDNESS — every trace/moment functional is invariant under ±1
  diagonal conjugation, so no spectral quantity of the Gram frame can see the
  μ-signs; (3) EXCHANGE COMPLETENESS — the only completely multiplicative sign
  functions constant on primes are `1` and `λ`: the exchange filter admits EXACTLY
  two sign characters, certifying that size weights and dilation are the only
  sign-visible mechanisms.

  ORIGIN.  Idea-generation session (two-axes program, wave 2).  All three came out
  of the adversarial panels as REFUTATIONS of attack seeds:
    * (1) refutes the cross-conductor μ-telescoping seed: with
      `one_defect_fixed_point` (GeometricTypeIIFixedPoint) giving
      `B_q = (−1/(q−2))·A_q` and `μ(q) = −1` at primes, every signed term
      `μ(q)·B_q = A_q/(q−2)` is POSITIVE — same sign at every conductor, nothing to
      telescope; summing at `j = 0` reproduces (dominates) the S₂ partial sum
      `Σ 1/(p−2)` — the "Euler-derivative" object IS the S₂ divergence renamed.
    * (2) refutes spectral-functional seeds: the μ-signs enter the Gram frame as a
      ±1 diagonal conjugation `A ↦ DAD` with `D² = 1` — a similarity; every
      `Tr(·^k)` (hence every Schatten even norm, cf. `zEnergy_eq_schatten`) is
      blind to them.
    * (3) upgrades the exchange filter (`neg_one_pow_cardFactors_exchange`) to a
      COMPLETENESS theorem: a completely multiplicative `f : ℕ → ℤ` with prime
      values in `{±1}`, constant on primes (= exchange-invariant), is `1` or `λ`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `defectProfile` / `defectMoment` — the CONCRETE one-defect model on
      `Fin (m+1)` (profile `1` at the marked point, `−1/m` elsewhere; defect moment
      against the transposition `swap 0 1`) — named structural objects, NOT targets;
    * `defectMoment_fixed_point` — the model instantiates the house fixed-point law
      `B = (−1/m)·A` (criterion-free reuse of `one_defect_fixed_point`);
    * `defect_even_moment_pos` / `defect_even_moment_zero` — `A > 0` always, and
      `A₀ = (m+1)/m` exactly;
    * `cross_conductor_sign_eating` — **NO-GO 1**: `μ(q)·B_q(j) > 0` for EVERY prime
      `q ≥ 5` and EVERY moment index `j` — the Möbius sign is eaten by the parity
      eigenvalue; μ-oscillation across the defect tower is structurally impossible;
    * `one_defect_tower_ge_S2` — **NO-GO 1, tower form**: `Σ_{p∈P} 1/(p−2) ≤
      Σ_{p∈P} μ(p)·B_p(0)` — the signed tower DOMINATES the S₂ partial sum (which
      is divergent: `schatten_S2_lower` / `mixed_mode_parity_scale` genre) — the
      tower is not an oscillating object at all;
    * `signed_conjugation_trace_blind` — **NO-GO 2**: for any matrix `A`, any sign
      vector `ε ∈ {±1}ⁿ`, and any `k`: `Tr((D_ε A D_ε)^k) = Tr(A^k)` — all spectral
      moments are sign-blind;
    * `exchange_invariant_sign_eq_one_or_liouville` — **NO-GO 3 (completeness)**:
      a completely multiplicative `f : ℕ → ℤ` with `f(p) ∈ {±1}` and `f` constant
      across primes equals `1` identically or `(−1)^Ω` identically (on `n ≠ 0`).

  DISCLOSURES (mandatory reading before quoting):
    * NO-GOS MOVE NOTHING (§110: zero movement by definition).  These theorems
      CLOSE routes; they do not touch, bound, or reduce any registered target
      (CRE, SemiprimeShortRestriction, HigherConductorDispersion,
      LowFreqRootCoherence, OneWingTarget).  Their value is map-hardening: three
      previously prose-level "closed route" annotations are now machine theorems.
    * The one-defect model here is the CANONICAL instance (`Fin (m+1)`, transposition
      defect); the house fixed-point law holds for every instance
      (`one_defect_fixed_point` is abstract) — the concrete model is chosen to make
      the tower sum a literal function of the conductor.
    * `μ` is `ArithmeticFunction.moebius`; the tower statement is about FINITE
      partial sums (no limits are taken; the divergence of `Σ 1/(p−2)` is the
      house S₂ genre, quoted not re-proved).
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIFixedPoint

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### No-go 1 — sign-eating: the concrete one-defect model and its signed tower -/

/-- The canonical one-defect profile on `Fin (m+1)`: `1` at the marked point `0`,
    the parity eigenvalue weight `−1/m` everywhere else. -/
noncomputable def defectProfile (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => if i = 0 then 1 else -1 / (m : ℝ)

/-- The one-defect moment of order `j` against the transposition defect
    `σ = swap 0 1` — the concrete instance of the `[2j+1, 1]`-sector moment. -/
noncomputable def defectMoment (m j : ℕ) : ℝ :=
  ∑ χ : Fin (m + 1), (defectProfile m χ) ^ (2 * j + 1)
    * defectProfile m (Equiv.swap 0 1 χ)

/-- `0 ≠ 1` in `Fin (m+1)` once `1 ≤ m`. -/
private theorem fin_zero_ne_one {m : ℕ} (hm1 : 1 ≤ m) :
    (0 : Fin (m + 1)) ≠ 1 := by
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m + 1)] at hval
  exact absurd hval (by omega)

/-- The concrete model satisfies the house fixed-point law `B = (−1/m)·A`
    (instance of `one_defect_fixed_point`). -/
theorem defectMoment_fixed_point {m : ℕ} (hm1 : 1 ≤ m) (j : ℕ) :
    defectMoment m j
      = (-1 / (m : ℝ)) * ∑ χ : Fin (m + 1), (defectProfile m χ) ^ (2 * j + 2) := by
  unfold defectMoment
  refine one_defect_fixed_point (ι := Fin (m + 1)) 0 m (by simp) hm1 j
    (defectProfile m) ?_ ?_ (Equiv.swap 0 1) ?_
  · simp [defectProfile]
  · intro i hi
    simp [defectProfile, hi]
  · rw [Equiv.swap_apply_left]
    exact (fin_zero_ne_one hm1).symm

/-- The even moment is strictly positive: the marked point alone contributes `1`,
    every other term is an even power. -/
theorem defect_even_moment_pos {m : ℕ} (j : ℕ) :
    0 < ∑ χ : Fin (m + 1), (defectProfile m χ) ^ (2 * j + 2) := by
  have hnn : ∀ χ ∈ (Finset.univ : Finset (Fin (m + 1))),
      (0 : ℝ) ≤ (defectProfile m χ) ^ (2 * j + 2) := by
    intro χ _
    have h2 : 2 * j + 2 = 2 * (j + 1) := by ring
    rw [h2, pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have h0 : (defectProfile m 0) ^ (2 * j + 2) = 1 := by
    simp [defectProfile]
  calc (0 : ℝ) < 1 := one_pos
    _ = (defectProfile m 0) ^ (2 * j + 2) := h0.symm
    _ ≤ ∑ χ : Fin (m + 1), (defectProfile m χ) ^ (2 * j + 2) :=
        Finset.single_le_sum hnn (Finset.mem_univ 0)

/-- The even moment at `j = 0`, exactly: `A₀ = Σ f² = 1 + m·(1/m²) = (m+1)/m`. -/
theorem defect_even_moment_zero {m : ℕ} (hm1 : 1 ≤ m) :
    ∑ χ : Fin (m + 1), (defectProfile m χ) ^ (2 * 0 + 2)
      = ((m : ℝ) + 1) / m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  have h0 : (defectProfile m 0) ^ (2 * 0 + 2) = 1 := by
    simp [defectProfile]
  have hrest : ∀ χ ∈ Finset.univ.erase (0 : Fin (m + 1)),
      (defectProfile m χ) ^ (2 * 0 + 2) = 1 / (m : ℝ) ^ 2 := by
    intro χ hχ
    have hχ0 : χ ≠ 0 := (Finset.mem_erase.mp hχ).1
    simp only [defectProfile, if_neg hχ0]
    rw [show 2 * 0 + 2 = 2 by norm_num, div_pow, neg_one_sq]
  rw [h0, Finset.sum_congr rfl hrest, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) := by
    push_cast [Nat.add_sub_cancel]
    ring
  rw [hcast]
  field_simp

/-- **NO-GO 1 — SIGN-EATING**: at every prime conductor `q ≥ 5` and every moment
    index `j`, the μ-SIGNED one-defect moment is strictly POSITIVE:
    `μ(q)·B_q(j) = A_q(j)/(q−2) > 0`.  The Möbius sign `μ(q) = −1` is EXACTLY
    annihilated by the parity eigenvalue `−1/(q−2)` — every term of the signed
    tower has the SAME sign, so μ-oscillation across conductors is structurally
    impossible in the one-defect sector. -/
theorem cross_conductor_sign_eating {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (j : ℕ) :
    0 < ((ArithmeticFunction.moebius q : ℤ) : ℝ) * defectMoment (q - 2) j := by
  have hμ : ArithmeticFunction.moebius q = -1 := moebius_apply_prime hq
  have hm1 : 1 ≤ q - 2 := by omega
  have hm0 : (0 : ℝ) < ((q - 2 : ℕ) : ℝ) := by
    have : 0 < q - 2 := by omega
    exact_mod_cast this
  rw [hμ, defectMoment_fixed_point hm1 j]
  have hA := defect_even_moment_pos (m := q - 2) j
  have hring : (((-1 : ℤ) : ℝ)) * (-1 / ((q - 2 : ℕ) : ℝ)
        * ∑ χ : Fin (q - 2 + 1), (defectProfile (q - 2) χ) ^ (2 * j + 2))
      = (∑ χ : Fin (q - 2 + 1), (defectProfile (q - 2) χ) ^ (2 * j + 2))
        / ((q - 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hring]
  exact div_pos hA hm0

/-- **NO-GO 1, TOWER FORM**: the μ-signed one-defect tower at `j = 0` DOMINATES the
    S₂ partial sum: `Σ_{p∈P} 1/(p−2) ≤ Σ_{p∈P} μ(p)·B_p(0)`.  The signed tower is
    not an oscillating object — it carries at least the full divergent S₂ mass
    (the "Euler-derivative" reading is the S₂ divergence renamed). -/
theorem one_defect_tower_ge_S2 {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) :
    ∑ p ∈ P, 1 / ((p : ℝ) - 2)
      ≤ ∑ p ∈ P, ((ArithmeticFunction.moebius p : ℤ) : ℝ) * defectMoment (p - 2) 0 := by
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hprime, h5⟩ := hP p hp
  have hμ : ArithmeticFunction.moebius p = -1 := moebius_apply_prime hprime
  have hm1 : 1 ≤ p - 2 := by omega
  have hmcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ p)]
    ring
  have hm0 : (0 : ℝ) < (p : ℝ) - 2 := by
    have h5r : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h5
    linarith
  rw [hμ, defectMoment_fixed_point hm1 0, defect_even_moment_zero hm1, hmcast]
  have hval : (((-1 : ℤ) : ℝ)) * (-1 / ((p : ℝ) - 2) * (((p : ℝ) - 2 + 1) / ((p : ℝ) - 2)))
      = (((p : ℝ) - 2) + 1) / (((p : ℝ) - 2) * ((p : ℝ) - 2)) := by
    push_cast
    field_simp
  rw [hval]
  rw [div_le_div_iff₀ hm0 (by positivity)]
  nlinarith [hm0]

/-! ### No-go 2 — spectral blindness: ±1 conjugation is a similarity -/

/-- **NO-GO 2 — SPECTRAL BLINDNESS**: for every square matrix `A`, every sign vector
    `ε ∈ {±1}ⁿ`, and every `k`, the `k`-th trace moment of the sign-conjugated
    matrix equals that of `A`: `Tr((D_ε A D_ε)^k) = Tr(A^k)`.  The μ-signs enter
    the Gram frame only as such a conjugation — hence NO spectral functional
    (traces, Schatten even norms, `zEnergy_eq_schatten` genre) can see them. -/
theorem signed_conjugation_trace_blind {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (ε : n → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (k : ℕ) :
    ((Matrix.diagonal ε * A * Matrix.diagonal ε) ^ k).trace = (A ^ k).trace := by
  have hD2 : Matrix.diagonal ε * Matrix.diagonal ε = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hone : (fun i => ε i * ε i) = fun _ => (1 : ℝ) := by
      funext i
      rcases hε i with h | h <;> rw [h] <;> norm_num
    rw [hone, Matrix.diagonal_one]
  have hpow : ∀ k : ℕ, (Matrix.diagonal ε * A * Matrix.diagonal ε) ^ k
      = Matrix.diagonal ε * A ^ k * Matrix.diagonal ε := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero, mul_one, hD2]
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        calc Matrix.diagonal ε * A ^ k * Matrix.diagonal ε
              * (Matrix.diagonal ε * A * Matrix.diagonal ε)
            = Matrix.diagonal ε * A ^ k
                * (Matrix.diagonal ε * Matrix.diagonal ε) * A
                * Matrix.diagonal ε := by
              noncomm_ring
          _ = Matrix.diagonal ε * A ^ k * 1 * A * Matrix.diagonal ε := by
              rw [hD2]
          _ = Matrix.diagonal ε * (A ^ k * A) * Matrix.diagonal ε := by
              rw [mul_one, mul_assoc (Matrix.diagonal ε) (A ^ k) A]
  rw [hpow k, Matrix.trace_mul_comm, ← mul_assoc, hD2, one_mul]

/-! ### No-go 3 — exchange completeness: the sign characters are exactly {1, λ} -/

/-- **NO-GO 3 — EXCHANGE COMPLETENESS**: a completely multiplicative `f : ℕ → ℤ`
    whose prime values are signs and which is CONSTANT across primes (the algebraic
    residue of exchange-invariance: the exchange `n ↦ (n/p)·q` multiplies `f` by
    `f(q)/f(p)`, so invariance forces `f(p) = f(q)`) is `1` identically or the
    Liouville sign `(−1)^Ω` identically.  The exchange filter admits EXACTLY two
    sign characters — certifying that size weights and dilation are the only
    sign-visible mechanisms on the wing. -/
theorem exchange_invariant_sign_eq_one_or_liouville
    (f : ℕ → ℤ) (hmul : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hsign : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1)
    (hexch : ∀ p q : ℕ, p.Prime → q.Prime → f p = f q) :
    (∀ n : ℕ, n ≠ 0 → f n = 1)
      ∨ (∀ n : ℕ, n ≠ 0 → f n = (-1) ^ (cardFactors n)) := by
  have hf2 := hsign 2 Nat.prime_two
  have hf1 : f 1 = 1 := by
    have h11 := hmul 1 1
    rw [mul_one] at h11
    have h0 : f 1 * (f 1 - 1) = 0 := by linear_combination -h11
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      have hz : f 2 = 0 := by
        have h21 := hmul 2 1
        rw [mul_one, h, mul_zero] at h21
        exact h21
      rcases hf2 with hs | hs <;> omega
    · omega
  have key : ∀ L : List ℕ, f L.prod = (L.map f).prod := by
    intro L
    induction L with
    | nil => simpa using hf1
    | cons p t ih =>
        rw [List.prod_cons, hmul, List.map_cons, List.prod_cons, ih]
  have hfn : ∀ n : ℕ, n ≠ 0 → f n = ((n.primeFactorsList).map f).prod := by
    intro n hn
    conv_lhs => rw [← Nat.prod_primeFactorsList hn]
    exact key _
  rcases hf2 with h2 | h2
  · left
    intro n hn
    have hall : ∀ x ∈ (n.primeFactorsList).map f, x = (1 : ℤ) := by
      intro x hx
      obtain ⟨p, hpmem, rfl⟩ := List.mem_map.mp hx
      rw [hexch p 2 (Nat.prime_of_mem_primeFactorsList hpmem) Nat.prime_two]
      exact h2
    rw [hfn n hn, List.prod_eq_one hall]
  · right
    intro n hn
    have hall : ∀ x ∈ (n.primeFactorsList).map f, x = (-1 : ℤ) := by
      intro x hx
      obtain ⟨p, hpmem, rfl⟩ := List.mem_map.mp hx
      rw [hexch p 2 (Nat.prime_of_mem_primeFactorsList hpmem) Nat.prime_two]
      exact h2
    rw [hfn n hn, List.prod_eq_pow_card _ (-1 : ℤ) hall, List.length_map,
      ← cardFactors_apply]

/-! ### Axiom audit -/

#print axioms defectMoment_fixed_point
#print axioms defect_even_moment_pos
#print axioms defect_even_moment_zero
#print axioms cross_conductor_sign_eating
#print axioms one_defect_tower_ge_S2
#print axioms signed_conjugation_trace_blind
#print axioms exchange_invariant_sign_eq_one_or_liouville

end TypeII
end Geometric
end EuclidsPath
