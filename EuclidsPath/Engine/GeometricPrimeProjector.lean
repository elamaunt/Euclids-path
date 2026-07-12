/-
  GeometricPrimeProjector — the Möbius prime-projector and the soft multiplicative
  projector.

  ORIGIN (user's geometric program, §XVI / §XXII / §XXIII of
  `geometric_twin_prime_program_full.md`): the squarefree Möbius generating function
  Σ_{d | rad n} μ(d) t^{ω(d)} = (1−t)^r collapses, at the linear order, to a projector
  that selects EXACTLY the prime (and prime-power) coordinates: −Σ μ(d) ω(d) = 1_{r=1}.
  A softer, uniform surrogate is t^{Ω(n)−1}, which sandwiches the primality indicator
  to within t.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `sum_signed_pow_card` — the squarefree Möbius generating identity in combinatorial
      form: Σ_{T ⊆ P} (−t)^|T| = (1−t)^|P| (P = the prime factors, |T| = ω of the
      corresponding squarefree divisor). This is §22's Σ μ(d) t^{ω(d)} = (1−t)^r;
    * `signed_card_sum` / `prime_projector_derivative` — the linear order selects primes:
      −Σ_{T ⊆ P} (−1)^|T| |T| = 1_{|P| = 1};
    * `softProjector_bounds` — 1_ℙ(n) ≤ t^{Ω(n)−1} ≤ 1_ℙ(n) + t (the uniform primality
      surrogate, §28), the engine of the reduction skeleton;
    * `gammaOmega_eq` — the per-prime pair Euler factor of the ω-model:
      v/(u²) = 1 − (1−t)²/(p−1+t)² (§31), an EXACT per-prime rational identity.

  DISCLOSURE.  These are exact algebraic / combinatorial identities about the divisor
  hypercube; they do not by themselves control any correlation.  Nothing here feeds the
  wall.  twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace Projector

open scoped BigOperators

/-! ## The squarefree Möbius generating identity (§22) -/

variable {R : Type*} [CommRing R]

/-- **Squarefree Möbius generating identity (§22).** Summing the signed weight `(−t)^|T|`
    over all subsets `T` of the prime-factor set `P` gives `(1−t)^|P|` — i.e.
    `Σ_{d | rad n} μ(d) t^{ω(d)} = (1−t)^r`. -/
theorem sum_signed_pow_card {ι : Type*} [DecidableEq ι] (P : Finset ι) (t : R) :
    ∑ T ∈ P.powerset, (-t) ^ T.card = (1 - t) ^ P.card := by
  induction P using Finset.induction with
  | empty => simp
  | @insert a P ha _ih =>
      have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        rw [Finset.mem_image] at hT'
        obtain ⟨S, _, hS⟩ := hT'
        exact ha (Finset.mem_powerset.mp hT (hS ▸ Finset.mem_insert_self a S))
      have hinj : ∀ S ∈ P.powerset, ∀ S' ∈ P.powerset,
          insert a S = insert a S' → S = S' := by
        intro S hS S' hS' hSS'
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        have haS' : a ∉ S' := fun h => ha (Finset.mem_powerset.mp hS' h)
        have hc := congrArg (fun s => Finset.erase s a) hSS'
        simpa [Finset.erase_insert haS, Finset.erase_insert haS'] using hc
      rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj]
      have key : ∀ T ∈ P.powerset, (-t) ^ (insert a T).card = (-t) * (-t) ^ T.card := by
        intro T hT
        have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
        rw [Finset.card_insert_of_notMem haT, pow_succ]
        ring
      rw [Finset.sum_congr rfl key, ← Finset.mul_sum, _ih,
        Finset.card_insert_of_notMem ha, pow_succ]
      ring

/-! ## The prime projector: the linear order selects primes (§22) -/

/-- **Signed cardinality sum.** `Σ_{T ⊆ P} (−1)^|T| |T| = 1_{|P|=1} · (−1)`: the alternating
    sum of subset sizes vanishes unless `P` is a single prime. -/
theorem signed_card_sum {ι : Type*} [DecidableEq ι] (P : Finset ι) :
    ∑ T ∈ P.powerset, (-1 : ℤ) ^ T.card * (T.card : ℤ)
      = if P.card = 1 then (-1 : ℤ) else 0 := by
  induction P using Finset.induction with
  | empty => simp
  | @insert a P ha _ih =>
      have hg : ∑ T ∈ P.powerset, (-1 : ℤ) ^ T.card = if P.card = 0 then (1 : ℤ) else 0 := by
        have h := sum_signed_pow_card P (1 : ℤ)
        rw [show ((1 : ℤ) - 1) = 0 by ring, zero_pow_eq] at h
        simpa using h
      have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        rw [Finset.mem_image] at hT'
        obtain ⟨S, _, hS⟩ := hT'
        exact ha (Finset.mem_powerset.mp hT (hS ▸ Finset.mem_insert_self a S))
      have hinj : ∀ S ∈ P.powerset, ∀ S' ∈ P.powerset,
          insert a S = insert a S' → S = S' := by
        intro S hS S' hS' hSS'
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        have haS' : a ∉ S' := fun h => ha (Finset.mem_powerset.mp hS' h)
        have hc := congrArg (fun s => Finset.erase s a) hSS'
        simpa [Finset.erase_insert haS, Finset.erase_insert haS'] using hc
      rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
        ← Finset.sum_add_distrib]
      have key : ∀ T ∈ P.powerset,
          (-1 : ℤ) ^ T.card * (T.card : ℤ)
            + (-1 : ℤ) ^ (insert a T).card * ((insert a T).card : ℤ)
            = -((-1 : ℤ) ^ T.card) := by
        intro T hT
        have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
        rw [Finset.card_insert_of_notMem haT]
        push_cast
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_neg_distrib, hg,
        Finset.card_insert_of_notMem ha]
      rcases Nat.eq_zero_or_pos P.card with hc | hc
      · simp [hc]
      · have hne : P.card + 1 ≠ 1 := by omega
        have hne0 : P.card ≠ 0 := hc.ne'
        simp [hne, hne0]

/-- **Prime projector derivative (§22).** `−Σ_{d | rad n} μ(d) ω(d) = 1_{r=1}`: minus the
    alternating first moment of the divisor hypercube is the indicator that `n` has a
    single prime factor. -/
theorem prime_projector_derivative {ι : Type*} [DecidableEq ι] (P : Finset ι) :
    -(∑ T ∈ P.powerset, (-1 : ℤ) ^ T.card * (T.card : ℤ))
      = if P.card = 1 then (1 : ℤ) else 0 := by
  rw [signed_card_sum]
  split <;> simp

/-! ## The soft multiplicative projector (§28) -/

/-- The soft projector `Q_t(n) = t^{Ω(n)−1}`. -/
noncomputable def softProjector (t : ℝ) (n : ℕ) : ℝ :=
  t ^ (ArithmeticFunction.cardFactors n - 1)

/-- Pointwise bound in terms of the abstract factor count `k = Ω(n)`. -/
theorem softProjector_pow_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    (if k = 1 then (1 : ℝ) else 0) ≤ t ^ (k - 1)
      ∧ t ^ (k - 1) ≤ (if k = 1 then (1 : ℝ) else 0) + t := by
  rcases eq_or_lt_of_le hk with h1 | h2
  · subst h1
    have hif : (if (1 : ℕ) = 1 then (1 : ℝ) else 0) = 1 := if_pos rfl
    rw [hif, Nat.sub_self, pow_zero]
    exact ⟨le_refl 1, by linarith⟩
  · have hne : k ≠ 1 := by omega
    have hle : t ^ (k - 1) ≤ t := by
      calc t ^ (k - 1) ≤ t ^ 1 := pow_le_pow_of_le_one ht0 ht1 (by omega)
        _ = t := pow_one t
    constructor
    · rw [if_neg hne]; exact pow_nonneg ht0 _
    · rw [if_neg hne, zero_add]; exact hle

/-- **Soft-projector sandwich (§28).** For `n ≥ 2` and `0 ≤ t ≤ 1`, the soft projector
    sandwiches the primality indicator to within `t`:
    `1_ℙ(n) ≤ t^{Ω(n)−1} ≤ 1_ℙ(n) + t`. This is the engine of the reduction skeleton. -/
theorem softProjector_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    (if n.Prime then (1 : ℝ) else 0) ≤ softProjector t n
      ∧ softProjector t n ≤ (if n.Prime then (1 : ℝ) else 0) + t := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have hk : 1 ≤ ArithmeticFunction.cardFactors n := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList h0).mpr ⟨hp, hpd⟩
    rw [ArithmeticFunction.cardFactors_apply]
    exact List.length_pos_of_mem hmem
  have hiff : ArithmeticFunction.cardFactors n = 1 ↔ n.Prime :=
    ArithmeticFunction.cardFactors_eq_one_iff_prime
  have hb := softProjector_pow_bounds ht0 ht1 hk
  unfold softProjector
  rw [show (if n.Prime then (1 : ℝ) else 0)
      = (if ArithmeticFunction.cardFactors n = 1 then (1 : ℝ) else 0) by
    by_cases hp : n.Prime <;> simp [hp, hiff]]
  exact hb

/-! ## The per-prime pair Euler factor of the ω-model (§31) -/

/-- The single-prime `ω`-model factor `u_p(t) = (p−1+t)/p`. -/
noncomputable def uOmega (p : ℕ) (t : ℝ) : ℝ := ((p : ℝ) - 1 + t) / p

/-- The pair `ω`-model factor `v_p(t) = (p−2+2t)/p`. -/
noncomputable def vOmega (p : ℕ) (t : ℝ) : ℝ := ((p : ℝ) - 2 + 2 * t) / p

/-- The pair Euler ratio `γ_p^{(ω)}(t) = 1 − (1−t)²/(p−1+t)²`. -/
noncomputable def gammaOmega (p : ℕ) (t : ℝ) : ℝ := 1 - (1 - t) ^ 2 / ((p : ℝ) - 1 + t) ^ 2

/-- **Pair Euler factor (§31).** The normalized pair factor `v/u²` equals
    `1 − (1−t)²/(p−1+t)²` — an EXACT per-prime rational identity. -/
theorem gammaOmega_eq {p : ℕ} {t : ℝ} (hp : (p : ℝ) ≠ 0) (hpt : (p : ℝ) - 1 + t ≠ 0) :
    vOmega p t / (uOmega p t) ^ 2 = gammaOmega p t := by
  unfold uOmega vOmega gammaOmega
  field_simp
  ring

end Projector
end Geometric
end EuclidsPath
