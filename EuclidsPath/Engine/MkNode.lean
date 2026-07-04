/-
  mkNode: construction of a RankNode from a clean composite side. Formalisation of the author's file.
  Source: step00 extraction of RankNode from GlobalOldAbsorption (2026-07-01). Prose: prose/34_MkNode.md.

  Provable ARITHMETIC (here, without named inputs):
    • prod_ge: list of factors >A ⟹ (A+1)^len ≤ prod;
    • factor_rank_le_four: factors >A, prod ≤ 6X_A+1 < A^5 ⟹ len ≤ 4;
    • composite_rank_ge_two: 1<N composite ⟹ ≥2 prime factors;
    • prime_factor_gt_A: clean side + p∣side ⟹ p>A;
    • mkNode: primeFactorsList yields a RankNode with factors>A, AmbientLegal, rank 2..4.

  The only genuine remainder (not here) — INFINITY of nodeable centres from GlobalOldAbsorption.
-/
import Mathlib
import EuclidsPath.Engine.ProductCore

set_option autoImplicit false

namespace EuclidsPath.MkNode

open EuclidsPath.ProductCore

/-- **prod ≥ (A+1)^len** for a list of factors `> A`. -/
theorem prod_ge_of_factors_gt {A : ℕ} (L : List ℕ) (h : ∀ a ∈ L, A < a) :
    (A + 1) ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.prod_cons, pow_succ]
    have hx : A + 1 ≤ x := h x (by simp)
    have hxs : (A + 1) ^ xs.length ≤ xs.prod := ih (fun a ha => h a (by simp [ha]))
    calc (A + 1) ^ xs.length * (A + 1) ≤ xs.prod * x := Nat.mul_le_mul hxs hx
      _ = x * xs.prod := by ring

/--
  **factor_rank_le_four (§7) — PROVED.** A list of prime factors `> A` with product
  `≤ 6X_A+1 < A^5` has length `≤ 4`. (Otherwise `(A+1)^5 ≤ prod ≤ 6X_A+1 < A^5 ≤ (A+1)^5`.) -/
theorem factor_rank_le_four {A X_A : ℕ} (L : List ℕ) (hA : 1 ≤ A)
    (hgt : ∀ a ∈ L, A < a) (hprod : L.prod ≤ 6 * X_A + 1) (hscale : 6 * X_A + 1 < A ^ 5) :
    L.length ≤ 4 := by
  by_contra h
  simp only [not_le] at h        -- 5 ≤ L.length (i.e. 4 < length)
  have h5 : (A + 1) ^ 5 ≤ L.prod :=
    le_trans (Nat.pow_le_pow_right (by omega) h) (prod_ge_of_factors_gt L hgt)
  have hA5 : A ^ 5 < (A + 1) ^ 5 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/--
  **composite_rank_ge_two (§7) — PROVED.** `1 < N`, `N` composite ⟹ list of prime factors
  has length `≥ 2`. (Length 0 ⟹ N=1; length 1 ⟹ N prime.) -/
theorem composite_rank_ge_two {N : ℕ} (hN : 1 < N) (hcomp : ¬ N.Prime) :
    2 ≤ (Nat.primeFactorsList N).length := by
  have hprod : (Nat.primeFactorsList N).prod = N := Nat.prod_primeFactorsList (by omega)
  by_contra h
  simp only [not_le] at h        -- length < 2
  interval_cases hl : (Nat.primeFactorsList N).length
  · -- length 0 ⟹ prod = 1 = N, contradiction with 1<N
    have : Nat.primeFactorsList N = [] := List.length_eq_zero_iff.mp hl
    rw [this, List.prod_nil] at hprod; omega
  · -- length 1 ⟹ prod = p = N, and p prime ⟹ N prime
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hl
    have hpp : p ∈ Nat.primeFactorsList N := by rw [hp]; exact List.mem_singleton.mpr rfl
    have hpprime := Nat.prime_of_mem_primeFactorsList hpp
    rw [hp, List.prod_singleton] at hprod      -- p = N
    rw [← hprod] at hcomp; exact hcomp hpprime

/--
  **mkNode (Theorem 7.1) — PROVED.** From `1 < N`, `N` composite, and `∀ p∣N → A<p` one constructs
  `RankNode r` (sign fixed) with `r = len(primeFactorsList N)`, `2 ≤ r ≤ 4`, factors `>A`,
  AmbientLegal (everything divides `N ≤ 6X_A+1`). Returns r, node, and proofs. -/
theorem mkNode_of_composite {A X_A N : ℕ} (sgn : Sign) (hA : 1 ≤ A)
    (hN : 1 < N) (hcomp : ¬ N.Prime) (hNle : N ≤ 6 * X_A + 1) (hscale : 6 * X_A + 1 < A ^ 5)
    (hbig : ∀ p, p.Prime → p ∣ N → A < p) :
    ∃ r, 2 ≤ r ∧ r ≤ 4 ∧ ∃ X : RankNode r,
        AmbientLegal X_A X.factors ∧ (List.ofFn X.factors).prod = N := by
  set L := Nat.primeFactorsList N with hL
  have hr2 : 2 ≤ L.length := composite_rank_ge_two hN hcomp
  have hgt : ∀ a ∈ L, A < a := fun a ha =>
    hbig a (Nat.prime_of_mem_primeFactorsList ha) (Nat.dvd_of_mem_primeFactorsList ha)
  have hprodN : L.prod = N := Nat.prod_primeFactorsList (by omega)
  have hr4 : L.length ≤ 4 := factor_rank_le_four L hA hgt (by rw [hprodN]; exact hNle) hscale
  refine ⟨L.length, hr2, hr4, ⟨sgn, fun i => L.get i⟩, ?_, ?_⟩
  · -- AmbientLegal: every L.get i divides N
    refine ⟨N, by omega, hNle, fun i => ?_⟩
    rw [← hprodN]; exact List.dvd_prod (List.get_mem L i)
  · -- (List.ofFn (L.get ·)).prod = L.prod = N
    simp only []
    rw [List.ofFn_get L]; exact hprodN

/-! ### Connection to carrier: composite side, prime factor > A -/

/-- `Clean A m` (ℕ-form, as in Residuals): no `q≤A` divides either side. -/
def Clean (A m : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))

/--
  **prime_factor_gt_A (Lemma 6.1) — PROVED.** Clean centre + prime `p ∣ 6m+1` (or `6m−1`) ⟹
  `p > A`. (Otherwise `p ≤ A` divides a clean side — contradiction.) -/
theorem prime_factor_gt_A_plus {A m p : ℕ} (hcl : Clean A m) (hp : p.Prime)
    (hdvd : p ∣ (6 * m + 1)) : A < p := by
  by_contra hle
  exact hcl p hp (by omega) (Or.inr hdvd)

theorem prime_factor_gt_A_minus {A m p : ℕ} (hcl : Clean A m) (hp : p.Prime)
    (hdvd : p ∣ (6 * m - 1)) : A < p := by
  by_contra hle
  exact hcl p hp (by omega) (Or.inl hdvd)

/--
  **composite_side_of_clean_not_twin (Lemma 5.1) — PROVED.** If `m` is NOT a twin centre (not both
  sides prime) and both sides are `> 1`, then there exists a side `> 1` that is composite. -/
theorem composite_side_of_not_twin {m : ℕ} (hlo : 1 < 6 * m - 1) (hhi : 1 < 6 * m + 1)
    (hnt : ¬ ((6 * m - 1).Prime ∧ (6 * m + 1).Prime)) :
    (1 < 6 * m - 1 ∧ ¬ (6 * m - 1).Prime) ∨ (1 < 6 * m + 1 ∧ ¬ (6 * m + 1).Prime) := by
  by_cases h1 : (6 * m - 1).Prime
  · by_cases h3 : (6 * m + 1).Prime
    · exact absurd ⟨h1, h3⟩ hnt
    · exact Or.inr ⟨hhi, h3⟩
  · exact Or.inl ⟨hlo, h1⟩

end EuclidsPath.MkNode
