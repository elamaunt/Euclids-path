/-
  GeometricTypeIIDegreeTwo — the degree-two (p,q) layer: exact one-defect contraction and the
  fully-connected S₄ budget.

  ORIGIN (parity_wall Prime-Chaos session dossier §51 / §67 steps 3–4). In the S₄ opening of the
  degree-two exact-conductor layer `c = pq` the local profiles factor over the two primes.  When
  the p-side is in the one-defect profile `[3+1]`, the fixed-point formula CONTRACTS it exactly:
  the whole (p,q)-block factors as `(−1/(p−2)) × (even moment at p) × (pure degree-one sum in q)` —
  a well-founded dimension reduction (chaos degree two → one, criterion C).  When BOTH sides are
  fully connected (`[1+1+1+1]` at each prime), the block is bounded by `36/((p−2)³(q−2)³)` —
  summable in both primes (criterion B; matches `degree_two_S4_mass`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `prod_sum_factor` — the (χ,ψ)-sum over a product functional factors exactly;
    * `degree_two_one_defect_contraction` — the `[3+1]`-defect sector of the (p,q) layer equals
      `(−1/m) · (Σ_χ f(χ)^{2j+2}) · (Σ_ψ G(ψ))`: chaos degree two → one, EXACTLY (criterion C);
    * `degree_two_connected_budget` — the fully-connected (p,q)-block is `≤ 36/(m³n³)` (criterion B).

  DISCLOSURE (the wall is NOT moved, renamed, or hidden):
    * All results here are exact AMBIENT local algebra (full CRT space).  By dossier §57 (withdrawn
      overclaim), ambient S₄ does NOT transfer to the short rectangle: neither the contraction nor
      the connected budget bounds the short Type-II restriction, and their conjunction with the S₄
      profile table does NOT close the degree-two layer — the ambient-to-short transfer IS the wall.
    * The degree-one layer reached by the contraction is closed only under standard analytic inputs
      (prime-conductor large sieve, dossier §64), not unconditionally in Lean.
    * The short restriction of the degree-two connected core remains EXACTLY the existing open
      target `SemiprimeShortRestriction` (residual C); `ω(c) ≥ 3` is `HigherConductorDispersion`
      (residual D).  This module introduces NO new open Prop and renames nothing.
    * Nothing here proves twins; twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIFixedPoint

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The product factorization -/

/-- The (χ,ψ)-sum over a product functional factors exactly. -/
theorem prod_sum_factor {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → ℝ) (G : κ → ℝ) :
    ∑ x : ι × κ, F x.1 * G x.2 = (∑ χ : ι, F χ) * (∑ ψ : κ, G ψ) := by
  rw [Finset.sum_mul_sum]
  exact Fintype.sum_prod_type _

/-! ## The one-defect contraction: chaos degree two → one (§51, criterion C) -/

/-- **Degree-two one-defect contraction (§51).** When the p-side of the (p,q)-block is in the
    one-defect profile `[3+1]`, the WHOLE block contracts exactly to
    `(−1/m) · (even moment at p) · (pure degree-one sum in q)`: the parity eigenvalue `−1/(p−2)`
    times a degree-ONE object — a well-founded dimension reduction (criterion C).  The remaining
    degree-one layer is the prime-conductor front (closed under standard large-sieve inputs). -/
theorem degree_two_one_defect_contraction {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (i₀ : ι) (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) (j : ℕ)
    (f : ι → ℝ) (hf0 : f i₀ = 1) (hf1 : ∀ i, i ≠ i₀ → f i = -1 / (m : ℝ))
    (σ : Equiv.Perm ι) (hσ : σ i₀ ≠ i₀) (G : κ → ℝ) :
    ∑ x : ι × κ, (f x.1) ^ (2 * j + 1) * f (σ x.1) * G x.2
      = (-1 / (m : ℝ)) * (∑ χ : ι, (f χ) ^ (2 * j + 2)) * (∑ ψ : κ, G ψ) := by
  have hfactor : ∑ x : ι × κ, (f x.1) ^ (2 * j + 1) * f (σ x.1) * G x.2
      = (∑ χ : ι, (f χ) ^ (2 * j + 1) * f (σ χ)) * (∑ ψ : κ, G ψ) :=
    prod_sum_factor (fun χ => (f χ) ^ (2 * j + 1) * f (σ χ)) G
  rw [hfactor, one_defect_fixed_point i₀ m hm hm1 j f hf0 hf1 σ hσ]

/-! ## The fully-connected budget (criterion B) -/

/-- **Fully-connected degree-two budget (§51).** When BOTH primes are in the fully-connected
    profile `[1+1+1+1]`, the (p,q)-block is bounded by `36/(m³n³)` — summable in both primes
    (`m = p−2`, `n = q−2`; matches `degree_two_S4_mass`). -/
theorem degree_two_connected_budget {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {a b c d : ι} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {a' b' c' d' : κ} (hab' : a' ≠ b') (hac' : a' ≠ c') (had' : a' ≠ d')
    (hbc' : b' ≠ c') (hbd' : b' ≠ d') (hcd' : c' ≠ d')
    (m n : ℕ) (hm : Fintype.card ι = m + 1) (hn : Fintype.card κ = n + 1)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) :
    |∑ x : ι × κ,
        ((onePoint a m x.1) * (onePoint b m x.1) * (onePoint c m x.1) * (onePoint d m x.1))
          * ((onePoint a' n x.2) * (onePoint b' n x.2) * (onePoint c' n x.2)
              * (onePoint d' n x.2))|
      ≤ 36 / ((m : ℝ) ^ 3 * (n : ℝ) ^ 3) := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rw [prod_sum_factor
    (fun χ => (onePoint a m χ) * (onePoint b m χ) * (onePoint c m χ) * (onePoint d m χ))
    (fun ψ => (onePoint a' n ψ) * (onePoint b' n ψ) * (onePoint c' n ψ) * (onePoint d' n ψ)),
    abs_mul]
  have h1 := s4_profile_1111_bound hab hac had hbc hbd hcd m hm hm1
  have h2 := s4_profile_1111_bound hab' hac' had' hbc' hbd' hcd' n hn hn1
  calc |∑ χ : ι, (onePoint a m χ) * (onePoint b m χ) * (onePoint c m χ) * (onePoint d m χ)|
        * |∑ ψ : κ, (onePoint a' n ψ) * (onePoint b' n ψ) * (onePoint c' n ψ) * (onePoint d' n ψ)|
      ≤ (6 / (m : ℝ) ^ 3) * (6 / (n : ℝ) ^ 3) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 36 / ((m : ℝ) ^ 3 * (n : ℝ) ^ 3) := by
        rw [div_mul_div_comm]
        norm_num

end TypeII
end Geometric
end EuclidsPath
