/-
  GeometricTypeIIForest — the forest recursion and the exact nonlocal closure.

  ORIGIN (parity_wall Prime-Chaos session dossier §30 / §33 / §34 / §35 / §36). The soft product
  `F_j = ∏_{i<j}(1 + c_{p_i})` satisfies the leaf-stripping recursion `F_J − 1 = Σ_j c_{p_j} F_{j−1}`
  (§30).  The centered local factor `1 + θ c_p(n)` factors through the Euler datum
  `a_p(θ)(1 − g_p(θ) 1_{p|L(n)})` (§35), and the local telescoping `a_p(θ)(1 − g_p(θ)/(p−1)) = 1`
  (§36) makes the main term collapse: after multiplicative expansion, ALL adapted backgrounds sum
  to `X_γ` plus a SINGLE signed dispersion remainder `Σ_d μ(d) R(d)`.  Rigidity (§34) pins the
  unique normalized hard annihilator to `(p−1)/(p−2)`; the soft factor stays in `[0, 1−θ]` (§33).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `forest_step`, `forest_telescope` — the exact leaf-stripping recursion (§30);
    * `soft_euler_factor` — `1 + θc_p = a_p(θ)(1 − g_p(θ)1_{p|L})` (§35);
    * `soft_euler_telescope` — `a_p(θ)(1 − g_p(θ)/(p−1)) = 1` (the main-term collapse, §36);
    * `local_rigidity` — the unique normalized hard annihilator is `(p−1)/(p−2)` (§34);
    * `soft_factor_bound` — the forbidden soft factor lies in `[0, 1−θ]` (§33).

  DISCLOSURE. The forest recursion is algebraically CLOSED into a single Möbius remainder; that
  remainder is the open target (the restriction-curvature commutator §29 and the information-horizon
  no-go §32 say it cannot be summed positively). twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The leaf-stripping forest recursion (§30) -/

/-- The soft product `F_j = ∏_{i<j}(1 + c_i)`. -/
noncomputable def forestProd (c : ℕ → ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (1 + c i)

/-- **Forest step (§30).** `F_{j+1} = (1 + c_j) F_j`. -/
theorem forest_step (c : ℕ → ℝ) (j : ℕ) : forestProd c (j + 1) = (1 + c j) * forestProd c j := by
  unfold forestProd
  rw [Finset.prod_range_succ]
  ring

/-- **Leaf-stripping recursion (§30).** `F_J − 1 = Σ_{j<J} c_j F_j`. -/
theorem forest_telescope (c : ℕ → ℝ) (J : ℕ) :
    forestProd c J - 1 = ∑ j ∈ Finset.range J, c j * forestProd c j := by
  induction J with
  | zero => simp [forestProd]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, forest_step]
    ring

/-! ## The soft Euler factorization and the main-term collapse (§35 / §36) -/

/-- **Soft Euler factor (§35).** `1 + θ c_p = a_p(θ)(1 − g_p(θ) 1_{p|L})`, where the centered local
    kernel `c_p` is `−1` on forbidden cells and `1/(p−2)` on allowed cells. -/
theorem soft_euler_factor (p : ℕ) (θ : ℝ) (hp : 5 ≤ p) (hθ : 0 ≤ θ) (fb : Prop) [Decidable fb] :
    1 + θ * (if fb then (-1 : ℝ) else 1 / ((p : ℝ) - 2))
      = ((p : ℝ) - 2 + θ) / ((p : ℝ) - 2)
          * (1 - θ * ((p : ℝ) - 1) / ((p : ℝ) - 2 + θ) * (if fb then (1 : ℝ) else 0)) := by
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hpθ : (p : ℝ) - 2 + θ ≠ 0 := by linarith
  by_cases h : fb
  · simp only [if_pos h]; field_simp; ring
  · simp only [if_neg h]; field_simp; ring

/-- **Main-term collapse (§36).** `a_p(θ)(1 − g_p(θ)/(p−1)) = 1`.  This local telescoping makes the
    principal part of every adapted background collapse to `X_γ`. -/
theorem soft_euler_telescope (p : ℕ) (θ : ℝ) (hp : 5 ≤ p) (hθ : 0 ≤ θ) :
    ((p : ℝ) - 2 + θ) / ((p : ℝ) - 2)
        * (1 - (θ * ((p : ℝ) - 1) / ((p : ℝ) - 2 + θ)) / ((p : ℝ) - 1)) = 1 := by
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpθ : (p : ℝ) - 2 + θ ≠ 0 := by linarith
  field_simp
  ring

/-! ## Local rigidity (§34) -/

/-- **Local rigidity (§34).** A normalized hard annihilator (zero on the forbidden cell, mean one)
    is FORCED to take value `(p−1)/(p−2)` on the allowed cells: the eigenvalue `−1/(p−2)` cannot be
    locally reduced. -/
theorem local_rigidity (p : ℕ) (x : ℝ) (hp : 5 ≤ p) (hmean : ((p : ℝ) - 2) * x = (p : ℝ) - 1) :
    x = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  rw [eq_div_iff hp2]
  linear_combination hmean

/-! ## The soft-recursion sandwich, local factor (§33) -/

/-- **Soft factor bound (§33).** For `0 ≤ θ ≤ 1` the forbidden soft factor `(1−θ)/(1+θ/(p−2))`
    lies in `[0, 1−θ]`, so `0 ≤ G_θ − S ≤ 1 − θ` locally. -/
theorem soft_factor_bound (p : ℕ) (θ : ℝ) (hp : 5 ≤ p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 ≤ (1 - θ) / (1 + θ / ((p : ℝ) - 2)) ∧ (1 - θ) / (1 + θ / ((p : ℝ) - 2)) ≤ 1 - θ := by
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hden : (1 : ℝ) ≤ 1 + θ / ((p : ℝ) - 2) := by
    have : 0 ≤ θ / ((p : ℝ) - 2) := div_nonneg hθ0 (le_of_lt hp2)
    linarith
  have hnum : (0 : ℝ) ≤ 1 - θ := by linarith
  refine ⟨div_nonneg hnum (by linarith), ?_⟩
  exact div_le_self hnum hden

end TypeII
end Geometric
end EuclidsPath
