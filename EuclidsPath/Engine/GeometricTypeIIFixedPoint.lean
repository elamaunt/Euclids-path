/-
  GeometricTypeIIFixedPoint — the one-defect fixed point: no finite even moment breaks the wall.

  ORIGIN (parity_wall Prime-Chaos session dossier §26 / §27 / §28). Locally the character
  eigenvalues are `λ(1) = 1`, `λ(χ) = −1/m` (`χ ≠ 1`), with `m + 1 = p − 1` characters.  For any
  moment order and any nontrivial shift `θ`, the "one-defect" contraction
  `B_{k,p}(θ) = Σ_χ λ(χ)^{2k−1} λ(χθ)` collapses EXACTLY to `−(1/m) A_{k,p}` where
  `A_{k,p} = Σ_χ |λ(χ)|^{2k}` — i.e. every finite even moment reproduces the SAME parity eigenvalue
  `−1/m = −1/(p−2)`.  Hence `S₄, S₆, S₈, …` by themselves do NOT break the wall.

  We formalize abstractly: `ι` finite of card `m+1`, a two-valued `f` (`f i₀ = 1`, `f i = −1/m`
  off `i₀`), and a permutation `σ` with `σ i₀ ≠ i₀` (the nontrivial shift).  The whole content is
  a finite delta-decomposition of the product `f(χ)^{2j+1} f(σχ)`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `A_moment` — `Σ_χ f(χ)^{2j+2} = 1 + (m)·v^{2j+2}` (the even moment, `v = −1/m`);
    * `one_defect_fixed_point` — `Σ_χ f(χ)^{2j+1} f(σχ) = (−1/m)·Σ_χ f(χ)^{2j+2}` (the wall
      eigenvalue reproduced at every order).

  DISCLOSURE. This is a no-go: the eigenvalue `−1/(p−2)` is a fixed point of every even moment, so
  higher moments alone cannot break the parity wall (§59). twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## Two elementary finite-sum facts -/

private theorem sum_ite_const {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (A B : ℝ) :
    ∑ χ : ι, (if χ = i₀ then A else B) = A + ((Fintype.card ι : ℝ) - 1) * B := by
  have h : ∀ χ : ι, (if χ = i₀ then A else B) = B + (if χ = i₀ then A - B else 0) := by
    intro χ; by_cases hχ : χ = i₀ <;> simp [hχ]
  rw [Finset.sum_congr rfl (fun χ _ => h χ), Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ i₀), Finset.card_univ, nsmul_eq_mul]
  ring

private theorem sum_indicator_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ∑ χ : ι, (if χ = a then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]

/-! ## The even moment and the one-defect fixed point (§27) -/

/-- **Even moment (§27).** `Σ_χ f(χ)^{2j+2} = 1 + m·v^{2j+2}`, `v = −1/m`. -/
theorem A_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (m : ℕ) (hm : Fintype.card ι = m + 1) (j : ℕ)
    (f : ι → ℝ) (hf0 : f i₀ = 1) (hf1 : ∀ i, i ≠ i₀ → f i = -1 / (m : ℝ)) :
    ∑ χ, (f χ) ^ (2 * j + 2) = 1 + (m : ℝ) * (-1 / (m : ℝ)) ^ (2 * j + 2) := by
  have hcard : (Fintype.card ι : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  have hpt : ∀ χ : ι, (f χ) ^ (2 * j + 2)
      = if χ = i₀ then (1 : ℝ) else (-1 / (m : ℝ)) ^ (2 * j + 2) := by
    intro χ; by_cases h : χ = i₀
    · rw [if_pos h, h, hf0, one_pow]
    · rw [if_neg h, hf1 χ h]
  rw [Finset.sum_congr rfl (fun χ _ => hpt χ), sum_ite_const i₀ 1 _, hcard]
  ring

/-- **One-defect fixed point (§27).** For any moment order `j` and any nontrivial shift `σ`, the
    contraction `Σ_χ f(χ)^{2j+1} f(σχ)` equals `(−1/m)` times the even moment — the parity
    eigenvalue `−1/(p−2)` is reproduced at every order.  Higher moments alone do not break the wall. -/
theorem one_defect_fixed_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) (j : ℕ)
    (f : ι → ℝ) (hf0 : f i₀ = 1) (hf1 : ∀ i, i ≠ i₀ → f i = -1 / (m : ℝ))
    (σ : Equiv.Perm ι) (hσ : σ i₀ ≠ i₀) :
    ∑ χ, (f χ) ^ (2 * j + 1) * f (σ χ) = (-1 / (m : ℝ)) * ∑ χ, (f χ) ^ (2 * j + 2) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcard : (Fintype.card ι : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  set v : ℝ := -1 / (m : ℝ) with hv
  set w : ℝ := v ^ (2 * j + 1) with hw
  have hi₀ne : i₀ ≠ σ⁻¹ i₀ := by
    intro h
    apply hσ
    have h2 : σ (σ⁻¹ i₀) = i₀ := by simp
    rw [← h] at h2
    exact h2
  -- pointwise forms
  have hBodd : ∀ χ : ι, (f χ) ^ (2 * j + 1) = if χ = i₀ then (1 : ℝ) else w := by
    intro χ; by_cases h : χ = i₀
    · rw [if_pos h, h, hf0, one_pow]
    · rw [if_neg h, hf1 χ h, hw]
  have hBsig : ∀ χ : ι, f (σ χ) = if χ = σ⁻¹ i₀ then (1 : ℝ) else v := by
    intro χ; by_cases h : χ = σ⁻¹ i₀
    · rw [if_pos h, h, show σ (σ⁻¹ i₀) = i₀ from by simp, hf0]
    · rw [if_neg h]; apply hf1; intro hc; apply h; rw [← hc]; simp
  have hdecomp : ∀ χ : ι, (f χ) ^ (2 * j + 1) * f (σ χ)
      = w * v + (1 - w) * v * (if χ = i₀ then (1 : ℝ) else 0)
          + w * (1 - v) * (if χ = σ⁻¹ i₀ then (1 : ℝ) else 0) := by
    intro χ
    rw [hBodd, hBsig]
    by_cases hA : χ = i₀
    · subst hA
      rw [if_pos rfl, if_neg hi₀ne, if_pos rfl, if_neg hi₀ne]; ring
    · by_cases hB : χ = σ⁻¹ i₀
      · subst hB
        rw [if_neg hA, if_pos rfl, if_neg hA, if_pos rfl]; ring
      · rw [if_neg hA, if_neg hB, if_neg hA, if_neg hB]; ring
  have hB : ∑ χ, (f χ) ^ (2 * j + 1) * f (σ χ)
      = w * v * (Fintype.card ι : ℝ) + (1 - w) * v + w * (1 - v) := by
    rw [Finset.sum_congr rfl (fun χ _ => hdecomp χ), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum,
      sum_indicator_eq_one i₀, sum_indicator_eq_one (σ⁻¹ i₀)]
    ring
  have hA : ∑ χ, (f χ) ^ (2 * j + 2) = 1 + (m : ℝ) * v ^ (2 * j + 2) := by
    have := A_moment i₀ m hm j f hf0 hf1
    rw [← hv] at this
    exact this
  have hvw : v ^ (2 * j + 2) = w * v := by rw [hw, ← pow_succ]
  rw [hB, hA, hcard, hvw, hv]
  field_simp
  ring

/-! ## The full S₄ profile table (§26)

The five profiles of the S₄ opening, classified by the multiplicity partition of the shifts.
`[4]` is `A_moment` at `k = 2` (the even moment itself, of order ONE — the main term, NOT a defect
sector); `[3+1]` is `one_defect_fixed_point` (the unique NON-summable defect, `−1/m` scale).  Below:
the three remaining profiles `[2+2]`, `[2+1+1]`, `[1+1+1+1]` are computed EXACTLY and are all
`O(1/m²)` — summable (criterion B).  So among the OFF-DIAGONAL profiles the one-defect `[3+1]` is
the only non-summable one: this LOCALIZES the non-summable ambient S₄ sector, it does not shrink
it — `[3+1]` carries exactly the parity eigenvalue `−1/(p−2)`, so higher moments alone still do not
break the wall (§59).

AMBIENT DISCLOSURE (§57). These are full-character-group computations; by the withdrawn overclaim
of dossier §57, ambient S₄ does NOT transfer to the short rectangle — restriction to a short
arithmetic trajectory can sharply increase coherence, and no short-interval statement is made or
implied here. -/

/-- The shifted local factor: `1` at the marked point `a`, `−1/m` elsewhere.  For a two-valued `f`
    and a permutation `σ`, `f(σχ) = onePoint (σ⁻¹ i₀) m χ` (`shift_eq_onePoint`). -/
noncomputable def onePoint {ι : Type*} [DecidableEq ι] (a : ι) (m : ℕ) : ι → ℝ :=
  fun χ => if χ = a then 1 else -1 / (m : ℝ)

/-- Bridge: a shifted two-valued factor is `onePoint` at the shifted marked point. -/
theorem shift_eq_onePoint {ι : Type*} [DecidableEq ι] (i₀ : ι) (m : ℕ) (f : ι → ℝ)
    (hf0 : f i₀ = 1) (hf1 : ∀ i, i ≠ i₀ → f i = -1 / (m : ℝ)) (σ : Equiv.Perm ι) (χ : ι) :
    f (σ χ) = onePoint (σ⁻¹ i₀) m χ := by
  unfold onePoint
  by_cases h : χ = σ⁻¹ i₀
  · rw [if_pos h, h]
    simp [hf0]
  · rw [if_neg h]
    apply hf1
    intro hc
    apply h
    rw [← hc]
    simp

/-- **Profile [2+2] (§26).** `Σ_χ (onePoint a)²(onePoint b)² = 2/m² + 1/m³ − 1/m⁴` for `a ≠ b`:
    exactly `O(1/m²)` — summable. -/
theorem s4_profile_22 {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) :
    ∑ χ, (onePoint a m χ) ^ 2 * (onePoint b m χ) ^ 2
      = 2 / (m : ℝ) ^ 2 + 1 / (m : ℝ) ^ 3 - 1 / (m : ℝ) ^ 4 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpt : ∀ χ : ι, (onePoint a m χ) ^ 2 * (onePoint b m χ) ^ 2
      = 1 / (m : ℝ) ^ 4
        + (1 / (m : ℝ) ^ 2 - 1 / (m : ℝ) ^ 4) * (if χ = a then 1 else 0)
        + (1 / (m : ℝ) ^ 2 - 1 / (m : ℝ) ^ 4) * (if χ = b then 1 else 0) := by
    intro χ
    unfold onePoint
    by_cases ha : χ = a
    · subst ha
      rw [if_pos rfl, if_neg hab, if_pos rfl, if_neg hab]
      field_simp
      ring
    · by_cases hb : χ = b
      · subst hb
        rw [if_neg (fun h => hab h.symm), if_pos rfl, if_neg (fun h => hab h.symm), if_pos rfl]
        field_simp
        ring
      · rw [if_neg ha, if_neg hb, if_neg ha, if_neg hb]
        field_simp
        ring
  rw [Finset.sum_congr rfl (fun χ _ => hpt χ), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_indicator_eq_one a, sum_indicator_eq_one b, Finset.card_univ, hm, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **Profile [2+1+1] (§26).** `Σ_χ (onePoint a)²(onePoint b)(onePoint c) = 1/m² − 1/m³ − 2/m⁴`
    for pairwise distinct `a, b, c`: exactly `O(1/m²)` — summable. -/
theorem s4_profile_211 {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) :
    ∑ χ, (onePoint a m χ) ^ 2 * (onePoint b m χ) * (onePoint c m χ)
      = 1 / (m : ℝ) ^ 2 - 1 / (m : ℝ) ^ 3 - 2 / (m : ℝ) ^ 4 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpt : ∀ χ : ι, (onePoint a m χ) ^ 2 * (onePoint b m χ) * (onePoint c m χ)
      = 1 / (m : ℝ) ^ 4
        + (1 / (m : ℝ) ^ 2 - 1 / (m : ℝ) ^ 4) * (if χ = a then 1 else 0)
        + (-(1 / (m : ℝ) ^ 3) - 1 / (m : ℝ) ^ 4) * (if χ = b then 1 else 0)
        + (-(1 / (m : ℝ) ^ 3) - 1 / (m : ℝ) ^ 4) * (if χ = c then 1 else 0) := by
    intro χ
    unfold onePoint
    by_cases ha : χ = a
    · subst ha
      rw [if_pos rfl, if_neg hab, if_neg hac, if_pos rfl, if_neg hab, if_neg hac]
      field_simp
      ring
    · by_cases hb : χ = b
      · subst hb
        rw [if_neg (fun h => hab h.symm), if_pos rfl, if_neg hbc,
          if_neg (fun h => hab h.symm), if_pos rfl, if_neg hbc]
        field_simp
        ring
      · by_cases hc : χ = c
        · subst hc
          rw [if_neg (fun h => hac h.symm), if_neg (fun h => hbc h.symm), if_pos rfl,
            if_neg (fun h => hac h.symm), if_neg (fun h => hbc h.symm), if_pos rfl]
          field_simp
          ring
        · rw [if_neg ha, if_neg hb, if_neg hc, if_neg ha, if_neg hb, if_neg hc]
          field_simp
          ring
  rw [Finset.sum_congr rfl (fun χ _ => hpt χ), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_indicator_eq_one a, sum_indicator_eq_one b, sum_indicator_eq_one c,
    Finset.card_univ, hm, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **Profile [1+1+1+1] (§26).** `Σ_χ ∏ᵢ onePoint aᵢ = −3/m³ − 3/m⁴` for pairwise distinct marked
    points: exactly `O(1/m³)` — the fully connected profile, summable. -/
theorem s4_profile_1111 {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) :
    ∑ χ, (onePoint a m χ) * (onePoint b m χ) * (onePoint c m χ) * (onePoint d m χ)
      = -(3 / (m : ℝ) ^ 3) - 3 / (m : ℝ) ^ 4 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpt : ∀ χ : ι, (onePoint a m χ) * (onePoint b m χ) * (onePoint c m χ) * (onePoint d m χ)
      = 1 / (m : ℝ) ^ 4
        + (-(1 / (m : ℝ) ^ 3) - 1 / (m : ℝ) ^ 4) * (if χ = a then 1 else 0)
        + (-(1 / (m : ℝ) ^ 3) - 1 / (m : ℝ) ^ 4) * (if χ = b then 1 else 0)
        + (-(1 / (m : ℝ) ^ 3) - 1 / (m : ℝ) ^ 4) * (if χ = c then 1 else 0)
        + (-(1 / (m : ℝ) ^ 3) - 1 / (m : ℝ) ^ 4) * (if χ = d then 1 else 0) := by
    intro χ
    unfold onePoint
    by_cases ha : χ = a
    · subst ha
      rw [if_pos rfl, if_neg hab, if_neg hac, if_neg had,
        if_pos rfl, if_neg hab, if_neg hac, if_neg had]
      field_simp
      ring
    · by_cases hb : χ = b
      · subst hb
        rw [if_neg (fun h => hab h.symm), if_pos rfl, if_neg hbc, if_neg hbd,
          if_neg (fun h => hab h.symm), if_pos rfl, if_neg hbc, if_neg hbd]
        field_simp
        ring
      · by_cases hc : χ = c
        · subst hc
          rw [if_neg (fun h => hac h.symm), if_neg (fun h => hbc h.symm), if_pos rfl, if_neg hcd,
            if_neg (fun h => hac h.symm), if_neg (fun h => hbc h.symm), if_pos rfl, if_neg hcd]
          field_simp
          ring
        · by_cases hd : χ = d
          · subst hd
            rw [if_neg (fun h => had h.symm), if_neg (fun h => hbd h.symm),
              if_neg (fun h => hcd h.symm), if_pos rfl,
              if_neg (fun h => had h.symm), if_neg (fun h => hbd h.symm),
              if_neg (fun h => hcd h.symm), if_pos rfl]
            field_simp
            ring
          · rw [if_neg ha, if_neg hb, if_neg hc, if_neg hd,
              if_neg ha, if_neg hb, if_neg hc, if_neg hd]
            field_simp
            ring
  rw [Finset.sum_congr rfl (fun χ _ => hpt χ), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_indicator_eq_one a, sum_indicator_eq_one b, sum_indicator_eq_one c,
    sum_indicator_eq_one d, Finset.card_univ, hm, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-! ## The off-diagonal profiles are summable (criterion B) -/

/-- `[2+2]` is `O(1/m²)`: `|Σ| ≤ 3/m²`. -/
theorem s4_profile_22_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) :
    |∑ χ, (onePoint a m χ) ^ 2 * (onePoint b m χ) ^ 2| ≤ 3 / (m : ℝ) ^ 2 := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmp : (0 : ℝ) < (m : ℝ) := by linarith
  rw [s4_profile_22 hab m hm hm1]
  have h43 : 1 / (m : ℝ) ^ 4 ≤ 1 / (m : ℝ) ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hmr (show (0:ℝ) ≤ (m:ℝ)^3 by positivity)]
  have h32 : 1 / (m : ℝ) ^ 3 ≤ 1 / (m : ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hmr (show (0:ℝ) ≤ (m:ℝ)^2 by positivity)]
  have h2 : (0:ℝ) < 1 / (m : ℝ) ^ 2 := by positivity
  have h40 : (0:ℝ) ≤ 1 / (m : ℝ) ^ 4 := by positivity
  have e2 : 2 / (m : ℝ) ^ 2 = 2 * (1 / (m : ℝ) ^ 2) := by ring
  have e3 : 3 / (m : ℝ) ^ 2 = 3 * (1 / (m : ℝ) ^ 2) := by ring
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- `[2+1+1]` is `O(1/m²)`: `|Σ| ≤ 2/m²` for `m ≥ 2`. -/
theorem s4_profile_211_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (m : ℕ) (hm : Fintype.card ι = m + 1) (hm2 : 2 ≤ m) :
    |∑ χ, (onePoint a m χ) ^ 2 * (onePoint b m χ) * (onePoint c m χ)| ≤ 2 / (m : ℝ) ^ 2 := by
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  rw [s4_profile_211 hab hac hbc m hm (by omega)]
  have e : 1 / (m : ℝ) ^ 2 - 1 / (m : ℝ) ^ 3 - 2 / (m : ℝ) ^ 4
      = ((m : ℝ) ^ 2 - (m : ℝ) - 2) / (m : ℝ) ^ 4 := by
    field_simp
  have hnum : (0:ℝ) ≤ (m : ℝ) ^ 2 - (m : ℝ) - 2 := by nlinarith
  have hV0 : (0:ℝ) ≤ 1 / (m : ℝ) ^ 2 - 1 / (m : ℝ) ^ 3 - 2 / (m : ℝ) ^ 4 := by
    rw [e]
    exact div_nonneg hnum (by positivity)
  rw [abs_of_nonneg hV0]
  have h3 : (0:ℝ) ≤ 1 / (m : ℝ) ^ 3 := by positivity
  have h4 : (0:ℝ) ≤ 2 / (m : ℝ) ^ 4 := by positivity
  have h2 : (0:ℝ) ≤ 1 / (m : ℝ) ^ 2 := by positivity
  have e2 : 2 / (m : ℝ) ^ 2 = 2 * (1 / (m : ℝ) ^ 2) := by ring
  linarith

/-- `[1+1+1+1]` is `O(1/m³)`: `|Σ| ≤ 6/m³` — the fully connected budget. -/
theorem s4_profile_1111_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (m : ℕ) (hm : Fintype.card ι = m + 1) (hm1 : 1 ≤ m) :
    |∑ χ, (onePoint a m χ) * (onePoint b m χ) * (onePoint c m χ) * (onePoint d m χ)|
      ≤ 6 / (m : ℝ) ^ 3 := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  rw [s4_profile_1111 hab hac had hbc hbd hcd m hm hm1]
  have h43 : 1 / (m : ℝ) ^ 4 ≤ 1 / (m : ℝ) ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hmr (show (0:ℝ) ≤ (m:ℝ)^3 by positivity)]
  have h3 : (0:ℝ) ≤ 3 / (m : ℝ) ^ 3 := by positivity
  have h4 : (0:ℝ) ≤ 3 / (m : ℝ) ^ 4 := by positivity
  have e3 : 3 / (m : ℝ) ^ 4 = 3 * (1 / (m : ℝ) ^ 4) := by ring
  have e4 : 3 / (m : ℝ) ^ 3 = 3 * (1 / (m : ℝ) ^ 3) := by ring
  have e6 : 6 / (m : ℝ) ^ 3 = 6 * (1 / (m : ℝ) ^ 3) := by ring
  rw [abs_of_nonpos (by linarith)]
  linarith

end TypeII
end Geometric
end EuclidsPath
