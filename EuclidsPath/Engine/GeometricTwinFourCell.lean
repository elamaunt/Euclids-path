/-
  GeometricTwinFourCell — THE FOUR-CELL SIGN-PATTERN IDENTITY, unconditional
  and finite, plus the conditional sign-pattern equidistribution under the
  named two-point Chowla hypothesis for the split form.

  (1) UNCONDITIONAL (finite combinatorics, `four_cell_identity`).  For any
      window `I : Finset ℕ`, any ±1-valued `a b : ℕ → ℤ` on `I`, and any
      signs `e, d ∈ {1, −1}`:

          4·#{m ∈ I : a m = e ∧ b m = d}
            = |I| + e·Σ_I a + d·Σ_I b + e·d·Σ_I (a·b).

      Proof: pointwise `(1 + e·a m)·(1 + d·b m) = 4·[a m = e ∧ b m = d]`,
      summed over `I` and expanded.

  (2) SPECIALIZATION to the twin wings (`window_four_cell`):
      `a m = λ(6m−1)`, `b m = λ(6m+1)` on `I = Icc 1 X`, so with
      `L− = wingMinusSum`, `L+ = wingPlusSum`, `Lx = crossSum`,

          4·N(e,d) = X + e·L− + d·L+ + e·d·Lx.

      COMMENT-LEVEL TIE to the strike identity: for `e = d = −1` this is the
      `(−1,−1)` cell.  On a rough window (where `Ω(6m∓1) ≤ 2` forces
      `λ = −1` exactly on the primes) the same four-cell algebra restricted
      to the rough window is the repo's exact identity
      `T = (1/4)(A − L− − L+ + Lx)`; here the identity is stated on the FULL
      window `Icc 1 X`, where `A` degenerates to `|I| = X`.

  (3) CONDITIONAL corollary under ONE named hypothesis (house
      named-hypothesis pattern — NO axiom, NO sorry):  `Chowla2Hypothesis`,
      the natural-density two-point Chowla for the split form,
      `Σ_{m ≤ X} λ(6m−1)·λ(6m+1) = o(X)`.  Under it all four sign-pattern
      densities `N(e,d)/X` tend to `1/4`
      (`pattern_density_of_chowla2`).  The single-wing inputs
      `Σ_{m ≤ X} λ(6m∓1) = o(X)` are UNCONDITIONAL — derived here from the
      campaign's proven per-class mod-6 Liouville cancellation
      (`Analytic.liouvilleRes_six_tendsto`) by the exact reindex
      `n = 6m∓1` onto the classes `5` resp. `1 (mod 6)`
      (`wingMinus_eq_res`, `wingPlus_eq_res`).

  DISCLOSURES (mandatory reading before quoting).
    * `Chowla2Hypothesis` is OPEN.  Tao 2016 (Forum Math. Pi) proves the
      LOGARITHMICALLY AVERAGED two-point Chowla; the natural-density form
      used here is strictly stronger and is not known.  Nothing in this
      file proves it, and no theorem here asserts it unconditionally.
    * NOTHING MOVES THE PARITY WALL.  (1) is finite bookkeeping; (3)
      converts one open pair statement into another — equidistribution of
      the four sign cells on the FULL window.  No claim is made on sieved
      (pair-rough) windows, where the wall lives.
    * No new axioms, no sorry.  The twin sorry (`twin_prime_conjecture`)
      is untouched.  This file is NOT registered in `EuclidsPath.lean`.
-/
import Mathlib
import EuclidsPath.Analytic.LiouvilleCancellation

set_option maxHeartbeats 800000

namespace EuclidsPath
namespace Geometric
namespace FourCell

open Finset Filter ArithmeticFunction

/-! ### (1) The unconditional finite four-cell identity -/

/-- A ±1 sign is `1` or `−1`. -/
theorem sign_cases {x : ℤ} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h0 : (x - 1) * (x + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **The pointwise cell factor**: for ±1 values and ±1 target signs,
`(1 + e·x)·(1 + d·y) = 4·[x = e ∧ y = d]`. -/
theorem cell_factor {x y e d : ℤ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    (1 + e * x) * (1 + d * y) = if x = e ∧ y = d then (4 : ℤ) else 0 := by
  rcases sign_cases hx with rfl | rfl <;> rcases sign_cases hy with rfl | rfl <;>
    rcases sign_cases he with rfl | rfl <;> rcases sign_cases hd with rfl | rfl <;>
      norm_num

/-- **THE FOUR-CELL IDENTITY** (unconditional, any finite window): if `a`
and `b` take values in `{1, −1}` on `I`, then for signs `e, d ∈ {1, −1}`
the pattern count `N(e,d) = #{m ∈ I : a m = e ∧ b m = d}` satisfies

`4·N(e,d) = |I| + e·Σ_I a + d·Σ_I b + e·d·Σ_I (a·b)`. -/
theorem four_cell_identity (I : Finset ℕ) (a b : ℕ → ℤ)
    (ha : ∀ m ∈ I, a m ^ 2 = 1) (hb : ∀ m ∈ I, b m ^ 2 = 1)
    {e d : ℤ} (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    4 * ((I.filter fun m => a m = e ∧ b m = d).card : ℤ)
      = (I.card : ℤ) + e * (∑ m ∈ I, a m) + d * (∑ m ∈ I, b m)
        + e * d * (∑ m ∈ I, a m * b m) := by
  have hcell : ∀ m ∈ I, (1 + e * a m) * (1 + d * b m)
      = if a m = e ∧ b m = d then (4 : ℤ) else 0 := fun m hm =>
    cell_factor (ha m hm) (hb m hm) he hd
  calc 4 * ((I.filter fun m => a m = e ∧ b m = d).card : ℤ)
      = ∑ m ∈ I, (if a m = e ∧ b m = d then (4 : ℤ) else 0) := by
        rw [← Finset.sum_boole, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
    _ = ∑ m ∈ I, (1 + e * a m) * (1 + d * b m) :=
        (Finset.sum_congr rfl hcell).symm
    _ = ∑ m ∈ I, (1 + (e * a m + (d * b m + e * d * (a m * b m)))) :=
        Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ _m ∈ I, (1 : ℤ) + (∑ m ∈ I, e * a m + (∑ m ∈ I, d * b m
          + ∑ m ∈ I, e * d * (a m * b m))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (I.card : ℤ) + e * (∑ m ∈ I, a m) + d * (∑ m ∈ I, b m)
        + e * d * (∑ m ∈ I, a m * b m) := by
        rw [Finset.sum_const, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          nsmul_eq_mul, mul_one]
        ring

/-! ### (2) The twin-wing window specialization -/

/-- `λ(n)² = 1` for `n ≠ 0`. -/
theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : (liouville n) ^ 2 = 1 := by
  rw [liouville_apply hn, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The minus-wing window sum `L− = Σ_{m ≤ X} λ(6m−1)`. -/
def wingMinusSum (X : ℕ) : ℤ := ∑ m ∈ Finset.Icc 1 X, liouville (6 * m - 1)

/-- The plus-wing window sum `L+ = Σ_{m ≤ X} λ(6m+1)`. -/
def wingPlusSum (X : ℕ) : ℤ := ∑ m ∈ Finset.Icc 1 X, liouville (6 * m + 1)

/-- The cross window sum `Lx = Σ_{m ≤ X} λ(6m−1)·λ(6m+1)`. -/
def crossSum (X : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 X, liouville (6 * m - 1) * liouville (6 * m + 1)

/-- The sign-pattern count `N(e,d) = #{m ≤ X : λ(6m−1) = e ∧ λ(6m+1) = d}`. -/
def patternCount (X : ℕ) (e d : ℤ) : ℕ :=
  ((Finset.Icc 1 X).filter fun m =>
    liouville (6 * m - 1) = e ∧ liouville (6 * m + 1) = d).card

/-- **The window four-cell identity** (unconditional): on `Icc 1 X`,
`4·N(e,d) = X + e·L− + d·L+ + e·d·Lx`. -/
theorem window_four_cell (X : ℕ) {e d : ℤ} (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    4 * (patternCount X e d : ℤ)
      = (X : ℤ) + e * wingMinusSum X + d * wingPlusSum X
        + e * d * crossSum X := by
  have ha : ∀ m ∈ Finset.Icc 1 X, (liouville (6 * m - 1)) ^ 2 = 1 := by
    intro m hm
    have h1 := (Finset.mem_Icc.mp hm).1
    exact liouville_sq (by omega)
  have hb : ∀ m ∈ Finset.Icc 1 X, (liouville (6 * m + 1)) ^ 2 = 1 := by
    intro m _
    exact liouville_sq (by omega)
  have h := four_cell_identity (Finset.Icc 1 X)
    (fun m => liouville (6 * m - 1)) (fun m => liouville (6 * m + 1))
    ha hb he hd
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h
  unfold patternCount wingMinusSum wingPlusSum crossSum
  exact h

/-! ### The single-wing reindex: `Σ_{m ≤ X} λ(6m∓1)` through the proven
per-class mod-6 Liouville cancellation -/

/-- `(k : ZMod 6) = 5` reads as `k % 6 = 5`. -/
theorem zmod_six_eq_five_iff (k : ℕ) : ((k : ZMod 6) = 5) ↔ k % 6 = 5 := by
  have h5 : ((5 : ℕ) : ZMod 6) = (5 : ZMod 6) := by norm_num
  rw [← h5, ZMod.natCast_eq_natCast_iff']

/-- `(k : ZMod 6) = 1` reads as `k % 6 = 1`. -/
theorem zmod_six_eq_one_iff (k : ℕ) : ((k : ZMod 6) = 1) ↔ k % 6 = 1 := by
  have h1 : ((1 : ℕ) : ZMod 6) = (1 : ZMod 6) := by norm_num
  rw [← h1, ZMod.natCast_eq_natCast_iff']

/-- **The minus-wing reindex**: `L−(X)` IS the class-5 restricted Liouville
summatory at `6X+1` — the map `m ↦ 6m−1` is a bijection of `Icc 1 X` onto
the class-5 elements of `Icc 1 (6X+1)`. -/
theorem wingMinus_eq_res (X : ℕ) :
    ((wingMinusSum X : ℤ) : ℝ)
      = Analytic.liouvilleRes (5 : ZMod 6) ((6 * X + 1 : ℕ) : ℝ) := by
  have hcast : ((wingMinusSum X : ℤ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 X, (liouville (6 * m - 1) : ℝ) := by
    unfold wingMinusSum
    push_cast
    rfl
  have hinjm : ∀ x ∈ Finset.Icc 1 X, ∀ y ∈ Finset.Icc 1 X,
      6 * x - 1 = 6 * y - 1 → x = y := by
    intro x hx y hy hxy
    have hx1 := (Finset.mem_Icc.mp hx).1
    have hy1 := (Finset.mem_Icc.mp hy).1
    omega
  have himg : ∑ m ∈ Finset.Icc 1 X, (liouville (6 * m - 1) : ℝ)
      = ∑ k ∈ (Finset.Icc 1 X).image (fun m => 6 * m - 1),
          (liouville k : ℝ) :=
    (Finset.sum_image (f := fun k => ((liouville k : ℤ) : ℝ)) hinjm).symm
  have hset : (Finset.Icc 1 X).image (fun m => 6 * m - 1)
      = (Finset.Icc 1 (6 * X + 1)).filter
          (fun k : ℕ => ((k : ZMod 6) = 5)) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc,
      zmod_six_eq_five_iff]
    constructor
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      omega
    · rintro ⟨⟨hk1, hk2⟩, hk5⟩
      exact ⟨(k + 1) / 6, by omega, by omega⟩
  rw [hcast, himg, hset]
  unfold Analytic.liouvilleRes
  rw [Nat.floor_natCast, Finset.sum_filter]

/-- **The plus-wing reindex**: the class-1 restricted Liouville summatory at
`6X+1` is `L+(X) + λ(1) = L+(X) + 1` — the class-1 elements of
`Icc 1 (6X+1)` are `{1}` together with the bijective image of `m ↦ 6m+1`. -/
theorem wingPlus_eq_res (X : ℕ) :
    Analytic.liouvilleRes (1 : ZMod 6) ((6 * X + 1 : ℕ) : ℝ)
      = ((wingPlusSum X : ℤ) : ℝ) + 1 := by
  unfold Analytic.liouvilleRes
  rw [Nat.floor_natCast, ← Finset.sum_filter]
  have hpred : (Finset.Icc 1 (6 * X + 1)).filter
        (fun k : ℕ => ((k : ZMod 6) = 1))
      = (Finset.Icc 1 (6 * X + 1)).filter (fun k : ℕ => k % 6 = 1) :=
    Finset.filter_congr fun k _ => zmod_six_eq_one_iff k
  have hset : (Finset.Icc 1 (6 * X + 1)).filter (fun k : ℕ => k % 6 = 1)
      = insert 1 ((Finset.Icc 1 X).image (fun m => 6 * m + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hk6⟩
      by_cases h : k = 1
      · exact Or.inl h
      · exact Or.inr ⟨k / 6, by omega, by omega⟩
    · rintro (rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩) <;> omega
  have hnot : (1 : ℕ) ∉ (Finset.Icc 1 X).image (fun m => 6 * m + 1) := by
    intro hmem
    simp only [Finset.mem_image, Finset.mem_Icc] at hmem
    obtain ⟨m, ⟨hm1, _⟩, hm⟩ := hmem
    omega
  have hinj : ∀ x ∈ Finset.Icc 1 X, ∀ y ∈ Finset.Icc 1 X,
      6 * x + 1 = 6 * y + 1 → x = y := by
    intro x _ y _ hxy
    omega
  rw [hpred, hset, Finset.sum_insert hnot, Finset.sum_image hinj]
  have hl1 : (liouville 1 : ℝ) = 1 := by
    rw [liouville_apply_one]
    norm_num
  rw [hl1]
  unfold wingPlusSum
  push_cast
  ring

/-- The scaled class-restricted summatory tends to `0` along `X ↦ 6X+1`,
divided by `X` — the unconditional engine behind both wings. -/
theorem res_scaled_tendsto {a : ZMod 6} (ha : IsUnit a) :
    Tendsto (fun X : ℕ =>
        Analytic.liouvilleRes a ((6 * X + 1 : ℕ) : ℝ) / (X : ℝ))
      atTop (nhds 0) := by
  have hN : Tendsto (fun X : ℕ => (6 * X + 1 : ℕ)) atTop atTop := by
    refine tendsto_atTop_mono (fun X => ?_) tendsto_id
    simp only [id_eq]
    omega
  have hcomp : Tendsto (fun X : ℕ => ((6 * X + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have h2 := (Analytic.liouvilleRes_six_tendsto ha).comp hcomp
  have hrat : Tendsto (fun X : ℕ => ((6 * X + 1 : ℕ) : ℝ) / (X : ℝ))
      atTop (nhds 6) := by
    have hbase : Tendsto (fun X : ℕ => (6 : ℝ) + 1 / (X : ℝ))
        atTop (nhds 6) := by
      have h0 : Tendsto (fun X : ℕ => 1 / (X : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h6 : Tendsto (fun _ : ℕ => (6 : ℝ)) atTop (nhds 6) :=
        tendsto_const_nhds
      have := h6.add h0
      rwa [add_zero] at this
    refine hbase.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hX0 : ((X : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  have h4 := h2.mul hrat
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hX0 : ((X : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h6X0 : ((6 * X + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Function.comp_apply]
  field_simp

/-- **The minus-wing cancellation** (unconditional): `L−(X) = o(X)`. -/
theorem wingMinus_div_tendsto :
    Tendsto (fun X : ℕ => ((wingMinusSum X : ℤ) : ℝ) / (X : ℝ))
      atTop (nhds 0) := by
  have h := res_scaled_tendsto (a := (5 : ZMod 6))
    ⟨⟨5, 5, by decide, by decide⟩, rfl⟩
  refine h.congr fun X => ?_
  rw [wingMinus_eq_res]

/-- **The plus-wing cancellation** (unconditional): `L+(X) = o(X)`. -/
theorem wingPlus_div_tendsto :
    Tendsto (fun X : ℕ => ((wingPlusSum X : ℤ) : ℝ) / (X : ℝ))
      atTop (nhds 0) := by
  have h := res_scaled_tendsto (a := (1 : ZMod 6)) isUnit_one
  have h1 : Tendsto (fun X : ℕ => 1 / (X : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h2 := h.sub h1
  rw [sub_zero] at h2
  refine h2.congr fun X => ?_
  rw [wingPlus_eq_res, div_sub_div_same, add_sub_cancel_right]

/-! ### (3) The named hypothesis and the conditional equidistribution -/

/-- **Chowla2Hypothesis** (house named-hypothesis pattern — NOT an axiom):
the natural-density two-point Chowla for the split form,

`Σ_{m ≤ X} λ(6m−1)·λ(6m+1) = o(X)`.

OPEN: Tao 2016 proves only the logarithmically averaged version; the
natural-density form is strictly stronger.  No theorem in this repository
asserts it. -/
def Chowla2Hypothesis : Prop :=
  Tendsto (fun X : ℕ => ((crossSum X : ℤ) : ℝ) / (X : ℝ)) atTop (nhds 0)

/-- **Conditional sign-pattern equidistribution**: under `Chowla2Hypothesis`
each of the four sign-pattern densities `N(e,d)/X` on `Icc 1 X` tends to
`1/4`.  The wing inputs are the UNCONDITIONAL `wingMinus_div_tendsto` and
`wingPlus_div_tendsto`; only the cross sum is hypothetical. -/
theorem pattern_density_of_chowla2 (hC : Chowla2Hypothesis)
    {e d : ℤ} (he : e ^ 2 = 1) (hd : d ^ 2 = 1) :
    Tendsto (fun X : ℕ => ((patternCount X e d : ℕ) : ℝ) / (X : ℝ))
      atTop (nhds (1 / 4)) := by
  have hC' : Tendsto (fun X : ℕ => ((crossSum X : ℤ) : ℝ) / (X : ℝ))
      atTop (nhds 0) := hC
  have hm := wingMinus_div_tendsto.const_mul (e : ℝ)
  have hp := wingPlus_div_tendsto.const_mul (d : ℝ)
  have hx := hC'.const_mul ((e : ℝ) * (d : ℝ))
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hbase := hone.add (hm.add (hp.add hx))
  rw [show (1 : ℝ) + ((e : ℝ) * 0 + ((d : ℝ) * 0 + ((e : ℝ) * (d : ℝ)) * 0))
      = 1 by ring] at hbase
  have hquarter := hbase.div_const (4 : ℝ)
  refine hquarter.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hX0 : ((X : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hid : (4 : ℝ) * ((patternCount X e d : ℕ) : ℝ)
      = ((X : ℕ) : ℝ) + (e : ℝ) * ((wingMinusSum X : ℤ) : ℝ)
        + (d : ℝ) * ((wingPlusSum X : ℤ) : ℝ)
        + (e : ℝ) * (d : ℝ) * ((crossSum X : ℤ) : ℝ) := by
    exact_mod_cast window_four_cell X he hd
  field_simp
  linear_combination -hid

/-- The pair-rough-relevant `(−1,−1)` cell explicitly: under
`Chowla2Hypothesis` the density of `m` with `λ(6m−1) = λ(6m+1) = −1`
tends to `1/4`. -/
theorem minus_minus_density_of_chowla2 (hC : Chowla2Hypothesis) :
    Tendsto (fun X : ℕ => ((patternCount X (-1) (-1) : ℕ) : ℝ) / (X : ℝ))
      atTop (nhds (1 / 4)) :=
  pattern_density_of_chowla2 hC (by norm_num) (by norm_num)

end FourCell
end Geometric
end EuclidsPath
