/-
  GeometricTypeIIBilinear — the genuine two-variable Type-II gain at FULL period (§9).

  ORIGIN (parity_wall Prime-Chaos session dossier §9). One local parity direction carries the
  non-summable `1/p` energy; but the TRUE two-variable Type-II averaging — both variables running
  over FULL periods — kills it: for intervals of lengths `R, L ≥ p` and coefficients bounded by 1,
  the bilinear block satisfies `|B_p| ≤ 3RL/(p−1)`, so the squared relative error is
  `(B_p/RL)² ≤ 9/(p−1)²` — SUMMABLE over primes (criterion B, at the bilinear level).

  The mechanism is the zero-sum isometry (`gram_quadratic_form`): collecting interval coefficients
  into residue classes gives class energies `≤ 2R²/p`, `≤ 2L²/p` (each class has `≤ ⌊R/p⌋+1 ≤ 2R/p`
  elements when `p ≤ R`), and Cauchy–Schwarz against the exact Gram form yields the gain.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `residue_class_card_le` / `scaled_class_card_le` — each interval residue class has
      `≤ ⌊R/p⌋+1` elements (also the §25 determinant-degenerate counting input, see
      `degenerate_pair_energy`);
    * `fiber_energy_le` → class energies `≤ 2R²/p` for `p ≤ R`;
    * `bilinear_Z_sq_bound` — the residual part: `(Σ_n (Σ_{a≠0} c_a Z_a(n)) d_n)² ≤ (p²/(p−1)²)·Ec·Ed`;
    * `bilinear_block_bound` — the headline: `|B_p| ≤ 3RL/(p−1)` for `7 ≤ p`, `p ≤ R`, `p ≤ L`;
    * `bilinear_gain_summable` — `9/(p−1)² ≤ 9(1/(p−2) − 1/(p−1))`: the gain telescopes (Σ < ∞);
    * `Zrow_forbidden_eq` — wall-visibility: the residual at the forbidden cell is
      `−p(p−2)/(p−1)²`, of order ONE.

  DISCLOSURE (the wall is NOT moved, renamed, or hidden):
    * The bound holds ONLY under the full-period hypotheses `p ≤ R`, `p ≤ L` with coefficients
      bounded by 1 (dossier §9: proved "under the stated interval premises").  They are load-bearing:
      for `R = L = 1` with the single pair on the forbidden cell, `|B| = 1 > 3/(p−1)`.  No statement
      is made or implied for `R < p` or `L < p`.
    * In the critical twin application the sieve moduli exceed the available Type-II block lengths,
      so the full-period hypothesis FAILS exactly where the parity wall lives; the sub-period regime
      remains the open short-restriction front — `CRE`, `SemiprimeShortRestriction`,
      `HigherConductorDispersion`, `LowFreqRootCoherence` are unchanged, and this module introduces
      NO new open Prop.
    * `Zrow_forbidden_eq` shows the pointwise residual is of order ONE (`→ −1`): the gain comes
      exclusively from averaging over full periods, never from pointwise smallness.  Together with
      `Zrow_mean_zero` these are wall-visibility lemmas, not smallness claims.
    * The constant 3 requires `7 ≤ p` on THIS proof route (`2/(p−1) + 5/(p−1)² ≤ 3/(p−1)` needs
      `p ≥ 6`); at `p = 5` no counterexample exists — only the route's constant degrades.
    * Nothing here proves twins; the parity wall is localized, not moved. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIGram

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## Interval residue classes: cardinality (§9 setup, §25 counting input) -/

/-- **Residue-class size.** In `range R`, each residue class mod `p` has `≤ ⌊R/p⌋ + 1` elements. -/
theorem residue_class_card_le {p : ℕ} [Fact p.Prime] (R : ℕ) (t : ZMod p) :
    ((Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = t)).card ≤ R / p + 1 := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmaps : ∀ k ∈ (Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = t),
      k / p ∈ Finset.range (R / p + 1) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkR : k < R := Finset.mem_range.mp hk'.1
    have h1 : k / p ≤ R / p := Nat.div_le_div_right (by omega)
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun k => k / p)
      ((Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = t)) := by
    intro k1 hk1 k2 hk2 heq
    have hk1' := Finset.mem_filter.mp (Finset.mem_coe.mp hk1)
    have hk2' := Finset.mem_filter.mp (Finset.mem_coe.mp hk2)
    have hcast : (k1 : ZMod p) = (k2 : ZMod p) := hk1'.2.trans hk2'.2.symm
    have hmodeq : k1 ≡ k2 [MOD p] := (ZMod.natCast_eq_natCast_iff k1 k2 p).mp hcast
    have hmod : k1 % p = k2 % p := hmodeq
    simp only at heq
    calc k1 = p * (k1 / p) + k1 % p := (Nat.div_add_mod k1 p).symm
      _ = p * (k2 / p) + k2 % p := by rw [heq, hmod]
      _ = k2 := Nat.div_add_mod k2 p
  calc ((Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = t)).card
      ≤ (Finset.range (R / p + 1)).card :=
        Finset.card_le_card_of_injOn (fun k => k / p) hmaps hinj
    _ = R / p + 1 := Finset.card_range _

/-- **Scaled class size.** Multiplying by an invertible `A` permutes the residue classes, so the
    same bound holds for the row map `k ↦ A·k`. -/
theorem scaled_class_card_le {p : ℕ} [Fact p.Prime] (R : ℕ) {A : ZMod p} (hA : A ≠ 0)
    (t : ZMod p) :
    ((Finset.range R).filter (fun (k : ℕ) => A * ((k : ZMod p)) = t)).card ≤ R / p + 1 := by
  have hfe : (Finset.range R).filter (fun (k : ℕ) => A * ((k : ZMod p)) = t)
      = (Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = A⁻¹ * t) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · intro h; rw [← h, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    · intro h; rw [h, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  rw [hfe]
  exact residue_class_card_le R _

/-! ## Generic fiber lemmas -/

/-- Regrouping a weighted sum along the fibers of `g`. -/
private theorem sum_mul_comp_fiberwise {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (g : ℕ → ZMod p)
    (f : ℕ → ℝ) (F : ZMod p → ℝ) :
    ∑ k ∈ s, f k * F (g k)
      = ∑ t : ZMod p, (∑ k ∈ s.filter (fun k => g k = t), f k) * F t := by
  rw [← Finset.sum_fiberwise s g (fun k => f k * F (g k))]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(Finset.mem_filter.mp hk).2]

/-- Fiber sums preserve the total. -/
private theorem fiber_sum_total {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (g : ℕ → ZMod p)
    (f : ℕ → ℝ) :
    ∑ t : ZMod p, ∑ k ∈ s.filter (fun k => g k = t), f k = ∑ k ∈ s, f k :=
  Finset.sum_fiberwise s g f

/-- **Fiber energy.** If every fiber has `≤ K` elements and `|u| ≤ 1`, the fiber-sum energy is
    `≤ K · |s|` (per-fiber Cauchy–Schwarz + partition). -/
private theorem fiber_energy_le {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (g : ℕ → ZMod p) (K : ℕ)
    (hcard : ∀ t : ZMod p, (s.filter (fun k => g k = t)).card ≤ K)
    (u : ℕ → ℝ) (hu : ∀ k ∈ s, |u k| ≤ 1) :
    ∑ t : ZMod p, (∑ k ∈ s.filter (fun k => g k = t), u k) ^ 2 ≤ (K : ℝ) * s.card := by
  have husq : ∀ k ∈ s, (u k) ^ 2 ≤ 1 := by
    intro k hk
    have := hu k hk
    nlinarith [sq_abs (u k), abs_nonneg (u k)]
  have hstep : ∀ t : ZMod p,
      (∑ k ∈ s.filter (fun k => g k = t), u k) ^ 2
        ≤ (K : ℝ) * ∑ k ∈ s.filter (fun k => g k = t), (u k) ^ 2 := by
    intro t
    calc (∑ k ∈ s.filter (fun k => g k = t), u k) ^ 2
        ≤ ((s.filter (fun k => g k = t)).card : ℝ)
            * ∑ k ∈ s.filter (fun k => g k = t), (u k) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (K : ℝ) * ∑ k ∈ s.filter (fun k => g k = t), (u k) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard t
          · exact Finset.sum_nonneg fun k _ => sq_nonneg _
  calc ∑ t : ZMod p, (∑ k ∈ s.filter (fun k => g k = t), u k) ^ 2
      ≤ ∑ t : ZMod p, (K : ℝ) * ∑ k ∈ s.filter (fun k => g k = t), (u k) ^ 2 :=
        Finset.sum_le_sum fun t _ => hstep t
    _ = (K : ℝ) * ∑ t : ZMod p, ∑ k ∈ s.filter (fun k => g k = t), (u k) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (K : ℝ) * ∑ k ∈ s, (u k) ^ 2 := by rw [fiber_sum_total]
    _ ≤ (K : ℝ) * s.card := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ k ∈ s, (u k) ^ 2 ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum husq
          _ = s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A single fiber sum is bounded by the fiber size. -/
private theorem fiber_abs_le {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (g : ℕ → ZMod p) (K : ℕ)
    (hcard : ∀ t : ZMod p, (s.filter (fun k => g k = t)).card ≤ K)
    (u : ℕ → ℝ) (hu : ∀ k ∈ s, |u k| ≤ 1) (t : ZMod p) :
    |∑ k ∈ s.filter (fun k => g k = t), u k| ≤ (K : ℝ) := by
  calc |∑ k ∈ s.filter (fun k => g k = t), u k|
      ≤ ∑ k ∈ s.filter (fun k => g k = t), |u k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s.filter (fun k => g k = t), (1 : ℝ) :=
        Finset.sum_le_sum fun k hk => hu k (Finset.mem_filter.mp hk).1
    _ = ((s.filter (fun k => g k = t)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (K : ℝ) := by exact_mod_cast hcard t

/-- The total absolute mass of the fiber sums is bounded by `|s|`. -/
private theorem fiber_abs_total_le {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (g : ℕ → ZMod p)
    (u : ℕ → ℝ) (hu : ∀ k ∈ s, |u k| ≤ 1) :
    ∑ t : ZMod p, |∑ k ∈ s.filter (fun k => g k = t), u k| ≤ (s.card : ℝ) := by
  calc ∑ t : ZMod p, |∑ k ∈ s.filter (fun k => g k = t), u k|
      ≤ ∑ t : ZMod p, ∑ k ∈ s.filter (fun k => g k = t), |u k| :=
        Finset.sum_le_sum fun t _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ s, |u k| := fiber_sum_total s g (fun k => |u k|)
    _ ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum hu
    _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Cast bound: `⌊R/p⌋ + 1 ≤ 2R/p` over `ℝ`, given `p ≤ R`. -/
private theorem cast_div_succ_le {p R : ℕ} (hp0 : 0 < p) (hpR : p ≤ R) :
    ((R / p : ℕ) : ℝ) + 1 ≤ 2 * (R : ℝ) / p := by
  have h1 : ((R / p : ℕ) : ℝ) ≤ (R : ℝ) / p := Nat.cast_div_le
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have h2 : (1 : ℝ) ≤ (R : ℝ) / p := by
    rw [le_div_iff₀ hppos, one_mul]
    exact_mod_cast hpR
  have : 2 * (R : ℝ) / p = (R : ℝ) / p + (R : ℝ) / p := by ring
  linarith

/-! ## The degenerate-locus counting input (§25) -/

/-- **Degenerate pair energy (§25, counting input).** The sum of squared class sizes — i.e. the
    number of pairs `(r₁,r₂)` in the interval with `r₁ ≡ r₂` — is `≤ (⌊R/p⌋+1)·R`.  This is the
    input to the summable determinant-degenerate budget `N_d ≤ 4·2^{ω(d)}R²L²/d`; it is NOT by
    itself progress of type A, B, or C on the wall. -/
theorem degenerate_pair_energy {p : ℕ} [Fact p.Prime] (R : ℕ) {A : ZMod p} (hA : A ≠ 0) :
    ∑ t : ZMod p, (((Finset.range R).filter (fun (k : ℕ) => A * ((k : ZMod p)) = t)).card : ℝ) ^ 2
      ≤ ((R / p + 1 : ℕ) : ℝ) * R := by
  have h := fiber_energy_le (Finset.range R) (fun (k : ℕ) => A * ((k : ZMod p))) (R / p + 1)
    (fun t => scaled_class_card_le R hA t) (fun _ => 1) (fun k _ => by norm_num)
  rw [Finset.card_range] at h
  have hval : ∀ t : ZMod p,
      ((((Finset.range R).filter (fun (k : ℕ) => A * ((k : ZMod p)) = t)).card : ℝ)) ^ 2
        = (∑ _k ∈ (Finset.range R).filter (fun (k : ℕ) => A * ((k : ZMod p)) = t), (1 : ℝ)) ^ 2 := by
    intro t
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun t _ => hval t)]
  exact h

/-! ## Pointwise wall-visibility values -/

/-- `Zrow 0` is the full-survival row: `0` at `n = 0`, `p/(p−1)²` elsewhere. -/
theorem Zrow_zero_row {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    Zrow (0 : ZMod p) n = if n = 0 then 0 else (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  rw [Zrow_eq hp2 0 n, Drow_zero_left hp2 n]
  by_cases hn : n = 0 <;> simp [hn]

/-- `Grow − 1` values: `1/(p−1)` at `0`, `−1/(p−1)²` elsewhere. -/
theorem Grow_sub_one_eq {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    Grow (p := p) n - 1
      = if n = 0 then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  unfold Grow
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos hn]; field_simp; ring
  · rw [if_neg hn, if_neg hn]; field_simp; ring

/-- **Wall visibility.** At the forbidden cell the residual is `−p(p−2)/(p−1)²` — of order ONE
    (it tends to `−1`).  There is no pointwise smallness; the bilinear gain below comes exclusively
    from full-period averaging. -/
theorem Zrow_forbidden_eq {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0) :
    Zrow a ((-2) / a) = -((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
      intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    simpa using this
  have hforb : a * ((-2) / a) + 2 = 0 := by
    rw [mul_comm, div_mul_cancel₀ _ ha]; ring
  have hD : Drow a ((-2) / a) = 1 := by unfold Drow; rw [if_pos hforb]
  have hY : Yrow a ((-2) / a) = 0 := by unfold Yrow; rw [hD]; ring
  have hn0 : ((-2 : ZMod p)) / a ≠ 0 := by
    intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact h2 (by linear_combination -h)
    · exact ha h
  unfold Zrow
  rw [hY, Grow, if_neg hn0]
  ring

/-! ## The residual bilinear bound (Level 1: class data) -/

/-- **Residual bilinear bound.** Cauchy–Schwarz against the exact Gram form: with class energies
    `Σ_{a≠0} c² ≤ Ec`, `Σ_n d² ≤ Ed`, the residual block satisfies
    `(Σ_n (Σ_{a≠0} c_a Z_a(n)) d_n)² ≤ (p²/(p−1)²)·Ec·Ed`. -/
theorem bilinear_Z_sq_bound {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (c d : ZMod p → ℝ) {Ec Ed : ℝ}
    (hEc : ∑ a ∈ Finset.univ.erase (0 : ZMod p), (c a) ^ 2 ≤ Ec)
    (hEd : ∑ n : ZMod p, (d n) ^ 2 ≤ Ed) :
    (∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) * d n) ^ 2
      ≤ (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 * Ec * Ed := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun n => ∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) d
  have hgram := gram_quadratic_form hp2 c
  have hgram_le :
      ∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) ^ 2
        ≤ (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 * Ec := by
    rw [hgram]
    have hkey : ((p : ℝ) - 1) * (∑ a ∈ Finset.univ.erase (0 : ZMod p), (c a) ^ 2)
          - (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a) ^ 2
        ≤ ((p : ℝ) - 1) * Ec := by
      have h1 : (∑ a ∈ Finset.univ.erase (0 : ZMod p), (c a) ^ 2) ≤ Ec := hEc
      nlinarith [sq_nonneg (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a)]
    calc (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 3
          * (((p : ℝ) - 1) * (∑ a ∈ Finset.univ.erase (0 : ZMod p), (c a) ^ 2)
              - (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a) ^ 2)
        ≤ (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 3 * (((p : ℝ) - 1) * Ec) := by
          apply mul_le_mul_of_nonneg_left hkey
          positivity
      _ = (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 * Ec := by
          field_simp
  have hd2 : (0 : ℝ) ≤ ∑ n : ZMod p, (d n) ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hS2 : (0 : ℝ) ≤ ∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  calc (∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) * d n) ^ 2
      ≤ (∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), c a * Zrow a n) ^ 2)
          * ∑ n : ZMod p, (d n) ^ 2 := hCS
    _ ≤ ((p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 * Ec) * Ed :=
        mul_le_mul hgram_le hEd hd2 (le_trans hS2 hgram_le)
    _ = (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 * Ec * Ed := by ring

/-! ## The headline: the full-period bilinear block (§9) -/

/-- **The two-variable Type-II gain (§9).** For a prime `7 ≤ p`, FULL periods `p ≤ R`, `p ≤ L`,
    an invertible row scale `A ≠ 0`, and coefficients bounded by 1:
    `|Σ_{k<R} Σ_{l<L} u_k v_l (Y_{Ak}(l) − 1)| ≤ 3RL/(p−1)`.
    One parity direction carries non-summable `1/p` energy; genuine TWO-variable full-period
    averaging turns the squared relative error into summable `O(1/p²)` (criterion B). -/
theorem bilinear_block_bound {p : ℕ} [Fact p.Prime] {R L : ℕ} {A : ZMod p}
    (hp7 : 7 ≤ p) (hpR : p ≤ R) (hpL : p ≤ L) (hA : A ≠ 0)
    (u v : ℕ → ℝ) (hu : ∀ k ∈ Finset.range R, |u k| ≤ 1) (hv : ∀ l ∈ Finset.range L, |v l| ≤ 1) :
    |∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
        u k * v l * (Yrow (A * ((k : ZMod p))) ((l : ZMod p)) - 1)|
      ≤ 3 * (R : ℝ) * L / ((p : ℝ) - 1) := by
  classical
  have hp2 : 2 < p := by omega
  have hp0 : 0 < p := by omega
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hpp : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp7
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hRr : (p : ℝ) ≤ (R : ℝ) := by exact_mod_cast hpR
  have hLr : (p : ℝ) ≤ (L : ℝ) := by exact_mod_cast hpL
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  -- class sums
  set gR : ℕ → ZMod p := fun k => A * ((k : ZMod p)) with hgR
  set gL : ℕ → ZMod p := fun l => ((l : ZMod p)) with hgL
  set cf : ZMod p → ℝ := fun a => ∑ k ∈ (Finset.range R).filter (fun k => gR k = a), u k with hcf
  set df : ZMod p → ℝ := fun n => ∑ l ∈ (Finset.range L).filter (fun l => gL l = n), v l with hdf
  -- regroup the interval block into class form
  have hregroup : ∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
      u k * v l * (Yrow (gR k) (gL l) - 1)
      = ∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * (Yrow a n - 1) := by
    have hinner : ∀ k ∈ Finset.range R,
        ∑ l ∈ Finset.range L, u k * v l * (Yrow (gR k) (gL l) - 1)
          = u k * ∑ n : ZMod p, df n * (Yrow (gR k) n - 1) := by
      intro k _
      rw [← sum_mul_comp_fiberwise (Finset.range L) gL v (fun n => Yrow (gR k) n - 1),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [Finset.sum_congr rfl hinner,
      sum_mul_comp_fiberwise (Finset.range R) gR u
        (fun a => ∑ n : ZMod p, df n * (Yrow a n - 1))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hregroup]
  -- split Y − 1 = Z + (G − 1)
  have hW : ∀ (a n : ZMod p), Yrow a n - 1 = Zrow a n + (Grow n - 1) := by
    intro a n; unfold Zrow; ring
  have hsplit : ∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * (Yrow a n - 1)
      = (∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n)
        + (cf 0 * ∑ n : ZMod p, df n * Zrow 0 n)
        + (∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1)) := by
    have e1 : ∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * (Yrow a n - 1)
        = (∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * Zrow a n)
          + ∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * (Grow n - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [hW a n]; ring
    have e2 : ∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * (Grow n - 1)
        = (∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro n _
      ring
    have e3 : ∑ a : ZMod p, ∑ n : ZMod p, cf a * df n * Zrow a n
        = (∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n)
          + cf 0 * ∑ n : ZMod p, df n * Zrow 0 n := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod p))]
      have e3a : ∑ n : ZMod p, cf 0 * df n * Zrow 0 n
          = cf 0 * ∑ n : ZMod p, df n * Zrow 0 n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      have e3b : ∑ a ∈ Finset.univ.erase (0 : ZMod p), ∑ n : ZMod p, cf a * df n * Zrow a n
          = ∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [e3a, e3b]
      ring
    rw [e1, e2, e3]
  rw [hsplit]
  -- component bounds
  have hcardR : ∀ t : ZMod p, ((Finset.range R).filter (fun k => gR k = t)).card ≤ R / p + 1 :=
    fun t => scaled_class_card_le R hA t
  have hcardL : ∀ t : ZMod p, ((Finset.range L).filter (fun l => gL l = t)).card ≤ L / p + 1 :=
    fun t => residue_class_card_le L t
  have hKR := cast_div_succ_le hp0 hpR
  have hKL := cast_div_succ_le hp0 hpL
  -- (1) the residual part
  have hEc : ∑ a ∈ Finset.univ.erase (0 : ZMod p), (cf a) ^ 2 ≤ 2 * (R : ℝ) ^ 2 / p := by
    have hsub : ∑ a ∈ Finset.univ.erase (0 : ZMod p), (cf a) ^ 2 ≤ ∑ a : ZMod p, (cf a) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun a _ _ => sq_nonneg _)
    have henergy := fiber_energy_le (Finset.range R) gR (R / p + 1) hcardR u hu
    rw [Finset.card_range] at henergy
    calc ∑ a ∈ Finset.univ.erase (0 : ZMod p), (cf a) ^ 2
        ≤ ∑ a : ZMod p, (cf a) ^ 2 := hsub
      _ ≤ ((R / p + 1 : ℕ) : ℝ) * R := henergy
      _ ≤ (2 * (R : ℝ) / p) * R := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hRpos)
          push_cast
          exact hKR
      _ = 2 * (R : ℝ) ^ 2 / p := by ring
  have hEd : ∑ n : ZMod p, (df n) ^ 2 ≤ 2 * (L : ℝ) ^ 2 / p := by
    have henergy := fiber_energy_le (Finset.range L) gL (L / p + 1) hcardL v hv
    rw [Finset.card_range] at henergy
    calc ∑ n : ZMod p, (df n) ^ 2
        ≤ ((L / p + 1 : ℕ) : ℝ) * L := henergy
      _ ≤ (2 * (L : ℝ) / p) * L := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hLpos)
          push_cast
          exact hKL
      _ = 2 * (L : ℝ) ^ 2 / p := by ring
  have hTZ : |∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n|
      ≤ 2 * (R : ℝ) * L / ((p : ℝ) - 1) := by
    have hsq := bilinear_Z_sq_bound hp2 cf df hEc hEd
    have hY : (0 : ℝ) ≤ 2 * (R : ℝ) * L / ((p : ℝ) - 1) := by positivity
    have hval : (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 * (2 * (R : ℝ) ^ 2 / p) * (2 * (L : ℝ) ^ 2 / p)
        = (2 * (R : ℝ) * L / ((p : ℝ) - 1)) ^ 2 := by
      field_simp
    rw [hval] at hsq
    have h3 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hY] at h3
  -- (2) the zero-row part
  have hc0 : |cf 0| ≤ 2 * (R : ℝ) / p := by
    have := fiber_abs_le (Finset.range R) gR (R / p + 1) hcardR u hu 0
    calc |cf 0| ≤ ((R / p + 1 : ℕ) : ℝ) := this
      _ ≤ 2 * (R : ℝ) / p := by push_cast; exact hKR
  have hdtotal : ∑ n : ZMod p, |df n| ≤ (L : ℝ) := by
    have := fiber_abs_total_le (Finset.range L) gL v hv
    rwa [Finset.card_range] at this
  have hZ0sum : |∑ n : ZMod p, df n * Zrow 0 n| ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 * L := by
    have hZ0val : ∀ n : ZMod p, |Zrow (0 : ZMod p) n| ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
      intro n
      rw [Zrow_zero_row hp2 n]
      by_cases hn : n = 0
      · rw [if_pos hn, abs_zero]; positivity
      · rw [if_neg hn, abs_of_nonneg (by positivity)]
    calc |∑ n : ZMod p, df n * Zrow 0 n|
        ≤ ∑ n : ZMod p, |df n * Zrow 0 n| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n : ZMod p, |df n| * |Zrow 0 n| := by
          apply Finset.sum_congr rfl; intro n _; rw [abs_mul]
      _ ≤ ∑ n : ZMod p, |df n| * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hZ0val n) (abs_nonneg _)
      _ = (∑ n : ZMod p, |df n|) * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
          rw [Finset.sum_mul]
      _ ≤ (L : ℝ) * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hdtotal (by positivity)
      _ = (p : ℝ) / ((p : ℝ) - 1) ^ 2 * L := by ring
  have hTZ0 : |cf 0 * ∑ n : ZMod p, df n * Zrow 0 n| ≤ 2 * (R : ℝ) * L / ((p : ℝ) - 1) ^ 2 := by
    rw [abs_mul]
    calc |cf 0| * |∑ n : ZMod p, df n * Zrow 0 n|
        ≤ (2 * (R : ℝ) / p) * ((p : ℝ) / ((p : ℝ) - 1) ^ 2 * L) :=
          mul_le_mul hc0 hZ0sum (abs_nonneg _) (by positivity)
      _ = 2 * (R : ℝ) * L / ((p : ℝ) - 1) ^ 2 := by
          field_simp
  -- (3) the mean-mode part
  have hcall : |∑ a : ZMod p, cf a| ≤ (R : ℝ) := by
    have htot : ∑ a : ZMod p, cf a = ∑ k ∈ Finset.range R, u k := fiber_sum_total _ _ _
    rw [htot]
    calc |∑ k ∈ Finset.range R, u k| ≤ ∑ k ∈ Finset.range R, |u k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range R, (1 : ℝ) := Finset.sum_le_sum hu
      _ = (R : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]
  have hd0 : |df 0| ≤ 2 * (L : ℝ) / p := by
    have := fiber_abs_le (Finset.range L) gL (L / p + 1) hcardL v hv 0
    calc |df 0| ≤ ((L / p + 1 : ℕ) : ℝ) := this
      _ ≤ 2 * (L : ℝ) / p := by push_cast; exact hKL
  have hGsum : |∑ n : ZMod p, df n * (Grow n - 1)| ≤ 3 * (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by
    have hsplit0 : ∑ n : ZMod p, df n * (Grow (p := p) n - 1)
        = df 0 * (1 / ((p : ℝ) - 1))
          + ∑ n ∈ Finset.univ.erase (0 : ZMod p), df n * (-(1 / ((p : ℝ) - 1) ^ 2)) := by
      rw [← Finset.add_sum_erase Finset.univ (fun n => df n * (Grow (p := p) n - 1))
        (Finset.mem_univ (0 : ZMod p))]
      congr 1
      · rw [Grow_sub_one_eq hp2 0, if_pos rfl]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [Grow_sub_one_eq hp2 n, if_neg (Finset.ne_of_mem_erase hn)]
    rw [hsplit0]
    have herase : |∑ n ∈ Finset.univ.erase (0 : ZMod p), df n * (-(1 / ((p : ℝ) - 1) ^ 2))|
        ≤ (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by
      calc |∑ n ∈ Finset.univ.erase (0 : ZMod p), df n * (-(1 / ((p : ℝ) - 1) ^ 2))|
          ≤ ∑ n ∈ Finset.univ.erase (0 : ZMod p), |df n * (-(1 / ((p : ℝ) - 1) ^ 2))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ n ∈ Finset.univ.erase (0 : ZMod p), |df n| * (1 / ((p : ℝ) - 1) ^ 2) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2)]
        _ = (∑ n ∈ Finset.univ.erase (0 : ZMod p), |df n|) * (1 / ((p : ℝ) - 1) ^ 2) := by
            rw [Finset.sum_mul]
        _ ≤ (L : ℝ) * (1 / ((p : ℝ) - 1) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc ∑ n ∈ Finset.univ.erase (0 : ZMod p), |df n|
                ≤ ∑ n : ZMod p, |df n| :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                    (fun n _ _ => abs_nonneg _)
              _ ≤ (L : ℝ) := hdtotal
        _ = (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by ring
    have hhead : |df 0 * (1 / ((p : ℝ) - 1))| ≤ 2 * (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((p : ℝ) - 1))]
      have h1 : |df 0| * (1 / ((p : ℝ) - 1)) ≤ (2 * (L : ℝ) / p) * (1 / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right hd0 (by positivity)
      have h2 : (2 * (L : ℝ) / p) * (1 / ((p : ℝ) - 1)) ≤ 2 * (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        have e : 2 * (L : ℝ) / ((p : ℝ) - 1) ^ 2 - (2 * (L : ℝ) / p) * (1 / ((p : ℝ) - 1))
            = 2 * (L : ℝ) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) := by
          field_simp
          ring
        have hnn : (0:ℝ) ≤ 2 * (L : ℝ) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) := by positivity
        linarith
      linarith
    calc |df 0 * (1 / ((p : ℝ) - 1))
          + ∑ n ∈ Finset.univ.erase (0 : ZMod p), df n * (-(1 / ((p : ℝ) - 1) ^ 2))|
        ≤ |df 0 * (1 / ((p : ℝ) - 1))|
          + |∑ n ∈ Finset.univ.erase (0 : ZMod p), df n * (-(1 / ((p : ℝ) - 1) ^ 2))| :=
          abs_add_le _ _
      _ ≤ 2 * (L : ℝ) / ((p : ℝ) - 1) ^ 2 + (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by
          linarith [hhead, herase]
      _ = 3 * (L : ℝ) / ((p : ℝ) - 1) ^ 2 := by ring
  have hTG : |(∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1))|
      ≤ 3 * (R : ℝ) * L / ((p : ℝ) - 1) ^ 2 := by
    rw [abs_mul]
    calc |∑ a : ZMod p, cf a| * |∑ n : ZMod p, df n * (Grow n - 1)|
        ≤ (R : ℝ) * (3 * (L : ℝ) / ((p : ℝ) - 1) ^ 2) :=
          mul_le_mul hcall hGsum (abs_nonneg _) (le_of_lt hRpos)
      _ = 3 * (R : ℝ) * L / ((p : ℝ) - 1) ^ 2 := by ring
  -- final combination: 2/(p−1) + 5/(p−1)² ≤ 3/(p−1) for p ≥ 7
  have habs : |(∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n)
        + (cf 0 * ∑ n : ZMod p, df n * Zrow 0 n)
        + (∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1))|
      ≤ 2 * (R : ℝ) * L / ((p : ℝ) - 1) + 5 * ((R : ℝ) * L) / ((p : ℝ) - 1) ^ 2 := by
    calc |(∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n)
          + (cf 0 * ∑ n : ZMod p, df n * Zrow 0 n)
          + (∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1))|
        ≤ |(∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n)
            + (cf 0 * ∑ n : ZMod p, df n * Zrow 0 n)|
          + |(∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1))| := abs_add_le _ _
      _ ≤ |∑ n : ZMod p, (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n|
          + |cf 0 * ∑ n : ZMod p, df n * Zrow 0 n|
          + |(∑ a : ZMod p, cf a) * (∑ n : ZMod p, df n * (Grow n - 1))| := by
          linarith [abs_add_le (∑ n : ZMod p,
            (∑ a ∈ Finset.univ.erase (0 : ZMod p), cf a * Zrow a n) * df n)
            (cf 0 * ∑ n : ZMod p, df n * Zrow 0 n)]
      _ ≤ 2 * (R : ℝ) * L / ((p : ℝ) - 1) + 2 * (R : ℝ) * L / ((p : ℝ) - 1) ^ 2
          + 3 * (R : ℝ) * L / ((p : ℝ) - 1) ^ 2 := by
          linarith [hTZ, hTZ0, hTG]
      _ = 2 * (R : ℝ) * L / ((p : ℝ) - 1) + 5 * ((R : ℝ) * L) / ((p : ℝ) - 1) ^ 2 := by ring
  have hfinal : 2 * (R : ℝ) * L / ((p : ℝ) - 1) + 5 * ((R : ℝ) * L) / ((p : ℝ) - 1) ^ 2
      ≤ 3 * (R : ℝ) * L / ((p : ℝ) - 1) := by
    have hRL : (0 : ℝ) ≤ (R : ℝ) * L := by positivity
    have hD5 : (5 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have e : 3 * (R : ℝ) * L / ((p : ℝ) - 1)
        - (2 * (R : ℝ) * L / ((p : ℝ) - 1) + 5 * ((R : ℝ) * L) / ((p : ℝ) - 1) ^ 2)
        = ((R : ℝ) * L) * (((p : ℝ) - 1) - 5) / ((p : ℝ) - 1) ^ 2 := by
      field_simp
      ring
    have hnn : 0 ≤ ((R : ℝ) * L) * (((p : ℝ) - 1) - 5) / ((p : ℝ) - 1) ^ 2 := by
      apply div_nonneg (mul_nonneg hRL (by linarith)) (by positivity)
    linarith [e, hnn]
  linarith [habs, hfinal]

/-! ## The gain is summable (criterion B) -/

/-- **The bilinear gain telescopes (§9).** `9/(p−1)² ≤ 9(1/(p−2) − 1/(p−1))`, so the squared
    relative error `(B_p/RL)² ≤ 9/(p−1)²` is SUMMABLE over primes — the machine form of the
    two-variable Type-II gain (criterion B). -/
theorem bilinear_gain_summable {p : ℕ} (hp : 3 ≤ p) :
    9 / ((p : ℝ) - 1) ^ 2 ≤ 9 * (1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1)) := by
  have h := two_row_summability hp
  have h9 : 9 / ((p : ℝ) - 1) ^ 2 = 9 * (1 / ((p : ℝ) - 1) ^ 2) := by ring
  linarith [h, h9]

end TypeII
end Geometric
end EuclidsPath
