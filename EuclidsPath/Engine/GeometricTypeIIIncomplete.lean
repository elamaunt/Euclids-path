/-
  GeometricTypeIIIncomplete — the completion×Weil engine: the first UNCONDITIONAL sub-period
  cancellation in the repo (incomplete Kloosterman / inversion sums, short-window circle counts).

  ORIGIN (§64 flank / §55 apparatus / dossier §22–25 geometry). The completion identity
  (`interval_completion`) turns any SHORT sum mod `p` into a complete Fourier-weighted sum; the
  repo's fourth-moment Weil input (`kloos_norm_le`: `‖Kl‖⁴ ≤ 2p³`) bounds every complete transform;
  the interval weight has kernel `L¹`-mass `≤ p(1 + log p)` (bridged to the EXISTING Dirichlet
  kernel bound `expKernel_bound` of `Step00LargeSieve` — no re-derivation of the Jordan sine floor).
  Composing: `‖Σ_{m<M} ψ(a·m⁻¹ + b·m)‖ ≤ 2^{1/4} p^{3/4} (M/p + 1 + log p)` UNCONDITIONALLY, and
  the short-window equidistribution of the circle's real coordinate.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `intervalWeight_eq_expKernel` — the bridge `W_M(h) = expKernel M (−h.val/p)`;
    * `intervalWeight_norm_le_tmin` — `‖W_M(h)‖ ≤ p/(2·tmin h)` via the existing kernel bound;
    * `intervalWeight_L1` — `Σ_{h≠0} ‖W_M(h)‖ ≤ p(1 + log p)`, uniformly in `M`.
    (Parts 2–3 continue below: uniform Weil bound, the incomplete-sum headline, circle payoff.)

  DISCLOSURE (conditional surface shrinks; the parity wall does NOT move):
    * The bounds are NONTRIVIAL only for `M ≫ p^{3/4} log p` (the window `[C·p^{3/4}·log p, p]` is
      nonempty roughly from `p ≳ 6·10⁴`; read asymptotically).  The source is the repo's
      fourth-moment Weil input `kloos_norm_le` (`‖Kl‖ ≤ 2^{1/4} p^{3/4}`), NOT the full Weil bound
      `2√p`; under full Weil the classical benchmark would be `M ≫ p^{1/2} log p` — the gap between
      the exponents `3/4` and `1/2` is real and stated.
    * SINGLE PRIME modulus only.  Composite/semiprime moduli (residuals C, D) and the SIGNED
      Möbius core over `q` (residual E, `CRE`) are untouched: nothing here bounds any registered
      open target.  This module discharges an enumerated external input (incomplete
      Kloosterman/inversion sums at `p^{3/4}` strength — previously available only as a named
      standard-analytic hypothesis of the §64 list); it is a conditional-surface reduction, NOT a
      §110 A/B/C event on a wall object.
    * This module introduces ZERO new open `Prop`s.  Nothing here proves twins; the parity wall is
      localized, not moved. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIICompletion
import EuclidsPath.Engine.Step00LargeSieve
import EuclidsPath.Engine.Step00KloostermanMoment

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open EuclidsPath.LargeSieve EuclidsPath.CircleEnergy EuclidsPath.KloostermanMoment

/-! ## The frequency distance `tmin` -/

/-- The distance of the frequency `h` from the zero mode: `min(h.val, p − h.val)`. -/
def tmin {p : ℕ} (h : ZMod p) : ℕ := min h.val (p - h.val)

theorem tmin_pos {p : ℕ} [NeZero p] {h : ZMod p} (hh : h ≠ 0) : 0 < tmin h := by
  have hv : 0 < h.val := by
    rcases Nat.eq_zero_or_pos h.val with h0 | h0
    · exact absurd ((ZMod.val_eq_zero h).mp h0) hh
    · exact h0
  have hvlt : h.val < p := ZMod.val_lt h
  unfold tmin
  omega

/-- Integer distance: the frequency `h.val/p` keeps distance `≥ tmin(h)/p` from EVERY integer. -/
theorem val_int_dist_lower {p : ℕ} [NeZero p] (hp0 : 0 < p) {h : ZMod p} (hh : h ≠ 0) :
    ∀ n : ℤ, ((tmin h : ℚ)) / p ≤ |((h.val : ℚ)) / p - (n : ℚ)| := by
  intro n
  have hqQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
  have hv1 : 1 ≤ h.val := by
    have := tmin_pos (p := p) hh
    unfold tmin at this
    omega
  have hvq : h.val < p := ZMod.val_lt h
  -- the integer core
  have hint : (tmin h : ℤ) ≤ |(h.val : ℤ) - n * p| := by
    have htm : (tmin h : ℤ) ≤ (h.val : ℤ) ∧ (tmin h : ℤ) ≤ (p : ℤ) - h.val := by
      constructor
      · exact_mod_cast Nat.min_le_left h.val (p - h.val)
      · have := Nat.min_le_right h.val (p - h.val)
        have hle : (p : ℤ) - h.val = ((p - h.val : ℕ) : ℤ) := by
          rw [Nat.cast_sub (le_of_lt hvq)]
        rw [hle]
        exact_mod_cast this
    by_cases hn : n ≤ 0
    · have hnp : n * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn (by exact_mod_cast Nat.zero_le p)
      rcases abs_cases ((h.val : ℤ) - n * p) with ⟨he, _⟩ | ⟨he, hneg⟩
      · omega
      · omega
    · push_neg at hn
      rcases lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        subst hn1
        rcases abs_cases ((h.val : ℤ) - 1 * p) with ⟨he, _⟩ | ⟨he, _⟩
        · omega
        · omega
      · have hnp : 2 * (p : ℤ) ≤ n * p := by
          apply mul_le_mul_of_nonneg_right hn2 (by exact_mod_cast Nat.zero_le p)
        rcases abs_cases ((h.val : ℤ) - n * p) with ⟨he, _⟩ | ⟨he, _⟩
        · omega
        · omega
  -- lift to ℚ
  have hrew : (h.val : ℚ) / p - (n : ℚ) = (((h.val : ℤ) - n * p : ℤ) : ℚ) / p := by
    push_cast
    field_simp
  rw [hrew, abs_div, abs_of_pos hqQ, ← Int.cast_abs]
  gcongr
  exact_mod_cast hint

/-! ## The bridge to the Dirichlet kernel frame -/

/-- **The bridge.** The interval Fourier weight IS the Dirichlet kernel of `Step00LargeSieve`
    at the rational frequency `−h.val/p`: the completion apparatus and the large-sieve kernel
    machinery are the same object in two frames. -/
theorem intervalWeight_eq_expKernel {p : ℕ} [NeZero p] (M : ℕ) (h : ZMod p) :
    intervalWeight p M h = expKernel M (-((h.val : ℚ) / p)) := by
  unfold intervalWeight expKernel
  apply Finset.sum_congr rfl
  intro m _
  have hval : ((h.val : ℕ) : ZMod p) = h := ZMod.natCast_rightInverse h
  have hcast : -(h * (m : ZMod p)) = (((-(h.val * m : ℕ) : ℤ)) : ZMod p) := by
    push_cast
    rw [hval]
  rw [hcast, ZMod.stdAddChar_coe]
  unfold e
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  push_cast
  field_simp

/-- `‖W_M(h)‖ ≤ p/(2·tmin h)` — one application of the EXISTING `expKernel_bound`. -/
theorem intervalWeight_norm_le_tmin {p : ℕ} [NeZero p] (hp0 : 0 < p) (M : ℕ)
    {h : ZMod p} (hh : h ≠ 0) :
    ‖intervalWeight p M h‖ ≤ (p : ℝ) / (2 * tmin h) := by
  have htm : 0 < tmin h := tmin_pos hh
  have hδ : (0 : ℚ) < (tmin h : ℚ) / p := by
    apply div_pos
    · exact_mod_cast htm
    · exact_mod_cast hp0
  have hlow := val_int_dist_lower hp0 hh
  have hbound := expKernel_bound hδ hlow M
  rw [intervalWeight_eq_expKernel, norm_expKernel_neg]
  calc ‖expKernel M ((h.val : ℚ) / p)‖ ≤ 1 / (2 * (((tmin h : ℚ) / p : ℚ) : ℝ)) := hbound
    _ = (p : ℝ) / (2 * tmin h) := by
        have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
        have htR : (0 : ℝ) < (tmin h : ℝ) := by exact_mod_cast htm
        push_cast
        field_simp

/-! ## The kernel L¹ bound -/

/-- `Σ_{h≠0} 1/tmin(h) ≤ 2(1 + log p)` — harmonic-sum bound via `1/min(v,p−v) ≤ 1/v + 1/(p−v)`. -/
theorem sum_inv_tmin_le {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    ∑ h ∈ Finset.univ.erase (0 : ZMod p), (1 : ℝ) / (tmin h)
      ≤ 2 * (1 + Real.log p) := by
  have hp0 : 0 < p := by omega
  -- pointwise: 1/tmin ≤ 1/val + 1/(p − val)
  have hpt : ∀ h ∈ Finset.univ.erase (0 : ZMod p),
      (1 : ℝ) / (tmin h) ≤ 1 / (h.val : ℝ) + 1 / ((p - h.val : ℕ) : ℝ) := by
    intro h hmem
    have hh : h ≠ 0 := Finset.ne_of_mem_erase hmem
    have hv1 : 1 ≤ h.val := by
      have := tmin_pos (p := p) hh
      unfold tmin at this
      omega
    have hvq : h.val < p := ZMod.val_lt h
    have h1 : (0 : ℝ) < (h.val : ℝ) := by exact_mod_cast hv1
    have h2 : (0 : ℝ) < ((p - h.val : ℕ) : ℝ) := by
      have : 0 < p - h.val := by omega
      exact_mod_cast this
    unfold tmin
    rcases min_cases h.val (p - h.val) with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]
      have : (0 : ℝ) ≤ 1 / ((p - h.val : ℕ) : ℝ) := by positivity
      linarith
    · rw [hmin]
      have : (0 : ℝ) ≤ 1 / (h.val : ℝ) := by positivity
      linarith
  have hstep := Finset.sum_le_sum hpt
  -- reindex the val sums to Icc 1 (p−1)
  have hbij : ∑ h ∈ Finset.univ.erase (0 : ZMod p),
      ((1 : ℝ) / (h.val : ℝ) + 1 / ((p - h.val : ℕ) : ℝ))
      = ∑ v ∈ Finset.Icc 1 (p - 1), ((1 : ℝ) / (v : ℝ) + 1 / ((p - v : ℕ) : ℝ)) := by
    apply Finset.sum_nbij' (fun h : ZMod p => h.val) (fun v : ℕ => (v : ZMod p))
    · intro h hmem
      have hh : h ≠ 0 := Finset.ne_of_mem_erase hmem
      have hv1 : 1 ≤ h.val := by
        have := tmin_pos (p := p) hh
        unfold tmin at this
        omega
      have hvq : h.val < p := ZMod.val_lt h
      simp only [Finset.mem_Icc]
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro hc
      have hmod : v % p = 0 % p := (ZMod.natCast_eq_natCast_iff v 0 p).mp (by simpa using hc)
      have hvp : v < p := by omega
      rw [Nat.mod_eq_of_lt hvp, Nat.zero_mod] at hmod
      omega
    · intro h _
      exact ZMod.natCast_rightInverse h
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      exact ZMod.val_cast_of_lt (by omega)
    · intro h _
      rfl
  -- the two harmonic halves
  have hsplit : ∑ v ∈ Finset.Icc 1 (p - 1), ((1 : ℝ) / (v : ℝ) + 1 / ((p - v : ℕ) : ℝ))
      = (∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (v : ℝ))
        + ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / ((p - v : ℕ) : ℝ) :=
    Finset.sum_add_distrib
  have hrefl : ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / ((p - v : ℕ) : ℝ)
      = ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (v : ℝ) := by
    apply Finset.sum_nbij' (fun v : ℕ => p - v) (fun v : ℕ => p - v)
    · intro v hv
      simp only [Finset.mem_Icc] at hv ⊢
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv ⊢
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      omega
    · intro v hv
      rfl
  -- harmonic bound
  have hharm : ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (v : ℝ) ≤ 1 + Real.log p := by
    have heq : ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (v : ℝ) = ((harmonic (p - 1) : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [one_div]
    rw [heq]
    calc ((harmonic (p - 1) : ℚ) : ℝ) ≤ 1 + Real.log (p - 1 : ℕ) := harmonic_le_one_add_log _
      _ ≤ 1 + Real.log p := by
          have h1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
            have : 0 < p - 1 := by omega
            exact_mod_cast this
          have h2 : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
            have : p - 1 ≤ p := by omega
            exact_mod_cast this
          have := Real.log_le_log h1 h2
          linarith
  calc ∑ h ∈ Finset.univ.erase (0 : ZMod p), (1 : ℝ) / (tmin h)
      ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p),
          ((1 : ℝ) / (h.val : ℝ) + 1 / ((p - h.val : ℕ) : ℝ)) := hstep
    _ = ∑ v ∈ Finset.Icc 1 (p - 1), ((1 : ℝ) / (v : ℝ) + 1 / ((p - v : ℕ) : ℝ)) := hbij
    _ = (∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (v : ℝ))
        + ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / ((p - v : ℕ) : ℝ) := hsplit
    _ = 2 * ∑ v ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (v : ℝ) := by rw [hrefl]; ring
    _ ≤ 2 * (1 + Real.log p) := by linarith [hharm]

/-- **The kernel L¹ bound (Step-1 headline).** `Σ_{h≠0} ‖W_M(h)‖ ≤ p(1 + log p)`,
    uniformly in `M`. -/
theorem intervalWeight_L1 {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (M : ℕ) :
    ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖
      ≤ (p : ℝ) * (1 + Real.log p) := by
  have hp0 : 0 < p := by omega
  have hstep : ∀ h ∈ Finset.univ.erase (0 : ZMod p),
      ‖intervalWeight p M h‖ ≤ ((p : ℝ) / 2) * ((1 : ℝ) / (tmin h)) := by
    intro h hmem
    have hh : h ≠ 0 := Finset.ne_of_mem_erase hmem
    have := intervalWeight_norm_le_tmin hp0 M hh
    have htm : (0 : ℝ) < (tmin h : ℝ) := by exact_mod_cast tmin_pos hh
    calc ‖intervalWeight p M h‖ ≤ (p : ℝ) / (2 * tmin h) := this
      _ = ((p : ℝ) / 2) * ((1 : ℝ) / (tmin h)) := by
          field_simp
  calc ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖
      ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p), ((p : ℝ) / 2) * ((1 : ℝ) / (tmin h)) :=
        Finset.sum_le_sum hstep
    _ = ((p : ℝ) / 2) * ∑ h ∈ Finset.univ.erase (0 : ZMod p), (1 : ℝ) / (tmin h) := by
        rw [Finset.mul_sum]
    _ ≤ ((p : ℝ) / 2) * (2 * (1 + Real.log p)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_tmin_le hp2) (by positivity)
    _ = (p : ℝ) * (1 + Real.log p) := by ring

/-! ## The uniform Weil input -/

/-- Fourth-root extraction: `x⁴ ≤ 2ℓ³ ⟹ x ≤ 2^{1/4} ℓ^{3/4}`. -/
theorem rpow_extract {l : ℕ} {x : ℝ} (hx : 0 ≤ x) (h4 : x ^ 4 ≤ 2 * (l : ℝ) ^ 3) :
    x ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) * (l : ℝ) ^ ((3 : ℝ) / 4) := by
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hx4 : (0 : ℝ) ≤ x ^ 4 := by positivity
  have h1 : x = (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast x 4, ← Real.rpow_mul hx,
      show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
  rw [h1]
  calc (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ (2 * (l : ℝ) ^ 3) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_le_rpow hx4 h4 (by norm_num)
    _ = (2 : ℝ) ^ ((1 : ℝ) / 4) * (l : ℝ) ^ ((3 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (l : ℝ) 3,
          ← Real.rpow_mul hl0,
          show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 4) = (3 : ℝ) / 4 by norm_num]

/-- **Uniform Weil input.** `‖Kl(c, a)‖ ≤ 2^{1/4} p^{3/4}` for ALL `c` (`a ≠ 0`): the `c ≠ 0`
    range is the repo's fourth-moment bound `kloos_norm_le`; `c = 0` is the Ramanujan value `−1`. -/
theorem kloos_norm_le_uniform {l : ℕ} [Fact l.Prime] (h2 : 2 < l) {a : ZMod l} (ha : a ≠ 0)
    (c : ZMod l) : ‖kloos c a‖ ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) * (l : ℝ) ^ ((3 : ℝ) / 4) := by
  by_cases hc : c = 0
  · subst hc
    rw [kloos_zero ha, norm_neg, norm_one]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by
      have : 1 ≤ l := by omega
      exact_mod_cast this
    have h2' : (1 : ℝ) ≤ (l : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.one_le_rpow hl1 (by norm_num)
    nlinarith
  · exact rpow_extract (norm_nonneg _) (kloos_norm_le h2 hc ha)

/-! ## The incomplete-sum headline -/

/-- `W_M(0) = M`. -/
theorem intervalWeight_zero_freq (p M : ℕ) [NeZero p] : intervalWeight p M 0 = (M : ℂ) := by
  unfold intervalWeight
  have hz : ∀ m : ℕ, ZMod.stdAddChar (-((0 : ZMod p) * (m : ZMod p))) = 1 := fun m => by
    rw [zero_mul, neg_zero, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl (fun m _ => hz m), Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_range]

/-- The complete transform of the guarded inversion phase IS a Kloosterman sum: shifting the
    linear frequency by `h` lands on `Kl(b + h, a)`. -/
theorem incomplete_transform_eq_kloos {p : ℕ} [Fact p.Prime] (a b h : ZMod p) :
    ∑ n : ZMod p,
        (if n = 0 then 0 else ZMod.stdAddChar (a * n⁻¹ + b * n)) * ZMod.stdAddChar (h * n)
      = kloos (b + h) a := by
  unfold kloos
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n = 0
  · rw [if_pos hn, if_neg (fun hcon : n ≠ 0 => hcon hn), zero_mul]
  · rw [if_neg hn, if_pos hn, ← AddChar.map_add_eq_mul]
    congr 1
    ring

/-- **The incomplete Kloosterman bound (headline).** UNCONDITIONAL: for prime `p`, `a ≠ 0`, any
    linear frequency `b` and ANY window length `M`,
    `‖Σ_{m<M} ψ(a·m⁻¹ + b·m)‖ ≤ 2^{1/4} p^{3/4} (M/p + 1 + log p)`.
    Completion → all transforms are complete Kloosterman sums → uniform Weil input → kernel L¹.
    Nontrivial for `M ≫ p^{3/4} log p`; the exponent `3/4` is the fourth-moment strength of
    `kloos_norm_le`, not full Weil `1/2`. -/
theorem incomplete_kloos_bound {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0)
    (b : ZMod p) (M : ℕ) :
    ‖∑ m ∈ Finset.range M,
        (if ((m : ZMod p)) = 0 then 0 else
          ZMod.stdAddChar (a * ((m : ZMod p))⁻¹ + b * ((m : ZMod p))))‖
      ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ ((3 : ℝ) / 4) * ((M : ℝ) / p + 1 + Real.log p) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set κ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ ((3 : ℝ) / 4) with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  -- completion
  have hcomp := interval_completion p M
    (fun n => if n = 0 then 0 else ZMod.stdAddChar (a * n⁻¹ + b * n))
  simp only [incomplete_transform_eq_kloos a b] at hcomp
  rw [hcomp]
  -- split off h = 0
  have hsplit : ∑ h : ZMod p, intervalWeight p M h * kloos (b + h) a
      = intervalWeight p M 0 * kloos (b + 0) a
        + ∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod p))).symm
  rw [hsplit]
  -- norms
  have hzero : ‖intervalWeight p M 0 * kloos (b + 0) a‖ ≤ (M : ℝ) * κ := by
    rw [norm_mul, intervalWeight_zero_freq, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (kloos_norm_le_uniform hp2 ha _) (Nat.cast_nonneg M)
  have htail : ‖∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a‖
      ≤ κ * ((p : ℝ) * (1 + Real.log p)) := by
    calc ‖∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a‖
        ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h * kloos (b + h) a‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖ * κ := by
          apply Finset.sum_le_sum
          intro h _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (kloos_norm_le_uniform hp2 ha _) (norm_nonneg _)
      _ = (∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖) * κ := by
          rw [Finset.sum_mul]
      _ ≤ ((p : ℝ) * (1 + Real.log p)) * κ :=
          mul_le_mul_of_nonneg_right (intervalWeight_L1 hp2 M) hκ0
      _ = κ * ((p : ℝ) * (1 + Real.log p)) := by ring
  calc ‖(p : ℂ)⁻¹ * (intervalWeight p M 0 * kloos (b + 0) a
        + ∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a)‖
      = (1 / (p : ℝ)) * ‖intervalWeight p M 0 * kloos (b + 0) a
          + ∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast, one_div]
    _ ≤ (1 / (p : ℝ)) * ((M : ℝ) * κ + κ * ((p : ℝ) * (1 + Real.log p))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖intervalWeight p M 0 * kloos (b + 0) a
              + ∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a‖
            ≤ ‖intervalWeight p M 0 * kloos (b + 0) a‖
              + ‖∑ h ∈ Finset.univ.erase (0 : ZMod p), intervalWeight p M h * kloos (b + h) a‖ :=
              norm_add_le _ _
          _ ≤ (M : ℝ) * κ + κ * ((p : ℝ) * (1 + Real.log p)) := by
              linarith [hzero, htail]
    _ = κ * ((M : ℝ) / p + 1 + Real.log p) := by
        field_simp
        ring

/-- **Sharp pure-inversion form (`b = 0`).**
    `‖Σ_{m<M} ψ(a·m⁻¹)‖ ≤ M/p + 2^{1/4} p^{3/4} (1 + log p)`: the `h = 0` transform is the
    Ramanujan value `Kl(0, a) = −1`, so the main term contributes only `M/p`. -/
theorem incomplete_inv_sum_bound {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0)
    (M : ℕ) :
    ‖∑ m ∈ Finset.range M,
        (if ((m : ZMod p)) = 0 then 0 else ZMod.stdAddChar (a * ((m : ZMod p))⁻¹))‖
      ≤ (M : ℝ) / p
        + (2 : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ ((3 : ℝ) / 4) * (1 + Real.log p) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set κ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ ((3 : ℝ) / 4) with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hf : ∀ n : ZMod p, (if n = 0 then (0 : ℂ) else ZMod.stdAddChar (a * n⁻¹))
      = (if n = 0 then 0 else ZMod.stdAddChar (a * n⁻¹ + (0 : ZMod p) * n)) := by
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_neg hn, zero_mul, add_zero]
  simp only [hf]
  have hcomp := interval_completion p M
    (fun n => if n = 0 then 0 else ZMod.stdAddChar (a * n⁻¹ + (0 : ZMod p) * n))
  simp only [incomplete_transform_eq_kloos a (0 : ZMod p)] at hcomp
  rw [hcomp]
  have hsplit : ∑ h : ZMod p, intervalWeight p M h * kloos ((0 : ZMod p) + h) a
      = intervalWeight p M 0 * kloos ((0 : ZMod p) + 0) a
        + ∑ h ∈ Finset.univ.erase (0 : ZMod p),
            intervalWeight p M h * kloos ((0 : ZMod p) + h) a :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod p))).symm
  rw [hsplit]
  have hzero : ‖intervalWeight p M 0 * kloos ((0 : ZMod p) + 0) a‖ = (M : ℝ) := by
    rw [norm_mul, intervalWeight_zero_freq, add_zero, kloos_zero ha, norm_neg, norm_one,
      mul_one, Complex.norm_natCast]
  have htail : ‖∑ h ∈ Finset.univ.erase (0 : ZMod p),
      intervalWeight p M h * kloos ((0 : ZMod p) + h) a‖
      ≤ κ * ((p : ℝ) * (1 + Real.log p)) := by
    calc ‖∑ h ∈ Finset.univ.erase (0 : ZMod p),
          intervalWeight p M h * kloos ((0 : ZMod p) + h) a‖
        ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p),
            ‖intervalWeight p M h * kloos ((0 : ZMod p) + h) a‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖ * κ := by
          apply Finset.sum_le_sum
          intro h _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (kloos_norm_le_uniform hp2 ha _) (norm_nonneg _)
      _ = (∑ h ∈ Finset.univ.erase (0 : ZMod p), ‖intervalWeight p M h‖) * κ := by
          rw [Finset.sum_mul]
      _ ≤ ((p : ℝ) * (1 + Real.log p)) * κ :=
          mul_le_mul_of_nonneg_right (intervalWeight_L1 hp2 M) hκ0
      _ = κ * ((p : ℝ) * (1 + Real.log p)) := by ring
  calc ‖(p : ℂ)⁻¹ * (intervalWeight p M 0 * kloos ((0 : ZMod p) + 0) a
        + ∑ h ∈ Finset.univ.erase (0 : ZMod p),
            intervalWeight p M h * kloos ((0 : ZMod p) + h) a)‖
      = (1 / (p : ℝ)) * ‖intervalWeight p M 0 * kloos ((0 : ZMod p) + 0) a
          + ∑ h ∈ Finset.univ.erase (0 : ZMod p),
              intervalWeight p M h * kloos ((0 : ZMod p) + h) a‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast, one_div]
    _ ≤ (1 / (p : ℝ)) * ((M : ℝ) + κ * ((p : ℝ) * (1 + Real.log p))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖intervalWeight p M 0 * kloos ((0 : ZMod p) + 0) a
              + ∑ h ∈ Finset.univ.erase (0 : ZMod p),
                  intervalWeight p M h * kloos ((0 : ZMod p) + h) a‖
            ≤ ‖intervalWeight p M 0 * kloos ((0 : ZMod p) + 0) a‖
              + ‖∑ h ∈ Finset.univ.erase (0 : ZMod p),
                  intervalWeight p M h * kloos ((0 : ZMod p) + h) a‖ := norm_add_le _ _
          _ ≤ (M : ℝ) + κ * ((p : ℝ) * (1 + Real.log p)) := by
              rw [hzero]
              linarith [htail]
    _ = (M : ℝ) / p + κ * (1 + Real.log p) := by
        field_simp

/-! ## The geometric payoff: short-window equidistribution of the circle -/

private theorem two_ne_zero_zmodl {l : ℕ} [Fact l.Prime] (h2 : 2 < l) : (2 : ZMod l) ≠ 0 := by
  have : ((2 : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod l) l 2]
    intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
  simpa using this

/-- The circle sum IS the Fourier transform of the real-coordinate fiber counts
    (standalone extraction of the inline step of `circleSum_eq_neg_kloos`). -/
theorem circleSum_eq_fiber_transform {d l : ℕ} [NeZero l] (u : ZMod l) :
    circleSum d u = ∑ a : ZMod l,
      (((circle d l).filter fun x => x.re = a).card : ℂ) * ZMod.stdAddChar (u * a) := by
  calc circleSum d u
      = ∑ a : ZMod l, ∑ _x ∈ (circle d l).filter (fun x => x.re = a),
          ZMod.stdAddChar (u * a) := by
        rw [circleSum_def]
        exact (Finset.sum_fiberwise' (circle d l) (fun x => x.re)
          (fun a => ZMod.stdAddChar (u * a))).symm
    _ = ∑ a : ZMod l, (((circle d l).filter fun x => x.re = a).card : ℂ)
          * ZMod.stdAddChar (u * a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Every nonzero frequency of the circle is Weil-small: `‖circleSum d h‖ ≤ 2^{1/4} ℓ^{3/4}`. -/
theorem circleSum_norm_le_rpow {d l : ℕ} [Fact l.Prime] (h2 : 2 < l)
    (hd : ¬ IsSquare ((d : ZMod l))) {h : ZMod l} (hh : h ≠ 0) :
    ‖circleSum d h‖ ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) * (l : ℝ) ^ ((3 : ℝ) / 4) := by
  have h20 : (2 : ZMod l) ≠ 0 := two_ne_zero_zmodl h2
  have hne : h * (2 : ZMod l)⁻¹ ≠ 0 := mul_ne_zero hh (inv_ne_zero h20)
  rw [circleSum_eq_neg_kloos h2 hd hh, norm_neg]
  exact rpow_extract (norm_nonneg _) (kloos_norm_le h2 hne hne)

/-- The window count is the short sum of the real-coordinate fiber counts (`M ≤ ℓ`). -/
private theorem circle_window_eq_fiber_sum {d l : ℕ} [Fact l.Prime] {M : ℕ} (hMl : M ≤ l) :
    ((circle d l).filter fun x => x.re.val < M).card
      = ∑ m ∈ Finset.range M, ((circle d l).filter fun x => x.re = ((m : ZMod l))).card := by
  have hx : ∀ r : ZMod l,
      ∑ m ∈ Finset.range M, (if r = ((m : ZMod l)) then (1 : ℕ) else 0)
        = if r.val < M then 1 else 0 := by
    intro r
    by_cases hr : r.val < M
    · rw [if_pos hr, Finset.sum_eq_single r.val]
      · rw [if_pos (ZMod.natCast_rightInverse r).symm]
      · intro m hm hne
        rw [if_neg]
        intro hc
        exact hne (by rw [hc, ZMod.val_cast_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hm) hMl)])
      · intro hnot
        exact absurd (Finset.mem_range.mpr hr) hnot
    · rw [if_neg hr]
      apply Finset.sum_eq_zero
      intro m hm
      rw [if_neg]
      intro hc
      exact hr (by
        rw [hc, ZMod.val_cast_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hm) hMl)]
        exact Finset.mem_range.mp hm)
  calc ((circle d l).filter fun x => x.re.val < M).card
      = ∑ x ∈ circle d l, (if x.re.val < M then (1 : ℕ) else 0) := Finset.card_filter _ _
    _ = ∑ x ∈ circle d l, ∑ m ∈ Finset.range M, (if x.re = ((m : ZMod l)) then (1 : ℕ) else 0) := by
        exact Finset.sum_congr rfl fun x _ => (hx x.re).symm
    _ = ∑ m ∈ Finset.range M, ∑ x ∈ circle d l, (if x.re = ((m : ZMod l)) then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ = ∑ m ∈ Finset.range M, ((circle d l).filter fun x => x.re = ((m : ZMod l))).card :=
        Finset.sum_congr rfl fun m _ => (Finset.card_filter _ _).symm

/-- **Short-window circle equidistribution (payoff).** For `M ≤ ℓ`, the number of circle points
    with real coordinate in the window `[0, M)` deviates from the expected `M(ℓ+1)/ℓ` by at most
    `2^{1/4} ℓ^{3/4} (1 + log ℓ)` — UNCONDITIONAL short-window equidistribution of the inversion
    geometry (the graph `K_{q,q}∖M` / hyperbola-circle of the repo's §22 bridge). -/
theorem circle_short_window_count {d l : ℕ} [Fact l.Prime] (h2 : 2 < l)
    (hd : ¬ IsSquare ((d : ZMod l))) {M : ℕ} (hMl : M ≤ l) :
    |(((circle d l).filter fun x => x.re.val < M).card : ℝ) - (M : ℝ) * ((l : ℝ) + 1) / l|
      ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) * (l : ℝ) ^ ((3 : ℝ) / 4) * (1 + Real.log l) := by
  have hl0 : 0 < l := by omega
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  set κ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) * (l : ℝ) ^ ((3 : ℝ) / 4) with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  -- completion applied to the fiber-count function
  have hcomp := interval_completion l M
    (fun a => (((circle d l).filter fun x => x.re = a).card : ℂ))
  have hF : ∀ h : ZMod l,
      (∑ n : ZMod l, (((circle d l).filter fun x => x.re = n).card : ℂ)
          * ZMod.stdAddChar (h * n))
        = circleSum d h := fun h => (circleSum_eq_fiber_transform h).symm
  simp only [hF] at hcomp
  have hshort : ∑ m ∈ Finset.range M,
      (((circle d l).filter fun x => x.re = ((m : ZMod l))).card : ℂ)
      = ((((circle d l).filter fun x => x.re.val < M).card : ℕ) : ℂ) := by
    rw [circle_window_eq_fiber_sum hMl]
    push_cast
    rfl
  rw [hshort] at hcomp
  -- the exact identity: ℓ·count = M(ℓ+1) + tail
  have hsplit : ∑ h : ZMod l, intervalWeight l M h * circleSum d h
      = intervalWeight l M 0 * circleSum d (0 : ZMod l)
        + ∑ h ∈ Finset.univ.erase (0 : ZMod l), intervalWeight l M h * circleSum d h :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod l))).symm
  have hW0 : intervalWeight l M 0 * circleSum d (0 : ZMod l) = (M : ℂ) * ((l : ℂ) + 1) := by
    rw [intervalWeight_zero_freq, circleSum_zero h2 hd]
  have hid : (l : ℂ) * ((((circle d l).filter fun x => x.re.val < M).card : ℕ) : ℂ)
      = (M : ℂ) * ((l : ℂ) + 1)
        + ∑ h ∈ Finset.univ.erase (0 : ZMod l), intervalWeight l M h * circleSum d h := by
    have hl0C : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc (l : ℂ) * ((((circle d l).filter fun x => x.re.val < M).card : ℕ) : ℂ)
        = (l : ℂ) * ((l : ℂ)⁻¹ * ∑ h : ZMod l, intervalWeight l M h * circleSum d h) := by
          rw [← hcomp]
      _ = ∑ h : ZMod l, intervalWeight l M h * circleSum d h := by
          rw [← mul_assoc, mul_inv_cancel₀ hl0C, one_mul]
      _ = (M : ℂ) * ((l : ℂ) + 1)
          + ∑ h ∈ Finset.univ.erase (0 : ZMod l), intervalWeight l M h * circleSum d h := by
          rw [hsplit, hW0]
  -- bound the tail
  have htail : ‖∑ h ∈ Finset.univ.erase (0 : ZMod l), intervalWeight l M h * circleSum d h‖
      ≤ κ * ((l : ℝ) * (1 + Real.log l)) := by
    calc ‖∑ h ∈ Finset.univ.erase (0 : ZMod l), intervalWeight l M h * circleSum d h‖
        ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod l), ‖intervalWeight l M h * circleSum d h‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod l), ‖intervalWeight l M h‖ * κ := by
          apply Finset.sum_le_sum
          intro h hmem
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (circleSum_norm_le_rpow h2 hd (Finset.ne_of_mem_erase hmem)) (norm_nonneg _)
      _ = (∑ h ∈ Finset.univ.erase (0 : ZMod l), ‖intervalWeight l M h‖) * κ := by
          rw [Finset.sum_mul]
      _ ≤ ((l : ℝ) * (1 + Real.log l)) * κ :=
          mul_le_mul_of_nonneg_right (intervalWeight_L1 h2 M) hκ0
      _ = κ * ((l : ℝ) * (1 + Real.log l)) := by ring
  -- real form + division by ℓ
  have hcx : (((l : ℝ) * (((circle d l).filter fun x => x.re.val < M).card : ℝ)
        - (M : ℝ) * ((l : ℝ) + 1) : ℝ) : ℂ)
      = ∑ h ∈ Finset.univ.erase (0 : ZMod l), intervalWeight l M h * circleSum d h := by
    push_cast
    linear_combination hid
  have habs : |(l : ℝ) * (((circle d l).filter fun x => x.re.val < M).card : ℝ)
        - (M : ℝ) * ((l : ℝ) + 1)|
      ≤ κ * ((l : ℝ) * (1 + Real.log l)) := by
    have h1 : |(l : ℝ) * (((circle d l).filter fun x => x.re.val < M).card : ℝ)
          - (M : ℝ) * ((l : ℝ) + 1)|
        = ‖(((l : ℝ) * (((circle d l).filter fun x => x.re.val < M).card : ℝ)
            - (M : ℝ) * ((l : ℝ) + 1) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hcx]
    exact htail
  have hdiv : (((circle d l).filter fun x => x.re.val < M).card : ℝ)
      - (M : ℝ) * ((l : ℝ) + 1) / l
      = ((l : ℝ) * (((circle d l).filter fun x => x.re.val < M).card : ℝ)
          - (M : ℝ) * ((l : ℝ) + 1)) / l := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hlR, div_le_iff₀ hlR]
  calc |(l : ℝ) * (((circle d l).filter fun x => x.re.val < M).card : ℝ)
        - (M : ℝ) * ((l : ℝ) + 1)|
      ≤ κ * ((l : ℝ) * (1 + Real.log l)) := habs
    _ = κ * (1 + Real.log l) * l := by ring

end TypeII
end Geometric
end EuclidsPath
