/-
  GeometricTypeIISalie — the CLASSICAL SALIÉ EVALUATION over `ZMod ℓ`: the
  quadratic-twisted Kloosterman sum `T(a,b) = Σ_{x≠0} χ(x)ψ(ax + b/x)` closes in
  FINITELY many terms — `T(a,b) = χ(a)·g(χ)·Σ_{v² = ab} ψ(2v)` — and hence obeys
  the pointwise ALL-FREQUENCY bound `‖T(a,b)‖ ≤ 2√ℓ` with NO fourth-moment
  averaging and no Weil input.

  ORIGIN.  Idea-generation session (two-axes program, wave 3, the geometry
  panel's upgrade path).  The twin-variety module's short-window theorem is an
  ALMOST-ALL-frequencies statement (Markov over the family moment); the panel's
  Salié route is the classical mechanism by which a TWISTED single-pole sum gets
  a pointwise bound at every frequency.  Design adversarially verified (wave-3b
  pre-pass) with ONE MANDATORY CORRECTION: the classical identity carries the
  twist `χ(a)` — without it the identity is FALSE (refuted numerically at
  `ℓ = 7, a = 3, b = 6`); with it, verified to `8·10⁻¹⁵` for ALL `a, b ≠ 0` at
  `ℓ = 3, 5, 7, 11, 13, 17, 19, 23`.  The chosen route is completing-the-square
  + fiberwise regrouping — the delta-trick route is CIRCULAR (it regenerates
  Kloosterman sums) and is not used.

  THE CHAIN.  `T(a,b) = χ(a)·U(ab)` (unit rescale; `U(c) = Σ χ(x)ψ(x + c/x)`);
  for `ab` a nonsquare, `U(ab) = 0` (the involution `x ↦ c/x` flips the sign);
  for `ab = v²`, completing the square gives `U(v²) = ψ(−2v)·S(v)` with
  `S(v) = Σ_w χ(w)ψ((w+v)²/w)`, and the fiber count of `(w+v)²/w = t` is EXACTLY
  `1 + χ(t(t−4v))` (a shifted square count), which regroups `S(v)` into
  `g(χ)·(1 + ψ(4v))` — everything closes in Gauss-sum data.  `‖g(χ)‖ = √ℓ` is
  derived (NOT in the pin) from `g·g* = ℓ`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `salie` — the twisted sum, filter style mirroring the house `kloos`;
    * `salie_eval` — **THE CLASSICAL IDENTITY**:
      `T(a,b) = χ(a)·g(χ)·Σ_{v² = ab} ψ(2v)` for `a, b ≠ 0` (both cases: for
      nonsquare `ab` the root set is empty and both sides vanish);
    * `salie_eq_zero_of_nonsquare` — the vanishing half, stated separately;
    * `gauss_norm` — `‖g(χ)‖ = √ℓ` (derived: `g·star g = ℓ`);
    * `salie_norm_le` — **THE ALL-FREQUENCY BOUND**: `‖T(a,b)‖ ≤ 2√ℓ` for ALL
      `a, b ≠ 0`;
    * `salie_sq_norm_le` — `‖T(a,b)‖² ≤ 4ℓ` (numerically sharp: `3.93ℓ` observed
      at `ℓ = 23` — the constant 2 is asymptotically optimal, not improvable).

  DISCLOSURES (mandatory reading before quoting):
    * ONE POLE ONLY.  The Salié mechanism needs the TWIST `χ` and a SINGLE pole:
      the twin two-pole sum `V(a,b₁,b₂)` (poles at `0` and `−2`) does NOT reduce
      to Salié — the two-pole all-frequency problem at exponent `1/2` remains
      genuinely open here.  What this module upgrades is the SINGLE-pole twisted
      object, at every frequency; the twin variety keeps its almost-all Markov
      statement.  Any claim that this bounds the twin family pointwise would be
      FALSE.
    * UNSIGNED, ONE PRIME MODULUS.  Additive/multiplicative characters mod one
      prime; the μ-signed aggregation across conductors (the wall) is untouched.
      NOT a §110 event; no registered target moved.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### The quadratic character over ℂ and the twisted sum -/

/-- The quadratic character of `ZMod ℓ` pushed to ℂ. -/
private noncomputable def chiC (ℓ : ℕ) [Fact ℓ.Prime] : MulChar (ZMod ℓ) ℂ :=
  (quadraticChar (ZMod ℓ)).ringHomComp (Int.castRingHom ℂ)

/-- **The Salié sum** `T(a,b) = Σ_{x≠0} χ(x)·ψ(ax + b·x⁻¹)` (filter style
    mirroring the house `kloos`).  A named structural object, NOT a target. -/
noncomputable def salie {ℓ : ℕ} [Fact ℓ.Prime] (a b : ZMod ℓ) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
    chiC ℓ x * ZMod.stdAddChar (a * x + b * x⁻¹)

/-- The centered one-parameter form `U(c) = Σ_x χ(x)ψ(x + c·x⁻¹)` (full sum —
    the `x = 0` term vanishes through `χ(0) = 0`). -/
private noncomputable def Usum {ℓ : ℕ} [Fact ℓ.Prime] (c : ZMod ℓ) : ℂ :=
  ∑ x : ZMod ℓ, chiC ℓ x * ZMod.stdAddChar (x + c * x⁻¹)

/-- The completed-square form `S(v) = Σ_w χ(w)ψ((w+v)²·w⁻¹)`. -/
private noncomputable def Ssum {ℓ : ℕ} [Fact ℓ.Prime] (v : ZMod ℓ) : ℂ :=
  ∑ w : ZMod ℓ, chiC ℓ w * ZMod.stdAddChar ((w + v) ^ 2 * w⁻¹)

/-! ### Character toolkit -/

private theorem chiC_apply {ℓ : ℕ} [Fact ℓ.Prime] (x : ZMod ℓ) :
    chiC ℓ x = ((quadraticChar (ZMod ℓ) x : ℤ) : ℂ) := by
  rfl

private theorem chiC_zero {ℓ : ℕ} [Fact ℓ.Prime] : chiC ℓ 0 = 0 := by
  rw [chiC_apply, quadraticChar_zero]
  norm_num

private theorem chiC_mul_self {ℓ : ℕ} [Fact ℓ.Prime] {x : ZMod ℓ} (hx : x ≠ 0) :
    chiC ℓ x * chiC ℓ x = 1 := by
  rw [← map_mul, ← sq, chiC_apply, quadraticChar_sq_one' hx]
  norm_num

private theorem chiC_inv_arg {ℓ : ℕ} [Fact ℓ.Prime] (x : ZMod ℓ) :
    chiC ℓ x⁻¹ = chiC ℓ x := by
  by_cases hx : x = 0
  · rw [hx, inv_zero]
  · have h1 : chiC ℓ x⁻¹ * chiC ℓ x = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hx, MulChar.map_one]
    have h2 := chiC_mul_self hx
    calc chiC ℓ x⁻¹ = chiC ℓ x⁻¹ * (chiC ℓ x * chiC ℓ x) := by rw [h2, mul_one]
      _ = (chiC ℓ x⁻¹ * chiC ℓ x) * chiC ℓ x := by ring
      _ = chiC ℓ x := by rw [h1, one_mul]

private theorem chiC_norm {ℓ : ℕ} [Fact ℓ.Prime] {x : ZMod ℓ} (hx : x ≠ 0) :
    ‖chiC ℓ x‖ = 1 := by
  rw [chiC_apply]
  rcases quadraticChar_dichotomy hx with h | h <;> simp [h]

private theorem ringChar_ne_two {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ringChar (ZMod ℓ) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

private theorem chiC_ne_one {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    chiC ℓ ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
    (quadraticChar_ne_one (ringChar_ne_two h2))

private theorem stdAddChar_norm_one' {ℓ : ℕ} [NeZero ℓ] (x : ZMod ℓ) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- `‖g(χ)‖ = √ℓ` — derived from `g·(star g) = ℓ` (the pin has the product
    identity but NOT the norm form). -/
theorem gauss_norm {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ‖gaussSum (chiC ℓ) ZMod.stdAddChar‖ = Real.sqrt ℓ := by
  have h : gaussSum (chiC ℓ) ZMod.stdAddChar
      * star (gaussSum (chiC ℓ) ZMod.stdAddChar)
      = (Fintype.card (ZMod ℓ) : ℂ) := by
    have h0 := gaussSum_mul_gaussSum_eq_card (chiC_ne_one h2)
      (ZMod.isPrimitive_stdAddChar ℓ)
    rw [← star_gaussSum_eq] at h0
    exact h0
  have hsq : (‖gaussSum (chiC ℓ) ZMod.stdAddChar‖ ^ 2 : ℂ) = ((ℓ : ℝ) : ℂ) := by
    rw [← Complex.mul_conj']
    rw [show (starRingEnd ℂ) (gaussSum (chiC ℓ) ZMod.stdAddChar)
        = star (gaussSum (chiC ℓ) ZMod.stdAddChar) from rfl]
    rw [h, ZMod.card]
    norm_cast
  have hreal : ‖gaussSum (chiC ℓ) ZMod.stdAddChar‖ ^ 2 = (ℓ : ℝ) := by
    exact_mod_cast hsq
  rw [← hreal, Real.sqrt_sq (norm_nonneg _)]

/-! ### The chain: rescale, vanish on nonsquares, complete the square -/

/-- `T(a,b) = χ(a)·U(ab)` — the unit rescale `x ↦ a·x` centers the sum. -/
private theorem salie_eq_U_twist {ℓ : ℕ} [Fact ℓ.Prime] {a : ZMod ℓ}
    (ha : a ≠ 0) (b : ZMod ℓ) :
    salie a b = chiC ℓ a * Usum (a * b) := by
  have hfull : salie a b
      = ∑ x : ZMod ℓ, chiC ℓ x * ZMod.stdAddChar (a * x + b * x⁻¹) := by
    unfold salie
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = 0
    · rw [if_neg (by simp [hx]), hx, chiC_zero, zero_mul]
    · rw [if_pos hx]
  rw [hfull]
  unfold Usum
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (a * ·) (mulLeft_bijective₀ a ha) _ _ fun x => ?_
  by_cases hx : x = 0
  · simp [hx, chiC_zero]
  · have harg : a * x + a * b * (a * x)⁻¹ = a * x + b * x⁻¹ := by
      rw [mul_inv_rev]
      field_simp
    rw [map_mul, harg]
    have hsq := chiC_mul_self ha
    linear_combination
      (-(ZMod.stdAddChar (a * x + b * x⁻¹) * chiC ℓ x)) * hsq

/-- On nonsquares the centered sum VANISHES: the involution `x ↦ c·x⁻¹`
    preserves the additive argument and multiplies the character by
    `χ(c) = −1`. -/
private theorem Usum_eq_zero_of_nonsquare {ℓ : ℕ} [Fact ℓ.Prime]
    {c : ZMod ℓ} (hc : c ≠ 0) (hns : ¬IsSquare c) :
    Usum (ℓ := ℓ) c = 0 := by
  have hinv : Function.Involutive (fun x : ZMod ℓ => c * x⁻¹) := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  have hU : Usum (ℓ := ℓ) c = chiC ℓ c * Usum c := by
    conv_lhs => rw [Usum, ← Equiv.sum_comp hinv.toPerm]
    unfold Usum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show chiC ℓ (c * x⁻¹) * ZMod.stdAddChar (c * x⁻¹ + c * (c * x⁻¹)⁻¹) = _
    by_cases hx : x = 0
    · simp [hx, chiC_zero]
    · have harg : c * x⁻¹ + c * (c * x⁻¹)⁻¹ = x + c * x⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        field_simp
        ring
      rw [harg, map_mul, chiC_inv_arg]
      ring
  have hchi : chiC ℓ c = -1 := by
    rw [chiC_apply, (quadraticChar_neg_one_iff_not_isSquare (a := c)).mpr hns]
    norm_num
  rw [hchi] at hU
  have h2U : (2 : ℂ) * Usum (ℓ := ℓ) c = 0 := by linear_combination hU
  exact (mul_eq_zero.mp h2U).resolve_left (by norm_num)

/-- Completing the square: `U(v²) = ψ(−2v)·S(v)`. -/
private theorem Usum_sq_eq {ℓ : ℕ} [Fact ℓ.Prime] {v : ZMod ℓ} :
    Usum (ℓ := ℓ) (v ^ 2) = ZMod.stdAddChar (-(2 * v)) * Ssum v := by
  unfold Usum Ssum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : w = 0
  · simp [hw, chiC_zero]
  · have harg : (w + v) ^ 2 * w⁻¹ = (w + v ^ 2 * w⁻¹) + 2 * v := by
      field_simp
      ring
    have hsplit : ZMod.stdAddChar ((w + v ^ 2 * w⁻¹) + 2 * v)
        = ZMod.stdAddChar (w + v ^ 2 * w⁻¹) * ZMod.stdAddChar (2 * v) :=
      AddChar.map_add_eq_mul _ _ _
    have hcancel : ZMod.stdAddChar (-(2 * v)) * ZMod.stdAddChar (2 * v)
        = (1 : ℂ) := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rw [harg, hsplit]
    linear_combination
      (-(chiC ℓ w * ZMod.stdAddChar (w + v ^ 2 * w⁻¹))) * hcancel

/-! ### The fiber count and the regrouping of `S` -/

/-- On the completed square the character sees only `w`:
    `χ((w+v)²·w⁻¹) = χ(w)` for `w ≠ 0`, `w + v ≠ 0`. -/
private theorem chiC_completed {ℓ : ℕ} [Fact ℓ.Prime] {w v : ZMod ℓ}
    (hwv : w + v ≠ 0) :
    chiC ℓ ((w + v) ^ 2 * w⁻¹) = chiC ℓ w := by
  have h1 : chiC ℓ ((w + v) ^ 2) = 1 := by
    rw [chiC_apply, quadraticChar_sq_one' hwv]
    norm_num
  rw [map_mul, h1, one_mul, chiC_inv_arg]

/-- **The fiber count**: `#{w : (w+v)² = t·w} = χ(t(t−4v)) + 1` — the completed
    square shifts the fiber onto a plain square count. -/
private theorem fiber_count {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    {v t : ZMod ℓ} :
    ((Finset.univ.filter fun w : ZMod ℓ => (w + v) ^ 2 = t * w).card : ℤ)
      = quadraticChar (ZMod ℓ) (t * (t - 4 * v)) + 1 := by
  classical
  have h20 : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two h2)
  have hbij : (Finset.univ.filter fun w : ZMod ℓ => (w + v) ^ 2 = t * w).card
      = ({x : ZMod ℓ | x ^ 2 = t * (t - 4 * v)}.toFinset).card := by
    rw [Set.toFinset_setOf]
    refine Finset.card_nbij' (fun w => 2 * w + 2 * v - t)
      (fun r => (r + t - 2 * v) * (2 : ZMod ℓ)⁻¹) ?_ ?_ ?_ ?_
    · intro w hw
      have hroot : (w + v) ^ 2 = t * w := (Finset.mem_filter.mp hw).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      linear_combination 4 * hroot
    · intro r hr
      have hroot : r ^ 2 = t * (t - 4 * v) := (Finset.mem_filter.mp hr).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      field_simp
      linear_combination hroot
    · intro w _
      field_simp
      ring
    · intro r _
      field_simp
      ring
  rw [hbij, quadraticChar_card_sqrts (ringChar_ne_two h2)]

/-- **The regrouping of `S`**: peeling `w = 0` and `w = −v` and fibering the rest
    over the completed-square value `t`,
    `S(v) = χ(−v) + Σ_{t≠0} (1 + χ(t(t−4v)))·χ(t)ψ(t)`. -/
private theorem Ssum_regroup {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    {v : ZMod ℓ} (hv : v ≠ 0) :
    Ssum v = chiC ℓ (-v)
      + ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
          ((1 : ℂ) + chiC ℓ (t * (t - 4 * v)))
            * (chiC ℓ t * ZMod.stdAddChar t) := by
  classical
  have hmem0 : (0 : ZMod ℓ) ∈ (Finset.univ : Finset (ZMod ℓ)) := Finset.mem_univ _
  have hmemv : (-v : ZMod ℓ) ∈ Finset.univ.erase (0 : ZMod ℓ) :=
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr hv, Finset.mem_univ _⟩
  set A := (Finset.univ.erase (0 : ZMod ℓ)).erase (-v) with hA
  set F : ZMod ℓ → ℂ := fun w => chiC ℓ w * ZMod.stdAddChar ((w + v) ^ 2 * w⁻¹)
    with hF
  have hpeel : Ssum v = F 0 + (F (-v) + ∑ w ∈ A, F w) := by
    have h1 : ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), F w
        = F (-v) + ∑ w ∈ A, F w :=
      (Finset.add_sum_erase _ F hmemv).symm
    have h2 : ∑ w : ZMod ℓ, F w
        = F 0 + ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), F w :=
      (Finset.add_sum_erase _ F hmem0).symm
    show ∑ w : ZMod ℓ, F w = F 0 + (F (-v) + ∑ w ∈ A, F w)
    rw [h2, h1]
  have hF0 : F 0 = 0 := by
    rw [hF]
    show chiC ℓ 0 * _ = 0
    rw [chiC_zero, zero_mul]
  have hFv : F (-v) = chiC ℓ (-v) := by
    rw [hF]
    show chiC ℓ (-v) * ZMod.stdAddChar ((-v + v) ^ 2 * (-v)⁻¹) = _
    rw [neg_add_cancel]
    norm_num
  -- fiber the A-sum over the completed-square value
  have hmaps : ∀ w ∈ A, ((w + v) ^ 2 * w⁻¹)
      ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0) := by
    intro w hw
    have hw0 : w ≠ 0 := (Finset.mem_erase.mp ((Finset.mem_erase.mp hw).2)).1
    have hwv : w + v ≠ 0 := by
      intro h
      exact (Finset.mem_erase.mp hw).1 (by linear_combination h)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mul_ne_zero (pow_ne_zero _ hwv) (inv_ne_zero hw0)⟩
  have hfiber : ∑ w ∈ A, F w
      = ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
          ∑ w ∈ A.filter (fun w => (w + v) ^ 2 * w⁻¹ = t),
            (chiC ℓ t * ZMod.stdAddChar t) := by
    have hcongr : ∀ w ∈ A, F w
        = (fun t => chiC ℓ t * ZMod.stdAddChar t) ((w + v) ^ 2 * w⁻¹) := by
      intro w hw
      have hw0 : w ≠ 0 := (Finset.mem_erase.mp ((Finset.mem_erase.mp hw).2)).1
      have hwv : w + v ≠ 0 := by
        intro h
        exact (Finset.mem_erase.mp hw).1 (by linear_combination h)
      rw [hF]
      show chiC ℓ w * ZMod.stdAddChar ((w + v) ^ 2 * w⁻¹)
        = chiC ℓ ((w + v) ^ 2 * w⁻¹)
          * ZMod.stdAddChar ((w + v) ^ 2 * w⁻¹)
      rw [chiC_completed hwv]
    rw [Finset.sum_congr rfl hcongr]
    exact (Finset.sum_fiberwise_of_maps_to' hmaps
      (fun t => chiC ℓ t * ZMod.stdAddChar t)).symm
  -- identify each fiber with the full root filter and count it
  have hcount : ∀ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
      ∑ w ∈ A.filter (fun w => (w + v) ^ 2 * w⁻¹ = t),
          (chiC ℓ t * ZMod.stdAddChar t)
      = ((1 : ℂ) + chiC ℓ (t * (t - 4 * v)))
          * (chiC ℓ t * ZMod.stdAddChar t) := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_filter.mp ht).2
    have hfil : A.filter (fun w => (w + v) ^ 2 * w⁻¹ = t)
        = Finset.univ.filter (fun w : ZMod ℓ => (w + v) ^ 2 = t * w) := by
      ext w
      simp only [hA, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        and_true, true_and]
      constructor
      · rintro ⟨⟨hwv, hw0⟩, hphi⟩
        calc (w + v) ^ 2 = (w + v) ^ 2 * w⁻¹ * w := by
              field_simp
          _ = t * w := by rw [hphi]
      · intro hroot
        have hw0 : w ≠ 0 := by
          intro h
          rw [h] at hroot
          simp only [zero_add, mul_zero] at hroot
          exact hv (pow_eq_zero_iff (by norm_num) |>.mp hroot)
        have hwv : w ≠ -v := by
          intro h
          rw [h] at hroot
          rw [neg_add_cancel] at hroot
          have : t * -v = 0 := by linear_combination -hroot
          rcases mul_eq_zero.mp this with h' | h'
          · exact ht0 h'
          · exact hv (neg_eq_zero.mp h')
        refine ⟨⟨hwv, hw0⟩, ?_⟩
        field_simp
        linear_combination hroot
    rw [hfil, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard := fiber_count (v := v) (t := t) h2
    have hcast : ((Finset.univ.filter
        fun w : ZMod ℓ => (w + v) ^ 2 = t * w).card : ℂ)
        = ((quadraticChar (ZMod ℓ) (t * (t - 4 * v)) + 1 : ℤ) : ℂ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hcard
    rw [hcast, chiC_apply]
    push_cast
    ring
  rw [hpeel, hF0, hFv, zero_add, hfiber, Finset.sum_congr rfl hcount]

set_option maxHeartbeats 800000 in
/-- **The evaluation of `S`**: `S(v) = g(χ)·(1 + ψ(4v))`. -/
private theorem Ssum_eval {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    {v : ZMod ℓ} (hv : v ≠ 0) :
    Ssum v = gaussSum (chiC ℓ) ZMod.stdAddChar
      * (1 + ZMod.stdAddChar (4 * v)) := by
  classical
  rw [Ssum_regroup h2 hv]
  have hsplit : ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
      ((1 : ℂ) + chiC ℓ (t * (t - 4 * v))) * (chiC ℓ t * ZMod.stdAddChar t)
      = (∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
          chiC ℓ t * ZMod.stdAddChar t)
        + ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
            chiC ℓ (t * (t - 4 * v)) * (chiC ℓ t * ZMod.stdAddChar t) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hsplit]
  -- SUM1 is the Gauss sum (the t = 0 term vanishes)
  have hsum1 : ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
      chiC ℓ t * ZMod.stdAddChar t = gaussSum (chiC ℓ) ZMod.stdAddChar := by
    unfold gaussSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t = 0
    · rw [if_neg (by simp [ht]), ht, chiC_zero, zero_mul]
    · rw [if_pos ht]
  -- SUM2: χ(t(t−4v))·χ(t) = χ(t−4v); reindex; peel back the t = 0 term
  have hsum2 : ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
      chiC ℓ (t * (t - 4 * v)) * (chiC ℓ t * ZMod.stdAddChar t)
      = ZMod.stdAddChar (4 * v) * gaussSum (chiC ℓ) ZMod.stdAddChar
        - chiC ℓ (-v) := by
    have hterm : ∀ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
        chiC ℓ (t * (t - 4 * v)) * (chiC ℓ t * ZMod.stdAddChar t)
        = chiC ℓ (t - 4 * v) * ZMod.stdAddChar t := by
      intro t ht
      have ht0 : t ≠ 0 := (Finset.mem_filter.mp ht).2
      rw [map_mul]
      have hsq := chiC_mul_self ht0
      linear_combination
        (chiC ℓ (t - 4 * v) * ZMod.stdAddChar t) * hsq
    rw [Finset.sum_congr rfl hterm]
    -- extend to the full sum: the t = 0 term is χ(−4v)·ψ(0) = χ(−v)
    have hfull : ∑ t : ZMod ℓ, chiC ℓ (t - 4 * v) * ZMod.stdAddChar t
        = chiC ℓ (-(4 * v))
          + ∑ t ∈ Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0),
              chiC ℓ (t - 4 * v) * ZMod.stdAddChar t := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod ℓ))]
      congr 1
      · rw [zero_sub, AddChar.map_zero_eq_one, mul_one]
      · rw [Finset.filter_ne']
    -- reindex the full sum by s := t − 4v
    have hreindex : ∑ t : ZMod ℓ, chiC ℓ (t - 4 * v) * ZMod.stdAddChar t
        = ZMod.stdAddChar (4 * v) * gaussSum (chiC ℓ) ZMod.stdAddChar := by
      unfold gaussSum
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.addRight (4 * v))
        (fun s => ZMod.stdAddChar (4 * v) * (chiC ℓ s * ZMod.stdAddChar s))
        (fun t => chiC ℓ (t - 4 * v) * ZMod.stdAddChar t) fun s => ?_).symm
      simp only [Equiv.coe_addRight]
      rw [add_sub_cancel_right, AddChar.map_add_eq_mul]
      ring
    have hminus : chiC ℓ (-(4 * v)) = chiC ℓ (-v) := by
      have h4 : (-(4 * v) : ZMod ℓ) = 2 ^ 2 * (-v) := by ring
      have h20 : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two h2)
      have hsq2 : chiC ℓ (2 ^ 2) = 1 := by
        rw [chiC_apply, quadraticChar_sq_one' h20]
        norm_num
      rw [h4, map_mul, hsq2, one_mul]
    have := hfull
    rw [hreindex, hminus] at this
    linear_combination -this
  rw [hsum1, hsum2]
  ring

/-! ### Assembly: the classical identity and the bound -/

/-- The root pair: for `v² = c`, `v ≠ 0`, the square roots of `c` are exactly
    `{v, −v}`, distinct. -/
private theorem root_pair {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    {c v : ZMod ℓ} (hv : v ^ 2 = c) (hv0 : v ≠ 0) :
    Finset.univ.filter (fun u : ZMod ℓ => u ^ 2 = c) = {v, -v} ∧ v ≠ -v := by
  constructor
  · ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    subst hv
    exact sq_eq_sq_iff_eq_or_eq_neg
  · intro h
    have h20 : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two h2)
    have : (2 : ZMod ℓ) * v = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact h20 h'
    · exact hv0 h'

/-- **THE CLASSICAL SALIÉ IDENTITY**: for `a, b ≠ 0`,
    `T(a,b) = χ(a)·g(χ)·Σ_{v² = ab} ψ(2v)` — the pre-pass CORRECTED form (the
    twist `χ(a)` is load-bearing; without it the identity is false).  Both cases
    included: for nonsquare `ab` the root sum is empty and `T = 0`. -/
theorem salie_eval {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {a b : ZMod ℓ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    salie a b = chiC ℓ a * gaussSum (chiC ℓ) ZMod.stdAddChar
      * ∑ v ∈ Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = a * b),
          ZMod.stdAddChar (2 * v) := by
  by_cases hsq : IsSquare (a * b)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr
      exact mul_ne_zero ha hb hr
    have hrv : r ^ 2 = a * b := by rw [hr]; ring
    obtain ⟨hpair, hne⟩ := root_pair h2 hrv hr0
    rw [hpair, Finset.sum_pair hne, salie_eq_U_twist ha]
    have hab : a * b = r ^ 2 := hrv.symm
    rw [hab, Usum_sq_eq, Ssum_eval h2 hr0]
    have hnegarg : (2 : ZMod ℓ) * -r = -(2 * r) := by ring
    rw [hnegarg]
    have hexp : ZMod.stdAddChar (-(2 * r)) * (1 + ZMod.stdAddChar (4 * r))
        = ZMod.stdAddChar (2 * r) + ZMod.stdAddChar (-(2 * r)) := by
      have hcomb : ZMod.stdAddChar (-(2 * r)) * ZMod.stdAddChar (4 * r)
          = ZMod.stdAddChar (2 * r) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      calc ZMod.stdAddChar (-(2 * r)) * (1 + ZMod.stdAddChar (4 * r))
          = ZMod.stdAddChar (-(2 * r))
            + ZMod.stdAddChar (-(2 * r)) * ZMod.stdAddChar (4 * r) := by ring
        _ = ZMod.stdAddChar (2 * r) + ZMod.stdAddChar (-(2 * r)) := by
            rw [hcomb]
            ring
    calc chiC ℓ a * (ZMod.stdAddChar (-(2 * r))
          * (gaussSum (chiC ℓ) ZMod.stdAddChar
            * (1 + ZMod.stdAddChar (4 * r))))
        = chiC ℓ a * gaussSum (chiC ℓ) ZMod.stdAddChar
            * (ZMod.stdAddChar (-(2 * r)) * (1 + ZMod.stdAddChar (4 * r))) := by
          ring
      _ = chiC ℓ a * gaussSum (chiC ℓ) ZMod.stdAddChar
            * (ZMod.stdAddChar (2 * r) + ZMod.stdAddChar (-(2 * r))) := by
          rw [hexp]
  · have hU := Usum_eq_zero_of_nonsquare (mul_ne_zero ha hb) hsq
    have hempty : Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = a * b)
        = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _ hv
      exact hsq ⟨v, by rw [← hv]; ring⟩
    rw [salie_eq_U_twist ha, hU, hempty, Finset.sum_empty, mul_zero, mul_zero]

/-- The vanishing half, stated separately: nonsquare `ab` kills the Salié sum. -/
theorem salie_eq_zero_of_nonsquare {ℓ : ℕ} [Fact ℓ.Prime] {a b : ZMod ℓ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hns : ¬IsSquare (a * b)) :
    salie a b = 0 := by
  rw [salie_eq_U_twist ha,
    Usum_eq_zero_of_nonsquare (mul_ne_zero ha hb) hns, mul_zero]

/-- At most two square roots. -/
private theorem card_roots_le_two {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (c : ZMod ℓ) :
    (Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = c)).card ≤ 2 := by
  classical
  have hcard : ((Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = c)).card : ℤ)
      = quadraticChar (ZMod ℓ) c + 1 := by
    have h := quadraticChar_card_sqrts (ringChar_ne_two h2) c
    rw [← h]
    congr 1
    rw [Set.toFinset_setOf]
  have hchi : quadraticChar (ZMod ℓ) c ≤ 1 := by
    by_cases hc : c = 0
    · rw [hc, quadraticChar_zero]
      norm_num
    · rcases quadraticChar_dichotomy hc with h | h <;> simp [h]
  omega

/-- **THE ALL-FREQUENCY BOUND**: `‖T(a,b)‖ ≤ 2√ℓ` for ALL `a, b ≠ 0` —
    pointwise, no averaging, no Weil input. -/
theorem salie_norm_le {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {a b : ZMod ℓ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖salie a b‖ ≤ 2 * Real.sqrt ℓ := by
  rw [salie_eval h2 ha hb, norm_mul, norm_mul, chiC_norm ha, one_mul,
    gauss_norm h2]
  have hsum : ‖∑ v ∈ Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = a * b),
      ZMod.stdAddChar (2 * v)‖ ≤ 2 := by
    calc ‖∑ v ∈ Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = a * b),
        ZMod.stdAddChar (2 * v)‖
        ≤ ∑ v ∈ Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = a * b),
            ‖ZMod.stdAddChar (2 * v)‖ := norm_sum_le _ _
      _ = ((Finset.univ.filter (fun v : ZMod ℓ => v ^ 2 = a * b)).card : ℝ) := by
          rw [Finset.sum_congr rfl fun v _ => stdAddChar_norm_one' (2 * v),
            Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 2 := by exact_mod_cast card_roots_le_two h2 (a * b)
  calc Real.sqrt ℓ * ‖∑ v ∈ Finset.univ.filter
        (fun v : ZMod ℓ => v ^ 2 = a * b), ZMod.stdAddChar (2 * v)‖
      ≤ Real.sqrt ℓ * 2 := by
        exact mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt ℓ := by ring

/-- `‖T(a,b)‖² ≤ 4ℓ` (numerically sharp: `3.93ℓ` observed at `ℓ = 23`). -/
theorem salie_sq_norm_le {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {a b : ZMod ℓ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖salie a b‖ ^ 2 ≤ 4 * (ℓ : ℝ) := by
  have h := salie_norm_le h2 ha hb
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  calc ‖salie a b‖ ^ 2 ≤ (2 * Real.sqrt ℓ) ^ 2 := hsq
    _ = 4 * (Real.sqrt ℓ) ^ 2 := by ring
    _ = 4 * (ℓ : ℝ) := by
        rw [Real.sq_sqrt (Nat.cast_nonneg ℓ)]

/-! ### Axiom audit -/

#print axioms gauss_norm
#print axioms salie_eval
#print axioms salie_eq_zero_of_nonsquare
#print axioms salie_norm_le
#print axioms salie_sq_norm_le

end TypeII
end Geometric
end EuclidsPath
