/-
  GeometricTypeIICocycle — the CRT COCYCLE of the standard additive character: over
  coprime moduli the character at `q₁q₂` factors into the characters at `q₁` and
  `q₂` with UNIT TWISTS `u₁ = q₂⁻¹ (mod q₁)`, `u₂ = q₁⁻¹ (mod q₂)` — the machine
  form of the partial-fraction cocycle `1/(q₁q₂) = u₁/q₁ + u₂/q₂ − integer`.

  ORIGIN.  Idea-generation session (two-axes program, wave 3, face-E
  infrastructure).  The wall's face E (`LowFreqRootCoherence`) lives on SIGNED
  low-frequency coherence across INCOMMENSURABLE moduli; every analytic approach
  to it must first speak a common frequency language across `q`.  This module
  provides that dictionary: the exact factorization of `ψ_{q₁q₂}` through
  `ψ_{q₁}·ψ_{q₂}` with the twisting units made explicit.  The mathlib pin has NO
  such factorization ready-made (checked: no `chineseRemainder` near `stdAddChar`
  anywhere in the pin) — the cocycle integer and the factorization are proved here
  from `ZMod.coe_mul_inv_eq_one` and `Complex.exp_eq_exp_iff_exists_int`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `crt_cocycle_dvd` — **THE COCYCLE INTEGER**: `q₁q₂ ∣ u₁q₂ + u₂q₁ − 1`
      (`u₁ = (q₂ mod q₁)⁻¹.val`, `u₂ = (q₁ mod q₂)⁻¹.val`) — the arithmetic heart:
      the partial-fraction decomposition of `1/(q₁q₂)` closes up to an integer;
    * `stdAddChar_crt_factor` — **THE FACTORIZATION**: for coprime `q₁, q₂` and
      every `x : ZMod (q₁q₂)`,
      `ψ(x) = ψ_{q₁}(u₁·x mod q₁) · ψ_{q₂}(u₂·x mod q₂)` — exact, all `x`.

  NUMERIC GROUNDING (wave-3 inline pre-pass): the factorization verified exactly
  (complex arithmetic, error < 1e−9) for `(q₁,q₂) = (3,5), (5,7), (4,9), (7,11)`,
  ALL residues `x` — including the non-prime, non-squarefree pair `(4,9)`: the
  cocycle needs coprimality only.

  DISCLOSURES (mandatory reading before quoting):
    * INFRASTRUCTURE ONLY — a per-`q` refactorization of the frequency language.
      The μ-SIGNS across moduli (the content of face E / LowFreqRootCoherence) are
      untouched by construction: rewriting each character exactly cannot create
      cancellation that was not already there.  NOT a §110 event; no registered
      target (CRE, SemiprimeShortRestriction, HigherConductorDispersion,
      LowFreqRootCoherence, OneWingTarget) is touched.
    * The intended downstream use (NOT claimed here): the two-frequency form of
      the semiprime remainder — `intervalWeight`/`rootFourier` objects at modulus
      `q₁q₂` rewritten through the `(q₁, q₂)` frequency pair, the dictionary in
      which face E's incommensurability becomes a literal two-variable statement.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

private instance neZero_mul_local {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] :
    NeZero (q₁ * q₂) :=
  ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩

/-- **THE COCYCLE INTEGER**: for coprime `q₁, q₂`, with `u₁ = (q₂ mod q₁)⁻¹` and
    `u₂ = (q₁ mod q₂)⁻¹` (values taken in `[0, qᵢ)`), the combination
    `u₁q₂ + u₂q₁ − 1` is divisible by `q₁q₂` — the partial-fraction decomposition
    `1/(q₁q₂) = u₁/q₁ + u₂/q₂ − e` closes with an integer `e`. -/
theorem crt_cocycle_dvd {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) :
    ((q₁ : ℤ) * q₂) ∣
      ((((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂ + (((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1) := by
  have h₁ : (q₁ : ℤ) ∣ ((((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂ - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_comm, ZMod.coe_mul_inv_eq_one q₂ hco.symm]
    ring
  have h₂ : (q₂ : ℤ) ∣ ((((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_comm, ZMod.coe_mul_inv_eq_one q₁ hco]
    ring
  have h₁' : (q₁ : ℤ) ∣
      ((((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂ + (((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1) := by
    have hsplit : (((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂
          + (((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1
        = ((((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂ - 1)
          + (((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ := by
      ring
    rw [hsplit]
    exact dvd_add h₁ ⟨(((q₁ : ZMod q₂)⁻¹.val : ℤ)), by ring⟩
  have h₂' : (q₂ : ℤ) ∣
      ((((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂ + (((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1) := by
    have hsplit : (((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂
          + (((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1
        = ((((q₁ : ZMod q₂)⁻¹.val : ℤ)) * q₁ - 1)
          + (((q₂ : ZMod q₁)⁻¹.val : ℤ)) * q₂ := by
      ring
    rw [hsplit]
    exact dvd_add h₂ ⟨(((q₂ : ZMod q₁)⁻¹.val : ℤ)), by ring⟩
  exact (Nat.Coprime.isCoprime hco).mul_dvd h₁' h₂'

/-- **THE CRT COCYCLE FACTORIZATION**: for coprime `q₁, q₂` and every
    `x : ZMod (q₁q₂)`, the standard character factors with unit twists:
    `ψ_{q₁q₂}(x) = ψ_{q₁}(q₂⁻¹·x) · ψ_{q₂}(q₁⁻¹·x)` (each factor at the reduced
    residue).  Exact for ALL `x`; coprimality is the only hypothesis. -/
theorem stdAddChar_crt_factor {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (x : ZMod (q₁ * q₂)) :
    ZMod.stdAddChar x
      = ZMod.stdAddChar
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
        * ZMod.stdAddChar
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x) := by
  have hq₁C : (q₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q₁)
  have hq₂C : (q₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q₂)
  -- the natural-number data
  set j : ℕ := x.val with hj
  set n₁ : ℕ := ((q₂ : ZMod q₁)⁻¹).val with hn₁
  set n₂ : ℕ := ((q₁ : ZMod q₂)⁻¹).val with hn₂
  -- rewrite all three characters as exponentials of ℤ-casts
  have hLHS : ZMod.stdAddChar x
      = Complex.exp (2 * Real.pi * Complex.I * (j : ℤ) / ((q₁ : ℕ) * q₂ : ℕ)) := by
    rw [← ZMod.natCast_zmod_val x, ← hj]
    rw [show ((j : ℕ) : ZMod (q₁ * q₂)) = ((j : ℤ) : ZMod (q₁ * q₂)) by push_cast; rfl]
    rw [ZMod.stdAddChar_coe]
  have hcast₁ : ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x = ((j : ℕ) : ZMod q₁) := by
    rw [← ZMod.natCast_zmod_val x, ← hj, map_natCast]
  have hcast₂ : ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x = ((j : ℕ) : ZMod q₂) := by
    rw [← ZMod.natCast_zmod_val x, ← hj, map_natCast]
  have hT₁ : ZMod.stdAddChar
      ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
      = Complex.exp (2 * Real.pi * Complex.I * ((n₁ * j : ℕ) : ℤ) / (q₁ : ℕ)) := by
    rw [hcast₁, ← ZMod.natCast_zmod_val ((q₂ : ZMod q₁)⁻¹), ← hn₁, ← Nat.cast_mul]
    rw [show ((n₁ * j : ℕ) : ZMod q₁) = (((n₁ * j : ℕ) : ℤ) : ZMod q₁) by push_cast; rfl]
    rw [ZMod.stdAddChar_coe]
  have hT₂ : ZMod.stdAddChar
      ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
      = Complex.exp (2 * Real.pi * Complex.I * ((n₂ * j : ℕ) : ℤ) / (q₂ : ℕ)) := by
    rw [hcast₂, ← ZMod.natCast_zmod_val ((q₁ : ZMod q₂)⁻¹), ← hn₂, ← Nat.cast_mul]
    rw [show ((n₂ * j : ℕ) : ZMod q₂) = (((n₂ * j : ℕ) : ℤ) : ZMod q₂) by push_cast; rfl]
    rw [ZMod.stdAddChar_coe]
  rw [hLHS, hT₁, hT₂, ← Complex.exp_add]
  -- the cocycle integer closes the exponent difference
  obtain ⟨e, he⟩ := crt_cocycle_dvd (q₁ := q₁) (q₂ := q₂) hco
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((j : ℤ) * e), ?_⟩
  have heC : ((n₁ : ℂ)) * q₂ + ((n₂ : ℂ)) * q₁ - 1 = ((q₁ : ℂ)) * q₂ * (e : ℤ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) he
  have hfrac : ((j : ℂ)) / ((q₁ : ℂ) * (q₂ : ℂ))
      = ((n₁ : ℂ)) * (j : ℂ) / (q₁ : ℂ) + ((n₂ : ℂ)) * (j : ℂ) / (q₂ : ℂ)
        - (j : ℂ) * (e : ℂ) := by
    field_simp
    linear_combination (-(j : ℂ)) * heC
  push_cast
  linear_combination (2 * Real.pi * Complex.I) * hfrac

/-! ### Axiom audit -/

#print axioms crt_cocycle_dvd
#print axioms stdAddChar_crt_factor

end TypeII
end Geometric
end EuclidsPath
