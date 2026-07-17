/-
  GeometricTypeIISalieCRT — SALIÉ'S 1932 MULTIPLICATIVITY, MACHINE-CHECKED:
  the twisted (Salié) sum with the JACOBI character factors through CRT with
  the cocycle twist on both frequency slots, and therefore the prime-line
  all-frequency Weil-strength bound propagates to semiprime moduli:

      ‖T_{ℓ₁ℓ₂}(a,b)‖ ≤ 4·√(ℓ₁ℓ₂)     (componentwise nondegenerate (a,b)).

  ORIGIN.  Autonomous continuation (wave 5e, the last composite-core brick):
  the χ-twisted port of the wave-5d Kloosterman factorization.  The correct
  composite character is the JACOBI symbol (`jacobiSym`, IN THE PIN with
  `mul_right` and `mod_left'`), which at odd primes is the Legendre symbol
  (`legendreSym.to_jacobiSym`) = the quadratic character of the wave-3 Salié
  module.  Numerical pre-pass (this session): the factorization verified at
  (5,7) over ALL 1225 frequency pairs, worst error 7.5e−15; the 4√q bound
  holds with 1.37× slack (max ‖T‖ = 17.25 vs 23.66) — the bound is SHARP-ish
  at semiprimes, unlike the fourth-moment routes.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `salieU` + `salieU_eq_salie` — the Jacobi-twisted sum on the unit
      domain; at odd primes it IS the wave-3 `salie` (the private quadratic
      character of that module is reached by definitional unfolding);
    * `salieU_crt_factor` — **THE 1932 FACTORIZATION**: for coprime ODD q₁,
      q₂, `T_{q₁q₂}(a,b) = T_{q₁}(u₁a₁, u₁b₁)·T_{q₂}(u₂a₂, u₂b₂)` — the
      Jacobi character splits WITHOUT a twist (`jacobiSym.mul_right`), the
      frequencies carry the partial-fraction cocycle units;
    * `salieU_norm_semiprime` — **THE HEADLINE**: `‖T‖ ≤ 4√q` at `q = ℓ₁ℓ₂`
      for ALL componentwise nondegenerate frequency pairs — a pointwise
      exponent-1/2 bound at a COMPOSITE modulus, no averaging.

  DISCLOSURES.
    * The exponent 1/2 is inherited from the prime-line `salie_norm_le`
      (classical Salié evaluation, elementary) — NOT from any Weil input;
      the pin has neither Weil nor Salié, both live in this repo.
    * ONE POLE with a χ-twist: the twin two-pole family does NOT reduce to
      Salié (wave-3 disclosure stands verbatim); the twin family keeps its
      almost-all Markov statement at every modulus (waves 5b/5c).
    * Componentwise nondegeneracy required on BOTH slots (the prime lemma
      needs `a ≠ 0` AND `b ≠ 0`); degenerate strata named, not claimed.
    * Unsigned complete sums, one composite modulus — composite-core
      infrastructure; the parity wall's faces are UNTOUCHED; NOT a §110
      event.  The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIITwinVarietyCRT
import EuclidsPath.Engine.GeometricTypeIISalie

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 1: the Jacobi-twisted sum on the unit domain -/

/-- **The unit Salié sum with the Jacobi character**:
`T_q(a,b) = Σ_{x unit} J(x|q)·ψ(ax + bx⁻¹)` — the correct twisted object off
the prime line (Jacobi = the CRT-compatible extension of Legendre). -/
noncomputable def salieU (q : ℕ) [NeZero q] (a b : ZMod q) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : ZMod q => x * x⁻¹ = 1),
    ((jacobiSym (x.val : ℤ) q : ℤ) : ℂ) * ZMod.stdAddChar (a * x + b * x⁻¹)

theorem salieU_apply {q : ℕ} [NeZero q] (a b : ZMod q) :
    salieU q a b
      = ∑ x ∈ Finset.univ.filter (fun x : ZMod q => x * x⁻¹ = 1),
          ((jacobiSym (x.val : ℤ) q : ℤ) : ℂ)
            * ZMod.stdAddChar (a * x + b * x⁻¹) := rfl

/-- At odd primes the Jacobi character IS the quadratic character (pointwise,
through `legendreSym.to_jacobiSym` and the definitional unfolding of
`legendreSym`). -/
private theorem jacobi_char_eq_quadratic {ℓ : ℕ} [Fact ℓ.Prime] (x : ZMod ℓ) :
    ((jacobiSym (x.val : ℤ) ℓ : ℤ) : ℂ)
      = (Int.castRingHom ℂ) (quadraticChar (ZMod ℓ) x) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  unfold legendreSym
  have hcast : (((x.val : ℕ) : ℤ) : ZMod ℓ) = x := by
    push_cast
    exact ZMod.natCast_rightInverse x
  rw [hcast]
  rfl

/-- At primes the unit Jacobi-twisted sum IS the wave-3 `salie` (total
reuse; the private character of that module is reached definitionally). -/
theorem salieU_eq_salie {ℓ : ℕ} [Fact ℓ.Prime] (a b : ZMod ℓ) :
    salieU ℓ a b = salie a b := by
  show salieU ℓ a b
    = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
        (quadraticChar (ZMod ℓ)).ringHomComp (Int.castRingHom ℂ) x
          * ZMod.stdAddChar (a * x + b * x⁻¹)
  rw [salieU_apply]
  rw [show Finset.univ.filter (fun x : ZMod ℓ => x * x⁻¹ = 1)
      = Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0) by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h hx0
      rw [hx0, zero_mul] at h
      exact zero_ne_one h
    · intro hx0
      exact ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hx0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [jacobi_char_eq_quadratic, MulChar.ringHomComp_apply]

/-! ### Layer 2: THE 1932 FACTORIZATION -/

/-- The Jacobi character is CRT-componentwise (no twist on the character
slot): `J(x|q₁q₂) = J(x₁|q₁)·J(x₂|q₂)`. -/
private theorem jacobi_crt_split {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (x : ZMod (q₁ * q₂)) :
    ((jacobiSym (x.val : ℤ) (q₁ * q₂) : ℤ) : ℂ)
      = ((jacobiSym (((ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁)) x).val : ℤ)
            q₁ : ℤ) : ℂ)
        * ((jacobiSym (((ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)) x).val : ℤ)
            q₂ : ℤ) : ℂ) := by
  have hx : ((x.val : ℕ) : ZMod (q₁ * q₂)) = x := ZMod.natCast_rightInverse x
  have hc₁ : (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁)) x
      = ((x.val : ℕ) : ZMod q₁) := by
    rw [← hx, map_natCast, hx]
  have hc₂ : (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)) x
      = ((x.val : ℕ) : ZMod q₂) := by
    rw [← hx, map_natCast, hx]
  have hv₁ : ((ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁)) x).val
      = x.val % q₁ := by
    rw [hc₁, ZMod.val_natCast]
  have hv₂ : ((ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)) x).val
      = x.val % q₂ := by
    rw [hc₂, ZMod.val_natCast]
  have hm₁ : jacobiSym ((((ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁)) x).val
      : ℕ) : ℤ) q₁ = jacobiSym (x.val : ℤ) q₁ := by
    refine jacobiSym.mod_left' ?_
    rw [hv₁]
    push_cast
    exact Int.emod_emod_of_dvd _ dvd_rfl
  have hm₂ : jacobiSym ((((ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)) x).val
      : ℕ) : ℤ) q₂ = jacobiSym (x.val : ℤ) q₂ := by
    refine jacobiSym.mod_left' ?_
    rw [hv₂]
    push_cast
    exact Int.emod_emod_of_dvd _ dvd_rfl
  rw [hm₁, hm₂, jacobiSym.mul_right, Int.cast_mul]

/-- **Salié's multiplicativity** (Salié 1932): over coprime moduli the
Jacobi-twisted sum factors — the character splits without a twist, the
frequencies carry the partial-fraction cocycle units.  (Numerically verified
at (5,7) over all 1225 pairs, worst error 7.5e−15.) -/
theorem salieU_crt_factor {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (a b : ZMod (q₁ * q₂)) :
    salieU (q₁ * q₂) a b
      = salieU q₁
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a)
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b)
        * salieU q₂
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a)
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b) := by
  classical
  set f₁ : ZMod q₁ → ℂ := fun t =>
    if t * t⁻¹ = 1
    then ((jacobiSym (t.val : ℤ) q₁ : ℤ) : ℂ) * ZMod.stdAddChar
      (((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a) * t
        + ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b) * t⁻¹)
    else 0 with hf₁
  set f₂ : ZMod q₂ → ℂ := fun t =>
    if t * t⁻¹ = 1
    then ((jacobiSym (t.val : ℤ) q₂ : ℤ) : ℂ) * ZMod.stdAddChar
      (((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a) * t
        + ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b) * t⁻¹)
    else 0 with hf₂
  have hLHS : salieU (q₁ * q₂) a b
      = ∑ x : ZMod (q₁ * q₂),
          f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
            * f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x) := by
    have hfold : salieU (q₁ * q₂) a b
        = ∑ x : ZMod (q₁ * q₂),
            (if x * x⁻¹ = 1
              then ((jacobiSym (x.val : ℤ) (q₁ * q₂) : ℤ) : ℂ)
                * ZMod.stdAddChar (a * x + b * x⁻¹) else 0) := by
      rw [salieU_apply, ← Finset.sum_filter]
    rw [hfold]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : IsUnit x
    · have hx1 : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ hx
      obtain ⟨hxu1, hxu2⟩ := (isUnit_crt_iff hco x).mp hx
      rw [if_pos hx1, hf₁, hf₂]
      show ((jacobiSym (x.val : ℤ) (q₁ * q₂) : ℤ) : ℂ)
          * ZMod.stdAddChar (a * x + b * x⁻¹)
        = (if _ * _⁻¹ = 1 then _ else 0) * (if _ * _⁻¹ = 1 then _ else 0)
      rw [if_pos (ZMod.mul_inv_of_unit _ hxu1), if_pos (ZMod.mul_inv_of_unit _ hxu2)]
      rw [jacobi_crt_split x,
        stdAddChar_crt_factor hco (a * x + b * x⁻¹)]
      have hψ₁ : ZMod.stdAddChar
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁)
            (a * x + b * x⁻¹))
          = ZMod.stdAddChar
            (((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a)
                * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x
              + ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b)
                * (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)⁻¹) := by
        congr 1
        rw [map_add, map_mul, map_mul, castHom_inv_of_isUnit _ hx]
        ring
      have hψ₂ : ZMod.stdAddChar
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)
            (a * x + b * x⁻¹))
          = ZMod.stdAddChar
            (((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a)
                * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x
              + ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b)
                * (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)⁻¹) := by
        congr 1
        rw [map_add, map_mul, map_mul, castHom_inv_of_isUnit _ hx]
        ring
      rw [hψ₁, hψ₂]
      ring
    · have hx1 : ¬(x * x⁻¹ = 1) := fun h => hx (IsUnit.of_mul_eq_one _ h)
      rw [if_neg hx1]
      rcases (not_and_or.mp (fun hboth => hx ((isUnit_crt_iff hco x).mpr hboth)))
        with h | h
      · rw [hf₁]
        show (0 : ℂ)
          = (if _ * _⁻¹ = 1 then _ else 0) * f₂ (ZMod.castHom _ (ZMod q₂) x)
        rw [if_neg (fun hc => h (IsUnit.of_mul_eq_one _ hc)), zero_mul]
      · rw [hf₂]
        show (0 : ℂ)
          = f₁ (ZMod.castHom _ (ZMod q₁) x) * (if _ * _⁻¹ = 1 then _ else 0)
        rw [if_neg (fun hc => h (IsUnit.of_mul_eq_one _ hc)), mul_zero]
  rw [hLHS, SegreFarey.crt_sum_factor hco f₁ f₂]
  congr 1
  · simp only [hf₁]
    rw [← Finset.sum_filter, salieU_apply]
  · simp only [hf₂]
    rw [← Finset.sum_filter, salieU_apply]

/-! ### Layer 3: THE SEMIPRIME HEADLINE -/

/-- **The all-frequency exponent-1/2 bound at semiprime moduli**: for
componentwise nondegenerate `(a,b)`,
`‖T_{ℓ₁ℓ₂}(a,b)‖ ≤ 4·√(ℓ₁ℓ₂)` — the prime-line classical Salié evaluation
per component through the 1932 factorization; pointwise, no averaging. -/
theorem salieU_norm_semiprime {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) {a b : ZMod (ℓ₁ * ℓ₂)}
    (ha₁ : ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) a ≠ 0)
    (hb₁ : ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) b ≠ 0)
    (ha₂ : ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) a ≠ 0)
    (hb₂ : ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) b ≠ 0) :
    ‖salieU (ℓ₁ * ℓ₂) a b‖ ≤ 4 * Real.sqrt ((ℓ₁ : ℝ) * ℓ₂) := by
  have hco : Nat.Coprime ℓ₁ ℓ₂ :=
    (Nat.coprime_primes Fact.out Fact.out).mpr hne
  have hq₂u : IsUnit ((ℓ₂ : ℕ) : ZMod ℓ₁) :=
    (ZMod.isUnit_iff_coprime ℓ₂ ℓ₁).mpr hco.symm
  have hq₁u : IsUnit ((ℓ₁ : ℕ) : ZMod ℓ₂) :=
    (ZMod.isUnit_iff_coprime ℓ₁ ℓ₂).mpr hco
  have hu₁ : ((ℓ₂ : ZMod ℓ₁))⁻¹ ≠ 0 := inv_ne_zero (IsUnit.ne_zero hq₂u)
  have hu₂ : ((ℓ₁ : ZMod ℓ₂))⁻¹ ≠ 0 := inv_ne_zero (IsUnit.ne_zero hq₁u)
  rw [salieU_crt_factor hco a b, norm_mul, salieU_eq_salie, salieU_eq_salie]
  have k₁ := salie_norm_le h₁ (mul_ne_zero hu₁ ha₁) (mul_ne_zero hu₁ hb₁)
  have k₂ := salie_norm_le h₂ (mul_ne_zero hu₂ ha₂) (mul_ne_zero hu₂ hb₂)
  calc ‖salie ((ℓ₂ : ZMod ℓ₁)⁻¹ * ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) a)
          ((ℓ₂ : ZMod ℓ₁)⁻¹ * ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) b)‖
        * ‖salie ((ℓ₁ : ZMod ℓ₂)⁻¹ * ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) a)
            ((ℓ₁ : ZMod ℓ₂)⁻¹ * ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) b)‖
      ≤ (2 * Real.sqrt ℓ₁) * (2 * Real.sqrt ℓ₂) :=
        mul_le_mul k₁ k₂ (norm_nonneg _) (by positivity)
    _ = 4 * (Real.sqrt ℓ₁ * Real.sqrt ℓ₂) := by ring
    _ = 4 * Real.sqrt ((ℓ₁ : ℝ) * ℓ₂) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg ℓ₁)]

end TypeII
end Geometric
end EuclidsPath
