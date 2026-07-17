/-
  GeometricTypeIIKloostermanCRT — KLOOSTERMAN'S 1926 MULTIPLICATIVITY,
  MACHINE-CHECKED: the classical Kloosterman sum over the UNIT domain factors
  through CRT with the cocycle twist on both frequency slots, and therefore
  the repo's fourth-moment pointwise bound propagates off the prime line:

      ‖Kl_{ℓ₁ℓ₂}(a,b)‖⁴ ≤ 4·(ℓ₁ℓ₂)³   (componentwise nondegenerate (a,b)),
      ‖Kl_{ℓ₁ℓ₂}(a,b)‖  ≤ √2·(ℓ₁ℓ₂)^{3/4}.

  ORIGIN.  Autonomous continuation (wave 5d): the one-pole port of the
  wave-5a cocycle factorization — strictly simpler than `twinVU_crt_factor`
  (ONE pole instead of two, no shifted-domain bookkeeping).  Kloosterman's
  multiplicativity (Kloosterman 1926, Salié 1932) is CLASSICAL; the pin
  contains no Kloosterman sums at all (the repo's `kloos` is already new to
  the pin at primes).  Numerical pre-pass (this session): the factorization
  verified at (5,7) over ALL 1225 frequency pairs, worst error 1.1e−14; the
  nondegenerate fourth-power bound holds with 3.8× slack.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `kloosU` + `kloosU_eq_kloos` — the unit-domain Kloosterman sum; at
      primes it IS the repo's `kloos` (total reuse);
    * `kloosU_crt_factor` — **THE 1926 FACTORIZATION**: for coprime q₁, q₂,
      `Kl_{q₁q₂}(a,b) = Kl_{q₁}(u₁a₁, u₁b₁)·Kl_{q₂}(u₂a₂, u₂b₂)` with the
      partial-fraction cocycle units u₁ = q₂⁻¹ mod q₁, u₂ = q₁⁻¹ mod q₂;
    * `kloosU_norm_semiprime` — the fourth-power pointwise bound above (the
      prime-line `kloos_norm_le` per component, constant 2 → 4);
    * `kloosU_norm_semiprime_rpow` — the √2·q^{3/4} headline form.

  DISCLOSURES.
    * The 3/4 exponent is the FOURTH-MOMENT exponent, not Weil's 1/2 — same
      honesty as the prime line (`kloos_norm_le` disclosure stands: the pin
      has no Weil bound and none is claimed).
    * The hypotheses require BOTH frequencies nonzero mod BOTH factors; the
      degenerate strata behave differently (e.g. `Kl(0,0) mod ℓ = ℓ−1`) and
      are NOT bounded here — named, not claimed.
    * Unsigned, single (composite) modulus, complete sums — infrastructure
      on the composite-modulus core; the parity wall's faces are UNTOUCHED;
      NOT a §110 event.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIITwinVarietyCRT
import EuclidsPath.Engine.Step00CircleEnergy
import EuclidsPath.Engine.Step00KloostermanMoment

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open EuclidsPath.CircleEnergy EuclidsPath.KloostermanMoment

/-! ### Layer 1: the unit-domain Kloosterman sum -/

/-- **The unit Kloosterman sum**: `Kl_q(a,b) = Σ_{x unit} ψ(ax + bx⁻¹)` — the
correct domain off the prime line (wave-5a lesson: `x ≠ 0` is not
CRT-componentwise, units are). -/
noncomputable def kloosU (q : ℕ) [NeZero q] (a b : ZMod q) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : ZMod q => x * x⁻¹ = 1),
    ZMod.stdAddChar (a * x + b * x⁻¹)

theorem kloosU_apply {q : ℕ} [NeZero q] (a b : ZMod q) :
    kloosU q a b
      = ∑ x ∈ Finset.univ.filter (fun x : ZMod q => x * x⁻¹ = 1),
          ZMod.stdAddChar (a * x + b * x⁻¹) := rfl

private theorem mem_kloosDomU {q : ℕ} [NeZero q] {x : ZMod q} :
    x ∈ Finset.univ.filter (fun x : ZMod q => x * x⁻¹ = 1) ↔ IsUnit x := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => IsUnit.of_mul_eq_one _ h
  · exact fun h => ZMod.mul_inv_of_unit _ h

/-- At primes the unit Kloosterman sum IS the repo's `kloos` (total reuse). -/
theorem kloosU_eq_kloos {ℓ : ℕ} [Fact ℓ.Prime] (a b : ZMod ℓ) :
    kloosU ℓ a b = kloos a b := by
  rw [kloosU_apply, kloos_def]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h hx0
    rw [hx0, zero_mul] at h
    exact zero_ne_one h
  · intro hx0
    exact ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hx0)

/-! ### Layer 2: THE 1926 FACTORIZATION -/

/-- **Kloosterman's multiplicativity** (Kloosterman 1926): over coprime
moduli the unit Kloosterman sum factors with the partial-fraction cocycle
units on both frequency slots.  (Numerically verified at (5,7) over all
1225 pairs, worst error 1.1e−14.) -/
theorem kloosU_crt_factor {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (a b : ZMod (q₁ * q₂)) :
    kloosU (q₁ * q₂) a b
      = kloosU q₁
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a)
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b)
        * kloosU q₂
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a)
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b) := by
  classical
  set f₁ : ZMod q₁ → ℂ := fun t =>
    if t * t⁻¹ = 1
    then ZMod.stdAddChar
      (((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a) * t
        + ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b) * t⁻¹)
    else 0 with hf₁
  set f₂ : ZMod q₂ → ℂ := fun t =>
    if t * t⁻¹ = 1
    then ZMod.stdAddChar
      (((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a) * t
        + ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b) * t⁻¹)
    else 0 with hf₂
  have hLHS : kloosU (q₁ * q₂) a b
      = ∑ x : ZMod (q₁ * q₂),
          f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
            * f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x) := by
    have hfold : kloosU (q₁ * q₂) a b
        = ∑ x : ZMod (q₁ * q₂),
            (if x * x⁻¹ = 1
              then ZMod.stdAddChar (a * x + b * x⁻¹) else 0) := by
      rw [kloosU_apply, ← Finset.sum_filter]
    rw [hfold]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : IsUnit x
    · have hx1 : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ hx
      obtain ⟨hxu1, hxu2⟩ := (isUnit_crt_iff hco x).mp hx
      rw [if_pos hx1, hf₁, hf₂]
      show ZMod.stdAddChar (a * x + b * x⁻¹)
        = (if _ * _⁻¹ = 1 then _ else 0) * (if _ * _⁻¹ = 1 then _ else 0)
      rw [if_pos (ZMod.mul_inv_of_unit _ hxu1), if_pos (ZMod.mul_inv_of_unit _ hxu2)]
      rw [stdAddChar_crt_factor hco (a * x + b * x⁻¹)]
      congr 1
      · congr 1
        rw [map_add, map_mul, map_mul, castHom_inv_of_isUnit _ hx]
        ring
      · congr 1
        rw [map_add, map_mul, map_mul, castHom_inv_of_isUnit _ hx]
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
    rw [← Finset.sum_filter, kloosU_apply]
  · simp only [hf₂]
    rw [← Finset.sum_filter, kloosU_apply]

/-! ### Layer 3: the semiprime pointwise bound -/

/-- **The fourth-power pointwise bound at semiprime moduli**: for
componentwise nondegenerate `(a,b)`,
`‖Kl_{ℓ₁ℓ₂}(a,b)‖⁴ ≤ 4·(ℓ₁ℓ₂)³` — the prime-line fourth-moment bound
(`kloos_norm_le`) per component through the 1926 factorization. -/
theorem kloosU_norm_semiprime {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) {a b : ZMod (ℓ₁ * ℓ₂)}
    (ha₁ : ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) a ≠ 0)
    (hb₁ : ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) b ≠ 0)
    (ha₂ : ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) a ≠ 0)
    (hb₂ : ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) b ≠ 0) :
    ‖kloosU (ℓ₁ * ℓ₂) a b‖ ^ 4 ≤ 4 * ((ℓ₁ : ℝ) * ℓ₂) ^ 3 := by
  have hco : Nat.Coprime ℓ₁ ℓ₂ :=
    (Nat.coprime_primes Fact.out Fact.out).mpr hne
  -- the cocycle units are nonzero in the component fields
  have hq₂u : IsUnit ((ℓ₂ : ℕ) : ZMod ℓ₁) :=
    (ZMod.isUnit_iff_coprime ℓ₂ ℓ₁).mpr hco.symm
  have hq₁u : IsUnit ((ℓ₁ : ℕ) : ZMod ℓ₂) :=
    (ZMod.isUnit_iff_coprime ℓ₁ ℓ₂).mpr hco
  have hu₁ : ((ℓ₂ : ZMod ℓ₁))⁻¹ ≠ 0 :=
    inv_ne_zero (IsUnit.ne_zero hq₂u)
  have hu₂ : ((ℓ₁ : ZMod ℓ₂))⁻¹ ≠ 0 :=
    inv_ne_zero (IsUnit.ne_zero hq₁u)
  rw [kloosU_crt_factor hco a b, norm_mul, mul_pow,
    kloosU_eq_kloos, kloosU_eq_kloos]
  have k₁ := kloos_norm_le h₁ (mul_ne_zero hu₁ ha₁) (mul_ne_zero hu₁ hb₁)
  have k₂ := kloos_norm_le h₂ (mul_ne_zero hu₂ ha₂) (mul_ne_zero hu₂ hb₂)
  calc ‖kloos ((ℓ₂ : ZMod ℓ₁)⁻¹ * ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) a)
          ((ℓ₂ : ZMod ℓ₁)⁻¹ * ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) b)‖ ^ 4
        * ‖kloos ((ℓ₁ : ZMod ℓ₂)⁻¹ * ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) a)
            ((ℓ₁ : ZMod ℓ₂)⁻¹ * ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) b)‖ ^ 4
      ≤ (2 * (ℓ₁ : ℝ) ^ 3) * (2 * (ℓ₂ : ℝ) ^ 3) :=
        mul_le_mul k₁ k₂ (by positivity) (by positivity)
    _ = 4 * ((ℓ₁ : ℝ) * ℓ₂) ^ 3 := by ring

/-- **The √2·q^{3/4} headline form** (fourth-root extraction; the 3/4 is the
fourth-moment exponent, not Weil's 1/2 — same honesty as the prime line). -/
theorem kloosU_norm_semiprime_rpow {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) {a b : ZMod (ℓ₁ * ℓ₂)}
    (ha₁ : ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) a ≠ 0)
    (hb₁ : ZMod.castHom (dvd_mul_right ℓ₁ ℓ₂) (ZMod ℓ₁) b ≠ 0)
    (ha₂ : ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) a ≠ 0)
    (hb₂ : ZMod.castHom (dvd_mul_left ℓ₂ ℓ₁) (ZMod ℓ₂) b ≠ 0) :
    ‖kloosU (ℓ₁ * ℓ₂) a b‖
      ≤ Real.sqrt 2 * ((ℓ₁ : ℝ) * ℓ₂) ^ ((3 : ℝ) / 4) := by
  have h4 := kloosU_norm_semiprime h₁ h₂ hne ha₁ hb₁ ha₂ hb₂
  set x := ‖kloosU (ℓ₁ * ℓ₂) a b‖ with hx_def
  have hx : (0 : ℝ) ≤ x := norm_nonneg _
  have hq0 : (0 : ℝ) ≤ (ℓ₁ : ℝ) * ℓ₂ := by positivity
  have hx4 : (0 : ℝ) ≤ x ^ 4 := by positivity
  have h1 : x = (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast x 4, ← Real.rpow_mul hx,
      show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
  rw [h1]
  calc (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 4)
      ≤ (4 * ((ℓ₁ : ℝ) * ℓ₂) ^ 3) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hx4 h4 (by norm_num)
    _ = Real.sqrt 2 * ((ℓ₁ : ℝ) * ℓ₂) ^ ((3 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_natCast ((ℓ₁ : ℝ) * ℓ₂) 3, ← Real.rpow_mul hq0,
          show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 4) = (3 : ℝ) / 4 by norm_num]
        congr 1
        rw [Real.sqrt_eq_rpow]
        have h42 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
          have h : (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by
            rw [← Real.rpow_natCast (2 : ℝ) 2]
            norm_num
          rw [h]
          norm_num
        rw [h42, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num

end TypeII
end Geometric
end EuclidsPath
