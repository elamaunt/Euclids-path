/-
  GeometricSegreFarey — the SEGRE×CRT FLAT-MODE ANNIHILATION: over the COMPLETE
  semiprime period `q₁q₂`, the exterior (Segre/connected) energy of any
  purely-left field against any purely-right field is EXACTLY ZERO —

      Σ_{x,y mod q₁q₂} (f₁(x₁) − f₁(y₁))·(f₂(x₂) − f₂(y₂)) = 0

  — by a COLLECTIVE cancellation (individually nonzero terms), because the two
  CRT coordinate directions are exactly independent over the full period.  The
  two fields ARE the flat modes of the two-frequency frame (each constant along
  the complementary CRT direction): the complete CRT frame sits ON the Segre
  quadric, and the connected defect of the flat sector is annihilated
  identically.

  ORIGIN.  Idea-generation session continuation (the wave-3 plan's Segre–Farey
  brick, REDESIGNED by the wave-4 pre-pass).  The literal panel statement
  ("exterior energy kills constant fields") is a TRIVIALITY (termwise-zero,
  already prose-recorded at `exterior_algebra_identity`; kept here only as the
  flagged display lemma `segre_flat_tangent`) — the pre-pass replaced it with
  the contentful theorem above, verified numerically: at `(q₁,q₂) = (5,7)` the
  energy vanishes to `2.4·10⁻¹³` while 840 of 1225 terms are individually
  nonzero; the non-squarefree pair `(4,9)` included (coprimality is the only
  hypothesis).  This is the exact structural sibling of the house criterion-A
  precedent `root_remainder_full_period`: COMPLETE period ⟹ exact kill.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `crt_sum_factor` — **THE FUBINI HEART**: for coprime `q₁, q₂`,
      `Σ_{x mod q₁q₂} f₁(x₁)f₂(x₂) = (Σ f₁)(Σ f₂)` (CRT reindex; the pin has no
      such lemma — checked);
    * `crt_sum_marginal_left/right` — the flat-field marginals `q₂·Σf₁`, `q₁·Σf₂`;
    * `exterior_energy_kills_flat_modes` — **THE ANNIHILATION** displayed above,
      through the house `Segre.exterior_algebra_identity`;
    * `two_freq_orthogonal` — the Fourier slice: over the complete period,
      `Σ_x ψ₁(h₁x₁)ψ₂(h₂x₂) = q₁[h₁=0]·q₂[h₂=0]` — ONLY the doubly-flat mode
      `(0,0)` survives; every flat pair `(h₁,0)`, `(0,h₂)` and every mixed pair
      dies.  The dictionary partner of `stdAddChar_crt_factor`
      (GeometricTypeIICocycle): together they say the semiprime frequency line
      factors exactly and its two factors are exactly orthogonal — at FULL
      period;
    * `segre_flat_tangent` — the trivial constant-field tangency (display only,
      flagged: zero map value beyond the `exterior_algebra_identity` docstring).

  DISCLOSURES (mandatory reading before quoting):
    * COMPLETE PERIOD ONLY — the short-window version is FALSE: the pre-pass
      measured the window-truncated connected defect at `(5,7)` as `−2, −6, −12`
      for `M = 12, 16, 23` (vs exactly `0` at `M = 35`).  That nonzero
      short-window defect IS the wall's face E (`LowFreqRootCoherence`): this
      module CONFINES the open content to the incommensurable short window —
      it does not reduce it (same disclosure pattern as
      `root_remainder_full_period`).
    * NOT a §110 event; no registered target (CRE, SemiprimeShortRestriction,
      HigherConductorDispersion, LowFreqRootCoherence, OneWingTarget) is
      touched, bounded, or reduced.  Infrastructure/visibility for face E.
    * The two-row exterior energy of the ROW frame is deliberately NOT recorded
      here — it is an invertible rescaling of `two_row_cov`
      (GeometricTypeIIProjection) and would be double-counting.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricSegreDefect
import EuclidsPath.Engine.Step00CircleVolume

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace SegreFarey

open scoped BigOperators

private instance neZero_mul_local {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] :
    NeZero (q₁ * q₂) :=
  ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩

/-! ### The Fubini heart -/

/-- **CRT Fubini**: over the complete semiprime period, a product of a
    purely-left and a purely-right field sums to the product of the marginals —
    the two CRT directions are exactly independent. -/
theorem crt_sum_factor {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) {R : Type*} [CommRing R]
    (f₁ : ZMod q₁ → R) (f₂ : ZMod q₂ → R) :
    ∑ x : ZMod (q₁ * q₂),
      f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
        * f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
      = (∑ a : ZMod q₁, f₁ a) * (∑ b : ZMod q₂, f₂ b) := by
  have hrw : ∀ x : ZMod (q₁ * q₂),
      f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
        * f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
      = (fun ab : ZMod q₁ × ZMod q₂ => f₁ ab.1 * f₂ ab.2)
          ((ZMod.chineseRemainder hco).toEquiv x) := by
    intro x
    show _ = f₁ (ZMod.chineseRemainder hco x).1
      * f₂ (ZMod.chineseRemainder hco x).2
    rw [CircleVolume.chineseRemainder_fst hco x,
      CircleVolume.chineseRemainder_snd hco x]
  rw [Finset.sum_congr rfl fun x _ => hrw x]
  rw [Equiv.sum_comp ((ZMod.chineseRemainder hco).toEquiv)
    (fun ab : ZMod q₁ × ZMod q₂ => f₁ ab.1 * f₂ ab.2)]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum]

/-- The purely-left flat marginal: `Σ_x f₁(x₁) = q₂·Σ f₁`. -/
theorem crt_sum_marginal_left {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) {R : Type*} [CommRing R] (f₁ : ZMod q₁ → R) :
    ∑ x : ZMod (q₁ * q₂),
      f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
      = (q₂ : R) * ∑ a : ZMod q₁, f₁ a := by
  have h := crt_sum_factor hco f₁ (fun _ => (1 : R))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at h
  rw [h]
  ring

/-- The purely-right flat marginal: `Σ_x f₂(x₂) = q₁·Σ f₂`. -/
theorem crt_sum_marginal_right {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) {R : Type*} [CommRing R] (f₂ : ZMod q₂ → R) :
    ∑ x : ZMod (q₁ * q₂),
      f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
      = (q₁ : R) * ∑ b : ZMod q₂, f₂ b := by
  have h := crt_sum_factor hco (fun _ => (1 : R)) f₂
  simp only [one_mul, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at h
  rw [h]
  ring

/-! ### The annihilation -/

/-- **THE SEGRE×CRT FLAT-MODE ANNIHILATION**: over the complete semiprime
    period, the exterior energy of a purely-left field against a purely-right
    field is EXACTLY zero — a collective cancellation (individually nonzero
    terms), the complete CRT frame sitting on the Segre quadric. -/
theorem exterior_energy_kills_flat_modes {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) {R : Type*} [CommRing R]
    (f₁ : ZMod q₁ → R) (f₂ : ZMod q₂ → R) :
    ∑ x : ZMod (q₁ * q₂), ∑ y : ZMod (q₁ * q₂),
      (f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
          - f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) y))
        * (f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
          - f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) y)) = 0 := by
  have hid := Segre.exterior_algebra_identity (R := R)
    (Finset.univ : Finset (ZMod (q₁ * q₂))) (fun _ => (1 : R))
    (fun x => f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x))
    (fun x => f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x))
  have hRHS : ∑ x : ZMod (q₁ * q₂), ∑ y : ZMod (q₁ * q₂),
      (f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
          - f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) y))
        * (f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
          - f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) y))
      = ∑ x : ZMod (q₁ * q₂), ∑ y : ZMod (q₁ * q₂),
        (1 : R) * 1
          * (f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
            - f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) y))
          * (f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
            - f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) y)) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hRHS, ← hid]
  -- the connected bracket vanishes: A·S = M₋·M₊ by Fubini and the marginals
  have hA : ∑ _k : ZMod (q₁ * q₂), (1 : R) = ((q₁ * q₂ : ℕ) : R) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  have hS : ∑ k : ZMod (q₁ * q₂),
      (1 : R) * f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) k)
        * f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) k)
      = (∑ a : ZMod q₁, f₁ a) * (∑ b : ZMod q₂, f₂ b) := by
    rw [← crt_sum_factor hco f₁ f₂]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hM₁ : ∑ k : ZMod (q₁ * q₂),
      (1 : R) * f₁ (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) k)
      = (q₂ : R) * ∑ a : ZMod q₁, f₁ a := by
    rw [← crt_sum_marginal_left hco f₁]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hM₂ : ∑ k : ZMod (q₁ * q₂),
      (1 : R) * f₂ (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) k)
      = (q₁ : R) * ∑ b : ZMod q₂, f₂ b := by
    rw [← crt_sum_marginal_right hco f₂]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hA, hS, hM₁, hM₂]
  push_cast
  ring

/-! ### The Fourier slice -/

/-- Full-line orthogonality at any modulus (local copy of the house collapse). -/
private theorem char_sum_collapse {q : ℕ} [NeZero q] (t : ZMod q) :
    ∑ a : ZMod q, ZMod.stdAddChar (t * a) = if t = 0 then (q : ℂ) else 0 := by
  have hcomm : ∀ a : ZMod q,
      ZMod.stdAddChar (t * a) = ZMod.stdAddChar (a * t) := by
    intro a
    rw [mul_comm]
  rw [Finset.sum_congr rfl fun a _ => hcomm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card,
    Nat.cast_ite, Nat.cast_zero]

/-- **The two-frequency orthogonality at full period**: only the doubly-flat
    mode `(0,0)` survives — every flat pair `(h₁,0)`, `(0,h₂)` and every mixed
    pair dies.  The dictionary partner of `stdAddChar_crt_factor`. -/
theorem two_freq_orthogonal {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (h₁ : ZMod q₁) (h₂ : ZMod q₂) :
    ∑ x : ZMod (q₁ * q₂),
      ZMod.stdAddChar (h₁ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
        * ZMod.stdAddChar (h₂ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x)
      = (if h₁ = 0 then (q₁ : ℂ) else 0) * (if h₂ = 0 then (q₂ : ℂ) else 0) := by
  rw [crt_sum_factor hco (fun a => ZMod.stdAddChar (h₁ * a))
    (fun b => ZMod.stdAddChar (h₂ * b))]
  rw [char_sum_collapse, char_sum_collapse]

/-! ### The display lemma (flagged trivial) -/

/-- DISPLAY ONLY (termwise-trivial, zero map value — recorded solely to close
    the `exterior_algebra_identity` docstring's tangency claim as a machine
    statement): a CONSTANT field is tangent to the Segre quadric. -/
theorem segre_flat_tangent {ι R : Type*} [CommRing R] (s : Finset ι)
    (w x : ι → R) (c : R) :
    (∑ k ∈ s, w k) * (∑ k ∈ s, w k * x k * c)
      - (∑ k ∈ s, w k * x k) * (∑ k ∈ s, w k * c) = 0 := by
  have h1 : ∑ k ∈ s, w k * x k * c = (∑ k ∈ s, w k * x k) * c := by
    rw [Finset.sum_mul]
  have h2 : ∑ k ∈ s, w k * c = (∑ k ∈ s, w k) * c := by
    rw [Finset.sum_mul]
  rw [h1, h2]
  ring

/-! ### Axiom audit -/

#print axioms crt_sum_factor
#print axioms crt_sum_marginal_left
#print axioms crt_sum_marginal_right
#print axioms exterior_energy_kills_flat_modes
#print axioms two_freq_orthogonal
#print axioms segre_flat_tangent

end SegreFarey
end Geometric
end EuclidsPath
