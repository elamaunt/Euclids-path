/-
  GeometricTypeIITwinVarietyCRT — the twin variety on COMPOSITE (squarefree)
  moduli: the unit-domain twin family `twinVU` factors under CRT with unit
  twists, and its family fourth moment is MULTIPLICATIVE —

      twinVU_{q₁q₂}(a,b₁,b₂)
        = twinVU_{q₁}(u₁a₁, u₁b₁₁, u₁b₂₁) · twinVU_{q₂}(u₂a₂, u₂b₁₂, u₂b₂₂),
      M4U(q₁q₂) = M4U(q₁)·M4U(q₂),   M4U(ℓ₁ℓ₂) = (ℓ₁ℓ₂)³·∏ᵢ(ℓᵢ−2)(2ℓᵢ−5)

  — extending the complete-sum core from prime to squarefree moduli: the
  frequency dictionary in which the wall's composite-modulus faces speak.

  ORIGIN.  Autonomous continuation (wave 5, idea a).  Design adversarially
  verified with a decisive REFUTATION adopted: the naive extension (keep the
  domain `x ≠ 0 ∧ x+2 ≠ 0` with ZMod's junk inverses) is FALSE — at `q = 35`
  the naive domain has 33 points against `15 = (5−2)(7−2)`, the zero-frequency
  value `33 ≠ 15` kills ANY unit-twisted factorization (twists fix 0), and all
  42 875 frequency triples violate it numerically.  The honest composite domain
  is the UNIT domain `twinDomU q = {x : IsUnit x ∧ IsUnit (x+2)}`; with it the
  twisted factorization is exact (verified to `6.5·10⁻¹⁵` at `(5,7)` and
  `2.0·10⁻¹⁴` at `(5,11)`, ALL triples), `u₁ = (q₂ mod q₁)⁻¹`,
  `u₂ = (q₁ mod q₂)⁻¹` — the SAME twist on all three frequency slots, NO twist
  on the domain variable.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twinDomU` + `mem_twinDomU` — the unit twin domain (decidability through
      the `x·x⁻¹ = 1` equation — no `DecidablePred IsUnit` needed);
    * `twinDomU_eq_twinDom` / `twinVU_eq_twinV` — **THE PRIME BRIDGE**: at prime
      moduli the unit domain IS the punctured domain and `twinVU = twinV` — no
      object changes at prime level, total reuse of the prime module;
    * `castHom_inv_of_isUnit` — component inverses of UNITS map componentwise
      (load-bearing unit hypothesis: 10 explicit nonunit counterexamples mod 35);
    * `isUnit_crt_iff` / `mem_twinDomU_crt` — the unit domain is CRT-componentwise
      (`x ≠ 0` is NOT — the reason the naive route dies);
    * `twinVU_crt_factor` — **THE TWISTED FACTORIZATION** displayed above;
    * `twinVU_family_fourth_full` / `twinVU_family_M4_norm` — the triple
      orthogonality and `M4U(q) = q³·N4U(q)` at EVERY modulus (the prime
      module's Layer-4 argument runs verbatim: `stdAddChar` is primitive at all
      `q`);
    * `twinN4U_card_crt` — **N4U IS CRT-MULTIPLICATIVE** (quadruple bijection;
      NOTE: the prime module's uniform fiber law does NOT port — composite
      fibers have sizes `{1,2,4}` — multiplicativity must go through the CRT
      bijection, and does);
    * `twinVU_family_M4_semiprime` — the closed form at semiprime moduli.

  DISCLOSURES (mandatory reading before quoting):
    * COMPLETE SUMS, UNSIGNED, FULL BOXES.  This is infrastructure for the
      composite-modulus complete-sum core; the wall's faces C/E live on SHORT
      windows and μ-SIGNED aggregation across moduli — neither is touched.
      Rewriting each character exactly creates no cancellation that was not
      already there.  NOT a §110 event; no registered target (CRE,
      SemiprimeShortRestriction, HigherConductorDispersion, LowFreqRootCoherence,
      OneWingTarget) moved.
    * Coprimality `q₁ ⊥ q₂` is the ONLY hypothesis of the factorization and of
      M4U-multiplicativity; oddness of the prime factors enters ONLY in the
      closed form (`ℓ = 3` admissible with factor `1·1`; `ℓ = 2` breaks the
      shape and is excluded there).
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIITwinVariety
import EuclidsPath.Engine.GeometricTypeIICocycle
import EuclidsPath.Engine.GeometricSegreFarey

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

private instance neZero_mul_tv {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] :
    NeZero (q₁ * q₂) :=
  ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩

/-! ### Layer 1 — the unit twin domain -/

/-- **The unit twin domain**: both `x` and `x + 2` invertible — the honest
    composite-modulus domain (decidable through the `x·x⁻¹ = 1` equations). -/
def twinDomU (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter (fun x : ZMod q =>
    x * x⁻¹ = 1 ∧ (x + 2) * (x + 2)⁻¹ = 1)

theorem mem_twinDomU {q : ℕ} [NeZero q] {x : ZMod q} :
    x ∈ twinDomU q ↔ IsUnit x ∧ IsUnit (x + 2) := by
  simp only [twinDomU, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨IsUnit.of_mul_eq_one _ h1, IsUnit.of_mul_eq_one _ h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ZMod.mul_inv_of_unit _ h1, ZMod.mul_inv_of_unit _ h2⟩

/-- **THE PRIME BRIDGE**: at prime moduli the unit domain IS the punctured
    domain. -/
theorem twinDomU_eq_twinDom {ℓ : ℕ} [Fact ℓ.Prime] :
    twinDomU ℓ = twinDom ℓ := by
  ext x
  rw [mem_twinDomU, mem_twinDom, isUnit_iff_ne_zero, isUnit_iff_ne_zero]

/-- Component inverses of UNITS map componentwise (the unit hypothesis is
    load-bearing — false on nonunits). -/
theorem castHom_inv_of_isUnit {q m : ℕ} [NeZero q] [NeZero m] (h : m ∣ q)
    {x : ZMod q} (hx : IsUnit x) :
    ZMod.castHom h (ZMod m) x⁻¹ = (ZMod.castHom h (ZMod m) x)⁻¹ := by
  have h1 : ZMod.castHom h (ZMod m) x * ZMod.castHom h (ZMod m) x⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ hx, map_one]
  have h2 : ZMod.castHom h (ZMod m) x * (ZMod.castHom h (ZMod m) x)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (hx.map _)
  exact (hx.map (ZMod.castHom h (ZMod m))).mul_left_cancel (h1.trans h2.symm)

/-- Units mod `q₁q₂` are exactly the componentwise units (`x ≠ 0` is NOT
    componentwise — the naive route's death). -/
theorem isUnit_crt_iff {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (x : ZMod (q₁ * q₂)) :
    IsUnit x
      ↔ IsUnit (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x)
        ∧ IsUnit (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x) := by
  constructor
  · intro hx
    exact ⟨hx.map _, hx.map _⟩
  · rintro ⟨h1, h2⟩
    have hpair : IsUnit (ZMod.chineseRemainder hco x) := by
      rw [CircleVolume.chineseRemainder_eq_pair hco x]
      exact (Prod.isUnit_iff).mpr ⟨h1, h2⟩
    have := hpair.map (ZMod.chineseRemainder hco).symm.toRingHom
    rwa [show (ZMod.chineseRemainder hco).symm.toRingHom
        (ZMod.chineseRemainder hco x) = x from
      (ZMod.chineseRemainder hco).symm_apply_apply x] at this

/-- The unit twin domain is CRT-componentwise. -/
theorem mem_twinDomU_crt {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (x : ZMod (q₁ * q₂)) :
    x ∈ twinDomU (q₁ * q₂)
      ↔ ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x ∈ twinDomU q₁
        ∧ ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x ∈ twinDomU q₂ := by
  rw [mem_twinDomU, mem_twinDomU, mem_twinDomU]
  have hshift1 : ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) (x + 2)
      = ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x + 2 := by
    rw [map_add, map_ofNat]
  have hshift2 : ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) (x + 2)
      = ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x + 2 := by
    rw [map_add, map_ofNat]
  rw [isUnit_crt_iff hco x, isUnit_crt_iff hco (x + 2), hshift1, hshift2]
  tauto

/-! ### Layer 2 — twinVU and the twisted factorization -/

/-- **The unit twin family**: the twin exponential sum over the unit domain.
    A named structural object, NOT a target. -/
noncomputable def twinVU (q : ℕ) [NeZero q] (a b₁ b₂ : ZMod q) : ℂ :=
  ∑ x ∈ twinDomU q, ZMod.stdAddChar (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹)

theorem twinVU_apply {q : ℕ} [NeZero q] (a b₁ b₂ : ZMod q) :
    twinVU q a b₁ b₂
      = ∑ x ∈ twinDomU q,
          ZMod.stdAddChar (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹) := rfl

/-- At prime moduli `twinVU = twinV` — total reuse of the prime module. -/
theorem twinVU_eq_twinV {ℓ : ℕ} [Fact ℓ.Prime] (a b₁ b₂ : ZMod ℓ) :
    twinVU ℓ a b₁ b₂ = twinV ℓ a b₁ b₂ := by
  rw [twinVU_apply, twinV_apply, twinDomU_eq_twinDom]

/-- **THE TWISTED FACTORIZATION**: over coprime moduli the unit twin family
    factors with the cocycle units on all three frequency slots (domain
    variable untwisted). -/
theorem twinVU_crt_factor {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (a b₁ b₂ : ZMod (q₁ * q₂)) :
    twinVU (q₁ * q₂) a b₁ b₂
      = twinVU q₁
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a)
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₁)
          ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₂)
        * twinVU q₂
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a)
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₁)
          ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₂) := by
  classical
  set c₁ := ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) with hc₁
  set c₂ := ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) with hc₂
  set u₁ : ZMod q₁ := (q₂ : ZMod q₁)⁻¹ with hu₁
  set u₂ : ZMod q₂ := (q₁ : ZMod q₂)⁻¹ with hu₂
  -- the two ite-extended component functions
  set f₁ : ZMod q₁ → ℂ := fun t =>
    if t ∈ twinDomU q₁
    then ZMod.stdAddChar ((u₁ * c₁ a) * t + (u₁ * c₁ b₁) * t⁻¹
      + (u₁ * c₁ b₂) * (t + 2)⁻¹) else 0 with hf₁
  set f₂ : ZMod q₂ → ℂ := fun t =>
    if t ∈ twinDomU q₂
    then ZMod.stdAddChar ((u₂ * c₂ a) * t + (u₂ * c₂ b₁) * t⁻¹
      + (u₂ * c₂ b₂) * (t + 2)⁻¹) else 0 with hf₂
  have hLHS : twinVU (q₁ * q₂) a b₁ b₂
      = ∑ x : ZMod (q₁ * q₂), f₁ (c₁ x) * f₂ (c₂ x) := by
    have hfold : twinVU (q₁ * q₂) a b₁ b₂
        = ∑ x : ZMod (q₁ * q₂),
            (if x ∈ twinDomU (q₁ * q₂)
              then ZMod.stdAddChar (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹)
              else 0) := by
      rw [twinVU_apply, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hfold]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ twinDomU (q₁ * q₂)
    · obtain ⟨hx1, hx2⟩ := (mem_twinDomU_crt hco x).mp hx
      obtain ⟨hxu, hx2u⟩ := mem_twinDomU.mp hx
      rw [if_pos hx, hf₁, hf₂]
      show ZMod.stdAddChar (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹)
        = (if c₁ x ∈ twinDomU q₁ then _ else 0)
          * (if c₂ x ∈ twinDomU q₂ then _ else 0)
      rw [if_pos hx1, if_pos hx2]
      rw [stdAddChar_crt_factor hco (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹)]
      congr 1
      · congr 1
        rw [map_add, map_add, map_mul, map_mul, map_mul,
          castHom_inv_of_isUnit _ hxu, castHom_inv_of_isUnit _ hx2u,
          map_add, map_ofNat]
        ring
      · congr 1
        rw [map_add, map_add, map_mul, map_mul, map_mul,
          castHom_inv_of_isUnit _ hxu, castHom_inv_of_isUnit _ hx2u,
          map_add, map_ofNat]
        ring
    · rw [if_neg hx]
      rcases (not_and_or.mp
        (fun hboth => hx ((mem_twinDomU_crt hco x).mpr hboth))) with h | h
      · rw [hf₁]
        show (0 : ℂ) = (if c₁ x ∈ twinDomU q₁ then _ else 0) * f₂ (c₂ x)
        rw [if_neg h, zero_mul]
      · rw [hf₂]
        show (0 : ℂ) = f₁ (c₁ x) * (if c₂ x ∈ twinDomU q₂ then _ else 0)
        rw [if_neg h, mul_zero]
  rw [hLHS, SegreFarey.crt_sum_factor hco f₁ f₂]
  congr 1
  · simp only [hf₁]
    rw [Finset.sum_ite_mem, Finset.univ_inter, twinVU_apply]
  · simp only [hf₂]
    rw [Finset.sum_ite_mem, Finset.univ_inter, twinVU_apply]

/-! ### Layer 3 — the fourth moment at every modulus and its multiplicativity -/

/-- The counting object at general modulus (unit domain, three keys). -/
def twinN4U (q : ℕ) [NeZero q] :
    Finset ((ZMod q × ZMod q) × (ZMod q × ZMod q)) :=
  ((twinDomU q ×ˢ twinDomU q) ×ˢ (twinDomU q ×ˢ twinDomU q)).filter
    (fun r => r.1.1 + r.1.2 = r.2.1 + r.2.2
      ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
      ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)

/-- At prime moduli `twinN4U = twinN4`. -/
theorem twinN4U_eq_twinN4 {ℓ : ℕ} [Fact ℓ.Prime] : twinN4U ℓ = twinN4 ℓ := by
  unfold twinN4U twinN4
  rw [twinDomU_eq_twinDom]

private theorem sum_pull3' {M ι κ : Type*} [AddCommMonoid M]
    (sa sb sc : Finset ι) (t : Finset κ) (f : ι → ι → ι → κ → M) :
    ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ p ∈ t, f a b c p
      = ∑ p ∈ t, ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, f a b c p := by
  calc ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ p ∈ t, f a b c p
      = ∑ a ∈ sa, ∑ b ∈ sb, ∑ p ∈ t, ∑ c ∈ sc, f a b c p :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_comm
    _ = ∑ a ∈ sa, ∑ p ∈ t, ∑ b ∈ sb, ∑ c ∈ sc, f a b c p :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ t, ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, f a b c p := Finset.sum_comm

private theorem stdAddChar_conj_u {q : ℕ} [NeZero q] (x : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hnorm : ‖ZMod.stdAddChar x‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hinv : ZMod.stdAddChar (-x) = (ZMod.stdAddChar x)⁻¹ :=
    AddChar.map_neg_eq_inv _ x
  rw [hinv, ← Complex.inv_eq_conj hnorm]

private theorem char_collapse_q {q : ℕ} [NeZero q] (t : ZMod q) :
    ∑ a : ZMod q, ZMod.stdAddChar (a * t) = if t = 0 then (q : ℂ) else 0 := by
  have hcomm : ∀ a : ZMod q,
      ZMod.stdAddChar (a * t) = ZMod.stdAddChar (a * t) := fun _ => rfl
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card,
    Nat.cast_ite, Nat.cast_zero]

private theorem triple_char_collapse_q {q : ℕ} [NeZero q] (u v w : ZMod q) :
    ∑ a : ZMod q, ∑ b : ZMod q, ∑ c : ZMod q,
      ZMod.stdAddChar (a * u + b * v + c * w)
      = if u = 0 ∧ v = 0 ∧ w = 0 then (q : ℂ) ^ 3 else 0 := by
  have hfactor : (∑ a : ZMod q, ZMod.stdAddChar (a * u))
        * ((∑ b : ZMod q, ZMod.stdAddChar (b * v))
          * (∑ c : ZMod q, ZMod.stdAddChar (c * w)))
      = ∑ a : ZMod q, ∑ b : ZMod q, ∑ c : ZMod q,
          ZMod.stdAddChar (a * u)
            * (ZMod.stdAddChar (b * v) * ZMod.stdAddChar (c * w)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  calc ∑ a : ZMod q, ∑ b : ZMod q, ∑ c : ZMod q,
        ZMod.stdAddChar (a * u + b * v + c * w)
      = ∑ a : ZMod q, ∑ b : ZMod q, ∑ c : ZMod q,
          ZMod.stdAddChar (a * u)
            * (ZMod.stdAddChar (b * v) * ZMod.stdAddChar (c * w)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = (∑ a : ZMod q, ZMod.stdAddChar (a * u))
          * ((∑ b : ZMod q, ZMod.stdAddChar (b * v))
            * (∑ c : ZMod q, ZMod.stdAddChar (c * w))) := hfactor.symm
    _ = (if u = 0 then (q : ℂ) else 0)
          * ((if v = 0 then (q : ℂ) else 0) * (if w = 0 then (q : ℂ) else 0)) := by
        rw [char_collapse_q, char_collapse_q, char_collapse_q]
    _ = if u = 0 ∧ v = 0 ∧ w = 0 then (q : ℂ) ^ 3 else 0 := by
        by_cases hu : u = 0
        · by_cases hv : v = 0
          · by_cases hw : w = 0
            · rw [if_pos hu, if_pos hv, if_pos hw, if_pos ⟨hu, hv, hw⟩]
              ring
            · rw [if_pos hu, if_pos hv, if_neg hw,
                if_neg (fun h : u = 0 ∧ v = 0 ∧ w = 0 => hw h.2.2)]
              ring
          · rw [if_pos hu, if_neg hv,
              if_neg (fun h : u = 0 ∧ v = 0 ∧ w = 0 => hv h.2.1)]
            ring
        · rw [if_neg hu, if_neg (fun h : u = 0 ∧ v = 0 ∧ w = 0 => hu h.1)]
          ring

private theorem twinVU_sq_expand {q : ℕ} [NeZero q] (a b₁ b₂ : ZMod q) :
    twinVU q a b₁ b₂ ^ 2
      = ∑ p ∈ twinDomU q ×ˢ twinDomU q,
          ZMod.stdAddChar (a * (p.1 + p.2) + b₁ * (p.1⁻¹ + p.2⁻¹)
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹)) := by
  rw [sq, twinVU_apply, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- **Triple orthogonality at EVERY modulus** — the prime module's Layer-4
    argument verbatim (`stdAddChar` is primitive at all `q`). -/
theorem twinVU_family_fourth_full {q : ℕ} [NeZero q] :
    ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
      twinVU q a b₁ b₂ ^ 2 * twinVU q (-a) (-b₁) (-b₂) ^ 2
      = (q : ℂ) ^ 3 * ((twinN4U q).card : ℂ) := by
  have hexpand : ∀ a b₁ b₂ : ZMod q,
      twinVU q a b₁ b₂ ^ 2 * twinVU q (-a) (-b₁) (-b₂) ^ 2
      = ∑ p ∈ twinDomU q ×ˢ twinDomU q, ∑ r ∈ twinDomU q ×ˢ twinDomU q,
          ZMod.stdAddChar (a * (p.1 + p.2 - (r.1 + r.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (r.1⁻¹ + r.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((r.1 + 2)⁻¹ + (r.2 + 2)⁻¹))) := by
    intro a b₁ b₂
    rw [twinVU_sq_expand, twinVU_sq_expand, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
        twinVU q a b₁ b₂ ^ 2 * twinVU q (-a) (-b₁) (-b₂) ^ 2
      = ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
          ∑ p ∈ twinDomU q ×ˢ twinDomU q, ∑ r ∈ twinDomU q ×ˢ twinDomU q,
          ZMod.stdAddChar (a * (p.1 + p.2 - (r.1 + r.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (r.1⁻¹ + r.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((r.1 + 2)⁻¹ + (r.2 + 2)⁻¹))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
          Finset.sum_congr rfl fun b₂ _ => hexpand a b₁ b₂
    _ = ∑ p ∈ twinDomU q ×ˢ twinDomU q, ∑ a : ZMod q, ∑ b₁ : ZMod q,
          ∑ b₂ : ZMod q, ∑ r ∈ twinDomU q ×ˢ twinDomU q,
          ZMod.stdAddChar (a * (p.1 + p.2 - (r.1 + r.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (r.1⁻¹ + r.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((r.1 + 2)⁻¹ + (r.2 + 2)⁻¹))) :=
        sum_pull3' _ _ _ _ _
    _ = ∑ p ∈ twinDomU q ×ˢ twinDomU q, ∑ r ∈ twinDomU q ×ˢ twinDomU q,
          ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
          ZMod.stdAddChar (a * (p.1 + p.2 - (r.1 + r.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (r.1⁻¹ + r.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((r.1 + 2)⁻¹ + (r.2 + 2)⁻¹))) :=
        Finset.sum_congr rfl fun p _ => sum_pull3' _ _ _ _ _
    _ = ∑ p ∈ twinDomU q ×ˢ twinDomU q, ∑ r ∈ twinDomU q ×ˢ twinDomU q,
          if (p.1 + p.2 = r.1 + r.2 ∧ p.1⁻¹ + p.2⁻¹ = r.1⁻¹ + r.2⁻¹
              ∧ (p.1 + 2)⁻¹ + (p.2 + 2)⁻¹ = (r.1 + 2)⁻¹ + (r.2 + 2)⁻¹)
            then (q : ℂ) ^ 3 else 0 := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
        rw [triple_char_collapse_q]
        simp only [sub_eq_zero]
    _ = ∑ p ∈ twinDomU q ×ˢ twinDomU q, ∑ r ∈ twinDomU q ×ˢ twinDomU q,
          (fun s : (ZMod q × ZMod q) × (ZMod q × ZMod q) =>
            if (s.1.1 + s.1.2 = s.2.1 + s.2.2
                ∧ s.1.1⁻¹ + s.1.2⁻¹ = s.2.1⁻¹ + s.2.2⁻¹
                ∧ (s.1.1 + 2)⁻¹ + (s.1.2 + 2)⁻¹ = (s.2.1 + 2)⁻¹ + (s.2.2 + 2)⁻¹)
              then (q : ℂ) ^ 3 else 0) (p, r) := rfl
    _ = ∑ s ∈ (twinDomU q ×ˢ twinDomU q) ×ˢ (twinDomU q ×ˢ twinDomU q),
          if (s.1.1 + s.1.2 = s.2.1 + s.2.2
              ∧ s.1.1⁻¹ + s.1.2⁻¹ = s.2.1⁻¹ + s.2.2⁻¹
              ∧ (s.1.1 + 2)⁻¹ + (s.1.2 + 2)⁻¹ = (s.2.1 + 2)⁻¹ + (s.2.2 + 2)⁻¹)
            then (q : ℂ) ^ 3 else 0 :=
        (Finset.sum_product (twinDomU q ×ˢ twinDomU q)
          (twinDomU q ×ˢ twinDomU q)
          (fun s : (ZMod q × ZMod q) × (ZMod q × ZMod q) =>
            if (s.1.1 + s.1.2 = s.2.1 + s.2.2
                ∧ s.1.1⁻¹ + s.1.2⁻¹ = s.2.1⁻¹ + s.2.2⁻¹
                ∧ (s.1.1 + 2)⁻¹ + (s.1.2 + 2)⁻¹ = (s.2.1 + 2)⁻¹ + (s.2.2 + 2)⁻¹)
              then (q : ℂ) ^ 3 else 0)).symm
    _ = (q : ℂ) ^ 3 * ((twinN4U q).card : ℂ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          nsmul_eq_mul, mul_comm, twinN4U]

/-- The norm form at every modulus: `M4U(q) = q³·N4U(q)`. -/
theorem twinVU_family_M4_norm_general {q : ℕ} [NeZero q] :
    ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q, ‖twinVU q a b₁ b₂‖ ^ 4
      = (q : ℝ) ^ 3 * ((twinN4U q).card : ℝ) := by
  have hconj : ∀ a b₁ b₂ : ZMod q,
      (starRingEnd ℂ) (twinVU q a b₁ b₂) = twinVU q (-a) (-b₁) (-b₂) := by
    intro a b₁ b₂
    rw [twinVU_apply, twinVU_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [stdAddChar_conj_u]
    congr 1
    ring
  have hterm : ∀ a b₁ b₂ : ZMod q,
      ((‖twinVU q a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
        = twinVU q a b₁ b₂ ^ 2 * twinVU q (-a) (-b₁) (-b₂) ^ 2 := by
    intro a b₁ b₂
    have hc : twinVU q a b₁ b₂ * (starRingEnd ℂ) (twinVU q a b₁ b₂)
        = ((‖twinVU q a b₁ b₂‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc ((‖twinVU q a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
        = (((‖twinVU q a b₁ b₂‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
          push_cast
          ring
      _ = (twinVU q a b₁ b₂ * (starRingEnd ℂ) (twinVU q a b₁ b₂)) ^ 2 := by
          rw [hc]
      _ = (twinVU q a b₁ b₂ * twinVU q (-a) (-b₁) (-b₂)) ^ 2 := by
          rw [hconj]
      _ = twinVU q a b₁ b₂ ^ 2 * twinVU q (-a) (-b₁) (-b₂) ^ 2 := by ring
  have key : ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
      ((‖twinVU q a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
      = (q : ℂ) ^ 3 * ((twinN4U q).card : ℂ) := by
    calc ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
          ((‖twinVU q a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
        = ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q,
            twinVU q a b₁ b₂ ^ 2 * twinVU q (-a) (-b₁) (-b₂) ^ 2 :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
            Finset.sum_congr rfl fun b₂ _ => hterm a b₁ b₂
      _ = (q : ℂ) ^ 3 * ((twinN4U q).card : ℂ) := twinVU_family_fourth_full
  exact_mod_cast key

/-- Component recovery of the CRT reconstruction. -/
private theorem symm_components {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (α : ZMod q₁) (β : ZMod q₂) :
    ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁)
        ((ZMod.chineseRemainder hco).symm (α, β)) = α
    ∧ ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)
        ((ZMod.chineseRemainder hco).symm (α, β)) = β := by
  have h := CircleVolume.chineseRemainder_eq_pair hco
    ((ZMod.chineseRemainder hco).symm (α, β))
  rw [(ZMod.chineseRemainder hco).apply_symm_apply] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

/-- CRT injectivity in cast form. -/
private theorem castHom_inj {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) {x y : ZMod (q₁ * q₂)}
    (h1 : ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) x
      = ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) y)
    (h2 : ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) x
      = ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) y) : x = y := by
  apply (ZMod.chineseRemainder hco).injective
  rw [CircleVolume.chineseRemainder_eq_pair hco x,
    CircleVolume.chineseRemainder_eq_pair hco y, h1, h2]

/-- The reconstruction of a point's own components is the point. -/
private theorem symm_pair_self {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (y : ZMod (q₁ * q₂)) :
    (ZMod.chineseRemainder hco).symm
      (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) y,
        ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) y) = y := by
  rw [← CircleVolume.chineseRemainder_eq_pair hco y,
    (ZMod.chineseRemainder hco).symm_apply_apply]

/-- Key 2 maps componentwise (units). -/
private theorem castHom_key₂ {q m : ℕ} [NeZero q] [NeZero m] (h : m ∣ q)
    {x z : ZMod q} (hx : IsUnit x) (hz : IsUnit z) :
    ZMod.castHom h (ZMod m) (x⁻¹ + z⁻¹)
      = (ZMod.castHom h (ZMod m) x)⁻¹ + (ZMod.castHom h (ZMod m) z)⁻¹ := by
  rw [map_add, castHom_inv_of_isUnit h hx, castHom_inv_of_isUnit h hz]

/-- Key 3 maps componentwise (shifted units). -/
private theorem castHom_key₃ {q m : ℕ} [NeZero q] [NeZero m] (h : m ∣ q)
    {x z : ZMod q} (hx : IsUnit (x + 2)) (hz : IsUnit (z + 2)) :
    ZMod.castHom h (ZMod m) ((x + 2)⁻¹ + (z + 2)⁻¹)
      = (ZMod.castHom h (ZMod m) x + 2)⁻¹
        + (ZMod.castHom h (ZMod m) z + 2)⁻¹ := by
  have ex : ZMod.castHom h (ZMod m) (x + 2)
      = ZMod.castHom h (ZMod m) x + 2 := by
    rw [map_add, map_ofNat]
  have ez : ZMod.castHom h (ZMod m) (z + 2)
      = ZMod.castHom h (ZMod m) z + 2 := by
    rw [map_add, map_ofNat]
  rw [map_add, castHom_inv_of_isUnit h hx, castHom_inv_of_isUnit h hz, ex, ez]

/-- **N4U IS CRT-MULTIPLICATIVE** — the quadruple bijection (the prime module's
    uniform fiber law does NOT port: composite fibers have sizes `{1,2,4}`; the
    bijection route is the honest one). -/
theorem twinN4U_card_crt {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) :
    (twinN4U (q₁ * q₂)).card = (twinN4U q₁).card * (twinN4U q₂).card := by
  classical
  rw [← Finset.card_product]
  set c₁ := ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) with hc₁
  set c₂ := ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) with hc₂
  refine Finset.card_nbij'
    (fun s => (((c₁ s.1.1, c₁ s.1.2), (c₁ s.2.1, c₁ s.2.2)),
      ((c₂ s.1.1, c₂ s.1.2), (c₂ s.2.1, c₂ s.2.2))))
    (fun t => (((ZMod.chineseRemainder hco).symm (t.1.1.1, t.2.1.1),
        (ZMod.chineseRemainder hco).symm (t.1.1.2, t.2.1.2)),
      ((ZMod.chineseRemainder hco).symm (t.1.2.1, t.2.2.1),
        (ZMod.chineseRemainder hco).symm (t.1.2.2, t.2.2.2))))
    ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hdom, hk1, hk2, hk3⟩ := Finset.mem_filter.mp hs
    obtain ⟨hd1, hd2⟩ := Finset.mem_product.mp hdom
    obtain ⟨hd11, hd12⟩ := Finset.mem_product.mp hd1
    obtain ⟨hd21, hd22⟩ := Finset.mem_product.mp hd2
    have hu11 := mem_twinDomU.mp hd11
    have hu12 := mem_twinDomU.mp hd12
    have hu21 := mem_twinDomU.mp hd21
    have hu22 := mem_twinDomU.mp hd22
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩,
      Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨((mem_twinDomU_crt hco _).mp hd11).1,
          ((mem_twinDomU_crt hco _).mp hd12).1⟩,
        Finset.mem_product.mpr ⟨((mem_twinDomU_crt hco _).mp hd21).1,
          ((mem_twinDomU_crt hco _).mp hd22).1⟩⟩
    · show c₁ s.1.1 + c₁ s.1.2 = c₁ s.2.1 + c₁ s.2.2
      rw [← map_add, ← map_add, hk1]
    · show (c₁ s.1.1)⁻¹ + (c₁ s.1.2)⁻¹ = (c₁ s.2.1)⁻¹ + (c₁ s.2.2)⁻¹
      rw [← castHom_key₂ _ hu11.1 hu12.1, ← castHom_key₂ _ hu21.1 hu22.1, hk2]
    · show (c₁ s.1.1 + 2)⁻¹ + (c₁ s.1.2 + 2)⁻¹
        = (c₁ s.2.1 + 2)⁻¹ + (c₁ s.2.2 + 2)⁻¹
      rw [← castHom_key₃ _ hu11.2 hu12.2, ← castHom_key₃ _ hu21.2 hu22.2, hk3]
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨((mem_twinDomU_crt hco _).mp hd11).2,
          ((mem_twinDomU_crt hco _).mp hd12).2⟩,
        Finset.mem_product.mpr ⟨((mem_twinDomU_crt hco _).mp hd21).2,
          ((mem_twinDomU_crt hco _).mp hd22).2⟩⟩
    · show c₂ s.1.1 + c₂ s.1.2 = c₂ s.2.1 + c₂ s.2.2
      rw [← map_add, ← map_add, hk1]
    · show (c₂ s.1.1)⁻¹ + (c₂ s.1.2)⁻¹ = (c₂ s.2.1)⁻¹ + (c₂ s.2.2)⁻¹
      rw [← castHom_key₂ _ hu11.1 hu12.1, ← castHom_key₂ _ hu21.1 hu22.1, hk2]
    · show (c₂ s.1.1 + 2)⁻¹ + (c₂ s.1.2 + 2)⁻¹
        = (c₂ s.2.1 + 2)⁻¹ + (c₂ s.2.2 + 2)⁻¹
      rw [← castHom_key₃ _ hu11.2 hu12.2, ← castHom_key₃ _ hu21.2 hu22.2, hk3]
  · intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_product.mp ht
    obtain ⟨hdomA, hka1, hkb1, hkc1⟩ := Finset.mem_filter.mp ht1
    obtain ⟨hdomB, hka2, hkb2, hkc2⟩ := Finset.mem_filter.mp ht2
    obtain ⟨hdA1, hdA2⟩ := Finset.mem_product.mp hdomA
    obtain ⟨hdA11, hdA12⟩ := Finset.mem_product.mp hdA1
    obtain ⟨hdA21, hdA22⟩ := Finset.mem_product.mp hdA2
    obtain ⟨hdB1, hdB2⟩ := Finset.mem_product.mp hdomB
    obtain ⟨hdB11, hdB12⟩ := Finset.mem_product.mp hdB1
    obtain ⟨hdB21, hdB22⟩ := Finset.mem_product.mp hdB2
    have hc11 := symm_components hco t.1.1.1 t.2.1.1
    have hc12 := symm_components hco t.1.1.2 t.2.1.2
    have hc21 := symm_components hco t.1.2.1 t.2.2.1
    have hc22 := symm_components hco t.1.2.2 t.2.2.2
    have hd11q : (ZMod.chineseRemainder hco).symm (t.1.1.1, t.2.1.1)
        ∈ twinDomU (q₁ * q₂) := (mem_twinDomU_crt hco _).mpr
      ⟨by rw [hc11.1]; exact hdA11, by rw [hc11.2]; exact hdB11⟩
    have hd12q : (ZMod.chineseRemainder hco).symm (t.1.1.2, t.2.1.2)
        ∈ twinDomU (q₁ * q₂) := (mem_twinDomU_crt hco _).mpr
      ⟨by rw [hc12.1]; exact hdA12, by rw [hc12.2]; exact hdB12⟩
    have hd21q : (ZMod.chineseRemainder hco).symm (t.1.2.1, t.2.2.1)
        ∈ twinDomU (q₁ * q₂) := (mem_twinDomU_crt hco _).mpr
      ⟨by rw [hc21.1]; exact hdA21, by rw [hc21.2]; exact hdB21⟩
    have hd22q : (ZMod.chineseRemainder hco).symm (t.1.2.2, t.2.2.2)
        ∈ twinDomU (q₁ * q₂) := (mem_twinDomU_crt hco _).mpr
      ⟨by rw [hc22.1]; exact hdA22, by rw [hc22.2]; exact hdB22⟩
    have hu11 := mem_twinDomU.mp hd11q
    have hu12 := mem_twinDomU.mp hd12q
    have hu21 := mem_twinDomU.mp hd21q
    have hu22 := mem_twinDomU.mp hd22q
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hd11q, hd12q⟩,
        Finset.mem_product.mpr ⟨hd21q, hd22q⟩⟩, ?_, ?_, ?_⟩
    · apply castHom_inj hco
      · rw [map_add, map_add, hc11.1, hc12.1, hc21.1, hc22.1]
        exact hka1
      · rw [map_add, map_add, hc11.2, hc12.2, hc21.2, hc22.2]
        exact hka2
    · apply castHom_inj hco
      · rw [castHom_key₂ _ hu11.1 hu12.1, castHom_key₂ _ hu21.1 hu22.1,
          hc11.1, hc12.1, hc21.1, hc22.1]
        exact hkb1
      · rw [castHom_key₂ _ hu11.1 hu12.1, castHom_key₂ _ hu21.1 hu22.1,
          hc11.2, hc12.2, hc21.2, hc22.2]
        exact hkb2
    · apply castHom_inj hco
      · rw [castHom_key₃ _ hu11.2 hu12.2, castHom_key₃ _ hu21.2 hu22.2,
          hc11.1, hc12.1, hc21.1, hc22.1]
        exact hkc1
      · rw [castHom_key₃ _ hu11.2 hu12.2, castHom_key₃ _ hu21.2 hu22.2,
          hc11.2, hc12.2, hc21.2, hc22.2]
        exact hkc2
  · intro s _
    show (((ZMod.chineseRemainder hco).symm (c₁ s.1.1, c₂ s.1.1),
        (ZMod.chineseRemainder hco).symm (c₁ s.1.2, c₂ s.1.2)),
      ((ZMod.chineseRemainder hco).symm (c₁ s.2.1, c₂ s.2.1),
        (ZMod.chineseRemainder hco).symm (c₁ s.2.2, c₂ s.2.2))) = s
    rw [symm_pair_self hco, symm_pair_self hco, symm_pair_self hco,
      symm_pair_self hco]
  · intro t _
    have hc11 := symm_components hco t.1.1.1 t.2.1.1
    have hc12 := symm_components hco t.1.1.2 t.2.1.2
    have hc21 := symm_components hco t.1.2.1 t.2.2.1
    have hc22 := symm_components hco t.1.2.2 t.2.2.2
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
      (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
      first
      | exact hc11.1 | exact hc12.1 | exact hc21.1 | exact hc22.1
      | exact hc11.2 | exact hc12.2 | exact hc21.2 | exact hc22.2

/-- **THE CLOSED FORM AT SEMIPRIME MODULI**:
    `M4U(ℓ₁ℓ₂) = (ℓ₁ℓ₂)³·(ℓ₁−2)(2ℓ₁−5)·(ℓ₂−2)(2ℓ₂−5)`. -/
theorem twinVU_family_M4_semiprime {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    ∑ a : ZMod (ℓ₁ * ℓ₂), ∑ b₁ : ZMod (ℓ₁ * ℓ₂), ∑ b₂ : ZMod (ℓ₁ * ℓ₂),
      ‖twinVU (ℓ₁ * ℓ₂) a b₁ b₂‖ ^ 4
      = ((ℓ₁ : ℝ) * ℓ₂) ^ 3 * (((ℓ₁ : ℝ) - 2) * (2 * ℓ₁ - 5))
        * (((ℓ₂ : ℝ) - 2) * (2 * ℓ₂ - 5)) := by
  have hco : Nat.Coprime ℓ₁ ℓ₂ :=
    (Nat.coprime_primes Fact.out Fact.out).mpr hne
  rw [twinVU_family_M4_norm_general, twinN4U_card_crt hco,
    twinN4U_eq_twinN4, twinN4U_eq_twinN4, twinN4_card h₁, twinN4_card h₂]
  push_cast [Nat.cast_sub (by omega : 2 ≤ ℓ₁),
    Nat.cast_sub (by omega : 2 ≤ ℓ₂),
    Nat.cast_sub (by omega : 5 ≤ 2 * ℓ₁),
    Nat.cast_sub (by omega : 5 ≤ 2 * ℓ₂)]
  ring

/-! ### Axiom audit -/

#print axioms mem_twinDomU
#print axioms twinDomU_eq_twinDom
#print axioms castHom_inv_of_isUnit
#print axioms isUnit_crt_iff
#print axioms mem_twinDomU_crt
#print axioms twinVU_eq_twinV
#print axioms twinVU_crt_factor
#print axioms twinVU_family_fourth_full
#print axioms twinVU_family_M4_norm_general
#print axioms twinN4U_card_crt
#print axioms twinVU_family_M4_semiprime

end TypeII
end Geometric
end EuclidsPath
