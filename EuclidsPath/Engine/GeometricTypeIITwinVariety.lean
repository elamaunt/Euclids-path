/-
  GeometricTypeIITwinVariety — the THREE-KEY TWIN VARIETY over `ZMod ℓ` and the exact
  fourth moment of its exponential-sum family: the complete-sum core of the program's
  off-diagonal genre, now with BOTH twin poles `x` and `x + 2` in one variety.

  ORIGIN.  Idea-generation session (two-axes program, wave 1a): the geometric panel's
  three-frequency twin variety.  The object is the kloosN4 blueprint
  (`Step00KloostermanMoment`, Layers 1–3) one level up: where the Kloosterman variety
  matches TWO symmetric keys (`x + z`, `x⁻¹ + z⁻¹`), the twin variety matches THREE —
  `x + z`, `x⁻¹ + z⁻¹`, and `(x+2)⁻¹ + (z+2)⁻¹` — over the doubly punctured line
  `D = {x : x ≠ 0, x + 2 ≠ 0}`.  The third key is the twin structure itself: the two
  poles of the variety are at distance 2, the twin gap.

  THE DIAMOND.  The third key COLLAPSES the antipodal stratum.  In kloosN4 the pairs
  `(x, −x)` carry fibers of size `ℓ − 1` (the inverse key is automatic on `x + z = 0` —
  the two-key fattening), which is why `N4 = 3(ℓ−1)(ℓ−2)` has the factor 3.  Here the
  third key cuts the antipodal fiber from `ℓ − 3` candidates to exactly 2 (`x₃ = ±x₁`),
  so EVERY off-diagonal left pair has fiber 2 and the diagonal has fiber 1:

      twinN4 = 2(ℓ−2)² − (ℓ−2) = (ℓ−2)(2ℓ−5)

  — a CLEANER count than the Kloosterman variety's, with a strictly better constant:
  the family fourth moment is `ℓ³(ℓ−2)(2ℓ−5) < 2ℓ⁵` over the full `ℓ³` frequency box.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twinDom_card` — the doubly punctured line has `ℓ − 2` points (`ℓ ≠ 2` load-bearing);
    * `twin_fiber` — **THE UNIFORM FIBER LAW**: for every left pair `(x, z) ∈ D²` the
      right pairs sharing all three keys are EXACTLY `{(x, z), (z, x)}`; the proof splits
      into the Vieta spine (`x + z ≠ 0`: keys 1–2 force the same quadratic, key 3 rides
      along) and the corner spine (`x + z = 0`: keys 1–3 give `4/(4−x²) = 4/(4−x₃²)`,
      key 2 is vacuous — the fattening killed by the third key);
    * `twinN4_card_int` / `twinN4_card` — **THE N4 COUNT**: `2(ℓ−2)² − (ℓ−2)`, by the
      uniform fiber law summed over the `(ℓ−2)²` left pairs (fiber 1 on the diagonal,
      2 off it) — no stratum trisection needed;
    * `twinV_family_fourth_full` — **THE TRIPLE ORTHOGONALITY REDUCTION**:
      `Σ_{a,b₁,b₂ ∈ ZMod ℓ} V(a,b₁,b₂)²·V(−a,−b₁,−b₂)² = ℓ³·N4` for the family
      `V(a,b₁,b₂) = Σ_{x ∈ D} ψ(ax + b₁x⁻¹ + b₂(x+2)⁻¹)` — all three frequencies
      summed over the FULL group;
    * `twinV_family_M4_norm` — **THE FAMILY FOURTH MOMENT**:
      `Σ_{a,b₁,b₂} ‖V(a,b₁,b₂)‖⁴ = ℓ³(ℓ−2)(2ℓ−5)` — exact, over ℝ;
    * `twinV_family_M4_le` — the subtraction-free envelope `Σ ‖V‖⁴ ≤ 2ℓ⁵`
      (witness: `2ℓ⁵ = M4 + ℓ³(9ℓ−10)`);
    * `twinV_markov` — **THE MARKOV COUNT OF BAD FREQUENCY PAIRS**: for every `K > 0`,
      at most `2ℓ²/K` pairs `(b₁,b₂)` have `Σ_a ‖V(a,b₁,b₂)‖⁴ ≥ Kℓ³`.  This is the
      module's cash value: outside an explicitly counted exceptional set, the
      twin-pole phase system is fourth-moment-small JOINTLY in both wings;
    * kernel demos: `twinN4CountN` (pure-Nat fold, Fermat inverses), `twinN4CountN 5 = 15`,
      `twinN4CountN 7 = 45` by `decide`; `twinN4TwoKeyCountN 7 = 53` — the SAME fold
      with the third key REMOVED counts 53 ≠ 45 at `ℓ = 7`: the machine witnesses that
      key 3 strictly cuts the two-key fattening (at `ℓ = 5` the two counts coincide,
      15 = 15 — the cut `(ℓ−3)(ℓ−5)` is empty there, so `ℓ = 7` is the honest witness).

  NUMERIC GROUNDING (wave-1 pre-pass, adversarial verifier): `N4 = 2(ℓ−2)² − (ℓ−2)`
  confirmed by exact brute force at `ℓ = 3, 5, 7, 11, 13`; `M4 = ℓ³·N4` confirmed at
  `ℓ = 3, 5, 7, 11`; every stratum count matched the fiber decomposition tuple-by-tuple.

  DISCLOSURES (mandatory reading before quoting):
    * COMPLETE SUMS ONLY, ONE PRIME MODULUS.  Every sum is over the full residue line,
      the full frequency box, the full family.  The serial-twin wall lives on INCOMPLETE
      sums over windows and on the μ-SIGNED aggregation over many moduli `q`; this module
      touches neither.  Nothing here claims to cross the complete/incomplete boundary or
      the parity barrier.
    * NO POINTWISE EXTRACTION — THE SCALING LAW IS ABSENT.  kloosN4's Layer 4 extracts a
      pointwise bound (`‖kloos‖ ≤ 2^{1/4}ℓ^{3/4}`) because `kloos_scale` makes the whole
      family one orbit, so a single term is bounded by the family moment over `ℓ − 1`
      members.  The twin family has NO scaling law (the two poles `0` and `−2` break
      multiplicative rescaling), the family is genuinely `ℓ³`-dimensional, and the
      single-term consequence of M4 is `‖V‖ ≤ 2^{1/4}·ℓ^{5/4}` — WORSE than the trivial
      bound `ℓ − 2`.  No pointwise theorem is stated; the value of M4 here is EXCLUSIVELY
      the averaged Markov statement (`twinV_markov`).  This asymmetry is the honest
      analogue of "Layer 4 does not port".
    * NOT A §110 EVENT.  No registered target (CRE, SemiprimeShortRestriction,
      HigherConductorDispersion, LowFreqRootCoherence, OneWingTarget) is touched: this is
      green-front growth of the complete-sum core (new exact identities), not a boundary
      move.  The registered faces of the wall stand exactly where they stood.
    * ZERO NEW OPEN PROPS.  Every declaration is a definition or a proved theorem;
      `twinDom`, `twinV`, `twinN4` are named structural objects, NOT targets and NOT
      bounds.  The twin sorry is untouched.

  ## Anti-vocabulary

  No claim in this file concerns windows, incomplete sums, densities, asymptotics, or
  the infinitude of anything.  Every theorem is an exact finite identity over a complete
  range, a finite counting statement, or a single-step consequence of one.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 1 — the doubly punctured line and the character toolkit -/

/-- `2 ≠ 0` in `ZMod ℓ` for `2 < ℓ` prime (house pattern; local private copy — the
    repo's other copies are `private` in their modules). -/
private theorem two_ne_zero_zmodt {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (2 : ZMod ℓ) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)

/-- Full-line character orthogonality `Σ_a ψ(a·t) = ℓ·[t = 0]` (local private copy of
    the house collapse step). -/
private theorem char_collapse {ℓ : ℕ} [Fact ℓ.Prime] (t : ZMod ℓ) :
    ∑ a : ZMod ℓ, ZMod.stdAddChar (a * t) = if t = 0 then (ℓ : ℂ) else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar ℓ), ZMod.card,
    Nat.cast_ite, Nat.cast_zero]

/-- `‖ψ(x)‖ = 1` (local private copy). -/
private theorem stdAddChar_norm_one {ℓ : ℕ} [NeZero ℓ] (x : ZMod ℓ) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- `conj ψ(x) = ψ(−x)` (local private copy). -/
private theorem stdAddChar_conj' {ℓ : ℕ} [NeZero ℓ] (x : ZMod ℓ) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hinv : ZMod.stdAddChar (-x) = (ZMod.stdAddChar x)⁻¹ := AddChar.map_neg_eq_inv _ x
  rw [hinv, ← Complex.inv_eq_conj (stdAddChar_norm_one x)]

/-- **The twin domain**: the doubly punctured line `D = {x : x ≠ 0 ∧ x + 2 ≠ 0}` —
    both poles of the twin variety removed.  A named structural object, NOT a target. -/
def twinDom (ℓ : ℕ) [NeZero ℓ] : Finset (ZMod ℓ) :=
  Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0 ∧ x + 2 ≠ 0)

theorem mem_twinDom {ℓ : ℕ} [NeZero ℓ] {x : ZMod ℓ} :
    x ∈ twinDom ℓ ↔ x ≠ 0 ∧ x + 2 ≠ 0 := by
  simp [twinDom]

/-- The twin domain has `ℓ − 2` points.  `ℓ ≠ 2` is load-bearing (at `ℓ = 2` the two
    poles coincide and `|D| = 1 ≠ 0`). -/
theorem twinDom_card {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (twinDom ℓ).card = ℓ - 2 := by
  have h20 : (2 : ZMod ℓ) ≠ 0 := two_ne_zero_zmodt h2
  have heq : twinDom ℓ = (Finset.univ.erase (0 : ZMod ℓ)).erase (-2 : ZMod ℓ) := by
    ext x
    simp only [mem_twinDom, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hx0, hx2⟩
      exact ⟨fun h => hx2 (by rw [h]; ring), hx0⟩
    · rintro ⟨hxm2, hx0⟩
      exact ⟨hx0, fun h => hxm2 (by linear_combination h)⟩
  have hmem : (-2 : ZMod ℓ) ∈ Finset.univ.erase (0 : ZMod ℓ) :=
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr h20, Finset.mem_univ _⟩
  rw [heq, Finset.card_erase_of_mem hmem,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  omega

/-! ### Layer 2 — the three-frequency twin exponential sum -/

/-- **The twin exponential-sum family**: `V(a,b₁,b₂) = Σ_{x ∈ D} ψ(ax + b₁x⁻¹ + b₂(x+2)⁻¹)`
    — the linear frequency `a`, the wing frequency `b₁` at the pole `0`, and the wing
    frequency `b₂` at the twin pole `−2`.  A named structural object, NOT a bound. -/
noncomputable def twinV (ℓ : ℕ) [NeZero ℓ] (a b₁ b₂ : ZMod ℓ) : ℂ :=
  ∑ x ∈ twinDom ℓ, ZMod.stdAddChar (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹)

theorem twinV_apply {ℓ : ℕ} [NeZero ℓ] (a b₁ b₂ : ZMod ℓ) :
    twinV ℓ a b₁ b₂
      = ∑ x ∈ twinDom ℓ, ZMod.stdAddChar (a * x + b₁ * x⁻¹ + b₂ * (x + 2)⁻¹) := rfl

/-- The squared-sum expansion: `V(a,b₁,b₂)² = Σ_{(x,z) ∈ D²} ψ(a(x+z) + b₁(x⁻¹+z⁻¹) +
    b₂((x+2)⁻¹+(z+2)⁻¹))` — the square as a single sum over ordered pairs, keyed by the
    THREE symmetric functions of the pair (blueprint: `kloos_sq_expand`, one key up). -/
private theorem twinV_sq_expand {ℓ : ℕ} [NeZero ℓ] (a b₁ b₂ : ZMod ℓ) :
    twinV ℓ a b₁ b₂ ^ 2
      = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ,
          ZMod.stdAddChar (a * (p.1 + p.2) + b₁ * (p.1⁻¹ + p.2⁻¹)
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹)) := by
  rw [sq, twinV_apply, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-! ### Layer 3 — the twin variety twinN4 and the uniform fiber law

The counting object: ordered pairs of ordered `D`-pairs sharing all THREE keys.  The
completeness spine, one key up from the blueprint: for `s = x + z ≠ 0` keys 1–2 force
the Vieta quadratic (key 3 rides along, being symmetric in the pair); for `s = 0` key 2
is automatic (the kloosN4 fattening) but key 3 now forces `4/(4−x²) = 4/(4−x₃²)`, i.e.
`x₃ = ±x` — fiber 2, not `ℓ − 1`.  The fiber is `{(x,z),(z,x)}` UNIFORMLY. -/

/-- **The twinN4 counting object**: ordered pairs of ordered `D`-pairs with equal key
    triples.  A named structural object, NOT a target. -/
def twinN4 (ℓ : ℕ) [NeZero ℓ] : Finset ((ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ)) :=
  ((twinDom ℓ ×ˢ twinDom ℓ) ×ˢ (twinDom ℓ ×ˢ twinDom ℓ)).filter
    (fun r => r.1.1 + r.1.2 = r.2.1 + r.2.2
      ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
      ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)

/-- The Vieta spine (`x + z ≠ 0`): keys 1–2 force `(q₁ − x)(q₁ − z) = 0` — the same
    monic quadratic (blueprint `fiber_of_ne_zero` core, keys unchanged). -/
private theorem twin_fiber_vieta {ℓ : ℕ} [Fact ℓ.Prime] {x z : ZMod ℓ}
    (hx0 : x ≠ 0) (hz0 : z ≠ 0) (hs : x + z ≠ 0) {q : ZMod ℓ × ZMod ℓ}
    (hq10 : q.1 ≠ 0) (hq20 : q.2 ≠ 0)
    (he1 : x + z = q.1 + q.2) (he2 : x⁻¹ + z⁻¹ = q.1⁻¹ + q.2⁻¹) :
    (q.1 - x) * (q.1 - z) = 0 := by
  have hx1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hz1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hq11 : q.1 * q.1⁻¹ = 1 := mul_inv_cancel₀ hq10
  have hq21 : q.2 * q.2⁻¹ = 1 := mul_inv_cancel₀ hq20
  have hA : (x⁻¹ + z⁻¹) * (x * z) = z + x := by
    linear_combination z * hx1 + x * hz1
  have hB : (q.1⁻¹ + q.2⁻¹) * (q.1 * q.2) = q.2 + q.1 := by
    linear_combination q.2 * hq11 + q.1 * hq21
  have hs' : x⁻¹ + z⁻¹ ≠ 0 := by
    intro h0
    apply hs
    have hA0 := hA
    rw [h0, zero_mul] at hA0
    linear_combination -hA0
  have hprod : q.1 * q.2 = x * z := by
    apply mul_left_cancel₀ hs'
    calc (x⁻¹ + z⁻¹) * (q.1 * q.2)
        = (q.1⁻¹ + q.2⁻¹) * (q.1 * q.2) := by rw [he2]
      _ = q.2 + q.1 := hB
      _ = x + z := by linear_combination -he1
      _ = (x⁻¹ + z⁻¹) * (x * z) := by linear_combination -hA
  linear_combination (-q.1) * he1 - hprod

/-- The corner spine (`x + z = 0`): key 2 is vacuous, but keys 1 and 3 force
    `(q₁ − x)(q₁ − z) = 0` through `4/(4−x²) = 4/(4−q₁²)` — the two-key antipodal
    fattening cut to fiber 2 by the third key.  THE NEW MECHANISM of this module. -/
private theorem twin_fiber_corner {ℓ : ℕ} [Fact ℓ.Prime] (h20 : (2 : ZMod ℓ) ≠ 0)
    {x z : ZMod ℓ} (hx2 : x + 2 ≠ 0) (hz2 : z + 2 ≠ 0) (hs : x + z = 0)
    {q : ZMod ℓ × ZMod ℓ} (hq12 : q.1 + 2 ≠ 0) (hq22 : q.2 + 2 ≠ 0)
    (he1 : x + z = q.1 + q.2)
    (he3 : (x + 2)⁻¹ + (z + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹) :
    (q.1 - x) * (q.1 - z) = 0 := by
  have hA1 : (x + 2) * (x + 2)⁻¹ = 1 := mul_inv_cancel₀ hx2
  have hB1 : (z + 2) * (z + 2)⁻¹ = 1 := mul_inv_cancel₀ hz2
  have hC1 : (q.1 + 2) * (q.1 + 2)⁻¹ = 1 := mul_inv_cancel₀ hq12
  have hD1 : (q.2 + 2) * (q.2 + 2)⁻¹ = 1 := mul_inv_cancel₀ hq22
  have hAB : ((x + 2)⁻¹ + (z + 2)⁻¹) * ((x + 2) * (z + 2)) = 4 := by
    linear_combination (z + 2) * hA1 + (x + 2) * hB1 + hs
  have hCD : ((q.1 + 2)⁻¹ + (q.2 + 2)⁻¹) * ((q.1 + 2) * (q.2 + 2)) = 4 := by
    linear_combination (q.2 + 2) * hC1 + (q.1 + 2) * hD1 + hs - he1
  have h40 : (4 : ZMod ℓ) ≠ 0 := by
    have h4 : (4 : ZMod ℓ) = 2 * 2 := by norm_num
    rw [h4]
    exact mul_ne_zero h20 h20
  have hSL : (x + 2)⁻¹ + (z + 2)⁻¹ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hAB
    exact h40 hAB.symm
  have hABCD : (x + 2) * (z + 2) = (q.1 + 2) * (q.2 + 2) := by
    apply mul_left_cancel₀ hSL
    calc ((x + 2)⁻¹ + (z + 2)⁻¹) * ((x + 2) * (z + 2))
        = (4 : ZMod ℓ) := hAB
      _ = ((q.1 + 2)⁻¹ + (q.2 + 2)⁻¹) * ((q.1 + 2) * (q.2 + 2)) := hCD.symm
      _ = ((x + 2)⁻¹ + (z + 2)⁻¹) * ((q.1 + 2) * (q.2 + 2)) := by rw [he3]
  linear_combination hABCD - (q.1 + 2) * he1

/-- **THE UNIFORM FIBER LAW**: for every left pair `(x, z) ∈ D²`, the right pairs
    sharing all three keys are EXACTLY the two orderings `{(x, z), (z, x)}` (which
    coincide on the diagonal).  The Vieta spine serves `x + z ≠ 0`, the corner spine
    serves `x + z = 0` — where kloosN4's fiber was the whole antipodal line, the third
    key cuts it to the pair. -/
theorem twin_fiber {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {x z : ZMod ℓ}
    (hx : x ∈ twinDom ℓ) (hz : z ∈ twinDom ℓ) :
    ((twinDom ℓ ×ˢ twinDom ℓ).filter
      (fun q => x + z = q.1 + q.2 ∧ x⁻¹ + z⁻¹ = q.1⁻¹ + q.2⁻¹
        ∧ (x + 2)⁻¹ + (z + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹))
      = {(x, z), (z, x)} := by
  have h20 : (2 : ZMod ℓ) ≠ 0 := two_ne_zero_zmodt h2
  obtain ⟨hx0, hx2⟩ := mem_twinDom.mp hx
  obtain ⟨hz0, hz2⟩ := mem_twinDom.mp hz
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hq1, hq2⟩, he1, he2, he3⟩
    obtain ⟨hq10, hq12⟩ := mem_twinDom.mp hq1
    obtain ⟨hq20, hq22⟩ := mem_twinDom.mp hq2
    have hviet : (q.1 - x) * (q.1 - z) = 0 := by
      by_cases hs : x + z = 0
      · exact twin_fiber_corner h20 hx2 hz2 hs hq12 hq22 he1 he3
      · exact twin_fiber_vieta hx0 hz0 hs hq10 hq20 he1 he2
    rcases mul_eq_zero.mp hviet with h | h
    · exact Or.inl (Prod.ext_iff.mpr
        ⟨by linear_combination h, by linear_combination -he1 - h⟩)
    · exact Or.inr (Prod.ext_iff.mpr
        ⟨by linear_combination h, by linear_combination -he1 - h⟩)
  · rintro (h | h) <;> subst h
    · exact ⟨⟨hx, hz⟩, rfl, rfl, rfl⟩
    · exact ⟨⟨hz, hx⟩, add_comm x z, add_comm x⁻¹ z⁻¹,
        add_comm (x + 2)⁻¹ (z + 2)⁻¹⟩

/-- The diagonal of `D²` has `ℓ − 2` points (house bijection pattern). -/
private theorem twin_diag_card {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ((twinDom ℓ ×ˢ twinDom ℓ).filter (fun p => p.1 = p.2)).card = ℓ - 2 := by
  have hbij : ((twinDom ℓ ×ˢ twinDom ℓ).filter (fun p => p.1 = p.2)).card
      = (twinDom ℓ).card := by
    refine Finset.card_bij' (fun p _ => p.1) (fun y _ => (y, y)) ?_ ?_ ?_ ?_
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hy⟩, rfl⟩
    · intro p hp
      have hpd : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      show (p.1, p.1) = p
      nth_rewrite 2 [hpd]
      rfl
    · intro y _
      rfl
  rw [hbij, twinDom_card h2]

/-- **THE N4 COUNT, over ℤ**: `twinN4 = 2(ℓ−2)² − (ℓ−2)`.  Route: fiber the count over
    the left pair; by the uniform fiber law every fiber is `{(x,z),(z,x)}` — size 1 on
    the diagonal, 2 off it — so the count is `2(ℓ−2)² − (ℓ−2)` with NO stratum
    trisection (the blueprint's factor-3 anomaly is gone: the third key removed it). -/
theorem twinN4_card_int {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ((twinN4 ℓ).card : ℤ) = 2 * ((ℓ : ℤ) - 2) ^ 2 - ((ℓ : ℤ) - 2) := by
  have h2' : 2 ≤ ℓ := by omega
  -- the count, fibered over the left pair
  have hcount : (twinN4 ℓ).card
      = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ,
        ((twinDom ℓ ×ˢ twinDom ℓ).filter
          (fun q => p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹
            ∧ (p.1 + 2)⁻¹ + (p.2 + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹)).card := by
    calc (twinN4 ℓ).card
        = ∑ r ∈ (twinDom ℓ ×ˢ twinDom ℓ) ×ˢ (twinDom ℓ ×ˢ twinDom ℓ),
            if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
                ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)
              then 1 else 0 := by
          rw [twinN4, Finset.card_filter]
      _ = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ,
            ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
            (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
              if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                  ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
                  ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)
                then 1 else 0) (p, q) :=
          Finset.sum_product (twinDom ℓ ×ˢ twinDom ℓ) (twinDom ℓ ×ˢ twinDom ℓ)
            (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
              if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                  ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
                  ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)
                then 1 else 0)
      _ = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ,
            ((twinDom ℓ ×ˢ twinDom ℓ).filter
              (fun q => p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹
                ∧ (p.1 + 2)⁻¹ + (p.2 + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹)).card :=
          Finset.sum_congr rfl fun p _ =>
            (Finset.card_filter
              (fun q : ZMod ℓ × ZMod ℓ =>
                p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹
                  ∧ (p.1 + 2)⁻¹ + (p.2 + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹) _).symm
  -- the uniform fiber value: 1 on the diagonal, 2 off it
  have hconst : ∀ p ∈ twinDom ℓ ×ˢ twinDom ℓ,
      ((twinDom ℓ ×ˢ twinDom ℓ).filter
        (fun q => p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹
          ∧ (p.1 + 2)⁻¹ + (p.2 + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹)).card
        = if p.1 = p.2 then 1 else 2 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [twin_fiber h2 hp1 hp2]
    by_cases hd : p.1 = p.2
    · rw [if_pos hd, hd,
        Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
        Finset.card_singleton]
    · rw [if_neg hd]
      refine Finset.card_pair ?_
      intro hEq
      exact hd (congrArg Prod.fst hEq)
  -- assemble: diagonal count + off-diagonal count
  have hNat : (twinN4 ℓ).card
      = ((twinDom ℓ ×ˢ twinDom ℓ).filter (fun p => p.1 = p.2)).card * 1
        + ((twinDom ℓ ×ˢ twinDom ℓ).filter (fun p => ¬(p.1 = p.2))).card * 2 := by
    rw [hcount, Finset.sum_congr rfl hconst, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have hDpart := Finset.card_filter_add_card_filter_not
    (s := twinDom ℓ ×ˢ twinDom ℓ) (fun p => p.1 = p.2)
  have hprod : (twinDom ℓ ×ˢ twinDom ℓ).card = (ℓ - 2) * (ℓ - 2) := by
    rw [Finset.card_product, twinDom_card h2]
  rw [twin_diag_card h2] at hNat hDpart
  rw [hprod] at hDpart
  zify [h2'] at hNat hDpart
  linear_combination hNat + 2 * hDpart

/-- The N4 count over ℕ, in product form: `twinN4 = (ℓ−2)(2ℓ−5)`
    (`15` at `ℓ = 5`, `45` at `ℓ = 7`). -/
theorem twinN4_card {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (twinN4 ℓ).card = (ℓ - 2) * (2 * ℓ - 5) := by
  have h2' : 2 ≤ ℓ := by omega
  have h5 : 5 ≤ 2 * ℓ := by omega
  zify [h2', h5]
  linear_combination twinN4_card_int h2

/-! ### Layer 4 — triple orthogonality and the family fourth moment M4 -/

/-- Pulling one outer sum through three (generic; keeps the family calc short). -/
private theorem sum_pull3 {M ι κ : Type*} [AddCommMonoid M]
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

/-- Triple orthogonality: `Σ_{a,b,c} ψ(au + bv + cw) = ℓ³·[u = v = w = 0]` — the M2
    collapse on all three frequency axes at once. -/
private theorem triple_char_collapse {ℓ : ℕ} [Fact ℓ.Prime] (u v w : ZMod ℓ) :
    ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, ∑ c : ZMod ℓ,
      ZMod.stdAddChar (a * u + b * v + c * w)
      = if u = 0 ∧ v = 0 ∧ w = 0 then (ℓ : ℂ) ^ 3 else 0 := by
  have hfactor : (∑ a : ZMod ℓ, ZMod.stdAddChar (a * u))
        * ((∑ b : ZMod ℓ, ZMod.stdAddChar (b * v))
          * (∑ c : ZMod ℓ, ZMod.stdAddChar (c * w)))
      = ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, ∑ c : ZMod ℓ,
          ZMod.stdAddChar (a * u)
            * (ZMod.stdAddChar (b * v) * ZMod.stdAddChar (c * w)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  calc ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, ∑ c : ZMod ℓ,
        ZMod.stdAddChar (a * u + b * v + c * w)
      = ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, ∑ c : ZMod ℓ,
          ZMod.stdAddChar (a * u)
            * (ZMod.stdAddChar (b * v) * ZMod.stdAddChar (c * w)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = (∑ a : ZMod ℓ, ZMod.stdAddChar (a * u))
          * ((∑ b : ZMod ℓ, ZMod.stdAddChar (b * v))
            * (∑ c : ZMod ℓ, ZMod.stdAddChar (c * w))) := hfactor.symm
    _ = (if u = 0 then (ℓ : ℂ) else 0)
          * ((if v = 0 then (ℓ : ℂ) else 0) * (if w = 0 then (ℓ : ℂ) else 0)) := by
        rw [char_collapse, char_collapse, char_collapse]
    _ = if u = 0 ∧ v = 0 ∧ w = 0 then (ℓ : ℂ) ^ 3 else 0 := by
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

/-- **THE TRIPLE ORTHOGONALITY REDUCTION**: summing `V(a,b₁,b₂)²·V(−a,−b₁,−b₂)²` over
    the FULL frequency box `(ZMod ℓ)³` collapses all three axes and leaves `ℓ³` times
    the twinN4 count — the blueprint's double orthogonality, one frequency up. -/
theorem twinV_family_fourth_full {ℓ : ℕ} [Fact ℓ.Prime] :
    ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
      twinV ℓ a b₁ b₂ ^ 2 * twinV ℓ (-a) (-b₁) (-b₂) ^ 2
      = (ℓ : ℂ) ^ 3 * ((twinN4 ℓ).card : ℂ) := by
  have hexpand : ∀ a b₁ b₂ : ZMod ℓ,
      twinV ℓ a b₁ b₂ ^ 2 * twinV ℓ (-a) (-b₁) (-b₂) ^ 2
      = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ, ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
          ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((q.1 + 2)⁻¹ + (q.2 + 2)⁻¹))) := by
    intro a b₁ b₂
    rw [twinV_sq_expand, twinV_sq_expand, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
        twinV ℓ a b₁ b₂ ^ 2 * twinV ℓ (-a) (-b₁) (-b₂) ^ 2
      = ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
          ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ, ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
          ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((q.1 + 2)⁻¹ + (q.2 + 2)⁻¹))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
          Finset.sum_congr rfl fun b₂ _ => hexpand a b₁ b₂
    _ = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ, ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ,
          ∑ b₂ : ZMod ℓ, ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
          ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((q.1 + 2)⁻¹ + (q.2 + 2)⁻¹))) :=
        sum_pull3 _ _ _ _ _
    _ = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ, ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
          ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
          ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
            + b₁ * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))
            + b₂ * ((p.1 + 2)⁻¹ + (p.2 + 2)⁻¹
              - ((q.1 + 2)⁻¹ + (q.2 + 2)⁻¹))) :=
        Finset.sum_congr rfl fun p _ => sum_pull3 _ _ _ _ _
    _ = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ, ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
          if (p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹
              ∧ (p.1 + 2)⁻¹ + (p.2 + 2)⁻¹ = (q.1 + 2)⁻¹ + (q.2 + 2)⁻¹)
            then (ℓ : ℂ) ^ 3 else 0 := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [triple_char_collapse]
        simp only [sub_eq_zero]
    _ = ∑ p ∈ twinDom ℓ ×ˢ twinDom ℓ, ∑ q ∈ twinDom ℓ ×ˢ twinDom ℓ,
          (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
            if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
                ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)
              then (ℓ : ℂ) ^ 3 else 0) (p, q) := rfl
    _ = ∑ r ∈ (twinDom ℓ ×ˢ twinDom ℓ) ×ˢ (twinDom ℓ ×ˢ twinDom ℓ),
          if (r.1.1 + r.1.2 = r.2.1 + r.2.2
              ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
              ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)
            then (ℓ : ℂ) ^ 3 else 0 :=
        (Finset.sum_product (twinDom ℓ ×ˢ twinDom ℓ) (twinDom ℓ ×ˢ twinDom ℓ)
          (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
            if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹
                ∧ (r.1.1 + 2)⁻¹ + (r.1.2 + 2)⁻¹ = (r.2.1 + 2)⁻¹ + (r.2.2 + 2)⁻¹)
              then (ℓ : ℂ) ^ 3 else 0)).symm
    _ = (ℓ : ℂ) ^ 3 * ((twinN4 ℓ).card : ℂ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          nsmul_eq_mul, mul_comm, twinN4]

/-! ### Layer 5 — the norm form and the Markov count of bad frequency pairs -/

/-- `conj V(a,b₁,b₂) = V(−a,−b₁,−b₂)` — conjugation negates all three frequencies. -/
private theorem twinV_conj {ℓ : ℕ} [NeZero ℓ] (a b₁ b₂ : ZMod ℓ) :
    (starRingEnd ℂ) (twinV ℓ a b₁ b₂) = twinV ℓ (-a) (-b₁) (-b₂) := by
  rw [twinV_apply, twinV_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [stdAddChar_conj']
  congr 1
  ring

/-- **THE FAMILY FOURTH MOMENT, norm form over ℝ**:
    `Σ_{a,b₁,b₂} ‖V(a,b₁,b₂)‖⁴ = ℓ³(ℓ−2)(2ℓ−5)` — exact, over the full frequency box. -/
theorem twinV_family_M4_norm {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ, ‖twinV ℓ a b₁ b₂‖ ^ 4
      = (ℓ : ℝ) ^ 3 * (((ℓ : ℝ) - 2) * (2 * (ℓ : ℝ) - 5)) := by
  have hterm : ∀ a b₁ b₂ : ZMod ℓ,
      ((‖twinV ℓ a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
        = twinV ℓ a b₁ b₂ ^ 2 * twinV ℓ (-a) (-b₁) (-b₂) ^ 2 := by
    intro a b₁ b₂
    have hc : twinV ℓ a b₁ b₂ * (starRingEnd ℂ) (twinV ℓ a b₁ b₂)
        = ((‖twinV ℓ a b₁ b₂‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc ((‖twinV ℓ a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
        = (((‖twinV ℓ a b₁ b₂‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
          push_cast
          ring
      _ = (twinV ℓ a b₁ b₂ * (starRingEnd ℂ) (twinV ℓ a b₁ b₂)) ^ 2 := by
          rw [hc]
      _ = (twinV ℓ a b₁ b₂ * twinV ℓ (-a) (-b₁) (-b₂)) ^ 2 := by
          rw [twinV_conj]
      _ = twinV ℓ a b₁ b₂ ^ 2 * twinV ℓ (-a) (-b₁) (-b₂) ^ 2 := by ring
  have hcast : ((twinN4 ℓ).card : ℂ) = ((ℓ : ℂ) - 2) * (2 * (ℓ : ℂ) - 5) := by
    have hint : ((twinN4 ℓ).card : ℂ) = 2 * ((ℓ : ℂ) - 2) ^ 2 - ((ℓ : ℂ) - 2) := by
      exact_mod_cast twinN4_card_int (ℓ := ℓ) h2
    rw [hint]
    ring
  have key : ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
      ((‖twinV ℓ a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
      = (ℓ : ℂ) ^ 3 * (((ℓ : ℂ) - 2) * (2 * (ℓ : ℂ) - 5)) := by
    calc ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
          ((‖twinV ℓ a b₁ b₂‖ ^ 4 : ℝ) : ℂ)
        = ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ,
            twinV ℓ a b₁ b₂ ^ 2 * twinV ℓ (-a) (-b₁) (-b₂) ^ 2 :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
            Finset.sum_congr rfl fun b₂ _ => hterm a b₁ b₂
      _ = (ℓ : ℂ) ^ 3 * ((twinN4 ℓ).card : ℂ) := twinV_family_fourth_full
      _ = (ℓ : ℂ) ^ 3 * (((ℓ : ℂ) - 2) * (2 * (ℓ : ℂ) - 5)) := by rw [hcast]
  exact_mod_cast key

/-- The subtraction-free envelope: `Σ ‖V‖⁴ ≤ 2ℓ⁵` (indeed `2ℓ⁵ = M4 + ℓ³(9ℓ−10)`). -/
theorem twinV_family_M4_le {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ, ‖twinV ℓ a b₁ b₂‖ ^ 4
      ≤ 2 * (ℓ : ℝ) ^ 5 := by
  rw [twinV_family_M4_norm h2]
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (by omega : 3 ≤ ℓ)
  nlinarith [pow_pos (by linarith : (0 : ℝ) < (ℓ : ℝ)) 3, sq_nonneg ((ℓ : ℝ))]

/-- **THE MARKOV COUNT OF BAD FREQUENCY PAIRS**: for every `K > 0`, the pairs `(b₁,b₂)`
    whose `a`-averaged fourth moment reaches `Kℓ³` number at most `2ℓ²/K` — the family
    moment converted into an explicit count of exceptional wing-frequency pairs.  This
    averaged statement is the module's entire cash value (see the disclosures: no
    pointwise extraction exists for this family). -/
theorem twinV_markov {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {K : ℝ} (hK : 0 < K) :
    ((Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
        K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4)).card : ℝ)
      ≤ 2 * (ℓ : ℝ) ^ 2 / K := by
  have hl0 : (0 : ℝ) < (ℓ : ℝ) := by
    have h0 : 0 < ℓ := by omega
    exact_mod_cast h0
  have hl3 : (0 : ℝ) < (ℓ : ℝ) ^ 3 := pow_pos hl0 3
  have htotal : ∑ bb : ZMod ℓ × ZMod ℓ, ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4
      ≤ 2 * (ℓ : ℝ) ^ 5 := by
    calc ∑ bb : ZMod ℓ × ZMod ℓ, ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4
        = ∑ a : ZMod ℓ, ∑ bb : ZMod ℓ × ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4 :=
          Finset.sum_comm
      _ = ∑ a : ZMod ℓ, ∑ b₁ : ZMod ℓ, ∑ b₂ : ZMod ℓ, ‖twinV ℓ a b₁ b₂‖ ^ 4 :=
          Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _
      _ ≤ 2 * (ℓ : ℝ) ^ 5 := twinV_family_M4_le h2
  have hcard : ((Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
        K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4)).card : ℝ)
        * (K * (ℓ : ℝ) ^ 3)
      ≤ ∑ bb ∈ Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
          K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4),
          ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4 := by
    have h := Finset.card_nsmul_le_sum
      (Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
        K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4))
      (fun bb => ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4) (K * (ℓ : ℝ) ^ 3)
      (fun bb hbb => (Finset.mem_filter.mp hbb).2)
    rwa [nsmul_eq_mul] at h
  have hsub : ∑ bb ∈ Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
        K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4),
        ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4
      ≤ ∑ bb : ZMod ℓ × ZMod ℓ, ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun bb _ _ => Finset.sum_nonneg fun a _ => by positivity)
  rw [le_div_iff₀ hK]
  refine le_of_mul_le_mul_right ?_ hl3
  calc ((Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
        K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4)).card : ℝ)
        * K * (ℓ : ℝ) ^ 3
      = ((Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
          K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4)).card : ℝ)
          * (K * (ℓ : ℝ) ^ 3) := by ring
    _ ≤ ∑ bb ∈ Finset.univ.filter (fun bb : ZMod ℓ × ZMod ℓ =>
          K * (ℓ : ℝ) ^ 3 ≤ ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4),
          ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4 := hcard
    _ ≤ ∑ bb : ZMod ℓ × ZMod ℓ, ∑ a : ZMod ℓ, ‖twinV ℓ a bb.1 bb.2‖ ^ 4 := hsub
    _ ≤ 2 * (ℓ : ℝ) ^ 5 := htotal
    _ = 2 * (ℓ : ℝ) ^ 2 * (ℓ : ℝ) ^ 3 := by ring

/-! ### Layer 6 — kernel demos (pure-Nat folds; `ZMod` instances stay OUT of every
decide path — house kernel discipline) -/

/-- Pure-Nat twinN4 counter: quadruples of doubly-punctured residues mod `n` matching
    all THREE keys, inverses as `t^(n−2) % n` (Fermat — valid for prime `n`).  The Nat
    clothing of `(twinN4 ℓ).card`. -/
def twinN4CountN (n : ℕ) : ℕ :=
  ((List.range n).map fun x1 =>
    ((List.range n).map fun x2 =>
      ((List.range n).map fun x3 =>
        ((List.range n).filter fun x4 =>
          x1 ≠ 0 && (x1 + 2) % n ≠ 0 && x2 ≠ 0 && (x2 + 2) % n ≠ 0
            && x3 ≠ 0 && (x3 + 2) % n ≠ 0 && x4 ≠ 0 && (x4 + 2) % n ≠ 0
            && (x1 + x2) % n == (x3 + x4) % n
            && (x1 ^ (n - 2) % n + x2 ^ (n - 2) % n) % n
                == (x3 ^ (n - 2) % n + x4 ^ (n - 2) % n) % n
            && (((x1 + 2) % n) ^ (n - 2) % n + ((x2 + 2) % n) ^ (n - 2) % n) % n
                == (((x3 + 2) % n) ^ (n - 2) % n
                  + ((x4 + 2) % n) ^ (n - 2) % n) % n).length).sum).sum).sum

/-- The SAME fold with the third key REMOVED — the two-key control counter that
    exhibits the antipodal fattening the third key cuts. -/
def twinN4TwoKeyCountN (n : ℕ) : ℕ :=
  ((List.range n).map fun x1 =>
    ((List.range n).map fun x2 =>
      ((List.range n).map fun x3 =>
        ((List.range n).filter fun x4 =>
          x1 ≠ 0 && (x1 + 2) % n ≠ 0 && x2 ≠ 0 && (x2 + 2) % n ≠ 0
            && x3 ≠ 0 && (x3 + 2) % n ≠ 0 && x4 ≠ 0 && (x4 + 2) % n ≠ 0
            && (x1 + x2) % n == (x3 + x4) % n
            && (x1 ^ (n - 2) % n + x2 ^ (n - 2) % n) % n
                == (x3 ^ (n - 2) % n + x4 ^ (n - 2) % n) % n).length).sum).sum).sum

/-- Kernel three-key count at `ℓ = 5`: `15 = 3·5 = (ℓ−2)(2ℓ−5)`. -/
theorem twinN4CountN_5 : twinN4CountN 5 = 15 := by decide

/-- Kernel three-key count at `ℓ = 7`: `45 = 5·9 = (ℓ−2)(2ℓ−5)`. -/
theorem twinN4CountN_7 : twinN4CountN 7 = 45 := by decide

/-- Two-key control at `ℓ = 5`: `15` — the SAME as the three-key count.  At `ℓ = 5` the
    third key's cut `(ℓ−3)² − 2(ℓ−3) = (ℓ−3)(ℓ−5)` is EMPTY, so this instance cannot
    witness key-3 necessity (disclosed; the honest witness is `ℓ = 7`). -/
theorem twinN4TwoKeyCountN_5 : twinN4TwoKeyCountN 5 = 15 := by decide

/-- Two-key control at `ℓ = 7`: `53 ≠ 45` — the machine witnesses that the third key
    STRICTLY cuts the two-key antipodal fattening: `53 = 45 − 2(ℓ−3) + (ℓ−3)²` with
    `ℓ − 3 = 4` (the fiber-`(ℓ−3)` stratum restored). -/
theorem twinN4TwoKeyCountN_7 : twinN4TwoKeyCountN 7 = 53 := by decide

/-- Agreement plaque: the Finset count through `twinN4_card` gives the SAME constants
    at both demo instances (exhibited through the closed form, not by a counting
    bijection — house discipline, disclosed in the header). -/
theorem twinN4_agreement :
    (twinN4 5).card = twinN4CountN 5 ∧ (twinN4 7).card = twinN4CountN 7 := by
  haveI h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [twinN4CountN_5, twinN4CountN_7, twinN4_card (by norm_num),
    twinN4_card (by norm_num)]
  exact ⟨rfl, rfl⟩

/-! ### Axiom audit -/

#print axioms twinDom_card
#print axioms twin_fiber
#print axioms twinN4_card_int
#print axioms twinN4_card
#print axioms twinV_family_fourth_full
#print axioms twinV_family_M4_norm
#print axioms twinV_family_M4_le
#print axioms twinV_markov
#print axioms twinN4CountN_5
#print axioms twinN4CountN_7
#print axioms twinN4TwoKeyCountN_5
#print axioms twinN4TwoKeyCountN_7
#print axioms twinN4_agreement

end TypeII
end Geometric
end EuclidsPath
