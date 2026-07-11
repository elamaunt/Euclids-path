/-
  Step00CircleEnergy — the energy/bridge core of the circle pass: the pair-count law,
  the exact energy identity, the Kloosterman bridge, and the family second moment M2.

  Everything here is an EXACT FINITE IDENTITY over a complete range — the full norm-one
  circle of `Quad d ℓ` or the full (punctured) residue line of `ZMod ℓ`.  No estimate,
  no `O(·)`, no unproven bound appears anywhere in this module.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `circle_re_pair_count` — the PAIR-COUNT LAW: the number of pairs `(x, y)` on the
      circle with equal real part is exactly `2ℓ` (each re-fiber is `{x, x̄}`, collapsing
      only at `x = ±1`; delivered through the χ-fiber counts, star-free);
    * `circle_fiber_card` / `hyperbola_fiber_card` — the two χ-fiber counts feeding
      everything: `#{x ∈ circle : x.re = a} = 1 − χ(a² − 1)` (d a nonresidue) and
      `#{y ≠ 0 : y + y⁻¹ = 2a} = 1 + χ(a² − 1)`; their sum is 2 at EVERY `a` — the
      machine-checked "conic + hyperbola = constant" fiber identity;
    * `energy_core` — THE ENERGY IDENTITY, conjugation-free core:
      `Σ_u S(u)·S(−u) = ℓ·2ℓ` where `S = circleSum`; corollary `energy`:
      `Σ_{u≠0} ‖S(u)‖² = ℓ² − 2ℓ − 1`.  This is the mean square of the circle's
      trigonometric sums — the Weil bound's AVERAGE case as a finite identity, no
      cohomology; the pointwise bound `‖S(u)‖ ≤ 2√ℓ` is NOT claimed (see disclosures);
    * `kloos` — the Kloosterman sum `Σ_{x≠0} ψ(ax + bx⁻¹)`, NEW to the pinned mathlib
      (no Kloosterman sums exist anywhere in the pin — grep-verified); basics
      `kloos_zero` (= −1), `kloos_conj`, `kloos_scale` (the `x ↦ a⁻¹x` substitution law
      `kloos a b = kloos 1 (ab)`, the input the M4 module consumes);
    * `circleSum_eq_neg_kloos` — THE KLOOSTERMAN BRIDGE: for `u ≠ 0`,
      `S(u) = −kloos(u/2, u/2)`.  The circle's trigonometry IS Kloosterman territory —
      machine-welded through the fiber identity, not metaphor;
    * `kloos_family_M2` — the FAMILY SECOND MOMENT:
      `Σ_{a≠0} kloos(a,1)·kloos(−a,−1) = ℓ² − ℓ − 1` (the `‖·‖²`-meaningful law, via
      `kloos_conj`; corollary `kloos_family_M2_norm` with norms);
    * `kloos_family_twisted` — the BONUS exact law the numeric probe caught:
      the literal product family `Σ_{a≠0} kloos(a,1)·kloos(−a,1) = −ℓ − 1` — a DIFFERENT
      constant from M2 (the disambiguation is real and machine-checked: the conjugate of
      `kloos a 1` is `kloos (−a) (−1)`, NOT `kloos (−a) 1`);
    * kernel demos: `pairCountN` (pure-Nat re-collision pair counter over the circle),
      `pairCountN 5 2 = 10`, `pairCountN 11 2 = 22` by `decide`, with the Finset pair
      count evaluated to the SAME constants through `circle_re_pair_count` (agreement
      exhibited at the instances, not derived by a bijection — house kernel discipline;
      `Quad` instances stay OUT of every decide path).

  NUMERIC GROUNDING (tools/circle_sum_run1.log, stage D of the circle-volume pass):
  every constant above was CONFIRMED EXACTLY by integer routes at all 302 odd primes
  ℓ ≤ 1999 across 628 (ℓ,d) pairs (two smallest nonresidues per prime + 25 random third
  nonresidues), with exact d-independence of the fiber histogram: pair count `2ℓ`,
  energy `ℓ² − 2ℓ − 1`, bridge per-value, `M2 = ℓ² − ℓ − 1`, twisted `−(ℓ+1)`,
  `kloos(0,1) = −1`.  The identities landed here are the Lean faces of that log.

  DISCLOSURES (mandatory reading before quoting):
    * COMPLETE vs INCOMPLETE — THE WALL'S SIXTH COSTUME.  Every sum in this module is
      COMPLETE: over the full circle, the full residue line, the full family.  The
      serial-twin wall lives on INCOMPLETE sums over windows.  The completed stage-D
      probe (tools/circle_sum_run1.log, T4) measured NO stable re-expression of
      defect-window pair-mode mass in complete Kloosterman data: the high-R² rows are
      interpolation artifacts of clustered census phases, the rest are unstable.  The
      complete/incomplete boundary is the same wall in its sixth costume (after the gap
      bound, the phase covers, the witness chains, the perpetual engine, and the parity
      barrier); nothing here claims to cross it.
    * POINTWISE WEIL NOT CLAIMED.  The pinned mathlib has no Weil bound; the pointwise
      estimates `‖circleSum u‖ ≤ 2√ℓ` and `‖kloos a b‖ ≤ 2√ℓ` are ABSENT and NOT
      claimed.  What is proved is the exact mean square — the average-case statement.
      The family-moment route to the weaker pointwise `‖kloos‖ ≤ 2^{1/4}·ℓ^{3/4}` is the
      M4 module (separate, gated); `kloos_scale` and both M2 laws are its declared
      inputs.
    * `Complex.abs` DEVIATION.  The pin has no `Complex.abs` (removed upstream); all
      absolute values are stated with the norm `‖·‖`, squared over `ℝ`.
    * COUNTER AGREEMENT, NOT COUNTER EQUALITY.  `pairCountN` and the Finset pair count
      are shown to AGREE on the demo instances (both equal 10 resp. 22); the general
      counting bijection between the Nat fold and the `Finset (Quad d ℓ × Quad d ℓ)`
      filter is not formalized.

  ## Anti-vocabulary

  No claim in this file concerns windows, incomplete sums, densities, bounds,
  asymptotics, or the infinitude of anything.  Every theorem is an exact finite
  identity over a complete range; every kernel demo is a single verified instance.
-/
import Mathlib
import EuclidsPath.Engine.Step00ImaginaryCircle

set_option autoImplicit false

namespace EuclidsPath
namespace CircleEnergy

open EuclidsPath.ImaginaryCircle
open QuadraticAlgebra

/-! ### Layer 1 — the circle, its trigonometric sums, and the Kloosterman sum

`ψ := ZMod.stdAddChar ℓ` throughout: the standard additive character
`t ↦ exp(2πi·t/ℓ)`.  The circle is the norm-one Finset of `Quad d ℓ`
(`Step00ImaginaryCircle`); `circleSum u` is its `u`-th trigonometric sum along the
real coordinate; `kloos a b` is the classical Kloosterman sum — NEW to the pinned
mathlib (no Kloosterman sums exist in the pin). -/

/-- The imaginary circle as a `Finset`: the norm-one points of `Quad d ℓ`.
    `circle_card_eq` gives `#circle = ℓ + 1` (via `ImaginaryCircle.circle_card`). -/
def circle (d ℓ : ℕ) [NeZero ℓ] : Finset (Quad d ℓ) :=
  Finset.univ.filter fun x => qnorm x = 1

theorem mem_circle {d ℓ : ℕ} [NeZero ℓ] {x : Quad d ℓ} :
    x ∈ circle d ℓ ↔ qnorm x = 1 := by
  unfold circle
  simp

/-- The circle has `ℓ + 1` points (restatement of `ImaginaryCircle.circle_card` on the
    `circle` Finset). -/
theorem circle_card_eq {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) : (circle d ℓ).card = ℓ + 1 := by
  unfold circle
  exact circle_card h2 hd

/-- The circle's trigonometric sum along the real coordinate:
    `circleSum d u = Σ_{x ∈ circle} ψ(u · x.re)`. -/
noncomputable def circleSum (d : ℕ) {ℓ : ℕ} [NeZero ℓ] (u : ZMod ℓ) : ℂ :=
  ∑ x ∈ circle d ℓ, ZMod.stdAddChar (u * x.re)

theorem circleSum_def {d ℓ : ℕ} [NeZero ℓ] (u : ZMod ℓ) :
    circleSum d u = ∑ x ∈ circle d ℓ, ZMod.stdAddChar (u * x.re) := rfl

/-- **The Kloosterman sum** `kloos a b = Σ_{x ≠ 0} ψ(a·x + b·x⁻¹)` over `ZMod ℓ`
    (`x⁻¹` is `ZMod.inv`, the field inverse for prime `ℓ`).  NEW to the pinned
    mathlib: the pin contains no Kloosterman sums. -/
noncomputable def kloos {ℓ : ℕ} [NeZero ℓ] (a b : ZMod ℓ) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
    ZMod.stdAddChar (a * x + b * x⁻¹)

theorem kloos_def {ℓ : ℕ} [NeZero ℓ] (a b : ZMod ℓ) :
    kloos a b = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar (a * x + b * x⁻¹) := rfl

/-- `2 ≠ 0` in `ZMod ℓ` for an odd prime `ℓ` (characteristic route). -/
private theorem two_ne_zero_zmod {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (2 : ZMod ℓ) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)

/-- Conjugation of the standard character is negation of the argument:
    `conj ψ(x) = ψ(−x)` — `ψ` takes values on the unit circle, where the conjugate is
    the inverse (`RCLike.inv_eq_conj`), and an `AddChar` maps negatives to inverses. -/
theorem stdAddChar_conj {N : ℕ} [NeZero N] (x : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have h1 : ‖ZMod.stdAddChar x‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  rw [← RCLike.inv_eq_conj h1, ← AddChar.map_neg_eq_inv]

/-- The conjugate of `circleSum u` is `circleSum (−u)` — the real coordinate is real,
    so conjugation only flips the frequency. -/
theorem circleSum_conj {d ℓ : ℕ} [NeZero ℓ] (u : ZMod ℓ) :
    (starRingEnd ℂ) (circleSum d u) = circleSum d (-u) := by
  rw [circleSum_def, circleSum_def, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [stdAddChar_conj]
  congr 1
  ring

/-- **Conjugation law of the Kloosterman sum**: `conj (kloos a b) = kloos (−a) (−b)` —
    NOT `kloos (−a) b`.  This is the disambiguation the numeric stage registered before
    measurement; it is what makes `kloos_family_M2` the `‖·‖²`-meaningful family law
    and `kloos_family_twisted` a genuinely different constant. -/
theorem kloos_conj {ℓ : ℕ} [NeZero ℓ] (a b : ZMod ℓ) :
    (starRingEnd ℂ) (kloos a b) = kloos (-a) (-b) := by
  rw [kloos_def, kloos_def, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [stdAddChar_conj]
  congr 1
  ring

/-! ### Layer 2 — the two χ-fiber counts (the engine of both the pair count and the
bridge)

`χ = quadraticChar (ZMod ℓ)`.  The circle fiber over a real part `a` is counted by the
square roots of `(a² − 1)/d` (`quadraticChar_card_sqrts`), the hyperbola (trace) fiber
over `2a` by the square roots of `a² − 1`; a nonresidue `d` flips the sign, so the two
counts sum to `2` at EVERY `a` — including `a = ±1`, where `χ(0) = 0` makes both
fibers equal to `1`. -/

/-- **Circle fiber count**: for a nonresidue `d`,
    `#{x ∈ circle : x.re = a} = 1 − χ(a² − 1)` (as integers).
    Route: the fiber is in bijection with `{b : b² = (a² − 1)·d⁻¹}` via `x ↦ x.im`,
    counted by `quadraticChar_card_sqrts`; `χ(d⁻¹) = χ(d) = −1` flips the sign. -/
theorem circle_fiber_card {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) (a : ZMod ℓ) :
    ((((circle d ℓ).filter fun x => x.re = a).card : ℤ))
      = 1 - quadraticChar (ZMod ℓ) (a ^ 2 - 1) := by
  have hchar : ringChar (ZMod ℓ) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hd0 : (d : ZMod ℓ) ≠ 0 := ne_zero_of_nonsquare hd
  -- the fiber is the square-root set of (a² − 1)·d⁻¹, transported along `x ↦ x.im`
  have hbij : ((circle d ℓ).filter fun x => x.re = a).card
      = (Finset.univ.filter fun b : ZMod ℓ =>
          b ^ 2 = (a ^ 2 - 1) * (d : ZMod ℓ)⁻¹).card := by
    refine Finset.card_bij' (fun x _ => x.im) (fun b _ => (⟨a, b⟩ : Quad d ℓ))
      ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have hq : qnorm x = 1 := mem_circle.mp hx1
      simp only [qnorm] at hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hx2]
      have hkey : x.re ^ 2 - 1 = (d : ZMod ℓ) * x.im ^ 2 := by linear_combination hq
      rw [hkey, mul_comm ((d : ZMod ℓ)) (x.im ^ 2), mul_assoc,
        mul_inv_cancel₀ hd0, mul_one]
    · intro b hb
      have hb2 : b ^ 2 = (a ^ 2 - 1) * (d : ZMod ℓ)⁻¹ := (Finset.mem_filter.mp hb).2
      refine Finset.mem_filter.mpr ⟨mem_circle.mpr ?_, rfl⟩
      show a ^ 2 - (d : ZMod ℓ) * b ^ 2 = 1
      calc a ^ 2 - (d : ZMod ℓ) * b ^ 2
          = a ^ 2 - (d : ZMod ℓ) * ((a ^ 2 - 1) * (d : ZMod ℓ)⁻¹) := by rw [hb2]
        _ = a ^ 2 - (a ^ 2 - 1) * ((d : ZMod ℓ) * (d : ZMod ℓ)⁻¹) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ hd0]; ring
    · intro x hx
      have hx2 : x.re = a := (Finset.mem_filter.mp hx).2
      ext
      · exact hx2.symm
      · rfl
    · intro b _
      rfl
  -- the square-root count, in χ clothes
  have hsq := quadraticChar_card_sqrts hchar ((a ^ 2 - 1) * (d : ZMod ℓ)⁻¹)
  simp only [Set.toFinset_setOf] at hsq
  -- χ((a² − 1)·d⁻¹) = −χ(a² − 1) since χ(d⁻¹) = χ(d) = −1
  have hchid : quadraticChar (ZMod ℓ) ((d : ZMod ℓ)) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hd
  have hdinv : quadraticChar (ZMod ℓ) ((d : ZMod ℓ)⁻¹) = -1 := by
    have hm : quadraticChar (ZMod ℓ) ((d : ZMod ℓ) * (d : ZMod ℓ)⁻¹) = 1 := by
      rw [mul_inv_cancel₀ hd0, MulChar.map_one]
    rw [map_mul, hchid] at hm
    linarith
  have hchi : quadraticChar (ZMod ℓ) ((a ^ 2 - 1) * (d : ZMod ℓ)⁻¹)
      = - quadraticChar (ZMod ℓ) (a ^ 2 - 1) := by
    rw [map_mul, hdinv]
    ring
  rw [hbij, hsq, hchi]
  ring

/-- **Hyperbola (trace) fiber count**:
    `#{y ≠ 0 : y + y⁻¹ = 2a} = 1 + χ(a² − 1)` (as integers).
    Route: `y + y⁻¹ = 2a ⟺ (y − a)² = a² − 1` (multiply by the unit `y`); the fiber is
    in bijection with the square roots of `a² − 1` via `y ↦ y − a`. -/
theorem hyperbola_fiber_card {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) (a : ZMod ℓ) :
    (((Finset.univ.filter fun y : ZMod ℓ => y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℤ))
      = quadraticChar (ZMod ℓ) (a ^ 2 - 1) + 1 := by
  have hchar : ringChar (ZMod ℓ) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hbij : (Finset.univ.filter fun y : ZMod ℓ => y ≠ 0 ∧ y + y⁻¹ = 2 * a).card
      = (Finset.univ.filter fun z : ZMod ℓ => z ^ 2 = a ^ 2 - 1).card := by
    refine Finset.card_bij' (fun y _ => y - a) (fun z _ => z + a) ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨-, hy0, hyt⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h1 : y * (y + y⁻¹) = y ^ 2 + 1 := by
        rw [mul_add, mul_inv_cancel₀ hy0]
        ring
      have h2' : y ^ 2 + 1 = 2 * a * y := by rw [← h1, hyt]; ring
      linear_combination h2'
    · intro z hz
      have hz2 : z ^ 2 = a ^ 2 - 1 := (Finset.mem_filter.mp hz).2
      have hy0 : z + a ≠ 0 := by
        intro h0
        have hz' : z = -a := by linear_combination h0
        rw [hz'] at hz2
        exact one_ne_zero (α := ZMod ℓ) (by linear_combination hz2)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0, ?_⟩
      have hkey : (z + a) * ((z + a) + (z + a)⁻¹ - 2 * a) = 0 := by
        rw [mul_sub, mul_add, mul_inv_cancel₀ hy0]
        linear_combination hz2
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hy0
      · linear_combination h
    · intro y _
      ring
    · intro z _
      ring
  have hsq := quadraticChar_card_sqrts hchar (a ^ 2 - 1)
  simp only [Set.toFinset_setOf] at hsq
  rw [hbij, hsq]

/-- The two fibers of the SAME value `χ(a² − 1)` sum to `2` at every `a` — the conic
    and the hyperbola share the line `ZMod ℓ` exactly.  (Stated over `ℤ`; this is the
    identity the bridge consumes.) -/
theorem fiber_sum_eq_two {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) (a : ZMod ℓ) :
    ((((circle d ℓ).filter fun x => x.re = a).card : ℤ))
      + (((Finset.univ.filter fun y : ZMod ℓ => y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℤ))
      = 2 := by
  rw [circle_fiber_card h2 hd a, hyperbola_fiber_card h2 a]
  ring

/-! ### Layer 3 — the pair-count law -/

/-- The im-zero locus of the circle is exactly `{±1}`: two points (counted through the
    square roots of `1`, χ-uniformly with the fiber counts; no nonresidue hypothesis is
    needed — the poles are `d`-blind). -/
theorem circle_im_zero_card {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ((circle d ℓ).filter fun x => x.im = 0).card = 2 := by
  have hchar : ringChar (ZMod ℓ) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hbij : ((circle d ℓ).filter fun x => x.im = 0).card
      = (Finset.univ.filter fun r : ZMod ℓ => r ^ 2 = 1).card := by
    refine Finset.card_bij' (fun x _ => x.re) (fun r _ => (⟨r, 0⟩ : Quad d ℓ))
      ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have hq : qnorm x = 1 := mem_circle.mp hx1
      simp only [qnorm] at hq
      rw [hx2] at hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      linear_combination hq
    · intro r hr
      have hr2 : r ^ 2 = 1 := (Finset.mem_filter.mp hr).2
      refine Finset.mem_filter.mpr ⟨mem_circle.mpr ?_, rfl⟩
      show r ^ 2 - (d : ZMod ℓ) * (0 : ZMod ℓ) ^ 2 = 1
      rw [hr2]
      ring
    · intro x hx
      have hx2 : x.im = 0 := (Finset.mem_filter.mp hx).2
      ext
      · rfl
      · exact hx2.symm
    · intro r _
      rfl
  have hsq := quadraticChar_card_sqrts hchar (1 : ZMod ℓ)
  simp only [Set.toFinset_setOf] at hsq
  rw [MulChar.map_one] at hsq
  have h2' : ((Finset.univ.filter fun r : ZMod ℓ => r ^ 2 = 1).card : ℤ) = 2 := by
    rw [hsq]
    norm_num
  rw [hbij]
  exact_mod_cast h2'

/-- **THE PAIR-COUNT LAW**: the circle has exactly `2ℓ` ordered pairs with equal real
    part.  Route: the fiber over `x.re` has size `1 − χ(x.re² − 1) = 1 − χ(d·x.im²)`,
    which is `1` when `x.im = 0` (χ(0) = 0, the two poles `±1`) and `2` otherwise
    (χ(d)·χ(square) = −1); summing over the `ℓ + 1` circle points:
    `2·(ℓ + 1) − 2 = 2ℓ`.  Confirmed exactly at all 302 odd primes ≤ 1999
    (tools/circle_sum_run1.log, T1a). -/
theorem circle_re_pair_count {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    (((circle d ℓ) ×ˢ (circle d ℓ)).filter fun p => p.1.re = p.2.re).card
      = 2 * ℓ := by
  -- the pair count is the sum of re-fiber sizes over the circle
  have hsplit : (((circle d ℓ) ×ˢ (circle d ℓ)).filter
        fun p => p.1.re = p.2.re).card
      = ∑ x ∈ circle d ℓ, ((circle d ℓ).filter fun y => y.re = x.re).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun y _ => if_congr eq_comm rfl rfl
  -- each fiber is 1 at the poles (x.im = 0) and 2 elsewhere
  have hfib : ∀ x ∈ circle d ℓ,
      ((circle d ℓ).filter fun y => y.re = x.re).card
        = if x.im = 0 then 1 else 2 := by
    intro x hx
    have hq : qnorm x = 1 := mem_circle.mp hx
    simp only [qnorm] at hq
    have harg : x.re ^ 2 - 1 = (d : ZMod ℓ) * x.im ^ 2 := by linear_combination hq
    have hcard := circle_fiber_card h2 hd x.re
    rw [harg] at hcard
    by_cases him : x.im = 0
    · rw [if_pos him]
      rw [him] at hcard
      rw [show (d : ZMod ℓ) * (0 : ZMod ℓ) ^ 2 = 0 by ring, quadraticChar_zero]
        at hcard
      have h1 : ((((circle d ℓ).filter fun y => y.re = x.re).card : ℤ)) = 1 := by
        rw [hcard]
        norm_num
      exact_mod_cast h1
    · rw [if_neg him]
      have hchi : quadraticChar (ZMod ℓ) ((d : ZMod ℓ) * x.im ^ 2) = -1 := by
        rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hd,
          quadraticChar_sq_one' him]
        ring
      rw [hchi] at hcard
      have h1 : ((((circle d ℓ).filter fun y => y.re = x.re).card : ℤ)) = 2 := by
        rw [hcard]
        norm_num
      exact_mod_cast h1
  rw [hsplit, Finset.sum_congr rfl hfib, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have h0 : ((circle d ℓ).filter fun x => x.im = 0).card = 2 :=
    circle_im_zero_card h2
  have htot := Finset.card_filter_add_card_filter_not (s := circle d ℓ)
    (fun x => x.im = 0)
  have hall : (circle d ℓ).card = ℓ + 1 := circle_card_eq h2 hd
  omega

/-! ### Layer 4 — THE ENERGY IDENTITY

The mean square of the circle's trigonometric sums is exactly `~ℓ` — the Weil bound's
AVERAGE case as a finite identity, no cohomology.  The pointwise Weil bound `2√ℓ` is
absent from the pin and NOT claimed.  Confirmed exactly at all 302 odd primes ≤ 1999
by the integer route `ℓ·(pair count) − (ℓ+1)²` (tools/circle_sum_run1.log, T1b). -/

/-- **The energy identity, conjugation-free core**:
    `Σ_u circleSum(u)·circleSum(−u) = ℓ·(2ℓ)`.
    Route: expand over circle pairs; `Σ_u ψ(u(x.re − y.re))` is `ℓ` on the re-diagonal
    and `0` off it (`AddChar.sum_mulShift`, primitivity of `ψ`); the diagonal is the
    pair count `2ℓ`. -/
theorem energy_core {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    ∑ u : ZMod ℓ, circleSum d u * circleSum d (-u) = (ℓ : ℂ) * (2 * ℓ) := by
  calc ∑ u : ZMod ℓ, circleSum d u * circleSum d (-u)
      = ∑ u : ZMod ℓ, ∑ x ∈ circle d ℓ, ∑ y ∈ circle d ℓ,
          ZMod.stdAddChar (u * (x.re - y.re)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [circleSum_def, circleSum_def, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = ∑ x ∈ circle d ℓ, ∑ u : ZMod ℓ, ∑ y ∈ circle d ℓ,
          ZMod.stdAddChar (u * (x.re - y.re)) := Finset.sum_comm
    _ = ∑ x ∈ circle d ℓ, ∑ y ∈ circle d ℓ, ∑ u : ZMod ℓ,
          ZMod.stdAddChar (u * (x.re - y.re)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ circle d ℓ, ∑ y ∈ circle d ℓ,
          if x.re = y.re then (ℓ : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar ℓ), ZMod.card]
        by_cases hxy : x.re = y.re
        · rw [if_pos (sub_eq_zero.mpr hxy), if_pos hxy]
        · rw [if_neg (fun h => hxy (sub_eq_zero.mp h)), if_neg hxy]
          simp
    _ = ∑ x ∈ circle d ℓ, ∑ y ∈ circle d ℓ,
          (fun p : Quad d ℓ × Quad d ℓ =>
            if p.1.re = p.2.re then (ℓ : ℂ) else 0) (x, y) := rfl
    _ = ∑ p ∈ (circle d ℓ) ×ˢ (circle d ℓ),
          if p.1.re = p.2.re then (ℓ : ℂ) else 0 :=
        (Finset.sum_product (circle d ℓ) (circle d ℓ)
          (fun p => if p.1.re = p.2.re then (ℓ : ℂ) else 0)).symm
    _ = (ℓ : ℂ) * (2 * ℓ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          circle_re_pair_count h2 hd, nsmul_eq_mul]
        push_cast
        ring

/-- The zero mode is the full circle: `circleSum 0 = ℓ + 1`. -/
theorem circleSum_zero {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    circleSum d (0 : ZMod ℓ) = (ℓ : ℂ) + 1 := by
  rw [circleSum_def]
  have h1 : ∀ x ∈ circle d ℓ, ZMod.stdAddChar ((0 : ZMod ℓ) * x.re) = 1 :=
    fun x _ => by rw [zero_mul, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, circle_card_eq h2 hd,
    nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **THE ENERGY IDENTITY**: `Σ_{u ≠ 0} ‖circleSum u‖² = ℓ² − 2ℓ − 1`.
    The mean square of the nonzero modes is exactly `ℓ − 2 − 1/ℓ` per mode — the Weil
    bound's average case as a finite identity.  Pointwise Weil (`2√ℓ`) is NOT claimed
    (absent from the pin, disclosed in the header). -/
theorem energy {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    ∑ u ∈ Finset.univ.erase (0 : ZMod ℓ), ‖circleSum d u‖ ^ 2
      = (ℓ : ℝ) ^ 2 - 2 * ℓ - 1 := by
  have hsq : ∀ u : ZMod ℓ, circleSum d u * circleSum d (-u)
      = ((‖circleSum d u‖ ^ 2 : ℝ) : ℂ) := fun u => by
    rw [← circleSum_conj (d := d) u, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ∑ u ∈ Finset.univ.erase (0 : ZMod ℓ), ((‖circleSum d u‖ ^ 2 : ℝ) : ℂ)
      = (ℓ : ℂ) ^ 2 - 2 * ℓ - 1 := by
    have hfull : ∑ u : ZMod ℓ, ((‖circleSum d u‖ ^ 2 : ℝ) : ℂ)
        = (ℓ : ℂ) * (2 * ℓ) :=
      (Finset.sum_congr rfl fun u _ => (hsq u).symm).trans (energy_core h2 hd)
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun u : ZMod ℓ => ((‖circleSum d u‖ ^ 2 : ℝ) : ℂ))
      (Finset.mem_univ (0 : ZMod ℓ))
    have h0 : ((‖circleSum d (0 : ZMod ℓ)‖ ^ 2 : ℝ) : ℂ) = ((ℓ : ℂ) + 1) ^ 2 := by
      rw [circleSum_zero h2 hd,
        show ((ℓ : ℂ) + 1) = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring,
        RCLike.norm_natCast]
      push_cast
      ring
    rw [h0, hfull] at hsplit
    linear_combination hsplit
  exact_mod_cast key

/-! ### Layer 5 — THE KLOOSTERMAN BRIDGE

The circle's trigonometry IS Kloosterman territory — machine-welded, not metaphor:
grouping the circle by real part and the punctured line by trace, the two χ-fiber
counts (Layer 2) sum to `2`, and the full-line frequency sum vanishes for `u ≠ 0`, so
the circle sum and the Kloosterman sum are exact negatives.  Confirmed per-value at
all 302 odd primes ≤ 1999 (tools/circle_sum_run1.log, T1c). -/

/-- **THE KLOOSTERMAN BRIDGE**: for `u ≠ 0`,
    `circleSum u = −kloos(u·2⁻¹, u·2⁻¹)`.
    Route: fiber both sums over `a ∈ ZMod ℓ` (real part on the circle side, half-trace
    on the hyperbola side); the fibers carry `1 − χ(a² − 1)` resp. `1 + χ(a² − 1)`
    copies of `ψ(ua)`; their sum `2·Σ_a ψ(ua)` vanishes by orthogonality. -/
theorem circleSum_eq_neg_kloos {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) {u : ZMod ℓ} (hu : u ≠ 0) :
    circleSum d u = - kloos (u * (2 : ZMod ℓ)⁻¹) (u * (2 : ZMod ℓ)⁻¹) := by
  have h20 : (2 : ZMod ℓ) ≠ 0 := two_ne_zero_zmod h2
  -- the circle side, fibered by real part
  have hC : circleSum d u = ∑ a : ZMod ℓ,
      (((circle d ℓ).filter fun x => x.re = a).card : ℂ)
        * ZMod.stdAddChar (u * a) := by
    calc circleSum d u
        = ∑ a : ZMod ℓ, ∑ x ∈ (circle d ℓ).filter (fun x => x.re = a),
            ZMod.stdAddChar (u * a) := by
          rw [circleSum_def]
          exact (Finset.sum_fiberwise' (circle d ℓ) (fun x => x.re)
            (fun a => ZMod.stdAddChar (u * a))).symm
      _ = ∑ a : ZMod ℓ, (((circle d ℓ).filter fun x => x.re = a).card : ℂ)
            * ZMod.stdAddChar (u * a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the trace fibers of the punctured line, in the hyperbola normal form
  have hfeq : ∀ a : ZMod ℓ,
      ((Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0)).filter
          fun y => (2 : ZMod ℓ)⁻¹ * (y + y⁻¹) = a)
        = Finset.univ.filter fun y : ZMod ℓ => y ≠ 0 ∧ y + y⁻¹ = 2 * a := by
    intro a
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun y _ => ?_
    constructor
    · rintro ⟨hy0, hya⟩
      refine ⟨hy0, ?_⟩
      calc y + y⁻¹ = ((2 : ZMod ℓ) * (2 : ZMod ℓ)⁻¹) * (y + y⁻¹) := by
            rw [mul_inv_cancel₀ h20, one_mul]
        _ = 2 * ((2 : ZMod ℓ)⁻¹ * (y + y⁻¹)) := by ring
        _ = 2 * a := by rw [hya]
    · rintro ⟨hy0, hya⟩
      exact ⟨hy0, by rw [hya, ← mul_assoc, inv_mul_cancel₀ h20, one_mul]⟩
  -- the Kloosterman side, fibered by half-trace
  have hK : kloos (u * (2 : ZMod ℓ)⁻¹) (u * (2 : ZMod ℓ)⁻¹) = ∑ a : ZMod ℓ,
      ((Finset.univ.filter fun y : ZMod ℓ => y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℂ)
        * ZMod.stdAddChar (u * a) := by
    calc kloos (u * (2 : ZMod ℓ)⁻¹) (u * (2 : ZMod ℓ)⁻¹)
        = ∑ y ∈ Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0),
            ZMod.stdAddChar (u * ((2 : ZMod ℓ)⁻¹ * (y + y⁻¹))) := by
          rw [kloos_def]
          refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          ring
      _ = ∑ a : ZMod ℓ, ∑ y ∈ (Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0)).filter
            (fun y => (2 : ZMod ℓ)⁻¹ * (y + y⁻¹) = a),
            ZMod.stdAddChar (u * a) :=
          (Finset.sum_fiberwise' (Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0))
            (fun y => (2 : ZMod ℓ)⁻¹ * (y + y⁻¹))
            (fun a => ZMod.stdAddChar (u * a))).symm
      _ = ∑ a : ZMod ℓ,
            ((Finset.univ.filter fun y : ZMod ℓ =>
                y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℂ)
              * ZMod.stdAddChar (u * a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hfeq a, Finset.sum_const, nsmul_eq_mul]
  -- the two fibered sums cancel: fibers sum to 2, and Σ_a ψ(ua) = 0 for u ≠ 0
  have hsum : circleSum d u
      + kloos (u * (2 : ZMod ℓ)⁻¹) (u * (2 : ZMod ℓ)⁻¹) = 0 := by
    rw [hC, hK, ← Finset.sum_add_distrib]
    have hterm : ∀ a ∈ (Finset.univ : Finset (ZMod ℓ)),
        (((circle d ℓ).filter fun x => x.re = a).card : ℂ)
            * ZMod.stdAddChar (u * a)
          + ((Finset.univ.filter fun y : ZMod ℓ =>
              y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℂ) * ZMod.stdAddChar (u * a)
        = 2 * ZMod.stdAddChar (u * a) := by
      intro a _
      rw [← add_mul]
      congr 1
      exact_mod_cast fiber_sum_eq_two h2 hd a
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hall : ∑ a : ZMod ℓ, ZMod.stdAddChar (u * a) = 0 := by
      have h := AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar ℓ)
      rw [if_neg hu, Nat.cast_zero] at h
      rw [← h]
      exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]
    rw [hall, mul_zero]
  exact eq_neg_of_add_eq_zero_left hsum

/-! ### Layer 6 — Kloosterman basics and THE FAMILY SECOND MOMENT M2

Two exact family laws, both confirmed at all 302 odd primes ≤ 1999
(tools/circle_sum_run1.log, T1d): the `‖·‖²`-meaningful second moment
`Σ_{a≠0} kloos(a,1)·kloos(−a,−1) = ℓ² − ℓ − 1`, and the twisted product family
`Σ_{a≠0} kloos(a,1)·kloos(−a,1) = −ℓ − 1` — a DIFFERENT constant, because
`conj (kloos a 1) = kloos (−a) (−1)`, not `kloos (−a) 1` (`kloos_conj`).  The numeric
stage registered this disambiguation BEFORE measurement; both laws land here. -/

/-- `Σ_{x ≠ 0} ψ(w·x⁻¹) = −1` for `w ≠ 0`: reindex by `x ↦ x⁻¹` and split off the
    zero term of the full-line sum (orthogonality). -/
private theorem sum_psi_inv {ℓ : ℕ} [Fact ℓ.Prime] {w : ZMod ℓ} (hw : w ≠ 0) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar (w * x⁻¹) = -1 := by
  have hre : ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar (w * x⁻¹)
      = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
        ZMod.stdAddChar (w * x) := by
    refine Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) ?_ ?_ ?_ ?_ ?_
    · exact fun x hx => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, inv_ne_zero (Finset.mem_filter.mp hx).2⟩
    · exact fun x hx => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, inv_ne_zero (Finset.mem_filter.mp hx).2⟩
    · exact fun x _ => inv_inv x
    · exact fun x _ => inv_inv x
    · exact fun x _ => rfl
  rw [hre]
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun x : ZMod ℓ => ZMod.stdAddChar (w * x)) (Finset.mem_univ (0 : ZMod ℓ))
  have hall : ∑ x : ZMod ℓ, ZMod.stdAddChar (w * x) = 0 := by
    have h := AddChar.sum_mulShift w (ZMod.isPrimitive_stdAddChar ℓ)
    rw [if_neg hw, Nat.cast_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  rw [hall, mul_zero, AddChar.map_zero_eq_one] at hsplit
  rw [Finset.filter_ne']
  linear_combination hsplit

/-- `kloos 0 b = −1` for `b ≠ 0` — the degenerate frequency is a Ramanujan-type sum
    over the punctured line.  (Feeds the `a = 0` term of both family laws.) -/
theorem kloos_zero {ℓ : ℕ} [Fact ℓ.Prime] {b : ZMod ℓ} (hb : b ≠ 0) :
    kloos (0 : ZMod ℓ) b = -1 := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar ((0 : ZMod ℓ) * x + b * x⁻¹)
        = ZMod.stdAddChar (b * x⁻¹) :=
    fun x _ => by rw [zero_mul, zero_add]
  rw [kloos_def, Finset.sum_congr rfl h]
  exact sum_psi_inv hb

/-- **The scaling law** `kloos a b = kloos 1 (a·b)` for `a ≠ 0` — the substitution
    `x ↦ a⁻¹x`.  This is the normalization the M4 module consumes: every nonzero
    frequency pair reduces to the diagonal family `kloos 1 m`. -/
theorem kloos_scale {ℓ : ℕ} [Fact ℓ.Prime] {a : ZMod ℓ} (ha : a ≠ 0) (b : ZMod ℓ) :
    kloos a b = kloos 1 (a * b) := by
  rw [kloos_def, kloos_def]
  refine Finset.sum_nbij' (fun x => a * x) (fun z => a⁻¹ * z) ?_ ?_ ?_ ?_ ?_
  · exact fun x hx => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, mul_ne_zero ha (Finset.mem_filter.mp hx).2⟩
  · exact fun z hz => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, mul_ne_zero (inv_ne_zero ha) (Finset.mem_filter.mp hz).2⟩
  · intro x _
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  · intro z _
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · intro x _
    congr 1
    rw [one_mul, mul_inv]
    rw [show a * b * (a⁻¹ * x⁻¹) = (a * a⁻¹) * (b * x⁻¹) by ring,
      mul_inv_cancel₀ ha, one_mul]

/-- The common engine of both family laws: for any twist `c`,
    `Σ_a kloos(a,1)·kloos(−a,c) = ℓ · Σ_{x≠0} ψ((1+c)·x⁻¹)` — orthogonality in the
    family variable `a` collapses the double unit sum to its diagonal `x = y`. -/
private theorem kloos_mul_full {ℓ : ℕ} [Fact ℓ.Prime] (c : ZMod ℓ) :
    ∑ a : ZMod ℓ, kloos a 1 * kloos (-a) c
      = (ℓ : ℂ) * ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
          ZMod.stdAddChar ((1 + c) * x⁻¹) := by
  calc ∑ a : ZMod ℓ, kloos a 1 * kloos (-a) c
      = ∑ a : ZMod ℓ, ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
          ∑ y ∈ Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0),
            ZMod.stdAddChar (a * (x - y))
              * ZMod.stdAddChar (x⁻¹ + c * y⁻¹) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [kloos_def, kloos_def, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0), ∑ a : ZMod ℓ,
          ∑ y ∈ Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0),
            ZMod.stdAddChar (a * (x - y))
              * ZMod.stdAddChar (x⁻¹ + c * y⁻¹) := Finset.sum_comm
    _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
          ∑ y ∈ Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0), ∑ a : ZMod ℓ,
            ZMod.stdAddChar (a * (x - y))
              * ZMod.stdAddChar (x⁻¹ + c * y⁻¹) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
          ∑ y ∈ Finset.univ.filter (fun y : ZMod ℓ => y ≠ 0),
            (if x - y = 0 then (ℓ : ℂ) else 0)
              * ZMod.stdAddChar (x⁻¹ + c * y⁻¹) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar ℓ),
          ZMod.card]
        congr 1
        by_cases hxy : x - y = 0
        · rw [if_pos hxy, if_pos hxy]
        · rw [if_neg hxy, if_neg hxy]
          simp
    _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
          (ℓ : ℂ) * ZMod.stdAddChar (x⁻¹ + c * x⁻¹) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.sum_eq_single x]
        · rw [sub_self, if_pos rfl]
        · intro y _ hyx
          rw [if_neg (sub_ne_zero_of_ne (Ne.symm hyx)), zero_mul]
        · intro hxx
          exact absurd hx hxx
    _ = (ℓ : ℂ) * ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
          ZMod.stdAddChar ((1 + c) * x⁻¹) := by
        rw [← Finset.mul_sum]
        refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
        congr 1
        ring

/-- **THE FAMILY SECOND MOMENT M2**:
    `Σ_{a ≠ 0} kloos(a,1)·kloos(−a,−1) = ℓ² − ℓ − 1`.
    This is the `‖·‖²`-meaningful law (`kloos_conj`: the second factor is the
    conjugate of the first).  Integer route: the full family sum is `ℓ(ℓ − 1)` by
    orthogonality (the `(1 + c)`-twist vanishes at `c = −1`), minus the `a = 0` term
    `kloos(0,1)·kloos(0,−1) = (−1)·(−1) = 1`. -/
theorem kloos_family_M2 {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ a ∈ Finset.univ.erase (0 : ZMod ℓ), kloos a 1 * kloos (-a) (-1)
      = (ℓ : ℂ) ^ 2 - ℓ - 1 := by
  have hfull := kloos_mul_full (ℓ := ℓ) (-1)
  have hcard : (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)).card = ℓ - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  have hone : ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar ((1 + (-1) : ZMod ℓ) * x⁻¹) = (ℓ : ℂ) - 1 := by
    have hz : ∀ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
        ZMod.stdAddChar ((1 + (-1) : ZMod ℓ) * x⁻¹) = 1 := fun x _ => by
      rw [show ((1 : ZMod ℓ) + -1) = 0 by ring, zero_mul, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl hz, Finset.sum_const, hcard, nsmul_eq_mul, mul_one,
      Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  rw [hone] at hfull
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun a : ZMod ℓ => kloos a 1 * kloos (-a) (-1)) (Finset.mem_univ (0 : ZMod ℓ))
  have h0 : kloos (0 : ZMod ℓ) 1 * kloos (-(0 : ZMod ℓ)) (-1) = 1 := by
    rw [neg_zero, kloos_zero one_ne_zero,
      kloos_zero (neg_ne_zero.mpr one_ne_zero)]
    ring
  rw [h0, hfull] at hsplit
  linear_combination hsplit

/-- The `‖·‖²`-corollary of M2: `Σ_{a ≠ 0} ‖kloos(a,1)‖² = ℓ² − ℓ − 1` — the family
    mean square of Kloosterman sums is exactly `~ℓ` per member, the average-case
    statement of the (unclaimed) pointwise Weil bound. -/
theorem kloos_family_M2_norm {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ a ∈ Finset.univ.erase (0 : ZMod ℓ), ‖kloos a 1‖ ^ 2
      = (ℓ : ℝ) ^ 2 - ℓ - 1 := by
  have hsq : ∀ a : ZMod ℓ, kloos a 1 * kloos (-a) (-1)
      = ((‖kloos a 1‖ ^ 2 : ℝ) : ℂ) := fun a => by
    rw [← kloos_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ∑ a ∈ Finset.univ.erase (0 : ZMod ℓ), ((‖kloos a 1‖ ^ 2 : ℝ) : ℂ)
      = (ℓ : ℂ) ^ 2 - ℓ - 1 :=
    (Finset.sum_congr rfl fun a _ => (hsq a).symm).trans (kloos_family_M2 h2)
  exact_mod_cast key

/-- **THE TWISTED FAMILY LAW (the bonus identity the probe caught)**:
    `Σ_{a ≠ 0} kloos(a,1)·kloos(−a,1) = −ℓ − 1`.
    The literal product family — same shape as M2 but WITHOUT the conjugation flip on
    the second index — is a different exact constant.  Integer route: the diagonal
    twist is now `(1 + 1)·x⁻¹ ≠ 0`, so the full family sum is `ℓ·(−1)` by
    `sum_psi_inv`, minus the same `a = 0` term `1`. -/
theorem kloos_family_twisted {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ a ∈ Finset.univ.erase (0 : ZMod ℓ), kloos a 1 * kloos (-a) 1
      = -(ℓ : ℂ) - 1 := by
  have h11 : (1 + 1 : ZMod ℓ) ≠ 0 := by
    rw [one_add_one_eq_two]
    exact two_ne_zero_zmod h2
  have hfull := kloos_mul_full (ℓ := ℓ) 1
  rw [sum_psi_inv h11] at hfull
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun a : ZMod ℓ => kloos a 1 * kloos (-a) 1) (Finset.mem_univ (0 : ZMod ℓ))
  have h0 : kloos (0 : ZMod ℓ) 1 * kloos (-(0 : ZMod ℓ)) 1 = 1 := by
    rw [neg_zero, kloos_zero one_ne_zero]
    ring
  rw [h0, hfull] at hsplit
  linear_combination hsplit

/-! ### Layer 7 — kernel demos (pure-Nat folds; `Quad` instances stay OUT of decide)

House kernel discipline: `pairCountN` is `ℕ`-recursion the kernel unfolds literally
(the `circleCountN` idiom of `Step00ImaginaryCircle`, squared fiberwise); the Finset
pair count is evaluated at the same instances THROUGH `circle_re_pair_count` — the
agreement is exhibited, not derived by a bijection (disclosed in the header). -/

/-- The re-fiber counter: `#{b ∈ [0,n) : a² ≡ 1 + d·b² (mod n)}` — the Nat clothing of
    `#{x ∈ circle : x.re = a}`. -/
def fiberCountN (n d a : ℕ) : ℕ :=
  ((List.range n).filter fun b => (a * a) % n == (1 + d * (b * b)) % n).length

/-- The pair counter: `Σ_a fiberCountN(a)²` — the number of ordered circle pairs with
    equal real part, in pure-Nat fold form. -/
def pairCountN (n d : ℕ) : ℕ :=
  ((List.range n).map fun a => fiberCountN n d a * fiberCountN n d a).sum

/-- Kernel pair count at `ℓ = 5, d = 2`: `10 = 2ℓ`. -/
theorem pairCountN_5_2 : pairCountN 5 2 = 10 := by decide

/-- Kernel pair count at `ℓ = 11, d = 2`: `22 = 2ℓ`. -/
theorem pairCountN_11_2 : pairCountN 11 2 = 22 := by decide

/-- The Finset pair count at `ℓ = 5, d = 2` — via `circle_re_pair_count`, NOT via
    decide on `Quad` (kernel discipline); agrees with `pairCountN_5_2`. -/
theorem circle_pair_card_5_2 :
    (((circle 2 5) ×ˢ (circle 2 5)).filter fun p => p.1.re = p.2.re).card = 10 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hns : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by
    rw [show ((2 : ℕ) : ZMod 5) = (2 : ZMod 5) by norm_cast,
      ZMod.exists_sq_eq_two_iff (by norm_num)]
    omega
  simpa using circle_re_pair_count (by norm_num) hns

/-- The Finset pair count at `ℓ = 11, d = 2` — agrees with `pairCountN_11_2`. -/
theorem circle_pair_card_11_2 :
    (((circle 2 11) ×ˢ (circle 2 11)).filter fun p => p.1.re = p.2.re).card
      = 22 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hns : ¬ IsSquare ((2 : ℕ) : ZMod 11) := by
    rw [show ((2 : ℕ) : ZMod 11) = (2 : ZMod 11) by norm_cast,
      ZMod.exists_sq_eq_two_iff (by norm_num)]
    omega
  simpa using circle_re_pair_count (by norm_num) hns

/-- Agreement plaque: the Nat fold and the Finset count give the same constant at both
    demo instances (exhibited, not derived — house discipline). -/
theorem pairCount_agreement :
    pairCountN 5 2
        = (((circle 2 5) ×ˢ (circle 2 5)).filter fun p => p.1.re = p.2.re).card
      ∧ pairCountN 11 2
        = (((circle 2 11) ×ˢ (circle 2 11)).filter fun p => p.1.re = p.2.re).card := by
  rw [pairCountN_5_2, pairCountN_11_2, circle_pair_card_5_2, circle_pair_card_11_2]
  exact ⟨rfl, rfl⟩

/-! ### Axiom audit -/

#print axioms circle_card_eq
#print axioms stdAddChar_conj
#print axioms circleSum_conj
#print axioms kloos_conj
#print axioms circle_fiber_card
#print axioms hyperbola_fiber_card
#print axioms fiber_sum_eq_two
#print axioms circle_im_zero_card
#print axioms circle_re_pair_count
#print axioms energy_core
#print axioms circleSum_zero
#print axioms energy
#print axioms circleSum_eq_neg_kloos
#print axioms kloos_zero
#print axioms kloos_scale
#print axioms kloos_family_M2
#print axioms kloos_family_M2_norm
#print axioms kloos_family_twisted
#print axioms pairCountN_5_2
#print axioms pairCountN_11_2
#print axioms circle_pair_card_5_2
#print axioms circle_pair_card_11_2
#print axioms pairCount_agreement

end CircleEnergy
end EuclidsPath
