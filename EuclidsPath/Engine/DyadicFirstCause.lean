/-
  DyadicFirstCause — 🟡 YELLOW LAYER: THE ORIGIN OF THE DYADIC CASCADE IS DECREED BY THE FIRST CAUSE.

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS HERE, WHAT IS NOT, AND WHERE THE TAINT IS.                      │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  PROJECT PATTERN MANIFESTATION. This file attaches the cascade blowup to the "seven masks"
  of the first cause IN EXACTLY THE SAME WAY as GeometryFront attaches the intersection of lines:
  green wall of impossibility (the cascade origin is NOT causable from inside) + yellow layer
  (the same first-cause decree supplies the origin from outside). The scheme is TWO WALLS /
  DECREED SUPPLY, not a bare `True`.

  WHAT IS HERE:
    • 🟢 (in `DyadicBlowup.lean`, §2quater, WITHOUT taint): `dyadicOrigin_uncausable_from_inside` —
      the largest shell `n=0` (outflow only, `kpInflow 0 = 0`) does NOT supply its own
      origin: its true dynamics carry `bottomForcing > 0` beyond the unforced `kpRHS`. External
      pumping is MANDATORY. This is the cascade analogue of `no_internalisedOriginEvent`.
    • 🟡 (HERE, TAINT via `step00FirstCause`): the same first-cause decree that decrees the
      seven masks ALSO DECREES the supply of the cascade origin (its `0` = the singularity of the
      cosmological reading). Realised by consuming the field `step00FirstCause.nsBoundary` (the
      third boundary of the decree — the NS energy-balance gate-law). Every 🟡-Prop carries REAL
      content (an object of the law `NsSolutionBalanceLaw` and/or the green wall of impossibility),
      NOT `True`.

  WHAT IS NOT HERE (RED LINES — LOUD):
    • This is NOT a solution of Navier–Stokes and NOT a Clay announcement. The gate boundary
      `nsBoundary` is a surviving decree candidate whose HONEST PRICE is disclosed in quarantine
      (the law may be overpaying).
    • This is NOT a proof of a FINITE-ENERGY blowup for the KP problem: §2bis/§2ter in
      `DyadicBlowup.lean` give ONE exact self-similar solution + a class with a front invariant,
      but NOT the full KP theorem.
    • The cascade blowup ATTACHES to the masks ONLY via its ORIGIN (n=0-pump), decreed from
      outside. THE GREEN DRIVE OUTPUT (STEP A/B: core §1, self-similarity §2bis, front invariant
      §2ter) IS SELF-CONTAINED and DOES NOT DEPEND on this yellow layer. Remove the first cause —
      the green blowup mathematics stays intact; only the answer to "who ignited the n=0-pump"
      disappears.
    • No direct connection to prime numbers — the project's red line is untouched (the decree is general).

  TAINT GROWS INTENTIONALLY. All 🟡-declarations are marked `⚠️ AXIOM-TAINTED` and consume the
  SINGLE axiom of the repository `step00FirstCause`. Below, `#print axioms` MECHANICALLY confirms:
  🟡-declarations carry `step00FirstCause`, while the green wall
  `DyadicBlowup.dyadicOrigin_uncausable_from_inside` does NOT
  (only the standard triple). No sorry, no native_decide, no NEW axiom.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/DyadicFirstCause.lean
  (will show the taint in `#print axioms` — this is EXPECTED, not an error).
-/
import Mathlib
import EuclidsPath.Engine.DyadicBlowup
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath.DyadicFirstCause

open EuclidsPath.DyadicBlowup
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- **`DyadicOriginDecreed` — NON-VACUOUS Prop of the decreed cascade origin.**

Packs TWO substantive components (NOT `True`):
  • `nsLaw` — the actual NS energy-balance gate-law `NsSolutionBalanceLaw` (the third boundary
    of the first-cause decree), which supplies the cascade origin with a supply at the largest scale;
  • `originUncausable` — accessibility of the green wall of impossibility
    (`DyadicBlowup.dyadicOrigin_uncausable_from_inside` for concrete `λ>1`, `t<T`), i.e. the fact
    that the origin is NOT causable from inside and therefore NEEDS an external decree.

The type is inhabited ONLY via a real boundary object `nsLaw` — vacuity is excluded. -/
def DyadicOriginDecreed : Prop :=
  EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw ∧
    (∀ (lam T t : ℝ), 1 < lam → t < T →
      ¬ HasDerivAt (fun s => ssMode lam T 0 s)
          (kpRHS lam (fun _ => 0) (ssMode lam T) 0 t) t)

/-- **`dyadicOrigin_from_firstCause` — 🟡 ⚠️ AXIOM-TAINTED.**

The dyadic cascade origin IS DECREED by the first cause: the supply at the largest scale `n=0`
is taken from the field `step00FirstCause.nsBoundary` (the third boundary of the decree —
the NS energy-balance gate-law). The second component is the green wall of impossibility
(`dyadicOrigin_uncausable_from_inside`); it is axiom-free but here is merely EXHIBITED as the
content explaining the NECESSITY of the decree.

The taint runs EXACTLY through `step00FirstCause` (first conjunct). No NEW axiom. -/
theorem dyadicOrigin_from_firstCause : DyadicOriginDecreed :=
  ⟨step00FirstCause.nsBoundary,
   fun _ _ _ hlam ht => dyadicOrigin_uncausable_from_inside hlam ht⟩

/-- **`dyadicBlowup_is_firstCauseManifestation` — 🟡 ⚠️ AXIOM-TAINTED (SLOGAN, TWO WALLS).**

The final manifestation slogan, honestly "two walls / decreed supply", NOT a bare `True`.
The conjunction refers SIMULTANEOUSLY to:
  (1) 🟢 the GREEN WALL of impossibility `DyadicBlowup.dyadicOrigin_uncausable_from_inside` —
      the cascade origin (n=0-pump) is internally uncausable (axiom-free fact, exhibited here);
  (2) 🟡 the DECREED SUPPLY `dyadicOrigin_from_firstCause` — the same first-cause decree that
      decrees the seven masks supplies this origin from outside (taint `step00FirstCause`);
  (3) 🟡 the object of the third boundary `step00FirstCause.nsBoundary` itself — which makes the
      type inhabited only via the accepted boundary (no vacuity).

Epistemic upshot: the cascade blowup attaches to the masks ONLY via its origin; the green drive
mathematics (STEP A/B) does NOT depend on this layer. Taint — only via (2) and (3). -/
theorem dyadicBlowup_is_firstCauseManifestation :
    (∀ (lam T t : ℝ), 1 < lam → t < T →
        ¬ HasDerivAt (fun s => ssMode lam T 0 s)
            (kpRHS lam (fun _ => 0) (ssMode lam T) 0 t) t) ∧
      DyadicOriginDecreed ∧
      EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw :=
  ⟨fun _ _ _ hlam ht => dyadicOrigin_uncausable_from_inside hlam ht,
   dyadicOrigin_from_firstCause,
   step00FirstCause.nsBoundary⟩

/-!
  ### Machine taint honesty (expectations)

  * Both 🟡-declarations below — beyond the standard triple `propext`, `Classical.choice`, `Quot.sound`
    carry EXACTLY `step00FirstCause` (via `.nsBoundary`).
  * For contrast: the green wall `DyadicBlowup.dyadicOrigin_uncausable_from_inside` (and
    `bottomForcing_pos`) — ONLY the standard triple, WITHOUT `step00FirstCause`. This confirms
    that the green output is self-contained and the taint is localised in this file.
-/

-- 🟡 MUST show step00FirstCause:
#print axioms dyadicOrigin_from_firstCause
#print axioms dyadicBlowup_is_firstCauseManifestation

-- 🟢 CONTROL (for comparison): must NOT show step00FirstCause.
#print axioms dyadicOrigin_uncausable_from_inside
#print axioms bottomForcing_pos

end EuclidsPath.DyadicFirstCause
