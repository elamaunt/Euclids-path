/-
  CollapseFirstCause — 🟡 YELLOW LAYER: THE REBOUND OF THE COLLAPSE IS DECREED BY THE FIRST CAUSE.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS HERE, WHAT IS NOT, AND WHERE THE TAINT IS.     │
  └───────────────────────────────────────────────────────────────────────────┘

  DUAL of `DyadicFirstCause`. Where the cascade's ORIGIN (n=0-pump) is decreed from outside, the
  collapse's REBOUND (a fresh 0 → 1 expansion out of the singular point r=0) is decreed from
  outside — IN EXACTLY THE SAME "two walls / decreed supply" scheme:
    • 🟢 GREEN WALL (in `CollapseExtinction.lean`, WITHOUT taint):
      `collapse_drive_forbids_rebound` — at r=0 the collapse drive r' ≤ -C·r^α (C>0, α>0) forces
      r' ≤ 0 (since 0^α = 0), so no re-expansion is possible from inside; a rebound needs external
      forcing. This is the collapse analogue of `DyadicBlowup.bottomForcing_pos` /
      `no_internalisedOriginEvent`.
    • 🟡 HERE (TAINT via `step00FirstCause`): the same first-cause decree that supplies the cascade
      origin ALSO supplies the collapse rebound, by REUSING the field `step00FirstCause.nsBoundary`
      (the third boundary — the NS energy-balance gate-law). NO new boundary is introduced (that
      would change `step00FirstCause_iff_causalClosure` and repeat the Collatz-boundary risk);
      the collapse is a fluid/continuum phenomenon and honestly shares the NS boundary.

  WHAT IS NOT HERE (RED LINES):
    • This is NOT physics. The "collapse / supernova / Big-Bang" reading is metaphor; deriving the
      inward drive from a self-gravity law (Euler–Poisson, Larson–Penston) is a named analytic input
      beyond mathlib, absent here.
    • The GREEN extinction mathematics (`sublinear_collapse_extinction`) is SELF-CONTAINED and does
      NOT depend on this yellow layer. Remove the first cause — the extinction proof stays intact;
      only the answer to "who re-ignites the rebound out of r=0" disappears.

  TAINT GROWS INTENTIONALLY by two declarations (the two 🟡-theorems), each consuming the SINGLE
  repository axiom `step00FirstCause` via `.nsBoundary`. `#print axioms` below confirms it. No sorry,
  no native_decide, no NEW axiom; the green wall carries only the standard triple.
-/
import Mathlib
import EuclidsPath.Engine.CollapseExtinction
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath.CollapseFirstCause

open EuclidsPath.CollapseExtinction
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- **`CollapseReboundDecreed` — NON-VACUOUS Prop of the decreed collapse rebound.**

Packs TWO substantive components (NOT `True`):
  • `nsLaw` — the actual NS energy-balance gate-law `NsSolutionBalanceLaw` (the third boundary of
    the first-cause decree), REUSED as the external supply of the rebound;
  • the green wall of impossibility `collapse_drive_forbids_rebound` (the drive at r=0 forces
    r' ≤ 0, so the rebound cannot be caused from inside and NEEDS an external decree).

Inhabited ONLY via the real boundary object `step00FirstCause.nsBoundary` — vacuity is excluded. -/
def CollapseReboundDecreed : Prop :=
  EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw ∧
    (∀ (C α r' : ℝ), 0 < C → 0 < α → r' ≤ -C * (0 : ℝ) ^ α → r' ≤ 0)

/-- **`collapseRebound_from_firstCause` — 🟡 ⚠️ AXIOM-TAINTED.**

The collapse rebound IS DECREED by the first cause: the re-ignition out of the singular point r=0
is supplied by `step00FirstCause.nsBoundary` (the third boundary — the NS energy-balance gate-law,
REUSED, no new boundary). The second component is the green wall of impossibility
(`collapse_drive_forbids_rebound`), axiom-free, exhibited as the content explaining the NECESSITY of
the decree. Taint runs EXACTLY through `step00FirstCause` (first conjunct). -/
theorem collapseRebound_from_firstCause : CollapseReboundDecreed :=
  ⟨step00FirstCause.nsBoundary,
   fun _C _α _r' hC hα hdrive => collapse_drive_forbids_rebound hC hα hdrive⟩

/-- **`collapseRebound_is_firstCauseManifestation` — 🟡 ⚠️ AXIOM-TAINTED (SLOGAN, TWO WALLS).**

The manifestation slogan, honestly "two walls / decreed supply", NOT a bare `True`:
  (1) 🟢 the GREEN WALL `collapse_drive_forbids_rebound` — the rebound (r' > 0 out of r=0) is
      internally uncausable (axiom-free, exhibited here);
  (2) 🟡 the DECREED SUPPLY `collapseRebound_from_firstCause` — the first-cause decree supplies the
      rebound from outside (taint `step00FirstCause`);
  (3) 🟡 the boundary object `step00FirstCause.nsBoundary` itself (no vacuity).

Epistemic upshot: the collapse attaches to the masks ONLY via its rebound; the green extinction
mathematics does NOT depend on this layer. Taint — only via (2) and (3). -/
theorem collapseRebound_is_firstCauseManifestation :
    (∀ (C α r' : ℝ), 0 < C → 0 < α → r' ≤ -C * (0 : ℝ) ^ α → r' ≤ 0) ∧
      CollapseReboundDecreed ∧
      EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw :=
  ⟨fun _C _α _r' hC hα hdrive => collapse_drive_forbids_rebound hC hα hdrive,
   collapseRebound_from_firstCause,
   step00FirstCause.nsBoundary⟩

/-!
  ### Machine taint honesty (expectations)
  * Both 🟡-theorems carry EXACTLY `step00FirstCause` (via `.nsBoundary`) beyond the standard triple.
  * The green wall `CollapseExtinction.collapse_drive_forbids_rebound` — ONLY the standard triple,
    WITHOUT `step00FirstCause`: the green output is self-contained and the taint is localised here.
-/

-- 🟡 MUST show step00FirstCause:
#print axioms collapseRebound_from_firstCause
#print axioms collapseRebound_is_firstCauseManifestation

-- 🟢 CONTROL: must NOT show step00FirstCause.
#print axioms collapse_drive_forbids_rebound

end EuclidsPath.CollapseFirstCause
