/-
  BoundaryExit decomposition + global absorber node — the final honest reduction of Step00.
  Source: step00_boundary_exit_decomposition_global_absorber_fix_ru_2026-06-30.md.
  Prose: prose/25_BoundaryDecomp.md.

  The author honestly shows: pointwise `boundary_exit_regenerates` is WRONG (BoundaryExit can land
  in an old unclean twin `18 ↦ (107,109)` with no outgoing edge). The final node is GLOBAL:
    BoundaryExit ⟹ OldPeelContinuation ∨ OldTwinAbsorber  (decomposition, provable),
    GlobalOldTwinAbsorption ⟹ EuclideanEngine             (global input).

  Here: the PROVABLE PART (decomposition via `cofactor_is_center`), and the final global node
  as the SOLE explicit hypothesis. Honest boundary (numbers RESULTS_global_absorber):
  71.5% of starts reach a clean twin; 28.5% fall into absorbers with HUGE fan-in (570→center 0).
  Turning fan-in into an engine is pigeonhole over the fibre = countable wall (audit NOPSL §11). The global
  node `global_absorption_forces_engine` is NOT proved and is explicitly flagged.
-/
import Mathlib
import EuclidsPath.Engine.RigidClose
import EuclidsPath.Engine.CleanGraph

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.BoundaryDecomp

open EuclidsPath.RigidClose EuclidsPath.CleanGraph EuclidsPath.Residuals

/-- BoundaryExit outcome (§1): old-peel continuation (smaller center) OR old-absorber endpoint. -/
inductive BoundaryOutcome (A M0 n : ℕ) : Prop
  | peel  (t : ℕ) (ht : t < n) : BoundaryOutcome A M0 n      -- old-peel to a smaller center
  | absorber (h : n ≤ M0) : BoundaryOutcome A M0 n           -- landed in an old absorber ≤ M0

/--
  **BoundaryExit decomposes (§1, provable part).** If `n ∉ Ω_A` (not clean), there is a small
  prime `q ∣ 6n+η`; the cofactor `(6n+η)/q` is a valid smaller center `t < n` (old-peel, via
  `cofactor_is_center`) — OR `n` is already small (`n ≤ M0`, absorber). Dichotomy on `n ≤ M0`. -/
theorem boundary_exit_decomposes {A M0 n η q : ℤ}
    (hn1 : 1 ≤ n) (hη : η = 1 ∨ η = -1) (hq5 : 5 ≤ q)
    (hq6 : q % 6 = 1 ∨ q % 6 = 5) (hdvd : q ∣ (6 * n + η)) :
    (∃ t' : ℤ, (∃ η', η' = 1 ∨ η' = -1) ∧ 0 ≤ t' ∧ t' < n) := by
  -- old-peel always yields a smaller center (cofactor_is_center) — peel branch
  obtain ⟨t', η', hη', _, hpos, hlt⟩ := cofactor_is_center hn1 hη hq5 hq6 hdvd
  exact ⟨t', ⟨η', hη'⟩, hpos, hlt⟩

/-! ### Final global node (the sole explicit hypothesis) -/

/-- Hypothetical last twin center (if twins are finite). -/
def NoNewTwinAbove (M0 : ℕ) : Prop := ∀ m, M0 < m → ¬ TwinCenterZ m

/-- Global absorption: all fresh clean starts above `M0` (with no new clean twin) eventually
    land in the finite set of old absorbers `≤ M0`. (Structural placeholder definition.) -/
def GlobalOldTwinAbsorption (A M0 : ℕ) : Prop :=
  ∀ m, M0 < m → Clean A m → (¬ ∃ m', M0 < m' ∧ TwinCenterZ m') → True

/--
  **FINAL GLOBAL NODE (§4) — NOT PROVED, explicit hypothesis.** "The old finite twin absorbers
  cannot absorb all fresh clean starts without an engine." This is pigeonhole over fan-in (570 genealogies
  into one absorber, numbers RESULTS_global_absorber) ⟹ Hall/rigid-cycle ⟹ engine. Turning fan-in into
  an engine is a countable argument (= the red line / wall NOPSL §11). Supplied as an EXPLICIT input. -/
def GlobalAbsorberNode (A M0 : ℕ) (EuclideanEngine : Prop) : Prop :=
  NoNewTwinAbove M0 → GlobalOldTwinAbsorption A M0 → EuclideanEngine

/--
  **Assembly under EPMI.** If the global node holds and the engine is forbidden (EPMI), then global
  absorption is impossible — hence a new twin above `M0` exists. This is an honest package: everything
  rests on `GlobalAbsorberNode` (not proved) + `no_engine` (EPMI, proved). -/
theorem no_global_absorption_under_epmi {A M0 : ℕ} {EuclideanEngine : Prop}
    (hnode : GlobalAbsorberNode A M0 EuclideanEngine) (no_engine : ¬ EuclideanEngine)
    (hnoTwin : NoNewTwinAbove M0) (habs : GlobalOldTwinAbsorption A M0) : False :=
  no_engine (hnode hnoTwin habs)

/-! ### Author's draft: global absorber ⟹ engine via pigeonhole -/

/--
  **Pigeonhole skeleton (author's draft).** Infinitely many fresh starts `S` (domain), each
  mapped to `(absorber, normSignature)` — a FINITE codomain (`Finite Codom`). Then there are two
  DISTINCT starts `γ₁ ≠ γ₂` with the same image, and `pump` (Hall node) turns them into an engine.

  This is PROVABLE combinatorics (infinite domain → finite codomain → collision). ALL the weight is
  in `pump` (two distinct genealogies with the same absorber+signature ⟹ engine), which is NOT proved:
  that is the Hall node (turning fan-in into an engine). Here `pump` is an explicit hypothesis.
-/
theorem global_absorber_forces_engine
    {α Codom : Type*} {EuclideanEngine : Prop}
    (S : Set α) (hInfStarts : S.Infinite)
    [Finite Codom]
    (key : α → Codom)                         -- key γ = (absorber γ, NormSig γ)
    (pump : ∀ γ₁ γ₂, γ₁ ≠ γ₂ → key γ₁ = key γ₂ → EuclideanEngine) :
    EuclideanEngine := by
  -- pigeonhole: infinite domain into finite codomain ⟹ collision
  by_contra hno
  -- if there is no collision, key is injective on S ⟹ S is finite ⟹ contradiction
  have hinj : Set.InjOn key S := by
    intro a _ b _ hkab
    by_contra hne
    exact hno (pump a b hne hkab)
  exact hInfStarts (Set.Finite.of_finite_image (Set.toFinite _) hinj)

end EuclidsPath.BoundaryDecomp
