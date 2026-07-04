/-
  BoundaryLedgerCollision — ledger-key collision ⟹ cycle (the last branch after a boundary defect).
  Source: EuclidsPath_boundary_ledger_collision_cycle_patch (external audit brick).
  Prose: prose/24_BoundaryDecomp.md (section "Ledger collision ⟹ cycle").

  Proved: pigeonhole (∞ defect-flows → finite key ⟹ collision), burning the payment branch via
  `impossiblePayment_false`, and all glue down to `False` under a local height. The single named input —
  `BoundaryLedgerCollisionResolves` (collision ⟹ cycle ∨ impossible payment). Does NOT close Step00.
-/
import EuclidsPath.Engine.LabelledFanIn
import EuclidsPath.Engine.BoundaryDefectPayment

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath

namespace BoundaryLedgerCollision

open EuclidsPath.LabelledFanIn
open EuclidsPath.BoundaryDefectPayment

variable {σ Key : Type*}

/-#############################################################################
  §1. Cycles and finite-key collisions
#############################################################################-/

/-- A legal nonempty cycle in the same real-step graph. -/
abbrev LegalCycle (RealStep : σ → σ → Prop) (Legal : σ → Prop) : Prop :=
  ∃ W : σ, Legal W ∧ EuclidsPath.LabelledFanIn.NonemptyPath RealStep W W

/--
Pure infinite pigeonhole: an infinite set mapped to a finite key type contains
two distinct elements with the same key.

This is only counting.  It does not create the Euclidean engine; it merely
produces the ledger collision that the Step00 arithmetic must interpret.
-/
theorem infinite_set_key_collision
    {S : Set σ} (hInf : S.Infinite)
    [Finite Key] (key : σ → Key) :
    ∃ U₁ U₂ : σ,
      U₁ ∈ S ∧ U₂ ∈ S ∧ U₁ ≠ U₂ ∧ key U₁ = key U₂ := by
  classical
  by_contra hno
  have hinj : Set.InjOn key S := by
    intro a ha b hb hab
    by_contra hne
    exact hno ⟨a, b, ha, hb, hne, hab⟩
  exact hInf (Set.Finite.of_finite_image (Set.toFinite _) hinj)

/-#############################################################################
  §2. Defect flows and the actual remaining obligation
#############################################################################-/

/--
A boundary-defect ledger resolution law.

Parameters:
* `Fresh` marks the starts/flows that came from fresh clean starts;
* `Defective` marks the flows that carry the boundary defect into the ledger;
* `key` is the finite normalized ledger key: absorber + normalized signature +
  whatever payment residue is supposed to be finite at fixed scale;
* `ImpossiblePayment` is the already-refuted no-tax payment branch.

Meaning:
if two distinct legal fresh defect-flows have the same finite ledger key, then
that merge cannot be free.  It must either splice the histories into a genuine
legal cycle, or exhibit an impossible payment certificate.

This is the last real Step00 arithmetic obligation.  The theorems below do not
prove it; they prove that once it is supplied, the defect branch closes.
-/
def BoundaryLedgerCollisionResolves
    (RealStep : σ → σ → Prop) (Legal Fresh Defective : σ → Prop)
    (key : σ → Key) (ImpossiblePayment : Prop) : Prop :=
  ∀ U₁ U₂ : σ,
    U₁ ≠ U₂ →
    Fresh U₁ → Defective U₁ → Legal U₁ →
    Fresh U₂ → Defective U₂ → Legal U₂ →
    key U₁ = key U₂ →
      LegalCycle RealStep Legal ∨ ImpossiblePayment

/--
An infinite family of legal fresh defect-flows over a finite key space produces
a concrete ledger collision, with all predicates carried along.
-/
theorem infinite_defect_flows_force_ledger_collision
    {RealStep : σ → σ → Prop} {Legal Fresh Defective : σ → Prop}
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S, Fresh U ∧ Defective U ∧ Legal U)
    [Finite Key] (key : σ → Key) :
    ∃ U₁ U₂ : σ,
      U₁ ≠ U₂ ∧
      U₁ ∈ S ∧ U₂ ∈ S ∧
      Fresh U₁ ∧ Defective U₁ ∧ Legal U₁ ∧
      Fresh U₂ ∧ Defective U₂ ∧ Legal U₂ ∧
      key U₁ = key U₂ := by
  classical
  obtain ⟨U₁, U₂, hU₁, hU₂, hne, hkey⟩ :=
    infinite_set_key_collision (S := S) hInf key
  have h₁ := hS U₁ hU₁
  have h₂ := hS U₂ hU₂
  exact ⟨U₁, U₂, hne, hU₁, hU₂,
    h₁.1, h₁.2.1, h₁.2.2,
    h₂.1, h₂.2.1, h₂.2.2,
    hkey⟩

/--
Main branch theorem, still with the payment alternative visible.

Many legal fresh defect-flows cannot all be absorbed by a finite ledger without
either producing a legal cycle or producing the impossible-payment branch.
-/
theorem infinite_defect_flows_force_cycle_or_payment
    {RealStep : σ → σ → Prop} {Legal Fresh Defective : σ → Prop}
    {ImpossiblePayment : Prop}
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S, Fresh U ∧ Defective U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh Defective key ImpossiblePayment) :
    LegalCycle RealStep Legal ∨ ImpossiblePayment := by
  classical
  obtain ⟨U₁, U₂, hne, _hU₁, _hU₂,
    hFr₁, hDef₁, hLeg₁, hFr₂, hDef₂, hLeg₂, hkey⟩ :=
    infinite_defect_flows_force_ledger_collision
      (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
      (Defective := Defective) (S := S) hInf hS key
  exact hResolve U₁ U₂ hne hFr₁ hDef₁ hLeg₁ hFr₂ hDef₂ hLeg₂ hkey

/--
If the payment branch is known impossible, the same branch theorem leaves an
actual legal cycle.
-/
theorem infinite_defect_flows_force_cycle
    {RealStep : σ → σ → Prop} {Legal Fresh Defective : σ → Prop}
    {ImpossiblePayment : Prop}
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S, Fresh U ∧ Defective U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh Defective key ImpossiblePayment)
    (hNoPayment : ImpossiblePayment → False) :
    LegalCycle RealStep Legal := by
  rcases infinite_defect_flows_force_cycle_or_payment
      (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
      (Defective := Defective) (ImpossiblePayment := ImpossiblePayment)
      (S := S) hInf hS key hResolve with hCycle | hPay
  · exact hCycle
  · exact False.elim (hNoPayment hPay)

/-#############################################################################
  §3. From ledger collision to engine / contradiction
#############################################################################-/

/--
With a `CycleBridge`, the finite-ledger collision branch gives the current
formal `EuclideanEngine`.
-/
theorem infinite_defect_flows_force_engine
    {RealStep : σ → σ → Prop} {Legal Fresh Defective : σ → Prop}
    {ImpossiblePayment EuclideanEngine : Prop}
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S, Fresh U ∧ Defective U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh Defective key ImpossiblePayment)
    (hNoPayment : ImpossiblePayment → False)
    (hBridge : EuclidsPath.LabelledFanIn.CycleBridge
      (RealStep := RealStep) Legal EuclideanEngine) :
    EuclideanEngine := by
  exact hBridge (infinite_defect_flows_force_cycle
    (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
    (Defective := Defective) (ImpossiblePayment := ImpossiblePayment)
    (S := S) hInf hS key hResolve hNoPayment)

/--
Under a local height witness, the same branch is contradictory.

This is the clean anti-vacuum check: if the concrete Step00 graph really has a
strict height/co-height along `RealStep`, and if the defect-ledger resolution
law is real, then an infinite family of legal fresh defect-flows cannot exist.
-/
theorem infinite_defect_flows_impossible_under_height
    {RealStep : σ → σ → Prop} {Legal Fresh Defective : σ → Prop}
    {ImpossiblePayment : Prop}
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S, Fresh U ∧ Defective U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh Defective key ImpossiblePayment)
    (hNoPayment : ImpossiblePayment → False)
    (height : σ → ℕ)
    (hdrop : ∀ {U V : σ}, RealStep U V → height U < height V) :
    False := by
  exact infinite_defect_flows_force_engine
    (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
    (Defective := Defective) (ImpossiblePayment := ImpossiblePayment)
    (EuclideanEngine := False)
    (S := S) hInf hS key hResolve hNoPayment
    (EuclidsPath.LabelledFanIn.cycleBridge_of_height height hdrop)

/-#############################################################################
  §4. Specialization to the previous boundary-defect/payment patch
#############################################################################-/

/--
A state-level carrier of the concrete small-prime defect from the previous
patch.  `centerOf` extracts the natural centre `n` whose sides `6n±1` carry the
small-prime obstruction.
-/
abbrev CarriesSmallPrimeDefect (A : ℕ) (centerOf : σ → ℕ) : σ → Prop :=
  fun U => EuclidsPath.BoundaryDefectPayment.SmallPrimeDefect A (centerOf U)

/--
Specialized version using the already-refuted
`BoundaryDefectPayment.ImpossiblePayment`.

This is the exact formal branch:

  infinitely many legal fresh states carrying actual small-prime defects
  + finite ledger key
  + collision-resolution law
  ---------------------------------------------------------------
  legal nonempty cycle.
-/
theorem infinite_smallPrimeDefect_flows_force_cycle
    {A : ℕ}
    {RealStep : σ → σ → Prop} {Legal Fresh : σ → Prop}
    (centerOf : σ → ℕ)
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S,
      Fresh U ∧ CarriesSmallPrimeDefect (σ := σ) A centerOf U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh (CarriesSmallPrimeDefect (σ := σ) A centerOf)
      key EuclidsPath.BoundaryDefectPayment.ImpossiblePayment) :
    LegalCycle RealStep Legal := by
  exact infinite_defect_flows_force_cycle
    (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
    (Defective := CarriesSmallPrimeDefect (σ := σ) A centerOf)
    (ImpossiblePayment := EuclidsPath.BoundaryDefectPayment.ImpossiblePayment)
    (S := S) hInf hS key hResolve
    EuclidsPath.BoundaryDefectPayment.impossiblePayment_false

/--
The same specialization, but immediately bridged to the current
`EuclideanEngine`.
-/
theorem infinite_smallPrimeDefect_flows_force_engine
    {A : ℕ}
    {RealStep : σ → σ → Prop} {Legal Fresh : σ → Prop}
    {EuclideanEngine : Prop}
    (centerOf : σ → ℕ)
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S,
      Fresh U ∧ CarriesSmallPrimeDefect (σ := σ) A centerOf U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh (CarriesSmallPrimeDefect (σ := σ) A centerOf)
      key EuclidsPath.BoundaryDefectPayment.ImpossiblePayment)
    (hBridge : EuclidsPath.LabelledFanIn.CycleBridge
      (RealStep := RealStep) Legal EuclideanEngine) :
    EuclideanEngine := by
  exact hBridge (infinite_smallPrimeDefect_flows_force_cycle
    (A := A) (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
    (centerOf := centerOf) (S := S) hInf hS key hResolve)

/--
Specialized contradiction under a local height witness.
-/
theorem infinite_smallPrimeDefect_flows_impossible_under_height
    {A : ℕ}
    {RealStep : σ → σ → Prop} {Legal Fresh : σ → Prop}
    (centerOf : σ → ℕ)
    {S : Set σ} (hInf : S.Infinite)
    (hS : ∀ U ∈ S,
      Fresh U ∧ CarriesSmallPrimeDefect (σ := σ) A centerOf U ∧ Legal U)
    [Finite Key] (key : σ → Key)
    (hResolve : BoundaryLedgerCollisionResolves
      RealStep Legal Fresh (CarriesSmallPrimeDefect (σ := σ) A centerOf)
      key EuclidsPath.BoundaryDefectPayment.ImpossiblePayment)
    (height : σ → ℕ)
    (hdrop : ∀ {U V : σ}, RealStep U V → height U < height V) :
    False := by
  exact infinite_defect_flows_impossible_under_height
    (RealStep := RealStep) (Legal := Legal) (Fresh := Fresh)
    (Defective := CarriesSmallPrimeDefect (σ := σ) A centerOf)
    (ImpossiblePayment := EuclidsPath.BoundaryDefectPayment.ImpossiblePayment)
    (S := S) hInf hS key hResolve
    EuclidsPath.BoundaryDefectPayment.impossiblePayment_false
    height hdrop

/-#############################################################################
  §5. Loud name for the remaining Step00 obligation
#############################################################################-/

/--
The remaining local Step00 obligation, in its precise ledger form.

To close the boundary-defect branch for the actual `6m±1` graph, instantiate
this with the real state type, real transition relation, real legality predicate,
real finite ledger key, and real defect predicate.

Everything around it is now formal glue; this proposition is where the true
arithmetic still lives.
-/
abbrev TheRemainingBoundaryLedgerObligation
    (RealStep : σ → σ → Prop) (Legal Fresh Defective : σ → Prop)
    (key : σ → Key) (ImpossiblePayment : Prop) : Prop :=
  BoundaryLedgerCollisionResolves RealStep Legal Fresh Defective key ImpossiblePayment

end BoundaryLedgerCollision

end EuclidsPath
