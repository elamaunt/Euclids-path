/-
  Riemann impossible engine, OffCritical version.

  Goal of this file:
    remove the extra `TrivialBelowZeroClassification` input by working directly with
    `OffCriticalZero`, the exact counterexample object to mathlib's `RiemannHypothesis`.

  Final theorem:
    RH_of_offCriticalRiemannEngineBridge :
      OffCriticalRiemannEngineBridge → RiemannHypothesis

  Remaining hard input:
    OffCriticalRiemannEngineBridge :
      ∀ Z : OffCriticalZero,
        Nonempty (RiemannEngineFactoryOff Z)

  Structural theorem proved here:
    no_riemannEngineFactoryOff :
      ∀ Z : OffCriticalZero,
        ¬ Nonempty (RiemannEngineFactoryOff Z)

  This file assumes the project module `EuclidsPath.Engine.ClosedUniverse`
  already provides:

    ClosedPaidDynamics
    no_infinite_closed_paid_run

  If your local module path differs, adjust the import below.
-/

import Mathlib
import Mathlib.NumberTheory.LSeries.Nonvanishing
import EuclidsPath.Engine.ClosedUniverse

set_option autoImplicit false

namespace EuclidsPath.RiemannImpossibleEngineOff

open Complex EuclidsPath.ClosedUniverse
open scoped BigOperators

/-!
## 1. Off-critical zero objects
-/

/--
A nontrivial zeta zero in the exact sense used by mathlib's
`RiemannHypothesis`.

The field `nontrivial` excludes trivial zeros:
`s = -2 * (n + 1)`.

The field `not_one` excludes the point `s = 1`.
-/
structure NontrivialZetaZero where
  s :
    ℂ

  zero :
    riemannZeta s = 0

  nontrivial :
    ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

  not_one :
    s ≠ 1

/--
A counterexample to RH in the exact mathlib sense:
a nontrivial zeta zero not lying on the critical line.
-/
structure OffCriticalZero extends NontrivialZetaZero where
  off_line :
    s.re ≠ (1 / 2 : ℝ)

/-!
## 2. Pure logic: `¬ RH ↔ Nonempty OffCriticalZero`
-/

/--
Pure extraction from `¬ RiemannHypothesis`.

Important detail:
after `push_neg`, the nontriviality hypothesis is usually in the form

`∀ n, s ≠ -2 * ((n : ℂ) + 1)`,

while our structure field expects

`¬ ∃ n, s = -2 * ((n : ℂ) + 1)`.

So we explicitly bridge the two forms.
-/
theorem offCriticalZero_of_not_RH
  (hNotRH : ¬ RiemannHypothesis) :
    Nonempty OffCriticalZero := by
  classical

  unfold RiemannHypothesis at hNotRH
  push_neg at hNotRH

  rcases hNotRH with
    ⟨s, hzero, hnontrivial_forall, hnot_one, hoff⟩

  have hnontrivial_exists :
      ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    exact hnontrivial_forall n hn

  exact ⟨
    {
      s := s
      zero := hzero
      nontrivial := hnontrivial_exists
      not_one := hnot_one
      off_line := hoff
    }
  ⟩

/--
Conversely, any off-critical nontrivial zero contradicts RH.
-/
theorem not_RH_of_offCriticalZero
  (Z : OffCriticalZero) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact Z.off_line
    (hRH Z.s Z.zero Z.nontrivial Z.not_one)

/--
Exact equivalence:
`¬ RH` iff there exists an off-critical nontrivial zero.
-/
theorem not_RH_iff_nonempty_offCriticalZero :
    ¬ RiemannHypothesis ↔ Nonempty OffCriticalZero := by
  constructor
  · exact offCriticalZero_of_not_RH
  · intro h
    rcases h with ⟨Z⟩
    exact not_RH_of_offCriticalZero Z

/-!
## 3. Optional upper strip bound

This is not needed for the final OffCritical bridge, but it is useful as an
audit lemma: every off-critical zero must satisfy `Z.s.re < 1`, using mathlib.
-/

/--
Upper strip bound from mathlib:
`riemannZeta_ne_zero_of_one_le_re`.
-/
theorem offCriticalZero_re_lt_one
  (Z : OffCriticalZero) :
    Z.s.re < 1 := by
  have hnot_le :
      ¬ 1 ≤ Z.s.re := by
    intro hle
    exact (riemannZeta_ne_zero_of_one_le_re hle) Z.zero

  exact lt_of_not_ge hnot_le

/-!
## 4. Eternal Riemann engine, OffCritical version
-/

/--
An eternal Riemann engine attached to an off-critical zero `Z`.

It is a literal infinite run inside a closed paid dynamics.
-/
structure EternalRiemannEngineOff
  (Z : OffCriticalZero) where

  State :
    Type

  Step :
    State → State → Prop

  dyn :
    ClosedPaidDynamics State Step

  path :
    ℕ → State

  start_in_universe :
    dyn.Universe (path 0)

  step :
    ∀ k,
      Step (path k) (path (k+1))

/--
No eternal Riemann engine exists.

This is the structural engine-killer.
-/
theorem no_eternalRiemannEngineOff
  (Z : OffCriticalZero) :
    ¬ Nonempty (EternalRiemannEngineOff Z) := by
  intro h
  rcases h with ⟨E⟩

  exact no_infinite_closed_paid_run E.dyn
    ⟨E.path, E.start_in_universe, E.step⟩

/-!
## 5. RiemannEngineFactoryOff
-/

/--
Factory form of the Riemann engine.

Instead of directly providing an infinite path, it provides:

1. a closed paid dynamics;
2. a legal seed;
3. a successor from every legal state.

This is enough to generate an impossible infinite closed paid run.
-/
structure RiemannEngineFactoryOff
  (Z : OffCriticalZero) where

  State :
    Type

  Step :
    State → State → Prop

  dyn :
    ClosedPaidDynamics State Step

  seed :
    State

  seed_in_universe :
    dyn.Universe seed

  next :
    ∀ x,
      dyn.Universe x →
        ∃ y, Step x y

/--
Choose the next legal state.

Important:
this is a `Type`-valued definition, so we must not destruct an existential
from `Prop` using large elimination. Use `Classical.choose` and
`Classical.choose_spec`.
-/
noncomputable def RiemannEngineFactoryOff.nextU
  {Z : OffCriticalZero}
  (F : RiemannEngineFactoryOff Z)
  (x : {s : F.State // F.dyn.Universe s}) :
    {y : {s : F.State // F.dyn.Universe s} //
      F.Step x.1 y.1} := by
  classical

  let y : F.State :=
    Classical.choose (F.next x.1 x.2)

  have hy :
      F.Step x.1 y :=
    Classical.choose_spec (F.next x.1 x.2)

  have hyU :
      F.dyn.Universe y :=
    F.dyn.closed x.2 hy

  exact ⟨⟨y, hyU⟩, hy⟩

/--
Recursive legal path generated by the factory.
-/
noncomputable def RiemannEngineFactoryOff.pathU
  {Z : OffCriticalZero}
  (F : RiemannEngineFactoryOff Z) :
    ℕ → {s : F.State // F.dyn.Universe s}
| 0 =>
    ⟨F.seed, F.seed_in_universe⟩
| n + 1 =>
    (F.nextU (RiemannEngineFactoryOff.pathU F n)).1

/--
Every adjacent pair in the generated path is connected by `F.Step`.
-/
theorem RiemannEngineFactoryOff.pathU_step
  {Z : OffCriticalZero}
  (F : RiemannEngineFactoryOff Z) :
    ∀ n,
      F.Step
        (RiemannEngineFactoryOff.pathU F n).1
        (RiemannEngineFactoryOff.pathU F (n+1)).1 := by
  intro n
  change F.Step
    (RiemannEngineFactoryOff.pathU F n).1
    ((F.nextU (RiemannEngineFactoryOff.pathU F n)).1).1
  exact (F.nextU (RiemannEngineFactoryOff.pathU F n)).2

/--
A factory yields an eternal engine.
-/
noncomputable def eternalEngineOff_of_factory
  {Z : OffCriticalZero}
  (F : RiemannEngineFactoryOff Z) :
    EternalRiemannEngineOff Z :=
{
  State := F.State
  Step := F.Step
  dyn := F.dyn
  path := fun n =>
    (RiemannEngineFactoryOff.pathU F n).1
  start_in_universe :=
    (RiemannEngineFactoryOff.pathU F 0).2
  step := by
    intro n
    exact RiemannEngineFactoryOff.pathU_step F n
}

/--
No factory can exist, because every factory produces an impossible
infinite closed paid run.
-/
theorem no_riemannEngineFactoryOff
  (Z : OffCriticalZero) :
    ¬ Nonempty (RiemannEngineFactoryOff Z) := by
  intro h
  rcases h with ⟨F⟩

  exact no_eternalRiemannEngineOff Z
    ⟨eternalEngineOff_of_factory F⟩

/-!
## 6. The remaining bridge and RH
-/

/--
The single remaining hard bridge:

an off-critical zero must force a Riemann engine factory.

This is the RH-level mathematical content.
-/
def OffCriticalRiemannEngineBridge : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (RiemannEngineFactoryOff Z)

/--
RH from the OffCritical Riemann engine bridge.

No `TrivialBelowZeroClassification` input is needed here.
No separate `¬ Engine` input is needed either, because
`no_riemannEngineFactoryOff` is proved structurally.
-/
theorem RH_of_offCriticalRiemannEngineBridge
  (bridge : OffCriticalRiemannEngineBridge) :
    RiemannHypothesis := by
  by_contra hNotRH

  rcases offCriticalZero_of_not_RH hNotRH with ⟨Z⟩

  have hFactory :
      Nonempty (RiemannEngineFactoryOff Z) :=
    bridge Z

  exact no_riemannEngineFactoryOff Z hFactory

/-!
## 7. Final status

Proved structurally in this file:

* `offCriticalZero_of_not_RH`
* `not_RH_iff_nonempty_offCriticalZero`
* `offCriticalZero_re_lt_one`
* `no_eternalRiemannEngineOff`
* `no_riemannEngineFactoryOff`
* `RH_of_offCriticalRiemannEngineBridge`

Remaining hard input:

```lean
OffCriticalRiemannEngineBridge
```

i.e.

```lean
∀ Z : OffCriticalZero,
  Nonempty (RiemannEngineFactoryOff Z)
```

This is the exact point where the analytic/dynamical content of RH remains.
-/


/-! ## 7bis. ЧЕСТНОСТЬ-ТЕОРЕМА: вход эквивалентен самой RH (циркулярность вскрыта машинно)

Раз `no_riemannEngineFactoryOff` доказана БЕЗУСЛОВНО (factory не существует ни для какого Z), вход
`OffCriticalRiemannEngineBridge = ∀ Z, Nonempty (Factory Z)` выполним ЛИШЬ вакуумно — когда off-critical
нулей нет вовсе. То есть вход ⟺ RH ДОСЛОВНО. «Редукция» через impossible engine — переформулировка RH,
а не понижение сложности. Любая будущая заявка доказать bridge = заявка доказать RH. -/

/-- **`offCriticalBridge_iff_RH` — ДОКАЗАНА (честность).** Вход `OffCriticalRiemannEngineBridge`
    ЭКВИВАЛЕНТЕН mathlib-`RiemannHypothesis`. Прямое направление — уже доказанная
    `RH_of_offCriticalRiemannEngineBridge`; обратное — при RH off-critical нулей нет, и `∀ Z, …`
    выполняется вакуумно (`not_RH_of_offCriticalZero`). -/
theorem offCriticalBridge_iff_RH :
    OffCriticalRiemannEngineBridge ↔ RiemannHypothesis := by
  constructor
  · exact RH_of_offCriticalRiemannEngineBridge
  · intro hRH Z
    exact absurd hRH (not_RH_of_offCriticalZero Z)

end EuclidsPath.RiemannImpossibleEngineOff
