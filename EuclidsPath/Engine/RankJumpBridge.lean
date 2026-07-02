/-
  RankJumpBridgeAround.lean

  Цель файла:
    формально закрыть "всё вокруг" узла

      LiouvilleViolation → TwinCarrierEnergyJump

    и оставить сам узел как единственный явный bridge/localization input.

  Что доказано здесь:
    1. Общий rank/parity язык.
    2. Rank-one descent флипает знак.
    3. RankParityHom переносит jumps.
    4. Глобальный jump НЕ переносится в локальный carrier автоматически:
       дана тривиальная контрмодель no_jump_unit.
    5. RankJumpLocalization → LiouvilleViolation → TwinCarrierEnergyJump.
    6. SpectralToTwinRankBridge строит TwinEngineFactory из OffCriticalZero.
    7. Любой ClosedPaidFactory невозможен через no_infinite_closed_paid_run.
    8. Следовательно, SpectralToTwinRankBridge запрещает OffCriticalZero.
    9. Если есть эквивалентность `¬RH ↔ Nonempty OffCriticalZero`,
       то bridge даёт RH.

  Сам мост, который остаётся содержательной математикой:

      buildRankJumpLocalization :
        RankJumpLocalization LiouvilleViolation TwinSystem

  или в голой форме:

      LiouvilleViolation → TwinCarrierEnergyJump TwinSystem

  Этот файл не доказывает RH и не доказывает близнецов. Он строго изолирует
  общий механизм вокруг bridge.

  Assumes project module:
    EuclidsPath.Engine.ClosedUniverse

  If your local namespace differs, adjust the import/open lines.
-/

import Mathlib
import EuclidsPath.Engine.ClosedUniverse

set_option autoImplicit false

namespace EuclidsPath.RankJumpBridge

open scoped BigOperators
open ArithmeticFunction
open EuclidsPath.ClosedUniverse

/-!
## 1. Общий rank/parity язык
-/

/--
A rank/parity system is any state space with a natural rank and an integer sign
equal to `(-1)^rank`.
-/
structure RankParitySystem where

  State :
    Type

  rank :
    State → ℕ

  sign :
    State → ℤ

  sign_eq_rank :
    ∀ s,
      sign s = (-1 : ℤ) ^ rank s

/--
A rank-energy jump is a pair of states whose rank and sign both change.
-/
structure RankEnergyJump
  (S : RankParitySystem) where

  before :
    S.State

  after :
    S.State

  rank_changes :
    S.rank before ≠ S.rank after

  sign_changes :
    S.sign before ≠ S.sign after

/--
A one-factor descent: rank drops by exactly one.
-/
structure RankOneDescent
  (S : RankParitySystem)
  (a b : S.State) : Prop where

  rank_drop :
    S.rank a = S.rank b + 1

/--
Universal rank/parity lemma:
rank-one descent flips the sign.

This abstracts the Liouville fact:
`deleteFactor` changes `Ω` by one, hence flips `λ`.
-/
theorem sign_flip_of_rank_one_descent
  (S : RankParitySystem)
  {a b : S.State}
  (h : RankOneDescent S a b) :
    S.sign a = - S.sign b := by
  rw [S.sign_eq_rank a, S.sign_eq_rank b]
  rw [h.rank_drop]
  rw [pow_succ]
  ring

/-!
## 2. Liouville as a rank/parity system
-/

/--
The Liouville rank system on nonzero natural numbers.

Rank is `cardFactors`; sign is `ArithmeticFunction.liouville`.
-/
def LiouvilleRankSystem : RankParitySystem :=
{
  State := {n : ℕ // n ≠ 0}

  rank := fun n =>
    cardFactors n.1

  sign := fun n =>
    liouville n.1

  sign_eq_rank := by
    intro n
    exact liouville_apply n.2
}

/--
Summatory Liouville function.
-/
noncomputable def L (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, liouville n

/--
Liouville violation: failure of the RH-strength Liouville bound in a cofinal
form.

This is used as the global spectral/rank imbalance.
-/
def LiouvilleViolation : Prop :=
  ∃ ε : ℝ,
    0 < ε ∧
    ∀ C : ℝ,
      0 < C →
        ∃ x : ℕ,
          C * (x : ℝ) ^ ((1 / 2 : ℝ) + ε)
            <
          |(L x : ℝ)|

/--
Prime multiplication flips Liouville sign.

This is the concrete arithmetic instance of `sign_flip_of_rank_one_descent`.
-/
theorem liouville_flip_of_mul_prime
  {p m : ℕ}
  (hp : p.Prime) :
    liouville (p * m) = - liouville m := by
  rw [liouville_apply_mul]
  rw [liouville_apply hp.ne_zero]
  rw [cardFactors_apply_prime hp]
  norm_num

/-!
## 3. Morphisms and transfer of jumps
-/

/--
A strict rank/parity homomorphism preserves rank and sign exactly.
-/
structure RankParityHom
  (S T : RankParitySystem) where

  toFun :
    S.State → T.State

  rank_preserve :
    ∀ s,
      T.rank (toFun s) = S.rank s

  sign_preserve :
    ∀ s,
      T.sign (toFun s) = S.sign s

/--
A rank/parity hom maps jumps to jumps.
-/
def RankParityHom.mapJump
  {S T : RankParitySystem}
  (F : RankParityHom S T)
  (J : RankEnergyJump S) :
    RankEnergyJump T :=
{
  before := F.toFun J.before
  after := F.toFun J.after

  rank_changes := by
    intro h
    apply J.rank_changes
    calc
      S.rank J.before = T.rank (F.toFun J.before) := by
        rw [F.rank_preserve]
      _ = T.rank (F.toFun J.after) := h
      _ = S.rank J.after := by
        rw [F.rank_preserve]

  sign_changes := by
    intro h
    apply J.sign_changes
    calc
      S.sign J.before = T.sign (F.toFun J.before) := by
        rw [F.sign_preserve]
      _ = T.sign (F.toFun J.after) := h
      _ = S.sign J.after := by
        rw [F.sign_preserve]
}

/-!
## 4. Why localization is a real extra input
-/

inductive TwoState
| lo
| hi
deriving DecidableEq

/--
A toy global system with a genuine jump.
-/
def TwoStateRankSystem : RankParitySystem :=
{
  State := TwoState

  rank := fun s =>
    match s with
    | TwoState.lo => 0
    | TwoState.hi => 1

  sign := fun s =>
    (-1 : ℤ) ^
      match s with
      | TwoState.lo => 0
      | TwoState.hi => 1

  sign_eq_rank := by
    intro s
    cases s <;> rfl
}

/--
The toy global system has a jump.
-/
theorem twoState_has_jump :
    Nonempty (RankEnergyJump TwoStateRankSystem) := by
  refine ⟨?_⟩
  refine
  {
    before := TwoState.lo
    after := TwoState.hi
    rank_changes := ?_
    sign_changes := ?_
  }

  · exact fun h => absurd h (by decide)

  · exact fun h => absurd h (by decide)

/--
A one-point local system with no possible jump.
-/
def UnitRankSystem : RankParitySystem :=
{
  State := PUnit

  rank := fun _ => 0

  sign := fun _ => 1

  sign_eq_rank := by
    intro s
    norm_num
}

/--
The one-point local system has no jump.
-/
theorem unit_no_jump :
    ¬ Nonempty (RankEnergyJump UnitRankSystem) := by
  intro h
  rcases h with ⟨J⟩
  cases J.before
  cases J.after
  exact J.rank_changes rfl

/--
Conclusion:
having the same formula `sign = (-1)^rank` does not by itself transfer a
jump from one system to another.

One needs an actual localization map/bridge.
-/
theorem rank_law_alone_does_not_localize :
    Nonempty (RankEnergyJump TwoStateRankSystem)
      ∧
    ¬ Nonempty (RankEnergyJump UnitRankSystem) :=
  ⟨twoState_has_jump, unit_no_jump⟩

/-!
## 5. The localization bridge
-/

/--
A constructive localization bridge from a global proposition `V`
—for us, `LiouvilleViolation`—
to a local rank/parity system.

This is the exact remaining mathematical bridge.
-/
structure RankJumpLocalization
  (V : Prop)
  (Local : RankParitySystem) where

  chooseBefore :
    V → Local.State

  chooseAfter :
    V → Local.State

  rank_changes :
    ∀ hV : V,
      Local.rank (chooseBefore hV)
        ≠
      Local.rank (chooseAfter hV)

  sign_changes :
    ∀ hV : V,
      Local.sign (chooseBefore hV)
        ≠
      Local.sign (chooseAfter hV)

/--
The local twin-carrier jump proposition for a local rank/parity system.
-/
def TwinCarrierEnergyJump
  (TwinSystem : RankParitySystem) : Prop :=
  Nonempty (RankEnergyJump TwinSystem)

/--
The core surrounding theorem:
localization turns a global Liouville violation into a local twin-carrier
energy jump.
-/
theorem twinCarrierJump_of_liouvilleViolation
  {TwinSystem : RankParitySystem}
  (Loc : RankJumpLocalization LiouvilleViolation TwinSystem)
  (hV : LiouvilleViolation) :
    TwinCarrierEnergyJump TwinSystem := by
  exact ⟨
    {
      before := Loc.chooseBefore hV
      after := Loc.chooseAfter hV
      rank_changes := Loc.rank_changes hV
      sign_changes := Loc.sign_changes hV
    }
  ⟩

/--
Equivalent compact form of the localization target.
-/
def RankJumpLocalizationTarget
  (TwinSystem : RankParitySystem) : Prop :=
  LiouvilleViolation → TwinCarrierEnergyJump TwinSystem

/--
A constructive `RankJumpLocalization` implies the compact localization target.
-/
theorem localizationTarget_of_rankJumpLocalization
  {TwinSystem : RankParitySystem}
  (Loc : RankJumpLocalization LiouvilleViolation TwinSystem) :
    RankJumpLocalizationTarget TwinSystem := by
  intro hV
  exact twinCarrierJump_of_liouvilleViolation Loc hV

/-!
## 6. Closed paid factories are impossible
-/

/--
A factory form for an impossible closed paid engine.

It provides:
1. a closed paid dynamics,
2. a legal seed,
3. a successor from every legal state.
-/
structure ClosedPaidFactory where

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

Use `Classical.choose` to avoid illegal Prop-to-Type elimination.
-/
noncomputable def ClosedPaidFactory.nextU
  (F : ClosedPaidFactory)
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
The infinite legal path generated by a factory.
-/
noncomputable def ClosedPaidFactory.pathU
  (F : ClosedPaidFactory) :
    ℕ → {s : F.State // F.dyn.Universe s}
| 0 =>
    ⟨F.seed, F.seed_in_universe⟩
| n + 1 =>
    (F.nextU (ClosedPaidFactory.pathU F n)).1

/--
Every adjacent pair in the generated path is connected by `Step`.
-/
theorem ClosedPaidFactory.pathU_step
  (F : ClosedPaidFactory) :
    ∀ n,
      F.Step
        (ClosedPaidFactory.pathU F n).1
        (ClosedPaidFactory.pathU F (n+1)).1 := by
  intro n
  change F.Step
    (ClosedPaidFactory.pathU F n).1
    ((F.nextU (ClosedPaidFactory.pathU F n)).1).1
  exact (F.nextU (ClosedPaidFactory.pathU F n)).2

/--
No closed paid factory can exist.
-/
theorem no_closedPaidFactory :
    ¬ Nonempty ClosedPaidFactory := by
  intro h
  rcases h with ⟨F⟩

  exact no_infinite_closed_paid_run F.dyn
    ⟨
      (fun n => (ClosedPaidFactory.pathU F n).1),
      (ClosedPaidFactory.pathU F 0).2,
      ClosedPaidFactory.pathU_step F
    ⟩

/-!
## 7. Spectral-to-twin bridge around the localization node
-/

/--
A full bridge package from off-critical zeros to the impossible twin engine,
factored through LiouvilleViolation and a localized twin-carrier rank jump.

`OffCriticalZero` is kept abstract here; it can be instantiated with the
OffCriticalZero type from the Riemann module.
-/
structure SpectralToTwinRankBridge
  (OffCriticalZero : Type)
  (TwinSystem : RankParitySystem) where

  zero_to_liouvilleViolation :
    OffCriticalZero →
      LiouvilleViolation

  localization :
    RankJumpLocalization LiouvilleViolation TwinSystem

  jump_to_factory :
    TwinCarrierEnergyJump TwinSystem →
      Nonempty ClosedPaidFactory

/--
An off-critical zero produces an impossible closed paid factory, assuming the
spectral-to-twin bridge.
-/
theorem twinFactory_of_offCriticalZero
  {OffCriticalZero : Type}
  {TwinSystem : RankParitySystem}
  (B : SpectralToTwinRankBridge OffCriticalZero TwinSystem)
  (Z : OffCriticalZero) :
    Nonempty ClosedPaidFactory := by

  have hV :
      LiouvilleViolation :=
    B.zero_to_liouvilleViolation Z

  have hJump :
      TwinCarrierEnergyJump TwinSystem :=
    twinCarrierJump_of_liouvilleViolation
      B.localization hV

  exact B.jump_to_factory hJump

/--
Since closed paid factories are impossible, the bridge rules out off-critical
zeros.
-/
theorem no_offCriticalZero_from_spectralTwinBridge
  {OffCriticalZero : Type}
  {TwinSystem : RankParitySystem}
  (B : SpectralToTwinRankBridge OffCriticalZero TwinSystem) :
    ¬ Nonempty OffCriticalZero := by
  intro hZ
  rcases hZ with ⟨Z⟩

  have hFactory :
      Nonempty ClosedPaidFactory :=
    twinFactory_of_offCriticalZero B Z

  exact no_closedPaidFactory hFactory

/--
Generic final logic:
if `¬ RH ↔ Nonempty OffCriticalZero`, then absence of off-critical zeros gives RH.
-/
theorem RH_of_no_offCriticalZero
  {RH : Prop}
  {OffCriticalZero : Type}
  (hiff :
    ¬ RH ↔ Nonempty OffCriticalZero)
  (hNo :
    ¬ Nonempty OffCriticalZero) :
    RH := by
  by_contra hNotRH
  exact hNo (hiff.mp hNotRH)

/--
Combining the generic RH equivalence with the spectral-to-twin bridge.
-/
theorem RH_of_spectralTwinBridge
  {RH : Prop}
  {OffCriticalZero : Type}
  {TwinSystem : RankParitySystem}
  (hiff :
    ¬ RH ↔ Nonempty OffCriticalZero)
  (B : SpectralToTwinRankBridge OffCriticalZero TwinSystem) :
    RH :=
  RH_of_no_offCriticalZero hiff
    (no_offCriticalZero_from_spectralTwinBridge B)

/-!
## 8. Final status

Everything around the localization node is formalized.

Proved:
* rank-one descent flips sign;
* Liouville is a rank/parity system;
* homomorphisms map jumps to jumps;
* rank-law alone does not localize jumps;
* `RankJumpLocalization` gives
  `LiouvilleViolation → TwinCarrierEnergyJump`;
* spectral-to-twin bridge gives an impossible closed paid factory;
* impossible factory contradicts `no_infinite_closed_paid_run`;
* with `¬RH ↔ Nonempty OffCriticalZero`, the bridge gives RH.

Still hard:
* construct `RankJumpLocalization LiouvilleViolation TwinSystem`;
* construct `zero_to_liouvilleViolation`;
* construct `jump_to_factory`.

The central mathematical node remains:

```lean
def RankJumpLocalizationTarget
  (TwinSystem : RankParitySystem) : Prop :=
  LiouvilleViolation → TwinCarrierEnergyJump TwinSystem
```
-/


/-! ## 8bis. ЧЕСТНОСТЬ: скрытое содержание моста (машинно)

`no_closedPaidFactory` безусловна ⟹ поле `jump_to_factory` эквивалентно `¬TwinJump`, а весь мост
форсит `¬LiouvilleViolation` (= LiouvilleBound-содержание, RH-силы). Мост — не нейтральная редукция:
он НЕСЁТ в себе и «джампа нет», и «дисбаланса нет». -/

/-- **`jumpToFactory_iff_no_jump` — ДОКАЗАНА (честность).** Поле `jump_to_factory` ⟺ `¬TwinJump`
    (factory безусловно невозможна, значит импликация выполнима лишь вакуумно). -/
theorem jumpToFactory_iff_no_jump (TwinSystem : RankParitySystem) :
    (TwinCarrierEnergyJump TwinSystem → Nonempty ClosedPaidFactory) ↔
    ¬ TwinCarrierEnergyJump TwinSystem := by
  constructor
  · intro h hJump
    exact no_closedPaidFactory (h hJump)
  · intro hNo hJump
    exact absurd hJump hNo

/-- **`spectralBridge_forces_no_violation` — ДОКАЗАНА (честность).** Любой `SpectralToTwinRankBridge`
    форсит `¬LiouvilleViolation`: localization даёт Violation→Jump, jump_to_factory даёт ¬Jump.
    То есть мост скрыто содержит LiouvilleBound (арифметическую RH-форму) — не нейтральный вход. -/
theorem spectralBridge_forces_no_violation {OffCriticalZero : Type}
    {TwinSystem : RankParitySystem}
    (B : SpectralToTwinRankBridge OffCriticalZero TwinSystem) :
    ¬ LiouvilleViolation := by
  intro hV
  have hJump : TwinCarrierEnergyJump TwinSystem :=
    twinCarrierJump_of_liouvilleViolation B.localization hV
  exact no_closedPaidFactory (B.jump_to_factory hJump)

end EuclidsPath.RankJumpBridge
