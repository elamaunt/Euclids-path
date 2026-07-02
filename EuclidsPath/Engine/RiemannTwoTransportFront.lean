/-
  RiemannTwoTransportFront — декомпозиция живого входа №1 RH-ветки (EngineBridge)
  в two-transport форму. Кирпичи: Riemann_two_transport_engine_bridge_patch +
  Riemann_two_transport_local_certificate_patch. Проза: prose/30.

  ЗДЕСЬ (чистая сборка, std аксиомы, без sorry):
    * TwoTransportLaw — non-opaque замена OffCriticalRiemannEngineBridge:
      все paid-dynamics обязательства выставлены полями;
    * локальный слой: TransportSide (flip-инволюция), SignedImbalance (paidWork > 0),
      SpectralTwoTransportSplit → LocalTwoTransportMechanism (левый И правый
      шаги с положительной работой, tethered-вселенная) → law core → фабрика;
    * сборочные теоремы: split + realization ⟹ certificate ⟹ core-мост ⟹
      старый мост ⟹ RH; TwoTransportStrictFront — точная карта обязательств.

  ⚠️ МАШИННАЯ ЧЕСТНОСТЬ (конкретный слой, добавлен при интеграции):
    * поля Universe/Total/Work закона ОТДЕЛЬНЫ от closedPaid — фабрика
      достигается только КОГЕРЕНТНЫМИ законами (CoherentLaw);
    * no_coherent_twoTransportLaw / no_coherent_lawCore — когерентный закон
      для реального нуля ПУСТ (фабрика безусловно пуста: engine-killer);
    * coherentTwoTransportBridge_iff_RH — когерентный two-transport мост
      ⟺ RH ДОСЛОВНО: циркулярность старого моста НАСЛЕДУЕТСЯ; декомпозиция —
      карта обязательств, а не некруговой путь;
    * regateTrivially — аудит-гейты zero_anchored/non_circular свободны
      (True-перегейтовка): маркеры, не проверки.
  Фиксы кирпичей: builder-дефы объявлены : Prop, но Law → Factory — Type 1
  (аннотация снята); слоган §6 — Type-конъюнкт обёрнут в Nonempty.
-/
import Mathlib
import EuclidsPath.Engine.ClosedUniverse
import EuclidsPath.Engine.RiemannImpossibleEngineOff

set_option autoImplicit false

namespace EuclidsPath
namespace RiemannImpossibleEngineOff

/-!
The declarations in this section are expected to be available from the existing
checked Riemann engine file.  They are repeated as comments rather than axioms.

```
structure OffCriticalZero where ...
structure ClosedPaidDynamics (State : Type) (Step : State → State → Prop) where ...
structure RiemannEngineFactoryOff (Z : OffCriticalZero) where ...
def OffCriticalRiemannEngineBridge : Prop :=
  ∀ Z : OffCriticalZero, Nonempty (RiemannEngineFactoryOff Z)
theorem RH_of_offCriticalRiemannEngineBridge :
  OffCriticalRiemannEngineBridge → RiemannHypothesis
```
-/

/--
A concrete two-transport law attached to one off-critical zero.

This is the first non-opaque replacement for `OffCriticalRiemannEngineBridge`.
It is intentionally not just a bare `Nonempty (RiemannEngineFactoryOff Z)`:
all paid-dynamics fields are exposed as obligations.

Interpretation of the fields:

* `State`, `Step`, `Universe` describe the transport universe.
* `Total` is the finite budget/potential.
* `Work` is the positive paid cost of a legal transport step.
* `closed`, `work_pos`, `paid` say this is a closed paid dynamics.
* `seed` and `next` say the off-critical zero regenerates the transport forever.

The proof obligations hidden in the old bridge are now exactly visible here.
-/
structure TwoTransportLaw
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type)
  (Z : OffCriticalZero) where

  State : Type

  Step : State → State → Prop

  Universe : State → Prop

  Total : State → ℕ

  Work : State → State → ℕ

  closedPaid : ClosedPaidDynamics State Step

  seed : State

  seed_in_universe : Universe seed

  next : ∀ x : State, Universe x → ∃ y : State, Step x y

  /-- Audit marker: this transport is produced from the zero, not postulated globally. -/
  zero_anchored : Prop

  zero_anchored_proof : zero_anchored

  /-- Audit marker: the construction does not merely assert `¬ RH` or LiouvilleBound. -/
  non_circular : Prop

  non_circular_proof : non_circular

/-!
The next section is parameterized over the existing checked objects.  This makes
the assembly theorem independent of the concrete module path, and also gives a
small compile-friendly core if the repo names are imported as parameters.
-/

section AbstractAssembly

variable {OffCriticalZero : Type}
variable {RiemannHypothesis : Prop}
variable {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
variable {RiemannEngineFactoryOff : OffCriticalZero → Type}

/--
How to turn the exposed two-transport law into the already-existing factory
object.  In the concrete repo this map is usually just structure construction:
make `dyn` from `closedPaid`, reuse `seed`, `seed_in_universe`, and `next`.

It is kept as a parameter here because the exact field names of
`ClosedPaidDynamics` are already fixed in the imported file.
-/
def TwoTransportLawBuildsFactory :=
  ∀ Z : OffCriticalZero,
    TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z →
      RiemannEngineFactoryOff Z

/--
The bridge in its non-opaque two-transport form.
-/
def TwoTransportBridge : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z)

/--
The old off-critical engine bridge, written in parameterized form.
-/
def OffCriticalEngineBridgeAbstract : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (RiemannEngineFactoryOff Z)

/--
The exact formal converter:

`TwoTransportBridge` is sufficient for the old `OffCriticalRiemannEngineBridge`.

No analytic theorem is used here; this is pure structure assembly.
-/
theorem offCriticalEngineBridge_of_twoTransportBridge
    (hBuild : TwoTransportLawBuildsFactory
      (OffCriticalZero := OffCriticalZero)
      (ClosedPaidDynamics := ClosedPaidDynamics)
      (RiemannEngineFactoryOff := RiemannEngineFactoryOff))
    (hTwo : TwoTransportBridge
      (OffCriticalZero := OffCriticalZero)
      (ClosedPaidDynamics := ClosedPaidDynamics)) :
    OffCriticalEngineBridgeAbstract
      (OffCriticalZero := OffCriticalZero)
      (RiemannEngineFactoryOff := RiemannEngineFactoryOff) := by
  intro Z
  rcases hTwo Z with ⟨T⟩
  exact ⟨hBuild Z T⟩

/--
Full RH assembly from the two-transport bridge.

This is the theorem we want the live route to use:
prove `TwoTransportBridge`, then the previously checked engine-killer finishes RH.
-/
theorem riemannHypothesis_of_twoTransportBridge
    (hRH_of_engine :
      OffCriticalEngineBridgeAbstract
        (OffCriticalZero := OffCriticalZero)
        (RiemannEngineFactoryOff := RiemannEngineFactoryOff) →
          RiemannHypothesis)
    (hBuild : TwoTransportLawBuildsFactory
      (OffCriticalZero := OffCriticalZero)
      (ClosedPaidDynamics := ClosedPaidDynamics)
      (RiemannEngineFactoryOff := RiemannEngineFactoryOff))
    (hTwo : TwoTransportBridge
      (OffCriticalZero := OffCriticalZero)
      (ClosedPaidDynamics := ClosedPaidDynamics)) :
    RiemannHypothesis := by
  exact hRH_of_engine
    (offCriticalEngineBridge_of_twoTransportBridge
      (OffCriticalZero := OffCriticalZero)
      (ClosedPaidDynamics := ClosedPaidDynamics)
      (RiemannEngineFactoryOff := RiemannEngineFactoryOff)
      hBuild hTwo)

end AbstractAssembly

/-!
## Concrete repo-facing specialization

Once the import path is enabled, the intended theorem shape is:

```
def TwoTransportBridgeConcrete : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z)

theorem RH_of_TwoTransportBridgeConcrete
    (hBuild : ∀ Z, TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z →
      RiemannEngineFactoryOff Z)
    (hTwo : TwoTransportBridgeConcrete) :
    RiemannHypothesis :=
  riemannHypothesis_of_twoTransportBridge
    RH_of_offCriticalRiemannEngineBridge
    hBuild
    hTwo
```

This patch deliberately does not fill `hTwo`.  Filling `hTwo` is exactly the
remaining hard analytic/dynamical work: build a closed paid two-transport
system from an arbitrary off-critical nontrivial zero.
-/

/--
Audit statement for the next target.

A genuine proof of the bridge must produce this data from `Z`; it must not merely
use the contradiction theorem, LiouvilleBound, or an equivalent form of RH.
-/
structure TwoTransportNextObligation
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type) where

  bridge : ∀ Z : OffCriticalZero,
    Nonempty (TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z)

  no_RH_leak : Prop

  no_RH_leak_proof : no_RH_leak

  no_vacuous_global_factory : Prop

  no_vacuous_global_factory_proof : no_vacuous_global_factory

/--
Slogan theorem: after the structural engine file, the remaining live route is
exactly the construction of a non-vacuous `TwoTransportLaw` from each
`OffCriticalZero`.
-/
theorem twoTransport_is_the_live_engineBridge_front
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    (O : TwoTransportNextObligation OffCriticalZero ClosedPaidDynamics) :
    ∀ Z : OffCriticalZero,
      Nonempty (TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z) := by
  exact O.bridge

end RiemannImpossibleEngineOff
end EuclidsPath

namespace EuclidsPath
namespace RiemannImpossibleEngineOff
namespace TwoTransportLocal

/-!
## 1. Transport sides and signed imbalance

The route is genuinely two-transport only if the zero produces two distinguishable
transport directions/sides and a visible nonzero imbalance.
-/

/-- The two transport directions. -/
inductive TransportSide where
  | left
  | right
  deriving DecidableEq, Repr

namespace TransportSide

/-- The opposite transport direction. -/
def flip : TransportSide → TransportSide
  | left => right
  | right => left

@[simp] theorem flip_left : flip left = right := rfl
@[simp] theorem flip_right : flip right = left := rfl

/-- Flipping twice returns the original side. -/
@[simp] theorem flip_flip (s : TransportSide) : flip (flip s) = s := by
  cases s <;> rfl

/-- A side is never equal to its flip. -/
theorem ne_flip (s : TransportSide) : s ≠ flip s := by
  cases s <;> decide

end TransportSide

/--
A signed imbalance extracted from an off-critical zero.

Only nonzero signed imbalance can power a paid two-transport mechanism.  The
actual analytic construction of `raw` is deliberately not included here; it is
part of the remaining bridge.
-/
structure SignedImbalance where
  raw : ℤ
  nonzero : raw ≠ 0

namespace SignedImbalance

/-- A strictly positive natural work token attached to a nonzero imbalance. -/
def paidWork (g : SignedImbalance) : ℕ :=
  Nat.succ (Int.natAbs g.raw)

/-- The work token is always positive. -/
theorem paidWork_pos (g : SignedImbalance) : 0 < g.paidWork := by
  exact Nat.succ_pos _

end SignedImbalance

/-!
## 2. Zero-anchored spectral split
-/

/--
A spectral two-transport split attached to one off-critical zero `Z`.

This is the first genuinely analytic object the bridge must build.  It is not a
factory and not a contradiction: it is local data extracted from the zero.

`zero_anchored` and `non_circular` are explicit audit gates.  In the concrete
repo they should be instantiated by meaningful propositions, e.g. “the split is
constructed from the completed zeta functional equation at `Z`” and “the
construction does not use RH/LiouvilleBound/OffCriticalRiemannEngineBridge”.
-/
structure SpectralTwoTransportSplit
  (OffCriticalZero : Type)
  (Z : OffCriticalZero) where

  imbalance : SignedImbalance

  left_label : Type
  right_label : Type

  zero_anchored : Prop
  zero_anchored_proof : zero_anchored

  non_circular : Prop
  non_circular_proof : non_circular

/-- The first bridge obligation: every off-critical zero has such a split. -/
def SpectralSplitBridge (OffCriticalZero : Type) : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (SpectralTwoTransportSplit OffCriticalZero Z)

/-!
## 3. Local closed paid realization of a split
-/

/--
A law shaped like the previous `TwoTransportLaw`, but kept local to this file.

This mirrors the previous patch's fields and is used for pure assembly.
-/
structure TwoTransportLawCore
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type)
  (Z : OffCriticalZero) where

  State : Type

  Step : State → State → Prop

  Universe : State → Prop

  Total : State → ℕ

  Work : State → State → ℕ

  closedPaid : ClosedPaidDynamics State Step

  seed : State

  seed_in_universe : Universe seed

  next : ∀ x : State, Universe x → ∃ y : State, Step x y

  zero_anchored : Prop

  zero_anchored_proof : zero_anchored

  non_circular : Prop

  non_circular_proof : non_circular

/-- The core two-transport bridge. -/
def TwoTransportBridgeCore
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type) : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z)

/--
A concrete local mechanism realizing a spectral split as a closed paid dynamics.

This is stronger and less vacuous than a bare `Nonempty` target:

* every state in the universe is tethered to the zero-generated split;
* both left and right transports are available locally;
* at least one paid transport can be chosen from every legal state;
* the audit fields from the split are preserved.

The exact analytic/dynamical construction of the fields is the remaining work.
-/
structure LocalTwoTransportMechanism
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type)
  (Z : OffCriticalZero)
  (S : SpectralTwoTransportSplit OffCriticalZero Z) where

  State : Type

  Step : State → State → Prop

  Universe : State → Prop

  Total : State → ℕ

  Work : State → State → ℕ

  closedPaid : ClosedPaidDynamics State Step

  side : State → TransportSide

  /-- States carrying this mechanism remain tethered to the chosen zero split. -/
  zeroTether : State → Prop

  /-- The legal universe does not contain untethered states. -/
  universe_tethered : ∀ x : State, Universe x → zeroTether x

  seed : State

  seed_in_universe : Universe seed

  /-- One local left transport step. -/
  leftStep :
    ∀ x : State,
      Universe x →
      zeroTether x →
        {y : State //
          Step x y ∧ Universe y ∧ zeroTether y ∧
          side y = TransportSide.left ∧ 0 < Work x y}

  /-- One local right transport step. -/
  rightStep :
    ∀ x : State,
      Universe x →
      zeroTether x →
        {y : State //
          Step x y ∧ Universe y ∧ zeroTether y ∧
          side y = TransportSide.right ∧ 0 < Work x y}

  /-- Audit: the two transports are not a single hidden gauge move. -/
  transports_distinguishable : Prop

  transports_distinguishable_proof : transports_distinguishable

namespace LocalTwoTransportMechanism

/--
A local mechanism gives the previous two-transport law core by choosing the left
transport as the successor.  The right transport and distinguishability remain as
audit data ensuring that the certificate was genuinely two-sided.
-/
noncomputable def toLawCore
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {Z : OffCriticalZero}
    {S : SpectralTwoTransportSplit OffCriticalZero Z}
    (M : LocalTwoTransportMechanism OffCriticalZero ClosedPaidDynamics Z S) :
    TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z :=
{
  State := M.State
  Step := M.Step
  Universe := M.Universe
  Total := M.Total
  Work := M.Work
  closedPaid := M.closedPaid
  seed := M.seed
  seed_in_universe := M.seed_in_universe
  next := by
    intro x hx
    let hxTether : M.zeroTether x := M.universe_tethered x hx
    let y := M.leftStep x hx hxTether
    exact ⟨y.1, y.2.1⟩
  zero_anchored := S.zero_anchored
  zero_anchored_proof := S.zero_anchored_proof
  non_circular := S.non_circular
  non_circular_proof := S.non_circular_proof
}

end LocalTwoTransportMechanism

/--
A complete local certificate for one off-critical zero: first produce the split,
then realize it as a local mechanism.
-/
structure LocalTwoTransportCertificate
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type)
  (Z : OffCriticalZero) where

  split : SpectralTwoTransportSplit OffCriticalZero Z

  mechanism : LocalTwoTransportMechanism OffCriticalZero ClosedPaidDynamics Z split

namespace LocalTwoTransportCertificate

/-- A local certificate gives the core two-transport law. -/
noncomputable def toLawCore
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {Z : OffCriticalZero}
    (C : LocalTwoTransportCertificate OffCriticalZero ClosedPaidDynamics Z) :
    TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z :=
  C.mechanism.toLawCore

/-- Every local certificate contains a genuine spectral split. -/
theorem has_spectral_split
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {Z : OffCriticalZero}
    (C : LocalTwoTransportCertificate OffCriticalZero ClosedPaidDynamics Z) :
    Nonempty (SpectralTwoTransportSplit OffCriticalZero Z) := by
  exact ⟨C.split⟩

end LocalTwoTransportCertificate

/-- Local certificate bridge: every off-critical zero has a local certificate. -/
def LocalTwoTransportCertificateBridge
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type) : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (LocalTwoTransportCertificate OffCriticalZero ClosedPaidDynamics Z)

/-- Realize every spectral split as a local two-transport mechanism. -/
def SpectralSplitRealizationBridge
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type) : Prop :=
  ∀ Z : OffCriticalZero,
  ∀ S : SpectralTwoTransportSplit OffCriticalZero Z,
    Nonempty (LocalTwoTransportMechanism OffCriticalZero ClosedPaidDynamics Z S)

/-!
## 4. Pure assembly theorems
-/

/-- A local certificate bridge gives the core two-transport bridge. -/
theorem twoTransportBridgeCore_of_localCertificateBridge
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    (hLocal : LocalTwoTransportCertificateBridge OffCriticalZero ClosedPaidDynamics) :
    TwoTransportBridgeCore OffCriticalZero ClosedPaidDynamics := by
  intro Z
  rcases hLocal Z with ⟨C⟩
  exact ⟨C.toLawCore⟩

/-- The local bridge cannot be vacuous: it forces the spectral split bridge. -/
theorem spectralSplitBridge_of_localCertificateBridge
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    (hLocal : LocalTwoTransportCertificateBridge OffCriticalZero ClosedPaidDynamics) :
    SpectralSplitBridge OffCriticalZero := by
  intro Z
  rcases hLocal Z with ⟨C⟩
  exact C.has_spectral_split

/-- If a zero has no spectral split, it has no local certificate. -/
theorem no_localCertificate_without_spectralSplit
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {Z : OffCriticalZero}
    (hNoSplit : ¬ Nonempty (SpectralTwoTransportSplit OffCriticalZero Z)) :
    ¬ Nonempty (LocalTwoTransportCertificate OffCriticalZero ClosedPaidDynamics Z) := by
  intro hCert
  rcases hCert with ⟨C⟩
  exact hNoSplit C.has_spectral_split

/--
The two sub-bridges together give the local certificate bridge.

This is the precise decomposition of the remaining front:

  off-critical zero
    → spectral split
    → local closed paid realization
    → two-transport law
    → engine factory
    → RH.
-/
theorem localCertificateBridge_of_split_and_realization
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    (hSplit : SpectralSplitBridge OffCriticalZero)
    (hRealize : SpectralSplitRealizationBridge OffCriticalZero ClosedPaidDynamics) :
    LocalTwoTransportCertificateBridge OffCriticalZero ClosedPaidDynamics := by
  intro Z
  rcases hSplit Z with ⟨S⟩
  rcases hRealize Z S with ⟨M⟩
  exact ⟨{ split := S, mechanism := M }⟩

/--
Consequently, split + realization give the core two-transport bridge.
-/
theorem twoTransportBridgeCore_of_split_and_realization
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    (hSplit : SpectralSplitBridge OffCriticalZero)
    (hRealize : SpectralSplitRealizationBridge OffCriticalZero ClosedPaidDynamics) :
    TwoTransportBridgeCore OffCriticalZero ClosedPaidDynamics := by
  exact twoTransportBridgeCore_of_localCertificateBridge
    (localCertificateBridge_of_split_and_realization hSplit hRealize)

/-!
## 5. Connection to the concrete old engine bridge

The next definitions keep the concrete repo dependency abstract.  Supply a map
from `TwoTransportLawCore Z` to the already checked `RiemannEngineFactoryOff Z`,
and the checked theorem `OffCriticalRiemannEngineBridge → RH` finishes.
-/

/-- A converter from this local core law to the existing external law/factory. -/
def LawCoreBuildsFactory
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type)
  (RiemannEngineFactoryOff : OffCriticalZero → Type) :=
  ∀ Z : OffCriticalZero,
    TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z →
      RiemannEngineFactoryOff Z

/-- Old engine bridge in abstract form. -/
def OffCriticalEngineBridgeAbstract
  (OffCriticalZero : Type)
  (RiemannEngineFactoryOff : OffCriticalZero → Type) : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (RiemannEngineFactoryOff Z)

/-- Core two-transport bridge implies the old engine bridge. -/
theorem offCriticalEngineBridge_of_twoTransportBridgeCore
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {RiemannEngineFactoryOff : OffCriticalZero → Type}
    (hBuild : LawCoreBuildsFactory OffCriticalZero ClosedPaidDynamics RiemannEngineFactoryOff)
    (hTwo : TwoTransportBridgeCore OffCriticalZero ClosedPaidDynamics) :
    OffCriticalEngineBridgeAbstract OffCriticalZero RiemannEngineFactoryOff := by
  intro Z
  rcases hTwo Z with ⟨T⟩
  exact ⟨hBuild Z T⟩

/--
Full RH assembly from the strict local split and realization obligations.

Everything here is pure assembly; all analytic content is confined to:

* `SpectralSplitBridge`;
* `SpectralSplitRealizationBridge`;
* the concrete `LawCoreBuildsFactory` structure map.
-/
theorem riemannHypothesis_of_spectralSplit_and_realization
    {OffCriticalZero : Type}
    {RiemannHypothesis : Prop}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {RiemannEngineFactoryOff : OffCriticalZero → Type}
    (hRH_of_engine :
      OffCriticalEngineBridgeAbstract OffCriticalZero RiemannEngineFactoryOff →
        RiemannHypothesis)
    (hBuild : LawCoreBuildsFactory OffCriticalZero ClosedPaidDynamics RiemannEngineFactoryOff)
    (hSplit : SpectralSplitBridge OffCriticalZero)
    (hRealize : SpectralSplitRealizationBridge OffCriticalZero ClosedPaidDynamics) :
    RiemannHypothesis := by
  apply hRH_of_engine
  exact offCriticalEngineBridge_of_twoTransportBridgeCore hBuild
    (twoTransportBridgeCore_of_split_and_realization hSplit hRealize)

/-!
## 6. Final audit object for the live front
-/

/--
The maximally strict current front for the engine route.

Compared with the old `EngineBridge`, this records exactly what must be shown:

a. construct a zero-anchored noncircular spectral split from every off-critical zero;
b. realize every such split as a closed paid local two-transport mechanism;
c. convert the local law into the existing engine factory structure.
-/
structure TwoTransportStrictFront
  (OffCriticalZero : Type)
  (ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type)
  (RiemannEngineFactoryOff : OffCriticalZero → Type) where

  spectral_split : SpectralSplitBridge OffCriticalZero

  local_realization : SpectralSplitRealizationBridge OffCriticalZero ClosedPaidDynamics

  builds_factory : LawCoreBuildsFactory OffCriticalZero ClosedPaidDynamics RiemannEngineFactoryOff

  no_RH_leak : Prop

  no_RH_leak_proof : no_RH_leak

  no_Liouville_leak : Prop

  no_Liouville_leak_proof : no_Liouville_leak

  no_vacuous_global_factory : Prop

  no_vacuous_global_factory_proof : no_vacuous_global_factory

/-- The strict front gives the old engine bridge. -/
theorem offCriticalEngineBridge_of_strictFront
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {RiemannEngineFactoryOff : OffCriticalZero → Type}
    (F : TwoTransportStrictFront OffCriticalZero ClosedPaidDynamics RiemannEngineFactoryOff) :
    OffCriticalEngineBridgeAbstract OffCriticalZero RiemannEngineFactoryOff := by
  exact offCriticalEngineBridge_of_twoTransportBridgeCore F.builds_factory
    (twoTransportBridgeCore_of_split_and_realization
      F.spectral_split F.local_realization)

/-- The strict front proves RH once connected to the checked engine-killer theorem. -/
theorem riemannHypothesis_of_twoTransportStrictFront
    {OffCriticalZero : Type}
    {RiemannHypothesis : Prop}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {RiemannEngineFactoryOff : OffCriticalZero → Type}
    (hRH_of_engine :
      OffCriticalEngineBridgeAbstract OffCriticalZero RiemannEngineFactoryOff →
        RiemannHypothesis)
    (F : TwoTransportStrictFront OffCriticalZero ClosedPaidDynamics RiemannEngineFactoryOff) :
    RiemannHypothesis := by
  exact hRH_of_engine (offCriticalEngineBridge_of_strictFront F)

/--
Slogan theorem: after the trivial-zero firewall and rank-jump collapse, the live
engine route is exactly the strict two-transport front.
-/
theorem twoTransportStrictFront_slogan
    {OffCriticalZero : Type}
    {ClosedPaidDynamics : (State : Type) → (State → State → Prop) → Type}
    {RiemannEngineFactoryOff : OffCriticalZero → Type}
    (F : TwoTransportStrictFront OffCriticalZero ClosedPaidDynamics RiemannEngineFactoryOff) :
    SpectralSplitBridge OffCriticalZero ∧
    SpectralSplitRealizationBridge OffCriticalZero ClosedPaidDynamics ∧
    Nonempty (LawCoreBuildsFactory OffCriticalZero ClosedPaidDynamics
      RiemannEngineFactoryOff) := by
  exact ⟨F.spectral_split, F.local_realization, ⟨F.builds_factory⟩⟩

end TwoTransportLocal
end RiemannImpossibleEngineOff
end EuclidsPath

/-! Конкретный слой + машинная честность -/

namespace EuclidsPath
namespace RiemannImpossibleEngineOff

open EuclidsPath.ClosedUniverse

/-- Когерентность: собственная вселенная закона совпадает со вселенной его
    платной динамики (без этого закон не достигает фабрики). -/
def CoherentLaw {Z : OffCriticalZero}
    (T : TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z) : Prop :=
  ∀ x, T.Universe x ↔ T.closedPaid.Universe x

/-- КОНКРЕТНЫЙ builder: когерентный two-transport закон строит фабрику репо. -/
def factoryOff_of_twoTransportLaw {Z : OffCriticalZero}
    (T : TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z)
    (hC : CoherentLaw T) :
    RiemannEngineFactoryOff Z where
  State := T.State
  Step := T.Step
  dyn := T.closedPaid
  seed := T.seed
  seed_in_universe := (hC T.seed).mp T.seed_in_universe
  next := fun x hx => T.next x ((hC x).mpr hx)

/-- **ЧЕСТНОСТЬ (пустота):** когерентный закон для РЕАЛЬНОГО нуля невозможен —
    он строил бы фабрику, а фабрика безусловно пуста (engine-killer). Выполнить
    обязательство «построй закон из нуля» некруговым образом нельзя: обитаемость
    закона = отсутствие нулей. -/
theorem no_coherent_twoTransportLaw {Z : OffCriticalZero}
    (T : TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z)
    (hC : CoherentLaw T) : False :=
  no_riemannEngineFactoryOff Z ⟨factoryOff_of_twoTransportLaw T hC⟩

/-- Когерентный two-transport мост (конкретная форма фронта). -/
def CoherentTwoTransportBridge : Prop :=
  ∀ Z : OffCriticalZero,
    ∃ T : TwoTransportLaw OffCriticalZero ClosedPaidDynamics Z, CoherentLaw T

/-- **ЧЕСТНОСТЬ (циркулярность наследуется):** когерентный two-transport мост
    ⟺ RH ДОСЛОВНО — как и старый opaque-мост. Декомпозиция полезна как карта
    обязательств, но выполнимой некруговым образом она не стала. -/
theorem coherentTwoTransportBridge_iff_RH :
    CoherentTwoTransportBridge ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply RH_of_offCriticalRiemannEngineBridge
    intro Z
    obtain ⟨T, hC⟩ := h Z
    exact ⟨factoryOff_of_twoTransportLaw T hC⟩
  · intro hRH Z
    exact ((no_riemannEngineFactoryOff Z)
      (offCriticalBridge_iff_RH.mpr hRH Z)).elim

namespace TwoTransportLocal

/-- Когерентность для локального core-закона. -/
def CoherentLawCore {Z : OffCriticalZero}
    (T : TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z) : Prop :=
  ∀ x, T.Universe x ↔ T.closedPaid.Universe x

/-- Builder для core-закона. -/
def factoryOff_of_lawCore {Z : OffCriticalZero}
    (T : TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z)
    (hC : CoherentLawCore T) :
    RiemannEngineFactoryOff Z where
  State := T.State
  Step := T.Step
  dyn := T.closedPaid
  seed := T.seed
  seed_in_universe := (hC T.seed).mp T.seed_in_universe
  next := fun x hx => T.next x ((hC x).mpr hx)

/-- **ЧЕСТНОСТЬ:** когерентный core-закон для реального нуля пуст. -/
theorem no_coherent_lawCore {Z : OffCriticalZero}
    (T : TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z)
    (hC : CoherentLawCore T) : False :=
  no_riemannEngineFactoryOff Z ⟨factoryOff_of_lawCore T hC⟩

/-- **ЧЕСТНОСТЬ (гейты свободны):** аудит-поля zero_anchored/non_circular —
    свободные Prop-поля: любой закон перегейтируется в True-гейты. Гейты —
    документирующие маркеры, НЕ машинная проверка некруговости. -/
def regateTrivially {Z : OffCriticalZero}
    (T : TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z) :
    TwoTransportLawCore OffCriticalZero ClosedPaidDynamics Z :=
  { T with zero_anchored := True, zero_anchored_proof := trivial,
           non_circular := True, non_circular_proof := trivial }

end TwoTransportLocal
end RiemannImpossibleEngineOff
end EuclidsPath
