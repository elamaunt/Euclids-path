/-
  RiemannRankProjection — строгая + градуальная декомпозиция живого узла №8
  RH-ветки (`TwinCarrierPairing.unpaired_gives_jump`).
  Кирпичи: Riemann_rank_projection_strict_patch + Riemann_gradual_rank_overflow_patch.
  Проза: prose/30_RiemannBranch.md (живой фронт).

  ЗДЕСЬ ДОКАЗАНО (std аксиомы, без sorry):
    * `rankProjectionSoundness` — (overflow ⟹ unpaired) + (unpaired ⟹ rank-jump)
      ⟹ (overflow ⟹ rank-jump): строгая проекция;
    * `exists_firstOverflowCrossing` — ДИСКРЕТНАЯ first-crossing лемма (Nat.find):
      положительный дефект где-то ⟹ ПЕРВОЕ пересечение порога с глобальной
      минимальностью; + переход к одношаговой форме (prev_safe ∧ now_pos);
    * `gradualOverflow_forces_rankJump` — градуальная цепь: safe-старт +
      overflow ⟹ first crossing ⟹ unpaired ⟹ rank-jump;
    * СТЫКОВКА (`RiemannRankProjectionBridge`): интерфейс/route-сертификат с
      endpoint-картами поставляет НАСТОЯЩИЙ `TwinCarrierPairing` репо —
      `unpaired_gives_jump` выводится, а не постулируется.

  ЧЕСТНАЯ ГРАНИЦА. RH НЕ доказана; вход №8 НЕ закрыт — он РАСПАЛСЯ на меньшие:
  (A) window-бухгалтерия (RelevantViolation ⟹ градуальное окно конкретного
  ledger'а), (B) first-crossing ⟹ unpaired carrier (локальная capacity/pairing),
  (C) rank-видимость unpaired-carrier'а, (D) endpoint-карты. RH-круговорот
  сюда не втащен: файлы кирпичей не упоминают RiemannHypothesis/LiouvilleBound/
  IrrelevantCancellation. «No-RH-leak аудиты» — документирующие маркеры, НЕ
  проверки (машинно: `rankProjectionAudit_is_free`, `gradualAudit_is_free`).
  Фиксы кирпичей: ASCII `exists` → `∃`; `Nat.pred_lt` → omega; `subst` двух
  проекций → транспорт `▸`.
-/
import Mathlib
import EuclidsPath.Engine.DissipativeCascade

set_option autoImplicit false

namespace RiemannRankProjection

/-!
## 1. Abstract target of the projection

A rank jump is intentionally tiny: it is only the existence of a before/after
rank pair with strict increase.  The concrete repo can later replace `before`
and `after` by its real rank states.
-/

structure RankJumpWitness where
  beforeRank : Int
  afterRank  : Int
  jump       : beforeRank < afterRank

/--
An unpaired carrier is not allowed to be gauge-only.  It must expose a strict
rank jump.

This is the local structural visibility certificate, not an analytic RH input.
In the concrete repo it should be proved from the definition of the
`twin-carrier` rank projection.
-/
structure UnpairedCarrierVisibleRank where
  UnpairedCarrier : Type
  toRankJump : UnpairedCarrier -> RankJumpWitness

/--
The finite pairing/capacity certificate.

`RelevantOverflow` is the concrete event “the relevant carrier mass exceeds
capacity”.  `UnpairedCarrier` is the concrete event “there is an unpaired
carrier”.  The field `overflow_forces_unpaired` is the contrapositive of the
finite cancellation/capacity lemma:

    if there is no unpaired carrier, the relevant part is within capacity.

This is strictly weaker than RH: it is a local finite carrier accounting
statement.
-/
structure RelevantCarrierCapacityProjection where
  RelevantOverflow : Prop
  UnpairedCarrier  : Type
  overflow_forces_unpaired : RelevantOverflow -> Nonempty UnpairedCarrier

/--
The rank-projection package: overflow produces an unpaired carrier, and every
unpaired carrier is visible in the rank coordinate.
-/
structure RankProjectionCertificate where
  RelevantOverflow : Prop
  UnpairedCarrier  : Type
  overflow_forces_unpaired : RelevantOverflow -> Nonempty UnpairedCarrier
  unpaired_visible_rank : UnpairedCarrier -> RankJumpWitness

/--
Build the rank-projection certificate from the two local pieces:
capacity projection and rank visibility.
-/
def RankProjectionCertificate.of_capacity_and_visibility
    (C : RelevantCarrierCapacityProjection)
    (V : UnpairedCarrierVisibleRank)
    (hSame : C.UnpairedCarrier = V.UnpairedCarrier) :
    RankProjectionCertificate :=
  { RelevantOverflow := C.RelevantOverflow
    UnpairedCarrier := C.UnpairedCarrier
    overflow_forces_unpaired := C.overflow_forces_unpaired
    unpaired_visible_rank := fun u => V.toRankJump (hSame ▸ u) }

/--
The desired strict projection theorem:

    relevant overflow -> rank jump.

No RH-equivalent bridge is used here.  The proof is only:
  overflow gives an unpaired carrier;
  the unpaired carrier is visible in rank.
-/
theorem rankProjectionSoundness
    (P : RankProjectionCertificate) :
    P.RelevantOverflow -> Nonempty RankJumpWitness := by
  intro hOverflow
  rcases P.overflow_forces_unpaired hOverflow with ⟨u⟩
  exact ⟨P.unpaired_visible_rank u⟩

/-!
## 2. Contradiction form used by the cascade

Many downstream files use the negative version: if rank jumps are impossible,
then relevant overflow is impossible.
-/

theorem noRelevantOverflow_of_noRankJump
    (P : RankProjectionCertificate)
    (hNoJump : Nonempty RankJumpWitness -> False) :
    P.RelevantOverflow -> False := by
  intro hOverflow
  exact hNoJump (rankProjectionSoundness P hOverflow)

theorem noRelevantOverflow_iff_rankProjectionBlocked
    (P : RankProjectionCertificate) :
    ((Nonempty RankJumpWitness -> False) -> P.RelevantOverflow -> False) := by
  intro hNoJump
  exact noRelevantOverflow_of_noRankJump P hNoJump

/-!
## 3. Interface matching the live RH route

This is the name-level bridge to the repo wording.  The concrete file
`DissipativeCascade.lean` can instantiate these fields using its own
`RelevantOverflow`, `TwinCarrierPairing`, and `RankJumpWitness` definitions.
-/

structure TwinCarrierRankProjectionInterface where
  RelevantOverflow : Prop
  RankJump : Prop
  projection : RelevantOverflow -> RankJump

/--
Turn the strict certificate into the route-facing interface.
-/
def TwinCarrierRankProjectionInterface.of_certificate
    (P : RankProjectionCertificate) :
    TwinCarrierRankProjectionInterface where
  RelevantOverflow := P.RelevantOverflow
  RankJump := Nonempty RankJumpWitness
  projection := rankProjectionSoundness P

/--
Route-facing theorem: this is the abstract replacement for
`TwinCarrierPairing.unpaired_gives_jump`.
-/
theorem unpaired_gives_jump_of_rankProjectionCertificate
    (P : RankProjectionCertificate) :
    P.RelevantOverflow -> Nonempty RankJumpWitness := by
  exact rankProjectionSoundness P

/-!
## 4. Audit: where circularity would have to enter

The projection can only be circular if one of the two local fields is secretly
defined using RH or using the final absence of Liouville violations.
This audit predicate makes that explicit instead of hiding it in a bridge.
-/

structure RankProjectionNoRHLeakAudit where
  certificate : RankProjectionCertificate
  capacity_is_local : Prop
  visibility_is_local : Prop
  no_RH_in_capacity : capacity_is_local
  no_RH_in_visibility : visibility_is_local

/--
If the no-leak audit is supplied, the projection theorem remains purely local.
The proof still uses only the certificate; the audit is carried to document
that no RH-strength assumption was smuggled in.
-/
theorem audited_unpaired_gives_jump
    (A : RankProjectionNoRHLeakAudit) :
    A.certificate.RelevantOverflow -> Nonempty RankJumpWitness := by
  exact rankProjectionSoundness A.certificate

/-!
## 5. Final slogan as a machine-checkable proposition
-/

def RankProjectionClosed : Prop :=
  ∃ P : RankProjectionCertificate,
    P.RelevantOverflow -> Nonempty RankJumpWitness

/--
The strict projection closes as soon as a concrete certificate is instantiated.
-/
theorem rankProjectionClosed_of_certificate
    (P : RankProjectionCertificate) :
    RankProjectionClosed := by
  exact ⟨P, rankProjectionSoundness P⟩

end RiemannRankProjection

namespace RiemannGradualRankOverflow

/-!
## 1. Rank jump target

This duplicates the tiny target shape from the previous projection patch, so
this file can be dropped into a repo independently.  The concrete repo can later
identify this witness with its own `RankJumpWitness`.
-/

structure RankJumpWitness where
  beforeRank : Int
  afterRank  : Int
  jump       : beforeRank < afterRank

/-!
## 2. Gradual prefix ledger

`mass n` is the relevant carrier mass accumulated up to prefix `n`.
`capacity n` is the available finite capacity up to prefix `n`.
The only quantity used by the first-crossing argument is the defect

    defect n = mass n - capacity n.
-/

structure GradualCarrierLedger where
  mass     : Nat -> Int
  capacity : Nat -> Int

namespace GradualCarrierLedger

def defect (L : GradualCarrierLedger) (n : Nat) : Int :=
  L.mass n - L.capacity n

end GradualCarrierLedger

open GradualCarrierLedger

/--
A finite window in which the relevant carrier system starts below or at capacity
and ends above capacity.
-/
structure GradualOverflowWindow (L : GradualCarrierLedger) (N : Nat) where
  initial_safe   : L.defect 0 <= 0
  final_overflow : 0 < L.defect N

/--
The first prefix at which the defect becomes positive.

`before_safe` is intentionally global over all earlier prefixes, not merely
about `k - 1`.  This is the exact minimality certificate needed by the
pairing/capacity side.
-/
structure FirstOverflowCrossing (L : GradualCarrierLedger) (N k : Nat) where
  hk_le       : k <= N
  crosses     : 0 < L.defect k
  before_safe : forall j : Nat, j < k -> L.defect j <= 0

/--
The local one-step form extracted from a first crossing.  This is the point
where a concrete repo normally proves “a new unpaired carrier is born”.
-/
structure StepOverflowCrossing (L : GradualCarrierLedger) (k : Nat) where
  k_pos     : 0 < k
  prev_safe : L.defect (k - 1) <= 0
  now_pos   : 0 < L.defect k

/-!
## 3. The first-crossing lemma

This is pure discrete order/minimality.  It does not use any analytic input.
-/

/--
If the defect is positive somewhere by time `N`, then there is a first positive
prefix `k <= N`.
-/
theorem exists_firstOverflowCrossing
    (L : GradualCarrierLedger) (N : Nat)
    (hN : 0 < L.defect N) :
    ∃ k : Nat, k <= N /\ FirstOverflowCrossing L N k := by
  let P : Nat -> Prop := fun k => k <= N /\ 0 < L.defect k
  have hExists : ∃ k : Nat, P k := by
    exact ⟨N, le_rfl, hN⟩
  let k : Nat := Nat.find hExists
  have hkSpec : P k := Nat.find_spec hExists
  refine ⟨k, hkSpec.1, ?_⟩
  refine
    { hk_le := hkSpec.1
      crosses := hkSpec.2
      before_safe := ?_ }
  intro j hj
  by_contra hNotSafe
  have hpos : 0 < L.defect j := by
    exact not_le.mp hNotSafe
  have hj_le_N : j <= N := by
    exact Nat.le_trans (Nat.le_of_lt hj) hkSpec.1
  have hPj : P j := ⟨hj_le_N, hpos⟩
  exact (Nat.find_min hExists hj) hPj

/--
If the window starts safe and ends overflowed, then the first positive prefix is
not the zeroth prefix.
-/
theorem firstOverflowCrossing_pos_of_initialSafe
    {L : GradualCarrierLedger} {N k : Nat}
    (W : GradualOverflowWindow L N)
    (C : FirstOverflowCrossing L N k) :
    0 < k := by
  by_contra hNotPos
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hNotPos
  have hpos0 : 0 < L.defect 0 := by
    simpa [hk0] using C.crosses
  exact (not_lt_of_ge W.initial_safe) hpos0

/--
Safe start plus positive end gives a positive first crossing.
-/
theorem exists_positive_firstOverflowCrossing
    {L : GradualCarrierLedger} {N : Nat}
    (W : GradualOverflowWindow L N) :
    ∃ k : Nat, k <= N /\ 0 < k /\ FirstOverflowCrossing L N k := by
  rcases exists_firstOverflowCrossing L N W.final_overflow with ⟨k, hk_le, C⟩
  exact ⟨k, hk_le, firstOverflowCrossing_pos_of_initialSafe W C, C⟩

/--
A positive first crossing yields the one-step crossing form: the previous prefix
is safe and the current prefix is positive.
-/
theorem firstOverflowCrossing_to_stepOverflowCrossing
    {L : GradualCarrierLedger} {N k : Nat}
    (C : FirstOverflowCrossing L N k)
    (hk_pos : 0 < k) :
    StepOverflowCrossing L k := by
  have hpred_lt : k - 1 < k := by omega
  exact
    { k_pos := hk_pos
      prev_safe := C.before_safe (k - 1) hpred_lt
      now_pos := C.crosses }

/--
A gradual overflow window yields a local one-step threshold crossing.
-/
theorem exists_stepOverflowCrossing
    {L : GradualCarrierLedger} {N : Nat}
    (W : GradualOverflowWindow L N) :
    ∃ k : Nat, k <= N /\ StepOverflowCrossing L k := by
  rcases exists_positive_firstOverflowCrossing W with ⟨k, hk_le, hk_pos, C⟩
  exact ⟨k, hk_le, firstOverflowCrossing_to_stepOverflowCrossing C hk_pos⟩

/-!
## 4. The next structural certificate

After the pure first-crossing lemma, the genuine repo-specific input is local:

    first threshold crossing -> unpaired carrier born at that prefix.

This is much smaller and more inspectable than the original global bridge
`relevant overflow -> rank jump`.
-/

structure GradualRankProjectionCertificate (L : GradualCarrierLedger) where
  UnpairedCarrierAt : Nat -> Type

  /-- Local capacity/pairing statement: at the first positive threshold crossing,
  an unpaired relevant carrier ∃ at that prefix. -/
  first_crossing_creates_unpaired :
    forall {N k : Nat},
      FirstOverflowCrossing L N k -> Nonempty (UnpairedCarrierAt k)

  /-- Rank visibility statement: an unpaired carrier at prefix `k` is not
  gauge-only; it exposes a strict rank jump. -/
  unpaired_visible_rank :
    forall {k : Nat}, UnpairedCarrierAt k -> RankJumpWitness

/--
The gradual form of the rank-projection theorem.

This proves:

    safe start + eventual relevant overflow
      -> first threshold crossing
      -> unpaired carrier
      -> rank jump.
-/
theorem gradualOverflow_forces_rankJump
    {L : GradualCarrierLedger} {N : Nat}
    (P : GradualRankProjectionCertificate L)
    (W : GradualOverflowWindow L N) :
    Nonempty RankJumpWitness := by
  rcases exists_firstOverflowCrossing L N W.final_overflow with ⟨k, _hk_le, C⟩
  rcases P.first_crossing_creates_unpaired C with ⟨u⟩
  exact ⟨P.unpaired_visible_rank u⟩

/--
Negative cascade-facing form: if rank jumps are impossible, then no gradual
relevant overflow window can exist.
-/
theorem noGradualOverflowWindow_of_noRankJump
    {L : GradualCarrierLedger} {N : Nat}
    (P : GradualRankProjectionCertificate L)
    (hNoJump : Nonempty RankJumpWitness -> False) :
    GradualOverflowWindow L N -> False := by
  intro W
  exact hNoJump (gradualOverflow_forces_rankJump P W)

/-!
## 5. Decomposition of the old global bridge

This is the new smaller front for route #8:

  A. global relevant overflow gives a gradual window;
  B. first crossing creates an unpaired carrier;
  C. unpaired carrier is visible in rank.

A is usually a bookkeeping lemma; B and C are the structural projection content.
-/

structure GlobalRelevantOverflowToWindow where
  RelevantOverflow : Prop
  L : GradualCarrierLedger
  N : Nat
  window_of_overflow : RelevantOverflow -> GradualOverflowWindow L N

structure GradualProjectionRouteCertificate where
  G : GlobalRelevantOverflowToWindow
  P : GradualRankProjectionCertificate G.L

/--
Route-facing theorem: the original global relevant overflow implies a rank jump
once it is decomposed through a gradual overflow window.
-/
theorem relevantOverflow_forces_rankJump_of_gradualRoute
    (R : GradualProjectionRouteCertificate) :
    R.G.RelevantOverflow -> Nonempty RankJumpWitness := by
  intro hOverflow
  exact gradualOverflow_forces_rankJump R.P (R.G.window_of_overflow hOverflow)

/--
Cascade-facing negative form.
-/
theorem noRelevantOverflow_of_gradualRoute_noRankJump
    (R : GradualProjectionRouteCertificate)
    (hNoJump : Nonempty RankJumpWitness -> False) :
    R.G.RelevantOverflow -> False := by
  intro hOverflow
  exact hNoJump (relevantOverflow_forces_rankJump_of_gradualRoute R hOverflow)

/-!
## 6. No-RH-leak audit

The proof above is discrete and local.  Any RH-strength circularity would have
to enter through one of the explicit fields below, not through the first-crossing
lemma.
-/

structure GradualRankProjectionNoRHLeakAudit where
  route : GradualProjectionRouteCertificate
  window_bookkeeping_is_local : Prop
  first_crossing_unpaired_is_local : Prop
  rank_visibility_is_local : Prop
  no_RH_in_window_bookkeeping : window_bookkeeping_is_local
  no_RH_in_first_crossing_unpaired : first_crossing_unpaired_is_local
  no_RH_in_rank_visibility : rank_visibility_is_local

/--
Audited route theorem.  The audit fields are carried only to mark where a hidden
RH-strength assumption would have to be found.
-/
theorem audited_relevantOverflow_forces_rankJump
    (A : GradualRankProjectionNoRHLeakAudit) :
    A.route.G.RelevantOverflow -> Nonempty RankJumpWitness := by
  exact relevantOverflow_forces_rankJump_of_gradualRoute A.route

/-!
## 7. Machine-checkable status summary
-/

def GradualRankProjectionClosed : Prop :=
  ∃ R : GradualProjectionRouteCertificate,
    R.G.RelevantOverflow -> Nonempty RankJumpWitness

/--
The gradual projection is closed once the route certificate is instantiated.
-/
theorem gradualRankProjectionClosed_of_route
    (R : GradualProjectionRouteCertificate) :
    GradualRankProjectionClosed := by
  exact ⟨R, relevantOverflow_forces_rankJump_of_gradualRoute R⟩

/--
After this patch, the old global route #8 is reduced to three explicit fields:
window extraction, first-crossing unpaired creation, and rank visibility.
-/
def NextBrickStatus : Prop :=
  ∃ R : GradualProjectionRouteCertificate,
    (R.G.RelevantOverflow -> Nonempty RankJumpWitness)

/--
The status proposition is exactly witnessed by the gradual route theorem.
-/
theorem nextBrickStatus_of_route
    (R : GradualProjectionRouteCertificate) :
    NextBrickStatus := by
  exact ⟨R, relevantOverflow_forces_rankJump_of_gradualRoute R⟩

end RiemannGradualRankOverflow

/-! Соединительный слой + машинная честность -/

namespace EuclidsPath.RiemannRankProjectionBridge

open EuclidsPath.DissipativeCascade
open EuclidsPath.RankJumpBridge (RankParitySystem)

/-- **СТЫКОВКА (строгая форма):** интерфейс проекции с endpoint-картами
    поставляет НАСТОЯЩИЙ `TwinCarrierPairing` репо — вход №8
    `unpaired_gives_jump` выводится, а не постулируется. Остаток: сам
    сертификат (capacity + видимость) и две endpoint-карты. -/
def twinCarrierPairing_of_projectionInterface
    (P : LiouvilleTwinPartition) (TwinSystem : RankParitySystem)
    (encode : ∀ {X : ℕ}, {n : ℕ // n ∈ P.relevant X} → TwinSystem.State)
    (paired : TwinSystem.State → TwinSystem.State → Prop)
    (paired_flips_sign : ∀ a b, paired a b → TwinSystem.sign a = - TwinSystem.sign b)
    (I : RiemannRankProjection.TwinCarrierRankProjectionInterface)
    (hO : RelevantLiouvilleViolation P → I.RelevantOverflow)
    (hJ : I.RankJump → TwinCarrierEnergyJump TwinSystem) :
    TwinCarrierPairing P TwinSystem where
  encode := encode
  paired := paired
  paired_flips_sign := paired_flips_sign
  unpaired_gives_jump := fun hRel => hJ (I.projection (hO hRel))

/-- **СТЫКОВКА (градуальная форма):** градуальный route-сертификат с
    endpoint-картами тоже поставляет `TwinCarrierPairing`. Остаток входа №8
    распался на: (A) window-бухгалтерию, (B) first-crossing ⟹ unpaired,
    (C) rank-видимость, (D) две endpoint-карты. -/
def twinCarrierPairing_of_gradualRoute
    (P : LiouvilleTwinPartition) (TwinSystem : RankParitySystem)
    (encode : ∀ {X : ℕ}, {n : ℕ // n ∈ P.relevant X} → TwinSystem.State)
    (paired : TwinSystem.State → TwinSystem.State → Prop)
    (paired_flips_sign : ∀ a b, paired a b → TwinSystem.sign a = - TwinSystem.sign b)
    (R : RiemannGradualRankOverflow.GradualProjectionRouteCertificate)
    (hO : RelevantLiouvilleViolation P → R.G.RelevantOverflow)
    (hJ : Nonempty RiemannGradualRankOverflow.RankJumpWitness →
      TwinCarrierEnergyJump TwinSystem) :
    TwinCarrierPairing P TwinSystem where
  encode := encode
  paired := paired
  paired_flips_sign := paired_flips_sign
  unpaired_gives_jump := fun hRel =>
    hJ (RiemannGradualRankOverflow.relevantOverflow_forces_rankJump_of_gradualRoute
      R (hO hRel))

/-- ЧЕСТНОСТЬ: no-RH-leak «аудит» выполним ТРИВИАЛЬНО для любого сертификата
    (поля-пропозиции свободны) — это документирующий маркер, где искать
    протечку, а НЕ машинная проверка её отсутствия. -/
theorem rankProjectionAudit_is_free
    (P : RiemannRankProjection.RankProjectionCertificate) :
    Nonempty RiemannRankProjection.RankProjectionNoRHLeakAudit :=
  ⟨⟨P, True, True, trivial, trivial⟩⟩

/-- Тот же честный факт для градуального аудита. -/
theorem gradualAudit_is_free
    (R : RiemannGradualRankOverflow.GradualProjectionRouteCertificate) :
    Nonempty RiemannGradualRankOverflow.GradualRankProjectionNoRHLeakAudit :=
  ⟨⟨R, True, True, True, trivial, trivial, trivial⟩⟩

end EuclidsPath.RiemannRankProjectionBridge
