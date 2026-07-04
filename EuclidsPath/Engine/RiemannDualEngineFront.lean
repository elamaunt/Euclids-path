/-
  RiemannDualEngineFront — the dual Riemann route (3 bricks in one assembly):

  1. PaymentSynchronization — synchronization of payments of the phantom (spectral) and
     genuine (rank-flow) engines over a shared ledger: one-sided
     payment builds a forbidden perpetual engine, so under `NoPerpetual`
     payments are equivalent; zero-indexed packages and closure packages up to Target.
  2. MeetingRankChange — local law "engines meet ⟺ shared seam
     changes rank"; firewalls against silent rank change without meeting and meeting
     without rank change; payment synchronization with rank seams.
  3. TwinMeetingZeroBridge — counting bridge twins ↔ meetings ↔ nontrivial
     zeros: infinitude transfer ONLY via data-injective bridges
     (encode/decode, left inverse) — anti-vacuity against a free
     origin event is built into the definition.

  HONESTY (assembly-audit flags, machine-checked):
    * All substantive conclusions of the series are CONDITIONAL on uninstantiated packages:
      `SharedPaymentLedger` carries `NoPerpetual`/`BuildsPerpetual*` as FIELDS
      (interface slots, not our theorems `no_someConcreteEuclideanEngine`);
      closure packages carry `noSynchronizedPaymentAtZero` and `*PaysAtZero`
      as INPUTS; `MeetingRankChangeLaw` carries BOTH directions of the law as fields.
      There are no unconditional strong conclusions.
    * Bridge #3 counts NONTRIVIAL zeros (`NontrivialZero` — an abstract type),
      NOT off-critical: filling the bridge would NOT carry RH information — their
      infinitude is classically known and compatible with RH in both directions.
      The obligation `FinalTwinMeetingZeroCountingObligation` is not instantiated.
    * Defect-class fixes for the bricks: `!=` on an arbitrary type without BEq →
      `≠` (SharedRankChangesAcross, SameSeamRankChange); DATA projections from
      Prop-structures (PhantomOnlyPayment etc.) → rintro decomposition; `Target`
      moved from `Type u` to `Prop` (otherwise RiemannHypothesis cannot be substituted and
      Prop→Type elimination arose in `rcases Nonempty`); the file-level
      doc-comment before import replaced by an ordinary block comment.
      The brick proofs themselves are preserved.
  No sorry/axiom.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/-! # Brick 1: payment synchronization of the dual engines -/

namespace RiemannDualEngine
namespace PaymentSynchronization

universe u

/-- A side of the dual-engine comparison. -/
inductive EngineSide where
  | phantom
  | genuine
deriving DecidableEq, Repr

/-- A mismatch of payments at a shared charge. -/
inductive PaymentMismatch where
  | phantomPaid_genuineUnpaid
  | genuinePaid_phantomUnpaid
  deriving DecidableEq, Repr

/--
A shared-payment interface for two engines.

`Charge` is the common invoice/observable amount.  The two engines may have
very different internal dynamics, but if they are `Aligned` then a payment at
one side is meant to be payment of the same external charge.

`Perpetual` is the forbidden discrepancy engine produced by one-sided payment.

HONESTY: `BuildsPerpetual*` and `NoPerpetual` are interface SLOTS (fields),
not theorems of the repository; the entire series is conditional on their instantiation.
-/
structure SharedPaymentLedger
    (Phantom Genuine Charge Perpetual : Type u) : Type (u+1) where
  Aligned : Phantom → Genuine → Prop
  PhantomPays : Phantom → Charge → Prop
  GenuinePays : Genuine → Charge → Prop
  BuildsPerpetualFromPhantomOnly :
    ∀ {p : Phantom} {g : Genuine} {c : Charge},
      Aligned p g →
      PhantomPays p c →
      (GenuinePays g c → False) →
      Perpetual
  BuildsPerpetualFromGenuineOnly :
    ∀ {p : Phantom} {g : Genuine} {c : Charge},
      Aligned p g →
      GenuinePays g c →
      (PhantomPays p c → False) →
      Perpetual
  NoPerpetual : Perpetual → False

namespace SharedPaymentLedger

variable {Phantom Genuine Charge Perpetual : Type u}
variable (L : SharedPaymentLedger Phantom Genuine Charge Perpetual)

/-- One-sided phantom payment is impossible under the no-perpetual theorem. -/
theorem phantom_payment_forces_genuine
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g)
    (hPay : L.PhantomPays p c) :
    L.GenuinePays g c := by
  by_contra hNot
  exact L.NoPerpetual (L.BuildsPerpetualFromPhantomOnly hAlign hPay hNot)

/-- One-sided genuine payment is impossible under the no-perpetual theorem. -/
theorem genuine_payment_forces_phantom
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g)
    (hPay : L.GenuinePays g c) :
    L.PhantomPays p c := by
  by_contra hNot
  exact L.NoPerpetual (L.BuildsPerpetualFromGenuineOnly hAlign hPay hNot)

/-- On aligned dual engines, the two payment predicates are equivalent. -/
theorem payment_iff
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g) :
    L.PhantomPays p c ↔ L.GenuinePays g c := by
  constructor
  · intro hp
    exact L.phantom_payment_forces_genuine hAlign hp
  · intro hg
    exact L.genuine_payment_forces_phantom hAlign hg

/-- A phantom-only payment is directly contradictory. -/
theorem no_phantom_only_payment
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g)
    (hP : L.PhantomPays p c)
    (hNotG : L.GenuinePays g c → False) :
    False := by
  exact L.NoPerpetual (L.BuildsPerpetualFromPhantomOnly hAlign hP hNotG)

/-- A genuine-only payment is directly contradictory. -/
theorem no_genuine_only_payment
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g)
    (hG : L.GenuinePays g c)
    (hNotP : L.PhantomPays p c → False) :
    False := by
  exact L.NoPerpetual (L.BuildsPerpetualFromGenuineOnly hAlign hG hNotP)

end SharedPaymentLedger

/--
A concrete dual payment state at a single shared charge.
(Fix: a Prop-structure with data fields is not allowed in Lean 4 — ∃-form.)
-/
def DualPaymentState
    (Phantom Genuine Charge : Type u)
    (Aligned : Phantom → Genuine → Prop)
    (PhantomPays : Phantom → Charge → Prop)
    (GenuinePays : Genuine → Charge → Prop) : Prop :=
  ∃ (p : Phantom) (g : Genuine) (c : Charge),
    Aligned p g ∧ PhantomPays p c ∧ GenuinePays g c

/--
The bad state: the phantom side pays a shared charge but the genuine side does not.
(∃-form, see above.)
-/
def PhantomOnlyPayment
    (Phantom Genuine Charge : Type u)
    (Aligned : Phantom → Genuine → Prop)
    (PhantomPays : Phantom → Charge → Prop)
    (GenuinePays : Genuine → Charge → Prop) : Prop :=
  ∃ (p : Phantom) (g : Genuine) (c : Charge),
    Aligned p g ∧ PhantomPays p c ∧ (GenuinePays g c → False)

/--
The symmetric bad state: genuine pays but phantom does not.
(∃-form, see above.)
-/
def GenuineOnlyPayment
    (Phantom Genuine Charge : Type u)
    (Aligned : Phantom → Genuine → Prop)
    (PhantomPays : Phantom → Charge → Prop)
    (GenuinePays : Genuine → Charge → Prop) : Prop :=
  ∃ (p : Phantom) (g : Genuine) (c : Charge),
    Aligned p g ∧ GenuinePays g c ∧ (PhantomPays p c → False)

namespace DualPaymentState

variable {Phantom Genuine Charge Perpetual : Type u}
variable (L : SharedPaymentLedger Phantom Genuine Charge Perpetual)

/-- A phantom-only state cannot exist.
    (Fix: rintro decomposition instead of data projections from a Prop-structure.) -/
theorem no_phantomOnly :
    PhantomOnlyPayment Phantom Genuine Charge L.Aligned L.PhantomPays L.GenuinePays → False := by
  rintro ⟨p, g, c, hAlign, hPaid, hUnpaid⟩
  exact L.no_phantom_only_payment hAlign hPaid hUnpaid

/-- A genuine-only state cannot exist.
    (Fix: rintro decomposition instead of data projections from a Prop-structure.) -/
theorem no_genuineOnly :
    GenuineOnlyPayment Phantom Genuine Charge L.Aligned L.PhantomPays L.GenuinePays → False := by
  rintro ⟨p, g, c, hAlign, hPaid, hUnpaid⟩
  exact L.no_genuine_only_payment hAlign hPaid hUnpaid

/-- Phantom payment can be completed to a synchronized dual-payment state. -/
theorem complete_from_phantom
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g)
    (hPay : L.PhantomPays p c) :
    DualPaymentState Phantom Genuine Charge L.Aligned L.PhantomPays L.GenuinePays := by
  refine ⟨p, g, c, hAlign, hPay, ?_⟩
  exact L.phantom_payment_forces_genuine hAlign hPay

/-- Genuine payment can be completed to a synchronized dual-payment state. -/
theorem complete_from_genuine
    {p : Phantom} {g : Genuine} {c : Charge}
    (hAlign : L.Aligned p g)
    (hPay : L.GenuinePays g c) :
    DualPaymentState Phantom Genuine Charge L.Aligned L.PhantomPays L.GenuinePays := by
  refine ⟨p, g, c, hAlign, ?_, hPay⟩
  exact L.genuine_payment_forces_phantom hAlign hPay

end DualPaymentState

/--
A zero-indexed dual-engine payment package.

For every zero, we obtain aligned phantom/genuine engines and a charge.  The
field `phantomPays` may be supplied by the spectral/imaginary side, or
`genuinePays` may be supplied by the rank-flow side.  Either one is enough,
because the shared ledger synchronizes payment.
-/
structure ZeroIndexedDualPayment
    (Zero Phantom Genuine Charge Perpetual : Type u) where
  ledger : SharedPaymentLedger Phantom Genuine Charge Perpetual
  phantomOf : Zero → Phantom
  genuineOf : Zero → Genuine
  chargeOf : Zero → Charge
  aligned : ∀ z : Zero, ledger.Aligned (phantomOf z) (genuineOf z)

namespace ZeroIndexedDualPayment

variable {Zero Phantom Genuine Charge Perpetual : Type u}
variable (D : ZeroIndexedDualPayment Zero Phantom Genuine Charge Perpetual)

/-- If the phantom engine pays the zero-indexed charge, the genuine engine pays it too. -/
theorem phantomPays_forces_genuinePays
    (z : Zero)
    (hP : D.ledger.PhantomPays (D.phantomOf z) (D.chargeOf z)) :
    D.ledger.GenuinePays (D.genuineOf z) (D.chargeOf z) := by
  exact D.ledger.phantom_payment_forces_genuine (D.aligned z) hP

/-- If the genuine engine pays the zero-indexed charge, the phantom engine pays it too. -/
theorem genuinePays_forces_phantomPays
    (z : Zero)
    (hG : D.ledger.GenuinePays (D.genuineOf z) (D.chargeOf z)) :
    D.ledger.PhantomPays (D.phantomOf z) (D.chargeOf z) := by
  exact D.ledger.genuine_payment_forces_phantom (D.aligned z) hG

/-- Zero-indexed payment equivalence. -/
theorem payment_iff_at_zero (z : Zero) :
    D.ledger.PhantomPays (D.phantomOf z) (D.chargeOf z) ↔
    D.ledger.GenuinePays (D.genuineOf z) (D.chargeOf z) := by
  exact D.ledger.payment_iff (D.aligned z)

/-- A synchronized payment state can be produced from a phantom-side payment. -/
theorem complete_from_phantom_at_zero
    (z : Zero)
    (hP : D.ledger.PhantomPays (D.phantomOf z) (D.chargeOf z)) :
    DualPaymentState Phantom Genuine Charge
      D.ledger.Aligned D.ledger.PhantomPays D.ledger.GenuinePays := by
  exact DualPaymentState.complete_from_phantom D.ledger (D.aligned z) hP

/-- A synchronized payment state can be produced from a genuine-side payment. -/
theorem complete_from_genuine_at_zero
    (z : Zero)
    (hG : D.ledger.GenuinePays (D.genuineOf z) (D.chargeOf z)) :
    DualPaymentState Phantom Genuine Charge
      D.ledger.Aligned D.ledger.PhantomPays D.ledger.GenuinePays := by
  exact DualPaymentState.complete_from_genuine D.ledger (D.aligned z) hG

end ZeroIndexedDualPayment

/--
A closure package for the dual-engine route.

The route is:
  * every zero gives a synchronized dual-payment interface;
  * one side pays the shared charge;
  * synchronized payment is impossible at a genuine off-critical zero;
  * therefore there are no zeros;
  * therefore the target follows.

HONESTY: `phantomPaysAtZero` and `noSynchronizedPaymentAtZero` are INPUTS
(package fields), not theorems; `Target : Prop` (fix: was `Type u`).
-/
structure DualPaymentClosurePackage
    (Zero Phantom Genuine Charge Perpetual : Type u) (Target : Prop) where
  D : ZeroIndexedDualPayment Zero Phantom Genuine Charge Perpetual
  phantomPaysAtZero : ∀ z : Zero,
    D.ledger.PhantomPays (D.phantomOf z) (D.chargeOf z)
  noSynchronizedPaymentAtZero : ∀ _z : Zero,
    DualPaymentState Phantom Genuine Charge
      D.ledger.Aligned D.ledger.PhantomPays D.ledger.GenuinePays → False
  noZerosToTarget : (Zero → False) → Target

namespace DualPaymentClosurePackage

variable {Zero Phantom Genuine Charge Perpetual : Type u} {Target : Prop}

/-- Every zero would create a synchronized payment state, impossible by hypothesis.
    (Fix: `P` is an explicit parameter; a variable in the body only is not picked up in Lean 4.) -/
theorem no_zero
    (P : DualPaymentClosurePackage Zero Phantom Genuine Charge Perpetual Target)
    (z : Zero) : False := by
  apply P.noSynchronizedPaymentAtZero z
  exact P.D.complete_from_phantom_at_zero z (P.phantomPaysAtZero z)

/-- No zeros. -/
theorem no_zeros
    (P : DualPaymentClosurePackage Zero Phantom Genuine Charge Perpetual Target) :
    Zero → False := by
  intro z
  exact P.no_zero z

/-- Target/RH wrapper. -/
theorem target
    (P : DualPaymentClosurePackage Zero Phantom Genuine Charge Perpetual Target) :
    Target := by
  exact P.noZerosToTarget P.no_zeros

end DualPaymentClosurePackage

/-- Symmetric closure package where the genuine side is the side known to pay. -/
structure DualPaymentClosurePackageFromGenuine
    (Zero Phantom Genuine Charge Perpetual : Type u) (Target : Prop) where
  D : ZeroIndexedDualPayment Zero Phantom Genuine Charge Perpetual
  genuinePaysAtZero : ∀ z : Zero,
    D.ledger.GenuinePays (D.genuineOf z) (D.chargeOf z)
  noSynchronizedPaymentAtZero : ∀ _z : Zero,
    DualPaymentState Phantom Genuine Charge
      D.ledger.Aligned D.ledger.PhantomPays D.ledger.GenuinePays → False
  noZerosToTarget : (Zero → False) → Target

namespace DualPaymentClosurePackageFromGenuine

variable {Zero Phantom Genuine Charge Perpetual : Type u} {Target : Prop}

/-- Every zero would create a synchronized payment state, impossible by hypothesis.
    (Fix: `P` is an explicit parameter.) -/
theorem no_zero
    (P : DualPaymentClosurePackageFromGenuine Zero Phantom Genuine Charge Perpetual Target)
    (z : Zero) : False := by
  apply P.noSynchronizedPaymentAtZero z
  exact P.D.complete_from_genuine_at_zero z (P.genuinePaysAtZero z)

/-- No zeros. -/
theorem no_zeros
    (P : DualPaymentClosurePackageFromGenuine Zero Phantom Genuine Charge Perpetual Target) :
    Zero → False := by
  intro z
  exact P.no_zero z

/-- Target/RH wrapper. -/
theorem target
    (P : DualPaymentClosurePackageFromGenuine Zero Phantom Genuine Charge Perpetual Target) :
    Target := by
  exact P.noZerosToTarget P.no_zeros

end DualPaymentClosurePackageFromGenuine

/-- Final obligation: the phantom side pays and synchronized payment is impossible. -/
def FinalDualPaymentClosureObligation
    (Zero Phantom Genuine Charge Perpetual : Type u) (Target : Prop) : Prop :=
  Nonempty (DualPaymentClosurePackage Zero Phantom Genuine Charge Perpetual Target)

/-- Symmetric final obligation: the genuine side pays. -/
def FinalDualPaymentClosureObligationFromGenuine
    (Zero Phantom Genuine Charge Perpetual : Type u) (Target : Prop) : Prop :=
  Nonempty (DualPaymentClosurePackageFromGenuine Zero Phantom Genuine Charge Perpetual Target)

/-- Closing theorem from the phantom-side payment route. -/
theorem target_of_finalDualPaymentClosureObligation
    {Zero Phantom Genuine Charge Perpetual : Type u} {Target : Prop}
    (h : FinalDualPaymentClosureObligation Zero Phantom Genuine Charge Perpetual Target) :
    Target := by
  rcases h with ⟨P⟩
  exact P.target

/-- Closing theorem from the genuine-side payment route. -/
theorem target_of_finalDualPaymentClosureObligationFromGenuine
    {Zero Phantom Genuine Charge Perpetual : Type u} {Target : Prop}
    (h : FinalDualPaymentClosureObligationFromGenuine Zero Phantom Genuine Charge Perpetual Target) :
    Target := by
  rcases h with ⟨P⟩
  exact P.target

/-- Audit slogan as a theorem-shaped constant-free statement. -/
theorem paymentSynchronization_slogan
    {Phantom Genuine Charge Perpetual : Type u}
    (L : SharedPaymentLedger Phantom Genuine Charge Perpetual) :
    ∀ {p : Phantom} {g : Genuine} {c : Charge},
      L.Aligned p g →
      (L.PhantomPays p c ↔ L.GenuinePays g c) := by
  intro p g c hAlign
  exact L.payment_iff hAlign

end PaymentSynchronization
end RiemannDualEngine

/-! # Brick 2: engine meetings ⟺ rank change at the seam -/

namespace RiemannDualEngineMeetingRankChange

/-- Side of a rank seam.  The two engines may approach the same charge from
opposite sides; the seam is where the rank changes. -/
inductive SeamSide where
  | before
  | after
  deriving DecidableEq, Repr

/-- Local observable coordinate shared by both engines.  `Charge` is the
common account/observable in which payment, meeting, and rank are compared. -/
structure DualEngineTrace (Time Charge : Type) where
  phantom : Time → Charge
  genuine : Time → Charge

/-- A rank interface: every shared charge has a rank. -/
structure RankInterface (Charge Rank : Type) where
  rankOf : Charge → Rank

/-- The two engines meet at time `t` exactly when they occupy the same shared
observable charge. -/
def EnginesMeetAt {Time Charge : Type}
    (T : DualEngineTrace Time Charge) (t : Time) : Prop :=
  T.phantom t = T.genuine t

/-- A shared charge changes rank across a local transition from `t` to `u`.
This is deliberately stated on the common observable; it is not tied to either
engine alone.  (Fix: `!=` without a BEq instance → `≠`.) -/
def SharedRankChangesAcross {Time Charge Rank : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (t u : Time) : Prop :=
  R.rankOf (T.phantom t) ≠ R.rankOf (T.phantom u) ∨
  R.rankOf (T.genuine t) ≠ R.rankOf (T.genuine u)

/-- A stricter same-seam rank change: both engines see the same rank transition
on the same shared account.  (Fix: `!=` → `≠`.) -/
structure SameSeamRankChange {Time Charge Rank : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (t u : Time) : Prop where
  phantom_changes : R.rankOf (T.phantom t) ≠ R.rankOf (T.phantom u)
  genuine_changes : R.rankOf (T.genuine t) ≠ R.rankOf (T.genuine u)
  same_before : R.rankOf (T.phantom t) = R.rankOf (T.genuine t)
  same_after : R.rankOf (T.phantom u) = R.rankOf (T.genuine u)

/-- The local seam event at a single time.  This is the abstract event in which
both engines are on the same charge and this charge is the interface at which
rank transport is charged. -/
structure RankSeamMeeting {Time Charge Rank : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (t u : Time) : Prop where
  meet_at_t : EnginesMeetAt T t
  seam_change : SameSeamRankChange T R t u

/-- The exact law needed for the dual-engine proof: meeting and rank-change are
not two independent events.  They are the same interface event.

HONESTY: BOTH directions of the law are fields (inputs), not theorems. -/
structure MeetingRankChangeLaw {Time Charge Rank : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank) where
  meet_forces_rank_change :
    ∀ t u, EnginesMeetAt T t → SameSeamRankChange T R t u
  rank_change_forces_meet :
    ∀ t u, SameSeamRankChange T R t u → EnginesMeetAt T t

namespace MeetingRankChangeLaw

variable {Time Charge Rank : Type}
variable {T : DualEngineTrace Time Charge}
variable {R : RankInterface Charge Rank}

/-- Forward direction: if the engines meet, the shared interface must be a
rank-change interface. -/
theorem rank_change_of_meet
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (hMeet : EnginesMeetAt T t) :
    SameSeamRankChange T R t u :=
  L.meet_forces_rank_change t u hMeet

/-- Backward direction: if the shared interface changes rank, the engines must
meet at the paying seam. -/
theorem meet_of_rank_change
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (hRank : SameSeamRankChange T R t u) :
    EnginesMeetAt T t :=
  L.rank_change_forces_meet t u hRank

/-- Main equivalence: engines meet exactly at rank-change events. -/
theorem meet_iff_rank_change
    (L : MeetingRankChangeLaw T R)
    (t u : Time) :
    EnginesMeetAt T t ↔ SameSeamRankChange T R t u :=
  Iff.intro
    (fun h => L.meet_forces_rank_change t u h)
    (fun h => L.rank_change_forces_meet t u h)

/-- A rank seam meeting is equivalent to a meeting, because the rank-change
component is forced by the law. -/
theorem rankSeamMeeting_of_meet
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (hMeet : EnginesMeetAt T t) :
    RankSeamMeeting T R t u :=
  { meet_at_t := hMeet
    seam_change := L.meet_forces_rank_change t u hMeet }

/-- Conversely, a rank seam meeting contains the ordinary meeting. -/
theorem meet_of_rankSeamMeeting
    {t u : Time}
    (h : RankSeamMeeting T R t u) :
    EnginesMeetAt T t :=
  h.meet_at_t

/-- No meeting iff no same-seam rank change.  This is useful as a firewall:
rank cannot silently change away from the dual-engine interface. -/
theorem not_meet_iff_not_rank_change
    (L : MeetingRankChangeLaw T R)
    (t u : Time) :
    (¬ EnginesMeetAt T t) ↔ ¬ SameSeamRankChange T R t u := by
  exact not_iff_not.mpr (L.meet_iff_rank_change t u)

/-- If a rank change occurs without a meeting, the meeting-rank law is violated. -/
theorem rank_change_without_meet_contradiction
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (hRank : SameSeamRankChange T R t u)
    (hNoMeet : ¬ EnginesMeetAt T t) :
    False :=
  hNoMeet (L.rank_change_forces_meet t u hRank)

/-- If a meeting occurs without rank change, the meeting-rank law is violated. -/
theorem meet_without_rank_change_contradiction
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (hMeet : EnginesMeetAt T t)
    (hNoRank : ¬ SameSeamRankChange T R t u) :
    False :=
  hNoRank (L.meet_forces_rank_change t u hMeet)

end MeetingRankChangeLaw

/-- A forbidden event: one engine claims a meeting/payment seam but the shared
rank does not change.  This is the dual-engine analogue of free payment. -/
structure PhantomMeetingWithoutRankChange {Time Charge Rank : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (t u : Time) : Prop where
  meet : EnginesMeetAt T t
  no_rank_change : ¬ SameSeamRankChange T R t u

/-- A forbidden event: rank changes without the two engines meeting.  This is a
silent rank jump. -/
structure SilentRankChangeWithoutMeeting {Time Charge Rank : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (t u : Time) : Prop where
  rank_change : SameSeamRankChange T R t u
  no_meet : ¬ EnginesMeetAt T t

namespace MeetingRankChangeLaw

variable {Time Charge Rank : Type}
variable {T : DualEngineTrace Time Charge}
variable {R : RankInterface Charge Rank}

/-- Under the law, meeting-without-rank-change is impossible. -/
theorem no_phantomMeetingWithoutRankChange
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (h : PhantomMeetingWithoutRankChange T R t u) :
    False :=
  L.meet_without_rank_change_contradiction h.meet h.no_rank_change

/-- Under the law, silent rank change without meeting is impossible. -/
theorem no_silentRankChangeWithoutMeeting
    (L : MeetingRankChangeLaw T R)
    {t u : Time}
    (h : SilentRankChangeWithoutMeeting T R t u) :
    False :=
  L.rank_change_without_meet_contradiction h.rank_change h.no_meet

end MeetingRankChangeLaw

/-- Bridge to the two-payment layer: a payment event occurs exactly at a meeting
rank seam.  This is the local statement needed to combine with the previous
payment-synchronization patch. -/
structure PaymentAtRankSeam {Time Charge Rank Payment : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (paymentAt : Time → Payment → Prop)
    (t u : Time)
    (p : Payment) : Prop where
  payment : paymentAt t p
  seam : RankSeamMeeting T R t u

/-- A synchronized payment/rank law: payments are neither earlier nor later than
rank-seam meetings.  HONESTY: both directions are fields (inputs). -/
structure PaymentRankSynchronization {Time Charge Rank Payment : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (paymentAt : Time → Payment → Prop) where
  payment_forces_meeting_rank_change :
    ∀ t u p, paymentAt t p → RankSeamMeeting T R t u
  meeting_rank_change_forces_payment :
    ∀ t u, RankSeamMeeting T R t u → ∃ p, paymentAt t p

namespace PaymentRankSynchronization

variable {Time Charge Rank Payment : Type}
variable {T : DualEngineTrace Time Charge}
variable {R : RankInterface Charge Rank}
variable {paymentAt : Time → Payment → Prop}

/-- If a payment exists, then the engines meet and rank changes. -/
theorem meeting_rank_change_of_payment
    (S : PaymentRankSynchronization T R paymentAt)
    {t u : Time} {p : Payment}
    (hp : paymentAt t p) :
    RankSeamMeeting T R t u :=
  S.payment_forces_meeting_rank_change t u p hp

/-- If the engines meet at a rank seam, then some synchronized payment exists. -/
theorem exists_payment_of_meeting_rank_change
    (S : PaymentRankSynchronization T R paymentAt)
    {t u : Time}
    (h : RankSeamMeeting T R t u) :
    ∃ p, paymentAt t p :=
  S.meeting_rank_change_forces_payment t u h

/-- Payment iff rank-seam meeting, existentially over the actual payment token. -/
theorem exists_payment_iff_rankSeamMeeting
    (S : PaymentRankSynchronization T R paymentAt)
    (t u : Time) :
    (∃ p, paymentAt t p) ↔ RankSeamMeeting T R t u :=
  Iff.intro
    (fun h => match h with
      | Exists.intro p hp => S.payment_forces_meeting_rank_change t u p hp)
    (fun h => S.meeting_rank_change_forces_payment t u h)

end PaymentRankSynchronization

/-- Final local package: meeting, rank-change, and payment are one synchronized
interface event. -/
structure DualEngineSeamSynchronization {Time Charge Rank Payment : Type}
    (T : DualEngineTrace Time Charge)
    (R : RankInterface Charge Rank)
    (paymentAt : Time → Payment → Prop) where
  meeting_rank_law : MeetingRankChangeLaw T R
  payment_rank_law : PaymentRankSynchronization T R paymentAt

namespace DualEngineSeamSynchronization

variable {Time Charge Rank Payment : Type}
variable {T : DualEngineTrace Time Charge}
variable {R : RankInterface Charge Rank}
variable {paymentAt : Time → Payment → Prop}

/-- Main tri-equivalence, packaged as two equivalences:
meeting ↔ rank-change and payment ↔ rank-seam meeting. -/
theorem meeting_iff_rank_change
    (D : DualEngineSeamSynchronization T R paymentAt)
    (t u : Time) :
    EnginesMeetAt T t ↔ SameSeamRankChange T R t u :=
  D.meeting_rank_law.meet_iff_rank_change t u

/-- Payment iff rank-seam meeting. -/
theorem payment_iff_rankSeamMeeting
    (D : DualEngineSeamSynchronization T R paymentAt)
    (t u : Time) :
    (∃ p, paymentAt t p) ↔ RankSeamMeeting T R t u :=
  D.payment_rank_law.exists_payment_iff_rankSeamMeeting t u

/-- Payment implies engine meeting. -/
theorem meet_of_payment
    (D : DualEngineSeamSynchronization T R paymentAt)
    {t u : Time} {p : Payment}
    (hp : paymentAt t p) :
    EnginesMeetAt T t :=
  (D.payment_rank_law.payment_forces_meeting_rank_change t u p hp).meet_at_t

/-- Payment implies same-seam rank change. -/
theorem rank_change_of_payment
    (D : DualEngineSeamSynchronization T R paymentAt)
    {t u : Time} {p : Payment}
    (hp : paymentAt t p) :
    SameSeamRankChange T R t u :=
  (D.payment_rank_law.payment_forces_meeting_rank_change t u p hp).seam_change

/-- Meeting implies a rank seam meeting, hence some synchronized payment. -/
theorem exists_payment_of_meet
    (D : DualEngineSeamSynchronization T R paymentAt)
    {t u : Time}
    (hMeet : EnginesMeetAt T t) :
    ∃ p, paymentAt t p :=
  D.payment_rank_law.meeting_rank_change_forces_payment t u
    (D.meeting_rank_law.rankSeamMeeting_of_meet hMeet)

/-- Rank change implies some synchronized payment. -/
theorem exists_payment_of_rank_change
    (D : DualEngineSeamSynchronization T R paymentAt)
    {t u : Time}
    (hRank : SameSeamRankChange T R t u) :
    ∃ p, paymentAt t p :=
  D.payment_rank_law.meeting_rank_change_forces_payment t u
    { meet_at_t := D.meeting_rank_law.meet_of_rank_change hRank
      seam_change := hRank }

end DualEngineSeamSynchronization

/-- Repo-facing obligation: instantiate this with the concrete phantom/genuine
Riemann engines.  Once this is filled, the previous payment-synchronization and
periodic-alignment kernels can share the same seam event.
(Fix: `Target : Prop`.) -/
structure FinalDualEngineMeetingRankObligation
    (Time Charge Rank Payment : Type) (Target : Prop) where
  T : DualEngineTrace Time Charge
  R : RankInterface Charge Rank
  paymentAt : Time → Payment → Prop
  sync : DualEngineSeamSynchronization T R paymentAt
  target_of_sync : DualEngineSeamSynchronization T R paymentAt → Target

/-- Final wrapper: the synchronized meet/rank/payment interface gives the target
once connected to the repo-specific target bridge. -/
theorem target_of_finalDualEngineMeetingRankObligation
    {Time Charge Rank Payment : Type} {Target : Prop}
    (O : FinalDualEngineMeetingRankObligation Time Charge Rank Payment Target) :
    Target :=
  O.target_of_sync O.sync

/-- Slogan as a constant (marker, not a proposition). -/
def dualEngineMeetingRankSlogan : String :=
  "phantom and genuine engines meet exactly at rank-change seams; payments live exactly there"

end RiemannDualEngineMeetingRankChange

/-! # Brick 3: counting bridge twins ↔ meetings ↔ nontrivial zeros -/

namespace RiemannTwinMeetingZeroBridge

universe u v w

/--
`ArbitrarilyMany α` means: for every finite length `n`, one can exhibit
`n` pairwise distinct elements of `α`.

This is a constructive, Fin-indexed form of infinitude that is convenient for
machine-checked injection transfer.
-/
def ArbitrarilyMany (α : Type u) : Prop :=
  ∀ n : ℕ, ∃ f : Fin n → α, Function.Injective f

/-- A data bridge `α → β` that remembers the original `α` by a decoder. -/
structure InjectiveBridge (α : Type u) (β : Type v) where
  encode : α → β
  decode : β → α
  decode_encode : Function.LeftInverse decode encode

namespace InjectiveBridge

/-- The encoded map is injective because it has a left inverse. -/
theorem encode_injective {α : Type u} {β : Type v}
    (B : InjectiveBridge α β) : Function.Injective B.encode := by
  intro a b h
  have h' : B.decode (B.encode a) = B.decode (B.encode b) := congrArg B.decode h
  simpa [B.decode_encode a, B.decode_encode b] using h'

/-- Infinitude transfers along an injective data bridge. -/
theorem arbitrarilyMany_of_source {α : Type u} {β : Type v}
    (B : InjectiveBridge α β)
    (hα : ArbitrarilyMany α) : ArbitrarilyMany β := by
  intro n
  rcases hα n with ⟨f, hf⟩
  refine ⟨fun i => B.encode (f i), ?_⟩
  intro i j hij
  exact hf (B.encode_injective hij)

/-- Composition of data bridges. -/
def comp {α : Type u} {β : Type v} {γ : Type w}
    (B₂ : InjectiveBridge β γ)
    (B₁ : InjectiveBridge α β) : InjectiveBridge α γ where
  encode := fun a => B₂.encode (B₁.encode a)
  decode := fun c => B₁.decode (B₂.decode c)
  decode_encode := by
    intro a
    show B₁.decode (B₂.decode (B₂.encode (B₁.encode a))) = a
    rw [B₂.decode_encode (B₁.encode a), B₁.decode_encode a]

end InjectiveBridge

/--
A bidirectional counting equivalence is two independent injective bridges.
It is weaker than an equivalence of types, but exactly enough to transfer
`ArbitrarilyMany` in both directions.
-/
structure CountingEquivalence (α : Type u) (β : Type v) where
  forward : InjectiveBridge α β
  backward : InjectiveBridge β α

namespace CountingEquivalence

/-- Transfer infinitude forward. -/
theorem forward_infinite {α : Type u} {β : Type v}
    (E : CountingEquivalence α β)
    (hα : ArbitrarilyMany α) : ArbitrarilyMany β :=
  E.forward.arbitrarilyMany_of_source hα

/-- Transfer infinitude backward. -/
theorem backward_infinite {α : Type u} {β : Type v}
    (E : CountingEquivalence α β)
    (hβ : ArbitrarilyMany β) : ArbitrarilyMany α :=
  E.backward.arbitrarilyMany_of_source hβ

/-- Infinitude is equivalent across a bidirectional counting bridge. -/
theorem infinite_iff {α : Type u} {β : Type v}
    (E : CountingEquivalence α β) :
    ArbitrarilyMany α ↔ ArbitrarilyMany β :=
  ⟨E.forward_infinite, E.backward_infinite⟩

end CountingEquivalence

/-!
## Engine meetings and rank changes

The previous dual-engine layer established the intended local equivalence:
engines meet exactly at rank-change seams.  Here we record the counting form:
an injective bridge in both directions between meeting events and rank-change events.
-/

/-- Counting-level form of "meetings iff rank changes". -/
abbrev MeetingRankCountingEquivalence
    (Meeting : Type u) (RankChange : Type v) : Prop :=
  Nonempty (CountingEquivalence Meeting RankChange)

/-- Infinite meetings give infinitely many rank changes. -/
theorem infinitelyMany_rankChanges_of_meetings
    {Meeting : Type u} {RankChange : Type v}
    (E : CountingEquivalence Meeting RankChange)
    (hMeet : ArbitrarilyMany Meeting) : ArbitrarilyMany RankChange :=
  E.forward_infinite hMeet

/-- Infinite rank changes give infinitely many meetings. -/
theorem infinitelyMany_meetings_of_rankChanges
    {Meeting : Type u} {RankChange : Type v}
    (E : CountingEquivalence Meeting RankChange)
    (hRank : ArbitrarilyMany RankChange) : ArbitrarilyMany Meeting :=
  E.backward_infinite hRank

/-- The exact counting theorem for meetings and rank changes. -/
theorem meetings_infinite_iff_rankChanges_infinite
    {Meeting : Type u} {RankChange : Type v}
    (E : CountingEquivalence Meeting RankChange) :
    ArbitrarilyMany Meeting ↔ ArbitrarilyMany RankChange :=
  E.infinite_iff

/-!
## Twins → meetings → nontrivial zeros
-/

/--
A forward bridge from twin-carriers to meetings, then from meetings to zeros.
Every arrow is required to be data-injective by a decoder.
-/
structure TwinToZeroViaMeetings
    (Twin : Type u) (Meeting : Type v) (NontrivialZero : Type w) where
  twin_to_meeting : InjectiveBridge Twin Meeting
  meeting_to_zero : InjectiveBridge Meeting NontrivialZero

namespace TwinToZeroViaMeetings

/-- Infinite twins force infinitely many meetings. -/
theorem infinite_meetings_of_infinite_twins
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : TwinToZeroViaMeetings Twin Meeting NontrivialZero)
    (hTwin : ArbitrarilyMany Twin) : ArbitrarilyMany Meeting :=
  P.twin_to_meeting.arbitrarilyMany_of_source hTwin

/-- Infinite meetings force infinitely many nontrivial zeros. -/
theorem infinite_zeros_of_infinite_meetings
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : TwinToZeroViaMeetings Twin Meeting NontrivialZero)
    (hMeet : ArbitrarilyMany Meeting) : ArbitrarilyMany NontrivialZero :=
  P.meeting_to_zero.arbitrarilyMany_of_source hMeet

/-- Infinite twins force infinitely many nontrivial zeros through meetings. -/
theorem infinite_zeros_of_infinite_twins
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : TwinToZeroViaMeetings Twin Meeting NontrivialZero)
    (hTwin : ArbitrarilyMany Twin) : ArbitrarilyMany NontrivialZero :=
  P.infinite_zeros_of_infinite_meetings
    (P.infinite_meetings_of_infinite_twins hTwin)

/-- The composed twin → zero bridge. -/
def twin_to_zero_bridge
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : TwinToZeroViaMeetings Twin Meeting NontrivialZero) :
    InjectiveBridge Twin NontrivialZero :=
  P.meeting_to_zero.comp P.twin_to_meeting

end TwinToZeroViaMeetings

/-!
## Nontrivial zeros → meetings → twins
-/

/--
The reverse bridge: nontrivial zeros generate meetings, and meetings generate
twin-carriers.  Again both arrows are data-injective.
-/
structure ZeroToTwinViaMeetings
    (Twin : Type u) (Meeting : Type v) (NontrivialZero : Type w) where
  zero_to_meeting : InjectiveBridge NontrivialZero Meeting
  meeting_to_twin : InjectiveBridge Meeting Twin

namespace ZeroToTwinViaMeetings

/-- Infinite nontrivial zeros force infinitely many meetings. -/
theorem infinite_meetings_of_infinite_zeros
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : ZeroToTwinViaMeetings Twin Meeting NontrivialZero)
    (hZero : ArbitrarilyMany NontrivialZero) : ArbitrarilyMany Meeting :=
  P.zero_to_meeting.arbitrarilyMany_of_source hZero

/-- Infinite meetings force infinitely many twin-carriers. -/
theorem infinite_twins_of_infinite_meetings
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : ZeroToTwinViaMeetings Twin Meeting NontrivialZero)
    (hMeet : ArbitrarilyMany Meeting) : ArbitrarilyMany Twin :=
  P.meeting_to_twin.arbitrarilyMany_of_source hMeet

/-- Infinite nontrivial zeros force infinitely many twin-carriers through meetings. -/
theorem infinite_twins_of_infinite_zeros
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : ZeroToTwinViaMeetings Twin Meeting NontrivialZero)
    (hZero : ArbitrarilyMany NontrivialZero) : ArbitrarilyMany Twin :=
  P.infinite_twins_of_infinite_meetings
    (P.infinite_meetings_of_infinite_zeros hZero)

/-- The composed zero → twin bridge. -/
def zero_to_twin_bridge
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (P : ZeroToTwinViaMeetings Twin Meeting NontrivialZero) :
    InjectiveBridge NontrivialZero Twin :=
  P.meeting_to_twin.comp P.zero_to_meeting

end ZeroToTwinViaMeetings

/-!
## Full bidirectional bridge
-/

/--
The full proposed bridge:
  infinite twins → infinite meetings → infinite nontrivial zeros,
and conversely
  infinite nontrivial zeros → infinite meetings → infinite twins.
-/
structure TwinZeroMeetingBridge
    (Twin : Type u) (Meeting : Type v) (NontrivialZero : Type w) where
  forward : TwinToZeroViaMeetings Twin Meeting NontrivialZero
  backward : ZeroToTwinViaMeetings Twin Meeting NontrivialZero

namespace TwinZeroMeetingBridge

/-- Forward direction: twins give meetings. -/
theorem meetings_of_twins
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero)
    (hTwin : ArbitrarilyMany Twin) : ArbitrarilyMany Meeting :=
  B.forward.infinite_meetings_of_infinite_twins hTwin

/-- Forward direction: twins give nontrivial zeros. -/
theorem zeros_of_twins
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero)
    (hTwin : ArbitrarilyMany Twin) : ArbitrarilyMany NontrivialZero :=
  B.forward.infinite_zeros_of_infinite_twins hTwin

/-- Reverse direction: nontrivial zeros give meetings. -/
theorem meetings_of_zeros
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero)
    (hZero : ArbitrarilyMany NontrivialZero) : ArbitrarilyMany Meeting :=
  B.backward.infinite_meetings_of_infinite_zeros hZero

/-- Reverse direction: nontrivial zeros give twins. -/
theorem twins_of_zeros
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero)
    (hZero : ArbitrarilyMany NontrivialZero) : ArbitrarilyMany Twin :=
  B.backward.infinite_twins_of_infinite_zeros hZero

/-- The final counting equivalence: twins are infinite iff nontrivial zeros are infinite. -/
theorem twins_infinite_iff_zeros_infinite
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero) :
    ArbitrarilyMany Twin ↔ ArbitrarilyMany NontrivialZero :=
  ⟨B.zeros_of_twins, B.twins_of_zeros⟩

/-- The final counting equivalence through meetings. -/
theorem twins_infinite_implies_meetings_and_zeros
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero)
    (hTwin : ArbitrarilyMany Twin) :
    ArbitrarilyMany Meeting ∧ ArbitrarilyMany NontrivialZero :=
  ⟨B.meetings_of_twins hTwin, B.zeros_of_twins hTwin⟩

/-- The reverse counting equivalence through meetings. -/
theorem zeros_infinite_implies_meetings_and_twins
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (B : TwinZeroMeetingBridge Twin Meeting NontrivialZero)
    (hZero : ArbitrarilyMany NontrivialZero) :
    ArbitrarilyMany Meeting ∧ ArbitrarilyMany Twin :=
  ⟨B.meetings_of_zeros hZero, B.twins_of_zeros hZero⟩

end TwinZeroMeetingBridge

/-!
## Anti-vacuity audit

The bridges above are intentionally data-level.  A free origin map that sends all
objects to the same meeting cannot satisfy the decoder/left-inverse condition if
there are two distinct source objects.
-/

/-- If a bridge encodes two source objects as the same target, those objects are equal. -/
theorem bridge_same_encoding_forces_same_source
    {α : Type u} {β : Type v}
    (B : InjectiveBridge α β)
    {a₁ a₂ : α}
    (h : B.encode a₁ = B.encode a₂) : a₁ = a₂ :=
  B.encode_injective h

/-- A constant origin event cannot encode two distinct source objects. -/
theorem no_constant_origin_bridge_on_distinct_sources
    {α : Type u} {β : Type v}
    (B : InjectiveBridge α β)
    (c : β)
    {a₁ a₂ : α}
    (h₁ : B.encode a₁ = c)
    (h₂ : B.encode a₂ = c)
    (hne : a₁ ≠ a₂) : False := by
  apply hne
  exact B.encode_injective (h₁.trans h₂.symm)

/--
Final named obligation for the proposed twin/meeting/zero counting equivalence.
This is the exact data that must be constructed in the concrete repositories.
-/
abbrev FinalTwinMeetingZeroCountingObligation
    (Twin : Type u) (Meeting : Type v) (NontrivialZero : Type w) : Prop :=
  Nonempty (TwinZeroMeetingBridge Twin Meeting NontrivialZero)

/-- If the final obligation is filled, twin infinitude and zero infinitude are equivalent. -/
theorem final_counting_obligation_closes_infinity_equivalence
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (h : FinalTwinMeetingZeroCountingObligation Twin Meeting NontrivialZero) :
    ArbitrarilyMany Twin ↔ ArbitrarilyMany NontrivialZero := by
  rcases h with ⟨B⟩
  exact B.twins_infinite_iff_zeros_infinite

/-- If the final obligation is filled, infinite twins produce infinite meetings and zeros. -/
theorem final_counting_obligation_twins_to_meetings_to_zeros
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (h : FinalTwinMeetingZeroCountingObligation Twin Meeting NontrivialZero)
    (hTwin : ArbitrarilyMany Twin) :
    ArbitrarilyMany Meeting ∧ ArbitrarilyMany NontrivialZero := by
  rcases h with ⟨B⟩
  exact B.twins_infinite_implies_meetings_and_zeros hTwin

/-- If the final obligation is filled, infinite zeros produce infinite meetings and twins. -/
theorem final_counting_obligation_zeros_to_meetings_to_twins
    {Twin : Type u} {Meeting : Type v} {NontrivialZero : Type w}
    (h : FinalTwinMeetingZeroCountingObligation Twin Meeting NontrivialZero)
    (hZero : ArbitrarilyMany NontrivialZero) :
    ArbitrarilyMany Meeting ∧ ArbitrarilyMany Twin := by
  rcases h with ⟨B⟩
  exact B.zeros_infinite_implies_meetings_and_twins hZero

end RiemannTwinMeetingZeroBridge

end EuclidsPath
