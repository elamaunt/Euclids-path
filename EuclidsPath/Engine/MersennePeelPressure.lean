/-
  MersennePeelPressure — два следующих слоя платёжного маршрута Мерсенна
  (кирпичи: mersenne_peel_payment_pressure + mersenne_peel_coverage_pressure).
  Проза: prose/24 (Мерсенн-ветка).

  Слой 1 (peel-payment): pressure расщеплён на
    CofinalMersennePeelCoverage (близнецы навязывают попадания генеалогий
    в base-4 repunit-центры) + PeelHitForcesPrimePayment (попадание платит
    обе стороны 6m_k ∓ 1); вместе + soundness ⟹ ∞ Мерсенн-близнецов.
  Слой 2 (peel-coverage/debt): coverage расщеплён дальше —
    CofinalPeelDebtPressure (неограниченные peel-debt индексы) +
    PeelDebtRealizesHit (debt-индекс реализуется как hit); полная
    дефект-трихотомия при tail-отсутствии.

  СТЫКОВКА (при интеграции): центры трёх слоёв совпадают (индукция по
  рекурренции); ЦЕПИ ДО ЦЕЛИ: twinLowersInfinite_of_peelPaymentRoute и
  twinLowersInfinite_of_debtRoute — оба route-пакета ⟹ TwinLowers.Infinite.

  ⚠️ МАШИННАЯ ЧЕСТНОСТЬ: canonical_coverage_iff — для канонической системы
  («hit = уже twin» над everything-prime леджером; payment-law дефинициален)
  coverage ⟺ переименованный ВЫВОД. Расщепления честны только для НАСТОЯЩЕЙ
  Step00-структуры: hit = реальное попадание генеалогии в repunit-центр
  (base-4 peel — подпоследовательность peel-шагов графа), платежи навязаны
  boundary/ledger-механикой. Их построение — живой фронт Мерсенн-ветки.
-/
import Mathlib
import EuclidsPath.Engine.MersennePaymentConflict

set_option autoImplicit false

namespace EuclidsPath
namespace Mersenne
namespace PeelPaymentPressure

/-#############################################################################
  §1. Mersenne centers, sides, and tail statements
#############################################################################-/

/-- Parametric primality predicate.  In concrete integration use `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- Base-4 repunit center sequence: `0, 1, 5, 21, 85, ...`. -/
def mersenneCenter : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * mersenneCenter k + 1

@[simp] theorem mersenneCenter_succ (k : Nat) :
    mersenneCenter (k + 1) = 4 * mersenneCenter k + 1 := by
  rfl

/-- A base-4 peel step: the larger center is `4` times the smaller center plus `1`. -/
def Base4PeelStep (large small : Nat) : Prop :=
  large = 4 * small + 1

/-- Mersenne centers satisfy the base-4 peel recurrence. -/
theorem mersenneCenter_base4PeelStep (k : Nat) :
    Base4PeelStep (mersenneCenter (k + 1)) (mersenneCenter k) := by
  rfl

/-- The lower side of a Step00 twin center. -/
def lowerSide (m : Nat) : Nat :=
  6 * m - 1

/-- The upper side of a Step00 twin center. -/
def upperSide (m : Nat) : Nat :=
  6 * m + 1

/-- Generic twin center relative to a primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- Mersenne-twin center at base-4 repunit index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Mersenne-twin supply at or above a Mersenne index horizon. -/
def MersenneTwinSupplyAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Mersenne-twin centers are absent on a tail. -/
def MersenneTwinAbsentAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Eventual absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, MersenneTwinAbsentAtOrAbove Prime K0

/-- Infinitely many Mersenne-twin centers in tail-supply form. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, MersenneTwinSupplyAtOrAbove Prime K0

/-- Eventual absence contradicts infinite Mersenne-twin supply. -/
theorem eventual_absence_forbids_infinite_mersenne_supply
    (Prime : PrimeLike)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    ¬ InfinitelyManyMersenneTwinCenters Prime := by
  intro hInf
  rcases hAbsent with ⟨K0, hTailAbsent⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hTailAbsent k hk hTwin

/-#############################################################################
  §2. Prime-payment ledger and extraction
#############################################################################-/

/-- A raw prime-payment ledger. -/
structure RawPrimePaymentLedger where
  Genealogy : Type
  PaysPrime : Genealogy → Nat → Prop

/-- Soundness of prime-payment: every paid token is genuinely prime. -/
def PrimePaymentSound (Prime : PrimeLike) (L : RawPrimePaymentLedger) : Prop :=
  ∀ Γ : L.Genealogy, ∀ n : Nat, L.PaysPrime Γ n → Prime n

/-- A genealogy pays both sides of the Mersenne center indexed by `k`. -/
def MersennePairPaid (L : RawPrimePaymentLedger) (Γ : L.Genealogy) (k : Nat) : Prop :=
  L.PaysPrime Γ (lowerSide (mersenneCenter k)) ∧
  L.PaysPrime Γ (upperSide (mersenneCenter k))

/-- A sound paid Mersenne pair extracts a genuine Mersenne-twin center. -/
theorem mersennePairPaid_extracts_twin
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    {Γ : L.Genealogy} {k : Nat}
    (hPaid : MersennePairPaid L Γ k) :
    MersenneTwinCenter Prime k := by
  exact ⟨hSound Γ (lowerSide (mersenneCenter k)) hPaid.1,
         hSound Γ (upperSide (mersenneCenter k)) hPaid.2⟩

/-- A paid Mersenne pair exists on or above a tail horizon. -/
def MersennePairPaidAtOrAbove (L : RawPrimePaymentLedger) (K0 : Nat) : Prop :=
  ∃ Γ : L.Genealogy,
  ∃ k : Nat,
    K0 ≤ k ∧ MersennePairPaid L Γ k

/-- Sound paid pair on a tail gives Mersenne-twin supply there. -/
theorem mersenne_supply_of_sound_pair_payment
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    (K0 : Nat)
    (hPaidTail : MersennePairPaidAtOrAbove L K0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  rcases hPaidTail with ⟨Γ, k, hk, hPaid⟩
  exact ⟨k, hk, mersennePairPaid_extracts_twin Prime L hSound hPaid⟩

/-- Tail absence plus soundness forbids paid pairs on that tail. -/
theorem absence_and_soundness_forbid_pair_payment
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    (K0 : Nat)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    ¬ MersennePairPaidAtOrAbove L K0 := by
  intro hPaidTail
  rcases mersenne_supply_of_sound_pair_payment Prime L hSound K0 hPaidTail with
    ⟨k, hk, hTwin⟩
  exact hAbsent k hk hTwin

/-#############################################################################
  §3. Ordinary twin supply and peel-hit pressure
#############################################################################-/

/-- Ordinary Step00 twin supply above a numeric horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/--
A peel-payment system: a prime-payment ledger plus a predicate saying that a
particular genealogy is anchored at the Mersenne peel center indexed by `k`.

`MersennePeelHit Γ k` must be instantiated later by the real Step00 genealogy / 
base-4 peel structure.  This file only audits the consequences.
-/
structure MersennePeelPaymentSystem where
  ledger : RawPrimePaymentLedger
  MersennePeelHit : ledger.Genealogy → Nat → Prop

namespace MersennePeelPaymentSystem

/-- Cofinal Mersenne peel coverage forced by ordinary twin supply. -/
def CofinalMersennePeelCoverage
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (S : MersennePeelPaymentSystem) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 →
      ∃ Γ : S.ledger.Genealogy,
      ∃ k : Nat,
        K0 ≤ k ∧ S.MersennePeelHit Γ k

/-- A peel hit forces both Mersenne side-prime payments. -/
def PeelHitForcesPrimePayment
    (S : MersennePeelPaymentSystem) : Prop :=
  ∀ Γ : S.ledger.Genealogy,
  ∀ k : Nat,
    S.MersennePeelHit Γ k → MersennePairPaid S.ledger Γ k

/-- The old pressure brick recovered from peel coverage and payment law. -/
def CofinalMersennePrimePaymentPressure
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : RawPrimePaymentLedger) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 → MersennePairPaidAtOrAbove L K0

/-- Peel coverage plus peel-payment law gives cofinal Mersenne prime-payment pressure. -/
theorem primePaymentPressure_of_peelCoverage_and_paymentLaw
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {S : MersennePeelPaymentSystem}
    (hCoverage : CofinalMersennePeelCoverage TwinAbove S)
    (hPay : PeelHitForcesPrimePayment S) :
    CofinalMersennePrimePaymentPressure TwinAbove S.ledger := by
  intro M0 K0 hTwin
  rcases hCoverage M0 K0 hTwin with ⟨Γ, k, hk, hHit⟩
  exact ⟨Γ, k, hk, hPay Γ k hHit⟩

/-- Cofinal prime-payment pressure plus soundness converts ordinary supply into Mersenne supply. -/
theorem mersenne_supply_of_primePaymentPressure
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : RawPrimePaymentLedger}
    (hPressure : CofinalMersennePrimePaymentPressure TwinAbove L)
    (hSound : PrimePaymentSound Prime L)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  exact mersenne_supply_of_sound_pair_payment Prime L hSound K0
    (hPressure M0 K0 hTwin)

/-- Peel coverage + payment law + soundness converts ordinary supply into Mersenne supply. -/
theorem mersenne_supply_of_peelCoverage_paymentLaw_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {S : MersennePeelPaymentSystem}
    (hCoverage : CofinalMersennePeelCoverage TwinAbove S)
    (hPay : PeelHitForcesPrimePayment S)
    (hSound : PrimePaymentSound Prime S.ledger)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  exact mersenne_supply_of_primePaymentPressure
    (primePaymentPressure_of_peelCoverage_and_paymentLaw hCoverage hPay)
    hSound M0 K0 hTwin

/-- Ordinary infinity plus peel coverage/payment/soundness gives infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_peelCoverage_paymentLaw_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {S : MersennePeelPaymentSystem}
    (hCoverage : CofinalMersennePeelCoverage TwinAbove S)
    (hPay : PeelHitForcesPrimePayment S)
    (hSound : PrimePaymentSound Prime S.ledger)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact mersenne_supply_of_peelCoverage_paymentLaw_soundness
    hCoverage hPay hSound 0 K0 (hOrdInf 0)

/-- Eventual absence contradicts ordinary infinity plus peel coverage/payment/soundness. -/
theorem eventual_absence_contradicts_peelCoverage_paymentLaw_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {S : MersennePeelPaymentSystem}
    (hCoverage : CofinalMersennePeelCoverage TwinAbove S)
    (hPay : PeelHitForcesPrimePayment S)
    (hSound : PrimePaymentSound Prime S.ledger)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  have hInf : InfinitelyManyMersenneTwinCenters Prime :=
    infinite_mersenne_supply_of_peelCoverage_paymentLaw_soundness
      hCoverage hPay hSound hOrdInf
  exact eventual_absence_forbids_infinite_mersenne_supply Prime hAbsent hInf

end MersennePeelPaymentSystem

/-#############################################################################
  §4. Defect split under eventual absence
#############################################################################-/

namespace Defects

/-- Cofinal peel coverage fails at a specific ordinary horizon and Mersenne tail. -/
def PeelCoverageCofinalityDefect
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (S : MersennePeelPaymentSystem)
    (M0 K0 : Nat) : Prop :=
  TwinAbove M0 ∧
    ¬ ∃ Γ : S.ledger.Genealogy,
      ∃ k : Nat,
        K0 ≤ k ∧ S.MersennePeelHit Γ k

/-- A peel hit exists on the tail but does not force the required paid pair. -/
def PeelPaymentLawDefect
    (S : MersennePeelPaymentSystem)
    (K0 : Nat) : Prop :=
  ∃ Γ : S.ledger.Genealogy,
  ∃ k : Nat,
    K0 ≤ k ∧ S.MersennePeelHit Γ k ∧ ¬ MersennePairPaid S.ledger Γ k

/-- A paid pair exists but sound extraction to a Mersenne twin fails. -/
def PrimePaymentExtractionDefect
    (Prime : PrimeLike)
    (S : MersennePeelPaymentSystem) : Prop :=
  ∃ Γ : S.ledger.Genealogy,
  ∃ k : Nat,
    MersennePairPaid S.ledger Γ k ∧ ¬ MersenneTwinCenter Prime k

/-- Soundness forbids prime-payment extraction defects. -/
theorem soundness_forbids_primePaymentExtractionDefect
    (Prime : PrimeLike)
    (S : MersennePeelPaymentSystem)
    (hSound : PrimePaymentSound Prime S.ledger) :
    ¬ PrimePaymentExtractionDefect Prime S := by
  intro hDefect
  rcases hDefect with ⟨Γ, k, hPaid, hNotTwin⟩
  exact hNotTwin (mersennePairPaid_extracts_twin Prime S.ledger hSound hPaid)

/--
Under tail absence and soundness, every tail peel hit must be a payment-law defect.
- if it paid both sides, soundness would extract a forbidden Mersenne-twin center.
-/
theorem tail_absence_turns_peelHit_into_paymentLawDefect
    (Prime : PrimeLike)
    (S : MersennePeelPaymentSystem)
    (hSound : PrimePaymentSound Prime S.ledger)
    (K0 : Nat)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0)
    {Γ : S.ledger.Genealogy}
    {k : Nat}
    (hk : K0 ≤ k)
    (hHit : S.MersennePeelHit Γ k) :
    ¬ MersennePairPaid S.ledger Γ k := by
  intro hPaid
  have hTwin : MersenneTwinCenter Prime k :=
    mersennePairPaid_extracts_twin Prime S.ledger hSound hPaid
  exact hAbsent k hk hTwin

/--
Under ordinary supply, tail absence, and soundness, any proposed raw peel-hit
mechanism must fail either at cofinal coverage or at the payment law.
-/
theorem absence_forces_peelCoverage_or_paymentLaw_defect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (S : MersennePeelPaymentSystem)
    (hSound : PrimePaymentSound Prime S.ledger)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    PeelCoverageCofinalityDefect TwinAbove S M0 K0 ∨
    PeelPaymentLawDefect S K0 := by
  by_cases hCoverageAtTail :
      ∃ Γ : S.ledger.Genealogy,
      ∃ k : Nat,
        K0 ≤ k ∧ S.MersennePeelHit Γ k
  · right
    rcases hCoverageAtTail with ⟨Γ, k, hk, hHit⟩
    have hNoPaid : ¬ MersennePairPaid S.ledger Γ k :=
      tail_absence_turns_peelHit_into_paymentLawDefect
        Prime S hSound K0 hAbsent hk hHit
    exact ⟨Γ, k, hk, hHit, hNoPaid⟩
  · left
    exact ⟨hTwin, hCoverageAtTail⟩

/-- If the payment law is assumed globally, absence forces cofinal coverage failure. -/
theorem absence_forces_peelCoverage_defect_of_paymentLaw
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (S : MersennePeelPaymentSystem)
    (hSound : PrimePaymentSound Prime S.ledger)
    (hPay : S.PeelHitForcesPrimePayment)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    PeelCoverageCofinalityDefect TwinAbove S M0 K0 := by
  have hNoCoverage :
      ¬ ∃ Γ : S.ledger.Genealogy,
      ∃ k : Nat,
        K0 ≤ k ∧ S.MersennePeelHit Γ k := by
    intro hCoverageAtTail
    rcases hCoverageAtTail with ⟨Γ, k, hk, hHit⟩
    have hPaid : MersennePairPaid S.ledger Γ k := hPay Γ k hHit
    have hTwinM : MersenneTwinCenter Prime k :=
      mersennePairPaid_extracts_twin Prime S.ledger hSound hPaid
    exact hAbsent k hk hTwinM
  exact ⟨hTwin, hNoCoverage⟩

end Defects

/-#############################################################################
  §5. Final route package
#############################################################################-/

/--
The next strict route package.

This does not assert coverage or payment law for free.  It names them as the two
new hard obligations.
-/
structure MersennePeelPaymentRoute
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  system : MersennePeelPaymentSystem
  sound : PrimePaymentSound Prime system.ledger
  ordinary_infinite : OrdinaryTwinInfinite TwinAbove
  peel_coverage : MersennePeelPaymentSystem.CofinalMersennePeelCoverage TwinAbove system
  peel_payment_law : MersennePeelPaymentSystem.PeelHitForcesPrimePayment system

/-- A peel-payment route yields cofinal Mersenne prime-payment pressure. -/
theorem primePaymentPressure_of_peelPaymentRoute
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelPaymentRoute Prime TwinAbove) :
    MersennePeelPaymentSystem.CofinalMersennePrimePaymentPressure TwinAbove R.system.ledger := by
  exact MersennePeelPaymentSystem.primePaymentPressure_of_peelCoverage_and_paymentLaw
    R.peel_coverage R.peel_payment_law

/-- A peel-payment route proves infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_peelPaymentRoute
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelPaymentRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact MersennePeelPaymentSystem.infinite_mersenne_supply_of_peelCoverage_paymentLaw_soundness
    R.peel_coverage R.peel_payment_law R.sound R.ordinary_infinite

/-- Therefore a peel-payment route forbids eventual Mersenne-twin absence. -/
theorem peelPaymentRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelPaymentRoute Prime TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbsent
  exact eventual_absence_forbids_infinite_mersenne_supply Prime hAbsent
    (infinite_mersenne_supply_of_peelPaymentRoute R)

/-- Final slogan for this layer. -/
theorem mersenne_peelPaymentPressure_slogan
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelPaymentRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime ∧
    MersennePeelPaymentSystem.CofinalMersennePrimePaymentPressure TwinAbove R.system.ledger := by
  exact ⟨infinite_mersenne_supply_of_peelPaymentRoute R,
         peelPaymentRoute_forbids_eventual_absence R,
         primePaymentPressure_of_peelPaymentRoute R⟩

end PeelPaymentPressure
end Mersenne
end EuclidsPath

namespace EuclidsPath
namespace Mersenne
namespace PeelCoveragePressure

/-#############################################################################
  §1. Minimal Mersenne/twin/payment vocabulary
#############################################################################-/

/-- Parametric primality predicate.  Instantiate with `Nat.Prime` in concrete use. -/
abbrev PrimeLike := Nat → Prop

/-- Base-4 repunit center sequence: `0, 1, 5, 21, 85, ...`. -/
def mersenneCenter : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * mersenneCenter k + 1

@[simp] theorem mersenneCenter_succ (k : Nat) :
    mersenneCenter (k + 1) = 4 * mersenneCenter k + 1 := by
  rfl

/-- Lower Step00 side of a twin center. -/
def lowerSide (m : Nat) : Nat :=
  6 * m - 1

/-- Upper Step00 side of a twin center. -/
def upperSide (m : Nat) : Nat :=
  6 * m + 1

/-- Ordinary twin center for an abstract primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- Mersenne-twin center at base-4 repunit index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Mersenne-twin supply at or above index `K0`. -/
def MersenneTwinSupplyAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Mersenne-twin centers absent on a tail. -/
def MersenneTwinAbsentAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Eventual Mersenne absence. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, MersenneTwinAbsentAtOrAbove Prime K0

/-- Infinite Mersenne supply in tail form. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, MersenneTwinSupplyAtOrAbove Prime K0

/-- Ordinary Step00 twin supply above a numeric horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/-- A raw prime-payment ledger. -/
structure RawPrimePaymentLedger where
  Genealogy : Type
  PaysPrime : Genealogy → Nat → Prop

/-- Payment soundness: anything paid as prime is genuinely prime. -/
def PrimePaymentSound (Prime : PrimeLike) (L : RawPrimePaymentLedger) : Prop :=
  ∀ Γ : L.Genealogy, ∀ n : Nat, L.PaysPrime Γ n → Prime n

/-- A genealogy pays both sides of Mersenne center `k`. -/
def MersennePairPaid (L : RawPrimePaymentLedger) (Γ : L.Genealogy) (k : Nat) : Prop :=
  L.PaysPrime Γ (lowerSide (mersenneCenter k)) ∧
  L.PaysPrime Γ (upperSide (mersenneCenter k))

/-- A sound paid pair extracts a Mersenne-twin center. -/
theorem mersennePairPaid_extracts_twin
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    {Γ : L.Genealogy} {k : Nat}
    (hPaid : MersennePairPaid L Γ k) :
    MersenneTwinCenter Prime k := by
  exact ⟨hSound Γ (lowerSide (mersenneCenter k)) hPaid.1,
         hSound Γ (upperSide (mersenneCenter k)) hPaid.2⟩

/-- Eventual absence contradicts infinite Mersenne supply. -/
theorem eventual_absence_forbids_infinite_mersenne_supply
    (Prime : PrimeLike)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    ¬ InfinitelyManyMersenneTwinCenters Prime := by
  intro hInf
  rcases hAbsent with ⟨K0, hTailAbsent⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hTailAbsent k hk hTwin

/-#############################################################################
  §2. Peel-hit system and old coverage brick
#############################################################################-/

/-- A system with a prime-payment ledger and a Mersenne peel-hit predicate. -/
structure MersennePeelPaymentSystem where
  ledger : RawPrimePaymentLedger
  MersennePeelHit : ledger.Genealogy → Nat → Prop

namespace MersennePeelPaymentSystem

/-- Cofinal Mersenne peel coverage forced by ordinary twin supply. -/
def CofinalMersennePeelCoverage
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (S : MersennePeelPaymentSystem) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 →
      ∃ Γ : S.ledger.Genealogy,
      ∃ k : Nat,
        K0 ≤ k ∧ S.MersennePeelHit Γ k

/-- A peel hit forces both side-prime payments. -/
def PeelHitForcesPrimePayment
    (S : MersennePeelPaymentSystem) : Prop :=
  ∀ Γ : S.ledger.Genealogy,
  ∀ k : Nat,
    S.MersennePeelHit Γ k → MersennePairPaid S.ledger Γ k

/-- Coverage + payment law + soundness gives one Mersenne twin above any tail. -/
theorem mersenne_supply_of_coverage_payment_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {S : MersennePeelPaymentSystem}
    (hCoverage : CofinalMersennePeelCoverage TwinAbove S)
    (hPay : PeelHitForcesPrimePayment S)
    (hSound : PrimePaymentSound Prime S.ledger)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  rcases hCoverage M0 K0 hTwin with ⟨Γ, k, hk, hHit⟩
  exact ⟨k, hk, mersennePairPaid_extracts_twin Prime S.ledger hSound (hPay Γ k hHit)⟩

/-- Ordinary infinity + coverage + payment + soundness gives infinite Mersenne supply. -/
theorem infinite_mersenne_supply_of_coverage_payment_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {S : MersennePeelPaymentSystem}
    (hCoverage : CofinalMersennePeelCoverage TwinAbove S)
    (hPay : PeelHitForcesPrimePayment S)
    (hSound : PrimePaymentSound Prime S.ledger)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact mersenne_supply_of_coverage_payment_soundness
    hCoverage hPay hSound 0 K0 (hOrdInf 0)

end MersennePeelPaymentSystem

/-#############################################################################
  §3. New split: peel-debt pressure
#############################################################################-/

/--
A peel-debt system enriches a peel-hit system with a debt index attached to each
ordinary-twin genealogy.

Intuition: `peelDebtIndex Γ` is the base-4 Mersenne peel layer that the genealogy
must eventually pay/visit.  If these indices are unbounded under ordinary twin
supply and every debt is realized as a peel hit, then cofinal peel coverage
follows.
-/
structure MersennePeelDebtSystem extends MersennePeelPaymentSystem where
  peelDebtIndex : ledger.Genealogy → Nat

namespace MersennePeelDebtSystem

/-- The underlying peel-payment system. -/
def toPaymentSystem (D : MersennePeelDebtSystem) : MersennePeelPaymentSystem where
  ledger := D.ledger
  MersennePeelHit := D.MersennePeelHit

@[simp] theorem toPaymentSystem_ledger (D : MersennePeelDebtSystem) :
    D.toPaymentSystem.ledger = D.ledger := rfl

/-- The debt index attached to a genealogy is realized as an actual Mersenne peel hit. -/
def PeelDebtRealizesHit (D : MersennePeelDebtSystem) : Prop :=
  ∀ Γ : D.ledger.Genealogy,
    D.MersennePeelHit Γ (D.peelDebtIndex Γ)

/-- Ordinary twin supply forces arbitrarily large peel-debt indices. -/
def CofinalPeelDebtPressure
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (D : MersennePeelDebtSystem) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 →
      ∃ Γ : D.ledger.Genealogy,
        K0 ≤ D.peelDebtIndex Γ

/-- Peel-debt pressure plus debt realization gives cofinal peel coverage. -/
theorem cofinalCoverage_of_debtPressure_and_realization
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : MersennePeelDebtSystem}
    (hDebt : CofinalPeelDebtPressure TwinAbove D)
    (hRealize : PeelDebtRealizesHit D) :
    MersennePeelPaymentSystem.CofinalMersennePeelCoverage TwinAbove D.toPaymentSystem := by
  intro M0 K0 hTwin
  rcases hDebt M0 K0 hTwin with ⟨Γ, hDebtLarge⟩
  exact ⟨Γ, D.peelDebtIndex Γ, hDebtLarge, hRealize Γ⟩

/-- A payment law on the debt system. -/
def PeelDebtHitForcesPrimePayment (D : MersennePeelDebtSystem) : Prop :=
  MersennePeelPaymentSystem.PeelHitForcesPrimePayment D.toPaymentSystem

/-- Debt pressure + realization + payment + soundness produces Mersenne supply. -/
theorem mersenne_supply_of_debtPressure_realization_payment_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : MersennePeelDebtSystem}
    (hDebt : CofinalPeelDebtPressure TwinAbove D)
    (hRealize : PeelDebtRealizesHit D)
    (hPay : PeelDebtHitForcesPrimePayment D)
    (hSound : PrimePaymentSound Prime D.ledger)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  exact MersennePeelPaymentSystem.mersenne_supply_of_coverage_payment_soundness
    (cofinalCoverage_of_debtPressure_and_realization hDebt hRealize)
    hPay
    hSound
    M0 K0 hTwin

/-- Ordinary infinity converts the debt route into infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_debtPressure_route
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : MersennePeelDebtSystem}
    (hDebt : CofinalPeelDebtPressure TwinAbove D)
    (hRealize : PeelDebtRealizesHit D)
    (hPay : PeelDebtHitForcesPrimePayment D)
    (hSound : PrimePaymentSound Prime D.ledger)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact mersenne_supply_of_debtPressure_realization_payment_soundness
    hDebt hRealize hPay hSound 0 K0 (hOrdInf 0)

/-- Eventual absence contradicts ordinary infinity plus the debt route. -/
theorem eventual_absence_contradicts_debtPressure_route
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : MersennePeelDebtSystem}
    (hDebt : CofinalPeelDebtPressure TwinAbove D)
    (hRealize : PeelDebtRealizesHit D)
    (hPay : PeelDebtHitForcesPrimePayment D)
    (hSound : PrimePaymentSound Prime D.ledger)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  exact eventual_absence_forbids_infinite_mersenne_supply Prime hAbsent
    (infinite_mersenne_supply_of_debtPressure_route
      hDebt hRealize hPay hSound hOrdInf)

end MersennePeelDebtSystem

/-#############################################################################
  §4. Defect analysis: what absence breaks
#############################################################################-/

namespace Defects

/-- Cofinal peel-debt pressure fails at a specific ordinary horizon and Mersenne tail. -/
def PeelDebtCofinalityDefect
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (D : MersennePeelDebtSystem)
    (M0 K0 : Nat) : Prop :=
  TwinAbove M0 ∧
    ¬ ∃ Γ : D.ledger.Genealogy, K0 ≤ D.peelDebtIndex Γ

/-- A debt index exists but is not realized as a peel hit. -/
def PeelDebtRealizationDefect
    (D : MersennePeelDebtSystem)
    (K0 : Nat) : Prop :=
  ∃ Γ : D.ledger.Genealogy,
    K0 ≤ D.peelDebtIndex Γ ∧
    ¬ D.MersennePeelHit Γ (D.peelDebtIndex Γ)

/-- A realized peel debt exists but does not force the required prime payments. -/
def PeelDebtPaymentDefect
    (D : MersennePeelDebtSystem)
    (K0 : Nat) : Prop :=
  ∃ Γ : D.ledger.Genealogy,
    K0 ≤ D.peelDebtIndex Γ ∧
    D.MersennePeelHit Γ (D.peelDebtIndex Γ) ∧
    ¬ MersennePairPaid D.ledger Γ (D.peelDebtIndex Γ)

/--
If a debt index is large, realized, and paid soundly, tail absence is impossible.
Thus under absence and soundness, such a genealogy must fail either realization
or payment.
-/
theorem absence_forces_realization_or_payment_defect_at_debt
    (Prime : PrimeLike)
    (D : MersennePeelDebtSystem)
    (hSound : PrimePaymentSound Prime D.ledger)
    (K0 : Nat)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0)
    (Γ : D.ledger.Genealogy)
    (hLarge : K0 ≤ D.peelDebtIndex Γ) :
    (¬ D.MersennePeelHit Γ (D.peelDebtIndex Γ)) ∨
    (D.MersennePeelHit Γ (D.peelDebtIndex Γ) ∧
      ¬ MersennePairPaid D.ledger Γ (D.peelDebtIndex Γ)) := by
  by_cases hHit : D.MersennePeelHit Γ (D.peelDebtIndex Γ)
  · right
    refine ⟨hHit, ?_⟩
    intro hPaid
    have hTwin : MersenneTwinCenter Prime (D.peelDebtIndex Γ) :=
      mersennePairPaid_extracts_twin Prime D.ledger hSound hPaid
    exact hAbsent (D.peelDebtIndex Γ) hLarge hTwin
  · left
    exact hHit

/--
Under tail absence and soundness, ordinary supply forces a trichotomy:
cofinal debt pressure fails, or debt realization fails, or debt payment fails.
-/
theorem absence_forces_debtCofinality_or_realization_or_payment_defect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (D : MersennePeelDebtSystem)
    (hSound : PrimePaymentSound Prime D.ledger)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    PeelDebtCofinalityDefect TwinAbove D M0 K0 ∨
    PeelDebtRealizationDefect D K0 ∨
    PeelDebtPaymentDefect D K0 := by
  by_cases hDebtAtTail : ∃ Γ : D.ledger.Genealogy, K0 ≤ D.peelDebtIndex Γ
  · rcases hDebtAtTail with ⟨Γ, hLarge⟩
    have hSplit := absence_forces_realization_or_payment_defect_at_debt
      Prime D hSound K0 hAbsent Γ hLarge
    rcases hSplit with hNoHit | hHitNoPaid
    · right
      left
      exact ⟨Γ, hLarge, hNoHit⟩
    · right
      right
      exact ⟨Γ, hLarge, hHitNoPaid.1, hHitNoPaid.2⟩
  · left
    exact ⟨hTwin, hDebtAtTail⟩

/-- If realization and payment law are global, absence forces debt cofinality failure. -/
theorem absence_forces_debtCofinality_defect_of_realization_payment
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (D : MersennePeelDebtSystem)
    (hSound : PrimePaymentSound Prime D.ledger)
    (hRealize : D.PeelDebtRealizesHit)
    (hPay : D.PeelDebtHitForcesPrimePayment)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    PeelDebtCofinalityDefect TwinAbove D M0 K0 := by
  have hNoDebtAtTail : ¬ ∃ Γ : D.ledger.Genealogy, K0 ≤ D.peelDebtIndex Γ := by
    intro hDebtAtTail
    rcases hDebtAtTail with ⟨Γ, hLarge⟩
    have hHit : D.MersennePeelHit Γ (D.peelDebtIndex Γ) := hRealize Γ
    have hPaid : MersennePairPaid D.ledger Γ (D.peelDebtIndex Γ) := hPay Γ (D.peelDebtIndex Γ) hHit
    have hTwinM : MersenneTwinCenter Prime (D.peelDebtIndex Γ) :=
      mersennePairPaid_extracts_twin Prime D.ledger hSound hPaid
    exact hAbsent (D.peelDebtIndex Γ) hLarge hTwinM
  exact ⟨hTwin, hNoDebtAtTail⟩

end Defects

/-#############################################################################
  §5. Final route package for this layer
#############################################################################-/

/--
The current strict route package: ordinary twin supply creates cofinal peel debt;
the debt is realized as a base-4 Mersenne peel hit; the hit pays both prime
sides; prime-payment soundness extracts Mersenne twins.
-/
structure MersennePeelDebtRoute
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  system : MersennePeelDebtSystem
  sound : PrimePaymentSound Prime system.ledger
  ordinary_infinite : OrdinaryTwinInfinite TwinAbove
  debt_pressure : MersennePeelDebtSystem.CofinalPeelDebtPressure TwinAbove system
  debt_realizes_hit : system.PeelDebtRealizesHit
  debt_payment_law : system.PeelDebtHitForcesPrimePayment

/-- The debt route yields cofinal peel coverage. -/
theorem cofinalCoverage_of_debtRoute
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelDebtRoute Prime TwinAbove) :
    MersennePeelPaymentSystem.CofinalMersennePeelCoverage TwinAbove R.system.toPaymentSystem := by
  exact MersennePeelDebtSystem.cofinalCoverage_of_debtPressure_and_realization
    R.debt_pressure R.debt_realizes_hit

/-- The debt route yields infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_debtRoute
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelDebtRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact MersennePeelDebtSystem.infinite_mersenne_supply_of_debtPressure_route
    R.debt_pressure R.debt_realizes_hit R.debt_payment_law R.sound R.ordinary_infinite

/-- The debt route forbids eventual Mersenne-twin absence. -/
theorem debtRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelDebtRoute Prime TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbsent
  exact eventual_absence_forbids_infinite_mersenne_supply Prime hAbsent
    (infinite_mersenne_supply_of_debtRoute R)

/-- Final slogan for this layer. -/
theorem mersenne_peelDebtPressure_slogan
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePeelDebtRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime ∧
    MersennePeelPaymentSystem.CofinalMersennePeelCoverage TwinAbove R.system.toPaymentSystem := by
  exact ⟨infinite_mersenne_supply_of_debtRoute R,
         debtRoute_forbids_eventual_absence R,
         cofinalCoverage_of_debtRoute R⟩

end PeelCoveragePressure
end Mersenne
end EuclidsPath

/-! Стыковка слоёв + цепь до цели + машинная честность -/

namespace EuclidsPath
namespace Mersenne

/-- Центры всех трёх слоёв совпадают (одна рекурренция). -/
theorem peelCenter_eq_conflictCenter :
    ∀ k, PeelPaymentPressure.mersenneCenter k
      = PrimePaymentConflict.mersenneCenter k
  | 0 => rfl
  | k + 1 => by
      rw [PeelPaymentPressure.mersenneCenter_succ,
        PrimePaymentConflict.mersenneCenter_succ,
        peelCenter_eq_conflictCenter k]

theorem coverageCenter_eq_conflictCenter :
    ∀ k, PeelCoveragePressure.mersenneCenter k
      = PrimePaymentConflict.mersenneCenter k
  | 0 => rfl
  | k + 1 => by
      rw [PeelCoveragePressure.mersenneCenter_succ,
        PrimePaymentConflict.mersenneCenter_succ,
        coverageCenter_eq_conflictCenter k]

/-- Перенос ∞-supply из peel-payment слоя в базовый. -/
theorem conflictSupply_of_peelSupply
    (h : PeelPaymentPressure.InfinitelyManyMersenneTwinCenters Nat.Prime) :
    PrimePaymentConflict.InfinitelyManyMersenneTwinCenters Nat.Prime := by
  intro K0
  obtain ⟨k, hk, hTwin⟩ := h K0
  have hraw : Nat.Prime (6 * PeelPaymentPressure.mersenneCenter k - 1) ∧
      Nat.Prime (6 * PeelPaymentPressure.mersenneCenter k + 1) := hTwin
  rw [peelCenter_eq_conflictCenter k] at hraw
  exact ⟨k, hk, hraw⟩

/-- Перенос ∞-supply из coverage слоя в базовый. -/
theorem conflictSupply_of_coverageSupply
    (h : PeelCoveragePressure.InfinitelyManyMersenneTwinCenters Nat.Prime) :
    PrimePaymentConflict.InfinitelyManyMersenneTwinCenters Nat.Prime := by
  intro K0
  obtain ⟨k, hk, hTwin⟩ := h K0
  have hraw : Nat.Prime (6 * PeelCoveragePressure.mersenneCenter k - 1) ∧
      Nat.Prime (6 * PeelCoveragePressure.mersenneCenter k + 1) := hTwin
  rw [coverageCenter_eq_conflictCenter k] at hraw
  exact ⟨k, hk, hraw⟩

/-- **ЦЕПЬ ДО ЦЕЛИ:** peel-payment route ⟹ TwinLowers.Infinite. -/
theorem twinLowersInfinite_of_peelPaymentRoute
    {TwinAbove : PeelPaymentPressure.OrdinaryTwinSupplyAbove}
    (R : PeelPaymentPressure.MersennePeelPaymentRoute Nat.Prime TwinAbove) :
    EuclidsPath.TwinLowers.Infinite :=
  twinLowersInfinite_of_infiniteMersenneSupply
    (conflictSupply_of_peelSupply
      (PeelPaymentPressure.infinite_mersenne_supply_of_peelPaymentRoute R))

/-- **ЦЕПЬ ДО ЦЕЛИ:** debt route ⟹ TwinLowers.Infinite. -/
theorem twinLowersInfinite_of_debtRoute
    {TwinAbove : PeelCoveragePressure.OrdinaryTwinSupplyAbove}
    (R : PeelCoveragePressure.MersennePeelDebtRoute Nat.Prime TwinAbove) :
    EuclidsPath.TwinLowers.Infinite :=
  twinLowersInfinite_of_infiniteMersenneSupply
    (conflictSupply_of_coverageSupply
      (PeelCoveragePressure.infinite_mersenne_supply_of_debtRoute R))

/-- Каноническая peel-система: «hit = уже twin» над everything-prime леджером. -/
def canonicalPeelSystem : PeelPaymentPressure.MersennePeelPaymentSystem where
  ledger := ⟨Unit, fun _ n => Nat.Prime n⟩
  MersennePeelHit := fun _ k =>
    PeelPaymentPressure.MersenneTwinCenter Nat.Prime k

/-- Для канонической системы payment-law выполняется дефинициально. -/
theorem canonical_paymentLaw :
    PeelPaymentPressure.MersennePeelPaymentSystem.PeelHitForcesPrimePayment
      canonicalPeelSystem :=
  fun _ _ h => h

/-- **ЧЕСТНОСТЬ:** для канонической системы coverage ⟺ переименованный ВЫВОД.
    Несущие входы честны только для НАСТОЯЩЕЙ Step00-структуры (hit = реальное
    попадание генеалогии в repunit-центр, платежи навязаны графом). -/
theorem canonical_coverage_iff
    {TwinAbove : PeelPaymentPressure.OrdinaryTwinSupplyAbove}
    (hInh : TwinAbove 0) :
    PeelPaymentPressure.MersennePeelPaymentSystem.CofinalMersennePeelCoverage
      TwinAbove canonicalPeelSystem ↔
    PeelPaymentPressure.InfinitelyManyMersenneTwinCenters Nat.Prime := by
  constructor
  · intro h K0
    obtain ⟨_, k, hk, hHit⟩ := h 0 K0 hInh
    exact ⟨k, hk, hHit⟩
  · intro h M0 K0 _
    obtain ⟨k, hk, hTwin⟩ := h K0
    exact ⟨(), k, hk, hTwin⟩

end Mersenne
end EuclidsPath
