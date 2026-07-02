/-
  MersennePaymentConflict — платёжный маршрут к Мерсенн-близнецам
  (кирпич: mersenne_prime_payment_conflict) + стыковка с MersenneBranch.
  Проза: prose/24 (Мерсенн-ветка).

  Маршрут кирпича (вся сборка доказана): sound-леджер платежей + обычная
  twin-бесконечность + КОФИНАЛЬНОЕ ДАВЛЕНИЕ (несущий вход:
  CofinalMersennePrimePaymentPressure — обычные близнецы навязывают
  оплаченные пары на repunit-центрах) ⟹ ∞ Мерсенн-близнецов; дихотомия
  дефектов при tail-отсутствии (cofinality vs extraction).

  СТЫКОВКА (при интеграции): repunit-центры кирпича = центры MersenneBranch
  при p = 2k+1 (sixCenter_add_one_eq_mersenne, без деления); ЦЕПЬ ДОВЕДЕНА
  ДО НАСТОЯЩЕЙ ЦЕЛИ: twinLowersInfinite_of_primePaymentRoute — платёжный
  route ⟹ TwinLowers.Infinite.

  ⚠️ МАШИННАЯ ЧЕСТНОСТЬ: pressure_iff_supply_for_everythingPrimeLedger —
  для канонического ledger'а «плати всё простое» pressure ⟺ переименованный
  ВЫВОД. Несущий вход честен только для НАСТОЯЩЕГО Step00-леджера генеалогий,
  где платежи навязаны структурой графа; его построение — живой фронт
  Мерсенн-ветки. Направление «близнецы ⟹ Мерсенн» по-прежнему НЕ утверждается:
  pressure сильнее обычной twin-бесконечности.
-/
import Mathlib
import EuclidsPath.Engine.MersenneBranch

set_option autoImplicit false

namespace EuclidsPath
namespace Mersenne
namespace PrimePaymentConflict

/-#############################################################################
  §1. Mersenne centers and Mersenne-twin centers
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

/-- The lower side of a Step00 twin center. -/
def lowerSide (m : Nat) : Nat :=
  6 * m - 1

/-- The upper side of a Step00 twin center. -/
def upperSide (m : Nat) : Nat :=
  6 * m + 1

/-- Generic twin center relative to a chosen primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- Mersenne-twin center at base-4 repunit index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Mersenne-twin supply at or above an index horizon. -/
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
  §2. Raw prime-payment ledger
#############################################################################-/

/--
A raw prime-payment ledger.

`PaysPrime Γ n` means that genealogy `Γ` pays/uses/certifies the number `n` as a
prime-payment token.  Soundness is NOT built in here; it is a separate
obligation so that defects can be stated explicitly.
-/
structure RawPrimePaymentLedger where
  Genealogy : Type
  PaysPrime : Genealogy → Nat → Prop

/-- Soundness of the prime-payment ledger. -/
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

/-- A Mersenne paid pair at or above a tail horizon. -/
def MersennePairPaidAtOrAbove (L : RawPrimePaymentLedger) (K0 : Nat) : Prop :=
  ∃ Γ : L.Genealogy,
  ∃ k : Nat,
    K0 ≤ k ∧ MersennePairPaid L Γ k

/-- Sound Mersenne pair-payment at a tail gives Mersenne-twin supply there. -/
theorem mersenne_supply_of_sound_pair_payment
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    (K0 : Nat)
    (hPaidTail : MersennePairPaidAtOrAbove L K0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  rcases hPaidTail with ⟨Γ, k, hk, hPaid⟩
  exact ⟨k, hk, mersennePairPaid_extracts_twin Prime L hSound hPaid⟩

/-- Tail absence forbids sound Mersenne pair-payment on that tail. -/
theorem tail_absence_forbids_sound_mersenne_pair_payment
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
  §3. Payment conflicts and defects
#############################################################################-/

/--
A payment conflict: a genealogy pays both sides of a Mersenne center on the tail,
but that index is not a Mersenne-twin center.
-/
def MersennePrimePaymentConflict
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (K0 : Nat) : Prop :=
  ∃ Γ : L.Genealogy,
  ∃ k : Nat,
    K0 ≤ k ∧ MersennePairPaid L Γ k ∧ ¬ MersenneTwinCenter Prime k

/-- Sound prime-payment forbids Mersenne prime-payment conflicts. -/
theorem soundness_forbids_mersennePrimePaymentConflict
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    (K0 : Nat) :
    ¬ MersennePrimePaymentConflict Prime L K0 := by
  intro hConflict
  rcases hConflict with ⟨Γ, k, _hk, hPaid, hNotTwin⟩
  exact hNotTwin (mersennePairPaid_extracts_twin Prime L hSound hPaid)

/-- Tail absence turns any paid Mersenne pair on the tail into a payment conflict. -/
theorem absence_plus_pair_payment_produces_paymentConflict
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (K0 : Nat)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0)
    (hPaidTail : MersennePairPaidAtOrAbove L K0) :
    MersennePrimePaymentConflict Prime L K0 := by
  rcases hPaidTail with ⟨Γ, k, hk, hPaid⟩
  exact ⟨Γ, k, hk, hPaid, hAbsent k hk⟩

/-- Therefore tail absence plus soundness forbids paid Mersenne pairs on the tail. -/
theorem absence_and_soundness_forbid_pair_payment
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    (K0 : Nat)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    ¬ MersennePairPaidAtOrAbove L K0 := by
  intro hPaidTail
  have hConflict := absence_plus_pair_payment_produces_paymentConflict
    Prime L K0 hAbsent hPaidTail
  exact soundness_forbids_mersennePrimePaymentConflict Prime L hSound K0 hConflict

/-#############################################################################
  §4. Ordinary twin supply and cofinal Mersenne prime-payment pressure
#############################################################################-/

/-- Ordinary Step00 twin supply above a numeric horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply, in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/--
Cofinal Mersenne prime-payment pressure.

This is the new live brick for the proposed route.  It says that ordinary twin
supply forces paid Mersenne pairs cofinally far out in the Mersenne index.
-/
structure CofinalMersennePrimePaymentPressure
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : RawPrimePaymentLedger) where
  cofinal_paid_pair :
    ∀ M0 K0 : Nat,
      TwinAbove M0 → MersennePairPaidAtOrAbove L K0

namespace CofinalMersennePrimePaymentPressure

/-- Cofinal prime-payment pressure plus soundness converts ordinary supply into Mersenne supply. -/
theorem mersenne_supply_of_ordinary_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : RawPrimePaymentLedger}
    (C : CofinalMersennePrimePaymentPressure TwinAbove L)
    (hSound : PrimePaymentSound Prime L)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  exact mersenne_supply_of_sound_pair_payment Prime L hSound K0
    (C.cofinal_paid_pair M0 K0 hTwin)

/-- Ordinary infinite supply plus pressure plus soundness gives infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_ordinary_infinite
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : RawPrimePaymentLedger}
    (C : CofinalMersennePrimePaymentPressure TwinAbove L)
    (hSound : PrimePaymentSound Prime L)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact C.mersenne_supply_of_ordinary_supply hSound 0 K0 (hOrdInf 0)

/-- Eventual absence contradicts any one ordinary supply point plus pressure plus soundness. -/
theorem eventual_absence_contradicts_pressure_of_ordinary_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : RawPrimePaymentLedger}
    (C : CofinalMersennePrimePaymentPressure TwinAbove L)
    (hSound : PrimePaymentSound Prime L)
    (M0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  rcases hAbsent with ⟨K0, hTailAbsent⟩
  have hPaidTail : MersennePairPaidAtOrAbove L K0 :=
    C.cofinal_paid_pair M0 K0 hTwin
  exact absence_and_soundness_forbid_pair_payment
    Prime L hSound K0 hTailAbsent hPaidTail

/-- Eventual absence contradicts ordinary infinite supply plus pressure plus soundness. -/
theorem eventual_absence_contradicts_ordinary_infinite_pressure_and_soundness
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : RawPrimePaymentLedger}
    (C : CofinalMersennePrimePaymentPressure TwinAbove L)
    (hSound : PrimePaymentSound Prime L)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  exact C.eventual_absence_contradicts_pressure_of_ordinary_supply
    hSound 0 (hOrdInf 0) hAbsent

/-- Therefore eventual absence rules out cofinal prime-payment pressure under ordinary infinity and soundness. -/
theorem no_pressure_of_ordinary_infinite_soundness_and_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : RawPrimePaymentLedger}
    (hSound : PrimePaymentSound Prime L)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    ¬ CofinalMersennePrimePaymentPressure TwinAbove L := by
  intro C
  exact C.eventual_absence_contradicts_ordinary_infinite_pressure_and_soundness
    hSound hOrdInf hAbsent

end CofinalMersennePrimePaymentPressure

/-#############################################################################
  §5. Defect dichotomy under Mersenne absence
#############################################################################-/

/--
Cofinality defect: ordinary twin supply is present at `M0`, but no paid Mersenne
pair appears on the Mersenne tail `K0`.
-/
def MersennePrimePaymentCofinalityDefect
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : RawPrimePaymentLedger)
    (M0 K0 : Nat) : Prop :=
  TwinAbove M0 ∧ ¬ MersennePairPaidAtOrAbove L K0

/--
Extraction defect: a paid Mersenne pair exists, but it does not extract a
Mersenne-twin center.  For a sound prime-payment ledger this is impossible.
-/
def MersennePrimePaymentExtractionDefect
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger) : Prop :=
  ∃ Γ : L.Genealogy,
  ∃ k : Nat,
    MersennePairPaid L Γ k ∧ ¬ MersenneTwinCenter Prime k

/-- Soundness forbids extraction defects. -/
theorem soundness_forbids_extractionDefect
    (Prime : PrimeLike)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L) :
    ¬ MersennePrimePaymentExtractionDefect Prime L := by
  intro hDefect
  rcases hDefect with ⟨Γ, k, hPaid, hNotTwin⟩
  exact hNotTwin (mersennePairPaid_extracts_twin Prime L hSound hPaid)

/--
Under ordinary supply at `M0`, tail absence at `K0` forces a defect in any raw
payment system: either no cofinal paid pair exists, or paid-pair extraction fails.
-/
theorem absence_forces_payment_cofinality_or_extraction_defect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : RawPrimePaymentLedger)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    MersennePrimePaymentCofinalityDefect TwinAbove L M0 K0 ∨
    MersennePrimePaymentExtractionDefect Prime L := by
  by_cases hPaidTail : MersennePairPaidAtOrAbove L K0
  · right
    rcases hPaidTail with ⟨Γ, k, hk, hPaid⟩
    exact ⟨Γ, k, hPaid, hAbsent k hk⟩
  · left
    exact ⟨hTwin, hPaidTail⟩

/-- If the ledger is sound, tail absence forces the cofinality defect. -/
theorem absence_forces_payment_cofinality_defect_of_soundness
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : RawPrimePaymentLedger)
    (hSound : PrimePaymentSound Prime L)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    MersennePrimePaymentCofinalityDefect TwinAbove L M0 K0 := by
  have hNoPaid : ¬ MersennePairPaidAtOrAbove L K0 :=
    absence_and_soundness_forbid_pair_payment Prime L hSound K0 hAbsent
  exact ⟨hTwin, hNoPaid⟩

/-#############################################################################
  §6. Final status object
#############################################################################-/

/--
The strict prime-payment route package.

If all fields are supplied, eventual absence of Mersenne-twin centers is
impossible.  The hard field is `pressure`.
-/
structure MersennePrimePaymentRoute
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  ledger : RawPrimePaymentLedger
  sound : PrimePaymentSound Prime ledger
  ordinary_infinite : OrdinaryTwinInfinite TwinAbove
  pressure : CofinalMersennePrimePaymentPressure TwinAbove ledger

/-- The prime-payment route proves infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_primePaymentRoute
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePrimePaymentRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact R.pressure.infinite_mersenne_supply_of_ordinary_infinite
    R.sound R.ordinary_infinite

/-- The prime-payment route forbids eventual absence. -/
theorem primePaymentRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePrimePaymentRoute Prime TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbsent
  exact eventual_absence_forbids_infinite_mersenne_supply Prime hAbsent
    (infinite_mersenne_supply_of_primePaymentRoute R)

/-- Final slogan: absence + sound payment + cofinal pressure is inconsistent. -/
theorem mersenne_primePayment_conflict_slogan
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePrimePaymentRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨infinite_mersenne_supply_of_primePaymentRoute R,
         primePaymentRoute_forbids_eventual_absence R⟩

end PrimePaymentConflict
end Mersenne
end EuclidsPath

/-! Стыковка с MersenneBranch + машинная честность -/

namespace EuclidsPath
namespace Mersenne

open PrimePaymentConflict

/-- Соответствие индексов: repunit-центр кирпича = центр MersenneBranch
    при p = 2k+1 (без деления: через 6c+1 = 2^p − 1). -/
theorem sixCenter_add_one_eq_mersenne :
    ∀ k : ℕ,
      6 * PrimePaymentConflict.mersenneCenter k + 1 = mersenne (2 * k + 1)
  | 0 => by norm_num [PrimePaymentConflict.mersenneCenter, mersenne]
  | k + 1 => by
      have ih := sixCenter_add_one_eq_mersenne k
      have hpow : (2 : ℕ) ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add]
        ring
      have h1 : 1 ≤ (2 : ℕ) ^ (2 * k + 1) := Nat.one_le_two_pow
      unfold mersenne at ih ⊢
      rw [PrimePaymentConflict.mersenneCenter_succ]
      omega

/-- Twin-центр кирпича = IsTwinCenter программы (дефинициально). -/
theorem twinCenter_iff_isTwinCenter (m : ℕ) :
    TwinCenter Nat.Prime m ↔ EuclidsPath.IsTwinCenter m :=
  Iff.rfl

/-- **ЦЕПЬ ДО НАСТОЯЩЕЙ ЦЕЛИ:** ∞ Мерсенн-близнецов (в форме кирпича) ⟹
    TwinLowers.Infinite (через мост MersenneBranch). -/
theorem twinLowersInfinite_of_infiniteMersenneSupply
    (h : InfinitelyManyMersenneTwinCenters Nat.Prime) :
    EuclidsPath.TwinLowers.Infinite := by
  apply EuclidsPath.MersenneBranch.twinLowersInfinite_of_mersenneTwins
  intro N
  obtain ⟨k, hk, hlo, hhi⟩ := h (N + 1)
  have hsix := sixCenter_add_one_eq_mersenne k
  have h1 : 1 ≤ (2 : ℕ) ^ (2 * k + 1) := Nat.one_le_two_pow
  refine ⟨2 * k + 1, ?_, ?_, ?_⟩
  · -- N < 2^(2k+1) − 3 при k ≥ N+1
    have hgrow : N + 3 < 2 ^ (N + 3) := Nat.lt_two_pow_self
    have hmono : (2 : ℕ) ^ (N + 3) ≤ 2 ^ (2 * k + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold mersenne at hsix
    omega
  · -- (2^(2k+1) − 3).Prime = нижняя сторона
    have : PrimePaymentConflict.lowerSide (PrimePaymentConflict.mersenneCenter k)
        = 2 ^ (2 * k + 1) - 3 := by
      unfold PrimePaymentConflict.lowerSide
      unfold mersenne at hsix
      omega
    rwa [this] at hlo
  · -- mersenne (2k+1) — верхняя сторона
    have : PrimePaymentConflict.upperSide (PrimePaymentConflict.mersenneCenter k)
        = mersenne (2 * k + 1) := by
      unfold PrimePaymentConflict.upperSide
      omega
    rwa [this] at hhi

/-- Полная цепь маршрута: платёжный route ⟹ гипотеза близнецов. -/
theorem twinLowersInfinite_of_primePaymentRoute
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersennePrimePaymentRoute Nat.Prime TwinAbove) :
    EuclidsPath.TwinLowers.Infinite :=
  twinLowersInfinite_of_infiniteMersenneSupply
    (infinite_mersenne_supply_of_primePaymentRoute R)

/-- Канонический ledger «плати всё простое». -/
def everythingPrimeLedger : RawPrimePaymentLedger where
  Genealogy := Unit
  PaysPrime := fun _ n => Nat.Prime n

theorem everythingPrimeLedger_sound :
    PrimePaymentSound Nat.Prime everythingPrimeLedger :=
  fun _ _ h => h

/-- **ЧЕСТНОСТЬ:** для канонического ledger'а pressure ⟺ переименованный
    ВЫВОД (∞ Мерсенн-близнецов). Несущий вход — pressure для НАСТОЯЩЕГО
    Step00-леджера генеалогий (где платежи навязаны структурой графа),
    а не для произвольного; иначе вход = заключение. -/
theorem pressure_iff_supply_for_everythingPrimeLedger
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hInh : TwinAbove 0) :
    Nonempty (CofinalMersennePrimePaymentPressure TwinAbove everythingPrimeLedger)
      ↔ InfinitelyManyMersenneTwinCenters Nat.Prime := by
  constructor
  · rintro ⟨C⟩ K0
    obtain ⟨_, k, hk, hlo, hhi⟩ := C.cofinal_paid_pair 0 K0 hInh
    exact ⟨k, hk, hlo, hhi⟩
  · intro h
    refine ⟨⟨fun M0 K0 _ => ?_⟩⟩
    obtain ⟨k, hk, hlo, hhi⟩ := h K0
    exact ⟨(), k, hk, hlo, hhi⟩

end Mersenne
end EuclidsPath
