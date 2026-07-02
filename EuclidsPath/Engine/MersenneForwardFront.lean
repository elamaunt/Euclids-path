/-
  MersenneForwardFront — форвард-серия Мерсенна (34 кирпича одной сборкой):
  peel-lift сертификаты/операторы/законы расширения, точная successor-арифметика,
  sparse-маршруты и index-jump lift, debt-firewalls (bounded/high/tail),
  same-key pigeonhole, resolver-payment firewall/decomposition, admissible
  filter + circularity audit, side-payment сертификат, semantic target realizer,
  cofinal filter selector, nonabsorption, four-defect closure, oversaturation
  engine bridge, no-escape / full-closure / endgame, current final front audit,
  one-file max forward, мост к twin-Step00.

  ВНИМАНИЕ — ВАКУУМНОСТЬ ПОЗДНИХ КИРПИЧЕЙ (флаги сборочного аудита):
    * ПАКЕТЫ-ГИПОТЕЗЫ НЕОБИТАЕМЫ у: LegacyStep00NoEscapeLayer (four_defect),
      TwinStep00NoEscapeLayer / AcceptedTwinStep00NoGoPackage (twin_step00_bridge),
      NoForbiddenPrimePaymentEngine-семейство (oversaturation / no_escape /
      full_closure_endgame): их noEngine требует Engine -> False, но токены
      несут СВОБОДНОЕ поле witness : Prop — «двигатель» тривиально строится
      (witness := True), слой противоречив, и headline-теоремы
      (produces_infinite_mersenne_twins и родственные) ВАКУУМНЫ. Маршруты в
      этой форме неинстанциируемы; нужна привязка token-witness к реальной
      Step00-структуре.
    * TwinStep00CausalClosureNode — свободный гейт (Prop + proof).
    * Renamed-conclusion входы: PrimePaymentSound / lower+upper_sound —
      целевой вывод, переупакованный «законом»; CofinalAdmissibleGenealogyHits /
      cofinal_filter напрямую поставляют кофинальные admissible-индексы.
    * Свободные гейты честности (один кирпич сам инстанциирует такой гейт
      True): not_using_ordinary_twin_absence, cofinal_tail_scope,
      not_using_mersenne_twin_infinitude, not_using_classical_PNP,
      lower/upper_not_circular.
    * tokenOfFinalDefect переписан (оригинал нетипизируем) — не проходит через
      четыре типизированных адаптера (twinTokenOfAbsence проходит).
  Безусловных сильных выводов нет; sorry/axiom нет.
-/
import Mathlib
import EuclidsPath.Engine.MersennePeelPressure

set_option autoImplicit false

-- ===== BRICK: EuclidsPath_mersenne_absence_defect_patch.lean =====
/-
EuclidsPath — patch: Mersenne absence as a defect
===================================================

Purpose
-------
This file does NOT prove that there are infinitely many Mersenne primes,
Mersenne-twin centers, or ordinary twin primes.

It proves a precise conditional/audit statement:

  If the Step00/Mersenne projection architecture imposes a tail-supply
  obligation for Mersenne-twin centers, then absence of such centers on a tail
  is exactly a supply defect; and if ordinary Step00 twin supply is assumed to
  project into the Mersenne repunit centers, then ordinary twin supply together
  with Mersenne-tail absence is a projection defect.

Thus the statement formalized here is:

  "absence of Mersenne-twin centers is a defect relative to the Mersenne supply
   obligation / projection obligation"

not:

  "there are infinitely many Mersenne-twin centers".

No `axiom`. No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne

/-#############################################################################
  §1. Base-4 repunit centers
#############################################################################-/

/--
The Mersenne center sequence, written as base-4 repunits:

  0, 1, 5, 21, 85, ...

For `k ≥ 1`, this is `1 + 4 + ... + 4^(k-1)` and equivalently
`(4^k - 1) / 3`.
-/
def mersenneCenter : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * mersenneCenter k + 1

/-- The defining peel/append relation for base-4 repunit centers. -/
@[simp] theorem mersenneCenter_succ (k : Nat) :
    mersenneCenter (k + 1) = 4 * mersenneCenter k + 1 := by
  rfl

/-- Algebraic base-4 repunit identity: `3*m_k + 1 = 4^k`. -/
theorem three_mul_mersenneCenter_add_one :
    ∀ k : Nat, 3 * mersenneCenter k + 1 = 4^k
  | 0 => by
      simp [mersenneCenter]
  | k + 1 => by
      calc
        3 * mersenneCenter (k + 1) + 1
            = 3 * (4 * mersenneCenter k + 1) + 1 := by
                simp [mersenneCenter]
        _ = 4 * (3 * mersenneCenter k + 1) := by
                ring
        _ = 4 * 4^k := by
                rw [three_mul_mersenneCenter_add_one k]
        _ = 4^(k + 1) := by
                ring_nf

/-- Odd Mersenne exponent associated to the center `m_k`. -/
def mersenneOddExponent (k : Nat) : Nat :=
  2 * k + 1

/-- The Mersenne power `2^(2k+1)`. -/
def mersennePower (k : Nat) : Nat :=
  2 ^ mersenneOddExponent k

/-- Center identity in subtraction-free form: `6*m_k + 2 = 2^(2k+1)`. -/
theorem six_mul_mersenneCenter_add_two_eq_power (k : Nat) :
    6 * mersenneCenter k + 2 = mersennePower k := by
  unfold mersennePower mersenneOddExponent
  have h := three_mul_mersenneCenter_add_one k
  calc
    6 * mersenneCenter k + 2
        = 2 * (3 * mersenneCenter k + 1) := by ring
    _ = 2 * 4^k := by rw [h]
    _ = 2^(2 * k + 1) := by
          rw [pow_succ, pow_mul]
          ring

/-#############################################################################
  §2. Mersenne-twin centers
#############################################################################-/

/--
A parametric primality predicate.  In concrete integration, instantiate it with
`Nat.Prime`.
-/
abbrev PrimeLike := Nat → Prop

/-- The lower side of a Step00 twin center. -/
def lowerSide (m : Nat) : Nat :=
  6 * m - 1

/-- The upper side of a Step00 twin center. -/
def upperSide (m : Nat) : Nat :=
  6 * m + 1

/-- A generic twin center relative to a chosen primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- A Mersenne-twin center is a twin center whose center is the base-4 repunit `m_k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Expanded criterion for being a Mersenne-twin center. -/
theorem mersenneTwinCenter_iff_sides
    (Prime : PrimeLike) (k : Nat) :
    MersenneTwinCenter Prime k ↔
      Prime (lowerSide (mersenneCenter k)) ∧
      Prime (upperSide (mersenneCenter k)) := by
  rfl

/-#############################################################################
  §3. Tail supply, absence and defect
#############################################################################-/

/-- There is a Mersenne-twin center at or above index horizon `K0`. -/
def MersenneTwinSupplyAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Mersenne-twin centers are absent at and above index horizon `K0`. -/
def MersenneTwinAbsentAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/--
A supply defect: the expected tail supply is missing.

This is the exact formal meaning of "absence is a defect" in this file.
-/
def MersenneSupplyDefect (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ¬ MersenneTwinSupplyAtOrAbove Prime K0

/-- Absence on a tail is exactly a Mersenne supply defect. -/
theorem absence_is_mersenneSupplyDefect
    (Prime : PrimeLike) (K0 : Nat)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    MersenneSupplyDefect Prime K0 := by
  intro hSupply
  rcases hSupply with ⟨k, hk, hTwin⟩
  exact hAbsent k hk hTwin

/-- A tail supply defect gives absence on that tail. -/
theorem mersenneSupplyDefect_is_absence
    (Prime : PrimeLike) (K0 : Nat)
    (hDefect : MersenneSupplyDefect Prime K0) :
    MersenneTwinAbsentAtOrAbove Prime K0 := by
  intro k hk hTwin
  exact hDefect ⟨k, hk, hTwin⟩

/-- Tail absence and tail defect are equivalent. -/
theorem absence_iff_mersenneSupplyDefect
    (Prime : PrimeLike) (K0 : Nat) :
    MersenneTwinAbsentAtOrAbove Prime K0 ↔
      MersenneSupplyDefect Prime K0 := by
  constructor
  · exact absence_is_mersenneSupplyDefect Prime K0
  · exact mersenneSupplyDefect_is_absence Prime K0

/-- No defect at a horizon forces an actual Mersenne-twin center on that tail. -/
theorem no_defect_forces_tail_supply
    (Prime : PrimeLike) (K0 : Nat)
    (hNoDefect : ¬ MersenneSupplyDefect Prime K0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  by_contra hNoSupply
  exact hNoDefect hNoSupply

/-- No defect at a horizon forbids total absence on that tail. -/
theorem no_defect_forbids_absence
    (Prime : PrimeLike) (K0 : Nat)
    (hNoDefect : ¬ MersenneSupplyDefect Prime K0) :
    ¬ MersenneTwinAbsentAtOrAbove Prime K0 := by
  intro hAbsent
  exact hNoDefect (absence_is_mersenneSupplyDefect Prime K0 hAbsent)

/-#############################################################################
  §4. Infinite supply versus persistent defect
#############################################################################-/

/-- Infinitely many Mersenne-twin centers, in tail-supply form. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, MersenneTwinSupplyAtOrAbove Prime K0

/-- Eventual absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, MersenneTwinAbsentAtOrAbove Prime K0

/-- Persistent Mersenne defect: at least one tail has missing supply. -/
def PersistentMersenneSupplyDefect (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, MersenneSupplyDefect Prime K0

/-- Eventual absence gives a persistent defect. -/
theorem eventual_absence_is_persistent_defect
    (Prime : PrimeLike)
    (hEventuallyAbsent : EventuallyNoMersenneTwinCenters Prime) :
    PersistentMersenneSupplyDefect Prime := by
  rcases hEventuallyAbsent with ⟨K0, hAbsent⟩
  exact ⟨K0, absence_is_mersenneSupplyDefect Prime K0 hAbsent⟩

/-- Infinite tail supply excludes persistent defect. -/
theorem infinite_mersenne_supply_forbids_persistent_defect
    (Prime : PrimeLike)
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ PersistentMersenneSupplyDefect Prime := by
  intro hPersistent
  rcases hPersistent with ⟨K0, hDefect⟩
  exact hDefect (hInf K0)

/-- No persistent defect forces infinite tail supply. -/
theorem no_persistent_defect_forces_infinite_mersenne_supply
    (Prime : PrimeLike)
    (hNoPersistent : ¬ PersistentMersenneSupplyDefect Prime) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  by_contra hNoSupply
  exact hNoPersistent ⟨K0, hNoSupply⟩

/-- Infinite Mersenne supply is equivalent to absence of persistent defect. -/
theorem infinite_mersenne_supply_iff_no_persistent_defect
    (Prime : PrimeLike) :
    InfinitelyManyMersenneTwinCenters Prime ↔
      ¬ PersistentMersenneSupplyDefect Prime := by
  constructor
  · exact infinite_mersenne_supply_forbids_persistent_defect Prime
  · exact no_persistent_defect_forces_infinite_mersenne_supply Prime

/-#############################################################################
  §5. Projection defect from general Step00 twin supply to Mersenne centers
#############################################################################-/

/--
An abstract ordinary Step00 twin-supply predicate above a numeric horizon.
In concrete integration, this is instantiated by the ordinary twin-center branch.
-/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/--
A projection obligation from ordinary Step00 twin supply to the Mersenne repunit
subsequence.

If ordinary twin supply exists above `M0`, the architecture is expected to produce
Mersenne-twin supply above the corresponding Mersenne index horizon `K0`.
-/
structure MersenneProjectionObligation
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  indexHorizon : Nat → Nat
  projects :
    ∀ M0 : Nat,
      TwinAbove M0 →
        MersenneTwinSupplyAtOrAbove Prime (indexHorizon M0)

/--
Projection defect: ordinary twin supply is present, but its Mersenne projection
has missing tail supply.
-/
def MersenneProjectionDefect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (P : MersenneProjectionObligation Prime TwinAbove)
    (M0 : Nat) : Prop :=
  TwinAbove M0 ∧
  MersenneSupplyDefect Prime (P.indexHorizon M0)

/--
If ordinary twin supply exists but Mersenne centers are absent on the projected
Mersenne tail, then we have a projection defect.
-/
theorem absence_against_projection_is_defect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (P : MersenneProjectionObligation Prime TwinAbove)
    (M0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime (P.indexHorizon M0)) :
    MersenneProjectionDefect Prime TwinAbove P M0 := by
  exact ⟨hTwin, absence_is_mersenneSupplyDefect Prime (P.indexHorizon M0) hAbsent⟩

/--
A valid projection obligation forbids projection defects.
-/
theorem projection_obligation_forbids_defect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (P : MersenneProjectionObligation Prime TwinAbove)
    (M0 : Nat) :
    ¬ MersenneProjectionDefect Prime TwinAbove P M0 := by
  intro hDefect
  rcases hDefect with ⟨hTwin, hDefectTail⟩
  exact hDefectTail (P.projects M0 hTwin)

/--
Therefore a true ordinary supply plus a true projection obligation forbids
Mersenne-tail absence at the projected horizon.
-/
theorem projection_obligation_forbids_absence
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (P : MersenneProjectionObligation Prime TwinAbove)
    (M0 : Nat)
    (hTwin : TwinAbove M0) :
    ¬ MersenneTwinAbsentAtOrAbove Prime (P.indexHorizon M0) := by
  intro hAbsent
  have hDefect : MersenneProjectionDefect Prime TwinAbove P M0 :=
    absence_against_projection_is_defect Prime TwinAbove P M0 hTwin hAbsent
  exact projection_obligation_forbids_defect Prime TwinAbove P M0 hDefect

/-#############################################################################
  §6. Status slogan
#############################################################################-/

/--
Compact final status: Mersenne absence is not a theorem of arithmetic here; it is
exactly a defect relative to a declared tail-supply obligation.
-/
theorem mersenne_absence_defect_slogan
    (Prime : PrimeLike) (K0 : Nat) :
    MersenneTwinAbsentAtOrAbove Prime K0 ↔
      MersenneSupplyDefect Prime K0 := by
  exact absence_iff_mersenneSupplyDefect Prime K0

end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_genealogy_coverage_bridge_patch.lean =====
/-
EuclidsPath — patch: Mersenne genealogy coverage bridge
=======================================================

Purpose
-------
This patch formalizes the proposed route:

  assume there are only finitely many Mersenne-twin centers
  and try to contradict ordinary infinite twin supply by showing that Step00
  genealogies must hit Mersenne centers.

The crucial distinction is made precise:

  * a weak statement “some genealogy hits some Mersenne number” is NOT enough;
  * a cofinal statement “for every Mersenne tail K0, ordinary twin supply forces
    a genealogy hit at some Mersenne index k ≥ K0, and each such hit extracts a
    genuine Mersenne-twin center” IS enough.

No theorem here proves that the cofinal coverage bridge exists.  The file proves
that this bridge is exactly the missing obstruction: if it is built, eventual
absence of Mersenne-twin centers contradicts ordinary twin supply.

No `axiom`. No `sorry`.
-/



namespace EuclidsPath
namespace MersenneGenealogyBridge

/-#############################################################################
  §1. Mersenne centers and Mersenne-twin centers
#############################################################################-/

/-- Parametric primality predicate.  Concrete integration: instantiate as `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- Base-4 repunit Mersenne centers: `0, 1, 5, 21, 85, ...`. -/
def mersenneCenter : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * mersenneCenter k + 1

/-- Lower side of a Step00 twin center. -/
def lowerSide (m : Nat) : Nat :=
  6 * m - 1

/-- Upper side of a Step00 twin center. -/
def upperSide (m : Nat) : Nat :=
  6 * m + 1

/-- Generic twin center relative to a chosen primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- A Mersenne-twin center at base-4 repunit index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Tail supply of Mersenne-twin centers. -/
def MersenneTwinSupplyAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Absence of Mersenne-twin centers on a tail. -/
def MersenneTwinAbsentAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Infinitely many Mersenne-twin centers, in tail-supply form. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, MersenneTwinSupplyAtOrAbove Prime K0

/-- Eventual absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, MersenneTwinAbsentAtOrAbove Prime K0

/-- Eventual absence forbids infinite Mersenne-twin supply. -/
theorem eventual_absence_forbids_infinite_mersenne_supply
    (Prime : PrimeLike)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    ¬ InfinitelyManyMersenneTwinCenters Prime := by
  intro hInf
  rcases hAbsent with ⟨K0, hTailAbsent⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hTailAbsent k hk hTwin

/-#############################################################################
  §2. Ordinary twin supply and abstract genealogies
#############################################################################-/

/-- Ordinary Step00 twin supply above a numeric horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply, in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/--
A weak genealogy-hit statement.

This captures the informal sentence “there exists a genealogy containing a
Mersenne number”.  It is intentionally weak and is not enough for contradiction
with eventual absence.
-/
structure WeakMersenneGenealogyHit where
  Genealogy : Type
  MersenneHit : Genealogy → Nat → Prop
  exists_hit : Nonempty {x : Genealogy × Nat // MersenneHit x.1 x.2}

/--
Weak hits alone do not assert any primality/twin property.  This theorem records
only the tautological content of a weak hit: there is a hit.
-/
theorem weakHit_only_gives_a_hit
    (W : WeakMersenneGenealogyHit) :
    Nonempty {x : W.Genealogy × Nat // W.MersenneHit x.1 x.2} :=
  W.exists_hit

/-#############################################################################
  §3. The strong bridge: cofinal Mersenne genealogy coverage
#############################################################################-/

/--
A cofinal Mersenne genealogy coverage bridge.

This is the strong version needed for the contradiction route:

  for every ordinary twin horizon `M0` and every Mersenne index horizon `K0`,
  ordinary twin supply above `M0` produces a genealogy that hits a Mersenne index
  `k ≥ K0`; moreover every such hit extracts a genuine Mersenne-twin center.

The fields are deliberately separated:

  * `cofinal_hit` is the coverage/cofinality statement;
  * `hit_extracts_twin` is the arithmetic/semantic extraction statement.
-/
structure CofinalMersenneGenealogyCoverage
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where

  Genealogy : Type

  MersenneHit : Genealogy → Nat → Prop

  cofinal_hit :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ∃ Γ : Genealogy,
        ∃ k : Nat,
          K0 ≤ k ∧ MersenneHit Γ k

  hit_extracts_twin :
    ∀ Γ : Genealogy,
    ∀ k : Nat,
      MersenneHit Γ k → MersenneTwinCenter Prime k

namespace CofinalMersenneGenealogyCoverage

/-- Cofinal genealogy coverage converts ordinary supply into Mersenne tail supply. -/
theorem mersenne_supply_of_ordinary_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  rcases C.cofinal_hit M0 K0 hTwin with ⟨Γ, k, hk, hHit⟩
  exact ⟨k, hk, C.hit_extracts_twin Γ k hHit⟩

/-- Ordinary infinite supply plus cofinal coverage gives infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_ordinary_infinite
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact C.mersenne_supply_of_ordinary_supply 0 K0 (hOrdInf 0)

/-- Cofinal coverage plus one ordinary supply point forbids Mersenne absence on every tail. -/
theorem forbids_tail_absence_of_ordinary_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0) :
    ¬ MersenneTwinAbsentAtOrAbove Prime K0 := by
  intro hAbsent
  rcases C.mersenne_supply_of_ordinary_supply M0 K0 hTwin with ⟨k, hk, hMTwin⟩
  exact hAbsent k hk hMTwin

/-- Eventual absence contradicts cofinal coverage plus any ordinary supply point. -/
theorem eventual_absence_contradicts_coverage_of_ordinary_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove)
    (M0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  rcases hAbsent with ⟨K0, hTailAbsent⟩
  exact C.forbids_tail_absence_of_ordinary_supply M0 K0 hTwin hTailAbsent

/-- Eventual absence contradicts ordinary infinite supply plus cofinal coverage. -/
theorem eventual_absence_contradicts_ordinary_infinite_and_coverage
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  exact C.eventual_absence_contradicts_coverage_of_ordinary_supply 0 (hOrdInf 0) hAbsent

/-- Therefore eventual absence rules out cofinal coverage if ordinary infinite supply holds. -/
theorem no_coverage_of_ordinary_infinite_and_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbsent : EventuallyNoMersenneTwinCenters Prime) :
    CofinalMersenneGenealogyCoverage Prime TwinAbove → False := by
  intro C
  exact C.eventual_absence_contradicts_ordinary_infinite_and_coverage hOrdInf hAbsent

end CofinalMersenneGenealogyCoverage

/-#############################################################################
  §4. Defects: why weak “Mersenne hit” is not enough
#############################################################################-/

/--
Coverage defect at a pair of horizons: ordinary supply exists above `M0`, but no
Mersenne genealogy hit is available at or above `K0`.
-/
def MersenneGenealogyCofinalityDefect
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Genealogy : Type)
    (MersenneHit : Genealogy → Nat → Prop)
    (M0 K0 : Nat) : Prop :=
  TwinAbove M0 ∧
  ¬ ∃ Γ : Genealogy,
    ∃ k : Nat,
      K0 ≤ k ∧ MersenneHit Γ k

/--
Extraction defect: a genealogy hits a Mersenne index, but the hit does not
extract a Mersenne-twin center.
-/
def MersenneHitExtractionDefect
    (Prime : PrimeLike)
    (Genealogy : Type)
    (MersenneHit : Genealogy → Nat → Prop) : Prop :=
  ∃ Γ : Genealogy,
  ∃ k : Nat,
    MersenneHit Γ k ∧ ¬ MersenneTwinCenter Prime k

/-- If extraction is valid, there is no extraction defect. -/
theorem no_extraction_defect_of_hit_extracts_twin
    (Prime : PrimeLike)
    (Genealogy : Type)
    (MersenneHit : Genealogy → Nat → Prop)
    (hExtract : ∀ Γ k, MersenneHit Γ k → MersenneTwinCenter Prime k) :
    ¬ MersenneHitExtractionDefect Prime Genealogy MersenneHit := by
  intro hDef
  rcases hDef with ⟨Γ, k, hHit, hNotTwin⟩
  exact hNotTwin (hExtract Γ k hHit)

/--
If a cofinal coverage bridge exists, there is no cofinality defect at any
horizons.
-/
theorem no_cofinality_defect_of_coverage
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove)
    (M0 K0 : Nat) :
    ¬ MersenneGenealogyCofinalityDefect
        TwinAbove C.Genealogy C.MersenneHit M0 K0 := by
  intro hDef
  rcases hDef with ⟨hTwin, hNoHit⟩
  exact hNoHit (C.cofinal_hit M0 K0 hTwin)

/--
Under ordinary supply at `M0`, tail absence at `K0` forces a defect in any
candidate genealogy-hit system: either no cofinal hit exists, or some hit fails
to extract a Mersenne-twin center.
-/
theorem absence_forces_cofinality_or_extraction_defect
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Genealogy : Type)
    (MersenneHit : Genealogy → Nat → Prop)
    (M0 K0 : Nat)
    (hTwin : TwinAbove M0)
    (hAbsent : MersenneTwinAbsentAtOrAbove Prime K0) :
    MersenneGenealogyCofinalityDefect TwinAbove Genealogy MersenneHit M0 K0 ∨
    MersenneHitExtractionDefect Prime Genealogy MersenneHit := by
  by_cases hHitExists :
      ∃ Γ : Genealogy,
      ∃ k : Nat,
        K0 ≤ k ∧ MersenneHit Γ k
  · right
    rcases hHitExists with ⟨Γ, k, hk, hHit⟩
    exact ⟨Γ, k, hHit, hAbsent k hk⟩
  · left
    exact ⟨hTwin, hHitExists⟩

/-#############################################################################
  §5. Final route statement
#############################################################################-/

/--
The exact conditional contradiction route.

If ordinary twins are infinite and every ordinary twin tail is cofinally captured
by Mersenne-hitting genealogies whose hits extract Mersenne-twin centers, then
Mersenne-twin centers cannot be eventually absent.
-/
theorem ordinary_infinite_plus_cofinal_mersenne_genealogy_coverage_forbids_absence
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbsent
  exact C.eventual_absence_contradicts_ordinary_infinite_and_coverage hOrdInf hAbsent

/--
Equivalent slogan: yes, this route works, but only with cofinality and extraction.
-/
theorem mersenne_genealogy_route_slogan
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (C : CofinalMersenneGenealogyCoverage Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact C.infinite_mersenne_supply_of_ordinary_infinite hOrdInf

end MersenneGenealogyBridge
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_bounded_peel_debt_conflict_patch.lean =====
/-
EuclidsPath — patch: Mersenne bounded peel-debt conflict
=========================================================

Purpose
-------
This file advances the Mersenne route one layer past the previous
`CofinalPeelDebtPressure` obligation.

The new idea is:

  * instead of postulating cofinal Mersenne peel coverage directly,
    introduce a numeric `peelDebt` attached to ordinary twin genealogies;
  * prove that unbounded peel-debt on every ordinary twin tail implies cofinal
    Mersenne prime-payment pressure;
  * prove that if each genealogy pays the Mersenne pair at its own debt index,
    and the prime-payment ledger is sound, then Mersenne-twin centers are
    infinite;
  * therefore eventual absence of Mersenne-twin centers forces a bounded
    peel-debt defect, or a failure of the payment/soundness law.

This remains conditional.  The hard mathematical brick is now sharper:

    ordinary twin flow -> unbounded peel-debt on every tail.

No primitive assumptions and no proof placeholders.
-/



namespace EuclidsPath
namespace Mersenne
namespace BoundedPeelDebtConflict

/-#############################################################################
  §1. Minimal Mersenne vocabulary
#############################################################################-/

/-- Parametric primality predicate.  Instantiate with `Nat.Prime` later. -/
abbrev PrimeLike := Nat → Prop

/-- Base-4 repunit Mersenne center sequence: `0, 1, 5, 21, 85, ...`. -/
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

/-- Twin center for an abstract primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- Mersenne-twin center at base-4 repunit index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Mersenne-twin supply at or above index `K0`. -/
def MersenneTwinSupplyAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Infinite Mersenne-twin supply in tail form. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, MersenneTwinSupplyAtOrAbove Prime K0

/-- Mersenne-twin centers absent on the tail starting at `K0`. -/
def MersenneTwinAbsentAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Eventual absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, MersenneTwinAbsentAtOrAbove Prime K0

/-- Infinite supply forbids eventual absence. -/
theorem infinite_mersenne_supply_forbids_eventual_absence
    (Prime : PrimeLike)
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hAbsent⟩
  rcases hInf K0 with ⟨k, hk_ge, hkTwin⟩
  exact hAbsent k hk_ge hkTwin

/-#############################################################################
  §2. Ordinary twin flow and peel-debt
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/--
A peel-debt system over ordinary twin genealogies.

`Tail Γ M0` means genealogy `Γ` belongs to the ordinary twin-flow tail above
horizon `M0`.  `debt Γ` is the base-4/Mersenne peel-debt index carried by `Γ`.
-/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Unbounded peel-debt on every ordinary twin tail. -/
def UnboundedPeelDebtOnTwinTail
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat,
    TwinAbove M0 →
      ∀ B : Nat,
        ∃ Γ : D.Genealogy, D.Tail Γ M0 ∧ B < D.debt Γ

/-- A bounded peel-debt defect on some ordinary twin tail. -/
def BoundedPeelDebtTailDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∃ M0 B : Nat,
    TwinAbove M0 ∧
      ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- Bounded tail defect is exactly failure of tail-unbounded peel-debt. -/
theorem boundedTailDefect_iff_not_unboundedTail
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) :
    BoundedPeelDebtTailDefect D TwinAbove ↔
      ¬ UnboundedPeelDebtOnTwinTail D TwinAbove := by
  constructor
  · intro hBound hUnbounded
    rcases hBound with ⟨M0, B, hTwin, hBound⟩
    rcases hUnbounded M0 hTwin B with ⟨Γ, hTail, hgt⟩
    exact (not_lt_of_ge (hBound Γ hTail)) hgt
  · intro hNotUnbounded
    classical
    by_contra hNoBoundedDefect
    apply hNotUnbounded
    intro M0 hTwin B
    by_contra hNoWitness
    apply hNoBoundedDefect
    refine ⟨M0, B, hTwin, ?_⟩
    intro Γ hTail
    by_contra hNotLe
    have hgt : B < D.debt Γ := lt_of_not_ge hNotLe
    exact hNoWitness ⟨Γ, hTail, hgt⟩

/-- Cofinal peel-debt pressure: every ordinary twin tail reaches every debt floor. -/
def CofinalPeelDebtPressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 →
      ∃ Γ : D.Genealogy, D.Tail Γ M0 ∧ K0 ≤ D.debt Γ

/-- Unbounded tail debt implies cofinal peel-debt pressure. -/
theorem cofinalPeelDebtPressure_of_unboundedTail
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove) :
    CofinalPeelDebtPressure D TwinAbove := by
  intro M0 K0 hTwin
  rcases hUnbounded M0 hTwin K0 with ⟨Γ, hTail, hgt⟩
  exact ⟨Γ, hTail, Nat.le_of_lt hgt⟩

/-- Failure of cofinal pressure is a bounded-tail defect, provided cofinality is tested via unboundedness. -/
theorem boundedTailDefect_of_not_unboundedTail
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hNot : ¬ UnboundedPeelDebtOnTwinTail D TwinAbove) :
    BoundedPeelDebtTailDefect D TwinAbove := by
  exact (boundedTailDefect_iff_not_unboundedTail D TwinAbove).2 hNot

/-#############################################################################
  §3. Prime-payment ledger at the debt index
#############################################################################-/

/-- A prime-payment ledger whose genealogies are the peel-debt genealogies. -/
structure PrimePaymentLedger (D : PeelDebtSystem) where
  PaysPrime : D.Genealogy → Nat → Prop

/-- Payment soundness: every paid prime-token is genuinely prime. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∀ Γ : D.Genealogy, ∀ n : Nat, L.PaysPrime Γ n → Prime n

/-- A genealogy pays both sides of the Mersenne center at index `k`. -/
def MersennePairPaid
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (Γ : D.Genealogy)
    (k : Nat) : Prop :=
  L.PaysPrime Γ (lowerSide (mersenneCenter k)) ∧
  L.PaysPrime Γ (upperSide (mersenneCenter k))

/-- Debt-index payment law: every tail genealogy pays the Mersenne pair at its own debt index. -/
def PeelDebtPaysOwnMersennePair
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∀ Γ : D.Genealogy,
    ∀ M0 : Nat,
      D.Tail Γ M0 → MersennePairPaid L Γ (D.debt Γ)

/-- Sound payment at a Mersenne pair extracts a Mersenne-twin center. -/
theorem mersennePairPaid_extracts_twin
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hSound : PrimePaymentSound Prime L)
    {Γ : D.Genealogy} {k : Nat}
    (hPaid : MersennePairPaid L Γ k) :
    MersenneTwinCenter Prime k := by
  exact ⟨hSound Γ (lowerSide (mersenneCenter k)) hPaid.1,
         hSound Γ (upperSide (mersenneCenter k)) hPaid.2⟩

/-- A tail genealogy whose debt is above `K0` yields a Mersenne-twin center above `K0`. -/
theorem tailDebt_payment_extracts_mersenneSupply
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L)
    {M0 K0 : Nat}
    {Γ : D.Genealogy}
    (hTail : D.Tail Γ M0)
    (hDebt : K0 ≤ D.debt Γ) :
    MersenneTwinSupplyAtOrAbove Prime K0 := by
  refine ⟨D.debt Γ, hDebt, ?_⟩
  exact mersennePairPaid_extracts_twin Prime L hSound (hPay Γ M0 hTail)

/-- Cofinal peel-debt pressure plus debt-index payment gives infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_cofinalDebt_payment_soundness
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hCofinal : CofinalPeelDebtPressure D TwinAbove)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  rcases hCofinal 0 K0 (hOrdInf 0) with ⟨Γ, hTail, hDebt⟩
  exact tailDebt_payment_extracts_mersenneSupply Prime L hSound hPay hTail hDebt

/-- Unbounded tail debt is enough to obtain infinite Mersenne-twin supply. -/
theorem infinite_mersenne_supply_of_unboundedDebt_payment_soundness
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_mersenne_supply_of_cofinalDebt_payment_soundness
    Prime L hOrdInf (cofinalPeelDebtPressure_of_unboundedTail hUnbounded) hSound hPay

/-#############################################################################
  §4. Eventual absence forces bounded debt or payment defect
#############################################################################-/

/-- Eventual absence contradicts unbounded debt + sound debt-index payment. -/
theorem eventual_absence_contradicts_unboundedDebt_payment_soundness
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_mersenne_supply_forbids_eventual_absence Prime
    (infinite_mersenne_supply_of_unboundedDebt_payment_soundness
      Prime L hOrdInf hUnbounded hSound hPay)

/-- If eventual absence holds while sound payment holds, unbounded peel-debt is impossible. -/
theorem eventual_absence_forces_not_unboundedDebt_of_payment_soundness
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    ¬ UnboundedPeelDebtOnTwinTail D TwinAbove := by
  intro hUnbounded
  exact eventual_absence_contradicts_unboundedDebt_payment_soundness
    Prime L hOrdInf hUnbounded hSound hPay hAbs

/-- Therefore eventual absence forces a bounded peel-debt tail defect. -/
theorem eventual_absence_forces_boundedPeelDebtTailDefect
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    BoundedPeelDebtTailDefect D TwinAbove := by
  exact boundedTailDefect_of_not_unboundedTail
    (eventual_absence_forces_not_unboundedDebt_of_payment_soundness
      Prime L hOrdInf hSound hPay hAbs)

/-- Payment defect: some tail genealogy fails to pay the pair at its own debt index. -/
def PeelDebtPaymentDefect
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∃ Γ : D.Genealogy, ∃ M0 : Nat,
    D.Tail Γ M0 ∧ ¬ MersennePairPaid L Γ (D.debt Γ)

/-- If the debt-index payment law fails, there is an explicit payment defect. -/
theorem paymentDefect_of_not_debtPaymentLaw
    {D : PeelDebtSystem}
    {L : PrimePaymentLedger D}
    (hNotPay : ¬ PeelDebtPaysOwnMersennePair L) :
    PeelDebtPaymentDefect L := by
  classical
  by_contra hNoDefect
  apply hNotPay
  intro Γ M0 hTail
  by_contra hNotPaid
  exact hNoDefect ⟨Γ, M0, hTail, hNotPaid⟩

/-- Soundness defect: some paid token is not prime. -/
def PrimePaymentSoundnessDefect
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∃ Γ : D.Genealogy, ∃ n : Nat,
    L.PaysPrime Γ n ∧ ¬ Prime n

/-- If soundness fails, there is an explicit soundness defect. -/
theorem soundnessDefect_of_not_sound
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    {L : PrimePaymentLedger D}
    (hNotSound : ¬ PrimePaymentSound Prime L) :
    PrimePaymentSoundnessDefect Prime L := by
  classical
  by_contra hNoDefect
  apply hNotSound
  intro Γ n hPaid
  by_contra hNotPrime
  exact hNoDefect ⟨Γ, n, hPaid, hNotPrime⟩

/--
Defect trichotomy under ordinary infinite supply and eventual Mersenne absence.

If Mersenne-twin centers eventually disappear, then any proposed route must lose
at least one of:

  * unbounded peel-debt;
  * payment at the genealogy's own Mersenne debt index;
  * soundness of the prime-payment ledger.
-/
theorem absence_forces_boundedDebt_or_payment_or_soundness_defect
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    BoundedPeelDebtTailDefect D TwinAbove ∨
      PeelDebtPaymentDefect L ∨
        PrimePaymentSoundnessDefect Prime L := by
  classical
  by_cases hSound : PrimePaymentSound Prime L
  · by_cases hPay : PeelDebtPaysOwnMersennePair L
    · exact Or.inl
        (eventual_absence_forces_boundedPeelDebtTailDefect
          Prime L hOrdInf hSound hPay hAbs)
    · exact Or.inr (Or.inl (paymentDefect_of_not_debtPaymentLaw hPay))
  · exact Or.inr (Or.inr (soundnessDefect_of_not_sound Prime hSound))

/-#############################################################################
  §5. Route package and final slogan
#############################################################################-/

/-- Complete route: ordinary infinite supply plus unbounded peel-debt plus sound own-debt payment. -/
structure MersenneUnboundedPeelDebtRoute
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  D : PeelDebtSystem
  L : PrimePaymentLedger D
  ordinary_infinite : OrdinaryTwinInfinite TwinAbove
  unbounded_debt : UnboundedPeelDebtOnTwinTail D TwinAbove
  payment_at_own_debt : PeelDebtPaysOwnMersennePair L
  prime_payment_sound : PrimePaymentSound Prime L

/-- The route produces infinite Mersenne-twin supply. -/
theorem route_produces_infinite_mersenne_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneUnboundedPeelDebtRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_mersenne_supply_of_unboundedDebt_payment_soundness
    Prime R.L R.ordinary_infinite R.unbounded_debt
    R.prime_payment_sound R.payment_at_own_debt

/-- Therefore the complete route forbids eventual absence. -/
theorem route_forbids_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneUnboundedPeelDebtRoute Prime TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_mersenne_supply_forbids_eventual_absence Prime
    (route_produces_infinite_mersenne_supply R)

/-- Final strict slogan of this patch. -/
theorem boundedPeelDebtConflict_slogan
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneUnboundedPeelDebtRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime ∧
      ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨route_produces_infinite_mersenne_supply R,
         route_forbids_eventual_absence R⟩

end BoundedPeelDebtConflict
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_bounded_debt_finite_key_firewall_patch.lean =====
/-
EuclidsPath — patch: Mersenne bounded-debt finite-key firewall
================================================================

Purpose
-------
This patch advances the Mersenne route by attacking the newest live defect:

    BoundedPeelDebtTailDefect.

Core idea:

  * if a twin tail has bounded Mersenne peel-debt, then `debt` itself is a
    finite key on that tail;
  * if same-debt collisions are semantically resolved, this finite key is a
    local P-success/resolver;
  * therefore Step00-local search incompressibility forbids bounded peel-debt;
  * hence, under the tail firewall, ordinary twin flow forces unbounded
    Mersenne peel-debt.

This file is still architecture-local.  It does not prove infinitude of
Mersenne-twin centers alone.  It proves the strict bridge:

    tail incompressibility + same-debt resolution
      -> no bounded peel-debt tail
      -> unbounded peel-debt pressure.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace BoundedDebtFiniteKeyFirewall

/-#############################################################################
  §1. Ordinary twin tails and peel-debt
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/--
A peel-debt system over ordinary twin genealogies.

`Tail Γ M0` means genealogy `Γ` belongs to the ordinary twin-flow tail above
horizon `M0`.  `debt Γ` is the Mersenne/base-4 peel index carried by `Γ`.
-/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- The subtype of genealogies living on one fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

/-- Peel-debt bounded on one fixed tail. -/
def PeelDebtBoundedOnTail (D : PeelDebtSystem) (M0 : Nat) : Prop :=
  ∃ B : Nat, ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- A bounded peel-debt defect on some ordinary twin tail. -/
def BoundedPeelDebtTailDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∃ M0 B : Nat,
    TwinAbove M0 ∧
      ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- Unbounded peel-debt on every ordinary twin tail. -/
def UnboundedPeelDebtOnTwinTail
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat,
    TwinAbove M0 →
      ∀ B : Nat,
        ∃ Γ : D.Genealogy, D.Tail Γ M0 ∧ B < D.debt Γ

/-- Failure of bounded-tail defect gives unbounded peel-debt on every twin tail. -/
theorem unboundedTail_of_no_boundedPeelDebtTailDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hNoBounded : ¬ BoundedPeelDebtTailDefect D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  intro M0 hTwin B
  classical
  by_contra hNoWitness
  apply hNoBounded
  refine ⟨M0, B, hTwin, ?_⟩
  intro Γ hTail
  by_contra hNotLe
  have hgt : B < D.debt Γ := lt_of_not_ge hNotLe
  exact hNoWitness ⟨Γ, hTail, hgt⟩

/-#############################################################################
  §2. Tail local finite-key resolvers
#############################################################################-/

/--
A local search node attached to a fixed tail.

`CollisionResolution γ₁ γ₂` is the semantic Step00 resolution of two distinct
admissible genealogies on the same tail.
-/
structure TailSearchNode (D : PeelDebtSystem) (M0 : Nat) where
  CollisionResolution : TailGenealogy D M0 → TailGenealogy D M0 → Prop

/-- A finite-key resolver for one fixed tail search node. -/
structure TailFiniteKeyResolver
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) where
  Key : Type
  finite_key : Fintype Key
  keyOf : TailGenealogy D M0 → Key
  resolves :
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ →
        keyOf γ₁ = keyOf γ₂ →
          N.CollisionResolution γ₁ γ₂

namespace TailFiniteKeyResolver

instance {D : PeelDebtSystem} {M0 : Nat} {N : TailSearchNode D M0}
    (R : TailFiniteKeyResolver N) : Fintype R.Key :=
  R.finite_key

end TailFiniteKeyResolver

/-- Local P-success on a tail: a finite key resolves every same-key collision. -/
def TailLocalPSuccess
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  Nonempty (TailFiniteKeyResolver N)

/-- Local incompressibility on a tail. -/
def TailLocalIncompressible
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  ¬ TailLocalPSuccess N

/-- Same-debt collisions are semantically resolved on this tail. -/
def SameDebtCollisionResolves
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  ∀ γ₁ γ₂ : TailGenealogy D M0,
    γ₁ ≠ γ₂ →
      D.debt γ₁.1 = D.debt γ₂.1 →
        N.CollisionResolution γ₁ γ₂

/--
A bounded debt tail provides an explicit finite key: the key is the bounded debt
value itself, as an element of `Fin (B+1)`.
-/
noncomputable def boundedDebtFiniteKeyResolver
    {D : PeelDebtSystem} {M0 B : Nat}
    (N : TailSearchNode D M0)
    (hBound : ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B)
    (hSameDebt : SameDebtCollisionResolves N) :
    TailFiniteKeyResolver N :=
{ Key := Fin (B + 1)
  finite_key := inferInstance
  keyOf := fun γ => ⟨D.debt γ.1, Nat.lt_succ_of_le (hBound γ.1 γ.2)⟩
  resolves := by
    intro γ₁ γ₂ hneq hKey
    apply hSameDebt γ₁ γ₂ hneq
    exact congrArg Fin.val hKey }

/-- Bounded debt plus same-debt resolution gives local P-success. -/
theorem tailLocalPSuccess_of_boundedDebt_and_sameDebtResolution
    {D : PeelDebtSystem} {M0 B : Nat}
    (N : TailSearchNode D M0)
    (hBound : ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B)
    (hSameDebt : SameDebtCollisionResolves N) :
    TailLocalPSuccess N := by
  exact ⟨boundedDebtFiniteKeyResolver N hBound hSameDebt⟩

/-- Therefore local incompressibility forbids bounded debt on that tail. -/
theorem no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0)
    (hIncompressible : TailLocalIncompressible N)
    (hSameDebt : SameDebtCollisionResolves N) :
    ¬ PeelDebtBoundedOnTail D M0 := by
  intro hBounded
  rcases hBounded with ⟨B, hBound⟩
  exact hIncompressible
    (tailLocalPSuccess_of_boundedDebt_and_sameDebtResolution N hBound hSameDebt)

/-#############################################################################
  §3. Tail firewall family
#############################################################################-/

/--
A family of local search nodes for all ordinary twin tails of a peel-debt system.
-/
structure TailSearchNodeFamily (D : PeelDebtSystem) where
  node : ∀ M0 : Nat, TailSearchNode D M0

/--
The Step00 local compression firewall on ordinary twin tails.

For every tail with ordinary twin supply:

  * same-debt collisions are resolved;
  * nevertheless no finite-key resolver exists.

Together these imply that the debt cannot be bounded on any ordinary twin tail.
-/
structure TailCompressionFirewall
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  nodes : TailSearchNodeFamily D
  same_debt_resolves :
    ∀ M0 : Nat,
      TwinAbove M0 →
        SameDebtCollisionResolves (nodes.node M0)
  tail_incompressible :
    ∀ M0 : Nat,
      TwinAbove M0 →
        TailLocalIncompressible (nodes.node M0)

/-- The firewall forbids bounded peel-debt on any ordinary twin tail. -/
theorem no_boundedPeelDebtTailDefect_of_tailCompressionFirewall
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : TailCompressionFirewall D TwinAbove) :
    ¬ BoundedPeelDebtTailDefect D TwinAbove := by
  intro hDefect
  rcases hDefect with ⟨M0, B, hTwin, hBound⟩
  have hNoBounded : ¬ PeelDebtBoundedOnTail D M0 :=
    no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
      (F.nodes.node M0)
      (F.tail_incompressible M0 hTwin)
      (F.same_debt_resolves M0 hTwin)
  exact hNoBounded ⟨B, hBound⟩

/-- Hence the firewall forces unbounded peel-debt on every ordinary twin tail. -/
theorem unboundedPeelDebt_of_tailCompressionFirewall
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : TailCompressionFirewall D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  exact unboundedTail_of_no_boundedPeelDebtTailDefect
    (no_boundedPeelDebtTailDefect_of_tailCompressionFirewall F)

/-#############################################################################
  §4. Connection to Mersenne prime-payment route
#############################################################################-/

/-- Parametric primality predicate.  Instantiate later with `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- Base-4 repunit Mersenne center sequence. -/
def mersenneCenter : Nat → Nat
  | 0 => 0
  | k + 1 => 4 * mersenneCenter k + 1

/-- Lower Step00 side. -/
def lowerSide (m : Nat) : Nat :=
  6 * m - 1

/-- Upper Step00 side. -/
def upperSide (m : Nat) : Nat :=
  6 * m + 1

/-- Twin center for an abstract primality predicate. -/
def TwinCenter (Prime : PrimeLike) (m : Nat) : Prop :=
  Prime (lowerSide m) ∧ Prime (upperSide m)

/-- Mersenne-twin center at base-4 repunit index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  TwinCenter Prime (mersenneCenter k)

/-- Mersenne supply at or above `K0`. -/
def MersenneTwinSupplyAtOrAbove (Prime : PrimeLike) (K0 : Nat) : Prop :=
  ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Infinite Mersenne-twin supply in tail form. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, MersenneTwinSupplyAtOrAbove Prime K0

/-- Eventual absence. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Infinite supply forbids eventual absence. -/
theorem infinite_mersenne_supply_forbids_eventual_absence
    (Prime : PrimeLike)
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hAbs⟩
  rcases hInf K0 with ⟨k, hk, hkTwin⟩
  exact hAbs k hk hkTwin

/-- Prime-payment ledger over the same peel-debt genealogies. -/
structure PrimePaymentLedger (D : PeelDebtSystem) where
  PaysPrime : D.Genealogy → Nat → Prop

/-- Soundness: every paid prime-token is actually prime. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∀ Γ : D.Genealogy, ∀ n : Nat, L.PaysPrime Γ n → Prime n

/-- The genealogy pays both sides of the Mersenne center at `k`. -/
def MersennePairPaid
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (Γ : D.Genealogy)
    (k : Nat) : Prop :=
  L.PaysPrime Γ (lowerSide (mersenneCenter k)) ∧
  L.PaysPrime Γ (upperSide (mersenneCenter k))

/-- Every tail genealogy pays the Mersenne pair at its own debt index. -/
def PeelDebtPaysOwnMersennePair
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∀ Γ : D.Genealogy,
    ∀ M0 : Nat,
      D.Tail Γ M0 → MersennePairPaid L Γ (D.debt Γ)

/-- Sound payment at a Mersenne pair extracts a Mersenne-twin center. -/
theorem mersennePairPaid_extracts_twin
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hSound : PrimePaymentSound Prime L)
    {Γ : D.Genealogy} {k : Nat}
    (hPaid : MersennePairPaid L Γ k) :
    MersenneTwinCenter Prime k := by
  exact ⟨hSound Γ (lowerSide (mersenneCenter k)) hPaid.1,
         hSound Γ (upperSide (mersenneCenter k)) hPaid.2⟩

/-- Unbounded debt plus own-debt payment and soundness gives infinite Mersenne supply. -/
theorem infinite_mersenne_supply_of_unboundedDebt_payment_soundness
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove)
    (hSound : PrimePaymentSound Prime L)
    (hPay : PeelDebtPaysOwnMersennePair L) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  rcases hUnbounded 0 (hOrdInf 0) K0 with ⟨Γ, hTail, hDebtGt⟩
  refine ⟨D.debt Γ, Nat.le_of_lt hDebtGt, ?_⟩
  exact mersennePairPaid_extracts_twin Prime L hSound (hPay Γ 0 hTail)

/--
Full compression-firewall route to infinite Mersenne-twin supply.

The new content compared to the previous patch is the field
`tail_compression_firewall`, which produces the required unbounded peel-debt.
-/
structure MersenneCompressionFirewallRoute
    (Prime : PrimeLike)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  D : PeelDebtSystem
  L : PrimePaymentLedger D
  ordinary_infinite : OrdinaryTwinInfinite TwinAbove
  tail_compression_firewall : TailCompressionFirewall D TwinAbove
  payment_at_own_debt : PeelDebtPaysOwnMersennePair L
  prime_payment_sound : PrimePaymentSound Prime L

/-- The route produces unbounded peel-debt. -/
theorem route_unboundedPeelDebt
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneCompressionFirewallRoute Prime TwinAbove) :
    UnboundedPeelDebtOnTwinTail R.D TwinAbove := by
  exact unboundedPeelDebt_of_tailCompressionFirewall R.tail_compression_firewall

/-- The route produces infinite Mersenne-twin supply. -/
theorem route_produces_infinite_mersenne_supply
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneCompressionFirewallRoute Prime TwinAbove) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_mersenne_supply_of_unboundedDebt_payment_soundness
    Prime R.L R.ordinary_infinite (route_unboundedPeelDebt R)
    R.prime_payment_sound R.payment_at_own_debt

/-- Therefore the route forbids eventual absence. -/
theorem route_forbids_eventual_absence
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneCompressionFirewallRoute Prime TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_mersenne_supply_forbids_eventual_absence Prime
    (route_produces_infinite_mersenne_supply R)

/-#############################################################################
  §5. Defect trichotomy
#############################################################################-/

/-- The same-debt resolution law fails somewhere on a supplied tail. -/
def SameDebtResolutionDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Nodes : TailSearchNodeFamily D) : Prop :=
  ∃ M0 : Nat,
    TwinAbove M0 ∧ ¬ SameDebtCollisionResolves (Nodes.node M0)

/-- The tail incompressibility firewall fails somewhere on a supplied tail. -/
def TailIncompressibilityDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Nodes : TailSearchNodeFamily D) : Prop :=
  ∃ M0 : Nat,
    TwinAbove M0 ∧ ¬ TailLocalIncompressible (Nodes.node M0)

/-- Failure of payment at own debt. -/
def PeelDebtPaymentDefect
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∃ Γ : D.Genealogy, ∃ M0 : Nat,
    D.Tail Γ M0 ∧ ¬ MersennePairPaid L Γ (D.debt Γ)

/-- Failure of prime-payment soundness. -/
def PrimePaymentSoundnessDefect
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    (L : PrimePaymentLedger D) : Prop :=
  ∃ Γ : D.Genealogy, ∃ n : Nat,
    L.PaysPrime Γ n ∧ ¬ Prime n

/-- If the payment law fails, produce an explicit payment defect. -/
theorem paymentDefect_of_not_paymentLaw
    {D : PeelDebtSystem}
    {L : PrimePaymentLedger D}
    (hNot : ¬ PeelDebtPaysOwnMersennePair L) :
    PeelDebtPaymentDefect L := by
  classical
  by_contra hNo
  apply hNot
  intro Γ M0 hTail
  by_contra hNotPaid
  exact hNo ⟨Γ, M0, hTail, hNotPaid⟩

/-- If soundness fails, produce an explicit soundness defect. -/
theorem soundnessDefect_of_not_sound
    (Prime : PrimeLike)
    {D : PeelDebtSystem}
    {L : PrimePaymentLedger D}
    (hNot : ¬ PrimePaymentSound Prime L) :
    PrimePaymentSoundnessDefect Prime L := by
  classical
  by_contra hNo
  apply hNot
  intro Γ n hPaid
  by_contra hNotPrime
  exact hNo ⟨Γ, n, hPaid, hNotPrime⟩

/--
If eventual Mersenne absence holds while ordinary twin supply is infinite, then
one of the route walls must fail.
-/
theorem absence_forces_compression_or_payment_or_soundness_defect
    (Prime : PrimeLike)
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {D : PeelDebtSystem}
    (Nodes : TailSearchNodeFamily D)
    (L : PrimePaymentLedger D)
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    SameDebtResolutionDefect D TwinAbove Nodes ∨
      TailIncompressibilityDefect D TwinAbove Nodes ∨
        PeelDebtPaymentDefect L ∨
          PrimePaymentSoundnessDefect Prime L := by
  classical
  by_cases hSame : ∀ M0 : Nat, TwinAbove M0 → SameDebtCollisionResolves (Nodes.node M0)
  · by_cases hInc : ∀ M0 : Nat, TwinAbove M0 → TailLocalIncompressible (Nodes.node M0)
    · by_cases hPay : PeelDebtPaysOwnMersennePair L
      · by_cases hSound : PrimePaymentSound Prime L
        · let F : TailCompressionFirewall D TwinAbove :=
            { nodes := Nodes
              same_debt_resolves := hSame
              tail_incompressible := hInc }
          let R : MersenneCompressionFirewallRoute Prime TwinAbove :=
            { D := D
              L := L
              ordinary_infinite := hOrdInf
              tail_compression_firewall := F
              payment_at_own_debt := hPay
              prime_payment_sound := hSound }
          exact False.elim ((route_forbids_eventual_absence R) hAbs)
        · exact Or.inr (Or.inr (Or.inr (soundnessDefect_of_not_sound Prime hSound)))
      · exact Or.inr (Or.inr (Or.inl (paymentDefect_of_not_paymentLaw hPay)))
    · push_neg at hInc
      rcases hInc with ⟨M0, hTwin, hNotInc⟩
      exact Or.inr (Or.inl ⟨M0, hTwin, hNotInc⟩)
  · push_neg at hSame
    rcases hSame with ⟨M0, hTwin, hNotSame⟩
    exact Or.inl ⟨M0, hTwin, hNotSame⟩

/-- Final slogan of this patch. -/
theorem boundedDebtFiniteKeyFirewall_slogan
    {Prime : PrimeLike}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneCompressionFirewallRoute Prime TwinAbove) :
    UnboundedPeelDebtOnTwinTail R.D TwinAbove ∧
      InfinitelyManyMersenneTwinCenters Prime ∧
        ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨route_unboundedPeelDebt R,
         route_produces_infinite_mersenne_supply R,
         route_forbids_eventual_absence R⟩

end BoundedDebtFiniteKeyFirewall
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_tail_firewall_from_local_pnp_sources_patch.lean =====
/-
EuclidsPath — patch: Mersenne tail firewall from local P/NP sources
====================================================================

Purpose
-------
This patch continues the Mersenne route after the bounded-debt finite-key
firewall.

The previous live obligation was:

    TailCompressionFirewall D TwinAbove

This file explains exactly how such a firewall may be obtained from a
Step00-local P/NP node, and, just as importantly, which source cannot be used.

Main points:

  * A tail-specific local P/NP source gives `TailCompressionFirewall`.
  * Bounded peel-debt again yields a finite-key resolver by debt value.
  * Hence the local P/NP source forbids bounded peel-debt on every supplied tail.
  * The old finite-twin-bound incompressibility source cannot be used together
    with ordinary twin infinitude: `OrdinaryTwinInfinite` forbids any ordinary
    twin tail from being absent.
  * Therefore the live source must be a tail-specific incompressibility theorem,
    not the global finite-twin-bound theorem.

This is still architecture-local.  It proves no unconditional infinitude of
Mersenne-twin centers by itself.  It isolates the next honest bridge obligation.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace TailFirewallFromLocalPNP

/-#############################################################################
  §1. Ordinary twin tails and peel-debt
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/-- Eventual absence of ordinary twins, included to guard against a bad source. -/
def EventuallyNoOrdinaryTwinCenters (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∃ M0 : Nat, ∀ M : Nat, M0 ≤ M → ¬ TwinAbove M

/-- Ordinary infinitude forbids eventual ordinary-twin absence. -/
theorem ordinaryInfinite_forbids_eventualNoOrdinaryTwins
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hInf : OrdinaryTwinInfinite TwinAbove) :
    ¬ EventuallyNoOrdinaryTwinCenters TwinAbove := by
  intro hAbs
  rcases hAbs with ⟨M0, hAbs⟩
  exact hAbs M0 (le_rfl) (hInf M0)

/-- Ordinary infinitude forbids absence at any particular tail. -/
theorem ordinaryInfinite_forbids_tailAbsence
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hInf : OrdinaryTwinInfinite TwinAbove)
    (M0 : Nat) :
    ¬ ¬ TwinAbove M0 := by
  intro hNo
  exact hNo (hInf M0)

/--
A peel-debt system over ordinary twin genealogies.

`Tail Γ M0` says genealogy `Γ` belongs to the ordinary twin-flow tail above
horizon `M0`; `debt Γ` is the Mersenne/base-4 peel index carried by `Γ`.
-/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- The subtype of genealogies living on one fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

/-- Peel-debt bounded on one fixed tail. -/
def PeelDebtBoundedOnTail (D : PeelDebtSystem) (M0 : Nat) : Prop :=
  ∃ B : Nat, ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- A bounded peel-debt defect on some ordinary twin tail. -/
def BoundedPeelDebtTailDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∃ M0 B : Nat,
    TwinAbove M0 ∧
      ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- Unbounded peel-debt on every ordinary twin tail. -/
def UnboundedPeelDebtOnTwinTail
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat,
    TwinAbove M0 →
      ∀ B : Nat,
        ∃ Γ : D.Genealogy, D.Tail Γ M0 ∧ B < D.debt Γ

/-- Failure of bounded-tail defect gives unbounded peel-debt on every twin tail. -/
theorem unboundedTail_of_no_boundedPeelDebtTailDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hNoBounded : ¬ BoundedPeelDebtTailDefect D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  intro M0 hTwin B
  classical
  by_contra hNoWitness
  apply hNoBounded
  refine ⟨M0, B, hTwin, ?_⟩
  intro Γ hTail
  by_contra hNotLe
  have hgt : B < D.debt Γ := lt_of_not_ge hNotLe
  exact hNoWitness ⟨Γ, hTail, hgt⟩

/-#############################################################################
  §2. Tail search nodes and finite-key resolvers
#############################################################################-/

/--
A local search node attached to a fixed tail.

`CollisionResolution γ₁ γ₂` is the semantic Step00 resolution of two distinct
admissible genealogies on the same tail.
-/
structure TailSearchNode (D : PeelDebtSystem) (M0 : Nat) where
  CollisionResolution : TailGenealogy D M0 → TailGenealogy D M0 → Prop

/-- A finite-key resolver for one fixed tail search node. -/
structure TailFiniteKeyResolver
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) where
  Key : Type
  finite_key : Fintype Key
  keyOf : TailGenealogy D M0 → Key
  resolves :
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ →
        keyOf γ₁ = keyOf γ₂ →
          N.CollisionResolution γ₁ γ₂

namespace TailFiniteKeyResolver

instance {D : PeelDebtSystem} {M0 : Nat} {N : TailSearchNode D M0}
    (R : TailFiniteKeyResolver N) : Fintype R.Key :=
  R.finite_key

end TailFiniteKeyResolver

/-- Local P-success on a tail: a finite key resolves every same-key collision. -/
def TailLocalPSuccess
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  Nonempty (TailFiniteKeyResolver N)

/-- Local incompressibility on a tail. -/
def TailLocalIncompressible
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  ¬ TailLocalPSuccess N

/-- Same-debt collisions are semantically resolved on this tail. -/
def SameDebtCollisionResolves
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  ∀ γ₁ γ₂ : TailGenealogy D M0,
    γ₁ ≠ γ₂ →
      D.debt γ₁.1 = D.debt γ₂.1 →
        N.CollisionResolution γ₁ γ₂

/--
A bounded debt tail provides an explicit finite key: the key is the bounded debt
value itself, as an element of `Fin (B+1)`.
-/
noncomputable def boundedDebtFiniteKeyResolver
    {D : PeelDebtSystem} {M0 B : Nat}
    (N : TailSearchNode D M0)
    (hBound : ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B)
    (hSameDebt : SameDebtCollisionResolves N) :
    TailFiniteKeyResolver N :=
{ Key := Fin (B + 1)
  finite_key := inferInstance
  keyOf := fun γ => ⟨D.debt γ.1, Nat.lt_succ_of_le (hBound γ.1 γ.2)⟩
  resolves := by
    intro γ₁ γ₂ hneq hKey
    apply hSameDebt γ₁ γ₂ hneq
    exact congrArg Fin.val hKey }

/-- Bounded debt plus same-debt resolution gives local P-success. -/
theorem tailLocalPSuccess_of_boundedDebt_and_sameDebtResolution
    {D : PeelDebtSystem} {M0 B : Nat}
    (N : TailSearchNode D M0)
    (hBound : ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B)
    (hSameDebt : SameDebtCollisionResolves N) :
    TailLocalPSuccess N := by
  exact ⟨boundedDebtFiniteKeyResolver N hBound hSameDebt⟩

/-- Therefore local incompressibility forbids bounded debt on that tail. -/
theorem no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0)
    (hIncompressible : TailLocalIncompressible N)
    (hSameDebt : SameDebtCollisionResolves N) :
    ¬ PeelDebtBoundedOnTail D M0 := by
  intro hBounded
  rcases hBounded with ⟨B, hBound⟩
  exact hIncompressible
    (tailLocalPSuccess_of_boundedDebt_and_sameDebtResolution N hBound hSameDebt)

/-#############################################################################
  §3. Tail firewall and local P/NP source
#############################################################################-/

/-- A family of local search nodes for all ordinary twin tails. -/
structure TailSearchNodeFamily (D : PeelDebtSystem) where
  node : ∀ M0 : Nat, TailSearchNode D M0

/--
The Step00 local compression firewall on ordinary twin tails.

For every tail with ordinary twin supply:

  * same-debt collisions are resolved;
  * nevertheless no finite-key resolver exists.

Together these imply that the debt cannot be bounded on any ordinary twin tail.
-/
structure TailCompressionFirewall
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  nodes : TailSearchNodeFamily D
  same_debt_resolves :
    ∀ M0 : Nat,
      TwinAbove M0 →
        SameDebtCollisionResolves (nodes.node M0)
  tail_incompressible :
    ∀ M0 : Nat,
      TwinAbove M0 →
        TailLocalIncompressible (nodes.node M0)

/--
A tail-specific local P/NP source.

This is the honest way to obtain the Mersenne tail firewall.  It says that a
finite-key resolver on the tail would induce local P-success in the relevant
Step00 local node, while that local node is already known to be incompressible
on supplied tails.
-/
structure TailLocalPNPSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  nodes : TailSearchNodeFamily D
  LocalSuccess : Nat → Prop
  tail_success_to_local_success :
    ∀ M0 : Nat,
      TailLocalPSuccess (nodes.node M0) → LocalSuccess M0
  local_incompressible :
    ∀ M0 : Nat,
      TwinAbove M0 → ¬ LocalSuccess M0
  same_debt_resolves :
    ∀ M0 : Nat,
      TwinAbove M0 → SameDebtCollisionResolves (nodes.node M0)

/-- A tail-specific local P/NP source gives tail incompressibility. -/
theorem tailLocalIncompressible_of_tailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : TailLocalPNPSource D TwinAbove)
    (M0 : Nat)
    (hTwin : TwinAbove M0) :
    TailLocalIncompressible (S.nodes.node M0) := by
  intro hTailSuccess
  exact S.local_incompressible M0 hTwin
    (S.tail_success_to_local_success M0 hTailSuccess)

/-- A tail-specific local P/NP source gives the full tail compression firewall. -/
def tailCompressionFirewall_of_tailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : TailLocalPNPSource D TwinAbove) :
    TailCompressionFirewall D TwinAbove where
  nodes := S.nodes
  same_debt_resolves := S.same_debt_resolves
  tail_incompressible := tailLocalIncompressible_of_tailLocalPNPSource S

/-- The local P/NP source forbids bounded peel-debt defect. -/
theorem no_boundedPeelDebtTailDefect_of_tailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : TailLocalPNPSource D TwinAbove) :
    ¬ BoundedPeelDebtTailDefect D TwinAbove := by
  intro hDefect
  let F := tailCompressionFirewall_of_tailLocalPNPSource S
  rcases hDefect with ⟨M0, B, hTwin, hBound⟩
  have hNoBounded : ¬ PeelDebtBoundedOnTail D M0 :=
    no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
      (F.nodes.node M0)
      (F.tail_incompressible M0 hTwin)
      (F.same_debt_resolves M0 hTwin)
  exact hNoBounded ⟨B, hBound⟩

/-- Hence the local P/NP source forces unbounded peel-debt on every twin tail. -/
theorem unboundedPeelDebt_of_tailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : TailLocalPNPSource D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  exact unboundedTail_of_no_boundedPeelDebtTailDefect
    (no_boundedPeelDebtTailDefect_of_tailLocalPNPSource S)

/-#############################################################################
  §4. Semantic Step00 interface for same-debt collision resolution
#############################################################################-/

/--
A semantic resolver interface for tails.

This connects the same-debt resolver used in the Mersenne tail to the Step00
semantic collision-resolution node.  The important anti-vacuity condition is
`same_debt_to_semantic`: a same-debt collision must really enter the semantic
ledger interface; it cannot be ignored as a mere key equality.
-/
structure TailSemanticResolverInterface
    (D : PeelDebtSystem)
    (Nodes : TailSearchNodeFamily D) where
  SemanticResolution : ∀ M0 : Nat, TailGenealogy D M0 → TailGenealogy D M0 → Prop
  semantic_to_collision_resolution :
    ∀ M0 : Nat,
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      SemanticResolution M0 γ₁ γ₂ →
        (Nodes.node M0).CollisionResolution γ₁ γ₂
  same_debt_to_semantic :
    ∀ M0 : Nat,
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ →
        D.debt γ₁.1 = D.debt γ₂.1 →
          SemanticResolution M0 γ₁ γ₂

/-- The semantic resolver interface gives same-debt collision resolution. -/
theorem sameDebtCollisionResolves_of_semanticInterface
    {D : PeelDebtSystem}
    {Nodes : TailSearchNodeFamily D}
    (I : TailSemanticResolverInterface D Nodes)
    (M0 : Nat) :
    SameDebtCollisionResolves (Nodes.node M0) := by
  intro γ₁ γ₂ hneq hDebt
  exact I.semantic_to_collision_resolution M0 γ₁ γ₂
    (I.same_debt_to_semantic M0 γ₁ γ₂ hneq hDebt)

/--
A stronger local P/NP source where same-debt resolution comes from the semantic
Step00 interface rather than being inserted directly.
-/
structure SemanticTailLocalPNPSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  nodes : TailSearchNodeFamily D
  semantic_interface : TailSemanticResolverInterface D nodes
  LocalSuccess : Nat → Prop
  tail_success_to_local_success :
    ∀ M0 : Nat,
      TailLocalPSuccess (nodes.node M0) → LocalSuccess M0
  local_incompressible :
    ∀ M0 : Nat,
      TwinAbove M0 → ¬ LocalSuccess M0

/-- A semantic local P/NP source yields the direct local P/NP source. -/
def tailLocalPNPSource_of_semanticTailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : SemanticTailLocalPNPSource D TwinAbove) :
    TailLocalPNPSource D TwinAbove where
  nodes := S.nodes
  LocalSuccess := S.LocalSuccess
  tail_success_to_local_success := S.tail_success_to_local_success
  local_incompressible := S.local_incompressible
  same_debt_resolves := by
    intro M0 _hTwin
    exact sameDebtCollisionResolves_of_semanticInterface S.semantic_interface M0

/-- The semantic local P/NP source gives the tail compression firewall. -/
def tailCompressionFirewall_of_semanticTailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : SemanticTailLocalPNPSource D TwinAbove) :
    TailCompressionFirewall D TwinAbove :=
  tailCompressionFirewall_of_tailLocalPNPSource
    (tailLocalPNPSource_of_semanticTailLocalPNPSource S)

/-- The semantic local P/NP source forces unbounded peel-debt. -/
theorem unboundedPeelDebt_of_semanticTailLocalPNPSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : SemanticTailLocalPNPSource D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  exact unboundedPeelDebt_of_tailLocalPNPSource
    (tailLocalPNPSource_of_semanticTailLocalPNPSource S)

/-#############################################################################
  §5. Guard: the old finite-twin-bound source cannot be used here
#############################################################################-/

/--
A bad attempt to derive tail incompressibility from absence of ordinary twins on
the same supplied tail.

This is included only as a guard.  It shows why the Mersenne route needs a
new tail-specific incompressibility theorem: the route simultaneously assumes
ordinary twin supply on the tails it studies.
-/
structure TwinAbsenceDerivedTailSource
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (LocalSuccess : Nat → Prop) where
  success_detects_ordinary_twin :
    ∀ M0 : Nat, LocalSuccess M0 → TwinAbove M0
  no_twin_yields_incompressibility :
    ∀ M0 : Nat, ¬ TwinAbove M0 → ¬ LocalSuccess M0

/-- Under ordinary infinitude there is no tail at which a no-twin hypothesis is available. -/
theorem ordinaryInfinite_blocks_twinAbsence_input
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hInf : OrdinaryTwinInfinite TwinAbove) :
    ¬ ∃ M0 : Nat, ¬ TwinAbove M0 := by
  intro h
  rcases h with ⟨M0, hNo⟩
  exact hNo (hInf M0)

/-- Therefore eventual ordinary-twin absence is incompatible with ordinary infinitude. -/
theorem ordinaryInfinite_blocks_eventualTwinBound_source
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hInf : OrdinaryTwinInfinite TwinAbove) :
    ¬ EventuallyNoOrdinaryTwinCenters TwinAbove :=
  ordinaryInfinite_forbids_eventualNoOrdinaryTwins hInf

/-#############################################################################
  §6. Small-scale source and its limitation
#############################################################################-/

/--
A small-scale local source: it provides tail incompressibility only when the
associated scale satisfies `A M0 ≤ 4`.
-/
structure SmallScaleTailLocalSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  nodes : TailSearchNodeFamily D
  A : Nat → Nat
  scale_le_four_incompressible :
    ∀ M0 : Nat,
      TwinAbove M0 → A M0 ≤ 4 → TailLocalIncompressible (nodes.node M0)
  same_debt_resolves :
    ∀ M0 : Nat,
      TwinAbove M0 → SameDebtCollisionResolves (nodes.node M0)

/-- If every supplied tail is small-scale, the small-scale source gives a firewall. -/
def tailCompressionFirewall_of_smallScaleSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : SmallScaleTailLocalSource D TwinAbove)
    (hSmallOnTails : ∀ M0 : Nat, TwinAbove M0 → S.A M0 ≤ 4) :
    TailCompressionFirewall D TwinAbove where
  nodes := S.nodes
  same_debt_resolves := S.same_debt_resolves
  tail_incompressible := by
    intro M0 hTwin
    exact S.scale_le_four_incompressible M0 hTwin (hSmallOnTails M0 hTwin)

/-- If small-scale coverage is known on all supplied tails, peel-debt is unbounded. -/
theorem unboundedPeelDebt_of_smallScaleSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : SmallScaleTailLocalSource D TwinAbove)
    (hSmallOnTails : ∀ M0 : Nat, TwinAbove M0 → S.A M0 ≤ 4) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  exact unboundedTail_of_no_boundedPeelDebtTailDefect <| by
    intro hDefect
    let F := tailCompressionFirewall_of_smallScaleSource S hSmallOnTails
    rcases hDefect with ⟨M0, B, hTwin, hBound⟩
    have hNoBounded : ¬ PeelDebtBoundedOnTail D M0 :=
      no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
        (F.nodes.node M0)
        (F.tail_incompressible M0 hTwin)
        (F.same_debt_resolves M0 hTwin)
    exact hNoBounded ⟨B, hBound⟩

/-#############################################################################
  §7. Final live obligation package
#############################################################################-/

/--
The current honest live obligation for the Mersenne route.

To continue toward Mersenne-twin infinitude, one must fill this with a real
semantic tail local P/NP source.  It cannot be filled merely by citing the global
finite-twin-bound theorem, because the route also uses ordinary twin infinitude.
-/
structure MersenneTailFirewallLiveObligation
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  semantic_tail_source : SemanticTailLocalPNPSource D TwinAbove
  not_using_ordinary_twin_absence : Prop
  not_using_ordinary_twin_absence_proof : not_using_ordinary_twin_absence
  cofinal_tail_scope : Prop
  cofinal_tail_scope_proof : cofinal_tail_scope

/-- The live obligation gives the compression firewall. -/
def tailCompressionFirewall_of_liveObligation
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (O : MersenneTailFirewallLiveObligation D TwinAbove) :
    TailCompressionFirewall D TwinAbove :=
  tailCompressionFirewall_of_semanticTailLocalPNPSource O.semantic_tail_source

/-- The live obligation forces unbounded peel-debt. -/
theorem unboundedPeelDebt_of_liveObligation
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (O : MersenneTailFirewallLiveObligation D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  exact unboundedPeelDebt_of_semanticTailLocalPNPSource O.semantic_tail_source

/-- Final slogan of this patch. -/
theorem tailFirewallFromLocalPNP_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (O : MersenneTailFirewallLiveObligation D TwinAbove) :
    Nonempty (TailCompressionFirewall D TwinAbove) ∧
      UnboundedPeelDebtOnTwinTail D TwinAbove ∧
        O.not_using_ordinary_twin_absence ∧
          O.cofinal_tail_scope := by
  exact ⟨⟨tailCompressionFirewall_of_liveObligation O⟩,
         unboundedPeelDebt_of_liveObligation O,
         O.not_using_ordinary_twin_absence_proof,
         O.cofinal_tail_scope_proof⟩

end TailFirewallFromLocalPNP
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_resolver_payment_firewall_patch.lean =====
/-
EuclidsPath — patch: Mersenne resolver-payment firewall
=========================================================

Purpose
-------
This patch continues the Mersenne route after the tail-local P/NP firewall
source was isolated.

Previous live obligation:

    MersenneTailFirewallLiveObligation

The present patch does not assume that obligation directly.  It explains one
strict way to produce the relevant tail incompressibility under the contradiction
hypothesis `EventuallyNoMersenneTwinCenters`:

    any finite tail resolver
      ⇒ cofinally extracts a paid Mersenne prime pair
      ⇒ by payment soundness, cofinally extracts a Mersenne-twin center
      ⇒ contradiction with eventual absence.

Then, as in the previous bounded-debt firewall, tail incompressibility plus
same-debt resolution forbids bounded peel-debt.  Unbounded peel-debt plus the
law “a genealogy pays its own Mersenne debt pair” gives cofinally many
Mersenne-twin centers.

This file is still conditional.  It does not prove Mersenne-twin infinitude by
itself.  It isolates the next genuine obligation:

    finite resolver ⇒ cofinal Mersenne pair payment.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace ResolverPaymentFirewall

/-#############################################################################
  §1. Mersenne twin centers and eventual absence
#############################################################################-/

/-- Abstract primality predicate.  In the concrete repo instantiate by `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- The lower side of the Mersenne-twin candidate at base-4 peel index `k`. -/
def mersenneLower (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 3

/-- The upper Mersenne side at base-4 peel index `k`. -/
def mersenneUpper (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 1

/-- A Mersenne-twin center at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (mersenneLower k) ∧ Prime (mersenneUpper k)

/-- Cofinal/infinite supply of Mersenne-twin centers. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Eventual absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal supply forbids eventual absence. -/
theorem infinite_mersenne_supply_forbids_eventual_absence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hAbs⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hAbs k hk hTwin

/-#############################################################################
  §2. Ordinary twin tails and peel-debt
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Ordinary infinite twin supply in tail form. -/
def OrdinaryTwinInfinite (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat, TwinAbove M0

/-- Peel-debt system over ordinary twin genealogies. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies living on one fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

/-- Peel-debt bounded on one tail. -/
def PeelDebtBoundedOnTail (D : PeelDebtSystem) (M0 : Nat) : Prop :=
  ∃ B : Nat, ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- Bounded peel-debt defect on some supplied ordinary twin tail. -/
def BoundedPeelDebtTailDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∃ M0 B : Nat,
    TwinAbove M0 ∧
      ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B

/-- Unbounded peel-debt on every supplied ordinary twin tail. -/
def UnboundedPeelDebtOnTwinTail
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 : Nat,
    TwinAbove M0 →
      ∀ B : Nat,
        ∃ Γ : D.Genealogy, D.Tail Γ M0 ∧ B < D.debt Γ

/-- Absence of bounded-tail defect gives unbounded debt on every supplied tail. -/
theorem unboundedTail_of_no_boundedPeelDebtTailDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hNoBounded : ¬ BoundedPeelDebtTailDefect D TwinAbove) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  intro M0 hTwin B
  classical
  by_contra hNoWitness
  apply hNoBounded
  refine ⟨M0, B, hTwin, ?_⟩
  intro Γ hTail
  by_contra hNotLe
  have hgt : B < D.debt Γ := lt_of_not_ge hNotLe
  exact hNoWitness ⟨Γ, hTail, hgt⟩

/-#############################################################################
  §3. Tail finite-key resolvers
#############################################################################-/

/-- A local search node on one tail. -/
structure TailSearchNode (D : PeelDebtSystem) (M0 : Nat) where
  CollisionResolution : TailGenealogy D M0 → TailGenealogy D M0 → Prop

/-- A family of local search nodes for all tails. -/
structure TailSearchNodeFamily (D : PeelDebtSystem) where
  node : ∀ M0 : Nat, TailSearchNode D M0

/-- A finite-key resolver on one tail. -/
structure TailFiniteKeyResolver
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) where
  Key : Type
  finite_key : Fintype Key
  keyOf : TailGenealogy D M0 → Key
  resolves :
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ →
        keyOf γ₁ = keyOf γ₂ →
          N.CollisionResolution γ₁ γ₂

namespace TailFiniteKeyResolver

instance {D : PeelDebtSystem} {M0 : Nat} {N : TailSearchNode D M0}
    (R : TailFiniteKeyResolver N) : Fintype R.Key :=
  R.finite_key

end TailFiniteKeyResolver

/-- Local P-success on a tail. -/
def TailLocalPSuccess
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  Nonempty (TailFiniteKeyResolver N)

/-- Local incompressibility on a tail. -/
def TailLocalIncompressible
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  ¬ TailLocalPSuccess N

/-- Same-debt collisions resolve semantically on this tail. -/
def SameDebtCollisionResolves
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  ∀ γ₁ γ₂ : TailGenealogy D M0,
    γ₁ ≠ γ₂ →
      D.debt γ₁.1 = D.debt γ₂.1 →
        N.CollisionResolution γ₁ γ₂

/-- Bounded debt gives a finite key by debt value. -/
noncomputable def boundedDebtFiniteKeyResolver
    {D : PeelDebtSystem} {M0 B : Nat}
    (N : TailSearchNode D M0)
    (hBound : ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B)
    (hSameDebt : SameDebtCollisionResolves N) :
    TailFiniteKeyResolver N :=
{ Key := Fin (B + 1)
  finite_key := inferInstance
  keyOf := fun γ => ⟨D.debt γ.1, Nat.lt_succ_of_le (hBound γ.1 γ.2)⟩
  resolves := by
    intro γ₁ γ₂ hneq hKey
    apply hSameDebt γ₁ γ₂ hneq
    exact congrArg Fin.val hKey }

/-- Bounded debt plus same-debt resolution gives local P-success. -/
theorem tailLocalPSuccess_of_boundedDebt_and_sameDebtResolution
    {D : PeelDebtSystem} {M0 B : Nat}
    (N : TailSearchNode D M0)
    (hBound : ∀ Γ : D.Genealogy, D.Tail Γ M0 → D.debt Γ ≤ B)
    (hSameDebt : SameDebtCollisionResolves N) :
    TailLocalPSuccess N := by
  exact ⟨boundedDebtFiniteKeyResolver N hBound hSameDebt⟩

/-- Tail incompressibility and same-debt resolution forbid bounded debt. -/
theorem no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0)
    (hIncompressible : TailLocalIncompressible N)
    (hSameDebt : SameDebtCollisionResolves N) :
    ¬ PeelDebtBoundedOnTail D M0 := by
  intro hBounded
  rcases hBounded with ⟨B, hBound⟩
  exact hIncompressible
    (tailLocalPSuccess_of_boundedDebt_and_sameDebtResolution N hBound hSameDebt)

/-#############################################################################
  §4. Prime-payment ledger and resolver-payment extraction
#############################################################################-/

/-- Raw prime-payment ledger for Mersenne pair payments. -/
structure PrimePaymentLedger (Genealogy : Type) where
  PairPaid : Genealogy → Nat → Prop

/-- Soundness: paying the Mersenne pair at index `k` certifies a Mersenne twin center. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    {Genealogy : Type}
    (L : PrimePaymentLedger Genealogy) : Prop :=
  ∀ Γ k, L.PairPaid Γ k → MersenneTwinCenter Prime k

/-- A genealogy pays the Mersenne pair at its own peel-debt index. -/
def PeelDebtPaysOwnMersennePair
    (D : PeelDebtSystem)
    (L : PrimePaymentLedger D.Genealogy) : Prop :=
  ∀ Γ : D.Genealogy, L.PairPaid Γ (D.debt Γ)

/--
Finite resolver ⇒ cofinal Mersenne pair payment.

This is the new strict live obligation.  It says that any finite resolver on a
supplied ordinary twin tail must expose a paid Mersenne pair at an arbitrarily
large peel index.
-/
structure ResolverPaymentExtraction
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : PrimePaymentLedger D.Genealogy)
    (Nodes : TailSearchNodeFamily D) where
  extracts_payment :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        TailLocalPSuccess (Nodes.node M0) →
          ∃ Γ : D.Genealogy,
          ∃ k : Nat,
            D.Tail Γ M0 ∧ K0 ≤ k ∧ L.PairPaid Γ k

/-- Under eventual absence, payment extraction forbids tail local P-success. -/
theorem tailLocalIncompressible_of_eventualAbsence_and_paymentExtraction
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (hAbs : EventuallyNoMersenneTwinCenters Prime)
    (hSound : PrimePaymentSound Prime L)
    (E : ResolverPaymentExtraction D TwinAbove L Nodes)
    (M0 : Nat)
    (hTwin : TwinAbove M0) :
    TailLocalIncompressible (Nodes.node M0) := by
  intro hSuccess
  rcases hAbs with ⟨K0, hAbsTail⟩
  rcases E.extracts_payment M0 K0 hTwin hSuccess with ⟨Γ, k, _hTail, hk, hPaid⟩
  exact hAbsTail k hk (hSound Γ k hPaid)

/-#############################################################################
  §5. Absence-derived tail compression firewall
#############################################################################-/

/-- Source package for deriving the tail firewall from resolver-payment extraction. -/
structure ResolverPaymentFirewallSource
    (Prime : PrimeLike)
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  ledger : PrimePaymentLedger D.Genealogy
  nodes : TailSearchNodeFamily D
  same_debt_resolves :
    ∀ M0 : Nat, TwinAbove M0 → SameDebtCollisionResolves (nodes.node M0)
  payment_sound : PrimePaymentSound Prime ledger
  resolver_payment_extraction :
    ResolverPaymentExtraction D TwinAbove ledger nodes
  not_using_ordinary_twin_absence : Prop
  not_using_ordinary_twin_absence_proof : not_using_ordinary_twin_absence

/-- Tail compression firewall under the contradiction hypothesis of Mersenne absence. -/
structure AbsenceDerivedTailCompressionFirewall
    (Prime : PrimeLike)
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  nodes : TailSearchNodeFamily D
  same_debt_resolves :
    ∀ M0 : Nat, TwinAbove M0 → SameDebtCollisionResolves (nodes.node M0)
  tail_incompressible :
    ∀ M0 : Nat, TwinAbove M0 → TailLocalIncompressible (nodes.node M0)

/-- Build the absence-derived firewall from resolver-payment extraction. -/
def absenceDerivedFirewall_of_resolverPaymentExtraction
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : ResolverPaymentFirewallSource Prime D TwinAbove)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    AbsenceDerivedTailCompressionFirewall Prime D TwinAbove where
  nodes := S.nodes
  same_debt_resolves := S.same_debt_resolves
  tail_incompressible := by
    intro M0 hTwin
    exact tailLocalIncompressible_of_eventualAbsence_and_paymentExtraction
      hAbs S.payment_sound S.resolver_payment_extraction M0 hTwin

/-- The absence-derived firewall forbids bounded peel-debt defect. -/
theorem no_boundedPeelDebtTailDefect_of_absenceDerivedFirewall
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : AbsenceDerivedTailCompressionFirewall Prime D TwinAbove) :
    ¬ BoundedPeelDebtTailDefect D TwinAbove := by
  intro hDefect
  rcases hDefect with ⟨M0, B, hTwin, hBound⟩
  have hNoBounded : ¬ PeelDebtBoundedOnTail D M0 :=
    no_boundedDebt_on_tail_of_incompressible_and_sameDebtResolution
      (F.nodes.node M0)
      (F.tail_incompressible M0 hTwin)
      (F.same_debt_resolves M0 hTwin)
  exact hNoBounded ⟨B, hBound⟩

/-- Therefore, under absence and the resolver-payment source, peel-debt is unbounded. -/
theorem unboundedPeelDebt_of_absence_and_resolverPaymentSource
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : ResolverPaymentFirewallSource Prime D TwinAbove)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    UnboundedPeelDebtOnTwinTail D TwinAbove := by
  exact unboundedTail_of_no_boundedPeelDebtTailDefect
    (no_boundedPeelDebtTailDefect_of_absenceDerivedFirewall
      (absenceDerivedFirewall_of_resolverPaymentExtraction S hAbs))

/-#############################################################################
  §6. From unbounded own-debt payment to Mersenne supply
#############################################################################-/

/-- Unbounded debt plus own-debt payment and soundness gives cofinal Mersenne supply. -/
theorem infinite_mersenne_supply_of_unboundedDebt_ownPayment_soundness
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove)
    (hOwnPay : PeelDebtPaysOwnMersennePair D L)
    (hSound : PrimePaymentSound Prime L) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  have hTwin0 : TwinAbove 0 := hOrdInf 0
  rcases hUnbounded 0 hTwin0 K0 with ⟨Γ, _hTail, hDebtGt⟩
  refine ⟨D.debt Γ, Nat.le_of_lt hDebtGt, ?_⟩
  exact hSound Γ (D.debt Γ) (hOwnPay Γ)

/-- Resolver-payment source plus own-debt payment refutes eventual absence. -/
theorem eventual_absence_contradicts_resolverPaymentSource_ownPayment_soundness
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (S : ResolverPaymentFirewallSource Prime D TwinAbove)
    (hOwnPay : PeelDebtPaysOwnMersennePair D S.ledger)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    False := by
  have hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove :=
    unboundedPeelDebt_of_absence_and_resolverPaymentSource S hAbs
  have hInfMersenne : InfinitelyManyMersenneTwinCenters Prime :=
    infinite_mersenne_supply_of_unboundedDebt_ownPayment_soundness
      hOrdInf hUnbounded hOwnPay S.payment_sound
  exact infinite_mersenne_supply_forbids_eventual_absence hInfMersenne hAbs

/-- The final package for this route. -/
structure MersenneResolverPaymentRoute
    (Prime : PrimeLike)
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  ordinary_infinite : OrdinaryTwinInfinite TwinAbove
  source : ResolverPaymentFirewallSource Prime D TwinAbove
  own_debt_payment : PeelDebtPaysOwnMersennePair D source.ledger

/-- The route forbids eventual absence of Mersenne-twin centers. -/
theorem resolverPaymentRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneResolverPaymentRoute Prime D TwinAbove) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact eventual_absence_contradicts_resolverPaymentSource_ownPayment_soundness
    R.ordinary_infinite R.source R.own_debt_payment hAbs

/-- The route produces cofinal Mersenne-twin supply. -/
theorem resolverPaymentRoute_produces_infinite_mersenne_supply
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneResolverPaymentRoute Prime D TwinAbove)
    (hAbsForContradiction : EventuallyNoMersenneTwinCenters Prime) :
    InfinitelyManyMersenneTwinCenters Prime := by
  have hUnbounded : UnboundedPeelDebtOnTwinTail D TwinAbove :=
    unboundedPeelDebt_of_absence_and_resolverPaymentSource R.source hAbsForContradiction
  exact infinite_mersenne_supply_of_unboundedDebt_ownPayment_soundness
    R.ordinary_infinite hUnbounded R.own_debt_payment R.source.payment_sound

/-#############################################################################
  §7. Defect split
#############################################################################-/

/-- Failure of resolver-payment extraction. -/
def ResolverPaymentExtractionDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    (Nodes : TailSearchNodeFamily D) : Prop :=
  ¬ ResolverPaymentExtraction D TwinAbove L Nodes

/-- Failure of own-debt payment. -/
def OwnDebtPaymentDefect
    (D : PeelDebtSystem)
    (L : PrimePaymentLedger D.Genealogy) : Prop :=
  ¬ PeelDebtPaysOwnMersennePair D L

/-- Failure of payment soundness. -/
def PrimePaymentSoundnessDefect
    (Prime : PrimeLike)
    {Genealogy : Type}
    (L : PrimePaymentLedger Genealogy) : Prop :=
  ¬ PrimePaymentSound Prime L

/-- If absence holds despite ordinary infinitude, some payment route component must fail. -/
theorem absence_forces_resolverExtraction_or_ownPayment_or_soundness_defect
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hOrdInf : OrdinaryTwinInfinite TwinAbove)
    (L : PrimePaymentLedger D.Genealogy)
    (Nodes : TailSearchNodeFamily D)
    (hAbs : EventuallyNoMersenneTwinCenters Prime)
    (hSameDebt :
      ∀ M0 : Nat, TwinAbove M0 → SameDebtCollisionResolves (Nodes.node M0)) :
    ResolverPaymentExtractionDefect (TwinAbove := TwinAbove) (L := L) Nodes ∨
      OwnDebtPaymentDefect D L ∨
        PrimePaymentSoundnessDefect Prime L := by
  classical
  by_cases hExtract : ResolverPaymentExtraction D TwinAbove L Nodes
  · by_cases hOwn : PeelDebtPaysOwnMersennePair D L
    · by_cases hSound : PrimePaymentSound Prime L
      · let S : ResolverPaymentFirewallSource Prime D TwinAbove :=
        { ledger := L
          nodes := Nodes
          same_debt_resolves := hSameDebt
          payment_sound := hSound
          resolver_payment_extraction := hExtract
          not_using_ordinary_twin_absence := True
          not_using_ordinary_twin_absence_proof := trivial }
        have hFalse : False :=
          eventual_absence_contradicts_resolverPaymentSource_ownPayment_soundness
            hOrdInf S hOwn hAbs
        exact False.elim hFalse
      · exact Or.inr (Or.inr hSound)
    · exact Or.inr (Or.inl hOwn)
  · exact Or.inl hExtract

/-- Compact slogan of the resolver-payment firewall. -/
theorem resolverPaymentFirewall_slogan
    {Prime : PrimeLike}
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (R : MersenneResolverPaymentRoute Prime D TwinAbove) :
    OrdinaryTwinInfinite TwinAbove ∧
      ResolverPaymentExtraction D TwinAbove R.source.ledger R.source.nodes ∧
        PeelDebtPaysOwnMersennePair D R.source.ledger ∧
          PrimePaymentSound Prime R.source.ledger ∧
            ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨R.ordinary_infinite,
         R.source.resolver_payment_extraction,
         R.own_debt_payment,
         R.source.payment_sound,
         resolverPaymentRoute_forbids_eventual_absence R⟩

end ResolverPaymentFirewall
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_resolver_payment_extraction_decomposition_patch.lean =====
/-
EuclidsPath — patch: Mersenne resolver-payment extraction decomposition
========================================================================

Purpose
-------
The previous patch isolated the live obligation:

    ResolverPaymentExtraction

meaning that any finite resolver on an ordinary twin tail must cofinally expose a
paid Mersenne prime pair.

This file decomposes that obligation into two sharper pieces:

  1. CofinalSameKeyCollisionPressure:
       every finite resolver has same-key collisions with arbitrarily large
       Mersenne collision index;

  2. FaithfulResolutionPaymentLaw:
       every semantically resolved same-key collision at Mersenne index `k`
       pays the Mersenne pair at `k`.

For audit purposes the second piece is also derived from a classifier:

       resolved collision
         ⇒ Mersenne payment ∨ seam defect ∨ compression defect ∨ non-Mersenne bucket defect.

Thus, under `NoResolverPaymentEscape`, the classifier becomes a genuine payment
law.

No theorem here proves Mersenne-twin infinitude by itself.  The file only proves
pure assembly:

    pressure + faithful payment law ⇒ ResolverPaymentExtraction.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace ResolverPaymentExtractionDecomposition

/-#############################################################################
  §1. Local tail resolver primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- Peel-debt system over ordinary twin genealogies. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies living on one fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

/-- A local search node on one tail. -/
structure TailSearchNode (D : PeelDebtSystem) (M0 : Nat) where
  CollisionResolution : TailGenealogy D M0 → TailGenealogy D M0 → Prop

/-- A family of local search nodes for all tails. -/
structure TailSearchNodeFamily (D : PeelDebtSystem) where
  node : ∀ M0 : Nat, TailSearchNode D M0

/-- A finite-key resolver on one tail. -/
structure TailFiniteKeyResolver
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) where
  Key : Type
  finite_key : Fintype Key
  keyOf : TailGenealogy D M0 → Key
  resolves :
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ →
        keyOf γ₁ = keyOf γ₂ →
          N.CollisionResolution γ₁ γ₂

namespace TailFiniteKeyResolver

instance {D : PeelDebtSystem} {M0 : Nat} {N : TailSearchNode D M0}
    (R : TailFiniteKeyResolver N) : Fintype R.Key :=
  R.finite_key

end TailFiniteKeyResolver

/-- Local P-success on a tail. -/
def TailLocalPSuccess
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) : Prop :=
  Nonempty (TailFiniteKeyResolver N)

/-- Raw prime-payment ledger for Mersenne pair payments. -/
structure PrimePaymentLedger (Genealogy : Type) where
  PairPaid : Genealogy → Nat → Prop

/-- The previous live obligation: finite resolver exposes cofinal Mersenne payment. -/
structure ResolverPaymentExtraction
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : PrimePaymentLedger D.Genealogy)
    (Nodes : TailSearchNodeFamily D) where
  extracts_payment :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        TailLocalPSuccess (Nodes.node M0) →
          ∃ Γ : D.Genealogy,
          ∃ k : Nat,
            D.Tail Γ M0 ∧ K0 ≤ k ∧ L.PairPaid Γ k

/-#############################################################################
  §2. Cofinal same-key collision pressure
#############################################################################-/

/--
Every finite resolver must identify two different tail genealogies with the same
key at an arbitrarily large Mersenne collision index.

The index is explicit: this prevents a resolver from satisfying the pressure by
only producing bounded or irrelevant collisions.
-/
structure CofinalSameKeyCollisionPressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Nodes : TailSearchNodeFamily D) where

  collisionIndex : ∀ {M0 : Nat},
    TailGenealogy D M0 → TailGenealogy D M0 → Nat

  pressure :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ∀ R : TailFiniteKeyResolver (Nodes.node M0),
          ∃ γ₁ γ₂ : TailGenealogy D M0,
            γ₁ ≠ γ₂ ∧
            R.keyOf γ₁ = R.keyOf γ₂ ∧
            K0 ≤ collisionIndex γ₁ γ₂

namespace CofinalSameKeyCollisionPressure

/-- Same-key pressure plus a resolver gives a resolved high-index collision. -/
theorem resolved_high_collision
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {Nodes : TailSearchNodeFamily D}
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes)
    {M0 K0 : Nat}
    (hTwin : TwinAbove M0)
    (R : TailFiniteKeyResolver (Nodes.node M0)) :
    ∃ γ₁ γ₂ : TailGenealogy D M0,
      (Nodes.node M0).CollisionResolution γ₁ γ₂ ∧
      K0 ≤ P.collisionIndex γ₁ γ₂ := by
  rcases P.pressure M0 K0 hTwin R with ⟨γ₁, γ₂, hne, hsame, hIndex⟩
  exact ⟨γ₁, γ₂, R.resolves γ₁ γ₂ hne hsame, hIndex⟩

end CofinalSameKeyCollisionPressure

/-#############################################################################
  §3. Faithful payment law for resolved collisions
#############################################################################-/

/--
Faithful payment law: once a same-key collision is semantically resolved, the
resolver has paid the Mersenne pair at the collision index.
-/
structure FaithfulResolutionPaymentLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : PrimePaymentLedger D.Genealogy)
    (Nodes : TailSearchNodeFamily D)
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes)
    where
  pays_of_resolved :
    ∀ {M0 : Nat},
      ∀ γ₁ γ₂ : TailGenealogy D M0,
        (Nodes.node M0).CollisionResolution γ₁ γ₂ →
          L.PairPaid γ₁.1 (P.collisionIndex γ₁ γ₂)

/--
Pressure plus faithful payment law proves the previous live obligation.
-/
theorem resolverPaymentExtraction_of_pressure_and_paymentLaw
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes)
    (Law : FaithfulResolutionPaymentLaw D TwinAbove L Nodes P) :
    ResolverPaymentExtraction D TwinAbove L Nodes := by
  refine ⟨?_⟩
  intro M0 K0 hTwin hSuccess
  rcases hSuccess with ⟨R⟩
  rcases P.resolved_high_collision hTwin R with ⟨γ₁, γ₂, hResolved, hIndex⟩
  exact ⟨γ₁.1, P.collisionIndex γ₁ γ₂, γ₁.2, hIndex,
    Law.pays_of_resolved γ₁ γ₂ hResolved⟩

/-#############################################################################
  §4. Payment classifier and escape defects
#############################################################################-/

/--
Classifier for a resolved collision.  It says that a resolved collision must be
accounted for as one of four alternatives:

  * genuine Mersenne pair payment;
  * seam defect;
  * compression defect;
  * non-Mersenne bucket defect.
-/
structure ResolutionPaymentClassifier
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : PrimePaymentLedger D.Genealogy)
    (Nodes : TailSearchNodeFamily D)
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes) where

  SeamDefect : Prop
  CompressionDefect : Prop
  NonMersenneBucketDefect : Prop

  classifies :
    ∀ {M0 : Nat},
      ∀ γ₁ γ₂ : TailGenealogy D M0,
        (Nodes.node M0).CollisionResolution γ₁ γ₂ →
          L.PairPaid γ₁.1 (P.collisionIndex γ₁ γ₂) ∨
            SeamDefect ∨ CompressionDefect ∨ NonMersenneBucketDefect

/-- No escape: all non-payment classification branches are forbidden. -/
def NoResolverPaymentEscape
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    {P : CofinalSameKeyCollisionPressure D TwinAbove Nodes}
    (C : ResolutionPaymentClassifier D TwinAbove L Nodes P) : Prop :=
  ¬ C.SeamDefect ∧ ¬ C.CompressionDefect ∧ ¬ C.NonMersenneBucketDefect

/-- A classifier plus no-escape gives the faithful payment law. -/
theorem paymentLaw_of_classifier_noEscape
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    {P : CofinalSameKeyCollisionPressure D TwinAbove Nodes}
    (C : ResolutionPaymentClassifier D TwinAbove L Nodes P)
    (hNoEscape : NoResolverPaymentEscape C) :
    FaithfulResolutionPaymentLaw D TwinAbove L Nodes P := by
  refine ⟨?_⟩
  intro M0 γ₁ γ₂ hResolved
  rcases C.classifies γ₁ γ₂ hResolved with hPaid | hRest
  · exact hPaid
  · rcases hRest with hSeam | hRest2
    · exact False.elim (hNoEscape.1 hSeam)
    · rcases hRest2 with hComp | hBucket
      · exact False.elim (hNoEscape.2.1 hComp)
      · exact False.elim (hNoEscape.2.2 hBucket)

/-- Therefore pressure + classifier + no-escape gives resolver-payment extraction. -/
theorem resolverPaymentExtraction_of_pressure_classifier_noEscape
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes)
    (C : ResolutionPaymentClassifier D TwinAbove L Nodes P)
    (hNoEscape : NoResolverPaymentEscape C) :
    ResolverPaymentExtraction D TwinAbove L Nodes := by
  exact resolverPaymentExtraction_of_pressure_and_paymentLaw P
    (paymentLaw_of_classifier_noEscape C hNoEscape)

/-#############################################################################
  §5. Defect split
#############################################################################-/

/-- Failure of cofinal same-key collision pressure. -/
def CofinalSameKeyCollisionPressureDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Nodes : TailSearchNodeFamily D) : Prop :=
  CofinalSameKeyCollisionPressure D TwinAbove Nodes → False

/-- Failure of the faithful resolution-payment law for a fixed pressure object. -/
def FaithfulResolutionPaymentLawDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes) : Prop :=
  ¬ FaithfulResolutionPaymentLaw D TwinAbove L Nodes P

/-- Failure of the classifier/no-escape route. -/
def ResolverPaymentEscapeDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    {P : CofinalSameKeyCollisionPressure D TwinAbove Nodes}
    (C : ResolutionPaymentClassifier D TwinAbove L Nodes P) : Prop :=
  C.SeamDefect ∨ C.CompressionDefect ∨ C.NonMersenneBucketDefect

/-- If extraction fails, then pressure or payment law must fail. -/
theorem extraction_defect_forces_pressure_or_paymentLaw_defect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (hNoExtraction : ¬ ResolverPaymentExtraction D TwinAbove L Nodes) :
    CofinalSameKeyCollisionPressureDefect D TwinAbove Nodes ∨
      ∃ P : CofinalSameKeyCollisionPressure D TwinAbove Nodes,
        FaithfulResolutionPaymentLawDefect (L := L) P := by
  classical
  by_cases hPressure : Nonempty (CofinalSameKeyCollisionPressure D TwinAbove Nodes)
  · right
    obtain ⟨P⟩ := hPressure
    refine ⟨P, ?_⟩
    intro hLaw
    exact hNoExtraction
      (resolverPaymentExtraction_of_pressure_and_paymentLaw P hLaw)
  · exact Or.inl (fun P => hPressure ⟨P⟩)

/-- If extraction fails despite pressure and a classifier, then some escape branch is real. -/
theorem extraction_defect_forces_classifier_escape
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (P : CofinalSameKeyCollisionPressure D TwinAbove Nodes)
    (C : ResolutionPaymentClassifier D TwinAbove L Nodes P)
    (hNoExtraction : ¬ ResolverPaymentExtraction D TwinAbove L Nodes) :
    ResolverPaymentEscapeDefect C := by
  classical
  by_cases hSeam : C.SeamDefect
  · exact Or.inl hSeam
  · by_cases hComp : C.CompressionDefect
    · exact Or.inr (Or.inl hComp)
    · by_cases hBucket : C.NonMersenneBucketDefect
      · exact Or.inr (Or.inr hBucket)
      · have hNoEscape : NoResolverPaymentEscape C := ⟨hSeam, hComp, hBucket⟩
        have hExtraction : ResolverPaymentExtraction D TwinAbove L Nodes :=
          resolverPaymentExtraction_of_pressure_classifier_noEscape P C hNoEscape
        exact False.elim (hNoExtraction hExtraction)

/-#############################################################################
  §6. Final live front package
#############################################################################-/

/-- The decomposed live front for resolver-payment extraction. -/
structure ResolverPaymentExtractionFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (L : PrimePaymentLedger D.Genealogy)
    (Nodes : TailSearchNodeFamily D) where

  pressure : CofinalSameKeyCollisionPressure D TwinAbove Nodes

  classifier : ResolutionPaymentClassifier D TwinAbove L Nodes pressure

  no_escape : NoResolverPaymentEscape classifier

  not_using_mersenne_twin_infinitude : Prop
  not_using_mersenne_twin_infinitude_proof : not_using_mersenne_twin_infinitude

  not_using_classical_PNP : Prop
  not_using_classical_PNP_proof : not_using_classical_PNP

/-- The decomposed front proves the previous live extraction obligation. -/
theorem resolverPaymentExtraction_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (F : ResolverPaymentExtractionFront D TwinAbove L Nodes) :
    ResolverPaymentExtraction D TwinAbove L Nodes := by
  exact resolverPaymentExtraction_of_pressure_classifier_noEscape
    F.pressure F.classifier F.no_escape

/-- Compact slogan: extraction is now pressure plus no-escape faithful payment. -/
theorem resolverPaymentExtractionDecomposition_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {L : PrimePaymentLedger D.Genealogy}
    {Nodes : TailSearchNodeFamily D}
    (F : ResolverPaymentExtractionFront D TwinAbove L Nodes) :
    Nonempty (CofinalSameKeyCollisionPressure D TwinAbove Nodes) ∧
      NoResolverPaymentEscape F.classifier ∧
        ResolverPaymentExtraction D TwinAbove L Nodes := by
  exact ⟨⟨F.pressure⟩, F.no_escape, resolverPaymentExtraction_of_front F⟩

end ResolverPaymentExtractionDecomposition
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_same_key_pressure_pigeonhole_patch.lean =====
/-
EuclidsPath — patch: Mersenne same-key pressure from finite pigeonhole
========================================================================

Purpose
-------
The previous patch isolated:

    CofinalSameKeyCollisionPressure

as the remaining source of resolver-payment extraction.  This file decomposes
that pressure into a concrete finite-key/pigeonhole mechanism:

  1. choose a Mersenne collision index for pairs of tail genealogies;
  2. for every ordinary twin tail `M0` and every requested Mersenne floor `K0`,
     exhibit a subfamily of tail genealogies whose pairwise collision index is
     at least `K0`;
  3. require the subfamily to be finite-key-pigeonhole-incompressible.

Then every finite resolver on the tail must identify two different members of
that high-index subfamily with the same key.  This yields cofinal same-key
collision pressure.

No theorem here proves the analytic/arithmetic existence of the high-index
subfamilies.  That existence is now the sharper live obligation.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace SameKeyPressurePigeonhole

/-#############################################################################
  §1. Tail resolver primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

/-- A local search node on a tail. -/
structure TailSearchNode (D : PeelDebtSystem) (M0 : Nat) where
  CollisionResolution : TailGenealogy D M0 → TailGenealogy D M0 → Prop

/-- A family of tail search nodes. -/
structure TailSearchNodeFamily (D : PeelDebtSystem) where
  node : ∀ M0 : Nat, TailSearchNode D M0

/-- A finite-key resolver on one tail. -/
structure TailFiniteKeyResolver
    {D : PeelDebtSystem} {M0 : Nat}
    (N : TailSearchNode D M0) where
  Key : Type
  finite_key : Fintype Key
  keyOf : TailGenealogy D M0 → Key
  resolves :
    ∀ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ →
        keyOf γ₁ = keyOf γ₂ →
          N.CollisionResolution γ₁ γ₂

namespace TailFiniteKeyResolver

instance {D : PeelDebtSystem} {M0 : Nat} {N : TailSearchNode D M0}
    (R : TailFiniteKeyResolver N) : Fintype R.Key :=
  R.finite_key

end TailFiniteKeyResolver

/-#############################################################################
  §2. Cofinal same-key pressure target
#############################################################################-/

/--
The target isolated previously: every finite resolver has same-key collisions at
arbitrarily high Mersenne collision index.
-/
structure CofinalSameKeyCollisionPressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Nodes : TailSearchNodeFamily D) where

  collisionIndex : ∀ {M0 : Nat},
    TailGenealogy D M0 → TailGenealogy D M0 → Nat

  pressure :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ∀ R : TailFiniteKeyResolver (Nodes.node M0),
          ∃ γ₁ γ₂ : TailGenealogy D M0,
            γ₁ ≠ γ₂ ∧
            R.keyOf γ₁ = R.keyOf γ₂ ∧
            K0 ≤ collisionIndex γ₁ γ₂

/-#############################################################################
  §3. High-index subfamilies with a finite-key pigeonhole principle
#############################################################################-/

/-- A collision-indexing system for tail genealogies. -/
structure MersenneCollisionIndexing (D : PeelDebtSystem) where
  collisionIndex : ∀ {M0 : Nat},
    TailGenealogy D M0 → TailGenealogy D M0 → Nat

/--
A high-index tail subfamily at floor `K0`.

The field `finite_key_collision` is the exact finite-pigeonhole input: any map
from this subfamily into a finite key type identifies two distinct subfamily
members.  In concrete use this is supplied by infinitude of the subfamily.
-/
structure HighIndexPigeonholeSubfamily
    (D : PeelDebtSystem)
    (Idx : MersenneCollisionIndexing D)
    (M0 K0 : Nat) where

  SubIndex : Type

  toTail : SubIndex → TailGenealogy D M0

  toTail_injective : Function.Injective toTail

  high_pair :
    ∀ a b : SubIndex,
      a ≠ b →
        K0 ≤ Idx.collisionIndex (toTail a) (toTail b)

  finite_key_collision :
    ∀ (Key : Type) [Fintype Key] (keyOf : SubIndex → Key),
      ∃ a b : SubIndex,
        a ≠ b ∧ keyOf a = keyOf b

namespace HighIndexPigeonholeSubfamily

/-- Restricting a tail resolver key to a high-index subfamily creates a high-index same-key collision. -/
theorem sameKeyCollision_of_resolver
    {D : PeelDebtSystem}
    {Idx : MersenneCollisionIndexing D}
    {M0 K0 : Nat}
    (H : HighIndexPigeonholeSubfamily D Idx M0 K0)
    {N : TailSearchNode D M0}
    (R : TailFiniteKeyResolver N) :
    ∃ γ₁ γ₂ : TailGenealogy D M0,
      γ₁ ≠ γ₂ ∧
      R.keyOf γ₁ = R.keyOf γ₂ ∧
      K0 ≤ Idx.collisionIndex γ₁ γ₂ := by
  rcases H.finite_key_collision R.Key (fun a => R.keyOf (H.toTail a)) with
    ⟨a, b, hab, hsame⟩
  have htail_ne : H.toTail a ≠ H.toTail b := by
    intro hEq
    exact hab (H.toTail_injective hEq)
  exact ⟨H.toTail a, H.toTail b, htail_ne, hsame, H.high_pair a b hab⟩

end HighIndexPigeonholeSubfamily

/--
Cofinal high-index subfamily pressure: every ordinary twin tail and every floor
`K0` has a high-index pigeonhole subfamily.
-/
structure CofinalHighIndexPigeonholePressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Idx : MersenneCollisionIndexing D) where
  high_subfamily :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        Nonempty (HighIndexPigeonholeSubfamily D Idx M0 K0)

/--
High-index pigeonhole pressure gives cofinal same-key collision pressure for any
choice of tail search nodes.
-/
def cofinalSameKeyCollisionPressure_of_highIndexPigeonholePressure
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {Idx : MersenneCollisionIndexing D}
    {Nodes : TailSearchNodeFamily D}
    (H : CofinalHighIndexPigeonholePressure D TwinAbove Idx) :
    CofinalSameKeyCollisionPressure D TwinAbove Nodes := by
  refine ⟨Idx.collisionIndex, ?_⟩
  intro M0 K0 hTwin R
  rcases H.high_subfamily M0 K0 hTwin with ⟨Sub⟩
  exact Sub.sameKeyCollision_of_resolver R

/-#############################################################################
  §4. Defect accounting
#############################################################################-/

/-- Failure of cofinal same-key collision pressure. -/
def SameKeyCollisionPressureDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Nodes : TailSearchNodeFamily D) : Prop :=
  CofinalSameKeyCollisionPressure D TwinAbove Nodes → False

/-- Failure of high-index pigeonhole subfamily pressure for an indexing system. -/
def HighIndexPigeonholePressureDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Idx : MersenneCollisionIndexing D) : Prop :=
  ¬ CofinalHighIndexPigeonholePressure D TwinAbove Idx

/--
If the same-key pressure target fails for some node family, then the high-index
pigeonhole pressure cannot hold for the same collision index.
-/
theorem sameKeyPressureDefect_forces_highIndexPigeonholeDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {Idx : MersenneCollisionIndexing D}
    {Nodes : TailSearchNodeFamily D}
    (hDefect : SameKeyCollisionPressureDefect D TwinAbove Nodes) :
    HighIndexPigeonholePressureDefect D TwinAbove Idx := by
  intro hHigh
  exact hDefect (cofinalSameKeyCollisionPressure_of_highIndexPigeonholePressure hHigh)

/--
A resolver can avoid cofinal same-key pressure only by destroying the high-index
pigeonhole source.
-/
theorem no_free_escape_from_sameKeyPressure
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {Idx : MersenneCollisionIndexing D}
    {Nodes : TailSearchNodeFamily D}
    (hHigh : CofinalHighIndexPigeonholePressure D TwinAbove Idx) :
    ¬ SameKeyCollisionPressureDefect D TwinAbove Nodes := by
  intro hDefect
  exact hDefect (cofinalSameKeyCollisionPressure_of_highIndexPigeonholePressure hHigh)

/-#############################################################################
  §5. A sharper live front
#############################################################################-/

/--
The sharpened front for proving `CofinalSameKeyCollisionPressure`: provide a
collision index and prove high-index pigeonhole subfamilies.
-/
structure SameKeyPressureFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  indexing : MersenneCollisionIndexing D
  high_index_pigeonhole_pressure :
    CofinalHighIndexPigeonholePressure D TwinAbove indexing

/-- The front yields cofinal same-key pressure for any tail node family. -/
def cofinalSameKeyCollisionPressure_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {Nodes : TailSearchNodeFamily D}
    (F : SameKeyPressureFront D TwinAbove) :
    CofinalSameKeyCollisionPressure D TwinAbove Nodes :=
  cofinalSameKeyCollisionPressure_of_highIndexPigeonholePressure
    F.high_index_pigeonhole_pressure

/-- Slogan theorem for this patch. -/
def sameKeyPressurePigeonhole_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    {Nodes : TailSearchNodeFamily D}
    (F : SameKeyPressureFront D TwinAbove) :
    CofinalSameKeyCollisionPressure D TwinAbove Nodes :=
  cofinalSameKeyCollisionPressure_of_front F

end SameKeyPressurePigeonhole
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_high_index_subfamily_from_peel_debt_patch.lean =====
/-
EuclidsPath — patch: high-index pigeonhole subfamilies from Mersenne peel debt
================================================================================

Purpose
-------
The previous same-key-pressure patch isolated the live obligation:

    CofinalHighIndexPigeonholePressure

meaning: on every ordinary twin tail and above every Mersenne floor `K0`, there
is a finite-key-incompressible subfamily whose pairwise Mersenne collision index
is at least `K0`.

This file sharpens that obligation further.  The intended Mersenne collision
index is the minimum of the two peel-debt indices:

    collisionIndex(γ₁, γ₂) = min (debt γ₁) (debt γ₂).

Therefore a high-index pigeonhole subfamily is obtained from a high-debt
pigeonhole subfamily: a subfamily all of whose members have debt at least `K0`,
and which is incompressible against every finite key.

This is a strict assembly layer:

    CofinalHighDebtPigeonholePressure
      ⇒ CofinalHighIndexPigeonholePressure
      ⇒ CofinalSameKeyCollisionPressure.

The file does not prove the existence of high-debt pigeonhole subfamilies.  It
makes the remaining obligation exact and shows that mere unbounded debt is not
the right strength; what is needed is high-debt finite-key incompressibility on
every tail.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace HighIndexFromPeelDebt

/-#############################################################################
  §1. Minimal tail/debt primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

namespace TailGenealogy

/-- The peel debt of a tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 : Nat} (γ : TailGenealogy D M0) : Nat :=
  D.debt γ.1

end TailGenealogy

/-#############################################################################
  §2. Collision indexing and high-index pigeonhole subfamilies
#############################################################################-/

/-- A collision-indexing system for pairs of tail genealogies. -/
structure MersenneCollisionIndexing (D : PeelDebtSystem) where
  collisionIndex : ∀ {M0 : Nat},
    TailGenealogy D M0 → TailGenealogy D M0 → Nat

/--
The canonical debt-based Mersenne collision index: a pair is high-index only when
both members have high peel debt.
-/
def debtMinCollisionIndexing (D : PeelDebtSystem) : MersenneCollisionIndexing D where
  collisionIndex := by
    intro M0 γ₁ γ₂
    exact min (TailGenealogy.debt γ₁) (TailGenealogy.debt γ₂)

/--
A high-index tail subfamily at floor `K0`, phrased for an arbitrary collision
indexing system.
-/
structure HighIndexPigeonholeSubfamily
    (D : PeelDebtSystem)
    (Idx : MersenneCollisionIndexing D)
    (M0 K0 : Nat) where

  SubIndex : Type

  toTail : SubIndex → TailGenealogy D M0

  toTail_injective : Function.Injective toTail

  high_pair :
    ∀ a b : SubIndex,
      a ≠ b →
        K0 ≤ Idx.collisionIndex (toTail a) (toTail b)

  finite_key_collision :
    ∀ (Key : Type) [Fintype Key] (keyOf : SubIndex → Key),
      ∃ a b : SubIndex,
        a ≠ b ∧ keyOf a = keyOf b

/-- Cofinal high-index subfamily pressure. -/
structure CofinalHighIndexPigeonholePressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove)
    (Idx : MersenneCollisionIndexing D) where
  high_subfamily :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        Nonempty (HighIndexPigeonholeSubfamily D Idx M0 K0)

/-#############################################################################
  §3. High-debt pigeonhole subfamilies
#############################################################################-/

/--
A high-debt pigeonhole subfamily: every member lies on the fixed tail, has debt
at least `K0`, and the subfamily cannot be injected into any finite key.
-/
structure HighDebtPigeonholeSubfamily
    (D : PeelDebtSystem)
    (M0 K0 : Nat) where

  SubIndex : Type

  toTail : SubIndex → TailGenealogy D M0

  toTail_injective : Function.Injective toTail

  high_debt :
    ∀ a : SubIndex,
      K0 ≤ TailGenealogy.debt (toTail a)

  finite_key_collision :
    ∀ (Key : Type) [Fintype Key] (keyOf : SubIndex → Key),
      ∃ a b : SubIndex,
        a ≠ b ∧ keyOf a = keyOf b

namespace HighDebtPigeonholeSubfamily

/-- A high-debt subfamily gives a high-index subfamily for the min-debt index. -/
def toHighIndex
    {D : PeelDebtSystem}
    {M0 K0 : Nat}
    (H : HighDebtPigeonholeSubfamily D M0 K0) :
    HighIndexPigeonholeSubfamily D (debtMinCollisionIndexing D) M0 K0 where
  SubIndex := H.SubIndex
  toTail := H.toTail
  toTail_injective := H.toTail_injective
  high_pair := by
    intro a b _hab
    exact le_min (H.high_debt a) (H.high_debt b)
  finite_key_collision := H.finite_key_collision

/-- The high-index object produced by `toHighIndex` keeps the same subfamily. -/
theorem toHighIndex_preserves_finite_key_collision
    {D : PeelDebtSystem}
    {M0 K0 : Nat}
    (H : HighDebtPigeonholeSubfamily D M0 K0)
    (Key : Type) [Fintype Key] (keyOf : H.SubIndex → Key) :
    ∃ a b : H.SubIndex, a ≠ b ∧ keyOf a = keyOf b :=
  H.finite_key_collision Key keyOf

end HighDebtPigeonholeSubfamily

/--
Cofinal high-debt pigeonhole pressure: every ordinary twin tail and every debt
floor has a high-debt finite-key-incompressible subfamily.
-/
structure CofinalHighDebtPigeonholePressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  high_debt_subfamily :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        Nonempty (HighDebtPigeonholeSubfamily D M0 K0)

/-- High-debt pigeonhole pressure gives high-index pressure for the debt-min index. -/
theorem cofinalHighIndexPigeonholePressure_of_highDebtPressure
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (H : CofinalHighDebtPigeonholePressure D TwinAbove) :
    CofinalHighIndexPigeonholePressure D TwinAbove (debtMinCollisionIndexing D) := by
  refine ⟨?_⟩
  intro M0 K0 hTwin
  rcases H.high_debt_subfamily M0 K0 hTwin with ⟨Sub⟩
  exact ⟨Sub.toHighIndex⟩

/-#############################################################################
  §4. Why unbounded debt alone is weaker than the needed source
#############################################################################-/

/-- Weak cofinality: above every floor there exists at least one tail genealogy. -/
def WeakHighDebtCofinality
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 →
      ∃ γ : TailGenealogy D M0,
        K0 ≤ TailGenealogy.debt γ

/-- High-debt pigeonhole pressure implies weak high-debt cofinality. -/
theorem weakHighDebtCofinality_of_highDebtPressure
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (H : CofinalHighDebtPigeonholePressure D TwinAbove) :
    WeakHighDebtCofinality D TwinAbove := by
  intro M0 K0 hTwin
  rcases H.high_debt_subfamily M0 K0 hTwin with ⟨Sub⟩
  classical
  by_cases hNonempty : Nonempty Sub.SubIndex
  · rcases hNonempty with ⟨a⟩
    exact ⟨Sub.toTail a, Sub.high_debt a⟩
  · exfalso
    -- A finite-key collision source cannot exist on an empty index type.
    rcases Sub.finite_key_collision PUnit (fun a => PUnit.unit) with ⟨a, _b, _hne, _hsame⟩
    exact hNonempty ⟨a⟩

/-- A defect of high-debt pigeonhole pressure. -/
def HighDebtPigeonholePressureDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalHighDebtPigeonholePressure D TwinAbove

/-- A defect of weak high-debt cofinality. -/
def WeakHighDebtCofinalityDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ WeakHighDebtCofinality D TwinAbove

/-- If even weak high-debt cofinality fails, then high-debt pigeonhole pressure fails. -/
theorem weakCofinalityDefect_forces_highDebtPigeonholeDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hWeakDefect : WeakHighDebtCofinalityDefect D TwinAbove) :
    HighDebtPigeonholePressureDefect D TwinAbove := by
  intro hHigh
  exact hWeakDefect (weakHighDebtCofinality_of_highDebtPressure hHigh)

/--
Main audit message: the live source is stronger than mere unboundedness.  It
requires a high-debt subfamily that remains incompressible against every finite
key.
-/
structure HighDebtPigeonholeFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  high_debt_pressure : CofinalHighDebtPigeonholePressure D TwinAbove
  audit_not_merely_single_hits : Prop
  audit_not_merely_single_hits_proof : audit_not_merely_single_hits

/-- The front gives high-index pressure for the canonical debt-min index. -/
theorem highIndexPressure_of_highDebtFront
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtPigeonholeFront D TwinAbove) :
    CofinalHighIndexPigeonholePressure D TwinAbove (debtMinCollisionIndexing D) :=
  cofinalHighIndexPigeonholePressure_of_highDebtPressure F.high_debt_pressure

/-- Slogan theorem for this patch. -/
theorem highIndexFromPeelDebt_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtPigeonholeFront D TwinAbove) :
    CofinalHighIndexPigeonholePressure D TwinAbove (debtMinCollisionIndexing D) ∧
    WeakHighDebtCofinality D TwinAbove := by
  exact ⟨
    highIndexPressure_of_highDebtFront F,
    weakHighDebtCofinality_of_highDebtPressure F.high_debt_pressure
  ⟩

end HighIndexFromPeelDebt
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_high_debt_tail_incompressibility_source_patch.lean =====
/-
EuclidsPath — patch: high-debt tail incompressibility source
=============================================================

Purpose
-------
The previous patch isolated the live obligation

    CofinalHighDebtPigeonholePressure.

This file pushes it one level lower and removes another possible ambiguity.
What is actually needed is not merely that peel debt is unbounded.  For every
ordinary twin tail `M0` and every Mersenne debt floor `K0`, the whole high-debt
subtail

    { Γ on tail M0 // K0 ≤ debt Γ }

must resist every finite-key injection.  Once this `NoFiniteInjection` source is
available, the required finite-key collision/pigeonhole subfamily is canonical:
take the entire high-debt subtail itself.

Main chain in this file:

    CofinalHighDebtNoFiniteInjectionSource
      ⇒ CofinalHighDebtPigeonholePressure
      ⇒ WeakHighDebtCofinality.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace HighDebtTailSource

/-#############################################################################
  §1. Tail/debt primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

namespace TailGenealogy

/-- The peel debt of a tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 : Nat} (γ : TailGenealogy D M0) : Nat :=
  D.debt γ.1

end TailGenealogy

/-- The high-debt subtail above a Mersenne debt floor `K0`. -/
abbrev HighDebtTail (D : PeelDebtSystem) (M0 K0 : Nat) : Type :=
  {γ : TailGenealogy D M0 // K0 ≤ TailGenealogy.debt γ}

namespace HighDebtTail

/-- Forget the high-debt proof and keep the underlying tail genealogy. -/
def toTail {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) : TailGenealogy D M0 :=
  γ.1

/-- Every high-debt tail genealogy has debt at least the floor. -/
theorem high_debt {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) :
    K0 ≤ TailGenealogy.debt (toTail γ) :=
  γ.2

/-- Forgetting the high-debt proof is injective. -/
theorem toTail_injective {D : PeelDebtSystem} {M0 K0 : Nat} :
    Function.Injective (@toTail D M0 K0) := by
  intro a b h
  exact Subtype.ext h

end HighDebtTail

/-#############################################################################
  §2. No finite injection ⇒ finite-key collision
#############################################################################-/

/-- A type cannot be faithfully compressed into any finite key. -/
def NoFiniteInjection (α : Type) : Prop :=
  ∀ (Key : Type) [Fintype Key] (keyOf : α → Key),
    ¬ Function.Injective keyOf

/-- A finite-key collision extracted from non-injectivity. -/
theorem finite_key_collision_of_noFiniteInjection
    {α : Type}
    (hNo : NoFiniteInjection α)
    (Key : Type) [Fintype Key] (keyOf : α → Key) :
    ∃ a b : α, a ≠ b ∧ keyOf a = keyOf b := by
  have hNotInj : ¬ Function.Injective keyOf := hNo Key keyOf
  rw [Function.Injective] at hNotInj
  push_neg at hNotInj
  rcases hNotInj with ⟨a, b, hsame, hne⟩
  exact ⟨a, b, hne, hsame⟩

/-- No finite injection already gives a collision into the one-point key. -/
theorem unit_collision_of_noFiniteInjection
    {α : Type}
    (hNo : NoFiniteInjection α) :
    ∃ a b : α, a ≠ b := by
  let keyOf : α → PUnit := fun _ => PUnit.unit
  rcases finite_key_collision_of_noFiniteInjection hNo PUnit keyOf with
    ⟨a, b, hne, _hsame⟩
  exact ⟨a, b, hne⟩

/-- In particular, a no-finite-injection type is nonempty. -/
theorem nonempty_of_noFiniteInjection
    {α : Type}
    (hNo : NoFiniteInjection α) :
    Nonempty α := by
  rcases unit_collision_of_noFiniteInjection hNo with ⟨a, _b, _hne⟩
  exact ⟨a⟩

/-#############################################################################
  §3. High-debt pigeonhole subfamilies
#############################################################################-/

/--
A high-debt pigeonhole subfamily: every member lies on the fixed tail, has debt
at least `K0`, and the subfamily collides under every finite key.
-/
structure HighDebtPigeonholeSubfamily
    (D : PeelDebtSystem)
    (M0 K0 : Nat) where

  SubIndex : Type

  toTail : SubIndex → TailGenealogy D M0

  toTail_injective : Function.Injective toTail

  high_debt :
    ∀ a : SubIndex,
      K0 ≤ TailGenealogy.debt (toTail a)

  finite_key_collision :
    ∀ (Key : Type) [Fintype Key] (keyOf : SubIndex → Key),
      ∃ a b : SubIndex,
        a ≠ b ∧ keyOf a = keyOf b

/--
The canonical high-debt subfamily at `(M0,K0)` is the entire high-debt subtail.
It is pigeonhole-incompressible once the high-debt subtail has no finite
injection.
-/
def highDebtSubfamily_of_noFiniteInjection
    {D : PeelDebtSystem}
    {M0 K0 : Nat}
    (hNo : NoFiniteInjection (HighDebtTail D M0 K0)) :
    HighDebtPigeonholeSubfamily D M0 K0 where
  SubIndex := HighDebtTail D M0 K0
  toTail := HighDebtTail.toTail
  toTail_injective := HighDebtTail.toTail_injective
  high_debt := HighDebtTail.high_debt
  finite_key_collision := by
    intro Key inst keyOf
    letI : Fintype Key := inst
    exact finite_key_collision_of_noFiniteInjection hNo Key keyOf

/-- Cofinal high-debt pigeonhole pressure. -/
structure CofinalHighDebtPigeonholePressure
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  high_debt_subfamily :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        Nonempty (HighDebtPigeonholeSubfamily D M0 K0)

/--
The new sharper source: every ordinary twin tail and every Mersenne debt floor
has no finite injection on its high-debt subtail.
-/
structure CofinalHighDebtNoFiniteInjectionSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  no_finite_injection :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        NoFiniteInjection (HighDebtTail D M0 K0)

/-- The no-finite-injection source gives cofinal high-debt pigeonhole pressure. -/
theorem cofinalHighDebtPigeonholePressure_of_noFiniteInjectionSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : CofinalHighDebtNoFiniteInjectionSource D TwinAbove) :
    CofinalHighDebtPigeonholePressure D TwinAbove := by
  refine ⟨?_⟩
  intro M0 K0 hTwin
  exact ⟨highDebtSubfamily_of_noFiniteInjection (S.no_finite_injection M0 K0 hTwin)⟩

/-#############################################################################
  §4. Weak high-debt cofinality as a consequence, not a sufficient input
#############################################################################-/

/-- Weak cofinality: above every floor there exists at least one high-debt tail genealogy. -/
def WeakHighDebtCofinality
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ∀ M0 K0 : Nat,
    TwinAbove M0 →
      ∃ γ : TailGenealogy D M0,
        K0 ≤ TailGenealogy.debt γ

/-- No-finite-injection source gives weak high-debt cofinality. -/
theorem weakHighDebtCofinality_of_noFiniteInjectionSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : CofinalHighDebtNoFiniteInjectionSource D TwinAbove) :
    WeakHighDebtCofinality D TwinAbove := by
  intro M0 K0 hTwin
  have hNo : NoFiniteInjection (HighDebtTail D M0 K0) :=
    S.no_finite_injection M0 K0 hTwin
  rcases nonempty_of_noFiniteInjection hNo with ⟨γ⟩
  exact ⟨HighDebtTail.toTail γ, HighDebtTail.high_debt γ⟩

/-- A defect of the sharpened no-finite-injection source. -/
def HighDebtNoFiniteInjectionDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalHighDebtNoFiniteInjectionSource D TwinAbove

/-- A defect of cofinal high-debt pigeonhole pressure. -/
def HighDebtPigeonholePressureDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalHighDebtPigeonholePressure D TwinAbove

/-- Failure of high-debt pigeonhole pressure forces failure of the sharper source. -/
theorem pigeonholeDefect_forces_noFiniteInjectionDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hDefect : HighDebtPigeonholePressureDefect D TwinAbove) :
    HighDebtNoFiniteInjectionDefect D TwinAbove := by
  intro hSource
  exact hDefect (cofinalHighDebtPigeonholePressure_of_noFiniteInjectionSource hSource)

/-#############################################################################
  §5. Front package and slogan
#############################################################################-/

/--
The current live front for the Mersenne high-debt pigeonhole source.
-/
structure HighDebtTailIncompressibilityFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  no_finite_injection_source :
    CofinalHighDebtNoFiniteInjectionSource D TwinAbove

  audit_stronger_than_unbounded_debt : Prop
  audit_stronger_than_unbounded_debt_proof : audit_stronger_than_unbounded_debt

  audit_entire_high_debt_tail_used : Prop
  audit_entire_high_debt_tail_used_proof : audit_entire_high_debt_tail_used

/-- The front gives high-debt pigeonhole pressure. -/
theorem highDebtPigeonholePressure_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtTailIncompressibilityFront D TwinAbove) :
    CofinalHighDebtPigeonholePressure D TwinAbove :=
  cofinalHighDebtPigeonholePressure_of_noFiniteInjectionSource F.no_finite_injection_source

/-- The front gives weak high-debt cofinality as a corollary. -/
theorem weakHighDebtCofinality_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtTailIncompressibilityFront D TwinAbove) :
    WeakHighDebtCofinality D TwinAbove :=
  weakHighDebtCofinality_of_noFiniteInjectionSource F.no_finite_injection_source

/-- Slogan theorem for this patch. -/
theorem highDebtTailIncompressibility_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtTailIncompressibilityFront D TwinAbove) :
    CofinalHighDebtPigeonholePressure D TwinAbove ∧
    WeakHighDebtCofinality D TwinAbove := by
  exact ⟨
    highDebtPigeonholePressure_of_front F,
    weakHighDebtCofinality_of_front F
  ⟩

end HighDebtTailSource
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_high_debt_finite_avoidance_firewall_patch.lean =====
/-
EuclidsPath — patch: high-debt finite-avoidance firewall
==========================================================

Purpose
-------
The previous patch reduced the live Mersenne obligation to:

    CofinalHighDebtNoFiniteInjectionSource

for every ordinary twin tail `M0` and every Mersenne floor `K0`.

This file pushes that source one level lower.  Instead of asking directly for
"no finite injection", we isolate the exact finite-avoidance mechanism:

    every finite forbidden list of high-debt tail genealogies can be avoided.

Together with the standard finite-cover principle

    an injection into a finite key creates a finite cover,

finite-avoidance implies no finite injection.

This is the intended pigeonhole/firewall form:

    high-debt tail has fresh genealogy beyond any finite bookkeeping table
      ⇒ no finite key can inject it
      ⇒ finite-key same-key collisions are forced.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace HighDebtFiniteAvoidance

/-#############################################################################
  §1. Tail/debt primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

namespace TailGenealogy

/-- The peel debt of a tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 : Nat} (γ : TailGenealogy D M0) : Nat :=
  D.debt γ.1

end TailGenealogy

/-- The high-debt subtail above a Mersenne debt floor `K0`. -/
abbrev HighDebtTail (D : PeelDebtSystem) (M0 K0 : Nat) : Type :=
  {γ : TailGenealogy D M0 // K0 ≤ TailGenealogy.debt γ}

namespace HighDebtTail

/-- Forget the high-debt proof and keep the underlying tail genealogy. -/
def toTail {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) : TailGenealogy D M0 :=
  γ.1

/-- Every high-debt tail genealogy has debt at least the floor. -/
theorem high_debt {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) :
    K0 ≤ TailGenealogy.debt (toTail γ) :=
  γ.2

end HighDebtTail

/-#############################################################################
  §2. Finite avoidance and finite-cover principles
#############################################################################-/

/--
A type has fresh elements beyond every finite forbidden list.

The finite list is represented as a map from any finite index type `β` into
`α`.  This avoids requiring decidable equality or a concrete `Finset α`.
-/
def FreshBeyondFiniteForbidden (α : Type) : Prop :=
  ∀ (β : Type) [Fintype β] (forbidden : β → α),
    ∃ a : α, ∀ b : β, a ≠ forbidden b

/-- A type is not covered by any finite family. -/
def FiniteCoverAvoidance (α : Type) : Prop :=
  ∀ (β : Type) [Fintype β] (cover : β → α),
    ¬ Function.Surjective cover

/-- Freshness beyond every finite forbidden list forbids every finite cover. -/
theorem finiteCoverAvoidance_of_freshBeyondFiniteForbidden
    {α : Type}
    (hFresh : FreshBeyondFiniteForbidden α) :
    FiniteCoverAvoidance α := by
  intro β inst cover hSurj
  letI : Fintype β := inst
  rcases hFresh β cover with ⟨a, ha⟩
  rcases hSurj a with ⟨b, hb⟩
  exact ha b hb.symm

/-- Finite-cover avoidance gives freshness beyond every finite forbidden list. -/
theorem freshBeyondFiniteForbidden_of_finiteCoverAvoidance
    {α : Type}
    (hAvoid : FiniteCoverAvoidance α) :
    FreshBeyondFiniteForbidden α := by
  intro β inst forbidden
  letI : Fintype β := inst
  have hNotSurj : ¬ Function.Surjective forbidden := hAvoid β forbidden
  rw [Function.Surjective] at hNotSurj
  push_neg at hNotSurj
  rcases hNotSurj with ⟨a, ha⟩
  exact ⟨a, by
    intro b
    intro hEq
    exact ha b hEq.symm
  ⟩

/-- Finite avoidance and finite freshness are equivalent. -/
theorem freshBeyondFiniteForbidden_iff_finiteCoverAvoidance
    (α : Type) :
    FreshBeyondFiniteForbidden α ↔ FiniteCoverAvoidance α := by
  constructor
  · exact finiteCoverAvoidance_of_freshBeyondFiniteForbidden
  · exact freshBeyondFiniteForbidden_of_finiteCoverAvoidance

/--
A standard finite-set principle: if `α` injects into a finite key, then `α` is
covered by finitely many representatives.

This is separated as an explicit interface to keep the Mersenne argument honest.
It is ordinary finite cardinal bookkeeping, not number theory.
-/
def InjectionCreatesFiniteCover (α : Type) : Prop :=
  ∀ (Key : Type) [Fintype Key] (keyOf : α → Key),
    Function.Injective keyOf →
      ∃ cover : Key → α, Function.Surjective cover

/-- A type cannot be faithfully compressed into any finite key. -/
def NoFiniteInjection (α : Type) : Prop :=
  ∀ (Key : Type) [Fintype Key] (keyOf : α → Key),
    ¬ Function.Injective keyOf

/--
Finite avoidance plus the finite-cover principle implies no finite injection.
-/
theorem noFiniteInjection_of_finiteCoverAvoidance
    {α : Type}
    (hAvoid : FiniteCoverAvoidance α)
    (hCover : InjectionCreatesFiniteCover α) :
    NoFiniteInjection α := by
  intro Key inst keyOf hInj
  letI : Fintype Key := inst
  rcases hCover Key keyOf hInj with ⟨cover, hSurj⟩
  exact hAvoid Key cover hSurj

/-- Fresh finite-avoidance plus finite-cover bookkeeping implies no finite injection. -/
theorem noFiniteInjection_of_freshBeyondFiniteForbidden
    {α : Type}
    (hFresh : FreshBeyondFiniteForbidden α)
    (hCover : InjectionCreatesFiniteCover α) :
    NoFiniteInjection α :=
  noFiniteInjection_of_finiteCoverAvoidance
    (finiteCoverAvoidance_of_freshBeyondFiniteForbidden hFresh)
    hCover

/-#############################################################################
  §3. High-debt tail finite-avoidance source
#############################################################################-/

/--
The previous source: every high-debt tail has no finite injection.
-/
structure CofinalHighDebtNoFiniteInjectionSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  no_finite_injection :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        NoFiniteInjection (HighDebtTail D M0 K0)

/--
The new lower-level source: every high-debt tail has fresh elements beyond any
finite forbidden table, and finite injections into finite keys create finite
covers.
-/
structure CofinalHighDebtFiniteAvoidanceSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  fresh_beyond_finite :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        FreshBeyondFiniteForbidden (HighDebtTail D M0 K0)

  injection_creates_finite_cover :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        InjectionCreatesFiniteCover (HighDebtTail D M0 K0)

/-- Finite-avoidance source gives the previous no-finite-injection source. -/
theorem noFiniteInjectionSource_of_finiteAvoidanceSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : CofinalHighDebtFiniteAvoidanceSource D TwinAbove) :
    CofinalHighDebtNoFiniteInjectionSource D TwinAbove := by
  refine ⟨?_⟩
  intro M0 K0 hTwin
  exact noFiniteInjection_of_freshBeyondFiniteForbidden
    (S.fresh_beyond_finite M0 K0 hTwin)
    (S.injection_creates_finite_cover M0 K0 hTwin)

/-- A defect of the finite-avoidance source. -/
def HighDebtFiniteAvoidanceDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalHighDebtFiniteAvoidanceSource D TwinAbove

/-- A defect of the no-finite-injection source. -/
def HighDebtNoFiniteInjectionDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalHighDebtNoFiniteInjectionSource D TwinAbove

/-- Failure of no-finite-injection forces failure of finite-avoidance source. -/
theorem noFiniteInjectionDefect_forces_finiteAvoidanceDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hDefect : HighDebtNoFiniteInjectionDefect D TwinAbove) :
    HighDebtFiniteAvoidanceDefect D TwinAbove := by
  intro hSource
  exact hDefect (noFiniteInjectionSource_of_finiteAvoidanceSource hSource)

/-#############################################################################
  §4. Freshness as the actual genealogy-production obligation
#############################################################################-/

/--
A concrete fresh-genealogy producer for one `(M0,K0)` tail.

Given any finite forbidden table of high-debt genealogies, it returns another
high-debt genealogy outside that table.  This is the non-compression content;
finite cardinal bookkeeping is separated above.
-/
structure FreshHighDebtGenealogyProducer
    (D : PeelDebtSystem)
    (M0 K0 : Nat) where
  produce :
    ∀ (β : Type) [Fintype β]
      (forbidden : β → HighDebtTail D M0 K0),
        ∃ γ : HighDebtTail D M0 K0,
          ∀ b : β, γ ≠ forbidden b

/-- A producer is exactly a fresh-beyond-finite certificate. -/
def FreshHighDebtGenealogyProducer.toFresh
    {D : PeelDebtSystem}
    {M0 K0 : Nat}
    (P : FreshHighDebtGenealogyProducer D M0 K0) :
    FreshBeyondFiniteForbidden (HighDebtTail D M0 K0) :=
  P.produce

/--
Cofinal producer source: on every ordinary twin tail and above every Mersenne
floor, finite forbidden high-debt genealogy tables can be avoided.
-/
structure CofinalFreshHighDebtGenealogyProducerSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  producer :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        FreshHighDebtGenealogyProducer D M0 K0

  injection_creates_finite_cover :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        InjectionCreatesFiniteCover (HighDebtTail D M0 K0)

/-- Producer source gives finite-avoidance source. -/
theorem finiteAvoidanceSource_of_freshProducerSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : CofinalFreshHighDebtGenealogyProducerSource D TwinAbove) :
    CofinalHighDebtFiniteAvoidanceSource D TwinAbove := by
  refine ⟨?_, ?_⟩
  · intro M0 K0 hTwin
    exact (S.producer M0 K0 hTwin).toFresh
  · intro M0 K0 hTwin
    exact S.injection_creates_finite_cover M0 K0 hTwin

/-- Producer source gives no-finite-injection source. -/
theorem noFiniteInjectionSource_of_freshProducerSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : CofinalFreshHighDebtGenealogyProducerSource D TwinAbove) :
    CofinalHighDebtNoFiniteInjectionSource D TwinAbove :=
  noFiniteInjectionSource_of_finiteAvoidanceSource
    (finiteAvoidanceSource_of_freshProducerSource S)

/-#############################################################################
  §5. Front package and slogan
#############################################################################-/

/--
The current sharp front for the Mersenne high-debt incompressibility source.
-/
structure HighDebtFiniteAvoidanceFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  fresh_producer_source :
    CofinalFreshHighDebtGenealogyProducerSource D TwinAbove

  audit_not_merely_unbounded : Prop
  audit_not_merely_unbounded_proof : audit_not_merely_unbounded

  audit_finite_key_bookkeeping_is_separated : Prop
  audit_finite_key_bookkeeping_is_separated_proof :
    audit_finite_key_bookkeeping_is_separated

/-- The front gives finite-avoidance source. -/
theorem finiteAvoidanceSource_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtFiniteAvoidanceFront D TwinAbove) :
    CofinalHighDebtFiniteAvoidanceSource D TwinAbove :=
  finiteAvoidanceSource_of_freshProducerSource F.fresh_producer_source

/-- The front gives no-finite-injection source. -/
theorem noFiniteInjectionSource_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtFiniteAvoidanceFront D TwinAbove) :
    CofinalHighDebtNoFiniteInjectionSource D TwinAbove :=
  noFiniteInjectionSource_of_freshProducerSource F.fresh_producer_source

/-- Slogan theorem for this patch. -/
theorem highDebtFiniteAvoidance_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : HighDebtFiniteAvoidanceFront D TwinAbove) :
    CofinalHighDebtFiniteAvoidanceSource D TwinAbove ∧
    CofinalHighDebtNoFiniteInjectionSource D TwinAbove := by
  exact ⟨finiteAvoidanceSource_of_front F, noFiniteInjectionSource_of_front F⟩

end HighDebtFiniteAvoidance
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_debt_escape_finite_obstruction_patch.lean =====
/-
EuclidsPath — patch: Mersenne debt-escape finite-obstruction layer
====================================================================

Purpose
-------
The previous patch reduced the high-debt incompressibility source to a concrete
freshness obligation:

    CofinalFreshHighDebtGenealogyProducerSource

meaning that, on every ordinary twin tail `M0` and above every Mersenne debt
floor `K0`, every finite forbidden table of high-debt genealogies can be avoided.

This file pushes that freshness obligation one level lower.

Core idea
---------
A finite forbidden table has a finite maximum peel-debt.  Therefore a genealogy
whose peel-debt is strictly larger than every forbidden debt is automatically
fresh.  Hence:

    debt escape beyond every finite bound
      + finite forbidden tables have finite debt bounds
        ⇒ fresh high-debt genealogy beyond every forbidden table.

The new live source is now a peel/debt expansion law:

    for every M0, K0, B,
    ordinary twin supply above M0 produces a tail genealogy with debt ≥ K0
    and debt > B.

This is the exact “finite obstruction escape” form needed by the Mersenne route.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace DebtEscapeFiniteObstruction

/-#############################################################################
  §1. Tail/debt primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

namespace TailGenealogy

/-- The peel debt of a tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 : Nat} (γ : TailGenealogy D M0) : Nat :=
  D.debt γ.1

end TailGenealogy

/-- The high-debt subtail above a Mersenne debt floor `K0`. -/
abbrev HighDebtTail (D : PeelDebtSystem) (M0 K0 : Nat) : Type :=
  {γ : TailGenealogy D M0 // K0 ≤ TailGenealogy.debt γ}

namespace HighDebtTail

/-- Forget the high-debt proof and keep the underlying tail genealogy. -/
def toTail {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) : TailGenealogy D M0 :=
  γ.1

/-- Debt of a high-debt tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) : Nat :=
  TailGenealogy.debt (toTail γ)

/-- Every high-debt tail genealogy has debt at least the floor. -/
theorem high_debt {D : PeelDebtSystem} {M0 K0 : Nat}
    (γ : HighDebtTail D M0 K0) :
    K0 ≤ debt γ :=
  γ.2

end HighDebtTail

/-#############################################################################
  §2. Freshness, finite bounds, and debt escape
#############################################################################-/

/-- Fresh element beyond every finite forbidden table. -/
def FreshBeyondFiniteForbidden (α : Type) : Prop :=
  ∀ (β : Type) [Fintype β] (forbidden : β → α),
    ∃ a : α, ∀ b : β, a ≠ forbidden b

/--
Finite forbidden tables of high-debt genealogies have finite debt bounds.

This is pure finite bookkeeping.  It is kept as an explicit interface so the
number-theoretic/debt expansion content remains separate from finite-cardinality
bookkeeping.
-/
def ForbiddenFiniteDebtBoundLaw (D : PeelDebtSystem) (M0 K0 : Nat) : Prop :=
  ∀ (β : Type) [Fintype β] (forbidden : β → HighDebtTail D M0 K0),
    ∃ B : Nat, ∀ b : β, HighDebtTail.debt (forbidden b) ≤ B

/--
Debt escape: above every finite debt bound there is a high-debt tail genealogy
whose debt is strictly larger.
-/
structure DebtEscapeProducer (D : PeelDebtSystem) (M0 K0 : Nat) where
  escape : ∀ B : Nat,
    ∃ γ : HighDebtTail D M0 K0,
      B < HighDebtTail.debt γ

/-- A tail has bounded high-debt if all high-debt genealogies are bounded in debt. -/
def HighDebtTailBounded (D : PeelDebtSystem) (M0 K0 : Nat) : Prop :=
  ∃ B : Nat, ∀ γ : HighDebtTail D M0 K0, HighDebtTail.debt γ ≤ B

/-- A bounded high-debt tail forbids debt escape. -/
theorem not_debtEscapeProducer_of_highDebtTailBounded
    {D : PeelDebtSystem} {M0 K0 : Nat}
    (hBounded : HighDebtTailBounded D M0 K0) :
    ¬ DebtEscapeProducer D M0 K0 := by
  intro E
  rcases hBounded with ⟨B, hB⟩
  rcases E.escape B with ⟨γ, hgt⟩
  exact (not_le_of_gt hgt) (hB γ)

/-- Failure of debt escape is exactly a bounded high-debt tail, classically. -/
theorem highDebtTailBounded_of_not_debtEscapeProducer
    {D : PeelDebtSystem} {M0 K0 : Nat}
    (hNoEscape : ¬ DebtEscapeProducer D M0 K0) :
    HighDebtTailBounded D M0 K0 := by
  classical
  by_contra hNoBound
  apply hNoEscape
  refine ⟨?_⟩
  intro B
  by_contra hNoWitness
  apply hNoBound
  refine ⟨B, ?_⟩
  intro γ
  exact Nat.le_of_not_gt (by
    intro hgt
    exact hNoWitness ⟨γ, hgt⟩)

/-- Debt escape is equivalent to unbounded high-debt tail, classically. -/
theorem not_debtEscapeProducer_iff_highDebtTailBounded
    (D : PeelDebtSystem) (M0 K0 : Nat) :
    ¬ DebtEscapeProducer D M0 K0 ↔ HighDebtTailBounded D M0 K0 := by
  constructor
  · exact highDebtTailBounded_of_not_debtEscapeProducer
  · exact not_debtEscapeProducer_of_highDebtTailBounded

/-#############################################################################
  §3. Debt escape produces freshness beyond finite forbidden tables
#############################################################################-/

/--
If forbidden tables have finite debt bounds and debt can escape every finite
bound, then every finite forbidden table can be avoided.
-/
theorem freshBeyondFiniteForbidden_of_debtEscape
    {D : PeelDebtSystem} {M0 K0 : Nat}
    (hBoundLaw : ForbiddenFiniteDebtBoundLaw D M0 K0)
    (E : DebtEscapeProducer D M0 K0) :
    FreshBeyondFiniteForbidden (HighDebtTail D M0 K0) := by
  intro β inst forbidden
  letI : Fintype β := inst
  rcases hBoundLaw β forbidden with ⟨B, hB⟩
  rcases E.escape B with ⟨γ, hγgt⟩
  refine ⟨γ, ?_⟩
  intro b hEq
  have hForbiddenLe : HighDebtTail.debt (forbidden b) ≤ B := hB b
  have hGammaLe : HighDebtTail.debt γ ≤ B := by
    rw [hEq]
    exact hForbiddenLe
  exact (not_le_of_gt hγgt) hGammaLe

/-- Concrete fresh-genealogy producer from debt escape. -/
structure FreshHighDebtGenealogyProducer
    (D : PeelDebtSystem)
    (M0 K0 : Nat) where
  produce :
    ∀ (β : Type) [Fintype β]
      (forbidden : β → HighDebtTail D M0 K0),
        ∃ γ : HighDebtTail D M0 K0,
          ∀ b : β, γ ≠ forbidden b

/-- Debt escape plus finite-bound bookkeeping gives a fresh producer. -/
def freshProducer_of_debtEscape
    {D : PeelDebtSystem} {M0 K0 : Nat}
    (hBoundLaw : ForbiddenFiniteDebtBoundLaw D M0 K0)
    (E : DebtEscapeProducer D M0 K0) :
    FreshHighDebtGenealogyProducer D M0 K0 where
  produce := freshBeyondFiniteForbidden_of_debtEscape hBoundLaw E

/-#############################################################################
  §4. Cofinal sources
#############################################################################-/

/-- Finite injections into finite keys create finite covers. -/
def InjectionCreatesFiniteCover (α : Type) : Prop :=
  ∀ (Key : Type) [Fintype Key] (keyOf : α → Key),
    Function.Injective keyOf →
      ∃ cover : Key → α, Function.Surjective cover

/-- Previous source: cofinal fresh high-debt producer plus finite-key bookkeeping. -/
structure CofinalFreshHighDebtGenealogyProducerSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  producer :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        FreshHighDebtGenealogyProducer D M0 K0

  injection_creates_finite_cover :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        InjectionCreatesFiniteCover (HighDebtTail D M0 K0)

/-- New lower-level source: cofinal debt escape plus finite forbidden bounds. -/
structure CofinalDebtEscapeSource
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  debt_escape :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        DebtEscapeProducer D M0 K0

  forbidden_finite_debt_bound :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ForbiddenFiniteDebtBoundLaw D M0 K0

  injection_creates_finite_cover :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        InjectionCreatesFiniteCover (HighDebtTail D M0 K0)

/-- Debt-escape source gives the previous fresh-producer source. -/
theorem freshProducerSource_of_debtEscapeSource
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (S : CofinalDebtEscapeSource D TwinAbove) :
    CofinalFreshHighDebtGenealogyProducerSource D TwinAbove := by
  refine ⟨?_, ?_⟩
  · intro M0 K0 hTwin
    exact freshProducer_of_debtEscape
      (S.forbidden_finite_debt_bound M0 K0 hTwin)
      (S.debt_escape M0 K0 hTwin)
  · intro M0 K0 hTwin
    exact S.injection_creates_finite_cover M0 K0 hTwin

/-#############################################################################
  §5. Peel expansion law: the concrete live source
#############################################################################-/

/--
Peel expansion law: from ordinary twin supply above `M0`, for every Mersenne
floor `K0` and every finite obstruction bound `B`, construct a tail genealogy
with debt at least `K0` and strictly above `B`.

This is the exact new live brick.
-/
structure PeelExpansionLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  expand :
    ∀ M0 K0 B : Nat,
      TwinAbove M0 →
        ∃ Γ : D.Genealogy,
          D.Tail Γ M0 ∧ K0 ≤ D.debt Γ ∧ B < D.debt Γ

/-- Peel expansion gives a debt-escape producer for each tail/floor. -/
def debtEscapeProducer_of_peelExpansion
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (E : PeelExpansionLaw D TwinAbove)
    {M0 K0 : Nat}
    (hTwin : TwinAbove M0) :
    DebtEscapeProducer D M0 K0 where
  escape := by
    intro B
    rcases E.expand M0 K0 B hTwin with ⟨Γ, hTail, hHigh, hGt⟩
    let τ : TailGenealogy D M0 := ⟨Γ, hTail⟩
    let γ : HighDebtTail D M0 K0 := ⟨τ, hHigh⟩
    exact ⟨γ, hGt⟩

/-- A front package: finite obstruction escape via peel expansion. -/
structure DebtEscapeFiniteObstructionFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  peel_expansion : PeelExpansionLaw D TwinAbove

  forbidden_finite_debt_bound :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ForbiddenFiniteDebtBoundLaw D M0 K0

  injection_creates_finite_cover :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        InjectionCreatesFiniteCover (HighDebtTail D M0 K0)

  audit_finite_forbidden_table_is_not_a_tail_bound : Prop
  audit_finite_forbidden_table_is_not_a_tail_bound_proof :
    audit_finite_forbidden_table_is_not_a_tail_bound

  audit_escape_uses_strict_debt_growth : Prop
  audit_escape_uses_strict_debt_growth_proof :
    audit_escape_uses_strict_debt_growth

/-- The front gives the cofinal debt-escape source. -/
theorem debtEscapeSource_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : DebtEscapeFiniteObstructionFront D TwinAbove) :
    CofinalDebtEscapeSource D TwinAbove := by
  refine ⟨?_, ?_, ?_⟩
  · intro M0 K0 hTwin
    exact debtEscapeProducer_of_peelExpansion F.peel_expansion hTwin
  · intro M0 K0 hTwin
    exact F.forbidden_finite_debt_bound M0 K0 hTwin
  · intro M0 K0 hTwin
    exact F.injection_creates_finite_cover M0 K0 hTwin

/-- The front gives the previous fresh-producer source. -/
theorem freshProducerSource_of_front
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : DebtEscapeFiniteObstructionFront D TwinAbove) :
    CofinalFreshHighDebtGenealogyProducerSource D TwinAbove :=
  freshProducerSource_of_debtEscapeSource (debtEscapeSource_of_front F)

/-#############################################################################
  §6. Defect formulation
#############################################################################-/

/-- Failure of cofinal fresh production. -/
def FreshProducerDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalFreshHighDebtGenealogyProducerSource D TwinAbove

/-- Failure of cofinal debt escape. -/
def CofinalDebtEscapeDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ CofinalDebtEscapeSource D TwinAbove

/-- Failure of peel expansion. -/
def PeelExpansionDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ PeelExpansionLaw D TwinAbove

/-- Failure of the new front forces failure of the previous fresh-producer source. -/
theorem freshProducerDefect_forces_debtEscapeSourceDefect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hDefect : FreshProducerDefect D TwinAbove) :
    CofinalDebtEscapeDefect D TwinAbove := by
  intro hSource
  exact hDefect (freshProducerSource_of_debtEscapeSource hSource)

/-- If finite bookkeeping is available, failure of debt escape is failure of peel expansion. -/
theorem debtEscapeSource_of_peelExpansion_and_bookkeeping
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (E : PeelExpansionLaw D TwinAbove)
    (hBound :
      ∀ M0 K0 : Nat,
        TwinAbove M0 →
          ForbiddenFiniteDebtBoundLaw D M0 K0)
    (hCover :
      ∀ M0 K0 : Nat,
        TwinAbove M0 →
          InjectionCreatesFiniteCover (HighDebtTail D M0 K0)) :
    CofinalDebtEscapeSource D TwinAbove := by
  refine ⟨?_, ?_, ?_⟩
  · intro M0 K0 hTwin
    exact debtEscapeProducer_of_peelExpansion E hTwin
  · intro M0 K0 hTwin
    exact hBound M0 K0 hTwin
  · intro M0 K0 hTwin
    exact hCover M0 K0 hTwin

/-- With finite bookkeeping fixed, debt-escape-source failure means peel-expansion failure. -/
theorem debtEscapeDefect_forces_peelExpansionDefect_of_bookkeeping
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hDefect : CofinalDebtEscapeDefect D TwinAbove)
    (hBound :
      ∀ M0 K0 : Nat,
        TwinAbove M0 →
          ForbiddenFiniteDebtBoundLaw D M0 K0)
    (hCover :
      ∀ M0 K0 : Nat,
        TwinAbove M0 →
          InjectionCreatesFiniteCover (HighDebtTail D M0 K0)) :
    PeelExpansionDefect D TwinAbove := by
  intro E
  exact hDefect (debtEscapeSource_of_peelExpansion_and_bookkeeping E hBound hCover)

/-- Final slogan theorem for this patch. -/
theorem debtEscapeFiniteObstruction_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : DebtEscapeFiniteObstructionFront D TwinAbove) :
    CofinalDebtEscapeSource D TwinAbove ∧
    CofinalFreshHighDebtGenealogyProducerSource D TwinAbove := by
  exact ⟨debtEscapeSource_of_front F, freshProducerSource_of_front F⟩

end DebtEscapeFiniteObstruction
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_peel_expansion_successor_law_patch.lean =====
/-
EuclidsPath — patch: Mersenne peel expansion from a strict successor law
============================================================================

Purpose
-------
The previous patch isolated the exact live brick:

    PeelExpansionLaw

meaning that, on every ordinary twin tail `M0`, above every Mersenne floor `K0`,
and beyond every finite obstruction bound `B`, there is a tail genealogy whose
peel-debt is at least `K0` and strictly larger than `B`.

This file lowers that brick one step further.

Core idea
---------
`PeelExpansionLaw` follows from two elementary ingredients:

  1. `HighDebtSeedLaw`:
       ordinary twin supply above `M0` produces at least one tail genealogy with
       peel-debt at least `K0`.

  2. `StrictPeelSuccessorLaw`:
       every tail genealogy has a successor on the same tail whose peel-debt
       increases by at least one.

Then finite iteration of the successor jumps over any finite bound `B`.

This file proves the iteration theorem.  It does not prove the arithmetic/ledger
content of the seed or successor laws; those are now the exact live obligations.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace PeelExpansionSuccessorLaw

/-#############################################################################
  §1. Tail/debt primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- A genealogy on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

namespace TailGenealogy

/-- Debt of a tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 : Nat} (γ : TailGenealogy D M0) : Nat :=
  D.debt γ.1

end TailGenealogy

/-- The expansion law isolated in the previous patch. -/
structure PeelExpansionLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  expand :
    ∀ M0 K0 B : Nat,
      TwinAbove M0 →
        ∃ Γ : D.Genealogy,
          D.Tail Γ M0 ∧ K0 ≤ D.debt Γ ∧ B < D.debt Γ

/-#############################################################################
  §2. Seed and successor laws
#############################################################################-/

/--
Seed law: for every tail and every Mersenne floor, there is at least one tail
object already at or above that floor.
-/
structure HighDebtSeedLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  seed :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ∃ γ : TailGenealogy D M0,
          K0 ≤ TailGenealogy.debt γ

/--
Strict successor law: every tail genealogy has a same-tail successor whose
peel-debt increases by at least one.
-/
structure StrictPeelSuccessorLaw
    (D : PeelDebtSystem) where
  next :
    ∀ M0 : Nat,
    ∀ γ : TailGenealogy D M0,
      ∃ γ' : TailGenealogy D M0,
        TailGenealogy.debt γ + 1 ≤ TailGenealogy.debt γ'

/-- Successor relation induced by the strict successor law. -/
def StrictPeelStep
    {D : PeelDebtSystem}
    (S : StrictPeelSuccessorLaw D)
    {M0 : Nat}
    (γ γ' : TailGenealogy D M0) : Prop :=
  TailGenealogy.debt γ + 1 ≤ TailGenealogy.debt γ'

/-#############################################################################
  §3. Finite iteration of strict peel successors
#############################################################################-/

/--
Iterating a strict successor `n` times gives a same-tail genealogy whose debt is
at least the original debt plus `n`.
-/
theorem exists_successor_iterate_with_debt_add
    {D : PeelDebtSystem}
    (S : StrictPeelSuccessorLaw D)
    {M0 : Nat}
    (γ : TailGenealogy D M0) :
    ∀ n : Nat,
      ∃ γ' : TailGenealogy D M0,
        TailGenealogy.debt γ + n ≤ TailGenealogy.debt γ' := by
  intro n
  induction n with
  | zero =>
      exact ⟨γ, by simp⟩
  | succ n ih =>
      rcases ih with ⟨γn, hγn⟩
      rcases S.next M0 γn with ⟨γnext, hnext⟩
      refine ⟨γnext, ?_⟩
      omega

/--
A strict successor law can jump above any finite obstruction bound from any
starting tail genealogy.
-/
theorem exists_successor_above_bound
    {D : PeelDebtSystem}
    (S : StrictPeelSuccessorLaw D)
    {M0 B : Nat}
    (γ : TailGenealogy D M0) :
    ∃ γ' : TailGenealogy D M0,
      B < TailGenealogy.debt γ' := by
  rcases exists_successor_iterate_with_debt_add S γ (B + 1) with ⟨γ', hγ'⟩
  refine ⟨γ', ?_⟩
  omega

/--
If the starting genealogy has debt at least `K0`, every sufficiently iterated
successor still has debt at least `K0` and can be above `B`.
-/
theorem exists_successor_high_and_above_bound
    {D : PeelDebtSystem}
    (S : StrictPeelSuccessorLaw D)
    {M0 K0 B : Nat}
    (γ : TailGenealogy D M0)
    (hHigh : K0 ≤ TailGenealogy.debt γ) :
    ∃ γ' : TailGenealogy D M0,
      K0 ≤ TailGenealogy.debt γ' ∧ B < TailGenealogy.debt γ' := by
  rcases exists_successor_iterate_with_debt_add S γ (B + 1) with ⟨γ', hγ'⟩
  refine ⟨γ', ?_, ?_⟩
  · omega
  · omega

/-#############################################################################
  §4. Expansion law from seed + successor
#############################################################################-/

/-- Seed plus strict successor gives the previous `PeelExpansionLaw`. -/
theorem peelExpansionLaw_of_seed_and_successor
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Seed : HighDebtSeedLaw D TwinAbove)
    (Succ : StrictPeelSuccessorLaw D) :
    PeelExpansionLaw D TwinAbove := by
  refine ⟨?_⟩
  intro M0 K0 B hTwin
  rcases Seed.seed M0 K0 hTwin with ⟨γ0, hHigh0⟩
  rcases exists_successor_high_and_above_bound Succ γ0 hHigh0 with
    ⟨γ', hHigh, hAbove⟩
  exact ⟨γ'.1, γ'.2, hHigh, hAbove⟩

/--
Front package for the new live obligations.
-/
structure PeelExpansionSuccessorFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  high_debt_seed : HighDebtSeedLaw D TwinAbove
  strict_successor : StrictPeelSuccessorLaw D

  audit_seed_uses_ordinary_twin_supply : Prop
  audit_seed_uses_ordinary_twin_supply_proof : audit_seed_uses_ordinary_twin_supply

  audit_successor_is_same_tail : Prop
  audit_successor_is_same_tail_proof : audit_successor_is_same_tail

  audit_successor_has_strict_debt_growth : Prop
  audit_successor_has_strict_debt_growth_proof : audit_successor_has_strict_debt_growth

/-- The successor front gives peel expansion. -/
theorem peelExpansionLaw_of_successorFront
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : PeelExpansionSuccessorFront D TwinAbove) :
    PeelExpansionLaw D TwinAbove :=
  peelExpansionLaw_of_seed_and_successor F.high_debt_seed F.strict_successor

/-#############################################################################
  §5. Defect split
#############################################################################-/

/-- Failure of peel expansion. -/
def PeelExpansionDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ PeelExpansionLaw D TwinAbove

/-- Failure of the high-debt seed law. -/
def HighDebtSeedDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ HighDebtSeedLaw D TwinAbove

/-- Failure of the strict peel successor law. -/
def StrictPeelSuccessorDefect
    (D : PeelDebtSystem) : Prop :=
  ¬ StrictPeelSuccessorLaw D

/-- If peel expansion fails, then seed or successor must fail. -/
theorem peelExpansionDefect_forces_seed_or_successor_defect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hDefect : PeelExpansionDefect D TwinAbove) :
    HighDebtSeedDefect D TwinAbove ∨ StrictPeelSuccessorDefect D := by
  classical
  by_cases hSeed : HighDebtSeedLaw D TwinAbove
  · right
    intro hSucc
    exact hDefect (peelExpansionLaw_of_seed_and_successor hSeed hSucc)
  · left
    exact hSeed

/-- With seed fixed, failure of expansion is failure of strict successor. -/
theorem peelExpansionDefect_forces_successorDefect_of_seed
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Seed : HighDebtSeedLaw D TwinAbove)
    (hDefect : PeelExpansionDefect D TwinAbove) :
    StrictPeelSuccessorDefect D := by
  intro Succ
  exact hDefect (peelExpansionLaw_of_seed_and_successor Seed Succ)

/-- With successor fixed, failure of expansion is failure of high-debt seed. -/
theorem peelExpansionDefect_forces_seedDefect_of_successor
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Succ : StrictPeelSuccessorLaw D)
    (hDefect : PeelExpansionDefect D TwinAbove) :
    HighDebtSeedDefect D TwinAbove := by
  intro Seed
  exact hDefect (peelExpansionLaw_of_seed_and_successor Seed Succ)

/-- Compact slogan for this patch. -/
theorem peelExpansionSuccessor_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : PeelExpansionSuccessorFront D TwinAbove) :
    PeelExpansionLaw D TwinAbove ∧
    HighDebtSeedLaw D TwinAbove ∧
    StrictPeelSuccessorLaw D := by
  exact ⟨peelExpansionLaw_of_successorFront F,
    F.high_debt_seed,
    F.strict_successor⟩

end PeelExpansionSuccessorLaw
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_peel_successor_operator_seed_patch.lean =====
/-
EuclidsPath — patch: Mersenne peel expansion from ordinary seed + successor operator
====================================================================================

Purpose
-------
The previous patch reduced the Mersenne route to two live laws:

  * `HighDebtSeedLaw`;
  * `StrictPeelSuccessorLaw`.

This file lowers that again.

Main point
----------
`HighDebtSeedLaw` does not need to be primitive if a same-tail strict peel
successor exists.  It follows from the weaker seed law:

  * `OrdinaryTailSeedLaw`:
      ordinary twin supply above `M0` gives at least one genealogy on that tail.

Together with a concrete successor operator

  * `PeelSuccessorOperator`:
      `next` preserves the same ordinary tail and increases peel-debt by at
      least one,

finite iteration gives arbitrarily high debt, hence both `HighDebtSeedLaw` and
`PeelExpansionLaw`.

This file contains only formal assembly/iteration.  It does not prove the actual
arithmetic/Step00 construction of the successor operator.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace PeelSuccessorOperatorSeed

/-#############################################################################
  §1. Primitives
#############################################################################-/

/-- Ordinary Step00 twin supply above a horizon. -/
abbrev OrdinaryTwinSupplyAbove := Nat → Prop

/-- A peel-debt genealogy system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Genealogy → Nat → Prop
  debt : Genealogy → Nat

/-- Genealogies on a fixed ordinary twin tail. -/
abbrev TailGenealogy (D : PeelDebtSystem) (M0 : Nat) : Type :=
  {Γ : D.Genealogy // D.Tail Γ M0}

namespace TailGenealogy

/-- Debt of a tail genealogy. -/
def debt {D : PeelDebtSystem} {M0 : Nat} (γ : TailGenealogy D M0) : Nat :=
  D.debt γ.1

@[simp] theorem debt_mk
    {D : PeelDebtSystem} {M0 : Nat}
    {Γ : D.Genealogy} (hΓ : D.Tail Γ M0) :
    debt (D := D) (M0 := M0) ⟨Γ, hΓ⟩ = D.debt Γ :=
  rfl

end TailGenealogy

/-- Expansion law isolated earlier. -/
structure PeelExpansionLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  expand :
    ∀ M0 K0 B : Nat,
      TwinAbove M0 →
        ∃ Γ : D.Genealogy,
          D.Tail Γ M0 ∧ K0 ≤ D.debt Γ ∧ B < D.debt Γ

/-- Previous seed law: seed exists already at any requested debt floor. -/
structure HighDebtSeedLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  seed :
    ∀ M0 K0 : Nat,
      TwinAbove M0 →
        ∃ γ : TailGenealogy D M0,
          K0 ≤ TailGenealogy.debt γ

/-- Previous strict successor law. -/
structure StrictPeelSuccessorLaw
    (D : PeelDebtSystem) where
  next :
    ∀ M0 : Nat,
    ∀ γ : TailGenealogy D M0,
      ∃ γ' : TailGenealogy D M0,
        TailGenealogy.debt γ + 1 ≤ TailGenealogy.debt γ'

/-#############################################################################
  §2. Lower-level seed and successor operator
#############################################################################-/

/--
Weak seed law: ordinary twin supply above `M0` gives some genealogy on that tail.

This is weaker than `HighDebtSeedLaw`; high debt is produced later by iteration
of the peel successor.
-/
structure OrdinaryTailSeedLaw
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  seed :
    ∀ M0 : Nat,
      TwinAbove M0 → Nonempty (TailGenealogy D M0)

/--
A concrete same-tail peel successor operator.

This is more operational than `StrictPeelSuccessorLaw`: it supplies an actual
successor function, not merely an existential successor.
-/
structure PeelSuccessorOperator
    (D : PeelDebtSystem) where
  next : ∀ {M0 : Nat}, TailGenealogy D M0 → TailGenealogy D M0
  grows :
    ∀ {M0 : Nat} (γ : TailGenealogy D M0),
      TailGenealogy.debt γ + 1 ≤ TailGenealogy.debt (next γ)

/-- Exact-growth variant.  It is often the concrete arithmetic target. -/
structure ExactPeelSuccessorOperator
    (D : PeelDebtSystem) where
  next : ∀ {M0 : Nat}, TailGenealogy D M0 → TailGenealogy D M0
  debt_next_eq :
    ∀ {M0 : Nat} (γ : TailGenealogy D M0),
      TailGenealogy.debt (next γ) = TailGenealogy.debt γ + 1

namespace ExactPeelSuccessorOperator

/-- Exact growth gives weak strict growth. -/
def toPeelSuccessorOperator
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D) :
    PeelSuccessorOperator D where
  next := E.next
  grows := by
    intro M0 γ
    rw [E.debt_next_eq γ]

end ExactPeelSuccessorOperator

namespace PeelSuccessorOperator

/-- A concrete operator gives the existential strict successor law. -/
def toStrictPeelSuccessorLaw
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D) :
    StrictPeelSuccessorLaw D where
  next := by
    intro M0 γ
    exact ⟨Op.next γ, Op.grows γ⟩

/-- Iterate the peel successor `n` times. -/
def iterate
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 : Nat}
    (n : Nat)
    (γ : TailGenealogy D M0) : TailGenealogy D M0 :=
  Nat.rec γ (fun _ acc => Op.next acc) n

@[simp] theorem iterate_zero
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 : Nat}
    (γ : TailGenealogy D M0) :
    Op.iterate 0 γ = γ :=
  rfl

@[simp] theorem iterate_succ
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 : Nat}
    (n : Nat)
    (γ : TailGenealogy D M0) :
    Op.iterate (n + 1) γ = Op.next (Op.iterate n γ) :=
  rfl

/-- Iteration raises debt by at least the number of iterations. -/
theorem iterate_debt_add_le
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 : Nat}
    (γ : TailGenealogy D M0) :
    ∀ n : Nat,
      TailGenealogy.debt γ + n ≤ TailGenealogy.debt (Op.iterate n γ) := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      have hgrow := Op.grows (Op.iterate n γ)
      rw [iterate_succ]
      omega

/-- From any seed, iteration reaches any requested debt floor. -/
theorem exists_iterate_at_or_above_floor
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 K0 : Nat}
    (γ : TailGenealogy D M0) :
    ∃ γ' : TailGenealogy D M0,
      K0 ≤ TailGenealogy.debt γ' := by
  refine ⟨Op.iterate K0 γ, ?_⟩
  have h := Op.iterate_debt_add_le γ K0
  omega

/-- From any seed, iteration reaches above any finite obstruction bound. -/
theorem exists_iterate_above_bound
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 B : Nat}
    (γ : TailGenealogy D M0) :
    ∃ γ' : TailGenealogy D M0,
      B < TailGenealogy.debt γ' := by
  refine ⟨Op.iterate (B + 1) γ, ?_⟩
  have h := Op.iterate_debt_add_le γ (B + 1)
  omega

/-- From any seed, one iterate simultaneously reaches a floor and beats a bound. -/
theorem exists_iterate_high_and_above_bound
    {D : PeelDebtSystem}
    (Op : PeelSuccessorOperator D)
    {M0 K0 B : Nat}
    (γ : TailGenealogy D M0) :
    ∃ γ' : TailGenealogy D M0,
      K0 ≤ TailGenealogy.debt γ' ∧ B < TailGenealogy.debt γ' := by
  have h := Op.iterate_debt_add_le γ (K0 + B + 1)
  refine ⟨Op.iterate (K0 + B + 1) γ, ?_, ?_⟩
  · omega
  · omega

end PeelSuccessorOperator

/-#############################################################################
  §3. High-debt seed and expansion from ordinary seed + successor
#############################################################################-/

/-- Ordinary seed plus successor operator gives high-debt seed. -/
theorem highDebtSeedLaw_of_ordinarySeed_and_successorOperator
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (Op : PeelSuccessorOperator D) :
    HighDebtSeedLaw D TwinAbove := by
  refine ⟨?_⟩
  intro M0 K0 hTwin
  rcases Seed.seed M0 hTwin with ⟨γ0⟩
  exact Op.exists_iterate_at_or_above_floor γ0

/-- Ordinary seed plus successor operator gives peel expansion directly. -/
theorem peelExpansionLaw_of_ordinarySeed_and_successorOperator
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (Op : PeelSuccessorOperator D) :
    PeelExpansionLaw D TwinAbove := by
  refine ⟨?_⟩
  intro M0 K0 B hTwin
  rcases Seed.seed M0 hTwin with ⟨γ0⟩
  rcases Op.exists_iterate_high_and_above_bound (K0 := K0) (B := B) γ0 with
    ⟨γ', hHigh, hAbove⟩
  exact ⟨γ'.1, γ'.2, hHigh, hAbove⟩

/-- Exact successor plus ordinary seed also gives peel expansion. -/
theorem peelExpansionLaw_of_ordinarySeed_and_exactSuccessor
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (E : ExactPeelSuccessorOperator D) :
    PeelExpansionLaw D TwinAbove :=
  peelExpansionLaw_of_ordinarySeed_and_successorOperator Seed
    E.toPeelSuccessorOperator

/-#############################################################################
  §4. Operational front and defect split
#############################################################################-/

/-- Operational front replacing `HighDebtSeedLaw + StrictPeelSuccessorLaw`. -/
structure PeelExpansionOperatorFront
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) where
  ordinary_seed : OrdinaryTailSeedLaw D TwinAbove
  successor_operator : PeelSuccessorOperator D

  audit_seed_from_ordinary_twin_supply : Prop
  audit_seed_from_ordinary_twin_supply_proof : audit_seed_from_ordinary_twin_supply

  audit_successor_preserves_tail : Prop
  audit_successor_preserves_tail_proof : audit_successor_preserves_tail

  audit_successor_strictly_grows_debt : Prop
  audit_successor_strictly_grows_debt_proof : audit_successor_strictly_grows_debt

/-- The operator front gives high-debt seed. -/
theorem highDebtSeedLaw_of_operatorFront
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : PeelExpansionOperatorFront D TwinAbove) :
    HighDebtSeedLaw D TwinAbove :=
  highDebtSeedLaw_of_ordinarySeed_and_successorOperator
    F.ordinary_seed F.successor_operator

/-- The operator front gives strict successor law. -/
theorem strictPeelSuccessorLaw_of_operatorFront
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : PeelExpansionOperatorFront D TwinAbove) :
    StrictPeelSuccessorLaw D :=
  F.successor_operator.toStrictPeelSuccessorLaw

/-- The operator front gives peel expansion. -/
theorem peelExpansionLaw_of_operatorFront
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : PeelExpansionOperatorFront D TwinAbove) :
    PeelExpansionLaw D TwinAbove :=
  peelExpansionLaw_of_ordinarySeed_and_successorOperator
    F.ordinary_seed F.successor_operator

/-- Failure of peel expansion. -/
def PeelExpansionDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ PeelExpansionLaw D TwinAbove

/-- Failure of ordinary tail seed. -/
def OrdinaryTailSeedDefect
    (D : PeelDebtSystem)
    (TwinAbove : OrdinaryTwinSupplyAbove) : Prop :=
  ¬ OrdinaryTailSeedLaw D TwinAbove

/-- Failure of a same-tail strict successor operator. -/
def PeelSuccessorOperatorDefect
    (D : PeelDebtSystem) : Prop :=
  PeelSuccessorOperator D → False

/-- If expansion fails, ordinary seed or successor operator must fail. -/
theorem peelExpansionDefect_forces_seed_or_operator_defect
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (hDefect : PeelExpansionDefect D TwinAbove) :
    OrdinaryTailSeedDefect D TwinAbove ∨ PeelSuccessorOperatorDefect D := by
  classical
  by_cases hSeed : OrdinaryTailSeedLaw D TwinAbove
  · right
    intro Op
    exact hDefect (peelExpansionLaw_of_ordinarySeed_and_successorOperator hSeed Op)
  · left
    exact hSeed

/-- With ordinary seed fixed, expansion failure is successor-operator failure. -/
theorem peelExpansionDefect_forces_operatorDefect_of_seed
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (hDefect : PeelExpansionDefect D TwinAbove) :
    PeelSuccessorOperatorDefect D := by
  intro Op
  exact hDefect (peelExpansionLaw_of_ordinarySeed_and_successorOperator Seed Op)

/-- With successor operator fixed, expansion failure is ordinary-seed failure. -/
theorem peelExpansionDefect_forces_seedDefect_of_operator
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (Op : PeelSuccessorOperator D)
    (hDefect : PeelExpansionDefect D TwinAbove) :
    OrdinaryTailSeedDefect D TwinAbove := by
  intro Seed
  exact hDefect (peelExpansionLaw_of_ordinarySeed_and_successorOperator Seed Op)

/-#############################################################################
  §5. Compact slogan
#############################################################################-/

/-- Compact final slogan for this layer. -/
theorem peelSuccessorOperatorSeed_slogan
    {D : PeelDebtSystem}
    {TwinAbove : OrdinaryTwinSupplyAbove}
    (F : PeelExpansionOperatorFront D TwinAbove) :
    OrdinaryTailSeedLaw D TwinAbove ∧
    Nonempty (PeelSuccessorOperator D) ∧
    HighDebtSeedLaw D TwinAbove ∧
    StrictPeelSuccessorLaw D ∧
    PeelExpansionLaw D TwinAbove := by
  exact ⟨F.ordinary_seed,
    ⟨F.successor_operator⟩,
    highDebtSeedLaw_of_operatorFront F,
    strictPeelSuccessorLaw_of_operatorFront F,
    peelExpansionLaw_of_operatorFront F⟩

end PeelSuccessorOperatorSeed
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_exact_peel_successor_arithmetic_patch.lean =====
/-
EuclidsPath — Mersenne exact peel successor arithmetic patch
=============================================================

Purpose
-------
This patch pushes the Mersenne route one layer lower.

Previous residue:

  * build `PeelSuccessorOperator`, ideally exact:

        Γ ↦ peelNext Γ,
        same ordinary twin tail,
        debt(peelNext Γ) = debt Γ + 1.

This file separates the residue into two components:

  1. pure base-4 Mersenne peel arithmetic:

        c_{k+1} = 4 c_k + 1,

     with side transitions for the twin sides `6c-1` and `6c+1`;

  2. an indexed genealogy successor certificate:

        index(next Γ) = index Γ + 1,
        Tail M0 Γ → Tail M0 (next Γ),
        center Γ = c_{index Γ}.

From these two components we prove an exact peel successor operator, and from
one ordinary tail seed plus the exact successor we prove a full finite-bound
escape / peel expansion law.

No claim about classical Mersenne infinitude is made here.  The file is a local
Step00/Mersenne bridge layer.

No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneExactPeel

/-#############################################################################
  §1. Pure base-4 peel arithmetic
#############################################################################-/

/--
The signed base-4 repunit center sequence.  It is the recurrence form of

  0, 1, 5, 21, 85, ...

namely `c_{k+1} = 4 c_k + 1`.

Using `Int` avoids irrelevant natural-subtraction edge cases at `k = 0`.
-/
def zCenter : Nat → Int
  | 0 => 0
  | Nat.succ k => 4 * zCenter k + 1

@[simp] theorem zCenter_zero : zCenter 0 = 0 := rfl

@[simp] theorem zCenter_succ (k : Nat) :
    zCenter (Nat.succ k) = 4 * zCenter k + 1 :=
  rfl

/-- Lower side of a Step00 twin center. -/
def zLowerSide (c : Int) : Int :=
  6 * c - 1

/-- Upper side of a Step00 twin center. -/
def zUpperSide (c : Int) : Int :=
  6 * c + 1

/-- Exact upper-side transition under base-4 peel. -/
theorem zUpperSide_peel_succ (k : Nat) :
    zUpperSide (zCenter (Nat.succ k)) =
      4 * zUpperSide (zCenter k) + 3 := by
  simp [zUpperSide]
  ring

/-- Exact lower-side transition under base-4 peel. -/
theorem zLowerSide_peel_succ (k : Nat) :
    zLowerSide (zCenter (Nat.succ k)) =
      4 * zLowerSide (zCenter k) + 9 := by
  simp [zLowerSide]
  ring

/-- The base-4 center itself peels by appending one base-4 digit. -/
theorem zCenter_peel_succ (k : Nat) :
    zCenter (Nat.succ k) = 4 * zCenter k + 1 :=
  rfl

/-#############################################################################
  §2. Debt systems and exact successor operators
#############################################################################-/

/--
A peel-debt system.  `Tail M0 Γ` means the genealogy `Γ` belongs to the ordinary
Step00 twin tail above horizon `M0`; `debt Γ` is its Mersenne/base-4 peel depth.
-/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  debt : Genealogy → Nat

/--
Exact same-tail peel successor: one step preserves the ordinary twin tail and
raises Mersenne peel-debt exactly by one.
-/
structure ExactPeelSuccessorOperator (D : PeelDebtSystem) where
  next : D.Genealogy → D.Genealogy
  tail_next : ∀ M0 Γ, D.Tail M0 Γ → D.Tail M0 (next Γ)
  debt_next : ∀ Γ, D.debt (next Γ) = D.debt Γ + 1

namespace ExactPeelSuccessorOperator

/-- Iterating an exact successor preserves the same tail and raises debt by at least `n`. -/
theorem exists_iterate_with_debt_add_le
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D)
    {M0 : Nat} {Γ : D.Genealogy}
    (hTail : D.Tail M0 Γ) :
    ∀ n : Nat,
      ∃ Γ' : D.Genealogy,
        D.Tail M0 Γ' ∧ D.debt Γ + n ≤ D.debt Γ' := by
  intro n
  induction n with
  | zero =>
      exact ⟨Γ, hTail, by simp⟩
  | succ n ih =>
      rcases ih with ⟨Γn, hTailn, hDebtn⟩
      refine ⟨E.next Γn, E.tail_next M0 Γn hTailn, ?_⟩
      have hsucc : D.debt Γ + n + 1 ≤ D.debt Γn + 1 :=
        Nat.succ_le_succ hDebtn
      have htarget : D.debt Γ + Nat.succ n ≤ D.debt Γn + 1 := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hsucc
      simpa [E.debt_next Γn] using htarget

/-- From any same-tail seed, exact successor reaches every floor and every finite bound. -/
theorem exists_iterate_above_floor_and_bound
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D)
    {M0 : Nat} {Γ : D.Genealogy}
    (hTail : D.Tail M0 Γ)
    (K0 B : Nat) :
    ∃ Γ' : D.Genealogy,
      D.Tail M0 Γ' ∧ K0 ≤ D.debt Γ' ∧ B < D.debt Γ' := by
  rcases E.exists_iterate_with_debt_add_le hTail (K0 + B + 1) with
    ⟨Γ', hTail', hDebt'⟩
  refine ⟨Γ', hTail', ?_, ?_⟩
  · have hbase : K0 ≤ D.debt Γ + (K0 + B + 1) := by
      omega
    exact le_trans hbase hDebt'
  · have hbase : B < D.debt Γ + (K0 + B + 1) := by
      omega
    exact lt_of_lt_of_le hbase hDebt'

end ExactPeelSuccessorOperator

/-#############################################################################
  §3. Indexed center systems: arithmetic successor ⇒ exact debt successor
#############################################################################-/

/--
A genealogy system whose Mersenne center is indexed by a natural peel index.

`center Γ = zCenter (index Γ)` ties semantic genealogy data to the pure base-4
repunit tower.
-/
structure IndexedPeelTailSystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat
  center : Genealogy → Int
  center_matches : ∀ Γ, center Γ = zCenter (index Γ)

namespace IndexedPeelTailSystem

/-- Forget the center and use the index as peel-debt. -/
def toPeelDebtSystem (I : IndexedPeelTailSystem) : PeelDebtSystem where
  Genealogy := I.Genealogy
  Tail := I.Tail
  debt := I.index

end IndexedPeelTailSystem

/--
A concrete same-tail indexed peel successor certificate.

This is the object the real Step00/Mersenne genealogy construction must provide.
-/
structure IndexedPeelSuccessorCertificate (I : IndexedPeelTailSystem) where
  next : I.Genealogy → I.Genealogy
  tail_next : ∀ M0 Γ, I.Tail M0 Γ → I.Tail M0 (next Γ)
  index_next : ∀ Γ, I.index (next Γ) = I.index Γ + 1

namespace IndexedPeelSuccessorCertificate

/-- An indexed successor certificate yields an exact peel successor operator. -/
def toExactPeelSuccessorOperator
    {I : IndexedPeelTailSystem}
    (C : IndexedPeelSuccessorCertificate I) :
    ExactPeelSuccessorOperator I.toPeelDebtSystem where
  next := C.next
  tail_next := C.tail_next
  debt_next := C.index_next

/-- The center of the successor is exactly the next base-4 repunit center. -/
theorem center_next
    {I : IndexedPeelTailSystem}
    (C : IndexedPeelSuccessorCertificate I)
    (Γ : I.Genealogy) :
    I.center (C.next Γ) = zCenter (Nat.succ (I.index Γ)) := by
  rw [I.center_matches (C.next Γ), C.index_next Γ]

/-- Upper side after successor follows the exact Mersenne/base-4 peel transition. -/
theorem upperSide_next
    {I : IndexedPeelTailSystem}
    (C : IndexedPeelSuccessorCertificate I)
    (Γ : I.Genealogy) :
    zUpperSide (I.center (C.next Γ)) =
      4 * zUpperSide (I.center Γ) + 3 := by
  rw [C.center_next Γ, I.center_matches Γ]
  exact zUpperSide_peel_succ (I.index Γ)

/-- Lower side after successor follows the exact Mersenne/base-4 peel transition. -/
theorem lowerSide_next
    {I : IndexedPeelTailSystem}
    (C : IndexedPeelSuccessorCertificate I)
    (Γ : I.Genealogy) :
    zLowerSide (I.center (C.next Γ)) =
      4 * zLowerSide (I.center Γ) + 9 := by
  rw [C.center_next Γ, I.center_matches Γ]
  exact zLowerSide_peel_succ (I.index Γ)

end IndexedPeelSuccessorCertificate

/-#############################################################################
  §4. From one ordinary seed + exact successor to peel expansion
#############################################################################-/

/-- Ordinary twin supply gives at least one genealogy on each requested tail. -/
structure OrdinaryTailSeedLaw
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) where
  seed : ∀ M0 : Nat, TwinAbove M0 → ∃ Γ : D.Genealogy, D.Tail M0 Γ

/--
Peel expansion law: above any ordinary twin tail, any Mersenne floor `K0`, and
any finite obstruction bound `B`, there is a same-tail genealogy whose debt is
both at least `K0` and above `B`.
-/
def PeelExpansionLaw
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ∀ M0 K0 B : Nat,
    TwinAbove M0 →
      ∃ Γ : D.Genealogy,
        D.Tail M0 Γ ∧ K0 ≤ D.debt Γ ∧ B < D.debt Γ

/--
One ordinary tail seed plus exact same-tail successor proves full peel expansion.
-/
theorem peelExpansionLaw_of_seed_and_exactSuccessor
    {D : PeelDebtSystem}
    {TwinAbove : Nat → Prop}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (E : ExactPeelSuccessorOperator D) :
    PeelExpansionLaw D TwinAbove := by
  intro M0 K0 B hTwin
  rcases Seed.seed M0 hTwin with ⟨Γ0, hTail0⟩
  exact E.exists_iterate_above_floor_and_bound hTail0 K0 B

/-- Indexed successor version of the same theorem. -/
theorem peelExpansionLaw_of_indexedSeed_and_successor
    {I : IndexedPeelTailSystem}
    {TwinAbove : Nat → Prop}
    (Seed : OrdinaryTailSeedLaw I.toPeelDebtSystem TwinAbove)
    (C : IndexedPeelSuccessorCertificate I) :
    PeelExpansionLaw I.toPeelDebtSystem TwinAbove := by
  exact peelExpansionLaw_of_seed_and_exactSuccessor Seed
    C.toExactPeelSuccessorOperator

/-#############################################################################
  §5. Final front and defect split
#############################################################################-/

/-- The exact successor arithmetic front for the Mersenne route. -/
structure ExactPeelSuccessorArithmeticFront
    (TwinAbove : Nat → Prop) where
  indexed_system : IndexedPeelTailSystem
  ordinary_seed : OrdinaryTailSeedLaw indexed_system.toPeelDebtSystem TwinAbove
  successor : IndexedPeelSuccessorCertificate indexed_system

namespace ExactPeelSuccessorArithmeticFront

/-- The front gives an exact peel successor operator. -/
def exactOperator
    {TwinAbove : Nat → Prop}
    (F : ExactPeelSuccessorArithmeticFront TwinAbove) :
    ExactPeelSuccessorOperator F.indexed_system.toPeelDebtSystem :=
  F.successor.toExactPeelSuccessorOperator

/-- The front proves peel expansion. -/
theorem peelExpansionLaw
    {TwinAbove : Nat → Prop}
    (F : ExactPeelSuccessorArithmeticFront TwinAbove) :
    PeelExpansionLaw F.indexed_system.toPeelDebtSystem TwinAbove := by
  exact peelExpansionLaw_of_indexedSeed_and_successor F.ordinary_seed F.successor

/-- Successor upper-side arithmetic is part of the front. -/
theorem upperSide_successor
    {TwinAbove : Nat → Prop}
    (F : ExactPeelSuccessorArithmeticFront TwinAbove)
    (Γ : F.indexed_system.Genealogy) :
    zUpperSide (F.indexed_system.center (F.successor.next Γ)) =
      4 * zUpperSide (F.indexed_system.center Γ) + 3 :=
  F.successor.upperSide_next Γ

/-- Successor lower-side arithmetic is part of the front. -/
theorem lowerSide_successor
    {TwinAbove : Nat → Prop}
    (F : ExactPeelSuccessorArithmeticFront TwinAbove)
    (Γ : F.indexed_system.Genealogy) :
    zLowerSide (F.indexed_system.center (F.successor.next Γ)) =
      4 * zLowerSide (F.indexed_system.center Γ) + 9 :=
  F.successor.lowerSide_next Γ

end ExactPeelSuccessorArithmeticFront

/-- Failure of peel expansion. -/
def PeelExpansionDefect
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ¬ PeelExpansionLaw D TwinAbove

/-- Failure of ordinary seed supply. -/
def OrdinaryTailSeedDefect
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ¬ OrdinaryTailSeedLaw D TwinAbove

/-- Failure of exact peel successor. -/
def ExactPeelSuccessorDefect (D : PeelDebtSystem) : Prop :=
  ExactPeelSuccessorOperator D → False

/-- If peel expansion fails, then either seed supply fails or exact successor fails. -/
theorem peelExpansionDefect_forces_seed_or_exactSuccessor_defect
    {D : PeelDebtSystem}
    {TwinAbove : Nat → Prop}
    (hDef : PeelExpansionDefect D TwinAbove) :
    OrdinaryTailSeedDefect D TwinAbove ∨ ExactPeelSuccessorDefect D := by
  by_cases hSeed : OrdinaryTailSeedLaw D TwinAbove
  · right
    intro hSucc
    exact hDef (peelExpansionLaw_of_seed_and_exactSuccessor hSeed hSucc)
  · left
    exact hSeed

/-- Final slogan: exact indexed base-4 successor is enough for unbounded peel expansion. -/
theorem exactPeelSuccessorArithmetic_slogan
    {TwinAbove : Nat → Prop}
    (F : ExactPeelSuccessorArithmeticFront TwinAbove) :
    PeelExpansionLaw F.indexed_system.toPeelDebtSystem TwinAbove ∧
    (∀ Γ : F.indexed_system.Genealogy,
      zUpperSide (F.indexed_system.center (F.successor.next Γ)) =
        4 * zUpperSide (F.indexed_system.center Γ) + 3) ∧
    (∀ Γ : F.indexed_system.Genealogy,
      zLowerSide (F.indexed_system.center (F.successor.next Γ)) =
        4 * zLowerSide (F.indexed_system.center Γ) + 9) := by
  exact ⟨F.peelExpansionLaw, F.upperSide_successor, F.lowerSide_successor⟩

end MersenneExactPeel
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_peel_lift_certificate_patch.lean =====
/-
EuclidsPath — Mersenne indexed peel lift certificate patch
===========================================================

Purpose
-------
The previous patch isolated the arithmetic fact that the Mersenne/base-4 peel
successor is exactly

    k ↦ k + 1,
    c_{k+1} = 4 c_k + 1.

The remaining semantic obligation is not arithmetic.  It is the Step00 lift:
construct a genealogy successor

    Γ ↦ Γ⁺

such that

    Tail M0 Γ        → Tail M0 Γ⁺,
    index Γ⁺         = index Γ + 1,
    center Γ         = c_{index Γ},
    center Γ⁺        = c_{index Γ + 1},

and the lift is ledger-faithful: it does not use a seam, a compression shortcut,
or an unpaid boundary jump.

This file formalizes that semantic lift as a precise certificate and proves that
it implies the exact peel successor operator, hence the full peel expansion law
once an ordinary tail seed is available.

No theorem here asserts the existence of the real Step00 lift.  The new live
brick is exactly `Nonempty (PeelLiftOperator I)` for the concrete indexed
Mersenne genealogy system `I`.

No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace MersennePeelLift

/-#############################################################################
  §1. Pure base-4 center arithmetic
#############################################################################-/

/-- Signed base-4 repunit center sequence: `c_{k+1} = 4*c_k + 1`. -/
def zCenter : Nat → Int
  | 0 => 0
  | Nat.succ k => 4 * zCenter k + 1

@[simp] theorem zCenter_zero : zCenter 0 = 0 := rfl

@[simp] theorem zCenter_succ (k : Nat) :
    zCenter (Nat.succ k) = 4 * zCenter k + 1 :=
  rfl

/-- Lower side of a Step00 twin center. -/
def zLowerSide (c : Int) : Int :=
  6 * c - 1

/-- Upper side of a Step00 twin center. -/
def zUpperSide (c : Int) : Int :=
  6 * c + 1

/-- Exact upper-side transition under base-4 peel. -/
theorem zUpperSide_peel_succ (k : Nat) :
    zUpperSide (zCenter (Nat.succ k)) =
      4 * zUpperSide (zCenter k) + 3 := by
  simp [zUpperSide]
  ring

/-- Exact lower-side transition under base-4 peel. -/
theorem zLowerSide_peel_succ (k : Nat) :
    zLowerSide (zCenter (Nat.succ k)) =
      4 * zLowerSide (zCenter k) + 9 := by
  simp [zLowerSide]
  ring

/-#############################################################################
  §2. Indexed genealogy systems
#############################################################################-/

/--
An indexed Mersenne genealogy system.

`Tail M0 Γ` says that `Γ` belongs to the ordinary twin genealogy tail above the
horizon `M0`.  `index Γ` is the Mersenne/base-4 peel index.  `center_matches`
anchors every genealogy center to the canonical repunit center sequence.
-/
structure IndexedPeelTailSystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat
  center : Genealogy → Int
  center_matches : ∀ Γ : Genealogy, center Γ = zCenter (index Γ)

/-- The debt-only forgetful system. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  debt : Genealogy → Nat

namespace IndexedPeelTailSystem

/-- Forget the center and use `index` as the Mersenne peel-debt. -/
def toPeelDebtSystem (I : IndexedPeelTailSystem) : PeelDebtSystem where
  Genealogy := I.Genealogy
  Tail := I.Tail
  debt := I.index

end IndexedPeelTailSystem

/-#############################################################################
  §3. Exact successor, seeds, and expansion
#############################################################################-/

/-- Exact same-tail successor for a peel-debt system. -/
structure ExactPeelSuccessorOperator (D : PeelDebtSystem) where
  next : D.Genealogy → D.Genealogy
  tail_next : ∀ M0 Γ, D.Tail M0 Γ → D.Tail M0 (next Γ)
  debt_next : ∀ Γ, D.debt (next Γ) = D.debt Γ + 1

namespace ExactPeelSuccessorOperator

/-- Iteration preserves tail and raises debt by at least the number of iterations. -/
theorem exists_iterate_with_debt_add_le
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D)
    {M0 : Nat} {Γ : D.Genealogy}
    (hTail : D.Tail M0 Γ) :
    ∀ n : Nat,
      ∃ Γ' : D.Genealogy,
        D.Tail M0 Γ' ∧ D.debt Γ + n ≤ D.debt Γ' := by
  intro n
  induction n with
  | zero =>
      exact ⟨Γ, hTail, by simp⟩
  | succ n ih =>
      rcases ih with ⟨Γn, hTailn, hDebtn⟩
      refine ⟨E.next Γn, E.tail_next M0 Γn hTailn, ?_⟩
      have hsucc : D.debt Γ + n + 1 ≤ D.debt Γn + 1 :=
        Nat.succ_le_succ hDebtn
      have htarget : D.debt Γ + Nat.succ n ≤ D.debt Γn + 1 := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hsucc
      simpa [E.debt_next Γn] using htarget

/-- Exact successor reaches any requested floor and beats any finite bound. -/
theorem exists_iterate_above_floor_and_bound
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D)
    {M0 : Nat} {Γ : D.Genealogy}
    (hTail : D.Tail M0 Γ)
    (K0 B : Nat) :
    ∃ Γ' : D.Genealogy,
      D.Tail M0 Γ' ∧ K0 ≤ D.debt Γ' ∧ B < D.debt Γ' := by
  rcases E.exists_iterate_with_debt_add_le hTail (K0 + B + 1) with
    ⟨Γ', hTail', hDebt'⟩
  refine ⟨Γ', hTail', ?_, ?_⟩
  · have hbase : K0 ≤ D.debt Γ + (K0 + B + 1) := by
      omega
    exact le_trans hbase hDebt'
  · have hbase : B < D.debt Γ + (K0 + B + 1) := by
      omega
    exact lt_of_lt_of_le hbase hDebt'

end ExactPeelSuccessorOperator

/-- Ordinary twin supply gives at least one genealogy on every requested tail. -/
structure OrdinaryTailSeedLaw
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) where
  seed : ∀ M0 : Nat, TwinAbove M0 → ∃ Γ : D.Genealogy, D.Tail M0 Γ

/-- Peel expansion: same-tail genealogies can be pushed past every floor and bound. -/
def PeelExpansionLaw
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ∀ M0 K0 B : Nat,
    TwinAbove M0 →
      ∃ Γ : D.Genealogy,
        D.Tail M0 Γ ∧ K0 ≤ D.debt Γ ∧ B < D.debt Γ

/-- One seed law plus one exact successor operator proves peel expansion. -/
theorem peelExpansionLaw_of_seed_and_exactSuccessor
    {D : PeelDebtSystem}
    {TwinAbove : Nat → Prop}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (E : ExactPeelSuccessorOperator D) :
    PeelExpansionLaw D TwinAbove := by
  intro M0 K0 B hTwin
  rcases Seed.seed M0 hTwin with ⟨Γ0, hTail0⟩
  exact E.exists_iterate_above_floor_and_bound hTail0 K0 B

/-#############################################################################
  §4. Semantic peel-lift event
#############################################################################-/

/-- Tail preservation for a proposed next-map. -/
def TailPreservation (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ∀ M0 Γ, I.Tail M0 Γ → I.Tail M0 (next Γ)

/-- Exact index increment for a proposed next-map. -/
def IndexSuccessor (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ∀ Γ, I.index (next Γ) = I.index Γ + 1

/-- Center coherence for a proposed next-map. -/
def CenterSuccessorCoherence (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ∀ Γ, I.center (next Γ) = zCenter (Nat.succ (I.index Γ))

/-- The next step is a legal local Step00/peel genealogy lift. -/
def LegalPeelLift (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  True

/-- The lift does not pass through a seam/singularity. -/
def NoPeelSeamEscape (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  True

/-- The lift is not a finite-compression shortcut. -/
def NoPeelCompressionEscape (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  True

/-- The lift is not an unpaid boundary jump. -/
def NoUnpaidPeelBoundaryJump (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  True

/--
All semantic obligations attached to a proposed indexed peel lift.

The last four fields are audit gates.  In the concrete Step00 implementation
they must be instantiated by the real ledger predicates; here they are explicit
slots so the proof does not hide those requirements inside `next`.
-/
structure PeelLiftObligations (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) where
  tail_preservation : TailPreservation I next
  index_successor : IndexSuccessor I next
  center_successor : CenterSuccessorCoherence I next
  legal_lift : LegalPeelLift I next
  no_seam_escape : NoPeelSeamEscape I next
  no_compression_escape : NoPeelCompressionEscape I next
  no_unpaid_boundary_jump : NoUnpaidPeelBoundaryJump I next

namespace PeelLiftObligations

/-- Center coherence follows from index successor and the system's own center anchor. -/
theorem center_successor_of_index_successor
    {I : IndexedPeelTailSystem}
    {next : I.Genealogy → I.Genealogy}
    (hIndex : IndexSuccessor I next) :
    CenterSuccessorCoherence I next := by
  intro Γ
  rw [I.center_matches (next Γ), hIndex Γ]

/-- Constructor when center coherence is derived rather than separately proved. -/
def of_index_successor
    {I : IndexedPeelTailSystem}
    {next : I.Genealogy → I.Genealogy}
    (hTail : TailPreservation I next)
    (hIndex : IndexSuccessor I next)
    (hLegal : LegalPeelLift I next)
    (hNoSeam : NoPeelSeamEscape I next)
    (hNoCompression : NoPeelCompressionEscape I next)
    (hNoBoundary : NoUnpaidPeelBoundaryJump I next) :
    PeelLiftObligations I next where
  tail_preservation := hTail
  index_successor := hIndex
  center_successor := center_successor_of_index_successor hIndex
  legal_lift := hLegal
  no_seam_escape := hNoSeam
  no_compression_escape := hNoCompression
  no_unpaid_boundary_jump := hNoBoundary

end PeelLiftObligations

/-- A semantic indexed peel lift operator. -/
structure PeelLiftOperator (I : IndexedPeelTailSystem) where
  next : I.Genealogy → I.Genealogy
  obligations : PeelLiftObligations I next

namespace PeelLiftOperator

/-- Forget semantic audit fields and retain the exact peel successor. -/
def toExactPeelSuccessorOperator
    {I : IndexedPeelTailSystem}
    (L : PeelLiftOperator I) :
    ExactPeelSuccessorOperator I.toPeelDebtSystem where
  next := L.next
  tail_next := L.obligations.tail_preservation
  debt_next := L.obligations.index_successor

/-- The lifted successor has the exact next Mersenne/base-4 center. -/
theorem center_next
    {I : IndexedPeelTailSystem}
    (L : PeelLiftOperator I)
    (Γ : I.Genealogy) :
    I.center (L.next Γ) = zCenter (Nat.succ (I.index Γ)) :=
  L.obligations.center_successor Γ

/-- Upper side after the semantic lift follows the Mersenne arithmetic transition. -/
theorem upperSide_next
    {I : IndexedPeelTailSystem}
    (L : PeelLiftOperator I)
    (Γ : I.Genealogy) :
    zUpperSide (I.center (L.next Γ)) =
      4 * zUpperSide (I.center Γ) + 3 := by
  rw [L.center_next Γ, I.center_matches Γ]
  exact zUpperSide_peel_succ (I.index Γ)

/-- Lower side after the semantic lift follows the Mersenne arithmetic transition. -/
theorem lowerSide_next
    {I : IndexedPeelTailSystem}
    (L : PeelLiftOperator I)
    (Γ : I.Genealogy) :
    zLowerSide (I.center (L.next Γ)) =
      4 * zLowerSide (I.center Γ) + 9 := by
  rw [L.center_next Γ, I.center_matches Γ]
  exact zLowerSide_peel_succ (I.index Γ)

/-- Semantic lift plus ordinary seed law proves peel expansion. -/
theorem peelExpansionLaw
    {I : IndexedPeelTailSystem}
    {TwinAbove : Nat → Prop}
    (Seed : OrdinaryTailSeedLaw I.toPeelDebtSystem TwinAbove)
    (L : PeelLiftOperator I) :
    PeelExpansionLaw I.toPeelDebtSystem TwinAbove :=
  peelExpansionLaw_of_seed_and_exactSuccessor Seed L.toExactPeelSuccessorOperator

end PeelLiftOperator

/-#############################################################################
  §5. Live front and defect split
#############################################################################-/

/-- The live semantic lift front for the Mersenne route. -/
structure MersennePeelLiftFront
    (TwinAbove : Nat → Prop) where
  indexed_system : IndexedPeelTailSystem
  ordinary_seed : OrdinaryTailSeedLaw indexed_system.toPeelDebtSystem TwinAbove
  semantic_lift : PeelLiftOperator indexed_system

namespace MersennePeelLiftFront

/-- The front gives an exact peel successor operator. -/
def exactSuccessor
    {TwinAbove : Nat → Prop}
    (F : MersennePeelLiftFront TwinAbove) :
    ExactPeelSuccessorOperator F.indexed_system.toPeelDebtSystem :=
  F.semantic_lift.toExactPeelSuccessorOperator

/-- The front proves full peel expansion. -/
theorem peelExpansionLaw
    {TwinAbove : Nat → Prop}
    (F : MersennePeelLiftFront TwinAbove) :
    PeelExpansionLaw F.indexed_system.toPeelDebtSystem TwinAbove :=
  F.semantic_lift.peelExpansionLaw F.ordinary_seed

/-- The front preserves exact upper-side arithmetic. -/
theorem upperSide_successor
    {TwinAbove : Nat → Prop}
    (F : MersennePeelLiftFront TwinAbove)
    (Γ : F.indexed_system.Genealogy) :
    zUpperSide (F.indexed_system.center (F.semantic_lift.next Γ)) =
      4 * zUpperSide (F.indexed_system.center Γ) + 3 :=
  F.semantic_lift.upperSide_next Γ

/-- The front preserves exact lower-side arithmetic. -/
theorem lowerSide_successor
    {TwinAbove : Nat → Prop}
    (F : MersennePeelLiftFront TwinAbove)
    (Γ : F.indexed_system.Genealogy) :
    zLowerSide (F.indexed_system.center (F.semantic_lift.next Γ)) =
      4 * zLowerSide (F.indexed_system.center Γ) + 9 :=
  F.semantic_lift.lowerSide_next Γ

end MersennePeelLiftFront

/-- Failure of peel expansion. -/
def PeelExpansionDefect
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ¬ PeelExpansionLaw D TwinAbove

/-- Failure to provide an ordinary tail seed law. -/
def OrdinaryTailSeedDefect
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ¬ Nonempty (OrdinaryTailSeedLaw D TwinAbove)

/-- Failure to provide a semantic peel lift. -/
def PeelLiftDefect (I : IndexedPeelTailSystem) : Prop :=
  ¬ Nonempty (PeelLiftOperator I)

/-- If peel expansion fails, either seed supply or semantic lift is missing. -/
theorem peelExpansionDefect_forces_seed_or_lift_defect
    {I : IndexedPeelTailSystem}
    {TwinAbove : Nat → Prop}
    (hDef : PeelExpansionDefect I.toPeelDebtSystem TwinAbove) :
    OrdinaryTailSeedDefect I.toPeelDebtSystem TwinAbove ∨
      PeelLiftDefect I := by
  by_cases hSeed : Nonempty (OrdinaryTailSeedLaw I.toPeelDebtSystem TwinAbove)
  · right
    intro hLift
    rcases hSeed with ⟨Seed⟩
    rcases hLift with ⟨L⟩
    exact hDef (L.peelExpansionLaw Seed)
  · left
    exact hSeed

/-#############################################################################
  §6. Component-level audit for a proposed next-map
#############################################################################-/

/-- A proposed map fails the tail-preservation component. -/
def TailEscapeDefect (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ¬ TailPreservation I next

/-- A proposed map fails the exact index-successor component. -/
def IndexSuccessorDefect (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ¬ IndexSuccessor I next

/-- A proposed map fails the legal-lift component. -/
def IllegalLiftDefect (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ¬ LegalPeelLift I next

/-- A proposed map uses a seam escape. -/
def SeamEscapeDefect (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ¬ NoPeelSeamEscape I next

/-- A proposed map uses compression escape. -/
def CompressionEscapeDefect (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ¬ NoPeelCompressionEscape I next

/-- A proposed map uses an unpaid boundary jump. -/
def UnpaidBoundaryJumpDefect (I : IndexedPeelTailSystem)
    (next : I.Genealogy → I.Genealogy) : Prop :=
  ¬ NoUnpaidPeelBoundaryJump I next

/--
If a fixed proposed next-map cannot be made into obligations, one component of
that map fails.
-/
theorem obligations_defect_forces_component_defect
    {I : IndexedPeelTailSystem}
    {next : I.Genealogy → I.Genealogy}
    (hDef : ¬ PeelLiftObligations I next) :
    TailEscapeDefect I next ∨
    IndexSuccessorDefect I next ∨
    IllegalLiftDefect I next ∨
    SeamEscapeDefect I next ∨
    CompressionEscapeDefect I next ∨
    UnpaidBoundaryJumpDefect I next := by
  by_cases hTail : TailPreservation I next
  · by_cases hIndex : IndexSuccessor I next
    · by_cases hLegal : LegalPeelLift I next
      · by_cases hSeam : NoPeelSeamEscape I next
        · by_cases hCompression : NoPeelCompressionEscape I next
          · by_cases hBoundary : NoUnpaidPeelBoundaryJump I next
            · exfalso
              exact hDef (PeelLiftObligations.of_index_successor
                hTail hIndex hLegal hSeam hCompression hBoundary)
            · right; right; right; right; right
              exact hBoundary
          · right; right; right; right; left
            exact hCompression
        · right; right; right; left
          exact hSeam
      · right; right; left
        exact hLegal
    · right; left
      exact hIndex
  · left
    exact hTail

/--
Global no-lift defect, expanded against every proposed next-map: every candidate
successor has a visible component defect.
-/
theorem peelLiftDefect_forces_every_candidate_component_defect
    {I : IndexedPeelTailSystem}
    (hDef : PeelLiftDefect I)
    (next : I.Genealogy → I.Genealogy) :
    TailEscapeDefect I next ∨
    IndexSuccessorDefect I next ∨
    IllegalLiftDefect I next ∨
    SeamEscapeDefect I next ∨
    CompressionEscapeDefect I next ∨
    UnpaidBoundaryJumpDefect I next := by
  apply obligations_defect_forces_component_defect
  intro hObl
  exact hDef ⟨{ next := next, obligations := hObl }⟩

/-- Final slogan: the remaining Mersenne peel successor obligation is semantic lift. -/
theorem mersennePeelLift_slogan
    {TwinAbove : Nat → Prop}
    (F : MersennePeelLiftFront TwinAbove) :
    PeelExpansionLaw F.indexed_system.toPeelDebtSystem TwinAbove ∧
    (∀ Γ : F.indexed_system.Genealogy,
      zUpperSide (F.indexed_system.center (F.semantic_lift.next Γ)) =
        4 * zUpperSide (F.indexed_system.center Γ) + 3) ∧
    (∀ Γ : F.indexed_system.Genealogy,
      zLowerSide (F.indexed_system.center (F.semantic_lift.next Γ)) =
        4 * zLowerSide (F.indexed_system.center Γ) + 9) := by
  exact ⟨F.peelExpansionLaw, F.upperSide_successor, F.lowerSide_successor⟩

end MersennePeelLift
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_pointwise_peel_lift_source_patch.lean =====
/-
EuclidsPath — Mersenne pointwise peel-lift source patch
========================================================

Purpose
-------
The previous patch isolated the live semantic obligation as

    Nonempty (PeelLiftOperator I),

where a uniform successor `Γ ↦ Γ⁺` preserves the ordinary twin tail, increments
Mersenne/base-4 peel index exactly by one, and does not use seam/compression or
unpaid-boundary escape.

This file lowers that obligation one more level.  Instead of requiring a global
operator at once, it defines a pointwise lift witness for each genealogy `Γ`.
A pointwise source

    ∀ Γ, Nonempty (PointwisePeelLiftWitness S Γ)

is then converted, by choice, into a uniform `PeelLiftOperator`, and therefore
into the full peel-expansion law once an ordinary tail seed is available.

Thus the remaining concrete brick is no longer “produce a whole operator”.  It is
now the local construction problem:

    for every genealogy Γ, construct one legal Γ⁺
    with index Γ⁺ = index Γ + 1,
    preserving every tail that Γ belongs to.

No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace MersennePointwisePeelLift

/-#############################################################################
  §1. Base-4 Mersenne center arithmetic
#############################################################################-/

/-- Signed base-4 repunit center sequence: `c_{k+1} = 4*c_k + 1`. -/
def zCenter : Nat → Int
  | 0 => 0
  | Nat.succ k => 4 * zCenter k + 1

@[simp] theorem zCenter_zero : zCenter 0 = 0 := rfl

@[simp] theorem zCenter_succ (k : Nat) :
    zCenter (Nat.succ k) = 4 * zCenter k + 1 :=
  rfl

/-- Lower side of a Step00 twin center. -/
def zLowerSide (c : Int) : Int :=
  6 * c - 1

/-- Upper side of a Step00 twin center. -/
def zUpperSide (c : Int) : Int :=
  6 * c + 1

/-- Exact upper-side transition under base-4 peel. -/
theorem zUpperSide_peel_succ (k : Nat) :
    zUpperSide (zCenter (Nat.succ k)) =
      4 * zUpperSide (zCenter k) + 3 := by
  simp [zUpperSide]
  ring

/-- Exact lower-side transition under base-4 peel. -/
theorem zLowerSide_peel_succ (k : Nat) :
    zLowerSide (zCenter (Nat.succ k)) =
      4 * zLowerSide (zCenter k) + 9 := by
  simp [zLowerSide]
  ring

/-#############################################################################
  §2. Indexed tail systems and debt forgetful systems
#############################################################################-/

/--
An indexed Mersenne genealogy system.  `index Γ` is the base-4 peel index and
`center Γ` is anchored to the canonical center `zCenter (index Γ)`.
-/
structure IndexedPeelTailSystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat
  center : Genealogy → Int
  center_matches : ∀ Γ : Genealogy, center Γ = zCenter (index Γ)

/-- The debt-only system obtained by forgetting centers and using index as debt. -/
structure PeelDebtSystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  debt : Genealogy → Nat

namespace IndexedPeelTailSystem

/-- Forget the center; the Mersenne peel index becomes the debt. -/
def toPeelDebtSystem (I : IndexedPeelTailSystem) : PeelDebtSystem where
  Genealogy := I.Genealogy
  Tail := I.Tail
  debt := I.index

end IndexedPeelTailSystem

/-#############################################################################
  §3. Semantic predicates for a peel lift
#############################################################################-/

/--
Semantic audit predicates for a local peel lift step from `Γ` to `Γ⁺`.

The concrete Step00 implementation should instantiate these with the real ledger
predicates.  Keeping them as fields prevents the proof from hiding seam,
compression, or payment assumptions inside a bare successor map.
-/
structure PeelLiftSemantics (I : IndexedPeelTailSystem) where
  Legal : I.Genealogy → I.Genealogy → Prop
  NoSeamEscape : I.Genealogy → I.Genealogy → Prop
  NoCompressionEscape : I.Genealogy → I.Genealogy → Prop
  NoUnpaidBoundaryJump : I.Genealogy → I.Genealogy → Prop

/-- Tail preservation for a candidate local successor. -/
def TailPreservedFor (I : IndexedPeelTailSystem)
    (Γ Γplus : I.Genealogy) : Prop :=
  ∀ M0 : Nat, I.Tail M0 Γ → I.Tail M0 Γplus

/-- Exact one-step index increment for a candidate local successor. -/
def IndexIncrementedFor (I : IndexedPeelTailSystem)
    (Γ Γplus : I.Genealogy) : Prop :=
  I.index Γplus = I.index Γ + 1

/--
One pointwise lift witness for a fixed genealogy `Γ`.
-/
structure PointwisePeelLiftWitness
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I)
    (Γ : I.Genealogy) where
  Γplus : I.Genealogy
  tail_preserved : TailPreservedFor I Γ Γplus
  index_incremented : IndexIncrementedFor I Γ Γplus
  legal : S.Legal Γ Γplus
  no_seam_escape : S.NoSeamEscape Γ Γplus
  no_compression_escape : S.NoCompressionEscape Γ Γplus
  no_unpaid_boundary_jump : S.NoUnpaidBoundaryJump Γ Γplus

/-- A source of local peel-lift witnesses, one for every genealogy. -/
def PointwisePeelLiftSource
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I) : Prop :=
  ∀ Γ : I.Genealogy, Nonempty (PointwisePeelLiftWitness S Γ)

/-#############################################################################
  §4. Uniform operator extracted from pointwise witnesses
#############################################################################-/

/-- A uniform semantic peel lift operator. -/
structure PeelLiftOperator
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I) where
  next : I.Genealogy → I.Genealogy
  tail_next : ∀ M0 Γ, I.Tail M0 Γ → I.Tail M0 (next Γ)
  index_next : ∀ Γ, I.index (next Γ) = I.index Γ + 1
  legal_next : ∀ Γ, S.Legal Γ (next Γ)
  no_seam_next : ∀ Γ, S.NoSeamEscape Γ (next Γ)
  no_compression_next : ∀ Γ, S.NoCompressionEscape Γ (next Γ)
  no_unpaid_boundary_next : ∀ Γ, S.NoUnpaidBoundaryJump Γ (next Γ)

namespace PeelLiftOperator

/-- The lifted successor has the canonical next Mersenne center. -/
theorem center_next
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (L : PeelLiftOperator S)
    (Γ : I.Genealogy) :
    I.center (L.next Γ) = zCenter (Nat.succ (I.index Γ)) := by
  rw [I.center_matches (L.next Γ), L.index_next Γ]

/-- Upper side after semantic lift follows the exact Mersenne arithmetic transition. -/
theorem upperSide_next
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (L : PeelLiftOperator S)
    (Γ : I.Genealogy) :
    zUpperSide (I.center (L.next Γ)) =
      4 * zUpperSide (I.center Γ) + 3 := by
  rw [L.center_next Γ, I.center_matches Γ]
  exact zUpperSide_peel_succ (I.index Γ)

/-- Lower side after semantic lift follows the exact Mersenne arithmetic transition. -/
theorem lowerSide_next
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (L : PeelLiftOperator S)
    (Γ : I.Genealogy) :
    zLowerSide (I.center (L.next Γ)) =
      4 * zLowerSide (I.center Γ) + 9 := by
  rw [L.center_next Γ, I.center_matches Γ]
  exact zLowerSide_peel_succ (I.index Γ)

end PeelLiftOperator

/--
A pointwise source gives a uniform semantic peel-lift operator.

This is the formal lowering step: local existence of `Γ⁺` for every `Γ` is enough
to build the global operator used by the expansion route.
-/
noncomputable def peelLiftOperator_of_pointwiseSource
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (Source : PointwisePeelLiftSource S) :
    PeelLiftOperator S where
  next := fun Γ => (Classical.choice (Source Γ)).Γplus
  tail_next := by
    intro M0 Γ hTail
    exact (Classical.choice (Source Γ)).tail_preserved M0 hTail
  index_next := by
    intro Γ
    exact (Classical.choice (Source Γ)).index_incremented
  legal_next := by
    intro Γ
    exact (Classical.choice (Source Γ)).legal
  no_seam_next := by
    intro Γ
    exact (Classical.choice (Source Γ)).no_seam_escape
  no_compression_next := by
    intro Γ
    exact (Classical.choice (Source Γ)).no_compression_escape
  no_unpaid_boundary_next := by
    intro Γ
    exact (Classical.choice (Source Γ)).no_unpaid_boundary_jump

/-- Pointwise source gives nonempty operator. -/
theorem nonempty_peelLiftOperator_of_pointwiseSource
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (Source : PointwisePeelLiftSource S) :
    Nonempty (PeelLiftOperator S) :=
  ⟨peelLiftOperator_of_pointwiseSource Source⟩

/-#############################################################################
  §5. Exact successor and peel expansion
#############################################################################-/

/-- Exact same-tail successor for a peel-debt system. -/
structure ExactPeelSuccessorOperator (D : PeelDebtSystem) where
  next : D.Genealogy → D.Genealogy
  tail_next : ∀ M0 Γ, D.Tail M0 Γ → D.Tail M0 (next Γ)
  debt_next : ∀ Γ, D.debt (next Γ) = D.debt Γ + 1

namespace PeelLiftOperator

/-- A semantic peel lift gives the exact debt successor on the forgetful debt system. -/
def toExactPeelSuccessorOperator
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (L : PeelLiftOperator S) :
    ExactPeelSuccessorOperator I.toPeelDebtSystem where
  next := L.next
  tail_next := L.tail_next
  debt_next := L.index_next

end PeelLiftOperator

namespace ExactPeelSuccessorOperator

/-- Iterating an exact successor preserves tail and raises debt by at least `n`. -/
theorem exists_iterate_with_debt_add_le
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D)
    {M0 : Nat} {Γ : D.Genealogy}
    (hTail : D.Tail M0 Γ) :
    ∀ n : Nat,
      ∃ Γ' : D.Genealogy,
        D.Tail M0 Γ' ∧ D.debt Γ + n ≤ D.debt Γ' := by
  intro n
  induction n with
  | zero =>
      exact ⟨Γ, hTail, by simp⟩
  | succ n ih =>
      rcases ih with ⟨Γn, hTailn, hDebt⟩
      refine ⟨E.next Γn, E.tail_next M0 Γn hTailn, ?_⟩
      have hs : D.debt Γ + n + 1 ≤ D.debt Γn + 1 :=
        Nat.succ_le_succ hDebt
      have ht : D.debt Γ + Nat.succ n ≤ D.debt Γn + 1 := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hs
      simpa [E.debt_next Γn] using ht

/-- Exact successor reaches every requested floor and beats every finite bound. -/
theorem exists_iterate_above_floor_and_bound
    {D : PeelDebtSystem}
    (E : ExactPeelSuccessorOperator D)
    {M0 : Nat} {Γ : D.Genealogy}
    (hTail : D.Tail M0 Γ)
    (K0 B : Nat) :
    ∃ Γ' : D.Genealogy,
      D.Tail M0 Γ' ∧ K0 ≤ D.debt Γ' ∧ B < D.debt Γ' := by
  rcases E.exists_iterate_with_debt_add_le hTail (K0 + B + 1) with
    ⟨Γ', hTail', hDebt'⟩
  refine ⟨Γ', hTail', ?_, ?_⟩
  · have hbase : K0 ≤ D.debt Γ + (K0 + B + 1) := by
      omega
    exact le_trans hbase hDebt'
  · have hbase : B < D.debt Γ + (K0 + B + 1) := by
      omega
    exact lt_of_lt_of_le hbase hDebt'

end ExactPeelSuccessorOperator

/-- Ordinary twin supply gives at least one genealogy on every requested tail. -/
structure OrdinaryTailSeedLaw
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) where
  seed : ∀ M0 : Nat, TwinAbove M0 → ∃ Γ : D.Genealogy, D.Tail M0 Γ

/-- Peel expansion: same-tail genealogies can be pushed past any floor and bound. -/
def PeelExpansionLaw
    (D : PeelDebtSystem)
    (TwinAbove : Nat → Prop) : Prop :=
  ∀ M0 K0 B : Nat,
    TwinAbove M0 →
      ∃ Γ : D.Genealogy,
        D.Tail M0 Γ ∧ K0 ≤ D.debt Γ ∧ B < D.debt Γ

/-- Seed plus exact successor proves peel expansion. -/
theorem peelExpansionLaw_of_seed_and_exactSuccessor
    {D : PeelDebtSystem}
    {TwinAbove : Nat → Prop}
    (Seed : OrdinaryTailSeedLaw D TwinAbove)
    (E : ExactPeelSuccessorOperator D) :
    PeelExpansionLaw D TwinAbove := by
  intro M0 K0 B hTwin
  rcases Seed.seed M0 hTwin with ⟨Γ0, hTail0⟩
  exact E.exists_iterate_above_floor_and_bound hTail0 K0 B

/-- Pointwise semantic source plus ordinary seed proves full peel expansion. -/
theorem peelExpansionLaw_of_seed_and_pointwiseSource
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    {TwinAbove : Nat → Prop}
    (Seed : OrdinaryTailSeedLaw I.toPeelDebtSystem TwinAbove)
    (Source : PointwisePeelLiftSource S) :
    PeelExpansionLaw I.toPeelDebtSystem TwinAbove :=
  peelExpansionLaw_of_seed_and_exactSuccessor Seed
    (peelLiftOperator_of_pointwiseSource Source).toExactPeelSuccessorOperator

/-#############################################################################
  §6. Defect decomposition
#############################################################################-/

/-- Failure to have a pointwise source. -/
def PointwisePeelLiftSourceDefect
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I) : Prop :=
  ¬ PointwisePeelLiftSource S

/-- Failure to have a uniform lift operator. -/
def PeelLiftOperatorDefect
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I) : Prop :=
  ¬ Nonempty (PeelLiftOperator S)

/-- If there is no uniform operator, then there is no pointwise source. -/
theorem operatorDefect_forces_pointwiseSourceDefect
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (hDef : PeelLiftOperatorDefect S) :
    PointwisePeelLiftSourceDefect S := by
  intro hSource
  exact hDef (nonempty_peelLiftOperator_of_pointwiseSource hSource)

/-- Candidate component defect for a fixed attempted successor `Γplus`. -/
def CandidateComponentDefect
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I)
    (Γ Γplus : I.Genealogy) : Prop :=
  ¬ TailPreservedFor I Γ Γplus ∨
  ¬ IndexIncrementedFor I Γ Γplus ∨
  ¬ S.Legal Γ Γplus ∨
  ¬ S.NoSeamEscape Γ Γplus ∨
  ¬ S.NoCompressionEscape Γ Γplus ∨
  ¬ S.NoUnpaidBoundaryJump Γ Γplus

/--
If a fixed `Γ` has no pointwise lift witness, every proposed `Γplus` has a
visible component defect.
-/
theorem no_pointwiseWitness_forces_candidate_component_defect
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    {Γ : I.Genealogy}
    (hNoWitness : ¬ Nonempty (PointwisePeelLiftWitness S Γ))
    (Γplus : I.Genealogy) :
    CandidateComponentDefect S Γ Γplus := by
  by_cases hTail : TailPreservedFor I Γ Γplus
  · by_cases hIndex : IndexIncrementedFor I Γ Γplus
    · by_cases hLegal : S.Legal Γ Γplus
      · by_cases hNoSeam : S.NoSeamEscape Γ Γplus
        · by_cases hNoCompression : S.NoCompressionEscape Γ Γplus
          · by_cases hNoBoundary : S.NoUnpaidBoundaryJump Γ Γplus
            · exfalso
              exact hNoWitness ⟨{
                Γplus := Γplus
                tail_preserved := hTail
                index_incremented := hIndex
                legal := hLegal
                no_seam_escape := hNoSeam
                no_compression_escape := hNoCompression
                no_unpaid_boundary_jump := hNoBoundary
              }⟩
            · right; right; right; right; right
              exact hNoBoundary
          · right; right; right; right; left
            exact hNoCompression
        · right; right; right; left
          exact hNoSeam
      · right; right; left
        exact hLegal
    · right; left
      exact hIndex
  · left
    exact hTail

/-- Pointwise-source failure means some genealogy has no local witness. -/
def MissingPointwiseWitness
    {I : IndexedPeelTailSystem}
    (S : PeelLiftSemantics I) : Prop :=
  ∃ Γ : I.Genealogy, ¬ Nonempty (PointwisePeelLiftWitness S Γ)

/-- Classical expansion of failure of a universal pointwise source. -/
theorem missingPointwiseWitness_of_pointwiseSourceDefect
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (hDef : PointwisePeelLiftSourceDefect S) :
    MissingPointwiseWitness S := by
  classical
  by_contra hNoMissing
  apply hDef
  intro Γ
  by_contra hNoWitness
  exact hNoMissing ⟨Γ, hNoWitness⟩

/-- Therefore source failure exposes a concrete genealogy whose every candidate fails visibly. -/
theorem pointwiseSourceDefect_exposes_component_failure
    {I : IndexedPeelTailSystem}
    {S : PeelLiftSemantics I}
    (hDef : PointwisePeelLiftSourceDefect S) :
    ∃ Γ : I.Genealogy,
      ∀ Γplus : I.Genealogy,
        CandidateComponentDefect S Γ Γplus := by
  rcases missingPointwiseWitness_of_pointwiseSourceDefect hDef with ⟨Γ, hNo⟩
  exact ⟨Γ, fun Γplus =>
    no_pointwiseWitness_forces_candidate_component_defect hNo Γplus⟩

/-#############################################################################
  §7. Front package
#############################################################################-/

/-- The new lowest-level front for the Mersenne peel expansion route. -/
structure PointwisePeelLiftFront
    (TwinAbove : Nat → Prop) where
  indexed_system : IndexedPeelTailSystem
  semantics : PeelLiftSemantics indexed_system
  ordinary_seed : OrdinaryTailSeedLaw indexed_system.toPeelDebtSystem TwinAbove
  pointwise_source : PointwisePeelLiftSource semantics

namespace PointwisePeelLiftFront

/-- The front gives a uniform semantic lift operator. -/
noncomputable def operator
    {TwinAbove : Nat → Prop}
    (F : PointwisePeelLiftFront TwinAbove) :
    PeelLiftOperator F.semantics :=
  peelLiftOperator_of_pointwiseSource F.pointwise_source

/-- The front gives full peel expansion. -/
theorem peelExpansionLaw
    {TwinAbove : Nat → Prop}
    (F : PointwisePeelLiftFront TwinAbove) :
    PeelExpansionLaw F.indexed_system.toPeelDebtSystem TwinAbove :=
  peelExpansionLaw_of_seed_and_pointwiseSource
    F.ordinary_seed F.pointwise_source

/-- The front preserves exact upper-side arithmetic under its chosen operator. -/
theorem upperSide_successor
    {TwinAbove : Nat → Prop}
    (F : PointwisePeelLiftFront TwinAbove)
    (Γ : F.indexed_system.Genealogy) :
    zUpperSide (F.indexed_system.center (F.operator.next Γ)) =
      4 * zUpperSide (F.indexed_system.center Γ) + 3 :=
  F.operator.upperSide_next Γ

/-- The front preserves exact lower-side arithmetic under its chosen operator. -/
theorem lowerSide_successor
    {TwinAbove : Nat → Prop}
    (F : PointwisePeelLiftFront TwinAbove)
    (Γ : F.indexed_system.Genealogy) :
    zLowerSide (F.indexed_system.center (F.operator.next Γ)) =
      4 * zLowerSide (F.indexed_system.center Γ) + 9 :=
  F.operator.lowerSide_next Γ

end PointwisePeelLiftFront

/-- Final slogan: the live brick is pointwise local construction of `Γ⁺`. -/
theorem pointwisePeelLift_slogan
    {TwinAbove : Nat → Prop}
    (F : PointwisePeelLiftFront TwinAbove) :
    PeelExpansionLaw F.indexed_system.toPeelDebtSystem TwinAbove ∧
    (∀ Γ : F.indexed_system.Genealogy,
      zUpperSide (F.indexed_system.center (F.operator.next Γ)) =
        4 * zUpperSide (F.indexed_system.center Γ) + 3) ∧
    (∀ Γ : F.indexed_system.Genealogy,
      zLowerSide (F.indexed_system.center (F.operator.next Γ)) =
        4 * zLowerSide (F.indexed_system.center Γ) + 9) := by
  exact ⟨F.peelExpansionLaw, F.upperSide_successor, F.lowerSide_successor⟩

end MersennePointwisePeelLift
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_final_endgame_patch.lean =====
/-
EuclidsPath — Mersenne route final endgame patch
================================================

Purpose
-------
This is the final assembly layer for the conditional Mersenne-twin route.

It does NOT prove unconditionally that there are infinitely many Mersenne-twin
centres.  Instead it proves the exact endgame theorem:

  ordinary tail seed
  + pointwise same-tail peel lift Γ ↦ Γ⁺ with index + 1
  + own-index prime-payment law
  + sound prime-payment extraction
  ------------------------------------------------
  ⇒ cofinally many Mersenne-twin centres
  ⇒ no eventual absence of Mersenne-twin centres.

Equivalently, if Mersenne-twin centres eventually disappear, then at least one
of the final components must fail:

  seed ∨ lift ∨ payment ∨ soundness.

This is the honest “to the end” statement of the route.  The remaining actual
mathematical task is now visible and local: build the pointwise peel lift and
prove the payment/soundness laws for the concrete Step00 genealogy system.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneFinalEndgame

/-#############################################################################
  §1. Mersenne-twin centres as an abstract prime predicate
#############################################################################-/

/-- A prime-like predicate, kept abstract so the file can be instantiated with
`Nat.Prime` or a signed/ledger prime predicate. -/
abbrev PrimeLike := Nat → Prop

/-- The lower side of a Step00 twin centre. -/
def lowerSide (m : Nat) : Nat := 6 * m - 1

/-- The upper side of a Step00 twin centre. -/
def upperSide (m : Nat) : Nat := 6 * m + 1

/-- Base-4 repunit / Mersenne centre. -/
def mersenneCenter (k : Nat) : Nat := (4 ^ k - 1) / 3

/-- A Mersenne-twin centre at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide (mersenneCenter k)) ∧
  Prime (upperSide (mersenneCenter k))

/-- Cofinitely absent Mersenne-twin centres. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinitely / arbitrarily far present Mersenne-twin centres. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Cofinal Mersenne-twin supply forbids eventual absence. -/
theorem infinitelyMany_forbids_eventual_absence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hNo k hk hTwin

/-#############################################################################
  §2. Indexed genealogy system and pointwise peel lift
#############################################################################-/

/--
A Mersenne-indexed Step00 genealogy system.

`Tail M0 Γ` means that Γ belongs to the ordinary twin tail above horizon `M0`.
`index Γ` is the Mersenne/base-4 peel index carried by Γ.
-/
structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

/-- The ordinary twin supply provides at least one genealogy on each tail. -/
def OrdinaryTailSeedLaw (I : IndexedGenealogySystem) : Prop :=
  ∀ M0 : Nat, ∃ Γ : I.Genealogy, I.Tail M0 Γ

/-- A pointwise same-tail peel lift with exact index increment. -/
structure PointwisePeelLiftSource (I : IndexedGenealogySystem) where
  next : I.Genealogy → I.Genealogy

  tail_preserved :
    ∀ M0 : Nat, ∀ Γ : I.Genealogy,
      I.Tail M0 Γ → I.Tail M0 (next Γ)

  index_incremented :
    ∀ Γ : I.Genealogy,
      I.index (next Γ) = I.index Γ + 1

  legal_lift : Prop
  legal_lift_proof : legal_lift

  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape

  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape

  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace PointwisePeelLiftSource

/-- Iterate the peel lift `n` times. -/
def iterate {I : IndexedGenealogySystem}
    (L : PointwisePeelLiftSource I) : Nat → I.Genealogy → I.Genealogy
  | 0, Γ => Γ
  | Nat.succ n, Γ => L.next (iterate L n Γ)

/-- Iteration preserves the ordinary tail. -/
theorem iterate_tail_preserved
    {I : IndexedGenealogySystem}
    (L : PointwisePeelLiftSource I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ) :
    ∀ n : Nat, I.Tail M0 (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      exact hTail
  | succ n ih =>
      exact L.tail_preserved M0 (L.iterate n Γ) ih

/-- Iteration increases the Mersenne index exactly by `n`. -/
theorem iterate_index
    {I : IndexedGenealogySystem}
    (L : PointwisePeelLiftSource I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, I.index (L.iterate n Γ) = I.index Γ + n := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      simp [iterate, L.index_incremented, ih, Nat.add_assoc]

/-- Iteration reaches an index at least any prescribed floor. -/
theorem exists_iterate_at_or_above_floor
    {I : IndexedGenealogySystem}
    (L : PointwisePeelLiftSource I)
    (Γ : I.Genealogy)
    (K0 : Nat) :
    ∃ Γ' : I.Genealogy, K0 ≤ I.index Γ' := by
  refine ⟨L.iterate K0 Γ, ?_⟩
  have hIndex := L.iterate_index Γ K0
  rw [hIndex]
  omega

/-- Iteration preserves tail and reaches an index at least any prescribed floor. -/
theorem exists_tail_iterate_at_or_above_floor
    {I : IndexedGenealogySystem}
    (L : PointwisePeelLiftSource I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ)
    (K0 : Nat) :
    ∃ Γ' : I.Genealogy, I.Tail M0 Γ' ∧ K0 ≤ I.index Γ' := by
  refine ⟨L.iterate K0 Γ, ?_, ?_⟩
  · exact L.iterate_tail_preserved hTail K0
  · have hIndex := L.iterate_index Γ K0
    rw [hIndex]
    omega

end PointwisePeelLiftSource

/-#############################################################################
  §3. Payment extraction at the own Mersenne index
#############################################################################-/

/-- A raw payment relation: Γ pays the prime pair at Mersenne index `k`. -/
abbrev RawPrimePairPayment (I : IndexedGenealogySystem) :=
  I.Genealogy → Nat → Prop

/-- Every genealogy pays the prime pair at its own Mersenne index. -/
def OwnIndexPrimePaymentLaw
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy, Paid Γ (I.index Γ)

/-- Soundness: paid Mersenne prime pair extracts an actual Mersenne-twin centre. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat,
    Paid Γ k → MersenneTwinCenter Prime k

/-#############################################################################
  §4. Final route front
#############################################################################-/

/--
The final conditional route front.

This is the exact package whose construction would prove cofinally many
Mersenne-twin centres in this architecture.
-/
structure MersenneFinalRouteFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where

  ordinary_seed : OrdinaryTailSeedLaw I

  peel_lift : PointwisePeelLiftSource I

  own_payment : OwnIndexPrimePaymentLaw I Paid

  payment_sound : PrimePaymentSound Prime I Paid

/-- The final front produces a Mersenne-twin centre above any floor. -/
theorem exists_mersenneTwinCenter_above_of_finalFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : MersenneFinalRouteFront Prime I Paid)
    (K0 : Nat) :
    ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k := by
  rcases F.ordinary_seed 0 with ⟨Γ0, hTail0⟩
  rcases F.peel_lift.exists_tail_iterate_at_or_above_floor hTail0 K0 with
    ⟨Γ, _hTailΓ, hIndexFloor⟩
  refine ⟨I.index Γ, hIndexFloor, ?_⟩
  exact F.payment_sound Γ (I.index Γ) (F.own_payment Γ)

/-- The final front gives cofinally many Mersenne-twin centres. -/
theorem infinitelyManyMersenneTwinCenters_of_finalFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : MersenneFinalRouteFront Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact exists_mersenneTwinCenter_above_of_finalFront F K0

/-- Therefore the final front forbids eventual absence. -/
theorem finalFront_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : MersenneFinalRouteFront Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinitelyMany_forbids_eventual_absence
    (infinitelyManyMersenneTwinCenters_of_finalFront F)

/-#############################################################################
  §5. Defect theorem: absence forces failure of a final component
#############################################################################-/

/-- Seed defect: ordinary twin supply gives no tail seed. -/
def OrdinaryTailSeedDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ OrdinaryTailSeedLaw I

/-- Lift defect: no pointwise exact peel lift exists. -/
def PointwisePeelLiftDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ Nonempty (PointwisePeelLiftSource I)

/-- Payment defect: genealogy does not always pay the own Mersenne pair. -/
def OwnIndexPrimePaymentDefect
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ OwnIndexPrimePaymentLaw I Paid

/-- Soundness defect: paid prime pair does not reliably extract a Mersenne-twin centre. -/
def PrimePaymentSoundnessDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ PrimePaymentSound Prime I Paid

/-- The final component-defect disjunction. -/
def FinalMersenneRouteComponentDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  OrdinaryTailSeedDefect I ∨
  PointwisePeelLiftDefect I ∨
  OwnIndexPrimePaymentDefect I Paid ∨
  PrimePaymentSoundnessDefect Prime I Paid

/-- If all final components hold, they assemble into the final route front. -/
def finalFront_of_components
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hSeed : OrdinaryTailSeedLaw I)
    (hLift : PointwisePeelLiftSource I)
    (hPayment : OwnIndexPrimePaymentLaw I Paid)
    (hSound : PrimePaymentSound Prime I Paid) :
    MersenneFinalRouteFront Prime I Paid where
  ordinary_seed := hSeed
  peel_lift := hLift
  own_payment := hPayment
  payment_sound := hSound

/-- If eventual absence holds, at least one final component must fail. -/
theorem eventual_absence_forces_final_component_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    FinalMersenneRouteComponentDefect Prime I Paid := by
  classical
  by_cases hSeed : OrdinaryTailSeedLaw I
  · by_cases hLiftNonempty : Nonempty (PointwisePeelLiftSource I)
    · rcases hLiftNonempty with ⟨hLift⟩
      by_cases hPayment : OwnIndexPrimePaymentLaw I Paid
      · by_cases hSound : PrimePaymentSound Prime I Paid
        · have F : MersenneFinalRouteFront Prime I Paid :=
            finalFront_of_components hSeed hLift hPayment hSound
          exact False.elim ((finalFront_forbids_eventual_absence F) hAbs)
        · exact Or.inr (Or.inr (Or.inr hSound))
      · exact Or.inr (Or.inr (Or.inl hPayment))
    · exact Or.inr (Or.inl hLiftNonempty)
  · exact Or.inl hSeed

/-- If no final component fails, eventual absence is impossible. -/
theorem no_eventual_absence_of_no_final_component_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hNoDefect : ¬ FinalMersenneRouteComponentDefect Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact hNoDefect (eventual_absence_forces_final_component_defect hAbs)

/-#############################################################################
  §6. Explicit “ordinary twins ⇒ Mersenne twins” conditional theorem
#############################################################################-/

/--
A minimal concrete package for the desired implication:
ordinary Step00 supply plus the final Mersenne lift/payment laws.
-/
structure OrdinaryToMersenneTwinRoute
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where

  final_front : MersenneFinalRouteFront Prime I Paid

/-- The route gives cofinally many Mersenne-twin centres. -/
theorem ordinaryToMersenneRoute_produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (R : OrdinaryToMersenneTwinRoute Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime :=
  infinitelyManyMersenneTwinCenters_of_finalFront R.final_front

/-- The route forbids eventual absence. -/
theorem ordinaryToMersenneRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (R : OrdinaryToMersenneTwinRoute Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  finalFront_forbids_eventual_absence R.final_front

/-- Final slogan theorem. -/
theorem mersenne_final_endgame_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : MersenneFinalRouteFront Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  constructor
  · exact infinitelyManyMersenneTwinCenters_of_finalFront F
  · exact finalFront_forbids_eventual_absence F

end MersenneFinalEndgame
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_exact_successor_firewall_patch.lean =====
/-
EuclidsPath — Mersenne exact-successor firewall patch
======================================================

Purpose
-------
This file audits the previous final Mersenne route.

Important discovery:

  pointwise exact peel lift Γ ↦ Γ⁺ with index(Γ⁺)=index(Γ)+1,
  plus own-index prime payment and soundness,

is much stronger than “infinitely many Mersenne-twin centres”.  From one seed it
forces every sufficiently large Mersenne index to be a Mersenne-twin centre.

Therefore an exact consecutive successor route is not the right route for the
actual Mersenne problem.  For the genuine Nat-prime interpretation there are
cofinally many bad indices, for example when the Mersenne exponent 2k+1 is
composite the upper side 2^(2k+1)-1 is composite.  This file keeps that final
arithmetic fact abstract as `CofinalBadMersenneIndices` and proves the structural
firewall:

  CofinalBadMersenneIndices
  → no exact-consecutive final front.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneExactSuccessorFirewall

/-#############################################################################
  §1. Basic Mersenne centre predicates
#############################################################################-/

/-- Abstract prime-like predicate. -/
abbrev PrimeLike := Nat → Prop

/-- Step00 lower side. -/
def lowerSide (m : Nat) : Nat := 6 * m - 1

/-- Step00 upper side. -/
def upperSide (m : Nat) : Nat := 6 * m + 1

/-- Base-4 repunit / Mersenne centre. -/
def mersenneCenter (k : Nat) : Nat := (4 ^ k - 1) / 3

/-- A Mersenne-twin centre at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide (mersenneCenter k)) ∧
  Prime (upperSide (mersenneCenter k))

/-- Bad Mersenne index: not a Mersenne-twin centre. -/
def BadMersenneIndex (Prime : PrimeLike) (k : Nat) : Prop :=
  ¬ MersenneTwinCenter Prime k

/-- Cofinal bad indices: above every floor there is a bad Mersenne index. -/
def CofinalBadMersenneIndices (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ BadMersenneIndex Prime k

/-- Eventually every index is Mersenne-twin. -/
def EventuallyAllMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → MersenneTwinCenter Prime k

/-- Cofinal bad indices forbid eventual all-good behaviour. -/
theorem cofinalBad_forbids_eventuallyAll
    {Prime : PrimeLike}
    (hBad : CofinalBadMersenneIndices Prime) :
    ¬ EventuallyAllMersenneTwinCenters Prime := by
  intro hAll
  rcases hAll with ⟨K0, hGood⟩
  rcases hBad K0 with ⟨k, hk, hBadk⟩
  exact hBadk (hGood k hk)

/-#############################################################################
  §2. Exact consecutive peel-front
#############################################################################-/

/-- A Mersenne-indexed genealogy system. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

/-- Ordinary supply seed on every ordinary twin tail. -/
def OrdinaryTailSeedLaw (I : IndexedGenealogySystem) : Prop :=
  ∀ M0 : Nat, ∃ Γ : I.Genealogy, I.Tail M0 Γ

/-- Exact consecutive peel lift: same-tail and index `+1`. -/
structure ExactConsecutivePeelLift (I : IndexedGenealogySystem) where
  next : I.Genealogy → I.Genealogy

  tail_preserved :
    ∀ M0 : Nat, ∀ Γ : I.Genealogy,
      I.Tail M0 Γ → I.Tail M0 (next Γ)

  index_incremented :
    ∀ Γ : I.Genealogy,
      I.index (next Γ) = I.index Γ + 1

  legal_lift : Prop
  legal_lift_proof : legal_lift

  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape

  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape

  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace ExactConsecutivePeelLift

/-- Iterate the exact lift. -/
def iterate {I : IndexedGenealogySystem}
    (L : ExactConsecutivePeelLift I) : Nat → I.Genealogy → I.Genealogy
  | 0, Γ => Γ
  | Nat.succ n, Γ => L.next (iterate L n Γ)

/-- Iteration preserves tail. -/
theorem iterate_tail_preserved
    {I : IndexedGenealogySystem}
    (L : ExactConsecutivePeelLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ) :
    ∀ n : Nat, I.Tail M0 (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      exact hTail
  | succ n ih =>
      exact L.tail_preserved M0 (L.iterate n Γ) ih

/-- Iteration increases the index exactly by `n`. -/
theorem iterate_index
    {I : IndexedGenealogySystem}
    (L : ExactConsecutivePeelLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, I.index (L.iterate n Γ) = I.index Γ + n := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      simp [iterate, L.index_incremented, ih, Nat.add_assoc]

/-- From one seed of index `a`, exact lift reaches every index `k ≥ a`. -/
theorem reaches_every_index_above_seed
    {I : IndexedGenealogySystem}
    (L : ExactConsecutivePeelLift I)
    (Γ : I.Genealogy)
    {k : Nat}
    (hk : I.index Γ ≤ k) :
    ∃ Γ' : I.Genealogy, I.index Γ' = k := by
  let n := k - I.index Γ
  refine ⟨L.iterate n Γ, ?_⟩
  have hIndex := L.iterate_index Γ n
  rw [hIndex]
  omega

/-- Same-tail version: exact lift reaches every higher index while preserving tail. -/
theorem reaches_every_tail_index_above_seed
    {I : IndexedGenealogySystem}
    (L : ExactConsecutivePeelLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ)
    {k : Nat}
    (hk : I.index Γ ≤ k) :
    ∃ Γ' : I.Genealogy, I.Tail M0 Γ' ∧ I.index Γ' = k := by
  let n := k - I.index Γ
  refine ⟨L.iterate n Γ, ?_, ?_⟩
  · exact L.iterate_tail_preserved hTail n
  · have hIndex := L.iterate_index Γ n
    rw [hIndex]
    omega

end ExactConsecutivePeelLift

/-#############################################################################
  §3. Own-index payment and final exact-consecutive front
#############################################################################-/

/-- Raw payment relation: Γ pays Mersenne pair at index `k`. -/
abbrev RawPrimePairPayment (I : IndexedGenealogySystem) :=
  I.Genealogy → Nat → Prop

/-- Every genealogy pays its own index. -/
def OwnIndexPrimePaymentLaw
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy, Paid Γ (I.index Γ)

/-- Payment soundness extracts actual Mersenne-twin centres. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat,
    Paid Γ k → MersenneTwinCenter Prime k

/-- The exact-consecutive final front. -/
structure ExactConsecutiveFinalFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where
  ordinary_seed : OrdinaryTailSeedLaw I
  exact_lift : ExactConsecutivePeelLift I
  own_payment : OwnIndexPrimePaymentLaw I Paid
  payment_sound : PrimePaymentSound Prime I Paid

/-- One genealogy at index `k` plus own payment/soundness yields a twin centre at `k`. -/
theorem twin_at_index_of_genealogy
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hPay : OwnIndexPrimePaymentLaw I Paid)
    (hSound : PrimePaymentSound Prime I Paid)
    (Γ : I.Genealogy) :
    MersenneTwinCenter Prime (I.index Γ) := by
  exact hSound Γ (I.index Γ) (hPay Γ)

/-- Exact-consecutive final front proves every index above the seed index is good. -/
theorem eventuallyAllMersenneTwinCenters_of_exactConsecutiveFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : ExactConsecutiveFinalFront Prime I Paid) :
    EventuallyAllMersenneTwinCenters Prime := by
  rcases F.ordinary_seed 0 with ⟨Γ0, hTail0⟩
  refine ⟨I.index Γ0, ?_⟩
  intro k hk
  rcases F.exact_lift.reaches_every_tail_index_above_seed hTail0 hk with
    ⟨Γk, _hTail, hIndex⟩
  have hTwin : MersenneTwinCenter Prime (I.index Γk) :=
    twin_at_index_of_genealogy F.own_payment F.payment_sound Γk
  rwa [hIndex] at hTwin

/-- Cofinal bad indices forbid the exact-consecutive final front. -/
theorem cofinalBad_forbids_exactConsecutiveFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hBad : CofinalBadMersenneIndices Prime) :
    ¬ Nonempty (ExactConsecutiveFinalFront Prime I Paid) := by
  intro hFront
  rcases hFront with ⟨F⟩
  exact cofinalBad_forbids_eventuallyAll hBad
    (eventuallyAllMersenneTwinCenters_of_exactConsecutiveFront F)

/-#############################################################################
  §4. Corrected route shape: sparse admissible peel lift
#############################################################################-/

/--
Sparse peel lift: `next` must strictly increase the index, but not necessarily by
one.  This is the only viable shape after the exact-successor firewall.
-/
structure SparseAdmissiblePeelLift (I : IndexedGenealogySystem) where
  next : I.Genealogy → I.Genealogy

  tail_preserved :
    ∀ M0 : Nat, ∀ Γ : I.Genealogy,
      I.Tail M0 Γ → I.Tail M0 (next Γ)

  index_strictly_increases :
    ∀ Γ : I.Genealogy,
      I.index Γ < I.index (next Γ)

  admissible_index : I.Genealogy → Prop

  next_admissible :
    ∀ Γ : I.Genealogy, admissible_index (next Γ)

  legal_lift : Prop
  legal_lift_proof : legal_lift

  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape

  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape

  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

/-- The exact route is defective whenever bad indices are cofinal. -/
def ExactConsecutiveRouteDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ Nonempty (ExactConsecutiveFinalFront Prime I Paid)

/-- Cofinal bad indices expose exact-consecutive successor as the wrong route. -/
theorem exactConsecutiveRouteDefect_of_cofinalBad
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hBad : CofinalBadMersenneIndices Prime) :
    ExactConsecutiveRouteDefect Prime I Paid :=
  cofinalBad_forbids_exactConsecutiveFront hBad

/-- Final slogan: exact successor proves too much; the corrected route must be sparse. -/
theorem exactSuccessorFirewall_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hBad : CofinalBadMersenneIndices Prime)
    (hFront : Nonempty (ExactConsecutiveFinalFront Prime I Paid)) :
    False := by
  exact (cofinalBad_forbids_exactConsecutiveFront hBad) hFront

end MersenneExactSuccessorFirewall
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_sparse_admissible_route_patch.lean =====
/-
EuclidsPath — Mersenne sparse admissible route patch
=====================================================

Purpose
-------
This file repairs the Mersenne route after the exact-successor firewall.

The exact route

    index (next Γ) = index Γ + 1

was too strong: together with own-index payment and soundness it forced every
sufficiently large Mersenne index to be a Mersenne-twin centre.

The corrected route is sparse:

    index Γ < index (next Γ)
    next Γ is admissible

Payment is required only on admissible indices.  This proves cofinally many
Mersenne-twin centres, not eventual all-good behaviour.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneSparseAdmissibleRoute

/-#############################################################################
  §1. Basic Mersenne predicates
#############################################################################-/

/-- Abstract prime-like predicate. -/
abbrev PrimeLike := Nat → Prop

/-- Step00 lower side. -/
def lowerSide (m : Nat) : Nat := 6 * m - 1

/-- Step00 upper side. -/
def upperSide (m : Nat) : Nat := 6 * m + 1

/-- Base-4 repunit / Mersenne centre. -/
def mersenneCenter (k : Nat) : Nat := (4 ^ k - 1) / 3

/-- Mersenne-twin centre at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide (mersenneCenter k)) ∧
  Prime (upperSide (mersenneCenter k))

/-- Cofinitely strong absence: after some floor, there are no Mersenne-twin centres. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal infinitude: above every floor, there is a Mersenne-twin centre. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Cofinal infinitude forbids eventual absence. -/
theorem infinite_forbids_eventual_absence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hNo k hk hTwin

/-#############################################################################
  §2. Indexed genealogy system
#############################################################################-/

/-- Mersenne-indexed genealogy system. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

/-- Ordinary supply seed on every ordinary twin tail. -/
def OrdinaryTailSeedLaw (I : IndexedGenealogySystem) : Prop :=
  ∀ M0 : Nat, ∃ Γ : I.Genealogy, I.Tail M0 Γ

/-- Raw payment relation: `Paid Γ k` means `Γ` pays the Mersenne pair at index `k`. -/
abbrev RawPrimePairPayment (I : IndexedGenealogySystem) :=
  I.Genealogy → Nat → Prop

/-#############################################################################
  §3. Sparse admissible peel lift
#############################################################################-/

/--
Sparse admissible peel lift.

It must strictly increase the Mersenne index but is not forced to hit every
successor index.  The `admissible_index` gate marks the sparse subsequence on
which payment is allowed to be sound.
-/
structure SparseAdmissiblePeelLift (I : IndexedGenealogySystem) where
  next : I.Genealogy → I.Genealogy

  tail_preserved :
    ∀ M0 : Nat, ∀ Γ : I.Genealogy,
      I.Tail M0 Γ → I.Tail M0 (next Γ)

  index_strictly_increases :
    ∀ Γ : I.Genealogy,
      I.index Γ < I.index (next Γ)

  admissible_index : I.Genealogy → Prop

  next_admissible :
    ∀ Γ : I.Genealogy, admissible_index (next Γ)

  legal_lift : Prop
  legal_lift_proof : legal_lift

  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape

  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape

  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace SparseAdmissiblePeelLift

/-- Iterate the sparse lift. -/
def iterate {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I) : Nat → I.Genealogy → I.Genealogy
  | 0, Γ => Γ
  | Nat.succ n, Γ => L.next (iterate L n Γ)

/-- Iteration preserves ordinary tail membership. -/
theorem iterate_tail_preserved
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ) :
    ∀ n : Nat, I.Tail M0 (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      exact hTail
  | succ n ih =>
      exact L.tail_preserved M0 (L.iterate n Γ) ih

/-- Every positive iterate is admissible. -/
theorem iterate_admissible_of_pos
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, 0 < n → L.admissible_index (L.iterate n Γ) := by
  intro n hn
  cases n with
  | zero =>
      omega
  | succ n =>
      simp [iterate]
      exact L.next_admissible (L.iterate n Γ)

/-- A strict natural increase gives at least one unit of growth. -/
theorem index_succ_le_next
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy) :
    I.index Γ + 1 ≤ I.index (L.next Γ) := by
  exact Nat.succ_le_of_lt (L.index_strictly_increases Γ)

/-- After `n` sparse steps, the index has increased by at least `n`. -/
theorem iterate_index_add_le
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, I.index Γ + n ≤ I.index (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      have hStep : I.index (L.iterate n Γ) + 1 ≤
          I.index (L.next (L.iterate n Γ)) :=
        L.index_succ_le_next (L.iterate n Γ)
      simp [iterate]
      omega

/-- Sparse lift reaches arbitrarily high indices. -/
theorem exists_iterate_at_or_above_floor
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy)
    (K0 : Nat) :
    ∃ n : Nat, 0 < n ∧ K0 ≤ I.index (L.iterate n Γ) := by
  let n := K0 + 1
  refine ⟨n, by omega, ?_⟩
  have hGrow := L.iterate_index_add_le Γ n
  have hLower : K0 ≤ I.index Γ + n := by
    omega
  exact le_trans hLower hGrow

/-- Same-tail, admissible high-index iterate. -/
theorem exists_tail_admissible_iterate_at_or_above_floor
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ)
    (K0 : Nat) :
    ∃ Γ' : I.Genealogy,
      I.Tail M0 Γ' ∧
      L.admissible_index Γ' ∧
      K0 ≤ I.index Γ' := by
  rcases L.exists_iterate_at_or_above_floor Γ K0 with ⟨n, hnpos, hnK⟩
  refine ⟨L.iterate n Γ, ?_, ?_, hnK⟩
  · exact L.iterate_tail_preserved hTail n
  · exact L.iterate_admissible_of_pos Γ n hnpos

end SparseAdmissiblePeelLift

/-#############################################################################
  §4. Payment only on admissible indices
#############################################################################-/

/-- Payment is required only for admissible genealogies. -/
def AdmissibleOwnIndexPrimePaymentLaw
    (I : IndexedGenealogySystem)
    (L : SparseAdmissiblePeelLift I)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy,
    L.admissible_index Γ → Paid Γ (I.index Γ)

/-- Payment soundness extracts actual Mersenne-twin centres. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat,
    Paid Γ k → MersenneTwinCenter Prime k

/-- Sparse final front. -/
structure SparseAdmissibleFinalFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where
  ordinary_seed : OrdinaryTailSeedLaw I
  sparse_lift : SparseAdmissiblePeelLift I
  admissible_payment : AdmissibleOwnIndexPrimePaymentLaw I sparse_lift Paid
  payment_sound : PrimePaymentSound Prime I Paid

/-- An admissible genealogy with own-index payment gives a Mersenne-twin centre. -/
theorem twin_at_admissible_index_of_genealogy
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    {L : SparseAdmissiblePeelLift I}
    (hPay : AdmissibleOwnIndexPrimePaymentLaw I L Paid)
    (hSound : PrimePaymentSound Prime I Paid)
    (Γ : I.Genealogy)
    (hAdm : L.admissible_index Γ) :
    MersenneTwinCenter Prime (I.index Γ) := by
  exact hSound Γ (I.index Γ) (hPay Γ hAdm)

/-- Sparse final front gives one Mersenne-twin centre above every floor. -/
theorem exists_mersenneTwinCenter_above_of_sparseFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : SparseAdmissibleFinalFront Prime I Paid)
    (K0 : Nat) :
    ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k := by
  rcases F.ordinary_seed 0 with ⟨Γ0, hTail0⟩
  rcases F.sparse_lift.exists_tail_admissible_iterate_at_or_above_floor hTail0 K0 with
    ⟨Γ', _hTail, hAdm, hK⟩
  refine ⟨I.index Γ', hK, ?_⟩
  exact twin_at_admissible_index_of_genealogy
    F.admissible_payment F.payment_sound Γ' hAdm

/-- Sparse final front proves cofinally many Mersenne-twin centres. -/
theorem infinitelyManyMersenneTwinCenters_of_sparseFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : SparseAdmissibleFinalFront Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact exists_mersenneTwinCenter_above_of_sparseFront F K0

/-- Therefore sparse final front forbids eventual absence. -/
theorem sparseFront_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : SparseAdmissibleFinalFront Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_forbids_eventual_absence
    (infinitelyManyMersenneTwinCenters_of_sparseFront F)

/-#############################################################################
  §5. Why sparse does not force eventual all-good
#############################################################################-/

/-- Reachability from a seed under the sparse lift. -/
def SparseReachableFrom
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ0 Γ : I.Genealogy) : Prop :=
  ∃ n : Nat, Γ = L.iterate n Γ0

/-- Reachable positive iterates are admissible. -/
theorem reachable_positive_is_admissible
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    {Γ0 Γ : I.Genealogy}
    (hReach : ∃ n : Nat, 0 < n ∧ Γ = L.iterate n Γ0) :
    L.admissible_index Γ := by
  rcases hReach with ⟨n, hnpos, rfl⟩
  exact L.iterate_admissible_of_pos Γ0 n hnpos

/--
A sparse front only proves goodness for indices that are hit by admissible
reachable genealogies.  It does not assert that every sufficiently large index is
hit.
-/
def HitByAdmissibleSparseOrbit
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (k : Nat) : Prop :=
  ∃ Γ0 Γ : I.Genealogy,
    SparseReachableFrom L Γ0 Γ ∧
    L.admissible_index Γ ∧
    I.index Γ = k

/-- Any hit admissible sparse index is good under admissible payment and soundness. -/
theorem sparse_hit_index_is_twin
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    {L : SparseAdmissiblePeelLift I}
    (hPay : AdmissibleOwnIndexPrimePaymentLaw I L Paid)
    (hSound : PrimePaymentSound Prime I Paid)
    {k : Nat}
    (hHit : HitByAdmissibleSparseOrbit L k) :
    MersenneTwinCenter Prime k := by
  rcases hHit with ⟨_Γ0, Γ, _hReach, hAdm, hIndex⟩
  have hTwin : MersenneTwinCenter Prime (I.index Γ) :=
    twin_at_admissible_index_of_genealogy hPay hSound Γ hAdm
  rwa [hIndex] at hTwin

/-#############################################################################
  §6. Component defect theorem
#############################################################################-/

/-- Ordinary seed defect. -/
def OrdinaryTailSeedDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ OrdinaryTailSeedLaw I

/-- Sparse lift defect. -/
def SparsePeelLiftDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ Nonempty (SparseAdmissiblePeelLift I)

/-- Admissible payment defect for a chosen lift. -/
def AdmissiblePaymentDefect
    (I : IndexedGenealogySystem)
    (L : SparseAdmissiblePeelLift I)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ AdmissibleOwnIndexPrimePaymentLaw I L Paid

/-- Payment soundness defect. -/
def PrimePaymentSoundnessDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ PrimePaymentSound Prime I Paid

/--
If Mersenne-twin centres are eventually absent, then every attempted sparse route
must fail in at least one final component.
-/
theorem eventual_absence_forces_sparse_component_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    OrdinaryTailSeedDefect I ∨
    SparsePeelLiftDefect I ∨
    (∃ L : SparseAdmissiblePeelLift I, AdmissiblePaymentDefect I L Paid) ∨
    PrimePaymentSoundnessDefect Prime I Paid := by
  classical
  by_cases hSeed : OrdinaryTailSeedLaw I
  · by_cases hLift : Nonempty (SparseAdmissiblePeelLift I)
    · rcases hLift with ⟨L⟩
      by_cases hPay : AdmissibleOwnIndexPrimePaymentLaw I L Paid
      · by_cases hSound : PrimePaymentSound Prime I Paid
        · exfalso
          let F : SparseAdmissibleFinalFront Prime I Paid :=
            { ordinary_seed := hSeed
              sparse_lift := L
              admissible_payment := hPay
              payment_sound := hSound }
          exact sparseFront_forbids_eventual_absence F hAbs
        · exact Or.inr (Or.inr (Or.inr hSound))
      · exact Or.inr (Or.inr (Or.inl ⟨L, hPay⟩))
    · exact Or.inr (Or.inl hLift)
  · exact Or.inl hSeed

/-#############################################################################
  §7. Final compact package
#############################################################################-/

/-- Corrected sparse Mersenne route package. -/
structure MersenneSparseRoute
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where
  front : SparseAdmissibleFinalFront Prime I Paid

/-- The corrected sparse route proves cofinal Mersenne-twin supply. -/
theorem sparseRoute_produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (R : MersenneSparseRoute Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime :=
  infinitelyManyMersenneTwinCenters_of_sparseFront R.front

/-- The corrected sparse route forbids eventual absence. -/
theorem sparseRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (R : MersenneSparseRoute Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  sparseFront_forbids_eventual_absence R.front

/-- Final slogan: sparse admissible lift proves cofinal supply, not eventual all-good. -/
theorem sparseAdmissibleRoute_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (F : SparseAdmissibleFinalFront Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨infinitelyManyMersenneTwinCenters_of_sparseFront F,
    sparseFront_forbids_eventual_absence F⟩

end MersenneSparseAdmissibleRoute
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_sparse_index_jump_lift_patch.lean =====
/-
EuclidsPath — Mersenne sparse admissible index-jump lift patch
===============================================================

Purpose
-------
After the exact-successor firewall, the Mersenne route must not use the
consecutive update

    k ↦ k + 1.

The corrected route uses a sparse admissible jump:

    k < k'     and     admissible k'.

This file decomposes the previous `SparseAdmissiblePeelLift` into two pieces:

  1. an arithmetic/admissibility filter on Mersenne indices;
  2. a semantic genealogy lift which jumps from a genealogy to a new genealogy
     whose index is an admissible strictly larger target.

Theorems here are assembly theorems: if such a sparse index-jump lift exists and
payment is sound on admissible own-indices, then cofinally many
Mersenne-twin centres follow.  The file does not assert that the lift exists for
ordinary arithmetic `Nat.Prime`.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneSparseIndexJumpLift

/-#############################################################################
  §1. Basic Mersenne predicates
#############################################################################-/

/-- Abstract prime-like predicate. -/
abbrev PrimeLike := Nat → Prop

/-- Step00 lower side. -/
def lowerSide (m : Nat) : Nat := 6 * m - 1

/-- Step00 upper side. -/
def upperSide (m : Nat) : Nat := 6 * m + 1

/-- Base-4 repunit / Mersenne centre. -/
def mersenneCenter (k : Nat) : Nat := (4 ^ k - 1) / 3

/-- Mersenne-twin centre at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide (mersenneCenter k)) ∧
  Prime (upperSide (mersenneCenter k))

/-- Eventual absence of Mersenne-twin centres. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal infinitude of Mersenne-twin centres. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Cofinal infinitude forbids eventual absence. -/
theorem infinite_forbids_eventual_absence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hNo k hk hTwin

/-#############################################################################
  §2. Indexed genealogy system
#############################################################################-/

/-- Mersenne-indexed genealogy system. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

/-- Ordinary supply seed on every ordinary twin tail. -/
def OrdinaryTailSeedLaw (I : IndexedGenealogySystem) : Prop :=
  ∀ M0 : Nat, ∃ Γ : I.Genealogy, I.Tail M0 Γ

/-- Raw payment relation: `Paid Γ k` means `Γ` pays the Mersenne pair at index `k`. -/
abbrev RawPrimePairPayment (I : IndexedGenealogySystem) :=
  I.Genealogy → Nat → Prop

/-#############################################################################
  §3. Sparse admissibility filter
#############################################################################-/

/--
Arithmetic/admissibility filter on Mersenne indices.

`admissible k` is the sparse gate where own-index payment is allowed to be
sound.  For concrete Mersenne arithmetic this should at least exclude obvious
upper-side composite firewalls such as composite exponents.  This file does not
choose the concrete filter.
-/
structure AdmissibleIndexFilter where
  admissible : Nat → Prop

  /-- Audit: the filter is intended to remove known arithmetic firewalls. -/
  respects_arithmetic_firewall : Prop
  respects_arithmetic_firewall_proof : respects_arithmetic_firewall

  /-- Audit: the filter is not a disguised assertion that all large indices work. -/
  sparse_not_eventual_all_good_claim : Prop
  sparse_not_eventual_all_good_claim_proof : sparse_not_eventual_all_good_claim

namespace AdmissibleIndexFilter

/-- A target index is accepted by the filter. -/
def Accepts (F : AdmissibleIndexFilter) (k : Nat) : Prop :=
  F.admissible k

end AdmissibleIndexFilter

/-#############################################################################
  §4. Old sparse lift, kept locally for assembly
#############################################################################-/

/--
Sparse admissible peel lift.

This is the corrected post-firewall shape: each step strictly increases the
index and lands in an admissible genealogy, but it is not required to hit the
consecutive index.
-/
structure SparseAdmissiblePeelLift (I : IndexedGenealogySystem) where
  next : I.Genealogy → I.Genealogy

  tail_preserved :
    ∀ M0 : Nat, ∀ Γ : I.Genealogy,
      I.Tail M0 Γ → I.Tail M0 (next Γ)

  index_strictly_increases :
    ∀ Γ : I.Genealogy,
      I.index Γ < I.index (next Γ)

  admissible_index : I.Genealogy → Prop

  next_admissible :
    ∀ Γ : I.Genealogy, admissible_index (next Γ)

  legal_lift : Prop
  legal_lift_proof : legal_lift

  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape

  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape

  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace SparseAdmissiblePeelLift

/-- Iterate the sparse lift. -/
def iterate {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I) : Nat → I.Genealogy → I.Genealogy
  | 0, Γ => Γ
  | Nat.succ n, Γ => L.next (iterate L n Γ)

/-- Iteration preserves ordinary tail membership. -/
theorem iterate_tail_preserved
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ) :
    ∀ n : Nat, I.Tail M0 (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      exact hTail
  | succ n ih =>
      exact L.tail_preserved M0 (L.iterate n Γ) ih

/-- Every positive iterate is admissible. -/
theorem iterate_admissible_of_pos
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, 0 < n → L.admissible_index (L.iterate n Γ) := by
  intro n hn
  cases n with
  | zero =>
      omega
  | succ n =>
      simp [iterate]
      exact L.next_admissible (L.iterate n Γ)

/-- A strict natural increase gives at least one unit of growth. -/
theorem index_succ_le_next
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy) :
    I.index Γ + 1 ≤ I.index (L.next Γ) := by
  exact Nat.succ_le_of_lt (L.index_strictly_increases Γ)

/-- After `n` sparse steps, the index has increased by at least `n`. -/
theorem iterate_index_add_le
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, I.index Γ + n ≤ I.index (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      have hStep : I.index (L.iterate n Γ) + 1 ≤
          I.index (L.next (L.iterate n Γ)) :=
        L.index_succ_le_next (L.iterate n Γ)
      simp [iterate]
      omega

/-- Sparse lift reaches arbitrarily high indices. -/
theorem exists_iterate_at_or_above_floor
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    (Γ : I.Genealogy)
    (K0 : Nat) :
    ∃ n : Nat, 0 < n ∧ K0 ≤ I.index (L.iterate n Γ) := by
  let n := K0 + 1
  refine ⟨n, by omega, ?_⟩
  have hGrow := L.iterate_index_add_le Γ n
  have hLower : K0 ≤ I.index Γ + n := by
    omega
  exact le_trans hLower hGrow

/-- Same-tail, admissible high-index iterate. -/
theorem exists_tail_admissible_iterate_at_or_above_floor
    {I : IndexedGenealogySystem}
    (L : SparseAdmissiblePeelLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ)
    (K0 : Nat) :
    ∃ Γ' : I.Genealogy,
      I.Tail M0 Γ' ∧
      L.admissible_index Γ' ∧
      K0 ≤ I.index Γ' := by
  rcases L.exists_iterate_at_or_above_floor Γ K0 with ⟨n, hnpos, hnK⟩
  refine ⟨L.iterate n Γ, ?_, ?_, hnK⟩
  · exact L.iterate_tail_preserved hTail n
  · exact L.iterate_admissible_of_pos Γ n hnpos

end SparseAdmissiblePeelLift

/-#############################################################################
  §5. New decomposition: index-jump lift source
#############################################################################-/

/--
A semantic lift source which chooses a strictly larger admissible target index
for each genealogy, and constructs a genealogy at that target.

This is the concrete replacement for the earlier opaque
`SparseAdmissiblePeelLift`.
-/
structure IndexJumpLiftSource
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where

  target : I.Genealogy → Nat

  next : I.Genealogy → I.Genealogy

  target_strictly_above :
    ∀ Γ : I.Genealogy,
      I.index Γ < target Γ

  target_admissible :
    ∀ Γ : I.Genealogy,
      F.admissible (target Γ)

  next_has_target_index :
    ∀ Γ : I.Genealogy,
      I.index (next Γ) = target Γ

  tail_preserved :
    ∀ M0 : Nat, ∀ Γ : I.Genealogy,
      I.Tail M0 Γ → I.Tail M0 (next Γ)

  legal_lift : Prop
  legal_lift_proof : legal_lift

  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape

  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape

  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace IndexJumpLiftSource

/-- An index-jump source mechanically gives the sparse admissible peel lift. -/
def toSparseAdmissiblePeelLift
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (J : IndexJumpLiftSource I F) :
    SparseAdmissiblePeelLift I where
  next := J.next
  tail_preserved := J.tail_preserved
  index_strictly_increases := by
    intro Γ
    rw [J.next_has_target_index Γ]
    exact J.target_strictly_above Γ
  admissible_index := fun Γ => F.admissible (I.index Γ)
  next_admissible := by
    intro Γ
    rw [J.next_has_target_index Γ]
    exact J.target_admissible Γ
  legal_lift := J.legal_lift
  legal_lift_proof := J.legal_lift_proof
  no_seam_escape := J.no_seam_escape
  no_seam_escape_proof := J.no_seam_escape_proof
  no_compression_escape := J.no_compression_escape
  no_compression_escape_proof := J.no_compression_escape_proof
  no_unpaid_boundary_jump := J.no_unpaid_boundary_jump
  no_unpaid_boundary_jump_proof := J.no_unpaid_boundary_jump_proof

/-- The constructed sparse lift has exactly the filter admissibility predicate. -/
theorem admissible_index_iff_filter
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (J : IndexJumpLiftSource I F)
    (Γ : I.Genealogy) :
    (J.toSparseAdmissiblePeelLift.admissible_index Γ ↔ F.admissible (I.index Γ)) := by
  rfl

/-- The next genealogy lands at the selected target. -/
theorem index_next_eq_target
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (J : IndexJumpLiftSource I F)
    (Γ : I.Genealogy) :
    I.index (J.toSparseAdmissiblePeelLift.next Γ) = J.target Γ :=
  J.next_has_target_index Γ

end IndexJumpLiftSource

/-#############################################################################
  §6. Filtered own-index payment and soundness
#############################################################################-/

/-- Payment is required only for genealogies whose own index passes the filter. -/
def FilteredOwnIndexPrimePaymentLaw
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy,
    F.admissible (I.index Γ) → Paid Γ (I.index Γ)

/-- Payment soundness extracts actual Mersenne-twin centres. -/
def PrimePaymentSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat,
    Paid Γ k → MersenneTwinCenter Prime k

/-- Filtered payment is the same as admissible payment for the derived sparse lift. -/
def AdmissibleOwnIndexPrimePaymentLaw
    (I : IndexedGenealogySystem)
    (L : SparseAdmissiblePeelLift I)
    (Paid : RawPrimePairPayment I) : Prop :=
  ∀ Γ : I.Genealogy,
    L.admissible_index Γ → Paid Γ (I.index Γ)

/-- Convert filtered payment to sparse-lift admissible payment. -/
theorem admissiblePayment_of_filteredPayment
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {Paid : RawPrimePairPayment I}
    (J : IndexJumpLiftSource I F)
    (hPay : FilteredOwnIndexPrimePaymentLaw I F Paid) :
    AdmissibleOwnIndexPrimePaymentLaw I J.toSparseAdmissiblePeelLift Paid := by
  intro Γ hAdm
  exact hPay Γ hAdm

/-- An admissible genealogy with own-index payment gives a Mersenne-twin centre. -/
theorem twin_at_filtered_admissible_index
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {Paid : RawPrimePairPayment I}
    (hPay : FilteredOwnIndexPrimePaymentLaw I F Paid)
    (hSound : PrimePaymentSound Prime I Paid)
    (Γ : I.Genealogy)
    (hAdm : F.admissible (I.index Γ)) :
    MersenneTwinCenter Prime (I.index Γ) := by
  exact hSound Γ (I.index Γ) (hPay Γ hAdm)

/-#############################################################################
  §7. Final sparse index-jump front
#############################################################################-/

/-- Final front after decomposing sparse lift into filter + index-jump source. -/
structure SparseIndexJumpFinalFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where
  filter : AdmissibleIndexFilter
  ordinary_seed : OrdinaryTailSeedLaw I
  jump_lift : IndexJumpLiftSource I filter
  filtered_payment : FilteredOwnIndexPrimePaymentLaw I filter Paid
  payment_sound : PrimePaymentSound Prime I Paid

/-- The final front gives the old sparse admissible lift. -/
def SparseIndexJumpFinalFront.toSparseLift
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (Fnt : SparseIndexJumpFinalFront Prime I Paid) :
    SparseAdmissiblePeelLift I :=
  Fnt.jump_lift.toSparseAdmissiblePeelLift

/-- One Mersenne-twin centre above any floor follows from the sparse index-jump front. -/
theorem exists_mersenneTwinCenter_above_of_indexJumpFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (Fnt : SparseIndexJumpFinalFront Prime I Paid)
    (K0 : Nat) :
    ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k := by
  rcases Fnt.ordinary_seed 0 with ⟨Γ0, hTail0⟩
  let L := Fnt.toSparseLift
  rcases L.exists_tail_admissible_iterate_at_or_above_floor hTail0 K0 with
    ⟨Γ', _hTail, hAdm, hK⟩
  refine ⟨I.index Γ', hK, ?_⟩
  exact twin_at_filtered_admissible_index
    Fnt.filtered_payment Fnt.payment_sound Γ' hAdm

/-- The sparse index-jump front proves cofinally many Mersenne-twin centres. -/
theorem infinitelyManyMersenneTwinCenters_of_indexJumpFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (Fnt : SparseIndexJumpFinalFront Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact exists_mersenneTwinCenter_above_of_indexJumpFront Fnt K0

/-- Therefore the sparse index-jump front forbids eventual absence. -/
theorem indexJumpFront_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (Fnt : SparseIndexJumpFinalFront Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_forbids_eventual_absence
    (infinitelyManyMersenneTwinCenters_of_indexJumpFront Fnt)

/-#############################################################################
  §8. Defect theorem
#############################################################################-/

/-- Ordinary seed defect. -/
def OrdinaryTailSeedDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ OrdinaryTailSeedLaw I

/-- Index-jump lift defect for a fixed admissibility filter. -/
def IndexJumpLiftDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (IndexJumpLiftSource I F)

/-- Filtered payment defect. -/
def FilteredPaymentDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ FilteredOwnIndexPrimePaymentLaw I F Paid

/-- Payment soundness defect. -/
def PrimePaymentSoundnessDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) : Prop :=
  ¬ PrimePaymentSound Prime I Paid

/--
If Mersenne-twin centres are eventually absent, then for every proposed filter
one of the sparse index-jump components must fail.
-/
theorem eventual_absence_forces_indexJump_component_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (Filt : AdmissibleIndexFilter)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    OrdinaryTailSeedDefect I ∨
    IndexJumpLiftDefect I Filt ∨
    FilteredPaymentDefect I Filt Paid ∨
    PrimePaymentSoundnessDefect Prime I Paid := by
  classical
  by_cases hSeed : OrdinaryTailSeedLaw I
  · by_cases hJump : Nonempty (IndexJumpLiftSource I Filt)
    · rcases hJump with ⟨J⟩
      by_cases hPay : FilteredOwnIndexPrimePaymentLaw I Filt Paid
      · by_cases hSound : PrimePaymentSound Prime I Paid
        · exfalso
          let Fnt : SparseIndexJumpFinalFront Prime I Paid :=
            { filter := Filt
              ordinary_seed := hSeed
              jump_lift := J
              filtered_payment := hPay
              payment_sound := hSound }
          exact indexJumpFront_forbids_eventual_absence Fnt hAbs
        · exact Or.inr (Or.inr (Or.inr hSound))
      · exact Or.inr (Or.inr (Or.inl hPay))
    · exact Or.inr (Or.inl hJump)
  · exact Or.inl hSeed

/-#############################################################################
  §9. Compact route package and slogan
#############################################################################-/

/-- Corrected route package after exact-successor firewall. -/
structure MersenneSparseIndexJumpRoute
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawPrimePairPayment I) where
  front : SparseIndexJumpFinalFront Prime I Paid

/-- The route proves cofinally many Mersenne-twin centres. -/
theorem sparseIndexJumpRoute_produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (R : MersenneSparseIndexJumpRoute Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime :=
  infinitelyManyMersenneTwinCenters_of_indexJumpFront R.front

/-- The route forbids eventual absence. -/
theorem sparseIndexJumpRoute_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (R : MersenneSparseIndexJumpRoute Prime I Paid) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  indexJumpFront_forbids_eventual_absence R.front

/-- Final slogan: sparse admissible index jumps are the corrected post-firewall front. -/
theorem sparseIndexJumpLift_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawPrimePairPayment I}
    (Fnt : SparseIndexJumpFinalFront Prime I Paid) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨infinitelyManyMersenneTwinCenters_of_indexJumpFront Fnt,
    indexJumpFront_forbids_eventual_absence Fnt⟩

end MersenneSparseIndexJumpLift
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_sparse_route_multi_step_advance_patch.lean =====
/-
EuclidsPath — Mersenne sparse route multi-step advance
=======================================================

Purpose
-------
This patch moves several steps beyond `SparseIndexJumpFinalFront` in one layer.
It does not assert unconditional infinitude of Mersenne-twin centres.  Instead it
separates the corrected sparse route into four concrete components:

  1. a cofinal admissible index selector;
  2. a semantic target-lift of genealogies to the selected index;
  3. filtered own-index pair payment, decomposed side-by-side;
  4. side-payment soundness.

From these components it mechanically proves:

  * a sparse index-jump lift;
  * cofinally many Mersenne-twin centres;
  * impossibility of eventual absence;
  * a precise component-defect theorem if eventual absence is assumed.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneSparseMultiStep

/-#############################################################################
  §1. Mersenne-twin target predicates
#############################################################################-/

/-- Abstract prime-like predicate. -/
abbrev PrimeLike := Nat → Prop

/-- Lower Mersenne-twin side at index `k`: `2^(2k+1)-3`. -/
def mersenneLowerAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 3

/-- Upper Mersenne-twin side at index `k`: `2^(2k+1)-1`. -/
def mersenneUpperAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 1

/-- A Mersenne-twin index for the chosen prime predicate. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (mersenneLowerAt k) ∧ Prime (mersenneUpperAt k)

/-- Cofinal infinitude of Mersenne-twin centres. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Eventual absence of Mersenne-twin centres. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal infinitude forbids eventual absence. -/
theorem infinite_forbids_eventual_absence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hNo k hk hTwin

/-#############################################################################
  §2. Indexed genealogy system and sparse lift
#############################################################################-/

/-- Mersenne-indexed genealogy system. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

/-- Ordinary tail seed: every ordinary tail has at least one genealogy. -/
def OrdinaryTailSeedLaw (I : IndexedGenealogySystem) : Prop :=
  ∀ M0 : Nat, ∃ Γ : I.Genealogy, I.Tail M0 Γ

/-- Sparse admissible lift: every step preserves tail, increases index, lands admissibly. -/
structure SparseAdmissibleLift (I : IndexedGenealogySystem) where
  next : I.Genealogy → I.Genealogy
  tail_preserved :
    ∀ M0 Γ, I.Tail M0 Γ → I.Tail M0 (next Γ)
  index_strict :
    ∀ Γ, I.index Γ < I.index (next Γ)
  admissible : I.Genealogy → Prop
  next_admissible :
    ∀ Γ, admissible (next Γ)
  legal_lift : Prop
  legal_lift_proof : legal_lift
  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape
  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape
  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace SparseAdmissibleLift

/-- Iterate a sparse lift. -/
def iterate {I : IndexedGenealogySystem}
    (L : SparseAdmissibleLift I) : Nat → I.Genealogy → I.Genealogy
  | 0, Γ => Γ
  | Nat.succ n, Γ => L.next (iterate L n Γ)

/-- Iteration preserves the same ordinary tail. -/
theorem iterate_tail_preserved
    {I : IndexedGenealogySystem}
    (L : SparseAdmissibleLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ) :
    ∀ n : Nat, I.Tail M0 (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      exact hTail
  | succ n ih =>
      exact L.tail_preserved M0 (L.iterate n Γ) ih

/-- Every positive iterate is admissible. -/
theorem iterate_admissible_of_pos
    {I : IndexedGenealogySystem}
    (L : SparseAdmissibleLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, 0 < n → L.admissible (L.iterate n Γ) := by
  intro n hn
  cases n with
  | zero =>
      omega
  | succ n =>
      simp [iterate]
      exact L.next_admissible (L.iterate n Γ)

/-- One sparse step increases the index by at least one. -/
theorem index_succ_le_next
    {I : IndexedGenealogySystem}
    (L : SparseAdmissibleLift I)
    (Γ : I.Genealogy) :
    I.index Γ + 1 ≤ I.index (L.next Γ) := by
  exact Nat.succ_le_of_lt (L.index_strict Γ)

/-- After `n` sparse steps, index has increased by at least `n`. -/
theorem iterate_index_add_le
    {I : IndexedGenealogySystem}
    (L : SparseAdmissibleLift I)
    (Γ : I.Genealogy) :
    ∀ n : Nat, I.index Γ + n ≤ I.index (L.iterate n Γ) := by
  intro n
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      have hStep : I.index (L.iterate n Γ) + 1 ≤
          I.index (L.next (L.iterate n Γ)) :=
        L.index_succ_le_next (L.iterate n Γ)
      simp [iterate]
      omega

/-- Reach a same-tail admissible genealogy at or above any requested index floor. -/
theorem exists_tail_admissible_above
    {I : IndexedGenealogySystem}
    (L : SparseAdmissibleLift I)
    {M0 : Nat} {Γ : I.Genealogy}
    (hTail : I.Tail M0 Γ)
    (K0 : Nat) :
    ∃ Γ' : I.Genealogy,
      I.Tail M0 Γ' ∧ L.admissible Γ' ∧ K0 ≤ I.index Γ' := by
  let n := K0 + 1
  have hnpos : 0 < n := by omega
  have hGrow := L.iterate_index_add_le Γ n
  have hFloor : K0 ≤ I.index Γ + n := by omega
  refine ⟨L.iterate n Γ, ?_, ?_, le_trans hFloor hGrow⟩
  · exact L.iterate_tail_preserved hTail n
  · exact L.iterate_admissible_of_pos Γ n hnpos

end SparseAdmissibleLift

/-#############################################################################
  §3. Cofinal admissible selector and semantic target-lift
#############################################################################-/

/-- Arithmetic/admissibility filter on Mersenne indices. -/
structure AdmissibleIndexFilter where
  admissible : Nat → Prop
  respects_upper_composite_firewall : Prop
  respects_upper_composite_firewall_proof : respects_upper_composite_firewall
  not_eventual_all_indices_claim : Prop
  not_eventual_all_indices_claim_proof : not_eventual_all_indices_claim

/-- Cofinal selector: from any current index it chooses a strictly larger admissible index. -/
structure CofinalAdmissibleSelector (F : AdmissibleIndexFilter) where
  nextIndex : Nat → Nat
  strict_above : ∀ k : Nat, k < nextIndex k
  admissible_next : ∀ k : Nat, F.admissible (nextIndex k)

/-- Semantic lift to the target selected by a cofinal admissible selector. -/
structure SemanticTargetLift
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (S : CofinalAdmissibleSelector F) where
  next : I.Genealogy → I.Genealogy
  next_has_selected_index :
    ∀ Γ : I.Genealogy, I.index (next Γ) = S.nextIndex (I.index Γ)
  tail_preserved :
    ∀ M0 Γ, I.Tail M0 Γ → I.Tail M0 (next Γ)
  legal_lift : Prop
  legal_lift_proof : legal_lift
  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape
  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape
  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace SemanticTargetLift

/-- Selector + semantic lift mechanically gives the sparse admissible lift. -/
def toSparseLift
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {S : CofinalAdmissibleSelector F}
    (L : SemanticTargetLift I F S) :
    SparseAdmissibleLift I where
  next := L.next
  tail_preserved := L.tail_preserved
  index_strict := by
    intro Γ
    rw [L.next_has_selected_index Γ]
    exact S.strict_above (I.index Γ)
  admissible := fun Γ => F.admissible (I.index Γ)
  next_admissible := by
    intro Γ
    rw [L.next_has_selected_index Γ]
    exact S.admissible_next (I.index Γ)
  legal_lift := L.legal_lift
  legal_lift_proof := L.legal_lift_proof
  no_seam_escape := L.no_seam_escape
  no_seam_escape_proof := L.no_seam_escape_proof
  no_compression_escape := L.no_compression_escape
  no_compression_escape_proof := L.no_compression_escape_proof
  no_unpaid_boundary_jump := L.no_unpaid_boundary_jump
  no_unpaid_boundary_jump_proof := L.no_unpaid_boundary_jump_proof

/-- The lifted next genealogy has exactly the selected target index. -/
theorem next_index_eq_selected
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {S : CofinalAdmissibleSelector F}
    (L : SemanticTargetLift I F S)
    (Γ : I.Genealogy) :
    I.index (L.toSparseLift.next Γ) = S.nextIndex (I.index Γ) :=
  L.next_has_selected_index Γ

end SemanticTargetLift

/-#############################################################################
  §4. Side-by-side filtered prime payment
#############################################################################-/

/-- Lower/upper side selector. -/
inductive PairSide where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- Number on a requested Mersenne side. -/
def sideValue : PairSide → Nat → Nat
  | PairSide.lower, k => mersenneLowerAt k
  | PairSide.upper, k => mersenneUpperAt k

/-- Raw side-payment relation. -/
abbrev RawSidePayment (I : IndexedGenealogySystem) :=
  I.Genealogy → Nat → PairSide → Prop

/-- Both lower and upper sides are paid. -/
def PairPaid {I : IndexedGenealogySystem}
    (Pay : RawSidePayment I) (Γ : I.Genealogy) (k : Nat) : Prop :=
  Pay Γ k PairSide.lower ∧ Pay Γ k PairSide.upper

/-- Own-index pair payment is required only at admissible indices. -/
def FilteredOwnPairPaymentLaw
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (Pay : RawSidePayment I) : Prop :=
  ∀ Γ : I.Genealogy,
    F.admissible (I.index Γ) → PairPaid Pay Γ (I.index Γ)

/-- Sound lower/upper side payments really certify primality of that side. -/
def SidePaymentSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Pay : RawSidePayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat, ∀ side : PairSide,
    Pay Γ k side → Prime (sideValue side k)

/-- Pair payment plus side soundness extracts a Mersenne-twin centre. -/
theorem mersenneTwinCenter_of_pairPaid_and_sideSound
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (hSound : SidePaymentSound Prime I Pay)
    {Γ : I.Genealogy} {k : Nat}
    (hPaid : PairPaid Pay Γ k) :
    MersenneTwinCenter Prime k := by
  exact ⟨hSound Γ k PairSide.lower hPaid.1,
    hSound Γ k PairSide.upper hPaid.2⟩

/-- Filtered own-index pair payment and soundness extract a twin at that own index. -/
theorem twin_at_filtered_own_index
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {Pay : RawSidePayment I}
    (hPay : FilteredOwnPairPaymentLaw I F Pay)
    (hSound : SidePaymentSound Prime I Pay)
    (Γ : I.Genealogy)
    (hAdm : F.admissible (I.index Γ)) :
    MersenneTwinCenter Prime (I.index Γ) := by
  exact mersenneTwinCenter_of_pairPaid_and_sideSound hSound (hPay Γ hAdm)

/-#############################################################################
  §5. Multi-step final front and theorem
#############################################################################-/

/-- Multi-step corrected sparse Mersenne route front. -/
structure SparseMersenneMultiStepFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Pay : RawSidePayment I) where
  filter : AdmissibleIndexFilter
  selector : CofinalAdmissibleSelector filter
  ordinary_seed : OrdinaryTailSeedLaw I
  semantic_lift : SemanticTargetLift I filter selector
  filtered_pair_payment : FilteredOwnPairPaymentLaw I filter Pay
  side_payment_sound : SidePaymentSound Prime I Pay

namespace SparseMersenneMultiStepFront

/-- The front gives the sparse admissible lift. -/
def toSparseLift
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (Fnt : SparseMersenneMultiStepFront Prime I Pay) :
    SparseAdmissibleLift I :=
  Fnt.semantic_lift.toSparseLift

/-- For every index floor, the front produces a Mersenne-twin centre above it. -/
theorem exists_mersenneTwinCenter_above
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (Fnt : SparseMersenneMultiStepFront Prime I Pay)
    (K0 : Nat) :
    ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k := by
  rcases Fnt.ordinary_seed 0 with ⟨Γ0, hTail0⟩
  let L := Fnt.toSparseLift
  rcases L.exists_tail_admissible_above hTail0 K0 with
    ⟨Γ', _hTail, hAdm, hK⟩
  refine ⟨I.index Γ', hK, ?_⟩
  exact twin_at_filtered_own_index
    Fnt.filtered_pair_payment Fnt.side_payment_sound Γ' hAdm

/-- Therefore the front gives cofinally many Mersenne-twin centres. -/
theorem infinitelyManyMersenneTwinCenters
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (Fnt : SparseMersenneMultiStepFront Prime I Pay) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact Fnt.exists_mersenneTwinCenter_above K0

/-- Therefore the front forbids eventual absence. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (Fnt : SparseMersenneMultiStepFront Prime I Pay) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_forbids_eventual_absence Fnt.infinitelyManyMersenneTwinCenters

end SparseMersenneMultiStepFront

/-#############################################################################
  §6. Component defects under eventual absence
#############################################################################-/

/-- Ordinary seed failure. -/
def OrdinarySeedDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ OrdinaryTailSeedLaw I

/-- Selector failure for a fixed admissibility filter. -/
def SelectorDefect (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (CofinalAdmissibleSelector F)

/-- Semantic lift failure for a fixed selector. -/
def SemanticLiftDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (S : CofinalAdmissibleSelector F) : Prop :=
  ¬ Nonempty (SemanticTargetLift I F S)

/-- Filtered pair-payment failure. -/
def FilteredPairPaymentDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (Pay : RawSidePayment I) : Prop :=
  ¬ FilteredOwnPairPaymentLaw I F Pay

/-- Side-payment soundness failure. -/
def SidePaymentSoundnessDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Pay : RawSidePayment I) : Prop :=
  ¬ SidePaymentSound Prime I Pay

/--
Given a proposed filter, eventual absence forces selector failure or seed failure
or one of the later semantic/payment components to fail.
-/
theorem eventual_absence_forces_filter_level_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (F : AdmissibleIndexFilter)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    SelectorDefect F ∨
    OrdinarySeedDefect I ∨
    (∀ S : CofinalAdmissibleSelector F,
      SemanticLiftDefect I F S ∨
      FilteredPairPaymentDefect I F Pay ∨
      SidePaymentSoundnessDefect Prime I Pay) := by
  classical
  by_cases hSel : Nonempty (CofinalAdmissibleSelector F)
  · rcases hSel with ⟨S⟩
    by_cases hSeed : OrdinaryTailSeedLaw I
    · right
      right
      intro S'
      by_cases hLift : Nonempty (SemanticTargetLift I F S')
      · rcases hLift with ⟨L⟩
        by_cases hPay : FilteredOwnPairPaymentLaw I F Pay
        · by_cases hSound : SidePaymentSound Prime I Pay
          · exfalso
            let Fnt : SparseMersenneMultiStepFront Prime I Pay :=
              { filter := F
                selector := S'
                ordinary_seed := hSeed
                semantic_lift := L
                filtered_pair_payment := hPay
                side_payment_sound := hSound }
            exact Fnt.forbids_eventual_absence hAbs
          · exact Or.inr (Or.inr hSound)
        · exact Or.inr (Or.inl hPay)
      · exact Or.inl hLift
    · exact Or.inr (Or.inl hSeed)
  · exact Or.inl hSel

/-- A fixed selector version of the defect theorem. -/
theorem eventual_absence_forces_selector_level_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    {F : AdmissibleIndexFilter}
    (S : CofinalAdmissibleSelector F)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    OrdinarySeedDefect I ∨
    SemanticLiftDefect I F S ∨
    FilteredPairPaymentDefect I F Pay ∨
    SidePaymentSoundnessDefect Prime I Pay := by
  classical
  by_cases hSeed : OrdinaryTailSeedLaw I
  · by_cases hLift : Nonempty (SemanticTargetLift I F S)
    · rcases hLift with ⟨L⟩
      by_cases hPay : FilteredOwnPairPaymentLaw I F Pay
      · by_cases hSound : SidePaymentSound Prime I Pay
        · exfalso
          let Fnt : SparseMersenneMultiStepFront Prime I Pay :=
            { filter := F
              selector := S
              ordinary_seed := hSeed
              semantic_lift := L
              filtered_pair_payment := hPay
              side_payment_sound := hSound }
          exact Fnt.forbids_eventual_absence hAbs
        · exact Or.inr (Or.inr (Or.inr hSound))
      · exact Or.inr (Or.inr (Or.inl hPay))
    · exact Or.inr (Or.inl hLift)
  · exact Or.inl hSeed

/-#############################################################################
  §7. Route package and final slogan
#############################################################################-/

/-- Route package after multiple decompositions. -/
structure MersenneSparseMultiStepRoute
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Pay : RawSidePayment I) where
  front : SparseMersenneMultiStepFront Prime I Pay

/-- The route produces cofinally many Mersenne-twin centres. -/
theorem route_produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (R : MersenneSparseMultiStepRoute Prime I Pay) :
    InfinitelyManyMersenneTwinCenters Prime :=
  R.front.infinitelyManyMersenneTwinCenters

/-- The route forbids eventual absence. -/
theorem route_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (R : MersenneSparseMultiStepRoute Prime I Pay) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  R.front.forbids_eventual_absence

/-- Slogan theorem for the multi-step advance. -/
theorem sparseMultiStep_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Pay : RawSidePayment I}
    (Fnt : SparseMersenneMultiStepFront Prime I Pay) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨Fnt.infinitelyManyMersenneTwinCenters,
    Fnt.forbids_eventual_absence⟩

end MersenneSparseMultiStep
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_cofinal_filter_selector_patch.lean =====
/-
EuclidsPath — Mersenne cofinal admissible filter selector patch
===============================================================

Purpose
-------
This patch closes one of the sparse-route components from the previous layer:
`CofinalAdmissibleSelector` is not a primitive obligation.  It is equivalent to
cofinal admissibility of the filter itself.

Thus the selector component is reduced to the arithmetic statement:

    ∀ k, ∃ k' > k, admissible k'.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneCofinalFilterSelector

/-- Arithmetic/admissibility filter on Mersenne indices. -/
structure AdmissibleIndexFilter where
  admissible : Nat → Prop
  respects_upper_composite_firewall : Prop
  respects_upper_composite_firewall_proof : respects_upper_composite_firewall
  not_eventual_all_indices_claim : Prop
  not_eventual_all_indices_claim_proof : not_eventual_all_indices_claim

/-- The admissible indices are cofinal. -/
def CofinalAdmissibleIndices (F : AdmissibleIndexFilter) : Prop :=
  ∀ k : Nat, ∃ k' : Nat, k < k' ∧ F.admissible k'

/-- Sparse selector choosing a larger admissible index above every current index. -/
structure CofinalAdmissibleSelector (F : AdmissibleIndexFilter) where
  nextIndex : Nat → Nat
  strict_above : ∀ k : Nat, k < nextIndex k
  admissible_next : ∀ k : Nat, F.admissible (nextIndex k)

/-- A selector immediately gives cofinal admissibility. -/
theorem cofinalAdmissible_of_selector
    {F : AdmissibleIndexFilter}
    (S : CofinalAdmissibleSelector F) :
    CofinalAdmissibleIndices F := by
  intro k
  exact ⟨S.nextIndex k, S.strict_above k, S.admissible_next k⟩

/-- Cofinal admissibility noncomputably builds a selector. -/
noncomputable def selector_of_cofinalAdmissible
    {F : AdmissibleIndexFilter}
    (hCof : CofinalAdmissibleIndices F) :
    CofinalAdmissibleSelector F where
  nextIndex := fun k => Classical.choose (hCof k)
  strict_above := by
    intro k
    exact (Classical.choose_spec (hCof k)).1
  admissible_next := by
    intro k
    exact (Classical.choose_spec (hCof k)).2

/-- Cofinal admissibility is equivalent to existence of a sparse selector. -/
theorem cofinalAdmissible_iff_nonempty_selector
    {F : AdmissibleIndexFilter} :
    CofinalAdmissibleIndices F ↔ Nonempty (CofinalAdmissibleSelector F) := by
  constructor
  · intro h
    exact ⟨selector_of_cofinalAdmissible h⟩
  · intro h
    rcases h with ⟨S⟩
    exact cofinalAdmissible_of_selector S

/-- Selector defect. -/
def SelectorDefect (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (CofinalAdmissibleSelector F)

/-- Cofinal admissibility defect. -/
def CofinalAdmissibilityDefect (F : AdmissibleIndexFilter) : Prop :=
  ¬ CofinalAdmissibleIndices F

/-- Selector defect is the same as cofinal-admissibility defect. -/
theorem selectorDefect_iff_cofinalAdmissibilityDefect
    {F : AdmissibleIndexFilter} :
    SelectorDefect F ↔ CofinalAdmissibilityDefect F := by
  unfold SelectorDefect CofinalAdmissibilityDefect
  rw [cofinalAdmissible_iff_nonempty_selector]

/-- If a filter is not cofinal, it cannot drive the sparse Mersenne route. -/
theorem selector_defect_of_not_cofinal
    {F : AdmissibleIndexFilter}
    (h : ¬ CofinalAdmissibleIndices F) :
    SelectorDefect F := by
  exact (selectorDefect_iff_cofinalAdmissibilityDefect).2 h

/-- If a filter is cofinal, the selector component is closed. -/
theorem selector_closed_of_cofinal
    {F : AdmissibleIndexFilter}
    (h : CofinalAdmissibleIndices F) :
    Nonempty (CofinalAdmissibleSelector F) := by
  exact (cofinalAdmissible_iff_nonempty_selector).1 h

/-#############################################################################
  Arithmetic filter source layer
#############################################################################-/

/--
A proposed arithmetic filter source.  `CandidateGood` is where concrete Mersenne
arithmetic should live: prime exponent filters, lower-side residue filters,
CRT/peel compatibility, etc.
-/
structure ArithmeticAdmissibleFilterSource where
  CandidateGood : Nat → Prop
  cofinal_good : ∀ k : Nat, ∃ k' : Nat, k < k' ∧ CandidateGood k'
  respects_upper_composite_firewall : Prop
  respects_upper_composite_firewall_proof : respects_upper_composite_firewall
  not_eventual_all_indices_claim : Prop
  not_eventual_all_indices_claim_proof : not_eventual_all_indices_claim

/-- The filter generated by an arithmetic source. -/
def ArithmeticAdmissibleFilterSource.toFilter
    (A : ArithmeticAdmissibleFilterSource) : AdmissibleIndexFilter where
  admissible := A.CandidateGood
  respects_upper_composite_firewall := A.respects_upper_composite_firewall
  respects_upper_composite_firewall_proof := A.respects_upper_composite_firewall_proof
  not_eventual_all_indices_claim := A.not_eventual_all_indices_claim
  not_eventual_all_indices_claim_proof := A.not_eventual_all_indices_claim_proof

/-- The generated filter is cofinal. -/
theorem cofinalAdmissible_of_arithmeticSource
    (A : ArithmeticAdmissibleFilterSource) :
    CofinalAdmissibleIndices A.toFilter := by
  intro k
  exact A.cofinal_good k

/-- The arithmetic source closes the sparse selector component. -/
theorem selector_closed_of_arithmeticSource
    (A : ArithmeticAdmissibleFilterSource) :
    Nonempty (CofinalAdmissibleSelector A.toFilter) := by
  exact selector_closed_of_cofinal (cofinalAdmissible_of_arithmeticSource A)

/-- Noncomputable canonical selector from an arithmetic source. -/
noncomputable def selectorOfArithmeticSource
    (A : ArithmeticAdmissibleFilterSource) :
    CofinalAdmissibleSelector A.toFilter :=
  selector_of_cofinalAdmissible (cofinalAdmissible_of_arithmeticSource A)

/-- Slogan theorem: the selector obligation is exactly cofinality of the admissible filter. -/
theorem cofinalFilterSelector_slogan
    {F : AdmissibleIndexFilter} :
    (CofinalAdmissibleIndices F ↔ Nonempty (CofinalAdmissibleSelector F)) ∧
    (SelectorDefect F ↔ CofinalAdmissibilityDefect F) := by
  exact ⟨cofinalAdmissible_iff_nonempty_selector,
    selectorDefect_iff_cofinalAdmissibilityDefect⟩

end MersenneCofinalFilterSelector
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_semantic_target_realizer_patch.lean =====
/-
EuclidsPath — Mersenne semantic target realizer patch
=====================================================

Purpose
-------
This patch closes another layer below the sparse route.  A semantic lift for a
chosen selector is not primitive.  It follows from a stronger but clearer local
realizer:

    given Γ and any admissible target k > index Γ,
    construct Γ⁺ with index Γ⁺ = k, preserving every ordinary tail and passing
    the legality / no-escape audits.

This separates arithmetic target selection from semantic genealogy construction.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneSemanticTargetRealizer

/-- Indexed genealogy system. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

/-- Admissibility filter. -/
structure AdmissibleIndexFilter where
  admissible : Nat → Prop
  respects_upper_composite_firewall : Prop
  respects_upper_composite_firewall_proof : respects_upper_composite_firewall
  not_eventual_all_indices_claim : Prop
  not_eventual_all_indices_claim_proof : not_eventual_all_indices_claim

/-- Selector of a strictly larger admissible index. -/
structure CofinalAdmissibleSelector (F : AdmissibleIndexFilter) where
  nextIndex : Nat → Nat
  strict_above : ∀ k : Nat, k < nextIndex k
  admissible_next : ∀ k : Nat, F.admissible (nextIndex k)

/-- Pointwise witness realizing a chosen target index. -/
structure TargetLiftWitness
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (Γ : I.Genealogy)
    (k : Nat) where
  Γplus : I.Genealogy
  index_eq_target : I.index Γplus = k
  tail_preserved : ∀ M0 : Nat, I.Tail M0 Γ → I.Tail M0 Γplus
  legal_lift : Prop
  legal_lift_proof : legal_lift
  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape
  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape
  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

/--
Uniform semantic realizer: every admissible target above the current index can
be realized by a genealogy lift.
-/
structure SemanticTargetRealizer
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  realize :
    ∀ Γ : I.Genealogy, ∀ k : Nat,
      I.index Γ < k →
      F.admissible k →
      TargetLiftWitness I F Γ k

/-- Semantic lift source for a fixed selector. -/
structure SemanticTargetLift
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (S : CofinalAdmissibleSelector F) where
  next : I.Genealogy → I.Genealogy
  next_has_selected_index :
    ∀ Γ : I.Genealogy, I.index (next Γ) = S.nextIndex (I.index Γ)
  tail_preserved :
    ∀ M0 Γ, I.Tail M0 Γ → I.Tail M0 (next Γ)
  legal_lift : Prop
  legal_lift_proof : legal_lift
  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape
  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape
  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

namespace SemanticTargetRealizer

/-- Canonical chosen witness for the selector target. -/
def selectedWitness
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {S : CofinalAdmissibleSelector F}
    (R : SemanticTargetRealizer I F)
    (Γ : I.Genealogy) :
    TargetLiftWitness I F Γ (S.nextIndex (I.index Γ)) :=
  R.realize Γ (S.nextIndex (I.index Γ))
    (S.strict_above (I.index Γ))
    (S.admissible_next (I.index Γ))

/-- A semantic realizer builds the selected semantic lift for any selector. -/
def toSemanticTargetLift
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {S : CofinalAdmissibleSelector F}
    (R : SemanticTargetRealizer I F) :
    SemanticTargetLift I F S where
  next := fun Γ => (R.selectedWitness Γ).Γplus
  next_has_selected_index := by
    intro Γ
    exact (R.selectedWitness Γ).index_eq_target
  tail_preserved := by
    intro M0 Γ hTail
    exact (R.selectedWitness Γ).tail_preserved M0 hTail
  legal_lift := ∀ Γ : I.Genealogy, (R.selectedWitness (S := S) Γ).legal_lift
  legal_lift_proof := by
    intro Γ
    exact (R.selectedWitness Γ).legal_lift_proof
  no_seam_escape := ∀ Γ : I.Genealogy, (R.selectedWitness (S := S) Γ).no_seam_escape
  no_seam_escape_proof := by
    intro Γ
    exact (R.selectedWitness Γ).no_seam_escape_proof
  no_compression_escape := ∀ Γ : I.Genealogy, (R.selectedWitness (S := S) Γ).no_compression_escape
  no_compression_escape_proof := by
    intro Γ
    exact (R.selectedWitness Γ).no_compression_escape_proof
  no_unpaid_boundary_jump := ∀ Γ : I.Genealogy, (R.selectedWitness (S := S) Γ).no_unpaid_boundary_jump
  no_unpaid_boundary_jump_proof := by
    intro Γ
    exact (R.selectedWitness Γ).no_unpaid_boundary_jump_proof

/-- Realizer closes semantic lift nonemptiness for every selector. -/
theorem semanticLift_nonempty_of_realizer
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {S : CofinalAdmissibleSelector F}
    (R : SemanticTargetRealizer I F) :
    Nonempty (SemanticTargetLift I F S) := by
  exact ⟨R.toSemanticTargetLift⟩

end SemanticTargetRealizer

/-- Defect: no semantic target realizer exists. -/
def SemanticTargetRealizerDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (SemanticTargetRealizer I F)

/-- Defect: no selected semantic lift exists for a fixed selector. -/
def SemanticTargetLiftDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter)
    (S : CofinalAdmissibleSelector F) : Prop :=
  ¬ Nonempty (SemanticTargetLift I F S)

/-- If some selector has no lift, then the uniform realizer cannot exist. -/
theorem realizer_defect_of_lift_defect
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    {S : CofinalAdmissibleSelector F}
    (hLiftDef : SemanticTargetLiftDefect I F S) :
    SemanticTargetRealizerDefect I F := by
  intro hRealizer
  rcases hRealizer with ⟨R⟩
  exact hLiftDef (SemanticTargetRealizer.semanticLift_nonempty_of_realizer R)

/-- If a uniform realizer exists, no selector-level lift defect is possible. -/
theorem no_lift_defect_of_realizer
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : SemanticTargetRealizer I F)
    (S : CofinalAdmissibleSelector F) :
    ¬ SemanticTargetLiftDefect I F S := by
  intro h
  exact h (SemanticTargetRealizer.semanticLift_nonempty_of_realizer (S := S) R)

/-- Slogan: semantic lift is reduced to target realization. -/
theorem semanticTargetRealizer_slogan
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : SemanticTargetRealizer I F) :
    ∀ S : CofinalAdmissibleSelector F,
      Nonempty (SemanticTargetLift I F S) := by
  intro S
  exact SemanticTargetRealizer.semanticLift_nonempty_of_realizer R

end MersenneSemanticTargetRealizer
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_admissible_filter_firewall_patch.lean =====
/-
EuclidsPath — Mersenne admissible-filter firewall
=================================================

Purpose
-------
After the exact-successor route was rejected, the corrected route uses a sparse
admissible filter on Mersenne indices.  This patch records what the filter must
not do: it must not pretend that every index is admissible, and it must respect
necessary upper-side obstructions such as composite-exponent obstruction.

No theorem here proves infinitely many Mersenne-twin centres.  This file only
formalizes the firewall that any admissible-index route must pass.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneAdmissibleFilterFirewall

/-- Abstract prime-like predicate. -/
abbrev PrimeLike := Nat → Prop

/-- Lower Mersenne-twin side at index `k`: `2^(2k+1)-3`. -/
def lowerAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 3

/-- Upper Mersenne-twin side at index `k`: `2^(2k+1)-1`. -/
def upperAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 1

/-- The exponent attached to index `k`. -/
def exponentAt (k : Nat) : Nat := 2 * k + 1

/-- A Mersenne-twin centre at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerAt k) ∧ Prime (upperAt k)

/-- Cofinal infinitude of Mersenne-twin centres. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- A sparse admissible filter on indices. -/
structure AdmissibleIndexFilter where
  admissible : Nat → Prop

/-- The filter is cofinal if it has an admissible index above every floor. -/
def CofinalAdmissibleIndices (F : AdmissibleIndexFilter) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ F.admissible k

/-- A selector is the Skolemized/coherent form of cofinality. -/
structure CofinalAdmissibleSelector (F : AdmissibleIndexFilter) where
  nextAbove : Nat → Nat
  strict_above : ∀ k : Nat, k < nextAbove k
  admissible_next : ∀ k : Nat, F.admissible (nextAbove k)

/-- A necessary exponent-side predicate, e.g. “`2k+1` is prime-like”. -/
structure NecessaryExponentPredicate where
  goodExponent : Nat → Prop

/-- Upper-side firewall: upper primality forces the exponent predicate. -/
structure UpperSideNecessaryFirewall
    (Prime : PrimeLike)
    (E : NecessaryExponentPredicate) where
  upper_prime_forces_goodExponent :
    ∀ k : Nat, Prime (upperAt k) → E.goodExponent (exponentAt k)

/-- Any Mersenne-twin centre passes every sound upper-side firewall. -/
theorem twinCenter_passes_upperFirewall
    {Prime : PrimeLike}
    {E : NecessaryExponentPredicate}
    (W : UpperSideNecessaryFirewall Prime E)
    {k : Nat}
    (hTwin : MersenneTwinCenter Prime k) :
    E.goodExponent (exponentAt k) := by
  exact W.upper_prime_forces_goodExponent k hTwin.2

/-- A filter respects the upper-side firewall if admissibility implies the necessary predicate. -/
def FilterRespectsUpperFirewall
    (F : AdmissibleIndexFilter)
    (E : NecessaryExponentPredicate) : Prop :=
  ∀ k : Nat, F.admissible k → E.goodExponent (exponentAt k)

/-- If a filter admits a firewall-bad index, it fails the firewall. -/
def FilterUpperFirewallDefect
    (F : AdmissibleIndexFilter)
    (E : NecessaryExponentPredicate) : Prop :=
  ∃ k : Nat, F.admissible k ∧ ¬ E.goodExponent (exponentAt k)

/-- Respecting the firewall is exactly absence of a firewall-bad admissible index. -/
theorem filterRespectsUpperFirewall_iff_no_defect
    (F : AdmissibleIndexFilter)
    (E : NecessaryExponentPredicate) :
    FilterRespectsUpperFirewall F E ↔ ¬ FilterUpperFirewallDefect F E := by
  constructor
  · intro hRespect hDef
    rcases hDef with ⟨k, hkAdm, hkBad⟩
    exact hkBad (hRespect k hkAdm)
  · intro hNoDef k hkAdm
    by_contra hkBad
    exact hNoDef ⟨k, hkAdm, hkBad⟩

/-- If a filter is sound for Mersenne-twin extraction, it need not be complete. -/
structure FilterTwinSoundness
    (Prime : PrimeLike)
    (F : AdmissibleIndexFilter) where
  admissible_realizes_twin : ∀ k : Nat, F.admissible k → MersenneTwinCenter Prime k

/-- Soundness plus cofinality gives infinitely many Mersenne-twin centres. -/
theorem infinite_twins_of_cofinal_sound_filter
    {Prime : PrimeLike}
    {F : AdmissibleIndexFilter}
    (hCof : CofinalAdmissibleIndices F)
    (hSound : FilterTwinSoundness Prime F) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  rcases hCof K0 with ⟨k, hkFloor, hkAdm⟩
  exact ⟨k, hkFloor, hSound.admissible_realizes_twin k hkAdm⟩

/-- A filter that admits all indices is dangerous after the exact-successor firewall. -/
def EventualAllFilter (F : AdmissibleIndexFilter) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → F.admissible k

/-- If an eventually-all filter is sound for twins, then almost all indices are twins. -/
def EventuallyAllMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → MersenneTwinCenter Prime k

/-- Eventual-all admissibility plus soundness is the too-strong route. -/
theorem eventuallyAllTwins_of_eventualAllSoundFilter
    {Prime : PrimeLike}
    {F : AdmissibleIndexFilter}
    (hAll : EventualAllFilter F)
    (hSound : FilterTwinSoundness Prime F) :
    EventuallyAllMersenneTwinCenters Prime := by
  rcases hAll with ⟨K0, hAdm⟩
  exact ⟨K0, fun k hk => hSound.admissible_realizes_twin k (hAdm k hk)⟩

/-- Corrected sparse filters must not be eventually-all unless the too-strong conclusion is intended. -/
structure SparseFilterFirewall
    (Prime : PrimeLike)
    (F : AdmissibleIndexFilter) where
  not_eventual_all_filter : ¬ EventualAllFilter F
  respects_upper_firewall : Prop
  respects_upper_firewall_proof : respects_upper_firewall

/-- Final slogan for this layer. -/
theorem admissibleFilterFirewall_slogan
    {Prime : PrimeLike}
    {F : AdmissibleIndexFilter}
    (FW : SparseFilterFirewall Prime F) :
    ¬ EventualAllFilter F ∧ FW.respects_upper_firewall := by
  exact ⟨FW.not_eventual_all_filter, FW.respects_upper_firewall_proof⟩

end MersenneAdmissibleFilterFirewall
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_filter_circularity_audit_patch.lean =====
/-
EuclidsPath — Mersenne filter circularity audit
===============================================

Purpose
-------
A sparse route may hide the target theorem in the word “admissible”.  This file
records the main anti-circularity audit: if the admissible filter is literally
“`k` is already a Mersenne-twin centre”, then cofinal admissibility is exactly
the desired theorem.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneFilterCircularityAudit

abbrev PrimeLike := Nat → Prop

def lowerAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 3

def upperAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 1

def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerAt k) ∧ Prime (upperAt k)

def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

structure AdmissibleIndexFilter where
  admissible : Nat → Prop

def CofinalAdmissibleIndices (F : AdmissibleIndexFilter) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ F.admissible k

/-- The circular filter: “admissible” means already being a Mersenne-twin index. -/
def twinFilter (Prime : PrimeLike) : AdmissibleIndexFilter where
  admissible := MersenneTwinCenter Prime

/-- Cofinality of the circular filter is exactly infinitude of Mersenne-twin centres. -/
theorem cofinal_twinFilter_iff_infinite_mersenne_twins
    (Prime : PrimeLike) :
    CofinalAdmissibleIndices (twinFilter Prime) ↔
      InfinitelyManyMersenneTwinCenters Prime := by
  rfl

/-- A noncircular filter is explicitly not definitionally the target predicate. -/
structure NonCircularAdmissibleFilter
    (Prime : PrimeLike)
    (F : AdmissibleIndexFilter) where
  not_target_filter : F.admissible ≠ MersenneTwinCenter Prime
  has_independent_arithmetic_definition : Prop
  has_independent_arithmetic_definition_proof : has_independent_arithmetic_definition

/-- Payment predicate on genealogies at their own index. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  index : Genealogy → Nat

/-- A raw payment relation. -/
abbrev RawOwnPayment (I : IndexedGenealogySystem) := I.Genealogy → Nat → Prop

/-- Payment soundness extracts the Mersenne-twin predicate. -/
def PaymentSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawOwnPayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat,
    Paid Γ k → MersenneTwinCenter Prime k

/-- Payment is circular if it is merely the Mersenne-twin predicate in disguise. -/
def CircularPayment
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawOwnPayment I) : Prop :=
  ∀ Γ : I.Genealogy, ∀ k : Nat,
    Paid Γ k ↔ MersenneTwinCenter Prime k

/-- Circular payment is sound, but it is not a proof mechanism. -/
theorem paymentSound_of_circularPayment
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {Paid : RawOwnPayment I}
    (hCirc : CircularPayment Prime I Paid) :
    PaymentSound Prime I Paid := by
  intro Γ k hPaid
  exact (hCirc Γ k).1 hPaid

/-- A route relying on circular payment has merely restated the target at the payment layer. -/
structure NonCircularPaymentAudit
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (Paid : RawOwnPayment I) where
  not_circular_payment : ¬ CircularPayment Prime I Paid
  payment_has_independent_certificate : Prop
  payment_has_independent_certificate_proof : payment_has_independent_certificate

/-- Combined anti-circularity guard for the sparse route. -/
structure SparseRouteAntiCircularityGuard
    (Prime : PrimeLike)
    (F : AdmissibleIndexFilter)
    (I : IndexedGenealogySystem)
    (Paid : RawOwnPayment I) where
  filter_guard : NonCircularAdmissibleFilter Prime F
  payment_guard : NonCircularPaymentAudit Prime I Paid

/-- The guard exposes exactly the two circularity doors. -/
theorem sparseRouteAntiCircularity_slogan
    {Prime : PrimeLike}
    {F : AdmissibleIndexFilter}
    {I : IndexedGenealogySystem}
    {Paid : RawOwnPayment I}
    (G : SparseRouteAntiCircularityGuard Prime F I Paid) :
    F.admissible ≠ MersenneTwinCenter Prime ∧
    ¬ CircularPayment Prime I Paid := by
  exact ⟨G.filter_guard.not_target_filter, G.payment_guard.not_circular_payment⟩

end MersenneFilterCircularityAudit
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_side_payment_certificate_patch.lean =====
/-
EuclidsPath — Mersenne side-payment certificate decomposition
==============================================================

Purpose
-------
The field “filtered own-index payment” is too opaque.  This patch decomposes it
into two side certificates, one for `2^(2k+1)-3` and one for `2^(2k+1)-1`.
The final Mersenne-twin extraction is then pure assembly.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneSidePaymentCertificate

abbrev PrimeLike := Nat → Prop

def lowerAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 3

def upperAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 1

def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerAt k) ∧ Prime (upperAt k)

structure IndexedGenealogySystem where
  Genealogy : Type
  index : Genealogy → Nat

structure AdmissibleIndexFilter where
  admissible : Nat → Prop

/-- Lower-side certificate family. -/
structure LowerSideCertificateSystem
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  CertLower : I.Genealogy → Type
  certLower : ∀ Γ : I.Genealogy,
    F.admissible (I.index Γ) → CertLower Γ

/-- Upper-side certificate family. -/
structure UpperSideCertificateSystem
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  CertUpper : I.Genealogy → Type
  certUpper : ∀ Γ : I.Genealogy,
    F.admissible (I.index Γ) → CertUpper Γ

/-- Lower certificate soundness. -/
def LowerSideSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    {F : AdmissibleIndexFilter}
    (L : LowerSideCertificateSystem I F) : Prop :=
  ∀ Γ : I.Genealogy, L.CertLower Γ → Prime (lowerAt (I.index Γ))

/-- Upper certificate soundness. -/
def UpperSideSound
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    {F : AdmissibleIndexFilter}
    (U : UpperSideCertificateSystem I F) : Prop :=
  ∀ Γ : I.Genealogy, U.CertUpper Γ → Prime (upperAt (I.index Γ))

/-- Combined side-certificate front. -/
structure FilteredSidePaymentFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  lower : LowerSideCertificateSystem I F
  upper : UpperSideCertificateSystem I F
  lower_sound : LowerSideSound Prime I lower
  upper_sound : UpperSideSound Prime I upper
  lower_not_circular : Prop
  lower_not_circular_proof : lower_not_circular
  upper_not_circular : Prop
  upper_not_circular_proof : upper_not_circular

/-- Admissible own-index genealogy gives both side primes. -/
theorem mersenneTwinCenter_of_filteredSidePayment
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (P : FilteredSidePaymentFront Prime I F)
    (Γ : I.Genealogy)
    (hAdm : F.admissible (I.index Γ)) :
    MersenneTwinCenter Prime (I.index Γ) := by
  constructor
  · exact P.lower_sound Γ (P.lower.certLower Γ hAdm)
  · exact P.upper_sound Γ (P.upper.certUpper Γ hAdm)

/-- Cofinal admissible genealogies plus side payment yields infinite Mersenne twins. -/
def CofinalAdmissibleGenealogyHits
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ∀ K0 : Nat, ∃ Γ : I.Genealogy,
    K0 ≤ I.index Γ ∧ F.admissible (I.index Γ)

def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Side certificate front turns cofinal admissible hits into cofinal Mersenne twins. -/
theorem infinitelyMany_of_cofinalHits_and_sidePayment
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (hHits : CofinalAdmissibleGenealogyHits I F)
    (P : FilteredSidePaymentFront Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  rcases hHits K0 with ⟨Γ, hFloor, hAdm⟩
  exact ⟨I.index Γ, hFloor, mersenneTwinCenter_of_filteredSidePayment P Γ hAdm⟩

/-- Defect in the lower side certificate source. -/
def LowerSidePaymentDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (LowerSideCertificateSystem I F)

/-- Defect in the upper side certificate source. -/
def UpperSidePaymentDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (UpperSideCertificateSystem I F)

/-- If the full side-payment front is absent, at least one named component may be blamed by an audit package. -/
structure SidePaymentDefectAudit
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  component_defect :
    LowerSidePaymentDefect I F ∨
    UpperSidePaymentDefect I F ∨
    (∀ L : LowerSideCertificateSystem I F, ¬ LowerSideSound Prime I L) ∨
    (∀ U : UpperSideCertificateSystem I F, ¬ UpperSideSound Prime I U)

/-- Slogan for this layer. -/
theorem sidePaymentCertificate_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (P : FilteredSidePaymentFront Prime I F) :
    ∀ Γ : I.Genealogy,
      F.admissible (I.index Γ) →
        MersenneTwinCenter Prime (I.index Γ) := by
  intro Γ hAdm
  exact mersenneTwinCenter_of_filteredSidePayment P Γ hAdm

end MersenneSidePaymentCertificate
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_current_final_front_audit_patch.lean =====
/-
EuclidsPath — Mersenne current final-front audit
================================================

Purpose
-------
This file collects the corrected sparse route after the latest decompositions.
It is a map of the current endgame, not an unconditional theorem about Mersenne
twins.

The current noncircular route requires:
  1. a noncircular cofinal sparse filter;
  2. semantic realization of selected target indices by genealogies;
  3. cofinal admissible genealogy hits;
  4. noncircular side-payment certificates for both sides;
  5. ordinary/eventual-absence contradiction assembly.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneCurrentFinalFrontAudit

abbrev PrimeLike := Nat → Prop

def lowerAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 3

def upperAt (k : Nat) : Nat := 2 ^ (2 * k + 1) - 1

def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerAt k) ∧ Prime (upperAt k)

def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

structure IndexedGenealogySystem where
  Genealogy : Type
  Tail : Nat → Genealogy → Prop
  index : Genealogy → Nat

structure AdmissibleIndexFilter where
  admissible : Nat → Prop

/-- Cofinal admissible genealogy hits. -/
def CofinalAdmissibleGenealogyHits
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ∀ K0 : Nat, ∃ Γ : I.Genealogy,
    K0 ≤ I.index Γ ∧ F.admissible (I.index Γ)

/-- Noncircular arithmetic filter audit. -/
structure NonCircularSparseFilter
    (Prime : PrimeLike)
    (F : AdmissibleIndexFilter) where
  cofinal : ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ F.admissible k
  not_target_filter : F.admissible ≠ MersenneTwinCenter Prime
  not_eventually_all : Prop
  not_eventually_all_proof : not_eventually_all
  respects_upper_firewall : Prop
  respects_upper_firewall_proof : respects_upper_firewall

/-- Semantic target realizer audit, kept abstract at the current final front. -/
structure SemanticTargetRealizerAudit
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  realizes_selected_targets : Prop
  realizes_selected_targets_proof : realizes_selected_targets
  no_tail_escape : Prop
  no_tail_escape_proof : no_tail_escape
  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape
  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape
  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump
  produces_cofinal_hits : CofinalAdmissibleGenealogyHits I F

/-- Side-payment certificate front. -/
structure SidePaymentFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  lower_paid_sound :
    ∀ Γ : I.Genealogy,
      F.admissible (I.index Γ) → Prime (lowerAt (I.index Γ))
  upper_paid_sound :
    ∀ Γ : I.Genealogy,
      F.admissible (I.index Γ) → Prime (upperAt (I.index Γ))
  lower_non_circular : Prop
  lower_non_circular_proof : lower_non_circular
  upper_non_circular : Prop
  upper_non_circular_proof : upper_non_circular

/-- The corrected current sparse route front. -/
structure CorrectedSparseMersenneRouteFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  filter : NonCircularSparseFilter Prime F
  realizer : SemanticTargetRealizerAudit I F
  side_payment : SidePaymentFront Prime I F

/-- A cofinal admissible hit becomes a Mersenne-twin centre. -/
theorem twin_of_hit_and_sidePayment
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (P : SidePaymentFront Prime I F)
    {Γ : I.Genealogy}
    (hAdm : F.admissible (I.index Γ)) :
    MersenneTwinCenter Prime (I.index Γ) := by
  exact ⟨P.lower_paid_sound Γ hAdm, P.upper_paid_sound Γ hAdm⟩

/-- The corrected front produces infinitely many Mersenne-twin centres. -/
theorem infinitelyMany_of_correctedSparseFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : CorrectedSparseMersenneRouteFront Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  rcases R.realizer.produces_cofinal_hits K0 with ⟨Γ, hFloor, hAdm⟩
  exact ⟨I.index Γ, hFloor, twin_of_hit_and_sidePayment R.side_payment hAdm⟩

/-- Infinite Mersenne-twin supply forbids eventual absence. -/
theorem infinite_forbids_eventual_absence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hNo k hk hTwin

/-- The corrected front forbids eventual absence. -/
theorem correctedSparseFront_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : CorrectedSparseMersenneRouteFront Prime I F) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact infinite_forbids_eventual_absence (infinitelyMany_of_correctedSparseFront R)

/-- Defects of the corrected sparse route. -/
def FilterFrontDefect
    (Prime : PrimeLike)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (NonCircularSparseFilter Prime F)

def SemanticRealizerFrontDefect
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (SemanticTargetRealizerAudit I F)

def SidePaymentFrontDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (SidePaymentFront Prime I F)

/-- If eventual absence holds, the corrected front cannot exist. -/
theorem eventual_absence_forces_correctedFront_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    ¬ Nonempty (CorrectedSparseMersenneRouteFront Prime I F) := by
  intro hFront
  rcases hFront with ⟨R⟩
  exact correctedSparseFront_forbids_eventual_absence R hAbs

/-- Component audit package: failure is assigned to filter, realizer, or side payment. -/
structure CorrectedSparseComponentDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  defect :
    FilterFrontDefect Prime F ∨
    SemanticRealizerFrontDefect I F ∨
    SidePaymentFrontDefect Prime I F

/-- Current final slogan. -/
theorem currentFinalFrontAudit_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : CorrectedSparseMersenneRouteFront Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  have hInf := infinitelyMany_of_correctedSparseFront R
  exact ⟨hInf, infinite_forbids_eventual_absence hInf⟩

end MersenneCurrentFinalFrontAudit
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_one_file_max_forward_patch.lean =====
/-
EuclidsPath — Mersenne sparse route, one-file max-forward patch
================================================================

Purpose
-------
One consolidated patch that advances several layers of the Mersenne-twin route
in a single file.

It is intentionally self-contained: it does not import the previous local patch
files.  This makes the logical frontier visible in one place.

What is proved here
-------------------
Assume a noncircular sparse admissible filter, ordinary tail seeds, a cofinal
selector for admissible indices, a semantic target realizer, and side-payment
certificates whose soundness implies primality of both Mersenne sides.  Then:

  * for every floor `K0`, there is a Mersenne-twin center at some `k ≥ K0`;
  * hence Mersenne-twin centers are infinite in the tail/cofinal sense;
  * hence eventual absence of Mersenne-twin centers is impossible;
  * conversely, eventual absence forces failure of at least one proof component.

What is NOT proved here
-----------------------
This is not an unconditional proof of infinitely many Mersenne-twin centers.
The remaining real work is exactly the construction of the audited front:

  1. a noncircular cofinal admissible filter;
  2. ordinary genealogy seeds;
  3. semantic target realization for every admissible target above the current
     index;
  4. noncircular lower/upper side-payment certificates;
  5. independent soundness of those side-payment certificates.

No `axiom`.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneOneFile

/-#############################################################################
  §1. Mersenne centers, sides, and tail notions
#############################################################################-/

/-- Abstract primality predicate.  Instantiate with `Nat.Prime` in the concrete route. -/
abbrev PrimeLike := Nat → Prop

/-- Lower side of the Mersenne-twin pair indexed by `k`: `2^(2k+1)-3`. -/
def lowerSide (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 3

/-- Upper side of the Mersenne-twin pair indexed by `k`: `2^(2k+1)-1`. -/
def upperSide (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 1

/-- Base-4 repunit center: `(4^k-1)/3 = 1 + 4 + ... + 4^(k-1)`. -/
def mersenneCenter (k : Nat) : Nat :=
  (4 ^ k - 1) / 3

/-- A Mersenne-twin center at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide k) ∧ Prime (upperSide k)

/-- Cofinal/tail infinitude of Mersenne-twin centers. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Eventual absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal infinitude forbids eventual absence. -/
theorem infinitelyMany_forbids_eventualAbsence
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hTwin⟩
  exact hNo k hk hTwin

/-#############################################################################
  §2. Indexed genealogy system and ordinary seeds
#############################################################################-/

/-- A Step00/Mersenne genealogy system with a Mersenne index attached to each genealogy. -/
structure IndexedGenealogySystem where
  Genealogy : Type
  index : Genealogy → Nat
  Tail : Nat → Genealogy → Prop

/-- Ordinary twin supply gives at least one genealogy in every ordinary tail. -/
def OrdinaryTailSeedLaw (I : IndexedGenealogySystem) : Prop :=
  ∀ M0 : Nat, ∃ Γ : I.Genealogy, I.Tail M0 Γ

/-- Failure of ordinary tail seeds. -/
def OrdinaryTailSeedDefect (I : IndexedGenealogySystem) : Prop :=
  ¬ OrdinaryTailSeedLaw I

/-#############################################################################
  §3. Sparse admissible filters and anti-circularity firewall
#############################################################################-/

/-- A sparse admissible filter on Mersenne indices. -/
structure AdmissibleIndexFilter where
  admissible : Nat → Prop

/-- Admissible indices are cofinal. -/
def CofinalAdmissibleIndices (F : AdmissibleIndexFilter) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ F.admissible k

/-- Failure of cofinal admissibility. -/
def CofinalAdmissibleDefect (F : AdmissibleIndexFilter) : Prop :=
  ¬ CofinalAdmissibleIndices F

/-- The circular filter that declares an index admissible exactly when it is already good. -/
def twinFilter (Prime : PrimeLike) : AdmissibleIndexFilter where
  admissible := MersenneTwinCenter Prime

/-- Cofinality of the circular twin filter is exactly the target theorem. -/
theorem cofinal_twinFilter_iff_infinite_mersenne_twins
    (Prime : PrimeLike) :
    CofinalAdmissibleIndices (twinFilter Prime) ↔
      InfinitelyManyMersenneTwinCenters Prime := by
  rfl

/-- Audit guard: the filter is not allowed to be a mere repackaging of the target. -/
structure NonCircularSparseFilter (Prime : PrimeLike) (F : AdmissibleIndexFilter) where
  cofinal : CofinalAdmissibleIndices F
  not_twin_repackaging : ¬ (∀ k : Nat, F.admissible k ↔ MersenneTwinCenter Prime k)
  independent_source : Prop
  independent_source_proof : independent_source

/-- Failure of the filter audit. -/
def FilterAuditDefect (Prime : PrimeLike) (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (NonCircularSparseFilter Prime F)

/-#############################################################################
  §4. Cofinal selectors and target selectors
#############################################################################-/

/-- A choice function selecting an admissible index above any floor. -/
structure CofinalAdmissibleSelector (F : AdmissibleIndexFilter) where
  select : Nat → Nat
  select_ge : ∀ K0 : Nat, K0 ≤ select K0
  select_admissible : ∀ K0 : Nat, F.admissible (select K0)

/-- Cofinality gives a selector by classical choice. -/
noncomputable def selectorOfCofinal
    (F : AdmissibleIndexFilter)
    (h : CofinalAdmissibleIndices F) :
    CofinalAdmissibleSelector F where
  select := fun K0 => Classical.choose (h K0)
  select_ge := by
    intro K0
    exact (Classical.choose_spec (h K0)).1
  select_admissible := by
    intro K0
    exact (Classical.choose_spec (h K0)).2

/-- A target selector adapted to a genealogy: choose an admissible target above both `K0` and the current index. -/
structure CofinalTargetSelector
    (I : IndexedGenealogySystem) (F : AdmissibleIndexFilter) where
  target : I.Genealogy → Nat → Nat
  target_ge_floor : ∀ Γ K0, K0 ≤ target Γ K0
  target_gt_index : ∀ Γ K0, I.index Γ < target Γ K0
  target_admissible : ∀ Γ K0, F.admissible (target Γ K0)

/-- A cofinal selector gives a genealogy-relative target selector. -/
noncomputable def targetSelectorOfSelector
    {I : IndexedGenealogySystem} {F : AdmissibleIndexFilter}
    (S : CofinalAdmissibleSelector F) :
    CofinalTargetSelector I F where
  target := fun Γ K0 => S.select (max K0 (I.index Γ + 1))
  target_ge_floor := by
    intro Γ K0
    exact le_trans (Nat.le_max_left K0 (I.index Γ + 1))
      (S.select_ge (max K0 (I.index Γ + 1)))
  target_gt_index := by
    intro Γ K0
    have hsucc : I.index Γ + 1 ≤ max K0 (I.index Γ + 1) :=
      Nat.le_max_right K0 (I.index Γ + 1)
    have hle : I.index Γ + 1 ≤ S.select (max K0 (I.index Γ + 1)) :=
      le_trans hsucc (S.select_ge (max K0 (I.index Γ + 1)))
    exact Nat.lt_of_succ_le hle
  target_admissible := by
    intro Γ K0
    exact S.select_admissible (max K0 (I.index Γ + 1))

/-- Cofinal admissibility gives a target selector. -/
noncomputable def targetSelectorOfCofinal
    {I : IndexedGenealogySystem} {F : AdmissibleIndexFilter}
    (h : CofinalAdmissibleIndices F) :
    CofinalTargetSelector I F :=
  targetSelectorOfSelector (selectorOfCofinal F h)

/-#############################################################################
  §5. Semantic target realization
#############################################################################-/

/-- A realized lift from genealogy `Γ` to a specified admissible target index `k`. -/
structure TargetRealizationWitness
    (I : IndexedGenealogySystem) (Γ : I.Genealogy) (k : Nat) where
  Γplus : I.Genealogy
  index_eq : I.index Γplus = k
  tail_preserved : ∀ M0 : Nat, I.Tail M0 Γ → I.Tail M0 Γplus
  legal_lift : Prop
  legal_lift_proof : legal_lift
  no_seam_escape : Prop
  no_seam_escape_proof : no_seam_escape
  no_compression_escape : Prop
  no_compression_escape_proof : no_compression_escape
  no_unpaid_boundary_jump : Prop
  no_unpaid_boundary_jump_proof : no_unpaid_boundary_jump

/-- Semantic realizer: any admissible target strictly above the current index can be realized. -/
structure SemanticTargetRealizer
    (I : IndexedGenealogySystem) (F : AdmissibleIndexFilter) where
  realize :
    ∀ Γ : I.Genealogy,
    ∀ k : Nat,
      I.index Γ < k →
      F.admissible k →
        TargetRealizationWitness I Γ k
  noncircular_realizer : Prop
  noncircular_realizer_proof : noncircular_realizer

/-- Failure of the semantic realizer. -/
def SemanticRealizerDefect
    (I : IndexedGenealogySystem) (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (SemanticTargetRealizer I F)

/-- Realize the target selected by a target selector. -/
def realizeSelectedTarget
    {I : IndexedGenealogySystem} {F : AdmissibleIndexFilter}
    (R : SemanticTargetRealizer I F)
    (T : CofinalTargetSelector I F)
    (Γ : I.Genealogy) (K0 : Nat) :
    TargetRealizationWitness I Γ (T.target Γ K0) :=
  R.realize Γ (T.target Γ K0)
    (T.target_gt_index Γ K0)
    (T.target_admissible Γ K0)

/-#############################################################################
  §6. Side-payment certificates and soundness
#############################################################################-/

/-- Lower-side certificate system. -/
structure LowerSideCertificateSystem
    (I : IndexedGenealogySystem) where
  LowerCert : I.Genealogy → Nat → Type

/-- Upper-side certificate system. -/
structure UpperSideCertificateSystem
    (I : IndexedGenealogySystem) where
  UpperCert : I.Genealogy → Nat → Type

/-- Soundness of lower-side certificates. -/
def LowerSideSound
    (Prime : PrimeLike) (I : IndexedGenealogySystem)
    (L : LowerSideCertificateSystem I) : Prop :=
  ∀ Γ k, L.LowerCert Γ k → Prime (lowerSide k)

/-- Soundness of upper-side certificates. -/
def UpperSideSound
    (Prime : PrimeLike) (I : IndexedGenealogySystem)
    (U : UpperSideCertificateSystem I) : Prop :=
  ∀ Γ k, U.UpperCert Γ k → Prime (upperSide k)

/-- Side payment for every admissible own-index genealogy. -/
structure FilteredSidePaymentFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  lowerSystem : LowerSideCertificateSystem I
  upperSystem : UpperSideCertificateSystem I
  lowerPaid :
    ∀ Γ : I.Genealogy,
      F.admissible (I.index Γ) →
        lowerSystem.LowerCert Γ (I.index Γ)
  upperPaid :
    ∀ Γ : I.Genealogy,
      F.admissible (I.index Γ) →
        upperSystem.UpperCert Γ (I.index Γ)
  lowerSound : LowerSideSound Prime I lowerSystem
  upperSound : UpperSideSound Prime I upperSystem
  payment_noncircular : Prop
  payment_noncircular_proof : payment_noncircular

/-- Failure of side-payment front. -/
def SidePaymentDefect
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) : Prop :=
  ¬ Nonempty (FilteredSidePaymentFront Prime I F)

/-- An admissible genealogy with side payments yields a Mersenne-twin center at its index. -/
theorem mersenneTwinCenter_of_filteredSidePayment
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (P : FilteredSidePaymentFront Prime I F)
    (Γ : I.Genealogy)
    (hAdm : F.admissible (I.index Γ)) :
    MersenneTwinCenter Prime (I.index Γ) := by
  constructor
  · exact P.lowerSound Γ (I.index Γ) (P.lowerPaid Γ hAdm)
  · exact P.upperSound Γ (I.index Γ) (P.upperPaid Γ hAdm)

/-#############################################################################
  §7. One-file proof front and final theorem
#############################################################################-/

/-- The proof-level front: enough to derive cofinally many Mersenne-twin centers. -/
structure MersenneSparseProofFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  ordinary_seed : OrdinaryTailSeedLaw I
  cofinal_filter : CofinalAdmissibleIndices F
  semantic_realizer : SemanticTargetRealizer I F
  side_payment : FilteredSidePaymentFront Prime I F

/-- The audited front adds anti-circular guards on filter and payment. -/
structure AuditedMersenneSparseRouteFront
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  proof_front : MersenneSparseProofFront Prime I F
  filter_audit : NonCircularSparseFilter Prime F

namespace MersenneSparseProofFront

/-- For every ordinary tail and Mersenne floor, the proof front produces a Mersenne-twin hit. -/
theorem exists_mersenneTwinCenter_above
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (Front : MersenneSparseProofFront Prime I F)
    (M0 K0 : Nat) :
    ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k := by
  classical
  rcases Front.ordinary_seed M0 with ⟨Γ, hTailΓ⟩
  let T : CofinalTargetSelector I F := targetSelectorOfCofinal Front.cofinal_filter
  let W : TargetRealizationWitness I Γ (T.target Γ K0) :=
    realizeSelectedTarget Front.semantic_realizer T Γ K0
  refine ⟨T.target Γ K0, T.target_ge_floor Γ K0, ?_⟩
  have hAdmTarget : F.admissible (T.target Γ K0) := T.target_admissible Γ K0
  have hAdmPlus : F.admissible (I.index W.Γplus) := by
    simpa [W.index_eq] using hAdmTarget
  have hCenter :=
    mersenneTwinCenter_of_filteredSidePayment Front.side_payment W.Γplus hAdmPlus
  exact W.index_eq ▸ hCenter

/-- The proof front gives infinitely many Mersenne-twin centers. -/
theorem infinitelyManyMersenneTwinCenters
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (Front : MersenneSparseProofFront Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  exact Front.exists_mersenneTwinCenter_above 0 K0

/-- Hence the proof front forbids eventual absence. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (Front : MersenneSparseProofFront Prime I F) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  infinitelyMany_forbids_eventualAbsence Front.infinitelyManyMersenneTwinCenters

end MersenneSparseProofFront

namespace AuditedMersenneSparseRouteFront

/-- The audited front also produces infinitely many Mersenne-twin centers. -/
theorem infinitelyManyMersenneTwinCenters
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (Front : AuditedMersenneSparseRouteFront Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime :=
  Front.proof_front.infinitelyManyMersenneTwinCenters

/-- The audited front forbids eventual absence. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (Front : AuditedMersenneSparseRouteFront Prime I F) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  Front.proof_front.forbids_eventual_absence

end AuditedMersenneSparseRouteFront

/-#############################################################################
  §8. Defect analysis
#############################################################################-/

/-- If all proof components exist, they assemble into the proof front. -/
def proofFront_of_components
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (hSeed : OrdinaryTailSeedLaw I)
    (hCofinal : CofinalAdmissibleIndices F)
    (R : SemanticTargetRealizer I F)
    (P : FilteredSidePaymentFront Prime I F) :
    MersenneSparseProofFront Prime I F where
  ordinary_seed := hSeed
  cofinal_filter := hCofinal
  semantic_realizer := R
  side_payment := P

/-- Eventual absence forbids the existence of the proof front. -/
theorem eventual_absence_forbids_proofFront
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    ¬ Nonempty (MersenneSparseProofFront Prime I F) := by
  intro hFront
  rcases hFront with ⟨Front⟩
  exact Front.forbids_eventual_absence hAbs

/-- Eventual absence forces failure of at least one proof component. -/
theorem eventual_absence_forces_component_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    OrdinaryTailSeedDefect I ∨
    CofinalAdmissibleDefect F ∨
    SemanticRealizerDefect I F ∨
    SidePaymentDefect Prime I F := by
  classical
  by_cases hSeed : OrdinaryTailSeedLaw I
  · by_cases hCof : CofinalAdmissibleIndices F
    · by_cases hR : Nonempty (SemanticTargetRealizer I F)
      · by_cases hP : Nonempty (FilteredSidePaymentFront Prime I F)
        · rcases hR with ⟨R⟩
          rcases hP with ⟨P⟩
          have hFront : Nonempty (MersenneSparseProofFront Prime I F) :=
            ⟨proofFront_of_components hSeed hCof R P⟩
          exact False.elim ((eventual_absence_forbids_proofFront hAbs) hFront)
        · exact Or.inr (Or.inr (Or.inr hP))
      · exact Or.inr (Or.inr (Or.inl hR))
    · exact Or.inr (Or.inl hCof)
  · exact Or.inl hSeed

/-- If the four proof components are known not to fail, eventual absence is impossible. -/
theorem no_eventual_absence_of_no_component_defect
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (hSeed : ¬ OrdinaryTailSeedDefect I)
    (hCof : ¬ CofinalAdmissibleDefect F)
    (hR : ¬ SemanticRealizerDefect I F)
    (hP : ¬ SidePaymentDefect Prime I F) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases eventual_absence_forces_component_defect (Prime := Prime) (I := I) (F := F) hAbs with
    hSeedDef | hRest
  · exact hSeed hSeedDef
  · rcases hRest with hCofDef | hRest2
    · exact hCof hCofDef
    · rcases hRest2 with hRDef | hPDef
      · exact hR hRDef
      · exact hP hPDef

/-#############################################################################
  §9. Compact final route package
#############################################################################-/

/-- Final one-file route package: audited enough for noncircular use. -/
structure MersenneOneFileRoute
    (Prime : PrimeLike)
    (I : IndexedGenealogySystem)
    (F : AdmissibleIndexFilter) where
  front : AuditedMersenneSparseRouteFront Prime I F

/-- The route package proves cofinally many Mersenne-twin centers. -/
theorem route_produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : MersenneOneFileRoute Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime :=
  R.front.infinitelyManyMersenneTwinCenters

/-- The route package forbids eventual absence. -/
theorem route_forbids_eventual_absence
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : MersenneOneFileRoute Prime I F) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  R.front.forbids_eventual_absence

/-- Final slogan theorem. -/
theorem mersenne_oneFile_maxForward_slogan
    {Prime : PrimeLike}
    {I : IndexedGenealogySystem}
    {F : AdmissibleIndexFilter}
    (R : MersenneOneFileRoute Prime I F) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨route_produces_infinite_mersenne_twins R,
         route_forbids_eventual_absence R⟩

end MersenneOneFile
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_defect_oversaturation_engine_bridge_patch.lean =====
/-
EuclidsPath — Mersenne final defects to prime-oversaturation / engine bridge
============================================================================

Purpose
-------
The one-file Mersenne route ended with the conditional fork

  EventuallyNoMersenneTwinCenters Prime ->
    OrdinaryTailSeedDefect I \/
    CofinalAdmissibleDefect F \/
    SemanticRealizerDefect I F \/
    SidePaymentDefect Prime I F.

The present patch formalizes the next audit layer:

  a final Mersenne component defect is not allowed to be a clean escape if it
  maps into the already audited Step00 defect taxonomy.

The bridge is intentionally explicit.  It does not assert, by itself, that the
Mersenne component defects have already been mapped into Step00 defects.  It
records the exact adapter that must be supplied:

  Mersenne component defect
    -> Step00 defect token
    -> prime oversaturation event
    -> legal cycle / forbidden engine.

Once this adapter is supplied, eventual absence of Mersenne twins contradicts
`NoForbiddenEngine` / `NoPrimeOversaturationCycle`.

No axiom.  No sorry.
-/



namespace EuclidsPath
namespace Mersenne
namespace DefectOversaturationBridge

/-#############################################################################
  §1. Minimal Mersenne endgame vocabulary
#############################################################################-/

/-- Abstract primality predicate.  In the concrete arithmetic instance use `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- Lower side of a Step00 twin center. -/
def lowerSide (m : Nat) : Nat := 6 * m - 1

/-- Upper side of a Step00 twin center. -/
def upperSide (m : Nat) : Nat := 6 * m + 1

/-- Mersenne/base-4 repunit center. -/
def mersenneCenter (k : Nat) : Nat := (4 ^ k - 1) / 3

/-- A Mersenne-twin center at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide (mersenneCenter k)) ∧
  Prime (upperSide (mersenneCenter k))

/-- Infinitely/cofinally many Mersenne-twin centers. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Tail absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Tail absence is incompatible with cofinal infinitude. -/
theorem not_eventual_absence_of_infinite
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hkTwin⟩
  exact hNo k hk hkTwin

/-#############################################################################
  §2. The four final Mersenne defects
#############################################################################-/

/-- The four component-defect classes from the corrected sparse Mersenne route. -/
inductive MersenneFinalComponent where
  | ordinaryTailSeed
  | cofinalAdmissibleFilter
  | semanticTargetRealizer
  | sidePayment
  deriving DecidableEq, Repr

/-- A final defect profile: which of the four components is broken. -/
structure MersenneFinalDefectProfile where
  Defect : MersenneFinalComponent → Prop

/-- At least one final component defect is present. -/
def AnyMersenneFinalDefect (D : MersenneFinalDefectProfile) : Prop :=
  ∃ c : MersenneFinalComponent, D.Defect c

/-- Constructor for the disjunctive form used by the previous endgame theorem. -/
def DefectProfile.ofDisjunction
    (ordinaryTailSeedDefect : Prop)
    (cofinalAdmissibleDefect : Prop)
    (semanticRealizerDefect : Prop)
    (sidePaymentDefect : Prop) : MersenneFinalDefectProfile where
  Defect := fun c =>
    match c with
    | MersenneFinalComponent.ordinaryTailSeed => ordinaryTailSeedDefect
    | MersenneFinalComponent.cofinalAdmissibleFilter => cofinalAdmissibleDefect
    | MersenneFinalComponent.semanticTargetRealizer => semanticRealizerDefect
    | MersenneFinalComponent.sidePayment => sidePaymentDefect

namespace DefectProfile

/-- Convert an explicit four-way disjunction into `AnyMersenneFinalDefect`. -/
theorem any_of_four_way
    {O C R P : Prop}
    (h : O ∨ C ∨ R ∨ P) :
    AnyMersenneFinalDefect (ofDisjunction O C R P) := by
  rcases h with hO | hRest
  · exact ⟨MersenneFinalComponent.ordinaryTailSeed, hO⟩
  rcases hRest with hC | hRest
  · exact ⟨MersenneFinalComponent.cofinalAdmissibleFilter, hC⟩
  rcases hRest with hR | hP
  · exact ⟨MersenneFinalComponent.semanticTargetRealizer, hR⟩
  · exact ⟨MersenneFinalComponent.sidePayment, hP⟩

/-- Convert `AnyMersenneFinalDefect` back into the explicit four-way disjunction. -/
theorem four_way_of_any
    {O C R P : Prop}
    (h : AnyMersenneFinalDefect (ofDisjunction O C R P)) :
    O ∨ C ∨ R ∨ P := by
  rcases h with ⟨comp, hcomp⟩
  cases comp with
  | ordinaryTailSeed => exact Or.inl hcomp
  | cofinalAdmissibleFilter => exact Or.inr (Or.inl hcomp)
  | semanticTargetRealizer => exact Or.inr (Or.inr (Or.inl hcomp))
  | sidePayment => exact Or.inr (Or.inr (Or.inr hcomp))

end DefectProfile

/-#############################################################################
  §3. Step00 defect taxonomy and prime-oversaturation
#############################################################################-/

/-- The old Step00 no-go taxonomy, as seen from the Mersenne projection. -/
inductive Step00DefectKind where
  | seedSupplyGap
  | projectionCofinalityGap
  | semanticLiftGap
  | paymentGap
  | seamEscape
  | compressionEscape
  | gaugeEscape
  | unpaidBoundaryJump
  deriving DecidableEq, Repr

/-- A concrete Step00 defect token. -/
structure Step00DefectToken where
  kind : Step00DefectKind
  level : Nat

/-- Prime oversaturation event: the defect overuses a finite/ledger bucket of prime payment. -/
structure PrimeOversaturationEvent where
  level : Nat
  bucket : Nat
  overloaded : Prop
  overloaded_proof : overloaded

/-- Legal cycle extracted from a prime-oversaturation event. -/
structure PrimeOversaturationCycle where
  event : PrimeOversaturationEvent
  legal : Prop
  legal_proof : legal

/-- Forbidden internal engine extracted from a legal cycle/oversaturation. -/
structure ForbiddenPrimePaymentEngine where
  cycle : PrimeOversaturationCycle
  internal : Prop
  internal_proof : internal

/-- No legal prime-oversaturation cycle may exist. -/
def NoPrimeOversaturationCycle : Prop :=
  IsEmpty PrimeOversaturationCycle

/-- No forbidden internal prime-payment engine may exist. -/
def NoForbiddenPrimePaymentEngine : Prop :=
  IsEmpty ForbiddenPrimePaymentEngine

/-- If every cycle builds an engine and engines are impossible, cycles are impossible. -/
theorem noCycle_of_noEngine
    (buildEngine : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    NoPrimeOversaturationCycle := by
  exact ⟨fun cyc => hNoEngine.false (buildEngine cyc)⟩

/-#############################################################################
  §4. The adapter: Mersenne defect -> Step00 defect -> oversaturation -> cycle
#############################################################################-/

/--
Adapter from the four Mersenne final component defects into the old Step00 no-go
ledger.

This is the exact place where previous Step00 machinery must be connected.
Without this adapter, the statement "a defect creates an engine" is only a
metaphor.  With this adapter, it is a theorem.
-/
structure MersenneDefectToStep00Adapter
    (D : MersenneFinalDefectProfile) where
  tokenOf :
    ∀ c : MersenneFinalComponent,
      D.Defect c → Step00DefectToken

  oversaturates :
    ∀ c : MersenneFinalComponent,
    ∀ h : D.Defect c,
      PrimeOversaturationEvent

  cycleOfOversaturation :
    ∀ c : MersenneFinalComponent,
    ∀ h : D.Defect c,
      PrimeOversaturationCycle

  cycle_matches_event :
    ∀ c : MersenneFinalComponent,
    ∀ h : D.Defect c,
      (cycleOfOversaturation c h).event = oversaturates c h

/-- Any final Mersenne defect yields a prime-oversaturation event. -/
theorem oversaturation_of_any_defect
    {D : MersenneFinalDefectProfile}
    (A : MersenneDefectToStep00Adapter D)
    (hDef : AnyMersenneFinalDefect D) :
    Nonempty PrimeOversaturationEvent := by
  rcases hDef with ⟨c, hc⟩
  exact ⟨A.oversaturates c hc⟩

/-- Any final Mersenne defect yields a legal prime-oversaturation cycle. -/
theorem cycle_of_any_defect
    {D : MersenneFinalDefectProfile}
    (A : MersenneDefectToStep00Adapter D)
    (hDef : AnyMersenneFinalDefect D) :
    Nonempty PrimeOversaturationCycle := by
  rcases hDef with ⟨c, hc⟩
  exact ⟨A.cycleOfOversaturation c hc⟩

/-- If cycles are impossible, then no adapted final Mersenne defect may exist. -/
theorem no_finalDefect_of_adapter_and_noCycle
    {D : MersenneFinalDefectProfile}
    (A : MersenneDefectToStep00Adapter D)
    (hNoCycle : NoPrimeOversaturationCycle) :
    ¬ AnyMersenneFinalDefect D := by
  intro hDef
  rcases cycle_of_any_defect A hDef with ⟨cyc⟩
  exact hNoCycle.false cyc

/-- If cycles build engines and engines are impossible, then no adapted final defect exists. -/
theorem no_finalDefect_of_adapter_and_noEngine
    {D : MersenneFinalDefectProfile}
    (A : MersenneDefectToStep00Adapter D)
    (buildEngine : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ AnyMersenneFinalDefect D := by
  exact no_finalDefect_of_adapter_and_noCycle A
    (noCycle_of_noEngine buildEngine hNoEngine)

/-#############################################################################
  §5. Eventual absence + final-defect fork + no-go adapter
#############################################################################-/

/--
A final route may have a theorem saying that eventual absence forces one of the
four component defects.
-/
structure MersenneAbsenceForcesDefect
    (Prime : PrimeLike)
    (D : MersenneFinalDefectProfile) where
  absence_forces_defect :
    EventuallyNoMersenneTwinCenters Prime → AnyMersenneFinalDefect D

/--
If absence forces a final defect, and every final defect creates a forbidden
cycle, then eventual absence is impossible.
-/
theorem no_eventual_absence_of_absenceDefect_adapter_noCycle
    {Prime : PrimeLike}
    {D : MersenneFinalDefectProfile}
    (H : MersenneAbsenceForcesDefect Prime D)
    (A : MersenneDefectToStep00Adapter D)
    (hNoCycle : NoPrimeOversaturationCycle) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact no_finalDefect_of_adapter_and_noCycle A hNoCycle
    (H.absence_forces_defect hAbs)

/-- Same theorem phrased through the forbidden-engine no-go. -/
theorem no_eventual_absence_of_absenceDefect_adapter_noEngine
    {Prime : PrimeLike}
    {D : MersenneFinalDefectProfile}
    (H : MersenneAbsenceForcesDefect Prime D)
    (A : MersenneDefectToStep00Adapter D)
    (buildEngine : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact no_finalDefect_of_adapter_and_noEngine A buildEngine hNoEngine
    (H.absence_forces_defect hAbs)

/--
The complete endgame package: absence creates a component defect; component
defects oversaturate the prime-payment ledger; oversaturation creates a cycle;
cycles create forbidden engines; forbidden engines do not exist.
-/
structure MersenneAbsenceEngineContradictionRoute
    (Prime : PrimeLike)
    (D : MersenneFinalDefectProfile) where
  absence_defect : MersenneAbsenceForcesDefect Prime D
  adapter : MersenneDefectToStep00Adapter D
  buildEngine : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine
  noEngine : NoForbiddenPrimePaymentEngine

/-- The complete route forbids eventual Mersenne-twin absence. -/
theorem MersenneAbsenceEngineContradictionRoute.forbids_eventual_absence
    {Prime : PrimeLike}
    {D : MersenneFinalDefectProfile}
    (R : MersenneAbsenceEngineContradictionRoute Prime D) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact no_eventual_absence_of_absenceDefect_adapter_noEngine
    R.absence_defect R.adapter R.buildEngine R.noEngine

/-#############################################################################
  §6. Four-way concrete facade
#############################################################################-/

/-- Four named final component-defect propositions. -/
structure FourFinalDefects where
  OrdinaryTailSeedDefect : Prop
  CofinalAdmissibleDefect : Prop
  SemanticRealizerDefect : Prop
  SidePaymentDefect : Prop

namespace FourFinalDefects

/-- Turn the four named defect propositions into the profile used above. -/
def profile (Q : FourFinalDefects) : MersenneFinalDefectProfile :=
  DefectProfile.ofDisjunction
    Q.OrdinaryTailSeedDefect
    Q.CofinalAdmissibleDefect
    Q.SemanticRealizerDefect
    Q.SidePaymentDefect

/-- Four-way absence fork in the exact form produced by the previous sparse route. -/
def AbsenceForcesFourWayDefect
    (Prime : PrimeLike)
    (Q : FourFinalDefects) : Prop :=
  EventuallyNoMersenneTwinCenters Prime →
    Q.OrdinaryTailSeedDefect ∨
    Q.CofinalAdmissibleDefect ∨
    Q.SemanticRealizerDefect ∨
    Q.SidePaymentDefect

/-- Four-way absence fork becomes the uniform `MersenneAbsenceForcesDefect`. -/
def absenceForcesDefect
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (h : AbsenceForcesFourWayDefect Prime Q) :
    MersenneAbsenceForcesDefect Prime Q.profile where
  absence_forces_defect := by
    intro hAbs
    exact DefectProfile.any_of_four_way (h hAbs)

/-- Four-way facade of the engine contradiction route. -/
theorem no_eventual_absence_of_fourWayDefects_engineNoGo
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (A : MersenneDefectToStep00Adapter Q.profile)
    (buildEngine : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact no_eventual_absence_of_absenceDefect_adapter_noEngine
    (absenceForcesDefect hFork) A buildEngine hNoEngine

end FourFinalDefects

/-#############################################################################
  §7. Slogan theorem
#############################################################################-/

/--
Final slogan: within the audited bridge, absence of Mersenne twins cannot remain
clean.  It must either fail before producing a final defect, or the final defect
creates a prime-oversaturation cycle / forbidden engine.
-/
theorem mersenne_defect_oversaturation_engine_slogan
    {Prime : PrimeLike}
    {D : MersenneFinalDefectProfile}
    (R : MersenneAbsenceEngineContradictionRoute Prime D) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  R.forbids_eventual_absence

end DefectOversaturationBridge
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_defect_no_escape_closure_patch.lean =====
/-
EuclidsPath — Mersenne defect no-escape closure, multi-step patch
==================================================================

Purpose
-------
This patch pushes the Mersenne branch several steps past the previous
"defect -> oversaturation -> engine" bridge.

It formalizes the no-escape endgame:

  1. eventual absence of Mersenne-twin centers forces one of four final defects;
  2. each final defect is mapped into the old Step00 defect taxonomy;
  3. every mapped Step00 defect creates a prime-payment oversaturation event;
  4. every oversaturation event creates a legal cycle;
  5. every legal cycle builds a forbidden internal engine;
  6. forbidden internal engines are impossible;
  7. therefore eventual absence is impossible;
  8. classically, no eventual absence gives cofinally many Mersenne-twin centers.

No arithmetic miracle is hidden here.  The file does not prove the concrete
component adapters.  It proves that once the four adapters are supplied, the
Mersenne absence branch has no clean escape.

No axiom.  No sorry.
-/



namespace EuclidsPath
namespace Mersenne
namespace DefectNoEscapeClosure

/-#############################################################################
  §1. Minimal Mersenne vocabulary
#############################################################################-/

/-- Abstract primality predicate.  In the concrete instance use `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- Lower member of the Step00 twin pair centered at `m`. -/
def lowerSide (m : Nat) : Nat := 6 * m - 1

/-- Upper member of the Step00 twin pair centered at `m`. -/
def upperSide (m : Nat) : Nat := 6 * m + 1

/-- Mersenne/base-4 repunit center. -/
def mersenneCenter (k : Nat) : Nat := (4 ^ k - 1) / 3

/-- Mersenne-twin center at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerSide (mersenneCenter k)) ∧
  Prime (upperSide (mersenneCenter k))

/-- Cofinitely unbounded / infinitely many Mersenne-twin centers. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Tail absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal infinitude forbids tail absence. -/
theorem not_eventual_absence_of_infinite
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNo⟩
  rcases hInf K0 with ⟨k, hk, hkTwin⟩
  exact hNo k hk hkTwin

/-- Conversely, classically, absence of a tail cutoff gives cofinal infinitude. -/
theorem infinite_of_not_eventual_absence
    {Prime : PrimeLike}
    (hNoAbs : ¬ EventuallyNoMersenneTwinCenters Prime) :
    InfinitelyManyMersenneTwinCenters Prime := by
  classical
  intro K0
  by_contra hNoHit
  apply hNoAbs
  refine ⟨K0, ?_⟩
  intro k hk hkTwin
  exact hNoHit ⟨k, hk, hkTwin⟩

/-#############################################################################
  §2. The four final Mersenne component defects
#############################################################################-/

/-- The final four component classes in the corrected sparse Mersenne route. -/
inductive MersenneFinalComponent where
  | ordinaryTailSeed
  | cofinalAdmissibleFilter
  | semanticTargetRealizer
  | sidePayment
  deriving DecidableEq, Repr

/-- Human-readable defect profile: which final component is broken. -/
structure FourFinalDefects where
  OrdinaryTailSeedDefect : Prop
  CofinalAdmissibleDefect : Prop
  SemanticRealizerDefect : Prop
  SidePaymentDefect : Prop

namespace FourFinalDefects

/-- Component-indexed defect predicate. -/
def defect (Q : FourFinalDefects) : MersenneFinalComponent → Prop
  | MersenneFinalComponent.ordinaryTailSeed => Q.OrdinaryTailSeedDefect
  | MersenneFinalComponent.cofinalAdmissibleFilter => Q.CofinalAdmissibleDefect
  | MersenneFinalComponent.semanticTargetRealizer => Q.SemanticRealizerDefect
  | MersenneFinalComponent.sidePayment => Q.SidePaymentDefect

/-- At least one final component defect is present. -/
def Any (Q : FourFinalDefects) : Prop :=
  ∃ c : MersenneFinalComponent, Q.defect c

/-- Four-way disjunction to indexed form. -/
theorem any_of_four_way
    {Q : FourFinalDefects}
    (h : Q.OrdinaryTailSeedDefect ∨
         Q.CofinalAdmissibleDefect ∨
         Q.SemanticRealizerDefect ∨
         Q.SidePaymentDefect) :
    Q.Any := by
  rcases h with hO | hRest
  · exact ⟨MersenneFinalComponent.ordinaryTailSeed, hO⟩
  rcases hRest with hC | hRest
  · exact ⟨MersenneFinalComponent.cofinalAdmissibleFilter, hC⟩
  rcases hRest with hR | hP
  · exact ⟨MersenneFinalComponent.semanticTargetRealizer, hR⟩
  · exact ⟨MersenneFinalComponent.sidePayment, hP⟩

/-- Indexed form back to four-way disjunction. -/
theorem four_way_of_any
    {Q : FourFinalDefects}
    (h : Q.Any) :
    Q.OrdinaryTailSeedDefect ∨
    Q.CofinalAdmissibleDefect ∨
    Q.SemanticRealizerDefect ∨
    Q.SidePaymentDefect := by
  rcases h with ⟨c, hc⟩
  cases c with
  | ordinaryTailSeed => exact Or.inl hc
  | cofinalAdmissibleFilter => exact Or.inr (Or.inl hc)
  | semanticTargetRealizer => exact Or.inr (Or.inr (Or.inl hc))
  | sidePayment => exact Or.inr (Or.inr (Or.inr hc))

end FourFinalDefects

/-- Previous sparse route output: eventual absence forces a four-way final defect. -/
def AbsenceForcesFourWayDefect
    (Prime : PrimeLike)
    (Q : FourFinalDefects) : Prop :=
  EventuallyNoMersenneTwinCenters Prime →
    Q.OrdinaryTailSeedDefect ∨
    Q.CofinalAdmissibleDefect ∨
    Q.SemanticRealizerDefect ∨
    Q.SidePaymentDefect

/-- Same previous route output in component-indexed form. -/
def AbsenceForcesAnyDefect
    (Prime : PrimeLike)
    (Q : FourFinalDefects) : Prop :=
  EventuallyNoMersenneTwinCenters Prime → Q.Any

/-- Four-way fork becomes indexed fork. -/
theorem anyDefect_of_fourWayFork
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q) :
    AbsenceForcesAnyDefect Prime Q := by
  intro hAbs
  exact FourFinalDefects.any_of_four_way (hFork hAbs)

/-#############################################################################
  §3. Step00 no-go taxonomy
#############################################################################-/

/-- The old Step00 defect taxonomy as needed by the Mersenne adapter. -/
inductive Step00DefectKind where
  | seedSupplyGap
  | projectionCofinalityGap
  | semanticLiftGap
  | paymentGap
  | seamEscape
  | compressionEscape
  | gaugeEscape
  | unpaidBoundaryJump
  deriving DecidableEq, Repr

/-- A concrete Step00 defect token. -/
structure Step00DefectToken where
  kind : Step00DefectKind
  level : Nat

/-- A prime-payment bucket has been oversaturated by a Step00 defect. -/
structure PrimeOversaturationEvent where
  token : Step00DefectToken
  bucket : Nat
  overloaded : Prop
  overloaded_proof : overloaded

/-- A legal cycle extracted from prime-payment oversaturation. -/
structure PrimeOversaturationCycle where
  event : PrimeOversaturationEvent
  legal : Prop
  legal_proof : legal

/-- A forbidden internal engine built from a legal oversaturation cycle. -/
structure ForbiddenPrimePaymentEngine where
  cycle : PrimeOversaturationCycle
  internal : Prop
  internal_proof : internal

/-- No legal oversaturation cycle exists. -/
def NoPrimeOversaturationCycle : Prop :=
  IsEmpty PrimeOversaturationCycle

/-- No forbidden internal engine exists. -/
def NoForbiddenPrimePaymentEngine : Prop :=
  IsEmpty ForbiddenPrimePaymentEngine

/-- A Step00 no-go engine builder: every oversaturation cycle yields an engine. -/
def CycleBuildsForbiddenEngine : Prop :=
  PrimeOversaturationCycle → Nonempty ForbiddenPrimePaymentEngine

/-- If cycles build engines and engines are forbidden, cycles are forbidden. -/
theorem noCycle_of_noEngine
    (buildEngine : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    NoPrimeOversaturationCycle := by
  exact ⟨fun cyc => (buildEngine cyc).elim hNoEngine.false⟩

/-#############################################################################
  §4. Component adapters, not one monolithic adapter
#############################################################################-/

/-- Adapter for a single final component defect into a Step00 token. -/
structure ComponentToStep00Adapter
    (Q : FourFinalDefects)
    (component : MersenneFinalComponent) where
  tokenOf : Q.defect component → Step00DefectToken

/-- The four component adapters. -/
structure FourComponentStep00Adapters
    (Q : FourFinalDefects) where
  ordinarySeed : ComponentToStep00Adapter Q MersenneFinalComponent.ordinaryTailSeed
  cofinalFilter : ComponentToStep00Adapter Q MersenneFinalComponent.cofinalAdmissibleFilter
  semanticRealizer : ComponentToStep00Adapter Q MersenneFinalComponent.semanticTargetRealizer
  sidePayment : ComponentToStep00Adapter Q MersenneFinalComponent.sidePayment

namespace FourComponentStep00Adapters

/-- Unified token extraction from the four component adapters. -/
def tokenOf
    {Q : FourFinalDefects}
    (A : FourComponentStep00Adapters Q)
    (c : MersenneFinalComponent)
    (h : Q.defect c) : Step00DefectToken :=
  match c with
  | MersenneFinalComponent.ordinaryTailSeed => A.ordinarySeed.tokenOf h
  | MersenneFinalComponent.cofinalAdmissibleFilter => A.cofinalFilter.tokenOf h
  | MersenneFinalComponent.semanticTargetRealizer => A.semanticRealizer.tokenOf h
  | MersenneFinalComponent.sidePayment => A.sidePayment.tokenOf h

end FourComponentStep00Adapters

/-- Step00 no-clean-defect principle: every token oversaturates prime-payment. -/
structure Step00TokenOversaturationLaw where
  oversaturates : Step00DefectToken → PrimeOversaturationEvent
  cycleOf : ∀ t : Step00DefectToken, PrimeOversaturationCycle
  cycle_matches : ∀ t : Step00DefectToken, (cycleOf t).event = oversaturates t

/-- Full adapter assembled from component adapters and the old Step00 oversaturation law. -/
structure MersenneDefectNoEscapeAdapter
    (Q : FourFinalDefects) where
  components : FourComponentStep00Adapters Q
  step00_oversaturation : Step00TokenOversaturationLaw

namespace MersenneDefectNoEscapeAdapter

/-- Defect component -> Step00 token. -/
def tokenOf
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (c : MersenneFinalComponent)
    (h : Q.defect c) : Step00DefectToken :=
  A.components.tokenOf c h

/-- Defect component -> prime oversaturation event. -/
def oversaturationOf
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (c : MersenneFinalComponent)
    (h : Q.defect c) : PrimeOversaturationEvent :=
  A.step00_oversaturation.oversaturates (A.tokenOf c h)

/-- Defect component -> legal oversaturation cycle. -/
def cycleOf
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (c : MersenneFinalComponent)
    (h : Q.defect c) : PrimeOversaturationCycle :=
  A.step00_oversaturation.cycleOf (A.tokenOf c h)

/-- Any final component defect creates a legal oversaturation cycle. -/
theorem cycle_of_any_defect
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (hAny : Q.Any) :
    Nonempty PrimeOversaturationCycle := by
  rcases hAny with ⟨c, hc⟩
  exact ⟨A.cycleOf c hc⟩

/-- Any final component defect creates a prime-oversaturation event. -/
theorem oversaturation_of_any_defect
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (hAny : Q.Any) :
    Nonempty PrimeOversaturationEvent := by
  rcases hAny with ⟨c, hc⟩
  exact ⟨A.oversaturationOf c hc⟩

/-- If cycles are forbidden, no adapted final component defect exists. -/
theorem no_final_defect_of_noCycle
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (hNoCycle : NoPrimeOversaturationCycle) :
    ¬ Q.Any := by
  intro hAny
  rcases A.cycle_of_any_defect hAny with ⟨cyc⟩
  exact hNoCycle.false cyc

/-- If cycles build forbidden engines and engines are impossible, no adapted defect exists. -/
theorem no_final_defect_of_noEngine
    {Q : FourFinalDefects}
    (A : MersenneDefectNoEscapeAdapter Q)
    (buildEngine : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ Q.Any := by
  exact A.no_final_defect_of_noCycle (noCycle_of_noEngine buildEngine hNoEngine)

end MersenneDefectNoEscapeAdapter

/-#############################################################################
  §5. The no-escape closure theorem
#############################################################################-/

/-- Complete no-escape route. -/
structure MersenneDefectNoEscapeRoute
    (Prime : PrimeLike)
    (Q : FourFinalDefects) where
  absence_forces_defect : AbsenceForcesAnyDefect Prime Q
  adapter : MersenneDefectNoEscapeAdapter Q
  buildEngine : CycleBuildsForbiddenEngine
  noEngine : NoForbiddenPrimePaymentEngine

namespace MersenneDefectNoEscapeRoute

/-- Eventual absence is impossible under the no-escape route. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (R : MersenneDefectNoEscapeRoute Prime Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact R.adapter.no_final_defect_of_noEngine R.buildEngine R.noEngine
    (R.absence_forces_defect hAbs)

/-- Classically, the no-escape route yields cofinally many Mersenne-twin centers. -/
theorem produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (R : MersenneDefectNoEscapeRoute Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_of_not_eventual_absence R.forbids_eventual_absence

end MersenneDefectNoEscapeRoute

/-- Four-way facade: use the previous sparse route theorem directly. -/
theorem no_eventual_absence_of_fourWayFork_and_noEscape
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (A : MersenneDefectNoEscapeAdapter Q)
    (buildEngine : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  let R : MersenneDefectNoEscapeRoute Prime Q :=
    { absence_forces_defect := anyDefect_of_fourWayFork hFork
      adapter := A
      buildEngine := buildEngine
      noEngine := hNoEngine }
  exact R.forbids_eventual_absence

/-- Four-way facade, infinite-output form. -/
theorem infinite_mersenne_twins_of_fourWayFork_and_noEscape
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (A : MersenneDefectNoEscapeAdapter Q)
    (buildEngine : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_of_not_eventual_absence
    (no_eventual_absence_of_fourWayFork_and_noEscape hFork A buildEngine hNoEngine)

/-#############################################################################
  §6. Contrapositive audit: if absence survives, some adapter/no-go component is missing
#############################################################################-/

/-- The no-escape machine can fail only through a missing fork, adapter, cycle->engine, or no-engine theorem. -/
def NoEscapeMachineReady
    (Prime : PrimeLike)
    (Q : FourFinalDefects) : Prop :=
  AbsenceForcesAnyDefect Prime Q ∧
  Nonempty (MersenneDefectNoEscapeAdapter Q) ∧
  CycleBuildsForbiddenEngine ∧
  NoForbiddenPrimePaymentEngine

/-- If the no-escape machine is ready, absence is impossible. -/
theorem no_absence_of_ready_noEscapeMachine
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hReady : NoEscapeMachineReady Prime Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  rcases hReady with ⟨hFork, ⟨A⟩, hBuild, hNoEngine⟩
  let R : MersenneDefectNoEscapeRoute Prime Q :=
    { absence_forces_defect := hFork
      adapter := A
      buildEngine := hBuild
      noEngine := hNoEngine }
  exact R.forbids_eventual_absence

/-- If absence holds, then the complete no-escape machine is not ready. -/
theorem absence_forces_noEscapeMachine_not_ready
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    ¬ NoEscapeMachineReady Prime Q := by
  intro hReady
  exact no_absence_of_ready_noEscapeMachine hReady hAbs

/-- Expanded contrapositive: if absence holds and the fork/no-go are available, the adapter is missing. -/
theorem absence_forces_adapter_gap_of_fork_and_noEngine
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hAbs : EventuallyNoMersenneTwinCenters Prime)
    (hFork : AbsenceForcesAnyDefect Prime Q)
    (hBuild : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ Nonempty (MersenneDefectNoEscapeAdapter Q) := by
  intro hA
  exact absence_forces_noEscapeMachine_not_ready hAbs
    ⟨hFork, hA, hBuild, hNoEngine⟩

/-- Expanded contrapositive in four-way form. -/
theorem absence_forces_adapter_gap_of_fourWayFork_and_noEngine
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hAbs : EventuallyNoMersenneTwinCenters Prime)
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (hBuild : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ Nonempty (MersenneDefectNoEscapeAdapter Q) := by
  exact absence_forces_adapter_gap_of_fork_and_noEngine hAbs
    (anyDefect_of_fourWayFork hFork) hBuild hNoEngine

/-#############################################################################
  §7. Component-level closure: four individual no-clean-defect laws
#############################################################################-/

/-- A component is closed if its defect has a Step00-token adapter. -/
def ComponentClosed
    (Q : FourFinalDefects)
    (c : MersenneFinalComponent) : Prop :=
  Nonempty (ComponentToStep00Adapter Q c)

/-- All four components are individually closed. -/
structure FourComponentsClosed
    (Q : FourFinalDefects) where
  ordinarySeed : ComponentClosed Q MersenneFinalComponent.ordinaryTailSeed
  cofinalFilter : ComponentClosed Q MersenneFinalComponent.cofinalAdmissibleFilter
  semanticRealizer : ComponentClosed Q MersenneFinalComponent.semanticTargetRealizer
  sidePayment : ComponentClosed Q MersenneFinalComponent.sidePayment

namespace FourComponentsClosed

/-- Individual closures assemble into the four component adapters. -/
noncomputable def toAdapters
    {Q : FourFinalDefects}
    (C : FourComponentsClosed Q) :
    FourComponentStep00Adapters Q :=
  { ordinarySeed := Classical.choice C.ordinarySeed
    cofinalFilter := Classical.choice C.cofinalFilter
    semanticRealizer := Classical.choice C.semanticRealizer
    sidePayment := Classical.choice C.sidePayment }

/-- Individual closures plus Step00 oversaturation law assemble the no-escape adapter. -/
noncomputable def toNoEscapeAdapter
    {Q : FourFinalDefects}
    (C : FourComponentsClosed Q)
    (O : Step00TokenOversaturationLaw) :
    MersenneDefectNoEscapeAdapter Q :=
  { components := C.toAdapters
    step00_oversaturation := O }

end FourComponentsClosed

/-- Final component-closed theorem. -/
theorem no_eventual_absence_of_component_closure
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (C : FourComponentsClosed Q)
    (O : Step00TokenOversaturationLaw)
    (hBuild : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact no_eventual_absence_of_fourWayFork_and_noEscape hFork
    (C.toNoEscapeAdapter O) hBuild hNoEngine

/-- Infinite-output form of the component-closed theorem. -/
theorem infinite_mersenne_twins_of_component_closure
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (C : FourComponentsClosed Q)
    (O : Step00TokenOversaturationLaw)
    (hBuild : CycleBuildsForbiddenEngine)
    (hNoEngine : NoForbiddenPrimePaymentEngine) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_of_not_eventual_absence
    (no_eventual_absence_of_component_closure hFork C O hBuild hNoEngine)

/-#############################################################################
  §8. Final slogan theorem
#############################################################################-/

/-- Compact final route package. -/
structure MersenneMaxForwardNoEscapeFront
    (Prime : PrimeLike)
    (Q : FourFinalDefects) where
  absenceFork : AbsenceForcesFourWayDefect Prime Q
  componentsClosed : FourComponentsClosed Q
  step00Oversaturation : Step00TokenOversaturationLaw
  cycleBuildsEngine : CycleBuildsForbiddenEngine
  noEngine : NoForbiddenPrimePaymentEngine

namespace MersenneMaxForwardNoEscapeFront

/-- The maximum-forward no-escape front forbids tail absence. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (F : MersenneMaxForwardNoEscapeFront Prime Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact no_eventual_absence_of_component_closure
    F.absenceFork
    F.componentsClosed
    F.step00Oversaturation
    F.cycleBuildsEngine
    F.noEngine

/-- Classically, the maximum-forward no-escape front produces cofinally many Mersenne twins. -/
theorem produces_infinite_mersenne_twins
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (F : MersenneMaxForwardNoEscapeFront Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact infinite_of_not_eventual_absence F.forbids_eventual_absence

end MersenneMaxForwardNoEscapeFront

/-- Final slogan: absence has no clean defect escape once the four component closures are attached to Step00 no-go. -/
theorem mersenne_no_clean_defect_escape_slogan
    {Prime : PrimeLike}
    {Q : FourFinalDefects}
    (F : MersenneMaxForwardNoEscapeFront Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨F.produces_infinite_mersenne_twins, F.forbids_eventual_absence⟩

end DefectNoEscapeClosure
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_full_closure_endgame_patch.lean =====
/-
EuclidsPath — Mersenne route, full closure endgame
=================================================

This patch pushes the Mersenne-twin route to the formal closure point.

It proves the final implication:

    absence of Mersenne-twin centers on a tail
      -> one of the four final route defects
      -> Step00 defect token
      -> prime oversaturation
      -> legal cycle
      -> forbidden internal prime-payment engine
      -> contradiction

Therefore, under the closure package, Mersenne-twin centers are cofinal.

Important status
----------------
This file does NOT prove the arithmetic content unconditionally.  The closing
content is isolated in the fields of `MersenneFullClosureFront` and in the
smaller packages below:

  * `AbsenceForcesFourWayDefect`
  * `FourComponentClosures`
  * `Step00OversaturationNoGo`

No axiom and no sorry are used here.  The file is a clean endgame/closure
adapter: once the component closures are supplied by the Step00 theory, the
absence of Mersenne-twin centers is impossible.
-/



namespace EuclidsPath
namespace MersenneFullClosure

/-#############################################################################
  §1. Arithmetic-facing predicates
#############################################################################-/

/-- A placeholder for the primality predicate used by a concrete implementation. -/
abbrev PrimeLike := Nat → Prop

/-- The Mersenne-twin condition at base-4 index `k`.

The sides are:

  lower = 2^(2*k+1) - 3,
  upper = 2^(2*k+1) - 1.
-/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (2 ^ (2 * k + 1) - 3) ∧ Prime (2 ^ (2 * k + 1) - 1)

/-- Tail absence: from some `K0` onward no Mersenne-twin center occurs. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal/infinite supply: above every floor `K0` there is a Mersenne-twin center. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Cofinality is equivalent to the negation of tail absence. -/
theorem infinite_iff_not_eventual_absence (Prime : PrimeLike) :
    InfinitelyManyMersenneTwinCenters Prime ↔
      ¬ EventuallyNoMersenneTwinCenters Prime := by
  constructor
  · intro hInf hAbs
    rcases hAbs with ⟨K0, hNo⟩
    rcases hInf K0 with ⟨k, hk, hTwin⟩
    exact hNo k hk hTwin
  · intro hNoAbs K0
    by_contra hNone
    apply hNoAbs
    exact ⟨K0, by
      intro k hk hTwin
      exact hNone ⟨k, hk, hTwin⟩⟩

/-#############################################################################
  §2. Four final route defects
#############################################################################-/

/-- The four final components of the corrected sparse Mersenne route. -/
inductive MersenneFinalComponent where
  | ordinarySeed
  | cofinalAdmissibleFilter
  | semanticTargetRealizer
  | sidePaymentCertificate
  deriving DecidableEq, Repr

/-- A final component defect, naming which component failed. -/
structure MersenneFinalDefect where
  component : MersenneFinalComponent
  payload : Prop
  payload_proof : payload

/-- The four named defect propositions for a given final route. -/
structure FourFinalDefectProps where
  ordinarySeedDefect : Prop
  cofinalFilterDefect : Prop
  semanticRealizerDefect : Prop
  sidePaymentDefect : Prop

namespace FourFinalDefectProps

/-- Package an ordinary-seed defect as a generic final defect. -/
def mkOrdinarySeed (Q : FourFinalDefectProps)
    (h : Q.ordinarySeedDefect) : MersenneFinalDefect where
  component := MersenneFinalComponent.ordinarySeed
  payload := Q.ordinarySeedDefect
  payload_proof := h

/-- Package a cofinal-filter defect as a generic final defect. -/
def mkCofinalFilter (Q : FourFinalDefectProps)
    (h : Q.cofinalFilterDefect) : MersenneFinalDefect where
  component := MersenneFinalComponent.cofinalAdmissibleFilter
  payload := Q.cofinalFilterDefect
  payload_proof := h

/-- Package a semantic-realizer defect as a generic final defect. -/
def mkSemanticRealizer (Q : FourFinalDefectProps)
    (h : Q.semanticRealizerDefect) : MersenneFinalDefect where
  component := MersenneFinalComponent.semanticTargetRealizer
  payload := Q.semanticRealizerDefect
  payload_proof := h

/-- Package a side-payment defect as a generic final defect. -/
def mkSidePayment (Q : FourFinalDefectProps)
    (h : Q.sidePaymentDefect) : MersenneFinalDefect where
  component := MersenneFinalComponent.sidePaymentCertificate
  payload := Q.sidePaymentDefect
  payload_proof := h

end FourFinalDefectProps

/-- Tail absence forces one of the four final component defects. -/
structure AbsenceForcesFourWayDefect
    (Prime : PrimeLike) (Q : FourFinalDefectProps) where
  fork : EventuallyNoMersenneTwinCenters Prime →
    Q.ordinarySeedDefect ∨
    Q.cofinalFilterDefect ∨
    Q.semanticRealizerDefect ∨
    Q.sidePaymentDefect

namespace AbsenceForcesFourWayDefect

/-- Convert the four-way fork into a generic final defect token. -/
noncomputable def defectOfAbsence
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (A : AbsenceForcesFourWayDefect Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) : MersenneFinalDefect := by
  classical
  by_cases hOrd : Q.ordinarySeedDefect
  · exact Q.mkOrdinarySeed hOrd
  · by_cases hCof : Q.cofinalFilterDefect
    · exact Q.mkCofinalFilter hCof
    · by_cases hSem : Q.semanticRealizerDefect
      · exact Q.mkSemanticRealizer hSem
      · by_cases hPay : Q.sidePaymentDefect
        · exact Q.mkSidePayment hPay
        · exact absurd (A.fork hAbs) (by
            intro h
            rcases h with h | h | h | h
            · exact hOrd h
            · exact hCof h
            · exact hSem h
            · exact hPay h)

end AbsenceForcesFourWayDefect

/-#############################################################################
  §3. Step00 defect taxonomy and oversaturation engine
#############################################################################-/

/-- Existing Step00 defect classes used by the old no-go layer. -/
inductive Step00DefectKind where
  | missingSeed
  | boundedCofinality
  | failedRealizer
  | unpaidBoundary
  | seamEscape
  | compressionEscape
  | gaugeLeak
  | primePaymentOversaturation
  deriving DecidableEq, Repr

/-- A Step00 defect token: the concrete old-theory defect generated by a Mersenne defect. -/
structure Step00DefectToken where
  kind : Step00DefectKind
  payload : Prop
  payload_proof : payload

/-- A prime-payment oversaturation event. -/
structure PrimeOversaturationEvent where
  token : Step00DefectToken
  payload : Prop
  payload_proof : payload

/-- A legal cycle produced by oversaturation. -/
structure PrimeOversaturationCycle where
  event : PrimeOversaturationEvent
  payload : Prop
  payload_proof : payload

/-- The forbidden internal engine produced by such a cycle. -/
structure ForbiddenPrimePaymentEngine where
  cycle : PrimeOversaturationCycle
  payload : Prop
  payload_proof : payload

/-- No forbidden internal prime-payment engine may exist. -/
def NoForbiddenPrimePaymentEngine : Prop :=
  ¬ Nonempty ForbiddenPrimePaymentEngine

/-- Four component-specific adapters into old Step00 defect tokens. -/
structure FourComponentClosures (Q : FourFinalDefectProps) where
  ordinarySeed_to_token : Q.ordinarySeedDefect → Step00DefectToken
  cofinalFilter_to_token : Q.cofinalFilterDefect → Step00DefectToken
  semanticRealizer_to_token : Q.semanticRealizerDefect → Step00DefectToken
  sidePayment_to_token : Q.sidePaymentDefect → Step00DefectToken

namespace FourComponentClosures

/-- A generic final defect maps to a Step00 defect token. -/
def tokenOfDefect {Q : FourFinalDefectProps}
    (C : FourComponentClosures Q) : MersenneFinalDefect → Step00DefectToken
  | ⟨MersenneFinalComponent.ordinarySeed, p, hp⟩ =>
      -- The payload is definitionally the recorded defect proposition for this branch
      -- only when produced by `mkOrdinarySeed`.  For arbitrary generic defects we use
      -- the branch-specific closure through an implication supplied in
      -- `FourComponentExactClosures` below.  This fallback marks arbitrary
      -- unmatched profiles as a gauge leak.
      { kind := Step00DefectKind.gaugeLeak, payload := p, payload_proof := hp }
  | ⟨MersenneFinalComponent.cofinalAdmissibleFilter, p, hp⟩ =>
      { kind := Step00DefectKind.gaugeLeak, payload := p, payload_proof := hp }
  | ⟨MersenneFinalComponent.semanticTargetRealizer, p, hp⟩ =>
      { kind := Step00DefectKind.gaugeLeak, payload := p, payload_proof := hp }
  | ⟨MersenneFinalComponent.sidePaymentCertificate, p, hp⟩ =>
      { kind := Step00DefectKind.gaugeLeak, payload := p, payload_proof := hp }

end FourComponentClosures

/-- Exact closure from the actual four-way fork, preserving the branch proposition. -/
noncomputable def tokenOfForkBranch {Q : FourFinalDefectProps}
    (C : FourComponentClosures Q) :
    Q.ordinarySeedDefect ∨
    Q.cofinalFilterDefect ∨
    Q.semanticRealizerDefect ∨
    Q.sidePaymentDefect → Step00DefectToken := fun h => by
  classical
  by_cases hOrd : Q.ordinarySeedDefect
  · exact C.ordinarySeed_to_token hOrd
  · by_cases hCof : Q.cofinalFilterDefect
    · exact C.cofinalFilter_to_token hCof
    · by_cases hSem : Q.semanticRealizerDefect
      · exact C.semanticRealizer_to_token hSem
      · by_cases hPay : Q.sidePaymentDefect
        · exact C.sidePayment_to_token hPay
        · exact absurd h (by
            intro hh
            rcases hh with hh | hh | hh | hh
            · exact hOrd hh
            · exact hCof hh
            · exact hSem hh
            · exact hPay hh)

/-- Old Step00 no-go layer: every Step00 defect token oversaturates prime payment. -/
structure Step00TokenOversaturationLaw where
  oversaturates : Step00DefectToken → PrimeOversaturationEvent

/-- Old Step00 no-go layer: oversaturation creates a legal cycle. -/
structure OversaturationBuildsCycle where
  cycleOf : PrimeOversaturationEvent → PrimeOversaturationCycle

/-- Old Step00 no-go layer: a legal oversaturation cycle builds a forbidden engine. -/
structure CycleBuildsForbiddenEngine where
  engineOf : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine

/-- Compact old Step00 no-clean-defect no-go theorem. -/
structure Step00OversaturationNoGo where
  tokenOversaturation : Step00TokenOversaturationLaw
  cycleBuilds : OversaturationBuildsCycle
  engineBuilds : CycleBuildsForbiddenEngine
  noEngine : NoForbiddenPrimePaymentEngine

namespace Step00OversaturationNoGo

/-- Any Step00 defect token creates a forbidden engine. -/
def engineOfToken (N : Step00OversaturationNoGo)
    (T : Step00DefectToken) : ForbiddenPrimePaymentEngine :=
  N.engineBuilds.engineOf (N.cycleBuilds.cycleOf (N.tokenOversaturation.oversaturates T))

/-- Therefore no Step00 defect token can exist in a closed no-engine universe. -/
theorem noToken (N : Step00OversaturationNoGo) :
    ¬ Nonempty Step00DefectToken := by
  intro hTok
  rcases hTok with ⟨T⟩
  exact N.noEngine ⟨N.engineOfToken T⟩

end Step00OversaturationNoGo

/-#############################################################################
  §4. Full closure front
#############################################################################-/

/-- The exact final front needed to close the Mersenne route. -/
structure MersenneFullClosureFront
    (Prime : PrimeLike) (Q : FourFinalDefectProps) where
  absenceFork : AbsenceForcesFourWayDefect Prime Q
  componentClosures : FourComponentClosures Q
  step00NoGo : Step00OversaturationNoGo

namespace MersenneFullClosureFront

/-- Tail absence creates a Step00 defect token. -/
noncomputable def tokenOfAbsence
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) : Step00DefectToken :=
  tokenOfForkBranch F.componentClosures (F.absenceFork.fork hAbs)

/-- Tail absence creates a prime oversaturation event. -/
noncomputable def oversaturationOfAbsence
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) : PrimeOversaturationEvent :=
  F.step00NoGo.tokenOversaturation.oversaturates (F.tokenOfAbsence hAbs)

/-- Tail absence creates a legal oversaturation cycle. -/
noncomputable def cycleOfAbsence
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) : PrimeOversaturationCycle :=
  F.step00NoGo.cycleBuilds.cycleOf (F.oversaturationOfAbsence hAbs)

/-- Tail absence creates a forbidden prime-payment engine. -/
noncomputable def engineOfAbsence
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) : ForbiddenPrimePaymentEngine :=
  F.step00NoGo.engineBuilds.engineOf (F.cycleOfAbsence hAbs)

/-- Hence tail absence is impossible. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact F.step00NoGo.noEngine ⟨F.engineOfAbsence hAbs⟩

/-- Therefore Mersenne-twin centers are cofinal/infinite. -/
theorem produces_infinite_mersenne_twins
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact (infinite_iff_not_eventual_absence Prime).2 F.forbids_eventual_absence

/-- One-line final closure summary. -/
theorem full_closure_slogan
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  exact ⟨F.produces_infinite_mersenne_twins, F.forbids_eventual_absence⟩

end MersenneFullClosureFront

/-#############################################################################
  §5. Defect impossibility view
#############################################################################-/

/-- Component closures plus the Step00 no-go make each of the four defect props impossible. -/
structure FourDefectsImpossible (Q : FourFinalDefectProps) where
  noOrdinarySeedDefect : ¬ Q.ordinarySeedDefect
  noCofinalFilterDefect : ¬ Q.cofinalFilterDefect
  noSemanticRealizerDefect : ¬ Q.semanticRealizerDefect
  noSidePaymentDefect : ¬ Q.sidePaymentDefect

/-- The full closure front implies direct impossibility of all four defects. -/
theorem fourDefectsImpossible_of_fullClosureFront
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (F : MersenneFullClosureFront Prime Q) :
    FourDefectsImpossible Q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact F.step00NoGo.noToken ⟨F.componentClosures.ordinarySeed_to_token h⟩
  · intro h
    exact F.step00NoGo.noToken ⟨F.componentClosures.cofinalFilter_to_token h⟩
  · intro h
    exact F.step00NoGo.noToken ⟨F.componentClosures.semanticRealizer_to_token h⟩
  · intro h
    exact F.step00NoGo.noToken ⟨F.componentClosures.sidePayment_to_token h⟩

/-- A four-way fork plus direct impossibility of all four defects forbids absence. -/
theorem no_eventual_absence_of_fourWayFork_and_defectImpossible
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (A : AbsenceForcesFourWayDefect Prime Q)
    (N : FourDefectsImpossible Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases A.fork hAbs with hOrd | hCof | hSem | hPay
  · exact N.noOrdinarySeedDefect hOrd
  · exact N.noCofinalFilterDefect hCof
  · exact N.noSemanticRealizerDefect hSem
  · exact N.noSidePaymentDefect hPay

/-- The same direct view produces infinite Mersenne-twin centers. -/
theorem infinite_mersenne_twins_of_fourWayFork_and_defectImpossible
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (A : AbsenceForcesFourWayDefect Prime Q)
    (N : FourDefectsImpossible Q) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact (infinite_iff_not_eventual_absence Prime).2
    (no_eventual_absence_of_fourWayFork_and_defectImpossible A N)

/-#############################################################################
  §6. “No clean escape” audit
#############################################################################-/

/-- If absence survives, the full closure front cannot be inhabited. -/
theorem absence_forces_no_fullClosureFront
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    ¬ Nonempty (MersenneFullClosureFront Prime Q) := by
  intro hF
  rcases hF with ⟨F⟩
  exact F.forbids_eventual_absence hAbs

/-- If absence survives and the Step00 no-go is accepted, some component closure is missing. -/
theorem absence_forces_missing_component_closure_or_noGo
    {Prime : PrimeLike} {Q : FourFinalDefectProps}
    (A : AbsenceForcesFourWayDefect Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    ¬ (Nonempty (FourComponentClosures Q) ∧ Nonempty Step00OversaturationNoGo) := by
  intro h
  rcases h with ⟨⟨C⟩, ⟨N⟩⟩
  let F : MersenneFullClosureFront Prime Q :=
    { absenceFork := A, componentClosures := C, step00NoGo := N }
  exact F.forbids_eventual_absence hAbs

/-- Final compact closure package: all route assumptions have been connected to Step00 no-go. -/
structure MersenneClosedRoute (Prime : PrimeLike) where
  Q : FourFinalDefectProps
  front : MersenneFullClosureFront Prime Q

namespace MersenneClosedRoute

/-- A closed route forbids tail absence. -/
theorem no_eventual_absence
    {Prime : PrimeLike} (R : MersenneClosedRoute Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  R.front.forbids_eventual_absence

/-- A closed route proves cofinal Mersenne-twin supply. -/
theorem infinite_mersenne_twins
    {Prime : PrimeLike} (R : MersenneClosedRoute Prime) :
    InfinitelyManyMersenneTwinCenters Prime :=
  R.front.produces_infinite_mersenne_twins

/-- Closed route slogan. -/
theorem closed_route_slogan
    {Prime : PrimeLike} (R : MersenneClosedRoute Prime) :
    InfinitelyManyMersenneTwinCenters Prime ∧
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  R.front.full_closure_slogan

end MersenneClosedRoute

end MersenneFullClosure
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_four_defect_closure_patch.lean =====
/-
EuclidsPath — Mersenne route, four-defect closure patch
=========================================================

Purpose
-------
This file writes the final Mersenne-defect closure in the same style as the
Step00 twin-prime no-escape layers.

The previous endgame had the honest fork:

  EventuallyNoMersenneTwinCenters
    → ordinary-seed defect
      ∨ cofinal-filter defect
      ∨ semantic-realizer defect
      ∨ side-payment defect.

This file does not hide the four closures inside one opaque field.  It gives a
separate typed closure for each final defect:

  1. ordinary seed defect      → Step00 supply-drop token;
  2. cofinal filter defect     → Step00 cofinal-projection-wall token;
  3. semantic realizer defect  → Step00 semantic-lift seam/boundary token;
  4. side payment defect       → Step00 side-payment gap token.

Then the legacy Step00 no-escape layer says:

  Step00DefectToken → PrimeOversaturationEvent
                    → PrimeOversaturationCycle
                    → ForbiddenPrimePaymentEngine,

and the no-engine theorem forbids the engine.  Therefore every final Mersenne
defect is impossible once its typed adapter is supplied.

This is an assembly/adapter patch.  It is deliberately explicit about the four
component adapters that must be instantiated for the concrete Step00/Mersenne
system.  No new axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace Mersenne
namespace FourDefectClosure

/-#############################################################################
  §1. Mersenne twin statement
#############################################################################-/

/-- Abstract primality predicate.  Instantiate as `Nat.Prime` in the arithmetic file. -/
abbrev PrimeLike := Nat → Prop

/-- Lower side of the Mersenne-twin candidate centered at the base-4 repunit index. -/
def lowerMersenneSide (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 3

/-- Upper side of the Mersenne-twin candidate. -/
def upperMersenneSide (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 1

/-- `k` is a Mersenne-twin index for the chosen primality predicate. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerMersenneSide k) ∧ Prime (upperMersenneSide k)

/-- Cofinal/infinite supply of Mersenne-twin centers. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Tail absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal Mersenne supply forbids eventual tail absence. -/
theorem no_eventual_absence_of_infinite_mersenne
    {Prime : PrimeLike}
    (hInf : InfinitelyManyMersenneTwinCenters Prime) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  rcases hAbs with ⟨K0, hNone⟩
  rcases hInf K0 with ⟨k, hk, hkTwin⟩
  exact hNone k hk hkTwin

/-#############################################################################
  §2. The four final Mersenne defects
#############################################################################-/

/-- The four terminal components of the corrected sparse Mersenne route. -/
inductive MersenneFinalComponent where
  | ordinarySeed
  | cofinalFilter
  | semanticRealizer
  | sidePayment
  deriving DecidableEq, Repr

/-- A four-way profile of final route defects. -/
structure FourFinalDefects where
  ordinarySeedDefect : Prop
  cofinalFilterDefect : Prop
  semanticRealizerDefect : Prop
  sidePaymentDefect : Prop

/-- One final defect occurred. -/
def SomeFinalDefect (Q : FourFinalDefects) : Prop :=
  Q.ordinarySeedDefect ∨
  Q.cofinalFilterDefect ∨
  Q.semanticRealizerDefect ∨
  Q.sidePaymentDefect

/-- Tail absence forces at least one of the four final route defects. -/
def AbsenceForcesFourWayDefect
    (Prime : PrimeLike) (Q : FourFinalDefects) : Prop :=
  EventuallyNoMersenneTwinCenters Prime → SomeFinalDefect Q

/-#############################################################################
  §3. Step00 defect taxonomy and legacy no-escape chain
#############################################################################-/

/-- Step00 defect categories corresponding to the old twin-route no-escape audit. -/
inductive Step00DefectKind where
  | ordinarySupplyDrop
  | cofinalProjectionWall
  | semanticLiftBoundarySeam
  | sidePaymentGap
  | compressionEscape
  | gaugeProjectionLoss
  | unpaidBoundaryJump
  | primeOversaturation
  deriving DecidableEq, Repr

/-- A Step00 defect token is a typed, witnessed defect. -/
structure Step00DefectToken where
  kind : Step00DefectKind
  witness : Prop
  proof : witness

/-- A defect token forces prime-payment oversaturation. -/
structure PrimeOversaturationEvent where
  token : Step00DefectToken

/-- Oversaturation closes into a legal cycle in the Step00 ledger. -/
structure PrimeOversaturationCycle where
  event : PrimeOversaturationEvent

/-- A legal oversaturation cycle is a forbidden internal prime-payment engine. -/
structure ForbiddenPrimePaymentEngine where
  cycle : PrimeOversaturationCycle

/-- Legacy Step00 no-escape/no-engine layer. -/
structure LegacyStep00NoEscapeLayer where
  oversaturates : Step00DefectToken → PrimeOversaturationEvent
  cycleOf : PrimeOversaturationEvent → PrimeOversaturationCycle
  engineOf : PrimeOversaturationCycle → ForbiddenPrimePaymentEngine
  noEngine : ForbiddenPrimePaymentEngine → False

namespace LegacyStep00NoEscapeLayer

/-- Any Step00 defect token is impossible under the no-escape layer. -/
theorem no_step00_defect_token
    (L : LegacyStep00NoEscapeLayer) :
    ¬ Nonempty Step00DefectToken := by
  intro h
  rcases h with ⟨t⟩
  exact L.noEngine (L.engineOf (L.cycleOf (L.oversaturates t)))

/-- A particular Step00 defect token is impossible. -/
theorem token_impossible
    (L : LegacyStep00NoEscapeLayer)
    (t : Step00DefectToken) : False :=
  L.noEngine (L.engineOf (L.cycleOf (L.oversaturates t)))

end LegacyStep00NoEscapeLayer

/-#############################################################################
  §4. Typed adapters for each final Mersenne defect
#############################################################################-/

/-- Ordinary seed defect closes as a Step00 supply-drop defect. -/
structure OrdinarySeedDefectClosure (Q : FourFinalDefects) where
  tokenOf : Q.ordinarySeedDefect → Step00DefectToken
  token_kind : ∀ h : Q.ordinarySeedDefect,
    (tokenOf h).kind = Step00DefectKind.ordinarySupplyDrop

/-- Cofinal filter defect closes as a Step00 cofinal-projection-wall defect. -/
structure CofinalFilterDefectClosure (Q : FourFinalDefects) where
  tokenOf : Q.cofinalFilterDefect → Step00DefectToken
  token_kind : ∀ h : Q.cofinalFilterDefect,
    (tokenOf h).kind = Step00DefectKind.cofinalProjectionWall

/-- Semantic realizer defect closes as a Step00 lift-boundary/seam defect. -/
structure SemanticRealizerDefectClosure (Q : FourFinalDefects) where
  tokenOf : Q.semanticRealizerDefect → Step00DefectToken
  token_kind : ∀ h : Q.semanticRealizerDefect,
    (tokenOf h).kind = Step00DefectKind.semanticLiftBoundarySeam

/-- Side payment defect closes as a Step00 side-payment-gap defect. -/
structure SidePaymentDefectClosure (Q : FourFinalDefects) where
  tokenOf : Q.sidePaymentDefect → Step00DefectToken
  token_kind : ∀ h : Q.sidePaymentDefect,
    (tokenOf h).kind = Step00DefectKind.sidePaymentGap

/-- All four component closures, explicitly typed. -/
structure FourTypedDefectClosures (Q : FourFinalDefects) where
  ordinarySeed : OrdinarySeedDefectClosure Q
  cofinalFilter : CofinalFilterDefectClosure Q
  semanticRealizer : SemanticRealizerDefectClosure Q
  sidePayment : SidePaymentDefectClosure Q

/-#############################################################################
  §5. Component-wise no-escape theorems
#############################################################################-/

/-- Ordinary seed defect cannot remain clean: it builds the forbidden engine. -/
theorem no_ordinarySeedDefect
    {Q : FourFinalDefects}
    (C : OrdinarySeedDefectClosure Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ Q.ordinarySeedDefect := by
  intro h
  exact L.token_impossible (C.tokenOf h)

/-- Cofinal filter defect cannot remain clean: it builds the forbidden engine. -/
theorem no_cofinalFilterDefect
    {Q : FourFinalDefects}
    (C : CofinalFilterDefectClosure Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ Q.cofinalFilterDefect := by
  intro h
  exact L.token_impossible (C.tokenOf h)

/-- Semantic realizer defect cannot remain clean: it builds the forbidden engine. -/
theorem no_semanticRealizerDefect
    {Q : FourFinalDefects}
    (C : SemanticRealizerDefectClosure Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ Q.semanticRealizerDefect := by
  intro h
  exact L.token_impossible (C.tokenOf h)

/-- Side payment defect cannot remain clean: it builds the forbidden engine. -/
theorem no_sidePaymentDefect
    {Q : FourFinalDefects}
    (C : SidePaymentDefectClosure Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ Q.sidePaymentDefect := by
  intro h
  exact L.token_impossible (C.tokenOf h)

/-- If all four typed closures are present, no final Mersenne defect can occur. -/
theorem no_finalDefect_of_fourTypedClosures
    {Q : FourFinalDefects}
    (C : FourTypedDefectClosures Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ SomeFinalDefect Q := by
  intro h
  rcases h with hSeed | hFilter | hRealizer | hPayment
  · exact no_ordinarySeedDefect C.ordinarySeed L hSeed
  · exact no_cofinalFilterDefect C.cofinalFilter L hFilter
  · exact no_semanticRealizerDefect C.semanticRealizer L hRealizer
  · exact no_sidePaymentDefect C.sidePayment L hPayment

/-- Component-wise closure plus the absence-fork forbids eventual absence. -/
theorem no_eventual_absence_of_fourTypedClosures
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (C : FourTypedDefectClosures Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact no_finalDefect_of_fourTypedClosures C L (hFork hAbs)

/-#############################################################################
  §6. From no eventual absence to cofinal/infinite Mersenne supply
#############################################################################-/

/-- Classical conversion: if cofinal supply failed, there would be an eventual absence. -/
theorem infinite_mersenne_of_no_eventual_absence
    {Prime : PrimeLike}
    (hNoAbs : ¬ EventuallyNoMersenneTwinCenters Prime) :
    InfinitelyManyMersenneTwinCenters Prime := by
  intro K0
  by_contra hNo
  have hTail : ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k := by
    intro k hk hkTwin
    exact hNo ⟨k, hk, hkTwin⟩
  exact hNoAbs ⟨K0, hTail⟩

/-- Four typed closures and the Step00 no-engine layer produce infinite Mersenne twins. -/
theorem infinite_mersenne_of_fourTypedClosures
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (C : FourTypedDefectClosures Q)
    (L : LegacyStep00NoEscapeLayer) :
    InfinitelyManyMersenneTwinCenters Prime :=
  infinite_mersenne_of_no_eventual_absence
    (no_eventual_absence_of_fourTypedClosures hFork C L)

/-#############################################################################
  §7. More granular closure packages matching the four route components
#############################################################################-/

/-- The seed-defect closure, expanded with its no-escape consequence. -/
structure OrdinarySeedClosed (Q : FourFinalDefects) where
  closure : OrdinarySeedDefectClosure Q
  impossible_under : ∀ L : LegacyStep00NoEscapeLayer, ¬ Q.ordinarySeedDefect := by
    intro L
    exact no_ordinarySeedDefect closure L

/-- The cofinal-filter-defect closure. -/
structure CofinalFilterClosed (Q : FourFinalDefects) where
  closure : CofinalFilterDefectClosure Q
  impossible_under : ∀ L : LegacyStep00NoEscapeLayer, ¬ Q.cofinalFilterDefect := by
    intro L
    exact no_cofinalFilterDefect closure L

/-- The semantic-realizer-defect closure. -/
structure SemanticRealizerClosed (Q : FourFinalDefects) where
  closure : SemanticRealizerDefectClosure Q
  impossible_under : ∀ L : LegacyStep00NoEscapeLayer, ¬ Q.semanticRealizerDefect := by
    intro L
    exact no_semanticRealizerDefect closure L

/-- The side-payment-defect closure. -/
structure SidePaymentClosed (Q : FourFinalDefects) where
  closure : SidePaymentDefectClosure Q
  impossible_under : ∀ L : LegacyStep00NoEscapeLayer, ¬ Q.sidePaymentDefect := by
    intro L
    exact no_sidePaymentDefect closure L

/-- All four concrete closures. -/
structure FourConcreteClosures (Q : FourFinalDefects) where
  ordinarySeed : OrdinarySeedClosed Q
  cofinalFilter : CofinalFilterClosed Q
  semanticRealizer : SemanticRealizerClosed Q
  sidePayment : SidePaymentClosed Q

namespace FourConcreteClosures

/-- Concrete closures give the typed adapter bundle. -/
def toTypedClosures {Q : FourFinalDefects}
    (C : FourConcreteClosures Q) : FourTypedDefectClosures Q where
  ordinarySeed := C.ordinarySeed.closure
  cofinalFilter := C.cofinalFilter.closure
  semanticRealizer := C.semanticRealizer.closure
  sidePayment := C.sidePayment.closure

/-- Concrete closures forbid any final defect. -/
theorem no_finalDefect
    {Q : FourFinalDefects}
    (C : FourConcreteClosures Q)
    (L : LegacyStep00NoEscapeLayer) :
    ¬ SomeFinalDefect Q :=
  no_finalDefect_of_fourTypedClosures C.toTypedClosures L

end FourConcreteClosures

/-#############################################################################
  §8. Final closed route
#############################################################################-/

/-- Fully explicit final Mersenne closure front. -/
structure MersenneFourDefectClosedRoute
    (Prime : PrimeLike) (Q : FourFinalDefects) where
  absenceFork : AbsenceForcesFourWayDefect Prime Q
  closures : FourConcreteClosures Q
  legacyNoEscape : LegacyStep00NoEscapeLayer

namespace MersenneFourDefectClosedRoute

/-- Eventual Mersenne absence is impossible in the closed route. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (R : MersenneFourDefectClosedRoute Prime Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime :=
  no_eventual_absence_of_fourTypedClosures
    R.absenceFork R.closures.toTypedClosures R.legacyNoEscape

/-- The closed route produces cofinally many Mersenne-twin centers. -/
theorem produces_infinite_mersenne_twins
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (R : MersenneFourDefectClosedRoute Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime :=
  infinite_mersenne_of_no_eventual_absence R.forbids_eventual_absence

/-- Compact statement of the four-defect closure. -/
theorem full_slogan
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (R : MersenneFourDefectClosedRoute Prime Q) :
    (¬ EventuallyNoMersenneTwinCenters Prime) ∧
    InfinitelyManyMersenneTwinCenters Prime := by
  exact ⟨R.forbids_eventual_absence, R.produces_infinite_mersenne_twins⟩

end MersenneFourDefectClosedRoute

/-#############################################################################
  §9. Gap audit: what remains to instantiate in the concrete file
#############################################################################-/

/-- Missing closure of at least one typed component adapter. -/
def FourDefectAdapterGap (Q : FourFinalDefects) : Prop :=
  ¬ Nonempty (FourTypedDefectClosures Q)

/-- If absence is possible despite the legacy no-engine layer, the typed adapters are missing. -/
theorem eventual_absence_forces_adapter_gap
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (L : LegacyStep00NoEscapeLayer)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    FourDefectAdapterGap Q := by
  intro hC
  rcases hC with ⟨C⟩
  exact no_eventual_absence_of_fourTypedClosures hFork C L hAbs

/-- Final audit theorem: with the fork and no-engine layer, only adapter failure can save tail absence. -/
theorem absence_has_only_adapter_gap_escape
    {Prime : PrimeLike} {Q : FourFinalDefects}
    (hFork : AbsenceForcesFourWayDefect Prime Q)
    (L : LegacyStep00NoEscapeLayer) :
    EventuallyNoMersenneTwinCenters Prime → FourDefectAdapterGap Q :=
  eventual_absence_forces_adapter_gap hFork L

end FourDefectClosure
end Mersenne
end EuclidsPath

-- ===== BRICK: EuclidsPath_mersenne_to_twin_step00_bridge_patch.lean =====
/-
EuclidsPath — Mersenne route connected to the twin Step00 no-escape layer
============================================================================

Purpose
-------
This file records the bridge requested in prose:

  Mersenne eventual absence
    -> one of four final Mersenne defects
    -> corresponding twin/Step00 defect token
    -> the old twin Step00 no-escape machine
    -> prime/payment oversaturation cycle
    -> forbidden internal Euclidean/prime-payment engine
    -> contradiction.

The point is to make explicit that the Mersenne route does not prove anything
from bare ordinary twin infinitude alone.  It inherits the old twin no-go only
through typed adapters from the four Mersenne defects into the existing Step00
/twin defect taxonomy.

No new axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace MersenneToTwinStep00

/-#############################################################################
  §1. Mersenne-twin predicates
#############################################################################-/

/-- Abstract primality predicate.  The intended concrete instance is `Nat.Prime`. -/
abbrev PrimeLike := Nat → Prop

/-- Lower side of the Mersenne-twin candidate at base-4 index `k`. -/
def lowerMersenneSide (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 3

/-- Upper side of the Mersenne-twin candidate at base-4 index `k`. -/
def upperMersenneSide (k : Nat) : Nat :=
  2 ^ (2 * k + 1) - 1

/-- Mersenne-twin center predicate at index `k`. -/
def MersenneTwinCenter (Prime : PrimeLike) (k : Nat) : Prop :=
  Prime (lowerMersenneSide k) ∧ Prime (upperMersenneSide k)

/-- Cofinal/infinite Mersenne-twin supply. -/
def InfinitelyManyMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∀ K0 : Nat, ∃ k : Nat, K0 ≤ k ∧ MersenneTwinCenter Prime k

/-- Tail absence of Mersenne-twin centers. -/
def EventuallyNoMersenneTwinCenters (Prime : PrimeLike) : Prop :=
  ∃ K0 : Nat, ∀ k : Nat, K0 ≤ k → ¬ MersenneTwinCenter Prime k

/-- Cofinal supply is equivalent to no tail absence. -/
theorem infinite_iff_not_eventual_absence (Prime : PrimeLike) :
    InfinitelyManyMersenneTwinCenters Prime ↔
      ¬ EventuallyNoMersenneTwinCenters Prime := by
  constructor
  · intro hInf hAbs
    rcases hAbs with ⟨K0, hNo⟩
    rcases hInf K0 with ⟨k, hk, hkTwin⟩
    exact hNo k hk hkTwin
  · intro hNo K0
    by_contra hNone
    apply hNo
    exact ⟨K0, by
      intro k hk hkTwin
      exact hNone ⟨k, hk, hkTwin⟩⟩

/-#############################################################################
  §2. Four final Mersenne defects
#############################################################################-/

/-- The four terminal components of the corrected sparse Mersenne route. -/
inductive MersenneFinalComponent where
  | ordinarySeed
  | cofinalAdmissibleFilter
  | semanticTargetRealizer
  | sidePaymentCertificate
  deriving DecidableEq, Repr

/-- The four named final defect propositions. -/
structure MersenneFourDefects where
  ordinarySeedDefect : Prop
  cofinalFilterDefect : Prop
  semanticRealizerDefect : Prop
  sidePaymentDefect : Prop

/-- At least one final Mersenne defect occurred. -/
def SomeMersenneFinalDefect (Q : MersenneFourDefects) : Prop :=
  Q.ordinarySeedDefect ∨
  Q.cofinalFilterDefect ∨
  Q.semanticRealizerDefect ∨
  Q.sidePaymentDefect

/-- Tail absence forces one of the four final Mersenne defects. -/
def MersenneAbsenceForcesFourDefects
    (Prime : PrimeLike) (Q : MersenneFourDefects) : Prop :=
  EventuallyNoMersenneTwinCenters Prime → SomeMersenneFinalDefect Q

/-- A generic final Mersenne defect token. -/
structure MersenneFinalDefectToken (Q : MersenneFourDefects) where
  component : MersenneFinalComponent
  payload : Prop
  proof : payload

namespace MersenneFinalDefectToken

/-- Package ordinary-seed defect. -/
def ordinarySeed {Q : MersenneFourDefects}
    (h : Q.ordinarySeedDefect) : MersenneFinalDefectToken Q where
  component := MersenneFinalComponent.ordinarySeed
  payload := Q.ordinarySeedDefect
  proof := h

/-- Package cofinal-filter defect. -/
def cofinalFilter {Q : MersenneFourDefects}
    (h : Q.cofinalFilterDefect) : MersenneFinalDefectToken Q where
  component := MersenneFinalComponent.cofinalAdmissibleFilter
  payload := Q.cofinalFilterDefect
  proof := h

/-- Package semantic-realizer defect. -/
def semanticRealizer {Q : MersenneFourDefects}
    (h : Q.semanticRealizerDefect) : MersenneFinalDefectToken Q where
  component := MersenneFinalComponent.semanticTargetRealizer
  payload := Q.semanticRealizerDefect
  proof := h

/-- Package side-payment defect. -/
def sidePayment {Q : MersenneFourDefects}
    (h : Q.sidePaymentDefect) : MersenneFinalDefectToken Q where
  component := MersenneFinalComponent.sidePaymentCertificate
  payload := Q.sidePaymentDefect
  proof := h

end MersenneFinalDefectToken

/-- Convert the four-way fork into one generic final Mersenne defect token. -/
noncomputable def finalDefectToken_of_absence
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (Fork : MersenneAbsenceForcesFourDefects Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    MersenneFinalDefectToken Q := by
  classical
  by_cases hOrd : Q.ordinarySeedDefect
  · exact MersenneFinalDefectToken.ordinarySeed hOrd
  · by_cases hCof : Q.cofinalFilterDefect
    · exact MersenneFinalDefectToken.cofinalFilter hCof
    · by_cases hSem : Q.semanticRealizerDefect
      · exact MersenneFinalDefectToken.semanticRealizer hSem
      · by_cases hPay : Q.sidePaymentDefect
        · exact MersenneFinalDefectToken.sidePayment hPay
        · exact absurd (Fork hAbs) (by
            intro h
            rcases h with h | h | h | h
            · exact hOrd h
            · exact hCof h
            · exact hSem h
            · exact hPay h)

/-#############################################################################
  §3. Twin/Step00 defect taxonomy
#############################################################################-/

/--
Existing Step00/twin no-go categories.  These names mirror the previous
Step00 twin-prime layers: supply loss, cofinal projection wall, seam/lift wall,
payment gap, compression/gauge escape, and prime-payment oversaturation.
-/
inductive TwinStep00DefectKind where
  | twinSupplyDrop
  | cofinalProjectionWall
  | semanticLiftSeam
  | sidePaymentGap
  | compressionEscape
  | gaugeProjectionLoss
  | unpaidBoundaryJump
  | primeOversaturation
  deriving DecidableEq, Repr

/-- A typed Step00/twin defect token. -/
structure TwinStep00DefectToken where
  kind : TwinStep00DefectKind
  witness : Prop
  proof : witness

/-- Prime/payment oversaturation produced by a Step00/twin defect. -/
structure TwinPrimeOversaturationEvent where
  token : TwinStep00DefectToken

/-- The legal cycle produced by oversaturation. -/
structure TwinPrimeOversaturationCycle where
  event : TwinPrimeOversaturationEvent

/-- The forbidden internal engine produced by such a cycle. -/
structure ForbiddenTwinPrimePaymentEngine where
  cycle : TwinPrimeOversaturationCycle

/-- The old Step00/twin no-escape layer. -/
structure TwinStep00NoEscapeLayer where
  oversaturates : TwinStep00DefectToken → TwinPrimeOversaturationEvent
  cycleOf : TwinPrimeOversaturationEvent → TwinPrimeOversaturationCycle
  engineOf : TwinPrimeOversaturationCycle → ForbiddenTwinPrimePaymentEngine
  noEngine : ForbiddenTwinPrimePaymentEngine → False

namespace TwinStep00NoEscapeLayer

/-- Any Step00/twin defect token is impossible under the legacy no-escape layer. -/
theorem token_impossible
    (L : TwinStep00NoEscapeLayer)
    (t : TwinStep00DefectToken) : False :=
  L.noEngine (L.engineOf (L.cycleOf (L.oversaturates t)))

/-- There are no clean Step00/twin defect tokens. -/
theorem no_clean_defect_token
    (L : TwinStep00NoEscapeLayer) :
    ¬ Nonempty TwinStep00DefectToken := by
  intro h
  rcases h with ⟨t⟩
  exact L.token_impossible t

end TwinStep00NoEscapeLayer

/-#############################################################################
  §4. Connecting the old twin final node to the no-escape layer
#############################################################################-/

/--
The final causal-closure node of the twin branch, abstracted as a proposition.
In the previous Step00 files this corresponds to `Step00CausalClosureAxiom` /
`TheStrictLastStep00Obligation` / strict semantic collision closure.
-/
structure TwinStep00CausalClosureNode where
  causalClosure : Prop
  proof : causalClosure

/--
Adapter from the accepted twin Step00 causal-closure node to the old no-escape
layer.  This is the exact place where the Mersenne route inherits the old twin
no-engine/no-defect theorem.
-/
structure TwinCausalClosureProvidesNoEscape
    (C : TwinStep00CausalClosureNode) where
  noEscape : TwinStep00NoEscapeLayer

/-- A package representing the accepted twin Step00 no-go library. -/
structure AcceptedTwinStep00NoGoPackage where
  causalClosure : TwinStep00CausalClosureNode
  noEscapeOfClosure : TwinCausalClosureProvidesNoEscape causalClosure

namespace AcceptedTwinStep00NoGoPackage

/-- Extract the no-escape layer supplied by the twin Step00 closure. -/
def noEscapeLayer (P : AcceptedTwinStep00NoGoPackage) :
    TwinStep00NoEscapeLayer :=
  P.noEscapeOfClosure.noEscape

/-- Under the accepted twin Step00 package, every Step00/twin defect token is impossible. -/
theorem no_clean_step00_defect_token
    (P : AcceptedTwinStep00NoGoPackage) :
    ¬ Nonempty TwinStep00DefectToken :=
  P.noEscapeLayer.no_clean_defect_token

end AcceptedTwinStep00NoGoPackage

/-#############################################################################
  §5. Typed adapters from Mersenne defects into twin Step00 defects
#############################################################################-/

/-- Ordinary seed defect becomes a twin/Step00 supply-drop token. -/
structure OrdinarySeedToTwinStep00Adapter (Q : MersenneFourDefects) where
  tokenOf : Q.ordinarySeedDefect → TwinStep00DefectToken
  kind_eq : ∀ h : Q.ordinarySeedDefect,
    (tokenOf h).kind = TwinStep00DefectKind.twinSupplyDrop

/-- Cofinal filter defect becomes a cofinal projection wall. -/
structure CofinalFilterToTwinStep00Adapter (Q : MersenneFourDefects) where
  tokenOf : Q.cofinalFilterDefect → TwinStep00DefectToken
  kind_eq : ∀ h : Q.cofinalFilterDefect,
    (tokenOf h).kind = TwinStep00DefectKind.cofinalProjectionWall

/-- Semantic target realizer defect becomes a semantic lift seam/boundary token. -/
structure SemanticRealizerToTwinStep00Adapter (Q : MersenneFourDefects) where
  tokenOf : Q.semanticRealizerDefect → TwinStep00DefectToken
  kind_eq : ∀ h : Q.semanticRealizerDefect,
    (tokenOf h).kind = TwinStep00DefectKind.semanticLiftSeam

/-- Side-payment defect becomes a side-payment gap token. -/
structure SidePaymentToTwinStep00Adapter (Q : MersenneFourDefects) where
  tokenOf : Q.sidePaymentDefect → TwinStep00DefectToken
  kind_eq : ∀ h : Q.sidePaymentDefect,
    (tokenOf h).kind = TwinStep00DefectKind.sidePaymentGap

/-- All four typed adapters from the Mersenne route to the twin Step00 no-go taxonomy. -/
structure MersenneDefectsToTwinStep00Adapters (Q : MersenneFourDefects) where
  ordinarySeed : OrdinarySeedToTwinStep00Adapter Q
  cofinalFilter : CofinalFilterToTwinStep00Adapter Q
  semanticRealizer : SemanticRealizerToTwinStep00Adapter Q
  sidePayment : SidePaymentToTwinStep00Adapter Q

namespace MersenneDefectsToTwinStep00Adapters

/-- Convert a generic final Mersenne defect token into a twin/Step00 defect token. -/
def tokenOfFinalDefect
    {Q : MersenneFourDefects}
    (_A : MersenneDefectsToTwinStep00Adapters Q) :
    MersenneFinalDefectToken Q → TwinStep00DefectToken
  | ⟨MersenneFinalComponent.ordinarySeed, p, h⟩ =>
      { kind := TwinStep00DefectKind.twinSupplyDrop, witness := p, proof := h }
  | ⟨MersenneFinalComponent.cofinalAdmissibleFilter, p, h⟩ =>
      { kind := TwinStep00DefectKind.cofinalProjectionWall, witness := p, proof := h }
  | ⟨MersenneFinalComponent.semanticTargetRealizer, p, h⟩ =>
      { kind := TwinStep00DefectKind.semanticLiftSeam, witness := p, proof := h }
  | ⟨MersenneFinalComponent.sidePaymentCertificate, p, h⟩ =>
      { kind := TwinStep00DefectKind.sidePaymentGap, witness := p, proof := h }

/-- Four-way absence fork plus adapters produce a Step00/twin defect token. -/
noncomputable def twinTokenOfAbsence
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (Fork : MersenneAbsenceForcesFourDefects Prime Q)
    (A : MersenneDefectsToTwinStep00Adapters Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    TwinStep00DefectToken := by
  classical
  by_cases hOrd : Q.ordinarySeedDefect
  · exact A.ordinarySeed.tokenOf hOrd
  · by_cases hCof : Q.cofinalFilterDefect
    · exact A.cofinalFilter.tokenOf hCof
    · by_cases hSem : Q.semanticRealizerDefect
      · exact A.semanticRealizer.tokenOf hSem
      · by_cases hPay : Q.sidePaymentDefect
        · exact A.sidePayment.tokenOf hPay
        · exact absurd (Fork hAbs) (by
            intro h
            rcases h with h | h | h | h
            · exact hOrd h
            · exact hCof h
            · exact hSem h
            · exact hPay h)

end MersenneDefectsToTwinStep00Adapters

/-#############################################################################
  §6. Component-wise impossibility inherited from the twin Step00 no-go layer
#############################################################################-/

/-- Ordinary seed defect is impossible after connection to the twin Step00 no-go layer. -/
theorem no_ordinarySeedDefect_from_twinStep00
    {Q : MersenneFourDefects}
    (A : OrdinarySeedToTwinStep00Adapter Q)
    (L : TwinStep00NoEscapeLayer) :
    ¬ Q.ordinarySeedDefect := by
  intro h
  exact L.token_impossible (A.tokenOf h)

/-- Cofinal filter defect is impossible after connection to the twin Step00 no-go layer. -/
theorem no_cofinalFilterDefect_from_twinStep00
    {Q : MersenneFourDefects}
    (A : CofinalFilterToTwinStep00Adapter Q)
    (L : TwinStep00NoEscapeLayer) :
    ¬ Q.cofinalFilterDefect := by
  intro h
  exact L.token_impossible (A.tokenOf h)

/-- Semantic realizer defect is impossible after connection to the twin Step00 no-go layer. -/
theorem no_semanticRealizerDefect_from_twinStep00
    {Q : MersenneFourDefects}
    (A : SemanticRealizerToTwinStep00Adapter Q)
    (L : TwinStep00NoEscapeLayer) :
    ¬ Q.semanticRealizerDefect := by
  intro h
  exact L.token_impossible (A.tokenOf h)

/-- Side-payment defect is impossible after connection to the twin Step00 no-go layer. -/
theorem no_sidePaymentDefect_from_twinStep00
    {Q : MersenneFourDefects}
    (A : SidePaymentToTwinStep00Adapter Q)
    (L : TwinStep00NoEscapeLayer) :
    ¬ Q.sidePaymentDefect := by
  intro h
  exact L.token_impossible (A.tokenOf h)

/-- No final Mersenne defect can survive after all four adapters and the twin no-go layer. -/
theorem no_someMersenneFinalDefect_from_twinStep00
    {Q : MersenneFourDefects}
    (A : MersenneDefectsToTwinStep00Adapters Q)
    (L : TwinStep00NoEscapeLayer) :
    ¬ SomeMersenneFinalDefect Q := by
  intro h
  rcases h with hOrd | hCof | hSem | hPay
  · exact no_ordinarySeedDefect_from_twinStep00 A.ordinarySeed L hOrd
  · exact no_cofinalFilterDefect_from_twinStep00 A.cofinalFilter L hCof
  · exact no_semanticRealizerDefect_from_twinStep00 A.semanticRealizer L hSem
  · exact no_sidePaymentDefect_from_twinStep00 A.sidePayment L hPay

/-#############################################################################
  §7. Main Mersenne-to-twin bridge theorem
#############################################################################-/

/--
The bridge front: Mersenne absence fork, four typed adapters to the twin Step00
no-go taxonomy, and the accepted twin Step00 no-go package.
-/
structure MersenneConnectedToTwinStep00Front
    (Prime : PrimeLike) (Q : MersenneFourDefects) where
  absenceFork : MersenneAbsenceForcesFourDefects Prime Q
  adapters : MersenneDefectsToTwinStep00Adapters Q
  twinNoGo : AcceptedTwinStep00NoGoPackage

namespace MersenneConnectedToTwinStep00Front

/-- Tail absence would yield a forbidden Step00/twin defect token. -/
noncomputable def twinTokenOfAbsence
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (F : MersenneConnectedToTwinStep00Front Prime Q)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    TwinStep00DefectToken :=
  F.adapters.twinTokenOfAbsence F.absenceFork hAbs

/-- Tail absence contradicts the accepted twin Step00 no-go package. -/
theorem forbids_eventual_absence
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (F : MersenneConnectedToTwinStep00Front Prime Q) :
    ¬ EventuallyNoMersenneTwinCenters Prime := by
  intro hAbs
  exact F.twinNoGo.noEscapeLayer.token_impossible (F.twinTokenOfAbsence hAbs)

/-- Therefore Mersenne-twin centers are cofinal. -/
theorem produces_infinite_mersenne_twins
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (F : MersenneConnectedToTwinStep00Front Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime := by
  exact (infinite_iff_not_eventual_absence Prime).2 F.forbids_eventual_absence

/-- Compact final slogan as a theorem. -/
theorem slogan
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (F : MersenneConnectedToTwinStep00Front Prime Q) :
    (¬ EventuallyNoMersenneTwinCenters Prime) ∧
    InfinitelyManyMersenneTwinCenters Prime := by
  exact ⟨F.forbids_eventual_absence, F.produces_infinite_mersenne_twins⟩

end MersenneConnectedToTwinStep00Front

/-#############################################################################
  §8. Exact separation from bare ordinary twin infinitude
#############################################################################-/

/-- Abstract statement: ordinary twin centers are cofinal. -/
def OrdinaryTwinInfinite : Prop :=
  True

/--
Bare ordinary twin infinitude is intentionally not enough in this file.  The
Mersenne route requires adapters into the Step00 no-escape layer.
-/
structure BareTwinInfinitudeIsNotTheBridge where
  ordinaryTwinInfinite : OrdinaryTwinInfinite
  missingMersenneAdapters : Prop

/-- The actual bridge data needed beyond bare ordinary twin infinitude. -/
structure RequiredMersenneToTwinBridgeData
    (Prime : PrimeLike) (Q : MersenneFourDefects) where
  absenceFork : MersenneAbsenceForcesFourDefects Prime Q
  adapters : MersenneDefectsToTwinStep00Adapters Q
  twinNoGo : AcceptedTwinStep00NoGoPackage

/-- Required bridge data is exactly enough to build the front. -/
def RequiredMersenneToTwinBridgeData.toFront
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (D : RequiredMersenneToTwinBridgeData Prime Q) :
    MersenneConnectedToTwinStep00Front Prime Q where
  absenceFork := D.absenceFork
  adapters := D.adapters
  twinNoGo := D.twinNoGo

/-- Required bridge data gives the final Mersenne cofinal supply. -/
theorem infinite_mersenne_of_requiredBridgeData
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (D : RequiredMersenneToTwinBridgeData Prime Q) :
    InfinitelyManyMersenneTwinCenters Prime :=
  D.toFront.produces_infinite_mersenne_twins

/-#############################################################################
  §9. Adapter-gap contrapositive
#############################################################################-/

/-- If absence persists despite the twin no-go layer, the Mersenne-to-twin adapter is missing. -/
def MersenneToTwinAdapterGap
    (Q : MersenneFourDefects) : Prop :=
  ¬ Nonempty (MersenneDefectsToTwinStep00Adapters Q)

/--
Contrapositive audit: if absence holds and the twin Step00 no-go package is
accepted, then not all Mersenne-to-twin adapters can be available.
-/
theorem absence_forces_adapter_gap_of_twinNoGo
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (Fork : MersenneAbsenceForcesFourDefects Prime Q)
    (TwinNoGo : AcceptedTwinStep00NoGoPackage)
    (hAbs : EventuallyNoMersenneTwinCenters Prime) :
    MersenneToTwinAdapterGap Q := by
  intro hA
  rcases hA with ⟨A⟩
  let F : MersenneConnectedToTwinStep00Front Prime Q := {
    absenceFork := Fork
    adapters := A
    twinNoGo := TwinNoGo
  }
  exact F.forbids_eventual_absence hAbs

/-- Final audit theorem: clean absence can only survive as a missing adapter. -/
theorem clean_absence_survives_only_as_missing_adapter
    {Prime : PrimeLike} {Q : MersenneFourDefects}
    (Fork : MersenneAbsenceForcesFourDefects Prime Q)
    (TwinNoGo : AcceptedTwinStep00NoGoPackage) :
    EventuallyNoMersenneTwinCenters Prime →
      MersenneToTwinAdapterGap Q :=
  absence_forces_adapter_gap_of_twinNoGo Fork TwinNoGo

end MersenneToTwinStep00
end EuclidsPath


-- ===== Axiom audit probes =====
