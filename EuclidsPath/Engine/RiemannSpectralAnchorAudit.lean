/-
  RiemannSpectralAnchorAudit — абстрактная формализация вскрытого коллапса
  arithmetic-two-transport маршрута + ИСПРАВЛЕННОЕ следующее обязательство
  (кирпичи: Riemann_arithmetic_law_origin_anchor_audit +
  Riemann_spectral_anchor_data_nonvacuity). Проза: prose/30.

  Слой 1 (origin-anchor audit): формализует мой аудит — FreeLawCollapse
  (закон ⟺ Z-независимый атом), front_pair_iff_no_zero для ЛЮБОЙ law-family,
  ZeroSeparating, «свободный закон = внешняя 0→1 поставка, не мост».
  Слой 2 (data-nonvacuity) — ТОНЬШЕ: Prop-уровневая невакуумность —
  НЕПРАВИЛЬНЫЙ критерий (доказано: мост ⟹ коллапс закона в True —
  propLevel_nonvacuity_incompatible_with_bridge); аудит обязан жить на
  уровне ДАННЫХ: DataAnchoredLaw (Admissible + Anchor), экстрактор атомов,
  SpectralInvariantAnchor (respects: инвариант атома = инвариант нуля) —
  NonVacuousDataAnchor запрещает free-origin поставку и константные
  экстракторы. Исправленный фронт: SpectralAnchorStrictFront.

  СТЫКОВКА: concrete_freeLawCollapse — моя law_iff_admissibleAtom и есть
  FreeLawCollapse конкретного маршрута ⟹ конкретный закон не разделяет нули;
  concreteDataLaw — заготовка data-закона (Atom := ArithmeticTransportAtom,
  Anchor — будущий спектральный вход).
  Фиксы кирпичей: ASCII forall/exists/not/<-> → Unicode; Prop→Type
  элиминация в constantExtractor → .choose (noncomputable); dot-call.
-/
import Mathlib
import EuclidsPath.Engine.RiemannArithmeticTwoTransport

set_option autoImplicit false

namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace OriginAnchorAudit

/-!
## 1. Abstract law/zero interface
-/

variable {OffCriticalZero : Type}

/-- A law family indexed by off-critical zeros. -/
abbrev LawFamily (OffCriticalZero : Type) := OffCriticalZero -> Prop

/-- The route bridge: every off-critical zero carries a law. -/
def Bridge (Law : LawFamily OffCriticalZero) : Prop :=
  ∀ Z : OffCriticalZero, Law Z

/-- The route impossibility: no off-critical zero can carry such a law. -/
def Impossible (Law : LawFamily OffCriticalZero) : Prop :=
  ∀ Z : OffCriticalZero, ¬ (Law Z)

/--
A `Z`-free collapse: the law at every zero is equivalent to one fixed,
zero-independent arithmetic atom question `AtomExists`.
-/
def FreeLawCollapse (Law : LawFamily OffCriticalZero) (AtomExists : Prop) : Prop :=
  ∀ Z : OffCriticalZero, Law Z ↔ AtomExists

/-- A bridge follows from the free atom question under a free collapse. -/
theorem bridge_of_atomExists_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists)
    (hAtom : AtomExists) :
    Bridge Law := by
  intro Z
  exact (hFree Z).2 hAtom

/-- If an off-critical zero ∃, a bridge recovers the free atom question. -/
theorem atomExists_of_bridge_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists)
    (hZ : Nonempty OffCriticalZero)
    (hBridge : Bridge Law) :
    AtomExists := by
  rcases hZ with ⟨Z⟩
  exact (hFree Z).1 (hBridge Z)

/-- With at least one off-critical zero, a free bridge is exactly the atom question. -/
theorem bridge_iff_atomExists_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists)
    (hZ : Nonempty OffCriticalZero) :
    Bridge Law ↔ AtomExists := by
  constructor
  · exact atomExists_of_bridge_under_freeCollapse hFree hZ
  · exact bridge_of_atomExists_under_freeCollapse hFree

/-- If the free atom question is false, impossibility follows under a free collapse. -/
theorem impossible_of_not_atomExists_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists)
    (hAtom : ¬ AtomExists) :
    Impossible Law := by
  intro Z hLaw
  exact hAtom ((hFree Z).1 hLaw)

/-- If an off-critical zero ∃, impossibility recovers failure of the free atom question. -/
theorem not_atomExists_of_impossible_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists)
    (hZ : Nonempty OffCriticalZero)
    (hImpossible : Impossible Law) :
    ¬ AtomExists := by
  intro hAtom
  rcases hZ with ⟨Z⟩
  exact hImpossible Z ((hFree Z).2 hAtom)

/-- With at least one zero, free impossibility is exactly negation of the atom question. -/
theorem impossible_iff_not_atomExists_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists)
    (hZ : Nonempty OffCriticalZero) :
    Impossible Law ↔ ¬ AtomExists := by
  constructor
  · exact not_atomExists_of_impossible_under_freeCollapse hFree hZ
  · exact impossible_of_not_atomExists_under_freeCollapse hFree

/-!
## 2. Bridge + impossibility is exactly no off-critical zero
-/

/--
For any law family whatsoever, bridge plus impossibility is equivalent to
nonexistence of off-critical zeros.

This is the precise machine meaning of the audit slogan:

    front_pair_iff_no_zero.
-/
theorem front_pair_iff_no_zero
    (Law : LawFamily OffCriticalZero) :
    (Bridge Law ∧ Impossible Law) ↔ ¬ (Nonempty OffCriticalZero) := by
  constructor
  · intro hPair hZ
    rcases hPair with ⟨hBridge, hImpossible⟩
    rcases hZ with ⟨Z⟩
    exact hImpossible Z (hBridge Z)
  · intro hNoZero
    constructor
    · intro Z
      exact False.elim (hNoZero ⟨Z⟩)
    · intro Z
      exact False.elim (hNoZero ⟨Z⟩)

/-- If RH is identified with `no off-critical zero`, the front pair is RH-strength. -/
theorem front_pair_iff_RH
    {Law : LawFamily OffCriticalZero}
    {RiemannHypothesis : Prop}
    (hNoZero_iff_RH : (¬ (Nonempty OffCriticalZero)) ↔ RiemannHypothesis) :
    (Bridge Law ∧ Impossible Law) ↔ RiemannHypothesis := by
  exact Iff.trans (front_pair_iff_no_zero Law) hNoZero_iff_RH

/-!
## 3. Free collapse carries no zero-specific information
-/

/-- A law family separates two zeros if it holds at one and fails at another. -/
def ZeroSeparating (Law : LawFamily OffCriticalZero) : Prop :=
  ∃ Z₁ : OffCriticalZero, ∃ Z₂ : OffCriticalZero,
    (Law Z₁ ∧ ¬ (Law Z₂)) ∨ (Law Z₂ ∧ ¬ (Law Z₁))

/-- A free collapse cannot distinguish one off-critical zero from another. -/
theorem no_zero_separation_under_freeCollapse
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hFree : FreeLawCollapse Law AtomExists) :
    ¬ (ZeroSeparating Law) := by
  intro hSep
  rcases hSep with ⟨Z₁, Z₂, hCases⟩
  cases hCases with
  | inl h =>
      rcases h with ⟨hZ₁, hNotZ₂⟩
      have hAtom : AtomExists := (hFree Z₁).1 hZ₁
      exact hNotZ₂ ((hFree Z₂).2 hAtom)
  | inr h =>
      rcases h with ⟨hZ₂, hNotZ₁⟩
      have hAtom : AtomExists := (hFree Z₂).1 hZ₂
      exact hNotZ₁ ((hFree Z₁).2 hAtom)

/-- Any law family that separates zeros cannot be Z-free. -/
theorem zero_separation_forces_no_freeCollapse
    {Law : LawFamily OffCriticalZero}
    (hSep : ZeroSeparating Law) :
    ∀ AtomExists : Prop, ¬ (FreeLawCollapse Law AtomExists) := by
  intro AtomExists hFree
  exact no_zero_separation_under_freeCollapse hFree hSep

/--
A strong non-vacuity condition: the anchor is ¬ allowed to collapse to any
zero-independent proposition.

This is the abstract version of "the anchor is carrying spectral information".
-/
def NonVacuousSpectralAnchor (Law : LawFamily OffCriticalZero) : Prop :=
  ∀ AtomExists : Prop, ¬ (FreeLawCollapse Law AtomExists)

/-- A free collapse contradicts a non-vacuous spectral anchor. -/
theorem freeCollapse_contradicts_nonVacuousSpectralAnchor
    {Law : LawFamily OffCriticalZero}
    {AtomExists : Prop}
    (hAnchor : NonVacuousSpectralAnchor Law)
    (hFree : FreeLawCollapse Law AtomExists) :
    False := by
  exact hAnchor AtomExists hFree

/-- Zero separation is a sufficient, concrete way to prove non-vacuity. -/
theorem nonVacuousSpectralAnchor_of_zeroSeparation
    {Law : LawFamily OffCriticalZero}
    (hSep : ZeroSeparating Law) :
    NonVacuousSpectralAnchor Law := by
  exact zero_separation_forces_no_freeCollapse hSep

/-!
## 4. Origin/boundary interpretation of a free arithmetic law
-/

/--
An external origin supply for a zero-independent atom question.

This is the Riemann two-transport analogue of a `0 -> 1` boundary event: the
law starts because the atom is supplied externally, ¬ because the particular
zero `Z` produced it.
-/
structure ExternalOriginSupply (AtomExists : Prop) where
  supplied : AtomExists

/--
A free origin package: the law is equivalent at every zero to one external
atom question.
-/
structure FreeOriginArithmeticLaw
    (Law : LawFamily OffCriticalZero) where
  AtomExists : Prop
  free : FreeLawCollapse Law AtomExists

/-- External origin supply creates the law for every zero under a free collapse. -/
theorem law_from_externalOriginSupply
    {Law : LawFamily OffCriticalZero}
    (O : FreeOriginArithmeticLaw Law)
    (S : ExternalOriginSupply O.AtomExists) :
    Bridge Law := by
  intro Z
  exact (O.free Z).2 S.supplied

/-- Under free origin, the law is independent of the chosen off-critical zero. -/
theorem freeOrigin_law_equiv_between_zeros
    {Law : LawFamily OffCriticalZero}
    (O : FreeOriginArithmeticLaw Law)
    (Z₁ Z₂ : OffCriticalZero) :
    Law Z₁ ↔ Law Z₂ := by
  constructor
  · intro hZ₁
    exact (O.free Z₂).2 ((O.free Z₁).1 hZ₁)
  · intro hZ₂
    exact (O.free Z₁).2 ((O.free Z₂).1 hZ₂)

/-- Therefore a free origin law carries no zero-specific separation. -/
theorem freeOrigin_has_no_zeroSeparation
    {Law : LawFamily OffCriticalZero}
    (O : FreeOriginArithmeticLaw Law) :
    ¬ (ZeroSeparating Law) := by
  exact no_zero_separation_under_freeCollapse O.free

/-- A free origin law cannot satisfy the non-vacuous spectral anchor condition. -/
theorem freeOrigin_not_nonVacuousSpectralAnchor
    {Law : LawFamily OffCriticalZero}
    (O : FreeOriginArithmeticLaw Law) :
    ¬ (NonVacuousSpectralAnchor Law) := by
  intro hAnchor
  exact hAnchor O.AtomExists O.free

/--
The strict audit slogan:

A free arithmetic law is an origin/boundary supply, ¬ a zero-extracted bridge.
-/
theorem free_arithmetic_law_is_origin_boundary_slogan
    {Law : LawFamily OffCriticalZero}
    (O : FreeOriginArithmeticLaw Law) :
    (∀ Z₁ Z₂ : OffCriticalZero, Law Z₁ ↔ Law Z₂) ∧
    ¬ (ZeroSeparating Law) ∧
    ¬ (NonVacuousSpectralAnchor Law) := by
  exact ⟨
    freeOrigin_law_equiv_between_zeros O,
    freeOrigin_has_no_zeroSeparation O,
    freeOrigin_not_nonVacuousSpectralAnchor O
  ⟩

/-!
## 5. What remains to make the bridge genuinely spectral
-/

/--
The next genuine obligation: construct a law family that does ¬ collapse to a
single Z-independent atom question.
-/
structure SpectralAnchorObligation
    (Law : LawFamily OffCriticalZero) where
  nonvacuous : NonVacuousSpectralAnchor Law

/-- A spectral anchor obligation rules out the free-origin interpretation. -/
theorem spectralAnchorObligation_rules_out_originBoundary
    {Law : LawFamily OffCriticalZero}
    (H : SpectralAnchorObligation Law)
    (O : FreeOriginArithmeticLaw Law) :
    False := by
  exact freeOrigin_not_nonVacuousSpectralAnchor O H.nonvacuous

/--
Final status theorem for the arithmetic-law route.

If the law is free, it is an external origin supply.  If it is to become a real
RH bridge, the free collapse must be refuted by a non-vacuous spectral anchor.
-/
theorem arithmeticLaw_final_anchor_status
    {Law : LawFamily OffCriticalZero}
    (O : FreeOriginArithmeticLaw Law) :
    ¬ (SpectralAnchorObligation Law) := by
  intro H
  exact spectralAnchorObligation_rules_out_originBoundary H O

end OriginAnchorAudit
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace SpectralAnchorData

/-!
## 1. Prop-level non-vacuity is the wrong target
-/

variable {Zero : Type}

/-- A proposition-valued law family indexed by off-critical zeros. -/
abbrev PropLawFamily (Zero : Type) := Zero -> Prop

/-- The usual bridge shape: every zero satisfies the law. -/
def PropBridge (Law : PropLawFamily Zero) : Prop :=
  ∀ Z : Zero, Law Z

/-- A `Zero`-free collapse of a proposition-valued law. -/
def PropFreeCollapse (Law : PropLawFamily Zero) (P : Prop) : Prop :=
  ∀ Z : Zero, Law Z ↔ P

/-- Once a Prop-valued bridge is proved, the law collapses to `True`. -/
theorem propBridge_forces_trueCollapse
    {Law : PropLawFamily Zero}
    (hBridge : PropBridge Law) :
    PropFreeCollapse Law True := by
  intro Z
  constructor
  · intro _
    trivial
  · intro _
    exact hBridge Z

/--
Therefore a criterion saying "the Prop-valued law never collapses to a
zero-independent proposition" is incompatible with the intended bridge itself.
-/
theorem propLevel_nonvacuity_incompatible_with_bridge
    {Law : PropLawFamily Zero}
    (hNoFree : ∀ P : Prop, ¬ (PropFreeCollapse Law P))
    (hBridge : PropBridge Law) :
    False := by
  exact hNoFree True (propBridge_forces_trueCollapse hBridge)

/-!
## 2. Data-level anchored laws
-/

variable {Atom : Type}

/--
A data-level anchored law: an atom is admissible, and an atom may be anchored at
an off-critical zero.

The route should extract atoms from zeros.  The truth value
`∃ atom, Admissible atom and Anchor Z atom` is only the shadow.
-/
structure DataAnchoredLaw (Zero : Type) (Atom : Type) where
  Admissible : Atom -> Prop
  Anchor : Zero -> Atom -> Prop

namespace DataAnchoredLaw

/-- The Prop-valued shadow of a data-level anchored law. -/
def LawAt (D : DataAnchoredLaw Zero Atom) (Z : Zero) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ D.Anchor Z atom

/-- A bridge at the data level: every zero has at least one anchored atom. -/
def Bridge (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, LawAt D Z

/-- A concrete extractor chooses an atom for each zero. -/
def Extractor (D : DataAnchoredLaw Zero Atom) : Type :=
  ∀ Z : Zero, { atom : Atom // D.Admissible atom ∧ D.Anchor Z atom }

/-- An extractor gives the bridge. -/
theorem bridge_of_extractor
    {D : DataAnchoredLaw Zero Atom}
    (E : Extractor D) :
    Bridge D := by
  intro Z
  exact ⟨(E Z).val, (E Z).property⟩

/--
A free origin supply: one admissible atom anchors at every zero.  This is the
data-level analogue of an external `0 -> 1` supply: it does ¬ need to read the
specific zero.
-/
def FreeOriginSupply (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ ∀ Z : Zero, D.Anchor Z atom

/-- A free origin supply trivially gives a bridge. -/
theorem bridge_of_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    (hFree : FreeOriginSupply D) :
    Bridge D := by
  rcases hFree with ⟨atom, hAdm, hAll⟩
  intro Z
  exact ⟨atom, hAdm, hAll Z⟩

/--
A free origin supply also gives a constant extractor.  This is exactly the
vacuous/origin-boundary behaviour we want to distinguish from spectral
extraction.
-/
noncomputable def constantExtractor_of_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    (hFree : FreeOriginSupply D) :
    Extractor D :=
  fun Z => ⟨hFree.choose, hFree.choose_spec.1, hFree.choose_spec.2 Z⟩

/-- A concrete extractor is constant if it extracts the same atom for all zeros. -/
def ConstantExtractor
    (D : DataAnchoredLaw Zero Atom)
    (E : Extractor D) : Prop :=
  ∃ atom₀ : Atom, ∀ Z : Zero, (E Z).val = atom₀

/-- The constant extractor induced by a free origin supply is constant. -/
theorem constantExtractor_is_constant
    {D : DataAnchoredLaw Zero Atom}
    (hFree : FreeOriginSupply D) :
    ConstantExtractor D (constantExtractor_of_freeOriginSupply hFree) :=
  ⟨hFree.choose, fun _ => rfl⟩

end DataAnchoredLaw

/-!
## 3. Spectral invariant anchors
-/

/--
A spectral invariant certificate for a data-level anchor.

The key condition is `respects`: if an atom is anchored at a zero, the invariant
carried by the atom must equal the invariant of that zero.  Thus one fixed atom
cannot anchor at two zeros with different spectral invariants.
-/
structure SpectralInvariantAnchor
    (D : DataAnchoredLaw Zero Atom) where
  Inv : Type
  zeroInv : Zero -> Inv
  atomInv : Atom -> Inv
  respects : ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom -> atomInv atom = zeroInv Z

/--
If two zeros have different spectral invariants, no one atom can anchor at both.
-/
theorem no_single_atom_anchors_two_distinct_invariants
    {D : DataAnchoredLaw Zero Atom}
    (S : SpectralInvariantAnchor D)
    {Z₁ Z₂ : Zero}
    (hDiff : S.zeroInv Z₁ ≠ S.zeroInv Z₂) :
    ¬ (∃ atom : Atom, D.Anchor Z₁ atom ∧ D.Anchor Z₂ atom) := by
  intro h
  rcases h with ⟨atom, hA₁, hA₂⟩
  have h₁ : S.atomInv atom = S.zeroInv Z₁ := S.respects Z₁ atom hA₁
  have h₂ : S.atomInv atom = S.zeroInv Z₂ := S.respects Z₂ atom hA₂
  have hEq : S.zeroInv Z₁ = S.zeroInv Z₂ := by
    exact h₁.symm.trans h₂
  exact hDiff hEq

/--
A non-vacuous data anchor: some pair of zeros has different spectral invariant.
This is a Type-valued certificate, ¬ a Prop-valued law condition.
-/
structure NonVacuousDataAnchor
    (D : DataAnchoredLaw Zero Atom) where
  spectral : SpectralInvariantAnchor D
  separates : ∃ Z₁ : Zero, ∃ Z₂ : Zero,
    spectral.zeroInv Z₁ ≠ spectral.zeroInv Z₂

/--
A non-vacuous data anchor forbids a single free origin atom from anchoring at all
zeros.
-/
theorem nonVacuousDataAnchor_forbids_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    (N : NonVacuousDataAnchor D) :
    ¬ (DataAnchoredLaw.FreeOriginSupply D) := by
  intro hFree
  rcases hFree with ⟨atom, _hAdm, hAll⟩
  rcases N.separates with ⟨Z₁, Z₂, hDiff⟩
  exact no_single_atom_anchors_two_distinct_invariants
    N.spectral hDiff ⟨atom, hAll Z₁, hAll Z₂⟩

/--
Any extractor under a non-vacuous data anchor cannot be constant.
-/
theorem extractor_not_constant_under_nonVacuousDataAnchor
    {D : DataAnchoredLaw Zero Atom}
    (N : NonVacuousDataAnchor D)
    (E : DataAnchoredLaw.Extractor D) :
    ¬ (DataAnchoredLaw.ConstantExtractor D E) := by
  intro hConst
  rcases hConst with ⟨atom₀, hEq⟩
  rcases N.separates with ⟨Z₁, Z₂, hDiff⟩
  have hA₁ : D.Anchor Z₁ atom₀ := by
    have hProp := (E Z₁).property.2
    simpa [hEq Z₁] using hProp
  have hA₂ : D.Anchor Z₂ atom₀ := by
    have hProp := (E Z₂).property.2
    simpa [hEq Z₂] using hProp
  exact no_single_atom_anchors_two_distinct_invariants
    N.spectral hDiff ⟨atom₀, hA₁, hA₂⟩

/-!
## 4. Corrected next obligation
-/

/--
The corrected strict front for the arithmetic two-transport route.

It is ¬ enough to prove a Prop-valued bridge.  One must provide:

  * a data-level anchored law;
  * a zero-indexed extractor of atoms;
  * a spectral invariant showing the extracted atom cannot be a single free
    origin atom reused for all zeros.

In the actual RH route, `Zero` should be the type of off-critical zeros and
`Atom` should be the arithmetic six-tuple/layer-box atom.
-/
structure SpectralAnchorStrictFront (Zero : Type) (Atom : Type) where
  D : DataAnchoredLaw Zero Atom
  extractor : DataAnchoredLaw.Extractor D
  nonvacuous : NonVacuousDataAnchor D

namespace SpectralAnchorStrictFront

/-- The strict front still gives the ordinary Prop-valued bridge. -/
theorem gives_propBridge
    (F : SpectralAnchorStrictFront Zero Atom) :
    PropBridge (DataAnchoredLaw.LawAt F.D) := by
  exact DataAnchoredLaw.bridge_of_extractor F.extractor

/-- But it cannot be explained by a free origin supply. -/
theorem not_freeOriginSupply
    (F : SpectralAnchorStrictFront Zero Atom) :
    ¬ (DataAnchoredLaw.FreeOriginSupply F.D) := by
  exact nonVacuousDataAnchor_forbids_freeOriginSupply F.nonvacuous

/-- Nor can its extractor be a constant extractor. -/
theorem extractor_not_constant
    (F : SpectralAnchorStrictFront Zero Atom) :
    ¬ (DataAnchoredLaw.ConstantExtractor F.D F.extractor) := by
  exact extractor_not_constant_under_nonVacuousDataAnchor F.nonvacuous F.extractor

end SpectralAnchorStrictFront

/-!
## 5. Final audit slogan
-/

/--
The corrected message for the next RH brick.

A Prop-valued arithmetic law can always collapse to `True` once the bridge is
proved.  The real non-vacuity obligation is data-level: the atom extracted from
`Z` must carry a spectral invariant of `Z`, preventing a single origin atom from
serving all zeros.
-/
theorem spectralAnchorData_final_slogan :
    True := by
  trivial

end SpectralAnchorData
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/-! Стыковка audit-слоёв с конкретным маршрутом -/

namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport

/-- Конкретный free-collapse: моя law_iff_admissibleAtom — в точности
    FreeLawCollapse для конкретного семейства законов маршрута. -/
theorem concrete_freeLawCollapse {OffCriticalZero : Type} :
    OriginAnchorAudit.FreeLawCollapse
      (fun Z : OffCriticalZero =>
        Nonempty (ArithmeticTwoTransportLaw OffCriticalZero Z))
      AdmissibleAtomExists :=
  fun Z => law_iff_admissibleAtom Z

/-- Следствие: конкретный закон НЕ разделяет нули и НЕ является
    non-vacuous spectral anchor (audit-слой применён к маршруту). -/
theorem concrete_law_is_origin_boundary {OffCriticalZero : Type} :
    ¬ OriginAnchorAudit.ZeroSeparating
      (fun Z : OffCriticalZero =>
        Nonempty (ArithmeticTwoTransportLaw OffCriticalZero Z)) :=
  OriginAnchorAudit.no_zero_separation_under_freeCollapse
    concrete_freeLawCollapse

/-- Кандидат data-anchored закона для маршрута: Atom := ArithmeticTransportAtom,
    Admissible := Nonempty (ArithmeticAdmissible ·); Anchor — БУДУЩИЙ
    спектральный вход (здесь параметр). -/
def concreteDataLaw (OffCriticalZero : Type)
    (Anchor : OffCriticalZero → ArithmeticTransportAtom → Prop) :
    SpectralAnchorData.DataAnchoredLaw OffCriticalZero ArithmeticTransportAtom where
  Admissible := fun T => Nonempty (ArithmeticAdmissible T)
  Anchor := Anchor

end ArithmeticTwoTransport
end Riemann
end EuclidsPath
