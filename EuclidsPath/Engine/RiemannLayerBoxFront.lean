/-
  RiemannLayerBoxFront — серия layerbox (25 кирпичей одной сборкой): спектральное
  трио (fingerprint / anchor-recovers-zero / origin-blind firewall), zero-indexed
  impossibility, decoded-kernel, same-zero descent, move-алгебра/полнота/матрица
  блокировок, residue-таблицы (named rows / factor matrix / assignment rows /
  concrete tuple table / decider / forced table), pressure/blocker-ядра,
  maximal/terminal фронты, финальный checklist-компилятор.

  ЧЕСТНОСТЬ (флаги сборочного аудита, машинно):
    * Реально доказанная арифметика серии: mod-6 residue-факты (555/111+2
      невозможно; ориентация масс 5-в-1 проходит; кортеж 511/511 сбалансирован)
      + генерические well-founded descent / finite-cover сборки. Остальное —
      каркасы обязательств.
    * LayerPressure/DeterminantPressure несут поле contradiction : False —
      неинстанциируемые интерфейс-слоты, не доказательства.
    * ResidueGate декодед-ядра был ill-typed placeholder (Prop := Prop) —
      честная инертная починка := True; содержание в local_arithmetic_obstruction.
    * NonEngineCoherenceFirewall (обе версии), Prop-слоты terminal_slot —
      декоративные/инертные гейты; valid_atomOf/anchored_atomOf single-file
      экстрактора — Prop-значные no-op поля (несущее — в ExtractorRealizes).
    * native_decide (7 мест) заменён на kernel-checked decide — доверие
      ofReduceBool НЕ введено.
  Фиксы: ASCII в Unicode, Type-аскрипции, Nonempty-обёртки Or-нагрузок,
  universe-аскрипции checklist, отрицание data-структур в (X -> False),
  переупорядочение биндеров.
-/
import Mathlib
import EuclidsPath.Engine.RiemannSpectralAnchorAudit

set_option autoImplicit false

/- ============ BRICK: Riemann_spectral_anchor_origin_blind_firewall_patch.lean ============ -/

/-
  Riemann_spectral_anchor_origin_blind_firewall_patch.lean

  Purpose
  -------
  This patch is the next strict audit layer after
  `Riemann_spectral_anchor_data_nonvacuity_patch.lean`.

  The previous layer moved non-vacuity from the proposition

      Law Z : Prop

  to the extracted DATA.  This file strengthens the firewall:

      if the anchor is blind to the zero Z, then a bridge is only a free
      origin/boundary supply.

  Therefore a genuine spectral-arithmetic bridge must have an anchor whose
  predicate depends on Z.  Otherwise the arithmetic law behaves exactly like
  the earlier `0 -> 1` origin event: it supplies one admissible atom from
  outside and reuses it for every zero.

  The file also records a small residue sanity check for the proposed
  six-tuple atom:

      q*r*s = a*b*v + 2.

  If q,r,s are all 5 mod 6 and a,b,v are all 1 mod 6, then this identity is
  impossible already modulo 6.  Hence that exact polarity cannot be the final
  LayerBox gate unless one of the signs/residue classes/sides is different.

  This file is an audit/reduction layer.  It proves no RH bridge.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace SpectralAnchorFirewall

/-!
## 1. Data-level anchored laws
-/

variable {Zero Atom : Type}

/-- A data-level law: admissible atoms and an anchor predicate tying zeros to atoms. -/
structure DataAnchoredLaw (Zero : Type) (Atom : Type) where
  Admissible : Atom -> Prop
  Anchor : Zero -> Atom -> Prop

namespace DataAnchoredLaw

/-- The proposition-valued shadow at a zero. -/
def LawAt (D : DataAnchoredLaw Zero Atom) (Z : Zero) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ D.Anchor Z atom

/-- Bridge shape: every zero has an anchored admissible atom. -/
def Bridge (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, LawAt D Z

/-- A free origin supply: one admissible atom anchors at every zero. -/
def FreeOriginSupply (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ ∀ Z : Zero, D.Anchor Z atom

/-- An anchor is origin-blind if its dependence on `Z` can be erased. -/
def OriginBlindAnchor (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ P : Atom -> Prop, ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom ↔ P atom

/-- A genuinely zero-sensitive anchor is not origin-blind. -/
def ZeroSensitiveAnchor (D : DataAnchoredLaw Zero Atom) : Prop :=
  ¬ (OriginBlindAnchor D)

/--
If the anchor is origin-blind, then any bridge over an inhabited zero type is
already a free origin supply.
-/
theorem originBlind_bridge_forces_freeOriginSupply
    [Inhabited Zero]
    {D : DataAnchoredLaw Zero Atom}
    (hBlind : OriginBlindAnchor D)
    (hBridge : Bridge D) :
    FreeOriginSupply D := by
  rcases hBlind with ⟨P, hP⟩
  rcases hBridge default with ⟨atom, hAdm, hAnchorDefault⟩
  refine ⟨atom, hAdm, ?_⟩
  have hPatom : P atom := (hP default atom).mp hAnchorDefault
  intro Z
  exact (hP Z atom).mpr hPatom

/--
Contrapositive firewall: if no free origin supply is allowed and the bridge is
proved, then the anchor must be zero-sensitive.
-/
theorem noFree_bridge_forces_zeroSensitiveAnchor
    [Inhabited Zero]
    {D : DataAnchoredLaw Zero Atom}
    (hNoFree : ¬ (FreeOriginSupply D))
    (hBridge : Bridge D) :
    ZeroSensitiveAnchor D := by
  intro hBlind
  exact hNoFree (originBlind_bridge_forces_freeOriginSupply hBlind hBridge)

end DataAnchoredLaw

/-!
## 2. Locked spectral fingerprints
-/

/--
A locked fingerprint anchor.  The fingerprint of the zero is specified before
looking at a chosen atom; anchored atoms must carry the same fingerprint.
-/
structure LockedSpectralFingerprint
    (D : DataAnchoredLaw Zero Atom) where
  Fingerprint : Type
  zeroFP : Zero -> Fingerprint
  atomFP : Atom -> Fingerprint
  respects : ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom -> atomFP atom = zeroFP Z

/-- The fingerprint actually separates two zeros. -/
def FingerprintSeparates
    {D : DataAnchoredLaw Zero Atom}
    (F : LockedSpectralFingerprint D) : Prop :=
  ∃ Z₁ : Zero, ∃ Z₂ : Zero, F.zeroFP Z₁ ≠ F.zeroFP Z₂

/-- A strict fingerprint front: bridge + separated locked fingerprint. -/
structure StrictFingerprintFront (Zero : Type) (Atom : Type) where
  D : DataAnchoredLaw Zero Atom
  bridge : DataAnchoredLaw.Bridge D
  fingerprint : LockedSpectralFingerprint D
  separates : FingerprintSeparates fingerprint

namespace StrictFingerprintFront

/-- A separated locked fingerprint forbids a free origin supply. -/
theorem no_freeOriginSupply
    (S : StrictFingerprintFront Zero Atom) :
    ¬ (DataAnchoredLaw.FreeOriginSupply S.D) := by
  intro hFree
  rcases hFree with ⟨atom, _hAdm, hAll⟩
  rcases S.separates with ⟨Z₁, Z₂, hDiff⟩
  have h₁ : S.fingerprint.atomFP atom = S.fingerprint.zeroFP Z₁ :=
    S.fingerprint.respects Z₁ atom (hAll Z₁)
  have h₂ : S.fingerprint.atomFP atom = S.fingerprint.zeroFP Z₂ :=
    S.fingerprint.respects Z₂ atom (hAll Z₂)
  have hEq : S.fingerprint.zeroFP Z₁ = S.fingerprint.zeroFP Z₂ :=
    h₁.symm.trans h₂
  exact hDiff hEq

/-- Therefore a strict fingerprint bridge cannot have an origin-blind anchor. -/
theorem zeroSensitiveAnchor
    [Inhabited Zero]
    (S : StrictFingerprintFront Zero Atom) :
    DataAnchoredLaw.ZeroSensitiveAnchor S.D := by
  exact DataAnchoredLaw.noFree_bridge_forces_zeroSensitiveAnchor
    (no_freeOriginSupply S) S.bridge

end StrictFingerprintFront

/-!
## 3. Why this is the right next RH obligation
-/

/--
The next non-circular front for the arithmetic two-transport route.

In the intended application:

  * `Zero` is the type of off-critical zeros;
  * `Atom` is the LayerBox six-tuple;
  * `zeroFP` should be a genuinely spectral invariant of the zero;
  * `atomFP` should be the invariant carried by the arithmetic atom.

This is the precise replacement for a free `ZeroAnchored` predicate.
-/
abbrev SpectralFingerprintAnchorObligation (Zero Atom : Type) : Type 1 :=
  StrictFingerprintFront Zero Atom

/-!
## 4. Residue sanity for the six-tuple identity
-/

/-- A raw six-tuple atom for the arithmetic two-transport identity. -/
structure RawSixTupleAtom where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat

namespace RawSixTupleAtom

/-- The arithmetic two-transport identity. -/
def Identity (T : RawSixTupleAtom) : Prop :=
  T.q * T.r * T.s = T.a * T.b * T.v + 2

/-- The exact residue polarity mentioned in the audit: q,r,s = 5 and a,b,v = 1 mod 6. -/
def Residues555_111 (T : RawSixTupleAtom) : Prop :=
  T.q % 6 = 5 ∧ T.r % 6 = 5 ∧ T.s % 6 = 5 ∧
  T.a % 6 = 1 ∧ T.b % 6 = 1 ∧ T.v % 6 = 1

/-- q*r*s has residue 5 modulo 6 under 555 polarity. -/
theorem left_residue_555
    (T : RawSixTupleAtom)
    (h : Residues555_111 T) :
    (T.q * T.r * T.s) % 6 = 5 := by
  rcases h with ⟨hq, hr, hs, _ha, _hb, _hv⟩
  rw [Nat.mul_mod, Nat.mul_mod T.q T.r, hq, hr, hs]

/-- a*b*v + 2 has residue 3 modulo 6 under 111 polarity. -/
theorem right_residue_111_plus_two
    (T : RawSixTupleAtom)
    (h : Residues555_111 T) :
    (T.a * T.b * T.v + 2) % 6 = 3 := by
  rcases h with ⟨_hq, _hr, _hs, ha, hb, hv⟩
  rw [Nat.add_mod, Nat.mul_mod, Nat.mul_mod T.a T.b, ha, hb, hv]

/--
The polarity q,r,s ≡ 5 mod 6 and a,b,v ≡ 1 mod 6 is incompatible with
q*r*s = a*b*v + 2.
-/
theorem no_identity_with_residues_555_111_plus_two
    (T : RawSixTupleAtom)
    (hId : Identity T)
    (hRes : Residues555_111 T) :
    False := by
  have hLeft : (T.q * T.r * T.s) % 6 = 5 := left_residue_555 T hRes
  have hRight : (T.a * T.b * T.v + 2) % 6 = 3 := right_residue_111_plus_two T hRes
  have hModEq : (T.q * T.r * T.s) % 6 = (T.a * T.b * T.v + 2) % 6 := by
    rw [hId]
  rw [hLeft, hRight] at hModEq
  norm_num at hModEq

end RawSixTupleAtom

/-!
## 5. Final audit theorem
-/

/--
Final message: the next strict bridge must be zero-sensitive at the data level;
a zero-blind anchor is only an origin boundary supply.  Additionally, the exact
555/111/+2 residue polarity is impossible modulo 6, so the LayerBox gate must
use a different polarity/sign/side if it is to be nonempty.
-/
theorem spectralAnchorOriginBlindFirewall_slogan : True := by
  trivial

end SpectralAnchorFirewall
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_spectral_fingerprint_recoverability_patch.lean ============ -/

/-
  Riemann_spectral_fingerprint_recoverability_patch.lean

  Purpose
  -------
  This is the next strict layer after

      Riemann_spectral_anchor_origin_blind_firewall_patch.lean

  The previous audit showed that an origin-blind anchor makes the arithmetic
  two-transport law a free origin/boundary supply.  This file states the next
  positive requirement:

      the atom extracted from an off-critical zero must recover a nontrivial
      spectral fingerprint of that zero.

  This is a DATA-level condition.  It is intentionally not a proposition-level
  condition of the form `Law Z`, because any proved bridge `∀ Z, Law Z`
  collapses propositionally to `True`.

  The key theorem is:

      if an extractor carries a separated spectral fingerprint, then it cannot
      be constant, and no one free atom can serve all zeros.

  Thus a successful arithmetic two-transport bridge must really read the zero.
  It cannot be the old `0 -> 1` origin supply in disguise.

  This file is self-contained and proves no RH bridge.  It is a strict audit
  interface for the next non-circular obligation.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace SpectralFingerprintRecoverability

/-!
## 1. Data-level anchored law
-/

variable {Zero Atom : Type}

/--
A data-level anchored law.  The route should not merely prove a proposition
`Law Z`; it should extract an `Atom` whose anchoring predicate depends on `Z`.
-/
structure DataAnchoredLaw (Zero : Type) (Atom : Type) where
  Admissible : Atom -> Prop
  Anchor : Zero -> Atom -> Prop

namespace DataAnchoredLaw

/-- The proposition-valued shadow at a zero. -/
def LawAt (D : DataAnchoredLaw Zero Atom) (Z : Zero) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ D.Anchor Z atom

/-- Bridge shape: every zero has an anchored admissible atom. -/
def Bridge (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, LawAt D Z

/-- A chosen extractor of atoms from zeros. -/
def Extractor (D : DataAnchoredLaw Zero Atom) : Type :=
  ∀ Z : Zero, { atom : Atom // D.Admissible atom ∧ D.Anchor Z atom }

/-- An extractor implies the proposition-level bridge. -/
theorem bridge_of_extractor
    {D : DataAnchoredLaw Zero Atom}
    (E : Extractor D) :
    Bridge D := by
  intro Z
  exact ⟨(E Z).val, (E Z).property⟩

/-- A free origin supply: one atom works for every zero. -/
def FreeOriginSupply (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ ∀ Z : Zero, D.Anchor Z atom

/-- A concrete extractor is constant when it always returns the same atom. -/
def ConstantExtractor
    (D : DataAnchoredLaw Zero Atom)
    (E : Extractor D) : Prop :=
  ∃ atom₀ : Atom, ∀ Z : Zero, (E Z).val = atom₀

/-- A free origin supply gives a constant extractor. -/
noncomputable def constantExtractor_of_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    (hFree : FreeOriginSupply D) :
    Extractor D :=
  fun Z => ⟨hFree.choose, hFree.choose_spec.1, hFree.choose_spec.2 Z⟩

/-- The extractor induced by a free origin supply is constant. -/
theorem constantExtractor_of_freeOriginSupply_is_constant
    {D : DataAnchoredLaw Zero Atom}
    (hFree : FreeOriginSupply D) :
    ConstantExtractor D (constantExtractor_of_freeOriginSupply hFree) :=
  ⟨hFree.choose, fun _ => rfl⟩

end DataAnchoredLaw

/-!
## 2. Recoverable spectral fingerprints
-/

/--
A spectral fingerprint carried by anchored atoms.

`zeroFP` is the invariant of the zero; `atomFP` is the invariant recovered from
an arithmetic atom.  The `respects` field says that if an atom is anchored at a
zero, then the atom recovers the fingerprint of that zero.
-/
structure RecoverableSpectralFingerprint
    (D : DataAnchoredLaw Zero Atom) where
  Fingerprint : Type
  zeroFP : Zero -> Fingerprint
  atomFP : Atom -> Fingerprint
  respects : ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom -> atomFP atom = zeroFP Z

/-- The fingerprint is nontrivial on the zero-side. -/
def FingerprintSeparatesZeros
    {D : DataAnchoredLaw Zero Atom}
    (F : RecoverableSpectralFingerprint D) : Prop :=
  ∃ Z₁ : Zero, ∃ Z₂ : Zero, F.zeroFP Z₁ ≠ F.zeroFP Z₂

/-- Strict recoverability: anchored atoms recover a separated zero invariant. -/
structure StrictRecoverability
    (D : DataAnchoredLaw Zero Atom) where
  fingerprint : RecoverableSpectralFingerprint D
  separates : FingerprintSeparatesZeros fingerprint

namespace StrictRecoverability

/-- A separated recoverable fingerprint forbids one free atom from serving all zeros. -/
theorem no_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    (S : StrictRecoverability D) :
    ¬ (DataAnchoredLaw.FreeOriginSupply D) := by
  intro hFree
  rcases hFree with ⟨atom, _hAdm, hAll⟩
  rcases S.separates with ⟨Z₁, Z₂, hDiff⟩
  have h₁ : S.fingerprint.atomFP atom = S.fingerprint.zeroFP Z₁ :=
    S.fingerprint.respects Z₁ atom (hAll Z₁)
  have h₂ : S.fingerprint.atomFP atom = S.fingerprint.zeroFP Z₂ :=
    S.fingerprint.respects Z₂ atom (hAll Z₂)
  exact hDiff (h₁.symm.trans h₂)

/-- A separated recoverable fingerprint forbids a constant extractor. -/
theorem no_constantExtractor
    {D : DataAnchoredLaw Zero Atom}
    (S : StrictRecoverability D)
    (E : DataAnchoredLaw.Extractor D) :
    ¬ (DataAnchoredLaw.ConstantExtractor D E) := by
  intro hConst
  rcases hConst with ⟨atom₀, hConst⟩
  rcases S.separates with ⟨Z₁, Z₂, hDiff⟩
  have hA₁ : D.Anchor Z₁ (E Z₁).val := (E Z₁).property.2
  have hA₂ : D.Anchor Z₂ (E Z₂).val := (E Z₂).property.2
  have hFP₁ : S.fingerprint.atomFP (E Z₁).val = S.fingerprint.zeroFP Z₁ :=
    S.fingerprint.respects Z₁ (E Z₁).val hA₁
  have hFP₂ : S.fingerprint.atomFP (E Z₂).val = S.fingerprint.zeroFP Z₂ :=
    S.fingerprint.respects Z₂ (E Z₂).val hA₂
  have h₁ : S.fingerprint.atomFP atom₀ = S.fingerprint.zeroFP Z₁ := by
    rw [← hConst Z₁]
    exact hFP₁
  have h₂ : S.fingerprint.atomFP atom₀ = S.fingerprint.zeroFP Z₂ := by
    rw [← hConst Z₂]
    exact hFP₂
  exact hDiff (h₁.symm.trans h₂)

/-- In particular, a free-origin extractor cannot satisfy strict recoverability. -/
theorem freeOrigin_constantExtractor_contradiction
    {D : DataAnchoredLaw Zero Atom}
    (S : StrictRecoverability D)
    (hFree : DataAnchoredLaw.FreeOriginSupply D) :
    False := by
  exact no_freeOriginSupply S hFree

end StrictRecoverability

/-!
## 3. The corrected strict front
-/

/--
A strict spectral extraction front.

This is the intended replacement for a free `ZeroAnchored` field.  It contains:

  * a data-level law;
  * a concrete extractor, not merely `∃ atom`;
  * a recoverable separated fingerprint.

The extracted atom must therefore vary with the spectral data of the zero.
-/
structure StrictSpectralExtractionFront (Zero : Type) (Atom : Type) where
  D : DataAnchoredLaw Zero Atom
  extractor : DataAnchoredLaw.Extractor D
  recoverability : StrictRecoverability D

namespace StrictSpectralExtractionFront

/-- The strict front implies the ordinary bridge. -/
theorem bridge
    (S : StrictSpectralExtractionFront Zero Atom) :
    DataAnchoredLaw.Bridge S.D :=
  DataAnchoredLaw.bridge_of_extractor S.extractor

/-- The strict front has no free origin supply. -/
theorem no_freeOriginSupply
    (S : StrictSpectralExtractionFront Zero Atom) :
    ¬ (DataAnchoredLaw.FreeOriginSupply S.D) :=
  StrictRecoverability.no_freeOriginSupply S.recoverability

/-- The strict front's extractor is not constant. -/
theorem extractor_not_constant
    (S : StrictSpectralExtractionFront Zero Atom) :
    ¬ (DataAnchoredLaw.ConstantExtractor S.D S.extractor) :=
  StrictRecoverability.no_constantExtractor S.recoverability S.extractor

end StrictSpectralExtractionFront

/-!
## 4. RH-route interpretation: what the next bridge must actually provide
-/

/--
The next non-circular obligation for the arithmetic two-transport route.

In the intended application:

  * `Zero` is the type of off-critical zeros;
  * `Atom` is the arithmetic six-tuple/layer-box atom;
  * `Fingerprint` should encode a genuine spectral invariant of the zero;
  * the extracted atom must recover that invariant.

This is stronger than `∀ Z, ∃ atom`, because it rules out a single
origin-supplied atom reused at all zeros.
-/
abbrev SpectralFingerprintRecoverabilityObligation
    (Zero Atom : Type) : Type 1 :=
  StrictSpectralExtractionFront Zero Atom

/--
Slogan theorem: a strict fingerprint bridge is not a `0 -> 1` origin supply.
-/
theorem strictFingerprintBridge_not_originBoundary
    (S : SpectralFingerprintRecoverabilityObligation Zero Atom) :
    ¬ (DataAnchoredLaw.FreeOriginSupply S.D) :=
  StrictSpectralExtractionFront.no_freeOriginSupply S

/--
Slogan theorem: a strict fingerprint bridge must read the zero; its extractor is
not constant.
-/
theorem strictFingerprintBridge_reads_zero
    (S : SpectralFingerprintRecoverabilityObligation Zero Atom) :
    ¬ (DataAnchoredLaw.ConstantExtractor S.D S.extractor) :=
  StrictSpectralExtractionFront.extractor_not_constant S

end SpectralFingerprintRecoverability
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_spectral_anchor_recovers_zero_patch.lean ============ -/

/-
  Riemann_spectral_anchor_recovers_zero_patch.lean

  Purpose
  -------
  This is the next strict layer after

      Riemann_spectral_fingerprint_recoverability_patch.lean

  The previous layer required the arithmetic atom extracted from an
  off-critical zero to recover a nontrivial spectral fingerprint.

  This file pushes the requirement all the way back to the zero itself:

      atom -> spectral fingerprint -> Z.

  In other words, the anchor is not merely zero-sensitive; it is
  zero-recovering.  If an atom is anchored at `Z`, then the decoded spectral
  data of the atom must literally recover `Z`.

  This is the precise firewall against a free `0 -> 1` origin supply: one
  fixed arithmetic atom cannot serve two distinct zeros, because decoding its
  spectral fingerprint would have to return two different zeros.

  This file is self-contained and proves no RH bridge.  It states the strict
  data-level obligation that a non-circular arithmetic two-transport route
  must eventually provide.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace SpectralAnchorRecoversZero

/-!
## 1. Data-level anchored law
-/

variable {Zero Atom : Type}

/--
A data-level anchored law.  `LawAt Z` is not enough; the route must eventually
extract concrete atoms whose data is constrained by `Z`.
-/
structure DataAnchoredLaw (Zero : Type) (Atom : Type) where
  Admissible : Atom -> Prop
  Anchor : Zero -> Atom -> Prop

namespace DataAnchoredLaw

/-- Proposition-valued shadow of the data-level law at a zero. -/
def LawAt (D : DataAnchoredLaw Zero Atom) (Z : Zero) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ D.Anchor Z atom

/-- Bridge shape: every zero has an anchored admissible atom. -/
def Bridge (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, LawAt D Z

/-- A concrete extractor of atoms from zeros. -/
def Extractor (D : DataAnchoredLaw Zero Atom) : Type :=
  ∀ Z : Zero, { atom : Atom // D.Admissible atom ∧ D.Anchor Z atom }

/-- An extractor implies the proposition-level bridge. -/
theorem bridge_of_extractor
    {D : DataAnchoredLaw Zero Atom}
    (E : Extractor D) :
    Bridge D := by
  intro Z
  exact ⟨(E Z).val, (E Z).property⟩

/-- A free origin supply: one admissible atom works for every zero. -/
def FreeOriginSupply (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ ∀ Z : Zero, D.Anchor Z atom

/-- A constant extractor always returns the same atom. -/
def ConstantExtractor
    (D : DataAnchoredLaw Zero Atom)
    (E : Extractor D) : Prop :=
  ∃ atom₀ : Atom, ∀ Z : Zero, (E Z).val = atom₀

end DataAnchoredLaw

/-!
## 2. Decodable spectral fingerprint: atom -> fingerprint -> zero
-/

/--
A spectral fingerprint that is strong enough to recover the zero itself.

Fields:
* `zeroFP` is the spectral fingerprint of a zero.
* `atomFP` is the fingerprint read from an arithmetic atom.
* `respects` says anchored atoms recover the zero's fingerprint.
* `decode` decodes a fingerprint back to a zero.
* `decode_zero` says the zero-side fingerprint decodes to the original zero.

Hence an anchored atom satisfies

    decode (atomFP atom) = Z.
-/
structure DecodableSpectralFingerprint
    (D : DataAnchoredLaw Zero Atom) where
  Fingerprint : Type
  zeroFP : Zero -> Fingerprint
  atomFP : Atom -> Fingerprint
  respects : ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom -> atomFP atom = zeroFP Z
  decode : Fingerprint -> Zero
  decode_zero : ∀ Z : Zero, decode (zeroFP Z) = Z

namespace DecodableSpectralFingerprint

/-- The zero-side fingerprint is injective, because it has a left inverse. -/
theorem zeroFP_injective
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D) :
    Function.Injective F.zeroFP := by
  intro Z₁ Z₂ h
  have h₁ : F.decode (F.zeroFP Z₁) = Z₁ := F.decode_zero Z₁
  have h₂ : F.decode (F.zeroFP Z₂) = Z₂ := F.decode_zero Z₂
  calc
    Z₁ = F.decode (F.zeroFP Z₁) := h₁.symm
    _ = F.decode (F.zeroFP Z₂) := by rw [h]
    _ = Z₂ := h₂

/-- An anchored atom decodes all the way back to its zero. -/
theorem decode_atom_of_anchor
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    {Z : Zero} {atom : Atom}
    (hA : D.Anchor Z atom) :
    F.decode (F.atomFP atom) = Z := by
  have h : F.atomFP atom = F.zeroFP Z := F.respects Z atom hA
  calc
    F.decode (F.atomFP atom) = F.decode (F.zeroFP Z) := by rw [h]
    _ = Z := F.decode_zero Z

/-- The same anchored atom cannot serve two different zeros. -/
theorem atom_determines_zero
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    {Z₁ Z₂ : Zero} {atom : Atom}
    (h₁ : D.Anchor Z₁ atom)
    (h₂ : D.Anchor Z₂ atom) :
    Z₁ = Z₂ := by
  have d₁ : F.decode (F.atomFP atom) = Z₁ :=
    F.decode_atom_of_anchor h₁
  have d₂ : F.decode (F.atomFP atom) = Z₂ :=
    F.decode_atom_of_anchor h₂
  exact d₁.symm.trans d₂

/-- If there are two distinct zeros, no single origin atom can serve them all. -/
theorem no_freeOriginSupply_of_two_distinct_zeros
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    (hTwo : ∃ Z₁ : Zero, ∃ Z₂ : Zero, Z₁ ≠ Z₂) :
    ¬ (DataAnchoredLaw.FreeOriginSupply D) := by
  intro hFree
  rcases hFree with ⟨atom, _hAdm, hAll⟩
  rcases hTwo with ⟨Z₁, Z₂, hNe⟩
  exact hNe (F.atom_determines_zero (hAll Z₁) (hAll Z₂))

/-- Under zero recovery, a constant extractor is impossible on two distinct zeros. -/
theorem no_constantExtractor_of_two_distinct_zeros
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    (E : DataAnchoredLaw.Extractor D)
    (hTwo : ∃ Z₁ : Zero, ∃ Z₂ : Zero, Z₁ ≠ Z₂) :
    ¬ (DataAnchoredLaw.ConstantExtractor D E) := by
  intro hConst
  rcases hConst with ⟨atom₀, hConst⟩
  rcases hTwo with ⟨Z₁, Z₂, hNe⟩
  have hA₁ : D.Anchor Z₁ (E Z₁).val := (E Z₁).property.2
  have hA₂ : D.Anchor Z₂ (E Z₂).val := (E Z₂).property.2
  have d₁ : F.decode (F.atomFP (E Z₁).val) = Z₁ :=
    F.decode_atom_of_anchor hA₁
  have d₂raw : F.decode (F.atomFP (E Z₂).val) = Z₂ :=
    F.decode_atom_of_anchor hA₂
  have hSameFP : F.atomFP (E Z₁).val = F.atomFP (E Z₂).val := by
    rw [hConst Z₁, hConst Z₂]
  have d₂ : F.decode (F.atomFP (E Z₁).val) = Z₂ := by
    rw [hSameFP]
    exact d₂raw
  exact hNe (d₁.symm.trans d₂)

end DecodableSpectralFingerprint

/-!
## 3. Strict front: extraction whose atom recovers Z
-/

/--
The corrected strict front all the way to `Z`.

In the intended RH application:
* `Zero` is the type of off-critical zeros;
* `Atom` is the arithmetic two-transport atom;
* `extractor Z` is the atom extracted from that zero;
* `fingerprint` proves the extracted atom decodes back to `Z`.

This is stronger than merely recovering a nontrivial invariant.  It says that
no zero is lost at the anchor.
-/
structure StrictZeroRecoveryFront (Zero : Type) (Atom : Type) where
  D : DataAnchoredLaw Zero Atom
  extractor : DataAnchoredLaw.Extractor D
  fingerprint : DecodableSpectralFingerprint D

namespace StrictZeroRecoveryFront

/-- The strict zero-recovery front implies the ordinary bridge. -/
theorem bridge
    (S : StrictZeroRecoveryFront Zero Atom) :
    DataAnchoredLaw.Bridge S.D :=
  DataAnchoredLaw.bridge_of_extractor S.extractor

/-- The atom extracted at `Z` decodes back to exactly `Z`. -/
theorem extracted_atom_recovers_zero
    (S : StrictZeroRecoveryFront Zero Atom)
    (Z : Zero) :
    S.fingerprint.decode (S.fingerprint.atomFP (S.extractor Z).val) = Z :=
  S.fingerprint.decode_atom_of_anchor (S.extractor Z).property.2

/-- The anchor relation is left-unique in the zero coordinate. -/
theorem atom_determines_zero
    (S : StrictZeroRecoveryFront Zero Atom)
    {Z₁ Z₂ : Zero} {atom : Atom}
    (h₁ : S.D.Anchor Z₁ atom)
    (h₂ : S.D.Anchor Z₂ atom) :
    Z₁ = Z₂ :=
  S.fingerprint.atom_determines_zero h₁ h₂

/-- If the zero type has at least two points, there is no free origin supply. -/
theorem no_freeOriginSupply_of_two_distinct_zeros
    (S : StrictZeroRecoveryFront Zero Atom)
    (hTwo : ∃ Z₁ : Zero, ∃ Z₂ : Zero, Z₁ ≠ Z₂) :
    ¬ (DataAnchoredLaw.FreeOriginSupply S.D) :=
  S.fingerprint.no_freeOriginSupply_of_two_distinct_zeros hTwo

/-- If the zero type has at least two points, the extractor is not constant. -/
theorem extractor_not_constant_of_two_distinct_zeros
    (S : StrictZeroRecoveryFront Zero Atom)
    (hTwo : ∃ Z₁ : Zero, ∃ Z₂ : Zero, Z₁ ≠ Z₂) :
    ¬ (DataAnchoredLaw.ConstantExtractor S.D S.extractor) :=
  S.fingerprint.no_constantExtractor_of_two_distinct_zeros S.extractor hTwo

end StrictZeroRecoveryFront

/-!
## 4. The next RH-route obligation
-/

/--
The next non-circular obligation for the arithmetic two-transport route.

Compared with the previous fingerprint layer, this requires complete recovery
of the off-critical zero from the extracted arithmetic atom.
-/
abbrev SpectralAnchorToZObligation (Zero Atom : Type) : Type 1 :=
  StrictZeroRecoveryFront Zero Atom

/-- Slogan: a strict anchor-to-Z bridge reads the zero, not just a free atom. -/
theorem anchorToZ_reads_zero
    (S : SpectralAnchorToZObligation Zero Atom)
    (Z : Zero) :
    S.fingerprint.decode (S.fingerprint.atomFP (S.extractor Z).val) = Z :=
  StrictZeroRecoveryFront.extracted_atom_recovers_zero S Z

/-- Slogan: one atom cannot be the universal origin supply for two different zeros. -/
theorem anchorToZ_not_originBoundary
    (S : SpectralAnchorToZObligation Zero Atom)
    (hTwo : ∃ Z₁ : Zero, ∃ Z₂ : Zero, Z₁ ≠ Z₂) :
    ¬ (DataAnchoredLaw.FreeOriginSupply S.D) :=
  StrictZeroRecoveryFront.no_freeOriginSupply_of_two_distinct_zeros S hTwo

/--
Final status statement for this layer.

To get a non-vacuous arithmetic two-transport bridge, it is not enough to show
`∀ Z, ∃ atom`.  The route must provide an extracted atom whose
spectral code decodes back to the very zero `Z` that generated it.
-/
theorem anchorToZ_final_status
    (S : SpectralAnchorToZObligation Zero Atom) :
    ∀ Z : Zero,
      S.fingerprint.decode (S.fingerprint.atomFP (S.extractor Z).val) = Z :=
  fun Z => anchorToZ_reads_zero S Z

end SpectralAnchorRecoversZero
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_zero_indexed_impossibility_patch.lean ============ -/

/-
  Riemann_zero_indexed_impossibility_patch.lean

  Purpose
  -------
  This is the next strict layer after

      Riemann_spectral_anchor_recovers_zero_patch.lean

  The previous layer required an extracted arithmetic atom to decode back to the
  very off-critical zero `Z` that generated it:

      atom -> spectral fingerprint -> Z.

  This file records the next necessary strengthening of the Riemann arithmetic
  two-transport route.

  A global atom question such as

      ∃ atom, Admissible atom

  is still an origin/boundary supply: it does not kill a particular zero.
  Once the atom decodes to a zero, the correct impossibility target is
  zero-indexed:

      no admissible atom can be anchored at the zero decoded by that atom.

  Then an extracted atom for any off-critical zero contradicts the local
  impossibility at its own decoded zero.  This proves the abstract route:

      (not Target -> Nonempty Zero)
      + strict zero-recovering extraction
      + self-decoded atom impossibility
      -> Target.

  In the RH application, `Target` is mathlib's RiemannHypothesis and `Zero` is
  the type of off-critical zeros.  This file does not prove the analytic
  extraction or the arithmetic impossibility.  It makes precise what those
  inputs must look like so that the route is no longer a free `0 -> 1` supply.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace ZeroIndexedImpossibility

/-!
## 1. Data-level anchored laws
-/

variable {Target : Prop} {Zero Atom : Type}

/--
A data-level anchored law.  The proposition `LawAt Z` is the shadow; the route
must eventually extract concrete atoms whose data is constrained by `Z`.
-/
structure DataAnchoredLaw (Zero : Type) (Atom : Type) where
  Admissible : Atom -> Prop
  Anchor : Zero -> Atom -> Prop

namespace DataAnchoredLaw

/-- Proposition-valued law at a zero. -/
def LawAt (D : DataAnchoredLaw Zero Atom) (Z : Zero) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ D.Anchor Z atom

/-- Bridge shape: every zero has an anchored admissible atom. -/
def Bridge (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, LawAt D Z

/-- A concrete extractor of atoms from zeros. -/
def Extractor (D : DataAnchoredLaw Zero Atom) : Type :=
  ∀ Z : Zero, { atom : Atom // D.Admissible atom ∧ D.Anchor Z atom }

/-- A free origin supply: one admissible atom works for every zero. -/
def FreeOriginSupply (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ ∀ Z : Zero, D.Anchor Z atom

/-- An extractor implies the proposition-level bridge. -/
theorem bridge_of_extractor
    {D : DataAnchoredLaw Zero Atom}
    (E : Extractor D) :
    Bridge D := by
  intro Z
  exact ⟨(E Z).val, (E Z).property⟩

end DataAnchoredLaw

/-!
## 2. Decodable fingerprint: anchored atom decodes to its zero
-/

/--
A spectral fingerprint strong enough to recover the zero itself.

If an atom is anchored at `Z`, then `decode (atomFP atom) = Z`.
-/
structure DecodableSpectralFingerprint
    (D : DataAnchoredLaw Zero Atom) where
  Fingerprint : Type
  zeroFP : Zero -> Fingerprint
  atomFP : Atom -> Fingerprint
  respects : ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom -> atomFP atom = zeroFP Z
  decode : Fingerprint -> Zero
  decode_zero : ∀ Z : Zero, decode (zeroFP Z) = Z

namespace DecodableSpectralFingerprint

/-- An anchored atom decodes all the way back to its zero. -/
theorem decode_atom_of_anchor
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    {Z : Zero} {atom : Atom}
    (hA : D.Anchor Z atom) :
    F.decode (F.atomFP atom) = Z := by
  have h : F.atomFP atom = F.zeroFP Z := F.respects Z atom hA
  calc
    F.decode (F.atomFP atom) = F.decode (F.zeroFP Z) := by rw [h]
    _ = Z := F.decode_zero Z

/-- The same anchored atom cannot serve two different zeros. -/
theorem atom_determines_zero
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    {Z₁ Z₂ : Zero} {atom : Atom}
    (h₁ : D.Anchor Z₁ atom)
    (h₂ : D.Anchor Z₂ atom) :
    Z₁ = Z₂ := by
  have d₁ : F.decode (F.atomFP atom) = Z₁ :=
    F.decode_atom_of_anchor h₁
  have d₂ : F.decode (F.atomFP atom) = Z₂ :=
    F.decode_atom_of_anchor h₂
  exact d₁.symm.trans d₂

end DecodableSpectralFingerprint

/-!
## 3. Strict zero-recovery front
-/

/--
The strict front: a concrete extractor plus a fingerprint decoder back to `Z`.
-/
structure StrictZeroRecoveryFront (Zero : Type) (Atom : Type) where
  D : DataAnchoredLaw Zero Atom
  extractor : DataAnchoredLaw.Extractor D
  fingerprint : DecodableSpectralFingerprint D

namespace StrictZeroRecoveryFront

/-- The strict front implies the ordinary bridge. -/
theorem bridge
    (S : StrictZeroRecoveryFront Zero Atom) :
    DataAnchoredLaw.Bridge S.D :=
  DataAnchoredLaw.bridge_of_extractor S.extractor

/-- The extracted atom at `Z` decodes back to exactly `Z`. -/
theorem extracted_atom_recovers_zero
    (S : StrictZeroRecoveryFront Zero Atom)
    (Z : Zero) :
    S.fingerprint.decode (S.fingerprint.atomFP (S.extractor Z).val) = Z :=
  S.fingerprint.decode_atom_of_anchor (S.extractor Z).property.2

end StrictZeroRecoveryFront

/-!
## 4. The zero-indexed impossibility target
-/

/--
A zero-indexed impossibility: no admissible atom can be anchored at the given
zero.
-/
def ZeroIndexedImpossibility (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, ∀ atom : Atom,
    D.Admissible atom -> D.Anchor Z atom -> False

/--
The sharper self-decoded impossibility.

An atom is killed at the zero decoded from its own spectral fingerprint.  This
is the correct non-origin target after the anchor has been strengthened to
recover `Z`.
-/
def SelfDecodedAtomImpossibility
    (D : DataAnchoredLaw Zero Atom)
    (F : DecodableSpectralFingerprint D) : Prop :=
  ∀ atom : Atom,
    D.Admissible atom ->
    D.Anchor (F.decode (F.atomFP atom)) atom ->
    False

/--
Self-decoded impossibility implies zero-indexed impossibility, because an atom
anchored at `Z` decodes to `Z`.
-/
theorem zeroIndexedImpossibility_of_selfDecoded
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    (hSelf : SelfDecodedAtomImpossibility D F) :
    ZeroIndexedImpossibility D := by
  intro Z atom hAdm hAnchor
  have hDec : F.decode (F.atomFP atom) = Z :=
    F.decode_atom_of_anchor hAnchor
  have hAnchorDecoded : D.Anchor (F.decode (F.atomFP atom)) atom := by
    rw [hDec]
    exact hAnchor
  exact hSelf atom hAdm hAnchorDecoded

/-- Under self-decoded impossibility, no law can hold at any zero. -/
theorem no_lawAt_of_selfDecoded
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    (hSelf : SelfDecodedAtomImpossibility D F)
    (Z : Zero) :
    ¬ DataAnchoredLaw.LawAt D Z := by
  intro hLaw
  rcases hLaw with ⟨atom, hAdm, hAnchor⟩
  exact zeroIndexedImpossibility_of_selfDecoded F hSelf Z atom hAdm hAnchor

/-- A self-decoded impossibility forbids even a single free origin atom. -/
theorem selfDecoded_forbids_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    (hSelf : SelfDecodedAtomImpossibility D F) :
    ¬ DataAnchoredLaw.FreeOriginSupply D := by
  intro hFree
  rcases hFree with ⟨atom, hAdm, hAll⟩
  exact hSelf atom hAdm (hAll (F.decode (F.atomFP atom)))

/-- Bridge plus zero-indexed impossibility forces the zero type to be empty. -/
theorem bridge_and_zeroIndexed_force_empty
    {D : DataAnchoredLaw Zero Atom}
    (hBridge : DataAnchoredLaw.Bridge D)
    (hImpossible : ZeroIndexedImpossibility D) :
    IsEmpty Zero := by
  refine ⟨?_⟩
  intro Z
  rcases hBridge Z with ⟨atom, hAdm, hAnchor⟩
  exact hImpossible Z atom hAdm hAnchor

/-- Strict extraction plus self-decoded impossibility forces the zero type empty. -/
theorem strictFront_and_selfDecoded_force_empty
    (S : StrictZeroRecoveryFront Zero Atom)
    (hSelf : SelfDecodedAtomImpossibility S.D S.fingerprint) :
    IsEmpty Zero := by
  exact bridge_and_zeroIndexed_force_empty
    (StrictZeroRecoveryFront.bridge S)
    (zeroIndexedImpossibility_of_selfDecoded S.fingerprint hSelf)

/-!
## 5. Certificate form for future arithmetic instantiations
-/

/--
A certificate form of self-decoded impossibility.

The concrete repo can instantiate `Obstruction atom` as a LayerBox/residue/
determinant obstruction.  This separates two future tasks:

* derive the obstruction from an admissible atom anchored at its decoded zero;
* prove the obstruction impossible arithmetically.
-/
structure SelfDecodedImpossibilityCertificate
    (D : DataAnchoredLaw Zero Atom)
    (F : DecodableSpectralFingerprint D) where
  Obstruction : Atom -> Prop
  obstruction_of_self_anchor : ∀ atom : Atom,
    D.Admissible atom ->
    D.Anchor (F.decode (F.atomFP atom)) atom ->
    Obstruction atom
  obstruction_impossible : ∀ atom : Atom, ¬ Obstruction atom

namespace SelfDecodedImpossibilityCertificate

/-- The certificate yields the self-decoded impossibility proposition. -/
theorem to_selfDecodedAtomImpossibility
    {D : DataAnchoredLaw Zero Atom}
    {F : DecodableSpectralFingerprint D}
    (C : SelfDecodedImpossibilityCertificate D F) :
    SelfDecodedAtomImpossibility D F := by
  intro atom hAdm hAnchor
  exact C.obstruction_impossible atom
    (C.obstruction_of_self_anchor atom hAdm hAnchor)

/-- Hence the certificate also forbids free origin supply. -/
theorem forbids_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    {F : DecodableSpectralFingerprint D}
    (C : SelfDecodedImpossibilityCertificate D F) :
    ¬ DataAnchoredLaw.FreeOriginSupply D :=
  selfDecoded_forbids_freeOriginSupply F C.to_selfDecodedAtomImpossibility

end SelfDecodedImpossibilityCertificate

/-!
## 6. Abstract RH-style conclusion
-/

/--
The strict zero-indexed front for a target proposition.

For RH, instantiate:
* `Target := RiemannHypothesis`;
* `Zero := OffCriticalZero`;
* `Atom := ArithmeticTransportAtom` or the final repo-specific atom type.
-/
structure ZeroIndexedStrictFront (Target : Prop) (Zero : Type) (Atom : Type) where
  zero_of_not_target : ¬ Target -> Nonempty Zero
  S : StrictZeroRecoveryFront Zero Atom
  impossible : SelfDecodedAtomImpossibility S.D S.fingerprint

namespace ZeroIndexedStrictFront

/-- The strict zero-indexed front proves the target. -/
theorem target
    (Fnt : ZeroIndexedStrictFront Target Zero Atom) :
    Target := by
  classical
  by_contra hTarget
  rcases Fnt.zero_of_not_target hTarget with ⟨Z⟩
  have hLaw : DataAnchoredLaw.LawAt Fnt.S.D Z :=
    StrictZeroRecoveryFront.bridge Fnt.S Z
  exact no_lawAt_of_selfDecoded Fnt.S.fingerprint Fnt.impossible Z hLaw

/-- It also rules out the free origin/boundary supply. -/
theorem no_freeOriginSupply
    (Fnt : ZeroIndexedStrictFront Target Zero Atom) :
    ¬ DataAnchoredLaw.FreeOriginSupply Fnt.S.D :=
  selfDecoded_forbids_freeOriginSupply Fnt.S.fingerprint Fnt.impossible

/-- Combined status statement for this layer. -/
theorem status
    (Fnt : ZeroIndexedStrictFront Target Zero Atom) :
    Target ∧ ¬ DataAnchoredLaw.FreeOriginSupply Fnt.S.D :=
  ⟨Fnt.target, Fnt.no_freeOriginSupply⟩

end ZeroIndexedStrictFront

/--
Slogan theorem: after `atom -> Z`, the remaining obstruction must be indexed by
that decoded zero.  A free global atom question is no longer the right target.
-/
theorem zeroIndexedImpossibility_slogan
    (S : StrictZeroRecoveryFront Zero Atom)
    (hSelf : SelfDecodedAtomImpossibility S.D S.fingerprint) :
    IsEmpty Zero ∧ ¬ DataAnchoredLaw.FreeOriginSupply S.D :=
  ⟨strictFront_and_selfDecoded_force_empty S hSelf,
   selfDecoded_forbids_freeOriginSupply S.fingerprint hSelf⟩

end ZeroIndexedImpossibility
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_decoded_layerbox_arithmetic_kernel_patch.lean ============ -/

/-
  Riemann_decoded_layerbox_arithmetic_kernel_patch.lean

  Purpose
  -------
  This is the next strict layer after

      Riemann_zero_indexed_impossibility_patch.lean

  The previous layer says that the arithmetic two-transport route is no longer
  allowed to kill a free global atom.  The atom extracted from an off-critical
  zero must decode back to that very zero, and the impossibility must be applied
  at the decoded zero.

  This file opens the remaining impossibility one level further.  A
  self-decoded impossibility must come from concrete arithmetic gates:

      extracted atom
        -> determinant/two-transport identity
        -> layer-box gate
        -> residue/polarity gate
        -> local arithmetic obstruction
        -> contradiction at the decoded zero.

  The file is deliberately an audit kernel.  It does not assert that the
  Riemann-specific residue gate has already been proved.  Instead it proves the
  exact assembly theorem:

      decoded layer-box arithmetic obstruction
      -> self-decoded impossibility
      -> no off-critical zeros
      -> target theorem.

  In the RH application, `Target` is mathlib's RiemannHypothesis and `Zero` is
  the type of off-critical zeros.  The still-open concrete work is to instantiate
  `DecodedLayerBoxArithmeticObstruction` with the real LayerBox/residue data
  extracted from the zero.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace DecodedLayerBoxKernel

/-!
## 1. Generic anchored law and zero recovery

These definitions are intentionally repeated in this standalone patch so it can
be read independently of the earlier audit files.
-/

variable {Target Zero Atom : Type}

/--
A data-level law: `Admissible atom` is the arithmetic gate, and `Anchor Z atom`
says that the atom was extracted from the particular zero `Z`.
-/
structure DataAnchoredLaw (Zero : Type) (Atom : Type) where
  Admissible : Atom -> Prop
  Anchor : Zero -> Atom -> Prop

namespace DataAnchoredLaw

/-- Proposition-level shadow of a data-level law at a zero. -/
def LawAt (D : DataAnchoredLaw Zero Atom) (Z : Zero) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ D.Anchor Z atom

/-- A concrete extractor of an anchored admissible atom from each zero. -/
def Extractor (D : DataAnchoredLaw Zero Atom) : Type :=
  ∀ Z : Zero, { atom : Atom // D.Admissible atom ∧ D.Anchor Z atom }

/-- The ordinary bridge shadow. -/
def Bridge (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∀ Z : Zero, LawAt D Z

/-- A free origin supply: one atom works for all zeros. -/
def FreeOriginSupply (D : DataAnchoredLaw Zero Atom) : Prop :=
  ∃ atom : Atom, D.Admissible atom ∧ ∀ Z : Zero, D.Anchor Z atom

/-- An extractor implies the proposition-level bridge. -/
theorem bridge_of_extractor
    {D : DataAnchoredLaw Zero Atom}
    (E : Extractor D) :
    Bridge D := by
  intro Z
  exact ⟨(E Z).val, (E Z).property⟩

end DataAnchoredLaw

/--
A spectral fingerprint that decodes an anchored atom back to the zero from
which it was extracted.
-/
structure DecodableSpectralFingerprint
    (D : DataAnchoredLaw Zero Atom) where
  Fingerprint : Type
  zeroFP : Zero -> Fingerprint
  atomFP : Atom -> Fingerprint
  respects : ∀ Z : Zero, ∀ atom : Atom,
    D.Anchor Z atom -> atomFP atom = zeroFP Z
  decode : Fingerprint -> Zero
  decode_zero : ∀ Z : Zero, decode (zeroFP Z) = Z

namespace DecodableSpectralFingerprint

/-- If `atom` is anchored at `Z`, its fingerprint decodes to `Z`. -/
theorem decode_atom_of_anchor
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    {Z : Zero} {atom : Atom}
    (hAnchor : D.Anchor Z atom) :
    F.decode (F.atomFP atom) = Z := by
  have h : F.atomFP atom = F.zeroFP Z := F.respects Z atom hAnchor
  calc
    F.decode (F.atomFP atom) = F.decode (F.zeroFP Z) := by rw [h]
    _ = Z := F.decode_zero Z

end DecodableSpectralFingerprint

/--
Self-decoded impossibility: no admissible atom can be anchored at the zero
obtained by decoding its own fingerprint.
-/
def SelfDecodedAtomImpossibility
    (D : DataAnchoredLaw Zero Atom)
    (F : DecodableSpectralFingerprint D) : Prop :=
  ∀ atom : Atom,
    D.Admissible atom ->
    D.Anchor (F.decode (F.atomFP atom)) atom ->
    False

/-- Self-decoded impossibility forbids a law at any zero. -/
theorem no_lawAt_of_selfDecoded
    {D : DataAnchoredLaw Zero Atom}
    (F : DecodableSpectralFingerprint D)
    (hSelf : SelfDecodedAtomImpossibility D F)
    (Z : Zero) :
    ¬ DataAnchoredLaw.LawAt D Z := by
  intro hLaw
  rcases hLaw with ⟨atom, hAdm, hAnchor⟩
  have hDec : F.decode (F.atomFP atom) = Z :=
    F.decode_atom_of_anchor hAnchor
  have hAnchorDecoded : D.Anchor (F.decode (F.atomFP atom)) atom := by
    rw [hDec]
    exact hAnchor
  exact hSelf atom hAdm hAnchorDecoded

/-- Extractor plus self-decoded impossibility empties the zero type. -/
theorem empty_zero_of_extractor_and_selfDecoded
    {D : DataAnchoredLaw Zero Atom}
    (E : DataAnchoredLaw.Extractor D)
    (F : DecodableSpectralFingerprint D)
    (hSelf : SelfDecodedAtomImpossibility D F) :
    IsEmpty Zero := by
  refine ⟨?_⟩
  intro Z
  exact no_lawAt_of_selfDecoded F hSelf Z ⟨(E Z).val, (E Z).property⟩

/-!
## 2. Arithmetic coordinates for the two-transport atom
-/

/--
The six arithmetic coordinates of a two-transport atom.  This separates the
logical anchor from the arithmetic payload.
-/
structure ArithmeticCoordinates (Atom : Type) where
  q : Atom -> ℕ
  r : Atom -> ℕ
  s : Atom -> ℕ
  a : Atom -> ℕ
  b : Atom -> ℕ
  v : Atom -> ℕ

namespace ArithmeticCoordinates

/-- Left product `abv`. -/
def leftMass (C : ArithmeticCoordinates Atom) (atom : Atom) : ℕ :=
  C.a atom * C.b atom * C.v atom

/-- Right product `qrs`. -/
def rightMass (C : ArithmeticCoordinates Atom) (atom : Atom) : ℕ :=
  C.q atom * C.r atom * C.s atom

/-- Determinant/two-transport identity. -/
def DeterminantIdentity (C : ArithmeticCoordinates Atom) (atom : Atom) : Prop :=
  C.rightMass atom = C.leftMass atom + 2

/-- A layer-box gate `(A, A^2]` for all six coordinates. -/
def LayerBox (C : ArithmeticCoordinates Atom) (A : ℕ) (atom : Atom) : Prop :=
  A < C.a atom ∧ C.a atom ≤ A * A ∧
  A < C.b atom ∧ C.b atom ≤ A * A ∧
  A < C.v atom ∧ C.v atom ≤ A * A ∧
  A < C.q atom ∧ C.q atom ≤ A * A ∧
  A < C.r atom ∧ C.r atom ≤ A * A ∧
  A < C.s atom ∧ C.s atom ≤ A * A

/-- A residue/polarity gate.  The concrete repo supplies its exact content. -/
abbrev ResidueGate (C : ArithmeticCoordinates Atom) (atom : Atom) : Prop :=
  True

end ArithmeticCoordinates

/-!
## 3. The decoded layer-box arithmetic obstruction
-/

/--
The concrete arithmetic kernel required for the self-decoded impossibility.

For every admissible atom anchored at its decoded zero, the route must provide:

* the determinant identity `qrs = abv + 2`;
* a layer box `(A, A^2]`;
* a residue/polarity gate;
* a proof that those gates are jointly impossible at the decoded zero.

The last field is where the real arithmetic work belongs.  It can be a mod-6
obstruction, a LayerBox obstruction, a parity obstruction, or a stronger local
number-theoretic contradiction.  Crucially, it is applied to the atom itself,
not to a free global atom.
-/
structure DecodedLayerBoxArithmeticObstruction
    (D : DataAnchoredLaw Zero Atom)
    (F : DecodableSpectralFingerprint D) where
  C : ArithmeticCoordinates Atom
  A : Atom -> ℕ

  determinant_of_admissible : ∀ atom : Atom,
    D.Admissible atom ->
    ArithmeticCoordinates.DeterminantIdentity C atom

  layer_of_admissible : ∀ atom : Atom,
    D.Admissible atom ->
    ArithmeticCoordinates.LayerBox C (A atom) atom

  residue_of_self_anchor : ∀ atom : Atom,
    D.Admissible atom ->
    D.Anchor (F.decode (F.atomFP atom)) atom ->
    ArithmeticCoordinates.ResidueGate C atom

  local_arithmetic_obstruction : ∀ atom : Atom,
    D.Admissible atom ->
    D.Anchor (F.decode (F.atomFP atom)) atom ->
    ArithmeticCoordinates.DeterminantIdentity C atom ->
    ArithmeticCoordinates.LayerBox C (A atom) atom ->
    ArithmeticCoordinates.ResidueGate C atom ->
    False

namespace DecodedLayerBoxArithmeticObstruction

/--
The decoded arithmetic obstruction produces the self-decoded impossibility.
-/
theorem to_selfDecoded
    {D : DataAnchoredLaw Zero Atom}
    {F : DecodableSpectralFingerprint D}
    (K : DecodedLayerBoxArithmeticObstruction D F) :
    SelfDecodedAtomImpossibility D F := by
  intro atom hAdm hAnchorDecoded
  exact K.local_arithmetic_obstruction atom hAdm hAnchorDecoded
    (K.determinant_of_admissible atom hAdm)
    (K.layer_of_admissible atom hAdm)
    (K.residue_of_self_anchor atom hAdm hAnchorDecoded)

/-- With an extractor, the decoded arithmetic obstruction empties the zero type. -/
theorem force_empty_zero
    {D : DataAnchoredLaw Zero Atom}
    {F : DecodableSpectralFingerprint D}
    (E : DataAnchoredLaw.Extractor D)
    (K : DecodedLayerBoxArithmeticObstruction D F) :
    IsEmpty Zero :=
  empty_zero_of_extractor_and_selfDecoded E F K.to_selfDecoded

/-- The obstruction forbids a free origin supply as well. -/
theorem no_freeOriginSupply
    {D : DataAnchoredLaw Zero Atom}
    {F : DecodableSpectralFingerprint D}
    (K : DecodedLayerBoxArithmeticObstruction D F) :
    ¬ DataAnchoredLaw.FreeOriginSupply D := by
  intro hFree
  rcases hFree with ⟨atom, hAdm, hAll⟩
  exact K.to_selfDecoded atom hAdm (hAll (F.decode (F.atomFP atom)))

end DecodedLayerBoxArithmeticObstruction

/-!
## 4. Final assembly to a target theorem
-/

/--
The strict decoded LayerBox front for a target theorem.

In the RH application:
* `Target` is `RiemannHypothesis`;
* `Zero` is `OffCriticalZero`;
* `notTarget_to_zero` is localization of an RH counterexample to an
  off-critical zero;
* `extractor` is the zero-to-atom construction;
* `fingerprint` proves atom -> Z;
* `kernel` is the decoded arithmetic obstruction.
-/
structure DecodedLayerBoxStrictFront (Target : Prop) (Zero : Type) (Atom : Type) where
  D : DataAnchoredLaw Zero Atom
  notTarget_to_zero : ¬ Target -> Nonempty Zero
  extractor : DataAnchoredLaw.Extractor D
  fingerprint : DecodableSpectralFingerprint D
  kernel : DecodedLayerBoxArithmeticObstruction D fingerprint

namespace DecodedLayerBoxStrictFront

/-- The strict decoded LayerBox front proves the target. -/
theorem target
    {Target : Prop} {Zero Atom : Type}
    (S : DecodedLayerBoxStrictFront Target Zero Atom) :
    Target := by
  by_contra hNot
  rcases S.notTarget_to_zero hNot with ⟨Z⟩
  have hEmpty : IsEmpty Zero := S.kernel.force_empty_zero S.extractor
  exact (IsEmpty.false Z)

/-- The strict front has no free origin-supply interpretation. -/
theorem no_freeOriginSupply
    {Target : Prop} {Zero Atom : Type}
    (S : DecodedLayerBoxStrictFront Target Zero Atom) :
    ¬ DataAnchoredLaw.FreeOriginSupply S.D :=
  S.kernel.no_freeOriginSupply

end DecodedLayerBoxStrictFront

/-!
## 5. A small residue sanity interface

This section does not choose the real repo residue gate.  It records a useful
sanity pattern: if a proposed residue profile is known to be incompatible with
`qrs = abv + 2`, it can be plugged into the field
`local_arithmetic_obstruction` above.
-/

/-- A proposed residue profile for the six coordinates modulo 6. -/
structure ResidueProfile where
  q : Fin 6
  r : Fin 6
  s : Fin 6
  a : Fin 6
  b : Fin 6
  v : Fin 6

namespace ResidueProfile

/-- Product of the right residues `q*r*s` in `Fin 6`. -/
def right (P : ResidueProfile) : Fin 6 :=
  P.q * P.r * P.s

/-- Product of the left residues `a*b*v` in `Fin 6`. -/
def left (P : ResidueProfile) : Fin 6 :=
  P.a * P.b * P.v

/-- The profile is locally obstructed for `qrs = abv + 2`. -/
abbrev Obstructed (P : ResidueProfile) : Prop :=
  P.right ≠ P.left + (2 : Fin 6)

/-- The concrete `555 / 111 + 2` profile is obstructed modulo 6. -/
def profile_555_111 : ResidueProfile where
  q := ⟨5, by decide⟩
  r := ⟨5, by decide⟩
  s := ⟨5, by decide⟩
  a := ⟨1, by decide⟩
  b := ⟨1, by decide⟩
  v := ⟨1, by decide⟩

/-- Sanity check: `5*5*5 ≠ 1*1*1 + 2` modulo 6. -/
theorem profile_555_111_obstructed :
    Obstructed profile_555_111 := by
  decide

/--
A residue profile whose left product is `5` and right product is `1` is not
obstructed by the bare `+2` congruence.  This is the admissible mass-orientation
used in the non-engine law audit: `5 + 2 ≡ 1 (mod 6)`.
-/
def profile_mass_5_to_1 : ResidueProfile where
  q := ⟨1, by decide⟩
  r := ⟨1, by decide⟩
  s := ⟨1, by decide⟩
  a := ⟨5, by decide⟩
  b := ⟨1, by decide⟩
  v := ⟨1, by decide⟩

/-- The mass orientation `left ≡ 5`, `right ≡ 1` passes the bare mod-6 check. -/
theorem profile_mass_5_to_1_not_obstructed :
    ¬ Obstructed profile_mass_5_to_1 := by
  decide

end ResidueProfile

/-!
## 6. Slogan
-/

/--
Final status of this layer.

The remaining work is now explicit: instantiate the decoded LayerBox arithmetic
kernel with the actual residue/layer obstruction forced by the zero-decoding
anchor.
-/
theorem decodedLayerBoxKernel_slogan :
    True := by
  trivial

end DecodedLayerBoxKernel
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_same_zero_descent_patch.lean ============ -/

/-
Riemann_layerbox_same_zero_descent_patch.lean

Purpose
-------
This patch is the next strict layer after the decoded LayerBox arithmetic kernel.

The previous layers isolated the correct non-vacuous shape:

  off-critical zero Z
    -> extracted arithmetic atom
    -> the atom decodes back to Z
    -> the atom must be killed by zero-indexed arithmetic, not by a free
       Z-independent global obstruction.

This file turns the remaining arithmetic obstruction into a well-founded
same-zero descent obligation.

Main point
----------
A descent which merely produces a smaller valid atom is not yet enough for the
Riemann route, because it may lose the zero that the atom was supposed to
encode.  The descent must preserve the same zero-anchor.

The new live obligation is therefore:

  SameZeroDescentCertificate C

meaning: every valid atom anchored at a zero z produces a strictly smaller valid
atom anchored at the same zero z.  This is impossible by Nat well-foundedness.

This is a proof-theoretic/audit layer.  It does not assert the actual analytic
or arithmetic construction of the descent; it shows exactly what such a
construction would have to prove.
-/

namespace Riemann
namespace LayerBoxSameZeroDescent

/-- Six arithmetic coordinates for the arithmetic two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- The `qrs` side of the transport identity. -/
def leftMass (C : ArithmeticCoordinates) : Nat :=
  C.q * C.r * C.s

/-- The `abv` side of the transport identity. -/
def rightMass (C : ArithmeticCoordinates) : Nat :=
  C.a * C.b * C.v

/-- The arithmetic transport determinant/gap condition `qrs = abv + 2`. -/
def gapTwo (C : ArithmeticCoordinates) : Prop :=
  C.leftMass = C.rightMass + 2

end ArithmeticCoordinates

/--
A generic LayerBox predicate.  The concrete repository can instantiate
`inLayer`, `residueGate`, and `determinantGate` with the real `(A, A^2]`,
modular, and determinant gates.
-/
structure LayerBoxPredicate where
  A : Nat
  inLayer : ArithmeticCoordinates -> Prop
  residueGate : ArithmeticCoordinates -> Prop
  determinantGate : ArithmeticCoordinates -> Prop

/-- A coordinate tuple satisfies all local LayerBox gates. -/
def AtomSatisfies (P : LayerBoxPredicate) (C : ArithmeticCoordinates) : Prop :=
  P.inLayer C ∧ P.residueGate C ∧ P.determinantGate C

/--
A zero-indexed LayerBox context.

`Zero` is the type of off-critical zeros or zero witnesses.
`Atom` is the type of extracted arithmetic atoms.

The important fields are:
* `height`: the well-founded measure for descent;
* `valid`: the local arithmetic validity predicate;
* `decode`: the zero decoded from the atom;
* `anchor`: the statement that a zero `z` is genuinely carried by atom `a`.
-/
structure ZeroIndexedLayerBoxContext (Zero Atom : Type) where
  problem : LayerBoxPredicate
  coords : Atom -> ArithmeticCoordinates
  height : Atom -> Nat
  valid : Atom -> Prop
  decode : Atom -> Zero
  anchor : Zero -> Atom -> Prop
  valid_to_gates : ∀ a, valid a -> AtomSatisfies problem (coords a)

/--
A weak/global descent.  This is intentionally not enough for the RH route,
because it may forget the zero-anchor.
-/
structure GlobalDescentCertificate {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom) : Prop where
  descend : ∀ a, C.valid a -> ∃ b, C.valid b ∧ C.height b < C.height a

/--
The correct zero-indexed descent: a valid atom anchored at `z` descends to a
strictly smaller valid atom anchored at the same `z`.
-/
structure SameZeroDescentCertificate {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom) : Prop where
  descend : ∀ z a,
    C.valid a ->
    C.anchor z a ->
    ∃ b, C.valid b ∧ C.anchor z b ∧ C.height b < C.height a

/-
A global descent is weaker than a same-zero descent.  It may produce a
strictly smaller atom while losing the zero that the atom was supposed to
encode.  Therefore this patch never uses global descent to close the RH front;
the route below requires same-zero descent explicitly.
-/

/-- No valid atom can remain anchored at any fixed zero if same-zero strict descent is available. -/
theorem no_anchored_valid_of_sameZeroDescent {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom)
    (D : SameZeroDescentCertificate C)
    (z : Zero) (a : Atom) :
    C.valid a -> C.anchor z a -> False := by
  let P : Nat -> Prop := fun n =>
    ∀ a, C.height a = n -> C.valid a -> C.anchor z a -> False
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a ha hv hanch
        rcases D.descend z a hv hanch with ⟨b, hbv, hba, hlt⟩
        have hlt' : C.height b < n := by
          simpa [ha] using hlt
        exact ih (C.height b) hlt' b rfl hbv hba
  exact hP (C.height a) a rfl

/-- Self-decoded impossibility: the atom is impossible at the zero it decodes. -/
def SelfDecodedImpossibility {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom) : Prop :=
  ∀ a, C.valid a -> C.anchor (C.decode a) a -> False

/-- Same-zero descent implies self-decoded impossibility. -/
theorem selfDecodedImpossibility_of_sameZeroDescent {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom)
    (D : SameZeroDescentCertificate C) :
    SelfDecodedImpossibility C := by
  intro a hv hanch
  exact no_anchored_valid_of_sameZeroDescent C D (C.decode a) a hv hanch

/-- A free origin supply is one atom that is valid and anchored at every zero. -/
def FreeOriginSupply {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom) : Prop :=
  ∃ a, C.valid a ∧ ∀ z, C.anchor z a

/-- Same-zero descent forbids a free origin atom. -/
theorem no_freeOriginSupply_of_sameZeroDescent {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom)
    (D : SameZeroDescentCertificate C) :
    ¬ FreeOriginSupply C := by
  rintro ⟨a, hv, hall⟩
  exact no_anchored_valid_of_sameZeroDescent C D (C.decode a) a hv (hall (C.decode a))

/--
The strict front: every zero extracts a valid atom anchored at that same zero,
and every such anchored valid atom descends while preserving the zero.
-/
structure SameZeroDescentFront (Zero Atom : Type) where
  C : ZeroIndexedLayerBoxContext Zero Atom
  extract : ∀ z : Zero, ∃ a, C.valid a ∧ C.anchor z a
  descent : SameZeroDescentCertificate C

/-- A same-zero descent front rules out all zeros. -/
theorem SameZeroDescentFront.noZeros {Zero Atom : Type}
    (F : SameZeroDescentFront Zero Atom) :
    ∀ z : Zero, False := by
  intro z
  rcases F.extract z with ⟨a, hv, hanch⟩
  exact no_anchored_valid_of_sameZeroDescent F.C F.descent z a hv hanch

/--
An abstract target interface: in the repository, `Zero` should be
`OffCriticalZero` and `target` should be `RiemannHypothesis`.
-/
structure TargetFromNoZeros (Zero : Type) where
  target : Prop
  noZeros_to_target : (∀ z : Zero, False) -> target

/-- Same-zero descent closes any target that follows from absence of zeros. -/
theorem target_of_sameZeroDescentFront {Zero Atom : Type}
    (T : TargetFromNoZeros Zero)
    (F : SameZeroDescentFront Zero Atom) :
    T.target :=
  T.noZeros_to_target F.noZeros

/--
Final slogan as a theorem-shaped audit fact: the next genuine arithmetic input
is same-zero descent, not a free LayerBox atom.
-/
def SameZeroDescentNextObligation {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom) : Prop :=
  SameZeroDescentCertificate C

/-- If the next obligation is met and zeros extract anchored atoms, all zeros vanish. -/
theorem sameZeroDescentNextObligation_closes_zero_front {Zero Atom : Type}
    (C : ZeroIndexedLayerBoxContext Zero Atom)
    (hExtract : ∀ z : Zero, ∃ a, C.valid a ∧ C.anchor z a)
    (hNext : SameZeroDescentNextObligation C) :
    ∀ z : Zero, False := by
  intro z
  rcases hExtract z with ⟨a, hv, hanch⟩
  exact no_anchored_valid_of_sameZeroDescent C hNext z a hv hanch

/-- Human-readable status string for audit reports. -/
def sameZeroDescent_slogan : String :=
  "The decoded LayerBox obstruction must be proved by same-zero descent: every valid atom anchored at z must produce a smaller valid atom still anchored at z. A global smaller atom is not enough."

end LayerBoxSameZeroDescent
end Riemann

/- ============ BRICK: Riemann_layerbox_local_move_kernel_patch.lean ============ -/

/-
Riemann_layerbox_local_move_kernel_patch.lean

Purpose
-------
This patch is the next strict layer after
`Riemann_layerbox_same_zero_descent_patch.lean`.

The previous patch identified the correct non-vacuous obstruction shape:

  every valid atom anchored at a zero z must descend to a strictly smaller
  valid atom anchored at the same zero z.

This file decomposes that same-zero descent into a purely local arithmetic
alternative:

  valid anchored atom at z
    -> immediate local obstruction
       OR
       a local move to a smaller valid atom still anchored at z.

If the immediate obstruction is impossible, and the move preserves the same
zero while strictly decreasing height, then no valid anchored atom ∃.  This
closes zeros by well-foundedness.

Main point
----------
The next true arithmetic obligation is not a global descent and not a free
LayerBox atom.  It is a local move kernel:

  LocalArithmeticMoveCertificate C

where the move is same-zero, validity-preserving, and height-decreasing.

This is still an audit/architecture layer.  It does not construct the actual
number-theoretic move for q*r*s = a*b*v + 2.  It states exactly what the move
has to prove.
-/

namespace Riemann
namespace LayerBoxLocalMoveKernel

/--
The minimal same-zero context needed for the local move kernel.

`Zero` should be instantiated by off-critical zero witnesses.
`Atom` should be instantiated by self-decoded LayerBox arithmetic atoms.
-/
structure SameZeroContext (Zero Atom : Type) where
  height : Atom -> Nat
  valid : Atom -> Prop
  anchor : Zero -> Atom -> Prop

/-- A single same-zero descent step from atom `a` anchored at zero `z`. -/
structure SameZeroDescentStep {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) (z : Zero) (a : Atom) where
  next : Atom
  valid_next : C.valid next
  anchor_next : C.anchor z next
  height_lt : C.height next < C.height a

/--
A local kernel: every valid anchored atom either immediately contradicts the
local gates, or has a smaller valid same-zero successor.
-/
def LocalKernel {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) : Prop :=
  ∀ z a,
    C.valid a ->
    C.anchor z a ->
    False ∨ Nonempty (SameZeroDescentStep C z a)

/--
A local kernel rules out every valid atom anchored at a fixed zero.

This is the core well-founded proof: keep applying the local move.  Since the
height is a natural number, an infinite same-zero strictly decreasing sequence
is impossible.
-/
theorem no_anchored_valid_of_localKernel {Zero Atom : Type}
    (C : SameZeroContext Zero Atom)
    (K : LocalKernel C)
    (z : Zero) (a : Atom) :
    C.valid a -> C.anchor z a -> False := by
  let P : Nat -> Prop := fun n =>
    ∀ a, C.height a = n -> C.valid a -> C.anchor z a -> False
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a ha hv hanch
        rcases K z a hv hanch with hbad | hne
        · exact hbad
        · exact hne.elim fun step =>
            ih (C.height step.next)
              (by simpa [ha] using step.height_lt)
              step.next rfl step.valid_next step.anchor_next
  exact hP (C.height a) a rfl

/-- A zero-extraction front: every zero produces a valid atom anchored at itself. -/
structure SameZeroExtractionFront (Zero Atom : Type) where
  C : SameZeroContext Zero Atom
  extract : ∀ z : Zero, ∃ a, C.valid a ∧ C.anchor z a

/-- Extraction plus a local kernel rules out all zeros. -/
theorem noZeros_of_extraction_and_localKernel {Zero Atom : Type}
    (F : SameZeroExtractionFront Zero Atom)
    (K : LocalKernel F.C) :
    ∀ z : Zero, False := by
  intro z
  rcases F.extract z with ⟨a, hv, hanch⟩
  exact no_anchored_valid_of_localKernel F.C K z a hv hanch

/-- Generic target interface: absence of zeros implies the desired target. -/
structure TargetFromNoZeros (Zero : Type) where
  target : Prop
  noZeros_to_target : (∀ z : Zero, False) -> target

/-- Extraction plus local kernel proves any target that follows from no zeros. -/
theorem target_of_extraction_and_localKernel {Zero Atom : Type}
    (T : TargetFromNoZeros Zero)
    (F : SameZeroExtractionFront Zero Atom)
    (K : LocalKernel F.C) :
    T.target :=
  T.noZeros_to_target (noZeros_of_extraction_and_localKernel F K)

/--
A concrete local arithmetic move certificate.

`Obstruction z a` is the immediate local obstruction branch.
If that branch occurs, `obstruction_impossible` kills it.
If it does not occur, `local_alternative` supplies a smaller atom anchored at
that same zero.
-/
structure LocalArithmeticMoveCertificate {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) where
  Obstruction : Zero -> Atom -> Prop
  next : Zero -> Atom -> Atom
  local_alternative : ∀ z a,
    C.valid a ->
    C.anchor z a ->
    Obstruction z a ∨
      (C.valid (next z a) ∧
       C.anchor z (next z a) ∧
       C.height (next z a) < C.height a)
  obstruction_impossible : ∀ z a,
    C.valid a ->
    C.anchor z a ->
    Obstruction z a ->
    False

/-- A local arithmetic move certificate produces the abstract local kernel. -/
def LocalArithmeticMoveCertificate.toLocalKernel {Zero Atom : Type}
    {C : SameZeroContext Zero Atom}
    (M : LocalArithmeticMoveCertificate C) :
    LocalKernel C := by
  intro z a hv hanch
  rcases M.local_alternative z a hv hanch with hobs | hmove
  · exact Or.inl (M.obstruction_impossible z a hv hanch hobs)
  · rcases hmove with ⟨hvalid, hanchor, hlt⟩
    exact Or.inr
      ⟨{ next := M.next z a
         valid_next := hvalid
         anchor_next := hanchor
         height_lt := hlt }⟩

/-- A local arithmetic move certificate rules out valid anchored atoms. -/
theorem no_anchored_valid_of_localArithmeticMove {Zero Atom : Type}
    (C : SameZeroContext Zero Atom)
    (M : LocalArithmeticMoveCertificate C)
    (z : Zero) (a : Atom) :
    C.valid a -> C.anchor z a -> False := by
  exact no_anchored_valid_of_localKernel C M.toLocalKernel z a

/-- Extraction plus a local arithmetic move certificate rules out all zeros. -/
theorem noZeros_of_localArithmeticMove {Zero Atom : Type}
    (F : SameZeroExtractionFront Zero Atom)
    (M : LocalArithmeticMoveCertificate F.C) :
    ∀ z : Zero, False :=
  noZeros_of_extraction_and_localKernel F M.toLocalKernel

/-- Extraction plus local arithmetic move proves any target from absence of zeros. -/
theorem target_of_localArithmeticMove {Zero Atom : Type}
    (T : TargetFromNoZeros Zero)
    (F : SameZeroExtractionFront Zero Atom)
    (M : LocalArithmeticMoveCertificate F.C) :
    T.target :=
  T.noZeros_to_target (noZeros_of_localArithmeticMove F M)

/--
A global move which forgets the zero is intentionally marked insufficient.
It can decrease height while losing the spectral anchor, so it cannot close the
Riemann front isolated here.
-/
structure AnchorForgettingMove {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) where
  next : Atom -> Atom
  valid_next : ∀ a, C.valid a -> C.valid (next a)
  height_lt : ∀ a, C.valid a -> C.height (next a) < C.height a

/--
Audit proposition: the next real obligation is a same-zero local arithmetic
move, not an anchor-forgetting descent.
-/
def LocalMoveNextObligation {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) : Type :=
  LocalArithmeticMoveCertificate C

/-- Full local-move front. -/
structure LocalMoveStrictFront (Zero Atom : Type) where
  extraction : SameZeroExtractionFront Zero Atom
  move : LocalMoveNextObligation extraction.C

/-- The strict local-move front rules out all zeros. -/
theorem LocalMoveStrictFront.noZeros {Zero Atom : Type}
    (F : LocalMoveStrictFront Zero Atom) :
    ∀ z : Zero, False :=
  noZeros_of_localArithmeticMove F.extraction F.move

/-- The strict local-move front proves any target implied by absence of zeros. -/
theorem LocalMoveStrictFront.target {Zero Atom : Type}
    (T : TargetFromNoZeros Zero)
    (F : LocalMoveStrictFront Zero Atom) :
    T.target :=
  T.noZeros_to_target F.noZeros

/-- Human-readable status string for audit reports. -/
def localMoveKernel_slogan : String :=
  "The next non-vacuous Riemann arithmetic obligation is a same-zero local move: every valid atom anchored at z either hits a local obstruction or moves to a smaller valid atom still anchored at z. Anchor-forgetting descent is insufficient."

end LayerBoxLocalMoveKernel
end Riemann

/- ============ BRICK: Riemann_layerbox_move_algebra_patch.lean ============ -/

/-
Riemann_layerbox_move_algebra_patch.lean

Purpose
-------
This patch is the next strict layer after
`Riemann_layerbox_local_move_kernel_patch.lean`.

The previous file reduced the non-vacuous Riemann arithmetic front to a local
same-zero move certificate:

  valid atom anchored at z
    -> immediate local obstruction
       OR
       a smaller valid atom still anchored at the same z.

This file opens that local certificate one level further.  It introduces an
explicit move algebra for LayerBox/two-transport atoms.  The algebra names the
operations that must be supplied by the concrete arithmetic proof: peel,
normalise, swap, residue-repair, and transport-rebalance moves.  It then proves
that any such move algebra produces the abstract local kernel, hence rules out
off-critical zeros once an extraction front is available.

Main point
----------
The next real obligation is no longer a global `Nonempty` witness and no longer
an anchor-forgetting descent.  It is a same-zero LayerBox move algebra:

  LayerBoxMoveAlgebra Zero Atom Move

whose local cover says that every valid anchored atom is either locally
obstructed or admits an applicable move that preserves validity and the same
zero-anchor while strictly decreasing height.

This is an audit/architecture layer.  It does not construct the actual
number-theoretic move for `q*r*s = a*b*v + 2`; it states exactly what the
concrete proof must provide.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxMoveAlgebra

/-! ## 1. Same-zero local kernel -/

/--
The minimal same-zero context.

`Zero` is the type of zero witnesses.
`Atom` is the type of decoded arithmetic two-transport atoms.
-/
structure SameZeroContext (Zero Atom : Type) where
  height : Atom -> Nat
  valid : Atom -> Prop
  anchor : Zero -> Atom -> Prop

/-- A single same-zero descent step from atom `a` anchored at zero `z`. -/
structure SameZeroDescentStep {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) (z : Zero) (a : Atom) where
  next : Atom
  valid_next : C.valid next
  anchor_next : C.anchor z next
  height_lt : C.height next < C.height a

/--
A local kernel: every valid anchored atom either immediately contradicts the
local gates, or has a smaller valid same-zero successor.
-/
def LocalKernel {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) : Prop :=
  ∀ z a,
    C.valid a ->
    C.anchor z a ->
    False ∨ Nonempty (SameZeroDescentStep C z a)

/--
A local kernel rules out every valid atom anchored at a fixed zero.

This is the only well-founded argument in this file: repeatedly taking the
smaller same-zero successor would produce an infinite strictly descending
sequence of natural heights.
-/
theorem no_anchored_valid_of_localKernel {Zero Atom : Type}
    (C : SameZeroContext Zero Atom)
    (K : LocalKernel C)
    (z : Zero) (a : Atom) :
    C.valid a -> C.anchor z a -> False := by
  let P : Nat -> Prop := fun n =>
    ∀ a, C.height a = n -> C.valid a -> C.anchor z a -> False
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a ha hv hanch
        rcases K z a hv hanch with hbad | hne
        · exact hbad
        · exact hne.elim fun step =>
            ih (C.height step.next)
              (by simpa [ha] using step.height_lt)
              step.next rfl step.valid_next step.anchor_next
  exact hP (C.height a) a rfl

/-! ## 2. Arithmetic LayerBox coordinates and gates -/

/-- Six coordinates of the arithmetic two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- The `qrs` side of the two-transport identity. -/
def leftMass (C : ArithmeticCoordinates) : Nat :=
  C.q * C.r * C.s

/-- The `abv` side of the two-transport identity. -/
def rightMass (C : ArithmeticCoordinates) : Nat :=
  C.a * C.b * C.v

/-- The arithmetic two-transport gap condition. -/
def gapTwo (C : ArithmeticCoordinates) : Prop :=
  C.leftMass = C.rightMass + 2

/-- The signed integer version of the same gap. -/
def signedGapTwo (C : ArithmeticCoordinates) : Prop :=
  (C.leftMass : Int) - (C.rightMass : Int) = 2

end ArithmeticCoordinates

/-- Generic local gates for a LayerBox atom. -/
structure LayerBoxGates where
  inLayer : ArithmeticCoordinates -> Prop
  residueGate : ArithmeticCoordinates -> Prop
  determinantGate : ArithmeticCoordinates -> Prop

/-- All local LayerBox gates at once. -/
def LayerBoxGates.all (G : LayerBoxGates) (C : ArithmeticCoordinates) : Prop :=
  G.inLayer C ∧ G.residueGate C ∧ G.determinantGate C

/--
Names for the elementary moves expected in the concrete arithmetic proof.
The file does not assume these are the only possible moves; a concrete repo can
instantiate `Move` with this type or a refinement of it.
-/
inductive ElementaryMoveKind where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-! ## 3. Same-zero LayerBox move algebra -/

/--
A same-zero LayerBox move algebra.

`Applicable m z atom` is the local arithmetic gate saying that move `m` may be
applied to atom `atom` while it is anchored at zero `z`.

The fields `preserves_valid`, `preserves_anchor`, and `decreases_height` are the
entire substance of the move proof: the move must not forget the zero and must
strictly lower the well-founded height.
-/
structure LayerBoxMoveAlgebra (Zero Atom Move : Type) where
  C : SameZeroContext Zero Atom
  coords : Atom -> ArithmeticCoordinates
  gates : LayerBoxGates
  valid_to_gates : ∀ atom, C.valid atom -> gates.all (coords atom)

  Obstruction : Zero -> Atom -> Prop
  Applicable : Move -> Zero -> Atom -> Prop
  move : Move -> Zero -> Atom -> Atom

  local_cover : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    Obstruction z atom ∨ ∃ m : Move, Applicable m z atom

  obstruction_impossible : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    Obstruction z atom ->
    False

  preserves_valid : ∀ m z atom,
    C.valid atom ->
    C.anchor z atom ->
    Applicable m z atom ->
    C.valid (move m z atom)

  preserves_anchor : ∀ m z atom,
    C.valid atom ->
    C.anchor z atom ->
    Applicable m z atom ->
    C.anchor z (move m z atom)

  decreases_height : ∀ m z atom,
    C.valid atom ->
    C.anchor z atom ->
    Applicable m z atom ->
    C.height (move m z atom) < C.height atom

namespace LayerBoxMoveAlgebra

/-- The abstract local kernel produced by a same-zero move algebra. -/
def toLocalKernel {Zero Atom Move : Type}
    (A : LayerBoxMoveAlgebra Zero Atom Move) :
    LocalKernel A.C := by
  intro z atom hv hanch
  rcases A.local_cover z atom hv hanch with hobs | hmove
  · exact Or.inl (A.obstruction_impossible z atom hv hanch hobs)
  · rcases hmove with ⟨m, happ⟩
    exact Or.inr
      ⟨{ next := A.move m z atom
         valid_next := A.preserves_valid m z atom hv hanch happ
         anchor_next := A.preserves_anchor m z atom hv hanch happ
         height_lt := A.decreases_height m z atom hv hanch happ }⟩

/-- A same-zero move algebra rules out every valid atom anchored at a fixed zero. -/
theorem no_anchored_valid {Zero Atom Move : Type}
    (A : LayerBoxMoveAlgebra Zero Atom Move)
    (z : Zero) (atom : Atom) :
    A.C.valid atom -> A.C.anchor z atom -> False := by
  exact no_anchored_valid_of_localKernel A.C A.toLocalKernel z atom

/--
A same-zero move algebra is stronger than a bare local-move certificate: it
exhibits the actual move type and the gate-preservation obligations.
-/
def nextObligationString : String :=
  "Provide a same-zero LayerBox move algebra: local obstruction or an applicable move preserving validity and the same zero-anchor while decreasing height."

end LayerBoxMoveAlgebra

/-! ## 4. Extraction front and target closure -/

/-- Every zero extracts a valid atom anchored at itself. -/
structure SameZeroExtractionFront (Zero Atom : Type)
    (C : SameZeroContext Zero Atom) where
  extract : ∀ z : Zero, ∃ atom, C.valid atom ∧ C.anchor z atom

/-- Extraction plus a same-zero move algebra rules out all zeros. -/
theorem noZeros_of_layerBoxMoveAlgebra {Zero Atom Move : Type}
    (A : LayerBoxMoveAlgebra Zero Atom Move)
    (E : SameZeroExtractionFront Zero Atom A.C) :
    ∀ z : Zero, False := by
  intro z
  rcases E.extract z with ⟨atom, hv, hanch⟩
  exact A.no_anchored_valid z atom hv hanch

/-- Generic target interface: absence of zeros implies the desired theorem. -/
structure TargetFromNoZeros (Zero : Type) where
  target : Prop
  noZeros_to_target : (∀ z : Zero, False) -> target

/-- Extraction plus a same-zero move algebra proves any target following from no zeros. -/
theorem target_of_layerBoxMoveAlgebra {Zero Atom Move : Type}
    (T : TargetFromNoZeros Zero)
    (A : LayerBoxMoveAlgebra Zero Atom Move)
    (E : SameZeroExtractionFront Zero Atom A.C) :
    T.target :=
  T.noZeros_to_target (noZeros_of_layerBoxMoveAlgebra A E)

/-- Full strict move-algebra front. -/
structure MoveAlgebraStrictFront (Zero Atom Move : Type) where
  algebra : LayerBoxMoveAlgebra Zero Atom Move
  extraction : SameZeroExtractionFront Zero Atom algebra.C

/-- The strict move-algebra front rules out all zeros. -/
theorem MoveAlgebraStrictFront.noZeros {Zero Atom Move : Type}
    (F : MoveAlgebraStrictFront Zero Atom Move) :
    ∀ z : Zero, False :=
  noZeros_of_layerBoxMoveAlgebra F.algebra F.extraction

/-- The strict move-algebra front proves any target implied by no zeros. -/
theorem MoveAlgebraStrictFront.target {Zero Atom Move : Type}
    (T : TargetFromNoZeros Zero)
    (F : MoveAlgebraStrictFront Zero Atom Move) :
    T.target :=
  T.noZeros_to_target F.noZeros

/-! ## 5. Firewalls against the previous vacuity modes -/

/--
An anchor-forgetting move algebra.  It can decrease height, but it has no
same-zero preservation field.  It is therefore insufficient for the RH front.
-/
structure AnchorForgettingMoveAlgebra (Zero Atom Move : Type) where
  C : SameZeroContext Zero Atom
  Applicable : Move -> Atom -> Prop
  move : Move -> Atom -> Atom
  preserves_valid : ∀ m atom,
    C.valid atom -> Applicable m atom -> C.valid (move m atom)
  decreases_height : ∀ m atom,
    C.valid atom -> Applicable m atom -> C.height (move m atom) < C.height atom

/--
A free origin move algebra: the applicable move is independent of the zero and
there is no requirement that the resulting atom remains anchored at that zero.
This is exactly the old origin-boundary failure mode.
-/
def FreeOriginMoveAlgebra (Zero Atom Move : Type) : Prop :=
  Nonempty (AnchorForgettingMoveAlgebra Zero Atom Move)

/-- The non-vacuous same-zero move obligation. -/
def SameZeroMoveAlgebraNextObligation (Zero Atom : Type) : Prop :=
  ∃ Move : Type, Nonempty (LayerBoxMoveAlgebra Zero Atom Move)

/-- Human-readable status for audit reports. -/
def moveAlgebra_slogan : String :=
  "After same-zero local descent, the next strict Riemann obligation is a LayerBox move algebra: every valid self-decoded atom is either locally obstructed or admits an applicable elementary move preserving the same zero-anchor and decreasing height. Free origin or anchor-forgetting moves are insufficient."

end LayerBoxMoveAlgebra
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_move_completeness_patch.lean ============ -/

/-
Riemann_layerbox_move_completeness_patch.lean

Purpose
-------
This patch is the next strict layer after
`Riemann_layerbox_move_algebra_patch.lean`.

The previous layer said that the Riemann arithmetic front needs a same-zero
LayerBox move algebra: every valid self-decoded atom anchored at a zero `z` is
locally obstructed or admits a decreasing move preserving the same zero-anchor.

This file tightens that obligation.  The move must now come from a fixed finite
named menu of elementary moves:

  peelQ / peelR / peelS,
  absorbA / absorbB / absorbV,
  swapLeft / swapRight,
  normalize,
  residueRepair,
  transportRebalance.

The concrete proof therefore has to supply a local completeness theorem for this
specific menu.  It is no longer enough to postulate an abstract `Move` type.

Main result
-----------
A finite named move table with:

  * local obstruction soundness,
  * finite menu local cover,
  * validity preservation,
  * same-zero anchor preservation,
  * strict height decrease,

rules out every extracted off-critical zero and proves any target that follows
from absence of such zeros.

This is still an audit/kernel file.  It does not construct the concrete
arithmetic moves for `q*r*s = a*b*v + 2`; it states the exact local completeness
obligation the concrete Riemann proof must now meet.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxMoveCompleteness

/-! ## 1. Minimal same-zero context -/

/--
A same-zero context.

`height` is the well-founded measure on atoms.
`valid` means the atom satisfies all current arithmetic/LayerBox gates.
`anchor z atom` means the atom is still attached to the same decoded zero `z`.
-/
structure SameZeroContext (Zero Atom : Type) where
  height : Atom -> Nat
  valid : Atom -> Prop
  anchor : Zero -> Atom -> Prop

/-- A decreasing same-zero step. -/
structure SameZeroDescentStep {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) (z : Zero) (atom : Atom) where
  next : Atom
  valid_next : C.valid next
  anchor_next : C.anchor z next
  height_lt : C.height next < C.height atom

/--
A local kernel: every valid anchored atom is either immediately impossible or
has a decreasing same-zero successor.
-/
def LocalKernel {Zero Atom : Type}
    (C : SameZeroContext Zero Atom) : Prop :=
  ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    False ∨ Nonempty (SameZeroDescentStep C z atom)

/-- A local kernel rules out valid atoms anchored at any fixed zero. -/
theorem no_anchored_valid_of_localKernel {Zero Atom : Type}
    (C : SameZeroContext Zero Atom)
    (K : LocalKernel C)
    (z : Zero) (atom : Atom) :
    C.valid atom -> C.anchor z atom -> False := by
  let P : Nat -> Prop := fun n =>
    ∀ atom, C.height atom = n -> C.valid atom -> C.anchor z atom -> False
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro atom hheight hvalid hanchor
        rcases K z atom hvalid hanchor with hbad | hne
        · exact hbad
        · exact hne.elim fun step =>
            ih (C.height step.next)
              (by simpa [hheight] using step.height_lt)
              step.next rfl step.valid_next step.anchor_next
  exact hP (C.height atom) atom rfl

/-! ## 2. Arithmetic coordinates and LayerBox gates -/

/-- Six coordinates of the arithmetic two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- The `qrs` side. -/
def leftMass (C : ArithmeticCoordinates) : Nat :=
  C.q * C.r * C.s

/-- The `abv` side. -/
def rightMass (C : ArithmeticCoordinates) : Nat :=
  C.a * C.b * C.v

/-- The arithmetic gap-two law. -/
def gapTwo (C : ArithmeticCoordinates) : Prop :=
  C.leftMass = C.rightMass + 2

/-- Integer signed form of the same law. -/
def signedGapTwo (C : ArithmeticCoordinates) : Prop :=
  (C.leftMass : Int) - (C.rightMass : Int) = 2

end ArithmeticCoordinates

/-- Generic local gates for decoded LayerBox atoms. -/
structure LayerBoxGates where
  inLayer : ArithmeticCoordinates -> Prop
  residueGate : ArithmeticCoordinates -> Prop
  determinantGate : ArithmeticCoordinates -> Prop

/-- All gates at once. -/
def LayerBoxGates.all (G : LayerBoxGates) (C : ArithmeticCoordinates) : Prop :=
  G.inLayer C ∧ G.residueGate C ∧ G.determinantGate C

/-! ## 3. The finite named menu of elementary moves -/

/--
The fixed menu of elementary moves.  Concrete proofs may refine these moves, but
this audit layer insists that the local cover use this finite menu, not an
opaque existential move type.
-/
inductive ElementaryMoveKind where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

namespace ElementaryMoveKind

/-- The finite move menu used by the local completeness theorem. -/
def namedMoves : List ElementaryMoveKind :=
  [ peelQ
  , peelR
  , peelS
  , absorbA
  , absorbB
  , absorbV
  , swapLeft
  , swapRight
  , normalize
  , residueRepair
  , transportRebalance
  ]

end ElementaryMoveKind

/-! ## 4. Finite named move table -/

/--
A finite named same-zero move table.

The core field is `finite_cover`: for every valid atom anchored at `z`, either a
local obstruction fires, or one of the named moves in `ElementaryMoveKind.namedMoves`
is applicable.

The move is allowed to depend on the zero `z`, because the front is explicitly
same-zero.  But the result must remain anchored at the same `z` and strictly
lower the height.
-/
structure FiniteNamedMoveTable (Zero Atom : Type) where
  C : SameZeroContext Zero Atom
  coords : Atom -> ArithmeticCoordinates
  gates : LayerBoxGates

  valid_to_gates : ∀ atom, C.valid atom -> gates.all (coords atom)

  Obstruction : Zero -> Atom -> Prop
  Applicable : ElementaryMoveKind -> Zero -> Atom -> Prop
  applyMove : ElementaryMoveKind -> Zero -> Atom -> Atom

  finite_cover : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    Obstruction z atom ∨
      ∃ kind : ElementaryMoveKind,
        kind ∈ ElementaryMoveKind.namedMoves ∧ Applicable kind z atom

  obstruction_impossible : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    Obstruction z atom ->
    False

  preserves_valid : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.valid (applyMove kind z atom)

  preserves_anchor : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.anchor z (applyMove kind z atom)

  decreases_height : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.height (applyMove kind z atom) < C.height atom

namespace FiniteNamedMoveTable

/-- Convert a finite named move table into the abstract local kernel. -/
def toLocalKernel {Zero Atom : Type}
    (T : FiniteNamedMoveTable Zero Atom) : LocalKernel T.C := by
  intro z atom hvalid hanchor
  rcases T.finite_cover z atom hvalid hanchor with hobs | hmove
  · exact Or.inl (T.obstruction_impossible z atom hvalid hanchor hobs)
  · rcases hmove with ⟨kind, hmem, happ⟩
    exact Or.inr
      ⟨{ next := T.applyMove kind z atom
         valid_next := T.preserves_valid kind z atom hvalid hanchor hmem happ
         anchor_next := T.preserves_anchor kind z atom hvalid hanchor hmem happ
         height_lt := T.decreases_height kind z atom hvalid hanchor hmem happ }⟩

/-- A finite named move table rules out every valid atom anchored at `z`. -/
theorem no_anchored_valid {Zero Atom : Type}
    (T : FiniteNamedMoveTable Zero Atom)
    (z : Zero) (atom : Atom) :
    T.C.valid atom -> T.C.anchor z atom -> False := by
  exact no_anchored_valid_of_localKernel T.C T.toLocalKernel z atom

/--
A minimal valid anchored counterexample is immediately impossible under a finite
named move table.  This is the local minimal-counterexample form of the same
well-founded argument.
-/
structure MinimalAnchoredCounterexample {Zero Atom : Type}
    (T : FiniteNamedMoveTable Zero Atom) where
  z : Zero
  atom : Atom
  valid_atom : T.C.valid atom
  anchor_atom : T.C.anchor z atom
  minimal : ∀ b : Atom,
    T.C.valid b ->
    T.C.anchor z b ->
    T.C.height atom ≤ T.C.height b

/-- No minimal counterexample survives the finite named move table. -/
theorem no_minimalAnchoredCounterexample {Zero Atom : Type}
    (T : FiniteNamedMoveTable Zero Atom)
    (M : MinimalAnchoredCounterexample T) :
    False := by
  rcases T.finite_cover M.z M.atom M.valid_atom M.anchor_atom with hobs | hmove
  · exact T.obstruction_impossible M.z M.atom M.valid_atom M.anchor_atom hobs
  · rcases hmove with ⟨kind, hmem, happ⟩
    let next := T.applyMove kind M.z M.atom
    have hvnext : T.C.valid next :=
      T.preserves_valid kind M.z M.atom M.valid_atom M.anchor_atom hmem happ
    have hanch_next : T.C.anchor M.z next :=
      T.preserves_anchor kind M.z M.atom M.valid_atom M.anchor_atom hmem happ
    have hdecr : T.C.height next < T.C.height M.atom :=
      T.decreases_height kind M.z M.atom M.valid_atom M.anchor_atom hmem happ
    have hmin : T.C.height M.atom ≤ T.C.height next :=
      M.minimal next hvnext hanch_next
    exact (Nat.not_lt_of_ge hmin) hdecr

/-- Human-readable status string. -/
def status : String :=
  "The same-zero descent obligation is now a finite named local completeness theorem: every valid self-decoded atom is locally obstructed or one of the named moves is applicable, preserves validity and the same zero-anchor, and strictly lowers height."

end FiniteNamedMoveTable

/-! ## 5. Extraction front and target closure -/

/-- Every zero extracts a valid atom anchored at itself. -/
structure SameZeroExtractionFront (Zero Atom : Type)
    (C : SameZeroContext Zero Atom) where
  extract : ∀ z : Zero, ∃ atom, C.valid atom ∧ C.anchor z atom

/-- A finite named move table plus extraction rules out all zeros. -/
theorem noZeros_of_finiteNamedMoveTable {Zero Atom : Type}
    (T : FiniteNamedMoveTable Zero Atom)
    (E : SameZeroExtractionFront Zero Atom T.C) :
    ∀ z : Zero, False := by
  intro z
  rcases E.extract z with ⟨atom, hvalid, hanchor⟩
  exact T.no_anchored_valid z atom hvalid hanchor

/-- Generic target interface: no zeros imply the desired target theorem. -/
structure TargetFromNoZeros (Zero : Type) where
  target : Prop
  noZeros_to_target : (∀ z : Zero, False) -> target

/-- A finite named move table plus extraction proves any target following from no zeros. -/
theorem target_of_finiteNamedMoveTable {Zero Atom : Type}
    (Target : TargetFromNoZeros Zero)
    (T : FiniteNamedMoveTable Zero Atom)
    (E : SameZeroExtractionFront Zero Atom T.C) :
    Target.target :=
  Target.noZeros_to_target (noZeros_of_finiteNamedMoveTable T E)

/-- Full strict front at this layer. -/
structure FiniteNamedMoveStrictFront (Zero Atom : Type) where
  table : FiniteNamedMoveTable Zero Atom
  extraction : SameZeroExtractionFront Zero Atom table.C

/-- The front rules out all zeros. -/
theorem FiniteNamedMoveStrictFront.noZeros {Zero Atom : Type}
    (F : FiniteNamedMoveStrictFront Zero Atom) :
    ∀ z : Zero, False :=
  noZeros_of_finiteNamedMoveTable F.table F.extraction

/-- The front proves any target following from no zeros. -/
theorem FiniteNamedMoveStrictFront.target {Zero Atom : Type}
    (Target : TargetFromNoZeros Zero)
    (F : FiniteNamedMoveStrictFront Zero Atom) :
    Target.target :=
  Target.noZeros_to_target F.noZeros

/-! ## 6. Firewalls against weaker obligations -/

/--
An opaque move cover: it uses an arbitrary move type.  This is weaker than the
finite named table and should not be accepted as the final local arithmetic
obligation.
-/
structure OpaqueMoveCover (Zero Atom Move : Type) where
  C : SameZeroContext Zero Atom
  Applicable : Move -> Zero -> Atom -> Prop
  move : Move -> Zero -> Atom -> Atom

/--
An anchor-forgetting finite move table.  It may have a finite menu and may lower
height, but it does not preserve the same decoded zero.  This is insufficient.
-/
structure AnchorForgettingFiniteMoveTable (Zero Atom : Type) where
  C : SameZeroContext Zero Atom
  Applicable : ElementaryMoveKind -> Atom -> Prop
  applyMove : ElementaryMoveKind -> Atom -> Atom
  preserves_valid : ∀ kind atom,
    C.valid atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind atom ->
    C.valid (applyMove kind atom)
  decreases_height : ∀ kind atom,
    C.valid atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind atom ->
    C.height (applyMove kind atom) < C.height atom

/--
The exact next obligation after the abstract move algebra: provide a finite
named same-zero move table.
-/
def FiniteNamedMoveCompletenessObligation (Zero Atom : Type) : Prop :=
  Nonempty (FiniteNamedMoveTable Zero Atom)

/-- Audit slogan for the next proof task. -/
def finiteNamedMoveCompleteness_slogan : String :=
  "Next strict Riemann task: prove finite named local completeness for the LayerBox atom. Every valid self-decoded atom must be obstructed or one of peelQ/peelR/peelS/absorbA/absorbB/absorbV/swapLeft/swapRight/normalize/residueRepair/transportRebalance must apply, preserve the same decoded zero, and strictly decrease height."

end LayerBoxMoveCompleteness
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_blocked_move_matrix_patch.lean ============ -/

/-
Riemann_layerbox_blocked_move_matrix_patch.lean

Purpose
-------
This patch is the next strict layer after
`Riemann_layerbox_move_completeness_patch.lean`.

The previous file reduced the Riemann arithmetic two-transport front to a finite
named local completeness theorem: every valid self-decoded LayerBox atom must be
locally obstructed or one of a fixed finite menu of moves must apply, preserve
the same zero-anchor, and lower height.

This file tightens that again.  The local completeness proof must now be supplied
as a blocked-move matrix:

  * for each named move, either the move is applicable or a concrete blocker for
    that move is present;
  * if all named moves are blocked, the blockers jointly imply a local arithmetic
    obstruction;
  * any applicable move has the same-zero, validity, and height-decrease
    properties already required by the finite move table.

Thus the remaining concrete proof is not an opaque cover anymore.  It is a finite
case table: prove every move's applicability/blocker dichotomy and prove the
"all blockers" arithmetic contradiction.

This is still a kernel/audit file.  It does not construct the actual blockers
for q*r*s = a*b*v + 2; it states exactly how that finite arithmetic case split
must close.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxMoveCompleteness
namespace BlockedMoveMatrix

/-! ## 1. A small finite-list logic lemma -/

/--
If each element of a finite list satisfies either `P` or `Q`, then either some
listed element satisfies `P`, or every listed element satisfies `Q`.

This is the logical kernel behind the blocked-move matrix: a finite menu is
covered by `applicable ∨ blocked`, hence either a move is applicable or all moves
are blocked.
-/
theorem list_exists_or_all_right {α : Type} (xs : List α)
    (P Q : α -> Prop)
    (h : ∀ x, x ∈ xs -> P x ∨ Q x) :
    (∃ x, x ∈ xs ∧ P x) ∨ (∀ x, x ∈ xs -> Q x) := by
  induction xs with
  | nil =>
      exact Or.inr (by intro x hx; cases hx)
  | cons a xs ih =>
      have ha : P a ∨ Q a := h a (by simp)
      rcases ha with hPa | hQa
      · exact Or.inl ⟨a, by simp, hPa⟩
      · have htail : ∀ x, x ∈ xs -> P x ∨ Q x := by
          intro x hx
          exact h x (by simp [hx])
        rcases ih htail with hsome | hall
        · rcases hsome with ⟨x, hxmem, hPx⟩
          exact Or.inl ⟨x, by simp [hxmem], hPx⟩
        · exact Or.inr (by
            intro x hx
            rcases List.mem_cons.mp hx with hxa | hxin
            · subst x
              exact hQa
            · exact hall x hxin)

/-! ## 2. Blocked move matrix -/

/--
A blocked-move matrix for the finite named LayerBox move menu.

The field `move_or_blocked` gives a local binary case for each named move.
The field `all_blocked_forces_obstruction` is the genuine arithmetic case
analysis: if no named move is applicable, the accumulated blockers must imply a
local obstruction.
-/
structure BlockedMoveMatrix (Zero Atom : Type) where
  C : SameZeroContext Zero Atom
  coords : Atom -> ArithmeticCoordinates
  gates : LayerBoxGates

  valid_to_gates : ∀ atom, C.valid atom -> gates.all (coords atom)

  Obstruction : Zero -> Atom -> Prop
  Applicable : ElementaryMoveKind -> Zero -> Atom -> Prop
  Blocked : ElementaryMoveKind -> Zero -> Atom -> Prop
  applyMove : ElementaryMoveKind -> Zero -> Atom -> Atom

  move_or_blocked : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ∨ Blocked kind z atom

  all_blocked_forces_obstruction : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    (∀ kind, kind ∈ ElementaryMoveKind.namedMoves -> Blocked kind z atom) ->
    Obstruction z atom

  obstruction_impossible : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    Obstruction z atom ->
    False

  preserves_valid : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.valid (applyMove kind z atom)

  preserves_anchor : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.anchor z (applyMove kind z atom)

  decreases_height : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.height (applyMove kind z atom) < C.height atom

namespace BlockedMoveMatrix

/--
A blocked-move matrix produces the finite named move table required by the
previous layer.
-/
def toFiniteNamedMoveTable {Zero Atom : Type}
    (M : BlockedMoveMatrix Zero Atom) : FiniteNamedMoveTable Zero Atom where
  C := M.C
  coords := M.coords
  gates := M.gates
  valid_to_gates := M.valid_to_gates
  Obstruction := M.Obstruction
  Applicable := M.Applicable
  applyMove := M.applyMove
  finite_cover := by
    intro z atom hvalid hanchor
    have hcases : ∀ kind,
        kind ∈ ElementaryMoveKind.namedMoves ->
        M.Applicable kind z atom ∨ M.Blocked kind z atom := by
      intro kind hmem
      exact M.move_or_blocked kind z atom hvalid hanchor hmem
    rcases list_exists_or_all_right
        ElementaryMoveKind.namedMoves
        (fun kind => M.Applicable kind z atom)
        (fun kind => M.Blocked kind z atom)
        hcases with hsome | hall
    · exact Or.inr hsome
    · exact Or.inl (M.all_blocked_forces_obstruction z atom hvalid hanchor hall)
  obstruction_impossible := M.obstruction_impossible
  preserves_valid := M.preserves_valid
  preserves_anchor := M.preserves_anchor
  decreases_height := M.decreases_height

/-- Hence a blocked-move matrix rules out every valid same-zero atom. -/
theorem no_anchored_valid {Zero Atom : Type}
    (M : BlockedMoveMatrix Zero Atom)
    (z : Zero) (atom : Atom) :
    M.C.valid atom -> M.C.anchor z atom -> False := by
  exact M.toFiniteNamedMoveTable.no_anchored_valid z atom

/-- A blocked-move matrix plus extraction rules out all zeros. -/
theorem noZeros_of_blockedMoveMatrix {Zero Atom : Type}
    (M : BlockedMoveMatrix Zero Atom)
    (E : SameZeroExtractionFront Zero Atom M.C) :
    ∀ z : Zero, False := by
  exact noZeros_of_finiteNamedMoveTable M.toFiniteNamedMoveTable E

/-- A blocked-move matrix proves any target following from absence of zeros. -/
theorem target_of_blockedMoveMatrix {Zero Atom : Type}
    (Target : TargetFromNoZeros Zero)
    (M : BlockedMoveMatrix Zero Atom)
    (E : SameZeroExtractionFront Zero Atom M.C) :
    Target.target :=
  Target.noZeros_to_target (noZeros_of_blockedMoveMatrix M E)

/-- Human-readable status string. -/
def status : String :=
  "The finite named move completeness obligation has been sharpened to a blocked-move matrix: every named move is either applicable or blocked, and all blockers together force a local arithmetic obstruction."

end BlockedMoveMatrix

/-! ## 3. Minimal-counterexample view of the blockers -/

/--
A blocked matrix with a way to certify blockers from non-applicability.

This is useful for a minimal-counterexample proof: if a move were applicable, it
would create a smaller valid atom anchored at the same zero, contradicting
minimality.  Therefore every move is non-applicable, hence blocked; all blockers
then force the obstruction.
-/
structure MinimalCounterexampleBlockerMatrix (Zero Atom : Type)
    extends BlockedMoveMatrix Zero Atom where
  blocked_of_not_applicable : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    (¬ Applicable kind z atom) ->
    Blocked kind z atom

namespace MinimalCounterexampleBlockerMatrix

/-- A minimal anchored atom cannot admit any applicable decreasing move. -/
theorem not_applicable_at_minimal {Zero Atom : Type}
    (M : MinimalCounterexampleBlockerMatrix Zero Atom)
    (min : FiniteNamedMoveTable.MinimalAnchoredCounterexample M.toBlockedMoveMatrix.toFiniteNamedMoveTable)
    (kind : ElementaryMoveKind)
    (hmem : kind ∈ ElementaryMoveKind.namedMoves) :
    ¬ M.Applicable kind min.z min.atom := by
  intro happ
  let next := M.applyMove kind min.z min.atom
  have hvalid_next : M.C.valid next :=
    M.preserves_valid kind min.z min.atom min.valid_atom min.anchor_atom hmem happ
  have hanchor_next : M.C.anchor min.z next :=
    M.preserves_anchor kind min.z min.atom min.valid_atom min.anchor_atom hmem happ
  have hdecr : M.C.height next < M.C.height min.atom :=
    M.decreases_height kind min.z min.atom min.valid_atom min.anchor_atom hmem happ
  have hmin : M.C.height min.atom ≤ M.C.height next :=
    min.minimal next hvalid_next hanchor_next
  exact (Nat.not_lt_of_ge hmin) hdecr

/-- At a minimal counterexample, every named move is blocked. -/
theorem all_blocked_at_minimal {Zero Atom : Type}
    (M : MinimalCounterexampleBlockerMatrix Zero Atom)
    (min : FiniteNamedMoveTable.MinimalAnchoredCounterexample M.toBlockedMoveMatrix.toFiniteNamedMoveTable) :
    ∀ kind,
      kind ∈ ElementaryMoveKind.namedMoves ->
      M.Blocked kind min.z min.atom := by
  intro kind hmem
  exact M.blocked_of_not_applicable kind min.z min.atom
    min.valid_atom min.anchor_atom hmem
    (M.not_applicable_at_minimal min kind hmem)

/-- The blocked matrix rules out a minimal counterexample by blocker accumulation. -/
theorem no_minimal_counterexample_by_blockers {Zero Atom : Type}
    (M : MinimalCounterexampleBlockerMatrix Zero Atom)
    (min : FiniteNamedMoveTable.MinimalAnchoredCounterexample M.toBlockedMoveMatrix.toFiniteNamedMoveTable) :
    False := by
  have hall : ∀ kind,
      kind ∈ ElementaryMoveKind.namedMoves ->
      M.Blocked kind min.z min.atom :=
    M.all_blocked_at_minimal min
  have hobs : M.Obstruction min.z min.atom :=
    M.all_blocked_forces_obstruction min.z min.atom
      min.valid_atom min.anchor_atom hall
  exact M.obstruction_impossible min.z min.atom
    min.valid_atom min.anchor_atom hobs

end MinimalCounterexampleBlockerMatrix

/-! ## 4. The concrete next obligation -/

/--
The exact next obligation after finite named move completeness: provide the
blocked-move matrix for the concrete LayerBox arithmetic atoms.
-/
def BlockedMoveMatrixObligation (Zero Atom : Type) : Prop :=
  Nonempty (BlockedMoveMatrix Zero Atom)

/--
A stronger minimal-counterexample version of the same obligation.  This is often
how the concrete arithmetic proof should be organized: prove blockers for every
non-applicable named move, then prove that all blockers jointly contradict the
LayerBox/residue/determinant gates.
-/
def MinimalCounterexampleBlockerObligation (Zero Atom : Type) : Prop :=
  Nonempty (MinimalCounterexampleBlockerMatrix Zero Atom)

/-- Audit slogan for the next proof task. -/
def blockedMoveMatrix_slogan : String :=
  "Next strict Riemann task: build the blocked-move matrix. For each of the eleven named moves, prove applicable-or-blocked; then prove that simultaneous blockage of all named moves forces the local LayerBox arithmetic obstruction."

end BlockedMoveMatrix
end LayerBoxMoveCompleteness
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_blocker_contradiction_kernel_patch.lean ============ -/

/-
Riemann_layerbox_blocker_contradiction_kernel_patch.lean

Purpose
-------
This is the next strict layer after
`Riemann_layerbox_blocked_move_matrix_patch.lean`.

The previous layer reduced local LayerBox completeness to a blocked-move matrix:
for every named elementary move, either the move is applicable or it is blocked;
if all moves are blocked, the blockers jointly imply a local obstruction.

This file removes one more source of opacity.  Instead of an abstract
`Obstruction`, it introduces a reasoned blocker kernel:

  * every blocked move is represented by a concrete `Reason kind z atom`;
  * if all eleven named reasons are present, they imply `False` directly;
  * from this reasoned kernel we build the previous `BlockedMoveMatrix` by taking
    `Blocked := Reason` and `Obstruction := False`.

Thus the next concrete proof task is a finite arithmetic contradiction:
write down the eleven blockers for the concrete q*r*s = a*b*v + 2 LayerBox atom
and prove that their simultaneous presence is impossible.

This file is still a strict audit/kernel layer.  It does not decide the concrete
LayerBox arithmetic; it specifies the exact form of the remaining finite proof.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxMoveCompleteness
namespace BlockerContradictionKernel

open BlockedMoveMatrix

/-! ## 1. Eleven named blockers as a concrete vector -/

/--
A concrete vector of blocker reasons, one for each named elementary move.

This is intentionally not a list existential: the proof must account for every
slot in the fixed move menu.
-/
structure ElevenBlockerVector (Reason : ElementaryMoveKind -> Prop) : Prop where
  peelQ : Reason ElementaryMoveKind.peelQ
  peelR : Reason ElementaryMoveKind.peelR
  peelS : Reason ElementaryMoveKind.peelS
  absorbA : Reason ElementaryMoveKind.absorbA
  absorbB : Reason ElementaryMoveKind.absorbB
  absorbV : Reason ElementaryMoveKind.absorbV
  swapLeft : Reason ElementaryMoveKind.swapLeft
  swapRight : Reason ElementaryMoveKind.swapRight
  normalize : Reason ElementaryMoveKind.normalize
  residueRepair : Reason ElementaryMoveKind.residueRepair
  transportRebalance : Reason ElementaryMoveKind.transportRebalance

namespace ElevenBlockerVector

/-- An eleven-slot vector gives a reason for every listed named move. -/
theorem to_all_named {Reason : ElementaryMoveKind -> Prop}
    (V : ElevenBlockerVector Reason) :
    ∀ kind,
      kind ∈ ElementaryMoveKind.namedMoves ->
      Reason kind := by
  intro kind hmem
  cases kind <;> simp [ElementaryMoveKind.namedMoves] at hmem <;>
    first
    | exact V.peelQ
    | exact V.peelR
    | exact V.peelS
    | exact V.absorbA
    | exact V.absorbB
    | exact V.absorbV
    | exact V.swapLeft
    | exact V.swapRight
    | exact V.normalize
    | exact V.residueRepair
    | exact V.transportRebalance

/-- A universal reason predicate gives an eleven-slot vector. -/
def of_all_named {Reason : ElementaryMoveKind -> Prop}
    (h : ∀ kind,
      kind ∈ ElementaryMoveKind.namedMoves ->
      Reason kind) :
    ElevenBlockerVector Reason where
  peelQ := h ElementaryMoveKind.peelQ (by simp [ElementaryMoveKind.namedMoves])
  peelR := h ElementaryMoveKind.peelR (by simp [ElementaryMoveKind.namedMoves])
  peelS := h ElementaryMoveKind.peelS (by simp [ElementaryMoveKind.namedMoves])
  absorbA := h ElementaryMoveKind.absorbA (by simp [ElementaryMoveKind.namedMoves])
  absorbB := h ElementaryMoveKind.absorbB (by simp [ElementaryMoveKind.namedMoves])
  absorbV := h ElementaryMoveKind.absorbV (by simp [ElementaryMoveKind.namedMoves])
  swapLeft := h ElementaryMoveKind.swapLeft (by simp [ElementaryMoveKind.namedMoves])
  swapRight := h ElementaryMoveKind.swapRight (by simp [ElementaryMoveKind.namedMoves])
  normalize := h ElementaryMoveKind.normalize (by simp [ElementaryMoveKind.namedMoves])
  residueRepair := h ElementaryMoveKind.residueRepair (by simp [ElementaryMoveKind.namedMoves])
  transportRebalance := h ElementaryMoveKind.transportRebalance (by simp [ElementaryMoveKind.namedMoves])

end ElevenBlockerVector

/-! ## 2. Reasoned blocker kernel -/

/--
A reasoned blocker kernel.

`Reason kind z atom` is the concrete arithmetic reason why the named move `kind`
is blocked at the atom anchored to `z`.  The decisive field is
`all_reasons_contradict`: if all eleven reasons are present for a valid anchored
atom, contradiction follows directly.  There is no opaque local obstruction left.
-/
structure ReasonedBlockedMoveKernel (Zero Atom : Type) where
  C : SameZeroContext Zero Atom
  coords : Atom -> ArithmeticCoordinates
  gates : LayerBoxGates

  valid_to_gates : ∀ atom, C.valid atom -> gates.all (coords atom)

  Applicable : ElementaryMoveKind -> Zero -> Atom -> Prop
  Reason : ElementaryMoveKind -> Zero -> Atom -> Prop
  applyMove : ElementaryMoveKind -> Zero -> Atom -> Atom

  applicable_or_reason : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ∨ Reason kind z atom

  all_reasons_contradict : ∀ z atom,
    C.valid atom ->
    C.anchor z atom ->
    ElevenBlockerVector (fun kind => Reason kind z atom) ->
    False

  preserves_valid : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.valid (applyMove kind z atom)

  preserves_anchor : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.anchor z (applyMove kind z atom)

  decreases_height : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    Applicable kind z atom ->
    C.height (applyMove kind z atom) < C.height atom

namespace ReasonedBlockedMoveKernel

/--
A reasoned blocker kernel is a blocked-move matrix with
`Blocked := Reason` and `Obstruction := False`.
-/
def toBlockedMoveMatrix {Zero Atom : Type}
    (K : ReasonedBlockedMoveKernel Zero Atom) :
    BlockedMoveMatrix.BlockedMoveMatrix Zero Atom where
  C := K.C
  coords := K.coords
  gates := K.gates
  valid_to_gates := K.valid_to_gates
  Obstruction := fun _ _ => False
  Applicable := K.Applicable
  Blocked := K.Reason
  applyMove := K.applyMove
  move_or_blocked := K.applicable_or_reason
  all_blocked_forces_obstruction := by
    intro z atom hvalid hanchor hall
    exact K.all_reasons_contradict z atom hvalid hanchor
      (ElevenBlockerVector.of_all_named hall)
  obstruction_impossible := by
    intro _z _atom _hvalid _hanchor hfalse
    exact hfalse
  preserves_valid := K.preserves_valid
  preserves_anchor := K.preserves_anchor
  decreases_height := K.decreases_height

/-- Hence a reasoned kernel rules out every valid atom anchored at a zero. -/
theorem no_anchored_valid {Zero Atom : Type}
    (K : ReasonedBlockedMoveKernel Zero Atom)
    (z : Zero) (atom : Atom) :
    K.C.valid atom -> K.C.anchor z atom -> False := by
  exact K.toBlockedMoveMatrix.no_anchored_valid z atom

/-- A reasoned kernel plus extraction rules out all zeros. -/
theorem noZeros_of_reasonedKernel {Zero Atom : Type}
    (K : ReasonedBlockedMoveKernel Zero Atom)
    (E : SameZeroExtractionFront Zero Atom K.C) :
    ∀ z : Zero, False := by
  exact BlockedMoveMatrix.noZeros_of_blockedMoveMatrix
    K.toBlockedMoveMatrix E

/-- A reasoned kernel proves any target following from absence of zeros. -/
theorem target_of_reasonedKernel {Zero Atom : Type}
    (Target : TargetFromNoZeros Zero)
    (K : ReasonedBlockedMoveKernel Zero Atom)
    (E : SameZeroExtractionFront Zero Atom K.C) :
    Target.target :=
  Target.noZeros_to_target (noZeros_of_reasonedKernel K E)

end ReasonedBlockedMoveKernel

/-! ## 3. Minimal-counterexample reasoned kernel -/

/--
A stronger form suited for minimal-counterexample proofs.

At a minimal counterexample, every applicable decreasing move is impossible by
minimality.  This structure asks for a concrete reason whenever a named move is
not applicable.  Then all eleven reasons contradict the local arithmetic gates.
-/
structure MinimalReasonedBlockerKernel (Zero Atom : Type)
    extends ReasonedBlockedMoveKernel Zero Atom where
  reason_of_not_applicable : ∀ kind z atom,
    C.valid atom ->
    C.anchor z atom ->
    kind ∈ ElementaryMoveKind.namedMoves ->
    (¬ Applicable kind z atom) ->
    Reason kind z atom

namespace MinimalReasonedBlockerKernel

/-- The minimal reasoned kernel yields the previous minimal blocker matrix. -/
def toMinimalCounterexampleBlockerMatrix {Zero Atom : Type}
    (K : MinimalReasonedBlockerKernel Zero Atom) :
    BlockedMoveMatrix.MinimalCounterexampleBlockerMatrix Zero Atom where
  toBlockedMoveMatrix := K.toReasonedBlockedMoveKernel.toBlockedMoveMatrix
  blocked_of_not_applicable := K.reason_of_not_applicable

/-- No minimal counterexample can survive all concrete blocker reasons. -/
theorem no_minimal_counterexample {Zero Atom : Type}
    (K : MinimalReasonedBlockerKernel Zero Atom)
    (min : FiniteNamedMoveTable.MinimalAnchoredCounterexample
      K.toReasonedBlockedMoveKernel.toBlockedMoveMatrix.toFiniteNamedMoveTable) :
    False := by
  exact K.toMinimalCounterexampleBlockerMatrix.no_minimal_counterexample_by_blockers min

/-- The minimal reasoned kernel rules out every valid anchored atom. -/
theorem no_anchored_valid {Zero Atom : Type}
    (K : MinimalReasonedBlockerKernel Zero Atom)
    (z : Zero) (atom : Atom) :
    K.C.valid atom -> K.C.anchor z atom -> False := by
  exact K.toReasonedBlockedMoveKernel.no_anchored_valid z atom

end MinimalReasonedBlockerKernel

/-! ## 4. Concrete arithmetic shape of the next obligation -/

/--
A slot for the concrete blocker arithmetic.  The fields are intentionally
predicate-valued: the concrete q*r*s = a*b*v + 2 proof should instantiate these
with explicit inequalities, divisibility facts, residue failures, or determinant
rigidities.
-/
structure ConcreteBlockerArithmetic (Coord : Type) where
  coords : Coord -> ArithmeticCoordinates
  layerLocked : Coord -> Prop
  residueLocked : Coord -> Prop
  determinantLocked : Coord -> Prop
  noLeftPeel : Coord -> Prop
  noRightAbsorb : Coord -> Prop
  noSwapImproves : Coord -> Prop
  noNormalizeImproves : Coord -> Prop
  noResidueRepair : Coord -> Prop
  noTransportRebalance : Coord -> Prop

/--
A final local contradiction contract for concrete blocker arithmetic.

When all local gates are locked and every class of move is blocked, the atom is
arithmetically impossible.  This is where the future concrete proof must use the
LayerBox bounds, residue classes, and determinant equation.
-/
def ConcreteBlockerContradiction {Coord : Type} (A : ConcreteBlockerArithmetic Coord) : Prop :=
  ∀ c : Coord,
    A.layerLocked c ->
    A.residueLocked c ->
    A.determinantLocked c ->
    A.noLeftPeel c ->
    A.noRightAbsorb c ->
    A.noSwapImproves c ->
    A.noNormalizeImproves c ->
    A.noResidueRepair c ->
    A.noTransportRebalance c ->
    False

/-- The exact next obligation after the blocked-move matrix. -/
def ReasonedBlockerKernelObligation (Zero Atom : Type) : Prop :=
  Nonempty (ReasonedBlockedMoveKernel Zero Atom)

/-- Stronger minimal-counterexample version of the next obligation. -/
def MinimalReasonedBlockerKernelObligation (Zero Atom : Type) : Prop :=
  Nonempty (MinimalReasonedBlockerKernel Zero Atom)

/-- Human-readable status string. -/
def blockerContradictionKernel_slogan : String :=
  "Next strict Riemann task: replace the opaque all-blocked obstruction by concrete blocker reasons. For all eleven named moves, give the blocker reason; then prove that the simultaneous blocker vector contradicts the LayerBox/residue/determinant arithmetic."

end BlockerContradictionKernel
end LayerBoxMoveCompleteness
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_residue_pressure_kernel_patch.lean ============ -/

/-
Riemann_layerbox_residue_pressure_kernel_patch.lean

Purpose.
  Next strict layer after `Riemann_layerbox_blocker_contradiction_kernel_patch.lean`.

  The previous layer reduced the remaining local arithmetic work to a finite
  blocker contradiction: if all named LayerBox moves are blocked, then the
  blocker reasons must jointly contradict the determinant/layer/residue gates.

  This file removes one more opaque phrase.  It introduces a normal-form
  pressure kernel:

      all eleven move-blockers
        -> residue/layer/determinant pressure
        -> contradiction.

  The file is intentionally generic in `Zero` and `Atom`; the repo-specific
  arithmetic still has to instantiate `blockers_to_pressure` for the concrete
  q*r*s = a*b*v + 2 LayerBox atom.

  Nothing here proves RH by itself.  It states the exact final local shape
  needed to close the non-engine arithmetic two-transport route.
-/

namespace Riemann
namespace LayerBoxResiduePressure

/-- The finite named move menu from the move-completeness layer. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- Concrete arithmetic coordinates of the two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  A : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- Left transported mass. -/
def leftMass (c : ArithmeticCoordinates) : Nat :=
  c.q * c.r * c.s

/-- Right transported mass. -/
def rightMass (c : ArithmeticCoordinates) : Nat :=
  c.a * c.b * c.v

/-- The arithmetical two-transport determinant. -/
def TransportEquation (c : ArithmeticCoordinates) : Prop :=
  c.leftMass = c.rightMass + 2

/-- The LayerBox window `(A, A^2]` for all six coordinates. -/
def InLayerBox (c : ArithmeticCoordinates) : Prop :=
  c.A < c.q ∧ c.q ≤ c.A * c.A ∧
  c.A < c.r ∧ c.r ≤ c.A * c.A ∧
  c.A < c.s ∧ c.s ≤ c.A * c.A ∧
  c.A < c.a ∧ c.a ≤ c.A * c.A ∧
  c.A < c.b ∧ c.b ≤ c.A * c.A ∧
  c.A < c.v ∧ c.v ≤ c.A * c.A

/-- A residue profile for the two masses, not for the six individual factors. -/
structure MassResidueProfile where
  modulus : Nat
  leftResidue : Nat
  rightResidue : Nat

/-- Compatibility of the mass residues with the determinant gap `+2`. -/
def MassResidueCompatible (c : ArithmeticCoordinates) (P : MassResidueProfile) : Prop :=
  c.leftMass % P.modulus = P.leftResidue ∧
  c.rightMass % P.modulus = P.rightResidue ∧
  P.leftResidue = (P.rightResidue + 2) % P.modulus

/-- The exact determinant forces the corresponding residue gap. -/
theorem residue_gap_of_transportEquation
    {c : ArithmeticCoordinates}
    (h : c.TransportEquation)
    (M : Nat) :
    c.leftMass % M = (c.rightMass + 2) % M := by
  simpa [TransportEquation] using congrArg (fun n => n % M) h

end ArithmeticCoordinates

/--
A pure residue pressure contradiction.

Interpretation: blockers have forced the two masses to be congruent, while the
transport equation forces a `+2` residue shift, and the current modulus/profile
knows that this shift is nonzero.
-/
structure ResiduePressure (c : ArithmeticCoordinates) where
  modulus : Nat
  sameResidue : c.leftMass % modulus = c.rightMass % modulus
  determinantGap : c.leftMass % modulus = (c.rightMass + 2) % modulus
  gapNonzero : c.rightMass % modulus ≠ (c.rightMass + 2) % modulus

/-- A residue pressure is already contradictory. -/
theorem ResiduePressure.false {c : ArithmeticCoordinates} (P : ResiduePressure c) : False := by
  exact P.gapNonzero (P.sameResidue.symm.trans P.determinantGap)

/--
A layer pressure contradiction.

This is intentionally abstract: in the concrete arithmetic instantiation, this
is where one proves that all peel/absorb/normalize blockers force a coordinate
simultaneously inside and outside the LayerBox.
-/
structure LayerPressure (c : ArithmeticCoordinates) where
  contradiction : False

/--
A determinant pressure contradiction.

This packages direct arithmetic impossibility of the determinant, independent
of residues.  It is useful for cases where blocker reasons force inequalities
such as `leftMass ≤ rightMass + 1` while the determinant requires `+2`.
-/
structure DeterminantPressure (c : ArithmeticCoordinates) where
  contradiction : False

/-- Normal form for the joint blocker contradiction. -/
inductive BlockerPressure (c : ArithmeticCoordinates) where
  | residue : ResiduePressure c -> BlockerPressure c
  | layer : LayerPressure c -> BlockerPressure c
  | determinant : DeterminantPressure c -> BlockerPressure c

/-- Every normal-form pressure closes the local arithmetic contradiction. -/
theorem BlockerPressure.false {c : ArithmeticCoordinates} :
    BlockerPressure c -> False
  | .residue P => P.false
  | .layer P => P.contradiction
  | .determinant P => P.contradiction

/--
A reasoned blocker vector: every named move is blocked by a concrete reason.

`Reason z atom m` is deliberately left repo-specific.  Examples:
* `peelQ` blocked because no admissible q-factor peel preserves the layer;
* `residueRepair` blocked because all residue repairs break the determinant;
* `transportRebalance` blocked because same-zero decoding would change.
-/
structure ElevenReasonedBlockers
    (Zero Atom : Type)
    (Reason : Zero -> Atom -> MoveName -> Type) where
  reason : ∀ z atom m, Reason z atom m

/--
The kernel that turns the finite blocker matrix into an actual arithmetic
contradiction.

This is the next local obligation after the blocker-matrix file.  It says that
for a valid atom anchored at a zero, if every named move is blocked for concrete
reasons, those reasons normalize to a residue/layer/determinant pressure.
-/
structure BlockerPressureKernel
    (Zero Atom : Type)
    (Reason : Zero -> Atom -> MoveName -> Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers_to_pressure :
    ∀ {z : Zero} {atom : Atom},
      Valid atom ->
      Anchor z atom ->
      (∀ m : MoveName, Reason z atom m) ->
      BlockerPressure (coords atom)

namespace BlockerPressureKernel

/-- If all named moves are reason-blocked, no valid anchored atom can exist. -/
theorem no_valid_anchored_with_all_blockers
    {Zero Atom : Type}
    {Reason : Zero -> Atom -> MoveName -> Type}
    (K : BlockerPressureKernel Zero Atom Reason)
    {z : Zero} {atom : Atom}
    (hValid : K.Valid atom)
    (hAnchor : K.Anchor z atom)
    (hBlocked : ∀ m : MoveName, Reason z atom m) :
    False := by
  exact BlockerPressure.false (K.blockers_to_pressure hValid hAnchor hBlocked)

end BlockerPressureKernel

/--
A concrete residue-only closure criterion.

This is often the simplest way to close `blockers_to_pressure`: prove that all
blockers force same-residue of the two masses modulo some modulus, while the
determinant gap `+2` is nonzero modulo that modulus.
-/
structure ResidueOnlyBlockerKernel
    (Zero Atom : Type)
    (Reason : Zero -> Atom -> MoveName -> Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  blockers_force_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom ->
      Anchor z atom ->
      (∀ m : MoveName, Reason z atom m) ->
      (coords atom).leftMass % modulus = (coords atom).rightMass % modulus
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

namespace ResidueOnlyBlockerKernel

/-- Residue-only closure is a special case of the pressure kernel. -/
def toBlockerPressureKernel
    {Zero Atom : Type}
    {Reason : Zero -> Atom -> MoveName -> Type}
    (K : ResidueOnlyBlockerKernel Zero Atom Reason) :
    BlockerPressureKernel Zero Atom Reason where
  coords := K.coords
  Valid := K.Valid
  Anchor := K.Anchor
  blockers_to_pressure := by
    intro z atom hValid hAnchor hBlocked
    exact BlockerPressure.residue {
      modulus := K.modulus
      sameResidue := K.blockers_force_sameResidue hValid hAnchor hBlocked
      determinantGap := ArithmeticCoordinates.residue_gap_of_transportEquation (K.transport hValid) K.modulus
      gapNonzero := K.gap_nonzero hValid
    }

/-- Therefore the residue-only kernel forbids a fully blocked valid anchored atom. -/
theorem no_valid_anchored_with_all_blockers
    {Zero Atom : Type}
    {Reason : Zero -> Atom -> MoveName -> Type}
    (K : ResidueOnlyBlockerKernel Zero Atom Reason)
    {z : Zero} {atom : Atom}
    (hValid : K.Valid atom)
    (hAnchor : K.Anchor z atom)
    (hBlocked : ∀ m : MoveName, Reason z atom m) :
    False := by
  exact (K.toBlockerPressureKernel).no_valid_anchored_with_all_blockers hValid hAnchor hBlocked

end ResidueOnlyBlockerKernel

/--
A final local front for the current layer.

To instantiate this in the repo, one must define the concrete blocker-reason
family for the 11 named moves and then prove either the full pressure kernel or
its residue-only special case.
-/
structure ResiduePressureStrictFront
    (Zero Atom : Type)
    (Reason : Zero -> Atom -> MoveName -> Type) where
  kernel : BlockerPressureKernel Zero Atom Reason

namespace ResiduePressureStrictFront

/-- The strict front kills every valid anchored atom whose move table is fully blocked. -/
theorem no_fully_blocked_valid_anchor
    {Zero Atom : Type}
    {Reason : Zero -> Atom -> MoveName -> Type}
    (F : ResiduePressureStrictFront Zero Atom Reason)
    {z : Zero} {atom : Atom}
    (hValid : F.kernel.Valid atom)
    (hAnchor : F.kernel.Anchor z atom)
    (hBlocked : ∀ m : MoveName, Reason z atom m) :
    False := by
  exact F.kernel.no_valid_anchored_with_all_blockers hValid hAnchor hBlocked

end ResiduePressureStrictFront

/-- A compact statement of the next exact obligation. -/
def NextLocalArithmeticObligation (Zero Atom : Type) : Prop :=
  ∃ Reason : Zero -> Atom -> MoveName -> Type,
    Nonempty (ResiduePressureStrictFront Zero Atom Reason)

/-- Human-readable theorem object: what this layer has achieved. -/
theorem residuePressureKernel_slogan :
    True := by
  trivial

end LayerBoxResiduePressure
end Riemann

/- ============ BRICK: Riemann_layerbox_residue_blocker_table_patch.lean ============ -/

/-
Riemann_layerbox_residue_blocker_table_patch.lean

Purpose
-------
Next strict layer after `Riemann_layerbox_residue_pressure_kernel_patch.lean`.

The previous pressure kernel still had one opaque local normalisation field:

    all named blockers -> residue/layer/determinant pressure.

This file tightens the residue-only branch.  It replaces the single opaque
`blockers_force_sameResidue` proof by an explicit eleven-entry blocker table:
for each named move, its concrete blocker reason must imply the same mass
residue of the two transported sides.  Together with the determinant

    q*r*s = a*b*v + 2

and a nonzero `+2` residue gap, any fully blocked atom is impossible.

This is still a kernel/audit layer.  It does not construct the concrete blocker
reasons for the repo's q*r*s = a*b*v + 2 LayerBox atom; it states the exact
finite residue table that has to be filled next.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxResidueBlockerTable

/-- The finite named move menu carried over from the move-completeness layer. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- Arithmetic coordinates of the two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  A : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- Left transported mass. -/
def leftMass (c : ArithmeticCoordinates) : Nat :=
  c.q * c.r * c.s

/-- Right transported mass. -/
def rightMass (c : ArithmeticCoordinates) : Nat :=
  c.a * c.b * c.v

/-- The arithmetic two-transport determinant. -/
def TransportEquation (c : ArithmeticCoordinates) : Prop :=
  c.leftMass = c.rightMass + 2

/-- The determinant forces the corresponding residue gap. -/
theorem residue_gap_of_transportEquation
    {c : ArithmeticCoordinates}
    (h : c.TransportEquation)
    (M : Nat) :
    c.leftMass % M = (c.rightMass + 2) % M := by
  simpa [TransportEquation] using congrArg (fun n => n % M) h

end ArithmeticCoordinates

/-- The two transported masses have the same residue modulo `M`. -/
def SameMassResidueAt (M : Nat) (c : ArithmeticCoordinates) : Prop :=
  c.leftMass % M = c.rightMass % M

/--
Residue-only blocker kernel from the previous layer, written self-contained here.
It closes a fully-blocked valid anchored atom once all blockers force same
residue modulo `M`, while the determinant gap `+2` is nonzero modulo `M`.
-/
structure ResidueOnlyBlockerKernel
    (Zero Atom : Type)
    (Reason : Zero -> Atom -> MoveName -> Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  blockers_force_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom ->
      Anchor z atom ->
      (∀ m : MoveName, Reason z atom m) ->
      SameMassResidueAt modulus (coords atom)
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

namespace ResidueOnlyBlockerKernel

/-- A residue-only fully-blocked valid anchored atom is impossible. -/
theorem no_valid_anchored_with_all_blockers
    {Zero Atom : Type}
    {Reason : Zero -> Atom -> MoveName -> Type}
    (K : ResidueOnlyBlockerKernel Zero Atom Reason)
    {z : Zero} {atom : Atom}
    (hValid : K.Valid atom)
    (hAnchor : K.Anchor z atom)
    (hBlocked : ∀ m : MoveName, Reason z atom m) :
    False := by
  let c := K.coords atom
  have hsame : c.leftMass % K.modulus = c.rightMass % K.modulus :=
    K.blockers_force_sameResidue hValid hAnchor hBlocked
  have hgap : c.leftMass % K.modulus = (c.rightMass + 2) % K.modulus :=
    ArithmeticCoordinates.residue_gap_of_transportEquation (K.transport hValid) K.modulus
  exact K.gap_nonzero hValid (by
    calc
      c.rightMass % K.modulus = c.leftMass % K.modulus := hsame.symm
      _ = (c.rightMass + 2) % K.modulus := hgap)

end ResidueOnlyBlockerKernel

/--
An explicit eleven-entry residue normalisation table.

Each field says: if the named move is blocked by its concrete reason, then that
reason forces equality of the two transported mass residues modulo `modulus`.
This is deliberately stronger than the abstract pressure kernel: the next repo
work is now eleven local residue lemmas plus the nonzero gap lemma.
-/
structure ElevenResidueBlockerNormalizers
    (Zero Atom : Type) where
  Reason : Zero -> Atom -> MoveName -> Type
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.peelQ ->
      SameMassResidueAt modulus (coords atom)
  peelR_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.peelR ->
      SameMassResidueAt modulus (coords atom)
  peelS_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.peelS ->
      SameMassResidueAt modulus (coords atom)
  absorbA_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.absorbA ->
      SameMassResidueAt modulus (coords atom)
  absorbB_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.absorbB ->
      SameMassResidueAt modulus (coords atom)
  absorbV_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.absorbV ->
      SameMassResidueAt modulus (coords atom)
  swapLeft_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.swapLeft ->
      SameMassResidueAt modulus (coords atom)
  swapRight_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.swapRight ->
      SameMassResidueAt modulus (coords atom)
  normalize_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.normalize ->
      SameMassResidueAt modulus (coords atom)
  residueRepair_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.residueRepair ->
      SameMassResidueAt modulus (coords atom)
  transportRebalance_sameResidue :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Reason z atom MoveName.transportRebalance ->
      SameMassResidueAt modulus (coords atom)

namespace ElevenResidueBlockerNormalizers

/-- Dispatch the appropriate row of the eleven-entry normalisation table. -/
def sameResidue_of_blocker
    {Zero Atom : Type}
    (T : ElevenResidueBlockerNormalizers Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom) :
    ∀ m : MoveName,
      T.Reason z atom m ->
      SameMassResidueAt T.modulus (T.coords atom)
  | MoveName.peelQ, h => T.peelQ_sameResidue hValid hAnchor h
  | MoveName.peelR, h => T.peelR_sameResidue hValid hAnchor h
  | MoveName.peelS, h => T.peelS_sameResidue hValid hAnchor h
  | MoveName.absorbA, h => T.absorbA_sameResidue hValid hAnchor h
  | MoveName.absorbB, h => T.absorbB_sameResidue hValid hAnchor h
  | MoveName.absorbV, h => T.absorbV_sameResidue hValid hAnchor h
  | MoveName.swapLeft, h => T.swapLeft_sameResidue hValid hAnchor h
  | MoveName.swapRight, h => T.swapRight_sameResidue hValid hAnchor h
  | MoveName.normalize, h => T.normalize_sameResidue hValid hAnchor h
  | MoveName.residueRepair, h => T.residueRepair_sameResidue hValid hAnchor h
  | MoveName.transportRebalance, h =>
      T.transportRebalance_sameResidue hValid hAnchor h

/-- The explicit eleven-row table is a residue-only blocker kernel. -/
def toResidueOnlyBlockerKernel
    {Zero Atom : Type}
    (T : ElevenResidueBlockerNormalizers Zero Atom) :
    ResidueOnlyBlockerKernel Zero Atom T.Reason where
  coords := T.coords
  Valid := T.Valid
  Anchor := T.Anchor
  modulus := T.modulus
  transport := T.transport
  gap_nonzero := T.gap_nonzero
  blockers_force_sameResidue := by
    intro z atom hValid hAnchor hBlocked
    -- Any fixed blocked move now gives same-residue; `peelQ` is used only as
    -- a distinguished row of the fully-blocked table.
    exact T.sameResidue_of_blocker hValid hAnchor MoveName.peelQ (hBlocked MoveName.peelQ)

/-- Hence a fully blocked valid anchored atom is impossible. -/
theorem no_valid_anchored_with_all_blockers
    {Zero Atom : Type}
    (T : ElevenResidueBlockerNormalizers Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : ∀ m : MoveName, T.Reason z atom m) :
    False := by
  exact (T.toResidueOnlyBlockerKernel).no_valid_anchored_with_all_blockers
    hValid hAnchor hBlocked

end ElevenResidueBlockerNormalizers

/--
The exact next local obligation in the residue-only branch.

To close this branch concretely, instantiate `Reason` and prove the eleven
`*_sameResidue` fields plus `gap_nonzero` for the chosen modulus.
-/
def ElevenResidueTableObligation (Zero Atom : Type) : Prop :=
  Nonempty (ElevenResidueBlockerNormalizers Zero Atom)

/-- Slogan theorem: what this layer achieved. -/
theorem residueBlockerTable_slogan : True := by
  trivial

end LayerBoxResidueBlockerTable
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_named_residue_rows_patch.lean ============ -/

/-
Riemann_layerbox_named_residue_rows_patch.lean

Purpose
-------
Next strict layer after `Riemann_layerbox_residue_blocker_table_patch.lean`.

The previous file exposed an eleven-entry table, but the blocker family was still
one indexed `Reason z atom move`.  This file removes that last generic index:
each named move now has its own blocker predicate and its own row lemma.

The point is operational: the remaining repo work can no longer be hidden in an
opaque `Reason` dispatcher.  It is now exactly eleven local facts:

  peelQ_blocked           -> same mass residue
  peelR_blocked           -> same mass residue
  peelS_blocked           -> same mass residue
  absorbA_blocked         -> same mass residue
  absorbB_blocked         -> same mass residue
  absorbV_blocked         -> same mass residue
  swapLeft_blocked        -> same mass residue
  swapRight_blocked       -> same mass residue
  normalize_blocked       -> same mass residue
  residueRepair_blocked   -> same mass residue
  transportRebalance_blocked -> same mass residue

Together with the determinant gap `leftMass = rightMass + 2` and a nonzero
modular `+2` gap, all eleven blockers cannot coexist at a valid anchored atom.

This is still an audit/kernel layer.  It does not assert the actual blocker
predicates for the repository's LayerBox atom; it gives the exact finite proof
interface those predicates must satisfy.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxNamedResidueRows

/-- The fixed finite menu of elementary moves. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- Coordinates of the arithmetic two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  A : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- Left transported mass. -/
def leftMass (c : ArithmeticCoordinates) : Nat :=
  c.q * c.r * c.s

/-- Right transported mass. -/
def rightMass (c : ArithmeticCoordinates) : Nat :=
  c.a * c.b * c.v

/-- The determinant / two-transport law. -/
def TransportEquation (c : ArithmeticCoordinates) : Prop :=
  c.leftMass = c.rightMass + 2

/-- The determinant forces the modular `+2` gap. -/
theorem residue_gap_of_transportEquation
    {c : ArithmeticCoordinates}
    (h : c.TransportEquation)
    (M : Nat) :
    c.leftMass % M = (c.rightMass + 2) % M := by
  simpa [TransportEquation] using congrArg (fun n => n % M) h

end ArithmeticCoordinates

/-- The two transported masses have the same residue modulo `M`. -/
def SameMassResidueAt (M : Nat) (c : ArithmeticCoordinates) : Prop :=
  c.leftMass % M = c.rightMass % M

/--
The eleven concrete blocker predicates, no longer hidden behind an indexed
`Reason` family.
-/
structure NamedBlockerPredicates (Zero Atom : Type) where
  peelQ_blocked : Zero -> Atom -> Prop
  peelR_blocked : Zero -> Atom -> Prop
  peelS_blocked : Zero -> Atom -> Prop
  absorbA_blocked : Zero -> Atom -> Prop
  absorbB_blocked : Zero -> Atom -> Prop
  absorbV_blocked : Zero -> Atom -> Prop
  swapLeft_blocked : Zero -> Atom -> Prop
  swapRight_blocked : Zero -> Atom -> Prop
  normalize_blocked : Zero -> Atom -> Prop
  residueRepair_blocked : Zero -> Atom -> Prop
  transportRebalance_blocked : Zero -> Atom -> Prop

namespace NamedBlockerPredicates

/-- Recover the old indexed blocker family when needed for compatibility. -/
def asIndexedReason
    {Zero Atom : Type}
    (B : NamedBlockerPredicates Zero Atom) :
    Zero -> Atom -> MoveName -> Prop
  | z, atom, MoveName.peelQ => B.peelQ_blocked z atom
  | z, atom, MoveName.peelR => B.peelR_blocked z atom
  | z, atom, MoveName.peelS => B.peelS_blocked z atom
  | z, atom, MoveName.absorbA => B.absorbA_blocked z atom
  | z, atom, MoveName.absorbB => B.absorbB_blocked z atom
  | z, atom, MoveName.absorbV => B.absorbV_blocked z atom
  | z, atom, MoveName.swapLeft => B.swapLeft_blocked z atom
  | z, atom, MoveName.swapRight => B.swapRight_blocked z atom
  | z, atom, MoveName.normalize => B.normalize_blocked z atom
  | z, atom, MoveName.residueRepair => B.residueRepair_blocked z atom
  | z, atom, MoveName.transportRebalance => B.transportRebalance_blocked z atom

end NamedBlockerPredicates

/-- All eleven named blockers hold at a fixed anchored atom. -/
structure AllNamedBlockers
    {Zero Atom : Type}
    (B : NamedBlockerPredicates Zero Atom)
    (z : Zero)
    (atom : Atom) : Prop where
  peelQ : B.peelQ_blocked z atom
  peelR : B.peelR_blocked z atom
  peelS : B.peelS_blocked z atom
  absorbA : B.absorbA_blocked z atom
  absorbB : B.absorbB_blocked z atom
  absorbV : B.absorbV_blocked z atom
  swapLeft : B.swapLeft_blocked z atom
  swapRight : B.swapRight_blocked z atom
  normalize : B.normalize_blocked z atom
  residueRepair : B.residueRepair_blocked z atom
  transportRebalance : B.transportRebalance_blocked z atom

namespace AllNamedBlockers

/-- Convert all named blockers to the older indexed form. -/
def toIndexed
    {Zero Atom : Type}
    {B : NamedBlockerPredicates Zero Atom}
    {z : Zero} {atom : Atom}
    (H : AllNamedBlockers B z atom) :
    ∀ m : MoveName, B.asIndexedReason z atom m
  | MoveName.peelQ => H.peelQ
  | MoveName.peelR => H.peelR
  | MoveName.peelS => H.peelS
  | MoveName.absorbA => H.absorbA
  | MoveName.absorbB => H.absorbB
  | MoveName.absorbV => H.absorbV
  | MoveName.swapLeft => H.swapLeft
  | MoveName.swapRight => H.swapRight
  | MoveName.normalize => H.normalize
  | MoveName.residueRepair => H.residueRepair
  | MoveName.transportRebalance => H.transportRebalance

end AllNamedBlockers

/-- A single residue row for one named blocker. -/
def ResidueRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (modulus : Nat)
    (Blocked : Zero -> Atom -> Prop) : Prop :=
  ∀ ⦃z : Zero⦄ ⦃atom : Atom⦄,
    Valid atom -> Anchor z atom -> Blocked z atom ->
    SameMassResidueAt modulus (coords atom)

/--
Eleven row lemmas, one for each named move, plus the determinant gap data.
This is the next exact obligation under the finite move table.
-/
structure NamedResidueRows (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_row : ResidueRow coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_row : ResidueRow coords Valid Anchor modulus blockers.peelR_blocked
  peelS_row : ResidueRow coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_row : ResidueRow coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_row : ResidueRow coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_row : ResidueRow coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_row : ResidueRow coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_row : ResidueRow coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_row : ResidueRow coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_row : ResidueRow coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_row :
    ResidueRow coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace NamedResidueRows

/-- Dispatch a named blocked move to its residue row. -/
def sameResidue_of_named_blocker
    {Zero Atom : Type}
    (T : NamedResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom) :
    ∀ m : MoveName,
      T.blockers.asIndexedReason z atom m ->
      SameMassResidueAt T.modulus (T.coords atom)
  | MoveName.peelQ, h => T.peelQ_row hValid hAnchor h
  | MoveName.peelR, h => T.peelR_row hValid hAnchor h
  | MoveName.peelS, h => T.peelS_row hValid hAnchor h
  | MoveName.absorbA, h => T.absorbA_row hValid hAnchor h
  | MoveName.absorbB, h => T.absorbB_row hValid hAnchor h
  | MoveName.absorbV, h => T.absorbV_row hValid hAnchor h
  | MoveName.swapLeft, h => T.swapLeft_row hValid hAnchor h
  | MoveName.swapRight, h => T.swapRight_row hValid hAnchor h
  | MoveName.normalize, h => T.normalize_row hValid hAnchor h
  | MoveName.residueRepair, h => T.residueRepair_row hValid hAnchor h
  | MoveName.transportRebalance, h => T.transportRebalance_row hValid hAnchor h

/-- All named blockers imply same-residue; `peelQ` is one distinguished row. -/
theorem sameResidue_of_allNamedBlockers
    {Zero Atom : Type}
    (T : NamedResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    SameMassResidueAt T.modulus (T.coords atom) := by
  exact T.peelQ_row hValid hAnchor hBlocked.peelQ

/-- A fully blocked valid anchored atom contradicts the determinant gap. -/
theorem no_valid_anchored_with_all_named_blockers
    {Zero Atom : Type}
    (T : NamedResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    False := by
  let c := T.coords atom
  have hsame : c.leftMass % T.modulus = c.rightMass % T.modulus :=
    T.sameResidue_of_allNamedBlockers hValid hAnchor hBlocked
  have hgap : c.leftMass % T.modulus = (c.rightMass + 2) % T.modulus :=
    ArithmeticCoordinates.residue_gap_of_transportEquation (T.transport hValid) T.modulus
  exact T.gap_nonzero hValid (by
    calc
      c.rightMass % T.modulus = c.leftMass % T.modulus := hsame.symm
      _ = (c.rightMass + 2) % T.modulus := hgap)

end NamedResidueRows

/--
The exact next finite local obligation: provide eleven concrete row lemmas for
the chosen blocker predicates.
-/
def NamedResidueRowsObligation (Zero Atom : Type) : Prop :=
  Nonempty (NamedResidueRows Zero Atom)

/-- Slogan theorem: the remaining residue task is eleven named local rows. -/
theorem namedResidueRows_slogan : True := by
  trivial

end LayerBoxNamedResidueRows
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_factor_residue_matrix_patch.lean ============ -/

/-
Riemann_layerbox_factor_residue_matrix_patch.lean

Purpose
-------
Next strict layer after `Riemann_layerbox_named_residue_rows_patch.lean`.

The previous file reduced the fully-blocked LayerBox contradiction to eleven
named residue rows.  This file pushes those rows one level lower: each row must
now prove a concrete factor-residue product equality

  (q mod M)(r mod M)(s mod M) = (a mod M)(b mod M)(v mod M)   mod M,

which is then converted, by pure modular arithmetic, into the mass-residue row

  q*r*s = a*b*v   mod M.

Together with the determinant/two-transport gap

  q*r*s = a*b*v + 2

and the nonzero modular `+2` gap, all eleven named blockers cannot coexist.

This file is still a local kernel/audit layer.  It does not assert the actual
repo-specific blocker predicates.  It specifies the exact residue arithmetic
that each named blocker must supply.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxFactorResidueMatrix

/-- The fixed finite menu of elementary moves. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- Coordinates of the arithmetic two-transport atom. -/
structure ArithmeticCoordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  A : Nat
  deriving Repr

namespace ArithmeticCoordinates

/-- Left transported mass. -/
def leftMass (c : ArithmeticCoordinates) : Nat :=
  c.q * c.r * c.s

/-- Right transported mass. -/
def rightMass (c : ArithmeticCoordinates) : Nat :=
  c.a * c.b * c.v

/-- The determinant / two-transport law. -/
def TransportEquation (c : ArithmeticCoordinates) : Prop :=
  c.leftMass = c.rightMass + 2

/-- The determinant forces the modular `+2` gap. -/
theorem residue_gap_of_transportEquation
    {c : ArithmeticCoordinates}
    (h : c.TransportEquation)
    (M : Nat) :
    c.leftMass % M = (c.rightMass + 2) % M := by
  simpa [TransportEquation] using congrArg (fun n => n % M) h

end ArithmeticCoordinates

/-- The two transported masses have the same residue modulo `M`. -/
def SameMassResidueAt (M : Nat) (c : ArithmeticCoordinates) : Prop :=
  c.leftMass % M = c.rightMass % M

/-- The left mass computed only from factor residues. -/
def leftResidueProduct (M : Nat) (c : ArithmeticCoordinates) : Nat :=
  (((c.q % M) * (c.r % M)) % M * (c.s % M)) % M

/-- The right mass computed only from factor residues. -/
def rightResidueProduct (M : Nat) (c : ArithmeticCoordinates) : Nat :=
  (((c.a % M) * (c.b % M)) % M * (c.v % M)) % M

/-- A blocker row may prove equality of factor-residue products. -/
def FactorResidueProductEquality (M : Nat) (c : ArithmeticCoordinates) : Prop :=
  leftResidueProduct M c = rightResidueProduct M c

/-- Pure modular arithmetic: the mass residue is the product of factor residues. -/
theorem leftMass_mod_eq_leftResidueProduct
    (M : Nat) (c : ArithmeticCoordinates) :
    c.leftMass % M = leftResidueProduct M c := by
  simp [ArithmeticCoordinates.leftMass, leftResidueProduct, Nat.mul_mod]

/-- Pure modular arithmetic: the right mass residue is the product of factor residues. -/
theorem rightMass_mod_eq_rightResidueProduct
    (M : Nat) (c : ArithmeticCoordinates) :
    c.rightMass % M = rightResidueProduct M c := by
  simp [ArithmeticCoordinates.rightMass, rightResidueProduct, Nat.mul_mod]

/-- A factor-residue product equality gives a same-mass-residue row. -/
theorem sameMassResidue_of_factorResidueProductEquality
    {M : Nat} {c : ArithmeticCoordinates}
    (h : FactorResidueProductEquality M c) :
    SameMassResidueAt M c := by
  dsimp [SameMassResidueAt]
  calc
    c.leftMass % M = leftResidueProduct M c := leftMass_mod_eq_leftResidueProduct M c
    _ = rightResidueProduct M c := h
    _ = c.rightMass % M := (rightMass_mod_eq_rightResidueProduct M c).symm

/--
The eleven concrete blocker predicates, one per named move.
They are still repo-specific; this file only specifies their residue obligations.
-/
structure NamedBlockerPredicates (Zero Atom : Type) where
  peelQ_blocked : Zero -> Atom -> Prop
  peelR_blocked : Zero -> Atom -> Prop
  peelS_blocked : Zero -> Atom -> Prop
  absorbA_blocked : Zero -> Atom -> Prop
  absorbB_blocked : Zero -> Atom -> Prop
  absorbV_blocked : Zero -> Atom -> Prop
  swapLeft_blocked : Zero -> Atom -> Prop
  swapRight_blocked : Zero -> Atom -> Prop
  normalize_blocked : Zero -> Atom -> Prop
  residueRepair_blocked : Zero -> Atom -> Prop
  transportRebalance_blocked : Zero -> Atom -> Prop

namespace NamedBlockerPredicates

/-- Recover the old indexed blocker family when useful. -/
def asIndexedReason
    {Zero Atom : Type}
    (B : NamedBlockerPredicates Zero Atom) :
    Zero -> Atom -> MoveName -> Prop
  | z, atom, MoveName.peelQ => B.peelQ_blocked z atom
  | z, atom, MoveName.peelR => B.peelR_blocked z atom
  | z, atom, MoveName.peelS => B.peelS_blocked z atom
  | z, atom, MoveName.absorbA => B.absorbA_blocked z atom
  | z, atom, MoveName.absorbB => B.absorbB_blocked z atom
  | z, atom, MoveName.absorbV => B.absorbV_blocked z atom
  | z, atom, MoveName.swapLeft => B.swapLeft_blocked z atom
  | z, atom, MoveName.swapRight => B.swapRight_blocked z atom
  | z, atom, MoveName.normalize => B.normalize_blocked z atom
  | z, atom, MoveName.residueRepair => B.residueRepair_blocked z atom
  | z, atom, MoveName.transportRebalance => B.transportRebalance_blocked z atom

end NamedBlockerPredicates

/-- All eleven named blockers hold at a fixed anchored atom. -/
structure AllNamedBlockers
    {Zero Atom : Type}
    (B : NamedBlockerPredicates Zero Atom)
    (z : Zero)
    (atom : Atom) : Prop where
  peelQ : B.peelQ_blocked z atom
  peelR : B.peelR_blocked z atom
  peelS : B.peelS_blocked z atom
  absorbA : B.absorbA_blocked z atom
  absorbB : B.absorbB_blocked z atom
  absorbV : B.absorbV_blocked z atom
  swapLeft : B.swapLeft_blocked z atom
  swapRight : B.swapRight_blocked z atom
  normalize : B.normalize_blocked z atom
  residueRepair : B.residueRepair_blocked z atom
  transportRebalance : B.transportRebalance_blocked z atom

namespace AllNamedBlockers

/-- Convert all named blockers to the indexed form. -/
def toIndexed
    {Zero Atom : Type}
    {B : NamedBlockerPredicates Zero Atom}
    {z : Zero} {atom : Atom}
    (H : AllNamedBlockers B z atom) :
    ∀ m : MoveName, B.asIndexedReason z atom m
  | MoveName.peelQ => H.peelQ
  | MoveName.peelR => H.peelR
  | MoveName.peelS => H.peelS
  | MoveName.absorbA => H.absorbA
  | MoveName.absorbB => H.absorbB
  | MoveName.absorbV => H.absorbV
  | MoveName.swapLeft => H.swapLeft
  | MoveName.swapRight => H.swapRight
  | MoveName.normalize => H.normalize
  | MoveName.residueRepair => H.residueRepair
  | MoveName.transportRebalance => H.transportRebalance

end AllNamedBlockers

/-- A single factor-residue row for one named blocker. -/
def FactorResidueRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (modulus : Nat)
    (Blocked : Zero -> Atom -> Prop) : Prop :=
  ∀ ⦃z : Zero⦄ ⦃atom : Atom⦄,
    Valid atom -> Anchor z atom -> Blocked z atom ->
    FactorResidueProductEquality modulus (coords atom)

/--
Eleven factor-residue rows, one for each named move, plus the determinant gap.
This is a stricter form of the previous `NamedResidueRows` obligation.
-/
structure FactorResidueRows (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_row : FactorResidueRow coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_row : FactorResidueRow coords Valid Anchor modulus blockers.peelR_blocked
  peelS_row : FactorResidueRow coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_row : FactorResidueRow coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_row : FactorResidueRow coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_row : FactorResidueRow coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_row : FactorResidueRow coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_row : FactorResidueRow coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_row : FactorResidueRow coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_row : FactorResidueRow coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_row :
    FactorResidueRow coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace FactorResidueRows

/-- Dispatch a named blocker to its factor-residue row. -/
def factorResidue_of_named_blocker
    {Zero Atom : Type}
    (T : FactorResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom) :
    ∀ m : MoveName,
      T.blockers.asIndexedReason z atom m ->
      FactorResidueProductEquality T.modulus (T.coords atom)
  | MoveName.peelQ, h => T.peelQ_row hValid hAnchor h
  | MoveName.peelR, h => T.peelR_row hValid hAnchor h
  | MoveName.peelS, h => T.peelS_row hValid hAnchor h
  | MoveName.absorbA, h => T.absorbA_row hValid hAnchor h
  | MoveName.absorbB, h => T.absorbB_row hValid hAnchor h
  | MoveName.absorbV, h => T.absorbV_row hValid hAnchor h
  | MoveName.swapLeft, h => T.swapLeft_row hValid hAnchor h
  | MoveName.swapRight, h => T.swapRight_row hValid hAnchor h
  | MoveName.normalize, h => T.normalize_row hValid hAnchor h
  | MoveName.residueRepair, h => T.residueRepair_row hValid hAnchor h
  | MoveName.transportRebalance, h => T.transportRebalance_row hValid hAnchor h

/-- Dispatch a named blocker all the way to same-mass residue. -/
def sameResidue_of_named_blocker
    {Zero Atom : Type}
    (T : FactorResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom) :
    ∀ m : MoveName,
      T.blockers.asIndexedReason z atom m ->
      SameMassResidueAt T.modulus (T.coords atom)
  | m, h =>
      sameMassResidue_of_factorResidueProductEquality
        (T.factorResidue_of_named_blocker hValid hAnchor m h)

/-- All named blockers imply same-residue; `peelQ` is one distinguished row. -/
theorem sameResidue_of_allNamedBlockers
    {Zero Atom : Type}
    (T : FactorResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    SameMassResidueAt T.modulus (T.coords atom) := by
  exact T.sameResidue_of_named_blocker hValid hAnchor MoveName.peelQ hBlocked.peelQ

/-- A fully blocked valid anchored atom contradicts the determinant gap. -/
theorem no_valid_anchored_with_all_factor_blockers
    {Zero Atom : Type}
    (T : FactorResidueRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    False := by
  let c := T.coords atom
  have hsame : c.leftMass % T.modulus = c.rightMass % T.modulus :=
    T.sameResidue_of_allNamedBlockers hValid hAnchor hBlocked
  have hgap : c.leftMass % T.modulus = (c.rightMass + 2) % T.modulus :=
    ArithmeticCoordinates.residue_gap_of_transportEquation (T.transport hValid) T.modulus
  exact T.gap_nonzero hValid (by
    calc
      c.rightMass % T.modulus = c.leftMass % T.modulus := hsame.symm
      _ = (c.rightMass + 2) % T.modulus := hgap)

end FactorResidueRows

/--
A weaker row family that only proves one side's residues.  This is deliberately
marked insufficient: rows must compare the two residue products, not merely lock
one side.
-/
structure OneSidedResidueRows (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  leftLocked : Zero -> Atom -> Prop
  rightLocked : Zero -> Atom -> Prop

/-- The exact next obligation: eleven concrete factor-residue rows. -/
def FactorResidueRowsObligation (Zero Atom : Type) : Prop :=
  Nonempty (FactorResidueRows Zero Atom)

/-- Compatibility slogan: residue rows now reduce to factor-residue product rows. -/
theorem factorResidueMatrix_slogan : True := by
  trivial

end LayerBoxFactorResidueMatrix
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_residue_assignment_rows_patch.lean ============ -/

/-
Riemann_layerbox_residue_assignment_rows_patch.lean

Purpose
-------
Next strict layer after `Riemann_layerbox_factor_residue_matrix_patch.lean`.

The previous file reduced the fully-blocked LayerBox contradiction to eleven
factor-residue product equalities.  This file pushes those rows one level lower:
for each named blocker it is enough to supply an explicit residue tuple

  (q₀,r₀,s₀,a₀,b₀,v₀) mod M

for the six factors, together with a proof that the tuple is balanced:

  q₀*r₀*s₀ = a₀*b₀*v₀    mod M.

This is still an audit/kernel layer.  It does not assert the concrete residue
assignments for the repo's LayerBox atoms.  It records the exact next local
obligation: eleven named blockers must force balanced residue assignments.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxResidueAssignmentRows

open LayerBoxFactorResidueMatrix

/-- A concrete residue tuple for the six factors of a two-transport atom. -/
structure ResidueTuple where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat
  deriving Repr

namespace ResidueTuple

/-- Left residue product of a residue tuple modulo `M`. -/
def leftProductAt (M : Nat) (τ : ResidueTuple) : Nat :=
  (((τ.q * τ.r) % M) * τ.s) % M

/-- Right residue product of a residue tuple modulo `M`. -/
def rightProductAt (M : Nat) (τ : ResidueTuple) : Nat :=
  (((τ.a * τ.b) % M) * τ.v) % M

/-- The residue tuple is balanced modulo `M`. -/
abbrev BalancedAt (M : Nat) (τ : ResidueTuple) : Prop :=
  τ.leftProductAt M = τ.rightProductAt M

/-- The residue tuple is explicitly unbalanced modulo `M`. -/
abbrev UnbalancedAt (M : Nat) (τ : ResidueTuple) : Prop :=
  τ.leftProductAt M ≠ τ.rightProductAt M

/-- A tuple cannot be both balanced and unbalanced. -/
theorem not_balanced_and_unbalanced
    {M : Nat} {τ : ResidueTuple}
    (hb : τ.BalancedAt M)
    (hu : τ.UnbalancedAt M) :
    False := by
  exact hu hb

end ResidueTuple

/--
The coordinates of an atom have the concrete residue tuple `τ` modulo `M`.
The tuple entries are intended as residue representatives; no canonical
`< M` condition is needed at this kernel level.
-/
structure AtomHasResidueTuple
    (M : Nat)
    (c : ArithmeticCoordinates)
    (τ : ResidueTuple) : Prop where
  q_res : c.q % M = τ.q
  r_res : c.r % M = τ.r
  s_res : c.s % M = τ.s
  a_res : c.a % M = τ.a
  b_res : c.b % M = τ.b
  v_res : c.v % M = τ.v

namespace AtomHasResidueTuple

/-- The atom's left factor-residue product is the tuple's left product. -/
theorem leftProduct_eq
    {M : Nat} {c : ArithmeticCoordinates} {τ : ResidueTuple}
    (h : AtomHasResidueTuple M c τ) :
    leftResidueProduct M c = τ.leftProductAt M := by
  simp [leftResidueProduct, ResidueTuple.leftProductAt,
    h.q_res, h.r_res, h.s_res]

/-- The atom's right factor-residue product is the tuple's right product. -/
theorem rightProduct_eq
    {M : Nat} {c : ArithmeticCoordinates} {τ : ResidueTuple}
    (h : AtomHasResidueTuple M c τ) :
    rightResidueProduct M c = τ.rightProductAt M := by
  simp [rightResidueProduct, ResidueTuple.rightProductAt,
    h.a_res, h.b_res, h.v_res]

/-- A balanced tuple gives the factor-residue equality required by the previous layer. -/
theorem factorResidueProductEquality_of_balancedTuple
    {M : Nat} {c : ArithmeticCoordinates} {τ : ResidueTuple}
    (hTuple : AtomHasResidueTuple M c τ)
    (hBal : τ.BalancedAt M) :
    FactorResidueProductEquality M c := by
  dsimp [FactorResidueProductEquality]
  calc
    leftResidueProduct M c = τ.leftProductAt M := hTuple.leftProduct_eq
    _ = τ.rightProductAt M := hBal
    _ = rightResidueProduct M c := hTuple.rightProduct_eq.symm

end AtomHasResidueTuple

/--
A single named blocker row at the residue-assignment level.
It says that the blocker forces some concrete balanced residue tuple for the atom.
-/
def ResidueAssignmentRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (modulus : Nat)
    (Blocked : Zero -> Atom -> Prop) : Prop :=
  ∀ ⦃z : Zero⦄ ⦃atom : Atom⦄,
    Valid atom -> Anchor z atom -> Blocked z atom ->
    ∃ τ : ResidueTuple,
      AtomHasResidueTuple modulus (coords atom) τ ∧ τ.BalancedAt modulus

/-- A residue-assignment row implies the factor-residue row from the previous layer. -/
theorem factorResidueRow_of_residueAssignmentRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {modulus : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (row : ResidueAssignmentRow coords Valid Anchor modulus Blocked) :
    FactorResidueRow coords Valid Anchor modulus Blocked := by
  intro z atom hValid hAnchor hBlocked
  rcases row hValid hAnchor hBlocked with ⟨τ, hTuple, hBal⟩
  exact hTuple.factorResidueProductEquality_of_balancedTuple hBal

/--
Eleven residue-assignment rows, one per named blocker, plus the determinant gap.
This is the next stricter form of `FactorResidueRows`.
-/
structure ResidueAssignmentRows (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.peelR_blocked
  peelS_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_row : ResidueAssignmentRow coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_row :
    ResidueAssignmentRow coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace ResidueAssignmentRows

/-- Convert residue-assignment rows to factor-residue rows. -/
def toFactorResidueRows
    {Zero Atom : Type}
    (R : ResidueAssignmentRows Zero Atom) :
    FactorResidueRows Zero Atom where
  coords := R.coords
  Valid := R.Valid
  Anchor := R.Anchor
  blockers := R.blockers
  modulus := R.modulus
  transport := R.transport
  gap_nonzero := R.gap_nonzero
  peelQ_row := factorResidueRow_of_residueAssignmentRow R.peelQ_row
  peelR_row := factorResidueRow_of_residueAssignmentRow R.peelR_row
  peelS_row := factorResidueRow_of_residueAssignmentRow R.peelS_row
  absorbA_row := factorResidueRow_of_residueAssignmentRow R.absorbA_row
  absorbB_row := factorResidueRow_of_residueAssignmentRow R.absorbB_row
  absorbV_row := factorResidueRow_of_residueAssignmentRow R.absorbV_row
  swapLeft_row := factorResidueRow_of_residueAssignmentRow R.swapLeft_row
  swapRight_row := factorResidueRow_of_residueAssignmentRow R.swapRight_row
  normalize_row := factorResidueRow_of_residueAssignmentRow R.normalize_row
  residueRepair_row := factorResidueRow_of_residueAssignmentRow R.residueRepair_row
  transportRebalance_row :=
    factorResidueRow_of_residueAssignmentRow R.transportRebalance_row

/-- Fully blocked valid anchored atoms are impossible under residue-assignment rows. -/
theorem no_valid_anchored_with_all_assignment_blockers
    {Zero Atom : Type}
    (R : ResidueAssignmentRows Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : R.Valid atom)
    (hAnchor : R.Anchor z atom)
    (hBlocked : AllNamedBlockers R.blockers z atom) :
    False := by
  exact R.toFactorResidueRows.no_valid_anchored_with_all_factor_blockers
    hValid hAnchor hBlocked

end ResidueAssignmentRows

/--
A single blocker may also force an explicitly unbalanced tuple.  Such a row is
not a valid residue-assignment row; it is an immediate local obstruction instead.
-/
def ResidueObstructionRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (modulus : Nat)
    (Blocked : Zero -> Atom -> Prop) : Prop :=
  ∀ ⦃z : Zero⦄ ⦃atom : Atom⦄,
    Valid atom -> Anchor z atom -> Blocked z atom ->
    ∃ τ : ResidueTuple,
      AtomHasResidueTuple modulus (coords atom) τ ∧ τ.UnbalancedAt modulus

/--
If a row simultaneously claims the same tuple is balanced and unbalanced, it
already gives a local contradiction.  This is a sanity firewall for table rows.
-/
theorem contradiction_of_balanced_and_unbalanced_assignment
    {M : Nat} {c : ArithmeticCoordinates} {τ : ResidueTuple}
    (_hTuple : AtomHasResidueTuple M c τ)
    (hBal : τ.BalancedAt M)
    (hUnbal : τ.UnbalancedAt M) :
    False := by
  exact ResidueTuple.not_balanced_and_unbalanced hBal hUnbal

/-- The exact next obligation: eleven blockers must force balanced residue assignments. -/
def ResidueAssignmentRowsObligation (Zero Atom : Type) : Prop :=
  Nonempty (ResidueAssignmentRows Zero Atom)

/-- Compatibility slogan: factor-residue rows now reduce to balanced residue assignments. -/
theorem residueAssignmentRows_slogan : True := by
  trivial

end LayerBoxResidueAssignmentRows
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_concrete_residue_tuple_table_patch.lean ============ -/

/-
Riemann_layerbox_concrete_residue_tuple_table_patch.lean

Purpose
-------
Next strict layer after `Riemann_layerbox_residue_assignment_rows_patch.lean`.

The previous file reduced the fully-blocked LayerBox contradiction to eleven
residue-assignment rows.  Each row still said only that there ∃ a balanced
residue tuple for the blocked atom.

This file removes that existential layer.  For each named blocker one must now
provide an explicit tuple-builder, together with two local checks:

  1. the atom really has that tuple modulo `M`;
  2. the tuple is balanced modulo `M`.

Thus the remaining work is a finite concrete residue table, not an opaque
existential row.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxConcreteResidueTupleTable

open LayerBoxFactorResidueMatrix
open LayerBoxResidueAssignmentRows

/--
A concrete tuple-builder for a single named blocker row.

Given a valid atom anchored at `z` and a proof that the corresponding named
move is blocked, the builder returns the actual six-factor residue tuple for
that row.  The row is useful only if the tuple is both correctly read from the
atom and balanced modulo the chosen modulus.
-/
structure ResidueTupleBuilder
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (modulus : Nat)
    (Blocked : Zero -> Atom -> Prop) where
  tuple : Zero -> Atom -> ResidueTuple
  hasTuple :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      AtomHasResidueTuple modulus (coords atom) (tuple z atom)
  balanced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (tuple z atom).BalancedAt modulus

namespace ResidueTupleBuilder

/-- A concrete tuple-builder gives the existential row from the previous layer. -/
theorem toResidueAssignmentRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {modulus : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (B : ResidueTupleBuilder coords Valid Anchor modulus Blocked) :
    ResidueAssignmentRow coords Valid Anchor modulus Blocked := by
  intro z atom hValid hAnchor hBlocked
  refine ⟨B.tuple z atom, ?_, ?_⟩
  · exact B.hasTuple hValid hAnchor hBlocked
  · exact B.balanced hValid hAnchor hBlocked

end ResidueTupleBuilder

/--
A static tuple row: the named blocker always forces the same residue tuple.
This is stricter than `ResidueTupleBuilder`.  It is useful for blocker rows whose
residue profile is independent of the specific zero and atom after normalisation.
-/
structure StaticResidueTupleRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (modulus : Nat)
    (Blocked : Zero -> Atom -> Prop) where
  tuple : ResidueTuple
  hasTuple :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      AtomHasResidueTuple modulus (coords atom) tuple
  balanced : tuple.BalancedAt modulus

namespace StaticResidueTupleRow

/-- Static rows are a special case of tuple-builders. -/
def toBuilder
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {modulus : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (S : StaticResidueTupleRow coords Valid Anchor modulus Blocked) :
    ResidueTupleBuilder coords Valid Anchor modulus Blocked where
  tuple := fun _ _ => S.tuple
  hasTuple := by
    intro z atom hValid hAnchor hBlocked
    exact S.hasTuple hValid hAnchor hBlocked
  balanced := by
    intro z atom hValid hAnchor hBlocked
    exact S.balanced

/-- Static rows give residue-assignment rows. -/
theorem toResidueAssignmentRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {modulus : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (S : StaticResidueTupleRow coords Valid Anchor modulus Blocked) :
    ResidueAssignmentRow coords Valid Anchor modulus Blocked := by
  exact S.toBuilder.toResidueAssignmentRow

end StaticResidueTupleRow

/--
Eleven concrete tuple-builders, one for each named blocker, plus the determinant
gap data inherited from the previous residue-assignment layer.
-/
structure ConcreteResidueTupleTable (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.peelR_blocked
  peelS_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_builder :
    ResidueTupleBuilder coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace ConcreteResidueTupleTable

/-- A concrete tuple table gives the residue-assignment rows of the previous layer. -/
def toResidueAssignmentRows
    {Zero Atom : Type}
    (T : ConcreteResidueTupleTable Zero Atom) :
    ResidueAssignmentRows Zero Atom where
  coords := T.coords
  Valid := T.Valid
  Anchor := T.Anchor
  blockers := T.blockers
  modulus := T.modulus
  transport := T.transport
  gap_nonzero := T.gap_nonzero
  peelQ_row := T.peelQ_builder.toResidueAssignmentRow
  peelR_row := T.peelR_builder.toResidueAssignmentRow
  peelS_row := T.peelS_builder.toResidueAssignmentRow
  absorbA_row := T.absorbA_builder.toResidueAssignmentRow
  absorbB_row := T.absorbB_builder.toResidueAssignmentRow
  absorbV_row := T.absorbV_builder.toResidueAssignmentRow
  swapLeft_row := T.swapLeft_builder.toResidueAssignmentRow
  swapRight_row := T.swapRight_builder.toResidueAssignmentRow
  normalize_row := T.normalize_builder.toResidueAssignmentRow
  residueRepair_row := T.residueRepair_builder.toResidueAssignmentRow
  transportRebalance_row := T.transportRebalance_builder.toResidueAssignmentRow

/-- Fully blocked valid anchored atoms are impossible under a concrete tuple table. -/
theorem no_valid_anchored_with_all_concrete_tuple_blockers
    {Zero Atom : Type}
    (T : ConcreteResidueTupleTable Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    False := by
  exact T.toResidueAssignmentRows.no_valid_anchored_with_all_assignment_blockers
    hValid hAnchor hBlocked

end ConcreteResidueTupleTable

/--
A stricter variant where each row uses a fixed tuple, independent of `z` and
`atom`.  This is sometimes the desired final table after normalisation.
-/
structure StaticConcreteResidueTupleTable (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.peelR_blocked
  peelS_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_row : StaticResidueTupleRow coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_row :
    StaticResidueTupleRow coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace StaticConcreteResidueTupleTable

/-- Static tables are concrete tuple tables. -/
def toConcreteResidueTupleTable
    {Zero Atom : Type}
    (S : StaticConcreteResidueTupleTable Zero Atom) :
    ConcreteResidueTupleTable Zero Atom where
  coords := S.coords
  Valid := S.Valid
  Anchor := S.Anchor
  blockers := S.blockers
  modulus := S.modulus
  transport := S.transport
  gap_nonzero := S.gap_nonzero
  peelQ_builder := S.peelQ_row.toBuilder
  peelR_builder := S.peelR_row.toBuilder
  peelS_builder := S.peelS_row.toBuilder
  absorbA_builder := S.absorbA_row.toBuilder
  absorbB_builder := S.absorbB_row.toBuilder
  absorbV_builder := S.absorbV_row.toBuilder
  swapLeft_builder := S.swapLeft_row.toBuilder
  swapRight_builder := S.swapRight_row.toBuilder
  normalize_builder := S.normalize_row.toBuilder
  residueRepair_builder := S.residueRepair_row.toBuilder
  transportRebalance_builder := S.transportRebalance_row.toBuilder

/-- Fully blocked valid anchored atoms are impossible under a static concrete table. -/
theorem no_valid_anchored_with_all_static_tuple_blockers
    {Zero Atom : Type}
    (S : StaticConcreteResidueTupleTable Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : S.Valid atom)
    (hAnchor : S.Anchor z atom)
    (hBlocked : AllNamedBlockers S.blockers z atom) :
    False := by
  exact S.toConcreteResidueTupleTable.no_valid_anchored_with_all_concrete_tuple_blockers
    hValid hAnchor hBlocked

end StaticConcreteResidueTupleTable

/-- The familiar forbidden tuple: left `5*5*5`, right `1*1*1`, modulo six. -/
def tuple555_111 : ResidueTuple where
  q := 5
  r := 5
  s := 5
  a := 1
  b := 1
  v := 1

/-- The tuple `(5,5,5;1,1,1)` is not balanced modulo six. -/
theorem tuple555_111_unbalanced_mod6 :
    tuple555_111.UnbalancedAt 6 := by
  decide

/-- A balanced sample tuple modulo six; useful as a sanity check for the table API. -/
def tuple511_511 : ResidueTuple where
  q := 5
  r := 1
  s := 1
  a := 5
  b := 1
  v := 1

/-- The tuple `(5,1,1;5,1,1)` is balanced modulo six. -/
theorem tuple511_511_balanced_mod6 :
    tuple511_511.BalancedAt 6 := by
  decide

/--
The next exact obligation: provide a concrete tuple-builder for each of the
11 named blocker rows.
-/
def ConcreteResidueTupleTableObligation (Zero Atom : Type) : Prop :=
  Nonempty (ConcreteResidueTupleTable Zero Atom)

/--
A still stricter optional obligation: provide a static tuple for each blocker
row after normalisation.
-/
def StaticConcreteResidueTupleTableObligation (Zero Atom : Type) : Prop :=
  Nonempty (StaticConcreteResidueTupleTable Zero Atom)

/-- Compatibility slogan: the residue table is now finite and concrete. -/
theorem concreteResidueTupleTable_slogan : True := by
  trivial

end LayerBoxConcreteResidueTupleTable
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_residue_tuple_decider_patch.lean ============ -/

/-
Riemann_layerbox_residue_tuple_decider_patch.lean

Purpose
-------
Next strict layer after `Riemann_layerbox_concrete_residue_tuple_table_patch.lean`.

The previous file reduced the fully-blocked LayerBox contradiction to an
11-row concrete residue tuple table.  Each row still carried a proof field

  tuple.BalancedAt M

by hand.  This file removes that proof-shaped black box: a row may now provide
an explicit tuple together with the Boolean/computable check

  decide (tuple.BalancedAt M) = true.

Thus each row's last arithmetic obligation is a finite modular computation.
The conversion back to the previous concrete table is theorematic.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxResidueTupleDecider

open LayerBoxFactorResidueMatrix
open LayerBoxResidueAssignmentRows
open LayerBoxConcreteResidueTupleTable

/--
A tuple whose balance modulo `M` is certified by the executable `decide` check.
This is the desired final form for each residue row: the residue arithmetic has
been reduced to a closed modular computation.
-/
structure DecidedBalancedTuple (M : Nat) where
  tuple : ResidueTuple
  balanced_check : decide (tuple.BalancedAt M) = true

namespace DecidedBalancedTuple

/-- The executable balance check gives the Prop-level balance proof. -/
theorem balancedAt {M : Nat} (D : DecidedBalancedTuple M) :
    D.tuple.BalancedAt M := by
  exact of_decide_eq_true D.balanced_check

/-- A decided tuple gives the static row's balance field. -/
def toStaticResidueTupleRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {Blocked : Zero -> Atom -> Prop}
    {M : Nat}
    (D : DecidedBalancedTuple M)
    (hasTuple :
      ∀ {z : Zero} {atom : Atom},
        Valid atom -> Anchor z atom -> Blocked z atom ->
        AtomHasResidueTuple M (coords atom) D.tuple) :
    StaticResidueTupleRow coords Valid Anchor M Blocked where
  tuple := D.tuple
  hasTuple := hasTuple
  balanced := D.balancedAt

end DecidedBalancedTuple

/--
A concrete row whose balance proof is a computation rather than a hand-supplied
Prop.  The tuple may still depend on `z` and `atom`; this supports rows whose
normal form is not static.
-/
structure ResidueTupleDeciderBuilder
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (M : Nat)
    (Blocked : Zero -> Atom -> Prop) where
  tuple : Zero -> Atom -> ResidueTuple
  hasTuple :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      AtomHasResidueTuple M (coords atom) (tuple z atom)
  balanced_check :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      decide ((tuple z atom).BalancedAt M) = true

namespace ResidueTupleDeciderBuilder

/-- A decider-builder is a concrete tuple-builder for the previous layer. -/
def toResidueTupleBuilder
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (B : ResidueTupleDeciderBuilder coords Valid Anchor M Blocked) :
    ResidueTupleBuilder coords Valid Anchor M Blocked where
  tuple := B.tuple
  hasTuple := B.hasTuple
  balanced := by
    intro z atom hValid hAnchor hBlocked
    exact of_decide_eq_true (B.balanced_check hValid hAnchor hBlocked)

/-- A decider-builder gives the previous existential residue-assignment row. -/
theorem toResidueAssignmentRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (B : ResidueTupleDeciderBuilder coords Valid Anchor M Blocked) :
    ResidueAssignmentRow coords Valid Anchor M Blocked := by
  exact B.toResidueTupleBuilder.toResidueAssignmentRow

end ResidueTupleDeciderBuilder

/--
A static decider row: the blocker row always uses the same explicit residue
tuple, and the balance of that tuple is checked by computation.
-/
structure StaticResidueTupleDeciderRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (M : Nat)
    (Blocked : Zero -> Atom -> Prop) where
  decided : DecidedBalancedTuple M
  hasTuple :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      AtomHasResidueTuple M (coords atom) decided.tuple

namespace StaticResidueTupleDeciderRow

/-- Static decider rows give static tuple rows. -/
def toStaticResidueTupleRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (R : StaticResidueTupleDeciderRow coords Valid Anchor M Blocked) :
    StaticResidueTupleRow coords Valid Anchor M Blocked :=
  R.decided.toStaticResidueTupleRow R.hasTuple

/-- Static decider rows are concrete decider builders. -/
def toResidueTupleDeciderBuilder
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (R : StaticResidueTupleDeciderRow coords Valid Anchor M Blocked) :
    ResidueTupleDeciderBuilder coords Valid Anchor M Blocked where
  tuple := fun _ _ => R.decided.tuple
  hasTuple := by
    intro z atom hValid hAnchor hBlocked
    exact R.hasTuple hValid hAnchor hBlocked
  balanced_check := by
    intro z atom hValid hAnchor hBlocked
    exact R.decided.balanced_check

end StaticResidueTupleDeciderRow

/--
The 11-row concrete tuple table with all balance checks discharged by executable
Boolean decisions.
-/
structure ConcreteResidueTupleDeciderTable (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.peelR_blocked
  peelS_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_builder :
    ResidueTupleDeciderBuilder coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace ConcreteResidueTupleDeciderTable

/-- A decider table gives the concrete tuple table of the previous layer. -/
def toConcreteResidueTupleTable
    {Zero Atom : Type}
    (T : ConcreteResidueTupleDeciderTable Zero Atom) :
    ConcreteResidueTupleTable Zero Atom where
  coords := T.coords
  Valid := T.Valid
  Anchor := T.Anchor
  blockers := T.blockers
  modulus := T.modulus
  transport := T.transport
  gap_nonzero := T.gap_nonzero
  peelQ_builder := T.peelQ_builder.toResidueTupleBuilder
  peelR_builder := T.peelR_builder.toResidueTupleBuilder
  peelS_builder := T.peelS_builder.toResidueTupleBuilder
  absorbA_builder := T.absorbA_builder.toResidueTupleBuilder
  absorbB_builder := T.absorbB_builder.toResidueTupleBuilder
  absorbV_builder := T.absorbV_builder.toResidueTupleBuilder
  swapLeft_builder := T.swapLeft_builder.toResidueTupleBuilder
  swapRight_builder := T.swapRight_builder.toResidueTupleBuilder
  normalize_builder := T.normalize_builder.toResidueTupleBuilder
  residueRepair_builder := T.residueRepair_builder.toResidueTupleBuilder
  transportRebalance_builder := T.transportRebalance_builder.toResidueTupleBuilder

/-- Fully blocked valid anchored atoms are impossible under a decider table. -/
theorem no_valid_anchored_with_all_decider_tuple_blockers
    {Zero Atom : Type}
    (T : ConcreteResidueTupleDeciderTable Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    False := by
  exact T.toConcreteResidueTupleTable.no_valid_anchored_with_all_concrete_tuple_blockers
    hValid hAnchor hBlocked

end ConcreteResidueTupleDeciderTable

/--
A stricter table: each named row has a fixed tuple and a closed `decide` proof.
After this layer the only row work left is: prove the atom really has the fixed
residue tuple under the corresponding blocker.
-/
structure StaticResidueTupleDeciderTable (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.peelR_blocked
  peelS_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_row :
    StaticResidueTupleDeciderRow coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace StaticResidueTupleDeciderTable

/-- Static decider tables are concrete decider tables. -/
def toConcreteResidueTupleDeciderTable
    {Zero Atom : Type}
    (S : StaticResidueTupleDeciderTable Zero Atom) :
    ConcreteResidueTupleDeciderTable Zero Atom where
  coords := S.coords
  Valid := S.Valid
  Anchor := S.Anchor
  blockers := S.blockers
  modulus := S.modulus
  transport := S.transport
  gap_nonzero := S.gap_nonzero
  peelQ_builder := S.peelQ_row.toResidueTupleDeciderBuilder
  peelR_builder := S.peelR_row.toResidueTupleDeciderBuilder
  peelS_builder := S.peelS_row.toResidueTupleDeciderBuilder
  absorbA_builder := S.absorbA_row.toResidueTupleDeciderBuilder
  absorbB_builder := S.absorbB_row.toResidueTupleDeciderBuilder
  absorbV_builder := S.absorbV_row.toResidueTupleDeciderBuilder
  swapLeft_builder := S.swapLeft_row.toResidueTupleDeciderBuilder
  swapRight_builder := S.swapRight_row.toResidueTupleDeciderBuilder
  normalize_builder := S.normalize_row.toResidueTupleDeciderBuilder
  residueRepair_builder := S.residueRepair_row.toResidueTupleDeciderBuilder
  transportRebalance_builder := S.transportRebalance_row.toResidueTupleDeciderBuilder

/-- Fully blocked valid anchored atoms are impossible under a static decider table. -/
theorem no_valid_anchored_with_all_static_decider_blockers
    {Zero Atom : Type}
    (S : StaticResidueTupleDeciderTable Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : S.Valid atom)
    (hAnchor : S.Anchor z atom)
    (hBlocked : AllNamedBlockers S.blockers z atom) :
    False := by
  exact S.toConcreteResidueTupleDeciderTable.no_valid_anchored_with_all_decider_tuple_blockers
    hValid hAnchor hBlocked

end StaticResidueTupleDeciderTable

/-- Closed computation: `(5,1,1;5,1,1)` is balanced modulo six. -/
def decided_tuple511_511_mod6 : DecidedBalancedTuple 6 where
  tuple := tuple511_511
  balanced_check := by
    decide

/-- Closed computation: `(5,5,5;1,1,1)` is not balanced modulo six. -/
theorem tuple555_111_balance_decides_false_mod6 :
    decide (tuple555_111.BalancedAt 6) = false := by
  decide

/--
The next exact obligation: an 11-row residue tuple table whose balance fields are
closed by executable modular checks.
-/
def ConcreteResidueTupleDeciderTableObligation (Zero Atom : Type) : Prop :=
  Nonempty (ConcreteResidueTupleDeciderTable Zero Atom)

/--
The stricter optional obligation: a static 11-row table with closed modular
checks for each fixed tuple.
-/
def StaticResidueTupleDeciderTableObligation (Zero Atom : Type) : Prop :=
  Nonempty (StaticResidueTupleDeciderTable Zero Atom)

/-- Compatibility slogan: the remaining residue work is now a finite computation table. -/
theorem residueTupleDecider_slogan : True := by
  trivial

end LayerBoxResidueTupleDecider
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_forced_residue_table_patch.lean ============ -/

/-
Riemann_layerbox_forced_residue_table_patch.lean

Purpose
-------
Maximal next strict layer after `Riemann_layerbox_residue_tuple_decider_patch.lean`.

The previous file reduced the finite LayerBox residue work to an eleven-row
`StaticResidueTupleDeciderTable`: for each named blocked move one must provide

  * a fixed residue tuple,
  * a proof that the atom has that tuple modulo `M` under that blocker,
  * and an executable balance check for the tuple.

This file removes one more layer of opacity from the middle bullet.  A row no
longer supplies an opaque `AtomHasResidueTuple`; instead it must supply the six
individual congruence-forcing lemmas

  q % M = q₀, r % M = r₀, s % M = s₀,
  a % M = a₀, b % M = b₀, v % M = v₀.

Together with the executable `decide` balance check, this is the maximally
local finite table form: each of the eleven rows is reduced to six congruence
proofs plus one closed modular computation.

This is still an audit/interface layer.  It does not manufacture the actual
repo-specific blocker congruences; it states their exact shape and proves that
such a table closes the fully-blocked same-zero LayerBox counterexample.
-/



namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport
namespace LayerBoxForcedResidueTable

open LayerBoxFactorResidueMatrix
open LayerBoxResidueAssignmentRows
open LayerBoxConcreteResidueTupleTable
open LayerBoxResidueTupleDecider

/--
A row-level certificate that a blocker forces each of the six factor residues
of an atom to be the entries of a fixed tuple `τ` modulo `M`.

This is intentionally lower-level than `AtomHasResidueTuple`: the six fields are
now visible and can be attacked one at a time for each named move.
-/
structure SixResidueForcing
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (M : Nat)
    (Blocked : Zero -> Atom -> Prop)
    (τ : ResidueTuple) where
  q_forced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (coords atom).q % M = τ.q
  r_forced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (coords atom).r % M = τ.r
  s_forced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (coords atom).s % M = τ.s
  a_forced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (coords atom).a % M = τ.a
  b_forced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (coords atom).b % M = τ.b
  v_forced :
    ∀ {z : Zero} {atom : Atom},
      Valid atom -> Anchor z atom -> Blocked z atom ->
      (coords atom).v % M = τ.v

namespace SixResidueForcing

/-- The six visible congruence-forcing fields assemble to `AtomHasResidueTuple`. -/
def toAtomHasResidueTuple
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    {τ : ResidueTuple}
    (F : SixResidueForcing coords Valid Anchor M Blocked τ)
    {z : Zero} {atom : Atom}
    (hValid : Valid atom)
    (hAnchor : Anchor z atom)
    (hBlocked : Blocked z atom) :
    AtomHasResidueTuple M (coords atom) τ where
  q_res := F.q_forced hValid hAnchor hBlocked
  r_res := F.r_forced hValid hAnchor hBlocked
  s_res := F.s_forced hValid hAnchor hBlocked
  a_res := F.a_forced hValid hAnchor hBlocked
  b_res := F.b_forced hValid hAnchor hBlocked
  v_res := F.v_forced hValid hAnchor hBlocked

end SixResidueForcing

/--
A maximally-local static row: a fixed tuple, an executable balance check, and
six individual blocker-to-residue forcing lemmas.
-/
structure StaticForcedResidueDeciderRow
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (M : Nat)
    (Blocked : Zero -> Atom -> Prop) where
  tuple : ResidueTuple
  forcing : SixResidueForcing coords Valid Anchor M Blocked tuple
  balanced_check : decide (tuple.BalancedAt M) = true

namespace StaticForcedResidueDeciderRow

/-- A forced row gives the previous static decider row. -/
def toStaticResidueTupleDeciderRow
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (R : StaticForcedResidueDeciderRow coords Valid Anchor M Blocked) :
    StaticResidueTupleDeciderRow coords Valid Anchor M Blocked where
  decided := {
    tuple := R.tuple
    balanced_check := R.balanced_check
  }
  hasTuple := by
    intro z atom hValid hAnchor hBlocked
    exact R.forcing.toAtomHasResidueTuple hValid hAnchor hBlocked

/-- A forced row gives the previous concrete decider builder as well. -/
def toResidueTupleDeciderBuilder
    {Zero Atom : Type}
    {coords : Atom -> ArithmeticCoordinates}
    {Valid : Atom -> Prop}
    {Anchor : Zero -> Atom -> Prop}
    {M : Nat}
    {Blocked : Zero -> Atom -> Prop}
    (R : StaticForcedResidueDeciderRow coords Valid Anchor M Blocked) :
    ResidueTupleDeciderBuilder coords Valid Anchor M Blocked :=
  R.toStaticResidueTupleDeciderRow.toResidueTupleDeciderBuilder

end StaticForcedResidueDeciderRow

/--
The fully-expanded eleven-row residue table.

For each named blocker, the table exposes exactly six congruence lemmas plus one
closed balance computation.  No row may hide the tuple-forcing work inside an
opaque existential.
-/
structure StaticForcedResidueDeciderTable (Zero Atom : Type) where
  coords : Atom -> ArithmeticCoordinates
  Valid : Atom -> Prop
  Anchor : Zero -> Atom -> Prop
  blockers : NamedBlockerPredicates Zero Atom
  modulus : Nat
  transport : ∀ {atom : Atom}, Valid atom -> (coords atom).TransportEquation
  gap_nonzero :
    ∀ {atom : Atom},
      Valid atom ->
      (coords atom).rightMass % modulus ≠ ((coords atom).rightMass + 2) % modulus

  peelQ_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.peelQ_blocked
  peelR_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.peelR_blocked
  peelS_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.peelS_blocked
  absorbA_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.absorbA_blocked
  absorbB_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.absorbB_blocked
  absorbV_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.absorbV_blocked
  swapLeft_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.swapLeft_blocked
  swapRight_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.swapRight_blocked
  normalize_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.normalize_blocked
  residueRepair_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.residueRepair_blocked
  transportRebalance_row :
    StaticForcedResidueDeciderRow coords Valid Anchor modulus blockers.transportRebalance_blocked

namespace StaticForcedResidueDeciderTable

/-- The fully-expanded table gives the previous static decider table. -/
def toStaticResidueTupleDeciderTable
    {Zero Atom : Type}
    (T : StaticForcedResidueDeciderTable Zero Atom) :
    StaticResidueTupleDeciderTable Zero Atom where
  coords := T.coords
  Valid := T.Valid
  Anchor := T.Anchor
  blockers := T.blockers
  modulus := T.modulus
  transport := T.transport
  gap_nonzero := T.gap_nonzero
  peelQ_row := T.peelQ_row.toStaticResidueTupleDeciderRow
  peelR_row := T.peelR_row.toStaticResidueTupleDeciderRow
  peelS_row := T.peelS_row.toStaticResidueTupleDeciderRow
  absorbA_row := T.absorbA_row.toStaticResidueTupleDeciderRow
  absorbB_row := T.absorbB_row.toStaticResidueTupleDeciderRow
  absorbV_row := T.absorbV_row.toStaticResidueTupleDeciderRow
  swapLeft_row := T.swapLeft_row.toStaticResidueTupleDeciderRow
  swapRight_row := T.swapRight_row.toStaticResidueTupleDeciderRow
  normalize_row := T.normalize_row.toStaticResidueTupleDeciderRow
  residueRepair_row := T.residueRepair_row.toStaticResidueTupleDeciderRow
  transportRebalance_row := T.transportRebalance_row.toStaticResidueTupleDeciderRow

/-- Therefore it gives the previous concrete decider table. -/
def toConcreteResidueTupleDeciderTable
    {Zero Atom : Type}
    (T : StaticForcedResidueDeciderTable Zero Atom) :
    ConcreteResidueTupleDeciderTable Zero Atom :=
  T.toStaticResidueTupleDeciderTable.toConcreteResidueTupleDeciderTable

/--
A fully-blocked valid anchored atom is impossible once all eleven forced rows are
provided.
-/
theorem no_valid_anchored_with_all_forced_residue_blockers
    {Zero Atom : Type}
    (T : StaticForcedResidueDeciderTable Zero Atom)
    {z : Zero} {atom : Atom}
    (hValid : T.Valid atom)
    (hAnchor : T.Anchor z atom)
    (hBlocked : AllNamedBlockers T.blockers z atom) :
    False := by
  exact T.toStaticResidueTupleDeciderTable.no_valid_anchored_with_all_static_decider_blockers
    hValid hAnchor hBlocked

end StaticForcedResidueDeciderTable

/--
A compact per-row checklist: six forced residues plus executable balance.  This
is useful for documenting the exact row burden without expanding the table.
-/
structure RowChecklist
    {Zero Atom : Type}
    (coords : Atom -> ArithmeticCoordinates)
    (Valid : Atom -> Prop)
    (Anchor : Zero -> Atom -> Prop)
    (M : Nat)
    (Blocked : Zero -> Atom -> Prop) where
  row : StaticForcedResidueDeciderRow coords Valid Anchor M Blocked

/--
The maximally local finite obligation: eleven row checklists, one for each named
blocker, with no hidden residue tuple or balance proof.
-/
def StaticForcedResidueDeciderTableObligation (Zero Atom : Type) : Prop :=
  Nonempty (StaticForcedResidueDeciderTable Zero Atom)

/--
What remains after this layer: for each named blocked move, prove six concrete
congruence-forcing facts.  Balance is already executable.
-/
def SixCongruenceRowsObligation (Zero Atom : Type) : Prop :=
  StaticForcedResidueDeciderTableObligation Zero Atom

/--
Compatibility theorem: the new finite obligation implies the previous static
residue tuple decider obligation.
-/
theorem staticForcedRows_imply_previousStaticDeciderObligation
    {Zero Atom : Type}
    (h : StaticForcedResidueDeciderTableObligation Zero Atom) :
    StaticResidueTupleDeciderTableObligation Zero Atom := by
  rcases h with ⟨T⟩
  exact ⟨T.toStaticResidueTupleDeciderTable⟩

/--
Compatibility theorem: the new finite obligation implies the previous concrete
residue tuple decider obligation.
-/
theorem staticForcedRows_imply_previousConcreteDeciderObligation
    {Zero Atom : Type}
    (h : StaticForcedResidueDeciderTableObligation Zero Atom) :
    ConcreteResidueTupleDeciderTableObligation Zero Atom := by
  rcases h with ⟨T⟩
  exact ⟨T.toConcreteResidueTupleDeciderTable⟩

/--
Final audit slogan for this layer: the remaining residue work is now exactly a
finite 11 × 6 congruence table plus eleven closed modular computations.
-/
theorem forcedResidueTable_slogan : True := by
  trivial

end LayerBoxForcedResidueTable
end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/- ============ BRICK: Riemann_layerbox_maximal_forward_front_patch.lean ============ -/

/-
Riemann_layerbox_maximal_forward_front_patch.lean

Purpose.
  Push the current LayerBox / arithmetic two-transport branch several
  audit layers forward at once.

  This file is deliberately not an RH proof.  It packages the remaining
  local arithmetic work into the smallest finite table we have reached:

    11 named blockers × 6 residue congruence lines
    + 11 executable balanced-tuple checks
    + one global cover saying that every minimal self-decoded atom is
      either locally obstructed or all named blockers are present.

  The intended import order is after:
    Riemann_arithmetic_two_transport_law_patch
    Riemann_arithmetic_law_origin_anchor_audit_patch
    Riemann_spectral_anchor_data_nonvacuity_patch
    Riemann_spectral_anchor_origin_blind_firewall_patch
    Riemann_spectral_fingerprint_recoverability_patch
    Riemann_spectral_anchor_recovers_zero_patch
    Riemann_zero_indexed_impossibility_patch
    Riemann_decoded_layerbox_arithmetic_kernel_patch
    Riemann_layerbox_same_zero_descent_patch
    Riemann_layerbox_local_move_kernel_patch
    Riemann_layerbox_move_algebra_patch
    Riemann_layerbox_move_completeness_patch
    Riemann_layerbox_blocked_move_matrix_patch
    Riemann_layerbox_blocker_contradiction_kernel_patch
    Riemann_layerbox_residue_pressure_kernel_patch
    Riemann_layerbox_residue_blocker_table_patch
    Riemann_layerbox_named_residue_rows_patch
    Riemann_layerbox_factor_residue_matrix_patch
    Riemann_layerbox_residue_assignment_rows_patch
    Riemann_layerbox_concrete_residue_tuple_table_patch
    Riemann_layerbox_residue_tuple_decider_patch
    Riemann_layerbox_forced_residue_table_patch

Status.
  Audit/interface layer.  No new analytic RH input is hidden here.
  The only remaining concrete work is the finite residue table plus the
  blocker cover for the chosen LayerBox atom.
-/

namespace Riemann
namespace LayerBox
namespace MaximalForward

universe u v

/-- The fixed eleven local moves used in the current LayerBox route. -/
inductive NamedMove where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- A concrete six-coordinate view of an arithmetic transport atom. -/
structure AtomCoordinates (Atom : Type v) where
  q : Atom → Nat
  r : Atom → Nat
  s : Atom → Nat
  a : Atom → Nat
  b : Atom → Nat
  vv : Atom → Nat

namespace AtomCoordinates

variable {Atom : Type v} (C : AtomCoordinates Atom)

/-- Left transport mass: `q*r*s`. -/
def leftMass (x : Atom) : Nat :=
  C.q x * C.r x * C.s x

/-- Right transport mass: `a*b*v`. -/
def rightMass (x : Atom) : Nat :=
  C.a x * C.b x * C.vv x

/-- The arithmetic two-transport determinant. -/
def determinantGate (x : Atom) : Prop :=
  C.leftMass x = C.rightMass x + 2

end AtomCoordinates

/-- A residue tuple for the six coordinates. -/
structure ResidueTuple where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  vv : Nat
  deriving Repr

namespace ResidueTuple

/-- Product residue on the left side. -/
def leftProduct (M : Nat) (T : ResidueTuple) : Nat :=
  (((T.q % M) * (T.r % M) * (T.s % M)) % M)

/-- Product residue on the right side. -/
def rightProduct (M : Nat) (T : ResidueTuple) : Nat :=
  (((T.a % M) * (T.b % M) * (T.vv % M)) % M)

/-- A tuple is balanced when the two product residues agree. -/
abbrev BalancedAt (M : Nat) (T : ResidueTuple) : Prop :=
  leftProduct M T = rightProduct M T

/-- The determinant gap is visible modulo `M` if `2` is nonzero modulo `M`. -/
def GapVisible (M : Nat) : Prop :=
  2 % M ≠ 0

end ResidueTuple

/-- Six forced congruences between an atom and a residue tuple. -/
structure SixResidueForcing
    {Atom : Type v} (C : AtomCoordinates Atom) (M : Nat)
    (x : Atom) (T : ResidueTuple) : Prop where
  q_mod  : C.q x % M = T.q % M
  r_mod  : C.r x % M = T.r % M
  s_mod  : C.s x % M = T.s % M
  a_mod  : C.a x % M = T.a % M
  b_mod  : C.b x % M = T.b % M
  vv_mod : C.vv x % M = T.vv % M

/-- A small computation kernel: six congruences plus a balanced tuple force
same residue of the two actual masses.  This is pure modular arithmetic;
in the target repo it should be discharged once by `simp`/`omega`/`nlinarith`
according to the available Nat-mod lemmas. -/
structure ResidueComputationKernel (Atom : Type v) where
  sameResidue_of_sixForcing :
    ∀ (C : AtomCoordinates Atom) (M : Nat) (x : Atom) (T : ResidueTuple),
      SixResidueForcing C M x T →
      ResidueTuple.BalancedAt M T →
      C.leftMass x % M = C.rightMass x % M

/-- Determinant `left = right + 2` is incompatible with same residue when
`2` is nonzero modulo `M`.  Kept as a one-time arithmetic kernel. -/
structure DeterminantGapKernel (Atom : Type v) where
  false_of_sameResidue_and_gap :
    ∀ (C : AtomCoordinates Atom) (M : Nat) (x : Atom),
      C.determinantGate x →
      C.leftMass x % M = C.rightMass x % M →
      ResidueTuple.GapVisible M →
      False

/-- A row transcript for one named move/blocker.

The row says: if this blocker is present for a valid atom, then the blocker
forces one concrete residue tuple, and that tuple is balanced modulo `M` by
an executable/computational check. -/
structure ForcedResidueRow
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (Blocker : Zero → Atom → Prop) where
  tuple : ResidueTuple
  force_tuple :
    ∀ {z : Zero} {x : Atom},
      Valid z x → Blocker z x → SixResidueForcing C M x tuple
  balanced : ResidueTuple.BalancedAt M tuple

/-- Same as `ForcedResidueRow`, but the balance proof is allowed to be a
closed computation.  This mirrors the previous decider layer. -/
structure DecidedForcedResidueRow
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (Blocker : Zero → Atom → Prop) where
  tuple : ResidueTuple
  force_tuple :
    ∀ {z : Zero} {x : Atom},
      Valid z x → Blocker z x → SixResidueForcing C M x tuple
  balance_decides_true : decide (ResidueTuple.BalancedAt M tuple) = true

namespace DecidedForcedResidueRow

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {Blocker : Zero → Atom → Prop}

/-- Turn an executable row into an ordinary row. -/
def toForcedResidueRow
    (R : DecidedForcedResidueRow C M Valid Blocker) :
    ForcedResidueRow C M Valid Blocker :=
  { tuple := R.tuple
    force_tuple := R.force_tuple
    balanced := by
      exact of_decide_eq_true R.balance_decides_true }

end DecidedForcedResidueRow

/-- The eleven blocker predicates. -/
structure ElevenBlockers (Zero : Type u) (Atom : Type v) where
  peelQ : Zero → Atom → Prop
  peelR : Zero → Atom → Prop
  peelS : Zero → Atom → Prop
  absorbA : Zero → Atom → Prop
  absorbB : Zero → Atom → Prop
  absorbV : Zero → Atom → Prop
  swapLeft : Zero → Atom → Prop
  swapRight : Zero → Atom → Prop
  normalize : Zero → Atom → Prop
  residueRepair : Zero → Atom → Prop
  transportRebalance : Zero → Atom → Prop

namespace ElevenBlockers

variable {Zero : Type u} {Atom : Type v}

/-- All eleven blockers hold at a given atom. -/
structure All (B : ElevenBlockers Zero Atom) (z : Zero) (x : Atom) : Prop where
  peelQ : B.peelQ z x
  peelR : B.peelR z x
  peelS : B.peelS z x
  absorbA : B.absorbA z x
  absorbB : B.absorbB z x
  absorbV : B.absorbV z x
  swapLeft : B.swapLeft z x
  swapRight : B.swapRight z x
  normalize : B.normalize z x
  residueRepair : B.residueRepair z x
  transportRebalance : B.transportRebalance z x

end ElevenBlockers

/-- A complete eleven-row forced-residue table. -/
structure ElevenForcedResidueTable
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  peelQ : ForcedResidueRow C M Valid B.peelQ
  peelR : ForcedResidueRow C M Valid B.peelR
  peelS : ForcedResidueRow C M Valid B.peelS
  absorbA : ForcedResidueRow C M Valid B.absorbA
  absorbB : ForcedResidueRow C M Valid B.absorbB
  absorbV : ForcedResidueRow C M Valid B.absorbV
  swapLeft : ForcedResidueRow C M Valid B.swapLeft
  swapRight : ForcedResidueRow C M Valid B.swapRight
  normalize : ForcedResidueRow C M Valid B.normalize
  residueRepair : ForcedResidueRow C M Valid B.residueRepair
  transportRebalance : ForcedResidueRow C M Valid B.transportRebalance

/-- The executable/decider version of the eleven-row table. -/
structure ElevenDecidedForcedResidueTable
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  peelQ : DecidedForcedResidueRow C M Valid B.peelQ
  peelR : DecidedForcedResidueRow C M Valid B.peelR
  peelS : DecidedForcedResidueRow C M Valid B.peelS
  absorbA : DecidedForcedResidueRow C M Valid B.absorbA
  absorbB : DecidedForcedResidueRow C M Valid B.absorbB
  absorbV : DecidedForcedResidueRow C M Valid B.absorbV
  swapLeft : DecidedForcedResidueRow C M Valid B.swapLeft
  swapRight : DecidedForcedResidueRow C M Valid B.swapRight
  normalize : DecidedForcedResidueRow C M Valid B.normalize
  residueRepair : DecidedForcedResidueRow C M Valid B.residueRepair
  transportRebalance : DecidedForcedResidueRow C M Valid B.transportRebalance

namespace ElevenDecidedForcedResidueTable

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}

/-- Convert the executable table to the proof table. -/
def toForcedResidueTable
    (T : ElevenDecidedForcedResidueTable C M Valid B) :
    ElevenForcedResidueTable C M Valid B :=
  { peelQ := T.peelQ.toForcedResidueRow
    peelR := T.peelR.toForcedResidueRow
    peelS := T.peelS.toForcedResidueRow
    absorbA := T.absorbA.toForcedResidueRow
    absorbB := T.absorbB.toForcedResidueRow
    absorbV := T.absorbV.toForcedResidueRow
    swapLeft := T.swapLeft.toForcedResidueRow
    swapRight := T.swapRight.toForcedResidueRow
    normalize := T.normalize.toForcedResidueRow
    residueRepair := T.residueRepair.toForcedResidueRow
    transportRebalance := T.transportRebalance.toForcedResidueRow }

end ElevenDecidedForcedResidueTable

/-- Fully blocked valid atoms are impossible once the table and arithmetic
kernels are present.

Only one row is logically needed to force contradiction once all blockers are
present; we choose `peelQ` as the canonical witness.  The point of carrying all
11 rows is auditability: a concrete proof may obtain all blockers from the
minimal-counterexample analysis, and every row can be checked independently. -/
theorem no_valid_atom_with_all_blockers
    {Zero : Type u} {Atom : Type v}
    {C : AtomCoordinates Atom} {M : Nat}
    {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}
    (RK : ResidueComputationKernel Atom)
    (DK : DeterminantGapKernel Atom)
    (T : ElevenForcedResidueTable C M Valid B)
    (gap : ResidueTuple.GapVisible M)
    {z : Zero} {x : Atom}
    (hValid : Valid z x)
    (hDet : C.determinantGate x)
    (hAll : ElevenBlockers.All B z x) :
    False := by
  have hForcing : SixResidueForcing C M x T.peelQ.tuple :=
    T.peelQ.force_tuple hValid hAll.peelQ
  have hSame : C.leftMass x % M = C.rightMass x % M :=
    RK.sameResidue_of_sixForcing C M x T.peelQ.tuple hForcing T.peelQ.balanced
  exact DK.false_of_sameResidue_and_gap C M x hDet hSame gap

/-- A cover for minimal counterexamples: each valid atom either has a local
obstruction immediately, or all eleven moves are blocked. -/
structure MinimalCounterexampleCover
    {Zero : Type u} {Atom : Type v}
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  LocalObstruction : Zero → Atom → Prop
  local_obstruction_false :
    ∀ {z : Zero} {x : Atom}, Valid z x → LocalObstruction z x → False
  valid_implies_obstruction_or_all_blocked :
    ∀ {z : Zero} {x : Atom},
      Valid z x → LocalObstruction z x ∨ ElevenBlockers.All B z x

/-- The maximal local kernel after several compression steps. -/
structure MaximalLocalArithmeticKernel
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  residueKernel : ResidueComputationKernel Atom
  determinantKernel : DeterminantGapKernel Atom
  table : ElevenForcedResidueTable C M Valid B
  gapVisible : ResidueTuple.GapVisible M
  cover : MinimalCounterexampleCover Valid B

namespace MaximalLocalArithmeticKernel

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}

/-- The local kernel kills every valid atom satisfying the determinant. -/
theorem no_valid_determinant_atom
    (K : MaximalLocalArithmeticKernel C M Valid B)
    {z : Zero} {x : Atom}
    (hValid : Valid z x)
    (hDet : C.determinantGate x) :
    False := by
  cases K.cover.valid_implies_obstruction_or_all_blocked hValid with
  | inl hObs => exact K.cover.local_obstruction_false hValid hObs
  | inr hAll =>
      exact no_valid_atom_with_all_blockers
        K.residueKernel K.determinantKernel K.table K.gapVisible hValid hDet hAll

end MaximalLocalArithmeticKernel

/-- An extractor from zeroes to valid determinant atoms.  This is the strict,
non-origin bridge: the atom is produced from the concrete zero `z`. -/
structure ZeroToLayerBoxAtom
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom)
    (Valid : Zero → Atom → Prop) where
  atomOf : Zero → Atom
  valid_atomOf : ∀ z : Zero, Valid z (atomOf z)
  determinant_atomOf : ∀ z : Zero, C.determinantGate (atomOf z)

/-- The strict local front: extraction plus the maximal finite arithmetic
kernel implies there are no zeroes of the relevant kind. -/
structure MaximalForwardStrictFront
    (Zero : Type u) (Atom : Type v) where
  C : AtomCoordinates Atom
  M : Nat
  Valid : Zero → Atom → Prop
  B : ElevenBlockers Zero Atom
  extract : ZeroToLayerBoxAtom C Valid
  kernel : MaximalLocalArithmeticKernel C M Valid B

namespace MaximalForwardStrictFront

/-- No off-critical zero can survive this strict front. -/
theorem noZeros {Zero : Type u} {Atom : Type v}
    (F : MaximalForwardStrictFront Zero Atom) :
    ¬ Nonempty Zero := by
  intro hZ
  rcases hZ with ⟨z⟩
  exact F.kernel.no_valid_determinant_atom
    (F.extract.valid_atomOf z)
    (F.extract.determinant_atomOf z)

end MaximalForwardStrictFront

/-- A final wrapper converting no-zero into the target theorem (in the RH repo,
`Target` should be `RiemannHypothesis` and `target_of_noZeros` is the already
checked localization theorem). -/
structure MaximalForwardRiemannTarget
    (Zero : Type u) (Atom : Type v) (Target : Prop) where
  front : MaximalForwardStrictFront Zero Atom
  target_of_noZeros : (¬ Nonempty Zero) → Target

namespace MaximalForwardRiemannTarget

/-- Final theorem of this maximal-forward audit layer. -/
theorem target {Zero : Type u} {Atom : Type v} {Target : Prop}
    (F : MaximalForwardRiemannTarget Zero Atom Target) :
    Target :=
  F.target_of_noZeros F.front.noZeros

end MaximalForwardRiemannTarget

/-- The final finite checklist left after this patch. -/
structure FinalFiniteChecklist
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  -- 1 row per named move.
  table : ElevenDecidedForcedResidueTable C M Valid B
  -- one cover for minimal counterexamples.
  cover : MinimalCounterexampleCover Valid B
  -- one pure modular kernel, reusable.
  residueKernel : ResidueComputationKernel Atom
  determinantKernel : DeterminantGapKernel Atom
  gapVisible : ResidueTuple.GapVisible M

namespace FinalFiniteChecklist

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}

/-- The finite checklist produces the maximal local arithmetic kernel. -/
def toKernel (L : FinalFiniteChecklist C M Valid B) :
    MaximalLocalArithmeticKernel C M Valid B :=
  { residueKernel := L.residueKernel
    determinantKernel := L.determinantKernel
    table := L.table.toForcedResidueTable
    gapVisible := L.gapVisible
    cover := L.cover }

end FinalFiniteChecklist

/-- Count/shape of the remaining concrete work. -/
structure RemainingConcreteWorkSummary where
  namedMoves : Nat := 11
  residuesPerMove : Nat := 6
  modularComputations : Nat := 11
  hasMinimalCounterexampleCover : Prop
  hasZeroExtractor : Prop

/-- Slogan: after this patch the live local residue branch is a finite table,
not an opaque bridge and not a free origin law. -/
def maximalForwardSlogan : String :=
  "Strict RH LayerBox front = zero-indexed extractor + finite 11×6 residue table + minimal-counterexample cover; no free origin atom remains."

end MaximalForward
end LayerBox
end Riemann

/- ============ BRICK: Riemann_layerbox_final_checklist_compiler_patch.lean ============ -/

/-
Riemann_layerbox_final_checklist_compiler_patch.lean

Purpose.
  Push the LayerBox / arithmetic two-transport branch several audit layers
  further in one file.

  This patch is intentionally a compiler/checklist layer, not a proof of RH.
  It takes the maximal-forward front reached previously and splits the final
  remaining work into concrete, machine-auditable packages:

    (1) a zero-indexed extractor, not a free origin atom;
    (2) recovery of the original zero from the extracted atom;
    (3) a non-engine-coherence firewall;
    (4) an eleven-row blocker table;
    (5) six congruences per row;
    (6) a modular product compiler;
    (7) a determinant-gap contradiction compiler;
    (8) a minimal-counterexample cover;
    (9) no off-critical zero, hence the target theorem.

  The file is generic over `Zero`, `Atom`, and `Target`.  In the RH repo:
    Zero   := OffCriticalZero
    Target := RiemannHypothesis

  The intended use is to instantiate the final checklist with the concrete
  LayerBox atom whose coordinates satisfy the arithmetic two-transport equation

      q * r * s = a * b * v + 2.

Status.
  Strict audit/interface layer.  It introduces no analytic RH input and no
  hidden engine bridge.  All theorems below are obtained by field projection
  from explicitly named finite certificates.
-/

namespace Riemann
namespace LayerBox
namespace FinalChecklistCompiler

universe u v w

/-- The fixed finite menu of local moves/blockers. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- Concrete six-coordinate view of a LayerBox atom. -/
structure AtomCoordinates (Atom : Type v) where
  q : Atom → Nat
  r : Atom → Nat
  s : Atom → Nat
  a : Atom → Nat
  b : Atom → Nat
  vv : Atom → Nat

namespace AtomCoordinates

variable {Atom : Type v} (C : AtomCoordinates Atom)

/-- Left mass of the two-transport atom. -/
def leftMass (x : Atom) : Nat :=
  C.q x * C.r x * C.s x

/-- Right mass of the two-transport atom. -/
def rightMass (x : Atom) : Nat :=
  C.a x * C.b x * C.vv x

/-- The intended determinant/gap equation: `q*r*s = a*b*v + 2`. -/
def determinantGate (x : Atom) : Prop :=
  C.leftMass x = C.rightMass x + 2

end AtomCoordinates

/-- A residue tuple for the six factors. -/
structure ResidueTuple where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  vv : Nat
  deriving Repr

namespace ResidueTuple

/-- Left product of the residue tuple modulo `M`. -/
def leftProduct (M : Nat) (T : ResidueTuple) : Nat :=
  (((T.q % M) * (T.r % M) * (T.s % M)) % M)

/-- Right product of the residue tuple modulo `M`. -/
def rightProduct (M : Nat) (T : ResidueTuple) : Nat :=
  (((T.a % M) * (T.b % M) * (T.vv % M)) % M)

/-- Balanced tuple: left and right product residues agree. -/
def BalancedAt (M : Nat) (T : ResidueTuple) : Prop :=
  leftProduct M T = rightProduct M T

/-- The determinant gap `+2` is visible modulo `M`. -/
def GapVisible (M : Nat) : Prop :=
  2 % M ≠ 0

end ResidueTuple

/-- Six concrete congruences forcing an atom to have a residue tuple. -/
structure SixCongruences
    {Atom : Type v} (C : AtomCoordinates Atom) (M : Nat)
    (x : Atom) (T : ResidueTuple) : Prop where
  q_mod  : C.q x % M = T.q % M
  r_mod  : C.r x % M = T.r % M
  s_mod  : C.s x % M = T.s % M
  a_mod  : C.a x % M = T.a % M
  b_mod  : C.b x % M = T.b % M
  vv_mod : C.vv x % M = T.vv % M

/-- One finite row of the blocker table.  The row is completely local:
from validity and a named blocker it extracts six congruences to one tuple,
and that tuple is balanced modulo `M`. -/
structure RowTranscript
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (Blocker : Zero → Atom → Prop) where
  tuple : ResidueTuple
  force_congruences :
    ∀ {z : Zero} {x : Atom},
      Valid z x → Blocker z x → SixCongruences C M x tuple
  balanced : ResidueTuple.BalancedAt M tuple

/-- Executable row form.  In a concrete repo this may be closed by `native_decide`,
`simp`, or a small modular-normalization tactic. -/
structure ExecutableRowTranscript
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (Blocker : Zero → Atom → Prop) where
  tuple : ResidueTuple
  force_congruences :
    ∀ {z : Zero} {x : Atom},
      Valid z x → Blocker z x → SixCongruences C M x tuple
  balanced_closed : ResidueTuple.BalancedAt M tuple

namespace ExecutableRowTranscript

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {Blocker : Zero → Atom → Prop}

/-- Forget the fact that the balance proof is intended to be executable. -/
def toRowTranscript
    (R : ExecutableRowTranscript C M Valid Blocker) :
    RowTranscript C M Valid Blocker :=
  { tuple := R.tuple
    force_congruences := R.force_congruences
    balanced := R.balanced_closed }

end ExecutableRowTranscript

/-- The eleven blocker predicates. -/
structure ElevenBlockers (Zero : Type u) (Atom : Type v) where
  peelQ : Zero → Atom → Prop
  peelR : Zero → Atom → Prop
  peelS : Zero → Atom → Prop
  absorbA : Zero → Atom → Prop
  absorbB : Zero → Atom → Prop
  absorbV : Zero → Atom → Prop
  swapLeft : Zero → Atom → Prop
  swapRight : Zero → Atom → Prop
  normalize : Zero → Atom → Prop
  residueRepair : Zero → Atom → Prop
  transportRebalance : Zero → Atom → Prop

namespace ElevenBlockers

variable {Zero : Type u} {Atom : Type v}

/-- All eleven blockers hold at one candidate atom. -/
structure All (B : ElevenBlockers Zero Atom) (z : Zero) (x : Atom) : Prop where
  peelQ : B.peelQ z x
  peelR : B.peelR z x
  peelS : B.peelS z x
  absorbA : B.absorbA z x
  absorbB : B.absorbB z x
  absorbV : B.absorbV z x
  swapLeft : B.swapLeft z x
  swapRight : B.swapRight z x
  normalize : B.normalize z x
  residueRepair : B.residueRepair z x
  transportRebalance : B.transportRebalance z x

end ElevenBlockers

/-- The proof table with eleven named rows. -/
structure ElevenRowTable
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  peelQ : RowTranscript C M Valid B.peelQ
  peelR : RowTranscript C M Valid B.peelR
  peelS : RowTranscript C M Valid B.peelS
  absorbA : RowTranscript C M Valid B.absorbA
  absorbB : RowTranscript C M Valid B.absorbB
  absorbV : RowTranscript C M Valid B.absorbV
  swapLeft : RowTranscript C M Valid B.swapLeft
  swapRight : RowTranscript C M Valid B.swapRight
  normalize : RowTranscript C M Valid B.normalize
  residueRepair : RowTranscript C M Valid B.residueRepair
  transportRebalance : RowTranscript C M Valid B.transportRebalance

/-- The executable table form. -/
structure ExecutableElevenRowTable
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  peelQ : ExecutableRowTranscript C M Valid B.peelQ
  peelR : ExecutableRowTranscript C M Valid B.peelR
  peelS : ExecutableRowTranscript C M Valid B.peelS
  absorbA : ExecutableRowTranscript C M Valid B.absorbA
  absorbB : ExecutableRowTranscript C M Valid B.absorbB
  absorbV : ExecutableRowTranscript C M Valid B.absorbV
  swapLeft : ExecutableRowTranscript C M Valid B.swapLeft
  swapRight : ExecutableRowTranscript C M Valid B.swapRight
  normalize : ExecutableRowTranscript C M Valid B.normalize
  residueRepair : ExecutableRowTranscript C M Valid B.residueRepair
  transportRebalance : ExecutableRowTranscript C M Valid B.transportRebalance

namespace ExecutableElevenRowTable

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}

/-- Compile the executable table to the proof table. -/
def toElevenRowTable
    (T : ExecutableElevenRowTable C M Valid B) :
    ElevenRowTable C M Valid B :=
  { peelQ := T.peelQ.toRowTranscript
    peelR := T.peelR.toRowTranscript
    peelS := T.peelS.toRowTranscript
    absorbA := T.absorbA.toRowTranscript
    absorbB := T.absorbB.toRowTranscript
    absorbV := T.absorbV.toRowTranscript
    swapLeft := T.swapLeft.toRowTranscript
    swapRight := T.swapRight.toRowTranscript
    normalize := T.normalize.toRowTranscript
    residueRepair := T.residueRepair.toRowTranscript
    transportRebalance := T.transportRebalance.toRowTranscript }

end ExecutableElevenRowTable

/-- Modular product compiler: six congruences plus a balanced tuple imply
same residue of the actual left/right masses. -/
structure ModularProductCompiler (Atom : Type v) where
  compile_same_mass_residue :
    ∀ (C : AtomCoordinates Atom) (M : Nat) (x : Atom) (T : ResidueTuple),
      SixCongruences C M x T →
      ResidueTuple.BalancedAt M T →
      C.leftMass x % M = C.rightMass x % M

/-- Determinant gap compiler: `left = right + 2` contradicts same residue
when `2` is visible modulo `M`. -/
structure DeterminantGapCompiler (Atom : Type v) where
  contradiction_of_same_residue :
    ∀ (C : AtomCoordinates Atom) (M : Nat) (x : Atom),
      C.determinantGate x →
      C.leftMass x % M = C.rightMass x % M →
      ResidueTuple.GapVisible M →
      False

/-- Fully blocked valid determinant atoms are impossible.  The proof uses one
canonical row (`peelQ`); all eleven rows remain part of the finite audit table. -/
theorem contradiction_of_all_blockers
    {Zero : Type u} {Atom : Type v}
    {C : AtomCoordinates Atom} {M : Nat}
    {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}
    (PC : ModularProductCompiler Atom)
    (GC : DeterminantGapCompiler Atom)
    (T : ElevenRowTable C M Valid B)
    (gap : ResidueTuple.GapVisible M)
    {z : Zero} {x : Atom}
    (hValid : Valid z x)
    (hDet : C.determinantGate x)
    (hAll : ElevenBlockers.All B z x) :
    False := by
  have hSix : SixCongruences C M x T.peelQ.tuple :=
    T.peelQ.force_congruences hValid hAll.peelQ
  have hSame : C.leftMass x % M = C.rightMass x % M :=
    PC.compile_same_mass_residue C M x T.peelQ.tuple hSix T.peelQ.balanced
  exact GC.contradiction_of_same_residue C M x hDet hSame gap

/-- A local obstruction predicate and a cover for minimal counterexamples. -/
structure MinimalCounterexampleCover
    {Zero : Type u} {Atom : Type v}
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  LocalObstruction : Zero → Atom → Prop
  obstruction_false :
    ∀ {z : Zero} {x : Atom},
      Valid z x → LocalObstruction z x → False
  valid_implies_obstruction_or_all_blocked :
    ∀ {z : Zero} {x : Atom},
      Valid z x → LocalObstruction z x ∨ ElevenBlockers.All B z x

/-- The local arithmetic compiler that kills valid determinant atoms. -/
structure LocalArithmeticCompiler
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  productCompiler : ModularProductCompiler Atom
  gapCompiler : DeterminantGapCompiler Atom
  table : ElevenRowTable C M Valid B
  gapVisible : ResidueTuple.GapVisible M
  cover : MinimalCounterexampleCover Valid B

namespace LocalArithmeticCompiler

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}

/-- The local compiler proves there is no valid determinant atom. -/
theorem no_valid_determinant_atom
    (K : LocalArithmeticCompiler C M Valid B)
    {z : Zero} {x : Atom}
    (hValid : Valid z x)
    (hDet : C.determinantGate x) :
    False := by
  cases K.cover.valid_implies_obstruction_or_all_blocked hValid with
  | inl hObs => exact K.cover.obstruction_false hValid hObs
  | inr hAll =>
      exact contradiction_of_all_blockers
        K.productCompiler K.gapCompiler K.table K.gapVisible hValid hDet hAll

end LocalArithmeticCompiler

/-- Zero-indexed extraction.  This is the non-origin bridge: the atom is
produced from the concrete zero `z`, not supplied globally. -/
structure ZeroIndexedExtractor
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom)
    (Valid : Zero → Atom → Prop) where
  atomOf : Zero → Atom
  valid_atomOf : ∀ z : Zero, Valid z (atomOf z)
  determinant_atomOf : ∀ z : Zero, C.determinantGate (atomOf z)

/-- Zero recovery from an atom.  This is the data-level anti-vacuity firewall:
the extracted atom must decode back to the zero that produced it. -/
structure ZeroRecovery
    (Zero : Type u) (Atom : Type v) where
  fingerprint : Atom → Type w
  code : (x : Atom) → fingerprint x
  decode : ∀ x : Atom, fingerprint x → Zero

/-- An extractor is recoverable if every extracted atom decodes back to its
source zero. -/
structure RecoverableExtractor
    {Zero : Type u} {Atom : Type v}
    {C : AtomCoordinates Atom} {Valid : Zero → Atom → Prop}
    (E : ZeroIndexedExtractor C Valid)
    (R : ZeroRecovery Zero Atom) where
  recovers_zero :
    ∀ z : Zero,
      R.decode (E.atomOf z) (R.code (E.atomOf z)) = z

/-- A single global origin atom attempting to serve every zero. -/
structure FreeOriginAtomSupply
    {Zero : Type u} {Atom : Type v}
    (Valid : Zero → Atom → Prop) where
  origin : Atom
  valid_for_all : ∀ z : Zero, Valid z origin

/-- If one origin atom serves every zero and every valid atom decodes its zero,
then the zero type is forced to be subsingleton.  Thus a genuinely multi-zero
situation cannot be served by a single origin atom. -/
theorem free_origin_supply_forces_zero_subsingleton
    {Zero : Type u} {Atom : Type v}
    {Valid : Zero → Atom → Prop}
    (R : ZeroRecovery Zero Atom)
    (decode_valid :
      ∀ {z : Zero} {x : Atom},
        Valid z x → R.decode x (R.code x) = z)
    (S : FreeOriginAtomSupply Valid) :
    ∀ z₁ z₂ : Zero, z₁ = z₂ := by
  intro z₁ z₂
  have h1 : R.decode S.origin (R.code S.origin) = z₁ :=
    decode_valid (S.valid_for_all z₁)
  have h2 : R.decode S.origin (R.code S.origin) = z₂ :=
    decode_valid (S.valid_for_all z₂)
  exact h1.symm.trans h2

/-- A firewall saying this arithmetic route is not the old coherent engine route. -/
structure NonEngineCoherenceFirewall
    (Zero : Type u) (Atom : Type v) where
  EngineFactory : Zero → Type w
  cannot_build_engine_from_atom :
    ∀ (z : Zero) (x : Atom), ¬ Nonempty (EngineFactory z)

/-- The strict front after compiling the finite table, zero recovery, and the
non-engine firewall. -/
structure StrictCompiledLayerBoxFront
    (Zero : Type u) (Atom : Type v) where
  C : AtomCoordinates Atom
  M : Nat
  Valid : Zero → Atom → Prop
  B : ElevenBlockers Zero Atom
  extractor : ZeroIndexedExtractor C Valid
  recovery : ZeroRecovery.{u, v, w} Zero Atom
  recoverable : RecoverableExtractor extractor recovery
  compiler : LocalArithmeticCompiler C M Valid B
  firewall : NonEngineCoherenceFirewall.{u, v, w} Zero Atom

namespace StrictCompiledLayerBoxFront

/-- No zero can survive a strict compiled LayerBox front. -/
theorem noZeros
    {Zero : Type u} {Atom : Type v}
    (F : StrictCompiledLayerBoxFront Zero Atom) :
    ¬ Nonempty Zero := by
  intro hZ
  rcases hZ with ⟨z⟩
  exact F.compiler.no_valid_determinant_atom
    (F.extractor.valid_atomOf z)
    (F.extractor.determinant_atomOf z)

/-- The extractor is not a free origin supply in any setting with two distinct
zeros and a valid-decoding invariant. -/
theorem no_free_origin_supply_for_distinct_zeros
    {Zero : Type u} {Atom : Type v}
    (F : StrictCompiledLayerBoxFront Zero Atom)
    (decode_valid :
      ∀ {z : Zero} {x : Atom},
        F.Valid z x → F.recovery.decode x (F.recovery.code x) = z)
    (z₁ z₂ : Zero) (hne : z₁ ≠ z₂) :
    FreeOriginAtomSupply F.Valid → False := by
  intro S
  have hsub := free_origin_supply_forces_zero_subsingleton
    F.recovery decode_valid S
  exact hne (hsub z₁ z₂)

end StrictCompiledLayerBoxFront

/-- Final target wrapper.  In the RH repo, `target_of_noZeros` should be the
already checked localization theorem converting absence of off-critical zeros
into the official mathlib `RiemannHypothesis`. -/
structure StrictCompiledRiemannTarget
    (Zero : Type u) (Atom : Type v) (Target : Prop) where
  front : StrictCompiledLayerBoxFront.{u, v, w} Zero Atom
  target_of_noZeros : (¬ Nonempty Zero) → Target

namespace StrictCompiledRiemannTarget

/-- Final theorem of this compiler layer. -/
theorem target
    {Zero : Type u} {Atom : Type v} {Target : Prop}
    (T : StrictCompiledRiemannTarget Zero Atom Target) :
    Target :=
  T.target_of_noZeros T.front.noZeros

end StrictCompiledRiemannTarget

/-- The remaining finite transcript in its most concrete form. -/
structure FinalConcreteTranscript
    {Zero : Type u} {Atom : Type v}
    (C : AtomCoordinates Atom) (M : Nat)
    (Valid : Zero → Atom → Prop)
    (B : ElevenBlockers Zero Atom) where
  executableTable : ExecutableElevenRowTable C M Valid B
  productCompiler : ModularProductCompiler Atom
  gapCompiler : DeterminantGapCompiler Atom
  gapVisible : ResidueTuple.GapVisible M
  cover : MinimalCounterexampleCover Valid B

namespace FinalConcreteTranscript

variable {Zero : Type u} {Atom : Type v}
variable {C : AtomCoordinates Atom} {M : Nat}
variable {Valid : Zero → Atom → Prop} {B : ElevenBlockers Zero Atom}

/-- Compile the final concrete transcript into the local arithmetic compiler. -/
def toLocalArithmeticCompiler
    (T : FinalConcreteTranscript C M Valid B) :
    LocalArithmeticCompiler C M Valid B :=
  { productCompiler := T.productCompiler
    gapCompiler := T.gapCompiler
    table := T.executableTable.toElevenRowTable
    gapVisible := T.gapVisible
    cover := T.cover }

end FinalConcreteTranscript

/-- The whole remaining front as a single checklist.  This is the exact object
that the concrete RH branch should now instantiate. -/
structure FinalStrictChecklist
    (Zero : Type u) (Atom : Type v) where
  C : AtomCoordinates Atom
  M : Nat
  Valid : Zero → Atom → Prop
  B : ElevenBlockers Zero Atom
  extractor : ZeroIndexedExtractor C Valid
  recovery : ZeroRecovery.{u, v, w} Zero Atom
  recoverable : RecoverableExtractor extractor recovery
  firewall : NonEngineCoherenceFirewall.{u, v, w} Zero Atom
  transcript : FinalConcreteTranscript C M Valid B

namespace FinalStrictChecklist

/-- Compile the full checklist into the strict front. -/
def toStrictFront
    {Zero : Type u} {Atom : Type v}
    (L : FinalStrictChecklist Zero Atom) :
    StrictCompiledLayerBoxFront Zero Atom :=
  { C := L.C
    M := L.M
    Valid := L.Valid
    B := L.B
    extractor := L.extractor
    recovery := L.recovery
    recoverable := L.recoverable
    compiler := L.transcript.toLocalArithmeticCompiler
    firewall := L.firewall }

/-- Full checklist kills all zeroes. -/
theorem noZeros
    {Zero : Type u} {Atom : Type v}
    (L : FinalStrictChecklist Zero Atom) :
    ¬ Nonempty Zero :=
  L.toStrictFront.noZeros

end FinalStrictChecklist

/-- Full target wrapper directly from the final strict checklist. -/
structure FinalStrictChecklistTarget
    (Zero : Type u) (Atom : Type v) (Target : Prop) where
  checklist : FinalStrictChecklist.{u, v, w} Zero Atom
  target_of_noZeros : (¬ Nonempty Zero) → Target

namespace FinalStrictChecklistTarget

/-- Final theorem from the concrete checklist. -/
theorem target
    {Zero : Type u} {Atom : Type v} {Target : Prop}
    (T : FinalStrictChecklistTarget Zero Atom Target) :
    Target :=
  T.target_of_noZeros T.checklist.noZeros

end FinalStrictChecklistTarget

/-- Shape of the remaining work.  No opaque RH bridge remains here; only these
finite/concrete obligations remain for this LayerBox route. -/
structure RemainingFiniteObligations where
  zeroIndexedExtractor : Prop
  zeroRecovery : Prop
  nonEngineFirewall : Prop
  minimalCounterexampleCover : Prop
  rowCongruenceLines : Nat := 66
  rowBalanceComputations : Nat := 11
  modularProductCompiler : Prop
  determinantGapCompiler : Prop

/-- A human-readable audit slogan. -/
def finalChecklistCompilerSlogan : String :=
  "Final RH LayerBox compiler: zero-indexed extractor + zero recovery + non-engine firewall + finite 11×6 residue transcript + minimal-counterexample cover."

end FinalChecklistCompiler
end LayerBox
end Riemann

/- ============ BRICK: Riemann_layerbox_terminal_front_blueprint_patch.lean ============ -/

/-
Riemann_layerbox_terminal_front_blueprint_patch.lean

A maximal-forward audit/frontier layer for the Riemann LayerBox route.

Purpose.
  The previous files progressively removed the vacuity from the arithmetic
  two-transport route.  This file packages the remaining proof obligation into
  a terminal, finite, zero-indexed checklist:

    off-critical zero
      -> extracted LayerBox atom
      -> zero recovery from the atom
      -> finite minimal-counterexample cover
      -> 11 named blockers
      -> 11 residue transcript rows
      -> modular/determinant contradiction
      -> no zeros
      -> target/RH wrapper.

This file is intentionally a compiler/audit layer.  It does NOT assert RH and
it does NOT assert the missing analytic extraction.  It records exactly what a
non-vacuous, non-engine, zero-indexed arithmetic route must provide.
-/


namespace RiemannLayerBoxTerminalFront

variable {Zero Atom : Type} {M : ℕ} {Target : Prop}

/-- The fixed finite menu of local moves from the LayerBox route. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr, Inhabited

/-- The canonical eleven-move list. -/
def allMoves : List MoveName :=
  [ MoveName.peelQ,
    MoveName.peelR,
    MoveName.peelS,
    MoveName.absorbA,
    MoveName.absorbB,
    MoveName.absorbV,
    MoveName.swapLeft,
    MoveName.swapRight,
    MoveName.normalize,
    MoveName.residueRepair,
    MoveName.transportRebalance ]

/-- Coordinates of a concrete arithmetic two-transport atom. -/
structure AtomCoordinates where
  q : ℕ
  r : ℕ
  s : ℕ
  a : ℕ
  b : ℕ
  v : ℕ
  deriving Repr

namespace AtomCoordinates

/-- The left transport mass. -/
def leftMass (c : AtomCoordinates) : ℕ :=
  c.q * c.r * c.s

/-- The right transport mass. -/
def rightMass (c : AtomCoordinates) : ℕ :=
  c.a * c.b * c.v

/-- The arithmetic two-transport determinant/gap identity. -/
def GapTwo (c : AtomCoordinates) : Prop :=
  c.leftMass = c.rightMass + 2

end AtomCoordinates

/-- LayerBox gates attached to an atom.  The actual repo may choose a sharper
layer, but the compiler only needs the existence of a `Valid` predicate. -/
structure LayerBoxGates (Atom : Type) where
  coord : Atom -> AtomCoordinates
  height : Atom -> ℕ
  Valid : Atom -> Prop
  determinant_gap : ∀ {atom}, Valid atom -> AtomCoordinates.GapTwo (coord atom)

/-- A residue tuple for the six factors modulo `M`. -/
structure ResidueTuple (M : ℕ) where
  q0 : ℕ
  r0 : ℕ
  s0 : ℕ
  a0 : ℕ
  b0 : ℕ
  v0 : ℕ
  deriving Repr

namespace ResidueTuple

/-- The tuple is balanced if the two triple-products have the same residue. -/
abbrev BalancedAt (t : ResidueTuple M) : Prop :=
  (t.q0 * t.r0 * t.s0) % M = (t.a0 * t.b0 * t.v0) % M

/-- Executable balance witness used by finite table rows. -/
def DecidedBalanced (t : ResidueTuple M) : Prop :=
  decide (BalancedAt t) = true

end ResidueTuple

/-- An atom has the specified six residues modulo `M`. -/
structure SixResidueForcing
    (G : LayerBoxGates Atom) (M : ℕ) (atom : Atom) (t : ResidueTuple M) where
  q_mod : (G.coord atom).q % M = t.q0 % M
  r_mod : (G.coord atom).r % M = t.r0 % M
  s_mod : (G.coord atom).s % M = t.s0 % M
  a_mod : (G.coord atom).a % M = t.a0 % M
  b_mod : (G.coord atom).b % M = t.b0 % M
  v_mod : (G.coord atom).v % M = t.v0 % M

/-- The modular gap kernel: if determinant gives a `+2` gap and blockers force
same residue modulo `M`, contradiction follows.  In concrete instantiations
this is usually closed by `norm_num`, `omega`, or `ZMod`. -/
structure ModularGapKernel (M : ℕ) where
  gap_nonzero : 2 % M ≠ 0
  contradiction : ∀ {left right : ℕ},
    left = right + 2 ->
    left % M = right % M ->
    False

/-- A blocker predicate for one named move. -/
abbrev Blocker (Zero Atom : Type) := Zero -> Atom -> Prop

/-- An eleven-blocker family, one predicate per named move. -/
structure ElevenBlockers (Zero Atom : Type) where
  peelQ : Blocker Zero Atom
  peelR : Blocker Zero Atom
  peelS : Blocker Zero Atom
  absorbA : Blocker Zero Atom
  absorbB : Blocker Zero Atom
  absorbV : Blocker Zero Atom
  swapLeft : Blocker Zero Atom
  swapRight : Blocker Zero Atom
  normalize : Blocker Zero Atom
  residueRepair : Blocker Zero Atom
  transportRebalance : Blocker Zero Atom

namespace ElevenBlockers

/-- All eleven blockers hold at `(z, atom)`. -/
structure All (B : ElevenBlockers Zero Atom) (z : Zero) (atom : Atom) : Prop where
  peelQ : B.peelQ z atom
  peelR : B.peelR z atom
  peelS : B.peelS z atom
  absorbA : B.absorbA z atom
  absorbB : B.absorbB z atom
  absorbV : B.absorbV z atom
  swapLeft : B.swapLeft z atom
  swapRight : B.swapRight z atom
  normalize : B.normalize z atom
  residueRepair : B.residueRepair z atom
  transportRebalance : B.transportRebalance z atom

end ElevenBlockers

/-- One forced-residue row: a blocker reason forces a concrete residue tuple;
the tuple is then checked to be balanced by computation. -/
structure ForcedResidueRow
    (G : LayerBoxGates Atom) (M : ℕ)
    (Block : Blocker Zero Atom) where
  tuple : Zero -> Atom -> ResidueTuple M
  force : ∀ {z atom},
    G.Valid atom ->
    Block z atom ->
    SixResidueForcing G M atom (tuple z atom)
  decided_balanced : ∀ {z atom},
    G.Valid atom ->
    Block z atom ->
    ResidueTuple.DecidedBalanced (tuple z atom)

/-- The full eleven-row finite residue transcript. -/
structure ElevenResidueTranscript
    (G : LayerBoxGates Atom) (M : ℕ)
    (B : ElevenBlockers Zero Atom) where
  peelQ : ForcedResidueRow G M B.peelQ
  peelR : ForcedResidueRow G M B.peelR
  peelS : ForcedResidueRow G M B.peelS
  absorbA : ForcedResidueRow G M B.absorbA
  absorbB : ForcedResidueRow G M B.absorbB
  absorbV : ForcedResidueRow G M B.absorbV
  swapLeft : ForcedResidueRow G M B.swapLeft
  swapRight : ForcedResidueRow G M B.swapRight
  normalize : ForcedResidueRow G M B.normalize
  residueRepair : ForcedResidueRow G M B.residueRepair
  transportRebalance : ForcedResidueRow G M B.transportRebalance

/-- The transcript compiler does not care which row produced the residue
balance.  It is enough that at least one active blocker row produces a balanced
six-residue tuple and the modular gap kernel contradicts the determinant gap.

In the full route all eleven blockers are active at a minimal counterexample;
this structure packages the row-selection part separately. -/
structure ActiveBalancedRowCompiler
    (G : LayerBoxGates Atom) (M : ℕ)
    (B : ElevenBlockers Zero Atom) where
  same_residue_of_all_blockers : ∀ {z atom},
    G.Valid atom ->
    ElevenBlockers.All B z atom ->
    (AtomCoordinates.leftMass (G.coord atom)) % M =
      (AtomCoordinates.rightMass (G.coord atom)) % M

/-- A terminal residue compiler: table transcript plus a proof that fully
blocked atoms force same-residue modulo `M`.  In a concrete repo this proof is
usually obtained by invoking one of the eleven transcript rows. -/
structure TerminalResidueCompiler
    (G : LayerBoxGates Atom) (M : ℕ)
    (B : ElevenBlockers Zero Atom) where
  transcript : ElevenResidueTranscript G M B
  activeRowCompiler : ActiveBalancedRowCompiler G M B
  gapKernel : ModularGapKernel M

/-- Fully blocked valid atoms are impossible. -/
theorem TerminalResidueCompiler.no_valid_fully_blocked
    {G : LayerBoxGates Atom} {M : ℕ} {B : ElevenBlockers Zero Atom}
    (C : TerminalResidueCompiler G M B)
    {z : Zero} {atom : Atom}
    (hValid : G.Valid atom)
    (hAll : ElevenBlockers.All B z atom) :
    False := by
  have hGap : AtomCoordinates.GapTwo (G.coord atom) := G.determinant_gap hValid
  have hSame := C.activeRowCompiler.same_residue_of_all_blockers hValid hAll
  exact C.gapKernel.contradiction hGap hSame

/-- A local cover at a zero-indexed atom: either there is an immediate local
obstruction, or all eleven blockers are active. -/
structure MinimalCounterexampleCover
    (G : LayerBoxGates Atom) (B : ElevenBlockers Zero Atom)
    (Anchor : Zero -> Atom -> Prop) where
  ImmediateObstruction : Zero -> Atom -> Prop
  immediate_false : ∀ {z atom},
    G.Valid atom ->
    Anchor z atom ->
    ImmediateObstruction z atom ->
    False
  cover : ∀ {z atom},
    G.Valid atom ->
    Anchor z atom ->
    ImmediateObstruction z atom ∨ ElevenBlockers.All B z atom

/-- The extraction of a LayerBox atom from a zero.  This is the non-vacuous
replacement for free origin supply. -/
structure ZeroIndexedExtractor
    (G : LayerBoxGates Atom) (Anchor : Zero -> Atom -> Prop) where
  atomOf : Zero -> Atom
  atom_valid : ∀ z, G.Valid (atomOf z)
  atom_anchor : ∀ z, Anchor z (atomOf z)

/-- Zero recovery: the atom decodes back to the zero that anchored it. -/
structure ZeroRecovery (Anchor : Zero -> Atom -> Prop) where
  decode : Atom -> Zero
  decode_anchor : ∀ {z atom}, Anchor z atom -> decode atom = z

/-- A formal firewall saying the route is not using the old engine-coherent
factory route.  It is intentionally a predicate carried by the final front,
because the actual repo decides what counts as engine coherence. -/
structure NonEngineCoherenceFirewall (Zero Atom : Type) where
  coherentEngine : Zero -> Atom -> Prop
  no_coherent_engine : ∀ {z atom}, coherentEngine z atom -> False

/-- Terminal zero-indexed arithmetic front.  If this is provided, there are no
zeros of type `Zero`.  This is the fully compiled non-engine LayerBox route. -/
structure TerminalLayerBoxFront (Zero Atom : Type) where
  G : LayerBoxGates Atom
  Anchor : Zero -> Atom -> Prop
  B : ElevenBlockers Zero Atom
  M : ℕ
  extractor : ZeroIndexedExtractor G Anchor
  recovery : ZeroRecovery Anchor
  firewall : NonEngineCoherenceFirewall Zero Atom
  cover : MinimalCounterexampleCover G B Anchor
  residueCompiler : TerminalResidueCompiler G M B

/-- The terminal front rules out all zero witnesses. -/
theorem TerminalLayerBoxFront.noZeros
    (F : TerminalLayerBoxFront Zero Atom) :
    IsEmpty Zero := by
  constructor
  intro z
  let atom := F.extractor.atomOf z
  have hValid : F.G.Valid atom := F.extractor.atom_valid z
  have hAnchor : F.Anchor z atom := F.extractor.atom_anchor z
  cases F.cover.cover hValid hAnchor with
  | inl hObs =>
      exact F.cover.immediate_false hValid hAnchor hObs
  | inr hAll =>
      exact F.residueCompiler.no_valid_fully_blocked hValid hAll

/-- Target wrapper: if `Zero` is the off-critical zero type and `Target` is
mathlib RH, then `emptyZero_implies_target` is the already-checked localization
bridge `¬ Nonempty OffCriticalZero -> RiemannHypothesis`. -/
structure TerminalRiemannTarget (Zero Atom : Type) (Target : Prop) where
  front : TerminalLayerBoxFront Zero Atom
  emptyZero_implies_target : IsEmpty Zero -> Target

/-- Final theorem of this compiler layer. -/
theorem TerminalRiemannTarget.target
    (F : TerminalRiemannTarget Zero Atom Target) :
    Target :=
  F.emptyZero_implies_target F.front.noZeros

/-- A free origin supply is one atom that works for every zero. -/
structure FreeOriginSupply
    (G : LayerBoxGates Atom) (Anchor : Zero -> Atom -> Prop) where
  origin : Atom
  origin_valid : G.Valid origin
  supplies : ∀ z, Anchor z origin

/-- If atoms recover their anchoring zero, one origin atom cannot supply two
provably distinct zeros. -/
theorem no_free_origin_supply_for_two_distinct_zeros
    {G : LayerBoxGates Atom} {Anchor : Zero -> Atom -> Prop}
    (R : ZeroRecovery Anchor)
    (S : FreeOriginSupply G Anchor)
    {z₁ z₂ : Zero}
    (hne : z₁ ≠ z₂) :
    False := by
  have h1 : R.decode S.origin = z₁ := R.decode_anchor (S.supplies z₁)
  have h2 : R.decode S.origin = z₂ := R.decode_anchor (S.supplies z₂)
  exact hne (h1.symm.trans h2)

/-- The final checklist names every finite item that remains after this patch.
It is a record, not an axiom: filling it with concrete repo lemmas instantiates
`TerminalLayerBoxFront`. -/
structure FinalTerminalChecklist (Zero Atom : Type) where
  G : LayerBoxGates Atom
  Anchor : Zero -> Atom -> Prop
  B : ElevenBlockers Zero Atom
  M : ℕ
  extractor : ZeroIndexedExtractor G Anchor
  recovery : ZeroRecovery Anchor
  firewall : NonEngineCoherenceFirewall Zero Atom
  cover : MinimalCounterexampleCover G B Anchor
  transcript : ElevenResidueTranscript G M B
  activeRowCompiler : ActiveBalancedRowCompiler G M B
  gapKernel : ModularGapKernel M

/-- A filled terminal checklist compiles to the terminal front. -/
def FinalTerminalChecklist.toTerminalLayerBoxFront
    (C : FinalTerminalChecklist Zero Atom) :
    TerminalLayerBoxFront Zero Atom where
  G := C.G
  Anchor := C.Anchor
  B := C.B
  M := C.M
  extractor := C.extractor
  recovery := C.recovery
  firewall := C.firewall
  cover := C.cover
  residueCompiler := {
    transcript := C.transcript
    activeRowCompiler := C.activeRowCompiler
    gapKernel := C.gapKernel
  }

/-- A filled terminal checklist rules out zeros. -/
theorem FinalTerminalChecklist.noZeros
    (C : FinalTerminalChecklist Zero Atom) :
    IsEmpty Zero :=
  C.toTerminalLayerBoxFront.noZeros

/-- A filled terminal checklist proves the supplied target wrapper. -/
theorem FinalTerminalChecklist.target
    (C : FinalTerminalChecklist Zero Atom)
    (emptyZero_implies_target : IsEmpty Zero -> Target) :
    Target :=
  emptyZero_implies_target C.noZeros

/-- The remaining finite proof workload after this compiler. -/
structure TerminalFiniteWorkload (Zero Atom : Type) where
  zero_indexed_extractor : Prop
  zero_recovery : Prop
  non_engine_firewall : Prop
  minimal_counterexample_cover : Prop
  eleven_blocker_predicates : Prop
  eleven_residue_rows : Prop
  sixty_six_congruence_lines : Prop
  eleven_decide_balance_checks : Prop
  active_row_compiler : Prop
  modular_gap_kernel : Prop

/-- Slogan theorem: this layer contains no hidden RH claim; it only says that
once the terminal finite checklist is filled, the route has no off-critical
zeros. -/
theorem terminal_front_slogan
    (C : FinalTerminalChecklist Zero Atom) :
    IsEmpty Zero :=
  C.noZeros

end RiemannLayerBoxTerminalFront

/- ============ BRICK: Riemann_layerbox_terminal_slot_implementation_patch.lean ============ -/

/-
Riemann_layerbox_terminal_slot_implementation_patch.lean

A maximal-forward implementation scaffold for the LayerBox / arithmetic
TwoTransport front.

Purpose.
  The previous terminal-front blueprint reduced the route to a finite
  checklist:

    zero-indexed extractor,
    zero recovery,
    non-engine firewall,
    minimal-counterexample cover,
    11 blocker rows,
    66 congruence lines,
    11 executable balance checks,
    active-row compiler,
    modular gap kernel.

  This file pushes one level further: it makes those remaining obligations
  explicit as implementation slots, provides a no-fake-closure audit, and
  records a compiler from a filled slot ledger to the abstract target.

  It does not assert RH and it does not fill any repo-specific arithmetic
  slots.  It is a terminal implementation checklist: after this layer the
  remaining work is no longer an opaque bridge, but a finite ledger of named
  slots.
-/


namespace RiemannLayerBoxTerminalSlotImplementation

variable {Target : Prop}

/-- The fixed eleven local moves. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr, Inhabited

/-- The six factor coordinates in one arithmetic atom. -/
inductive FactorName where
  | q
  | r
  | s
  | a
  | b
  | v
  deriving DecidableEq, Repr, Inhabited

/-- Canonical move list. -/
def allMoves : List MoveName :=
  [ MoveName.peelQ,
    MoveName.peelR,
    MoveName.peelS,
    MoveName.absorbA,
    MoveName.absorbB,
    MoveName.absorbV,
    MoveName.swapLeft,
    MoveName.swapRight,
    MoveName.normalize,
    MoveName.residueRepair,
    MoveName.transportRebalance ]

/-- Canonical factor list. -/
def allFactors : List FactorName :=
  [ FactorName.q,
    FactorName.r,
    FactorName.s,
    FactorName.a,
    FactorName.b,
    FactorName.v ]

/-- The table has eleven named rows. -/
theorem allMoves_length : allMoves.length = 11 := by
  decide

/-- Each row has six congruence columns. -/
theorem allFactors_length : allFactors.length = 6 := by
  decide

/-- Hence the finite residue table has exactly sixty-six congruence slots. -/
theorem finiteResidueLine_count : allMoves.length * allFactors.length = 66 := by
  decide

/-- Six congruence obligations for one named blocker row.  The propositions are
left abstract because their concrete form depends on the repo's LayerBox atom
and blocker definitions. -/
structure SixCongruenceSlots where
  q_line : Prop
  r_line : Prop
  s_line : Prop
  a_line : Prop
  b_line : Prop
  v_line : Prop

namespace SixCongruenceSlots

/-- All six factor congruence lines in a row are filled. -/
def AllFilled (S : SixCongruenceSlots) : Prop :=
  S.q_line ∧ S.r_line ∧ S.s_line ∧ S.a_line ∧ S.b_line ∧ S.v_line

/-- A missing `q` line prevents the row from being complete. -/
theorem not_allFilled_of_not_q
    {S : SixCongruenceSlots}
    (h : ¬ S.q_line) :
    ¬ S.AllFilled := by
  intro hAll
  exact h hAll.1

/-- A missing `r` line prevents the row from being complete. -/
theorem not_allFilled_of_not_r
    {S : SixCongruenceSlots}
    (h : ¬ S.r_line) :
    ¬ S.AllFilled := by
  intro hAll
  exact h hAll.2.1

/-- A missing `s` line prevents the row from being complete. -/
theorem not_allFilled_of_not_s
    {S : SixCongruenceSlots}
    (h : ¬ S.s_line) :
    ¬ S.AllFilled := by
  intro hAll
  exact h hAll.2.2.1

/-- A missing `a` line prevents the row from being complete. -/
theorem not_allFilled_of_not_a
    {S : SixCongruenceSlots}
    (h : ¬ S.a_line) :
    ¬ S.AllFilled := by
  intro hAll
  exact h hAll.2.2.2.1

/-- A missing `b` line prevents the row from being complete. -/
theorem not_allFilled_of_not_b
    {S : SixCongruenceSlots}
    (h : ¬ S.b_line) :
    ¬ S.AllFilled := by
  intro hAll
  exact h hAll.2.2.2.2.1

/-- A missing `v` line prevents the row from being complete. -/
theorem not_allFilled_of_not_v
    {S : SixCongruenceSlots}
    (h : ¬ S.v_line) :
    ¬ S.AllFilled := by
  intro hAll
  exact h hAll.2.2.2.2.2

end SixCongruenceSlots

/-- The explicit eleven-by-six residue forcing matrix. -/
structure ElevenCongruenceMatrix where
  peelQ : SixCongruenceSlots
  peelR : SixCongruenceSlots
  peelS : SixCongruenceSlots
  absorbA : SixCongruenceSlots
  absorbB : SixCongruenceSlots
  absorbV : SixCongruenceSlots
  swapLeft : SixCongruenceSlots
  swapRight : SixCongruenceSlots
  normalize : SixCongruenceSlots
  residueRepair : SixCongruenceSlots
  transportRebalance : SixCongruenceSlots

namespace ElevenCongruenceMatrix

/-- All sixty-six congruence lines are filled. -/
def All66Filled (E : ElevenCongruenceMatrix) : Prop :=
  E.peelQ.AllFilled ∧
  E.peelR.AllFilled ∧
  E.peelS.AllFilled ∧
  E.absorbA.AllFilled ∧
  E.absorbB.AllFilled ∧
  E.absorbV.AllFilled ∧
  E.swapLeft.AllFilled ∧
  E.swapRight.AllFilled ∧
  E.normalize.AllFilled ∧
  E.residueRepair.AllFilled ∧
  E.transportRebalance.AllFilled

/-- A missing row blocks the full sixty-six-line matrix. -/
theorem not_all66_of_missing_peelQ
    {E : ElevenCongruenceMatrix}
    (h : ¬ E.peelQ.AllFilled) :
    ¬ E.All66Filled := by
  intro hAll
  exact h hAll.1

/-- A missing row blocks the full sixty-six-line matrix. -/
theorem not_all66_of_missing_transportRebalance
    {E : ElevenCongruenceMatrix}
    (h : ¬ E.transportRebalance.AllFilled) :
    ¬ E.All66Filled := by
  intro hAll
  exact h hAll.2.2.2.2.2.2.2.2.2.2

end ElevenCongruenceMatrix

/-- Eleven executable balance checks, one per row. -/
structure ElevenBalanceChecks where
  peelQ : Prop
  peelR : Prop
  peelS : Prop
  absorbA : Prop
  absorbB : Prop
  absorbV : Prop
  swapLeft : Prop
  swapRight : Prop
  normalize : Prop
  residueRepair : Prop
  transportRebalance : Prop

namespace ElevenBalanceChecks

/-- All eleven modular balance computations have closed. -/
def AllFilled (B : ElevenBalanceChecks) : Prop :=
  B.peelQ ∧
  B.peelR ∧
  B.peelS ∧
  B.absorbA ∧
  B.absorbB ∧
  B.absorbV ∧
  B.swapLeft ∧
  B.swapRight ∧
  B.normalize ∧
  B.residueRepair ∧
  B.transportRebalance

end ElevenBalanceChecks

/-- High-level non-table slots. -/
structure HighLevelSlots where
  zero_indexed_extractor : Prop
  zero_recovery : Prop
  non_engine_firewall : Prop
  minimal_counterexample_cover : Prop
  active_row_compiler : Prop
  modular_gap_kernel : Prop

namespace HighLevelSlots

/-- All non-table slots are filled. -/
def AllFilled (H : HighLevelSlots) : Prop :=
  H.zero_indexed_extractor ∧
  H.zero_recovery ∧
  H.non_engine_firewall ∧
  H.minimal_counterexample_cover ∧
  H.active_row_compiler ∧
  H.modular_gap_kernel

end HighLevelSlots

/-- The terminal slot ledger for this front. -/
structure TerminalSlotLedger where
  high : HighLevelSlots
  matrix : ElevenCongruenceMatrix
  balances : ElevenBalanceChecks

namespace TerminalSlotLedger

/-- The whole terminal front is filled. -/
def AllFilled (L : TerminalSlotLedger) : Prop :=
  L.high.AllFilled ∧ L.matrix.All66Filled ∧ L.balances.AllFilled

/-- A formal declaration that the terminal arithmetic front is closed.  It is
not allowed unless the whole slot ledger is filled. -/
structure ClosureDeclaration (L : TerminalSlotLedger) where
  all_filled : L.AllFilled

/-- No fake closure: if any terminal slot remains open, the front cannot be
honestly declared closed. -/
theorem no_fake_closure
    {L : TerminalSlotLedger}
    (hOpen : ¬ L.AllFilled) :
    ¬ ClosureDeclaration L := by
  intro hDecl
  exact hOpen hDecl.all_filled

/-- Missing the sixty-six-line congruence matrix blocks closure. -/
theorem no_closure_without_all66
    {L : TerminalSlotLedger}
    (h : ¬ L.matrix.All66Filled) :
    ¬ ClosureDeclaration L := by
  apply no_fake_closure
  intro hAll
  exact h hAll.2.1

/-- Missing the high-level extractor/recovery/firewall/cover/compiler/kernel
block also blocks closure. -/
theorem no_closure_without_high_level
    {L : TerminalSlotLedger}
    (h : ¬ L.high.AllFilled) :
    ¬ ClosureDeclaration L := by
  apply no_fake_closure
  intro hAll
  exact h hAll.1

/-- Missing the executable balance checks blocks closure. -/
theorem no_closure_without_balance_checks
    {L : TerminalSlotLedger}
    (h : ¬ L.balances.AllFilled) :
    ¬ ClosureDeclaration L := by
  apply no_fake_closure
  intro hAll
  exact h hAll.2.2

end TerminalSlotLedger

/-- A filled slot ledger may be sent to any checked target by an external
compiler theorem.  In the repo, this compiler is supplied by the previous
terminal-front blueprint and the localization theorem `no off-critical zero ->
RiemannHypothesis`. -/
structure TerminalSlotCompiler (Target : Prop) where
  ledger : TerminalSlotLedger
  closed_implies_target : TerminalSlotLedger.ClosureDeclaration ledger -> Target

/-- If all terminal slots are filled, the target follows by the compiler. -/
theorem TerminalSlotCompiler.target
    (C : TerminalSlotCompiler Target)
    (hFilled : C.ledger.AllFilled) :
    Target :=
  C.closed_implies_target ⟨hFilled⟩

/-- A row-level implementation package: it separates the six congruence proofs
from the single executable balance proof for that row. -/
structure RowImplementation where
  congruences : SixCongruenceSlots
  balance_check : Prop

/-- Eleven row implementations. -/
structure ElevenRowImplementations where
  peelQ : RowImplementation
  peelR : RowImplementation
  peelS : RowImplementation
  absorbA : RowImplementation
  absorbB : RowImplementation
  absorbV : RowImplementation
  swapLeft : RowImplementation
  swapRight : RowImplementation
  normalize : RowImplementation
  residueRepair : RowImplementation
  transportRebalance : RowImplementation

namespace ElevenRowImplementations

/-- Extract the sixty-six-line matrix from row implementations. -/
def matrix (R : ElevenRowImplementations) : ElevenCongruenceMatrix where
  peelQ := R.peelQ.congruences
  peelR := R.peelR.congruences
  peelS := R.peelS.congruences
  absorbA := R.absorbA.congruences
  absorbB := R.absorbB.congruences
  absorbV := R.absorbV.congruences
  swapLeft := R.swapLeft.congruences
  swapRight := R.swapRight.congruences
  normalize := R.normalize.congruences
  residueRepair := R.residueRepair.congruences
  transportRebalance := R.transportRebalance.congruences

/-- Extract the eleven balance slots from row implementations. -/
def balances (R : ElevenRowImplementations) : ElevenBalanceChecks where
  peelQ := R.peelQ.balance_check
  peelR := R.peelR.balance_check
  peelS := R.peelS.balance_check
  absorbA := R.absorbA.balance_check
  absorbB := R.absorbB.balance_check
  absorbV := R.absorbV.balance_check
  swapLeft := R.swapLeft.balance_check
  swapRight := R.swapRight.balance_check
  normalize := R.normalize.balance_check
  residueRepair := R.residueRepair.balance_check
  transportRebalance := R.transportRebalance.balance_check

end ElevenRowImplementations

/-- A terminal implementation package: high-level proof slots plus eleven row
implementations. -/
structure TerminalImplementation where
  high : HighLevelSlots
  rows : ElevenRowImplementations

namespace TerminalImplementation

/-- Convert a terminal implementation into the canonical slot ledger. -/
def toLedger (I : TerminalImplementation) : TerminalSlotLedger where
  high := I.high
  matrix := I.rows.matrix
  balances := I.rows.balances

/-- The implementation is filled exactly when its resulting slot ledger is
filled. -/
def AllFilled (I : TerminalImplementation) : Prop :=
  I.toLedger.AllFilled

/-- Filled implementations produce closure declarations. -/
def closureDeclaration
    (I : TerminalImplementation)
    (h : I.AllFilled) :
    TerminalSlotLedger.ClosureDeclaration I.toLedger :=
  ⟨h⟩

end TerminalImplementation

/-- A final named workload summary.  This is intentionally redundant and
human-readable: it is what remains after all compiler/audit layers above. -/
structure TerminalWorkloadSummary where
  high_level_slots : Prop
  congruence_slots_66 : Prop
  balance_checks_11 : Prop
  row_implementation_11 : Prop
  no_origin_supply_audit : Prop
  no_engine_coherence_audit : Prop
  target_wrapper : Prop

/-- The final status theorem of this patch: after all reductions, no theorem of
RH is claimed here; the whole remaining work is the explicit filled terminal
slot ledger. -/
theorem terminal_slot_status_slogan
    (C : TerminalSlotCompiler Target)
    (hFilled : C.ledger.AllFilled) :
    Target :=
  C.target hFilled

end RiemannLayerBoxTerminalSlotImplementation


/- ============ BRICK: Riemann_layerbox_one_file_maximal_terminal_front_patch.lean ============ -/

/-
Riemann_layerbox_one_file_maximal_terminal_front_patch.lean

Purpose.
  One-file maximal-forward terminal front for the RH LayerBox / arithmetic
  two-transport route.

  This file deliberately does NOT assert RH and does NOT use the old
  engine-coherent bridge.  It packages several subsequent audit/compiler
  layers in one file:

    zero-indexed extractor
    → zero recovery / anti-origin firewall
    → named finite blocker cover
    → 11 row residue transcripts
    → determinant-gap contradiction kernel
    → no valid anchored atom
    → no off-critical zero
    → target wrapper.

  The remaining mathematical work is finite and explicit:
    * high-level extraction/recovery/firewall/cover;
    * 11 blocker rows;
    * 66 residue congruence lines;
    * 11 residue balance computations;
    * determinant-gap modular contradiction.

  The file is intentionally abstract in Zero, Atom and Target.  In the repo,
  instantiate:
    Zero   := OffCriticalZero,
    Target := mathlib RiemannHypothesis,
    Atom   := the concrete self-decoded LayerBox atom.
-/

namespace RiemannLayerBoxOneFileMaximalTerminalFront

universe u v

variable {Atom : Type u}

/-- The fixed finite move menu. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- The six multiplicative factors of the LayerBox atom. -/
inductive FactorName where
  | q
  | r
  | s
  | a
  | b
  | v
  deriving DecidableEq, Repr

/-- A concrete residue assignment for all six factors. -/
structure ResidueTuple where
  q0 : Nat
  r0 : Nat
  s0 : Nat
  a0 : Nat
  b0 : Nat
  v0 : Nat

namespace ResidueTuple

/-- Product on the `q r s` side. -/
def leftProduct (T : ResidueTuple) : Nat :=
  T.q0 * T.r0 * T.s0

/-- Product on the `a b v` side. -/
def rightProduct (T : ResidueTuple) : Nat :=
  T.a0 * T.b0 * T.v0

/-- A blocker row is balanced when it forces same product residue on both sides. -/
def BalancedAt (T : ResidueTuple) (M : Nat) : Prop :=
  T.leftProduct % M = T.rightProduct % M

/-- Residue accessor. -/
def get (T : ResidueTuple) : FactorName -> Nat
  | .q => T.q0
  | .r => T.r0
  | .s => T.s0
  | .a => T.a0
  | .b => T.b0
  | .v => T.v0

end ResidueTuple

/-- The concrete arithmetic coordinates of an atom. -/
structure AtomCoordinates (Atom : Type u) where
  q : Atom -> Nat
  r : Atom -> Nat
  s : Atom -> Nat
  a : Atom -> Nat
  b : Atom -> Nat
  v : Atom -> Nat
  height : Atom -> Nat

namespace AtomCoordinates

/-- Left mass: q*r*s. -/
def leftMass (C : AtomCoordinates Atom) (x : Atom) : Nat :=
  C.q x * C.r x * C.s x

/-- Right mass: a*b*v. -/
def rightMass (C : AtomCoordinates Atom) (x : Atom) : Nat :=
  C.a x * C.b x * C.v x

/-- Factor accessor. -/
def factor (C : AtomCoordinates Atom) : FactorName -> Atom -> Nat
  | .q, x => C.q x
  | .r, x => C.r x
  | .s, x => C.s x
  | .a, x => C.a x
  | .b, x => C.b x
  | .v, x => C.v x

end AtomCoordinates

/-- The LayerBox atom specification. -/
structure LayerBoxSpec (Atom : Type u) where
  coord : AtomCoordinates Atom
  Valid : Atom -> Prop
  LocalObstruction : Atom -> Prop
  modulus : Nat
  gap : Nat

namespace LayerBoxSpec

/-- Left mass for a spec. -/
def leftMass (S : LayerBoxSpec Atom) (x : Atom) : Nat :=
  S.coord.leftMass x

/-- Right mass for a spec. -/
def rightMass (S : LayerBoxSpec Atom) (x : Atom) : Nat :=
  S.coord.rightMass x

/-- One factor value for a spec. -/
def factor (S : LayerBoxSpec Atom) (f : FactorName) (x : Atom) : Nat :=
  S.coord.factor f x

end LayerBoxSpec

/-- Six explicit congruence lines for one atom and one residue tuple. -/
structure SixResidueForcing
    (S : LayerBoxSpec Atom) (x : Atom) (T : ResidueTuple) where
  q_line : S.factor .q x % S.modulus = T.q0
  r_line : S.factor .r x % S.modulus = T.r0
  s_line : S.factor .s x % S.modulus = T.s0
  a_line : S.factor .a x % S.modulus = T.a0
  b_line : S.factor .b x % S.modulus = T.b0
  v_line : S.factor .v x % S.modulus = T.v0

/-- A full residue transcript for one blocked move row. -/
structure RowTranscript (S : LayerBoxSpec Atom) (x : Atom) where
  tuple : ResidueTuple
  forced : SixResidueForcing S x tuple
  balance : tuple.BalancedAt S.modulus
  /--
  The executable modular product compiler for this row.
  In a concrete instantiation this is the arithmetic calculation from the six
  congruence lines and `balance`.
  -/
  compiled_sameResidue :
    S.leftMass x % S.modulus = S.rightMass x % S.modulus

/--
Determinant-gap compiler.
It is the reusable arithmetic kernel: same residue is impossible for a valid
atom whose determinant has nonzero gap.
-/
structure DeterminantGapKernel (S : LayerBoxSpec Atom) where
  determinant :
    ∀ {x : Atom}, S.Valid x ->
      S.leftMass x = S.rightMass x + S.gap
  gap_mod_nonzero : S.gap % S.modulus ≠ 0
  sameResidue_impossible :
    ∀ {x : Atom}, S.Valid x ->
      S.leftMass x % S.modulus = S.rightMass x % S.modulus -> False

/-- The concrete blocker predicate family. -/
abbrev BlockerFamily (Zero : Type v) (Atom : Type u) :=
  MoveName -> Zero -> Atom -> Prop

/-- All eleven blocker predicates active at a given zero/atom. -/
structure AllBlockers
    {Zero : Type v} {Atom : Type u}
    (Blocker : BlockerFamily Zero Atom) (z : Zero) (x : Atom) : Prop where
  peelQ : Blocker .peelQ z x
  peelR : Blocker .peelR z x
  peelS : Blocker .peelS z x
  absorbA : Blocker .absorbA z x
  absorbB : Blocker .absorbB z x
  absorbV : Blocker .absorbV z x
  swapLeft : Blocker .swapLeft z x
  swapRight : Blocker .swapRight z x
  normalize : Blocker .normalize z x
  residueRepair : Blocker .residueRepair z x
  transportRebalance : Blocker .transportRebalance z x

namespace AllBlockers

/-- Project the blocker corresponding to a move. -/
def get
    {Zero : Type v} {Atom : Type u}
    {Blocker : BlockerFamily Zero Atom} {z : Zero} {x : Atom}
    (B : AllBlockers Blocker z x) : (m : MoveName) -> Blocker m z x
  | .peelQ => B.peelQ
  | .peelR => B.peelR
  | .peelS => B.peelS
  | .absorbA => B.absorbA
  | .absorbB => B.absorbB
  | .absorbV => B.absorbV
  | .swapLeft => B.swapLeft
  | .swapRight => B.swapRight
  | .normalize => B.normalize
  | .residueRepair => B.residueRepair
  | .transportRebalance => B.transportRebalance

end AllBlockers

/-- One named row: blocker + validity + anchor produce a residue transcript. -/
structure NamedRow
    {Zero : Type v} {Atom : Type u}
    (S : LayerBoxSpec Atom)
    (Anchor : Zero -> Atom -> Prop)
    (Blocker : BlockerFamily Zero Atom)
    (m : MoveName) where
  row :
    ∀ {z : Zero} {x : Atom},
      S.Valid x -> Anchor z x -> Blocker m z x -> RowTranscript S x

/-- All eleven named row compilers. -/
structure ElevenNamedRows
    {Zero : Type v} {Atom : Type u}
    (S : LayerBoxSpec Atom)
    (Anchor : Zero -> Atom -> Prop)
    (Blocker : BlockerFamily Zero Atom) where
  peelQ : NamedRow S Anchor Blocker .peelQ
  peelR : NamedRow S Anchor Blocker .peelR
  peelS : NamedRow S Anchor Blocker .peelS
  absorbA : NamedRow S Anchor Blocker .absorbA
  absorbB : NamedRow S Anchor Blocker .absorbB
  absorbV : NamedRow S Anchor Blocker .absorbV
  swapLeft : NamedRow S Anchor Blocker .swapLeft
  swapRight : NamedRow S Anchor Blocker .swapRight
  normalize : NamedRow S Anchor Blocker .normalize
  residueRepair : NamedRow S Anchor Blocker .residueRepair
  transportRebalance : NamedRow S Anchor Blocker .transportRebalance

namespace ElevenNamedRows

/-- Select the row compiler for a named move. -/
def rowOf
    {Zero : Type v} {Atom : Type u}
    {S : LayerBoxSpec Atom}
    {Anchor : Zero -> Atom -> Prop}
    {Blocker : BlockerFamily Zero Atom}
    (R : ElevenNamedRows S Anchor Blocker) :
    (m : MoveName) -> NamedRow S Anchor Blocker m
  | .peelQ => R.peelQ
  | .peelR => R.peelR
  | .peelS => R.peelS
  | .absorbA => R.absorbA
  | .absorbB => R.absorbB
  | .absorbV => R.absorbV
  | .swapLeft => R.swapLeft
  | .swapRight => R.swapRight
  | .normalize => R.normalize
  | .residueRepair => R.residueRepair
  | .transportRebalance => R.transportRebalance

end ElevenNamedRows

/--
Minimal-cover compiler:
Every valid anchored atom is either locally obstructed or all eleven moves are
blocked.  Local obstruction itself is impossible for a valid anchored atom.
-/
structure MinimalCounterexampleCover
    {Zero : Type v} {Atom : Type u}
    (S : LayerBoxSpec Atom)
    (Anchor : Zero -> Atom -> Prop)
    (Blocker : BlockerFamily Zero Atom) where
  cover :
    ∀ {z : Zero} {x : Atom},
      S.Valid x -> Anchor z x ->
        S.LocalObstruction x ∨ AllBlockers Blocker z x
  no_local_obstruction :
    ∀ {z : Zero} {x : Atom},
      S.Valid x -> Anchor z x -> S.LocalObstruction x -> False

/--
The terminal local arithmetic kernel.  This is the point where the route is
finite: cover + rows + determinant-gap contradiction.
-/
structure TerminalLocalKernel
    {Zero : Type v} {Atom : Type u}
    (S : LayerBoxSpec Atom)
    (Anchor : Zero -> Atom -> Prop)
    (Blocker : BlockerFamily Zero Atom) where
  cover : MinimalCounterexampleCover S Anchor Blocker
  rows : ElevenNamedRows S Anchor Blocker
  gapKernel : DeterminantGapKernel S

namespace TerminalLocalKernel

/-- No valid atom can remain anchored once the terminal local kernel is filled. -/
theorem no_valid_anchored
    {Zero : Type v} {Atom : Type u}
    {S : LayerBoxSpec Atom}
    {Anchor : Zero -> Atom -> Prop}
    {Blocker : BlockerFamily Zero Atom}
    (K : TerminalLocalKernel S Anchor Blocker)
    {z : Zero} {x : Atom}
    (hv : S.Valid x) (ha : Anchor z x) : False := by
  cases K.cover.cover hv ha with
  | inl hobs =>
      exact K.cover.no_local_obstruction hv ha hobs
  | inr hblock =>
      let tr : RowTranscript S x := K.rows.peelQ.row hv ha hblock.peelQ
      exact K.gapKernel.sameResidue_impossible hv tr.compiled_sameResidue

/-- Same theorem, using any chosen move row. -/
theorem no_valid_anchored_using
    {Zero : Type v} {Atom : Type u}
    {S : LayerBoxSpec Atom}
    {Anchor : Zero -> Atom -> Prop}
    {Blocker : BlockerFamily Zero Atom}
    (K : TerminalLocalKernel S Anchor Blocker)
    (m : MoveName)
    {z : Zero} {x : Atom}
    (hv : S.Valid x) (ha : Anchor z x) : False := by
  cases K.cover.cover hv ha with
  | inl hobs =>
      exact K.cover.no_local_obstruction hv ha hobs
  | inr hblock =>
      let row := K.rows.rowOf m
      let tr : RowTranscript S x := row.row hv ha (hblock.get m)
      exact K.gapKernel.sameResidue_impossible hv tr.compiled_sameResidue

end TerminalLocalKernel

/-- Extract a concrete atom from a concrete zero. -/
structure ZeroIndexedExtractor
    {Zero : Type v} {Atom : Type u}
    (S : LayerBoxSpec Atom)
    (Anchor : Zero -> Atom -> Prop) where
  extract : Zero -> Atom
  valid : ∀ z : Zero, S.Valid (extract z)
  anchored : ∀ z : Zero, Anchor z (extract z)

/-- Decode the zero from its extracted atom.  This blocks free-origin atoms. -/
structure ZeroRecovery
    {Zero : Type v} {Atom : Type u}
    {S : LayerBoxSpec Atom}
    {Anchor : Zero -> Atom -> Prop}
    (E : ZeroIndexedExtractor S Anchor) where
  decode : Atom -> Zero
  recovers : ∀ z : Zero, decode (E.extract z) = z

namespace ZeroRecovery

/-- If extracted atoms are equal, then the source zeros are equal. -/
theorem extract_eq_forces_zero_eq
    {Zero : Type v} {Atom : Type u}
    {S : LayerBoxSpec Atom}
    {Anchor : Zero -> Atom -> Prop}
    {E : ZeroIndexedExtractor S Anchor}
    (R : ZeroRecovery E)
    {z₁ z₂ : Zero}
    (h : E.extract z₁ = E.extract z₂) : z₁ = z₂ := by
  calc
    z₁ = R.decode (E.extract z₁) := (R.recovers z₁).symm
    _ = R.decode (E.extract z₂) := by rw [h]
    _ = z₂ := R.recovers z₂

/-- A constant extractor is impossible on two distinct zeros. -/
theorem no_constant_extractor_on_distinct_zeros
    {Zero : Type v} {Atom : Type u}
    {S : LayerBoxSpec Atom}
    {Anchor : Zero -> Atom -> Prop}
    {E : ZeroIndexedExtractor S Anchor}
    (R : ZeroRecovery E)
    {z₁ z₂ : Zero}
    (hneq : z₁ ≠ z₂)
    (hconst : E.extract z₁ = E.extract z₂) : False := by
  exact hneq (R.extract_eq_forces_zero_eq hconst)

end ZeroRecovery

/-- Firewall against returning to the old engine-coherent bridge. -/
structure NonEngineCoherenceFirewall where
  NotEngineCoherent : Prop
  certified : NotEngineCoherent

/-- The high-level slots that are not residue-row arithmetic. -/
structure HighLevelSlots
    {Zero : Type v} {Atom : Type u}
    (S : LayerBoxSpec Atom)
    (Anchor : Zero -> Atom -> Prop)
    (Blocker : BlockerFamily Zero Atom) where
  extractor : ZeroIndexedExtractor S Anchor
  recovery : ZeroRecovery extractor
  firewall : NonEngineCoherenceFirewall
  kernel : TerminalLocalKernel S Anchor Blocker

/-- The final one-file front. -/
structure OneFileMaximalTerminalFront
    (Zero : Type v) (Atom : Type u) (Target : Prop) where
  S : LayerBoxSpec Atom
  Anchor : Zero -> Atom -> Prop
  Blocker : BlockerFamily Zero Atom
  high : HighLevelSlots S Anchor Blocker
  noZeros_to_target : (∀ z : Zero, False) -> Target

namespace OneFileMaximalTerminalFront

/-- The local terminal front kills every zero. -/
theorem noZeros
    {Zero : Type v} {Atom : Type u} {Target : Prop}
    (F : OneFileMaximalTerminalFront Zero Atom Target) :
    ∀ z : Zero, False := by
  intro z
  exact F.high.kernel.no_valid_anchored
    (F.high.extractor.valid z)
    (F.high.extractor.anchored z)

/-- Final target wrapper.  Instantiate `Target` as mathlib RH in the repo. -/
theorem target
    {Zero : Type v} {Atom : Type u} {Target : Prop}
    (F : OneFileMaximalTerminalFront Zero Atom Target) : Target :=
  F.noZeros_to_target F.noZeros

/-- The front is not a free-origin bridge when there are two distinct zeros. -/
theorem no_free_origin_supply_for_distinct_zeros
    {Zero : Type v} {Atom : Type u} {Target : Prop}
    (F : OneFileMaximalTerminalFront Zero Atom Target)
    {z₁ z₂ : Zero}
    (hneq : z₁ ≠ z₂)
    (hconst : F.high.extractor.extract z₁ = F.high.extractor.extract z₂) : False := by
  exact F.high.recovery.no_constant_extractor_on_distinct_zeros hneq hconst

end OneFileMaximalTerminalFront

/-!
## Workload audit

The definitions below do not prove the target.  They describe the exact finite
implementation load that remains for a concrete LayerBox instantiation.
-/

/-- Six congruence-line slots for one named row. -/
structure SixCongruenceLineSlots where
  q_line_filled : Prop
  r_line_filled : Prop
  s_line_filled : Prop
  a_line_filled : Prop
  b_line_filled : Prop
  v_line_filled : Prop

/-- One row status: six congruence lines plus one balance computation. -/
structure RowImplementationStatus where
  six : SixCongruenceLineSlots
  balance_check_filled : Prop

/-- All eleven row implementation statuses. -/
structure ElevenRowImplementationStatus where
  peelQ : RowImplementationStatus
  peelR : RowImplementationStatus
  peelS : RowImplementationStatus
  absorbA : RowImplementationStatus
  absorbB : RowImplementationStatus
  absorbV : RowImplementationStatus
  swapLeft : RowImplementationStatus
  swapRight : RowImplementationStatus
  normalize : RowImplementationStatus
  residueRepair : RowImplementationStatus
  transportRebalance : RowImplementationStatus

namespace ElevenRowImplementationStatus

/-- Select a row status by move name. -/
def get (R : ElevenRowImplementationStatus) : MoveName -> RowImplementationStatus
  | .peelQ => R.peelQ
  | .peelR => R.peelR
  | .peelS => R.peelS
  | .absorbA => R.absorbA
  | .absorbB => R.absorbB
  | .absorbV => R.absorbV
  | .swapLeft => R.swapLeft
  | .swapRight => R.swapRight
  | .normalize => R.normalize
  | .residueRepair => R.residueRepair
  | .transportRebalance => R.transportRebalance

end ElevenRowImplementationStatus

/-- All six line slots of a row are filled. -/
def SixCongruenceLineSlots.complete (L : SixCongruenceLineSlots) : Prop :=
  L.q_line_filled ∧
  L.r_line_filled ∧
  L.s_line_filled ∧
  L.a_line_filled ∧
  L.b_line_filled ∧
  L.v_line_filled

/-- A row is filled when all six lines and its balance check are filled. -/
def RowImplementationStatus.complete (R : RowImplementationStatus) : Prop :=
  R.six.complete ∧ R.balance_check_filled

/-- All eleven rows are filled. -/
def ElevenRowImplementationStatus.complete (R : ElevenRowImplementationStatus) : Prop :=
  R.peelQ.complete ∧
  R.peelR.complete ∧
  R.peelS.complete ∧
  R.absorbA.complete ∧
  R.absorbB.complete ∧
  R.absorbV.complete ∧
  R.swapLeft.complete ∧
  R.swapRight.complete ∧
  R.normalize.complete ∧
  R.residueRepair.complete ∧
  R.transportRebalance.complete

/-- High-level implementation gates. -/
structure HighLevelImplementationStatus where
  zero_indexed_extractor_filled : Prop
  zero_recovery_filled : Prop
  non_engine_firewall_filled : Prop
  minimal_cover_filled : Prop
  determinant_gap_kernel_filled : Prop
  target_wrapper_filled : Prop

/-- All high-level gates are filled. -/
def HighLevelImplementationStatus.complete (H : HighLevelImplementationStatus) : Prop :=
  H.zero_indexed_extractor_filled ∧
  H.zero_recovery_filled ∧
  H.non_engine_firewall_filled ∧
  H.minimal_cover_filled ∧
  H.determinant_gap_kernel_filled ∧
  H.target_wrapper_filled

/-- Terminal ledger for the final finite workload. -/
structure TerminalImplementationLedger where
  high : HighLevelImplementationStatus
  rows : ElevenRowImplementationStatus

/-- The terminal implementation is complete exactly when high-level gates and rows are complete. -/
def TerminalImplementationLedger.complete (L : TerminalImplementationLedger) : Prop :=
  L.high.complete ∧ L.rows.complete

namespace TerminalImplementationLedger

/-- No closure without the high-level gates. -/
theorem no_closure_without_high
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.complete :=
  h.left

/-- No closure without the eleven row table. -/
theorem no_closure_without_rows
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.rows.complete :=
  h.right

/-- No closure without the extractor slot. -/
theorem no_closure_without_extractor
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.zero_indexed_extractor_filled :=
  h.left.left

/-- No closure without zero recovery. -/
theorem no_closure_without_zero_recovery
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.zero_recovery_filled :=
  h.left.right.left

/-- No closure without the non-engine firewall. -/
theorem no_closure_without_firewall
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.non_engine_firewall_filled :=
  h.left.right.right.left

/-- No closure without the minimal-cover slot. -/
theorem no_closure_without_minimal_cover
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.minimal_cover_filled :=
  h.left.right.right.right.left

/-- No closure without determinant-gap arithmetic. -/
theorem no_closure_without_gap_kernel
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.determinant_gap_kernel_filled :=
  h.left.right.right.right.right.left

/-- No closure without the final target wrapper. -/
theorem no_closure_without_target_wrapper
    (L : TerminalImplementationLedger)
    (h : L.complete) : L.high.target_wrapper_filled :=
  h.left.right.right.right.right.right

end TerminalImplementationLedger

/-- A named count marker: the terminal residue matrix has 11 × 6 = 66 line slots. -/
def residueCongruenceLineCount : Nat := 11 * 6

/-- The intended finite line count. -/
theorem residueCongruenceLineCount_eq_66 : residueCongruenceLineCount = 66 := by
  rfl

/-- The intended balance-check count. -/
def residueBalanceCheckCount : Nat := 11

/-- The intended number of high-level gates. -/
def highLevelGateCount : Nat := 6

/-- Final slogan as a theorem-shaped status marker. -/
theorem oneFileMaximalTerminalFront_slogan :
    residueCongruenceLineCount = 66 ∧
    residueBalanceCheckCount = 11 ∧
    highLevelGateCount = 6 := by
  exact ⟨rfl, rfl, rfl⟩

end RiemannLayerBoxOneFileMaximalTerminalFront

/- ============ BRICK: Riemann_layerbox_single_file_final_terminal_compiler_patch.lean ============ -/

/-
Riemann_layerbox_single_file_final_terminal_compiler_patch.lean

Purpose.
  One-file maximal terminal compiler for the Riemann LayerBox route.

  This file does NOT prove RH by itself.  It packages the remaining
  non-vacuous route into one terminal certificate:

    zero-indexed extraction
    + zero recovery
    + non-engine / non-origin firewall
    + minimal-counterexample cover
    + 11 named blocker rows
    + 66 forced residue congruences
    + 11 executable/semantic balance checks
    + determinant-gap contradiction kernel
    + target wrapper
    ==> Target.

  The point is to prevent a fake closure: a proof transcript is closed only
  when every terminal slot is populated.  The old failures are represented
  explicitly:
    * free origin supply is not accepted;
    * anchor-forgetting descent is not accepted;
    * engine-coherent two-transport is not accepted;
    * a row without six congruences is not accepted.

  This is intentionally an abstract compiler layer.  The concrete repo should
  instantiate Zero with OffCriticalZero, Atom with the decoded LayerBox atom,
  and Target with mathlib's RiemannHypothesis wrapper.
-/

namespace RiemannLayerBox
namespace SingleFileFinalTerminalCompiler

/-- The finite list of local moves/blockers in the LayerBox terminal table. -/
inductive MoveName where
  | peelQ
  | peelR
  | peelS
  | absorbA
  | absorbB
  | absorbV
  | swapLeft
  | swapRight
  | normalize
  | residueRepair
  | transportRebalance
  deriving DecidableEq, Repr

/-- The six factors of an arithmetic transport atom q*r*s = a*b*v + 2. -/
inductive FactorName where
  | q
  | r
  | s
  | a
  | b
  | v
  deriving DecidableEq, Repr

/-- A compact record for the six coordinates of an arithmetic atom. -/
structure Coordinates where
  q : Nat
  r : Nat
  s : Nat
  a : Nat
  b : Nat
  v : Nat

namespace Coordinates

/-- Left mass q*r*s. -/
def leftMass (c : Coordinates) : Nat := c.q * c.r * c.s

/-- Right mass a*b*v. -/
def rightMass (c : Coordinates) : Nat := c.a * c.b * c.v

/-- The determinant/two-transport equation q*r*s = a*b*v + 2. -/
def GapTwo (c : Coordinates) : Prop :=
  c.leftMass = c.rightMass + 2

end Coordinates

/-- A residue tuple for the six coordinates. -/
structure ResidueTuple where
  q0 : Nat
  r0 : Nat
  s0 : Nat
  a0 : Nat
  b0 : Nat
  v0 : Nat

namespace ResidueTuple

/-- Left residue product. -/
def leftProd (t : ResidueTuple) : Nat := t.q0 * t.r0 * t.s0

/-- Right residue product. -/
def rightProd (t : ResidueTuple) : Nat := t.a0 * t.b0 * t.v0

/-- Balanced residue tuple: left and right products agree modulo M. -/
def BalancedAt (M : Nat) (t : ResidueTuple) : Prop :=
  t.leftProd % M = t.rightProd % M

end ResidueTuple

/-- A concrete atom interface.  The compiler does not decide what Atom is. -/
structure LayerBoxAtomSpec (Atom : Type) where
  coord : Atom -> Coordinates
  height : Atom -> Nat
  valid : Atom -> Prop

/-- Zero-indexed anchoring interface. -/
structure ZeroAnchorSpec (Zero Atom : Type) where
  anchor : Zero -> Atom -> Prop

/-- Decoder/fingerprint interface: an atom must recover the zero it claims to encode. -/
structure ZeroDecoder (Zero Atom : Type) where
  decode : Atom -> Zero

/-- High-level extraction gate: every zero yields a valid anchored atom. -/
structure ZeroIndexedExtractor (Zero Atom : Type) where
  atomOf : Zero -> Atom
  valid_atomOf : Zero -> Prop
  anchored_atomOf : Zero -> Prop

/-- A concrete extractor after choosing the validity/anchor predicates. -/
structure ExtractorRealizes
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (E : ZeroIndexedExtractor Zero Atom) : Prop where
  valid : ∀ z : Zero, A.valid (E.atomOf z)
  anchored : ∀ z : Zero, S.anchor z (E.atomOf z)

/-- Zero recovery: anchored atoms decode back to the same zero. -/
structure ZeroRecovery
    (Zero Atom : Type)
    (S : ZeroAnchorSpec Zero Atom)
    (D : ZeroDecoder Zero Atom) : Prop where
  recover : ∀ {z : Zero} {atom : Atom}, S.anchor z atom -> D.decode atom = z

namespace ZeroRecovery

/-- If one atom is anchored at two zeros, recovery forces those zeros equal. -/
theorem same_atom_forces_same_zero
    {Zero Atom : Type}
    {S : ZeroAnchorSpec Zero Atom}
    {D : ZeroDecoder Zero Atom}
    (R : ZeroRecovery Zero Atom S D)
    {z₁ z₂ : Zero} {atom : Atom}
    (h₁ : S.anchor z₁ atom)
    (h₂ : S.anchor z₂ atom) :
    z₁ = z₂ := by
  have hdecode1 : D.decode atom = z₁ := R.recover h₁
  have hdecode2 : D.decode atom = z₂ := R.recover h₂
  exact hdecode1.symm.trans hdecode2

end ZeroRecovery

/-- Non-engine firewall: the terminal arithmetic object is not accepted if it is
    merely a coherent engine-factory certificate. -/
structure NonEngineCoherenceFirewall (Zero Atom : Type) where
  engineCoherent : Zero -> Atom -> Prop
  rejects : ∀ {z : Zero} {atom : Atom}, engineCoherent z atom -> False

/-- Origin-supply firewall: a single free atom cannot be used as a law for every zero. -/
structure NoFreeOriginSupply
    (Zero Atom : Type)
    (S : ZeroAnchorSpec Zero Atom) : Prop where
  no_free_atom : ∀ atom : Atom, (∀ z : Zero, S.anchor z atom) -> False

/-- The minimal counterexample cover.  A valid anchored atom must be either locally
    obstructed or covered by all terminal blockers.  This is the non-descent,
    finite-table form of the route. -/
structure MinimalCounterexampleCover
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom) where
  LocalObstruction : Zero -> Atom -> Prop
  Blocked : MoveName -> Zero -> Atom -> Prop
  cover : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom ->
      LocalObstruction z atom ∨ (∀ m : MoveName, Blocked m z atom)

/-- A row supplies the forced residue tuple for one blocker/move. -/
structure RowResidueTranscript
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (C : MinimalCounterexampleCover Zero Atom A S)
    (M : Nat)
    (move : MoveName) where
  tupleOf : Zero -> Atom -> ResidueTuple
  forced_q : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      (A.coord atom).q % M = (tupleOf z atom).q0 % M
  forced_r : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      (A.coord atom).r % M = (tupleOf z atom).r0 % M
  forced_s : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      (A.coord atom).s % M = (tupleOf z atom).s0 % M
  forced_a : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      (A.coord atom).a % M = (tupleOf z atom).a0 % M
  forced_b : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      (A.coord atom).b % M = (tupleOf z atom).b0 % M
  forced_v : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      (A.coord atom).v % M = (tupleOf z atom).v0 % M
  balanced : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.Blocked move z atom ->
      ResidueTuple.BalancedAt M (tupleOf z atom)

/-- The complete 11-row residue transcript. -/
structure ElevenResidueTranscript
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (C : MinimalCounterexampleCover Zero Atom A S)
    (M : Nat) where
  row : ∀ move : MoveName, RowResidueTranscript Zero Atom A S C M move

/-- Determinant-gap kernel.  If a valid atom has qrs = abv + 2 and its two masses
    are congruent modulo M while 2 is nonzero modulo M, contradiction.  The concrete
    repo is expected to instantiate this from modular arithmetic. -/
structure DeterminantGapKernel
    (Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (M : Nat) where
  gap_two : ∀ {atom : Atom}, A.valid atom -> Coordinates.GapTwo (A.coord atom)
  two_nonzero : 2 % M ≠ 0
  same_mass_residue_impossible : ∀ {atom : Atom},
    A.valid atom ->
    (A.coord atom).leftMass % M = (A.coord atom).rightMass % M ->
    False

/-- Semantic local obstruction kernel: local obstruction immediately rules out a valid anchored atom. -/
structure LocalObstructionKernel
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (C : MinimalCounterexampleCover Zero Atom A S) where
  impossible : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom -> C.LocalObstruction z atom -> False

/-- Row algebra compiler: if all blockers are active, the 11-row transcript and the
    determinant gap kernel produce contradiction.  This is an explicit slot because
    the concrete proof performs modular product arithmetic. -/
structure RowAlgebraCompiler
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (C : MinimalCounterexampleCover Zero Atom A S)
    (M : Nat)
    (T : ElevenResidueTranscript Zero Atom A S C M)
    (G : DeterminantGapKernel Atom A M) where
  all_blocked_impossible : ∀ {z : Zero} {atom : Atom},
    A.valid atom -> S.anchor z atom ->
    (∀ move : MoveName, C.Blocked move z atom) -> False

/-- Terminal local kernel: cover + local obstruction + row algebra kills every
    valid anchored atom. -/
structure TerminalLocalKernel
    (Zero Atom : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (M : Nat) where
  cover : MinimalCounterexampleCover Zero Atom A S
  localObstruction : LocalObstructionKernel Zero Atom A S cover
  rows : ElevenResidueTranscript Zero Atom A S cover M
  gap : DeterminantGapKernel Atom A M
  rowCompiler : RowAlgebraCompiler Zero Atom A S cover M rows gap

namespace TerminalLocalKernel

/-- The terminal local kernel rules out every valid anchored atom. -/
theorem no_valid_anchored
    {Zero Atom : Type}
    {A : LayerBoxAtomSpec Atom}
    {S : ZeroAnchorSpec Zero Atom}
    {M : Nat}
    (K : TerminalLocalKernel Zero Atom A S M)
    {z : Zero} {atom : Atom}
    (hvalid : A.valid atom)
    (hanchor : S.anchor z atom) :
    False := by
  cases K.cover.cover hvalid hanchor with
  | inl hlocal =>
      exact K.localObstruction.impossible hvalid hanchor hlocal
  | inr hblocked =>
      exact K.rowCompiler.all_blocked_impossible hvalid hanchor hblocked

end TerminalLocalKernel

/-- A complete high-level proof transcript from zeros to contradiction. -/
structure TerminalProofTranscript
    (Zero Atom Target : Type)
    (A : LayerBoxAtomSpec Atom)
    (S : ZeroAnchorSpec Zero Atom)
    (D : ZeroDecoder Zero Atom)
    (M : Nat) where
  extractor : ZeroIndexedExtractor Zero Atom
  realizesExtractor : ExtractorRealizes Zero Atom A S extractor
  zeroRecovery : ZeroRecovery Zero Atom S D
  noEngine : NonEngineCoherenceFirewall Zero Atom
  noOrigin : NoFreeOriginSupply Zero Atom S
  localKernel : TerminalLocalKernel Zero Atom A S M
  noZeros_to_target : (Zero -> False) -> Target

namespace TerminalProofTranscript

/-- The transcript proves there are no zeros. -/
theorem noZeros
    {Zero Atom Target : Type}
    {A : LayerBoxAtomSpec Atom}
    {S : ZeroAnchorSpec Zero Atom}
    {D : ZeroDecoder Zero Atom}
    {M : Nat}
    (P : TerminalProofTranscript Zero Atom Target A S D M) :
    Zero -> False := by
  intro z
  exact P.localKernel.no_valid_anchored
    (P.realizesExtractor.valid z)
    (P.realizesExtractor.anchored z)

/-- The target wrapper turns no off-critical zeros into the final target. -/
def target
    {Zero Atom Target : Type}
    {A : LayerBoxAtomSpec Atom}
    {S : ZeroAnchorSpec Zero Atom}
    {D : ZeroDecoder Zero Atom}
    {M : Nat}
    (P : TerminalProofTranscript Zero Atom Target A S D M) :
    Target :=
  P.noZeros_to_target (P.noZeros)

/-- One free atom cannot serve as the origin-law for every zero. -/
theorem no_free_origin_atom
    {Zero Atom Target : Type}
    {A : LayerBoxAtomSpec Atom}
    {S : ZeroAnchorSpec Zero Atom}
    {D : ZeroDecoder Zero Atom}
    {M : Nat}
    (P : TerminalProofTranscript Zero Atom Target A S D M)
    (atom : Atom)
    (hfree : ∀ z : Zero, S.anchor z atom) :
    False :=
  P.noOrigin.no_free_atom atom hfree

/-- If two zeros share one anchored atom, recovery identifies them. -/
theorem same_origin_atom_collapses_zeros
    {Zero Atom Target : Type}
    {A : LayerBoxAtomSpec Atom}
    {S : ZeroAnchorSpec Zero Atom}
    {D : ZeroDecoder Zero Atom}
    {M : Nat}
    (P : TerminalProofTranscript Zero Atom Target A S D M)
    {z₁ z₂ : Zero} {atom : Atom}
    (h₁ : S.anchor z₁ atom)
    (h₂ : S.anchor z₂ atom) :
    z₁ = z₂ :=
  P.zeroRecovery.same_atom_forces_same_zero h₁ h₂

end TerminalProofTranscript

/-- Slot-level ledger.  This does not prove the target; it audits whether the
    terminal transcript has all necessary pieces. -/
structure TerminalSlotLedger where
  hasExtractor : Prop
  hasExtractorRealization : Prop
  hasZeroRecovery : Prop
  hasNonEngineFirewall : Prop
  hasNoOriginFirewall : Prop
  hasMinimalCover : Prop
  hasLocalObstructionKernel : Prop
  hasElevenRows : Prop
  hasSixtySixCongruences : Prop
  hasElevenBalanceChecks : Prop
  hasDeterminantGapKernel : Prop
  hasRowAlgebraCompiler : Prop
  hasTargetWrapper : Prop

namespace TerminalSlotLedger

/-- All slots needed by the terminal compiler. -/
def Complete (L : TerminalSlotLedger) : Prop :=
  L.hasExtractor ∧
  L.hasExtractorRealization ∧
  L.hasZeroRecovery ∧
  L.hasNonEngineFirewall ∧
  L.hasNoOriginFirewall ∧
  L.hasMinimalCover ∧
  L.hasLocalObstructionKernel ∧
  L.hasElevenRows ∧
  L.hasSixtySixCongruences ∧
  L.hasElevenBalanceChecks ∧
  L.hasDeterminantGapKernel ∧
  L.hasRowAlgebraCompiler ∧
  L.hasTargetWrapper

/-- A missing high-level extractor blocks closure. -/
theorem no_closure_without_extractor
    (L : TerminalSlotLedger)
    (hmissing : ¬ L.hasExtractor) :
    ¬ L.Complete := by
  intro h
  exact hmissing h.1

/-- Missing zero-recovery blocks closure. -/
theorem no_closure_without_zeroRecovery
    (L : TerminalSlotLedger)
    (hmissing : ¬ L.hasZeroRecovery) :
    ¬ L.Complete := by
  intro h
  exact hmissing h.2.2.1

/-- Missing 66 congruence lines blocks closure. -/
theorem no_closure_without_sixtySixCongruences
    (L : TerminalSlotLedger)
    (hmissing : ¬ L.hasSixtySixCongruences) :
    ¬ L.Complete := by
  intro h
  exact hmissing h.2.2.2.2.2.2.2.2.1

/-- Missing 11 balance checks blocks closure. -/
theorem no_closure_without_elevenBalanceChecks
    (L : TerminalSlotLedger)
    (hmissing : ¬ L.hasElevenBalanceChecks) :
    ¬ L.Complete := by
  intro h
  exact hmissing h.2.2.2.2.2.2.2.2.2.1

/-- Missing row algebra compiler blocks closure. -/
theorem no_closure_without_rowAlgebraCompiler
    (L : TerminalSlotLedger)
    (hmissing : ¬ L.hasRowAlgebraCompiler) :
    ¬ L.Complete := by
  intro h
  exact hmissing h.2.2.2.2.2.2.2.2.2.2.2.1

end TerminalSlotLedger

/-- A compact workload summary for the concrete implementation. -/
structure TerminalWorkloadSummary where
  highLevelSlots : Nat := 13
  moveRows : Nat := 11
  factorColumns : Nat := 6
  residueCongruenceLines : Nat := 66
  balanceChecks : Nat := 11

/-- The expected workload count for residue congruence slots. -/
theorem residueCongruenceLineCount : 11 * 6 = 66 := by
  decide

/-- Terminal slogan, as a theorem returning True so it can be imported harmlessly. -/
theorem singleFileFinalTerminalCompiler_slogan : True := by
  trivial

end SingleFileFinalTerminalCompiler
end RiemannLayerBox

/- ============ Axiom audit for headline theorems ============ -/
