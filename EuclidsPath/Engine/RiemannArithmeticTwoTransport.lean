/-
  RiemannArithmeticTwoTransport — the non-engine arithmetic target of the RH branch
  (brick: Riemann_arithmetic_two_transport_law). Prose: prose/30.

  Answer to the uncovered collapse of the coherent route (coherentTwoTransportBridge
  ⟺ RH): the certificate is built around the twin-layer identity qrs = abv + 2,
  WITHOUT a factory and WITHOUT engine-killer dynamics (firewall NotEngineCoherent).

  PROVED (brick, pure arithmetic/assembly): the gap is exactly 2 (natGap_eq_two),
  positivity, integer orientation abv − qrs = −2; RH assembly from two
  inputs (bridge: zero ⟹ law; impossibility: no law) — both future targets.

  ⚠️ MACHINE HONESTY (on integration):
    * trivialAtom — unconstrained atom exists (3 = 1 + 2);
    * law_iff_admissibleAtom — gates (anchor/noncircular/firewall) are FREE:
      law at a given Z ⟺ Z-INDEPENDENT existence of an admissible atom
      (AdmissibleAtomExists — LayerBox + residues mod 6);
    * bridge_iff / impossible_iff — both inputs = ONE arithmetic question
      AdmissibleAtomExists, split by polarity under the zero hypothesis;
    * front_pair_iff_no_zero — the pair of inputs is jointly satisfiable ⟺ no zeros:
      circularity is preserved AS LONG AS the anchor is free. The next honest
      task of the route is to make the zero anchoring a LOAD-BEARING carrier (a law
      genuinely depending on Z), or to solve AdmissibleAtomExists as an independent
      arithmetic problem (the question is open and interesting in its own right).
  Concrete RH assembly with real repo extraction: RH_of_concreteArithmeticFront.
-/
import Mathlib
import EuclidsPath.Engine.RiemannImpossibleEngineOff

set_option autoImplicit false

namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport

/-!
## 1. The bare arithmetic transport atom
-/

/--
The six positive natural parameters of the arithmetic two-transport law.

The intended reading is

* `a*b*v` is one transported product;
* `q*r*s` is the opposite transported product;
* the two transports differ by exactly `2`.

This is the Riemann-side analogue of the determinant relation from the
rank-`(3,3)` twin layer, but it is kept abstract and zero-anchored later.
-/
structure ArithmeticTransportAtom where
  q : ℕ
  r : ℕ
  s : ℕ
  a : ℕ
  b : ℕ
  v : ℕ

  q_pos : 0 < q
  r_pos : 0 < r
  s_pos : 0 < s
  a_pos : 0 < a
  b_pos : 0 < b
  v_pos : 0 < v

  transport_identity : q * r * s = a * b * v + 2

namespace ArithmeticTransportAtom

/-- The left arithmetic product. -/
def leftMass (T : ArithmeticTransportAtom) : ℕ :=
  T.a * T.b * T.v

/-- The right arithmetic product. -/
def rightMass (T : ArithmeticTransportAtom) : ℕ :=
  T.q * T.r * T.s

/-- The defining identity, in mass notation. -/
theorem rightMass_eq_leftMass_add_two (T : ArithmeticTransportAtom) :
    T.rightMass = T.leftMass + 2 := by
  unfold rightMass leftMass
  exact T.transport_identity

/-- The two sides are not equal: the right side is strictly larger by two. -/
theorem leftMass_lt_rightMass (T : ArithmeticTransportAtom) :
    T.leftMass < T.rightMass := by
  rw [rightMass_eq_leftMass_add_two T]
  omega

/-- The two transported products are distinct. -/
theorem leftMass_ne_rightMass (T : ArithmeticTransportAtom) :
    T.leftMass ≠ T.rightMass := by
  exact ne_of_lt (leftMass_lt_rightMass T)

/-- The gap, written as a natural subtraction. -/
def natGap (T : ArithmeticTransportAtom) : ℕ :=
  T.rightMass - T.leftMass

/-- The arithmetic transport gap is exactly two. -/
theorem natGap_eq_two (T : ArithmeticTransportAtom) :
    T.natGap = 2 := by
  unfold natGap
  rw [rightMass_eq_leftMass_add_two T]
  omega

/-- Positivity of the left product. -/
theorem leftMass_pos (T : ArithmeticTransportAtom) :
    0 < T.leftMass := by
  unfold leftMass
  exact Nat.mul_pos (Nat.mul_pos T.a_pos T.b_pos) T.v_pos

/-- Positivity of the right product. -/
theorem rightMass_pos (T : ArithmeticTransportAtom) :
    0 < T.rightMass := by
  unfold rightMass
  exact Nat.mul_pos (Nat.mul_pos T.q_pos T.r_pos) T.s_pos

/-- Integer determinant orientation: `abv - qrs = -2`. -/
theorem int_left_sub_right_eq_neg_two (T : ArithmeticTransportAtom) :
    ((T.leftMass : ℤ) - (T.rightMass : ℤ)) = -2 := by
  have h := rightMass_eq_leftMass_add_two T
  omega

/-- Integer determinant orientation in the twin-style factor notation. -/
theorem int_abv_sub_qrs_eq_neg_two (T : ArithmeticTransportAtom) :
    (((T.a * T.b * T.v : ℕ) : ℤ) - ((T.q * T.r * T.s : ℕ) : ℤ)) = -2 := by
  simpa [leftMass, rightMass] using int_left_sub_right_eq_neg_two T

end ArithmeticTransportAtom

/-!
## 2. Arithmetic admissibility and zero anchoring
-/

/-- A dyadic/layer box for the six factors. -/
def LayerBox (A : ℕ) (T : ArithmeticTransportAtom) : Prop :=
  A < T.a ∧ T.a ≤ A * A ∧
  A < T.b ∧ T.b ≤ A * A ∧
  A < T.v ∧ T.v ≤ A * A ∧
  A < T.q ∧ T.q ≤ A * A ∧
  A < T.r ∧ T.r ≤ A * A ∧
  A < T.s ∧ T.s ≤ A * A

/--
Congruence and layer admissibility for the arithmetic transport atom.

The congruence fields are intentionally explicit.  From the identity
`rightMass = leftMass + 2`, one expects `leftMass ≡ 5 mod 6` and
`rightMass ≡ 1 mod 6`; the concrete repo can replace these fields with derived
lemmas once the exact residue construction is available.
-/
structure ArithmeticAdmissible (T : ArithmeticTransportAtom) where
  A : ℕ
  A_pos : 0 < A
  in_layer : LayerBox A T
  left_mod_six : T.leftMass % 6 = 5
  right_mod_six : T.rightMass % 6 = 1

/--
The center reconstructed from the left product.

This is intentionally a raw natural expression.  The field `left_mod_six` in
`ArithmeticAdmissible` is the proof gate that this is the intended integer
center for the `6m-1` side.
-/
def reconstructedCenter (T : ArithmeticTransportAtom) : ℕ :=
  (T.leftMass + 1) / 6

/--
A zero-anchoring predicate says that the arithmetic atom was extracted from the
specific off-critical zero `Z`, not postulated globally.
-/
structure ZeroAnchored
    (OffCriticalZero : Type)
    (Z : OffCriticalZero)
    (T : ArithmeticTransportAtom) where
  anchor : Prop
  anchor_proof : anchor

/--
A strict audit gate excluding RH/Liouville/old-engine leaks.

The concrete instantiation should make these propositions meaningful, e.g.
"the construction does not use `RiemannHypothesis`", "does not use
`LiouvilleBound`", and "does not use `OffCriticalRiemannEngineBridge`".
-/
structure NonCircularArithmeticConstruction where
  no_RH_leak : Prop
  no_RH_leak_proof : no_RH_leak

  no_Liouville_leak : Prop
  no_Liouville_leak_proof : no_Liouville_leak

  no_engine_bridge_leak : Prop
  no_engine_bridge_leak_proof : no_engine_bridge_leak

/--
The firewall separating the new arithmetic law from the coherent engine route.

If a certificate is engine-coherent, it has fallen back into the old route.
The new law requires a proof that this is not the case.
-/
structure NotEngineCoherent where
  engine_coherent : Prop
  not_engine_coherent : ¬ engine_coherent

/-!
## 3. The strict arithmetic two-transport law
-/

/--
The non-engine arithmetic two-transport law attached to one off-critical zero.

This is the next strict target for the Riemann route.  It contains the concrete
identity `qrs = abv + 2`, residue/layer admissibility, zero anchoring, and a
firewall against the already-collapsed engine-coherent route.
-/
structure ArithmeticTwoTransportLaw
    (OffCriticalZero : Type)
    (Z : OffCriticalZero) where
  atom : ArithmeticTransportAtom
  admissible : ArithmeticAdmissible atom
  anchored : ZeroAnchored OffCriticalZero Z atom
  noncircular : NonCircularArithmeticConstruction
  firewall : NotEngineCoherent

namespace ArithmeticTwoTransportLaw

/-- The law contains the exact arithmetic transport identity. -/
theorem rightMass_eq_leftMass_add_two
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    L.atom.rightMass = L.atom.leftMass + 2 := by
  exact ArithmeticTransportAtom.rightMass_eq_leftMass_add_two L.atom

/-- Any law has a strict two-unit gap. -/
theorem strict_gap
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    L.atom.leftMass < L.atom.rightMass := by
  exact ArithmeticTransportAtom.leftMass_lt_rightMass L.atom

/-- Any law has natural gap exactly two. -/
theorem natGap_eq_two
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    L.atom.natGap = 2 := by
  exact ArithmeticTransportAtom.natGap_eq_two L.atom

/-- The law is explicitly not engine-coherent. -/
theorem not_engine_coherent
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    ¬ L.firewall.engine_coherent := by
  exact L.firewall.not_engine_coherent

/-- Therefore a law cannot be used as a coherent engine certificate. -/
theorem no_engine_coherent_subcertificate
    {OffCriticalZero : Type}
    {Z : OffCriticalZero} :
    ¬ Nonempty {L : ArithmeticTwoTransportLaw OffCriticalZero Z // L.firewall.engine_coherent} := by
  intro h
  rcases h with ⟨L, hcoh⟩
  exact L.not_engine_coherent hcoh

/-- The law preserves its zero anchor as accessible data. -/
theorem has_zero_anchor
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    L.anchored.anchor := by
  exact L.anchored.anchor_proof

/-- The law preserves its RH-leak firewall as accessible data. -/
theorem has_no_RH_leak_gate
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    L.noncircular.no_RH_leak := by
  exact L.noncircular.no_RH_leak_proof

end ArithmeticTwoTransportLaw

/-!
## 4. The bridge and the arithmetic impossibility target
-/

/--
The new bridge target: every off-critical zero produces a strict arithmetic
transport law.
-/
def ArithmeticTwoTransportBridge (OffCriticalZero : Type) : Prop :=
  ∀ Z : OffCriticalZero,
    Nonempty (ArithmeticTwoTransportLaw OffCriticalZero Z)

/--
The new impossibility target: no strict arithmetic transport law can exist.

This is intended to be proved by arithmetic from `q*r*s = a*b*v + 2` plus
admissibility, not by the closed paid engine killer.
-/
def ArithmeticTwoTransportImpossible (OffCriticalZero : Type) : Prop :=
  ∀ Z : OffCriticalZero,
    ¬ Nonempty (ArithmeticTwoTransportLaw OffCriticalZero Z)

/-- Bridge + impossibility forbid off-critical zeros. -/
theorem no_offCriticalZero_of_arithmeticTwoTransport
    {OffCriticalZero : Type}
    (hBridge : ArithmeticTwoTransportBridge OffCriticalZero)
    (hImpossible : ArithmeticTwoTransportImpossible OffCriticalZero) :
    ¬ Nonempty OffCriticalZero := by
  intro hZ
  rcases hZ with ⟨Z⟩
  exact hImpossible Z (hBridge Z)

/--
Abstract RH assembly from the arithmetic two-transport route.

`hExtract` is the already checked logical extraction
`¬ RiemannHypothesis → Nonempty OffCriticalZero`.
-/
theorem riemannHypothesis_of_arithmeticTwoTransport
    {OffCriticalZero : Type}
    {RiemannHypothesis : Prop}
    (hExtract : ¬ RiemannHypothesis → Nonempty OffCriticalZero)
    (hBridge : ArithmeticTwoTransportBridge OffCriticalZero)
    (hImpossible : ArithmeticTwoTransportImpossible OffCriticalZero) :
    RiemannHypothesis := by
  by_contra hNotRH
  exact no_offCriticalZero_of_arithmeticTwoTransport hBridge hImpossible
    (hExtract hNotRH)

/-!
## 5. The strict front object
-/

/--
The full current non-engine Riemann front.

It has exactly two mathematical fields:

1. construct the arithmetic law from every off-critical zero;
2. prove the law arithmetically impossible.

The audit fields state that this route is not the old coherent engine route and
not the Liouville-bound route.
-/
structure ArithmeticTwoTransportFront (OffCriticalZero : Type) where
  bridge : ArithmeticTwoTransportBridge OffCriticalZero
  impossible : ArithmeticTwoTransportImpossible OffCriticalZero

  not_coherent_engine_route : Prop
  not_coherent_engine_route_proof : not_coherent_engine_route

  not_Liouville_route : Prop
  not_Liouville_route_proof : not_Liouville_route

/-- The strict front proves RH once `¬ RH` extracts an off-critical zero. -/
theorem riemannHypothesis_of_arithmeticTwoTransportFront
    {OffCriticalZero : Type}
    {RiemannHypothesis : Prop}
    (hExtract : ¬ RiemannHypothesis → Nonempty OffCriticalZero)
    (F : ArithmeticTwoTransportFront OffCriticalZero) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_arithmeticTwoTransport hExtract F.bridge F.impossible

/--
Slogan theorem: the new law is the determinant identity plus three firewalls.
-/
theorem arithmeticTwoTransportLaw_slogan
    {OffCriticalZero : Type}
    {Z : OffCriticalZero}
    (L : ArithmeticTwoTransportLaw OffCriticalZero Z) :
    L.atom.rightMass = L.atom.leftMass + 2 ∧
    L.atom.natGap = 2 ∧
    L.anchored.anchor ∧
    L.noncircular.no_RH_leak ∧
    ¬ L.firewall.engine_coherent := by
  exact ⟨
    L.rightMass_eq_leftMass_add_two,
    L.natGap_eq_two,
    L.has_zero_anchor,
    L.has_no_RH_leak_gate,
    L.not_engine_coherent
  ⟩

/--
Final route slogan: RH follows from the arithmetic bridge and arithmetic
impossibility, not from a coherent engine factory.
-/
theorem arithmeticTwoTransportFront_slogan
    {OffCriticalZero : Type}
    (F : ArithmeticTwoTransportFront OffCriticalZero) :
    ArithmeticTwoTransportBridge OffCriticalZero ∧
    ArithmeticTwoTransportImpossible OffCriticalZero ∧
    F.not_coherent_engine_route ∧
    F.not_Liouville_route := by
  exact ⟨
    F.bridge,
    F.impossible,
    F.not_coherent_engine_route_proof,
    F.not_Liouville_route_proof
  ⟩

end ArithmeticTwoTransport
end Riemann
end EuclidsPath

/-! Concrete repo anchoring + machine honesty -/

namespace EuclidsPath
namespace Riemann
namespace ArithmeticTwoTransport

/-- An unconstrained atom exists: 3·1·1 = 1·1·1 + 2. -/
def trivialAtom : ArithmeticTransportAtom where
  q := 3; r := 1; s := 1; a := 1; b := 1; v := 1
  q_pos := by norm_num
  r_pos := by norm_num
  s_pos := by norm_num
  a_pos := by norm_num
  b_pos := by norm_num
  v_pos := by norm_num
  transport_identity := by norm_num

/-- Existence of an ADMISSIBLE atom is a Z-independent arithmetic question. -/
def AdmissibleAtomExists : Prop :=
  ∃ T : ArithmeticTransportAtom, Nonempty (ArithmeticAdmissible T)

/-- **HONESTY (gates are free):** inhabitedness of the law at a given Z ⟺
    existence of an admissible atom — anchor/noncircular/firewall
    are gated away for free (True/True/False). Zero anchoring is NOT yet load-bearing. -/
theorem law_iff_admissibleAtom
    {OffCriticalZero : Type} (Z : OffCriticalZero) :
    Nonempty (ArithmeticTwoTransportLaw OffCriticalZero Z) ↔
      AdmissibleAtomExists := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.atom, ⟨L.admissible⟩⟩
  · rintro ⟨T, ⟨adm⟩⟩
    exact ⟨⟨T, adm, ⟨True, trivial⟩,
      ⟨True, trivial, True, trivial, True, trivial⟩,
      ⟨False, fun h => h⟩⟩⟩

/-- Bridge ⟺ (there is a zero ⟹ an atom exists). -/
theorem bridge_iff
    {OffCriticalZero : Type} :
    ArithmeticTwoTransportBridge OffCriticalZero ↔
      (Nonempty OffCriticalZero → AdmissibleAtomExists) := by
  constructor
  · rintro h ⟨Z⟩
    exact (law_iff_admissibleAtom Z).mp (h Z)
  · intro h Z
    exact (law_iff_admissibleAtom Z).mpr (h ⟨Z⟩)

/-- Impossibility ⟺ (there is a zero ⟹ no atom exists). -/
theorem impossible_iff
    {OffCriticalZero : Type} :
    ArithmeticTwoTransportImpossible OffCriticalZero ↔
      (Nonempty OffCriticalZero → ¬ AdmissibleAtomExists) := by
  constructor
  · rintro h ⟨Z⟩ hAtom
    exact h Z ((law_iff_admissibleAtom Z).mpr hAtom)
  · intro h Z hLaw
    exact h ⟨Z⟩ ((law_iff_admissibleAtom Z).mp hLaw)

/-- **HONESTY (circularity with free gates):** the front's pair of inputs is
    jointly satisfiable ⟺ no zeros. Both inputs are ONE Z-independent
    arithmetic question (AdmissibleAtomExists), split by polarity:
    disentanglement is possible only if the anchor is made NON-free (genuine
    dependence of the law on the zero) — that is the next honest task. -/
theorem front_pair_iff_no_zero
    {OffCriticalZero : Type} :
    (ArithmeticTwoTransportBridge OffCriticalZero ∧
      ArithmeticTwoTransportImpossible OffCriticalZero) ↔
      ¬ Nonempty OffCriticalZero := by
  constructor
  · rintro ⟨hB, hI⟩ ⟨Z⟩
    exact hI Z (hB Z)
  · intro hNo
    exact ⟨fun Z => (hNo ⟨Z⟩).elim, fun Z => (hNo ⟨Z⟩).elim⟩

/-- Concrete RH assembly with REAL repo extraction (¬RH ⟹ zero). -/
theorem RH_of_concreteArithmeticFront
    (F : ArithmeticTwoTransportFront
      EuclidsPath.RiemannImpossibleEngineOff.OffCriticalZero) :
    RiemannHypothesis :=
  riemannHypothesis_of_arithmeticTwoTransportFront
    (fun hNotRH =>
      EuclidsPath.RiemannImpossibleEngineOff.offCriticalZero_of_not_RH hNotRH)
    F

end ArithmeticTwoTransport
end Riemann
end EuclidsPath
