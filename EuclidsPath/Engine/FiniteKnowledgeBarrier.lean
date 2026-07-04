/-
  FiniteKnowledgeBarrier — STRICT theorem: "a finite system can know
  almost nothing about twin primes" (author's request; joining the parity
  wall ParityBarrier with the epistemics of the first cause).
  Prose: prose/24 (section "Epistemics").

  PROVED HERE (UNCONDITIONALLY; core — propext only):
    * knowledge_forces_pure_class — finite sound knowledge of a twin B
      is possible ONLY if the entire finite equivalence class of B consists of
      twins: finite knowledge is about the class, not about the number;
    * mixed_class_twin_unknowable — a twin whose finite class contains
      even one non-twin is FUNDAMENTALLY unknowable by any finite system at
      that level;
    * trivialView_knows_nothing / trivialView_infinitude_unknowable —
      concrete instantiation: for the trivial view the knowledge is EMPTY and
      infinitude is unknowable (unconditionally; non-twin m=4);
    * knowsInfinite_forces_cofinal_pure_classes /
      infinitude_unknowable_of_eventually_mixed — infinitude can be certified
      only when cofinally pure classes exist; with eventual mixing —
      it cannot;
    * knowing_twins_requires_cofinal_information — wall in the knowledge
      dictionary;
    * two_walls_one_nature — TWO WALLS, ONE NATURE: from inside a finite
      view twins with a mixed class are invisible; from inside the system the
      first cause is invisible (cause_unknowable). The infinitude of twins and
      the first cause are external knowledge for any finite/internal system.

  HONEST BOUNDARY: mixed classes of a non-trivial view at concrete levels
  are an arithmetic input (like the AmbiguousAtEveryFiniteLevel wall);
  structural theorems and the trivial-view instantiation are unconditional here.
-/
import Mathlib
import EuclidsPath.Engine.ParityBarrier
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath
namespace FiniteKnowledgeBarrier

open EuclidsPath.ParityBarrier
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- "A finite system KNOWS twin B": a sound certificate depending only on
    the finite view of level A fires on B. -/
def FiniteSystemKnowsTwin (S : SieveViewSystem) (A : ℕ)
    (Cert : ℕ → Prop) (B : ℕ) : Prop :=
  ParityBlindPredicate S A Cert ∧ SoundTwinCert Cert ∧ Cert B

/-- **CLASS PURITY (unconditionally):** a finite sound system can know twin B
    only if the ENTIRE finite equivalence class of B consists of twins.
    Finite knowledge is not about B — it is about the class as a whole. -/
theorem knowledge_forces_pure_class
    (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) (B : ℕ)
    (hK : FiniteSystemKnowsTwin S A Cert B) :
    ∀ B' : ℕ, SieveEquivalent S A B B' → IsTwin B' := by
  obtain ⟨hBlind, hSound, hCB⟩ := hK
  intro B' hEq
  exact hSound B' ((hBlind B B' hEq).mp hCB)

/-- **MIXED-CLASS INVISIBILITY (unconditionally):** a twin whose finite class
    contains even one non-twin is FUNDAMENTALLY unknowable by any finite system
    at that level. -/
theorem mixed_class_twin_unknowable
    (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) (B : ℕ)
    (bad : ℕ) (hEq : SieveEquivalent S A B bad) (hNot : ¬ IsTwin bad) :
    ¬ FiniteSystemKnowsTwin S A Cert B :=
  fun hK => hNot (knowledge_forces_pure_class S A Cert B hK bad hEq)

/-- The coarsest system: trivial view (everything is equivalent to everything). -/
def trivialView : SieveViewSystem where
  View := fun _ => Unit
  view := fun _ _ => ()

/-- **CONCRETE TOTAL BLINDNESS (unconditionally, instantiated):** for the
    trivial view finite knowledge is EMPTY — the common class always contains
    a non-twin (from exists_clean_nonTwin_block). -/
theorem trivialView_knows_nothing (A : ℕ) (Cert : ℕ → Prop) :
    ∀ B : ℕ, ¬ FiniteSystemKnowsTwin trivialView A Cert B := by
  intro B hK
  obtain ⟨m, _, hNot⟩ := exists_clean_nonTwin_block
  exact hNot (knowledge_forces_pure_class trivialView A Cert B hK m rfl)

/-- "Knowledge of infinitude": the system presents a known twin above every
    threshold. -/
def FiniteSystemKnowsTwinsInfinite (S : SieveViewSystem) (A : ℕ)
    (Cert : ℕ → Prop) : Prop :=
  ∀ N : ℕ, ∃ B : ℕ, N < B ∧ FiniteSystemKnowsTwin S A Cert B

/-- **KNOWLEDGE OF INFINITUDE REQUIRES COFINALLY PURE CLASSES (unconditionally):**
    a finite system can certify infinitude only if cofinally there exist
    ENTIRELY twin classes of its finite view. -/
theorem knowsInfinite_forces_cofinal_pure_classes
    (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop)
    (hInf : FiniteSystemKnowsTwinsInfinite S A Cert) :
    ∀ N : ℕ, ∃ B : ℕ, N < B ∧
      ∀ B' : ℕ, SieveEquivalent S A B B' → IsTwin B' := by
  intro N
  obtain ⟨B, hNB, hK⟩ := hInf N
  exact ⟨B, hNB, knowledge_forces_pure_class S A Cert B hK⟩

/-- **INFINITUDE UNKNOWABLE under eventual mixing (unconditionally):** if
    beyond some threshold the class of EVERY block contains a non-twin, no
    finite system at level A can certify the infinitude of twins. -/
theorem infinitude_unknowable_of_eventually_mixed
    (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop)
    (hMix : ∃ N : ℕ, ∀ B : ℕ, N < B →
      ∃ bad : ℕ, SieveEquivalent S A B bad ∧ ¬ IsTwin bad) :
    ¬ FiniteSystemKnowsTwinsInfinite S A Cert := by
  intro hInf
  obtain ⟨N, hN⟩ := hMix
  obtain ⟨B, hNB, hpure⟩ :=
    knowsInfinite_forces_cofinal_pure_classes S A Cert hInf N
  obtain ⟨bad, hEq, hNot⟩ := hN B hNB
  exact hNot (hpure bad hEq)

/-- For the trivial view infinitude is unknowable UNCONDITIONALLY. -/
theorem trivialView_infinitude_unknowable (A : ℕ) (Cert : ℕ → Prop) :
    ¬ FiniteSystemKnowsTwinsInfinite trivialView A Cert := by
  apply infinitude_unknowable_of_eventually_mixed
  obtain ⟨m, _, hNot⟩ := exists_clean_nonTwin_block
  exact ⟨0, fun B _ => ⟨m, rfl, hNot⟩⟩

/-- Restatement of the wall in the knowledge dictionary: a sound certificate
    under ambiguity at every level must see cofinally (not a finite system). -/
theorem knowing_twins_requires_cofinal_information
    (S : SieveViewSystem) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert)
    (hAmbAll : AmbiguousAtEveryFiniteLevel S Cert) :
    RequiresCofinalInformation S Cert :=
  sound_cert_requires_cofinal_information S Cert hSound hAmbAll

/-- **TWO WALLS — ONE NATURE (both are theorems, axiom-free):**
    from inside a finite view, twins with a mixed class are invisible;
    from inside the system, the first cause is invisible (knowledge = engine).
    The infinitude of twins and the first cause are external knowledge for any
    finite/internal system. -/
theorem two_walls_one_nature :
    (∀ (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) (B bad : ℕ),
        SieveEquivalent S A B bad → ¬ IsTwin bad →
        ¬ FiniteSystemKnowsTwin S A Cert B) ∧
    ¬ InternalKnowledgeOfCause :=
  ⟨fun S A Cert B bad hEq hNot =>
      mixed_class_twin_unknowable S A Cert B bad hEq hNot,
   cause_unknowable⟩



/-#############################################################################
  MASTER THEOREM OF HIGHER-ENERGY INCOMPATIBILITY
  (by the author's decision; unconditional core + corollary under the first cause)
#############################################################################-/

/-- **MASTER THEOREM OF HIGHER-ENERGY INCOMPATIBILITY (core,
    unconditionally).** Internal/finite knowledge is energetically incompatible
    with infinitude — five facets of one incompatibility:

    1. knowledge of the first cause BUILDS a perpetual engine;
    2. therefore the first cause is unknowable (no engines exist — lexRank);
    3. a finite view knows a twin only through an entirely pure class —
       a twin with a mixed class is fundamentally invisible;
    4. under eventual class mixing the infinitude of twins cannot be certified
       from within;
    5. CARRIER FACET: the incompatibility itself (absence of engines =
       unknowability) + the accepted causal boundary ⟹ twins are infinite —
       infinitude arrives precisely FROM incompatibility.

    Energy reading: "knowing from within" costs infinite energy (perpetual
    engine), which a closed system does not have; the infinitude of twins is
    external knowledge, paid for by the first cause. -/
theorem higherEnergyIncompatibility_main :
    (InternalKnowledgeOfCause → SomeConcreteEuclideanEngine) ∧
    (¬ InternalKnowledgeOfCause) ∧
    (∀ (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) (B bad : ℕ),
        SieveEquivalent S A B bad → ¬ IsTwin bad →
        ¬ FiniteSystemKnowsTwin S A Cert B) ∧
    (∀ (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop),
        (∃ N : ℕ, ∀ B : ℕ, N < B →
          ∃ bad : ℕ, SieveEquivalent S A B bad ∧ ¬ IsTwin bad) →
        ¬ FiniteSystemKnowsTwinsInfinite S A Cert) ∧
    (¬ SomeConcreteEuclideanEngine → Step00CausalClosureAxiom →
        EuclidsPath.TwinLowers.Infinite) :=
  ⟨knowledge_builds_perpetualEngine,
   cause_unknowable,
   fun S A Cert B bad hEq hNot =>
     mixed_class_twin_unknowable S A Cert B bad hEq hNot,
   fun S A Cert hMix =>
     infinitude_unknowable_of_eventually_mixed S A Cert hMix,
   twins_infinite_of_noEngine_and_boundary⟩

/-- **Corollary of the master theorem under the accepted first cause:** twins
    are infinite — because knowing is impossible. ⚠️ AXIOM-TAINTED (facet 5
    instantiated by decree; the core above is fully green). -/
theorem higherEnergyIncompatibility_twins :
    EuclidsPath.TwinLowers.Infinite :=
  twins_because_unknowable

end FiniteKnowledgeBarrier
end EuclidsPath
