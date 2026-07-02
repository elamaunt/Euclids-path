/-
  ClassicalPNPBridge — строгий мост Step00-локального P/NP к классическим
  классам + extraction-слой. Кирпичи: classical_pnp_bridge_strict +
  p_decider_extraction_field. Проза: prose/24 (§12).

  НЕ доказательство P ≠ NP (BridgeScopeGuard кирпича). Всё — условная сборка:
    * ClassicalProblem/PolyManyOneReduction/ClassicalComplexityFrame
      (InP/InNP АБСТРАКТНЫ; замыкание P под poly-preimage);
    * Step00LocalNode (verifier + local success) + twin/small-scale обструкции;
    * Step00ToClassicalBridge: несущее поле — P_decider_extracts_local_success;
      несжимаемость + мост ⟹ ClassesSeparate (относительно фрейма!);
    * extraction-слой: PDecider (sound/complete) + ConcretePAccess +
      LocalResolverTarget + CanonicalResolverReconstruction ⟹ недостающее
      поле построено (extracts_local_success); NP-hardness бухгалтерия §4.

  КОНКРЕТНАЯ ИНСТАНЦИАЦИЯ (при интеграции): concreteNode из LocalPNP.Concrete;
  P-сторона — теорема; ПРИ A ≤ 4 НЕСЖИМАЕМОСТЬ УЗЛА — ТЕОРЕМА (5-адическая
  цепь) — вторая половина RemainingClassicalBridgeObligation закрыта на малых
  масштабах безусловно; twin/small-scale обструкции инстанциированы.

  ⚠️ МАШИННАЯ ЧЕСТНОСТЬ: trivialFrame_separates_for_free — фрейм абстрактен,
  тривиальный фрейм разделяет классы ДАРОМ: без реальной модели машин никакого
  утверждения о настоящих P/NP нет; вся тяжесть — в верности фрейма + в
  CanonicalResolverReconstruction (живой фронт §7 extraction-кирпича).
  regateReconstruction — аудит-гейты свободны (маркеры, не проверки).
  Фикс кирпича: not_accepts_of_run_false — композиция равенств Bool.
-/
import Mathlib
import EuclidsPath.Engine.LocalPNPNode

set_option autoImplicit false

namespace EuclidsPath
namespace ClassicalPNPBridge

/-#############################################################################
  §1. Classical complexity interface
#############################################################################-/

/--
A classical decision problem/language, represented extensionally by its type of
instances and acceptance predicate.
-/
structure ClassicalProblem where
  Instance : Type
  Accepts : Instance → Prop

namespace ClassicalProblem

/-- Extensional implication between classical problems on possibly different encodings. -/
def Implies (A B : ClassicalProblem) : Prop :=
  ∀ x : A.Instance, A.Accepts x → ∃ y : B.Instance, B.Accepts y

end ClassicalProblem

/--
A many-one reduction with an explicit polynomial-time audit field.

The field `polynomial_time` is a proposition because this abstract bridge does
not choose a concrete machine model.  A concrete instantiation must replace it by
an actual Turing/RAM/Lambda encoding theorem.
-/
structure PolyManyOneReduction (A B : ClassicalProblem) where
  map : A.Instance → B.Instance
  preserves : ∀ x : A.Instance, A.Accepts x ↔ B.Accepts (map x)
  polynomial_time : Prop
  polynomial_time_proof : polynomial_time

/--
A minimal classical complexity frame.

`InP` and `InNP` are predicates on languages.  Closure of P under polynomial
many-one preimages is included because it is the standard theorem needed for
NP-hardness bookkeeping.  It is not used to smuggle in the Step00 bridge.
-/
structure ClassicalComplexityFrame where
  InP : ClassicalProblem → Prop
  InNP : ClassicalProblem → Prop
  P_closed_under_poly_preimage :
    ∀ {A B : ClassicalProblem},
      PolyManyOneReduction A B → InP B → InP A

namespace ClassicalComplexityFrame

/-- Classical class equality, extensionally over the chosen frame. -/
def ClassesCoincide (C : ClassicalComplexityFrame) : Prop :=
  ∀ L : ClassicalProblem, C.InP L ↔ C.InNP L

/-- Classical separation: an NP language outside P exists. -/
def ClassesSeparate (C : ClassicalComplexityFrame) : Prop :=
  ∃ L : ClassicalProblem, C.InNP L ∧ ¬ C.InP L

/-- A separating language proves non-coincidence of the two classical classes. -/
theorem classesSeparate_implies_not_classesCoincide
    {C : ClassicalComplexityFrame}
    (hSep : C.ClassesSeparate) :
    ¬ C.ClassesCoincide := by
  intro hEq
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP ((hEq L).2 hNP)

/-- Direct constructor for classical separation from one NP language outside P. -/
theorem classesSeparate_of_language
    {C : ClassicalComplexityFrame}
    {L : ClassicalProblem}
    (hNP : C.InNP L)
    (hNotP : ¬ C.InP L) :
    C.ClassesSeparate := by
  exact ⟨L, hNP, hNotP⟩

/-- If classical classes coincide, every NP language is in P. -/
theorem inP_of_inNP_under_classesCoincide
    {C : ClassicalComplexityFrame}
    (hEq : C.ClassesCoincide)
    {L : ClassicalProblem}
    (hNP : C.InNP L) :
    C.InP L :=
  (hEq L).2 hNP

end ClassicalComplexityFrame

/-#############################################################################
  §2. Abstract Step00-local node
#############################################################################-/

/--
The minimal local node needed for a classical bridge.

The previous Step00-local file gives a concrete instance by taking
`LocalPSuccess` to be `Nonempty (PolyCertificateSuffices P)`.
-/
structure Step00LocalNode where
  /-- Local verifier side: given genealogy certificates are easy to verify. -/
  VerifierEasy : Prop

  /-- Local P-success: finite/rank-bounded key resolves same-key genealogy collisions. -/
  LocalPSuccess : Prop

namespace Step00LocalNode

/-- Local incompressibility: the local resolving certificate does not exist. -/
def LocalSearchIncompressible (N : Step00LocalNode) : Prop :=
  ¬ N.LocalPSuccess

/-- Local incompressibility is exactly negation of local P-success. -/
theorem localSearchIncompressible_iff_not_localPSuccess
    (N : Step00LocalNode) :
    N.LocalSearchIncompressible ↔ ¬ N.LocalPSuccess := by
  rfl

end Step00LocalNode

/--
A twin-bound obstruction to local P-success.

This abstracts the earlier theorem:

    LocalPSuccess -> TwinAbove M0

so `¬ TwinAbove M0` implies local incompressibility.
-/
structure TwinBoundLocalObstruction (N : Step00LocalNode) where
  M0 : Nat
  TwinAbove : Nat → Prop
  detects : N.LocalPSuccess → TwinAbove M0

namespace TwinBoundLocalObstruction

/-- No twin above the horizon forces local incompressibility. -/
theorem localIncompressible_of_noTwinAbove
    {N : Step00LocalNode}
    (B : TwinBoundLocalObstruction N)
    (hNoTwinAbove : ¬ B.TwinAbove B.M0) :
    N.LocalSearchIncompressible := by
  intro hSuccess
  exact hNoTwinAbove (B.detects hSuccess)

end TwinBoundLocalObstruction

/--
A small-scale unconditional obstruction, e.g. an already checked theorem such as
`no_projection_resolves_at_smallScale` for `A ≤ 4`.
-/
structure SmallScaleLocalObstruction (N : Step00LocalNode) where
  A : Nat
  blocks : A ≤ 4 → N.LocalSearchIncompressible

namespace SmallScaleLocalObstruction

/-- At scale `A ≤ 4`, local incompressibility is unconditional. -/
theorem localIncompressible
    {N : Step00LocalNode}
    (S : SmallScaleLocalObstruction N)
    (hA : S.A ≤ 4) :
    N.LocalSearchIncompressible :=
  S.blocks hA

end SmallScaleLocalObstruction

/-#############################################################################
  §3. The actual Step00 -> classical bridge obligations
#############################################################################-/

/--
Encoding of a Step00-local genealogy-search node as a classical language.

The two load-bearing fields are:

* `verifier_yields_NP`: the Step00 verifier becomes an ordinary NP verifier;
* `P_decider_extracts_local_success`: any ordinary polynomial-time decider for
  the encoded language yields the Step00 local resolving certificate.

The second field is the hard bridge.  If it is missing, local separation does not
imply classical separation.
-/
structure Step00ToClassicalBridge
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  genealogyLanguage : ClassicalProblem

  verifier_yields_NP : C.InNP genealogyLanguage

  P_decider_extracts_local_success :
    C.InP genealogyLanguage → N.LocalPSuccess

  /-- Audit: the encoding preserves the intended genealogy-search semantics. -/
  faithful_encoding : Prop
  faithful_encoding_proof : faithful_encoding

  /-- Audit: witnesses of the classical language are actual Step00 genealogies. -/
  witness_soundness : Prop
  witness_soundness_proof : witness_soundness

  /-- Audit: the extraction from a P-decider does not invoke twin infinitude. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  /-- Audit: the extraction from a P-decider is not the final causal-closure axiom in disguise. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace Step00ToClassicalBridge

/-- The encoded genealogy-search language is in classical NP. -/
theorem genealogyLanguage_in_NP
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (B : Step00ToClassicalBridge C N) :
    C.InNP B.genealogyLanguage :=
  B.verifier_yields_NP

/--
If the local resolving certificate is impossible, the encoded language is not in P.
-/
theorem genealogyLanguage_not_in_P_of_localIncompressible
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (B : Step00ToClassicalBridge C N)
    (hLocal : N.LocalSearchIncompressible) :
    ¬ C.InP B.genealogyLanguage := by
  intro hP
  exact hLocal (B.P_decider_extracts_local_success hP)

/--
Main bridge theorem: local incompressibility plus the extraction bridge gives a
classical separating language.
-/
theorem classicalSeparation_of_localIncompressible
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (B : Step00ToClassicalBridge C N)
    (hLocal : N.LocalSearchIncompressible) :
    C.ClassesSeparate := by
  exact C.classesSeparate_of_language
    B.verifier_yields_NP
    (B.genealogyLanguage_not_in_P_of_localIncompressible hLocal)

/-- Same theorem as explicit non-coincidence of classes. -/
theorem classicalClasses_do_not_coincide_of_localIncompressible
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (B : Step00ToClassicalBridge C N)
    (hLocal : N.LocalSearchIncompressible) :
    ¬ C.ClassesCoincide := by
  exact C.classesSeparate_implies_not_classesCoincide
    (B.classicalSeparation_of_localIncompressible hLocal)

/--
Twin-bound version: if local P-success would detect a twin above `M0`, then a
no-twin-above bound gives classical separation through the bridge.
-/
theorem classicalSeparation_under_twinBound
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (Bridge : Step00ToClassicalBridge C N)
    (TwinObstruction : TwinBoundLocalObstruction N)
    (hNoTwinAbove : ¬ TwinObstruction.TwinAbove TwinObstruction.M0) :
    C.ClassesSeparate := by
  exact Bridge.classicalSeparation_of_localIncompressible
    (TwinObstruction.localIncompressible_of_noTwinAbove hNoTwinAbove)

/-- Non-coincidence form of the twin-bound theorem. -/
theorem classicalClasses_do_not_coincide_under_twinBound
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (Bridge : Step00ToClassicalBridge C N)
    (TwinObstruction : TwinBoundLocalObstruction N)
    (hNoTwinAbove : ¬ TwinObstruction.TwinAbove TwinObstruction.M0) :
    ¬ C.ClassesCoincide := by
  exact Bridge.classicalClasses_do_not_coincide_of_localIncompressible
    (TwinObstruction.localIncompressible_of_noTwinAbove hNoTwinAbove)

/--
Small-scale version: a checked `A ≤ 4` local obstruction gives a classical
separating language through the bridge.
-/
theorem classicalSeparation_at_smallScale
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (Bridge : Step00ToClassicalBridge C N)
    (Small : SmallScaleLocalObstruction N)
    (hA : Small.A ≤ 4) :
    C.ClassesSeparate := by
  exact Bridge.classicalSeparation_of_localIncompressible
    (Small.localIncompressible hA)

/-- Non-coincidence form of the small-scale theorem. -/
theorem classicalClasses_do_not_coincide_at_smallScale
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (Bridge : Step00ToClassicalBridge C N)
    (Small : SmallScaleLocalObstruction N)
    (hA : Small.A ≤ 4) :
    ¬ C.ClassesCoincide := by
  exact Bridge.classicalClasses_do_not_coincide_of_localIncompressible
    (Small.localIncompressible hA)

end Step00ToClassicalBridge

/-#############################################################################
  §4. NP-hardness bookkeeping: useful, but not the missing bridge
#############################################################################-/

/--
An NP-complete source problem reducing to the encoded Step00 genealogy language.

This is useful for orienting reductions, but it is not enough by itself to prove
`P ≠ NP`.  The decisive bridge remains `P_decider_extracts_local_success`.
-/
structure NPCompleteToStep00Bridge
    (C : ClassicalComplexityFrame)
    {N : Step00LocalNode}
    (B : Step00ToClassicalBridge C N) where
  source : ClassicalProblem
  source_in_NP : C.InNP source
  reduces_source_to_step00 : PolyManyOneReduction source B.genealogyLanguage

namespace NPCompleteToStep00Bridge

/-- If the Step00 language is in P, then the NP-complete source is in P. -/
theorem source_in_P_of_step00_in_P
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {B : Step00ToClassicalBridge C N}
    (R : NPCompleteToStep00Bridge C B)
    (hStep00P : C.InP B.genealogyLanguage) :
    C.InP R.source :=
  C.P_closed_under_poly_preimage R.reduces_source_to_step00 hStep00P

/-- If the source is not in P, then the Step00 language is not in P. -/
theorem step00_not_in_P_of_source_not_in_P
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {B : Step00ToClassicalBridge C N}
    (R : NPCompleteToStep00Bridge C B)
    (hSourceNotP : ¬ C.InP R.source) :
    ¬ C.InP B.genealogyLanguage := by
  intro hStep00P
  exact hSourceNotP (R.source_in_P_of_step00_in_P hStep00P)

end NPCompleteToStep00Bridge

/-#############################################################################
  §5. Bridge front: what remains to prove
#############################################################################-/

/--
The honest current bridge front from Step00-local separation to classical P/NP.
-/
structure ClassicalBridgeFront (C : ClassicalComplexityFrame) where
  localNode : Step00LocalNode
  bridge : Step00ToClassicalBridge C localNode

  /-- This is the decisive theorem: the concrete local node is incompressible. -/
  local_incompressible : localNode.LocalSearchIncompressible

namespace ClassicalBridgeFront

/-- A completed bridge front gives a classical separating language. -/
theorem gives_classicalSeparation
    {C : ClassicalComplexityFrame}
    (F : ClassicalBridgeFront C) :
    C.ClassesSeparate :=
  F.bridge.classicalSeparation_of_localIncompressible F.local_incompressible

/-- A completed bridge front gives non-coincidence of P and NP in the frame. -/
theorem gives_not_classesCoincide
    {C : ClassicalComplexityFrame}
    (F : ClassicalBridgeFront C) :
    ¬ C.ClassesCoincide :=
  F.bridge.classicalClasses_do_not_coincide_of_localIncompressible
    F.local_incompressible

end ClassicalBridgeFront

/--
The exact obligation left before claiming classical separation from the Step00
node.
-/
abbrev RemainingClassicalBridgeObligation
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∃ B : Step00ToClassicalBridge C N,
    N.LocalSearchIncompressible

/-- If the remaining bridge obligation is solved, classical separation follows. -/
theorem classicalSeparation_of_remainingBridgeObligation
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (H : RemainingClassicalBridgeObligation C N) :
    C.ClassesSeparate := by
  rcases H with ⟨B, hLocal⟩
  exact B.classicalSeparation_of_localIncompressible hLocal

/-- Non-coincidence form of the remaining-obligation theorem. -/
theorem not_classesCoincide_of_remainingBridgeObligation
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (H : RemainingClassicalBridgeObligation C N) :
    ¬ C.ClassesCoincide := by
  exact C.classesSeparate_implies_not_classesCoincide
    (classicalSeparation_of_remainingBridgeObligation H)

/-#############################################################################
  §6. Anti-overclaim guard
#############################################################################-/

/--
A guard recording that this file proves only conditional bridge theorems unless a
concrete `Step00ToClassicalBridge` is supplied.
-/
structure BridgeScopeGuard where
  no_claim_without_encoding : Prop
  no_claim_without_P_to_local_extraction : Prop
  no_claim_without_machine_model : Prop

/-- Canonical guard. -/
def bridgeScopeGuard : BridgeScopeGuard where
  no_claim_without_encoding := True
  no_claim_without_P_to_local_extraction := True
  no_claim_without_machine_model := True

/-- The guard is satisfied by construction. -/
theorem bridgeScopeGuard_ok :
    bridgeScopeGuard.no_claim_without_encoding ∧
    bridgeScopeGuard.no_claim_without_P_to_local_extraction ∧
    bridgeScopeGuard.no_claim_without_machine_model := by
  exact ⟨trivial, trivial, trivial⟩

/--
Final slogan: the missing bridge is exactly extraction of a local resolver from a
classical P decider for the encoded genealogy-search language.
-/
abbrev BridgeSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∀ B : Step00ToClassicalBridge C N,
    N.LocalSearchIncompressible → C.ClassesSeparate

/-- The bridge slogan is a theorem. -/
theorem bridgeSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) :
    BridgeSlogan C N := by
  intro B hLocal
  exact B.classicalSeparation_of_localIncompressible hLocal

end ClassicalPNPBridge
end EuclidsPath

namespace EuclidsPath
namespace ClassicalPNPBridge
namespace PDeciderExtraction

/-#############################################################################
  §1. Concrete deciders behind an abstract `InP` predicate
#############################################################################-/

/--
A concrete deterministic decider for a classical language.

The previous `ClassicalComplexityFrame` deliberately kept `InP` abstract.  To
extract Step00-local structure from `C.InP L`, we must expose an actual decider
object.  A concrete machine model can refine this structure with time bounds,
encodings and tapes; this bridge only needs the extensional decision interface.
-/
structure PDecider (L : ClassicalProblem) where
  run : L.Instance → Bool
  sound : ∀ x : L.Instance, run x = true → L.Accepts x
  complete : ∀ x : L.Instance, L.Accepts x → run x = true

namespace PDecider

/-- The decider is extensionally correct. -/
theorem accepts_iff_run_true
    {L : ClassicalProblem}
    (D : PDecider L)
    (x : L.Instance) :
    L.Accepts x ↔ D.run x = true := by
  constructor
  · exact D.complete x
  · exact D.sound x

/-- If the decider rejects, the language predicate is false. -/
theorem not_accepts_of_run_false
    {L : ClassicalProblem}
    (D : PDecider L)
    {x : L.Instance}
    (hFalse : D.run x = false) :
    ¬ L.Accepts x := by
  intro hAcc
  have hTrue : D.run x = true := D.complete x hAcc
  rw [hTrue] at hFalse
  exact Bool.noConfusion hFalse

end PDecider

/--
Access layer turning abstract `C.InP L` membership into an actual decider.

This is not automatic from the previous abstract frame.  It is a necessary
bridge assumption whenever we want to *extract* data from a classical P proof.
-/
structure ConcretePAccess (C : ClassicalComplexityFrame) where
  deciderOfInP : ∀ L : ClassicalProblem, C.InP L → Nonempty (PDecider L)

namespace ConcretePAccess

/-- Extract a concrete decider from a classical P-membership proof. -/
theorem exists_decider
    {C : ClassicalComplexityFrame}
    (A : ConcretePAccess C)
    {L : ClassicalProblem}
    (hP : C.InP L) :
    Nonempty (PDecider L) :=
  A.deciderOfInP L hP

end ConcretePAccess

/-#############################################################################
  §2. The local resolver target
#############################################################################-/

/--
A concrete object type whose realization is the Step00 local P-success
certificate.

For the concrete Step00-local file, instantiate `Resolver` as the actual finite
key / collision-resolving package, e.g. a `PolyCertificateSuffices P`, and
`realizes` as `Nonempty.intro`.
-/
structure LocalResolverTarget (N : Step00LocalNode) where
  Resolver : Type
  realizes : Resolver → N.LocalPSuccess

  /-- Audit: the resolver really carries a finite key system. -/
  finite_key_sound : Resolver → Prop
  finite_key_sound_proof : ∀ R : Resolver, finite_key_sound R

  /-- Audit: the resolver is bounded in the local rank/lexRank sense. -/
  rank_bounded : Resolver → Prop
  rank_bounded_proof : ∀ R : Resolver, rank_bounded R

  /-- Audit: the resolver resolves same-key genealogy collisions. -/
  collision_sound : Resolver → Prop
  collision_sound_proof : ∀ R : Resolver, collision_sound R

namespace LocalResolverTarget

/-- Any resolver in the target gives local P-success. -/
theorem localSuccess_of_resolver
    {N : Step00LocalNode}
    (T : LocalResolverTarget N)
    (R : T.Resolver) :
    N.LocalPSuccess :=
  T.realizes R

end LocalResolverTarget

/-#############################################################################
  §3. Encoded genealogy query interface
#############################################################################-/

/--
The query language seen by a classical decider.

This layer prevents the extractor from being a black box: it records that the
classical language is queried through genealogy/collision-shaped instances.
-/
structure GenealogyDecisionQueryInterface
    (L : ClassicalProblem) where

  Query : Type

  encode : Query → L.Instance

  /-- Audit: encoded instances faithfully represent Step00 genealogy queries. -/
  faithful_query_encoding : Prop
  faithful_query_encoding_proof : faithful_query_encoding

  /-- Audit: every query is tied to the intended Step00 genealogy/collision node. -/
  genealogy_query_sound : Prop
  genealogy_query_sound_proof : genealogy_query_sound

  /-- Audit: encoding has the intended polynomial/rank-bounded size behaviour. -/
  size_control : Prop
  size_control_proof : size_control

namespace GenealogyDecisionQueryInterface

/-- Run a decider on an encoded genealogy query. -/
def ask
    {L : ClassicalProblem}
    (Q : GenealogyDecisionQueryInterface L)
    (D : PDecider L)
    (q : Q.Query) : Bool :=
  D.run (Q.encode q)

/-- Soundness of a positive answer to an encoded query. -/
theorem accepts_of_ask_true
    {L : ClassicalProblem}
    (Q : GenealogyDecisionQueryInterface L)
    (D : PDecider L)
    {q : Q.Query}
    (h : Q.ask D q = true) :
    L.Accepts (Q.encode q) :=
  D.sound (Q.encode q) h

/-- Completeness of the decider on encoded queries. -/
theorem ask_true_of_accepts
    {L : ClassicalProblem}
    (Q : GenealogyDecisionQueryInterface L)
    (D : PDecider L)
    {q : Q.Query}
    (h : L.Accepts (Q.encode q)) :
    Q.ask D q = true :=
  D.complete (Q.encode q) h

end GenealogyDecisionQueryInterface

/-#############################################################################
  §4. Reconstructing a local resolver from a classical P decider
#############################################################################-/

/--
The concrete reconstruction theorem.

This is the load-bearing mathematical/programming object.  It says that a
classical decider for the encoded genealogy language can be self-reduced into a
local Step00 resolver.

In a concrete implementation, `reconstruct` should be an algorithm using queries
through `GenealogyDecisionQueryInterface.ask`; the audit fields below prevent the
field from hiding the final Step00 collision axiom.
-/
structure CanonicalResolverReconstruction
    (L : ClassicalProblem)
    {N : Step00LocalNode}
    (Target : LocalResolverTarget N) where

  queryInterface : GenealogyDecisionQueryInterface L

  reconstruct : PDecider L → Target.Resolver

  /-- Audit: reconstruction uses the decider only through encoded genealogy queries. -/
  uses_only_encoded_queries : Prop
  uses_only_encoded_queries_proof : uses_only_encoded_queries

  /-- Audit: reconstruction is uniform, not hand-picked for one hidden instance. -/
  uniform_over_instances : Prop
  uniform_over_instances_proof : uniform_over_instances

  /-- Audit: reconstructed finite keys are sound. -/
  finite_key_sound_after_reconstruction :
    ∀ D : PDecider L, Target.finite_key_sound (reconstruct D)

  /-- Audit: reconstructed resolver respects lexRank/rank bounds. -/
  rank_bounded_after_reconstruction :
    ∀ D : PDecider L, Target.rank_bounded (reconstruct D)

  /-- Audit: reconstructed resolver really resolves Step00 same-key collisions. -/
  collision_sound_after_reconstruction :
    ∀ D : PDecider L, Target.collision_sound (reconstruct D)

  /-- Audit: no use of twin infinitude or a twin oracle. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  /-- Audit: no use of Step00CausalClosureAxiom or equivalent final collision axiom. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace CanonicalResolverReconstruction

/-- A concrete decider reconstructs a local resolver. -/
def resolverOfDecider
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (R : CanonicalResolverReconstruction L Target)
    (D : PDecider L) :
    Target.Resolver :=
  R.reconstruct D

/-- A concrete decider reconstructs local P-success. -/
theorem localSuccessOfDecider
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (R : CanonicalResolverReconstruction L Target)
    (D : PDecider L) :
    N.LocalPSuccess :=
  Target.localSuccess_of_resolver (R.resolverOfDecider D)

end CanonicalResolverReconstruction

/-#############################################################################
  §5. The missing field, built from the extractor package
#############################################################################-/

/--
Package exactly sufficient to build

    C.InP L → N.LocalPSuccess.

This is the field we were missing in the previous bridge.
-/
structure PDeciderExtractionField
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode)
    (L : ClassicalProblem) where

  concreteP : ConcretePAccess C

  target : LocalResolverTarget N

  reconstruction : CanonicalResolverReconstruction L target

  /-- Audit: the extraction is not merely the final local P-success asserted as a field. -/
  non_vacuous_extraction : Prop
  non_vacuous_extraction_proof : non_vacuous_extraction

namespace PDeciderExtractionField

/--
The missing field from the previous bridge, now constructed from concrete
P-access plus canonical resolver reconstruction.
-/
theorem extracts_local_success
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    (F : PDeciderExtractionField C N L) :
    C.InP L → N.LocalPSuccess := by
  intro hP
  rcases F.concreteP.exists_decider hP with ⟨D⟩
  exact F.reconstruction.localSuccessOfDecider D

/-- If local P-success is impossible, the encoded language is not in P. -/
theorem language_not_in_P_of_localIncompressible
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    (F : PDeciderExtractionField C N L)
    (hLocal : N.LocalSearchIncompressible) :
    ¬ C.InP L := by
  intro hP
  exact hLocal (F.extracts_local_success hP)

end PDeciderExtractionField

/-#############################################################################
  §6. Building the full `Step00ToClassicalBridge` from the field
#############################################################################-/

/--
All encoding data except the missing P-decider extraction field.
-/
structure Step00EncodingData
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  genealogyLanguage : ClassicalProblem

  verifier_yields_NP : C.InNP genealogyLanguage

  faithful_encoding : Prop
  faithful_encoding_proof : faithful_encoding

  witness_soundness : Prop
  witness_soundness_proof : witness_soundness

/--
A strict completed encoding: ordinary NP verifier side plus the extracted
`P_decider_extracts_local_success` field.
-/
structure StrictStep00ClassicalEncoding
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  encoding : Step00EncodingData C N

  extraction : PDeciderExtractionField C N encoding.genealogyLanguage

namespace StrictStep00ClassicalEncoding

/-- Convert the strict encoding into the previous bridge object. -/
def toBridge
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (E : StrictStep00ClassicalEncoding C N) :
    Step00ToClassicalBridge C N where

  genealogyLanguage := E.encoding.genealogyLanguage

  verifier_yields_NP := E.encoding.verifier_yields_NP

  P_decider_extracts_local_success := E.extraction.extracts_local_success

  faithful_encoding := E.encoding.faithful_encoding
  faithful_encoding_proof := E.encoding.faithful_encoding_proof

  witness_soundness := E.encoding.witness_soundness
  witness_soundness_proof := E.encoding.witness_soundness_proof

  no_twin_axiom_leak := E.extraction.reconstruction.no_twin_axiom_leak
  no_twin_axiom_leak_proof := E.extraction.reconstruction.no_twin_axiom_leak_proof

  no_causal_closure_leak := E.extraction.reconstruction.no_causal_closure_leak
  no_causal_closure_leak_proof := E.extraction.reconstruction.no_causal_closure_leak_proof

/-- The strict encoding provides the exact missing field. -/
theorem provides_missing_field
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (E : StrictStep00ClassicalEncoding C N) :
    C.InP E.encoding.genealogyLanguage → N.LocalPSuccess :=
  E.extraction.extracts_local_success

/-- With local incompressibility, the strict encoding gives a classical separating language. -/
theorem classicalSeparation_of_localIncompressible
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (E : StrictStep00ClassicalEncoding C N)
    (hLocal : N.LocalSearchIncompressible) :
    C.ClassesSeparate :=
  E.toBridge.classicalSeparation_of_localIncompressible hLocal

/-- Non-coincidence form. -/
theorem not_classesCoincide_of_localIncompressible
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (E : StrictStep00ClassicalEncoding C N)
    (hLocal : N.LocalSearchIncompressible) :
    ¬ C.ClassesCoincide :=
  E.toBridge.classicalClasses_do_not_coincide_of_localIncompressible hLocal

/-- The previous remaining bridge obligation is solved by strict encoding plus local incompressibility. -/
theorem remainingBridgeObligation_of_strictEncoding
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (E : StrictStep00ClassicalEncoding C N)
    (hLocal : N.LocalSearchIncompressible) :
    RemainingClassicalBridgeObligation C N := by
  exact ⟨E.toBridge, hLocal⟩

end StrictStep00ClassicalEncoding

/-#############################################################################
  §7. Final current frontier
#############################################################################-/

/--
After this patch, the live concrete frontier is exactly this object.

To complete the classical bridge in a real machine model, instantiate:

* `ConcretePAccess` for the chosen model;
* `Step00EncodingData` for the encoded genealogy language;
* `CanonicalResolverReconstruction`, i.e. the self-reduction extracting a local
  finite-key collision resolver from every P decider for that language.
-/
structure CurrentExtractionFront
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  strictEncoding : StrictStep00ClassicalEncoding C N

  local_incompressible : N.LocalSearchIncompressible

namespace CurrentExtractionFront

/-- A completed current extraction front gives classical separation. -/
theorem gives_classicalSeparation
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CurrentExtractionFront C N) :
    C.ClassesSeparate :=
  F.strictEncoding.classicalSeparation_of_localIncompressible F.local_incompressible

/-- A completed current extraction front gives non-coincidence of the classes. -/
theorem gives_not_classesCoincide
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CurrentExtractionFront C N) :
    ¬ C.ClassesCoincide :=
  F.strictEncoding.not_classesCoincide_of_localIncompressible F.local_incompressible

end CurrentExtractionFront

/--
Slogan: the missing field is no longer opaque.  It is exactly concrete P-access
plus canonical reconstruction of a Step00 local resolver from a P decider.
-/
abbrev ExtractionFieldSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode)
    (L : ClassicalProblem) : Prop :=
  ∀ F : PDeciderExtractionField C N L,
    C.InP L → N.LocalPSuccess

/-- The extraction-field slogan is a theorem. -/
theorem extractionFieldSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode)
    (L : ClassicalProblem) :
    ExtractionFieldSlogan C N L := by
  intro F hP
  exact F.extracts_local_success hP

end PDeciderExtraction
end ClassicalPNPBridge
end EuclidsPath

/-! Конкретная инстанциация узла + машинная честность -/

namespace EuclidsPath
namespace ClassicalPNPBridge

open EuclidsPath.LocalPNP EuclidsPath.LocalPNP.Concrete

/-- Конкретный узел из локального P/NP-модуля (обе стороны). -/
def concreteNode (A M0 : ℕ) : Step00LocalNode where
  VerifierEasy :=
    ∀ i, GenealogyCertificate.VerificationEasy ((concreteFamily A M0).cert i)
  LocalPSuccess := EuclidsPath.LocalPNP.LocalPSuccess (concreteProblem A M0)

/-- P-сторона конкретного узла — теорема (verificationEasy_always). -/
theorem concreteNode_verifierEasy (A M0 : ℕ) :
    (concreteNode A M0).VerifierEasy :=
  fun i => GenealogyCertificate.verificationEasy_always _

/-- **При A ≤ 4 несжимаемость конкретного узла — ТЕОРЕМА** (5-адическая цепь). -/
theorem concreteNode_incompressible_smallScale {A : ℕ} (hA : A ≤ 4) :
    (concreteNode A 1).LocalSearchIncompressible :=
  concrete_localSearchIncompressible_smallScale hA

/-- Конкретная small-scale обструкция для моста. -/
def concreteSmallScaleObstruction (A : ℕ) :
    SmallScaleLocalObstruction (concreteNode A 1) where
  A := A
  blocks := fun hA => concreteNode_incompressible_smallScale hA

/-- Конкретная twin-обструкция: локальный P-успех детектирует twin выше M0. -/
noncomputable def concreteTwinObstruction (A M0 : ℕ) :
    TwinBoundLocalObstruction (concreteNode A M0) where
  M0 := M0
  TwinAbove := fun m0 =>
    ∃ m : ℕ, m0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m
  detects := fun h => by
    rcases h with ⟨S⟩
    exact (concreteTwinDetector A M0).detects S

/-- **ЧЕСТНОСТЬ (относительность фрейма):** InP/InNP абстрактны — тривиальный
    фрейм делает «разделение классов» БЕСПЛАТНЫМ. Никакое утверждение о
    настоящих P/NP не возникает, пока фрейм не инстанциирован реальной
    моделью машин; вся тяжесть — в верности фрейма и в извлечении. -/
def trivialFrame : ClassicalComplexityFrame where
  InP := fun _ => False
  InNP := fun _ => True
  P_closed_under_poly_preimage := fun _ h => h.elim

theorem trivialFrame_separates_for_free :
    trivialFrame.ClassesSeparate :=
  ⟨⟨PUnit, fun _ => True⟩, trivial, fun h => h⟩

/-- **ЧЕСТНОСТЬ (гейты свободны):** аудит-поля Prop-типа перегейтируются в
    True — документирующие маркеры, не машинные проверки. -/
def PDeciderExtraction.regateReconstruction
    {L : ClassicalProblem} {N : Step00LocalNode}
    {Target : PDeciderExtraction.LocalResolverTarget N}
    (R : PDeciderExtraction.CanonicalResolverReconstruction L Target) :
    PDeciderExtraction.CanonicalResolverReconstruction L Target :=
  { R with
    uses_only_encoded_queries := True
    uses_only_encoded_queries_proof := trivial
    uniform_over_instances := True
    uniform_over_instances_proof := trivial
    no_twin_axiom_leak := True
    no_twin_axiom_leak_proof := trivial
    no_causal_closure_leak := True
    no_causal_closure_leak_proof := trivial }

end ClassicalPNPBridge
end EuclidsPath
