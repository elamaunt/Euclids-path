/-
  LocalPNPNode — строгий локальный P/NP-узел (кирпич: local_pnp_node_strict)
  + КОНКРЕТНАЯ ИНСТАНЦИАЦИЯ из объектов репо (добавлена при интеграции).
  Проза: prose/24 (§12-аналогия). НЕ утверждение о классических P/NP:
  ни машин Тьюринга, ни редукций, ни теоремы «P ≠ NP» (scope guard кирпича).

  Кирпич (абстрактно, всё доказано): ранжированный граф со строгим спуском;
  сертификаты-генеалогии; P-сторона (verificationEasy_always, длина ≤ lexRank);
  конечноключевая компрессия и коллизии; LocalPSuccess/incompressibility;
  twin-детектор-мост; small-scale firewall; семантический интерфейс.

  КОНКРЕТНАЯ ИНСТАНЦИАЦИЯ (LocalPNP.Concrete): граф = САМ Step00-граф
  (State, RealStep, lexRank); сертификаты флоу ИНЪЕКТИВНЫ (данные-поля +
  proof irrelevance); интерфейс: LocalPSuccess ⟺ ∃ резолвящая проекция;
  детектор — twin_above_of_resolves; **при A ≤ 4 collision principle и
  несжимаемость БЕЗУСЛОВНЫ** (5-адическая цепь) — полный статус-пакет
  LocalPNPStatus инстанциирован машинно.
  Фикс кирпича: induction-имена в len_le_lexRank (inaccessible vars).
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph

set_option autoImplicit false

namespace EuclidsPath
namespace LocalPNP

/-#############################################################################
  §1. Ranked forward graph and finite genealogy paths
#############################################################################-/

/--
A forward graph with a natural-valued `lexRank` that strictly decreases on every
legal forward step.

This is the local substitute for a genuine complexity measure.  It is not a
Turing-machine running time; it is the Step00 rank budget.
-/
structure RankedForwardGraph where
  State : Type
  Step : State → State → Prop
  lexRank : State → Nat
  step_decreases : ∀ {x y : State}, Step x y → lexRank y < lexRank x

/-- A length-indexed forward path. -/
inductive PathN (G : RankedForwardGraph) : G.State → G.State → Nat → Prop where
  | nil (x : G.State) : PathN G x x 0
  | cons {x y z : G.State} {n : Nat} :
      G.Step x y → PathN G y z n → PathN G x z (n + 1)

namespace PathN

/-- The length of a forward path is bounded by the starting `lexRank`. -/
theorem len_le_lexRank
    {G : RankedForwardGraph} {x y : G.State} {n : Nat}
    (p : PathN G x y n) :
    n ≤ G.lexRank x := by
  induction p with
  | nil x =>
      simp
  | cons hxy hyz ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (G.step_decreases hxy))

end PathN

/--
A genealogy certificate is just a finite legal path with named start, finish and
length.
-/
structure GenealogyCertificate (G : RankedForwardGraph) where
  start : G.State
  finish : G.State
  len : Nat
  path : PathN G start finish len

namespace GenealogyCertificate

/-- The certificate length is bounded by the starting rank. -/
theorem steps_le_lexRank
    {G : RankedForwardGraph} (c : GenealogyCertificate G) :
    c.len ≤ G.lexRank c.start :=
  PathN.len_le_lexRank c.path

/-- Local verification predicate: the certificate carries a legal path and a rank bound. -/
def VerificationEasy {G : RankedForwardGraph} (c : GenealogyCertificate G) : Prop :=
  PathN G c.start c.finish c.len ∧ c.len ≤ G.lexRank c.start

/-- Every genealogy certificate is easy to verify in the Step00-local sense. -/
theorem verificationEasy_always
    {G : RankedForwardGraph} (c : GenealogyCertificate G) :
    VerificationEasy c := by
  exact ⟨c.path, c.steps_le_lexRank⟩

end GenealogyCertificate

/-#############################################################################
  §2. Admissible genealogy families and finite-key compression
#############################################################################-/

/--
An indexed family of admissible genealogy certificates.

`distinct_cert` says different indices really represent different genealogies.
The actual infinitude/pigeonhole theorem is supplied separately by
`FiniteKeyCollisionPrinciple`, so this file can be used with either an already
machine-proved infinite-family theorem or a concrete finite-scale adversarial
probe.
-/
structure GenealogyFamily (G : RankedForwardGraph) where
  Index : Type
  cert : Index → GenealogyCertificate G
  distinct_cert : Function.Injective cert

/-- A finite-key compressor for a genealogy family. -/
structure FiniteKeyCompression {G : RankedForwardGraph} (F : GenealogyFamily G) where
  Key : Type
  finite_key : Fintype Key
  keyOf : F.Index → Key

namespace FiniteKeyCompression

instance {G : RankedForwardGraph} {F : GenealogyFamily G}
    (C : FiniteKeyCompression F) : Fintype C.Key :=
  C.finite_key

/-- The compressor is injective if no two genealogy indices share a key. -/
def Injective {G : RankedForwardGraph} {F : GenealogyFamily G}
    (C : FiniteKeyCompression F) : Prop :=
  Function.Injective C.keyOf

end FiniteKeyCompression

/-- A same-key collision of two distinct genealogy indices. -/
structure KeyCollision {G : RankedForwardGraph} {F : GenealogyFamily G}
    (C : FiniteKeyCompression F) where
  i : F.Index
  j : F.Index
  distinct : i ≠ j
  same_key : C.keyOf i = C.keyOf j

/--
Pigeonhole/collision principle for a family: every finite-key compressor creates
a same-key collision.

For a genuinely infinite admissible family this is the usual finite-pigeonhole
obstruction.  We keep it as an explicit parameter so the file does not smuggle in
any hidden infinitude theorem.
-/
def FiniteKeyCollisionPrinciple
    {G : RankedForwardGraph} (F : GenealogyFamily G) : Prop :=
  ∀ C : FiniteKeyCompression F, Nonempty (KeyCollision C)

/-- If every finite-key compression collides, no finite-key compression is injective. -/
theorem no_injective_finiteKeyCompression_of_collisionPrinciple
    {G : RankedForwardGraph} {F : GenealogyFamily G}
    (hCollide : FiniteKeyCollisionPrinciple F)
    (C : FiniteKeyCompression F) :
    ¬ C.Injective := by
  intro hInj
  rcases hCollide C with ⟨K⟩
  exact K.distinct (hInj K.same_key)

/-#############################################################################
  §3. Local search problem and local P-success
#############################################################################-/

/--
A Step00-local search problem: an admissible genealogy family plus a local notion
of resolving a collision of two genealogy indices.
-/
structure Step00LocalSearchProblem (G : RankedForwardGraph) where
  family : GenealogyFamily G
  CollisionResolution : family.Index → family.Index → Prop

namespace Step00LocalSearchProblem

/-- Every certificate in the problem is easy to verify. -/
theorem verificationEasy_for_family
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G)
    (i : P.family.Index) :
    GenealogyCertificate.VerificationEasy (P.family.cert i) :=
  GenealogyCertificate.verificationEasy_always (P.family.cert i)

/-- The length of every family certificate is bounded by the starting `lexRank`. -/
theorem family_steps_le_lexRank
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G)
    (i : P.family.Index) :
    (P.family.cert i).len ≤ G.lexRank (P.family.cert i).start :=
  GenealogyCertificate.steps_le_lexRank (P.family.cert i)

end Step00LocalSearchProblem

/--
`PolyCertificateSuffices` is local P-success: one finite key system resolves all
same-key collisions of distinct admissible genealogies.

This is not classical polynomial time.  The word `Poly` here records the local
rank-bounded verifier/compressor role from the Step00 audit.
-/
structure PolyCertificateSuffices
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where
  compression : FiniteKeyCompression P.family
  resolves :
    ∀ {i j : P.family.Index},
      i ≠ j →
      compression.keyOf i = compression.keyOf j →
      P.CollisionResolution i j

/-- Local P-success exists iff there is a resolving finite-key certificate. -/
def LocalPSuccess {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) : Prop :=
  Nonempty (PolyCertificateSuffices P)

/-- Local search incompressibility means no resolving finite-key certificate exists. -/
def LocalSearchIncompressible
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) : Prop :=
  ¬ LocalPSuccess P

/--
A resolving finite-key certificate turns any forced key collision into a resolved
collision.
-/
theorem resolved_collision_of_polyCertificate
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (S : PolyCertificateSuffices P)
    (K : KeyCollision S.compression) :
    P.CollisionResolution K.i K.j := by
  exact S.resolves K.distinct K.same_key

/--
If finite-key collisions are unavoidable, local P-success supplies at least one
resolved collision.
-/
theorem exists_resolved_collision_of_polyCertificate_and_collisionPrinciple
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (hCollide : FiniteKeyCollisionPrinciple P.family)
    (S : PolyCertificateSuffices P) :
    ∃ i j : P.family.Index, i ≠ j ∧ P.CollisionResolution i j := by
  rcases hCollide S.compression with ⟨K⟩
  exact ⟨K.i, K.j, K.distinct, resolved_collision_of_polyCertificate S K⟩

/-#############################################################################
  §4. Twin detector bridge
#############################################################################-/

/--
A local bridge saying that successful collision resolution detects a twin above
`M0`.

This abstracts the session theorem called informally
`twin_above_of_resolves`.
-/
structure TwinDetectorBridge
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where
  M0 : Nat
  TwinAbove : Nat → Prop
  detects : PolyCertificateSuffices P → TwinAbove M0

/-- Local P-success detects a twin above the chosen horizon. -/
theorem localP_success_detects_twin
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (B : TwinDetectorBridge P)
    (S : PolyCertificateSuffices P) :
    B.TwinAbove B.M0 :=
  B.detects S

/-- If there is no twin above `M0`, local P-success is impossible. -/
theorem twinBound_forces_localSearchIncompressible
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (B : TwinDetectorBridge P)
    (hNoTwinAbove : ¬ B.TwinAbove B.M0) :
    LocalSearchIncompressible P := by
  intro hSuccess
  rcases hSuccess with ⟨S⟩
  exact hNoTwinAbove (B.detects S)

/-- Same result in `IsEmpty` form. -/
theorem isEmpty_polyCertificateSuffices_of_twinBound
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (B : TwinDetectorBridge P)
    (hNoTwinAbove : ¬ B.TwinAbove B.M0) :
    IsEmpty (PolyCertificateSuffices P) := by
  exact ⟨fun S => hNoTwinAbove (B.detects S)⟩

/-#############################################################################
  §5. Small-scale unconditional firewall
#############################################################################-/

/--
An external small-scale theorem of the form:

  if `A ≤ 4`, no projection resolves all collisions.

This is where a machine theorem such as `no_projection_resolves_at_smallScale`
plugs into the local P/NP node.
-/
structure SmallScaleFirewall
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where
  A : Nat
  no_projection_resolves_at_smallScale :
    A ≤ 4 → LocalSearchIncompressible P

/-- At scale `A ≤ 4`, local search incompressibility is unconditional. -/
theorem smallScale_unconditional_localSearchIncompressible
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (W : SmallScaleFirewall P)
    (hA : W.A ≤ 4) :
    LocalSearchIncompressible P :=
  W.no_projection_resolves_at_smallScale hA

/-#############################################################################
  §6. Semantic Step00 collision-resolution interface
#############################################################################-/

/--
Interface between local P-success and the final Step00 semantic collision node.

The actual twin-prime branch identifies this semantic node with the final
causal-closure obligation.  This structure records the equivalence without
pretending it is a classical complexity-theoretic result.
-/
structure SemanticCollisionInterface
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where
  SemanticFlowLedgerCollisionResolves : Prop
  poly_to_semantic :
    PolyCertificateSuffices P → SemanticFlowLedgerCollisionResolves
  semantic_to_poly :
    SemanticFlowLedgerCollisionResolves → PolyCertificateSuffices P

namespace SemanticCollisionInterface

/-- Local P-success is equivalent to the semantic Step00 collision-resolution node. -/
theorem localPSuccess_iff_semanticFlowLedgerCollisionResolves
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (I : SemanticCollisionInterface P) :
    LocalPSuccess P ↔ I.SemanticFlowLedgerCollisionResolves := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact I.poly_to_semantic S
  · intro h
    exact ⟨I.semantic_to_poly h⟩

/-- If semantic collision resolution detects twins, then local P-success detects twins. -/
def semanticTwinDetector
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (I : SemanticCollisionInterface P)
    (M0 : Nat)
    (TwinAbove : Nat → Prop)
    (hSemanticDetectsTwin :
      I.SemanticFlowLedgerCollisionResolves → TwinAbove M0) :
    TwinDetectorBridge P where
  M0 := M0
  TwinAbove := TwinAbove
  detects := by
    intro S
    exact hSemanticDetectsTwin (I.poly_to_semantic S)

end SemanticCollisionInterface

/-#############################################################################
  §7. Classical P/NP scope guard
#############################################################################-/

/--
A classical-complexity bridge would need actual encodings/reductions.  This file
does not build such a bridge.
-/
structure ClassicalPNPBridge where
  Language : Type
  Instance : Type
  Witness : Instance → Type
  verifier : ∀ I : Instance, Witness I → Prop
  reduction_to_genealogy_search : Prop
  reduction_from_genealogy_search : Prop

/--
The exact scope of this file: local verifier/search/compression statements exist,
but no classical P/NP bridge is produced here.
-/
structure LocalPNPScopeGuard where
  no_turing_machine_model_declared : Prop
  no_np_complete_reduction_declared : Prop
  no_classical_PneqNP_claim : Prop

/-- A canonical scope guard. -/
def localPNP_scopeGuard : LocalPNPScopeGuard where
  no_turing_machine_model_declared := True
  no_np_complete_reduction_declared := True
  no_classical_PneqNP_claim := True

/-- The local P/NP node is architecture-local. -/
theorem localPNP_is_architecture_local :
    localPNP_scopeGuard.no_turing_machine_model_declared ∧
    localPNP_scopeGuard.no_np_complete_reduction_declared ∧
    localPNP_scopeGuard.no_classical_PneqNP_claim := by
  exact ⟨trivial, trivial, trivial⟩

/-#############################################################################
  §8. Compact final status theorem
#############################################################################-/

/--
The complete strict local P/NP status package for one Step00 local search problem.
-/
structure LocalPNPStatus
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where
  collision_principle : FiniteKeyCollisionPrinciple P.family
  semantic_interface : SemanticCollisionInterface P
  twin_detector : TwinDetectorBridge P
  scope_guard : LocalPNPScopeGuard

/-- The P-side: every given genealogy certificate verifies easily. -/
theorem status_verificationEasy_always
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (_S : LocalPNPStatus P)
    (i : P.family.Index) :
    GenealogyCertificate.VerificationEasy (P.family.cert i) :=
  P.verificationEasy_for_family i

/-- The finite-key NP/search side: every finite key has a same-key collision. -/
theorem status_every_finiteKeyCompression_collides
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (S : LocalPNPStatus P)
    (C : FiniteKeyCompression P.family) :
    Nonempty (KeyCollision C) :=
  S.collision_principle C

/-- Local P-success is equivalent to the semantic collision-resolution node. -/
theorem status_localPSuccess_iff_semantic
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (S : LocalPNPStatus P) :
    LocalPSuccess P ↔
      S.semantic_interface.SemanticFlowLedgerCollisionResolves :=
  S.semantic_interface.localPSuccess_iff_semanticFlowLedgerCollisionResolves

/-- Local P-success detects a twin above the bridge horizon. -/
theorem status_localP_success_detects_twin
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (S : LocalPNPStatus P)
    (hSuccess : LocalPSuccess P) :
    S.twin_detector.TwinAbove S.twin_detector.M0 := by
  rcases hSuccess with ⟨pc⟩
  exact S.twin_detector.detects pc

/-- No twin above the bridge horizon forces local search incompressibility. -/
theorem status_twinBound_forces_localSearchIncompressible
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (S : LocalPNPStatus P)
    (hNoTwinAbove : ¬ S.twin_detector.TwinAbove S.twin_detector.M0) :
    LocalSearchIncompressible P :=
  twinBound_forces_localSearchIncompressible S.twin_detector hNoTwinAbove

/-- Final slogan theorem for the strict local node. -/
theorem localPNP_status_slogan
    {G : RankedForwardGraph} {P : Step00LocalSearchProblem G}
    (S : LocalPNPStatus P) :
    (∀ i : P.family.Index,
      GenealogyCertificate.VerificationEasy (P.family.cert i)) ∧
    (∀ C : FiniteKeyCompression P.family, Nonempty (KeyCollision C)) ∧
    (LocalPSuccess P ↔
      S.semantic_interface.SemanticFlowLedgerCollisionResolves) ∧
    (LocalPSuccess P →
      S.twin_detector.TwinAbove S.twin_detector.M0) ∧
    localPNP_scopeGuard.no_classical_PneqNP_claim := by
  constructor
  · intro i
    exact status_verificationEasy_always S i
  · constructor
    · intro C
      exact status_every_finiteKeyCompression_collides S C
    · constructor
      · exact status_localPSuccess_iff_semantic S
      · constructor
        · intro hSuccess
          exact status_localP_success_detects_twin S hSuccess
        · trivial

end LocalPNP

/-! Конкретная инстанциация из объектов репо + машинная честность -/

namespace LocalPNP
namespace Concrete

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.LabelledFanIn

/-- Конкретный ранжированный граф: САМ Step00-граф репо. -/
def concreteGraph (A M0 : ℕ) : RankedForwardGraph where
  State := State
  Step := RealStep A M0
  lexRank := lexRank
  step_decreases := fun h => lexRank_strict_decrease_on_RealStep h

/-- Конвертация путей репо в пути локального узла. -/
theorem toLocalPathN {A M0 : ℕ} :
    ∀ {n : ℕ} {X Y : State},
      EuclidsPath.LabelledFanIn.PathN (RealStep A M0) n X Y →
      PathN (concreteGraph A M0) X Y n := by
  intro n
  induction n with
  | zero =>
      intro X Y h
      have hXY : X = Y := h
      subst hXY
      exact PathN.nil (G := concreteGraph A M0) X
  | succ k ih =>
      intro X Y h
      obtain ⟨Z, hXZ, hZY⟩ := h
      exact PathN.cons hXZ (ih hZY)

/-- Сертификат конкретной генеалогии. -/
def concreteCertificate {A M0 : ℕ} (F : ExtendedProperGeneratedFlow A M0) :
    GenealogyCertificate (concreteGraph A M0) where
  start := State.center F.start
  finish := F.terminal
  len := F.steps
  path := toLocalPathN (properPath_to_realPath F.properPath)

/-- Инъективность: данные-поля флоу восстановимы из сертификата,
    Prop-поля — proof irrelevance. -/
theorem concreteCertificate_injective {A M0 : ℕ} :
    Function.Injective (concreteCertificate (A := A) (M0 := M0)) := by
  intro F G h
  have h1 : State.center F.start = State.center G.start :=
    congrArg GenealogyCertificate.start h
  have h2 : F.terminal = G.terminal := congrArg GenealogyCertificate.finish h
  have h3 : F.steps = G.steps := congrArg GenealogyCertificate.len h
  have h1' : F.start = G.start := by injection h1
  cases F; cases G
  dsimp at h1' h2 h3
  subst h1'; subst h2; subst h3
  rfl

/-- Конкретная семья генеалогий. -/
def concreteFamily (A M0 : ℕ) : GenealogyFamily (concreteGraph A M0) where
  Index := ExtendedProperGeneratedFlow A M0
  cert := concreteCertificate
  distinct_cert := concreteCertificate_injective

/-- Конкретная задача поиска: резолюция = альтернатива репо (цикл ∨ оплата). -/
def concreteProblem (A M0 : ℕ) : Step00LocalSearchProblem (concreteGraph A M0) where
  family := concreteFamily A M0
  CollisionResolution := fun _ _ => ExtendedFlowResolutionAlternative A M0

/-- Семантический интерфейс: локальный P-успех ⟺ ∃ резолвящая проекция репо. -/
noncomputable def concreteSemanticInterface (A M0 : ℕ) :
    SemanticCollisionInterface (concreteProblem A M0) where
  SemanticFlowLedgerCollisionResolves :=
    ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj
  poly_to_semantic := fun S =>
    ⟨{ Key := S.compression.Key
       finiteKey := @Finite.of_fintype _ S.compression.finite_key
       keyFlow := S.compression.keyOf },
     fun _ _ hne _ _ hkey => S.resolves hne hkey⟩
  semantic_to_poly := fun h =>
    { compression :=
        { Key := h.choose.Key
          finite_key := @Fintype.ofFinite _ h.choose.finiteKey
          keyOf := h.choose.keyFlow }
      resolves := fun {i j} hne hkey =>
        h.choose_spec i j hne
          (extendedFlow_admissible i) (extendedFlow_admissible j) hkey }

/-- Конкретный twin-детектор: семантика ⟹ twin выше M0 (twin_above_of_resolves). -/
noncomputable def concreteTwinDetector (A M0 : ℕ) :
    TwinDetectorBridge (concreteProblem A M0) :=
  (concreteSemanticInterface A M0).semanticTwinDetector M0
    (fun m0 => ∃ m : ℕ, m0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m)
    (fun h => by
      obtain ⟨proj, hres⟩ := h
      exact twin_above_of_resolves proj hres)

/-- **БЕЗУСЛОВНЫЙ collision principle при A ≤ 4** (5-адическая цепь). -/
theorem concrete_collisionPrinciple_smallScale {A : ℕ} (hA : A ≤ 4) :
    FiniteKeyCollisionPrinciple (concreteFamily A 1) := by
  intro C
  classical
  obtain ⟨k₁, k₂, hne, hkey⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k => C.keyOf (fiveAdicChainFlow hA k))
  exact ⟨⟨fiveAdicChainFlow hA k₁, fiveAdicChainFlow hA k₂,
    fun h => hne (fiveAdicChainFlow_injective hA h), hkey⟩⟩

/-- **БЕЗУСЛОВНАЯ локальная несжимаемость при A ≤ 4.** -/
theorem concrete_localSearchIncompressible_smallScale {A : ℕ} (hA : A ≤ 4) :
    LocalSearchIncompressible (concreteProblem A 1) := by
  rintro ⟨S⟩
  obtain ⟨K⟩ := concrete_collisionPrinciple_smallScale hA S.compression
  exact no_extendedFlowResolutionAlternative A 1
    (S.resolves K.distinct K.same_key)

/-- **ПОЛНЫЙ конкретный статус-пакет при A ≤ 4** — все четыре компоненты
    инстанциированы из объектов репо (collision principle безусловен). -/
noncomputable def concreteLocalPNPStatus_smallScale {A : ℕ} (hA : A ≤ 4) :
    LocalPNPStatus (concreteProblem A 1) where
  collision_principle := concrete_collisionPrinciple_smallScale hA
  semantic_interface := concreteSemanticInterface A 1
  twin_detector := concreteTwinDetector A 1
  scope_guard := localPNP_scopeGuard

end Concrete
end LocalPNP
end EuclidsPath
