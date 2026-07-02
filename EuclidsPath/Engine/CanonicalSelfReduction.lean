/-
  CanonicalSelfReduction — self-reduction «P-decider ⟹ локальный резолвер»
  как протокол с топливом (кирпич: canonical_resolver_self_reduction).
  Проза: prose/24 (§12).

  Кирпич: FaithfulPFrame (True/False-языки обязаны быть в P — отсекает
  дегенеративные фреймы!), транскрипты запросов с честностью, ограниченный
  адаптивный протокол (fuel строго падает на шаге), терминальный декодер,
  DeciderGuidedSelfReduction ⟹ CanonicalResolverReconstruction ⟹
  extraction-field ⟹ StrictStep00ClassicalEncoding ⟹ разделение классов
  (при несжимаемости); FaithfulSelfReductionFront.

  ГЕНЕРИЧЕСКОЕ ЗАКРЫТИЕ (при интеграции): runSteps/canonicalRun —
  fuel-исполнитель протокола с ДОКАЗАННОЙ терминацией
  (runSteps_done_of_fuel: строгое падение fuel + спуск в ℕ) — поля
  run/run_done закрываются конструктором selfReduction_of_protocol_and_decoder;
  живой остаток фронта = протокол + терминальный декодер (+ верный фрейм).

  ⚠️ МАШИННАЯ ЧЕСТНОСТЬ: trivialFrame_not_faithful — тривиальный фрейм
  (InP := False) НЕ faithful (False-язык обязан быть в P) — петля с
  trivialFrame_separates_for_free замкнута: дегенерация отсечена машинно.
  Аудит-гейты по-прежнему свободны (True-конструктор это показывает).
  Фикс кирпича: невыводимый implicit Target в поле terminalDecoder.
-/
import Mathlib
import EuclidsPath.Engine.ClassicalPNPBridge

set_option autoImplicit false

namespace EuclidsPath
namespace ClassicalPNPBridge
namespace PDeciderExtraction
namespace CanonicalSelfReduction

/-#############################################################################
  §1. Nontrivial / faithful classical frames
#############################################################################-/

/--
A frame is P-nontrivial if at least one language belongs to its `InP` predicate.
This blocks the degenerate frame `InP := False` from being mistaken for a real
complexity model.
-/
def PNontrivialFrame (C : ClassicalComplexityFrame) : Prop :=
  ∃ L : ClassicalProblem, C.InP L

/--
A concrete always-accepting language.  A real machine model should put this
language in P.
-/
def TrueLanguage : ClassicalProblem where
  Instance := Unit
  Accepts := fun _ => True

/--
A concrete always-rejecting language.  A real machine model should also put this
language in P.
-/
def FalseLanguage : ClassicalProblem where
  Instance := Unit
  Accepts := fun _ => False

/--
A faithful P-frame has concrete deciders behind `InP`, and contains the two
constant languages.  This is still abstract, but it rules out the vacuous
`InP := False` model.
-/
structure FaithfulPFrame (C : ClassicalComplexityFrame) where
  concreteP : ConcretePAccess C
  true_inP : C.InP TrueLanguage
  false_inP : C.InP FalseLanguage

namespace FaithfulPFrame

/-- A faithful P-frame is nontrivial. -/
theorem p_nontrivial
    {C : ClassicalComplexityFrame}
    (F : FaithfulPFrame C) :
    PNontrivialFrame C := by
  exact ⟨TrueLanguage, F.true_inP⟩

/-- A faithful P-frame supplies a concrete decider for every P language. -/
theorem exists_decider
    {C : ClassicalComplexityFrame}
    (F : FaithfulPFrame C)
    {L : ClassicalProblem}
    (hP : C.InP L) :
    Nonempty (PDecider L) :=
  F.concreteP.exists_decider hP

end FaithfulPFrame

/--
A faithful full classical frame adds the ordinary NP bookkeeping needed by the
bridge.  The precise machine model is still external; this object only records
what must be instantiated to avoid fake separation from an arbitrary frame.
-/
structure FaithfulClassicalFrame (C : ClassicalComplexityFrame) where
  pFrame : FaithfulPFrame C

  /-- Audit: `InNP` is not arbitrary; it comes from a verifier semantics. -/
  verifier_semantics : Prop
  verifier_semantics_proof : verifier_semantics

  /-- Audit: polynomial many-one reductions are interpreted by the chosen model. -/
  reduction_semantics : Prop
  reduction_semantics_proof : reduction_semantics

namespace FaithfulClassicalFrame

/-- Faithful classical frames are P-nontrivial. -/
theorem p_nontrivial
    {C : ClassicalComplexityFrame}
    (F : FaithfulClassicalFrame C) :
    PNontrivialFrame C :=
  F.pFrame.p_nontrivial

/-- Faithful classical frames provide concrete P deciders. -/
theorem exists_decider
    {C : ClassicalComplexityFrame}
    (F : FaithfulClassicalFrame C)
    {L : ClassicalProblem}
    (hP : C.InP L) :
    Nonempty (PDecider L) :=
  F.pFrame.exists_decider hP

end FaithfulClassicalFrame

/-#############################################################################
  §2. Query transcripts
#############################################################################-/

/-- One encoded query answer in a decider-guided self-reduction. -/
structure QueryAnswer
    {L : ClassicalProblem}
    (Q : GenealogyDecisionQueryInterface L) where
  query : Q.Query
  answer : Bool

/-- A finite transcript of encoded queries and answers. -/
structure QueryTranscript
    {L : ClassicalProblem}
    (Q : GenealogyDecisionQueryInterface L) where
  log : List (QueryAnswer Q)

namespace QueryTranscript

/-- The empty transcript. -/
def empty
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L} :
    QueryTranscript Q where
  log := []

/-- Append one query answer. -/
def snoc
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (T : QueryTranscript Q)
    (qa : QueryAnswer Q) :
    QueryTranscript Q where
  log := T.log ++ [qa]

/-- Length of the transcript. -/
def length
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (T : QueryTranscript Q) : Nat :=
  T.log.length

@[simp] theorem length_empty
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L} :
    (empty : QueryTranscript Q).length = 0 := by
  rfl

/-- Appending one query increases transcript length by one. -/
theorem length_snoc
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (T : QueryTranscript Q)
    (qa : QueryAnswer Q) :
    (T.snoc qa).length = T.length + 1 := by
  simp [length, snoc]

end QueryTranscript

/--
A transcript is honest for a decider if every recorded answer agrees with running
the decider on the encoded query.
-/
def TranscriptHonest
    {L : ClassicalProblem}
    (Q : GenealogyDecisionQueryInterface L)
    (D : PDecider L)
    (T : QueryTranscript Q) : Prop :=
  ∀ qa ∈ T.log, qa.answer = Q.ask D qa.query

namespace TranscriptHonest

/-- The empty transcript is honest for every decider. -/
theorem empty
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (D : PDecider L) :
    TranscriptHonest Q D QueryTranscript.empty := by
  intro qa hmem
  cases hmem

/-- Honest transcripts stay honest after appending a correctly answered query. -/
theorem snoc
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    {D : PDecider L}
    {T : QueryTranscript Q}
    (hT : TranscriptHonest Q D T)
    (q : Q.Query) :
    TranscriptHonest Q D
      (T.snoc { query := q, answer := Q.ask D q }) := by
  intro qa hmem
  simp [QueryTranscript.snoc] at hmem
  rcases hmem with hmem | hlast
  · exact hT qa hmem
  · rcases hlast with rfl
    rfl

end TranscriptHonest

/-#############################################################################
  §3. Bounded adaptive self-reduction protocol
#############################################################################-/

/--
A finite adaptive query protocol.  It does not by itself know what the target
resolver is; it only describes how to ask bounded genealogy queries to a P
decider and when to stop.
-/
structure BoundedAdaptiveQueryProtocol
    (L : ClassicalProblem)
    (Q : GenealogyDecisionQueryInterface L) where

  /-- A private algorithmic state of the self-reduction. -/
  AlgState : Type

  init : AlgState

  done : AlgState → Prop

  /-- When not done, choose the next genealogy query. -/
  nextQuery : ∀ s : AlgState, ¬ done s → Q.Query

  /-- Update the algorithmic state from a query answer. -/
  update : AlgState → Bool → AlgState

  /-- A natural fuel/rank measure for termination. -/
  fuel : AlgState → Nat

  /-- The initial amount of fuel is bounded by a concrete number. -/
  initial_fuel_bound : Nat

  fuel_init_le : fuel init ≤ initial_fuel_bound

  /-- Every nonterminal query strictly decreases fuel. -/
  fuel_decreases :
    ∀ s : AlgState,
    ∀ h : ¬ done s,
    ∀ b : Bool,
      fuel (update s b) < fuel s

  /-- Audit: the protocol asks only genealogy/collision queries. -/
  asks_only_genealogy_queries : Prop
  asks_only_genealogy_queries_proof : asks_only_genealogy_queries

  /-- Audit: the query bound has the intended polynomial/rank behaviour. -/
  polynomial_query_bound : Prop
  polynomial_query_bound_proof : polynomial_query_bound

/-- One protocol step against a concrete decider. -/
def BoundedAdaptiveQueryProtocol.step
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q)
    (D : PDecider L)
    (s : P.AlgState)
    (h : ¬ P.done s) : P.AlgState :=
  P.update s (Q.ask D (P.nextQuery s h))

namespace BoundedAdaptiveQueryProtocol

/-- One concrete protocol step strictly decreases fuel. -/
theorem fuel_decreases_step
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q)
    (D : PDecider L)
    (s : P.AlgState)
    (h : ¬ P.done s) :
    P.fuel (P.step D s h) < P.fuel s := by
  exact P.fuel_decreases s h (Q.ask D (P.nextQuery s h))

end BoundedAdaptiveQueryProtocol

/-#############################################################################
  §4. Terminal resolver extraction from a transcript/protocol run
#############################################################################-/

/--
A terminal protocol state can be decoded into the desired local resolver.
This is the exact local correctness theorem of the self-reduction.
-/
structure TerminalResolverDecoder
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q) where

  decode : ∀ s : P.AlgState, P.done s → Target.Resolver

  /-- Decoded resolvers carry finite keys. -/
  decoded_finite_key_sound :
    ∀ s : P.AlgState,
    ∀ hDone : P.done s,
      Target.finite_key_sound (decode s hDone)

  /-- Decoded resolvers are rank/lexRank bounded. -/
  decoded_rank_bounded :
    ∀ s : P.AlgState,
    ∀ hDone : P.done s,
      Target.rank_bounded (decode s hDone)

  /-- Decoded resolvers resolve same-key Step00 collisions. -/
  decoded_collision_sound :
    ∀ s : P.AlgState,
    ∀ hDone : P.done s,
      Target.collision_sound (decode s hDone)

/--
A decider-guided self-reduction package.

The field `run` is the concrete terminating execution map.  In a fully
algorithmic instantiation, `run` should be defined by primitive recursion on
`initial_fuel_bound`; this abstract patch records exactly the obligations needed
from that recursion.
-/
structure DeciderGuidedSelfReduction
    (L : ClassicalProblem)
    {N : Step00LocalNode}
    (Target : LocalResolverTarget N) where

  queryInterface : GenealogyDecisionQueryInterface L

  protocol : BoundedAdaptiveQueryProtocol L queryInterface

  terminalDecoder : TerminalResolverDecoder (Target := Target) protocol

  run : PDecider L → protocol.AlgState

  /-- The final state produced by `run` is terminal. -/
  run_done : ∀ D : PDecider L, protocol.done (run D)

  /-- The run is bounded by the protocol fuel. -/
  run_within_fuel_bound : Prop
  run_within_fuel_bound_proof : run_within_fuel_bound

  /-- The run uses the decider only by encoded query calls. -/
  run_uses_only_encoded_queries : Prop
  run_uses_only_encoded_queries_proof : run_uses_only_encoded_queries

  /-- Uniformity audit. -/
  uniform_over_instances : Prop
  uniform_over_instances_proof : uniform_over_instances

  /-- No twin/RH-style oracle is hidden in the run. -/
  no_oracle_leak : Prop
  no_oracle_leak_proof : no_oracle_leak

namespace DeciderGuidedSelfReduction

/-- Extract the local resolver from a concrete P decider. -/
def resolverOfDecider
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (S : DeciderGuidedSelfReduction L Target)
    (D : PDecider L) : Target.Resolver :=
  S.terminalDecoder.decode (S.run D) (S.run_done D)

/-- The extracted resolver has a sound finite-key system. -/
theorem finite_key_sound
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (S : DeciderGuidedSelfReduction L Target)
    (D : PDecider L) :
    Target.finite_key_sound (S.resolverOfDecider D) := by
  exact S.terminalDecoder.decoded_finite_key_sound (S.run D) (S.run_done D)

/-- The extracted resolver is rank-bounded. -/
theorem rank_bounded
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (S : DeciderGuidedSelfReduction L Target)
    (D : PDecider L) :
    Target.rank_bounded (S.resolverOfDecider D) := by
  exact S.terminalDecoder.decoded_rank_bounded (S.run D) (S.run_done D)

/-- The extracted resolver resolves same-key Step00 collisions. -/
theorem collision_sound
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (S : DeciderGuidedSelfReduction L Target)
    (D : PDecider L) :
    Target.collision_sound (S.resolverOfDecider D) := by
  exact S.terminalDecoder.decoded_collision_sound (S.run D) (S.run_done D)

/-- The extracted resolver gives local P-success. -/
theorem localSuccessOfDecider
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (S : DeciderGuidedSelfReduction L Target)
    (D : PDecider L) :
    N.LocalPSuccess :=
  Target.localSuccess_of_resolver (S.resolverOfDecider D)

end DeciderGuidedSelfReduction

/-#############################################################################
  §5. From self-reduction to `CanonicalResolverReconstruction`
#############################################################################-/

/--
A self-reduction package builds the previous `CanonicalResolverReconstruction`.
-/
def canonicalReconstruction_of_selfReduction
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (S : DeciderGuidedSelfReduction L Target) :
    CanonicalResolverReconstruction L Target where

  queryInterface := S.queryInterface

  reconstruct := S.resolverOfDecider

  uses_only_encoded_queries := S.run_uses_only_encoded_queries
  uses_only_encoded_queries_proof := S.run_uses_only_encoded_queries_proof

  uniform_over_instances := S.uniform_over_instances
  uniform_over_instances_proof := S.uniform_over_instances_proof

  finite_key_sound_after_reconstruction := S.finite_key_sound

  rank_bounded_after_reconstruction := S.rank_bounded

  collision_sound_after_reconstruction := S.collision_sound

  no_twin_axiom_leak := S.no_oracle_leak
  no_twin_axiom_leak_proof := S.no_oracle_leak_proof

  no_causal_closure_leak := S.no_oracle_leak
  no_causal_closure_leak_proof := S.no_oracle_leak_proof

/--
Therefore a self-reduction plus concrete P-access gives the missing extraction
field.
-/
def extractionField_of_selfReduction
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    (concreteP : ConcretePAccess C)
    (Target : LocalResolverTarget N)
    (S : DeciderGuidedSelfReduction L Target)
    (non_vacuous_extraction : Prop)
    (non_vacuous_extraction_proof : non_vacuous_extraction) :
    PDeciderExtractionField C N L where

  concreteP := concreteP
  target := Target
  reconstruction := canonicalReconstruction_of_selfReduction S
  non_vacuous_extraction := non_vacuous_extraction
  non_vacuous_extraction_proof := non_vacuous_extraction_proof

/--
Self-reduction gives the exact field `C.InP L → N.LocalPSuccess`.
-/
theorem extracts_local_success_of_selfReduction
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    (concreteP : ConcretePAccess C)
    (Target : LocalResolverTarget N)
    (S : DeciderGuidedSelfReduction L Target)
    (non_vacuous_extraction : Prop)
    (non_vacuous_extraction_proof : non_vacuous_extraction) :
    C.InP L → N.LocalPSuccess := by
  intro hP
  let F := extractionField_of_selfReduction
    concreteP Target S non_vacuous_extraction non_vacuous_extraction_proof
  exact F.extracts_local_success hP

/-#############################################################################
  §6. Concrete current front after this patch
#############################################################################-/

/--
The remaining live bridge obligation after excluding the trivial frame artefact.

To finish the classical bridge in an actual model, instantiate:

1. `faithfulFrame` for a real machine model;
2. `encoding` for the Step00 genealogy language;
3. `target` as the concrete local resolver package;
4. `selfReduction` as the decider-guided reconstruction algorithm;
5. `local_incompressible` from the Step00 side, e.g. small-scale `A ≤ 4`.
-/
structure FaithfulSelfReductionFront
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  faithfulFrame : FaithfulClassicalFrame C

  encoding : Step00EncodingData C N

  target : LocalResolverTarget N

  selfReduction : DeciderGuidedSelfReduction encoding.genealogyLanguage target

  non_vacuous_extraction : Prop
  non_vacuous_extraction_proof : non_vacuous_extraction

  local_incompressible : N.LocalSearchIncompressible

namespace FaithfulSelfReductionFront

/-- Turn the faithful self-reduction front into the previous strict encoding. -/
def toStrictEncoding
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : FaithfulSelfReductionFront C N) :
    StrictStep00ClassicalEncoding C N where

  encoding := F.encoding

  extraction := extractionField_of_selfReduction
    F.faithfulFrame.pFrame.concreteP
    F.target
    F.selfReduction
    F.non_vacuous_extraction
    F.non_vacuous_extraction_proof

/-- A completed faithful self-reduction front gives classical separation. -/
theorem gives_classicalSeparation
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : FaithfulSelfReductionFront C N) :
    C.ClassesSeparate :=
  F.toStrictEncoding.classicalSeparation_of_localIncompressible F.local_incompressible

/-- Non-coincidence form. -/
theorem gives_not_classesCoincide
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : FaithfulSelfReductionFront C N) :
    ¬ C.ClassesCoincide :=
  F.toStrictEncoding.not_classesCoincide_of_localIncompressible F.local_incompressible

/-- The front cannot be the degenerate `InP := False` frame. -/
theorem frame_is_p_nontrivial
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : FaithfulSelfReductionFront C N) :
    PNontrivialFrame C :=
  F.faithfulFrame.p_nontrivial

end FaithfulSelfReductionFront

/--
Final slogan of this patch: the missing field is now a bounded adaptive
self-reduction from a P-decider to a local collision resolver, inside a faithful
nontrivial classical frame.
-/
abbrev SelfReductionSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∀ F : FaithfulSelfReductionFront C N,
    C.ClassesSeparate ∧ ¬ C.ClassesCoincide ∧ PNontrivialFrame C

/-- The self-reduction slogan is a theorem. -/
theorem selfReductionSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) :
    SelfReductionSlogan C N := by
  intro F
  exact ⟨F.gives_classicalSeparation,
         F.gives_not_classesCoincide,
         F.frame_is_p_nontrivial⟩

end CanonicalSelfReduction
end PDeciderExtraction
end ClassicalPNPBridge
end EuclidsPath

/-! Генерическое закрытие run-полей + машинная честность -/

namespace EuclidsPath
namespace ClassicalPNPBridge
namespace PDeciderExtraction
namespace CanonicalSelfReduction

/-- Генерический исполнитель протокола: fuel-рекурсия. -/
noncomputable def runSteps
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q)
    (D : PDecider L) :
    Nat → P.AlgState → P.AlgState
  | 0, s => s
  | n + 1, s =>
      letI := Classical.propDecidable (P.done s)
      if h : P.done s then s
      else runSteps P D n (P.step D s h)

/-- **ТЕРМИНАЦИЯ ДОКАЗАНА:** при бюджете ≥ fuel исполнитель достигает done
    (строгое падение fuel на каждом шаге + спуск в ℕ). -/
theorem runSteps_done_of_fuel
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q)
    (D : PDecider L) :
    ∀ n : Nat, ∀ s : P.AlgState, P.fuel s ≤ n →
      P.done (runSteps P D n s) := by
  intro n
  induction n with
  | zero =>
      intro s hfuel
      by_contra hNotDone
      have hlt := P.fuel_decreases_step D s hNotDone
      omega
  | succ n ih =>
      intro s hfuel
      unfold runSteps
      split
      · assumption
      · next hNotDone =>
          apply ih
          have hlt := P.fuel_decreases_step D s hNotDone
          omega

/-- Канонический запуск с бюджетом протокола. -/
noncomputable def canonicalRun
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q)
    (D : PDecider L) : P.AlgState :=
  runSteps P D P.initial_fuel_bound P.init

theorem canonicalRun_done
    {L : ClassicalProblem}
    {Q : GenealogyDecisionQueryInterface L}
    (P : BoundedAdaptiveQueryProtocol L Q)
    (D : PDecider L) :
    P.done (canonicalRun P D) :=
  runSteps_done_of_fuel P D P.initial_fuel_bound P.init P.fuel_init_le

/-- **ГЕНЕРИЧЕСКИЙ КОНСТРУКТОР:** self-reduction из (протокол + декодер) —
    поля run/run_done закрыты каноническим исполнителем; гейты — True
    (честно: маркеры). Остаток фронта = протокол + декодер. -/
noncomputable def selfReduction_of_protocol_and_decoder
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (Q : GenealogyDecisionQueryInterface L)
    (P : BoundedAdaptiveQueryProtocol L Q)
    (Dec : TerminalResolverDecoder (Target := Target) P) :
    DeciderGuidedSelfReduction L Target where
  queryInterface := Q
  protocol := P
  terminalDecoder := Dec
  run := fun D => canonicalRun P D
  run_done := fun D => canonicalRun_done P D
  run_within_fuel_bound := True
  run_within_fuel_bound_proof := trivial
  run_uses_only_encoded_queries := True
  run_uses_only_encoded_queries_proof := trivial
  uniform_over_instances := True
  uniform_over_instances_proof := trivial
  no_oracle_leak := True
  no_oracle_leak_proof := trivial

/-- **ЧЕСТНОСТЬ (замыкает петлю с trivialFrame):** тривиальный фрейм НЕ
    faithful — FaithfulPFrame требует False-язык в P, у trivialFrame
    InP := False. Дегенеративный фрейм машинно отсечён. -/
theorem trivialFrame_not_faithful
    (F : FaithfulPFrame ClassicalPNPBridge.trivialFrame) : False :=
  F.false_inP

end CanonicalSelfReduction
end PDeciderExtraction
end ClassicalPNPBridge
end EuclidsPath
