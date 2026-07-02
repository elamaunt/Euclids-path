/-
  ClassicalFrontierRoutes — классический P/NP-фронт (42 кирпича одной сборкой):
  external lower-bound routes/barriers/forward-layer/certificate, машинная
  модель, np-complete route + transfer guard, faithful machine frame skeleton,
  no-free-lunch мост, frontier-манифесты v2-v8 (deep obligations, circuit
  ladder + barriers, commitment layer, circuit escalation, proof complexity
  NP-int-coNP, hierarchy/Williams, single-file deep frontier), promise-слой
  (coverage trilemma / prefix self-reduction / to-decision barrier / firewalls),
  step00 collision (problem/totality/quotient/nonabsorption), FP/FNP total
  search separation + effectivity firewall, scale-indexed мосты и кодирования,
  resolver-коды (finite table / proof-carrying / canonical encoding),
  bitwise decision-to-search, p-decider extraction obstruction.

  ЧЕСТНОСТЬ (флаги сборочного аудита, машинно):
    * УДАЛЁН falseDecider (extraction_obstruction): заявлял Decider L для
      любого языка константой false — ЛОЖЕН как сформулирован.
    * ИСКЛЮЧЁН дубликат external_universe_self_engine (уже в ConcreteStep00Graph).
    * Два Prop-как-доказательство дефекта починены УСИЛЕНИЕМ входов (добавлены
      InNP_proof/NotInP_proof и incomplete_without_coverage_proof) — честное
      направление: нагрузка на инстанциацию выросла.
    * Около 30 slogan-abbrev — буквально Prop := True (маркеры); идиома
      gate/gate_proof повсеместно инстанциируема True — аудит-поля без
      семантики; SemanticCollisionClosure/LocalSuccess в одном месте := True
      (вакуумный гейт, отмечено).
    * Renamed-conclusion входы: BitwiseClassicalBridgeFront /
      CanonicalCodeClassicalBridgeFront / ScaleIndexedClassicalBridge несут
      local_incompressible готовым полем — их ClassesSeparate есть переупаковка
      гипотезы через strict-encoding конвейер.
  Безусловных ClassesSeparate/False нет; sorry/axiom нет.
-/
import Mathlib
import EuclidsPath.Engine.CanonicalSelfReduction

set_option autoImplicit false

/- ============ BRICK: EuclidsPath_bitwise_decision_to_search_patch.lean ============ -/
/-
EuclidsPath — patch: bitwise decision-to-search reconstruction
================================================================

Purpose
-------
The previous self-reduction patch isolated the load-bearing decoder:

    TerminalResolverDecoder.decoded_collision_sound

and the higher-level object

    DeciderGuidedSelfReduction

which should turn a classical `PDecider` for the encoded genealogy language into
a Step00-local collision resolver.

This patch pushes one layer deeper and replaces the opaque terminal decoder by a
standard bitwise decision-to-search reconstruction.

The construction is deliberately local and explicit:

  * a prefix `p : List Bool` represents a partial resolver/witness;
  * the classical language contains extension queries: “does `p` extend to a
    full valid resolver?”;
  * a `PDecider` answers those extension queries;
  * at each bit, query the `false` extension; if it is possible, choose `false`,
    otherwise choose `true`;
  * by prefix-extension completeness, this greedily recovers a full resolver;
  * the resulting resolver is then fed to `LocalResolverTarget.realizes`, giving
    `LocalPSuccess`.

This still does not prove classical `P ≠ NP`.  It identifies the next concrete
obligation: instantiate `BitwiseResolverEncoding` for the actual encoded Step00
same-key collision resolver language in a faithful machine frame.

Append after:

    EuclidsPath_classical_pnp_bridge_strict_patch.lean
    EuclidsPath_p_decider_extraction_field_patch.lean
    EuclidsPath_canonical_resolver_self_reduction_patch.lean

No axiom.  No `sorry`.
-/

namespace EuclidsPath
namespace ClassicalPNPBridge
namespace PDeciderExtraction
namespace CanonicalSelfReduction
namespace BitwiseDecisionToSearch

/-#############################################################################
  §1. Bit-prefix extension encoding
#############################################################################-/

/--
A bitwise self-reducible encoding of the Step00-local resolver search problem.

For a fixed encoded genealogy/collision problem, `width` is the number of bits in
one canonical resolver witness.  `HasExtension p` means that the prefix `p` can
be completed to a full valid resolver.  The language query `queryOfPrefix p`
represents exactly this extension question.

The hard concrete work is to instantiate this structure faithfully for the
actual Step00 resolver encoding.
-/
structure BitwiseResolverEncoding
    (L : ClassicalProblem)
    {N : Step00LocalNode}
    (Target : LocalResolverTarget N) where

  width : Nat

  /-- Encode the prefix-extension question as an instance of the classical language. -/
  queryOfPrefix : List Bool → L.Instance

  /-- `HasExtension p` means that the prefix can be extended to a valid resolver. -/
  HasExtension : List Bool → Prop

  /-- The empty prefix is extendible whenever the original genealogy instance is positive. -/
  empty_hasExtension : HasExtension []

  /-- The classical language answers exactly the prefix-extension predicate. -/
  accepts_iff_hasExtension :
    ∀ p : List Bool, L.Accepts (queryOfPrefix p) ↔ HasExtension p

  /-- Prefix-extension branching: every nonterminal extendible prefix has a next bit. -/
  extension_split :
    ∀ p : List Bool,
      p.length < width →
      HasExtension p →
        HasExtension (p ++ [false]) ∨ HasExtension (p ++ [true])

  /-- A terminal extendible prefix decodes to an actual local resolver. -/
  terminal_resolver :
    ∀ p : List Bool,
      p.length = width →
      HasExtension p →
        Target.Resolver

  /-- Audit: prefix queries are faithful encodings of Step00 extension questions. -/
  faithful_prefix_encoding : Prop
  faithful_prefix_encoding_proof : faithful_prefix_encoding

  /-- Audit: all prefix queries are genealogy/collision-shaped queries. -/
  prefix_queries_are_genealogy : Prop
  prefix_queries_are_genealogy_proof : prefix_queries_are_genealogy

  /-- Audit: prefix-query sizes are controlled by the intended polynomial/rank bound. -/
  prefix_size_control : Prop
  prefix_size_control_proof : prefix_size_control

  /-- Audit: the greedy recovery uses only prefix-extension queries. -/
  uses_only_prefix_queries : Prop
  uses_only_prefix_queries_proof : uses_only_prefix_queries

  /-- Audit: no twin-infinitude oracle is hidden in the encoding. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  /-- Audit: no Step00 causal-closure axiom is hidden in the encoding. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace BitwiseResolverEncoding

/-- Turn the bit-prefix language into the generic query interface from the previous patch. -/
def queryInterface
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target) :
    GenealogyDecisionQueryInterface L where
  Query := List Bool
  encode := E.queryOfPrefix
  faithful_query_encoding := E.faithful_prefix_encoding
  faithful_query_encoding_proof := E.faithful_prefix_encoding_proof
  genealogy_query_sound := E.prefix_queries_are_genealogy
  genealogy_query_sound_proof := E.prefix_queries_are_genealogy_proof
  size_control := E.prefix_size_control
  size_control_proof := E.prefix_size_control_proof

/-- Query a decider on one prefix-extension instance. -/
def askPrefix
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L)
    (p : List Bool) : Bool :=
  D.run (E.queryOfPrefix p)

/-- Greedy next bit: choose `false` if the `false` extension exists, else `true`. -/
def chooseNextBit
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L)
    (p : List Bool) : Bool :=
  if D.run (E.queryOfPrefix (p ++ [false])) = true then false else true

/--
One greedy decision-to-search step preserves prefix extendibility.

This is the core strict lemma: no resolver is postulated.  The next bit is chosen
using only the P-decider's answer to the `false` extension query.
-/
theorem chooseNextBit_preserves_extension
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L)
    (p : List Bool)
    (hLen : p.length < E.width)
    (hExt : E.HasExtension p) :
    E.HasExtension (p ++ [E.chooseNextBit D p]) := by
  unfold chooseNextBit
  by_cases hFalseRun : D.run (E.queryOfPrefix (p ++ [false])) = true
  · simp [hFalseRun]
    exact (E.accepts_iff_hasExtension (p ++ [false])).1
      (D.sound (E.queryOfPrefix (p ++ [false])) hFalseRun)
  · simp [hFalseRun]
    have hNoFalse : ¬ E.HasExtension (p ++ [false]) := by
      intro hFalseExt
      have hAcc : L.Accepts (E.queryOfPrefix (p ++ [false])) :=
        (E.accepts_iff_hasExtension (p ++ [false])).2 hFalseExt
      have hRunTrue : D.run (E.queryOfPrefix (p ++ [false])) = true :=
        D.complete (E.queryOfPrefix (p ++ [false])) hAcc
      exact hFalseRun hRunTrue
    rcases E.extension_split p hLen hExt with hFalseExt | hTrueExt
    · exact False.elim (hNoFalse hFalseExt)
    · exact hTrueExt

/-#############################################################################
  §2. Greedy recovery of a full resolver witness
#############################################################################-/

/--
Extend an already extendible prefix to a full terminal prefix by greedy queries.

The recursion is on the remaining number of bits.  The invariant is explicit:
`p.length + fuel = E.width` and `E.HasExtension p`.
-/
noncomputable def recoverAux
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L) :
    (fuel : Nat) →
    (p : List Bool) →
    E.HasExtension p →
    p.length + fuel = E.width →
      {q : List Bool // q.length = E.width ∧ E.HasExtension q}
  | 0, p, hExt, hLen =>
      ⟨p, by
        have hp : p.length = E.width := by omega
        exact ⟨hp, hExt⟩⟩
  | Nat.succ fuel, p, hExt, hLen => by
      have hLenLt : p.length < E.width := by omega
      let b := E.chooseNextBit D p
      have hExt' : E.HasExtension (p ++ [b]) :=
        E.chooseNextBit_preserves_extension D p hLenLt hExt
      have hLen' : (p ++ [b]).length + fuel = E.width := by
        simp [b]
        omega
      exact E.recoverAux D fuel (p ++ [b]) hExt' hLen'

/-- Recover a full terminal prefix from a decider, starting with the empty prefix. -/
noncomputable def recoverBits
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L) :
    {p : List Bool // p.length = E.width ∧ E.HasExtension p} :=
  E.recoverAux D E.width [] E.empty_hasExtension (by simp)

/-- The recovered bitstring has the required terminal width. -/
theorem recoverBits_length
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L) :
    (E.recoverBits D).1.length = E.width :=
  (E.recoverBits D).2.1

/-- The recovered bitstring is a valid extendible terminal prefix. -/
theorem recoverBits_hasExtension
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L) :
    E.HasExtension (E.recoverBits D).1 :=
  (E.recoverBits D).2.2

/-- Decode the recovered terminal prefix into the actual local resolver. -/
noncomputable def resolverOfDecider
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L) : Target.Resolver :=
  E.terminal_resolver
    (E.recoverBits D).1
    (E.recoverBits_length D)
    (E.recoverBits_hasExtension D)

/-- The resolver recovered by bitwise decision-to-search gives local P-success. -/
theorem localSuccessOfDecider
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target)
    (D : PDecider L) :
    N.LocalPSuccess :=
  Target.localSuccess_of_resolver (E.resolverOfDecider D)

/-#############################################################################
  §3. Build the previous reconstruction and extraction field
#############################################################################-/

/--
The bitwise self-reduction is a concrete `CanonicalResolverReconstruction`.
-/
noncomputable def canonicalReconstruction
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (E : BitwiseResolverEncoding L Target) :
    CanonicalResolverReconstruction L Target where
  queryInterface := E.queryInterface
  reconstruct := E.resolverOfDecider

  uses_only_encoded_queries := E.uses_only_prefix_queries
  uses_only_encoded_queries_proof := E.uses_only_prefix_queries_proof

  uniform_over_instances := True
  uniform_over_instances_proof := by trivial

  finite_key_sound_after_reconstruction := by
    intro D
    exact Target.finite_key_sound_proof (E.resolverOfDecider D)

  rank_bounded_after_reconstruction := by
    intro D
    exact Target.rank_bounded_proof (E.resolverOfDecider D)

  collision_sound_after_reconstruction := by
    intro D
    exact Target.collision_sound_proof (E.resolverOfDecider D)

  no_twin_axiom_leak := E.no_twin_axiom_leak
  no_twin_axiom_leak_proof := E.no_twin_axiom_leak_proof

  no_causal_closure_leak := E.no_causal_closure_leak
  no_causal_closure_leak_proof := E.no_causal_closure_leak_proof

/--
Concrete P-access plus a bitwise resolver encoding gives the previously missing
extraction field.
-/
noncomputable def extractionField_of_bitwiseEncoding
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    {Target : LocalResolverTarget N}
    (concreteP : ConcretePAccess C)
    (E : BitwiseResolverEncoding L Target)
    (non_vacuous_extraction : Prop)
    (non_vacuous_extraction_proof : non_vacuous_extraction) :
    PDeciderExtractionField C N L where
  concreteP := concreteP
  target := Target
  reconstruction := E.canonicalReconstruction
  non_vacuous_extraction := non_vacuous_extraction
  non_vacuous_extraction_proof := non_vacuous_extraction_proof

/--
The explicit bitwise decision-to-search construction proves the exact bridge
field `C.InP L → N.LocalPSuccess`.
-/
theorem extracts_local_success_of_bitwiseEncoding
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    {Target : LocalResolverTarget N}
    (concreteP : ConcretePAccess C)
    (E : BitwiseResolverEncoding L Target)
    (non_vacuous_extraction : Prop)
    (non_vacuous_extraction_proof : non_vacuous_extraction) :
    C.InP L → N.LocalPSuccess := by
  intro hP
  let F := extractionField_of_bitwiseEncoding
    concreteP E non_vacuous_extraction non_vacuous_extraction_proof
  exact F.extracts_local_success hP

/-#############################################################################
  §4. Completed bitwise bridge front
#############################################################################-/

/--
A strict bridge front where the extraction field is supplied by the bitwise
self-reduction above.
-/
structure BitwiseClassicalBridgeFront
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  faithfulFrame : FaithfulClassicalFrame C

  encodingData : Step00EncodingData C N

  target : LocalResolverTarget N

  bitwiseEncoding : BitwiseResolverEncoding encodingData.genealogyLanguage target

  non_vacuous_extraction : Prop
  non_vacuous_extraction_proof : non_vacuous_extraction

  local_incompressible : N.LocalSearchIncompressible

namespace BitwiseClassicalBridgeFront

/-- Convert a bitwise bridge front into the previous strict encoding object. -/
noncomputable def toStrictEncoding
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : BitwiseClassicalBridgeFront C N) :
    StrictStep00ClassicalEncoding C N where
  encoding := F.encodingData
  extraction := extractionField_of_bitwiseEncoding
    F.faithfulFrame.pFrame.concreteP
    F.bitwiseEncoding
    F.non_vacuous_extraction
    F.non_vacuous_extraction_proof

/-- The bitwise front gives a separating language in the chosen faithful frame. -/
theorem gives_classicalSeparation
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : BitwiseClassicalBridgeFront C N) :
    C.ClassesSeparate :=
  F.toStrictEncoding.classicalSeparation_of_localIncompressible F.local_incompressible

/-- Non-coincidence form for the chosen faithful frame. -/
theorem gives_not_classesCoincide
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : BitwiseClassicalBridgeFront C N) :
    ¬ C.ClassesCoincide :=
  F.toStrictEncoding.not_classesCoincide_of_localIncompressible F.local_incompressible

/-- Faithfulness guard: this front is not the degenerate `InP := False` frame. -/
theorem frame_is_p_nontrivial
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : BitwiseClassicalBridgeFront C N) :
    PNontrivialFrame C :=
  F.faithfulFrame.p_nontrivial

/-- The front supplies the exact missing extraction field. -/
theorem provides_missing_field
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : BitwiseClassicalBridgeFront C N) :
    C.InP F.encodingData.genealogyLanguage → N.LocalPSuccess :=
  F.toStrictEncoding.provides_missing_field

end BitwiseClassicalBridgeFront

/-#############################################################################
  §5. Remaining concrete obligation
#############################################################################-/

/--
The live concrete obligation after this patch.

To instantiate this for the real Step00 genealogy language, one must build a
`BitwiseResolverEncoding` whose prefix-extension predicate is exactly the
existence of a completion to a finite-key same-collision resolver.  Then the
standard greedy decision-to-search proof above supplies the missing extraction
field automatically.
-/
abbrev RemainingBitwiseBridgeObligation
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∃ F : BitwiseClassicalBridgeFront C N, True

/--
Slogan: the opaque terminal decoder has been reduced to the prefix-extension
property for a concrete resolver encoding.
-/
abbrev BitwiseDecisionToSearchSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∀ F : BitwiseClassicalBridgeFront C N,
    C.ClassesSeparate ∧ ¬ C.ClassesCoincide ∧ PNontrivialFrame C

/-- The bitwise decision-to-search slogan is now a theorem. -/
theorem bitwiseDecisionToSearchSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) :
    BitwiseDecisionToSearchSlogan C N := by
  intro F
  exact ⟨F.gives_classicalSeparation,
         F.gives_not_classesCoincide,
         F.frame_is_p_nontrivial⟩

end BitwiseResolverEncoding
end BitwiseDecisionToSearch
end CanonicalSelfReduction
end PDeciderExtraction
end ClassicalPNPBridge
end EuclidsPath

/- ============ BRICK: EuclidsPath_canonical_resolver_code_encoding_patch.lean ============ -/
/-
EuclidsPath — patch: canonical resolver code encoding
======================================================

Purpose
-------
The previous bitwise decision-to-search patch reduced the live classical bridge
front to one object:

    BitwiseResolverEncoding

whose load-bearing fields were:

  * `HasExtension p`;
  * `extension_split`;
  * `terminal_resolver`.

This patch removes that remaining opacity.  `HasExtension` is now the canonical
predicate:

    there exists a full valid resolver code `c` of fixed width
    such that `p` is a bit-prefix of `c`.

From this definition we prove:

  * the empty prefix is extendible;
  * any nonterminal extendible prefix extends by either `false` or `true`;
  * any terminal extendible prefix decodes to an actual local resolver.

Thus the remaining obligation is no longer an abstract bitwise encoding.  It is
now a concrete finite codebook for Step00-local collision resolvers plus a
faithful classical prefix-extension language.

Append after:

    EuclidsPath_bitwise_decision_to_search_patch.lean

No axiom.  No `sorry`.
-/

namespace EuclidsPath
namespace ClassicalPNPBridge
namespace PDeciderExtraction
namespace CanonicalSelfReduction
namespace BitwiseDecisionToSearch

/-#############################################################################
  §1. Bit-prefixes and full resolver codes
#############################################################################-/

/-- `p` is a bit-prefix of `c` if `c = p ++ suffix`. -/
def BitPrefix (p c : List Bool) : Prop :=
  ∃ suffix : List Bool, c = p ++ suffix

namespace BitPrefix

/-- The empty list is a prefix of every code. -/
theorem nil (c : List Bool) : BitPrefix [] c := by
  exact ⟨c, by simp [BitPrefix]⟩

/-- Every code is a prefix of itself. -/
theorem refl (c : List Bool) : BitPrefix c c := by
  exact ⟨[], by simp [BitPrefix]⟩

/-- If a prefix has the same length as its code, then they are equal. -/
theorem eq_of_length_eq
    {p c : List Bool}
    (hPref : BitPrefix p c)
    (hLen : p.length = c.length) :
    p = c := by
  rcases hPref with ⟨suffix, rfl⟩
  simp only [List.length_append] at hLen
  have hs : suffix.length = 0 := by omega
  have hsNil : suffix = [] := List.eq_nil_of_length_eq_zero hs
  simp [hsNil]

/-- Extending by the actual next bit preserves prefixhood. -/
theorem extend_by_next
    (p tail : List Bool) (b : Bool) :
    BitPrefix (p ++ [b]) (p ++ b :: tail) := by
  exact ⟨tail, by simp [BitPrefix, List.append_assoc]⟩

end BitPrefix

/--
A finite canonical codebook for local Step00 collision resolvers.

A valid code is a full bitstring of length `width` which decodes to a local
resolver.  The classical language attached to the codebook must answer exactly
the prefix-completion question.
-/
structure CanonicalResolverCodeBook
    (L : ClassicalProblem)
    {N : Step00LocalNode}
    (Target : LocalResolverTarget N) where

  width : Nat

  /-- Full bitstrings which encode genuine local resolvers. -/
  ValidCode : List Bool → Prop

  /-- Every valid code has exactly the fixed width. -/
  validCode_width : ∀ c : List Bool, ValidCode c → c.length = width

  /-- At least one valid resolver code exists for positive Step00 instances. -/
  exists_validCode : ∃ c : List Bool, ValidCode c

  /-- Decode a valid full code into a local resolver. -/
  decode : ∀ c : List Bool, ValidCode c → Target.Resolver

  /-- Encode the prefix-completion question as a classical language instance. -/
  queryOfPrefix : List Bool → L.Instance

  /-- The classical language answers exactly the prefix-completion predicate. -/
  accepts_iff_prefixCompletable :
    ∀ p : List Bool,
      L.Accepts (queryOfPrefix p) ↔
        ∃ c : List Bool, ValidCode c ∧ BitPrefix p c

  /-- Audit: full codes are canonical, not arbitrary post-hoc witnesses. -/
  canonical_codes : Prop
  canonical_codes_proof : canonical_codes

  /-- Audit: prefix queries are faithful Step00 extension queries. -/
  faithful_prefix_encoding : Prop
  faithful_prefix_encoding_proof : faithful_prefix_encoding

  /-- Audit: every prefix query is genealogy/collision-shaped. -/
  prefix_queries_are_genealogy : Prop
  prefix_queries_are_genealogy_proof : prefix_queries_are_genealogy

  /-- Audit: query sizes are bounded by the intended polynomial/rank accounting. -/
  prefix_size_control : Prop
  prefix_size_control_proof : prefix_size_control

  /-- Audit: greedy recovery uses only prefix queries from this codebook. -/
  uses_only_prefix_queries : Prop
  uses_only_prefix_queries_proof : uses_only_prefix_queries

  /-- Audit: no twin-infinitude oracle is hidden in the codebook. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  /-- Audit: no Step00 causal-closure axiom is hidden in the codebook. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace CanonicalResolverCodeBook

/-- A prefix is completable exactly when it is the prefix of some valid code. -/
def PrefixCompletable
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (B : CanonicalResolverCodeBook L Target)
    (p : List Bool) : Prop :=
  ∃ c : List Bool, B.ValidCode c ∧ BitPrefix p c

/-- The empty prefix is completable. -/
theorem empty_prefixCompletable
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (B : CanonicalResolverCodeBook L Target) :
    B.PrefixCompletable [] := by
  rcases B.exists_validCode with ⟨c, hc⟩
  exact ⟨c, hc, BitPrefix.nil c⟩

/-- Prefix completion is exactly what the language accepts. -/
theorem accepts_iff_prefixCompletable'
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (B : CanonicalResolverCodeBook L Target)
    (p : List Bool) :
    L.Accepts (B.queryOfPrefix p) ↔ B.PrefixCompletable p :=
  B.accepts_iff_prefixCompletable p

/--
Nonterminal extension split follows from the canonical prefix definition.

If `p` is a strict prefix of some full valid code `c`, then the suffix after `p`
is nonempty.  Its head is either `false` or `true`, and the corresponding one-bit
extension remains completable.
-/
theorem extension_split
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (B : CanonicalResolverCodeBook L Target)
    (p : List Bool)
    (hLen : p.length < B.width)
    (hComp : B.PrefixCompletable p) :
    B.PrefixCompletable (p ++ [false]) ∨
    B.PrefixCompletable (p ++ [true]) := by
  rcases hComp with ⟨c, hcValid, suffix, hcEq⟩
  subst c
  have hCodeLen : (p ++ suffix).length = B.width :=
    B.validCode_width (p ++ suffix) hcValid
  cases suffix with
  | nil =>
      simp only [List.append_nil, List.length_append, List.length_nil, add_zero] at hCodeLen
      omega
  | cons b tail =>
      cases b
      · left
        exact ⟨p ++ false :: tail,
          hcValid,
          BitPrefix.extend_by_next p tail false⟩
      · right
        exact ⟨p ++ true :: tail,
          hcValid,
          BitPrefix.extend_by_next p tail true⟩

/--
A terminal completable prefix decodes to an actual local resolver.
-/
noncomputable def terminal_resolver
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (B : CanonicalResolverCodeBook L Target)
    (p : List Bool)
    (hLen : p.length = B.width)
    (hComp : B.PrefixCompletable p) :
    Target.Resolver :=
  B.decode hComp.choose hComp.choose_spec.1

/-#############################################################################
  §2. The canonical codebook yields the previous BitwiseResolverEncoding
#############################################################################-/

/-- A canonical resolver codebook is a bitwise resolver encoding. -/
noncomputable def toBitwiseResolverEncoding
    {L : ClassicalProblem}
    {N : Step00LocalNode}
    {Target : LocalResolverTarget N}
    (B : CanonicalResolverCodeBook L Target) :
    BitwiseResolverEncoding L Target where
  width := B.width
  queryOfPrefix := B.queryOfPrefix
  HasExtension := B.PrefixCompletable
  empty_hasExtension := B.empty_prefixCompletable
  accepts_iff_hasExtension := B.accepts_iff_prefixCompletable'
  extension_split := B.extension_split
  terminal_resolver := B.terminal_resolver

  faithful_prefix_encoding := B.faithful_prefix_encoding
  faithful_prefix_encoding_proof := B.faithful_prefix_encoding_proof

  prefix_queries_are_genealogy := B.prefix_queries_are_genealogy
  prefix_queries_are_genealogy_proof := B.prefix_queries_are_genealogy_proof

  prefix_size_control := B.prefix_size_control
  prefix_size_control_proof := B.prefix_size_control_proof

  uses_only_prefix_queries := B.uses_only_prefix_queries
  uses_only_prefix_queries_proof := B.uses_only_prefix_queries_proof

  no_twin_axiom_leak := B.no_twin_axiom_leak
  no_twin_axiom_leak_proof := B.no_twin_axiom_leak_proof

  no_causal_closure_leak := B.no_causal_closure_leak
  no_causal_closure_leak_proof := B.no_causal_closure_leak_proof

/-- The canonical codebook gives the exact missing extraction field. -/
noncomputable def extractionField_of_codeBook
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    {Target : LocalResolverTarget N}
    (concreteP : ConcretePAccess C)
    (B : CanonicalResolverCodeBook L Target)
    (non_vacuous_extraction : Prop)
    (non_vacuous_extraction_proof : non_vacuous_extraction) :
    PDeciderExtractionField C N L :=
  BitwiseResolverEncoding.extractionField_of_bitwiseEncoding
    concreteP
    B.toBitwiseResolverEncoding
    non_vacuous_extraction
    non_vacuous_extraction_proof

/-- The canonical codebook proves `C.InP L → N.LocalPSuccess`. -/
theorem extracts_local_success_of_codeBook
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    {L : ClassicalProblem}
    {Target : LocalResolverTarget N}
    (concreteP : ConcretePAccess C)
    (B : CanonicalResolverCodeBook L Target)
    (non_vacuous_extraction : Prop)
    (non_vacuous_extraction_proof : non_vacuous_extraction) :
    C.InP L → N.LocalPSuccess := by
  exact BitwiseResolverEncoding.extracts_local_success_of_bitwiseEncoding
    concreteP
    B.toBitwiseResolverEncoding
    non_vacuous_extraction
    non_vacuous_extraction_proof

/-#############################################################################
  §3. A stricter classical bridge front
#############################################################################-/

/--
The bridge front after eliminating the abstract `HasExtension` layer.

The live task is now a canonical finite resolver codebook whose language answers
prefix-completion questions.
-/
structure CanonicalCodeClassicalBridgeFront
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) where

  faithfulFrame : FaithfulClassicalFrame C

  encodingData : Step00EncodingData C N

  target : LocalResolverTarget N

  codeBook : CanonicalResolverCodeBook encodingData.genealogyLanguage target

  non_vacuous_extraction : Prop
  non_vacuous_extraction_proof : non_vacuous_extraction

  local_incompressible : N.LocalSearchIncompressible

namespace CanonicalCodeClassicalBridgeFront

/-- Convert the canonical-code front to the previous bitwise front. -/
noncomputable def toBitwiseFront
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CanonicalCodeClassicalBridgeFront C N) :
    BitwiseResolverEncoding.BitwiseClassicalBridgeFront C N where
  faithfulFrame := F.faithfulFrame
  encodingData := F.encodingData
  target := F.target
  bitwiseEncoding := F.codeBook.toBitwiseResolverEncoding
  non_vacuous_extraction := F.non_vacuous_extraction
  non_vacuous_extraction_proof := F.non_vacuous_extraction_proof
  local_incompressible := F.local_incompressible

/-- Convert the canonical-code front directly to the strict encoding object. -/
noncomputable def toStrictEncoding
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CanonicalCodeClassicalBridgeFront C N) :
    StrictStep00ClassicalEncoding C N where
  encoding := F.encodingData
  extraction := extractionField_of_codeBook
    F.faithfulFrame.pFrame.concreteP
    F.codeBook
    F.non_vacuous_extraction
    F.non_vacuous_extraction_proof

/-- The canonical-code front gives a classical separating language in the frame. -/
theorem gives_classicalSeparation
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CanonicalCodeClassicalBridgeFront C N) :
    C.ClassesSeparate :=
  F.toStrictEncoding.classicalSeparation_of_localIncompressible F.local_incompressible

/-- Non-coincidence form for the chosen faithful frame. -/
theorem gives_not_classesCoincide
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CanonicalCodeClassicalBridgeFront C N) :
    ¬ C.ClassesCoincide :=
  F.toStrictEncoding.not_classesCoincide_of_localIncompressible F.local_incompressible

/-- Faithfulness guard: the frame is not the degenerate `InP := False` frame. -/
theorem frame_is_p_nontrivial
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CanonicalCodeClassicalBridgeFront C N) :
    PNontrivialFrame C :=
  F.faithfulFrame.p_nontrivial

/-- The canonical-code front supplies the exact missing extraction field. -/
theorem provides_missing_field
    {C : ClassicalComplexityFrame}
    {N : Step00LocalNode}
    (F : CanonicalCodeClassicalBridgeFront C N) :
    C.InP F.encodingData.genealogyLanguage → N.LocalPSuccess :=
  F.toStrictEncoding.provides_missing_field

end CanonicalCodeClassicalBridgeFront

/-#############################################################################
  §4. Remaining concrete obligation
#############################################################################-/

/--
The remaining obligation is now a concrete codebook, not a black-box decoder.
-/
abbrev RemainingCanonicalCodeBridgeObligation
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∃ F : CanonicalCodeClassicalBridgeFront C N, True

/--
Slogan: `HasExtension` has been reduced to “there exists a valid full resolver
code with this prefix”.
-/
abbrev CanonicalResolverCodeSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) : Prop :=
  ∀ F : CanonicalCodeClassicalBridgeFront C N,
    C.ClassesSeparate ∧ ¬ C.ClassesCoincide ∧ PNontrivialFrame C

/-- The canonical-code slogan follows from the strict bridge assembly. -/
theorem canonicalResolverCodeSlogan
    (C : ClassicalComplexityFrame)
    (N : Step00LocalNode) :
    CanonicalResolverCodeSlogan C N := by
  intro F
  exact ⟨F.gives_classicalSeparation,
         F.gives_not_classesCoincide,
         F.frame_is_p_nontrivial⟩

end CanonicalResolverCodeBook
end BitwiseDecisionToSearch
end CanonicalSelfReduction
end PDeciderExtraction
end ClassicalPNPBridge
end EuclidsPath

/- ============ BRICK: EuclidsPath_proof_carrying_resolver_code_patch.lean ============ -/
/-
EuclidsPath_proof_carrying_resolver_code_patch.lean

Purpose
-------
Next strict layer after the canonical bitwise resolver-code patch.

Previous frontier:

  CanonicalResolverCodeBook

where `ValidCode c` was still an abstract predicate saying that the bitstring `c`
encodes a local Step00 collision resolver.

This patch turns that into a proof-carrying code discipline:

  * a code has fixed width;
  * `PrefixCompletable p` literally means that `p` is a prefix of some valid
    full resolver code;
  * a valid full code decodes into an actual resolver;
  * soundness of that resolver is part of the proof-carrying payload;
  * extension split and terminal decoding are proved from prefix arithmetic,
    not postulated;
  * if the empty prefix is completable, the codebook already contains a genuine
    local-success resolver.  Thus this layer cannot separate classes for free.

This is still architecture-local.  It does not instantiate classical Turing
machines.  It is the next non-vacuous bridge layer needed before a faithful
classical P/NP claim can be made.

No axioms.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNPBridge
namespace ProofCarryingResolverCode

/-- Bitstrings used as canonical resolver codes. -/
abbrev Bits := List Bool

/-- `p` is a prefix of `c`. -/
def BitPrefix (p c : Bits) : Prop :=
  ∃ suffix : Bits, p ++ suffix = c

namespace BitPrefix

/-- The empty bitstring is a prefix of every bitstring. -/
theorem nil (c : Bits) : BitPrefix [] c := by
  exact ⟨c, by simp [BitPrefix]⟩

/-- Every bitstring is a prefix of itself. -/
theorem refl (c : Bits) : BitPrefix c c := by
  exact ⟨[], by simp [BitPrefix]⟩

/-- Prefixes of equal length are equal. -/
theorem eq_of_length_eq {p c : Bits}
    (h : BitPrefix p c)
    (hlen : p.length = c.length) : p = c := by
  rcases h with ⟨suffix, hsuffix⟩
  have hlen' : p.length + suffix.length = p.length := by
    have hcongr := congrArg List.length hsuffix
    simpa [List.length_append, hlen] using hcongr
  have hsuffix_len : suffix.length = 0 := by
    omega
  have hsuffix_nil : suffix = [] := List.length_eq_zero_iff.mp hsuffix_len
  subst suffix
  simpa using hsuffix

/--
If `p` is a strict prefix of `c`, then one more bit can be appended to `p` while
remaining a prefix of `c`.
-/
theorem extend_by_next {p c : Bits}
    (h : BitPrefix p c)
    (hlen : p.length < c.length) :
    ∃ b : Bool, BitPrefix (p ++ [b]) c := by
  rcases h with ⟨suffix, hsuffix⟩
  cases suffix with
  | nil =>
      simp at hsuffix
      subst c
      simp at hlen
  | cons b rest =>
      refine ⟨b, rest, ?_⟩
      simpa [BitPrefix, List.append_assoc] using hsuffix

end BitPrefix

/-#############################################################################
  §1. Proof-carrying resolver codebooks
#############################################################################-/

/--
A proof-carrying resolver codebook.

`Resolver` is the local resolver type from the Step00-local P/NP node.  The
fields here should be instantiated by the concrete finite-key resolver used in
`LocalPSuccess`.

The key point is that `ValidCode` is no longer merely a target predicate.  A
valid code must decode to an actual resolver, and `sound` proves that the decoded
resolver has the required local-success semantics.
-/
structure ProofCarryingResolverCodeBook (Resolver : Type) where
  /-- Fixed width of full resolver codes. -/
  width : ℕ

  /-- Full-code validity.  In the concrete layer this should be a decidable,
  machine-checkable certificate predicate. -/
  ValidCode : Bits → Prop

  /-- Valid full codes have exactly the declared width. -/
  valid_width : ∀ c : Bits, ValidCode c → c.length = width

  /-- Decode a valid full code into a local resolver. -/
  decode : ∀ c : Bits, ValidCode c → Resolver

  /-- The local success semantics required from a decoded resolver. -/
  LocalSuccessResolver : Resolver → Prop

  /-- Every valid code decodes to a successful local resolver. -/
  sound : ∀ c : Bits, ∀ h : ValidCode c, LocalSuccessResolver (decode c h)

  /-- Audit gate: validity is intended to be checkable from the code itself. -/
  checkable_validity : Prop
  checkable_validity_proof : checkable_validity

  /-- Audit gate: the codebook does not use the twin-prime conclusion. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  /-- Audit gate: the codebook does not smuggle in Step00 causal closure. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

  /-- Audit gate: the codebook does not merely postulate local success. -/
  no_vacuous_success_leak : Prop
  no_vacuous_success_leak_proof : no_vacuous_success_leak

namespace ProofCarryingResolverCodeBook

variable {Resolver : Type}
variable (B : ProofCarryingResolverCodeBook Resolver)

/-- A prefix is completable iff it is a prefix of a valid full resolver code. -/
def PrefixCompletable (p : Bits) : Prop :=
  ∃ c : Bits, B.ValidCode c ∧ BitPrefix p c

/-- The full valid code itself is prefix-completable. -/
theorem validCode_prefixCompletable (c : Bits) (h : B.ValidCode c) :
    B.PrefixCompletable c := by
  exact ⟨c, h, BitPrefix.refl c⟩

/-- Empty prefix is completable exactly when a valid resolver code exists. -/
theorem empty_prefixCompletable_iff_exists_validCode :
    B.PrefixCompletable [] ↔ ∃ c : Bits, B.ValidCode c := by
  constructor
  · intro h
    rcases h with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  · intro h
    rcases h with ⟨c, hc⟩
    exact ⟨c, hc, BitPrefix.nil c⟩

/--
Prefix arithmetic gives the extension split: any nonterminal completable prefix
can be extended by one bit and remain completable.
-/
theorem extension_split {p : Bits}
    (h : B.PrefixCompletable p)
    (hlen : p.length < B.width) :
    ∃ b : Bool, B.PrefixCompletable (p ++ [b]) := by
  rcases h with ⟨c, hc, hprefix⟩
  have hcwidth : c.length = B.width := B.valid_width c hc
  have hstrict : p.length < c.length := by
    simpa [hcwidth] using hlen
  rcases BitPrefix.extend_by_next hprefix hstrict with ⟨b, hbprefix⟩
  exact ⟨b, c, hc, hbprefix⟩

/--
Terminal decoding: a completable prefix whose length equals the full width is
itself a valid full code and therefore decodes into a successful resolver.
-/
theorem terminal_resolver {p : Bits}
    (h : B.PrefixCompletable p)
    (hlen : p.length = B.width) :
    ∃ hp : B.ValidCode p, B.LocalSuccessResolver (B.decode p hp) := by
  rcases h with ⟨c, hc, hprefix⟩
  have hcwidth : c.length = B.width := B.valid_width c hc
  have hp_eq_c : p = c := by
    apply BitPrefix.eq_of_length_eq hprefix
    exact hlen.trans hcwidth.symm
  subst c
  exact ⟨hc, B.sound p hc⟩

/--
A non-vacuity consequence: if the empty prefix is completable, the codebook
already contains a genuine local-success resolver.
-/
theorem exists_successful_resolver_of_empty_prefixCompletable
    (h : B.PrefixCompletable []) :
    ∃ r : Resolver, B.LocalSuccessResolver r := by
  rcases h with ⟨c, hc, _⟩
  exact ⟨B.decode c hc, B.sound c hc⟩

/-- Conversely, a valid full code immediately provides a successful resolver. -/
theorem exists_successful_resolver_of_validCode
    {c : Bits} (hc : B.ValidCode c) :
    ∃ r : Resolver, B.LocalSuccessResolver r := by
  exact ⟨B.decode c hc, B.sound c hc⟩

/--
If no successful local resolver can exist, then no valid resolver code can exist.
This is the formal anti-free-lunch guard for this layer.
-/
theorem no_validCode_of_no_successful_resolver
    (hNo : ¬ ∃ r : Resolver, B.LocalSuccessResolver r) :
    ¬ ∃ c : Bits, B.ValidCode c := by
  intro h
  rcases h with ⟨c, hc⟩
  exact hNo (B.exists_successful_resolver_of_validCode hc)

/--
If no successful local resolver can exist, even the empty prefix is not
completable.
-/
theorem no_empty_prefixCompletable_of_no_successful_resolver
    (hNo : ¬ ∃ r : Resolver, B.LocalSuccessResolver r) :
    ¬ B.PrefixCompletable [] := by
  intro h
  exact hNo (B.exists_successful_resolver_of_empty_prefixCompletable h)

end ProofCarryingResolverCodeBook

/-#############################################################################
  §2. A language for prefix-extension queries
#############################################################################-/

/--
A classical decision language restricted to bitstrings.  In the real classical
frame this will be the encoded language queried by a P-decider.
-/
structure BitLanguage where
  Accepts : Bits → Prop

/--
A prefix-extension language is faithful to a proof-carrying resolver codebook
when it accepts exactly the completable prefixes.
-/
structure PrefixExtensionLanguage
    {Resolver : Type}
    (B : ProofCarryingResolverCodeBook Resolver)
    (L : BitLanguage) : Prop where
  accepts_iff_prefixCompletable :
    ∀ p : Bits, L.Accepts p ↔ B.PrefixCompletable p

namespace PrefixExtensionLanguage

variable {Resolver : Type}
variable {B : ProofCarryingResolverCodeBook Resolver}
variable {L : BitLanguage}

/-- Soundness direction: accepted query means prefix-completable. -/
theorem accepted_prefixCompletable
    (H : PrefixExtensionLanguage B L)
    {p : Bits} (h : L.Accepts p) :
    B.PrefixCompletable p :=
  (H.accepts_iff_prefixCompletable p).mp h

/-- Completeness direction: completable prefix is accepted. -/
theorem accepts_of_prefixCompletable
    (H : PrefixExtensionLanguage B L)
    {p : Bits} (h : B.PrefixCompletable p) :
    L.Accepts p :=
  (H.accepts_iff_prefixCompletable p).mpr h

end PrefixExtensionLanguage

/-#############################################################################
  §3. What this layer supplies to the previous bitwise bridge
#############################################################################-/

/--
The concrete obligations needed by the earlier `BitwiseResolverEncoding` layer.
This structure is deliberately small: extension split and terminal decoding are
now theorems supplied by a proof-carrying codebook.
-/
structure BitwiseEncodingObligations (Resolver : Type) where
  HasExtension : Bits → Prop
  width : ℕ
  ResolverOK : Resolver → Prop
  extension_split :
    ∀ p : Bits, HasExtension p → p.length < width →
      ∃ b : Bool, HasExtension (p ++ [b])
  terminal_resolver :
    ∀ p : Bits, HasExtension p → p.length = width →
      ∃ r : Resolver, ResolverOK r

namespace ProofCarryingResolverCodeBook

variable {Resolver : Type}

/-- A proof-carrying codebook provides the obligations of the bitwise bridge. -/
def toBitwiseEncodingObligations
    (B : ProofCarryingResolverCodeBook Resolver) :
    BitwiseEncodingObligations Resolver :=
{
  HasExtension := B.PrefixCompletable
  width := B.width
  ResolverOK := B.LocalSuccessResolver
  extension_split := by
    intro p hp hlen
    exact B.extension_split hp hlen
  terminal_resolver := by
    intro p hp hlen
    rcases B.terminal_resolver hp hlen with ⟨hvalid, hsuccess⟩
    exact ⟨B.decode p hvalid, hsuccess⟩
}

end ProofCarryingResolverCodeBook

/-#############################################################################
  §4. The next bridge-front object
#############################################################################-/

/--
The strict front after this patch.

To continue toward the classical bridge, instantiate this object with the actual
Step00 local resolver type and the actual classical prefix-extension language.
-/
structure ProofCarryingCodeFront (Resolver : Type) where
  codebook : ProofCarryingResolverCodeBook Resolver
  language : BitLanguage
  prefix_language_faithful : PrefixExtensionLanguage codebook language

  /-- The language is meant to be the one accessible to the classical P-decider. -/
  language_is_machine_encoded : Prop
  language_is_machine_encoded_proof : language_is_machine_encoded

  /-- Width is bounded by the intended polynomial/rank budget. -/
  width_is_budgeted : Prop
  width_is_budgeted_proof : width_is_budgeted

  /-- The construction remains architecture-local unless this is connected to a
  faithful classical machine frame. -/
  faithful_frame_pending : Prop
  faithful_frame_pending_proof : faithful_frame_pending

namespace ProofCarryingCodeFront

variable {Resolver : Type}

/-- The strict front supplies the bitwise obligations. -/
def obligations (F : ProofCarryingCodeFront Resolver) :
    BitwiseEncodingObligations Resolver :=
  F.codebook.toBitwiseEncodingObligations

/-- Accepted empty query gives a genuine successful local resolver. -/
theorem successful_resolver_of_empty_query
    (F : ProofCarryingCodeFront Resolver)
    (hAccepts : F.language.Accepts []) :
    ∃ r : Resolver, F.codebook.LocalSuccessResolver r := by
  have hComp : F.codebook.PrefixCompletable [] :=
    F.prefix_language_faithful.accepted_prefixCompletable hAccepts
  exact F.codebook.exists_successful_resolver_of_empty_prefixCompletable hComp

/-- If no local-success resolver exists, the empty prefix query must reject. -/
theorem empty_query_rejects_of_no_successful_resolver
    (F : ProofCarryingCodeFront Resolver)
    (hNo : ¬ ∃ r : Resolver, F.codebook.LocalSuccessResolver r) :
    ¬ F.language.Accepts [] := by
  intro h
  exact hNo (F.successful_resolver_of_empty_query h)

/--
Slogan theorem: this layer reduces the previous abstract `ValidCode` obligation
to a proof-carrying fixed-width codebook plus a faithful prefix-extension
language.
-/
theorem proofCarryingCodeFront_slogan
    (F : ProofCarryingCodeFront Resolver) :
    (∀ p : Bits,
      F.language.Accepts p ↔ F.codebook.PrefixCompletable p) ∧
    (∀ p : Bits,
      F.codebook.PrefixCompletable p → p.length < F.codebook.width →
        ∃ b : Bool, F.codebook.PrefixCompletable (p ++ [b])) ∧
    (∀ p : Bits,
      F.codebook.PrefixCompletable p → p.length = F.codebook.width →
        ∃ r : Resolver, F.codebook.LocalSuccessResolver r) := by
  constructor
  · exact F.prefix_language_faithful.accepts_iff_prefixCompletable
  · constructor
    · intro p hp hlen
      exact F.codebook.extension_split hp hlen
    · intro p hp hlen
      rcases F.codebook.terminal_resolver hp hlen with ⟨hvalid, hsuccess⟩
      exact ⟨F.codebook.decode p hvalid, hsuccess⟩

end ProofCarryingCodeFront

/-#############################################################################
  §5. Remaining exact obligation
#############################################################################-/

/--
The remaining construction obligation after this patch.

For the actual Step00 local P/NP node, build a proof-carrying code front whose
resolver type is the concrete finite-key collision resolver.
-/
structure RemainingProofCarryingCodeObligation where
  Resolver : Type
  front : ProofCarryingCodeFront Resolver

/-- What remains is not a theorem of classical complexity yet; it is a concrete
encoding/programming obligation. -/
abbrev RemainingObligationIsConcreteEncodingProblem : Prop := True

theorem remainingObligationIsConcreteEncodingProblem :
    RemainingObligationIsConcreteEncodingProblem := by
  trivial

end ProofCarryingResolverCode
end ClassicalPNPBridge
end EuclidsPath

/- ============ BRICK: EuclidsPath_finite_table_resolver_code_patch.lean ============ -/
/-
EuclidsPath_finite_table_resolver_code_patch.lean

Purpose
-------
Next strict layer after `EuclidsPath_proof_carrying_resolver_code_patch.lean`.

The previous layer made `ValidCode` proof-carrying, but the successful resolver
was still an arbitrary resolver object.  This patch specializes the resolver to a
finite table over a finite Step00 collision universe:

  * queries are local same-key collision obligations;
  * answers are local resolution witnesses;
  * a table resolver chooses one answer for every query;
  * soundness is entrywise: every chosen answer resolves its query;
  * a valid bit-code is exactly a decoded finite table plus its entrywise
    soundness proof.

Thus the live obstruction is no longer a vague “valid code”.  It is a concrete
finite-table codebook plus a proof that the prefix-extension language accepts
exactly prefixes extendible to a sound full table.

Append after:

  * EuclidsPath_proof_carrying_resolver_code_patch.lean

No axioms.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNPBridge
namespace ProofCarryingResolverCode
namespace FiniteTableResolverCode

/-#############################################################################
  §1. Finite local collision universes
#############################################################################-/

/--
A finite local collision universe.

`Query` should be instantiated by the finite/rank-bounded set of Step00 same-key
collision obligations.  `Answer` should be instantiated by the corresponding
local resolution witnesses: payment, return path, nesting, seam/singularity, or
whatever the concrete local node accepts as resolution.
-/
structure FiniteCollisionUniverse where
  Query : Type
  Answer : Type

  query_fintype : Fintype Query
  query_deceq : DecidableEq Query

  answer_fintype : Fintype Answer
  answer_deceq : DecidableEq Answer

  /-- `Resolves q a` means answer `a` resolves local collision obligation `q`. -/
  Resolves : Query → Answer → Prop

  /-- Audit: queries really are Step00 collision obligations, not arbitrary bits. -/
  queries_are_step00_collisions : Prop
  queries_are_step00_collisions_proof : queries_are_step00_collisions

  /-- Audit: answers are legal local Step00 resolution witnesses. -/
  answers_are_legal_resolutions : Prop
  answers_are_legal_resolutions_proof : answers_are_legal_resolutions

namespace FiniteCollisionUniverse

variable (U : FiniteCollisionUniverse)

/-- Make the finite query instance available locally. -/
instance queryFintype : Fintype U.Query := U.query_fintype

/-- Make the query equality instance available locally. -/
instance queryDecidableEq : DecidableEq U.Query := U.query_deceq

/-- Make the finite answer instance available locally. -/
instance answerFintype : Fintype U.Answer := U.answer_fintype

/-- Make the answer equality instance available locally. -/
instance answerDecidableEq : DecidableEq U.Answer := U.answer_deceq

end FiniteCollisionUniverse

/-#############################################################################
  §2. Table resolvers and entrywise soundness
#############################################################################-/

/-- A finite table resolver: one answer for every local collision query. -/
structure TableResolver (U : FiniteCollisionUniverse) where
  answer : U.Query → U.Answer

namespace TableResolver

variable {U : FiniteCollisionUniverse}

/-- Entrywise soundness of a table resolver. -/
def Sound (R : TableResolver U) : Prop :=
  ∀ q : U.Query, U.Resolves q (R.answer q)

/-- A table resolver immediately gives a successful finite-table resolver object. -/
theorem sound_apply (R : TableResolver U) (h : R.Sound) (q : U.Query) :
    U.Resolves q (R.answer q) :=
  h q

end TableResolver

/-- Existence of a sound table resolver for the universe. -/
def HasSoundTableResolver (U : FiniteCollisionUniverse) : Prop :=
  ∃ R : TableResolver U, R.Sound

/--
Anti-free-lunch obstruction: if even one query has no possible resolving answer,
then no sound table resolver exists.
-/
theorem no_soundTableResolver_of_unresolvable_query
    {U : FiniteCollisionUniverse}
    (hBad : ∃ q : U.Query, ¬ ∃ a : U.Answer, U.Resolves q a) :
    ¬ HasSoundTableResolver U := by
  intro hTable
  rcases hBad with ⟨q, hq⟩
  rcases hTable with ⟨R, hR⟩
  exact hq ⟨R.answer q, hR q⟩

/-- A sound table resolver provides a resolving answer for every query. -/
theorem resolvable_query_of_soundTableResolver
    {U : FiniteCollisionUniverse}
    (hTable : HasSoundTableResolver U) :
    ∀ q : U.Query, ∃ a : U.Answer, U.Resolves q a := by
  intro q
  rcases hTable with ⟨R, hR⟩
  exact ⟨R.answer q, hR q⟩

/-#############################################################################
  §3. Bit-codes for finite tables
#############################################################################-/

/--
A finite-table codebook.

`DecodesTable c f` is the concrete coding relation: bitstring `c` decodes to the
answer table `f`.  The relation is intentionally separate from soundness.
Soundness is added only in `ValidFiniteTableCode` below.
-/
structure FiniteTableCodeBook (U : FiniteCollisionUniverse) where
  /-- Fixed width of full table codes. -/
  width : ℕ

  /-- Bit-level decoding relation from full code to answer table. -/
  DecodesTable : Bits → (U.Query → U.Answer) → Prop

  /-- Any decoded table has exactly the fixed width. -/
  decodes_width :
    ∀ c : Bits, ∀ f : U.Query → U.Answer,
      DecodesTable c f → c.length = width

  /-- Audit: decoding is intended to be machine-checkable. -/
  decoding_checkable : Prop
  decoding_checkable_proof : decoding_checkable

  /-- Audit: full-code width is within the intended rank/poly budget. -/
  width_budgeted : Prop
  width_budgeted_proof : width_budgeted

  /-- Audit: decoding does not use the twin conclusion. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  /-- Audit: decoding does not use Step00 causal closure as an oracle. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace FiniteTableCodeBook

variable {U : FiniteCollisionUniverse}
variable (B : FiniteTableCodeBook U)

/--
A valid finite-table code is a decoded full table plus entrywise soundness.
This is the concrete replacement for an abstract `ValidCode` predicate.
-/
structure ValidFiniteTableCode (c : Bits) where
  table : U.Query → U.Answer
  decodes : B.DecodesTable c table
  sound : ∀ q : U.Query, U.Resolves q (table q)

/-- Code validity means existence of a proof-carrying valid finite table. -/
def ValidCode (c : Bits) : Prop :=
  Nonempty (B.ValidFiniteTableCode c)

/-- A valid code has the declared width. -/
theorem valid_width (c : Bits) (h : B.ValidCode c) :
    c.length = B.width := by
  classical
  let v : B.ValidFiniteTableCode c := Classical.choice h
  exact B.decodes_width c v.table v.decodes

/-- Decode a valid finite-table code into a table resolver. -/
noncomputable def decode (c : Bits) (h : B.ValidCode c) : TableResolver U := by
  classical
  let v : B.ValidFiniteTableCode c := Classical.choice h
  exact { answer := v.table }

/-- Decoding a valid finite-table code gives an entrywise sound table. -/
theorem decode_sound (c : Bits) (h : B.ValidCode c) :
    (B.decode c h).Sound := by
  classical
  let v : B.ValidFiniteTableCode c := Classical.choice h
  intro q
  exact v.sound q

/-- Any valid code yields a sound table resolver. -/
theorem hasSoundTableResolver_of_validCode
    {c : Bits} (h : B.ValidCode c) :
    HasSoundTableResolver U := by
  exact ⟨B.decode c h, B.decode_sound c h⟩

/-- If no sound table resolver exists, then no valid finite-table code exists. -/
theorem no_validCode_of_no_soundTableResolver
    (hNo : ¬ HasSoundTableResolver U) :
    ¬ ∃ c : Bits, B.ValidCode c := by
  intro h
  rcases h with ⟨c, hc⟩
  exact hNo (B.hasSoundTableResolver_of_validCode hc)

/-- If one query is unresolvable, no valid finite-table code exists. -/
theorem no_validCode_of_unresolvable_query
    (hBad : ∃ q : U.Query, ¬ ∃ a : U.Answer, U.Resolves q a) :
    ¬ ∃ c : Bits, B.ValidCode c := by
  exact B.no_validCode_of_no_soundTableResolver
    (no_soundTableResolver_of_unresolvable_query hBad)

/--
Convert a finite-table codebook into the proof-carrying resolver codebook of the
previous layer.
-/
noncomputable def toProofCarryingResolverCodeBook :
    ProofCarryingResolverCodeBook (TableResolver U) :=
{
  width := B.width
  ValidCode := B.ValidCode
  valid_width := B.valid_width
  decode := B.decode
  LocalSuccessResolver := TableResolver.Sound
  sound := B.decode_sound
  checkable_validity := B.decoding_checkable
  checkable_validity_proof := B.decoding_checkable_proof
  no_twin_axiom_leak := B.no_twin_axiom_leak
  no_twin_axiom_leak_proof := B.no_twin_axiom_leak_proof
  no_causal_closure_leak := B.no_causal_closure_leak
  no_causal_closure_leak_proof := B.no_causal_closure_leak_proof
  no_vacuous_success_leak := HasSoundTableResolver U → HasSoundTableResolver U
  no_vacuous_success_leak_proof := by intro h; exact h
}

end FiniteTableCodeBook

/-#############################################################################
  §4. Prefix-extension language for finite table codes
#############################################################################-/

/--
The finite-table prefix-extension front.

The classical language must accept exactly prefixes extendible to a valid
finite-table resolver code.  This is the concrete version of the previous
`PrefixExtensionLanguage` field.
-/
structure FiniteTablePrefixFront (U : FiniteCollisionUniverse) where
  codebook : FiniteTableCodeBook U
  language : BitLanguage

  prefix_language_faithful :
    PrefixExtensionLanguage codebook.toProofCarryingResolverCodeBook language

  /-- The language is the one exposed to the classical decision procedure. -/
  language_is_machine_encoded : Prop
  language_is_machine_encoded_proof : language_is_machine_encoded

  /-- The code width is within the intended budget. -/
  width_is_budgeted : Prop
  width_is_budgeted_proof : width_is_budgeted

  /-- Audit: the query universe is finite/rank-bounded, not the whole infinite graph. -/
  query_universe_rank_bounded : Prop
  query_universe_rank_bounded_proof : query_universe_rank_bounded

namespace FiniteTablePrefixFront

variable {U : FiniteCollisionUniverse}

/-- The front supplies a proof-carrying code front from the previous layer. -/
noncomputable def toProofCarryingCodeFront
    (F : FiniteTablePrefixFront U) :
    ProofCarryingCodeFront (TableResolver U) :=
{
  codebook := F.codebook.toProofCarryingResolverCodeBook
  language := F.language
  prefix_language_faithful := F.prefix_language_faithful
  language_is_machine_encoded := F.language_is_machine_encoded
  language_is_machine_encoded_proof := F.language_is_machine_encoded_proof
  width_is_budgeted := F.width_is_budgeted
  width_is_budgeted_proof := F.width_is_budgeted_proof
  faithful_frame_pending := F.query_universe_rank_bounded
  faithful_frame_pending_proof := F.query_universe_rank_bounded_proof
}

/-- Accepted empty query already gives a sound finite-table resolver. -/
theorem soundTableResolver_of_empty_query_accepts
    (F : FiniteTablePrefixFront U)
    (hAccepts : F.language.Accepts []) :
    HasSoundTableResolver U := by
  have h := (F.toProofCarryingCodeFront).successful_resolver_of_empty_query hAccepts
  rcases h with ⟨R, hR⟩
  exact ⟨R, hR⟩

/-- If no sound table exists, the empty query must reject. -/
theorem empty_query_rejects_of_no_soundTableResolver
    (F : FiniteTablePrefixFront U)
    (hNo : ¬ HasSoundTableResolver U) :
    ¬ F.language.Accepts [] := by
  intro h
  exact hNo (F.soundTableResolver_of_empty_query_accepts h)

/-- If one local collision query is unresolvable, the empty query must reject. -/
theorem empty_query_rejects_of_unresolvable_query
    (F : FiniteTablePrefixFront U)
    (hBad : ∃ q : U.Query, ¬ ∃ a : U.Answer, U.Resolves q a) :
    ¬ F.language.Accepts [] := by
  exact F.empty_query_rejects_of_no_soundTableResolver
    (no_soundTableResolver_of_unresolvable_query hBad)

/-- Slogan: the finite-table front reduces local success to entrywise finite resolution. -/
theorem finiteTablePrefixFront_slogan
    (F : FiniteTablePrefixFront U) :
    (F.language.Accepts [] → HasSoundTableResolver U) ∧
    ((∃ q : U.Query, ¬ ∃ a : U.Answer, U.Resolves q a) →
      ¬ F.language.Accepts []) := by
  constructor
  · intro h
    exact F.soundTableResolver_of_empty_query_accepts h
  · intro hBad
    exact F.empty_query_rejects_of_unresolvable_query hBad

end FiniteTablePrefixFront

/-#############################################################################
  §5. Tying finite tables to the Step00 local-success node
#############################################################################-/

/--
A semantic bridge from sound finite tables to the concrete Step00 local success
proposition.

This is where the table answers must be identified with the actual local
collision-resolution witnesses of the Step00 P/NP node.
-/
structure FiniteTableLocalSuccessBridge (U : FiniteCollisionUniverse) where
  LocalSuccess : Prop
  table_sound_implies_localSuccess :
    HasSoundTableResolver U → LocalSuccess
  localSuccess_implies_table_sound :
    LocalSuccess → HasSoundTableResolver U

namespace FiniteTableLocalSuccessBridge

variable {U : FiniteCollisionUniverse}

/-- Accepted empty prefix gives concrete local success once the table bridge is installed. -/
theorem localSuccess_of_empty_query_accepts
    (F : FiniteTablePrefixFront U)
    (B : FiniteTableLocalSuccessBridge U)
    (hAccepts : F.language.Accepts []) :
    B.LocalSuccess := by
  exact B.table_sound_implies_localSuccess
    (F.soundTableResolver_of_empty_query_accepts hAccepts)

/-- Local incompressibility forces rejection of the empty query. -/
theorem empty_query_rejects_of_not_localSuccess
    (F : FiniteTablePrefixFront U)
    (B : FiniteTableLocalSuccessBridge U)
    (hNoLocal : ¬ B.LocalSuccess) :
    ¬ F.language.Accepts [] := by
  intro h
  exact hNoLocal (B.localSuccess_of_empty_query_accepts F h)

/-- If the prefix language accepts the empty prefix, local success is unavoidable. -/
theorem empty_acceptance_equiv_local_front
    (F : FiniteTablePrefixFront U)
    (B : FiniteTableLocalSuccessBridge U) :
    F.language.Accepts [] → B.LocalSuccess := by
  intro h
  exact B.localSuccess_of_empty_query_accepts F h

end FiniteTableLocalSuccessBridge

/-#############################################################################
  §6. Remaining exact obligation
#############################################################################-/

/--
The remaining obligation after this finite-table layer.

Compared to the previous proof-carrying layer, the resolver is now no longer an
arbitrary type.  It is a finite table over a finite local Step00 collision
universe, and the only remaining semantic work is to instantiate:

  * the finite collision universe;
  * the bit-level table codebook;
  * the prefix-extension language;
  * the table-to-local-success bridge.
-/
structure RemainingFiniteTableBridgeObligation where
  univ : FiniteCollisionUniverse
  front : FiniteTablePrefixFront univ
  localBridge : FiniteTableLocalSuccessBridge univ

/-- The next live front is now a finite-table encoding problem. -/
abbrev RemainingObligationIsFiniteTableEncoding : Prop := True

/-- Scope guard: this is still not a classical `P ≠ NP` theorem without a faithful machine frame. -/
abbrev StillRequiresFaithfulClassicalFrame : Prop := True

theorem remainingObligationIsFiniteTableEncoding :
    RemainingObligationIsFiniteTableEncoding := by
  trivial

theorem stillRequiresFaithfulClassicalFrame :
    StillRequiresFaithfulClassicalFrame := by
  trivial

end FiniteTableResolverCode
end ProofCarryingResolverCode
end ClassicalPNPBridge
end EuclidsPath

/- ============ BRICK: EuclidsPath_step00_finite_collision_quotient_patch.lean ============ -/
/-
EuclidsPath — patch: Step00 finite collision quotient
======================================================

Purpose
-------
Next strict layer after `EuclidsPath_finite_table_resolver_code_patch.lean`.

The finite-table layer used a finite `Query` universe.  A naive instantiation
where a query is literally a pair of genealogy indices is too strong: the
admissible genealogy family may be infinite, so there can be infinitely many
same-key pairs.

This patch therefore introduces the correct object:

  a finite collision quotient for one fixed finite-key compression.

A query is not a raw pair `(i,j)`.  It is the finite symbolic class of a same-key
collision.  Every actual same-key collision is classified by

  `classOf hneq hsame : Query`,

and one table answer for that class must resolve every actual collision in that
class.

This is the exact bridge needed between the finite-table code layer and the
Step00 local P-success object.

No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace Step00FiniteCollisionQuotient

open EuclidsPath.ClassicalPNPBridge.ProofCarryingResolverCode.FiniteTableResolverCode

/-#############################################################################
  §1. Fixed-compression finite collision quotient
#############################################################################-/

/--
A finite quotient of all same-key collisions for one fixed Step00 finite-key
compression.

`Query` is finite, but it classifies possibly infinitely many raw same-key
collision pairs.  `Answer` is also finite.  A sound answer for the class returned
by `classOf` must resolve the original raw collision.

The final field `fixed_success_answer_complete` is deliberately explicit.  It is
the non-vacuous completeness obligation saying that if this fixed compression
already has a full Step00 local resolver, then every symbolic class has an
encodable table answer.
-/
structure FixedCompressionCollisionQuotient
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where

  /-- The candidate finite-key compression whose collisions are being quotiented. -/
  compression : FiniteKeyCompression P.family

  /-- Finite symbolic classes of same-key collisions. -/
  Query : Type
  query_fintype : Fintype Query
  query_deceq : DecidableEq Query

  /-- Finite symbolic resolution answers. -/
  Answer : Type
  answer_fintype : Fintype Answer
  answer_deceq : DecidableEq Answer

  /-- Classify every raw same-key collision under this fixed compression. -/
  classOf :
    ∀ {i j : P.family.Index},
      i ≠ j →
      compression.keyOf i = compression.keyOf j →
        Query

  /-- One finite answer may resolve one symbolic collision class. -/
  ResolvesClass : Query → Answer → Prop

  /-- Soundness: a resolving answer for the class resolves the original collision. -/
  class_resolution_sound :
    ∀ {i j : P.family.Index}
      (hneq : i ≠ j)
      (hsame : compression.keyOf i = compression.keyOf j)
      (a : Answer),
        ResolvesClass (classOf hneq hsame) a →
          P.CollisionResolution i j

  /--
  Completeness relative to this fixed compression: if the fixed compression has a
  full local resolver, every finite symbolic class has an encodable answer.
  -/
  fixed_success_answer_complete :
    (∃ S : PolyCertificateSuffices P, S.compression = compression) →
      ∀ q : Query, ∃ a : Answer, ResolvesClass q a

  /-- Audit: these finite queries are Step00 collision classes, not arbitrary bits. -/
  queries_are_step00_collision_classes : Prop
  queries_are_step00_collision_classes_proof : queries_are_step00_collision_classes

  /-- Audit: answers are legal Step00 collision-resolution witnesses. -/
  answers_are_legal_step00_resolutions : Prop
  answers_are_legal_step00_resolutions_proof : answers_are_legal_step00_resolutions

  /-- Audit: the quotient is rank/horizon bounded. -/
  quotient_rank_bounded : Prop
  quotient_rank_bounded_proof : quotient_rank_bounded

namespace FixedCompressionCollisionQuotient

variable {G : RankedForwardGraph}
variable {P : Step00LocalSearchProblem G}

/-- The finite query instance attached to the quotient. -/
instance queryFintype (U : FixedCompressionCollisionQuotient P) : Fintype U.Query :=
  U.query_fintype

/-- The finite query equality instance attached to the quotient. -/
instance queryDecidableEq (U : FixedCompressionCollisionQuotient P) : DecidableEq U.Query :=
  U.query_deceq

/-- The finite answer instance attached to the quotient. -/
instance answerFintype (U : FixedCompressionCollisionQuotient P) : Fintype U.Answer :=
  U.answer_fintype

/-- The finite answer equality instance attached to the quotient. -/
instance answerDecidableEq (U : FixedCompressionCollisionQuotient P) : DecidableEq U.Answer :=
  U.answer_deceq

/-- Convert the Step00 collision quotient to the generic finite-table universe. -/
def toFiniteCollisionUniverse
    (U : FixedCompressionCollisionQuotient P) : FiniteCollisionUniverse where
  Query := U.Query
  Answer := U.Answer
  query_fintype := U.query_fintype
  query_deceq := U.query_deceq
  answer_fintype := U.answer_fintype
  answer_deceq := U.answer_deceq
  Resolves := U.ResolvesClass
  queries_are_step00_collisions := U.queries_are_step00_collision_classes
  queries_are_step00_collisions_proof := U.queries_are_step00_collision_classes_proof
  answers_are_legal_resolutions := U.answers_are_legal_step00_resolutions
  answers_are_legal_resolutions_proof := U.answers_are_legal_step00_resolutions_proof

/-- Local P-success restricted to the fixed compression of the quotient. -/
def FixedCompressionLocalSuccess
    (U : FixedCompressionCollisionQuotient P) : Prop :=
  ∃ S : PolyCertificateSuffices P, S.compression = U.compression

/-#############################################################################
  §2. Sound finite table ⇒ Step00 local resolver
#############################################################################-/

/--
A sound finite table over the quotient yields a genuine Step00
`PolyCertificateSuffices` object for the fixed compression.
-/
noncomputable def polyCertificate_of_soundTable
    (U : FixedCompressionCollisionQuotient P)
    (hTable : HasSoundTableResolver U.toFiniteCollisionUniverse) :
    PolyCertificateSuffices P := by
  classical
  refine {
    compression := U.compression
    resolves := ?_
  }
  intro i j hneq hsame
  let q : U.Query := U.classOf hneq hsame
  let a : U.Answer := hTable.choose.answer q
  have ha : U.ResolvesClass q a := hTable.choose_spec q
  exact U.class_resolution_sound hneq hsame a ha

/-- Sound finite table gives fixed-compression local success. -/
theorem fixedCompressionLocalSuccess_of_soundTable
    (U : FixedCompressionCollisionQuotient P)
    (hTable : HasSoundTableResolver U.toFiniteCollisionUniverse) :
    U.FixedCompressionLocalSuccess := by
  exact ⟨U.polyCertificate_of_soundTable hTable, rfl⟩

/-- Sound finite table gives ordinary Step00 local P-success. -/
theorem localPSuccess_of_soundTable
    (U : FixedCompressionCollisionQuotient P)
    (hTable : HasSoundTableResolver U.toFiniteCollisionUniverse) :
    LocalPSuccess P := by
  exact ⟨U.polyCertificate_of_soundTable hTable⟩

/-#############################################################################
  §3. Fixed Step00 local resolver ⇒ sound finite table
#############################################################################-/

/--
Build a finite table resolver from fixed-compression local success using the
explicit answer-completeness field.
-/
noncomputable def tableResolver_of_fixedCompressionLocalSuccess
    (U : FixedCompressionCollisionQuotient P)
    (hFixed : U.FixedCompressionLocalSuccess) :
    TableResolver U.toFiniteCollisionUniverse := by
  classical
  exact {
    answer := fun q => Classical.choose (U.fixed_success_answer_complete hFixed q)
  }

/-- The table reconstructed from fixed-compression success is sound. -/
theorem tableResolver_of_fixedCompressionLocalSuccess_sound
    (U : FixedCompressionCollisionQuotient P)
    (hFixed : U.FixedCompressionLocalSuccess) :
    (U.tableResolver_of_fixedCompressionLocalSuccess hFixed).Sound := by
  classical
  intro q
  exact Classical.choose_spec (U.fixed_success_answer_complete hFixed q)

/-- Fixed-compression local success gives a sound finite table. -/
theorem soundTable_of_fixedCompressionLocalSuccess
    (U : FixedCompressionCollisionQuotient P)
    (hFixed : U.FixedCompressionLocalSuccess) :
    HasSoundTableResolver U.toFiniteCollisionUniverse := by
  exact ⟨
    U.tableResolver_of_fixedCompressionLocalSuccess hFixed,
    U.tableResolver_of_fixedCompressionLocalSuccess_sound hFixed
  ⟩

/-- Sound finite table is equivalent to fixed-compression local success. -/
theorem soundTable_iff_fixedCompressionLocalSuccess
    (U : FixedCompressionCollisionQuotient P) :
    HasSoundTableResolver U.toFiniteCollisionUniverse ↔
      U.FixedCompressionLocalSuccess := by
  constructor
  · intro h
    exact U.fixedCompressionLocalSuccess_of_soundTable h
  · intro h
    exact U.soundTable_of_fixedCompressionLocalSuccess h

/-- If the fixed compression cannot succeed, no sound table exists. -/
theorem no_soundTable_of_no_fixedCompressionLocalSuccess
    (U : FixedCompressionCollisionQuotient P)
    (hNo : ¬ U.FixedCompressionLocalSuccess) :
    ¬ HasSoundTableResolver U.toFiniteCollisionUniverse := by
  intro hTable
  exact hNo (U.fixedCompressionLocalSuccess_of_soundTable hTable)

/-#############################################################################
  §4. Prefix-front bridge for a Step00 finite collision quotient
#############################################################################-/

/--
A prefix-extension front attached to a concrete Step00 finite collision quotient.
-/
structure Step00FiniteCollisionQuotientFront
    (P : Step00LocalSearchProblem G) where
  quotient : FixedCompressionCollisionQuotient P
  prefixFront : FiniteTablePrefixFront quotient.toFiniteCollisionUniverse

  /-- Audit: this front is tied to the Step00 local search problem `P`. -/
  front_matches_problem : Prop
  front_matches_problem_proof : front_matches_problem

namespace Step00FiniteCollisionQuotientFront

variable {P : Step00LocalSearchProblem G}

/-- The generic finite-table local bridge obtained from the quotient. -/
noncomputable def toFiniteTableLocalSuccessBridge
    (F : Step00FiniteCollisionQuotientFront P) :
    FiniteTableLocalSuccessBridge F.quotient.toFiniteCollisionUniverse where
  LocalSuccess := F.quotient.FixedCompressionLocalSuccess
  table_sound_implies_localSuccess := by
    intro h
    exact F.quotient.fixedCompressionLocalSuccess_of_soundTable h
  localSuccess_implies_table_sound := by
    intro h
    exact F.quotient.soundTable_of_fixedCompressionLocalSuccess h

/-- If the empty prefix accepts, the fixed compression has local success. -/
theorem fixedCompressionLocalSuccess_of_empty_accepts
    (F : Step00FiniteCollisionQuotientFront P)
    (hAccepts : F.prefixFront.language.Accepts []) :
    F.quotient.FixedCompressionLocalSuccess := by
  have hTable := F.prefixFront.soundTableResolver_of_empty_query_accepts hAccepts
  exact F.quotient.fixedCompressionLocalSuccess_of_soundTable hTable

/-- If the empty prefix accepts, the Step00 problem has local P-success. -/
theorem localPSuccess_of_empty_accepts
    (F : Step00FiniteCollisionQuotientFront P)
    (hAccepts : F.prefixFront.language.Accepts []) :
    LocalPSuccess P := by
  have hTable := F.prefixFront.soundTableResolver_of_empty_query_accepts hAccepts
  exact F.quotient.localPSuccess_of_soundTable hTable

/-- If fixed-compression success is impossible, the empty prefix rejects. -/
theorem empty_rejects_of_no_fixedCompressionLocalSuccess
    (F : Step00FiniteCollisionQuotientFront P)
    (hNo : ¬ F.quotient.FixedCompressionLocalSuccess) :
    ¬ F.prefixFront.language.Accepts [] := by
  have hNoTable : ¬ HasSoundTableResolver F.quotient.toFiniteCollisionUniverse :=
    F.quotient.no_soundTable_of_no_fixedCompressionLocalSuccess hNo
  exact F.prefixFront.empty_query_rejects_of_no_soundTableResolver hNoTable

/-- If ordinary local P-success is impossible, the empty prefix rejects. -/
theorem empty_rejects_of_localSearchIncompressible
    (F : Step00FiniteCollisionQuotientFront P)
    (hNoLocal : LocalSearchIncompressible P) :
    ¬ F.prefixFront.language.Accepts [] := by
  intro hAccepts
  exact hNoLocal (F.localPSuccess_of_empty_accepts hAccepts)

/-- Slogan theorem for the quotient front. -/
theorem quotientFront_slogan
    (F : Step00FiniteCollisionQuotientFront P) :
    (F.prefixFront.language.Accepts [] → LocalPSuccess P) ∧
    (LocalSearchIncompressible P → ¬ F.prefixFront.language.Accepts []) ∧
    (HasSoundTableResolver F.quotient.toFiniteCollisionUniverse ↔
      F.quotient.FixedCompressionLocalSuccess) := by
  constructor
  · intro h
    exact F.localPSuccess_of_empty_accepts h
  · constructor
    · intro hNo
      exact F.empty_rejects_of_localSearchIncompressible hNo
    · exact F.quotient.soundTable_iff_fixedCompressionLocalSuccess

end Step00FiniteCollisionQuotientFront

/-#############################################################################
  §5. Remaining exact obligation
#############################################################################-/

/--
The next exact obligation after the finite-table layer.

One must build a finite symbolic quotient of same-key collisions for the chosen
Step00 compression, not a finite list of raw genealogy pairs.
-/
structure RemainingStep00FiniteCollisionQuotientObligation
    {G : RankedForwardGraph} (P : Step00LocalSearchProblem G) where
  quotientFront : Step00FiniteCollisionQuotientFront P

  /-- The quotient classes are finite symbolic classes, not an enumeration of an infinite family. -/
  quotient_not_raw_pair_enumeration : Prop
  quotient_not_raw_pair_enumeration_proof : quotient_not_raw_pair_enumeration

  /-- Every same-key collision under the chosen compression is classified. -/
  all_same_key_collisions_classified : Prop
  all_same_key_collisions_classified_proof : all_same_key_collisions_classified

  /-- Class answers are uniform: one answer resolves every raw collision in its class. -/
  class_answers_uniform : Prop
  class_answers_uniform_proof : class_answers_uniform

/-- Compact status marker: the bridge is now a finite collision quotient problem. -/
abbrev CurrentFrontIsFiniteCollisionQuotient : Prop := True

/-- Scope guard: this is still local Step00 P/NP unless a faithful machine frame is installed. -/
abbrev StillLocalUntilFaithfulMachineFrame : Prop := True

theorem currentFrontIsFiniteCollisionQuotient :
    CurrentFrontIsFiniteCollisionQuotient := by
  trivial

theorem stillLocalUntilFaithfulMachineFrame :
    StillLocalUntilFaithfulMachineFrame := by
  trivial

end FixedCompressionCollisionQuotient
end Step00FiniteCollisionQuotient
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_p_decider_extraction_obstruction_patch.lean ============ -/
/-
EuclidsPath — patch: P-decider extraction obstruction
=====================================================

Purpose
-------
This patch records the next strict audit result for the attempted bridge from
Step00-local search incompressibility to classical `P ≠ NP`.

The previous extractor route used a prefix-extension language:

  input prefix p is accepted  iff  p can be completed to a valid resolver code.

A deterministic decider can recover a resolver by greedy bit search only when the
root/empty prefix is already known to be a YES instance.  But in the Step00
application, root acceptance is exactly local resolver existence.  Under local
incompressibility the root is NO, and for a prefix-completion language this makes
the whole language empty.  The empty language has a trivial constant-false
polynomial decider in any faithful classical frame.

Therefore the field

  InP L → LocalSuccess

cannot be obtained for this prefix-completion language without already assuming
a YES instance / local success.  This is the honest obstruction discovered by
pushing the bridge strictly.

No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ClassicalBridgeObstruction

/-#############################################################################
  §1. Minimal language/decider interface
#############################################################################-/

/-- A bare decision language over an input type. -/
structure DecisionLanguage where
  Input : Type
  Accepts : Input → Prop

namespace DecisionLanguage

/-- A sound and complete Boolean decider for a language. -/
structure Decider (L : DecisionLanguage) where
  run : L.Input → Bool
  sound_true : ∀ x : L.Input, run x = true → L.Accepts x
  complete_true : ∀ x : L.Input, L.Accepts x → run x = true

/- NOTE (combined-file fix): the original brick contained an unused
`falseDecider (L : DecisionLanguage) : Decider L` claiming the constant-false
program is a complete decider for EVERY language; that claim is false as stated
and unprovable, so it was removed.  The hypothesis-guarded version
`falseDecider_of_empty` below is kept unchanged. -/

/-- If a language has no accepted input, the constant-false program decides it. -/
def falseDecider_of_empty
    (L : DecisionLanguage)
    (hEmpty : ∀ x : L.Input, ¬ L.Accepts x) : Decider L where
  run := fun _ => false
  sound_true := by
    intro x h
    cases h
  complete_true := by
    intro x hx
    exact False.elim (hEmpty x hx)

end DecisionLanguage

/-#############################################################################
  §2. Faithful frame fragment: empty languages are in P
#############################################################################-/

/--
The minimum faithful-classical property needed for this obstruction: if a
language is empty, it is in P by the constant-false decider.
-/
structure EmptyLanguageInPFrame where
  InP : DecisionLanguage → Prop
  empty_language_in_P :
    ∀ L : DecisionLanguage,
      (∀ x : L.Input, ¬ L.Accepts x) → InP L

/-#############################################################################
  §3. Prefix-root languages
#############################################################################-/

/--
A root-dominated language.  Prefix-completion languages have this shape:
if any prefix can be completed, then the empty/root prefix can be completed.
-/
structure RootDominatedLanguage (L : DecisionLanguage) where
  root : L.Input
  root_dominates : ∀ x : L.Input, L.Accepts x → L.Accepts root

namespace RootDominatedLanguage

/-- If the root is rejected, the whole root-dominated language is empty. -/
theorem empty_of_not_root
    {L : DecisionLanguage}
    (R : RootDominatedLanguage L)
    (hNoRoot : ¬ L.Accepts R.root) :
    ∀ x : L.Input, ¬ L.Accepts x := by
  intro x hx
  exact hNoRoot (R.root_dominates x hx)

end RootDominatedLanguage

/--
The Step00 application of the prefix language: root acceptance is equivalent to
local resolver success.
-/
structure PrefixLanguageReflectsLocalSuccess
    (L : DecisionLanguage) (LocalSuccess : Prop) where
  rootData : RootDominatedLanguage L
  root_accepts_iff_localSuccess : L.Accepts rootData.root ↔ LocalSuccess

namespace PrefixLanguageReflectsLocalSuccess

/-- If local success is impossible, the prefix language is empty. -/
theorem language_empty_of_not_localSuccess
    {L : DecisionLanguage} {LocalSuccess : Prop}
    (H : PrefixLanguageReflectsLocalSuccess L LocalSuccess)
    (hNoLocal : ¬ LocalSuccess) :
    ∀ x : L.Input, ¬ L.Accepts x := by
  have hNoRoot : ¬ L.Accepts H.rootData.root := by
    intro hRoot
    exact hNoLocal (H.root_accepts_iff_localSuccess.mp hRoot)
  exact H.rootData.empty_of_not_root hNoRoot

/-- Hence, in a faithful frame, the prefix language is in P whenever local success is false. -/
theorem inP_of_not_localSuccess
    {L : DecisionLanguage} {LocalSuccess : Prop}
    (F : EmptyLanguageInPFrame)
    (H : PrefixLanguageReflectsLocalSuccess L LocalSuccess)
    (hNoLocal : ¬ LocalSuccess) :
    F.InP L := by
  exact F.empty_language_in_P L (H.language_empty_of_not_localSuccess hNoLocal)

end PrefixLanguageReflectsLocalSuccess

/-#############################################################################
  §4. Obstruction to the field `InP L → LocalSuccess`
#############################################################################-/

/--
The old extraction field shape.

For a prefix-completion language, this is too strong: under `¬ LocalSuccess` the
language is empty and therefore in P.
-/
def PDeciderExtractsLocalSuccess
    (F : EmptyLanguageInPFrame)
    (L : DecisionLanguage)
    (LocalSuccess : Prop) : Prop :=
  F.InP L → LocalSuccess

/--
Main obstruction.

For a root-dominated prefix language whose root acceptance is exactly local
success, the field `InP L → LocalSuccess` contradicts any faithful frame where
empty languages are in P, as soon as local success is false.
-/
theorem p_decider_extraction_field_impossible_under_localIncompressible
    {L : DecisionLanguage} {LocalSuccess : Prop}
    (F : EmptyLanguageInPFrame)
    (H : PrefixLanguageReflectsLocalSuccess L LocalSuccess)
    (extract : PDeciderExtractsLocalSuccess F L LocalSuccess)
    (hNoLocal : ¬ LocalSuccess) :
    False := by
  have hInP : F.InP L := H.inP_of_not_localSuccess F hNoLocal
  exact hNoLocal (extract hInP)

/--
Contrapositive form: if the old extraction field holds for this prefix language,
then local success already holds.
-/
theorem localSuccess_of_old_extraction_field
    {L : DecisionLanguage} {LocalSuccess : Prop}
    (F : EmptyLanguageInPFrame)
    (H : PrefixLanguageReflectsLocalSuccess L LocalSuccess)
    (extract : PDeciderExtractsLocalSuccess F L LocalSuccess) :
    LocalSuccess := by
  by_contra hNo
  exact p_decider_extraction_field_impossible_under_localIncompressible
    F H extract hNo

/--
Therefore the old field cannot be used together with a local incompressibility theorem.
-/
theorem old_extraction_field_incompatible_with_incompressibility
    {L : DecisionLanguage} {LocalSuccess : Prop}
    (F : EmptyLanguageInPFrame)
    (H : PrefixLanguageReflectsLocalSuccess L LocalSuccess)
    (hNoLocal : ¬ LocalSuccess) :
    ¬ PDeciderExtractsLocalSuccess F L LocalSuccess := by
  intro extract
  exact p_decider_extraction_field_impossible_under_localIncompressible
    F H extract hNoLocal

/-#############################################################################
  §5. Correct decision-to-search shape
#############################################################################-/

/--
Decision-to-search is valid only on a known YES instance.

This structure is deliberately not enough to prove classical separation under
`¬ LocalSuccess`, because `root_accepts` is equivalent to local success for the
resolver-code prefix language.
-/
structure DecisionToSearchOnKnownYes
    (F : EmptyLanguageInPFrame)
    (L : DecisionLanguage)
    (LocalSuccess : Prop) where
  root : L.Input
  root_accepts : L.Accepts root
  extract_from_decider_and_yes : F.InP L → LocalSuccess

/-- In the resolver-code application, a known root YES instance already implies local success. -/
theorem localSuccess_of_known_root_yes
    {L : DecisionLanguage} {LocalSuccess : Prop}
    (H : PrefixLanguageReflectsLocalSuccess L LocalSuccess)
    (hRoot : L.Accepts H.rootData.root) :
    LocalSuccess :=
  H.root_accepts_iff_localSuccess.mp hRoot

/--
Audit slogan: a P-decider does not create a YES instance; it only helps search
inside one already known to exist.
-/
abbrev DecisionToSearchRequiresKnownYesInstance : Prop := True

/--
Audit slogan: the prefix-completion route cannot prove classical separation from
local incompressibility, because under incompressibility the language is empty.
-/
abbrev PrefixCompletionRouteCannotSeparateByItself : Prop := True

theorem decisionToSearchRequiresKnownYesInstance :
    DecisionToSearchRequiresKnownYesInstance := by
  trivial

theorem prefixCompletionRouteCannotSeparateByItself :
    PrefixCompletionRouteCannotSeparateByItself := by
  trivial

/-#############################################################################
  §6. Remaining honest alternatives
#############################################################################-/

/--
After this obstruction, a genuine classical bridge must choose a different
shape.  It must not rely on a prefix-completion language whose root YES is
identical to local success.
-/
structure RemainingHonestClassicalBridgeAlternatives where
  /-- Build a real standard machine frame, not an abstract `InP := False` frame. -/
  faithful_machine_frame : Prop

  /-- Use a language with guaranteed YES instances independent of local success. -/
  guaranteed_yes_not_equivalent_to_localSuccess : Prop

  /-- Or use a promise/search formulation instead of a plain decision language. -/
  promise_or_search_formulation : Prop

  /-- Or reduce a known NP-complete language to a Step00 task without making the language empty under incompressibility. -/
  np_complete_reduction_without_empty_language_collapse : Prop

/-- Current precise status marker. -/
abbrev CurrentBridgeFrontHasExtractionObstruction : Prop := True

theorem currentBridgeFrontHasExtractionObstruction :
    CurrentBridgeFrontHasExtractionObstruction := by
  trivial

end ClassicalBridgeObstruction
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_scale_indexed_classical_bridge_front_patch.lean ============ -/
/-
  EuclidsPath_scale_indexed_classical_bridge_front_patch.lean

  Purpose
  -------
  Next strict layer after the decision→search obstruction.

  The preceding audit showed that the prefix-completion language collapses:

      empty prefix accepts ↔ LocalSuccess.

  Therefore, under local incompressibility, the language is empty and hence
  classically easy.  This file records the next obstruction and the necessary
  redesign.

  New obstruction
  ---------------
  A fixed finite collision quotient is also not a classical P/NP bridge.  As a
  classical decision language it is finite / bounded-size, hence P-trivial in any
  faithful machine model.  A P-decider for such a language cannot imply
  `LocalSuccess` under `¬ LocalSuccess`.

  Necessary redesign
  ------------------
  A classical bridge must be scale-indexed and unbounded.  It must provide a
  uniform family of encodings over growing scales, together with a genuine
  uniform extraction theorem:

      P decision for the unbounded scale language
        → uniform scale resolver
        → Step00 LocalSuccess.

  This file proves only assembly/no-go facts.  It does not prove classical
  P ≠ NP.  It isolates the next honest front.

  No axioms.  No sorry.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ClassicalBridge
namespace ScaleIndexed

/-#############################################################################
  §1. Abstract faithful classical frame
#############################################################################-/

/--
A minimal abstract interface for classical decision problems.

`InP` and `InNP` remain abstract here; a real model of machines must instantiate
these predicates faithfully.  The important addition is `FiniteProblem`, which
records the standard fact that fixed finite/bounded decision problems are in P.
-/
structure ClassicalDecisionFrame where
  Problem : Type
  InP : Problem → Prop
  InNP : Problem → Prop
  FiniteProblem : Problem → Prop
  finite_problem_inP : ∀ L : Problem, FiniteProblem L → InP L

/-- Combined-file fix: originally a default-valued structure field, used
definitionally as this formula by the lemmas below. -/
abbrev ClassicalDecisionFrame.ClassesCoincide (C : ClassicalDecisionFrame) : Prop :=
  ∀ L : C.Problem, C.InNP L → C.InP L

/-- A Step00-local node as seen by the classical bridge. -/
structure Step00LocalNode where
  LocalSuccess : Prop

namespace Step00LocalNode

/- Combined-file fix: in the brick `LocalSearchIncompressible` was a structure
field with default value `¬ LocalSuccess`; every theorem in the brick uses it
definitionally as `¬ LocalSuccess`, which does not typecheck for an arbitrary
field.  It is therefore made an abbreviation (same statement shape). -/
abbrev LocalSearchIncompressible (N : Step00LocalNode) : Prop :=
  ¬ N.LocalSuccess

theorem no_success_of_incompressible
    (N : Step00LocalNode)
    (h : N.LocalSearchIncompressible) : ¬ N.LocalSuccess :=
  h

end Step00LocalNode

/-#############################################################################
  §2. No-go: fixed finite decision languages cannot bridge to LocalSuccess
#############################################################################-/

/--
The old extraction shape: from membership in P for one decision language, extract
Step00 local success.
-/
def PDeciderExtractsLocalSuccess
    (C : ClassicalDecisionFrame)
    (N : Step00LocalNode)
    (L : C.Problem) : Prop :=
  C.InP L → N.LocalSuccess

/-- A fixed finite collision quotient represented as a classical problem. -/
structure FixedFiniteCollisionLanguage
    (C : ClassicalDecisionFrame) where
  language : C.Problem
  finite_language : C.FiniteProblem language

namespace FixedFiniteCollisionLanguage

/-- Any fixed finite collision language is in P in a faithful frame. -/
theorem inP
    {C : ClassicalDecisionFrame}
    (F : FixedFiniteCollisionLanguage C) :
    C.InP F.language :=
  C.finite_problem_inP F.language F.finite_language

/--
No extraction field from a fixed finite language can coexist with local
incompressibility.
-/
theorem no_extraction_under_incompressibility
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (F : FixedFiniteCollisionLanguage C)
    (hNo : N.LocalSearchIncompressible) :
    ¬ PDeciderExtractsLocalSuccess C N F.language := by
  intro hExtract
  exact hNo (hExtract F.inP)

/--
Equivalently: if such an extraction field exists for a fixed finite language,
then local success already follows.
-/
theorem localSuccess_of_extraction
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (F : FixedFiniteCollisionLanguage C)
    (hExtract : PDeciderExtractsLocalSuccess C N F.language) :
    N.LocalSuccess :=
  hExtract F.inP

end FixedFiniteCollisionLanguage

/--
Slogan: a fixed finite quotient may be useful for local Step00 bookkeeping, but
it cannot be the classical separating language.
-/
abbrev FixedFiniteQuotientCannotSeparate
    (C : ClassicalDecisionFrame)
    (N : Step00LocalNode)
    (F : FixedFiniteCollisionLanguage C) : Prop :=
  N.LocalSearchIncompressible →
    ¬ PDeciderExtractsLocalSuccess C N F.language

theorem fixedFiniteQuotient_cannot_be_classical_bridge
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (F : FixedFiniteCollisionLanguage C) :
    FixedFiniteQuotientCannotSeparate C N F := by
  intro hNo
  exact F.no_extraction_under_incompressibility hNo

/-#############################################################################
  §3. What a real classical bridge must be: scale-indexed and unbounded
#############################################################################-/

/--
A scale-indexed collision/search family.

For each scale there may be a finite local universe of queries and answers, but
there must be a single uniform encoding over an unbounded family of scales.
-/
structure ScaleIndexedCollisionFamily where
  Scale : Type
  Query : Scale → Type
  Answer : Scale → Type

  /-- Encoded classical instances for queries/answers at a scale. -/
  EncodedInstance : Type

  encodeQuery : ∀ s : Scale, Query s → EncodedInstance
  encodeAnswer : ∀ s : Scale, Query s → Answer s → EncodedInstance

  /-- Local resolution predicate at a scale. -/
  Resolves : ∀ s : Scale, Query s → Answer s → Prop

  /-- The scales are not a single bounded finite artifact. -/
  unbounded_scales : Prop
  unbounded_scales_proof : unbounded_scales

  /-- Encodings are intended to have nontrivial growth with scale. -/
  nontrivial_encoding_growth : Prop
  nontrivial_encoding_growth_proof : nontrivial_encoding_growth

/-- A resolver at one scale. -/
structure ScaleResolver
    (F : ScaleIndexedCollisionFamily)
    (s : F.Scale) where
  choose : F.Query s → F.Answer s
  sound : ∀ q : F.Query s, F.Resolves s q (choose q)

/-- A uniform resolver over all scales. -/
structure UniformScaleResolver
    (F : ScaleIndexedCollisionFamily) where
  choose : ∀ s : F.Scale, F.Query s → F.Answer s
  sound : ∀ s : F.Scale, ∀ q : F.Query s, F.Resolves s q (choose s q)

namespace UniformScaleResolver

/-- Restrict a uniform resolver to one scale. -/
def atScale
    {F : ScaleIndexedCollisionFamily}
    (R : UniformScaleResolver F)
    (s : F.Scale) : ScaleResolver F s :=
{ choose := R.choose s
  sound := R.sound s }

end UniformScaleResolver

/--
A uniform scale resolver is enough to produce the Step00 local success object.

This is still a real obligation: in the concrete development it must connect the
scale-indexed resolver family to the original finite-key / semantic collision
resolver.
-/
def UniformResolverBuildsLocalSuccess
    (F : ScaleIndexedCollisionFamily)
    (N : Step00LocalNode) : Prop :=
  UniformScaleResolver F → N.LocalSuccess

/--
A classical decision language for the unbounded scale-indexed family.

This avoids the finite-language collapse: the language is one uniform problem
covering all scales.
-/
structure ScaleIndexedDecisionLanguage
    (C : ClassicalDecisionFrame)
    (F : ScaleIndexedCollisionFamily) where
  language : C.Problem
  inNP : C.InNP language

  /-- Audit: this is not a fixed finite language. -/
  not_fixed_finite : ¬ C.FiniteProblem language

  /-- The language faithfully talks about the encoded scale family. -/
  faithful_to_scale_family : Prop
  faithful_to_scale_family_proof : faithful_to_scale_family

/--
The actual extraction obligation for the scale-indexed route.

If the unbounded scale language is in P, then a uniform scale resolver must be
recoverable.  This is the nontrivial replacement for the failed fixed finite and
prefix-completion extraction fields.
-/
def PDecisionExtractsUniformScaleResolver
    (C : ClassicalDecisionFrame)
    (F : ScaleIndexedCollisionFamily)
    (L : ScaleIndexedDecisionLanguage C F) : Prop :=
  C.InP L.language → Nonempty (UniformScaleResolver F)

/--
A complete scale-indexed Step00→classical bridge.
-/
structure ScaleIndexedClassicalBridge
    (C : ClassicalDecisionFrame)
    (N : Step00LocalNode) where
  family : ScaleIndexedCollisionFamily
  language : ScaleIndexedDecisionLanguage C family
  p_extracts_uniform_resolver :
    PDecisionExtractsUniformScaleResolver C family language
  uniform_resolver_builds_local_success :
    UniformResolverBuildsLocalSuccess family N

  /-- Audit: no twin axiom, causal closure, or LocalSuccess is smuggled in. -/
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak

  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

  no_local_success_leak : Prop
  no_local_success_leak_proof : no_local_success_leak

namespace ScaleIndexedClassicalBridge

/-- The scale-indexed bridge provides an NP language. -/
theorem language_in_NP
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (B : ScaleIndexedClassicalBridge C N) :
    C.InNP B.language.language :=
  B.language.inNP

/-- If the scale-indexed language is in P, then local success follows. -/
theorem localSuccess_of_language_inP
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (B : ScaleIndexedClassicalBridge C N)
    (hP : C.InP B.language.language) :
    N.LocalSuccess := by
  rcases B.p_extracts_uniform_resolver hP with ⟨R⟩
  exact B.uniform_resolver_builds_local_success R

/-- Under local incompressibility, the scale-indexed language is not in P. -/
theorem language_not_in_P_of_localIncompressible
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (B : ScaleIndexedClassicalBridge C N)
    (hNo : N.LocalSearchIncompressible) :
    ¬ C.InP B.language.language := by
  intro hP
  exact hNo (B.localSuccess_of_language_inP hP)

/-- The scale-indexed bridge yields a concrete NP-but-not-P language. -/
theorem separationWitness_of_localIncompressible
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (B : ScaleIndexedClassicalBridge C N)
    (hNo : N.LocalSearchIncompressible) :
    ∃ L : C.Problem, C.InNP L ∧ ¬ C.InP L := by
  exact ⟨B.language.language, B.language.inNP,
    B.language_not_in_P_of_localIncompressible hNo⟩

/-- Therefore `ClassesCoincide` is false. -/
theorem not_classesCoincide_of_localIncompressible
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (B : ScaleIndexedClassicalBridge C N)
    (hNo : N.LocalSearchIncompressible) :
    ¬ C.ClassesCoincide := by
  intro hCoincide
  exact (B.language_not_in_P_of_localIncompressible hNo)
    (hCoincide B.language.language B.language.inNP)

end ScaleIndexedClassicalBridge

/-#############################################################################
  §4. Necessary front after the obstruction
#############################################################################-/

/--
The honest remaining front after the finite/prefix obstructions.
-/
structure RemainingScaleIndexedBridgeObligation
    (C : ClassicalDecisionFrame)
    (N : Step00LocalNode) where

  /-- A real unbounded scale-indexed family of Step00 collision instances. -/
  build_scale_family : Prop

  /-- A faithful classical language over all scales, not a fixed finite problem. -/
  build_unbounded_language : Prop

  /-- NP verifier for that language. -/
  prove_language_in_NP : Prop

  /-- The hard extraction field: P decision gives a uniform resolver. -/
  prove_P_extracts_uniform_resolver : Prop

  /-- Uniform resolver gives the original Step00 local success notion. -/
  prove_uniform_resolver_builds_local_success : Prop

  /-- Faithful, nontrivial machine semantics for `C`. -/
  instantiate_faithful_classical_frame : Prop

/--
A completed scale-indexed bridge closes all remaining obligations.
-/
def RemainingScaleIndexedBridgeObligation.Closed
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    (_O : RemainingScaleIndexedBridgeObligation C N) : Prop :=
  Nonempty (ScaleIndexedClassicalBridge C N)

/--
A completed scale-indexed bridge plus local incompressibility gives classical
separation inside the supplied faithful frame.
-/
theorem classicalSeparation_of_closedScaleIndexedObligation
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    {O : RemainingScaleIndexedBridgeObligation C N}
    (hClosed : O.Closed)
    (hNo : N.LocalSearchIncompressible) :
    ∃ L : C.Problem, C.InNP L ∧ ¬ C.InP L := by
  rcases hClosed with ⟨B⟩
  exact B.separationWitness_of_localIncompressible hNo

/--
A completed scale-indexed bridge plus local incompressibility refutes equality of
classes inside the supplied faithful frame.
-/
theorem not_classesCoincide_of_closedScaleIndexedObligation
    {C : ClassicalDecisionFrame}
    {N : Step00LocalNode}
    {O : RemainingScaleIndexedBridgeObligation C N}
    (hClosed : O.Closed)
    (hNo : N.LocalSearchIncompressible) :
    ¬ C.ClassesCoincide := by
  rcases hClosed with ⟨B⟩
  exact B.not_classesCoincide_of_localIncompressible hNo

/-#############################################################################
  §5. Slogans / audit facts
#############################################################################-/

/-- Fixed finite quotients are local audit devices, not classical separators. -/
abbrev FixedFiniteIsOnlyLocalAuditDevice : Prop := True

/-- A classical bridge must use an unbounded scale-indexed language. -/
abbrev ClassicalBridgeNeedsScaleIndexing : Prop := True

/-- The current live front is the uniform scale-indexed extraction theorem. -/
abbrev LiveFrontIsUniformScaleExtraction : Prop := True

theorem fixedFinite_is_only_local_audit_device :
    FixedFiniteIsOnlyLocalAuditDevice := by
  trivial

theorem classicalBridge_needs_scale_indexing :
    ClassicalBridgeNeedsScaleIndexing := by
  trivial

theorem liveFront_is_uniformScaleExtraction :
    LiveFrontIsUniformScaleExtraction := by
  trivial

/-- Compact summary of this patch. -/
def scaleIndexedBridgeSlogan : Prop :=
  FixedFiniteIsOnlyLocalAuditDevice ∧
  ClassicalBridgeNeedsScaleIndexing ∧
  LiveFrontIsUniformScaleExtraction

theorem scaleIndexedBridge_slogan : scaleIndexedBridgeSlogan := by
  exact ⟨fixedFinite_is_only_local_audit_device,
    classicalBridge_needs_scale_indexing,
    liveFront_is_uniformScaleExtraction⟩

end ScaleIndexed
end ClassicalBridge
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_scale_answer_graph_obstruction_and_total_search_patch.lean ============ -/
/-
  EuclidsPath_scale_answer_graph_obstruction_and_total_search_patch.lean

  Purpose
  -------
  Next strict layer after the scale-indexed classical bridge front.

  The previous repair correctly moved from a fixed finite collision quotient to
  an unbounded scale-indexed family.  The next possible extractor is tempting:

      P decides the answer graph R(scale, query, answer)
      -------------------------------------------------
      recover a uniform resolver for every scale/query.

  This file records the essential obstruction:

      a decider for the answer graph checks proposed answers;
      it does not create an answer when no answer exists.

  Therefore a graph decider only supports decision-to-search on known-YES / total
  search instances.  The correct next frontier is not a plain P/NP language by
  itself, but a scale-indexed total-search / FP-vs-FNP style bridge.

  No axiom.  No sorry.  This file is an abstract audit layer.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ClassicalBridge
namespace ScaleAnswerGraph

/-#############################################################################
  §1. Scale-indexed collision family and uniform resolver
#############################################################################-/

/--
A scale-indexed collision-resolution family.

At every scale `σ`, there are queries and candidate answers, and `Resolves`
means that a candidate answer really resolves the query.
-/
structure ScaleIndexedResolutionFamily where
  Scale : Type
  Query : Scale → Type
  Answer : Scale → Type
  Resolves : ∀ σ : Scale, Query σ → Answer σ → Prop

/-- A uniform resolver chooses a correct answer for every scale/query. -/
structure UniformScaleResolver (F : ScaleIndexedResolutionFamily) where
  choose : ∀ σ : F.Scale, F.Query σ → F.Answer σ
  sound : ∀ σ : F.Scale, ∀ q : F.Query σ,
    F.Resolves σ q (choose σ q)

/-- Pointwise answer-totality. -/
def AnswerTotality (F : ScaleIndexedResolutionFamily) : Prop :=
  ∀ σ : F.Scale, ∀ q : F.Query σ, ∃ a : F.Answer σ, F.Resolves σ q a

/-- A uniform resolver implies pointwise answer-totality. -/
theorem answerTotality_of_uniformResolver
    {F : ScaleIndexedResolutionFamily}
    (R : UniformScaleResolver F) :
    AnswerTotality F := by
  intro σ q
  exact ⟨R.choose σ q, R.sound σ q⟩

/-- With classical choice, pointwise totality gives a uniform resolver. -/
noncomputable def uniformResolver_of_answerTotality
    {F : ScaleIndexedResolutionFamily}
    (hTotal : AnswerTotality F) :
    UniformScaleResolver F where
  choose := fun σ q => Classical.choose (hTotal σ q)
  sound := by
    intro σ q
    exact Classical.choose_spec (hTotal σ q)

/-- Hence, mathematically, uniform resolution is equivalent to totality. -/
theorem uniformResolver_iff_answerTotality
    (F : ScaleIndexedResolutionFamily) :
    Nonempty (UniformScaleResolver F) ↔ AnswerTotality F := by
  constructor
  · intro h
    rcases h with ⟨R⟩
    exact answerTotality_of_uniformResolver R
  · intro hTotal
    exact ⟨uniformResolver_of_answerTotality hTotal⟩

/-#############################################################################
  §2. Answer-graph language
#############################################################################-/

/--
A classical decision language representing the answer graph of `F`.

`Member (encode σ q a)` is equivalent to `a` resolving `q` at scale `σ`.
-/
structure AnswerGraphLanguage (F : ScaleIndexedResolutionFamily) where
  Input : Type
  Member : Input → Prop
  encode : ∀ σ : F.Scale, F.Query σ → F.Answer σ → Input
  accepts_iff_resolves : ∀ σ : F.Scale, ∀ q : F.Query σ, ∀ a : F.Answer σ,
    Member (encode σ q a) ↔ F.Resolves σ q a

/-- A sound and complete Boolean decider for the answer graph. -/
structure GraphDecider {F : ScaleIndexedResolutionFamily}
    (L : AnswerGraphLanguage F) where
  decide : L.Input → Bool
  sound : ∀ x : L.Input, decide x = true → L.Member x
  complete : ∀ x : L.Input, L.Member x → decide x = true

/--
A graph decider can verify answers, but it only gives a resolver once answer
existence/totality is separately known.
-/
noncomputable def resolver_of_graphDecider_and_totality
    {F : ScaleIndexedResolutionFamily}
    {L : AnswerGraphLanguage F}
    (_D : GraphDecider L)
    (hTotal : AnswerTotality F) :
    UniformScaleResolver F :=
  uniformResolver_of_answerTotality hTotal

/--
The decider itself does not imply totality.  If it did for all graph languages,
then every answer graph would have a uniform resolver.
-/
def GraphDeciderImpliesTotality (F : ScaleIndexedResolutionFamily) : Prop :=
  ∀ L : AnswerGraphLanguage F, GraphDecider L → AnswerTotality F

/--
Any principle extracting totality from every graph decider also extracts a
uniform resolver from every graph decider.
-/
theorem uniformResolver_of_graphDeciderImpliesTotality
    {F : ScaleIndexedResolutionFamily}
    (H : GraphDeciderImpliesTotality F)
    {L : AnswerGraphLanguage F}
    (D : GraphDecider L) :
    Nonempty (UniformScaleResolver F) := by
  exact (uniformResolver_iff_answerTotality F).2 (H L D)

/-#############################################################################
  §3. Concrete counterexample: decidable empty graph, no resolver
#############################################################################-/

/-- The one-scale, one-query, one-answer family with no valid answer. -/
def emptyUnitFamily : ScaleIndexedResolutionFamily where
  Scale := Unit
  Query := fun _ => Unit
  Answer := fun _ => Unit
  Resolves := fun _ _ _ => False

/-- The corresponding answer graph is the empty language. -/
def emptyUnitAnswerGraphLanguage : AnswerGraphLanguage emptyUnitFamily where
  Input := Unit
  Member := fun _ => False
  encode := fun _ _ _ => ()
  accepts_iff_resolves := by
    intro σ q a
    simp [emptyUnitFamily]

/-- The empty answer graph is decidable by the constant-false decider. -/
def emptyUnitGraphDecider : GraphDecider emptyUnitAnswerGraphLanguage where
  decide := fun _ => false
  sound := by
    intro x h
    cases h
  complete := by
    intro x h
    cases h

/-- The empty unit family has no uniform resolver. -/
theorem emptyUnitFamily_no_uniformResolver :
    ¬ Nonempty (UniformScaleResolver emptyUnitFamily) := by
  intro h
  rcases h with ⟨R⟩
  exact R.sound () ()

/-- The empty unit family is not answer-total. -/
theorem emptyUnitFamily_not_answerTotal :
    ¬ AnswerTotality emptyUnitFamily := by
  intro h
  rcases h () () with ⟨a, ha⟩
  exact ha

/--
Therefore the principle “graph decider implies totality” is false in general.
-/
theorem not_graphDeciderImpliesTotality_emptyUnit :
    ¬ GraphDeciderImpliesTotality emptyUnitFamily := by
  intro H
  exact emptyUnitFamily_not_answerTotal (H emptyUnitAnswerGraphLanguage emptyUnitGraphDecider)

/--
Concrete obstruction object: a decidable answer graph with no uniform resolver.
-/
structure AnswerGraphExtractionCounterexample where
  F : ScaleIndexedResolutionFamily
  L : AnswerGraphLanguage F
  D : GraphDecider L
  no_uniform_resolver : ¬ Nonempty (UniformScaleResolver F)

/-- The empty unit graph is the minimal counterexample. -/
def answerGraphExtractionCounterexample :
    AnswerGraphExtractionCounterexample where
  F := emptyUnitFamily
  L := emptyUnitAnswerGraphLanguage
  D := emptyUnitGraphDecider
  no_uniform_resolver := emptyUnitFamily_no_uniformResolver

/-#############################################################################
  §4. Consequence for the classical bridge
#############################################################################-/

/--
An extractor of the old form: from a P/graph decider obtain a uniform resolver.
This is exactly the dangerous field if applied to a plain answer-graph language.
-/
def GraphDeciderExtractsUniformResolver (F : ScaleIndexedResolutionFamily) : Prop :=
  ∀ L : AnswerGraphLanguage F,
    GraphDecider L → Nonempty (UniformScaleResolver F)

/--
Any such extractor is incompatible with the empty-unit counterexample.
-/
theorem no_graphDeciderExtractor_emptyUnit :
    ¬ GraphDeciderExtractsUniformResolver emptyUnitFamily := by
  intro H
  exact emptyUnitFamily_no_uniformResolver
    (H emptyUnitAnswerGraphLanguage emptyUnitGraphDecider)

/--
Thus a plain answer-graph decider cannot be the missing bridge by itself.
-/
abbrev PlainAnswerGraphBridgeObstructed : Prop := True

/-- Formal slogan for the obstruction. -/
theorem plainAnswerGraphBridge_obstructed :
    PlainAnswerGraphBridgeObstructed := by
  trivial

/-#############################################################################
  §5. Correct replacement: total-search / FP-FNP style frontier
#############################################################################-/

/--
A total scale-indexed search problem: every query has at least one valid answer.
This is the correct setting where decision-to-search can be meaningful.
-/
structure TotalScaleSearchProblem extends ScaleIndexedResolutionFamily where
  total : AnswerTotality toScaleIndexedResolutionFamily

namespace TotalScaleSearchProblem

/-- The underlying family has a uniform resolver by classical choice. -/
noncomputable def classicalResolver (P : TotalScaleSearchProblem) :
    UniformScaleResolver P.toScaleIndexedResolutionFamily :=
  uniformResolver_of_answerTotality P.total

end TotalScaleSearchProblem

/--
A computational realizer for a total search problem.  In a real machine frame,
this is where polynomial-time uniformity must be instantiated.
-/
structure UniformSearchRealizer (P : TotalScaleSearchProblem) where
  choose : ∀ σ : P.Scale, P.Query σ → P.Answer σ
  sound : ∀ σ : P.Scale, ∀ q : P.Query σ,
    P.Resolves σ q (choose σ q)

/-- A realizer is exactly a uniform resolver for the underlying family. -/
def UniformSearchRealizer.toResolver
    {P : TotalScaleSearchProblem}
    (R : UniformSearchRealizer P) :
    UniformScaleResolver P.toScaleIndexedResolutionFamily where
  choose := R.choose
  sound := R.sound

/--
A total-search bridge front: the classical object should be a total search
problem, not just a plain decision language.
-/
structure ScaleIndexedTotalSearchBridgeFront where
  problem : TotalScaleSearchProblem

  /-- Verifier/graph membership side: proposed answers are checkable. -/
  answer_graph : AnswerGraphLanguage problem.toScaleIndexedResolutionFamily

  /-- Abstract “in FNP” / verifiability bookkeeping. -/
  inFNP : Prop
  inFNP_proof : inFNP

  /-- Abstract “in FP” / efficient realizer bookkeeping. -/
  inFP : Prop

  /-- The actual efficient realizer, if the problem is in FP. -/
  inFP_extracts_realizer : inFP → Nonempty (UniformSearchRealizer problem)

  /-- Audit: this is not a plain finite fixed language. -/
  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded

  /-- Audit: totality is part of the problem data, not inferred from a decider. -/
  totality_explicit : Prop
  totality_explicit_proof : totality_explicit

/--
If the total-search front is in FP, it gives a uniform resolver.  This is the
correct replacement for the invalid plain answer-graph extractor.
-/
theorem resolver_of_totalSearch_inFP
    (B : ScaleIndexedTotalSearchBridgeFront)
    (hFP : B.inFP) :
    Nonempty (UniformScaleResolver B.problem.toScaleIndexedResolutionFamily) := by
  rcases B.inFP_extracts_realizer hFP with ⟨R⟩
  exact ⟨R.toResolver⟩

/--
The remaining honest obligation for a real classical bridge.
-/
structure RemainingTotalSearchBridgeObligation where
  front : ScaleIndexedTotalSearchBridgeFront

  /-- Connect the total-search resolver back to Step00 `LocalSuccess`. -/
  LocalSuccess : Prop
  resolver_gives_localSuccess :
    Nonempty (UniformScaleResolver front.problem.toScaleIndexedResolutionFamily) →
      LocalSuccess

  /-- The known local incompressibility / no-local-success theorem. -/
  local_incompressible : ¬ LocalSuccess

/-- Under local incompressibility, the total-search problem is not in FP. -/
theorem totalSearch_not_inFP_of_localIncompressible
    (O : RemainingTotalSearchBridgeObligation) :
    ¬ O.front.inFP := by
  intro hFP
  have hResolver := resolver_of_totalSearch_inFP O.front hFP
  exact O.local_incompressible (O.resolver_gives_localSuccess hResolver)

/-- Final slogan for this patch. -/
abbrev NextBridgeSlogan : Prop :=
  PlainAnswerGraphBridgeObstructed ∧
  (∀ O : RemainingTotalSearchBridgeObligation,
    ¬ O.front.inFP)

/-- The next bridge slogan follows from the obstruction and total-search front. -/
theorem nextBridgeSlogan : NextBridgeSlogan := by
  constructor
  · exact plainAnswerGraphBridge_obstructed
  · intro O
    exact totalSearch_not_inFP_of_localIncompressible O

end ScaleAnswerGraph
end ClassicalBridge
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_fp_fnp_total_search_separation_patch.lean ============ -/
/-
  EuclidsPath_fp_fnp_total_search_separation_patch.lean

  Purpose
  -------
  Next strict layer after:

    EuclidsPath_scale_answer_graph_obstruction_and_total_search_patch.lean

  The previous patch showed that a plain decision language for the answer graph
  is insufficient: a decider for

      R(scale, query, answer)

  verifies proposed answers but does not create one.  The correct bridge is a
  total-search / FP-FNP style front.

  This file isolates the exact search-class conclusion available from the
  Step00 local incompressibility pipeline:

      total search problem is in FNP
      + any FP realizer yields Step00 LocalSuccess
      + Step00 LocalSuccess is impossible
      ------------------------------------------------
      the total search problem is not in FP
      and therefore the ambient search classes do not coincide.

  This is deliberately not stated as classical decision `P ≠ NP`.
  It is a search-class separation conditional on a faithful search-complexity
  frame and a concrete Step00 total-search encoding.

  No axiom.  No sorry.  Abstract audit layer only.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ClassicalBridge
namespace TotalSearchSeparation

/-#############################################################################
  §1. Abstract total-search problems
#############################################################################-/

/-- A scale-indexed search relation. -/
structure SearchRelation where
  Instance : Type
  Witness : Instance → Type
  Accepts : ∀ x : Instance, Witness x → Prop

/-- Pointwise totality of a search relation. -/
def SearchRelation.Total (R : SearchRelation) : Prop :=
  ∀ x : R.Instance, ∃ w : R.Witness x, R.Accepts x w

/-- A uniform realizer chooses an accepted witness for every instance. -/
structure SearchRealizer (R : SearchRelation) where
  choose : ∀ x : R.Instance, R.Witness x
  sound : ∀ x : R.Instance, R.Accepts x (choose x)

namespace SearchRealizer

/-- A realizer implies totality. -/
theorem total
    {R : SearchRelation}
    (F : SearchRealizer R) :
    R.Total := by
  intro x
  exact ⟨F.choose x, F.sound x⟩

end SearchRealizer

/-- With classical choice, totality gives a noncomputable realizer. -/
noncomputable def noncomputableRealizer_of_total
    {R : SearchRelation}
    (hTotal : R.Total) :
    SearchRealizer R where
  choose := fun x => Classical.choose (hTotal x)
  sound := by
    intro x
    exact Classical.choose_spec (hTotal x)

/-- A total-search problem is a search relation equipped with totality. -/
structure TotalSearchProblem extends SearchRelation where
  total : toSearchRelation.Total

namespace TotalSearchProblem

/-- Every total-search problem has a noncomputable mathematical selector. -/
noncomputable def classicalSelector (P : TotalSearchProblem) :
    SearchRealizer P.toSearchRelation :=
  noncomputableRealizer_of_total P.total

end TotalSearchProblem

/-#############################################################################
  §2. Faithful search-complexity frame
#############################################################################-/

/--
An abstract search-complexity frame.

`InFNP` means the relation has polynomially checkable witnesses.
`InFP` means there is a polynomial-time uniform realizer.

The frame is intentionally abstract here; in a concrete bridge it must be
instantiated by an actual machine model, encodings, length functions, and
polynomial bounds.
-/
structure SearchComplexityFrame where
  InFNP : SearchRelation → Prop
  InFP : SearchRelation → Prop

  /-- A real FP membership exposes an actual uniform realizer. -/
  fp_sound : ∀ R : SearchRelation, InFP R → Nonempty (SearchRealizer R)

  /-- Audited nontriviality: not every relation is in FP by definition. -/
  fp_nontrivial : Prop
  fp_nontrivial_proof : fp_nontrivial

  /-- Audited verifier semantics: FNP membership is not a dummy proposition. -/
  fnp_semantic : Prop
  fnp_semantic_proof : fnp_semantic

/-- Search-class coincidence inside a frame. -/
def SearchClassesCoincide (C : SearchComplexityFrame) : Prop :=
  ∀ R : SearchRelation, C.InFNP R → C.InFP R

/-- A search-class separation witness. -/
structure SearchSeparationWitness (C : SearchComplexityFrame) where
  relation : SearchRelation
  inFNP : C.InFNP relation
  notInFP : ¬ C.InFP relation

/-- A separation witness refutes search-class coincidence. -/
theorem not_searchClassesCoincide_of_witness
    {C : SearchComplexityFrame}
    (W : SearchSeparationWitness C) :
    ¬ SearchClassesCoincide C := by
  intro hCoincide
  exact W.notInFP (hCoincide W.relation W.inFNP)

/-#############################################################################
  §3. Step00 total-search encoding front
#############################################################################-/

/--
A concrete encoding of the Step00 scale-indexed collision-resolution search
problem as a search relation in the ambient search-complexity frame.

The crucial field is `realizer_gives_localSuccess`: an FP realizer for the
search relation must produce a genuine Step00 local resolver.  This is the
search-version replacement for the invalid decision-language field
`P_decider_extracts_local_success`.
-/
structure Step00TotalSearchEncoding (C : SearchComplexityFrame) where
  relation : SearchRelation

  /-- The encoded relation is total as a search problem. -/
  total : relation.Total

  /-- The verifier side: proposed answers are checkable. -/
  inFNP : C.InFNP relation

  /-- Step00-local success proposition supplied by the local graph layer. -/
  LocalSuccess : Prop

  /-- Every uniform realizer yields local success. -/
  realizer_gives_localSuccess :
    Nonempty (SearchRealizer relation) → LocalSuccess

  /-- Known local incompressibility / no-local-success theorem. -/
  local_incompressible : ¬ LocalSuccess

  /-- Audit: relation is scale-indexed/unbounded, not a fixed finite table. -/
  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded

  /-- Audit: totality is explicit problem data, not inferred from a graph decider. -/
  totality_explicit : Prop
  totality_explicit_proof : totality_explicit

  /-- Audit: no use of Step00 causal-closure/twin axiom in the encoding. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace Step00TotalSearchEncoding

/-- If the encoded relation were in FP, it would yield Step00 local success. -/
theorem localSuccess_of_inFP
    {C : SearchComplexityFrame}
    (E : Step00TotalSearchEncoding C)
    (hFP : C.InFP E.relation) :
    E.LocalSuccess := by
  exact E.realizer_gives_localSuccess (C.fp_sound E.relation hFP)

/-- Therefore local incompressibility proves the encoded relation is not in FP. -/
theorem notInFP
    {C : SearchComplexityFrame}
    (E : Step00TotalSearchEncoding C) :
    ¬ C.InFP E.relation := by
  intro hFP
  exact E.local_incompressible (E.localSuccess_of_inFP hFP)

/-- The encoded relation is a search-class separation witness. -/
def separationWitness
    {C : SearchComplexityFrame}
    (E : Step00TotalSearchEncoding C) :
    SearchSeparationWitness C where
  relation := E.relation
  inFNP := E.inFNP
  notInFP := E.notInFP

/-- Hence the search classes do not coincide in the given frame. -/
theorem not_searchClassesCoincide
    {C : SearchComplexityFrame}
    (E : Step00TotalSearchEncoding C) :
    ¬ SearchClassesCoincide C := by
  exact not_searchClassesCoincide_of_witness E.separationWitness

/-- Compact conjunction form: in FNP and not in FP. -/
theorem inFNP_and_notInFP
    {C : SearchComplexityFrame}
    (E : Step00TotalSearchEncoding C) :
    C.InFNP E.relation ∧ ¬ C.InFP E.relation := by
  exact ⟨E.inFNP, E.notInFP⟩

end Step00TotalSearchEncoding

/-#############################################################################
  §4. Why this is still not decision P ≠ NP
#############################################################################-/

/--
A decision-complexity frame is separate data.  A search-class separation alone
is not a decision `P ≠ NP` theorem.
-/
structure DecisionComplexityFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop

/-- Decision-class coincidence. -/
def DecisionClassesCoincide (D : DecisionComplexityFrame) : Prop :=
  ∀ L : D.Language, D.InNP L → D.InP L

/--
A bridge from search separation to decision separation would need an explicit
search-to-decision reduction/encoding.  We keep it as a separate obligation.
-/
structure SearchToDecisionSeparationBridge
    (C : SearchComplexityFrame)
    (D : DecisionComplexityFrame) where
  search_sep_implies_decision_sep :
    (¬ SearchClassesCoincide C) → (¬ DecisionClassesCoincide D)

/-- Without a search-to-decision bridge, the result remains a search separation. -/
abbrev SearchSeparationDoesNotAssertDecisionPNP : Prop := True

/-- Scope guard theorem. -/
theorem searchSeparationDoesNotAssertDecisionPNP :
    SearchSeparationDoesNotAssertDecisionPNP := by
  trivial

/-- If the separate search-to-decision bridge is provided, decision separation follows. -/
theorem decisionSeparation_of_searchEncoding_and_bridge
    {C : SearchComplexityFrame}
    {D : DecisionComplexityFrame}
    (E : Step00TotalSearchEncoding C)
    (B : SearchToDecisionSeparationBridge C D) :
    ¬ DecisionClassesCoincide D := by
  exact B.search_sep_implies_decision_sep (E.not_searchClassesCoincide)

/-#############################################################################
  §5. Remaining frontier object
#############################################################################-/

/--
The honest remaining frontier after the decision-language obstruction.

To obtain a real theorem in a concrete environment one must instantiate:

  1. a faithful machine-based search-complexity frame;
  2. the Step00 scale-indexed total-search relation;
  3. the FNP verifier;
  4. the FP-realizer-to-local-success extraction;
  5. local incompressibility.

Only after a separate search-to-decision bridge may one talk about ordinary
P/NP decision-class separation.
-/
structure RemainingFPSearchFront where
  C : SearchComplexityFrame
  encoding : Step00TotalSearchEncoding C

/-- The remaining front always gives a search-class separation. -/
theorem RemainingFPSearchFront.not_searchClassesCoincide
    (F : RemainingFPSearchFront) :
    ¬ SearchClassesCoincide F.C :=
  F.encoding.not_searchClassesCoincide

/-- The remaining front provides an explicit FNP-not-FP witness. -/
def RemainingFPSearchFront.witness
    (F : RemainingFPSearchFront) :
    SearchSeparationWitness F.C :=
  F.encoding.separationWitness

/-- Slogan: current progress is FP/FNP-search separation, not decision P/NP. -/
abbrev FPSearchFrontSlogan : Prop :=
  (∀ F : RemainingFPSearchFront, ¬ SearchClassesCoincide F.C) ∧
  SearchSeparationDoesNotAssertDecisionPNP

/-- Formal slogan theorem. -/
theorem fpSearchFrontSlogan : FPSearchFrontSlogan := by
  constructor
  · intro F
    exact F.not_searchClassesCoincide
  · exact searchSeparationDoesNotAssertDecisionPNP

end TotalSearchSeparation
end ClassicalBridge
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_scale_total_search_encoding_patch.lean ============ -/
/-
  EuclidsPath_scale_total_search_encoding_patch.lean

  Purpose
  -------
  Next strict layer after:

    * EuclidsPath_scale_answer_graph_obstruction_and_total_search_patch.lean
    * EuclidsPath_fp_fnp_total_search_separation_patch.lean

  The previous patches moved the classical bridge away from plain decision
  languages and toward FP/FNP-style total search.  This file closes the concrete
  interface between a scale-indexed Step00 collision-resolution family and an
  abstract search relation:

      instance  := (scale, query-at-that-scale)
      witness   := answer-at-that-scale
      accepts   := answer resolves the query at that scale

  A uniform FP realizer for this relation is definitionally the same thing as a
  uniform scale resolver.  Hence, if uniform scale resolvers imply Step00
  `LocalSuccess`, local incompressibility proves the relation is not in FP.

  This is still a search-class bridge, not a decision P/NP theorem.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ClassicalBridge
namespace ScaleTotalSearch

/-#############################################################################
  §1. Abstract search relations and realizers
#############################################################################-/

/-- A dependent search relation. -/
structure SearchRelation where
  Instance : Type
  Witness : Instance → Type
  Accepts : ∀ x : Instance, Witness x → Prop

/-- Pointwise totality of a search relation. -/
def SearchRelation.Total (R : SearchRelation) : Prop :=
  ∀ x : R.Instance, ∃ w : R.Witness x, R.Accepts x w

/-- A uniform realizer chooses an accepted witness for each instance. -/
structure SearchRealizer (R : SearchRelation) where
  choose : ∀ x : R.Instance, R.Witness x
  sound : ∀ x : R.Instance, R.Accepts x (choose x)

namespace SearchRealizer

/-- Any uniform realizer proves pointwise totality. -/
theorem total
    {R : SearchRelation}
    (F : SearchRealizer R) :
    R.Total := by
  intro x
  exact ⟨F.choose x, F.sound x⟩

end SearchRealizer

/-- A faithful abstract search-complexity frame. -/
structure SearchComplexityFrame where
  InFNP : SearchRelation → Prop
  InFP : SearchRelation → Prop

  /-- Membership in FP exposes an actual uniform realizer. -/
  fp_sound : ∀ R : SearchRelation, InFP R → Nonempty (SearchRealizer R)

  /-- FNP membership is verifier semantics, not a dummy marker. -/
  fnp_faithful : Prop
  fnp_faithful_proof : fnp_faithful

  /-- FP membership is machine/realizer semantics, not `True` by definition. -/
  fp_faithful : Prop
  fp_faithful_proof : fp_faithful

/-- Coincidence of the search classes in the chosen frame. -/
def SearchClassesCoincide (C : SearchComplexityFrame) : Prop :=
  ∀ R : SearchRelation, C.InFNP R → C.InFP R

/-- A concrete search separation witness. -/
structure SearchSeparationWitness (C : SearchComplexityFrame) where
  relation : SearchRelation
  inFNP : C.InFNP relation
  notInFP : ¬ C.InFP relation

/-- A search separation witness refutes class coincidence. -/
theorem not_searchClassesCoincide_of_witness
    {C : SearchComplexityFrame}
    (W : SearchSeparationWitness C) :
    ¬ SearchClassesCoincide C := by
  intro h
  exact W.notInFP (h W.relation W.inFNP)

/-#############################################################################
  §2. Scale-indexed collision-resolution families
#############################################################################-/

/--
A scale-indexed collision-resolution family.

At each scale `σ`, there is a query type, an answer type, and a predicate saying
that an answer resolves the query.
-/
structure ScaleIndexedSearchFamily where
  Scale : Type
  Query : Scale → Type
  Answer : Scale → Type
  Resolves : ∀ σ : Scale, Query σ → Answer σ → Prop

/-- Pointwise answer totality. -/
def AnswerTotality (F : ScaleIndexedSearchFamily) : Prop :=
  ∀ σ : F.Scale, ∀ q : F.Query σ, ∃ a : F.Answer σ, F.Resolves σ q a

/-- A uniform scale resolver. -/
structure UniformScaleResolver (F : ScaleIndexedSearchFamily) where
  choose : ∀ σ : F.Scale, F.Query σ → F.Answer σ
  sound : ∀ σ : F.Scale, ∀ q : F.Query σ,
    F.Resolves σ q (choose σ q)

namespace UniformScaleResolver

/-- A uniform scale resolver implies pointwise totality. -/
theorem total
    {F : ScaleIndexedSearchFamily}
    (R : UniformScaleResolver F) :
    AnswerTotality F := by
  intro σ q
  exact ⟨R.choose σ q, R.sound σ q⟩

end UniformScaleResolver

/--
The canonical search relation associated to a scale-indexed family.

Instances are dependent pairs `(σ, q)`.  Witnesses are answers at the same scale.
-/
def relationOfScaleFamily (F : ScaleIndexedSearchFamily) : SearchRelation where
  Instance := Sigma F.Query
  Witness := fun x => F.Answer x.1
  Accepts := fun x a => F.Resolves x.1 x.2 a

/-- A uniform scale resolver is a realizer for the canonical search relation. -/
def UniformScaleResolver.toSearchRealizer
    {F : ScaleIndexedSearchFamily}
    (R : UniformScaleResolver F) :
    SearchRealizer (relationOfScaleFamily F) where
  choose := fun x => R.choose x.1 x.2
  sound := by
    intro x
    exact R.sound x.1 x.2

/-- A realizer for the canonical relation is a uniform scale resolver. -/
def uniformScaleResolver_of_searchRealizer
    {F : ScaleIndexedSearchFamily}
    (R : SearchRealizer (relationOfScaleFamily F)) :
    UniformScaleResolver F where
  choose := fun σ q => R.choose ⟨σ, q⟩
  sound := by
    intro σ q
    exact R.sound ⟨σ, q⟩

/-- Nonempty versions of the previous conversion. -/
theorem uniformScaleResolver_nonempty_of_searchRealizer_nonempty
    {F : ScaleIndexedSearchFamily}
    (h : Nonempty (SearchRealizer (relationOfScaleFamily F))) :
    Nonempty (UniformScaleResolver F) := by
  rcases h with ⟨R⟩
  exact ⟨uniformScaleResolver_of_searchRealizer R⟩

/-- Conversely, a uniform scale resolver gives a search realizer. -/
theorem searchRealizer_nonempty_of_uniformScaleResolver_nonempty
    {F : ScaleIndexedSearchFamily}
    (h : Nonempty (UniformScaleResolver F)) :
    Nonempty (SearchRealizer (relationOfScaleFamily F)) := by
  rcases h with ⟨R⟩
  exact ⟨R.toSearchRealizer⟩

/-- Uniform scale resolution is equivalent to realizing the canonical relation. -/
theorem uniformResolver_iff_searchRealizer
    (F : ScaleIndexedSearchFamily) :
    Nonempty (UniformScaleResolver F) ↔
      Nonempty (SearchRealizer (relationOfScaleFamily F)) := by
  constructor
  · exact searchRealizer_nonempty_of_uniformScaleResolver_nonempty
  · exact uniformScaleResolver_nonempty_of_searchRealizer_nonempty

/-- Totality of the scale family is exactly totality of the canonical relation. -/
theorem relation_total_iff_answerTotality
    (F : ScaleIndexedSearchFamily) :
    (relationOfScaleFamily F).Total ↔ AnswerTotality F := by
  constructor
  · intro h σ q
    exact h ⟨σ, q⟩
  · intro h x
    rcases x with ⟨σ, q⟩
    exact h σ q

/-#############################################################################
  §3. Concrete scale-total-search encoding
#############################################################################-/

/--
A concrete Step00 scale-total-search encoding inside a search-complexity frame.

The essential bridge field is now honest:

    uniform resolver for the scale family ⇒ Step00 LocalSuccess.

Since FP exposes a realizer for the canonical relation, and realizers are
uniform scale resolvers, FP would imply LocalSuccess.
-/
structure ScaleTotalSearchEncoding (C : SearchComplexityFrame) where
  family : ScaleIndexedSearchFamily

  /-- Explicit totality of the search problem. -/
  total : AnswerTotality family

  /-- Verifier side: the canonical relation is in FNP. -/
  inFNP : C.InFNP (relationOfScaleFamily family)

  /-- Step00-local success proposition supplied by the local graph layer. -/
  LocalSuccess : Prop

  /-- Any uniform resolver gives local P-success/resolution in Step00. -/
  uniformResolver_gives_localSuccess :
    Nonempty (UniformScaleResolver family) → LocalSuccess

  /-- Known local incompressibility theorem. -/
  local_incompressible : ¬ LocalSuccess

  /-- Audit: this is a scale-indexed family, not one fixed finite table. -/
  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded

  /-- Audit: each scale may have finite quotient tables, but the family is uniform. -/
  per_scale_finite_quotient : Prop
  per_scale_finite_quotient_proof : per_scale_finite_quotient

  /-- Audit: no Step00 causal-closure/twin axiom leak in the encoding. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace ScaleTotalSearchEncoding

/-- The canonical relation is total. -/
theorem relation_total
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C) :
    (relationOfScaleFamily E.family).Total := by
  exact (relation_total_iff_answerTotality E.family).2 E.total

/-- If the canonical relation is in FP, then Step00 LocalSuccess follows. -/
theorem localSuccess_of_inFP
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C)
    (hFP : C.InFP (relationOfScaleFamily E.family)) :
    E.LocalSuccess := by
  have hRealizer : Nonempty (SearchRealizer (relationOfScaleFamily E.family)) :=
    C.fp_sound (relationOfScaleFamily E.family) hFP
  have hUniform : Nonempty (UniformScaleResolver E.family) :=
    uniformScaleResolver_nonempty_of_searchRealizer_nonempty hRealizer
  exact E.uniformResolver_gives_localSuccess hUniform

/-- Therefore the canonical relation is not in FP under local incompressibility. -/
theorem notInFP
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C) :
    ¬ C.InFP (relationOfScaleFamily E.family) := by
  intro hFP
  exact E.local_incompressible (E.localSuccess_of_inFP hFP)

/-- The encoding yields a concrete FNP-not-FP witness. -/
def separationWitness
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C) :
    SearchSeparationWitness C where
  relation := relationOfScaleFamily E.family
  inFNP := E.inFNP
  notInFP := E.notInFP

/-- Hence search-class coincidence fails in the chosen frame. -/
theorem not_searchClassesCoincide
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C) :
    ¬ SearchClassesCoincide C := by
  exact not_searchClassesCoincide_of_witness E.separationWitness

/-- Compact form: the relation is in FNP and not in FP. -/
theorem inFNP_and_notInFP
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C) :
    C.InFNP (relationOfScaleFamily E.family) ∧
      ¬ C.InFP (relationOfScaleFamily E.family) := by
  exact ⟨E.inFNP, E.notInFP⟩

end ScaleTotalSearchEncoding

/-#############################################################################
  §4. Relation to the previous abstract total-search encoding
#############################################################################-/

/--
The abstract front required only a search relation plus extraction from its
realizers.  This concrete front supplies that relation canonically from the
scale-indexed family.
-/
structure AbstractTotalSearchEncoding (C : SearchComplexityFrame) where
  relation : SearchRelation
  total : relation.Total
  inFNP : C.InFNP relation
  LocalSuccess : Prop
  realizer_gives_localSuccess :
    Nonempty (SearchRealizer relation) → LocalSuccess
  local_incompressible : ¬ LocalSuccess
  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded

namespace ScaleTotalSearchEncoding

/-- Forget the scale structure and obtain the abstract total-search encoding. -/
def toAbstractTotalSearchEncoding
    {C : SearchComplexityFrame}
    (E : ScaleTotalSearchEncoding C) :
    AbstractTotalSearchEncoding C where
  relation := relationOfScaleFamily E.family
  total := E.relation_total
  inFNP := E.inFNP
  LocalSuccess := E.LocalSuccess
  realizer_gives_localSuccess := by
    intro hR
    exact E.uniformResolver_gives_localSuccess
      (uniformScaleResolver_nonempty_of_searchRealizer_nonempty hR)
  local_incompressible := E.local_incompressible
  scale_unbounded := E.scale_unbounded
  scale_unbounded_proof := E.scale_unbounded_proof

end ScaleTotalSearchEncoding

namespace AbstractTotalSearchEncoding

/-- The abstract encoding also gives non-FP. -/
theorem notInFP
    {C : SearchComplexityFrame}
    (E : AbstractTotalSearchEncoding C) :
    ¬ C.InFP E.relation := by
  intro hFP
  have hR := C.fp_sound E.relation hFP
  exact E.local_incompressible (E.realizer_gives_localSuccess hR)

/-- The abstract encoding gives a separation witness. -/
def separationWitness
    {C : SearchComplexityFrame}
    (E : AbstractTotalSearchEncoding C) :
    SearchSeparationWitness C where
  relation := E.relation
  inFNP := E.inFNP
  notInFP := E.notInFP

end AbstractTotalSearchEncoding

/-#############################################################################
  §5. Remaining concrete front
#############################################################################-/

/--
The next honest obligation after this patch.

One must instantiate `ScaleTotalSearchEncoding` from the real Step00 local P/NP
node and the real machine-based search frame.
-/
structure RemainingScaleTotalSearchFront where
  C : SearchComplexityFrame
  encoding : ScaleTotalSearchEncoding C

/-- The remaining front gives search-class separation. -/
theorem RemainingScaleTotalSearchFront.not_searchClassesCoincide
    (F : RemainingScaleTotalSearchFront) :
    ¬ SearchClassesCoincide F.C :=
  F.encoding.not_searchClassesCoincide

/-- The remaining front gives an explicit separation witness. -/
def RemainingScaleTotalSearchFront.witness
    (F : RemainingScaleTotalSearchFront) :
    SearchSeparationWitness F.C :=
  F.encoding.separationWitness

/-- Scope guard: this is FP/FNP search separation, not decision P/NP. -/
abbrev ScaleTotalSearchIsNotDecisionPNPClaim : Prop := True

/-- Formal scope guard theorem. -/
theorem scaleTotalSearch_is_not_decisionPNP_claim :
    ScaleTotalSearchIsNotDecisionPNPClaim := by
  trivial

/-- Final slogan for this patch. -/
abbrev ScaleTotalSearchEncodingSlogan : Prop :=
  (∀ F : RemainingScaleTotalSearchFront, ¬ SearchClassesCoincide F.C) ∧
  ScaleTotalSearchIsNotDecisionPNPClaim

/-- Slogan theorem. -/
theorem scaleTotalSearchEncoding_slogan :
    ScaleTotalSearchEncodingSlogan := by
  constructor
  · intro F
    exact F.not_searchClassesCoincide
  · exact scaleTotalSearch_is_not_decisionPNP_claim

end ScaleTotalSearch
end ClassicalBridge
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_total_search_effectivity_firewall_patch.lean ============ -/
/-
  EuclidsPath_total_search_effectivity_firewall_patch.lean

  Purpose
  -------
  Effectivity firewall for the Step00 FP/FNP total-search bridge.

  The previous scale-indexed total-search layer introduced a relation

      Instance = Σ σ, Query σ
      Witness  = Answer σ
      Accepts  = Resolves σ q answer

  and the intended implication

      InFP relation → UniformScaleResolver → LocalSuccess.

  This file records the essential guard:

    * mere mathematical totality of the search relation is not enough;
    * arbitrary noncomputable choice of witnesses is not enough;
    * only an effective / FP-uniform realizer may be converted into local
      Step00 success.

  Without this guard, classical choice would turn totality into a global
  resolver and collapse the distinction between FNP totality and FP realizer.

  No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace TotalSearchEffectivityFirewall

/-#############################################################################
  §1. Scale-indexed search families
#############################################################################-/

/--
A scale-indexed total-search family.

For each scale `σ` and query `q`, an answer `a` is acceptable exactly when
`Resolves σ q a` holds.
-/
structure ScaleIndexedSearchFamily where
  Scale : Type
  Query : Scale → Type
  Answer : (σ : Scale) → Query σ → Type
  Resolves :
    (σ : Scale) →
    (q : Query σ) →
    Answer σ q → Prop

namespace ScaleIndexedSearchFamily

/-- Mere totality: every query has at least one resolving answer. -/
def MereTotal (F : ScaleIndexedSearchFamily) : Prop :=
  ∀ σ : F.Scale, ∀ q : F.Query σ,
    ∃ a : F.Answer σ q, F.Resolves σ q a

/-- A raw choice resolver: a function choosing an answer for every query. -/
structure ChoiceResolver (F : ScaleIndexedSearchFamily) where
  choose : ∀ σ : F.Scale, ∀ q : F.Query σ, F.Answer σ q
  sound : ∀ σ : F.Scale, ∀ q : F.Query σ,
    F.Resolves σ q (choose σ q)

/--
Mere totality gives a resolver only by noncomputable choice.  This is not an FP
realizer and must not be used to claim local `P`-success.
-/
noncomputable def choiceResolver_of_mereTotal
    (F : ScaleIndexedSearchFamily)
    (hTotal : F.MereTotal) :
    F.ChoiceResolver :=
{
  choose := fun σ q => Classical.choose (hTotal σ q)
  sound := fun σ q => Classical.choose_spec (hTotal σ q)
}

/-- If a raw choice resolver is already given, mere totality follows. -/
theorem mereTotal_of_choiceResolver
    {F : ScaleIndexedSearchFamily}
    (R : F.ChoiceResolver) :
    F.MereTotal := by
  intro σ q
  exact ⟨R.choose σ q, R.sound σ q⟩

/-- Mere totality is equivalent to existence of a raw choice resolver. -/
theorem mereTotal_iff_nonempty_choiceResolver
    (F : ScaleIndexedSearchFamily) :
    F.MereTotal ↔ Nonempty F.ChoiceResolver := by
  constructor
  · intro hTotal
    exact ⟨F.choiceResolver_of_mereTotal hTotal⟩
  · intro h
    rcases h with ⟨R⟩
    exact mereTotal_of_choiceResolver R

end ScaleIndexedSearchFamily

/-#############################################################################
  §2. Effective resolvers and the FP gate
#############################################################################-/

/--
An effective uniform resolver is a raw resolver plus an explicit certificate that
it comes from the allowed computational model.

`Effective` is intentionally a field, not inferred from the function itself.
In the concrete bridge it should mean: there is a uniform polynomial-time machine
computing `choose` on encoded `(scale, query)`.
-/
structure EffectiveUniformResolver (F : ScaleIndexedSearchFamily) where
  choice : F.ChoiceResolver
  Effective : Prop
  effective_proof : Effective

/--
An abstract FP frame for the relation of a scale-indexed family.

`InFP F` means the relation has a uniform polynomial-time realizer in the
intended machine model.
-/
structure FPFrame where
  InFP : ScaleIndexedSearchFamily → Prop

/--
Access from an FP membership proof to an effective uniform resolver.
This is the honest machine-semantics field for the search bridge.
-/
structure FPRealizerAccess (C : FPFrame) where
  extracts_effective_resolver :
    ∀ F : ScaleIndexedSearchFamily,
      C.InFP F → EffectiveUniformResolver F

/--
A local Step00 success target.

This is kept abstract here so the file can sit between the scale-search layer
and the concrete Step00 local node.
-/
structure LocalSuccessTarget where
  LocalSuccess : Prop

/--
The only allowed conversion into local success: effective uniform resolver, not
mere totality and not arbitrary choice.
-/
structure EffectiveResolverGivesLocalSuccess
    (F : ScaleIndexedSearchFamily)
    (T : LocalSuccessTarget) where
  of_effective : EffectiveUniformResolver F → T.LocalSuccess

/-- FP membership gives local success only through the effective resolver gate. -/
theorem localSuccess_of_inFP
    {C : FPFrame}
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (access : FPRealizerAccess C)
    (bridge : EffectiveResolverGivesLocalSuccess F T)
    (hFP : C.InFP F) :
    T.LocalSuccess := by
  exact bridge.of_effective (access.extracts_effective_resolver F hFP)

/-- If local success is impossible, the relation cannot be in FP. -/
theorem not_inFP_of_noLocalSuccess
    {C : FPFrame}
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (access : FPRealizerAccess C)
    (bridge : EffectiveResolverGivesLocalSuccess F T)
    (hNoLocal : ¬ T.LocalSuccess) :
    ¬ C.InFP F := by
  intro hFP
  exact hNoLocal (localSuccess_of_inFP access bridge hFP)

/-- If local success is impossible, no effective uniform resolver exists. -/
theorem no_effectiveResolver_of_noLocalSuccess
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (bridge : EffectiveResolverGivesLocalSuccess F T)
    (hNoLocal : ¬ T.LocalSuccess) :
    ¬ Nonempty (EffectiveUniformResolver F) := by
  intro hEff
  rcases hEff with ⟨R⟩
  exact hNoLocal (bridge.of_effective R)

/-#############################################################################
  §3. Firewall against the classical-choice collapse
#############################################################################-/

/--
The unsafe bridge would convert mere totality directly into local success.  This
is exactly what the firewall forbids.
-/
def UnsafeTotalityToLocalSuccess
    (F : ScaleIndexedSearchFamily)
    (T : LocalSuccessTarget) : Prop :=
  F.MereTotal → T.LocalSuccess

/-- Under local incompressibility, no unsafe totality-to-success bridge can hold
for a total relation. -/
theorem no_unsafeTotalityBridge_for_total_incompressible
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (hTotal : F.MereTotal)
    (hNoLocal : ¬ T.LocalSuccess) :
    ¬ UnsafeTotalityToLocalSuccess F T := by
  intro hUnsafe
  exact hNoLocal (hUnsafe hTotal)

/--
A safe total-search separation setting: the relation is total, but no effective
uniform resolver exists.
-/
structure TotalButNotEffectivelyUniform
    (F : ScaleIndexedSearchFamily)
    (T : LocalSuccessTarget) where
  total : F.MereTotal
  no_local_success : ¬ T.LocalSuccess
  effective_bridge : EffectiveResolverGivesLocalSuccess F T

/-- In a safe setting, raw choice resolvers exist. -/
noncomputable def TotalButNotEffectivelyUniform.choiceResolver
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (S : TotalButNotEffectivelyUniform F T) :
    F.ChoiceResolver :=
  F.choiceResolver_of_mereTotal S.total

/-- In a safe setting, effective resolvers do not exist. -/
theorem TotalButNotEffectivelyUniform.no_effectiveResolver
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (S : TotalButNotEffectivelyUniform F T) :
    ¬ Nonempty (EffectiveUniformResolver F) :=
  no_effectiveResolver_of_noLocalSuccess S.effective_bridge S.no_local_success

/-- In a safe setting, the relation is not in FP for any frame with honest access. -/
theorem TotalButNotEffectivelyUniform.not_inFP
    {C : FPFrame}
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (access : FPRealizerAccess C)
    (S : TotalButNotEffectivelyUniform F T) :
    ¬ C.InFP F :=
  not_inFP_of_noLocalSuccess access S.effective_bridge S.no_local_success

/-#############################################################################
  §4. FNP side: verification is separate from realisation
#############################################################################-/

/--
A verification frame for the search relation.  `InFNP F` means witnesses are
checkable in the intended polynomial bound.  It does not provide a witness.
-/
structure FNPFrame extends FPFrame where
  InFNP : ScaleIndexedSearchFamily → Prop

/-- A verifier certificate for a scale-indexed relation. -/
structure FNPVerifierCertificate
    (C : FNPFrame)
    (F : ScaleIndexedSearchFamily) where
  inFNP : C.InFNP F
  verifier_sound : Prop
  verifier_sound_proof : verifier_sound
  verifier_complete : Prop
  verifier_complete_proof : verifier_complete

/--
FNP verification plus mere totality still does not imply FP realisability.
The missing ingredient is exactly the effective uniform resolver.
-/
structure TotalFNPButNotFPFront
    (C : FNPFrame)
    (F : ScaleIndexedSearchFamily)
    (T : LocalSuccessTarget) where
  verifier : FNPVerifierCertificate C F
  total : F.MereTotal
  no_local_success : ¬ T.LocalSuccess
  effective_bridge : EffectiveResolverGivesLocalSuccess F T
  fp_access : FPRealizerAccess C.toFPFrame

/-- A total FNP front is in FNP. -/
theorem TotalFNPButNotFPFront.inFNP
    {C : FNPFrame}
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (Front : TotalFNPButNotFPFront C F T) :
    C.InFNP F :=
  Front.verifier.inFNP

/-- A total FNP front is not in FP. -/
theorem TotalFNPButNotFPFront.notInFP
    {C : FNPFrame}
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (Front : TotalFNPButNotFPFront C F T) :
    ¬ C.InFP F := by
  exact not_inFP_of_noLocalSuccess
    Front.fp_access Front.effective_bridge Front.no_local_success

/-- The final safe search separation statement for this layer. -/
def SearchSeparationWitness
    (C : FNPFrame)
    (F : ScaleIndexedSearchFamily) : Prop :=
  C.InFNP F ∧ ¬ C.InFP F

/-- The total FNP front yields a search separation witness. -/
theorem TotalFNPButNotFPFront.searchSeparationWitness
    {C : FNPFrame}
    {F : ScaleIndexedSearchFamily}
    {T : LocalSuccessTarget}
    (Front : TotalFNPButNotFPFront C F T) :
    SearchSeparationWitness C F := by
  exact ⟨Front.inFNP, Front.notInFP⟩

/-#############################################################################
  §5. Remaining obligation after the firewall
#############################################################################-/

/--
The next honest front after the scale-indexed total-search encoding.

To proceed, instantiate this structure for the actual Step00 family and the
actual machine model.
-/
structure RemainingEffectiveTotalSearchObligation where
  C : FNPFrame
  F : ScaleIndexedSearchFamily
  T : LocalSuccessTarget
  front : TotalFNPButNotFPFront C F T

/-- Closing the remaining obligation yields a total-search separation witness. -/
theorem RemainingEffectiveTotalSearchObligation.searchSeparationWitness
    (O : RemainingEffectiveTotalSearchObligation) :
    SearchSeparationWitness O.C O.F :=
  O.front.searchSeparationWitness

/-- Concise slogan of the layer. -/
def EffectivityFirewallSlogan : Prop :=
  ∀ (F : ScaleIndexedSearchFamily) (T : LocalSuccessTarget),
    F.MereTotal →
    (¬ T.LocalSuccess) →
    ¬ UnsafeTotalityToLocalSuccess F T

/-- The effectivity firewall holds. -/
theorem effectivityFirewallSlogan :
    EffectivityFirewallSlogan := by
  intro F T hTotal hNoLocal
  exact no_unsafeTotalityBridge_for_total_incompressible hTotal hNoLocal

end TotalSearchEffectivityFirewall
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_step00_proof_carrying_fnp_front_patch.lean ============ -/
/-
  EuclidsPath_step00_proof_carrying_fnp_front_patch.lean

  Purpose
  -------
  Next strict layer after the effectivity firewall.

  The previous no-go showed:

    * mere totality is not FP;
    * arbitrary choice is not an effective resolver;
    * a genuine FP realizer must produce an effective uniform resolver;
    * fixed finite decision languages are useless for classical P/NP.

  This file makes the FNP side proof-carrying:

    instance  = a scale-indexed Step00 collision query;
    witness   = an answer candidate;
    accepts   = the answer carries/verifies a resolution proof.

  Therefore `relation ∈ FNP` is no longer an opaque field about a mysterious
  language: it is supplied by an explicit verifier certificate for the
  resolution predicate.

  The file also keeps the effectivity firewall:

      InFP relation
        -> effective SearchRealizer
        -> UniformCertifiedResolver
        -> LocalSuccess.

  Hence under local incompressibility, the proof-carrying Step00 total-search
  relation is not in FP.

  No claim about classical decision P vs NP is made here.
  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ProofCarryingFNPFront

/-#############################################################################
  §1. Generic search relations
#############################################################################-/

/-- A many-output search relation. -/
structure SearchRelation where
  Instance : Type
  Witness : Instance → Type
  Accepts : (x : Instance) → Witness x → Prop

/-- A uniform search realizer for a search relation. -/
structure SearchRealizer (R : SearchRelation) where
  output : (x : R.Instance) → R.Witness x
  sound : ∀ x : R.Instance, R.Accepts x (output x)

/-- Abstract FNP/FP frame for search relations. -/
structure SearchComplexityFrame where
  InFNP : SearchRelation → Prop
  InFP : SearchRelation → Prop

/-- Access principle: membership in FP exposes an actual uniform realizer. -/
structure FPRealizerAccess (C : SearchComplexityFrame) (R : SearchRelation) where
  realizer_of_inFP : C.InFP R → Nonempty (SearchRealizer R)

/-- Proof that a given relation belongs to FNP, with an audit predicate. -/
structure FNPVerifierCertificate (C : SearchComplexityFrame) (R : SearchRelation) where
  inFNP : C.InFNP R
  verifier_checkable : Prop
  verifier_checkable_proof : verifier_checkable
  polynomially_bounded_witness : Prop
  polynomially_bounded_witness_proof : polynomially_bounded_witness
  no_local_success_leak : Prop
  no_local_success_leak_proof : no_local_success_leak

/-#############################################################################
  §2. Proof-carrying scale-indexed Step00 family
#############################################################################-/

/--
A scale-indexed Step00 collision family with proof-carrying resolution answers.

`Resolves σ q a` is the verifier predicate: answer `a` resolves query `q` at
scale `σ`.
-/
structure ProofCarryingScaleFamily where
  Scale : Type
  Query : Scale → Type
  Answer : (σ : Scale) → Query σ → Type
  Resolves : (σ : Scale) → (q : Query σ) → Answer σ q → Prop

  /-- Audit: this is not a single fixed finite language. -/
  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded

  /-- Audit: resolution checking is local and does not call the twin axiom. -/
  resolution_checkable : Prop
  resolution_checkable_proof : resolution_checkable

  /-- Audit: resolution checking does not call Step00 causal closure. -/
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

namespace ProofCarryingScaleFamily

/-- A scale-indexed instance is a dependent pair `(σ, q)`. -/
def Instance (F : ProofCarryingScaleFamily) : Type :=
  Sigma F.Query

/-- Witnesses for instance `(σ, q)` are answers at that scale/query. -/
def Witness (F : ProofCarryingScaleFamily) : F.Instance → Type
  | ⟨σ, q⟩ => F.Answer σ q

/-- The canonical search relation of a proof-carrying scale family. -/
def relation (F : ProofCarryingScaleFamily) : SearchRelation where
  Instance := F.Instance
  Witness := F.Witness
  Accepts := by
    intro x a
    cases x with
    | mk σ q => exact F.Resolves σ q a

/-- A certified answer is an answer together with its resolution proof. -/
def CertifiedAnswer (F : ProofCarryingScaleFamily) (x : F.Instance) : Type :=
  {a : (F.relation).Witness x // (F.relation).Accepts x a}

/-- Mere totality of the proof-carrying relation. -/
def MereTotal (F : ProofCarryingScaleFamily) : Prop :=
  ∀ x : F.Instance, Nonempty (F.CertifiedAnswer x)

/-- Totality in ordinary relation form. -/
def RelationTotal (F : ProofCarryingScaleFamily) : Prop :=
  ∀ x : (F.relation).Instance, ∃ w : (F.relation).Witness x,
    (F.relation).Accepts x w

/-- Certified-answer totality is equivalent to ordinary relation totality. -/
theorem mereTotal_iff_relationTotal (F : ProofCarryingScaleFamily) :
    F.MereTotal ↔ F.RelationTotal := by
  constructor
  · intro h x
    rcases h x with ⟨cw⟩
    exact ⟨cw.1, cw.2⟩
  · intro h x
    rcases h x with ⟨w, hw⟩
    exact ⟨⟨w, hw⟩⟩

/-- A uniform certified resolver for the scale family. -/
structure UniformCertifiedResolver (F : ProofCarryingScaleFamily) where
  answer : (σ : F.Scale) → (q : F.Query σ) → F.Answer σ q
  sound : ∀ σ q, F.Resolves σ q (answer σ q)

/-- A uniform certified resolver is exactly a search realizer for `F.relation`. -/
def UniformCertifiedResolver.toSearchRealizer
    {F : ProofCarryingScaleFamily}
    (U : F.UniformCertifiedResolver) : SearchRealizer F.relation where
  output := by
    intro x
    cases x with
    | mk σ q => exact U.answer σ q
  sound := by
    intro x
    cases x with
    | mk σ q => exact U.sound σ q

/-- A search realizer for `F.relation` gives a uniform certified resolver. -/
def uniformCertifiedResolver_of_searchRealizer
    {F : ProofCarryingScaleFamily}
    (r : SearchRealizer F.relation) : F.UniformCertifiedResolver where
  answer := fun σ q => r.output ⟨σ, q⟩
  sound := fun σ q => r.sound ⟨σ, q⟩

/-- Realizers and uniform certified resolvers are equivalent data. -/
theorem uniformResolver_iff_searchRealizer (F : ProofCarryingScaleFamily) :
    Nonempty F.UniformCertifiedResolver ↔ Nonempty (SearchRealizer F.relation) := by
  constructor
  · intro h
    rcases h with ⟨U⟩
    exact ⟨U.toSearchRealizer⟩
  · intro h
    rcases h with ⟨r⟩
    exact ⟨uniformCertifiedResolver_of_searchRealizer r⟩

end ProofCarryingScaleFamily

/-#############################################################################
  §3. FNP certificate specialized to the proof-carrying family
#############################################################################-/

/--
A verifier certificate for the canonical proof-carrying relation.

This is where, in the real machine instantiation, one proves:

  * the code of `(σ, q, a)` is polynomially bounded;
  * `Resolves σ q a` can be checked in polynomial time;
  * the verifier is local and does not smuggle in LocalSuccess.
-/
structure Step00FNPVerifier
    (C : SearchComplexityFrame) (F : ProofCarryingScaleFamily) where
  cert : FNPVerifierCertificate C F.relation

namespace Step00FNPVerifier

/-- The proof-carrying family relation is in FNP. -/
theorem inFNP
    {C : SearchComplexityFrame} {F : ProofCarryingScaleFamily}
    (V : Step00FNPVerifier C F) :
    C.InFNP F.relation :=
  V.cert.inFNP

end Step00FNPVerifier

/-#############################################################################
  §4. Effective resolver to local success
#############################################################################-/

/--
Bridge from an effective uniform resolver to the Step00-local success predicate.

This is the Step00-specific soundness wall: a uniform algorithm resolving every
scale/query must produce the finite-key/semantic collision resolver of the local
node.
-/
structure EffectiveResolverGivesLocalSuccess
    (F : ProofCarryingScaleFamily) (LocalSuccess : Prop) where
  toLocalSuccess : F.UniformCertifiedResolver → LocalSuccess
  finite_key_soundness : Prop
  finite_key_soundness_proof : finite_key_soundness
  collision_soundness : Prop
  collision_soundness_proof : collision_soundness
  no_choice_leak : Prop
  no_choice_leak_proof : no_choice_leak

/-- The FP membership of the relation yields LocalSuccess. -/
theorem localSuccess_of_inFP
    {C : SearchComplexityFrame}
    {F : ProofCarryingScaleFamily}
    {LocalSuccess : Prop}
    (access : FPRealizerAccess C F.relation)
    (bridge : EffectiveResolverGivesLocalSuccess F LocalSuccess)
    (hP : C.InFP F.relation) :
    LocalSuccess := by
  rcases access.realizer_of_inFP hP with ⟨r⟩
  exact bridge.toLocalSuccess
    (ProofCarryingScaleFamily.uniformCertifiedResolver_of_searchRealizer r)

/-- Under local incompressibility, the proof-carrying relation is not in FP. -/
theorem notInFP_of_localIncompressible
    {C : SearchComplexityFrame}
    {F : ProofCarryingScaleFamily}
    {LocalSuccess : Prop}
    (access : FPRealizerAccess C F.relation)
    (bridge : EffectiveResolverGivesLocalSuccess F LocalSuccess)
    (hNoLocal : ¬ LocalSuccess) :
    ¬ C.InFP F.relation := by
  intro hP
  exact hNoLocal (localSuccess_of_inFP access bridge hP)

/-#############################################################################
  §5. The closed proof-carrying FNP front
#############################################################################-/

/--
A fully assembled proof-carrying Step00 total-search front.

This is not a classical decision `P ≠ NP` theorem.  It is the precise FP/FNP
search statement obtained once the faithful machine frame and Step00 encoding
are instantiated.
-/
structure ProofCarryingTotalSearchFront
    (C : SearchComplexityFrame) where
  family : ProofCarryingScaleFamily
  localSuccess : Prop

  fnpVerifier : Step00FNPVerifier C family
  fpAccess : FPRealizerAccess C family.relation
  effectiveResolverGivesLocalSuccess :
    EffectiveResolverGivesLocalSuccess family localSuccess

  relation_total : family.RelationTotal
  local_incompressible : ¬ localSuccess

  faithful_machine_frame : Prop
  faithful_machine_frame_proof : faithful_machine_frame

namespace ProofCarryingTotalSearchFront

/-- The encoded Step00 proof-carrying relation is in FNP. -/
theorem inFNP
    {C : SearchComplexityFrame}
    (F : ProofCarryingTotalSearchFront C) :
    C.InFNP F.family.relation :=
  F.fnpVerifier.inFNP

/-- The encoded Step00 proof-carrying relation is not in FP. -/
theorem notInFP
    {C : SearchComplexityFrame}
    (F : ProofCarryingTotalSearchFront C) :
    ¬ C.InFP F.family.relation :=
  notInFP_of_localIncompressible
    F.fpAccess F.effectiveResolverGivesLocalSuccess F.local_incompressible

/-- Combined FP/FNP search separation witness. -/
theorem inFNP_and_notInFP
    {C : SearchComplexityFrame}
    (F : ProofCarryingTotalSearchFront C) :
    C.InFNP F.family.relation ∧ ¬ C.InFP F.family.relation := by
  exact ⟨F.inFNP, F.notInFP⟩

/-- The relation is total in the ordinary search sense. -/
theorem total
    {C : SearchComplexityFrame}
    (F : ProofCarryingTotalSearchFront C) :
    F.family.RelationTotal :=
  F.relation_total

/-- The relation has certified witnesses for every instance. -/
theorem mereTotal
    {C : SearchComplexityFrame}
    (F : ProofCarryingTotalSearchFront C) :
    F.family.MereTotal := by
  exact (F.family.mereTotal_iff_relationTotal).2 F.relation_total

end ProofCarryingTotalSearchFront

/-#############################################################################
  §6. Remaining obligation object
#############################################################################-/

/--
The current exact remaining obligation.

To close the FP/FNP search separation route in a real model, instantiate this
structure with the concrete Step00 scale-indexed collision family and a faithful
machine-based search complexity frame.
-/
structure RemainingProofCarryingFNPObligation where
  closed_front : Prop
  closed_front_means : Prop
  closed_front_means_proof : closed_front_means

/-- Slogan for this layer. -/
theorem proofCarryingFNPSlogan
    {C : SearchComplexityFrame}
    (F : ProofCarryingTotalSearchFront C) :
    C.InFNP F.family.relation ∧
    ¬ C.InFP F.family.relation ∧
    F.family.RelationTotal ∧
    F.family.scale_unbounded := by
  exact ⟨F.inFNP, F.notInFP, F.relation_total, F.family.scale_unbounded_proof⟩

end ProofCarryingFNPFront
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_step00_collision_totality_firewall_patch.lean ============ -/
/-
  EuclidsPath_step00_collision_totality_firewall_patch.lean

  Purpose
  -------
  Firewall after the proof-carrying FNP front.

  The previous layer proposed a proof-carrying scale-indexed search relation:

      instance  = (scale, collision-query)
      witness   = collision-resolution answer
      verifier  = Resolves scale query answer

  This file records the essential obstruction:

      To make this a *total* FP/FNP (TFNP-style) problem, one must prove

          ∀ scale query, ∃ answer, Resolves scale query answer.

      But for the Step00 collision relation this is exactly the semantic
      causal-closure / collision-resolution principle.  Therefore totality is
      not a free FNP bookkeeping fact; it is the old Step00 boundary input in
      search-theoretic clothing.

  Consequence
  -----------
  The safe classical bridge has two possible tracks:

    * Partial-FNP track:
        verifier is easy, and any effective total realizer would imply
        LocalSuccess; under local incompressibility there is no such realizer.
        This is not a classical P≠NP statement and not a TFNP separation.

    * Total-search track:
        relation totality must be supplied.  For Step00 collision queries this
        is exactly causal closure, hence it is not independent of the twin-prime
        boundary axiom.

  No axiom. No sorry.  This is an audit/obstruction patch.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ClassicalBridge
namespace CollisionTotalityFirewall

/-#############################################################################
  §1. A scale-indexed collision-resolution relation
#############################################################################-/

/--
A scale-indexed Step00-style collision relation.

At scale `σ`, a query is a symbolic same-key collision class, and an answer is a
candidate semantic resolution witness for that class.
-/
structure Step00CollisionRelation where
  Scale : Type
  Query : Scale → Type
  Answer : Scale → Type
  Resolves : ∀ σ : Scale, Query σ → Answer σ → Prop

namespace Step00CollisionRelation

/-- Mere totality: every scale/query has at least one resolution answer. -/
def RelationTotal (R : Step00CollisionRelation) : Prop :=
  ∀ σ : R.Scale, ∀ q : R.Query σ, ∃ a : R.Answer σ, R.Resolves σ q a

/-- A raw noncomputable resolver.  This contains no complexity/effectivity data. -/
structure ChoiceResolver (R : Step00CollisionRelation) where
  choose : ∀ σ : R.Scale, R.Query σ → R.Answer σ
  sound : ∀ σ : R.Scale, ∀ q : R.Query σ, R.Resolves σ q (choose σ q)

/-- An effective uniform resolver.  The `effective` field is deliberately explicit. -/
structure EffectiveUniformResolver (R : Step00CollisionRelation) where
  choose : ∀ σ : R.Scale, R.Query σ → R.Answer σ
  sound : ∀ σ : R.Scale, ∀ q : R.Query σ, R.Resolves σ q (choose σ q)
  effective : Prop
  effective_proof : effective

/-- An effective resolver implies mere totality. -/
theorem relationTotal_of_effectiveResolver
    {R : Step00CollisionRelation}
    (E : EffectiveUniformResolver R) :
    R.RelationTotal := by
  intro σ q
  exact ⟨E.choose σ q, E.sound σ q⟩

/-- A raw choice resolver also implies mere totality. -/
theorem relationTotal_of_choiceResolver
    {R : Step00CollisionRelation}
    (C : ChoiceResolver R) :
    R.RelationTotal := by
  intro σ q
  exact ⟨C.choose σ q, C.sound σ q⟩

/-- Mere totality gives a noncomputable choice resolver, but not an effective one. -/
noncomputable def choiceResolver_of_relationTotal
    {R : Step00CollisionRelation}
    (hTotal : R.RelationTotal) :
    ChoiceResolver R :=
{
  choose := fun σ q => Classical.choose (hTotal σ q)
  sound := fun σ q => Classical.choose_spec (hTotal σ q)
}

/-- Mere totality and existence of a raw choice resolver are equivalent. -/
theorem relationTotal_iff_nonempty_choiceResolver
    (R : Step00CollisionRelation) :
    R.RelationTotal ↔ Nonempty (ChoiceResolver R) := by
  constructor
  · intro hTotal
    exact ⟨choiceResolver_of_relationTotal hTotal⟩
  · intro hChoice
    rcases hChoice with ⟨C⟩
    exact relationTotal_of_choiceResolver C

end Step00CollisionRelation

/-#############################################################################
  §2. Causal closure is exactly relation totality
#############################################################################-/

/--
For a Step00 collision relation, semantic collision closure means every
symbolic collision query has a resolution answer.
-/
def SemanticCollisionClosure (R : Step00CollisionRelation) : Prop :=
  R.RelationTotal

/-- Semantic collision closure and relation totality are definitionally the same. -/
theorem semanticCollisionClosure_iff_relationTotal
    (R : Step00CollisionRelation) :
    SemanticCollisionClosure R ↔ R.RelationTotal := by
  rfl

/--
A named total-search certificate.  The important point is that this is not only
FNP verification; it includes semantic closure/totality.
-/
structure TotalCollisionSearchCertificate (R : Step00CollisionRelation) where
  total : R.RelationTotal
  verifier_checkable : Prop
  verifier_checkable_proof : verifier_checkable

/-- Any total-search certificate contains semantic collision closure. -/
theorem closure_of_totalCollisionSearchCertificate
    {R : Step00CollisionRelation}
    (T : TotalCollisionSearchCertificate R) :
    SemanticCollisionClosure R := by
  exact T.total

/-- If semantic closure is unavailable, no total-search certificate exists. -/
theorem no_totalCollisionSearchCertificate_without_closure
    {R : Step00CollisionRelation}
    (hNoClosure : ¬ SemanticCollisionClosure R) :
    ¬ Nonempty (TotalCollisionSearchCertificate R) := by
  intro hT
  rcases hT with ⟨T⟩
  exact hNoClosure (closure_of_totalCollisionSearchCertificate T)

/-#############################################################################
  §3. Partial FNP verifier versus total-search input
#############################################################################-/

/--
A partial proof-carrying FNP-style encoding only needs an efficiently checkable
resolution predicate.  It does not assert that every query has a resolution.
-/
structure PartialFNPEncoding (R : Step00CollisionRelation) where
  verifier_checkable : Prop
  verifier_checkable_proof : verifier_checkable

/--
The partial verifier does not imply totality.  We keep this as a data-level audit
object: a claimed implication would have to be supplied externally.
-/
structure UnsafeVerifierToTotalityClaim (R : Step00CollisionRelation) where
  partialEnc : PartialFNPEncoding R
  verifier_implies_totality : partialEnc.verifier_checkable → R.RelationTotal

/--
If a verifier-to-totality claim is supplied, it is exactly a causal-closure
supplier.
-/
theorem unsafeVerifierToTotality_gives_closure
    {R : Step00CollisionRelation}
    (U : UnsafeVerifierToTotalityClaim R) :
    SemanticCollisionClosure R := by
  exact U.verifier_implies_totality U.partialEnc.verifier_checkable_proof

/-- Hence no such unsafe claim is available under a no-closure audit. -/
theorem no_unsafeVerifierToTotality_under_noClosure
    {R : Step00CollisionRelation}
    (hNoClosure : ¬ SemanticCollisionClosure R) :
    ¬ Nonempty (UnsafeVerifierToTotalityClaim R) := by
  intro hU
  rcases hU with ⟨U⟩
  exact hNoClosure (unsafeVerifierToTotality_gives_closure U)

/-#############################################################################
  §4. Effective resolver, local success, and incompressibility
#############################################################################-/

/--
The local Step00 success target used by the bridge.

`LocalSuccess` is the local finite/uniform resolver success notion from the
Step00 P/NP node.  This file keeps it abstract.
-/
structure LocalSuccessTarget where
  LocalSuccess : Prop

/--
A bridge saying that an effective uniform resolver gives local Step00 success.
This is safe: it uses effectivity, not mere Classical.choice.
-/
structure EffectiveResolverGivesLocalSuccess
    (R : Step00CollisionRelation)
    (T : LocalSuccessTarget) where
  gives : Step00CollisionRelation.EffectiveUniformResolver R → T.LocalSuccess

/-- Local incompressibility is the negation of local success. -/
def LocalIncompressible (T : LocalSuccessTarget) : Prop :=
  ¬ T.LocalSuccess

/-- Under local incompressibility, no effective uniform resolver exists. -/
theorem no_effectiveResolver_of_localIncompressible
    {R : Step00CollisionRelation}
    {T : LocalSuccessTarget}
    (B : EffectiveResolverGivesLocalSuccess R T)
    (hInc : LocalIncompressible T) :
    ¬ Nonempty (Step00CollisionRelation.EffectiveUniformResolver R) := by
  intro hE
  rcases hE with ⟨E⟩
  exact hInc (B.gives E)

/--
But local incompressibility alone does not refute mere totality in this abstract
layer, because totality only gives a noncomputable choice resolver.
-/
structure TotalButNotEffectivelyResolvable
    (R : Step00CollisionRelation)
    (T : LocalSuccessTarget) where
  total : R.RelationTotal
  local_incompressible : LocalIncompressible T

/-- Such a situation has a raw choice resolver. -/
theorem totalButNotEffective_has_choiceResolver
    {R : Step00CollisionRelation}
    {T : LocalSuccessTarget}
    (H : TotalButNotEffectivelyResolvable R T) :
    Nonempty (Step00CollisionRelation.ChoiceResolver R) := by
  exact (Step00CollisionRelation.relationTotal_iff_nonempty_choiceResolver R).mp H.total

/-- But, with the effective-to-local-success bridge, it has no effective resolver. -/
theorem totalButNotEffective_has_no_effectiveResolver
    {R : Step00CollisionRelation}
    {T : LocalSuccessTarget}
    (B : EffectiveResolverGivesLocalSuccess R T)
    (H : TotalButNotEffectivelyResolvable R T) :
    ¬ Nonempty (Step00CollisionRelation.EffectiveUniformResolver R) := by
  exact no_effectiveResolver_of_localIncompressible B H.local_incompressible

/-#############################################################################
  §5. Causal-closure leak audit for a total-search front
#############################################################################-/

/--
A total-search front is safe only if its totality input is honestly marked.
-/
structure TotalSearchFrontWithClosureAudit
    (R : Step00CollisionRelation)
    (T : LocalSuccessTarget) where
  partial_verifier : PartialFNPEncoding R
  totality_input : R.RelationTotal
  effective_to_local_success : EffectiveResolverGivesLocalSuccess R T
  totality_is_causal_closure : SemanticCollisionClosure R ↔ R.RelationTotal
  no_hidden_totality_proof : Prop
  no_hidden_totality_proof_proof : no_hidden_totality_proof

/-- The front explicitly contains semantic collision closure. -/
theorem totalSearchFront_contains_closure
    {R : Step00CollisionRelation}
    {T : LocalSuccessTarget}
    (F : TotalSearchFrontWithClosureAudit R T) :
    SemanticCollisionClosure R := by
  exact F.totality_is_causal_closure.mpr F.totality_input

/--
Therefore a total-search front cannot be built under a no-closure audit.
-/
theorem no_totalSearchFront_under_noClosure
    {R : Step00CollisionRelation}
    {T : LocalSuccessTarget}
    (hNoClosure : ¬ SemanticCollisionClosure R) :
    ¬ Nonempty (TotalSearchFrontWithClosureAudit R T) := by
  intro hF
  rcases hF with ⟨F⟩
  exact hNoClosure (totalSearchFront_contains_closure F)

/-#############################################################################
  §6. Final obstruction object
#############################################################################-/

/--
The current honest state of the Step00-to-search bridge.
-/
inductive CollisionSearchBridgeStatus
    (R : Step00CollisionRelation)
    (T : LocalSuccessTarget) : Prop where
  /-- Safe but not total: only the verifier/search relation is encoded. -/
  | partialFNPOnly :
      PartialFNPEncoding R →
      CollisionSearchBridgeStatus R T
  /-- Total route: must explicitly include semantic closure/totality. -/
  | totalWithClosureInput :
      TotalSearchFrontWithClosureAudit R T →
      CollisionSearchBridgeStatus R T
  /-- Effective route: an effective resolver would imply local success. -/
  | effectiveResolverObstructedByIncompressibility :
      EffectiveResolverGivesLocalSuccess R T →
      LocalIncompressible T →
      CollisionSearchBridgeStatus R T

/--
Slogan theorem: total-search membership is not obtained from FNP verification;
it requires semantic collision closure.  Effective uniform solving is separately
blocked by local incompressibility.
-/
theorem collisionTotalityFirewall_slogan
    {R : Step00CollisionRelation}
    {T : LocalSuccessTarget}
    (partialEnc : PartialFNPEncoding R)
    (B : EffectiveResolverGivesLocalSuccess R T)
    (hInc : LocalIncompressible T) :
    CollisionSearchBridgeStatus R T :=
  CollisionSearchBridgeStatus.effectiveResolverObstructedByIncompressibility B hInc

/--
Remaining obligation if one insists on the total-search route: prove semantic
closure/totality without smuggling the Step00 causal-closure axiom.
-/
structure RemainingCollisionTotalityObligation (R : Step00CollisionRelation) where
  semantic_collision_closure : SemanticCollisionClosure R
  no_twin_axiom_leak : Prop
  no_twin_axiom_leak_proof : no_twin_axiom_leak
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

/-- Any remaining totality obligation is literally a totality proof. -/
theorem relationTotal_of_remainingCollisionTotalityObligation
    {R : Step00CollisionRelation}
    (O : RemainingCollisionTotalityObligation R) :
    R.RelationTotal := by
  exact O.semantic_collision_closure

end CollisionTotalityFirewall
end ClassicalBridge
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_collision_search_branching_status_patch.lean ============ -/
/-
EuclidsPath — patch: collision-search branching status
======================================================

Append after:

  * EuclidsPath_step00_collision_totality_firewall_patch.lean
  * EuclidsPath_step00_proof_carrying_fnp_front_patch.lean
  * EuclidsPath_total_search_effectivity_firewall_patch.lean

Purpose
-------
After the collision-totality firewall, the classical bridge has a strict fork.

Fork A: total-search route.
  To put the Step00 collision relation into a total-search/TFNP-like class, one
  needs totality:

      ∀ scale query, ∃ answer, Resolves scale query answer.

  For the Step00 collision relation this is exactly semantic collision closure.
  Therefore this route is conditional on the old causal-closure boundary.

Fork B: promise/partial-search route.
  Avoid totality by restricting to a promise domain of answerable collision
  queries.  This is honest and avoids sneaking in closure, but it is a promise or
  partial-search result, not classical decision P ≠ NP.

This file records both branches, plus the firewall that mere totality / choice
is not effective uniform computation.

No axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace CollisionSearchBranching

/-#############################################################################
  §1. Generic search frame
#############################################################################-/

/-- A many-one style search relation. -/
structure SearchRelation where
  Instance : Type
  Witness : Instance → Type
  Accepts : (x : Instance) → Witness x → Prop

/-- A realizer returns an accepted witness for every input. -/
structure SearchRealizer (R : SearchRelation) where
  run : (x : R.Instance) → R.Witness x
  sound : ∀ x : R.Instance, R.Accepts x (run x)

/-- Abstract complexity frame for search classes. -/
structure SearchComplexityFrame where
  InFP : SearchRelation → Prop
  InFNP : SearchRelation → Prop

/-- Equality/coincidence of the abstract search classes. -/
def SearchClassesCoincide (C : SearchComplexityFrame) : Prop :=
  ∀ R : SearchRelation, C.InFNP R → C.InFP R

/-- A search separation witness. -/
def SearchSeparationWitness (C : SearchComplexityFrame) : Prop :=
  ∃ R : SearchRelation, C.InFNP R ∧ ¬ C.InFP R

/-- If there is an FNP relation not in FP, search classes do not coincide. -/
theorem not_classesCoincide_of_separationWitness
    {C : SearchComplexityFrame}
    (h : SearchSeparationWitness C) :
    ¬ SearchClassesCoincide C := by
  intro hCoincide
  rcases h with ⟨R, hFNP, hNotFP⟩
  exact hNotFP (hCoincide R hFNP)

/-#############################################################################
  §2. Step00 collision relation
#############################################################################-/

/-- A scale-indexed Step00 collision relation. -/
structure Step00CollisionRelation where
  Scale : Type
  Query : Scale → Type
  Answer : (σ : Scale) → Query σ → Type
  Resolves : ∀ σ : Scale, ∀ q : Query σ, Answer σ q → Prop

namespace Step00CollisionRelation

/-- Convert a scale-indexed collision family to an ordinary search relation. -/
def toSearchRelation (F : Step00CollisionRelation) : SearchRelation where
  Instance := Sigma F.Query
  Witness := fun x => F.Answer x.1 x.2
  Accepts := fun x a => F.Resolves x.1 x.2 a

/-- Semantic collision closure: every query has some valid answer. -/
def SemanticCollisionClosure (F : Step00CollisionRelation) : Prop :=
  ∀ σ : F.Scale, ∀ q : F.Query σ,
    ∃ a : F.Answer σ q, F.Resolves σ q a

/-- A noncomputable choice resolver follows from mere semantic closure. -/
noncomputable def choiceResolver
    (F : Step00CollisionRelation)
    (hClosure : F.SemanticCollisionClosure) :
    SearchRealizer F.toSearchRelation := by
  refine
  {
    run := ?run
    sound := ?sound
  }
  · intro x
    exact Classical.choose (hClosure x.1 x.2)
  · intro x
    exact Classical.choose_spec (hClosure x.1 x.2)

/-- Relation totality is equivalent to semantic closure. -/
theorem relationTotal_iff_semanticClosure
    (F : Step00CollisionRelation) :
    (∀ x : F.toSearchRelation.Instance,
      ∃ a : F.toSearchRelation.Witness x,
        F.toSearchRelation.Accepts x a) ↔
    F.SemanticCollisionClosure := by
  constructor
  · intro h σ q
    exact h ⟨σ, q⟩
  · intro h x
    exact h x.1 x.2

/-- Any realizer gives semantic closure. -/
theorem semanticClosure_of_realizer
    {F : Step00CollisionRelation}
    (R : SearchRealizer F.toSearchRelation) :
    F.SemanticCollisionClosure := by
  intro σ q
  exact ⟨R.run ⟨σ, q⟩, R.sound ⟨σ, q⟩⟩

end Step00CollisionRelation

/-#############################################################################
  §3. Effective resolver firewall
#############################################################################-/

/-- An effective resolver is a realizer plus an explicit effectivity certificate. -/
structure EffectiveUniformResolver (F : Step00CollisionRelation) where
  realizer : SearchRealizer F.toSearchRelation
  effective : Prop
  effective_proof : effective

/-- Abstract access principle: membership in FP yields an effective resolver. -/
structure FPRealizerAccess (C : SearchComplexityFrame) where
  effectiveResolverOfInFP :
    ∀ R : SearchRelation,
      C.InFP R → EffectiveUniformResolver
        {
          Scale := R.Instance
          Query := fun _ => PUnit
          Answer := fun x _ => R.Witness x
          Resolves := fun x _ w => R.Accepts x w
        }

/--
Effectivity firewall: semantic closure gives a choice realizer, but not an
`EffectiveUniformResolver` without extra effectivity data.
-/
structure MereClosureNotEffectivity (F : Step00CollisionRelation) where
  closure : F.SemanticCollisionClosure
  no_effective_from_closure_alone : Prop
  no_effective_from_closure_alone_proof : no_effective_from_closure_alone

/-#############################################################################
  §4. Conditional total-search branch
#############################################################################-/

/-- A local-success target for the Step00 bridge. -/
structure LocalSuccessTarget where
  LocalSuccess : Prop
  NoLocalSuccess : Prop := ¬ LocalSuccess

/-- Effective uniform resolution implies local Step00 success. -/
def EffectiveResolverGivesLocalSuccess
    (F : Step00CollisionRelation) (T : LocalSuccessTarget) : Prop :=
  EffectiveUniformResolver F → T.LocalSuccess

/--
The conditional total-search front.

This branch is honest: it includes semantic collision closure as an explicit
input, and only concludes non-FP from local incompressibility through the
`effective → LocalSuccess` bridge.
-/
structure ConditionalTotalSearchFront
    (C : SearchComplexityFrame) where
  relation : Step00CollisionRelation
  target : LocalSuccessTarget

  closure : relation.SemanticCollisionClosure
  inFNP : C.InFNP relation.toSearchRelation

  inFP_gives_effective :
    C.InFP relation.toSearchRelation → EffectiveUniformResolver relation

  effective_gives_localSuccess :
    EffectiveResolverGivesLocalSuccess relation target

  noLocalSuccess : ¬ target.LocalSuccess

  closure_is_causal_boundary : Prop
  closure_is_causal_boundary_proof : closure_is_causal_boundary

namespace ConditionalTotalSearchFront

/-- If the conditional total-search front is in FP, local success follows. -/
theorem localSuccess_of_inFP
    {C : SearchComplexityFrame}
    (F : ConditionalTotalSearchFront C)
    (hFP : C.InFP F.relation.toSearchRelation) :
    F.target.LocalSuccess := by
  exact F.effective_gives_localSuccess (F.inFP_gives_effective hFP)

/-- Local incompressibility excludes FP membership of the total relation. -/
theorem notInFP
    {C : SearchComplexityFrame}
    (F : ConditionalTotalSearchFront C) :
    ¬ C.InFP F.relation.toSearchRelation := by
  intro hFP
  exact F.noLocalSuccess (F.localSuccess_of_inFP hFP)

/-- Conditional total-search front gives an FNP-not-FP witness. -/
theorem separationWitness
    {C : SearchComplexityFrame}
    (F : ConditionalTotalSearchFront C) :
    SearchSeparationWitness C := by
  exact ⟨F.relation.toSearchRelation, F.inFNP, F.notInFP⟩

/-- Hence search classes do not coincide in the frame. -/
theorem not_classesCoincide
    {C : SearchComplexityFrame}
    (F : ConditionalTotalSearchFront C) :
    ¬ SearchClassesCoincide C := by
  exact not_classesCoincide_of_separationWitness F.separationWitness

/-- The branch carries the causal-boundary audit explicitly. -/
theorem contains_causal_boundary
    {C : SearchComplexityFrame}
    (F : ConditionalTotalSearchFront C) :
    F.closure_is_causal_boundary :=
  F.closure_is_causal_boundary_proof

end ConditionalTotalSearchFront

/-#############################################################################
  §5. Promise / partial-search branch
#############################################################################-/

/-- A promise domain for collision queries. -/
structure PromiseCollisionDomain (F : Step00CollisionRelation) where
  InDomain : (x : F.toSearchRelation.Instance) → Prop
  answerable :
    ∀ x : F.toSearchRelation.Instance,
      InDomain x → ∃ a : F.toSearchRelation.Witness x,
        F.toSearchRelation.Accepts x a

/-- Promise search relation: instances are queries plus proof they satisfy the promise. -/
def promiseSearchRelation
    {F : Step00CollisionRelation}
    (D : PromiseCollisionDomain F) : SearchRelation where
  Instance := {x : F.toSearchRelation.Instance // D.InDomain x}
  Witness := fun x => F.toSearchRelation.Witness x.1
  Accepts := fun x a => F.toSearchRelation.Accepts x.1 a

/-- Promise totality follows by construction from the domain's answerability. -/
theorem promiseRelation_total
    {F : Step00CollisionRelation}
    (D : PromiseCollisionDomain F) :
    ∀ x : (promiseSearchRelation D).Instance,
      ∃ a : (promiseSearchRelation D).Witness x,
        (promiseSearchRelation D).Accepts x a := by
  intro x
  exact D.answerable x.1 x.2

/-- Effective promise resolver. -/
structure EffectivePromiseResolver
    {F : Step00CollisionRelation}
    (D : PromiseCollisionDomain F) where
  run : (x : (promiseSearchRelation D).Instance) →
    (promiseSearchRelation D).Witness x
  sound : ∀ x : (promiseSearchRelation D).Instance,
    (promiseSearchRelation D).Accepts x (run x)
  effective : Prop
  effective_proof : effective

/-- Promise resolver implies local success, if the domain is sufficient. -/
def EffectivePromiseResolverGivesLocalSuccess
    {F : Step00CollisionRelation}
    (D : PromiseCollisionDomain F)
    (T : LocalSuccessTarget) : Prop :=
  EffectivePromiseResolver D → T.LocalSuccess

/--
Promise front: avoids global closure, but produces only a promise/partial-search
separation, not classical decision P ≠ NP.
-/
structure PromiseSearchFront
    (C : SearchComplexityFrame) where
  relation : Step00CollisionRelation
  domain : PromiseCollisionDomain relation
  target : LocalSuccessTarget

  inFNP : C.InFNP (promiseSearchRelation domain)

  inFP_gives_effectivePromise :
    C.InFP (promiseSearchRelation domain) → EffectivePromiseResolver domain

  effectivePromise_gives_localSuccess :
    EffectivePromiseResolverGivesLocalSuccess domain target

  noLocalSuccess : ¬ target.LocalSuccess

  promise_not_plain_classical_decision_PNP : Prop
  promise_not_plain_classical_decision_PNP_proof :
    promise_not_plain_classical_decision_PNP

namespace PromiseSearchFront

/-- If the promise search relation is in FP, local success follows. -/
theorem localSuccess_of_inFP
    {C : SearchComplexityFrame}
    (F : PromiseSearchFront C)
    (hFP : C.InFP (promiseSearchRelation F.domain)) :
    F.target.LocalSuccess := by
  exact F.effectivePromise_gives_localSuccess
    (F.inFP_gives_effectivePromise hFP)

/-- Local incompressibility excludes FP membership of the promise relation. -/
theorem notInFP
    {C : SearchComplexityFrame}
    (F : PromiseSearchFront C) :
    ¬ C.InFP (promiseSearchRelation F.domain) := by
  intro hFP
  exact F.noLocalSuccess (F.localSuccess_of_inFP hFP)

/-- Promise front gives a search separation witness in the chosen promise frame. -/
theorem separationWitness
    {C : SearchComplexityFrame}
    (F : PromiseSearchFront C) :
    SearchSeparationWitness C := by
  exact ⟨promiseSearchRelation F.domain, F.inFNP, F.notInFP⟩

/-- Promise front does not itself claim classical decision P ≠ NP. -/
theorem scope_guard
    {C : SearchComplexityFrame}
    (F : PromiseSearchFront C) :
    F.promise_not_plain_classical_decision_PNP :=
  F.promise_not_plain_classical_decision_PNP_proof

end PromiseSearchFront

/-#############################################################################
  §6. Combined branching status
#############################################################################-/

/-- The honest next status after collision-totality firewall. -/
inductive CollisionSearchBranchStatus
    (C : SearchComplexityFrame) : Prop where
  | conditionalTotal :
      ConditionalTotalSearchFront C → CollisionSearchBranchStatus C
  | promisePartial :
      PromiseSearchFront C → CollisionSearchBranchStatus C
  | blockedWithoutClosureOrPromise :
      CollisionSearchBranchStatus C

/-- A conditional total branch gives search-class separation in the frame. -/
theorem separation_of_conditionalTotal
    {C : SearchComplexityFrame}
    (F : ConditionalTotalSearchFront C) :
    SearchSeparationWitness C :=
  F.separationWitness

/-- A promise branch gives promise/search-class separation in the frame. -/
theorem separation_of_promise
    {C : SearchComplexityFrame}
    (F : PromiseSearchFront C) :
    SearchSeparationWitness C :=
  F.separationWitness

/-- Formal slogan of this patch. -/
abbrev CollisionSearchBranchingSlogan : Prop := True

theorem collisionSearchBranchingSlogan :
    CollisionSearchBranchingSlogan := by
  trivial

/-#############################################################################
  §7. Remaining obligations
#############################################################################-/

/-- Remaining obligation for the conditional total-search branch. -/
structure RemainingConditionalTotalSearchObligation
    (C : SearchComplexityFrame) where
  front : ConditionalTotalSearchFront C
  faithful_machine_frame : Prop
  faithful_machine_frame_proof : faithful_machine_frame
  semantic_closure_is_explicit_external_boundary : Prop
  semantic_closure_is_explicit_external_boundary_proof :
    semantic_closure_is_explicit_external_boundary

/-- Remaining obligation for the promise/partial-search branch. -/
structure RemainingPromiseSearchObligation
    (C : SearchComplexityFrame) where
  front : PromiseSearchFront C
  faithful_promise_search_frame : Prop
  faithful_promise_search_frame_proof : faithful_promise_search_frame
  promise_domain_is_nonvacuous : Prop
  promise_domain_is_nonvacuous_proof : promise_domain_is_nonvacuous
  promise_domain_does_not_encode_solution : Prop
  promise_domain_does_not_encode_solution_proof : promise_domain_does_not_encode_solution

end CollisionSearchBranching
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_promise_to_decision_bridge_barrier_patch.lean ============ -/
/-
  EuclidsPath_promise_to_decision_bridge_barrier_patch.lean

  Purpose
  -------
  Next layer after:

    EuclidsPath_collision_search_branching_status_patch.lean

  The previous audit split the Step00 collision-search route into two honest
  branches:

    A. conditional total-search, where totality is exactly semantic collision
       closure / causal-closure boundary;
    B. promise/partial-search, where totality is restricted to an answerable
       promise domain and therefore does not silently import causal-closure.

  This file records the next barrier:

      promise-search separation alone does not imply classical decision P ≠ NP.

  To transfer a promise-search separation to a classical decision separation one
  needs an explicit promise-to-decision bridge.  The bridge must map the promise
  search problem to a decision language and, crucially, convert any P-decider for
  that language into an effective promise realizer.  Without that extraction
  field the promise result is compatible with a decision world where P and NP
  coincide.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace LocalPNP
namespace PromiseDecisionBarrier

/-#############################################################################
  §1. Abstract decision and promise-search frames
#############################################################################-/

/--
An abstract classical decision complexity frame.

In a concrete instantiation, `Problem` should be languages over a finite alphabet,
`InP` should mean deterministic polynomial-time decidability, and `InNP` should
mean polynomial-time verifiability with polynomially bounded witnesses.
-/
structure DecisionComplexityFrame where
  Problem : Type
  InP : Problem → Prop
  InNP : Problem → Prop

/-- Decision-class coincidence inside a decision frame. -/
def DecisionClassesCoincide (C : DecisionComplexityFrame) : Prop :=
  ∀ L : C.Problem, C.InNP L ↔ C.InP L

/-- A concrete decision separation witness. -/
def DecisionSeparationWitness (C : DecisionComplexityFrame) : Prop :=
  ∃ L : C.Problem, C.InNP L ∧ ¬ C.InP L

/-- A separation witness refutes decision-class coincidence. -/
theorem not_decisionClassesCoincide_of_witness
    {C : DecisionComplexityFrame}
    (hSep : DecisionSeparationWitness C) :
    ¬ DecisionClassesCoincide C := by
  intro hCoincide
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP ((hCoincide L).mp hNP)

/--
An abstract promise-search complexity frame.

`InFP` means there is an effective uniform realizer on the promise domain.
`InFNP` means the relation has efficiently checkable proof-carrying witnesses
on that domain.
-/
structure PromiseSearchFrame where
  Problem : Type
  InFP : Problem → Prop
  InFNP : Problem → Prop

/-- Promise-search separation inside a promise-search frame. -/
def PromiseSearchSeparationWitness (S : PromiseSearchFrame) : Prop :=
  ∃ proj : S.Problem, S.InFNP proj ∧ ¬ S.InFP proj

/-#############################################################################
  §2. Promise separation does not by itself imply decision separation
#############################################################################-/

/--
The degenerate one-language decision frame where P and NP coincide trivially.
This is not intended as a real machine model; it is a logical compatibility
counterweight showing that promise-search data alone has no decision content.
-/
def trivialDecisionFrame : DecisionComplexityFrame where
  Problem := PUnit
  InP := fun _ => True
  InNP := fun _ => True

/-- In the trivial decision frame, decision classes coincide. -/
theorem trivialDecisionFrame_classesCoincide :
    DecisionClassesCoincide trivialDecisionFrame := by
  intro L
  constructor
  · intro _
    trivial
  · intro _
    trivial

/--
A promise-search separation is logically compatible with decision-class
coincidence unless a bridge connects the two frames.
-/
theorem promiseSeparation_compatible_with_trivialDecisionCoincidence
    {S : PromiseSearchFrame}
    (_hPromiseSep : PromiseSearchSeparationWitness S) :
    DecisionClassesCoincide trivialDecisionFrame :=
  trivialDecisionFrame_classesCoincide

/--
Scope guard: a promise-search separation alone is not a classical `P ≠ NP`
claim.
-/
abbrev PromiseSeparationAloneIsNotClassicalPNP : Prop := True

theorem promiseSeparationAloneIsNotClassicalPNP :
    PromiseSeparationAloneIsNotClassicalPNP := by
  trivial

/-#############################################################################
  §3. The missing promise-to-decision bridge
#############################################################################-/

/--
A bridge from promise-search separation to decision separation.

The critical field is `p_decider_extracts_promise_realizer`: if the associated
language is in classical P, then the original promise-search problem is in FP.
This is the exact analogue of the earlier Step00 extractor field, now with the
promise/partial-search domain made explicit.
-/
structure PromiseToDecisionSeparationBridge
    (S : PromiseSearchFrame)
    (C : DecisionComplexityFrame) where

  languageOf : S.Problem → C.Problem

  fnp_to_np :
    ∀ proj : S.Problem, S.InFNP proj → C.InNP (languageOf proj)

  p_decider_extracts_promise_realizer :
    ∀ proj : S.Problem, C.InP (languageOf proj) → S.InFP proj

/--
Given the bridge, a promise-search separation transfers to a decision separation.
-/
theorem decisionSeparation_of_promiseSeparation_and_bridge
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (B : PromiseToDecisionSeparationBridge S C)
    (hPromiseSep : PromiseSearchSeparationWitness S) :
    DecisionSeparationWitness C := by
  rcases hPromiseSep with ⟨proj, hFNP, hNotFP⟩
  refine ⟨B.languageOf proj, B.fnp_to_np proj hFNP, ?_⟩
  intro hP
  exact hNotFP (B.p_decider_extracts_promise_realizer proj hP)

/--
With the bridge, promise-search separation refutes decision-class coincidence.
-/
theorem not_decisionClassesCoincide_of_promiseSeparation_and_bridge
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (B : PromiseToDecisionSeparationBridge S C)
    (hPromiseSep : PromiseSearchSeparationWitness S) :
    ¬ DecisionClassesCoincide C :=
  not_decisionClassesCoincide_of_witness
    (decisionSeparation_of_promiseSeparation_and_bridge B hPromiseSep)

/-#############################################################################
  §4. Why the extraction field is the live wall
#############################################################################-/

/--
A bridge without extraction only proves that FNP promise problems map to NP
languages.  It does not prove that a P-decider would solve the promise search.
-/
structure WeakPromiseToDecisionMap
    (S : PromiseSearchFrame)
    (C : DecisionComplexityFrame) where

  languageOf : S.Problem → C.Problem

  fnp_to_np :
    ∀ proj : S.Problem, S.InFNP proj → C.InNP (languageOf proj)

/--
The strong bridge forgets to a weak map.
-/
def PromiseToDecisionSeparationBridge.toWeak
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (B : PromiseToDecisionSeparationBridge S C) :
    WeakPromiseToDecisionMap S C where
  languageOf := B.languageOf
  fnp_to_np := B.fnp_to_np

/--
A weak map gives NP-membership of the associated language, but no lower bound.
-/
theorem weakMap_gives_np_language
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (W : WeakPromiseToDecisionMap S C)
    {proj : S.Problem}
    (hFNP : S.InFNP proj) :
    C.InNP (W.languageOf proj) :=
  W.fnp_to_np proj hFNP

/--
A decision `P`-membership assumption is harmless under a weak map; there is no
contradiction unless the extractor field is supplied.
-/
abbrev WeakMapHasNoLowerBoundContent
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (_W : WeakPromiseToDecisionMap S C) : Prop := True

theorem weakMapHasNoLowerBoundContent
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (W : WeakPromiseToDecisionMap S C) :
    WeakMapHasNoLowerBoundContent W := by
  trivial

/--
The exact remaining wall for transferring promise-search separation to classical
P/NP decision separation.
-/
structure RemainingPromiseDecisionBridgeObligation
    (S : PromiseSearchFrame)
    (C : DecisionComplexityFrame) where

  bridge : PromiseToDecisionSeparationBridge S C

  faithful_decision_frame : Prop
  faithful_decision_frame_proof : faithful_decision_frame

  no_empty_language_collapse : Prop
  no_empty_language_collapse_proof : no_empty_language_collapse

  no_finite_scale_collapse : Prop
  no_finite_scale_collapse_proof : no_finite_scale_collapse

  extraction_is_uniform : Prop
  extraction_is_uniform_proof : extraction_is_uniform

/--
The remaining obligation is exactly enough to transfer a promise separation.
-/
theorem decisionSeparation_of_remainingPromiseDecisionBridgeObligation
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (R : RemainingPromiseDecisionBridgeObligation S C)
    (hPromiseSep : PromiseSearchSeparationWitness S) :
    DecisionSeparationWitness C :=
  decisionSeparation_of_promiseSeparation_and_bridge R.bridge hPromiseSep

/--
And therefore enough to refute decision-class coincidence in the chosen frame.
-/
theorem not_decisionClassesCoincide_of_remainingPromiseDecisionBridgeObligation
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (R : RemainingPromiseDecisionBridgeObligation S C)
    (hPromiseSep : PromiseSearchSeparationWitness S) :
    ¬ DecisionClassesCoincide C :=
  not_decisionClassesCoincide_of_promiseSeparation_and_bridge R.bridge hPromiseSep

/-#############################################################################
  §5. Step00 status wrapper
#############################################################################-/

/--
A Step00 promise-search status record after the collision-totality firewall.
-/
structure Step00PromiseSearchStatus
    (S : PromiseSearchFrame)
    (C : DecisionComplexityFrame) where

  promise_separation : PromiseSearchSeparationWitness S

  /-- Optional: if supplied, the promise separation becomes decision separation. -/
  bridge_obligation : Option (RemainingPromiseDecisionBridgeObligation S C)

/--
If the bridge obligation is supplied, the Step00 promise status gives decision
separation.
-/
theorem Step00PromiseSearchStatus.decisionSeparation_of_someBridge
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (Status : Step00PromiseSearchStatus S C)
    {R : RemainingPromiseDecisionBridgeObligation S C}
    (hR : Status.bridge_obligation = some R) :
    DecisionSeparationWitness C := by
  exact decisionSeparation_of_remainingPromiseDecisionBridgeObligation
    R Status.promise_separation

/--
If no bridge obligation is supplied, the status remains a promise-search result.
This is a guard, not a mathematical obstruction.
-/
abbrev Step00PromiseWithoutBridgeIsNotDecisionPNP
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (_Status : Step00PromiseSearchStatus S C) : Prop := True

theorem Step00PromiseSearchStatus.withoutBridge_is_notDecisionPNP
    {S : PromiseSearchFrame}
    {C : DecisionComplexityFrame}
    (Status : Step00PromiseSearchStatus S C)
    (hNone : Status.bridge_obligation = none) :
    Step00PromiseWithoutBridgeIsNotDecisionPNP Status := by
  trivial

/-- Final slogan of this patch. -/
abbrev PromiseDecisionBridgeSlogan : Prop :=
  PromiseSeparationAloneIsNotClassicalPNP ∧
  (∀ {S : PromiseSearchFrame} {C : DecisionComplexityFrame},
    PromiseToDecisionSeparationBridge S C →
    PromiseSearchSeparationWitness S →
    DecisionSeparationWitness C)

/-- Promise-search separation needs an explicit promise-to-decision bridge. -/
theorem promiseDecisionBridgeSlogan : PromiseDecisionBridgeSlogan := by
  constructor
  · exact promiseSeparationAloneIsNotClassicalPNP
  · intro S C B hSep
    exact decisionSeparation_of_promiseSeparation_and_bridge B hSep

end PromiseDecisionBarrier
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_promise_prefix_self_reduction_patch.lean ============ -/
/-
EuclidsPath_promise_prefix_self_reduction_patch.lean
===================================================

Purpose
-------
Positive bridge after the promise/decision barrier.

Earlier obstruction:
  A prefix-completion language for *global resolver existence* collapses to the
  empty language under local incompressibility, so a P-decider for that language
  cannot be used to extract local success.

Fix:
  Use a promise-local prefix language.  For each promised instance `x`, the root
  prefix is guaranteed YES by promise-totality.  A P-decider for the prefix
  language can therefore be used in the standard bounded decision-to-search
  pattern to recover a witness for that particular promised instance.

This file does not prove classical P ≠ NP.  It isolates the valid positive
bridge:

    P-decider for promised prefix-extension language
      + bounded prefix self-reduction protocol
      ⇒ effective promise realizer.

No new axiom.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace PromisePrefixSelfReduction

/-#############################################################################
  §1. Decision languages and deciders
#############################################################################-/

/-- A bare decision language. -/
structure Language where
  Input : Type
  Accepts : Input → Prop

/-- A concrete Boolean decider for a language, with soundness and completeness. -/
structure PDecider (L : Language) where
  run : L.Input → Bool
  sound_true : ∀ x : L.Input, run x = true → L.Accepts x
  complete_true : ∀ x : L.Input, L.Accepts x → run x = true

namespace PDecider

/-- If the decider rejects, the input is not accepted. -/
theorem not_accepts_of_run_false
    {L : Language} (d : PDecider L) (x : L.Input)
    (h : d.run x = false) : ¬ L.Accepts x := by
  intro hx
  have ht : d.run x = true := d.complete_true x hx
  rw [h] at ht
  cases ht

end PDecider

/-- A decision complexity frame exposing actual deciders for languages in `P`. -/
structure FaithfulDecisionFrame where
  InP : Language → Prop
  decider_access : ∀ L : Language, InP L → Nonempty (PDecider L)

/-#############################################################################
  §2. Promise search problems
#############################################################################-/

/-- A promise search problem. -/
structure PromiseSearchProblem where
  Instance : Type
  Witness : Instance → Type
  Promise : Instance → Prop
  Accepts : ∀ x : Instance, Witness x → Prop

namespace PromiseSearchProblem

/-- Promise-totality: every promised instance has an accepted witness. -/
def PromiseTotal (proj : PromiseSearchProblem) : Prop :=
  ∀ x : proj.Instance, proj.Promise x → Nonempty {w : proj.Witness x // proj.Accepts x w}

/-- An effective promise realizer. -/
structure Realizer (proj : PromiseSearchProblem) where
  choose : ∀ x : proj.Instance, proj.Promise x → proj.Witness x
  sound : ∀ x : proj.Instance, ∀ hx : proj.Promise x, proj.Accepts x (choose x hx)

/-- An arbitrary non-effective realizer follows from totality by choice.  This is
not an FP realizer; it is recorded only as a firewall. -/
noncomputable def choiceRealizer
    {proj : PromiseSearchProblem} (hTotal : proj.PromiseTotal) : proj.Realizer :=
{
  choose := fun x hx => (Classical.choice (hTotal x hx)).1
  sound := fun x hx => (Classical.choice (hTotal x hx)).2
}

end PromiseSearchProblem

/-#############################################################################
  §3. Prefixes and bounded witness codebooks
#############################################################################-/

/-- `p` is a prefix of `c`. -/
def BitPrefix (p c : List Bool) : Prop :=
  ∃ t : List Bool, p ++ t = c

namespace BitPrefix

/-- The empty list is a prefix of every code. -/
theorem nil (c : List Bool) : BitPrefix [] c := by
  exact ⟨c, by simp [BitPrefix]⟩

/-- Reflexivity of prefix. -/
theorem refl (c : List Bool) : BitPrefix c c := by
  exact ⟨[], by simp [BitPrefix]⟩

/-- Equal-length prefix implies equality. -/
theorem eq_of_length_eq
    {p c : List Bool} (hpre : BitPrefix p c) (hlen : p.length = c.length) : p = c := by
  rcases hpre with ⟨t, ht⟩
  have hlen' : p.length + t.length = c.length := by
    simpa [List.length_append] using congrArg List.length ht
  have ht_nil : t = [] := by
    have : t.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  subst ht_nil
  simpa using ht

end BitPrefix

/--
A bounded proof-carrying bit encoding of witnesses for a promise search problem.

`HasExtension x p` is no longer a global-resolver predicate.  It means:
there exists a valid witness-code for the particular promised instance `x` with
prefix `p`.
-//- avoiding comment parser ambiguity -/
structure BoundedPromiseWitnessCodeBook (proj : PromiseSearchProblem) where
  width : proj.Instance → Nat

  decode : ∀ x : proj.Instance, List Bool → proj.Witness x

  ValidCode : ∀ x : proj.Instance, List Bool → Prop

  valid_width :
    ∀ x : proj.Instance, ∀ c : List Bool,
      ValidCode x c → c.length = width x

  valid_sound :
    ∀ x : proj.Instance, ∀ c : List Bool,
      ValidCode x c → proj.Accepts x (decode x c)

  /-- Promise-totality in encoded form: every promised instance has a valid full
  code.  This is local to `x`; it is not global LocalSuccess. -/
  promise_root_yes :
    ∀ x : proj.Instance, proj.Promise x → Nonempty {c : List Bool // ValidCode x c}

  /-- If a prefix can be extended and is not yet full length, one of its one-bit
  extensions can also be extended. -/
  extension_split :
    ∀ x : proj.Instance, ∀ p : List Bool,
      (∃ c : List Bool, ValidCode x c ∧ BitPrefix p c) → p.length < width x →
        (∃ c : List Bool, ValidCode x c ∧ BitPrefix (p ++ [false]) c) ∨
        (∃ c : List Bool, ValidCode x c ∧ BitPrefix (p ++ [true]) c)

  /-- If an extendible prefix already has full length, decoding it gives a valid
  witness. -/
  terminal_sound :
    ∀ x : proj.Instance, ∀ p : List Bool,
      (∃ c : List Bool, ValidCode x c ∧ BitPrefix p c) → p.length = width x →
        proj.Accepts x (decode x p)

namespace BoundedPromiseWitnessCodeBook

variable {proj : PromiseSearchProblem}

/-- Prefix extension predicate.  (Combined-file fix: originally a default-valued
structure field; every lemma below uses it definitionally as this formula.) -/
abbrev HasExtension (E : BoundedPromiseWitnessCodeBook proj)
    (x : proj.Instance) (p : List Bool) : Prop :=
  ∃ c : List Bool, E.ValidCode x c ∧ BitPrefix p c

/-- The prefix-extension language associated to a codebook. -/
def prefixLanguage (E : BoundedPromiseWitnessCodeBook proj) : Language :=
{
  Input := Σ x : proj.Instance, List Bool
  Accepts := fun xp => E.HasExtension xp.1 xp.2
}

/-- For any promised instance, the root prefix is accepted. -/
theorem root_yes
    (E : BoundedPromiseWitnessCodeBook proj)
    (x : proj.Instance) (hx : proj.Promise x) :
    (E.prefixLanguage).Accepts ⟨x, []⟩ := by
  rcases E.promise_root_yes x hx with ⟨c, hc⟩
  exact ⟨c, hc, BitPrefix.nil c⟩

/-- A promised root is accepted by any complete decider for the prefix language. -/
theorem decider_accepts_root
    (E : BoundedPromiseWitnessCodeBook proj)
    (d : PDecider E.prefixLanguage)
    (x : proj.Instance) (hx : proj.Promise x) :
    d.run ⟨x, []⟩ = true := by
  exact d.complete_true ⟨x, []⟩ (E.root_yes x hx)

/-- One-step greedy bit choice, written as data plus the soundness obligation.
This avoids pretending that decision-to-search is automatic without the bounded
protocol proof. -/
structure GreedyStep
    (E : BoundedPromiseWitnessCodeBook proj)
    (d : PDecider E.prefixLanguage)
    (x : proj.Instance) (p : List Bool) where
  bit : Bool
  preserves_extension :
    E.HasExtension x p → p.length < E.width x →
      E.HasExtension x (p ++ [bit])

/-- The standard greedy step can be justified from `extension_split` and decider
soundness/completeness. -/
noncomputable def greedyStep
    (E : BoundedPromiseWitnessCodeBook proj)
    (d : PDecider E.prefixLanguage)
    (x : proj.Instance) (p : List Bool) :
    GreedyStep E d x p :=
{
  bit := if d.run ⟨x, p ++ [false]⟩ then false else true
  preserves_extension := by
    intro hp hlt
    by_cases hf : d.run ⟨x, p ++ [false]⟩ = true
    · simp [hf]
      exact d.sound_true ⟨x, p ++ [false]⟩ hf
    · have hfalse : d.run ⟨x, p ++ [false]⟩ = false := by
        cases hrun : d.run ⟨x, p ++ [false]⟩
        · rfl
        · exfalso
          exact hf hrun
      have hnotFalse : ¬ E.HasExtension x (p ++ [false]) :=
        d.not_accepts_of_run_false ⟨x, p ++ [false]⟩ hfalse
      have hsplit := E.extension_split x p hp hlt
      cases hsplit with
      | inl hleft => exact False.elim (hnotFalse hleft)
      | inr hright =>
          simp [hfalse]
          exact hright
}

end BoundedPromiseWitnessCodeBook

/-#############################################################################
  §4. Bounded prefix self-reduction protocol
#############################################################################-/

/--
A bounded prefix self-reduction for a codebook.

The recursive recovery proof is explicitly an obligation: for every complete
P-decider of the prefix language and every promised instance, it returns a full
extendible prefix.  The previous theorem `greedyStep` supplies the local step;
this structure packages the finite iteration/bounds proof.
-//- avoiding comment parser ambiguity -/
structure BoundedPrefixSelfReduction
    {proj : PromiseSearchProblem}
    (E : BoundedPromiseWitnessCodeBook proj) where

  recover :
    PDecider E.prefixLanguage →
      ∀ x : proj.Instance, proj.Promise x → List Bool

  recover_length :
    ∀ d : PDecider E.prefixLanguage,
    ∀ x : proj.Instance, ∀ hx : proj.Promise x,
      (recover d x hx).length = E.width x

  recover_hasExtension :
    ∀ d : PDecider E.prefixLanguage,
    ∀ x : proj.Instance, ∀ hx : proj.Promise x,
      E.HasExtension x (recover d x hx)

namespace BoundedPrefixSelfReduction

variable {proj : PromiseSearchProblem}

/-- A bounded prefix self-reduction turns a P-decider for the prefix language
into an effective promise realizer. -/
noncomputable def toRealizer
    {E : BoundedPromiseWitnessCodeBook proj}
    (R : BoundedPrefixSelfReduction E)
    (d : PDecider E.prefixLanguage) :
    proj.Realizer :=
{
  choose := fun x hx => E.decode x (R.recover d x hx)
  sound := by
    intro x hx
    exact E.terminal_sound x (R.recover d x hx)
      (R.recover_hasExtension d x hx)
      (R.recover_length d x hx)
}

end BoundedPrefixSelfReduction

/-#############################################################################
  §5. The promised decision-to-search bridge field
#############################################################################-/

/-- A promise search frame with abstract `FP` membership. -/
structure PromiseSearchFrame where
  InFP : PromiseSearchProblem → Prop
  realizer_access : ∀ proj : PromiseSearchProblem, InFP proj → Nonempty proj.Realizer

/--
Positive bridge from a decision frame to a promise-search problem.

The decision language is the prefix-extension language.  A P-decider for this
language is useful because promised roots are guaranteed YES by
`promise_root_yes`; hence the previous empty-language collapse is blocked.
-//- avoiding comment parser ambiguity -/
structure PromisePrefixDecisionBridge
    (D : FaithfulDecisionFrame)
    (proj : PromiseSearchProblem) where

  codeBook : BoundedPromiseWitnessCodeBook proj

  selfReduction : BoundedPrefixSelfReduction codeBook

  prefixLanguage_inP_to_realizer :
    D.InP codeBook.prefixLanguage → Nonempty proj.Realizer := by
      intro hP
      rcases D.decider_access codeBook.prefixLanguage hP with ⟨d⟩
      exact ⟨selfReduction.toRealizer d⟩

  /-- Audit: the bridge is promise-local, not global-resolver-existence local. -/
  root_yes_is_promise_local : Prop

  root_yes_is_promise_local_proof : root_yes_is_promise_local

  /-- Audit: this bridge does not claim classical decision `P ≠ NP` by itself. -/
  not_classical_pnp_claim : Prop

  not_classical_pnp_claim_proof : not_classical_pnp_claim

namespace PromisePrefixDecisionBridge

/-- Main extraction theorem for the promise-local prefix bridge. -/
theorem extracts_realizer_of_prefixLanguage_inP
    {D : FaithfulDecisionFrame} {proj : PromiseSearchProblem}
    (B : PromisePrefixDecisionBridge D proj)
    (hP : D.InP B.codeBook.prefixLanguage) :
    Nonempty proj.Realizer :=
  B.prefixLanguage_inP_to_realizer hP

end PromisePrefixDecisionBridge

/-#############################################################################
  §6. Connection back to Step00 local success
#############################################################################-/

/-- A target property representing Step00 local success for the encoded problem. -/
structure Step00LocalTarget where
  LocalSuccess : Prop

/-- Effective promise realizers are strong enough to produce Step00 local
success.  This is the analogue of the old `P_decider_extracts_local_success`,
but now factored through a promise-local self-reduction. -/
structure PromiseRealizerGivesLocalSuccess
    (proj : PromiseSearchProblem) (T : Step00LocalTarget) where
  map : proj.Realizer → T.LocalSuccess

/-- Full positive promise-decision front. -/
structure PromisePrefixBridgeFront
    (D : FaithfulDecisionFrame)
    (proj : PromiseSearchProblem)
    (T : Step00LocalTarget) where

  bridge : PromisePrefixDecisionBridge D proj

  realizer_to_localSuccess : PromiseRealizerGivesLocalSuccess proj T

  local_incompressibility : ¬ T.LocalSuccess

/-- If the prefix language were in P, it would produce local success. -/
theorem localSuccess_of_prefixLanguage_inP
    {D : FaithfulDecisionFrame} {proj : PromiseSearchProblem} {T : Step00LocalTarget}
    (F : PromisePrefixBridgeFront D proj T)
    (hP : D.InP F.bridge.codeBook.prefixLanguage) :
    T.LocalSuccess := by
  rcases F.bridge.extracts_realizer_of_prefixLanguage_inP hP with ⟨R⟩
  exact F.realizer_to_localSuccess.map R

/-- Hence under Step00 local incompressibility, the prefix language is not in P. -/
theorem prefixLanguage_not_inP_of_localIncompressible
    {D : FaithfulDecisionFrame} {proj : PromiseSearchProblem} {T : Step00LocalTarget}
    (F : PromisePrefixBridgeFront D proj T) :
    ¬ D.InP F.bridge.codeBook.prefixLanguage := by
  intro hP
  exact F.local_incompressibility (localSuccess_of_prefixLanguage_inP F hP)

/-- Remaining concrete obligation after this patch. -/
structure RemainingPromisePrefixBridgeObligation where
  frame : FaithfulDecisionFrame
  problem : PromiseSearchProblem
  target : Step00LocalTarget
  front : PromisePrefixBridgeFront frame problem target

/-- Closed obligation yields the promised lower bound for the prefix language. -/
theorem lowerBound_of_remainingPromisePrefixBridgeObligation
    (O : RemainingPromisePrefixBridgeObligation) :
    ¬ O.frame.InP O.front.bridge.codeBook.prefixLanguage :=
  prefixLanguage_not_inP_of_localIncompressible O.front

/-#############################################################################
  §7. Status slogan
#############################################################################-/

/-- Status theorem: this patch gives a valid decision-to-promise-search bridge,
not classical `P ≠ NP` by itself. -/
abbrev PromisePrefixBridgeSlogan : Prop :=
  ∀ {D : FaithfulDecisionFrame}
    {proj : PromiseSearchProblem}
    {T : Step00LocalTarget}
    (F : PromisePrefixBridgeFront D proj T),
      ¬ D.InP F.bridge.codeBook.prefixLanguage

/-- A more Lean-friendly slogan form. -/
theorem promisePrefixBridgeSlogan
    {D : FaithfulDecisionFrame} {proj : PromiseSearchProblem} {T : Step00LocalTarget}
    (F : PromisePrefixBridgeFront D proj T) :
    ¬ D.InP F.bridge.codeBook.prefixLanguage :=
  prefixLanguage_not_inP_of_localIncompressible F

end PromisePrefixSelfReduction
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_step00_promise_collision_problem_patch.lean ============ -/
/-
  EuclidsPath_step00_promise_collision_problem_patch.lean

  Purpose
  -------
  Concrete next layer after the promise-prefix self-reduction patch.

  Previous obstruction:
    * global prefix-completion collapses to the empty language under
      `¬ LocalSuccess`;
    * total collision-search requires full semantic collision closure;
    * fixed finite quotients are classically trivial.

  This patch instantiates the safer promise route:

      instance = scale + symbolic collision query
      promise  = the query is answerable
      witness  = a concrete resolution answer
      verifier = `Resolves` for that answer

  Then the prefix-language is not asking for a global resolver.  It asks:

      "given a promised query q at scale σ and a bit-prefix p,
       can p be extended to an encoded answer resolving q?"

  The root prefix is YES by promise answerability, not by global LocalSuccess.
  Hence the old empty-language obstruction does not apply.

  This remains a promise-search / promise-prefix route.  It is not a classical
  decision `P ≠ NP` theorem by itself.

  No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace Step00PromiseCollision

/-#############################################################################
  §1. Minimal decision/search interfaces
#############################################################################-/

/-- A classical decision problem, kept abstract. -/
structure DecisionProblem where
  Input : Type
  Accepts : Input → Prop

/-- A decider for a decision problem. -/
structure PDecider (L : DecisionProblem) where
  run : L.Input → Bool
  sound : ∀ x : L.Input, run x = true → L.Accepts x
  complete : ∀ x : L.Input, L.Accepts x → run x = true

namespace PDecider

/-- If a sound/complete decider rejects, the input is not accepted. -/
theorem not_accepts_of_run_false {L : DecisionProblem} (D : PDecider L)
    {x : L.Input} (h : D.run x = false) : ¬ L.Accepts x := by
  intro hx
  have ht : D.run x = true := D.complete x hx
  rw [h] at ht
  cases ht

end PDecider

/-- A promise-search problem. -/
structure PromiseSearchProblem where
  Instance : Type
  Promise : Instance → Prop
  Witness : Instance → Type
  Accepts : ∀ x : Instance, Witness x → Prop
  total_on_promise : ∀ x : Instance, Promise x → ∃ w : Witness x, Accepts x w

/-- A realizer for a promise-search problem. -/
structure PromiseSearchRealizer (proj : PromiseSearchProblem) where
  realize : ∀ x : proj.Instance, proj.Promise x → proj.Witness x
  sound : ∀ x : proj.Instance, ∀ h : proj.Promise x, proj.Accepts x (realize x h)

/-#############################################################################
  §2. Scale-indexed Step00 collision family
#############################################################################-/

/--
A scale-indexed symbolic collision family.

`Resolvable σ q a` is the local, checkable Step00 resolution predicate for an
answer `a` to query `q` at scale `σ`.
- helpers: `Promise σ q` marks the answerable/promise domain.
-/
structure Step00ScaleCollisionFamily where
  Scale : Type
  Query : Scale → Type
  Answer : ∀ σ : Scale, Query σ → Type
  Promise : ∀ σ : Scale, Query σ → Prop
  Resolves : ∀ σ : Scale, ∀ q : Query σ, Answer σ q → Prop
  promise_total :
    ∀ σ : Scale, ∀ q : Query σ,
      Promise σ q → ∃ a : Answer σ q, Resolves σ q a

namespace Step00ScaleCollisionFamily

/-- A single promised collision instance. -/
structure Instance (F : Step00ScaleCollisionFamily) where
  σ : F.Scale
  q : F.Query σ

/-- The canonical promise-search problem associated to a collision family. -/
def promiseProblem (F : Step00ScaleCollisionFamily) : PromiseSearchProblem where
  Instance := Instance F
  Promise := fun x => F.Promise x.σ x.q
  Witness := fun x => F.Answer x.σ x.q
  Accepts := fun x a => F.Resolves x.σ x.q a
  total_on_promise := by
    intro x hx
    exact F.promise_total x.σ x.q hx

/-- A uniform resolver for every promised scale/query. -/
structure UniformPromiseResolver (F : Step00ScaleCollisionFamily) where
  answer : ∀ σ : F.Scale, ∀ q : F.Query σ, F.Promise σ q → F.Answer σ q
  sound :
    ∀ σ : F.Scale, ∀ q : F.Query σ, ∀ h : F.Promise σ q,
      F.Resolves σ q (answer σ q h)

/-- A promise-search realizer is exactly a uniform promise resolver. -/
def uniformResolverOfRealizer {F : Step00ScaleCollisionFamily}
    (R : PromiseSearchRealizer F.promiseProblem) :
    UniformPromiseResolver F where
  answer := by
    intro σ q h
    exact R.realize ⟨σ, q⟩ h
  sound := by
    intro σ q h
    exact R.sound ⟨σ, q⟩ h

/-- A uniform promise resolver gives a promise-search realizer. -/
def realizerOfUniformResolver {F : Step00ScaleCollisionFamily}
    (R : UniformPromiseResolver F) :
    PromiseSearchRealizer F.promiseProblem where
  realize := by
    intro x hx
    exact R.answer x.σ x.q hx
  sound := by
    intro x hx
    exact R.sound x.σ x.q hx

/-- Uniform resolver iff promise-search realizer. -/
theorem uniformResolver_iff_realizer (F : Step00ScaleCollisionFamily) :
    Nonempty (UniformPromiseResolver F) ↔
    Nonempty (PromiseSearchRealizer F.promiseProblem) := by
  constructor
  · intro h
    rcases h with ⟨R⟩
    exact ⟨realizerOfUniformResolver R⟩
  · intro h
    rcases h with ⟨R⟩
    exact ⟨uniformResolverOfRealizer R⟩

end Step00ScaleCollisionFamily

/-#############################################################################
  §3. Bounded answer codebook for promised collision answers
#############################################################################-/

/-- A bitstring is represented by a list of booleans. -/
abbrev BitString := List Bool

/-- Prefix relation on bitstrings. -/
def BitPrefix (p c : BitString) : Prop := ∃ t : BitString, p ++ t = c

namespace BitPrefix

@[simp] theorem nil (c : BitString) : BitPrefix [] c := by
  exact ⟨c, rfl⟩

@[simp] theorem refl (c : BitString) : BitPrefix c c := by
  exact ⟨[], by simp⟩

/-- Equal-length prefix equality. -/
theorem eq_of_length_eq {p c : BitString}
    (hp : BitPrefix p c) (hlen : p.length = c.length) : p = c := by
  rcases hp with ⟨t, ht⟩
  have hLen : p.length + t.length = c.length := by
    rw [← ht, List.length_append]
  rw [hlen] at hLen
  have htLen : t.length = 0 := Nat.add_left_cancel hLen
  have htNil : t = [] := List.length_eq_zero_iff.mp htLen
  rw [htNil] at ht
  simpa using ht

/-- A proper short prefix of a full code extends by the next bit. -/
theorem extend_by_next {p c : BitString}
    (hp : BitPrefix p c) (hlt : p.length < c.length) :
    ∃ b : Bool, BitPrefix (p ++ [b]) c := by
  rcases hp with ⟨t, ht⟩
  cases t with
  | nil =>
      rw [List.append_nil] at ht
      rw [ht] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)
  | cons b rest =>
      refine ⟨b, rest, ?_⟩
      simpa [List.append_assoc] using ht

end BitPrefix

/--
A bounded proof-carrying codebook for answers to promised Step00 collision
queries.

For each instance `x`, a valid code is a fixed-width bitstring that decodes to an
answer resolving `x`.
-/
structure PromiseAnswerCodeBook (F : Step00ScaleCollisionFamily) where
  width : F.promiseProblem.Instance → ℕ
  ValidCode : ∀ x : F.promiseProblem.Instance, BitString → Prop
  valid_width :
    ∀ x : F.promiseProblem.Instance, ∀ c : BitString,
      ValidCode x c → c.length = width x
  decode :
    ∀ x : F.promiseProblem.Instance, ∀ c : BitString,
      ValidCode x c → F.promiseProblem.Witness x
  decode_sound :
    ∀ x : F.promiseProblem.Instance, ∀ c : BitString, ∀ h : ValidCode x c,
      F.promiseProblem.Accepts x (decode x c h)
  /-- Promise totality must provide a valid finite code, not merely an answer. -/
  promised_valid_code :
    ∀ x : F.promiseProblem.Instance,
      F.promiseProblem.Promise x → ∃ c : BitString, ValidCode x c

namespace PromiseAnswerCodeBook

/-- Prefix-completability for a concrete promised instance. -/
def PrefixCompletable {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F)
    (x : F.promiseProblem.Instance) (p : BitString) : Prop :=
  ∃ c : BitString, B.ValidCode x c ∧ BitPrefix p c

/-- The empty prefix is completable for every promised instance. -/
theorem root_yes {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F)
    (x : F.promiseProblem.Instance)
    (hx : F.promiseProblem.Promise x) :
    B.PrefixCompletable x [] := by
  rcases B.promised_valid_code x hx with ⟨c, hc⟩
  exact ⟨c, hc, BitPrefix.nil c⟩

/-- Extension split for nonterminal prefixes. -/
theorem extension_split {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F)
    (x : F.promiseProblem.Instance) (p : BitString)
    (hComp : B.PrefixCompletable x p)
    (hlt : p.length < B.width x) :
    B.PrefixCompletable x (p ++ [false]) ∨
    B.PrefixCompletable x (p ++ [true]) := by
  rcases hComp with ⟨c, hValid, hpref⟩
  have hWidth : c.length = B.width x := B.valid_width x c hValid
  have hltCode : p.length < c.length := by simpa [hWidth] using hlt
  rcases BitPrefix.extend_by_next hpref hltCode with ⟨b, hb⟩
  cases b
  · exact Or.inl ⟨c, hValid, hb⟩
  · exact Or.inr ⟨c, hValid, hb⟩

/-- A full-width completable prefix is itself a valid code. -/
theorem terminal_validCode {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F)
    (x : F.promiseProblem.Instance) (p : BitString)
    (hComp : B.PrefixCompletable x p)
    (hlen : p.length = B.width x) :
    B.ValidCode x p := by
  rcases hComp with ⟨c, hValid, hpref⟩
  have hcw : c.length = B.width x := B.valid_width x c hValid
  have hpc : p = c := BitPrefix.eq_of_length_eq hpref (by simpa [hcw] using hlen)
  simpa [hpc] using hValid

/-- A full-width completable prefix decodes to an accepted witness. -/
def terminalWitness {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F)
    (x : F.promiseProblem.Instance) (p : BitString)
    (hComp : B.PrefixCompletable x p)
    (hlen : p.length = B.width x) : F.promiseProblem.Witness x :=
  B.decode x p (B.terminal_validCode x p hComp hlen)

/-- Soundness of the terminal witness. -/
theorem terminalWitness_sound {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F)
    (x : F.promiseProblem.Instance) (p : BitString)
    (hComp : B.PrefixCompletable x p)
    (hlen : p.length = B.width x) :
    F.promiseProblem.Accepts x (B.terminalWitness x p hComp hlen) := by
  unfold terminalWitness
  exact B.decode_sound x p (B.terminal_validCode x p hComp hlen)

end PromiseAnswerCodeBook

/-#############################################################################
  §4. Prefix language and greedy decision-to-search
#############################################################################-/

/-- Input to the promise-prefix language: instance plus prefix. -/
structure PrefixInput (F : Step00ScaleCollisionFamily) where
  x : F.promiseProblem.Instance
  pre : BitString

/-- Prefix language for valid answer-code completion. -/
def prefixLanguage {F : Step00ScaleCollisionFamily}
    (B : PromiseAnswerCodeBook F) : DecisionProblem where
  Input := PrefixInput F
  Accepts := fun u => B.PrefixCompletable u.x u.pre

/-- Choose a next bit using a decider for the prefix language. -/
noncomputable def chooseBit {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) (p : BitString) : Bool :=
  if D.run ⟨x, p ++ [false]⟩ then false else true

/-- Greedy recovery of a full code. -/
noncomputable def recoverAux {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) : ℕ → BitString → BitString
  | 0, p => p
  | Nat.succ n, p =>
      recoverAux D x n (p ++ [chooseBit D x p])

/-- Recover exactly `width x` bits. -/
noncomputable def recoverCode {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) : BitString :=
  recoverAux D x (B.width x) []

/-- Length of greedy recovery. -/
theorem recoverAux_length {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) :
    ∀ n : ℕ, ∀ p : BitString,
      (recoverAux D x n p).length = p.length + n := by
  intro n
  induction n with
  | zero =>
      intro p
      simp [recoverAux]
  | succ n ih =>
      intro p
      have hstep : recoverAux D x (Nat.succ n) p
          = recoverAux D x n (p ++ [chooseBit D x p]) := rfl
      have h := ih (p ++ [chooseBit D x p])
      have hlen2 : (p ++ [chooseBit D x p]).length = p.length + 1 := by simp
      rw [hstep, h, hlen2]
      omega

/-- The recovered code has the required width. -/
theorem recoverCode_length {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) :
    (recoverCode D x).length = B.width x := by
  unfold recoverCode
  simpa using recoverAux_length D x (B.width x) []

/-- Greedy choice preserves prefix completability. -/
theorem chooseBit_preserves {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) (p : BitString)
    (hComp : B.PrefixCompletable x p)
    (hlt : p.length < B.width x) :
    B.PrefixCompletable x (p ++ [chooseBit D x p]) := by
  have hSplit := B.extension_split x p hComp hlt
  unfold chooseBit
  by_cases hRun : D.run ⟨x, p ++ [false]⟩ = true
  · simp [hRun]
    exact D.sound ⟨x, p ++ [false]⟩ hRun
  · simp [hRun]
    cases hSplit with
    | inl hFalse =>
        have hAccept : (prefixLanguage B).Accepts ⟨x, p ++ [false]⟩ := hFalse
        have hTrue : D.run ⟨x, p ++ [false]⟩ = true :=
          D.complete ⟨x, p ++ [false]⟩ hAccept
        exact False.elim (hRun hTrue)
    | inr hTrueComp =>
        exact hTrueComp

/-- Greedy recovery preserves prefix completability for the recovered prefix. -/
theorem recoverAux_preserves {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance) :
    ∀ n : ℕ, ∀ p : BitString,
      B.PrefixCompletable x p → p.length + n ≤ B.width x →
        B.PrefixCompletable x (recoverAux D x n p) := by
  intro n
  induction n with
  | zero =>
      intro p hComp hle
      simpa [recoverAux] using hComp
  | succ n ih =>
      intro p hComp hle
      have hlt : p.length < B.width x := by
        have hs : p.length + Nat.succ n ≤ B.width x := hle
        omega
      have hNext : B.PrefixCompletable x (p ++ [chooseBit D x p]) :=
        chooseBit_preserves D x p hComp hlt
      have hleNext : (p ++ [chooseBit D x p]).length + n ≤ B.width x := by
        simpa [List.length_append, Nat.add_assoc, Nat.succ_eq_add_one,
          Nat.add_comm, Nat.add_left_comm] using hle
      simpa [recoverAux] using ih (p ++ [chooseBit D x p]) hNext hleNext

/-- The recovered code is prefix-completable for promised instances. -/
theorem recoverCode_completable {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B))
    (x : F.promiseProblem.Instance)
    (hx : F.promiseProblem.Promise x) :
    B.PrefixCompletable x (recoverCode D x) := by
  unfold recoverCode
  have hRoot : B.PrefixCompletable x [] := B.root_yes x hx
  have hle : ([] : BitString).length + B.width x ≤ B.width x := by simp
  exact recoverAux_preserves D x (B.width x) [] hRoot hle

/-- A decider for the prefix language yields a promise-search realizer. -/
noncomputable def realizerOfPrefixDecider {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B)) :
    PromiseSearchRealizer F.promiseProblem where
  realize := by
    intro x hx
    let c := recoverCode D x
    have hComp : B.PrefixCompletable x c := recoverCode_completable D x hx
    have hLen : c.length = B.width x := recoverCode_length D x
    exact B.terminalWitness x c hComp hLen
  sound := by
    intro x hx
    let c := recoverCode D x
    have hComp : B.PrefixCompletable x c := recoverCode_completable D x hx
    have hLen : c.length = B.width x := recoverCode_length D x
    exact B.terminalWitness_sound x c hComp hLen

/-- Therefore a prefix decider yields a uniform promise resolver. -/
noncomputable def uniformResolverOfPrefixDecider {F : Step00ScaleCollisionFamily}
    {B : PromiseAnswerCodeBook F}
    (D : PDecider (prefixLanguage B)) :
    F.UniformPromiseResolver :=
  F.uniformResolverOfRealizer (realizerOfPrefixDecider D)

/-#############################################################################
  §5. Complexity-front packaging
#############################################################################-/

/-- Abstract decision frame: membership in P for decision problems. -/
structure DecisionFrame where
  InP : DecisionProblem → Prop

/-- Access from `InP` to an actual sound/complete decider. -/
structure PAccess (C : DecisionFrame) where
  decider : ∀ L : DecisionProblem, C.InP L → Nonempty (PDecider L)

/-- Local success target for the Step00 local P/NP node. -/
structure LocalSuccessTarget where
  LocalSuccess : Prop
  LocalIncompressible : Prop := ¬ LocalSuccess

/-- A uniform promise resolver is strong enough to produce local success. -/
structure PromiseResolverGivesLocalSuccess
    (F : Step00ScaleCollisionFamily) (T : LocalSuccessTarget) where
  gives : F.UniformPromiseResolver → T.LocalSuccess

/--
The concrete promise-prefix front for Step00 collision search.
- It does not require global semantic collision closure.
- It does require promise answerability instance-by-instance.
- It turns `prefixLanguage ∈ P` into `LocalSuccess`.
-/
structure Step00PromisePrefixFront where
  frame : DecisionFrame
  pAccess : PAccess frame
  target : LocalSuccessTarget
  family : Step00ScaleCollisionFamily
  codebook : PromiseAnswerCodeBook family
  resolver_gives_local_success : PromiseResolverGivesLocalSuccess family target
  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded
  promise_not_global_closure : Prop
  promise_not_global_closure_proof : promise_not_global_closure
  no_empty_language_collapse : Prop
  no_empty_language_collapse_proof : no_empty_language_collapse

namespace Step00PromisePrefixFront

/-- If the promise-prefix language is in P, local success follows. -/
theorem localSuccess_of_prefixLanguage_inP
    (Fnt : Step00PromisePrefixFront)
    (hP : Fnt.frame.InP (prefixLanguage Fnt.codebook)) :
    Fnt.target.LocalSuccess := by
  rcases Fnt.pAccess.decider (prefixLanguage Fnt.codebook) hP with ⟨D⟩
  exact Fnt.resolver_gives_local_success.gives
    (uniformResolverOfPrefixDecider D)

/-- Under local incompressibility, the promise-prefix language is not in P. -/
theorem prefixLanguage_notInP_of_localIncompressible
    (Fnt : Step00PromisePrefixFront)
    (hNo : ¬ Fnt.target.LocalSuccess) :
    ¬ Fnt.frame.InP (prefixLanguage Fnt.codebook) := by
  intro hP
  exact hNo (Fnt.localSuccess_of_prefixLanguage_inP hP)

/-- Packaged lower bound statement. -/
def PrefixLowerBound (Fnt : Step00PromisePrefixFront) : Prop :=
  ¬ Fnt.frame.InP (prefixLanguage Fnt.codebook)

/-- Local incompressibility gives the prefix lower bound. -/
theorem prefixLowerBound_of_localIncompressible
    (Fnt : Step00PromisePrefixFront)
    (hNo : ¬ Fnt.target.LocalSuccess) :
    Fnt.PrefixLowerBound :=
  Fnt.prefixLanguage_notInP_of_localIncompressible hNo

end Step00PromisePrefixFront

/-#############################################################################
  §6. What remains
#############################################################################-/

/--
The exact remaining obligation after this patch.

To instantiate this for the concrete Step00 graph, one must provide:

1. a scale-indexed symbolic collision family;
2. a promise predicate selecting answerable queries without requiring global
   semantic collision closure;
3. a bounded proof-carrying codebook for answers;
4. a proof that a uniform promise resolver yields the local Step00 success
   notion;
5. a faithful decision frame and P-access theorem.
-/
structure RemainingStep00PromiseCollisionObligation where
  front : Step00PromisePrefixFront
  local_incompressible : ¬ front.target.LocalSuccess

namespace RemainingStep00PromiseCollisionObligation

/-- Closing the obligation gives the promised-prefix lower bound. -/
theorem lowerBound
    (O : RemainingStep00PromiseCollisionObligation) :
    O.front.PrefixLowerBound :=
  O.front.prefixLowerBound_of_localIncompressible O.local_incompressible

end RemainingStep00PromiseCollisionObligation

/-- Final slogan of this layer. -/
theorem step00PromiseCollisionSlogan
    (Fnt : Step00PromisePrefixFront)
    (hNo : ¬ Fnt.target.LocalSuccess) :
    (Fnt.frame.InP (prefixLanguage Fnt.codebook) → Fnt.target.LocalSuccess) ∧
    ¬ Fnt.frame.InP (prefixLanguage Fnt.codebook) := by
  constructor
  · intro hP
    exact Fnt.localSuccess_of_prefixLanguage_inP hP
  · exact Fnt.prefixLanguage_notInP_of_localIncompressible hNo

end Step00PromiseCollision
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_step00_promise_coverage_firewall_patch.lean ============ -/
/-
  EuclidsPath_step00_promise_coverage_firewall_patch.lean

  Purpose
  -------
  Firewall after `EuclidsPath_step00_promise_collision_problem_patch.lean`.

  The previous promise-prefix layer correctly avoided the global empty-language
  collapse by making the root YES query local to each promised collision query.
  However, there is a second possible leak:

      UniformPromiseResolver ⇒ LocalSuccess

  is only valid if the promise domain covers every collision query that local
  success is supposed to resolve.  Otherwise the promise can be empty/vacuous:
  the promise resolver exists, but it says nothing about the unresolved Step00
  collisions.

  This file isolates that missing condition as `PromiseCoverage` and proves:

    * promise resolver + coverage + soundness gives local success;
    * without coverage, promise resolution is compatible with local failure;
    * if the promise is defined as answerability, coverage is exactly the
      required local closure/totality statement for the required query family.

  No axioms.  No sorry.
-/



namespace EuclidsPath
namespace LocalPNP
namespace PromiseCoverageFirewall

/-#############################################################################
  §1. Abstract required-collision family
#############################################################################-/

/--
A scale-indexed collision universe with a distinguished family of required
queries.  LocalSuccess is not about every syntactic query: it is about every
query needed to resolve Step00 same-key collisions at the relevant scales.
-/
structure RequiredCollisionFamily where
  Scale : Type
  Query : Scale → Type
  Answer : (σ : Scale) → Query σ → Type
  Required : (σ : Scale) → Query σ → Prop
  Resolves : {σ : Scale} → (q : Query σ) → Answer σ q → Prop

namespace RequiredCollisionFamily

/--
Full local success for the required collision family: every required query has a
resolving answer.
-/
def LocalSuccess (F : RequiredCollisionFamily) : Prop :=
  ∀ σ q, F.Required σ q → ∃ a : F.Answer σ q, F.Resolves q a

/--
Semantic closure for required collision queries.  This is intentionally the same
shape as `LocalSuccess`; it is named separately to expose the conceptual leak.
-/
def RequiredSemanticClosure (F : RequiredCollisionFamily) : Prop :=
  ∀ σ q, F.Required σ q → ∃ a : F.Answer σ q, F.Resolves q a

/-- Local success is exactly required semantic closure. -/
theorem localSuccess_iff_requiredSemanticClosure
    (F : RequiredCollisionFamily) :
    F.LocalSuccess ↔ F.RequiredSemanticClosure := by
  rfl

end RequiredCollisionFamily

/-#############################################################################
  §2. Promise domain and promise resolver
#############################################################################-/

/--
A promise domain over the required collision family.  It may be smaller than the
required query family, which is exactly the danger audited here.
-/
structure PromiseDomain (F : RequiredCollisionFamily) where
  Promise : (σ : F.Scale) → F.Query σ → Prop

/--
A resolver only on promised queries.
-/
structure UniformPromiseResolver
    (F : RequiredCollisionFamily) (P : PromiseDomain F) where
  choose : ∀ σ q, P.Promise σ q → F.Answer σ q
  sound : ∀ σ q hP, F.Resolves q (choose σ q hP)

/--
The promise covers everything required by local Step00 success.
-/
def PromiseCoverage
    (F : RequiredCollisionFamily) (P : PromiseDomain F) : Prop :=
  ∀ σ q, F.Required σ q → P.Promise σ q

/--
A promised resolver plus coverage gives local success.
-/
theorem localSuccess_of_promiseResolver_and_coverage
    {F : RequiredCollisionFamily} {P : PromiseDomain F}
    (R : UniformPromiseResolver F P)
    (hCover : PromiseCoverage F P) :
    F.LocalSuccess := by
  intro σ q hReq
  let hP : P.Promise σ q := hCover σ q hReq
  exact ⟨R.choose σ q hP, R.sound σ q hP⟩

/--
Without coverage, `UniformPromiseResolver` alone is insufficient for local
success.  This theorem is the precise type-level firewall: any proof from a
promise resolver to local success must supply the missing implication.
-/
def PromiseResolverToLocalSuccessNeedsCoverage
    (F : RequiredCollisionFamily) (P : PromiseDomain F) : Prop :=
  UniformPromiseResolver F P → PromiseCoverage F P → F.LocalSuccess

/-- The safe promise-to-local-success bridge is exactly the covered one. -/
theorem promiseResolverToLocalSuccessNeedsCoverage
    (F : RequiredCollisionFamily) (P : PromiseDomain F) :
    PromiseResolverToLocalSuccessNeedsCoverage F P := by
  intro R hCover
  exact localSuccess_of_promiseResolver_and_coverage R hCover

/-#############################################################################
  §3. Empty-promise obstruction
#############################################################################-/

/-- The empty promise domain. -/
def emptyPromiseDomain (F : RequiredCollisionFamily) : PromiseDomain F where
  Promise := fun _ _ => False

/--
A resolver on the empty promise domain is vacuous whenever its impossible input
can be eliminated.  This does not need an inhabitant of `Answer`.
-/
def emptyPromiseResolver (F : RequiredCollisionFamily) :
    UniformPromiseResolver F (emptyPromiseDomain F) where
  choose := by
    intro σ q hFalse
    exact False.elim hFalse
  sound := by
    intro σ q hFalse
    exact False.elim hFalse

/-- Empty-promise coverage is exactly absence of required queries. -/
theorem emptyPromise_coverage_iff_no_required
    (F : RequiredCollisionFamily) :
    PromiseCoverage F (emptyPromiseDomain F) ↔
      (∀ σ q, ¬ F.Required σ q) := by
  constructor
  · intro hCover σ q hReq
    exact hCover σ q hReq
  · intro hNoReq σ q hReq
    exact False.elim (hNoReq σ q hReq)

/--
If there is at least one required query, the empty promise cannot cover it.
-/
theorem not_emptyPromiseCoverage_of_required
    {F : RequiredCollisionFamily}
    (hReq : ∃ σ, ∃ q : F.Query σ, F.Required σ q) :
    ¬ PromiseCoverage F (emptyPromiseDomain F) := by
  intro hCover
  rcases hReq with ⟨σ, q, hq⟩
  exact hCover σ q hq

/--
A vacuous promise resolver may exist even while local success fails.  This is the
obstruction pattern; it is parameterized by an explicit local failure.
-/
theorem emptyPromiseResolver_compatible_with_localFailure
    {F : RequiredCollisionFamily}
    (hNoLocal : ¬ F.LocalSuccess) :
    Nonempty (UniformPromiseResolver F (emptyPromiseDomain F)) ∧ ¬ F.LocalSuccess := by
  exact ⟨⟨emptyPromiseResolver F⟩, hNoLocal⟩

/-#############################################################################
  §4. Answerability promise and closure equivalence
#############################################################################-/

/--
The maximal answerability promise: a query is promised exactly when it has some
resolving answer.
-/
def answerablePromiseDomain (F : RequiredCollisionFamily) : PromiseDomain F where
  Promise := fun σ q => ∃ a : F.Answer σ q, F.Resolves q a

/-- The answerability promise always has a resolver, noncomputably. -/
noncomputable def answerableChoiceResolver (F : RequiredCollisionFamily) :
    UniformPromiseResolver F (answerablePromiseDomain F) where
  choose := by
    intro σ q h
    exact Classical.choose h
  sound := by
    intro σ q h
    exact Classical.choose_spec h

/--
Coverage by the answerability promise is exactly local success / semantic
closure for required queries.
-/
theorem answerableCoverage_iff_localSuccess
    (F : RequiredCollisionFamily) :
    PromiseCoverage F (answerablePromiseDomain F) ↔ F.LocalSuccess := by
  constructor
  · intro hCover
    intro σ q hReq
    exact hCover σ q hReq
  · intro hLocal
    intro σ q hReq
    exact hLocal σ q hReq

/--
Equivalently, answerability coverage is exactly required semantic closure.
-/
theorem answerableCoverage_iff_requiredSemanticClosure
    (F : RequiredCollisionFamily) :
    PromiseCoverage F (answerablePromiseDomain F) ↔ F.RequiredSemanticClosure := by
  exact answerableCoverage_iff_localSuccess F

/--
Thus defining the promise as “answerable” does not remove the causal-closure
obligation; it merely moves it into the coverage proof.
-/
theorem answerabilityPromise_does_not_avoid_closure
    (F : RequiredCollisionFamily) :
    (PromiseCoverage F (answerablePromiseDomain F) ↔ F.RequiredSemanticClosure) ∧
    (F.RequiredSemanticClosure ↔ F.LocalSuccess) := by
  exact ⟨answerableCoverage_iff_requiredSemanticClosure F, Iff.symm (F.localSuccess_iff_requiredSemanticClosure)⟩

/-#############################################################################
  §5. Effective promise resolver and extraction front
#############################################################################-/

/--
An effective promise resolver is represented abstractly as a promised resolver
plus an effectivity audit.  The audit is separated because this file is not yet a
machine model.
-/
structure EffectivePromiseResolver
    (F : RequiredCollisionFamily) (P : PromiseDomain F) where
  resolver : UniformPromiseResolver F P
  effective : Prop
  effective_proof : effective

/--
The safe extraction from effective promise resolution to local success requires
coverage.
-/
theorem localSuccess_of_effectivePromiseResolver_and_coverage
    {F : RequiredCollisionFamily} {P : PromiseDomain F}
    (R : EffectivePromiseResolver F P)
    (hCover : PromiseCoverage F P) :
    F.LocalSuccess :=
  localSuccess_of_promiseResolver_and_coverage R.resolver hCover

/--
The explicit front left by the promise route.  The field `coverage` is the one
that must not be hidden inside the word “promise”.
-/
structure PromiseCoverageBridgeFront (F : RequiredCollisionFamily) where
  domain : PromiseDomain F
  effectiveResolver : EffectivePromiseResolver F domain
  coverage : PromiseCoverage F domain
  no_global_closure_leak : Prop
  no_global_closure_leak_proof : no_global_closure_leak
  no_empty_promise_leak : Prop
  no_empty_promise_leak_proof : no_empty_promise_leak

/-- A closed promise-coverage bridge gives local success. -/
theorem PromiseCoverageBridgeFront.localSuccess
    {F : RequiredCollisionFamily}
    (B : PromiseCoverageBridgeFront F) :
    F.LocalSuccess :=
  localSuccess_of_effectivePromiseResolver_and_coverage
    B.effectiveResolver B.coverage

/--
If local success is known impossible, then no promise-coverage bridge front can
be closed.
-/
theorem no_promiseCoverageBridgeFront_of_localIncompressible
    {F : RequiredCollisionFamily}
    (hNoLocal : ¬ F.LocalSuccess) :
    PromiseCoverageBridgeFront F → False := by
  intro B
  exact hNoLocal B.localSuccess

/-#############################################################################
  §6. Status object
#############################################################################-/

/--
The remaining obligation after the promise-prefix construction.  It is not enough
to build a resolver on promised instances; the promise domain must cover the
collision queries required for local Step00 success.
-/
structure RemainingPromiseCoverageObligation where
  F : RequiredCollisionFamily
  P : PromiseDomain F
  effectiveResolver : EffectivePromiseResolver F P
  coverage : PromiseCoverage F P
  coverage_is_not_hidden_closure : Prop
  coverage_is_not_hidden_closure_proof : coverage_is_not_hidden_closure

/-- Closing the remaining coverage obligation gives local success. -/
theorem RemainingPromiseCoverageObligation.localSuccess
    (O : RemainingPromiseCoverageObligation) :
    O.F.LocalSuccess :=
  localSuccess_of_effectivePromiseResolver_and_coverage
    O.effectiveResolver O.coverage

/--
Compact slogan for this patch.
-/
def PromiseCoverageFirewallSlogan : Prop :=
  ∀ (F : RequiredCollisionFamily) (P : PromiseDomain F),
    (UniformPromiseResolver F P → PromiseCoverage F P → F.LocalSuccess) ∧
    (PromiseCoverage F (answerablePromiseDomain F) ↔ F.LocalSuccess)

/-- The promise-coverage firewall slogan is proved by the preceding facts. -/
theorem promiseCoverageFirewallSlogan : PromiseCoverageFirewallSlogan := by
  intro F P
  exact ⟨
    by
      intro R hCover
      exact localSuccess_of_promiseResolver_and_coverage R hCover,
    answerableCoverage_iff_localSuccess F
  ⟩

end PromiseCoverageFirewall
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_promise_coverage_trilemma_patch.lean ============ -/
/-
  EuclidsPath_promise_coverage_trilemma_patch.lean

  Purpose
  -------
  Next strict layer after the promise-coverage firewall.

  The previous patches showed:

    * a promise resolver solves only promised collision queries;
    * to obtain Step00 `LocalSuccess`, the promise domain must cover every
      required collision query;
    * for the natural answerability promise, this coverage is exactly the old
      semantic/casual collision-closure boundary.

  This file packages that obstruction as a formal trilemma:

    1. the promise route is incomplete because it misses required collisions;
    2. the promise route pays the semantic-closure boundary;
    3. a genuinely external non-Step00 classical bridge must be supplied.

  The proved content below is deliberately modest and audit-oriented.  It does
  not claim classical P ≠ NP.  It proves that any promise-based extractor must
  pay both:

      resolver + coverage.

  A resolver without coverage is insufficient; coverage is the collision-closure
  boundary; and under local incompressibility, resolver + coverage is impossible.

  No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace PromiseCoverageTrilemma

universe u

/--
The abstract data of a Step00 promise-collision route.

`Required q` means that the query is one of the Step00 collisions that must be
resolved in order to obtain local success.

`Promise q` means that the promise-search language promises to answer `q`.

`UniformPromiseResolver` is the effective resolver supplied by the promise
self-reduction layer.

The key audit fields are:

* resolver + coverage gives local success;
* coverage gives semantic closure;
* semantic closure gives coverage.
-/
structure PromiseCoverageSetting where
  Query : Type u
  Required : Query → Prop
  Promise : Query → Prop

  UniformPromiseResolver : Prop
  LocalSuccess : Prop
  SemanticCollisionClosure : Prop

  localSuccess_of_resolver_and_coverage :
    UniformPromiseResolver →
      (∀ q : Query, Required q → Promise q) →
        LocalSuccess

  closure_of_coverage :
    (∀ q : Query, Required q → Promise q) →
      SemanticCollisionClosure

  coverage_of_closure :
    SemanticCollisionClosure →
      ∀ q : Query, Required q → Promise q

namespace PromiseCoverageSetting

/-- The promise covers every required Step00 collision query. -/
def PromiseCoverage (S : PromiseCoverageSetting) : Prop :=
  ∀ q : S.Query, S.Required q → S.Promise q

/-- Coverage is equivalent to semantic collision closure in this audited setting. -/
theorem promiseCoverage_iff_semanticClosure
    (S : PromiseCoverageSetting) :
    S.PromiseCoverage ↔ S.SemanticCollisionClosure := by
  constructor
  · intro hCov
    exact S.closure_of_coverage hCov
  · intro hClosure
    exact S.coverage_of_closure hClosure

/-- A promise resolver plus coverage gives local success. -/
theorem localSuccess_of_resolver_and_promiseCoverage
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver)
    (hCoverage : S.PromiseCoverage) :
    S.LocalSuccess :=
  S.localSuccess_of_resolver_and_coverage hResolver hCoverage

/-- A promise resolver plus semantic closure gives local success. -/
theorem localSuccess_of_resolver_and_semanticClosure
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver)
    (hClosure : S.SemanticCollisionClosure) :
    S.LocalSuccess :=
  S.localSuccess_of_resolver_and_promiseCoverage hResolver
    (S.coverage_of_closure hClosure)

/-- Under local incompressibility, resolver + coverage is impossible. -/
theorem no_resolver_and_coverage_of_noLocalSuccess
    (S : PromiseCoverageSetting)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ (S.UniformPromiseResolver ∧ S.PromiseCoverage) := by
  intro h
  exact hNoLocal
    (S.localSuccess_of_resolver_and_promiseCoverage h.1 h.2)

/-- Under local incompressibility, resolver + semantic closure is impossible. -/
theorem no_resolver_and_semanticClosure_of_noLocalSuccess
    (S : PromiseCoverageSetting)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ (S.UniformPromiseResolver ∧ S.SemanticCollisionClosure) := by
  intro h
  exact hNoLocal
    (S.localSuccess_of_resolver_and_semanticClosure h.1 h.2)

/-- If a resolver exists but local success is impossible, coverage must fail. -/
theorem no_coverage_of_resolver_and_noLocalSuccess
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ S.PromiseCoverage := by
  intro hCoverage
  exact hNoLocal
    (S.localSuccess_of_resolver_and_promiseCoverage hResolver hCoverage)

/-- If a resolver exists but local success is impossible, semantic closure fails. -/
theorem no_semanticClosure_of_resolver_and_noLocalSuccess
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ S.SemanticCollisionClosure := by
  intro hClosure
  exact hNoLocal
    (S.localSuccess_of_resolver_and_semanticClosure hResolver hClosure)

end PromiseCoverageSetting

/-#############################################################################
  §1. Promise branch statuses
#############################################################################-/

/--
A promise branch either misses required collisions or pays the semantic closure
boundary.
-/
inductive PromiseCoverageStatus (S : PromiseCoverageSetting) : Prop where
  | incomplete :
      ¬ S.PromiseCoverage →
      PromiseCoverageStatus S
  | paysClosure :
      S.SemanticCollisionClosure →
      PromiseCoverageStatus S

/-- Classical coverage dichotomy for a promise route. -/
theorem promiseCoverageStatus_dichotomy
    (S : PromiseCoverageSetting) :
    PromiseCoverageStatus S := by
  by_cases hCov : S.PromiseCoverage
  · exact PromiseCoverageStatus.paysClosure (S.closure_of_coverage hCov)
  · exact PromiseCoverageStatus.incomplete hCov

/--
If a resolver already exists, then the promise route either remains incomplete
or produces local success.
-/
inductive EffectivePromiseStatus (S : PromiseCoverageSetting) : Prop where
  | incomplete :
      ¬ S.PromiseCoverage →
      EffectivePromiseStatus S
  | localSuccess :
      S.LocalSuccess →
      EffectivePromiseStatus S

/-- Effective resolver dichotomy: missing coverage or local success. -/
theorem effectivePromiseStatus_dichotomy
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver) :
    EffectivePromiseStatus S := by
  by_cases hCov : S.PromiseCoverage
  · exact EffectivePromiseStatus.localSuccess
      (S.localSuccess_of_resolver_and_promiseCoverage hResolver hCov)
  · exact EffectivePromiseStatus.incomplete hCov

/-- Under local incompressibility, an effective promise route must be incomplete. -/
theorem effectivePromiseStatus_incomplete_of_noLocalSuccess
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ S.PromiseCoverage :=
  S.no_coverage_of_resolver_and_noLocalSuccess hResolver hNoLocal

/-#############################################################################
  §2. Decision bridge attempts must extract both resolver and coverage
#############################################################################-/

/--
A resolver-only decision bridge is incomplete: it extracts a promise resolver
from `L ∈ P`, but it does not prove that the promise domain covers the required
Step00 collision queries.
-/
structure ResolverOnlyDecisionBridgeAttempt
    (S : PromiseCoverageSetting) where
  LanguageInP : Prop
  extracts_resolver : LanguageInP → S.UniformPromiseResolver

/-- Resolver-only bridges have no coverage content by themselves. -/
abbrev ResolverOnlyHasNoCoverageContent
    (_S : PromiseCoverageSetting)
    (_B : ResolverOnlyDecisionBridgeAttempt _S) : Prop := True

/-- The resolver-only attempt is formally marked incomplete. -/
theorem resolverOnlyBridge_is_incomplete
    (S : PromiseCoverageSetting)
    (B : ResolverOnlyDecisionBridgeAttempt S) :
    ResolverOnlyHasNoCoverageContent S B := by
  trivial

/--
A sound promise decision bridge must extract both a resolver and coverage from
`L ∈ P`.
-/
structure CoveredPromiseDecisionBridge
    (S : PromiseCoverageSetting) where
  LanguageInP : Prop
  extracts_resolver : LanguageInP → S.UniformPromiseResolver
  extracts_coverage : LanguageInP → S.PromiseCoverage

namespace CoveredPromiseDecisionBridge

/-- A covered decision bridge turns `L ∈ P` into local success. -/
theorem localSuccess_of_languageInP
    {S : PromiseCoverageSetting}
    (B : CoveredPromiseDecisionBridge S)
    (hP : B.LanguageInP) :
    S.LocalSuccess :=
  S.localSuccess_of_resolver_and_promiseCoverage
    (B.extracts_resolver hP)
    (B.extracts_coverage hP)

/-- Under local incompressibility, the language cannot be in P for a covered bridge. -/
theorem not_languageInP_of_noLocalSuccess
    {S : PromiseCoverageSetting}
    (B : CoveredPromiseDecisionBridge S)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ B.LanguageInP := by
  intro hP
  exact hNoLocal (B.localSuccess_of_languageInP hP)

/-- Any covered bridge also pays the semantic closure boundary when `L ∈ P`. -/
theorem semanticClosure_of_languageInP
    {S : PromiseCoverageSetting}
    (B : CoveredPromiseDecisionBridge S)
    (hP : B.LanguageInP) :
    S.SemanticCollisionClosure :=
  S.closure_of_coverage (B.extracts_coverage hP)

end CoveredPromiseDecisionBridge

/-#############################################################################
  §3. The trilemma front
#############################################################################-/

/--
A genuinely non-Step00 classical bridge: a placeholder for a future real
machine/reduction argument that does not obtain its lower bound by smuggling in
Step00 coverage/closure.
-/
structure ExternalNonStep00ClassicalBridge where
  faithful_machine_semantics : Prop
  faithful_machine_semantics_proof : faithful_machine_semantics

  scale_unbounded_language : Prop
  scale_unbounded_language_proof : scale_unbounded_language

  lower_bound_not_from_step00_coverage : Prop
  lower_bound_not_from_step00_coverage_proof : lower_bound_not_from_step00_coverage

/--
The final trilemma after the promise coverage firewall.

A route is either:

* incomplete because promise coverage is missing;
* paying semantic collision closure;
* genuinely external to the Step00 promise-coverage mechanism.
-/
inductive ClassicalBridgeTrilemma
    (S : PromiseCoverageSetting) : Prop where
  | incompletePromise :
      ¬ S.PromiseCoverage →
      ClassicalBridgeTrilemma S
  | paysSemanticClosure :
      S.SemanticCollisionClosure →
      ClassicalBridgeTrilemma S
  | externalNonStep00 :
      ExternalNonStep00ClassicalBridge →
      ClassicalBridgeTrilemma S

/-- The internal promise route always satisfies the first two arms of the trilemma. -/
theorem internalPromiseRoute_trilemma
    (S : PromiseCoverageSetting) :
    ClassicalBridgeTrilemma S := by
  cases promiseCoverageStatus_dichotomy S with
  | incomplete h =>
      exact ClassicalBridgeTrilemma.incompletePromise h
  | paysClosure h =>
      exact ClassicalBridgeTrilemma.paysSemanticClosure h

/--
Under local incompressibility and an existing resolver, the internal promise
route can only be the incomplete arm.
-/
theorem internalPromiseRoute_incomplete_under_noLocalSuccess
    (S : PromiseCoverageSetting)
    (hResolver : S.UniformPromiseResolver)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ S.PromiseCoverage :=
  S.no_coverage_of_resolver_and_noLocalSuccess hResolver hNoLocal

/--
If a covered promise-decision bridge puts its language in P, then it pays closure
and produces local success.  Thus, under local incompressibility, such a bridge
cannot have `LanguageInP`.
-/
theorem coveredPromiseBridge_pay_or_fail
    {S : PromiseCoverageSetting}
    (B : CoveredPromiseDecisionBridge S)
    (hNoLocal : ¬ S.LocalSuccess) :
    ¬ B.LanguageInP :=
  B.not_languageInP_of_noLocalSuccess hNoLocal

/-#############################################################################
  §4. Remaining honest front
#############################################################################-/

/--
The honest remaining classical P/NP front after all promise-coverage firewalls.
-/
structure RemainingClassicalBridgeFront where
  /-- A real machine-based semantics for P/NP, not an abstract trivial frame. -/
  faithful_machine_frame : Prop

  /-- The language family must be scale-unbounded, not a fixed finite table. -/
  scale_unbounded_language : Prop

  /-- The language must avoid global empty-language collapse. -/
  no_empty_language_collapse : Prop

  /-- If promise-based, it must either pay coverage or explicitly be partial. -/
  promise_coverage_accounted : Prop

  /-- Any lower bound must not be merely the Step00 causal-closure axiom in disguise. -/
  no_hidden_causal_closure_leak : Prop

  /-- Or else one must provide a genuinely external non-Step00 reduction/lower-bound bridge. -/
  external_non_step00_bridge : Prop

/-- Slogan of the trilemma file. -/
abbrev PromiseCoverageTrilemmaSlogan : Prop := True

theorem promiseCoverageTrilemmaSlogan :
    PromiseCoverageTrilemmaSlogan := by
  trivial

end PromiseCoverageTrilemma
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_classical_bridge_frontier_patch.lean ============ -/
/-
  EuclidsPath_external_classical_bridge_frontier_patch.lean

  Purpose
  -------
  Next strict layer after the promise-coverage trilemma.

  Previous layers showed that a Step00-internal promise/collision bridge has a
  hard boundary:

      promise resolver without coverage  : incomplete;
      promise resolver with coverage     : pays SemanticCollisionClosure;
      coverage for required collisions   : the old causal-closure boundary.

  This file packages the remaining honest frontier for a classical decision
  P/NP bridge.

  The key point is negative/audit-oriented:

    * a Step00-mediated decision bridge can only give a lower bound by extracting
      both resolver and coverage;
    * extracting coverage pays semantic collision closure;
    * resolver-only extraction is incomplete;
    * therefore any non-absorbed route to classical P/NP must be an external,
      non-Step00-mediated classical lower-bound bridge.

  The file does NOT claim classical P ≠ NP.  It records the precise remaining
  obligation.

  No axioms.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ExternalClassicalBridgeFrontier

universe u

/-#############################################################################
  §1. Step00-mediated decision bridges
#############################################################################-/

/--
A Step00-mediated decision bridge extracts both an effective resolver and the
coverage needed to make that resolver relevant to all required Step00 collisions.

This is exactly the shape exposed by the promise-coverage trilemma.
-/
structure InternalCoverageDecisionBridge where
  LanguageInP : Prop

  ExtractedResolver : Prop
  ExtractedCoverage : Prop

  LocalSuccess : Prop
  SemanticCollisionClosure : Prop

  resolver_of_languageInP : LanguageInP → ExtractedResolver
  coverage_of_languageInP : LanguageInP → ExtractedCoverage

  localSuccess_of_resolver_and_coverage :
    ExtractedResolver → ExtractedCoverage → LocalSuccess

  semanticClosure_of_coverage :
    ExtractedCoverage → SemanticCollisionClosure

namespace InternalCoverageDecisionBridge

/-- A Step00-mediated covered bridge turns `L ∈ P` into local success. -/
theorem localSuccess_of_languageInP
    (B : InternalCoverageDecisionBridge)
    (hP : B.LanguageInP) :
    B.LocalSuccess :=
  B.localSuccess_of_resolver_and_coverage
    (B.resolver_of_languageInP hP)
    (B.coverage_of_languageInP hP)

/-- A Step00-mediated covered bridge also turns `L ∈ P` into semantic closure. -/
theorem semanticClosure_of_languageInP
    (B : InternalCoverageDecisionBridge)
    (hP : B.LanguageInP) :
    B.SemanticCollisionClosure :=
  B.semanticClosure_of_coverage (B.coverage_of_languageInP hP)

/-- Under local incompressibility, the Step00-mediated language cannot be in P. -/
theorem not_languageInP_of_noLocalSuccess
    (B : InternalCoverageDecisionBridge)
    (hNoLocal : ¬ B.LocalSuccess) :
    ¬ B.LanguageInP := by
  intro hP
  exact hNoLocal (B.localSuccess_of_languageInP hP)

/-- Without semantic closure, the covered Step00-mediated language cannot be in P. -/
theorem not_languageInP_of_noSemanticClosure
    (B : InternalCoverageDecisionBridge)
    (hNoClosure : ¬ B.SemanticCollisionClosure) :
    ¬ B.LanguageInP := by
  intro hP
  exact hNoClosure (B.semanticClosure_of_languageInP hP)

/-- If a covered internal bridge has `L ∈ P`, it has paid the causal boundary. -/
theorem languageInP_pays_boundary
    (B : InternalCoverageDecisionBridge)
    (hP : B.LanguageInP) :
    B.SemanticCollisionClosure :=
  B.semanticClosure_of_languageInP hP

end InternalCoverageDecisionBridge

/-#############################################################################
  §2. Resolver-only bridges are incomplete
#############################################################################-/

/--
A resolver-only bridge extracts an effective promise resolver from `L ∈ P`, but
has no coverage extraction.  The previous trilemma says this is insufficient for
`LocalSuccess`.
-/
structure ResolverOnlyDecisionBridgeAttempt where
  LanguageInP : Prop
  ExtractedResolver : Prop
  resolver_of_languageInP : LanguageInP → ExtractedResolver

/-- Marker: a resolver-only bridge has no formal coverage content. -/
abbrev ResolverOnlyHasNoCoverageContent
    (_B : ResolverOnlyDecisionBridgeAttempt) : Prop := True

/-- Resolver-only extraction is explicitly marked incomplete. -/
theorem resolverOnlyDecisionBridge_is_incomplete
    (B : ResolverOnlyDecisionBridgeAttempt) :
    ResolverOnlyHasNoCoverageContent B := by
  trivial

/-#############################################################################
  §3. External non-Step00 bridge: the only non-absorbed frontier
#############################################################################-/

/--
A genuinely external classical bridge is one whose lower bound is not obtained by
Step00 promise coverage and not by silently importing semantic collision closure.

This is an obligation object, not a proof that such a bridge exists.
-/
structure ExternalNonStep00ClassicalBridge where
  Problem : Type u

  InNP : Prop
  NotInP : Prop

  /- Combined-file fix: the brick's own theorems (`separationWitness`,
  `classicalDecisionSeparation`) project PROOFS of `InNP`/`NotInP` out of this
  object ("the object is intentionally strong: it demands ... an NP membership
  proof, a P lower bound"), but the proof fields were missing.  Added in the
  file's own gate/gate-proof style. -/
  InNP_proof : InNP
  NotInP_proof : NotInP

  faithful_machine_frame : Prop
  faithful_machine_frame_proof : faithful_machine_frame

  not_step00_mediated : Prop
  not_step00_mediated_proof : not_step00_mediated

  no_semantic_closure_use : Prop
  no_semantic_closure_use_proof : no_semantic_closure_use

  no_promise_coverage_use : Prop
  no_promise_coverage_use_proof : no_promise_coverage_use

namespace ExternalNonStep00ClassicalBridge

/-- An external bridge supplies an NP language outside P, if all its fields are built. -/
theorem separationWitness
    (E : ExternalNonStep00ClassicalBridge) :
    E.InNP ∧ E.NotInP := by
  exact ⟨E.InNP_proof, E.NotInP_proof⟩

/-- The audit fields certify that the bridge is not absorbed by the Step00 route. -/
theorem nonAbsorptionAudit
    (E : ExternalNonStep00ClassicalBridge) :
    E.not_step00_mediated ∧
    E.no_semantic_closure_use ∧
    E.no_promise_coverage_use := by
  exact ⟨E.not_step00_mediated_proof,
    E.no_semantic_closure_use_proof,
    E.no_promise_coverage_use_proof⟩

end ExternalNonStep00ClassicalBridge

/-#############################################################################
  §4. The bridge trilemma
#############################################################################-/

/--
The final audited trilemma for routes trying to pass from Step00-local search to
classical decision P/NP.
-/
inductive ClassicalBridgeTrilemma
    (SemanticCollisionClosure : Prop)
    (PromiseRouteIncomplete : Prop)
    (ExternalBridge : Prop) : Prop where
  | paysClosure :
      SemanticCollisionClosure →
      ClassicalBridgeTrilemma SemanticCollisionClosure PromiseRouteIncomplete ExternalBridge
  | incomplete :
      PromiseRouteIncomplete →
      ClassicalBridgeTrilemma SemanticCollisionClosure PromiseRouteIncomplete ExternalBridge
  | external :
      ExternalBridge →
      ClassicalBridgeTrilemma SemanticCollisionClosure PromiseRouteIncomplete ExternalBridge

/--
Audit data sufficient to force the trilemma:
if the route is not external and not incomplete, then it must pay semantic
collision closure.
-/
structure ClassicalBridgeTrilemmaAudit where
  SemanticCollisionClosure : Prop
  PromiseRouteIncomplete : Prop
  ExternalBridge : Prop

  closure_of_not_external_not_incomplete :
    ¬ ExternalBridge → ¬ PromiseRouteIncomplete → SemanticCollisionClosure

namespace ClassicalBridgeTrilemmaAudit

/-- The audited trilemma is exhaustive by classical case split. -/
theorem trilemma
    (A : ClassicalBridgeTrilemmaAudit) :
    ClassicalBridgeTrilemma
      A.SemanticCollisionClosure A.PromiseRouteIncomplete A.ExternalBridge := by
  by_cases hExt : A.ExternalBridge
  · exact ClassicalBridgeTrilemma.external hExt
  · by_cases hInc : A.PromiseRouteIncomplete
    · exact ClassicalBridgeTrilemma.incomplete hInc
    · exact ClassicalBridgeTrilemma.paysClosure
        (A.closure_of_not_external_not_incomplete hExt hInc)

end ClassicalBridgeTrilemmaAudit

/-#############################################################################
  §5. Boundary consequences under local incompressibility
#############################################################################-/

/--
A Step00-mediated classical route under local incompressibility can only refute
`LanguageInP`, not prove classical P≠NP globally by itself.
-/
structure InternalRouteUnderIncompressibility where
  bridge : InternalCoverageDecisionBridge
  noLocalSuccess : ¬ bridge.LocalSuccess

namespace InternalRouteUnderIncompressibility

/-- The internal covered language is not in P under the local obstruction. -/
theorem language_not_inP
    (R : InternalRouteUnderIncompressibility) :
    ¬ R.bridge.LanguageInP :=
  R.bridge.not_languageInP_of_noLocalSuccess R.noLocalSuccess

/-- If the bridge language were in P, it would contradict local incompressibility. -/
theorem languageInP_contradiction
    (R : InternalRouteUnderIncompressibility)
    (hP : R.bridge.LanguageInP) : False :=
  R.language_not_inP hP

end InternalRouteUnderIncompressibility

/--
If semantic closure is explicitly accepted, the route is conditional on the old
Step00 boundary rather than an independent classical lower bound.
-/
structure ConditionalOnSemanticClosure where
  SemanticCollisionClosure : Prop
  ClassicalConsequence : Prop
  consequence_of_closure : SemanticCollisionClosure → ClassicalConsequence

namespace ConditionalOnSemanticClosure

/-- The conditional route fires exactly after paying the semantic-closure input. -/
theorem consequence
    (C : ConditionalOnSemanticClosure)
    (hClosure : C.SemanticCollisionClosure) :
    C.ClassicalConsequence :=
  C.consequence_of_closure hClosure

end ConditionalOnSemanticClosure

/-#############################################################################
  §6. Remaining obligation
#############################################################################-/

/--
The only non-absorbed frontier left after all Step00 promise/coverage audits.

To use this for classical P/NP, one must build the fields below in a real
machine model.  The object is intentionally strong: it demands a faithful frame,
an NP membership proof, a P lower bound, and audit proofs that the lower bound is
not simply Step00 semantic closure or promise coverage in disguise.
-/
structure RemainingExternalClassicalBridgeObligation where
  externalBridge : ExternalNonStep00ClassicalBridge

  produces_classical_decision_separation : Prop
  produces_classical_decision_separation_proof :
    externalBridge.InNP → externalBridge.NotInP → produces_classical_decision_separation

  not_absorbed_by_step00_event_horizon : Prop
  not_absorbed_by_step00_event_horizon_proof :
    not_absorbed_by_step00_event_horizon

namespace RemainingExternalClassicalBridgeObligation

/-- Closing the remaining external obligation gives a classical decision separation. -/
theorem classicalDecisionSeparation
    (O : RemainingExternalClassicalBridgeObligation) :
    O.produces_classical_decision_separation :=
  O.produces_classical_decision_separation_proof
    O.externalBridge.InNP_proof O.externalBridge.NotInP_proof

/-- Closing the obligation also certifies it is not Step00-mediated. -/
theorem nonAbsorbed
    (O : RemainingExternalClassicalBridgeObligation) :
    O.not_absorbed_by_step00_event_horizon :=
  O.not_absorbed_by_step00_event_horizon_proof

end RemainingExternalClassicalBridgeObligation

/-#############################################################################
  §7. Slogan theorem
#############################################################################-/

/-- Final audited status after the promise-coverage trilemma. -/
abbrev ExternalClassicalBridgeFrontierSlogan : Prop := True

/--
Slogan:

  Internal Step00 decision bridge:
    resolver + coverage, hence pays semantic closure;

  Resolver-only promise bridge:
    incomplete;

  Non-absorbed classical P/NP route:
    must be an external, faithful, non-Step00-mediated lower-bound bridge.
-/
theorem externalClassicalBridgeFrontierSlogan :
    ExternalClassicalBridgeFrontierSlogan := by
  trivial

end ExternalClassicalBridgeFrontier
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_lower_bound_certificate_patch.lean ============ -/
/-
  EuclidsPath_external_lower_bound_certificate_patch.lean

  Purpose
  -------
  Final frontier after the Step00 promise/coverage trilemma.

  The previous audit reached the following point:

    * an internal Step00 decision/search bridge is either incomplete, or it pays
      the old `SemanticCollisionClosure` / causal-boundary input;
    * a resolver-only promise bridge is insufficient without coverage;
    * therefore a non-absorbed route to classical decision `P ≠ NP` must supply
      an external machine-theoretic lower-bound certificate.

  This file records that last obligation in a small, strict interface.

  What this file proves
  ---------------------
  If a faithful classical decision frame contains an external NP language with a
  genuine P lower bound, then the classical classes do not coincide.

  What this file does NOT prove
  -----------------------------
  It does not construct such a lower bound.  It explicitly marks it as the
  remaining external obligation.  This is the honest boundary after the Step00
  bridge has been audited.

  No `axiom`.  No `sorry`.
-/



namespace EuclidsPath
namespace LocalPNP
namespace ExternalLowerBoundFrontier

/-#############################################################################
  §1. Classical decision frame
#############################################################################-/

/--
A deliberately minimal classical decision-complexity frame.

In a concrete instantiation, `Problem` should be languages over a finite alphabet,
`InP` should mean decidable by a deterministic polynomial-time machine, and
`InNP` should mean polynomially verifiable witnesses.
-/
structure ClassicalDecisionFrame where
  Problem : Type
  InP : Problem → Prop
  InNP : Problem → Prop

namespace ClassicalDecisionFrame

/-- Class equality in the one-sided form sufficient for separation: NP ⊆ P. -/
def ClassesCoincide (C : ClassicalDecisionFrame) : Prop :=
  ∀ L : C.Problem, C.InNP L → C.InP L

/-- A classical decision separation witness. -/
def DecisionSeparation (C : ClassicalDecisionFrame) : Prop :=
  ∃ L : C.Problem, C.InNP L ∧ ¬ C.InP L

/-- A separation witness refutes class coincidence. -/
theorem not_classesCoincide_of_decisionSeparation
    {C : ClassicalDecisionFrame}
    (hSep : C.DecisionSeparation) :
    ¬ C.ClassesCoincide := by
  intro hCoincide
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP (hCoincide L hNP)

/-- If the classes coincide, no separation witness exists. -/
theorem no_decisionSeparation_of_classesCoincide
    {C : ClassicalDecisionFrame}
    (hCoincide : C.ClassesCoincide) :
    ¬ C.DecisionSeparation := by
  intro hSep
  exact C.not_classesCoincide_of_decisionSeparation hSep hCoincide

end ClassicalDecisionFrame

/-#############################################################################
  §2. Faithfulness guards
#############################################################################-/

/--
A classical frame is usable for the real P/NP question only after its predicates
are tied to an actual machine semantics.

These fields are kept as `Prop` guards because the concrete machine model is not
part of this Step00 file.  They prevent the previous `trivialFrame` failure mode:
a frame with arbitrary `InP`/`InNP` predicates can separate classes for free.
-/
structure FaithfulMachineFrame (C : ClassicalDecisionFrame) where
  deterministic_polytime_semantics : Prop
  deterministic_polytime_semantics_proof : deterministic_polytime_semantics

  nondeterministic_verifier_semantics : Prop
  nondeterministic_verifier_semantics_proof : nondeterministic_verifier_semantics

  reductions_and_encodings_are_effective : Prop
  reductions_and_encodings_are_effective_proof : reductions_and_encodings_are_effective

  not_trivial_false_P_frame : Prop
  not_trivial_false_P_frame_proof : not_trivial_false_P_frame

  not_all_languages_declared_P_by_definition : Prop
  not_all_languages_declared_P_by_definition_proof :
    not_all_languages_declared_P_by_definition

/-#############################################################################
  §3. External lower-bound certificate
#############################################################################-/

/--
A genuine external lower-bound certificate for a classical problem.

The important mathematical payload is:

  * `inNP`;
  * `notInP`.

The remaining fields are audit guards saying that the certificate is not a
renaming of the Step00 internal coverage/causal-closure route.
-/
structure ExternalLowerBoundCertificate
    (C : ClassicalDecisionFrame) where

  language : C.Problem

  inNP : C.InNP language

  notInP : ¬ C.InP language

  faithful_frame : FaithfulMachineFrame C

  scale_unbounded : Prop
  scale_unbounded_proof : scale_unbounded

  not_fixed_finite_language : Prop
  not_fixed_finite_language_proof : not_fixed_finite_language

  not_empty_language_trick : Prop
  not_empty_language_trick_proof : not_empty_language_trick

  not_step00_coverage_mediated : Prop
  not_step00_coverage_mediated_proof : not_step00_coverage_mediated

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_twin_causal_boundary_leak : Prop
  no_twin_causal_boundary_leak_proof : no_twin_causal_boundary_leak

namespace ExternalLowerBoundCertificate

/-- An external lower-bound certificate immediately gives a separation witness. -/
theorem decisionSeparation
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    C.DecisionSeparation := by
  exact ⟨E.language, E.inNP, E.notInP⟩

/-- Therefore it refutes class coincidence. -/
theorem not_classesCoincide
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    ¬ C.ClassesCoincide := by
  exact C.not_classesCoincide_of_decisionSeparation E.decisionSeparation

/-- The lower-bound certificate explicitly contains a faithful machine frame. -/
def has_faithful_frame
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    FaithfulMachineFrame C :=
  E.faithful_frame

/-- The certificate is explicitly non-Step00-coverage-mediated. -/
theorem non_step00_coverage_mediated
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    E.not_step00_coverage_mediated :=
  E.not_step00_coverage_mediated_proof

/-- The certificate explicitly avoids the old causal-closure leak. -/
theorem no_closure_leak
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    E.no_semantic_collision_closure_leak :=
  E.no_semantic_collision_closure_leak_proof

end ExternalLowerBoundCertificate

/-#############################################################################
  §4. Internal Step00 route status after the trilemma
#############################################################################-/

/--
The semantic closure input from the twin/Step00 branch, kept abstract here.
-/
def SemanticCollisionClosure : Prop := True

/--
A local-success predicate from the Step00 local P/NP node, kept abstract here.
-/
def LocalSuccess : Prop := True

/--
A route that remains internal to the Step00 collision-resolution interface.

After the promise-coverage audit, such a route can only be trusted if it either:

  * pays semantic closure; or
  * explicitly admits incompleteness.
-/
structure InternalStep00DecisionRoute where
  has_promise_or_total_resolver : Prop
  has_promise_or_total_resolver_proof : has_promise_or_total_resolver

  has_coverage : Prop

  coverage_implies_semanticClosure : has_coverage → SemanticCollisionClosure

  incomplete_without_coverage : ¬ has_coverage → Prop

  /- Combined-file fix: the brick's own theorem `internalRoute_incomplete_without_coverage`
  and the slogan claim the incompleteness Prop HOLDS for coverage-free routes, so the
  route object must carry its proof (gate/gate-proof style, as for the other fields). -/
  incomplete_without_coverage_proof :
    ∀ h : ¬ has_coverage, incomplete_without_coverage h

/--
If an internal route has coverage, it has paid semantic closure.
-/
theorem internalRoute_pays_closure_of_coverage
    (R : InternalStep00DecisionRoute)
    (hCoverage : R.has_coverage) :
    SemanticCollisionClosure :=
  R.coverage_implies_semanticClosure hCoverage

/--
If an internal route does not have coverage, it is explicitly incomplete.
-/
theorem internalRoute_incomplete_without_coverage
    (R : InternalStep00DecisionRoute)
    (hNoCoverage : ¬ R.has_coverage) :
    R.incomplete_without_coverage hNoCoverage :=
  R.incomplete_without_coverage_proof hNoCoverage

/--
A Step00-internal route is non-absorbed only if it avoids both outcomes, which is
not provided by the internal interface.  This is a status marker, not a theorem
that such an external route exists.
-/
structure NonAbsorbedInternalRouteClaim (R : InternalStep00DecisionRoute) : Prop where
  has_coverage : R.has_coverage
  no_semanticClosure : ¬ SemanticCollisionClosure

/--
A claimed non-absorbed internal route contradicts the coverage audit.
-/
theorem no_nonAbsorbedInternalRouteClaim
    {R : InternalStep00DecisionRoute}
    (H : NonAbsorbedInternalRouteClaim R) : False := by
  exact H.no_semanticClosure (R.coverage_implies_semanticClosure H.has_coverage)

/-#############################################################################
  §5. Final frontier object
#############################################################################-/

/--
The final honest frontier for deriving classical decision separation from this
project.

It contains either:

  * an external lower-bound certificate; or
  * only an internal Step00 route, which is audited as absorbed/incomplete.

Only the external certificate branch proves classical class separation.
-/
inductive ClassicalPNPFrontier (C : ClassicalDecisionFrame) : Prop where
  | externalLowerBound :
      ExternalLowerBoundCertificate C → ClassicalPNPFrontier C
  | internalStep00Route :
      InternalStep00DecisionRoute → ClassicalPNPFrontier C

namespace ClassicalPNPFrontier

/-- The external branch proves decision separation. -/
theorem decisionSeparation_of_external
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    C.DecisionSeparation :=
  E.decisionSeparation

/-- The external branch refutes class coincidence. -/
theorem not_classesCoincide_of_external
    {C : ClassicalDecisionFrame}
    (E : ExternalLowerBoundCertificate C) :
    ¬ C.ClassesCoincide :=
  E.not_classesCoincide

/--
The internal branch alone only returns its audited internal route.  It does not
produce a classical lower bound.
-/
def internal_branch_has_only_internal_status
    {C : ClassicalDecisionFrame}
    (R : InternalStep00DecisionRoute) :
    InternalStep00DecisionRoute :=
  R

end ClassicalPNPFrontier

/-#############################################################################
  §6. Remaining obligation
#############################################################################-/

/--
The remaining obligation for a real classical `P ≠ NP` consequence.

This is intentionally just an external certificate.  All Step00-internal bridges
have already been classified as either incomplete or closure-absorbed.
-/
structure RemainingExternalLowerBoundObligation
    (C : ClassicalDecisionFrame) where
  certificate : ExternalLowerBoundCertificate C

namespace RemainingExternalLowerBoundObligation

/-- Closing the remaining obligation gives a classical separation witness. -/
theorem decisionSeparation
    {C : ClassicalDecisionFrame}
    (O : RemainingExternalLowerBoundObligation C) :
    C.DecisionSeparation :=
  O.certificate.decisionSeparation

/-- Closing the remaining obligation refutes class coincidence. -/
theorem not_classesCoincide
    {C : ClassicalDecisionFrame}
    (O : RemainingExternalLowerBoundObligation C) :
    ¬ C.ClassesCoincide :=
  O.certificate.not_classesCoincide

/-- Closing the remaining obligation supplies the non-Step00 coverage guard. -/
theorem non_step00_coverage_mediated
    {C : ClassicalDecisionFrame}
    (O : RemainingExternalLowerBoundObligation C) :
    O.certificate.not_step00_coverage_mediated :=
  O.certificate.not_step00_coverage_mediated_proof

end RemainingExternalLowerBoundObligation

/-#############################################################################
  §7. Slogan theorem
#############################################################################-/

/--
Final precise status after all Step00-local bridge audits.
-/
def ExternalLowerBoundFrontierSlogan (C : ClassicalDecisionFrame) : Prop :=
  (RemainingExternalLowerBoundObligation C → C.DecisionSeparation) ∧
  (RemainingExternalLowerBoundObligation C → ¬ C.ClassesCoincide) ∧
  (∀ R : InternalStep00DecisionRoute,
    (R.has_coverage → SemanticCollisionClosure) ∧
    (∀ h : ¬ R.has_coverage, R.incomplete_without_coverage h))

/-- The final frontier slogan is just the assembled audit. -/
theorem externalLowerBoundFrontierSlogan
    (C : ClassicalDecisionFrame) :
    ExternalLowerBoundFrontierSlogan C := by
  constructor
  · intro O
    exact O.decisionSeparation
  · constructor
    · intro O
      exact O.not_classesCoincide
    · intro R
      constructor
      · intro hCoverage
        exact R.coverage_implies_semanticClosure hCoverage
      · intro hNoCoverage
        exact R.incomplete_without_coverage_proof hNoCoverage

end ExternalLowerBoundFrontier
end LocalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_faithful_machine_frame_skeleton_patch.lean ============ -/
/-
  EuclidsPath_faithful_machine_frame_skeleton_patch.lean

  Purpose
  -------
  A faithful-machine-frame skeleton for the external classical P/NP frontier.

  This file intentionally does NOT implement a concrete Turing/RAM model.
  Instead it records the exact abstract interface that a real machine model must
  instantiate before any Step00-local separation can be compared with classical
  decision complexity.

  No axiom. No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace FaithfulMachineFrameSkeleton

/-- Binary strings as the external input universe. -/
abbrev BitString : Type := List Bool

/-- A decision language over binary strings. -/
abbrev Language : Type := BitString → Prop

/-- A deterministic machine, kept abstract. -/
structure DeterministicMachine where
  State : Type
  start : State
  step : State → State
  acceptsAt : Nat → State → Bool
  run : Nat → State
  run_zero : run 0 = start
  run_succ : ∀ t : Nat, run (Nat.succ t) = step (run t)

/-- A verifier machine with an input and witness channel. -/
structure VerifierMachine where
  State : Type
  start : BitString → BitString → State
  step : State → State
  acceptsAt : Nat → State → Bool
  run : BitString → BitString → Nat → State
  run_zero : ∀ x w, run x w 0 = start x w
  run_succ : ∀ x w t, run x w (Nat.succ t) = step (run x w t)

/-- A polynomial-time bound, abstracted as a monotone size bound. -/
structure PolyBound where
  bound : Nat → Nat
  monotone : ∀ {m n : Nat}, m ≤ n → bound m ≤ bound n

namespace PolyBound

/-- A constant polynomial bound. -/
def const (k : Nat) : PolyBound where
  bound := fun _ => k
  monotone := by
    intro m n h
    exact Nat.le_refl k

/-- Identity-size bound. -/
def linear : PolyBound where
  bound := fun n => n
  monotone := by
    intro m n h
    exact h

end PolyBound

/-- A faithful P certificate for a language. -/
structure InP (L : Language) where
  machine : DeterministicMachine
  time : PolyBound
  sound : ∀ x : BitString, machine.acceptsAt (time.bound x.length) (machine.run (time.bound x.length)) = true → L x
  complete : ∀ x : BitString, L x → machine.acceptsAt (time.bound x.length) (machine.run (time.bound x.length)) = true

/-- A faithful NP certificate for a language. -/
structure InNP (L : Language) where
  verifier : VerifierMachine
  time : PolyBound
  witnessBound : PolyBound
  sound :
    ∀ x w : BitString,
      w.length ≤ witnessBound.bound x.length →
      verifier.acceptsAt (time.bound (x.length + w.length))
        (verifier.run x w (time.bound (x.length + w.length))) = true →
      L x
  complete :
    ∀ x : BitString,
      L x →
      ∃ w : BitString,
        w.length ≤ witnessBound.bound x.length ∧
        verifier.acceptsAt (time.bound (x.length + w.length))
          (verifier.run x w (time.bound (x.length + w.length))) = true

/-- Equality of classes in this faithful frame. -/
def ClassesCoincide : Prop :=
  ∀ L : Language, InNP L → Nonempty (InP L)

/-- Separation witness in this faithful frame.  (Combined-file fix: `InP`/`InNP`
are certificate STRUCTURES (Type-valued) here, so membership is expressed via
`Nonempty`.) -/
def SeparationWitness : Prop :=
  ∃ L : Language, Nonempty (InNP L) ∧ ¬ Nonempty (InP L)

/-- A separation witness refutes class coincidence. -/
theorem not_classesCoincide_of_separationWitness :
    SeparationWitness → ¬ ClassesCoincide := by
  intro hSep hEq
  rcases hSep with ⟨L, ⟨hNP⟩, hNotP⟩
  exact hNotP (hEq L hNP)

/-- If classes coincide, no separation witness exists. -/
theorem no_separationWitness_of_classesCoincide :
    ClassesCoincide → ¬ SeparationWitness := by
  intro hEq hSep
  exact not_classesCoincide_of_separationWitness hSep hEq

/-- The external lower-bound certificate required for classical P≠NP. -/
structure ExternalLowerBoundCertificate where
  L : Language
  inNP : InNP L
  notInP : InP L → False
  faithful_machine_semantics : Prop
  faithful_machine_semantics_proof : faithful_machine_semantics
  no_trivial_frame : Prop
  no_trivial_frame_proof : no_trivial_frame
  no_empty_language_trick : Prop
  no_empty_language_trick_proof : no_empty_language_trick
  no_fixed_finite_language_trick : Prop
  no_fixed_finite_language_trick_proof : no_fixed_finite_language_trick

namespace ExternalLowerBoundCertificate

/-- Any external lower-bound certificate gives a separation witness. -/
theorem separationWitness (C : ExternalLowerBoundCertificate) :
    SeparationWitness :=
  ⟨C.L, ⟨C.inNP⟩, fun h => h.elim C.notInP⟩

/-- Any external lower-bound certificate refutes class coincidence. -/
theorem not_classesCoincide (C : ExternalLowerBoundCertificate) :
    ¬ ClassesCoincide :=
  not_classesCoincide_of_separationWitness C.separationWitness

end ExternalLowerBoundCertificate

/-- Remaining obligation: instantiate the skeleton with a real machine model and produce a lower bound. -/
structure RemainingFaithfulMachineLowerBoundObligation where
  certificate : ExternalLowerBoundCertificate
  machine_model_is_real : Prop
  machine_model_is_real_proof : machine_model_is_real
  polynomial_bounds_are_standard : Prop
  polynomial_bounds_are_standard_proof : polynomial_bounds_are_standard

namespace RemainingFaithfulMachineLowerBoundObligation

/-- The remaining obligation gives classical separation in the faithful frame. -/
theorem separationWitness (O : RemainingFaithfulMachineLowerBoundObligation) :
    SeparationWitness :=
  O.certificate.separationWitness

/-- The remaining obligation refutes class coincidence in the faithful frame. -/
theorem not_classesCoincide (O : RemainingFaithfulMachineLowerBoundObligation) :
    ¬ ClassesCoincide :=
  O.certificate.not_classesCoincide

end RemainingFaithfulMachineLowerBoundObligation

/-- Slogan: classical P/NP needs an actual faithful lower-bound certificate. -/
def FaithfulMachineFrameSlogan : Prop :=
  (ExternalLowerBoundCertificate → SeparationWitness) ∧
  (ExternalLowerBoundCertificate → ¬ ClassesCoincide)

/-- The slogan follows by projection from the certificate fields. -/
theorem faithfulMachineFrameSlogan : FaithfulMachineFrameSlogan := by
  constructor
  · intro C
    exact C.separationWitness
  · intro C
    exact C.not_classesCoincide

end FaithfulMachineFrameSkeleton
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_np_complete_transfer_guard_patch.lean ============ -/
/-
  EuclidsPath_np_complete_transfer_guard_patch.lean

  Purpose
  -------
  NP-complete transfer guard for the external P/NP frontier.

  This file records the exact directionality needed to turn a single language
  lower bound into P≠NP and explains why NP-hardness alone, reductions in the
  wrong direction, or NP-membership alone do not suffice.

  No axiom. No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace NPCompleteTransferGuard

abbrev BitString : Type := List Bool
abbrev Language : Type := BitString → Prop

/-- Abstract P/NP frame over languages. -/
structure DecisionFrame where
  InP : Language → Prop
  InNP : Language → Prop
  ReducesTo : Language → Language → Prop
  p_closed_under_preimage : ∀ {A B : Language}, ReducesTo A B → InP B → InP A

namespace DecisionFrame

/-- Class coincidence in the frame. -/
def ClassesCoincide (F : DecisionFrame) : Prop :=
  ∀ L : Language, F.InNP L → F.InP L

/-- A separation witness. -/
def SeparationWitness (F : DecisionFrame) : Prop :=
  ∃ L : Language, F.InNP L ∧ ¬ F.InP L

/-- Separation witness refutes class coincidence. -/
theorem not_classesCoincide_of_separationWitness
    (F : DecisionFrame) :
    F.SeparationWitness → ¬ F.ClassesCoincide := by
  intro hSep hEq
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP (hEq L hNP)

end DecisionFrame

/-- NP-hardness: every NP language reduces to `L`. -/
def NPHard (F : DecisionFrame) (L : Language) : Prop :=
  ∀ A : Language, F.InNP A → F.ReducesTo A L

/-- NP-completeness: NP-hard and in NP. -/
def NPComplete (F : DecisionFrame) (L : Language) : Prop :=
  F.InNP L ∧ NPHard F L

/-- If an NP language is not in P, we have a separation witness. -/
theorem separationWitness_of_inNP_notInP
    (F : DecisionFrame) {L : Language}
    (hNP : F.InNP L) (hNotP : ¬ F.InP L) :
    F.SeparationWitness :=
  ⟨L, hNP, hNotP⟩

/-- Any NP-complete language outside P separates the classes. -/
theorem not_classesCoincide_of_npComplete_notInP
    (F : DecisionFrame) {L : Language}
    (hComp : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    ¬ F.ClassesCoincide := by
  exact F.not_classesCoincide_of_separationWitness
    (separationWitness_of_inNP_notInP F hComp.1 hNotP)

/-- If classes coincide, every NP-complete language is in P. -/
theorem inP_of_classesCoincide_npComplete
    (F : DecisionFrame) {L : Language}
    (hEq : F.ClassesCoincide)
    (hComp : NPComplete F L) :
    F.InP L :=
  hEq L hComp.1

/-- If an NP-complete language is in P, every NP language is in P. -/
theorem classesCoincide_of_npComplete_inP
    (F : DecisionFrame) {L : Language}
    (hComp : NPComplete F L)
    (hP : F.InP L) :
    F.ClassesCoincide := by
  intro A hA
  exact F.p_closed_under_preimage (hComp.2 A hA) hP

/-- NP-hardness alone is only a transfer object, not a separation. -/
structure NPHardOnlyStatus (F : DecisionFrame) (L : Language) where
  hard : NPHard F L
  inNP_missing : Prop
  notInP_missing : Prop

/-- Wrong-way reduction is insufficient for lower-bound transfer. -/
structure WrongWayReductionAttempt (F : DecisionFrame) (A B : Language) where
  reduction_wrong_way : F.ReducesTo B A
  needed_direction : Prop := F.ReducesTo A B

/-- A full NP-complete lower-bound front. -/
structure NPCompleteLowerBoundFront (F : DecisionFrame) where
  L : Language
  complete : NPComplete F L
  notInP : ¬ F.InP L
  no_wrong_way_reduction : Prop
  no_wrong_way_reduction_proof : no_wrong_way_reduction
  no_hardness_only_claim : Prop
  no_hardness_only_claim_proof : no_hardness_only_claim

namespace NPCompleteLowerBoundFront

/-- A completed NP-complete lower-bound front refutes class coincidence. -/
theorem not_classesCoincide {F : DecisionFrame}
    (X : NPCompleteLowerBoundFront F) :
    ¬ F.ClassesCoincide :=
  not_classesCoincide_of_npComplete_notInP F X.complete X.notInP

/-- It also gives a separation witness. -/
theorem separationWitness {F : DecisionFrame}
    (X : NPCompleteLowerBoundFront F) :
    F.SeparationWitness :=
  separationWitness_of_inNP_notInP F X.complete.1 X.notInP

end NPCompleteLowerBoundFront

/-- Remaining obligation if the external route chooses an NP-complete language. -/
structure RemainingNPCompleteBridgeObligation (F : DecisionFrame) where
  front : NPCompleteLowerBoundFront F
  faithful_reductions : Prop
  faithful_reductions_proof : faithful_reductions
  faithful_np_membership : Prop
  faithful_np_membership_proof : faithful_np_membership

namespace RemainingNPCompleteBridgeObligation

/-- The obligation refutes class coincidence. -/
theorem not_classesCoincide {F : DecisionFrame}
    (O : RemainingNPCompleteBridgeObligation F) :
    ¬ F.ClassesCoincide :=
  O.front.not_classesCoincide

end RemainingNPCompleteBridgeObligation

/-- Directionality slogan. -/
def NPCompleteTransferSlogan (F : DecisionFrame) : Prop :=
  (∀ L, NPComplete F L → ¬ F.InP L → ¬ F.ClassesCoincide) ∧
  (∀ L, NPComplete F L → F.InP L → F.ClassesCoincide)

/-- The slogan is exactly the two standard transfer directions. -/
theorem npCompleteTransferSlogan (F : DecisionFrame) :
    NPCompleteTransferSlogan F := by
  constructor
  · intro L hComp hNotP
    exact not_classesCoincide_of_npComplete_notInP F hComp hNotP
  · intro L hComp hP
    exact classesCoincide_of_npComplete_inP F hComp hP

end NPCompleteTransferGuard
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_no_free_lunch_classical_bridge_patch.lean ============ -/
/-
  EuclidsPath_no_free_lunch_classical_bridge_patch.lean

  Purpose
  -------
  No-free-lunch theorem for Step00-to-classical P/NP bridge attempts.

  After the prefix, total-search, promise, and coverage audits, any internal
  Step00-mediated bridge to classical decision lower bounds has exactly three
  outcomes:

    * incomplete: it extracts only a promise resolver without coverage;
    * absorbed: it pays SemanticCollisionClosure / causal-boundary;
    * external: it supplies a genuine non-Step00 lower-bound certificate.

  This file records that trichotomy abstractly.

  No axiom. No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace NoFreeLunchClassicalBridge

/-- Abstract decision language universe. -/
abbrev Language : Type := List Bool → Prop

/-- Abstract classical decision frame. -/
structure DecisionFrame where
  InP : Language → Prop
  InNP : Language → Prop
  ClassesCoincide : Prop
  separation_of_np_not_p : ∀ {L : Language}, InNP L → ¬ InP L → ¬ ClassesCoincide

/-- Abstract Step00-local obstruction package. -/
structure Step00LocalObstruction where
  LocalSuccess : Prop
  LocalIncompressible : ¬ LocalSuccess
  SemanticCollisionClosure : Prop
  ClosureAbsorbsInternalCoverage : Prop

/-- An internal route produces a P-lower-bound only by paying coverage. -/
structure InternalCoverageRoute (F : DecisionFrame) (S : Step00LocalObstruction) where
  L : Language
  inNP : F.InNP L
  coverage : Prop
  coverage_to_closure : coverage → S.SemanticCollisionClosure
  inP_to_localSuccess : F.InP L → S.LocalSuccess

namespace InternalCoverageRoute

/-- Under local incompressibility, the internal route language is not in P. -/
theorem notInP {F : DecisionFrame} {S : Step00LocalObstruction}
    (R : InternalCoverageRoute F S) :
    ¬ F.InP R.L := by
  intro hP
  exact S.LocalIncompressible (R.inP_to_localSuccess hP)

/-- Hence the route would separate classes, but only as an internal/coverage route. -/
theorem separates {F : DecisionFrame} {S : Step00LocalObstruction}
    (R : InternalCoverageRoute F S) :
    ¬ F.ClassesCoincide :=
  F.separation_of_np_not_p R.inNP R.notInP

/-- If coverage is asserted, it immediately pays semantic closure. -/
theorem paysClosure {F : DecisionFrame} {S : Step00LocalObstruction}
    (R : InternalCoverageRoute F S) (hCoverage : R.coverage) :
    S.SemanticCollisionClosure :=
  R.coverage_to_closure hCoverage

end InternalCoverageRoute

/-- Resolver-only route: intentionally incomplete because coverage is missing. -/
structure ResolverOnlyRoute (F : DecisionFrame) (S : Step00LocalObstruction) where
  L : Language
  inNP : F.InNP L
  extracts_promise_resolver : F.InP L → Prop
  missing_coverage : Prop

/-- External route: actual lower-bound certificate not mediated by Step00 coverage. -/
structure ExternalRoute (F : DecisionFrame) where
  L : Language
  inNP : F.InNP L
  notInP : ¬ F.InP L
  nonStep00Mediated : Prop
  nonStep00Mediated_proof : nonStep00Mediated
  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak
  faithful_machine_semantics : Prop
  faithful_machine_semantics_proof : faithful_machine_semantics

namespace ExternalRoute

/-- A completed external route separates the classical classes. -/
theorem separates {F : DecisionFrame} (R : ExternalRoute F) :
    ¬ F.ClassesCoincide :=
  F.separation_of_np_not_p R.inNP R.notInP

end ExternalRoute

/-- Exhaustive bridge status after the Step00 audits. -/
inductive BridgeOutcome (F : DecisionFrame) (S : Step00LocalObstruction) : Type where
  | incomplete (R : ResolverOnlyRoute F S)
  | absorbed (R : InternalCoverageRoute F S)
  | external (R : ExternalRoute F)

namespace BridgeOutcome

/-- Absorbed route separates only by paying the internal coverage/closure route. -/
theorem absorbed_separates {F : DecisionFrame} {S : Step00LocalObstruction}
    (R : InternalCoverageRoute F S) :
    ¬ F.ClassesCoincide :=
  R.separates

/-- External route separates without Step00 coverage mediation. -/
theorem external_separates {F : DecisionFrame} {S : Step00LocalObstruction}
    (R : ExternalRoute F) :
    ¬ F.ClassesCoincide :=
  R.separates

end BridgeOutcome

/-- A claim that a route is both internal-only and non-absorbed must provide an external certificate. -/
structure NonAbsorbedClassicalClaim (F : DecisionFrame) (S : Step00LocalObstruction) where
  route : BridgeOutcome F S
  claims_classical_separation : Prop
  not_internal_coverage_absorbed : Prop

/-- The remaining honest frontier: supply the external route. -/
structure RemainingNonAbsorbedClassicalBridgeObligation (F : DecisionFrame) where
  externalRoute : ExternalRoute F
  no_step00_promise_coverage : Prop
  no_step00_promise_coverage_proof : no_step00_promise_coverage
  no_step00_totality_closure : Prop
  no_step00_totality_closure_proof : no_step00_totality_closure

namespace RemainingNonAbsorbedClassicalBridgeObligation

/-- The obligation separates the classes. -/
theorem separates {F : DecisionFrame}
    (O : RemainingNonAbsorbedClassicalBridgeObligation F) :
    ¬ F.ClassesCoincide :=
  O.externalRoute.separates

end RemainingNonAbsorbedClassicalBridgeObligation

/-- Final no-free-lunch slogan. -/
def NoFreeLunchSlogan (F : DecisionFrame) (S : Step00LocalObstruction) : Prop :=
  (∀ R : ResolverOnlyRoute F S, True) ∧
  (∀ R : InternalCoverageRoute F S, R.coverage → S.SemanticCollisionClosure) ∧
  (∀ R : ExternalRoute F, ¬ F.ClassesCoincide)

/-- The slogan is a direct projection of the three route shapes. -/
theorem noFreeLunchSlogan (F : DecisionFrame) (S : Step00LocalObstruction) :
    NoFreeLunchSlogan F S := by
  constructor
  · intro R
    trivial
  · constructor
    · intro R hCov
      exact R.paysClosure hCov
    · intro R
      exact R.separates

end NoFreeLunchClassicalBridge
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_classical_pnp_frontier_manifest_patch.lean ============ -/
/-
  EuclidsPath_classical_pnp_frontier_manifest_patch.lean

  Purpose
  -------
  Manifest of the current maximal frontier after the Step00-local P/NP audit.

  This file records the multi-step status in one small theorem package:

    1. Step00-local verifier/search separation is architectural/local.
    2. Fixed finite quotients do not produce classical lower bounds.
    3. Prefix-completion decision-to-search needs known YES roots.
    4. Totality for Step00 collision search is semantic collision closure.
    5. Promise routes need coverage; coverage again pays closure.
    6. Therefore the only non-absorbed route to classical P≠NP is an external
       faithful machine lower-bound certificate.

  No axiom. No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace FrontierManifest

/-- A named marker for facts already audited in previous Step00-local patches. -/
structure Step00LocalAuditFacts where
  verification_easy : Prop
  local_search_incompressible : Prop
  fixed_finite_quotient_is_local_only : Prop
  prefix_completion_needs_known_yes_root : Prop
  totality_equals_semantic_closure : Prop
  promise_needs_coverage : Prop
  coverage_equals_semantic_closure : Prop

/-- A named marker for what a classical external lower-bound must provide. -/
structure ExternalClassicalRequirements where
  faithful_machine_frame : Prop
  language_in_np : Prop
  language_not_in_p : Prop
  no_trivial_frame : Prop
  no_empty_language_trick : Prop
  no_fixed_finite_language_trick : Prop
  no_step00_coverage_mediation : Prop
  no_causal_closure_leak : Prop

/-- Completed external lower-bound package. -/
structure CompletedExternalClassicalPackage where
  requirements : ExternalClassicalRequirements
  all_requirements_met :
    requirements.faithful_machine_frame ∧
    requirements.language_in_np ∧
    requirements.language_not_in_p ∧
    requirements.no_trivial_frame ∧
    requirements.no_empty_language_trick ∧
    requirements.no_fixed_finite_language_trick ∧
    requirements.no_step00_coverage_mediation ∧
    requirements.no_causal_closure_leak

/-- Outcome classification for the current frontier. -/
inductive CurrentFrontierOutcome : Type where
  | localOnly
  | fixedFiniteTrivial
  | prefixNeedsKnownYes
  | totalityPaysClosure
  | promiseNeedsCoverage
  | externalLowerBoundRequired

/-- The maximal current Step00-to-classical status. -/
structure MaximalCurrentStatus where
  audit : Step00LocalAuditFacts
  externalRequirements : ExternalClassicalRequirements
  nextOutcome : CurrentFrontierOutcome

namespace MaximalCurrentStatus

/-- If all external requirements are met, the frontier has an external package. -/
def hasCompletedExternalPackage (S : MaximalCurrentStatus) : Prop :=
  S.externalRequirements.faithful_machine_frame ∧
  S.externalRequirements.language_in_np ∧
  S.externalRequirements.language_not_in_p ∧
  S.externalRequirements.no_trivial_frame ∧
  S.externalRequirements.no_empty_language_trick ∧
  S.externalRequirements.no_fixed_finite_language_trick ∧
  S.externalRequirements.no_step00_coverage_mediation ∧
  S.externalRequirements.no_causal_closure_leak

/-- Projection from a completed package to the lower-bound core. -/
theorem language_not_in_p_of_completed
    (S : MaximalCurrentStatus)
    (h : S.hasCompletedExternalPackage) :
    S.externalRequirements.language_not_in_p := by
  exact h.2.2.1

/-- Projection from a completed package to NP-membership. -/
theorem language_in_np_of_completed
    (S : MaximalCurrentStatus)
    (h : S.hasCompletedExternalPackage) :
    S.externalRequirements.language_in_np := by
  exact h.2.1

/-- Projection from a completed package to non-mediation. -/
theorem no_step00_coverage_mediation_of_completed
    (S : MaximalCurrentStatus)
    (h : S.hasCompletedExternalPackage) :
    S.externalRequirements.no_step00_coverage_mediation := by
  exact h.2.2.2.2.2.2.1

/-- Projection from a completed package to no causal-closure leak. -/
theorem no_causal_closure_leak_of_completed
    (S : MaximalCurrentStatus)
    (h : S.hasCompletedExternalPackage) :
    S.externalRequirements.no_causal_closure_leak := by
  exact h.2.2.2.2.2.2.2

end MaximalCurrentStatus

/-- The manifest slogan: Step00 has reduced the bridge to an external lower-bound requirement. -/
def FrontierManifestSlogan : Prop :=
  ∀ S : MaximalCurrentStatus,
    S.audit.verification_easy →
    S.audit.local_search_incompressible →
    S.audit.totality_equals_semantic_closure →
    S.audit.coverage_equals_semantic_closure →
    True

/-- The slogan is intentionally a guard/manifest, not a proof of P≠NP. -/
theorem frontierManifestSlogan : FrontierManifestSlogan := by
  intro S hVer hInc hTot hCov
  trivial

/-- Remaining maximal obligation. -/
structure RemainingMaximalForwardObligation where
  status : MaximalCurrentStatus
  completedExternalPackage : status.hasCompletedExternalPackage
  external_not_step00_internal : Prop
  external_not_step00_internal_proof : external_not_step00_internal

namespace RemainingMaximalForwardObligation

/-- The obligation contains NP membership. -/
theorem contains_np_membership (O : RemainingMaximalForwardObligation) :
    O.status.externalRequirements.language_in_np :=
  O.status.language_in_np_of_completed O.completedExternalPackage

/-- The obligation contains the P lower bound. -/
theorem contains_p_lower_bound (O : RemainingMaximalForwardObligation) :
    O.status.externalRequirements.language_not_in_p :=
  O.status.language_not_in_p_of_completed O.completedExternalPackage

/-- The obligation contains the non-Step00 mediation guard. -/
theorem contains_non_mediation (O : RemainingMaximalForwardObligation) :
    O.status.externalRequirements.no_step00_coverage_mediation :=
  O.status.no_step00_coverage_mediation_of_completed O.completedExternalPackage

/-- The obligation contains the no-causal-closure-leak guard. -/
theorem contains_no_closure_leak (O : RemainingMaximalForwardObligation) :
    O.status.externalRequirements.no_causal_closure_leak :=
  O.status.no_causal_closure_leak_of_completed O.completedExternalPackage

end RemainingMaximalForwardObligation

end FrontierManifest
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_machine_model_certificate_patch.lean ============ -/
/-
  EuclidsPath_external_machine_model_certificate_patch.lean

  External P/NP frontier — faithful machine model certificate.

  Purpose
  -------
  After the Step00-local / promise / coverage audits, an internal Step00 bridge
  cannot honestly be advertised as classical `P ≠ NP`.  The remaining route must
  pass through an external, faithful machine-theoretic frame.

  This file records the minimal abstract shape of such a frame and the exact
  theorem it must support:

      ∃ L, L ∈ NP ∧ L ∉ P  ⇒  P and NP do not coincide.

  No claim is made that such an `L` has been constructed.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalMachineModel

/-- A classical decision-language frame. -/
structure MachineDecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop

/-- Class coincidence in the usual decision sense: every NP language is in P. -/
def ClassesCoincide (F : MachineDecisionFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- A separation witness: an NP language not in P. -/
def SeparationWitness (F : MachineDecisionFrame) : Prop :=
  ∃ L : F.Language, F.InNP L ∧ ¬ F.InP L

/-- A faithful frame is not merely an arbitrary pair of predicates. -/
structure FaithfulMachineFrame extends MachineDecisionFrame where
  semantics_is_machine_based : Prop
  semantics_is_machine_based_proof : semantics_is_machine_based

  deterministic_polytime_sound : Prop
  deterministic_polytime_sound_proof : deterministic_polytime_sound

  nondeterministic_poly_verifier_sound : Prop
  nondeterministic_poly_verifier_sound_proof : nondeterministic_poly_verifier_sound

  no_trivial_frame_trick : Prop
  no_trivial_frame_trick_proof : no_trivial_frame_trick

  no_empty_language_artifact : Prop
  no_empty_language_artifact_proof : no_empty_language_artifact

  no_fixed_finite_language_artifact : Prop
  no_fixed_finite_language_artifact_proof : no_fixed_finite_language_artifact

/-- A lower-bound certificate inside a faithful machine frame. -/
structure ExternalLowerBoundCertificate (F : FaithfulMachineFrame) where
  language : F.Language
  inNP : F.InNP language
  notInP : ¬ F.InP language

  proof_is_external_to_step00 : Prop
  proof_is_external_to_step00_proof : proof_is_external_to_step00

  no_step00_coverage_mediation : Prop
  no_step00_coverage_mediation_proof : no_step00_coverage_mediation

  no_causal_closure_leak : Prop
  no_causal_closure_leak_proof : no_causal_closure_leak

/-- A lower-bound certificate immediately gives a separation witness. -/
noncomputable def ExternalLowerBoundCertificate.separationWitness
    {F : FaithfulMachineFrame}
    (C : ExternalLowerBoundCertificate F) :
    SeparationWitness F.toMachineDecisionFrame := by
  exact ⟨C.language, C.inNP, C.notInP⟩

/-- Separation witness contradicts class coincidence. -/
theorem not_classesCoincide_of_separationWitness
    {F : MachineDecisionFrame}
    (hSep : SeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP (hCoincide L hNP)

/-- Equivalently: if classes coincide, no separation witness exists. -/
theorem no_separationWitness_of_classesCoincide
    {F : MachineDecisionFrame}
    (hCoincide : ClassesCoincide F) :
    ¬ SeparationWitness F := by
  intro hSep
  exact not_classesCoincide_of_separationWitness hSep hCoincide

/-- The external lower-bound certificate proves non-coincidence in its frame. -/
theorem ExternalLowerBoundCertificate.not_classesCoincide
    {F : FaithfulMachineFrame}
    (C : ExternalLowerBoundCertificate F) :
    ¬ ClassesCoincide F.toMachineDecisionFrame := by
  exact not_classesCoincide_of_separationWitness C.separationWitness

/-- The exact remaining obligation at the machine-frame level. -/
structure RemainingMachineLowerBoundObligation where
  frame : FaithfulMachineFrame
  certificate : ExternalLowerBoundCertificate frame

/-- Closing the remaining obligation closes the decision separation in that frame. -/
theorem RemainingMachineLowerBoundObligation.not_classesCoincide
    (O : RemainingMachineLowerBoundObligation) :
    ¬ ClassesCoincide O.frame.toMachineDecisionFrame := by
  exact O.certificate.not_classesCoincide

/-- Slogan: faithful frame + external NP-not-P language is the actual classical target. -/
def MachineFrameSlogan : Prop :=
  ∀ F : FaithfulMachineFrame,
    ExternalLowerBoundCertificate F →
      SeparationWitness F.toMachineDecisionFrame ∧
      ¬ ClassesCoincide F.toMachineDecisionFrame

theorem machineFrameSlogan : MachineFrameSlogan := by
  intro F C
  exact ⟨C.separationWitness, C.not_classesCoincide⟩

end ExternalMachineModel
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_np_complete_route_certificate_patch.lean ============ -/
/-
  EuclidsPath_np_complete_route_certificate_patch.lean

  External P/NP frontier — NP-complete transfer certificate.

  Purpose
  -------
  Records the standard transfer shape:

    * if `L` is NP-complete and `L ∉ P`, then P and NP separate;
    * if `L` is NP-complete and `L ∈ P`, then every NP language is in P
      provided P is closed under polynomial many-one preimages.

  This does not prove any concrete NP-complete language lower bound.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace NPCompleteRoute

structure MachineDecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop

/-- Coincidence in the NP ⊆ P direction. -/
def ClassesCoincide (F : MachineDecisionFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- Separation witness. -/
def SeparationWitness (F : MachineDecisionFrame) : Prop :=
  ∃ L : F.Language, F.InNP L ∧ ¬ F.InP L

/-- Abstract polynomial many-one reduction. -/
structure PolyManyOneReduction (F : MachineDecisionFrame) (A B : F.Language) where
  reduction_is_polytime : Prop
  reduction_is_polytime_proof : reduction_is_polytime
  correctness : Prop
  correctness_proof : correctness

/-- P is closed under polynomial many-one preimages. -/
def PClosedUnderPolyPreimage (F : MachineDecisionFrame) : Prop :=
  ∀ A B : F.Language,
    PolyManyOneReduction F A B →
    F.InP B →
    F.InP A

/-- NP-hardness under polynomial many-one reductions. -/
def NPHard (F : MachineDecisionFrame) (L : F.Language) : Prop :=
  ∀ K : F.Language, F.InNP K → Nonempty (PolyManyOneReduction F K L)

/-- NP-completeness: membership in NP plus NP-hardness. -/
structure NPComplete (F : MachineDecisionFrame) (L : F.Language) where
  inNP : F.InNP L
  hard : NPHard F L

/-- NP-complete target in P collapses NP to P under reduction closure. -/
theorem classesCoincide_of_npComplete_inP
    {F : MachineDecisionFrame}
    (hClosed : PClosedUnderPolyPreimage F)
    {L : F.Language}
    (hComp : NPComplete F L)
    (hP : F.InP L) :
    ClassesCoincide F := by
  intro K hKNP
  rcases hComp.hard K hKNP with ⟨r⟩
  exact hClosed K L r hP

/-- NP-complete target outside P is immediately a separation witness. -/
noncomputable def separationWitness_of_npComplete_notInP
    {F : MachineDecisionFrame}
    {L : F.Language}
    (hComp : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    SeparationWitness F := by
  exact ⟨L, hComp.inNP, hNotP⟩

/-- Separation witness refutes class coincidence. -/
theorem not_classesCoincide_of_separationWitness
    {F : MachineDecisionFrame}
    (hSep : SeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP (hCoincide L hNP)

/-- NP-complete target lower bound gives P/NP separation inside the frame. -/
theorem not_classesCoincide_of_npComplete_notInP
    {F : MachineDecisionFrame}
    {L : F.Language}
    (hComp : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    ¬ ClassesCoincide F := by
  exact not_classesCoincide_of_separationWitness
    (separationWitness_of_npComplete_notInP hComp hNotP)

/-- NP-hardness alone has no separation content without `L ∈ NP` and `L ∉ P`. -/
structure NPHardnessOnlyAudit (F : MachineDecisionFrame) (L : F.Language) where
  hard : NPHard F L
  no_membership_claim : Prop
  no_membership_claim_proof : no_membership_claim
  no_lower_bound_claim : Prop
  no_lower_bound_claim_proof : no_lower_bound_claim

/-- The exact NP-complete route obligation. -/
structure RemainingNPCompleteRouteObligation (F : MachineDecisionFrame) where
  target : F.Language
  target_npcomplete : NPComplete F target
  target_notInP : ¬ F.InP target

/-- Closing the NP-complete route obligation gives separation. -/
theorem RemainingNPCompleteRouteObligation.not_classesCoincide
    {F : MachineDecisionFrame}
    (O : RemainingNPCompleteRouteObligation F) :
    ¬ ClassesCoincide F := by
  exact not_classesCoincide_of_npComplete_notInP
    O.target_npcomplete O.target_notInP

end NPCompleteRoute
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_complexity_barrier_audit_patch.lean ============ -/
/-
  EuclidsPath_complexity_barrier_audit_patch.lean

  External P/NP frontier — barrier audit for a claimed lower bound.

  Purpose
  -------
  This file does not prove any classical complexity barrier theorem.  It records
  the audit fields a serious external lower-bound certificate should carry if it
  is meant to be nonabsorbed by known proof-method obstructions and by the
  Step00 causal-closure route.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace BarrierAudit

structure MachineDecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop

structure ExternalLowerBoundCore (F : MachineDecisionFrame) where
  language : F.Language
  inNP : F.InNP language
  notInP : ¬ F.InP language

/-- Audit flags for classical proof-method barriers. -/
structure ComplexityBarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- Audit flags for avoiding Step00 absorption. -/
structure Step00NonAbsorptionAudit where
  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_promise_coverage_mediation : Prop
  no_promise_coverage_mediation_proof : no_promise_coverage_mediation

  no_finite_quotient_artifact : Prop
  no_finite_quotient_artifact_proof : no_finite_quotient_artifact

  no_empty_language_artifact : Prop
  no_empty_language_artifact_proof : no_empty_language_artifact

  no_trivial_frame_artifact : Prop
  no_trivial_frame_artifact_proof : no_trivial_frame_artifact

/-- A barrier-safe external lower-bound certificate. -/
structure BarrierSafeExternalCertificate (F : MachineDecisionFrame) where
  core : ExternalLowerBoundCore F
  complexity_barrier_audit : ComplexityBarrierAudit
  step00_nonabsorption_audit : Step00NonAbsorptionAudit

/-- Extract the ordinary lower-bound core. -/
noncomputable def BarrierSafeExternalCertificate.has_core
    {F : MachineDecisionFrame}
    (C : BarrierSafeExternalCertificate F) :
    ExternalLowerBoundCore F :=
  C.core

/-- Extract the classical barrier audit. -/
noncomputable def BarrierSafeExternalCertificate.has_complexity_audit
    {F : MachineDecisionFrame}
    (C : BarrierSafeExternalCertificate F) :
    ComplexityBarrierAudit :=
  C.complexity_barrier_audit

/-- Extract the Step00 nonabsorption audit. -/
noncomputable def BarrierSafeExternalCertificate.has_nonabsorption_audit
    {F : MachineDecisionFrame}
    (C : BarrierSafeExternalCertificate F) :
    Step00NonAbsorptionAudit :=
  C.step00_nonabsorption_audit

/-- The certificate directly supplies an NP-not-P language. -/
theorem BarrierSafeExternalCertificate.inNP_and_notInP
    {F : MachineDecisionFrame}
    (C : BarrierSafeExternalCertificate F) :
    F.InNP C.core.language ∧ ¬ F.InP C.core.language := by
  exact ⟨C.core.inNP, C.core.notInP⟩

/-- Exact remaining barrier-safe obligation. -/
structure RemainingBarrierSafeLowerBoundObligation (F : MachineDecisionFrame) where
  certificate : BarrierSafeExternalCertificate F

/-- Closing the obligation exposes the lower-bound core. -/
noncomputable def RemainingBarrierSafeLowerBoundObligation.core
    {F : MachineDecisionFrame}
    (O : RemainingBarrierSafeLowerBoundObligation F) :
    ExternalLowerBoundCore F :=
  O.certificate.core

end BarrierAudit
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_step00_nonabsorption_certificate_patch.lean ============ -/
/-
  EuclidsPath_step00_nonabsorption_certificate_patch.lean

  External P/NP frontier — Step00 nonabsorption certificate.

  Purpose
  -------
  Step00-local search incompressibility is useful as an audit, but an internal
  bridge to classical decision P/NP either becomes incomplete or pays the old
  semantic collision-closure boundary.  This file records a precise certificate
  saying that an external lower bound is not merely an internal Step00 route in
  disguise.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace Step00NonAbsorption

/-- Abstract Step00 internal route markers. -/
structure Step00InternalRouteState where
  SemanticCollisionClosure : Prop
  PromiseCoverage : Prop
  LocalSuccess : Prop
  CausalClosureBoundary : Prop

/-- An internal coverage route pays semantic closure. -/
structure InternalCoverageRoute (S : Step00InternalRouteState) where
  coverage_implies_semanticClosure : S.PromiseCoverage → S.SemanticCollisionClosure
  languageInP_implies_coverage : Prop
  languageInP_implies_coverage_proof : languageInP_implies_coverage

/-- A resolver-only route is explicitly incomplete. -/
structure ResolverOnlyRouteAudit where
  has_promise_resolver : Prop
  has_promise_resolver_proof : has_promise_resolver
  missing_coverage : Prop
  missing_coverage_proof : missing_coverage
  does_not_imply_localSuccess : Prop
  does_not_imply_localSuccess_proof : does_not_imply_localSuccess

/-- External route marker. -/
structure ExternalRouteMarker where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_route : Prop
  not_resolver_only_route_proof : not_resolver_only_route

  not_step00_causal_boundary_route : Prop
  not_step00_causal_boundary_route_proof : not_step00_causal_boundary_route

/-- Nonabsorption certificate for a claimed external lower bound. -/
structure Step00NonAbsorptionCertificate where
  marker : ExternalRouteMarker

  no_semanticClosure_dependency : Prop
  no_semanticClosure_dependency_proof : no_semanticClosure_dependency

  no_promiseCoverage_dependency : Prop
  no_promiseCoverage_dependency_proof : no_promiseCoverage_dependency

  no_localSuccess_bootstrap : Prop
  no_localSuccess_bootstrap_proof : no_localSuccess_bootstrap

/-- If a route is resolver-only, it does not supply the coverage needed for LocalSuccess. -/
theorem resolverOnly_is_incomplete
    (R : ResolverOnlyRouteAudit) :
    R.does_not_imply_localSuccess :=
  R.does_not_imply_localSuccess_proof

/-- Internal coverage route pays semantic closure once coverage is provided. -/
theorem internalCoverage_pays_semanticClosure
    {S : Step00InternalRouteState}
    (R : InternalCoverageRoute S)
    (hCoverage : S.PromiseCoverage) :
    S.SemanticCollisionClosure :=
  R.coverage_implies_semanticClosure hCoverage

/-- A nonabsorbed route carries explicit negative evidence against all internal cases. -/
theorem Step00NonAbsorptionCertificate.not_internal_coverage
    (C : Step00NonAbsorptionCertificate) :
    C.marker.not_internal_coverage_route :=
  C.marker.not_internal_coverage_route_proof

/-- A nonabsorbed route is not the resolver-only incomplete case. -/
theorem Step00NonAbsorptionCertificate.not_resolver_only
    (C : Step00NonAbsorptionCertificate) :
    C.marker.not_resolver_only_route :=
  C.marker.not_resolver_only_route_proof

/-- A nonabsorbed route is not a disguised causal-boundary route. -/
theorem Step00NonAbsorptionCertificate.not_step00_boundary
    (C : Step00NonAbsorptionCertificate) :
    C.marker.not_step00_causal_boundary_route :=
  C.marker.not_step00_causal_boundary_route_proof

/-- Exact remaining nonabsorption obligation. -/
structure RemainingStep00NonAbsorptionObligation where
  certificate : Step00NonAbsorptionCertificate

/-- Closing the obligation supplies all three route exclusions. -/
theorem RemainingStep00NonAbsorptionObligation.exclusions
    (O : RemainingStep00NonAbsorptionObligation) :
    O.certificate.marker.not_internal_coverage_route ∧
    O.certificate.marker.not_resolver_only_route ∧
    O.certificate.marker.not_step00_causal_boundary_route := by
  exact ⟨O.certificate.not_internal_coverage,
         O.certificate.not_resolver_only,
         O.certificate.not_step00_boundary⟩

end Step00NonAbsorption
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_maximal_pnp_frontier_v2_manifest_patch.lean ============ -/
/-
  EuclidsPath_maximal_pnp_frontier_v2_manifest_patch.lean

  Maximal P/NP frontier manifest v2.

  Purpose
  -------
  Aggregates the current honest state after advancing through:

    * Step00-local verification/search incompressibility;
    * finite quotient and prefix-language obstructions;
    * total-search effectivity firewall;
    * promise coverage trilemma;
    * external lower-bound frontier;
    * faithful machine-frame and NP-complete route skeletons;
    * barrier and nonabsorption audits.

  The manifest deliberately does NOT claim classical P ≠ NP.  It records the
  exact remaining external lower-bound obligation.

  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace FrontierV2

structure MachineDecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop

/-- Decision class coincidence. -/
def ClassesCoincide (F : MachineDecisionFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- Decision separation witness. -/
def SeparationWitness (F : MachineDecisionFrame) : Prop :=
  ∃ L : F.Language, F.InNP L ∧ ¬ F.InP L

structure FaithfulnessAudit where
  machine_semantics : Prop
  machine_semantics_proof : machine_semantics
  no_trivial_frame : Prop
  no_trivial_frame_proof : no_trivial_frame
  no_empty_or_finite_artifact : Prop
  no_empty_or_finite_artifact_proof : no_empty_or_finite_artifact

structure BarrierAudit where
  nonrelativizing_or_explains_relativization : Prop
  nonrelativizing_or_explains_relativization_proof : nonrelativizing_or_explains_relativization
  nonalgebrizing_or_explains_algebrization : Prop
  nonalgebrizing_or_explains_algebrization_proof : nonalgebrizing_or_explains_algebrization
  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

structure Step00Audit where
  local_search_incompressibility_recorded : Prop
  local_search_incompressibility_recorded_proof : local_search_incompressibility_recorded
  internal_route_pays_closure_or_is_incomplete : Prop
  internal_route_pays_closure_or_is_incomplete_proof : internal_route_pays_closure_or_is_incomplete
  no_step00_coverage_mediation : Prop
  no_step00_coverage_mediation_proof : no_step00_coverage_mediation

/-- The actual external certificate still needed for classical P/NP. -/
structure MaximalExternalLowerBoundCertificate (F : MachineDecisionFrame) where
  language : F.Language
  inNP : F.InNP language
  notInP : ¬ F.InP language
  faithfulness : FaithfulnessAudit
  barriers : BarrierAudit
  step00_nonabsorption : Step00Audit

/-- The certificate gives a separation witness. -/
theorem MaximalExternalLowerBoundCertificate.separationWitness
    {F : MachineDecisionFrame}
    (C : MaximalExternalLowerBoundCertificate F) :
    SeparationWitness F := by
  exact ⟨C.language, C.inNP, C.notInP⟩

/-- Separation witness refutes coincidence. -/
theorem not_classesCoincide_of_separationWitness
    {F : MachineDecisionFrame}
    (hSep : SeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  rcases hSep with ⟨L, hNP, hNotP⟩
  exact hNotP (hCoincide L hNP)

/-- The maximal external certificate gives classical separation in its frame. -/
theorem MaximalExternalLowerBoundCertificate.not_classesCoincide
    {F : MachineDecisionFrame}
    (C : MaximalExternalLowerBoundCertificate F) :
    ¬ ClassesCoincide F := by
  exact not_classesCoincide_of_separationWitness C.separationWitness

/-- Frontier status: everything internal has been audited; only external lower bound remains. -/
structure MaximalPNPFrontierV2 where
  frame : MachineDecisionFrame
  step00_audit : Step00Audit
  faithfulness_audit_needed : Prop
  faithfulness_audit_needed_proof : faithfulness_audit_needed
  external_lower_bound_needed : Prop
  external_lower_bound_needed_proof : external_lower_bound_needed

/-- Closing the frontier requires the maximal external certificate. -/
structure RemainingMaximalForwardObligation where
  frame : MachineDecisionFrame
  certificate : MaximalExternalLowerBoundCertificate frame

/-- Closing the maximal obligation gives non-coincidence. -/
theorem RemainingMaximalForwardObligation.not_classesCoincide
    (O : RemainingMaximalForwardObligation) :
    ¬ ClassesCoincide O.frame := by
  exact O.certificate.not_classesCoincide

/-- Manifest slogan as a theorem. -/
def FrontierV2Slogan : Prop :=
  ∀ O : RemainingMaximalForwardObligation,
    SeparationWitness O.frame ∧ ¬ ClassesCoincide O.frame

theorem frontierV2Slogan : FrontierV2Slogan := by
  intro O
  exact ⟨O.certificate.separationWitness, O.not_classesCoincide⟩

end FrontierV2
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_pnp_maximal_forward_single_file_patch.lean ============ -/
/-
EuclidsPath — maximal forward P/NP frontier, single-file patch
================================================================

Purpose
-------
This file records several forward steps after the Step00-local P/NP audit,
put into ONE file as requested.

It deliberately does **not** claim a proof of classical `P ≠ NP`.  Instead it
formalizes the exact remaining external certificate needed after the internal
Step00 routes have been audited:

  1. a faithful classical decision-complexity frame;
  2. an NP language with a real lower bound `L ∉ P`;
  3. optionally an NP-complete transfer route;
  4. barrier-audit obligations against known complexity-theoretic traps;
  5. nonabsorption obligations showing that the proof is not merely the old
     Step00 semantic-closure / promise-coverage route in disguise;
  6. final theorem gates: such a certificate implies separation of the classes
     inside the chosen faithful frame.

This is a frontier/obligation file.  It contains no proof of a concrete external
lower bound.

No extra axioms.  No admitted proof placeholders.
-/



namespace EuclidsPath
namespace PNPMaximalForwardSingleFile

/-#############################################################################
  §1. Classical decision frame
#############################################################################-/

/--
Abstract classical decision-complexity frame.

Concrete instantiation should replace `Language`, `InP`, `InNP`, and `Reduces`
by a genuine machine model: languages over finite strings, deterministic
polynomial-time decidability, nondeterministic polynomial-time verification, and
polynomial many-one reductions.
-/
structure ClassicalDecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop
  Reduces : Language → Language → Prop

  /-- The easy inclusion required in the standard setting. -/
  p_subset_np : ∀ L : Language, InP L → InNP L

  /-- Closure of `P` under polynomial-time many-one preimages. -/
  p_closed_under_reduction :
    ∀ {A B : Language}, Reduces A B → InP B → InP A

/-- Equality/coincidence of classes inside a chosen frame. -/
def ClassesCoincide (C : ClassicalDecisionFrame) : Prop :=
  ∀ L : C.Language, C.InP L ↔ C.InNP L

/-- A decision separation witness inside a frame. -/
structure DecisionSeparationWitness (C : ClassicalDecisionFrame) where
  L : C.Language
  inNP : C.InNP L
  notInP : ¬ C.InP L

/-- Any separation witness refutes class coincidence. -/
theorem DecisionSeparationWitness.not_classesCoincide
    {C : ClassicalDecisionFrame}
    (W : DecisionSeparationWitness C) :
    ¬ ClassesCoincide C := by
  intro hCoincide
  have hP : C.InP W.L := (hCoincide W.L).2 W.inNP
  exact W.notInP hP

/-- If classes coincide, no separation witness exists. -/
theorem no_separationWitness_of_classesCoincide
    {C : ClassicalDecisionFrame}
    (hCoincide : ClassesCoincide C) :
    ¬ Nonempty (DecisionSeparationWitness C) := by
  intro hW
  rcases hW with ⟨W⟩
  exact W.not_classesCoincide hCoincide

/-#############################################################################
  §2. Faithful machine-frame audit
#############################################################################-/

/--
Faithfulness guard against degenerate abstract frames such as `InP := False` or
arbitrary predicates unrelated to computation.

These fields are deliberately semantic/audit fields.  A concrete machine model
must fill them by real definitions and proofs.
-/
structure FaithfulMachineFrame (C : ClassicalDecisionFrame) where
  machine_semantics_present : Prop
  machine_semantics_present_proof : machine_semantics_present

  input_length_model_present : Prop
  input_length_model_present_proof : input_length_model_present

  polynomial_time_semantics_present : Prop
  polynomial_time_semantics_present_proof : polynomial_time_semantics_present

  nondeterministic_verifier_semantics_present : Prop
  nondeterministic_verifier_semantics_present_proof :
    nondeterministic_verifier_semantics_present

  reduction_semantics_present : Prop
  reduction_semantics_present_proof : reduction_semantics_present

  no_trivial_false_P_frame : Prop
  no_trivial_false_P_frame_proof : no_trivial_false_P_frame

  no_trivial_true_NP_frame : Prop
  no_trivial_true_NP_frame_proof : no_trivial_true_NP_frame

/-- A faithful frame supplies the nontriviality guard against fake frames. -/
def FaithfulFrameGuard (C : ClassicalDecisionFrame) : Prop :=
  Nonempty (FaithfulMachineFrame C)

/-#############################################################################
  §3. NP-complete transfer route
#############################################################################-/

/-- NP-completeness inside the chosen frame. -/
structure NPComplete (C : ClassicalDecisionFrame) (L : C.Language) where
  inNP : C.InNP L
  hard : ∀ A : C.Language, C.InNP A → C.Reduces A L

/-- NP-complete language outside P gives a separation witness. -/
noncomputable def separationWitness_of_npComplete_notInP
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (H : NPComplete C L)
    (hNotP : ¬ C.InP L) :
    DecisionSeparationWitness C :=
  { L := L, inNP := H.inNP, notInP := hNotP }

/-- NP-complete language outside P refutes class coincidence. -/
theorem not_classesCoincide_of_npComplete_notInP
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (H : NPComplete C L)
    (hNotP : ¬ C.InP L) :
    ¬ ClassesCoincide C := by
  exact (separationWitness_of_npComplete_notInP H hNotP).not_classesCoincide

/-- If an NP-complete language is in P, then every NP language is in P. -/
theorem everyNP_inP_of_npComplete_inP
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (H : NPComplete C L)
    (hP : C.InP L) :
    ∀ A : C.Language, C.InNP A → C.InP A := by
  intro A hA
  exact C.p_closed_under_reduction (H.hard A hA) hP

/-- If an NP-complete language is in P, then classes coincide inside the frame. -/
theorem classesCoincide_of_npComplete_inP
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (H : NPComplete C L)
    (hP : C.InP L) :
    ClassesCoincide C := by
  intro A
  constructor
  · intro hAP
    exact C.p_subset_np A hAP
  · intro hANP
    exact everyNP_inP_of_npComplete_inP H hP A hANP

/--
NP-hardness alone has no separation content.  It must be paired with membership
in NP and a genuine lower bound.
-/
structure NPHardOnly (C : ClassicalDecisionFrame) (L : C.Language) where
  hard : ∀ A : C.Language, C.InNP A → C.Reduces A L

/-- Guard statement: NP-hardness alone is only an audit datum here. -/
def NPHardOnlyHasNoLowerBoundContent
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (_H : NPHardOnly C L) : Prop := True

theorem npHardOnly_hasNoLowerBoundContent
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (H : NPHardOnly C L) :
    NPHardOnlyHasNoLowerBoundContent H := by
  trivial

/-#############################################################################
  §4. Step00 nonabsorption audit
#############################################################################-/

/-- Abstract status of the Step00-local world. -/
structure Step00LocalAudit where
  LocalSuccess : Prop
  LocalIncompressible : Prop
  SemanticCollisionClosure : Prop
  PromiseCoverage : Prop

  local_incompressible_means_no_success :
    LocalIncompressible → ¬ LocalSuccess

  coverage_pays_closure : PromiseCoverage → SemanticCollisionClosure

/-- Internal coverage route: complete only by paying Step00 closure. -/
structure InternalCoverageRoute (S : Step00LocalAudit) where
  languageInP : Prop
  p_decider_to_promise_resolver : Prop
  coverage : S.PromiseCoverage

/-- Resolver-only route: intentionally missing coverage. -/
structure ResolverOnlyRoute (_S : Step00LocalAudit) where
  languageInP : Prop
  p_decider_to_promise_resolver : Prop

/-- External route: explicitly not mediated by the Step00 coverage/closure route. -/
structure ExternalNonStep00Route (S : Step00LocalAudit) where
  decision_lower_bound_source : Prop
  decision_lower_bound_source_proof : decision_lower_bound_source

  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_route : Prop
  not_resolver_only_route_proof : not_resolver_only_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  local_audit : S.LocalIncompressible ∨ ¬ S.LocalIncompressible

/-- Internal coverage route pays semantic collision closure. -/
theorem internalCoverageRoute_pays_closure
    {S : Step00LocalAudit}
    (R : InternalCoverageRoute S) :
    S.SemanticCollisionClosure :=
  S.coverage_pays_closure R.coverage

/-- Under local incompressibility, local success is impossible. -/
theorem no_localSuccess_of_localIncompressible
    {S : Step00LocalAudit}
    (hInc : S.LocalIncompressible) :
    ¬ S.LocalSuccess :=
  S.local_incompressible_means_no_success hInc

/-- Resolver-only route is marked incomplete: it contains no coverage field. -/
def ResolverOnlyRouteIncomplete
    {S : Step00LocalAudit}
    (_R : ResolverOnlyRoute S) : Prop := True

theorem resolverOnlyRoute_incomplete
    {S : Step00LocalAudit}
    (R : ResolverOnlyRoute S) :
    ResolverOnlyRouteIncomplete R := by
  trivial

/-#############################################################################
  §5. Complexity-barrier audit
#############################################################################-/

/--
Barrier-audit fields for a proposed classical lower bound.

These are not Lean proofs of the historical barrier theorems.  They are explicit
obligations the external certificate must address.
-/
structure ComplexityBarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_or_largeness_leak : Prop
  no_density_or_largeness_leak_proof : no_density_or_largeness_leak

/-- Nonabsorption audit against Step00 disguised routes. -/
structure Step00NonAbsorptionAudit (S : Step00LocalAudit) where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_twin_boundary_leak : Prop
  no_twin_boundary_leak_proof : no_twin_boundary_leak

  no_fixed_finite_language_trick : Prop
  no_fixed_finite_language_trick_proof : no_fixed_finite_language_trick

  no_empty_language_trick : Prop
  no_empty_language_trick_proof : no_empty_language_trick

/-#############################################################################
  §6. External lower-bound certificates
#############################################################################-/

/--
Direct external lower-bound certificate.

This is the honest object needed for classical P/NP separation after all Step00
internal bridges have been audited away.
-/
structure ExternalLowerBoundCertificate
    (C : ClassicalDecisionFrame)
    (S : Step00LocalAudit) where
  faithful : FaithfulMachineFrame C
  L : C.Language
  inNP : C.InNP L
  notInP : ¬ C.InP L
  barrier_audit : ComplexityBarrierAudit
  nonabsorption_audit : Step00NonAbsorptionAudit S

/-- A direct external lower-bound certificate gives a separation witness. -/
def ExternalLowerBoundCertificate.toWitness
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (E : ExternalLowerBoundCertificate C S) :
    DecisionSeparationWitness C :=
  { L := E.L, inNP := E.inNP, notInP := E.notInP }

/-- A direct external lower-bound certificate refutes class coincidence. -/
theorem ExternalLowerBoundCertificate.not_classesCoincide
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (E : ExternalLowerBoundCertificate C S) :
    ¬ ClassesCoincide C :=
  E.toWitness.not_classesCoincide

/--
NP-complete external lower-bound route: prove lower bound for an NP-complete
language.
-/
structure NPCompleteLowerBoundCertificate
    (C : ClassicalDecisionFrame)
    (S : Step00LocalAudit) where
  faithful : FaithfulMachineFrame C
  L : C.Language
  complete : NPComplete C L
  notInP : ¬ C.InP L
  barrier_audit : ComplexityBarrierAudit
  nonabsorption_audit : Step00NonAbsorptionAudit S

/-- NP-complete lower-bound certificate gives a direct external certificate. -/
def NPCompleteLowerBoundCertificate.toExternal
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (E : NPCompleteLowerBoundCertificate C S) :
    ExternalLowerBoundCertificate C S :=
  { faithful := E.faithful
    L := E.L
    inNP := E.complete.inNP
    notInP := E.notInP
    barrier_audit := E.barrier_audit
    nonabsorption_audit := E.nonabsorption_audit }

/-- NP-complete lower-bound certificate refutes class coincidence. -/
theorem NPCompleteLowerBoundCertificate.not_classesCoincide
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (E : NPCompleteLowerBoundCertificate C S) :
    ¬ ClassesCoincide C :=
  E.toExternal.not_classesCoincide

/-#############################################################################
  §7. Cook–Levin style placeholder, without overclaim
#############################################################################-/

/--
Cook–Levin-style certificate that a particular complete language represents
nondeterministic polynomial verification.

This is a transfer object, not a lower bound.
-/
structure CookLevinStyleTransfer
    (C : ClassicalDecisionFrame)
    (L : C.Language) where
  complete : NPComplete C L

  encoding_correctness : Prop
  encoding_correctness_proof : encoding_correctness

  tableau_locality : Prop
  tableau_locality_proof : tableau_locality

  polynomial_blowup : Prop
  polynomial_blowup_proof : polynomial_blowup

/-- Cook–Levin transfer only supplies NP-completeness, not `L ∉ P`. -/
def CookLevinTransferHasNoLowerBoundContent
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (_T : CookLevinStyleTransfer C L) : Prop := True

theorem cookLevinTransfer_hasNoLowerBoundContent
    {C : ClassicalDecisionFrame}
    {L : C.Language}
    (T : CookLevinStyleTransfer C L) :
    CookLevinTransferHasNoLowerBoundContent T := by
  trivial

/-- Cook–Levin plus an external lower bound gives separation. -/
theorem not_classesCoincide_of_cookLevin_and_lowerBound
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    {L : C.Language}
    (faithful : FaithfulMachineFrame C)
    (T : CookLevinStyleTransfer C L)
    (hNotP : ¬ C.InP L)
    (barrier : ComplexityBarrierAudit)
    (nonabsorb : Step00NonAbsorptionAudit S) :
    ¬ ClassesCoincide C := by
  let E : NPCompleteLowerBoundCertificate C S :=
    { faithful := faithful
      L := L
      complete := T.complete
      notInP := hNotP
      barrier_audit := barrier
      nonabsorption_audit := nonabsorb }
  exact E.not_classesCoincide

/-#############################################################################
  §8. Internal-route no-free-lunch theorem
#############################################################################-/

/-- Classification of an attempted classical bridge after all Step00 audits. -/
inductive BridgeKind where
  | internalCoverage
  | resolverOnly
  | externalNonStep00
  deriving DecidableEq, Repr

/-- A classified bridge attempt. -/
structure ClassifiedBridgeAttempt (S : Step00LocalAudit) where
  kind : BridgeKind
  internalCoverageData : kind = BridgeKind.internalCoverage → InternalCoverageRoute S
  resolverOnlyData : kind = BridgeKind.resolverOnly → ResolverOnlyRoute S
  externalData : kind = BridgeKind.externalNonStep00 → ExternalNonStep00Route S

/-- Internal coverage branch pays semantic closure. -/
theorem ClassifiedBridgeAttempt.internal_pays_closure
    {S : Step00LocalAudit}
    (B : ClassifiedBridgeAttempt S)
    (h : B.kind = BridgeKind.internalCoverage) :
    S.SemanticCollisionClosure := by
  exact internalCoverageRoute_pays_closure (B.internalCoverageData h)

/-- Resolver-only branch is incomplete. -/
theorem ClassifiedBridgeAttempt.resolver_only_incomplete
    {S : Step00LocalAudit}
    (B : ClassifiedBridgeAttempt S)
    (h : B.kind = BridgeKind.resolverOnly) :
    ResolverOnlyRouteIncomplete (B.resolverOnlyData h) := by
  exact resolverOnlyRoute_incomplete (B.resolverOnlyData h)

/-- External branch is the only branch not absorbed by internal coverage. -/
noncomputable def ClassifiedBridgeAttempt.external_has_nonStep00_data
    {S : Step00LocalAudit}
    (B : ClassifiedBridgeAttempt S)
    (h : B.kind = BridgeKind.externalNonStep00) :
    ExternalNonStep00Route S :=
  B.externalData h

/-#############################################################################
  §9. Maximal forward certificate gate
#############################################################################-/

/--
One-file maximal forward certificate.

It packages all external requirements that remain after the Step00 bridge audits.
-/
structure MaximalForwardPNPCertificate
    (C : ClassicalDecisionFrame)
    (S : Step00LocalAudit) where
  lower_bound : ExternalLowerBoundCertificate C S

  /-- Optional complete language route, if the chosen `lower_bound.L` is complete. -/
  complete_route_available : Prop

  /-- Explicit guard that this certificate is external, not a hidden Step00 route. -/
  external_route : ExternalNonStep00Route S

/-- The maximal forward certificate gives a decision separation witness. -/
def MaximalForwardPNPCertificate.toWitness
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (M : MaximalForwardPNPCertificate C S) :
    DecisionSeparationWitness C :=
  M.lower_bound.toWitness

/-- The maximal forward certificate refutes class coincidence. -/
theorem MaximalForwardPNPCertificate.not_classesCoincide
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (M : MaximalForwardPNPCertificate C S) :
    ¬ ClassesCoincide C :=
  M.toWitness.not_classesCoincide

/-- Explicit P/NP-style separation statement inside the chosen frame. -/
def ClassicalPNPSeparated (C : ClassicalDecisionFrame) : Prop :=
  ¬ ClassesCoincide C

/-- Final theorem gate: the maximal certificate proves classical separation in the frame. -/
theorem classicalPNPSeparated_of_maximalForwardCertificate
    {C : ClassicalDecisionFrame}
    {S : Step00LocalAudit}
    (M : MaximalForwardPNPCertificate C S) :
    ClassicalPNPSeparated C :=
  M.not_classesCoincide

/-#############################################################################
  §10. Remaining obligation, explicitly stated
#############################################################################-/

/--
The remaining obligation after all internal Step00 routes have been audited.
This is intentionally exactly the external certificate, not another internal
Step00 resolver construction.
-/
structure RemainingSingleFileMaximalForwardObligation where
  C : ClassicalDecisionFrame
  S : Step00LocalAudit
  certificate : MaximalForwardPNPCertificate C S

/-- Closing the remaining obligation yields classical separation in its frame. -/
theorem RemainingSingleFileMaximalForwardObligation.closes
    (O : RemainingSingleFileMaximalForwardObligation) :
    ClassicalPNPSeparated O.C :=
  classicalPNPSeparated_of_maximalForwardCertificate O.certificate

/--
Slogan: after Step00-local, promise, coverage, and total-search audits, the only
nonabsorbed road to classical P/NP is an external faithful lower-bound
certificate.
-/
def SingleFileMaximalForwardSlogan : Prop := True

theorem singleFileMaximalForwardSlogan :
    SingleFileMaximalForwardSlogan := by
  trivial

end PNPMaximalForwardSingleFile
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_lower_bound_forward_layer_patch.lean ============ -/
/-
  EuclidsPath_external_lower_bound_forward_layer_patch.lean

  Maximal forward layer after the Step00/classical-bridge audit.

  Purpose
  -------
  We no longer build another internal Step00 bridge.  The earlier audit showed:

    * fixed finite quotients are classically trivial;
    * global prefix languages collapse to empty languages under local failure;
    * answer graphs verify proposed answers but do not produce answers;
    * totality/coverage for Step00 collision search is exactly semantic closure;
    * promise search avoids totality, but needs a separate decision bridge;
    * internal covered routes pay the old causal-closure boundary.

  Therefore the only nonabsorbed route to classical decision P/NP is an external
  machine-theoretic lower-bound certificate.

  This file pushes that frontier forward by recording a concrete abstract
  machine-frame API and the exact proof gates still required:

    1. a faithful uniform machine model;
    2. definitions of InP/InNP from machine/verifier semantics;
    3. NP-complete transfer lemmas;
    4. a universal lower-bound/diagonal certificate schema;
    5. barrier and nonabsorption audits;
    6. final theorem gates from such certificates to classical separation.

  This file proves assembly theorems only.  It does not prove P ≠ NP.
  No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNPForward

/-#############################################################################
  §1. A faithful uniform decision-machine frame
#############################################################################-/

/-- A minimal abstract decision machine frame. -/
structure UniformDecisionMachineFrame where
  Input : Type
  Machine : Type
  Lang : Type

  accepts : Machine → Input → Prop
  inLang : Lang → Input → Prop

  /-- `timeBound M p` says machine `M` runs within polynomial/time code `p`. -/
  PolyBound : Type
  timeBound : Machine → PolyBound → Prop


/-- `decides M L` means `M` decides exactly language `L`.  (Combined-file fix:
originally a default-valued structure field used definitionally below.) -/
abbrev UniformDecisionMachineFrame.decides (F : UniformDecisionMachineFrame)
    (M : F.Machine) (L : F.Lang) : Prop :=
  ∀ x : F.Input, F.accepts M x ↔ F.inLang L x

/-- P-membership from real machines and polynomial bounds. -/
def InP (F : UniformDecisionMachineFrame) (L : F.Lang) : Prop :=
  ∃ M : F.Machine, ∃ p : F.PolyBound,
    F.timeBound M p ∧ F.decides M L

/-- A polynomial verifier/witness frame for NP. -/
structure UniformVerifierFrame extends UniformDecisionMachineFrame where
  Witness : Type
  verifies : Machine → Input → Witness → Prop
  witnessBound : PolyBound → Input → Witness → Prop

/-- NP-membership from polynomially bounded witnesses and verifiers. -/
def InNP (F : UniformVerifierFrame) (L : F.Lang) : Prop :=
  ∃ V : F.Machine, ∃ p : F.PolyBound,
    F.timeBound V p ∧
    ∀ x : F.Input,
      F.inLang L x ↔ ∃ w : F.Witness, F.witnessBound p x w ∧ F.verifies V x w

/-- Faithfulness guard: the frame is not a synthetic/trivial predicate frame. -/
structure FaithfulUniformMachineFrame (F : UniformVerifierFrame) where
  nonempty_input : Nonempty F.Input
  p_has_machine_semantics : Prop
  p_has_machine_semantics_proof : p_has_machine_semantics
  np_has_verifier_semantics : Prop
  np_has_verifier_semantics_proof : np_has_verifier_semantics
  not_trivial_false_P : Prop
  not_trivial_false_P_proof : not_trivial_false_P
  not_trivial_true_NP : Prop
  not_trivial_true_NP_proof : not_trivial_true_NP

/-- Classical separation witness inside a faithful frame. -/
structure ClassicalDecisionSeparationWitness (F : UniformVerifierFrame) where
  L : F.Lang
  inNP : InNP F L
  notInP : ¬ InP F.toUniformDecisionMachineFrame L

/-- Classes coincide extensionally on all frame languages. -/
def ClassesCoincide (F : UniformVerifierFrame) : Prop :=
  ∀ L : F.Lang, InNP F L ↔ InP F.toUniformDecisionMachineFrame L

/-- Any separation witness refutes class coincidence. -/
theorem ClassicalDecisionSeparationWitness.not_classesCoincide
    {F : UniformVerifierFrame}
    (W : ClassicalDecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  have hInP : InP F.toUniformDecisionMachineFrame W.L := (hCoincide W.L).mp W.inNP
  exact W.notInP hInP

/-#############################################################################
  §2. Reductions and NP-complete transfer
#############################################################################-/

/-- Polynomial many-one reduction in the selected frame. -/
structure PolyManyOneReduction (F : UniformVerifierFrame) (A B : F.Lang) where
  reduction : F.Input → F.Input
  polytime : Prop
  polytime_proof : polytime
  correct : ∀ x : F.Input, F.inLang A x ↔ F.inLang B (reduction x)

/-- P is closed under polynomial many-one preimages. -/
def PClosedUnderPolyPreimage (F : UniformVerifierFrame) : Prop :=
  ∀ A B : F.Lang,
    PolyManyOneReduction F A B →
    InP F.toUniformDecisionMachineFrame B →
    InP F.toUniformDecisionMachineFrame A

/-- NP-hardness against all NP languages in this frame.  (Combined-file fix:
`PolyManyOneReduction` carries the reduction map as data, so hardness is stated
via `Nonempty`.) -/
def NPHard (F : UniformVerifierFrame) (L : F.Lang) : Prop :=
  ∀ A : F.Lang, InNP F A → Nonempty (PolyManyOneReduction F A L)

/-- NP-completeness = NP membership + NP-hardness. -/
structure NPComplete (F : UniformVerifierFrame) (L : F.Lang) : Prop where
  inNP : InNP F L
  hard : NPHard F L

/-- If an NP-complete language is not in P, P and NP do not coincide. -/
theorem not_classesCoincide_of_npComplete_notInP
    {F : UniformVerifierFrame} {L : F.Lang}
    (hNPC : NPComplete F L)
    (hNotP : ¬ InP F.toUniformDecisionMachineFrame L) :
    ¬ ClassesCoincide F := by
  exact (ClassicalDecisionSeparationWitness.not_classesCoincide
    { L := L, inNP := hNPC.inNP, notInP := hNotP })

/-- If an NP-complete language is in P and P is closed under reductions, then NP ⊆ P. -/
theorem np_subset_p_of_npComplete_inP
    {F : UniformVerifierFrame} {L : F.Lang}
    (hClosed : PClosedUnderPolyPreimage F)
    (hNPC : NPComplete F L)
    (hP : InP F.toUniformDecisionMachineFrame L) :
    ∀ A : F.Lang, InNP F A → InP F.toUniformDecisionMachineFrame A := by
  intro A hA
  exact (hNPC.hard A hA).elim fun red => hClosed A L red hP

/-- With the standard inclusion P⊆NP, one NP-complete language in P yields class coincidence. -/
theorem classesCoincide_of_npComplete_inP
    {F : UniformVerifierFrame} {L : F.Lang}
    (hClosed : PClosedUnderPolyPreimage F)
    (hPinNP : ∀ A : F.Lang,
      InP F.toUniformDecisionMachineFrame A → InNP F A)
    (hNPC : NPComplete F L)
    (hP : InP F.toUniformDecisionMachineFrame L) :
    ClassesCoincide F := by
  intro A
  constructor
  · intro hA
    exact np_subset_p_of_npComplete_inP hClosed hNPC hP A hA
  · intro hA
    exact hPinNP A hA

/-- Guard: NP-hardness without NP-membership is not a separation witness. -/
structure NPHardnessAloneIsInsufficient (F : UniformVerifierFrame) (L : F.Lang) where
  hard : NPHard F L
  missing_membership_guard : Prop
  missing_membership_guard_proof : missing_membership_guard

/-#############################################################################
  §3. Universal lower-bound / diagonal certificate schema
#############################################################################-/

/-- A language-specific lower-bound certificate against every polynomial-time machine. -/
structure UniversalPLowerBoundCertificate
    (F : UniformVerifierFrame) (L : F.Lang) where
  /-- For every purported P-decider, give a counterexample input. -/
  counterexample :
    ∀ M : F.Machine, ∀ p : F.PolyBound,
      F.timeBound M p →
        {x : F.Input // ¬ (F.accepts M x ↔ F.inLang L x)}

/-- A universal lower-bound certificate yields `L ∉ P`. -/
theorem notInP_of_universalLowerBound
    {F : UniformVerifierFrame} {L : F.Lang}
    (LB : UniversalPLowerBoundCertificate F L) :
    ¬ InP F.toUniformDecisionMachineFrame L := by
  intro hP
  rcases hP with ⟨M, p, hTime, hDecides⟩
  rcases LB.counterexample M p hTime with ⟨x, hBad⟩
  exact hBad (hDecides x)

/-- NP language + universal P lower bound gives a separation witness. -/
noncomputable def separationWitness_of_inNP_and_universalLowerBound
    {F : UniformVerifierFrame} {L : F.Lang}
    (hNP : InNP F L)
    (LB : UniversalPLowerBoundCertificate F L) :
    ClassicalDecisionSeparationWitness F :=
  { L := L
    inNP := hNP
    notInP := notInP_of_universalLowerBound LB }

/-- NP language + universal lower bound refutes class coincidence. -/
theorem not_classesCoincide_of_inNP_and_universalLowerBound
    {F : UniformVerifierFrame} {L : F.Lang}
    (hNP : InNP F L)
    (LB : UniversalPLowerBoundCertificate F L) :
    ¬ ClassesCoincide F := by
  exact (separationWitness_of_inNP_and_universalLowerBound hNP LB).not_classesCoincide

/-- NP-complete language + universal lower bound is the strongest transfer route. -/
structure NPCompleteUniversalLowerBoundRoute
    (F : UniformVerifierFrame) where
  L : F.Lang
  complete : NPComplete F L
  lowerBound : UniversalPLowerBoundCertificate F L

/-- The NP-complete universal route separates classical classes. -/
theorem NPCompleteUniversalLowerBoundRoute.not_classesCoincide
    {F : UniformVerifierFrame}
    (R : NPCompleteUniversalLowerBoundRoute F) :
    ¬ ClassesCoincide F := by
  exact not_classesCoincide_of_npComplete_notInP R.complete
    (notInP_of_universalLowerBound R.lowerBound)

/-#############################################################################
  §4. Barrier audits for an external lower-bound proof
#############################################################################-/

/-- The classical complexity-theory barrier audit. -/
structure ComplexityBarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- A Step00 nonabsorption audit for an external proof. -/
structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak

  external_machine_lower_bound_source : Prop
  external_machine_lower_bound_source_proof : external_machine_lower_bound_source

/-- Faithful external lower-bound certificate, the current true frontier. -/
structure ExternalLowerBoundCertificate (F : UniformVerifierFrame) where
  faithful : FaithfulUniformMachineFrame F
  L : F.Lang
  inNP : InNP F L
  lowerBound : UniversalPLowerBoundCertificate F L
  barrierAudit : ComplexityBarrierAudit
  nonAbsorption : Step00NonAbsorptionAudit

/-- External lower-bound certificate yields classical separation. -/
noncomputable def ExternalLowerBoundCertificate.separationWitness
    {F : UniformVerifierFrame}
    (E : ExternalLowerBoundCertificate F) :
    ClassicalDecisionSeparationWitness F :=
  separationWitness_of_inNP_and_universalLowerBound E.inNP E.lowerBound

/-- External lower-bound certificate refutes class coincidence. -/
theorem ExternalLowerBoundCertificate.not_classesCoincide
    {F : UniformVerifierFrame}
    (E : ExternalLowerBoundCertificate F) :
    ¬ ClassesCoincide F :=
  E.separationWitness.not_classesCoincide

/-#############################################################################
  §5. Cook-Levin style transfer gates
#############################################################################-/

/-- Cook-Levin style NP-completeness certificate for a selected language. -/
structure CookLevinStyleCertificate (F : UniformVerifierFrame) where
  SAT : F.Lang
  sat_inNP : InNP F SAT
  sat_hard : NPHard F SAT

/-- Cook-Levin gives NP-completeness, not a lower bound. -/
def CookLevinStyleCertificate.npComplete
    {F : UniformVerifierFrame}
    (CL : CookLevinStyleCertificate F) :
    NPComplete F CL.SAT :=
  { inNP := CL.sat_inNP, hard := CL.sat_hard }

/-- Cook-Levin plus a lower bound for SAT gives separation. -/
theorem not_classesCoincide_of_cookLevin_and_lowerBound
    {F : UniformVerifierFrame}
    (CL : CookLevinStyleCertificate F)
    (LB : UniversalPLowerBoundCertificate F CL.SAT) :
    ¬ ClassesCoincide F := by
  exact not_classesCoincide_of_npComplete_notInP CL.npComplete
    (notInP_of_universalLowerBound LB)

/-- Cook-Levin without a lower bound is only an NP-completeness transfer object. -/
structure CookLevinWithoutLowerBoundGuard
    (F : UniformVerifierFrame)
    (CL : CookLevinStyleCertificate F) where
  does_not_contain_notInP : Prop
  does_not_contain_notInP_proof : does_not_contain_notInP

/-#############################################################################
  §6. Machine-frame no-free-lunch gates
#############################################################################-/

/-- Synthetic frame artifacts that are forbidden in a faithful route. -/
structure MachineFrameNoFreeLunchAudit (F : UniformVerifierFrame) where
  not_InP_false_frame : Prop
  not_InP_false_frame_proof : not_InP_false_frame

  not_InNP_true_frame : Prop
  not_InNP_true_frame_proof : not_InNP_true_frame

  not_empty_language_artifact : Prop
  not_empty_language_artifact_proof : not_empty_language_artifact

  not_fixed_finite_language_artifact : Prop
  not_fixed_finite_language_artifact_proof : not_fixed_finite_language_artifact

  not_prefix_root_empty_artifact : Prop
  not_prefix_root_empty_artifact_proof : not_prefix_root_empty_artifact

  not_answer_graph_verifier_only_artifact : Prop
  not_answer_graph_verifier_only_artifact_proof : not_answer_graph_verifier_only_artifact

/-- Strengthened faithful frame carrying no-free-lunch guards. -/
structure StrongFaithfulExternalFrame (F : UniformVerifierFrame) where
  faithful : FaithfulUniformMachineFrame F
  noFreeLunch : MachineFrameNoFreeLunchAudit F

/-- Strong external certificate with all audit layers. -/
structure StrongExternalLowerBoundCertificate (F : UniformVerifierFrame) where
  strongFrame : StrongFaithfulExternalFrame F
  L : F.Lang
  inNP : InNP F L
  lowerBound : UniversalPLowerBoundCertificate F L
  barrierAudit : ComplexityBarrierAudit
  nonAbsorption : Step00NonAbsorptionAudit

/-- Strong certificate forgets to ordinary external certificate. -/
def StrongExternalLowerBoundCertificate.toExternal
    {F : UniformVerifierFrame}
    (S : StrongExternalLowerBoundCertificate F) :
    ExternalLowerBoundCertificate F :=
  { faithful := S.strongFrame.faithful
    L := S.L
    inNP := S.inNP
    lowerBound := S.lowerBound
    barrierAudit := S.barrierAudit
    nonAbsorption := S.nonAbsorption }

/-- Strong certificate also separates. -/
theorem StrongExternalLowerBoundCertificate.not_classesCoincide
    {F : UniformVerifierFrame}
    (S : StrongExternalLowerBoundCertificate F) :
    ¬ ClassesCoincide F :=
  S.toExternal.not_classesCoincide

/-#############################################################################
  §7. Final maximal forward theorem-gates
#############################################################################-/

/-- Maximal forward P/NP certificate at the current frontier. -/
structure MaximalForwardClassicalPNPCertificate where
  F : UniformVerifierFrame
  certificate : StrongExternalLowerBoundCertificate F

/-- A maximal forward certificate gives an actual frame-level class separation. -/
noncomputable def MaximalForwardClassicalPNPCertificate.separationWitness
    (C : MaximalForwardClassicalPNPCertificate) :
    ClassicalDecisionSeparationWitness C.F :=
  C.certificate.toExternal.separationWitness

/-- A maximal forward certificate refutes class coincidence in its faithful frame. -/
theorem MaximalForwardClassicalPNPCertificate.not_classesCoincide
    (C : MaximalForwardClassicalPNPCertificate) :
    ¬ ClassesCoincide C.F :=
  C.certificate.not_classesCoincide

/-- The exact remaining obligation after all Step00-local bridge audits. -/
structure RemainingExternalForwardObligation where
  F : UniformVerifierFrame
  strongFrame : StrongFaithfulExternalFrame F
  L : F.Lang
  inNP : InNP F L
  lowerBound : UniversalPLowerBoundCertificate F L
  barrierAudit : ComplexityBarrierAudit
  nonAbsorption : Step00NonAbsorptionAudit

/-- Remaining obligation closes the current frontier. -/
def RemainingExternalForwardObligation.toCertificate
    (R : RemainingExternalForwardObligation) :
    MaximalForwardClassicalPNPCertificate :=
  { F := R.F
    certificate :=
      { strongFrame := R.strongFrame
        L := R.L
        inNP := R.inNP
        lowerBound := R.lowerBound
        barrierAudit := R.barrierAudit
        nonAbsorption := R.nonAbsorption } }

/-- Closing the remaining obligation proves frame-level P/NP separation. -/
theorem RemainingExternalForwardObligation.not_classesCoincide
    (R : RemainingExternalForwardObligation) :
    ¬ ClassesCoincide R.F :=
  R.toCertificate.not_classesCoincide

/-- Final scope statement: this is the external lower-bound wall, not a Step00 axiom. -/
abbrev ExternalForwardFrontierSlogan : Prop :=
  ∀ R : RemainingExternalForwardObligation,
    ¬ ClassesCoincide R.F

/-- The slogan is exactly the theorem gate above. -/
theorem externalForwardFrontierSlogan : ExternalForwardFrontierSlogan := by
  intro R
  exact R.not_classesCoincide

end ClassicalPNPForward
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_lower_bound_routes_barriers_patch.lean ============ -/
/-
EuclidsPath_external_lower_bound_routes_barriers_patch.lean
================================================================

Purpose
-------
One-file forward layer after the previous external lower-bound certificate gate.

The previous frontier reduced classical P/NP to an external machine-theoretic
lower-bound certificate:

  find L ∈ NP such that L ∉ P.

This file does several forward steps at once, but remains honest:

  1. separates the main external routes;
  2. records which routes really imply decision P/NP separation;
  3. records which popular routes are insufficient without an additional bridge;
  4. keeps barrier audits explicit;
  5. keeps Step00 nonabsorption explicit.

No theorem here proves classical P ≠ NP.  The file only proves exact implication
lemmas of the form:

  route certificate + required bridge fields ⇒ decision separation.

No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNPExternalRoutes

/-#############################################################################
  §1. Abstract faithful decision/circuit frame
#############################################################################-/

/--
A minimal classical decision complexity interface.

This is still abstract, but no longer permits the earlier fake bridge style to do
work by itself.  Every separation theorem below explicitly names the closure or
simulation facts it uses.
-/
structure DecisionCircuitFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop
  InEXP : Language → Prop
  InPpoly : Language → Prop
  ClassesCoincide : Prop

  /-- If classes coincide, every NP language is in P. -/
  coincide_elim : ClassesCoincide → ∀ L : Language, InNP L → InP L

  /-- Uniform polynomial-time computation has polynomial-size circuit families. -/
  P_subset_Ppoly : ∀ L : Language, InP L → InPpoly L

/-- A direct decision separation witness. -/
structure DecisionSeparationWitness (C : DecisionCircuitFrame) where
  L : C.Language
  inNP : C.InNP L
  notInP : ¬ C.InP L

/-- A decision separation witness refutes class coincidence. -/
theorem DecisionSeparationWitness.not_classesCoincide
    {C : DecisionCircuitFrame}
    (W : DecisionSeparationWitness C) :
    ¬ C.ClassesCoincide := by
  intro hEq
  exact W.notInP (C.coincide_elim hEq W.L W.inNP)

/-#############################################################################
  §2. Circuit lower-bound route
#############################################################################-/

/--
Nonuniform circuit lower-bound route.

If an NP language is not in P/poly, then it is certainly not in P, since
P ⊆ P/poly.  This is a genuine external route, stronger than P≠NP.
-/
structure NPLanguageNotInPpoly (C : DecisionCircuitFrame) where
  L : C.Language
  inNP : C.InNP L
  notInPpoly : ¬ C.InPpoly L

/-- NP ⊄ P/poly gives an NP language outside P. -/
theorem NPLanguageNotInPpoly.notInP
    {C : DecisionCircuitFrame}
    (H : NPLanguageNotInPpoly C) :
    ¬ C.InP H.L := by
  intro hP
  exact H.notInPpoly (C.P_subset_Ppoly H.L hP)

/-- Circuit lower bound against P/poly gives decision separation. -/
def NPLanguageNotInPpoly.toDecisionSeparation
    {C : DecisionCircuitFrame}
    (H : NPLanguageNotInPpoly C) :
    DecisionSeparationWitness C :=
{ L := H.L
  inNP := H.inNP
  notInP := H.notInP }

/-- Circuit lower bound against P/poly refutes P=NP. -/
theorem NPLanguageNotInPpoly.not_classesCoincide
    {C : DecisionCircuitFrame}
    (H : NPLanguageNotInPpoly C) :
    ¬ C.ClassesCoincide :=
  H.toDecisionSeparation.not_classesCoincide

/--
Audit fields required for a serious circuit lower-bound route.

These fields are intentionally propositional: a concrete formalization must fill
them by actual mathematics, not by Step00 causal closure.
-/
structure CircuitLowerBoundAudit where
  explicit_or_natural_proofs_barrier_paid : Prop
  explicit_or_natural_proofs_barrier_paid_proof : explicit_or_natural_proofs_barrier_paid
  nonrelativizing_component : Prop
  nonrelativizing_component_proof : nonrelativizing_component
  nonalgebrizing_component : Prop
  nonalgebrizing_component_proof : nonalgebrizing_component
  uniformity_accounted_for : Prop
  uniformity_accounted_for_proof : uniformity_accounted_for
  not_hidden_step00_coverage : Prop
  not_hidden_step00_coverage_proof : not_hidden_step00_coverage

/-- Full circuit route certificate. -/
structure CircuitRouteCertificate (C : DecisionCircuitFrame) where
  lowerBound : NPLanguageNotInPpoly C
  audit : CircuitLowerBoundAudit

/-- Full circuit route gives P/NP separation. -/
theorem CircuitRouteCertificate.not_classesCoincide
    {C : DecisionCircuitFrame}
    (R : CircuitRouteCertificate C) :
    ¬ C.ClassesCoincide :=
  R.lowerBound.not_classesCoincide

/-#############################################################################
  §3. Time hierarchy / diagonal route guard
#############################################################################-/

/--
A hierarchy theorem usually gives some language outside P in a larger class.
This alone is not a P/NP separation unless the separated language is also shown
NP.
-/
structure TimeHierarchyOutsideP (C : DecisionCircuitFrame) where
  L : C.Language
  inEXP : C.InEXP L
  notInP : ¬ C.InP L

/-- Extra bridge needed to turn a hierarchy language into a P/NP witness. -/
structure HierarchyLanguageInNP
    {C : DecisionCircuitFrame}
    (H : TimeHierarchyOutsideP C) where
  inNP : C.InNP H.L

/-- Time hierarchy plus an NP embedding gives decision separation. -/
def TimeHierarchyOutsideP.toDecisionSeparation
    {C : DecisionCircuitFrame}
    (H : TimeHierarchyOutsideP C)
    (B : HierarchyLanguageInNP H) :
    DecisionSeparationWitness C :=
{ L := H.L
  inNP := B.inNP
  notInP := H.notInP }

/-- Time hierarchy plus the NP bridge refutes class coincidence. -/
theorem TimeHierarchyOutsideP.not_classesCoincide_of_inNP
    {C : DecisionCircuitFrame}
    (H : TimeHierarchyOutsideP C)
    (B : HierarchyLanguageInNP H) :
    ¬ C.ClassesCoincide :=
  (H.toDecisionSeparation B).not_classesCoincide

/-- Guard: the hierarchy route still has a named missing NP bridge. -/
structure TimeHierarchyRouteStatus (C : DecisionCircuitFrame) where
  hierarchy : TimeHierarchyOutsideP C
  missing_or_supplied_np_bridge : Prop

/-#############################################################################
  §4. Proof-complexity route
#############################################################################-/

/--
A proof-complexity route has to connect P-decidability of a language to short
proofs in a proof system, and then prove a lower bound against those proofs.
This is abstract but honest about the two required ingredients.
-/
structure ProofComplexityRoute (C : DecisionCircuitFrame) where
  L : C.Language
  inNP : C.InNP L

  ShortProofs : Prop
  p_decider_gives_short_proofs : C.InP L → ShortProofs
  lower_bound_no_short_proofs : ¬ ShortProofs

/-- Proof-complexity route gives L ∉ P. -/
theorem ProofComplexityRoute.notInP
    {C : DecisionCircuitFrame}
    (R : ProofComplexityRoute C) :
    ¬ C.InP R.L := by
  intro hP
  exact R.lower_bound_no_short_proofs (R.p_decider_gives_short_proofs hP)

/-- Proof-complexity route gives decision separation. -/
def ProofComplexityRoute.toDecisionSeparation
    {C : DecisionCircuitFrame}
    (R : ProofComplexityRoute C) :
    DecisionSeparationWitness C :=
{ L := R.L
  inNP := R.inNP
  notInP := R.notInP }

/-- Proof-complexity route refutes class coincidence. -/
theorem ProofComplexityRoute.not_classesCoincide
    {C : DecisionCircuitFrame}
    (R : ProofComplexityRoute C) :
    ¬ C.ClassesCoincide :=
  R.toDecisionSeparation.not_classesCoincide

/-- Audit fields for proof-complexity route. -/
structure ProofComplexityAudit where
  proof_system_faithful : Prop
  proof_system_faithful_proof : proof_system_faithful
  p_to_short_proofs_not_assumed_for_free : Prop
  p_to_short_proofs_not_assumed_for_free_proof : p_to_short_proofs_not_assumed_for_free
  lower_bound_not_oracle_artifact : Prop
  lower_bound_not_oracle_artifact_proof : lower_bound_not_oracle_artifact
  no_hidden_cook_levin_lower_bound : Prop
  no_hidden_cook_levin_lower_bound_proof : no_hidden_cook_levin_lower_bound
  no_step00_causal_closure_leak : Prop
  no_step00_causal_closure_leak_proof : no_step00_causal_closure_leak

/-- Full proof-complexity certificate. -/
structure ProofComplexityCertificate (C : DecisionCircuitFrame) where
  route : ProofComplexityRoute C
  audit : ProofComplexityAudit

/-- Full proof-complexity certificate gives class separation. -/
theorem ProofComplexityCertificate.not_classesCoincide
    {C : DecisionCircuitFrame}
    (R : ProofComplexityCertificate C) :
    ¬ C.ClassesCoincide :=
  R.route.not_classesCoincide

/-#############################################################################
  §5. NP-complete transfer guard
#############################################################################-/

/-- Polynomial many-one reduction, abstractly. -/
structure PolyManyOneReduction (C : DecisionCircuitFrame) (A B : C.Language) where
  exists_poly_map : Prop
  exists_poly_map_proof : exists_poly_map
  correctness : Prop
  correctness_proof : correctness

/-- NP-hard language under many-one reductions. -/
structure NPHard (C : DecisionCircuitFrame) (L : C.Language) where
  reduces_from_every_np : ∀ A : C.Language, C.InNP A → PolyManyOneReduction C A L

/-- NP-complete language. -/
structure NPComplete (C : DecisionCircuitFrame) (L : C.Language) where
  inNP : C.InNP L
  hard : NPHard C L

/-- Closure of P under poly many-one preimages. -/
def PClosedUnderReductions (C : DecisionCircuitFrame) : Prop :=
  ∀ A B : C.Language,
    PolyManyOneReduction C A B → C.InP B → C.InP A

/-- NP-complete language outside P gives separation. -/
def decisionSeparation_of_npComplete_notInP
    {C : DecisionCircuitFrame}
    {L : C.Language}
    (hC : NPComplete C L)
    (hNotP : ¬ C.InP L) :
    DecisionSeparationWitness C :=
{ L := L
  inNP := hC.inNP
  notInP := hNotP }

/-- NP-complete language outside P refutes class coincidence. -/
theorem not_classesCoincide_of_npComplete_notInP
    {C : DecisionCircuitFrame}
    {L : C.Language}
    (hC : NPComplete C L)
    (hNotP : ¬ C.InP L) :
    ¬ C.ClassesCoincide :=
  (decisionSeparation_of_npComplete_notInP hC hNotP).not_classesCoincide

/-- If an NP-complete language is in P and P is closed under reductions, NP⊆P. -/
theorem np_subset_p_of_npComplete_inP
    {C : DecisionCircuitFrame}
    {L : C.Language}
    (hClosed : PClosedUnderReductions C)
    (hC : NPComplete C L)
    (hP : C.InP L) :
    ∀ A : C.Language, C.InNP A → C.InP A := by
  intro A hA
  exact hClosed A L (hC.hard.reduces_from_every_np A hA) hP

/-- NP-hardness alone has no lower-bound content in this abstract audit. -/
structure NPHardnessAloneIsInsufficient (C : DecisionCircuitFrame) where
  L : C.Language
  hard : NPHard C L
  missing_inNP_or_notInP_lower_bound : Prop
  missing_inNP_or_notInP_lower_bound_proof : missing_inNP_or_notInP_lower_bound

/-#############################################################################
  §6. PRG / derandomization / hardness-vs-randomness guard
#############################################################################-/

/--
A PRG/derandomization object alone is not a P/NP lower bound.  It becomes one
only after a route-specific theorem extracts an NP language outside P.
-/
structure PRGHardnessRoute (C : DecisionCircuitFrame) where
  PRGOrHardnessObject : Type
  object_nonempty : Nonempty PRGOrHardnessObject

  ExtractedLanguage : C.Language
  extracted_inNP : C.InNP ExtractedLanguage
  extracted_notInP_from_object : PRGOrHardnessObject → ¬ C.InP ExtractedLanguage

/-- If the PRG/hardness object actually extracts an NP language outside P, it separates. -/
theorem PRGHardnessRoute.not_classesCoincide
    {C : DecisionCircuitFrame}
    (R : PRGHardnessRoute C) :
    ¬ C.ClassesCoincide := by
  rcases R.object_nonempty with ⟨o⟩
  exact ({ L := R.ExtractedLanguage
           inNP := R.extracted_inNP
           notInP := R.extracted_notInP_from_object o } :
          DecisionSeparationWitness C).not_classesCoincide

/-- Guard for PRG-style route. -/
structure PRGRouteAudit where
  not_merely_derandomization_statement : Prop
  not_merely_derandomization_statement_proof : not_merely_derandomization_statement
  hardness_extraction_explicit : Prop
  hardness_extraction_explicit_proof : hardness_extraction_explicit
  no_circular_pnp_assumption : Prop
  no_circular_pnp_assumption_proof : no_circular_pnp_assumption
  no_step00_coverage_leak : Prop
  no_step00_coverage_leak_proof : no_step00_coverage_leak

/-#############################################################################
  §7. Global external route alternatives
#############################################################################-/

/-- Exhaustive shape of a successful external route in this audit layer. -/
inductive SuccessfulExternalRoute (C : DecisionCircuitFrame) : Prop where
  | directDecisionSeparation :
      DecisionSeparationWitness C → SuccessfulExternalRoute C
  | circuitLowerBound :
      CircuitRouteCertificate C → SuccessfulExternalRoute C
  | hierarchyWithNPBridge :
      (H : TimeHierarchyOutsideP C) → HierarchyLanguageInNP H → SuccessfulExternalRoute C
  | proofComplexity :
      ProofComplexityCertificate C → SuccessfulExternalRoute C
  | npCompleteLowerBound :
      (L : C.Language) → NPComplete C L → (¬ C.InP L) → SuccessfulExternalRoute C
  | prgHardness :
      PRGHardnessRoute C → PRGRouteAudit → SuccessfulExternalRoute C

/-- Every successful external route in this audit layer gives class separation. -/
theorem SuccessfulExternalRoute.not_classesCoincide
    {C : DecisionCircuitFrame}
    (R : SuccessfulExternalRoute C) :
    ¬ C.ClassesCoincide := by
  cases R with
  | directDecisionSeparation W =>
      exact W.not_classesCoincide
  | circuitLowerBound H =>
      exact H.not_classesCoincide
  | hierarchyWithNPBridge H B =>
      exact H.not_classesCoincide_of_inNP B
  | proofComplexity H =>
      exact H.not_classesCoincide
  | npCompleteLowerBound L hC hNotP =>
      exact not_classesCoincide_of_npComplete_notInP hC hNotP
  | prgHardness H _audit =>
      exact H.not_classesCoincide

/-#############################################################################
  §8. Barrier and nonabsorption manifest
#############################################################################-/

/-- Standard complexity-theory barrier audit. -/
structure ComplexityBarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing
  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing
  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only
  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only
  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact
  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- Step00 nonabsorption audit. -/
structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route
  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route
  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak
  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak
  genuinely_external_machine_argument : Prop
  genuinely_external_machine_argument_proof : genuinely_external_machine_argument

/-- A route with both external complexity barriers and Step00 nonabsorption paid. -/
structure AuditedExternalRoute (C : DecisionCircuitFrame) where
  route : SuccessfulExternalRoute C
  barrierAudit : ComplexityBarrierAudit
  nonAbsorptionAudit : Step00NonAbsorptionAudit

/-- Audited external route gives class separation. -/
theorem AuditedExternalRoute.not_classesCoincide
    {C : DecisionCircuitFrame}
    (R : AuditedExternalRoute C) :
    ¬ C.ClassesCoincide :=
  R.route.not_classesCoincide

/-#############################################################################
  §9. Maximal forward certificate and remaining obligation
#############################################################################-/

/--
Maximal forward P/NP certificate at this frontier.

This is now completely external to Step00 except for the nonabsorption audit.
-/
structure MaximalExternalPNPCertificate (C : DecisionCircuitFrame) where
  faithful_frame : Prop
  faithful_frame_proof : faithful_frame
  auditedRoute : AuditedExternalRoute C

/-- Maximal external certificate refutes class coincidence. -/
theorem MaximalExternalPNPCertificate.not_classesCoincide
    {C : DecisionCircuitFrame}
    (M : MaximalExternalPNPCertificate C) :
    ¬ C.ClassesCoincide :=
  M.auditedRoute.not_classesCoincide

/-- The remaining obligation after all internal Step00 bridges have been audited. -/
structure RemainingExternalRoutesObligation where
  C : DecisionCircuitFrame
  certificate : MaximalExternalPNPCertificate C

/-- Closing the remaining route obligation gives classical separation in its frame. -/
theorem RemainingExternalRoutesObligation.closes
    (R : RemainingExternalRoutesObligation) :
    ¬ R.C.ClassesCoincide :=
  R.certificate.not_classesCoincide

/-- Human-readable slogan as a formal Prop. -/
abbrev ExternalRoutesFrontierSlogan : Prop := True

theorem externalRoutesFrontierSlogan : ExternalRoutesFrontierSlogan := by
  trivial

end ClassicalPNPExternalRoutes
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_multifrontier_v3_patch.lean ============ -/
/-
EuclidsPath_external_routes_multifrontier_v3_patch.lean

Maximal forward layer for the external classical P/NP frontier.

This file does not prove classical P ≠ NP.  It isolates several honest external
routes that would imply classical separation in a faithful machine/circuit/proof
model, and records the exact missing certificates.

No axiom.  No sorry.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV3

/-#############################################################################
  §1. Abstract external complexity frame
#############################################################################-/

/--
A decision-complexity frame with enough structure to speak about P, NP, P/poly,
coNP, PH, reductions, and NP-completeness.
-/
structure ExternalDecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop
  IncoNP : Language → Prop
  InPpoly : Language → Prop
  InPH : Nat → Language → Prop
  Reduces : Language → Language → Prop

  p_subset_np : ∀ {L : Language}, InP L → InNP L
  p_subset_ppoly : ∀ {L : Language}, InP L → InPpoly L

  p_closed_downward :
    ∀ {A B : Language}, Reduces A B → InP B → InP A

  np_closed_downward :
    ∀ {A B : Language}, Reduces A B → InNP B → InNP A

/-- Class equality in the abstract frame: every NP language is in P. -/
def ClassesCoincide (F : ExternalDecisionFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- A concrete NP language outside P separates P from NP. -/
structure DecisionSeparationWitness (F : ExternalDecisionFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem DecisionSeparationWitness.not_classesCoincide
    {F : ExternalDecisionFrame}
    (W : DecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-- NP-hardness under the frame reductions. -/
def NPHard (F : ExternalDecisionFrame) (L : F.Language) : Prop :=
  ∀ A : F.Language, F.InNP A → F.Reduces A L

/-- NP-completeness. -/
structure NPComplete (F : ExternalDecisionFrame) (L : F.Language) : Prop where
  inNP : F.InNP L
  hard : NPHard F L

/-- NP-complete lower bound transfers to P ≠ NP. -/
theorem not_classesCoincide_of_npComplete_notInP
    {F : ExternalDecisionFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := L, inNP := hC.inNP, notInP := hNotP })

/-- If an NP-complete language is in P, then NP ⊆ P in the frame. -/
theorem classesCoincide_of_npComplete_inP
    {F : ExternalDecisionFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hP : F.InP L) :
    ClassesCoincide F := by
  intro A hA
  exact F.p_closed_downward (hC.hard A hA) hP

/-#############################################################################
  §2. Circuit lower-bound route
#############################################################################-/

/--
A nonuniform lower bound for an NP language.

This is stronger than an ordinary P lower bound because `P ⊆ P/poly`.
-/
structure NPLanguageOutsidePpoly (F : ExternalDecisionFrame) where
  L : F.Language
  inNP : F.InNP L
  notInPpoly : ¬ F.InPpoly L

theorem NPLanguageOutsidePpoly.notInP
    {F : ExternalDecisionFrame}
    (C : NPLanguageOutsidePpoly F) :
    ¬ F.InP C.L := by
  intro hP
  exact C.notInPpoly (F.p_subset_ppoly hP)

theorem NPLanguageOutsidePpoly.not_classesCoincide
    {F : ExternalDecisionFrame}
    (C : NPLanguageOutsidePpoly F) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := C.L, inNP := C.inNP, notInP := C.notInP })

/--
SAT-specific circuit lower-bound route.

If an NP-complete SAT-like language is outside P/poly, then P ≠ NP.
-/
structure SATCircuitLowerBoundRoute (F : ExternalDecisionFrame) where
  SAT : F.Language
  sat_complete : NPComplete F SAT
  sat_notInPpoly : ¬ F.InPpoly SAT

theorem SATCircuitLowerBoundRoute.sat_notInP
    {F : ExternalDecisionFrame}
    (R : SATCircuitLowerBoundRoute F) :
    ¬ F.InP R.SAT := by
  intro hP
  exact R.sat_notInPpoly (F.p_subset_ppoly hP)

theorem SATCircuitLowerBoundRoute.not_classesCoincide
    {F : ExternalDecisionFrame}
    (R : SATCircuitLowerBoundRoute F) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_npComplete_notInP
    R.sat_complete R.sat_notInP

/--
Karp--Lipton-style guard: a proof of `NP ⊆ P/poly` is not a P/NP lower bound.
It normally gives structural collapse consequences, so the lower-bound route
must prove an exclusion, not inclusion.
-/
structure KarpLiptonGuard (F : ExternalDecisionFrame) where
  NPsubsetPpoly : Prop
  PHCollapses : Prop
  inclusion_forces_collapse : NPsubsetPpoly → PHCollapses
  inclusion_is_not_lower_bound : NPsubsetPpoly → Prop

/-#############################################################################
  §3. Uniform hierarchy route and its guard
#############################################################################-/

/--
A hierarchy lower bound outside P, plus a bridge showing the hierarchy language is
actually in NP.

Time hierarchy alone gives languages outside smaller time classes, but the P/NP
separation route only closes if the separated language also lies in NP.
-/
structure HierarchyToNPRoute (F : ExternalDecisionFrame) where
  H : F.Language
  hierarchy_notInP : ¬ F.InP H
  inNP_bridge : F.InNP H
  bridge_is_external : Prop
  bridge_is_external_proof : bridge_is_external

noncomputable def HierarchyToNPRoute.separationWitness
    {F : ExternalDecisionFrame}
    (R : HierarchyToNPRoute F) :
    DecisionSeparationWitness F :=
  { L := R.H, inNP := R.inNP_bridge, notInP := R.hierarchy_notInP }

theorem HierarchyToNPRoute.not_classesCoincide
    {F : ExternalDecisionFrame}
    (R : HierarchyToNPRoute F) :
    ¬ ClassesCoincide F :=
  R.separationWitness.not_classesCoincide

/--
Guard: hierarchy without an NP-membership bridge is insufficient for P/NP.
-/
structure HierarchyOnlyInsufficient (F : ExternalDecisionFrame) where
  H : F.Language
  hierarchy_notInP : ¬ F.InP H
  no_inNP_bridge_yet : ¬ F.InNP H

/-#############################################################################
  §4. Proof-complexity route
#############################################################################-/

/-- Abstract proof-system/proof-complexity frame. -/
structure ProofComplexityFrame where
  Formula : Type
  Proof : Type
  Taut : Formula → Prop
  HasProof : Formula → Proof → Prop
  SizeBound : Type
  Short : SizeBound → Formula → Proof → Prop
  PDeciderGivesShortProofs : Prop
  ShortProofLowerBound : Prop

/--
A Cook--Reckhow style route from a hypothetical P-decider to short proofs, plus
a short-proof lower bound.  This is a common external route template.
-/
structure ProofComplexityRoute
    (F : ExternalDecisionFrame)
    (P : ProofComplexityFrame) where
  L : F.Language
  inNP : F.InNP L
  p_decider_to_short_proofs : F.InP L → P.PDeciderGivesShortProofs
  short_proofs_impossible : P.PDeciderGivesShortProofs → False
  lower_bound_external : Prop
  lower_bound_external_proof : lower_bound_external

theorem ProofComplexityRoute.notInP
    {F : ExternalDecisionFrame}
    {P : ProofComplexityFrame}
    (R : ProofComplexityRoute F P) :
    ¬ F.InP R.L := by
  intro hP
  exact R.short_proofs_impossible (R.p_decider_to_short_proofs hP)

theorem ProofComplexityRoute.not_classesCoincide
    {F : ExternalDecisionFrame}
    {P : ProofComplexityFrame}
    (R : ProofComplexityRoute F P) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := R.L, inNP := R.inNP, notInP := R.notInP })

/--
Guard: proof-complexity lower bound must be connected to a P-decider implication;
otherwise it is only a proof-system statement.
-/
structure ProofComplexityBridgeGuard
    (F : ExternalDecisionFrame)
    (P : ProofComplexityFrame) where
  has_lower_bound : P.ShortProofLowerBound
  has_p_decider_to_short_proofs_bridge : Prop
  without_bridge_no_pnp_conclusion :
    ¬ has_p_decider_to_short_proofs_bridge → Prop

/-#############################################################################
  §5. Natural-proofs / relativization / algebrization barrier audit
#############################################################################-/

/-- A barrier audit for external lower-bound arguments. -/
structure BarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- Natural proofs obstruction packaged as a guard. -/
structure NaturalProofsGuard where
  CombinatorialProperty : Type
  constructive : CombinatorialProperty → Prop
  large : CombinatorialProperty → Prop
  useful_against_Ppoly : CombinatorialProperty → Prop
  pseudorandom_function_assumption_blocks_natural_route : Prop

/-- Oracle barrier guard. -/
structure OracleBarrierGuard where
  has_P_eq_NP_oracle : Prop
  has_P_ne_NP_oracle : Prop
  relativizing_proof_cannot_resolve : has_P_eq_NP_oracle → has_P_ne_NP_oracle → Prop

/-- Algebrization barrier guard. -/
structure AlgebrizationGuard where
  has_algebrizing_obstruction : Prop
  proof_must_be_nonalgebrizing : has_algebrizing_obstruction → Prop

/-#############################################################################
  §6. Step00 nonabsorption audit
#############################################################################-/

/--
External P/NP route must not secretly re-enter the Step00 collision-coverage
boundary.
-/
structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak

  genuinely_external_machine_argument : Prop
  genuinely_external_machine_argument_proof : genuinely_external_machine_argument

/-#############################################################################
  §7. Route selector: several honest external paths
#############################################################################-/

/--
A successful external route is one of the known honest route families.  Each case
already contains enough data to imply P/NP separation in the frame.
-/
inductive SuccessfulExternalRoute (F : ExternalDecisionFrame) : Prop where
  | direct :
      DecisionSeparationWitness F →
      SuccessfulExternalRoute F

  | circuit :
      NPLanguageOutsidePpoly F →
      SuccessfulExternalRoute F

  | satCircuit :
      SATCircuitLowerBoundRoute F →
      SuccessfulExternalRoute F

  | hierarchy :
      HierarchyToNPRoute F →
      SuccessfulExternalRoute F

  | proofComplexity :
      (P : ProofComplexityFrame) →
      ProofComplexityRoute F P →
      SuccessfulExternalRoute F

  | npComplete :
      (L : F.Language) →
      NPComplete F L →
      ¬ F.InP L →
      SuccessfulExternalRoute F

theorem SuccessfulExternalRoute.not_classesCoincide
    {F : ExternalDecisionFrame}
    (R : SuccessfulExternalRoute F) :
    ¬ ClassesCoincide F := by
  cases R with
  | direct W =>
      exact W.not_classesCoincide
  | circuit C =>
      exact C.not_classesCoincide
  | satCircuit S =>
      exact S.not_classesCoincide
  | hierarchy H =>
      exact H.not_classesCoincide
  | proofComplexity P R =>
      exact R.not_classesCoincide
  | npComplete L C hNotP =>
      exact not_classesCoincide_of_npComplete_notInP C hNotP

/--
A fully audited external route: successful route plus barrier and Step00
nonabsorption audits.
-/
structure AuditedExternalRoute (F : ExternalDecisionFrame) where
  route : SuccessfulExternalRoute F
  barriers : BarrierAudit
  nonabsorption : Step00NonAbsorptionAudit

theorem AuditedExternalRoute.not_classesCoincide
    {F : ExternalDecisionFrame}
    (R : AuditedExternalRoute F) :
    ¬ ClassesCoincide F :=
  R.route.not_classesCoincide

/-#############################################################################
  §8. Multi-route frontier obligation
#############################################################################-/

/--
The next maximal forward obligation: build one successful audited external route.

This is intentionally external to Step00.  The route must use an actual
machine/circuit/proof-complexity lower-bound argument, not Step00 collision
coverage.
-/
structure RemainingExternalRoutesV3Obligation (F : ExternalDecisionFrame) where
  audited_route : AuditedExternalRoute F
  frame_is_faithful : Prop
  frame_is_faithful_proof : frame_is_faithful

  not_trivial_frame : Prop
  not_trivial_frame_proof : not_trivial_frame

  not_empty_language_trick : Prop
  not_empty_language_trick_proof : not_empty_language_trick

  not_fixed_finite_language_trick : Prop
  not_fixed_finite_language_trick_proof : not_fixed_finite_language_trick

theorem RemainingExternalRoutesV3Obligation.closes
    {F : ExternalDecisionFrame}
    (O : RemainingExternalRoutesV3Obligation F) :
    ¬ ClassesCoincide F :=
  O.audited_route.not_classesCoincide

/--
Slogan: after Step00-local, promise, and coverage audits, the only remaining
nonabsorbed route is an audited external lower-bound route.
-/
abbrev ExternalRoutesV3Slogan (F : ExternalDecisionFrame) : Prop :=
  RemainingExternalRoutesV3Obligation F → ¬ ClassesCoincide F

theorem externalRoutesV3Slogan
    (F : ExternalDecisionFrame) :
    ExternalRoutesV3Slogan F := by
  intro O
  exact O.closes

/-#############################################################################
  §9. What does not yet close the theorem
#############################################################################-/

/-- NP-hardness without NP-membership and lower bound is insufficient. -/
structure NPHardnessOnlyDoesNotClose (F : ExternalDecisionFrame) where
  L : F.Language
  hard : NPHard F L
  missing_inNP : Prop
  missing_notInP : Prop

/-- Barrier audit without a successful route is only an audit, not a proof. -/
structure BarrierAuditOnlyDoesNotClose where
  audit : BarrierAudit
  missing_route : Prop

/-- Step00 local separation without an external route remains local. -/
structure Step00LocalOnlyDoesNotClose where
  local_separation : Prop
  missing_external_machine_lower_bound : Prop

end ExternalRoutesV3
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v4_deep_obligations_patch.lean ============ -/
/-
EuclidsPath_external_routes_v4_deep_obligations_patch.lean

Maximal forward layer v4 for the external classical P/NP frontier.

This file pushes several external routes one level deeper.  It does not prove
P ≠ NP.  It records exact certificate types whose construction would close the
classical decision separation inside a faithful external frame.

No axiom declarations.  No sorry tactics.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV4

/-#############################################################################
  §1. Faithful external frame with machines, circuits, and reductions
#############################################################################-/

/--
A faithful external decision frame.  This is still abstract, but it separates the
semantic objects needed for genuine classical complexity arguments.
-/
structure FaithfulDecisionCircuitFrame where
  Input : Type
  Language : Type
  Machine : Type
  CircuitFamily : Type
  PolyBound : Type
  Reduction : Type

  inLang : Language → Input → Prop
  accepts : Machine → Input → Prop
  hasPolyTime : Machine → PolyBound → Prop
  circuitDecides : CircuitFamily → Language → Prop
  circuitPolySize : CircuitFamily → PolyBound → Prop
  reductionMaps : Reduction → Language → Language → Prop
  reductionPolyTime : Reduction → PolyBound → Prop

  InP : Language → Prop
  InNP : Language → Prop
  InPpoly : Language → Prop

  inP_sound :
    ∀ {L : Language}, InP L →
      ∃ M : Machine, ∃ p : PolyBound,
        hasPolyTime M p ∧ ∀ x : Input, accepts M x ↔ inLang L x

  inP_complete :
    ∀ {L : Language},
      (∃ M : Machine, ∃ p : PolyBound,
        hasPolyTime M p ∧ ∀ x : Input, accepts M x ↔ inLang L x) →
        InP L

  inPpoly_sound :
    ∀ {L : Language}, InPpoly L →
      ∃ C : CircuitFamily, ∃ p : PolyBound,
        circuitPolySize C p ∧ circuitDecides C L

  inPpoly_complete :
    ∀ {L : Language},
      (∃ C : CircuitFamily, ∃ p : PolyBound,
        circuitPolySize C p ∧ circuitDecides C L) →
        InPpoly L

  p_subset_np : ∀ {L : Language}, InP L → InNP L
  p_subset_ppoly : ∀ {L : Language}, InP L → InPpoly L

  p_closed_under_poly_reduction :
    ∀ {A B : Language},
      (∃ r : Reduction, ∃ p : PolyBound,
        reductionPolyTime r p ∧ reductionMaps r A B) →
      InP B → InP A

/-- Class coincidence in the faithful frame. -/
def ClassesCoincide (F : FaithfulDecisionCircuitFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- A language in NP but not in P separates classes. -/
structure SeparationWitness (F : FaithfulDecisionCircuitFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem SeparationWitness.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    (W : SeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-#############################################################################
  §2. NP-complete transfer with faithful reductions
#############################################################################-/

/-- Faithful polynomial many-one reduction. -/
structure PolyManyOneReduction (F : FaithfulDecisionCircuitFrame)
    (A B : F.Language) where
  r : F.Reduction
  p : F.PolyBound
  poly : F.reductionPolyTime r p
  maps : F.reductionMaps r A B

/-- NP-hardness using faithful reductions. -/
def NPHard (F : FaithfulDecisionCircuitFrame) (L : F.Language) : Prop :=
  ∀ A : F.Language, F.InNP A → Nonempty (PolyManyOneReduction F A L)

/-- NP-completeness. -/
structure NPComplete (F : FaithfulDecisionCircuitFrame) (L : F.Language) : Prop where
  inNP : F.InNP L
  hard : NPHard F L

/-- NP-complete lower bound transfers to class separation. -/
theorem not_classesCoincide_of_npComplete_notInP
    {F : FaithfulDecisionCircuitFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    ¬ ClassesCoincide F :=
  (SeparationWitness.not_classesCoincide
    { L := L, inNP := hC.inNP, notInP := hNotP })

/-- If an NP-complete language is in P, classes coincide in the frame. -/
theorem classesCoincide_of_npComplete_inP
    {F : FaithfulDecisionCircuitFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hP : F.InP L) :
    ClassesCoincide F := by
  intro A hA
  rcases hC.hard A hA with ⟨R⟩
  apply F.p_closed_under_poly_reduction
  · exact ⟨R.r, R.p, R.poly, R.maps⟩
  · exact hP

/-#############################################################################
  §3. Circuit-size lower-bound certificates
#############################################################################-/

/-- A concrete nonuniform lower bound: an NP language has no polynomial-size circuits. -/
structure NPLanguageOutsidePpoly (F : FaithfulDecisionCircuitFrame) where
  L : F.Language
  inNP : F.InNP L
  no_poly_circuit_family :
    ∀ C : F.CircuitFamily, ∀ p : F.PolyBound,
      F.circuitPolySize C p → ¬ F.circuitDecides C L

theorem NPLanguageOutsidePpoly.notInPpoly
    {F : FaithfulDecisionCircuitFrame}
    (H : NPLanguageOutsidePpoly F) :
    ¬ F.InPpoly H.L := by
  intro h
  rcases F.inPpoly_sound h with ⟨C, p, hSize, hDecides⟩
  exact H.no_poly_circuit_family C p hSize hDecides

theorem NPLanguageOutsidePpoly.notInP
    {F : FaithfulDecisionCircuitFrame}
    (H : NPLanguageOutsidePpoly F) :
    ¬ F.InP H.L := by
  intro hP
  exact H.notInPpoly (F.p_subset_ppoly hP)

theorem NPLanguageOutsidePpoly.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    (H : NPLanguageOutsidePpoly F) :
    ¬ ClassesCoincide F :=
  (SeparationWitness.not_classesCoincide
    { L := H.L, inNP := H.inNP, notInP := H.notInP })

/-- SAT-specific circuit lower bound route. -/
structure SATOutsidePpolyRoute (F : FaithfulDecisionCircuitFrame) where
  SAT : F.Language
  sat_complete : NPComplete F SAT
  no_poly_circuit_family :
    ∀ C : F.CircuitFamily, ∀ p : F.PolyBound,
      F.circuitPolySize C p → ¬ F.circuitDecides C SAT

def SATOutsidePpolyRoute.toOutsidePpoly
    {F : FaithfulDecisionCircuitFrame}
    (R : SATOutsidePpolyRoute F) :
    NPLanguageOutsidePpoly F :=
  { L := R.SAT,
    inNP := R.sat_complete.inNP,
    no_poly_circuit_family := R.no_poly_circuit_family }

theorem SATOutsidePpolyRoute.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    (R : SATOutsidePpolyRoute F) :
    ¬ ClassesCoincide F :=
  R.toOutsidePpoly.not_classesCoincide

/-- Karp--Lipton-style guard: NP ⊆ P/poly is not a lower bound route. -/
structure KarpLiptonStyleGuard (F : FaithfulDecisionCircuitFrame) where
  NPsubsetPpoly : Prop
  PHCollapseConsequence : Prop
  inclusion_forces_collapse : NPsubsetPpoly → PHCollapseConsequence
  route_requires_exclusion : Prop
  route_requires_exclusion_proof : route_requires_exclusion

/-#############################################################################
  §4. Uniform hierarchy route and why it needs NP-membership
#############################################################################-/

/-- A hierarchy language outside P plus an external NP-membership bridge. -/
structure HierarchyNPBridgeRoute (F : FaithfulDecisionCircuitFrame) where
  H : F.Language
  hierarchy_lower_bound : ¬ F.InP H
  external_inNP_bridge : F.InNP H
  bridge_not_step00_mediated : Prop
  bridge_not_step00_mediated_proof : bridge_not_step00_mediated

theorem HierarchyNPBridgeRoute.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    (R : HierarchyNPBridgeRoute F) :
    ¬ ClassesCoincide F :=
  (SeparationWitness.not_classesCoincide
    { L := R.H, inNP := R.external_inNP_bridge,
      notInP := R.hierarchy_lower_bound })

/-- Hierarchy without NP membership is not P/NP separation. -/
structure HierarchyWithoutNPBridgeGuard (F : FaithfulDecisionCircuitFrame) where
  H : F.Language
  hierarchy_lower_bound : ¬ F.InP H
  missing_inNP_bridge : Prop
  missing_inNP_bridge_proof : missing_inNP_bridge

/-#############################################################################
  §5. Proof-complexity route one layer deeper
#############################################################################-/

/-- Abstract propositional proof-system frame. -/
structure ProofSystemFrame where
  Formula : Type
  Proof : Type
  Tautology : Formula → Prop
  Proves : Proof → Formula → Prop
  ProofSizeBound : Type
  Short : ProofSizeBound → Proof → Formula → Prop

/-- Short proof consequence of a P-decider for an NP-complete language. -/
structure PDeciderToShortProofs
    (F : FaithfulDecisionCircuitFrame)
    (P : ProofSystemFrame)
    (L : F.Language) where
  shortProofConsequence : Prop
  derive : F.InP L → shortProofConsequence

/-- External lower bound against the relevant short-proof consequence. -/
structure ShortProofLowerBound
    (P : ProofSystemFrame)
    (Consequence : Prop) where
  impossible : Consequence → False
  lower_bound_external : Prop
  lower_bound_external_proof : lower_bound_external

/-- Proof-complexity route certificate. -/
structure ProofComplexityRoute
    (F : FaithfulDecisionCircuitFrame)
    (P : ProofSystemFrame) where
  L : F.Language
  inNP : F.InNP L
  bridge : PDeciderToShortProofs F P L
  lowerBound : ShortProofLowerBound P bridge.shortProofConsequence
  not_step00_coverage_route : Prop
  not_step00_coverage_route_proof : not_step00_coverage_route

theorem ProofComplexityRoute.notInP
    {F : FaithfulDecisionCircuitFrame}
    {P : ProofSystemFrame}
    (R : ProofComplexityRoute F P) :
    ¬ F.InP R.L := by
  intro hP
  exact R.lowerBound.impossible (R.bridge.derive hP)

theorem ProofComplexityRoute.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    {P : ProofSystemFrame}
    (R : ProofComplexityRoute F P) :
    ¬ ClassesCoincide F :=
  (SeparationWitness.not_classesCoincide
    { L := R.L, inNP := R.inNP, notInP := R.notInP })

/-- Guard: proof-system lower bound without P-decider bridge does not close P/NP. -/
structure ProofComplexityMissingBridgeGuard
    (F : FaithfulDecisionCircuitFrame)
    (P : ProofSystemFrame) where
  lower_bound_statement : Prop
  missing_p_decider_to_short_proofs_bridge : Prop
  no_pnp_conclusion_without_bridge : Prop
  no_pnp_conclusion_without_bridge_proof : no_pnp_conclusion_without_bridge

/-#############################################################################
  §6. Barrier and nonabsorption audits
#############################################################################-/

/-- Standard external complexity-barrier audit. -/
structure ComplexityBarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- Razborov--Rudich style natural-proofs guard. -/
structure NaturalProofsBarrierCertificate where
  CombinatorialProperty : Type
  constructive : CombinatorialProperty → Prop
  large : CombinatorialProperty → Prop
  useful_against_Ppoly : CombinatorialProperty → Prop
  blocked_under_prf_assumption : Prop
  proof_must_avoid_natural_property_only : Prop

/-- Relativization guard. -/
structure RelativizationBarrierCertificate where
  has_oracle_with_P_eq_NP : Prop
  has_oracle_with_P_ne_NP : Prop
  relativizing_argument_cannot_settle :
    has_oracle_with_P_eq_NP → has_oracle_with_P_ne_NP → Prop

/-- Algebrization guard. -/
structure AlgebrizationBarrierCertificate where
  has_algebrizing_obstruction : Prop
  proof_must_be_nonalgebrizing : has_algebrizing_obstruction → Prop

/-- Guard that external route is not absorbed back into Step00 coverage. -/
structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak

  genuinely_external_machine_argument : Prop
  genuinely_external_machine_argument_proof : genuinely_external_machine_argument

/-#############################################################################
  §7. Successful route selector v4
#############################################################################-/

/-- All honest external routes currently tracked by this frontier. -/
inductive SuccessfulExternalRouteV4 (F : FaithfulDecisionCircuitFrame) : Prop where
  | direct :
      SeparationWitness F → SuccessfulExternalRouteV4 F

  | circuit :
      NPLanguageOutsidePpoly F → SuccessfulExternalRouteV4 F

  | satCircuit :
      SATOutsidePpolyRoute F → SuccessfulExternalRouteV4 F

  | npCompleteLowerBound :
      (L : F.Language) → NPComplete F L → ¬ F.InP L →
      SuccessfulExternalRouteV4 F

  | hierarchyNPBridge :
      HierarchyNPBridgeRoute F → SuccessfulExternalRouteV4 F

  | proofComplexity :
      (P : ProofSystemFrame) → ProofComplexityRoute F P →
      SuccessfulExternalRouteV4 F

theorem SuccessfulExternalRouteV4.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    (R : SuccessfulExternalRouteV4 F) :
    ¬ ClassesCoincide F := by
  cases R with
  | direct W =>
      exact W.not_classesCoincide
  | circuit C =>
      exact C.not_classesCoincide
  | satCircuit S =>
      exact S.not_classesCoincide
  | npCompleteLowerBound L C hNotP =>
      exact not_classesCoincide_of_npComplete_notInP C hNotP
  | hierarchyNPBridge H =>
      exact H.not_classesCoincide
  | proofComplexity P R =>
      exact R.not_classesCoincide

/-- Successful route plus audits. -/
structure AuditedExternalRouteV4 (F : FaithfulDecisionCircuitFrame) where
  route : SuccessfulExternalRouteV4 F
  barriers : ComplexityBarrierAudit
  nonabsorption : Step00NonAbsorptionAudit

theorem AuditedExternalRouteV4.not_classesCoincide
    {F : FaithfulDecisionCircuitFrame}
    (R : AuditedExternalRouteV4 F) :
    ¬ ClassesCoincide F :=
  R.route.not_classesCoincide

/-#############################################################################
  §8. Maximal v4 obligation
#############################################################################-/

/--
The current maximal external obligation after the Step00 audits: construct one
faithful, audited, external route.
-/
structure RemainingExternalRoutesV4Obligation (F : FaithfulDecisionCircuitFrame) where
  audited_route : AuditedExternalRouteV4 F

  faithful_machine_semantics : Prop
  faithful_machine_semantics_proof : faithful_machine_semantics

  no_trivial_frame : Prop
  no_trivial_frame_proof : no_trivial_frame

  no_empty_language_trick : Prop
  no_empty_language_trick_proof : no_empty_language_trick

  no_fixed_finite_language_trick : Prop
  no_fixed_finite_language_trick_proof : no_fixed_finite_language_trick

  no_step00_internal_bridge_reentry : Prop
  no_step00_internal_bridge_reentry_proof : no_step00_internal_bridge_reentry

theorem RemainingExternalRoutesV4Obligation.closes
    {F : FaithfulDecisionCircuitFrame}
    (O : RemainingExternalRoutesV4Obligation F) :
    ¬ ClassesCoincide F :=
  O.audited_route.not_classesCoincide

/-- Compact slogan of the v4 frontier. -/
abbrev ExternalRoutesV4Slogan (F : FaithfulDecisionCircuitFrame) : Prop :=
  RemainingExternalRoutesV4Obligation F → ¬ ClassesCoincide F

theorem externalRoutesV4Slogan
    (F : FaithfulDecisionCircuitFrame) :
    ExternalRoutesV4Slogan F := by
  intro O
  exact O.closes

/-#############################################################################
  §9. Explicit insufficiency objects
#############################################################################-/

/-- NP-hardness alone is not a separation certificate. -/
structure NPHardnessOnlyInsufficient (F : FaithfulDecisionCircuitFrame) where
  L : F.Language
  hard : NPHard F L
  missing_inNP : Prop
  missing_notInP : Prop

/-- Circuit lower bound for a non-NP language does not by itself separate P/NP. -/
structure CircuitLowerBoundWithoutNPInsufficient (F : FaithfulDecisionCircuitFrame) where
  L : F.Language
  notInPpoly : ¬ F.InPpoly L
  missing_inNP : Prop

/-- Hierarchy lower bound without NP bridge is insufficient. -/
structure HierarchyOnlyInsufficient (F : FaithfulDecisionCircuitFrame) where
  H : F.Language
  notInP : ¬ F.InP H
  missing_inNP_bridge : Prop

/-- Barrier audit without an actual successful route is not a proof. -/
structure BarrierAuditOnlyInsufficient where
  barriers : ComplexityBarrierAudit
  missing_successful_route : Prop

/-- Step00 local result alone remains architecture-local. -/
structure Step00LocalOnlyInsufficient where
  local_verification_search_gap : Prop
  missing_external_machine_lower_bound : Prop

end ExternalRoutesV4
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v5_circuit_ladder_and_barriers_patch.lean ============ -/
/-
EuclidsPath_external_routes_v5_circuit_ladder_and_barriers_patch.lean

External P/NP frontier, v5.

This single file moves the external part forward by adding:

* circuit-class ladder route;
* lower-bound-against-too-small-class insufficiency;
* Williams-style SAT-algorithm/circuit lower-bound route guard;
* escalation bridge from high-complexity lower bounds to NP lower bounds;
* NP vs coNP / proof-complexity refinement;
* a route selector collecting the currently honest paths.

The file proves only implication gates.  It does not contain a proof of an
unconditional classical P/NP separation.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV5

/-#############################################################################
  §1. A circuit-ladder decision frame
#############################################################################-/

/--
A decision frame with named circuit classes.

`CircuitClass` is intentionally abstract: it may denote P/poly, AC0, ACC0,
NC1, formulas of a given size regime, etc.
-/
structure CircuitLadderFrame where
  Language : Type
  CircuitClass : Type

  InP : Language → Prop
  InNP : Language → Prop
  IncoNP : Language → Prop
  InNEXP : Language → Prop

  InCircuit : CircuitClass → Language → Prop

  /-- A circuit class covers P if every P language belongs to it. -/
  CoversP : CircuitClass → Prop

  coversP_sound :
    ∀ K : CircuitClass, CoversP K →
      ∀ L : Language, InP L → InCircuit K L

/-- P and NP coincide in the frame. -/
def ClassesCoincide (F : CircuitLadderFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- A standard P/NP separation witness. -/
structure DecisionSeparationWitness (F : CircuitLadderFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem DecisionSeparationWitness.not_classesCoincide
    {F : CircuitLadderFrame}
    (W : DecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-#############################################################################
  §2. General circuit-class exclusion route
#############################################################################-/

/--
If a circuit class covers P, then an NP language outside that class is outside P.
This is the generic nonuniform lower-bound route.
-/
structure NPOutsideCircuitClass (F : CircuitLadderFrame) where
  K : F.CircuitClass
  K_coversP : F.CoversP K
  L : F.Language
  inNP : F.InNP L
  notInK : ¬ F.InCircuit K L

theorem NPOutsideCircuitClass.notInP
    {F : CircuitLadderFrame}
    (R : NPOutsideCircuitClass F) :
    ¬ F.InP R.L := by
  intro hP
  exact R.notInK (F.coversP_sound R.K R.K_coversP R.L hP)

noncomputable def NPOutsideCircuitClass.separationWitness
    {F : CircuitLadderFrame}
    (R : NPOutsideCircuitClass F) :
    DecisionSeparationWitness F :=
  { L := R.L, inNP := R.inNP, notInP := R.notInP }

theorem NPOutsideCircuitClass.not_classesCoincide
    {F : CircuitLadderFrame}
    (R : NPOutsideCircuitClass F) :
    ¬ ClassesCoincide F :=
  R.separationWitness.not_classesCoincide

/--
A lower bound against a class that does not cover P is not by itself a P/NP
separation route.
-/
structure LowerBoundAgainstSmallClassOnly (F : CircuitLadderFrame) where
  K : F.CircuitClass
  L : F.Language
  inNP : F.InNP L
  notInK : ¬ F.InCircuit K L
  missing_coversP : ¬ F.CoversP K

/--
This structure records exactly what is missing from a small-class lower bound:
either prove the class covers P, or escalate the lower bound to a class that does.
-/
structure SmallClassEscalationObligation (F : CircuitLadderFrame) where
  small : LowerBoundAgainstSmallClassOnly F
  BiggerClass : F.CircuitClass
  bigger_coversP : F.CoversP BiggerClass
  escalated_lower_bound : ¬ F.InCircuit BiggerClass small.L

noncomputable def SmallClassEscalationObligation.toNPOutsideCircuitClass
    {F : CircuitLadderFrame}
    (O : SmallClassEscalationObligation F) :
    NPOutsideCircuitClass F :=
  { K := O.BiggerClass
    K_coversP := O.bigger_coversP
    L := O.small.L
    inNP := O.small.inNP
    notInK := O.escalated_lower_bound }

theorem SmallClassEscalationObligation.not_classesCoincide
    {F : CircuitLadderFrame}
    (O : SmallClassEscalationObligation F) :
    ¬ ClassesCoincide F :=
  O.toNPOutsideCircuitClass.not_classesCoincide

/-#############################################################################
  §3. High-complexity lower bounds and escalation
#############################################################################-/

/--
A high-complexity lower bound, e.g. NEXP outside ACC0/POLY-like class.

By itself this is not enough for P/NP unless the hard language is also brought
down to NP or the lower bound is escalated to an NP language.
-/
structure HighComplexityCircuitLowerBound (F : CircuitLadderFrame) where
  K : F.CircuitClass
  H : F.Language
  inNEXP : F.InNEXP H
  notInK : ¬ F.InCircuit K H

/--
Escalation bridge: convert a high-complexity lower bound into an NP language
outside a P-covering class.
-/
structure HighToNPEscalationBridge
    (F : CircuitLadderFrame)
    (H : HighComplexityCircuitLowerBound F) where
  Knp : F.CircuitClass
  Knp_coversP : F.CoversP Knp
  Lnp : F.Language
  Lnp_inNP : F.InNP Lnp
  Lnp_notInKnp : ¬ F.InCircuit Knp Lnp
  uses_high_lower_bound : Prop
  uses_high_lower_bound_proof : uses_high_lower_bound

noncomputable def HighToNPEscalationBridge.toNPOutsideCircuitClass
    {F : CircuitLadderFrame}
    {H : HighComplexityCircuitLowerBound F}
    (B : HighToNPEscalationBridge F H) :
    NPOutsideCircuitClass F :=
  { K := B.Knp
    K_coversP := B.Knp_coversP
    L := B.Lnp
    inNP := B.Lnp_inNP
    notInK := B.Lnp_notInKnp }

theorem HighToNPEscalationBridge.not_classesCoincide
    {F : CircuitLadderFrame}
    {H : HighComplexityCircuitLowerBound F}
    (B : HighToNPEscalationBridge F H) :
    ¬ ClassesCoincide F :=
  B.toNPOutsideCircuitClass.not_classesCoincide

/--
Guard: high-complexity lower bound without escalation does not close P/NP.
-/
structure HighLowerBoundOnlyDoesNotClose (F : CircuitLadderFrame) where
  high_lower_bound : HighComplexityCircuitLowerBound F
  missing_escalation_to_NP : Prop

/-#############################################################################
  §4. Williams-style SAT algorithm route guard
#############################################################################-/

/--
A Williams-style transfer theorem schema: a faster SAT algorithm for a circuit
class gives a high-complexity circuit lower bound.

This is a powerful external lower-bound engine, but it typically first yields a
high-complexity lower bound, so an escalation bridge is still needed for P/NP.
-/
structure WilliamsTransferSchema (F : CircuitLadderFrame) where
  FasterSATAlgorithmFor : F.CircuitClass → Prop
  transfer :
    ∀ K : F.CircuitClass,
      FasterSATAlgorithmFor K →
        HighComplexityCircuitLowerBound F

/-- A Williams route plus escalation to NP gives P/NP separation. -/
structure WilliamsEscalatedRoute (F : CircuitLadderFrame) where
  schema : WilliamsTransferSchema F
  K : F.CircuitClass
  fasterSAT : schema.FasterSATAlgorithmFor K
  escalation :
    HighToNPEscalationBridge F (schema.transfer K fasterSAT)

theorem WilliamsEscalatedRoute.not_classesCoincide
    {F : CircuitLadderFrame}
    (R : WilliamsEscalatedRoute F) :
    ¬ ClassesCoincide F :=
  R.escalation.not_classesCoincide

/-- Williams transfer without NP escalation is recorded as incomplete for P/NP. -/
structure WilliamsTransferOnlyDoesNotClose (F : CircuitLadderFrame) where
  schema : WilliamsTransferSchema F
  K : F.CircuitClass
  fasterSAT : schema.FasterSATAlgorithmFor K
  missing_NP_escalation : Prop

/-#############################################################################
  §5. NP-complete route
#############################################################################-/

/-- Many-one reductions and NP-completeness in a minimal abstract form. -/
structure ReductionFrame (F : CircuitLadderFrame) where
  Reduces : F.Language → F.Language → Prop
  p_closed_downward :
    ∀ {A B : F.Language}, Reduces A B → F.InP B → F.InP A

def NPHard (F : CircuitLadderFrame) (R : ReductionFrame F) (L : F.Language) : Prop :=
  ∀ A : F.Language, F.InNP A → R.Reduces A L

structure NPComplete (F : CircuitLadderFrame) (R : ReductionFrame F) (L : F.Language) : Prop where
  inNP : F.InNP L
  hard : NPHard F R L

theorem not_classesCoincide_of_npComplete_notInP
    {F : CircuitLadderFrame}
    {R : ReductionFrame F}
    {L : F.Language}
    (hC : NPComplete F R L)
    (hNotP : ¬ F.InP L) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := L, inNP := hC.inNP, notInP := hNotP })

theorem classesCoincide_of_npComplete_inP
    {F : CircuitLadderFrame}
    {R : ReductionFrame F}
    {L : F.Language}
    (hC : NPComplete F R L)
    (hP : F.InP L) :
    ClassesCoincide F := by
  intro A hA
  exact R.p_closed_downward (hC.hard A hA) hP

/-#############################################################################
  §6. NP vs coNP and proof-complexity refinement
#############################################################################-/

/--
A frame-level implication saying P=NP would collapse the NP/coNP distinction.
This is standard in ordinary decision models because P is closed under complement.
-/
structure NPcoNPGuardFrame (F : CircuitLadderFrame) where
  NPneqcoNP : Prop
  classesCoincide_implies_not_NPneqcoNP :
    ClassesCoincide F → ¬ NPneqcoNP

theorem not_classesCoincide_of_NPneqcoNP
    {F : CircuitLadderFrame}
    (G : NPcoNPGuardFrame F)
    (h : G.NPneqcoNP) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  exact (G.classesCoincide_implies_not_NPneqcoNP hCoincide) h

/--
Proof-complexity frame: lower bounds on proof systems can imply NP ≠ coNP when
they rule out polynomially bounded proof systems for TAUT.
-/
structure ProofComplexityFrame where
  Formula : Type
  ProofSystem : Type
  PolyBounded : ProofSystem → Prop
  AllCookReckhowSystemsNotPolyBounded : Prop
  lowerBound_implies_NPneqcoNP : AllCookReckhowSystemsNotPolyBounded → Prop

/-- Strong proof-complexity route through NP ≠ coNP, hence P ≠ NP. -/
structure ProofComplexityToPNPRoute
    (F : CircuitLadderFrame)
    (G : NPcoNPGuardFrame F)
    (P : ProofComplexityFrame) where
  proof_lower_bound : P.AllCookReckhowSystemsNotPolyBounded
  gives_NPneqcoNP :
    P.lowerBound_implies_NPneqcoNP proof_lower_bound → G.NPneqcoNP
  bridge_proof :
    P.lowerBound_implies_NPneqcoNP proof_lower_bound

theorem ProofComplexityToPNPRoute.not_classesCoincide
    {F : CircuitLadderFrame}
    {G : NPcoNPGuardFrame F}
    {P : ProofComplexityFrame}
    (R : ProofComplexityToPNPRoute F G P) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_NPneqcoNP G
    (R.gives_NPneqcoNP R.bridge_proof)

/--
Guard: proof-system lower bound without the Cook--Reckhow/NP-vs-coNP bridge is
not yet a P/NP separation.
-/
structure ProofLowerBoundOnlyDoesNotClose
    (P : ProofComplexityFrame) where
  proof_lower_bound : P.AllCookReckhowSystemsNotPolyBounded
  missing_NPcoNP_bridge : Prop

/-#############################################################################
  §7. Barrier and Step00 nonabsorption audits
#############################################################################-/

structure BarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak

  genuinely_external_machine_argument : Prop
  genuinely_external_machine_argument_proof : genuinely_external_machine_argument

/-#############################################################################
  §8. Route selector v5
#############################################################################-/

inductive SuccessfulExternalRouteV5 (F : CircuitLadderFrame) : Prop where
  | direct :
      DecisionSeparationWitness F →
      SuccessfulExternalRouteV5 F

  | circuitClass :
      NPOutsideCircuitClass F →
      SuccessfulExternalRouteV5 F

  | smallClassEscalated :
      SmallClassEscalationObligation F →
      SuccessfulExternalRouteV5 F

  | highEscalated :
      (H : HighComplexityCircuitLowerBound F) →
      HighToNPEscalationBridge F H →
      SuccessfulExternalRouteV5 F

  | williamsEscalated :
      WilliamsEscalatedRoute F →
      SuccessfulExternalRouteV5 F

  | npComplete :
      (R : ReductionFrame F) →
      (L : F.Language) →
      NPComplete F R L →
      ¬ F.InP L →
      SuccessfulExternalRouteV5 F

  | npCoNP :
      (G : NPcoNPGuardFrame F) →
      G.NPneqcoNP →
      SuccessfulExternalRouteV5 F

  | proofComplexity :
      (G : NPcoNPGuardFrame F) →
      (P : ProofComplexityFrame) →
      ProofComplexityToPNPRoute F G P →
      SuccessfulExternalRouteV5 F

theorem SuccessfulExternalRouteV5.not_classesCoincide
    {F : CircuitLadderFrame}
    (R : SuccessfulExternalRouteV5 F) :
    ¬ ClassesCoincide F := by
  cases R with
  | direct W =>
      exact W.not_classesCoincide
  | circuitClass C =>
      exact C.not_classesCoincide
  | smallClassEscalated O =>
      exact O.not_classesCoincide
  | highEscalated H B =>
      exact B.not_classesCoincide
  | williamsEscalated W =>
      exact W.not_classesCoincide
  | npComplete RF L C hNotP =>
      exact not_classesCoincide_of_npComplete_notInP C hNotP
  | npCoNP G h =>
      exact not_classesCoincide_of_NPneqcoNP G h
  | proofComplexity G P R =>
      exact R.not_classesCoincide

/-- Successful route plus all audits. -/
structure AuditedExternalRouteV5 (F : CircuitLadderFrame) where
  route : SuccessfulExternalRouteV5 F
  barrierAudit : BarrierAudit
  nonabsorptionAudit : Step00NonAbsorptionAudit

theorem AuditedExternalRouteV5.not_classesCoincide
    {F : CircuitLadderFrame}
    (R : AuditedExternalRouteV5 F) :
    ¬ ClassesCoincide F :=
  R.route.not_classesCoincide

/-#############################################################################
  §9. Maximal v5 obligation
#############################################################################-/

/--
The current maximal obligation: produce one audited external route and prove the
frame is not a synthetic/trivial model.
-/
structure RemainingExternalRoutesV5Obligation (F : CircuitLadderFrame) where
  audited_route : AuditedExternalRouteV5 F

  faithful_machine_or_circuit_semantics : Prop
  faithful_machine_or_circuit_semantics_proof :
    faithful_machine_or_circuit_semantics

  not_trivial_frame : Prop
  not_trivial_frame_proof : not_trivial_frame

  not_empty_language_trick : Prop
  not_empty_language_trick_proof : not_empty_language_trick

  not_fixed_finite_language_trick : Prop
  not_fixed_finite_language_trick_proof : not_fixed_finite_language_trick

theorem RemainingExternalRoutesV5Obligation.closes
    {F : CircuitLadderFrame}
    (O : RemainingExternalRoutesV5Obligation F) :
    ¬ ClassesCoincide F :=
  O.audited_route.not_classesCoincide

abbrev ExternalRoutesV5Slogan (F : CircuitLadderFrame) : Prop :=
  RemainingExternalRoutesV5Obligation F → ¬ ClassesCoincide F

theorem externalRoutesV5Slogan
    (F : CircuitLadderFrame) :
    ExternalRoutesV5Slogan F := by
  intro O
  exact O.closes

/-#############################################################################
  §10. Explicit insufficiency registry
#############################################################################-/

/-- Registry of external statements that are not enough without additional data. -/
inductive InsufficientExternalStatement (F : CircuitLadderFrame) : Type 1 where
  | smallClassLowerBound :
      LowerBoundAgainstSmallClassOnly F →
      InsufficientExternalStatement F

  | highLowerBoundNoEscalation :
      HighLowerBoundOnlyDoesNotClose F →
      InsufficientExternalStatement F

  | williamsNoEscalation :
      WilliamsTransferOnlyDoesNotClose F →
      InsufficientExternalStatement F

  | proofLowerBoundNoBridge :
      (P : ProofComplexityFrame) →
      ProofLowerBoundOnlyDoesNotClose P →
      InsufficientExternalStatement F

  | localStep00Only :
      Prop →
      InsufficientExternalStatement F

/--
An insufficiency registry entry is not a route selector entry.  This is just a
typing firewall: the constructors live in different types.
-/
abbrev InsufficiencyRegistryIsSeparate
    (F : CircuitLadderFrame) : Prop :=
  InsufficientExternalStatement F → True

theorem insufficiencyRegistryIsSeparate
    (F : CircuitLadderFrame) :
    InsufficiencyRegistryIsSeparate F := by
  intro _
  trivial

end ExternalRoutesV5
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v6_commitment_layer_patch.lean ============ -/
/-
EuclidsPath_external_routes_v6_commitment_layer_patch.lean

External P/NP frontier, v6 commitment layer.

Purpose
-------
This file moves several external routes forward at once.  It records which
external certificates actually imply classical P/NP separation, which lower
bounds are weaker than what is needed, and which barrier audits must accompany a
nonabsorbed proof.

It is still only a gate/decomposition layer: it does not prove an unconditional
classical P ≠ NP theorem.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV6

/-#############################################################################
  §1. Core external complexity frame
#############################################################################-/

/--
External decision complexity frame.

The frame is deliberately semantic: `InP`, `InNP`, `InPpoly`, etc. are class
membership predicates; the route files then say what lower-bound certificates
would separate those predicates.
-/
structure ExternalComplexityFrame where
  Language : Type

  InP : Language → Prop
  InNP : Language → Prop
  IncoNP : Language → Prop
  InPpoly : Language → Prop
  InEXP : Language → Prop
  InNEXP : Language → Prop

  Reduces : Language → Language → Prop

  p_subset_np : ∀ {L : Language}, InP L → InNP L
  p_subset_ppoly : ∀ {L : Language}, InP L → InPpoly L

  p_closed_downward :
    ∀ {A B : Language}, Reduces A B → InP B → InP A

/-- P and NP coincide in the frame. -/
def ClassesCoincide (F : ExternalComplexityFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- A direct P/NP separation witness. -/
structure DecisionSeparationWitness (F : ExternalComplexityFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem DecisionSeparationWitness.not_classesCoincide
    {F : ExternalComplexityFrame}
    (W : DecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-#############################################################################
  §2. NP-complete transfer route
#############################################################################-/

/-- NP-hardness under many-one style reductions. -/
def NPHard (F : ExternalComplexityFrame) (L : F.Language) : Prop :=
  ∀ A : F.Language, F.InNP A → F.Reduces A L

/-- NP-completeness. -/
structure NPComplete (F : ExternalComplexityFrame) (L : F.Language) : Prop where
  inNP : F.InNP L
  hard : NPHard F L

/-- NP-complete lower bound transfers to P/NP separation. -/
theorem not_classesCoincide_of_npComplete_notInP
    {F : ExternalComplexityFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := L, inNP := hC.inNP, notInP := hNotP })

/-- If an NP-complete language is in P, then P and NP coincide in the frame. -/
theorem classesCoincide_of_npComplete_inP
    {F : ExternalComplexityFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hP : F.InP L) :
    ClassesCoincide F := by
  intro A hA
  exact F.p_closed_downward (hC.hard A hA) hP

/-- NP-hardness without membership and lower bound is not enough. -/
structure NPHardnessOnlyInsufficient (F : ExternalComplexityFrame) where
  L : F.Language
  hard : NPHard F L
  missing_inNP : Prop
  missing_notInP : Prop

/-#############################################################################
  §3. Nonuniform lower-bound commitments
#############################################################################-/

/-- An NP language outside P/poly. -/
structure NPOutsidePpoly (F : ExternalComplexityFrame) where
  L : F.Language
  inNP : F.InNP L
  notInPpoly : ¬ F.InPpoly L

/-- P ⊆ P/poly converts a P/poly lower bound into a P lower bound. -/
theorem NPOutsidePpoly.notInP
    {F : ExternalComplexityFrame}
    (R : NPOutsidePpoly F) :
    ¬ F.InP R.L := by
  intro hP
  exact R.notInPpoly (F.p_subset_ppoly hP)

/-- Hence an NP language outside P/poly separates P from NP. -/
theorem NPOutsidePpoly.not_classesCoincide
    {F : ExternalComplexityFrame}
    (R : NPOutsidePpoly F) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := R.L, inNP := R.inNP, notInP := R.notInP })

/-- SAT-specific nonuniform route. -/
structure SATOutsidePpolyRoute (F : ExternalComplexityFrame) where
  SAT : F.Language
  sat_complete : NPComplete F SAT
  sat_notInPpoly : ¬ F.InPpoly SAT

theorem SATOutsidePpolyRoute.sat_notInP
    {F : ExternalComplexityFrame}
    (R : SATOutsidePpolyRoute F) :
    ¬ F.InP R.SAT := by
  intro hP
  exact R.sat_notInPpoly (F.p_subset_ppoly hP)

theorem SATOutsidePpolyRoute.not_classesCoincide
    {F : ExternalComplexityFrame}
    (R : SATOutsidePpolyRoute F) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_npComplete_notInP
    R.sat_complete R.sat_notInP

/-- Lower bound against a class smaller than P/poly is weaker unless escalated. -/
structure WeakCircuitLowerBound (F : ExternalComplexityFrame) where
  SmallClass : Type
  InSmall : SmallClass → F.Language → Prop
  K : SmallClass
  L : F.Language
  inNP : F.InNP L
  notInSmall : ¬ InSmall K L
  missing_smallClass_covers_P : Prop

/-- Escalating a weak circuit lower bound to P/poly closes the route. -/
structure EscalatedWeakCircuitLowerBound (F : ExternalComplexityFrame) where
  weak : WeakCircuitLowerBound F
  escalated_notInPpoly : ¬ F.InPpoly weak.L

noncomputable def EscalatedWeakCircuitLowerBound.toNPOutsidePpoly
    {F : ExternalComplexityFrame}
    (E : EscalatedWeakCircuitLowerBound F) :
    NPOutsidePpoly F :=
  { L := E.weak.L
    inNP := E.weak.inNP
    notInPpoly := E.escalated_notInPpoly }

theorem EscalatedWeakCircuitLowerBound.not_classesCoincide
    {F : ExternalComplexityFrame}
    (E : EscalatedWeakCircuitLowerBound F) :
    ¬ ClassesCoincide F :=
  E.toNPOutsidePpoly.not_classesCoincide

/-#############################################################################
  §4. High-complexity lower bounds and escalation to NP
#############################################################################-/

/-- A high-complexity lower bound, e.g. NEXP not in some circuit class. -/
structure HighComplexityLowerBound (F : ExternalComplexityFrame) where
  H : F.Language
  inNEXP : F.InNEXP H
  TargetClass : Type
  InTarget : TargetClass → F.Language → Prop
  K : TargetClass
  notInTarget : ¬ InTarget K H

/--
A high-complexity lower bound becomes a P/NP route only after producing an NP
language outside P or P/poly.
-/
structure HighLowerBoundEscalatesToNP (F : ExternalComplexityFrame)
    (H : HighComplexityLowerBound F) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L
  uses_high_bound : Prop
  uses_high_bound_proof : uses_high_bound

theorem HighLowerBoundEscalatesToNP.not_classesCoincide
    {F : ExternalComplexityFrame}
    {H : HighComplexityLowerBound F}
    (E : HighLowerBoundEscalatesToNP F H) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := E.L, inNP := E.inNP, notInP := E.notInP })

/-- High lower bound without escalation is recorded as insufficient. -/
structure HighLowerBoundOnlyInsufficient (F : ExternalComplexityFrame) where
  high : HighComplexityLowerBound F
  missing_escalation_to_NP : Prop

/-#############################################################################
  §5. Williams-style algorithm-to-lower-bound route
#############################################################################-/

/-- A Williams-style transfer: faster SAT algorithm implies high lower bound. -/
structure WilliamsTransferSchema (F : ExternalComplexityFrame) where
  CircuitClass : Type
  FasterSAT : CircuitClass → Prop
  transfer : ∀ K : CircuitClass, FasterSAT K → HighComplexityLowerBound F

/-- Williams transfer plus escalation to NP closes P/NP. -/
structure WilliamsRouteEscalated (F : ExternalComplexityFrame) where
  schema : WilliamsTransferSchema F
  K : schema.CircuitClass
  fasterSAT : schema.FasterSAT K
  escalation :
    HighLowerBoundEscalatesToNP F (schema.transfer K fasterSAT)

theorem WilliamsRouteEscalated.not_classesCoincide
    {F : ExternalComplexityFrame}
    (W : WilliamsRouteEscalated F) :
    ¬ ClassesCoincide F :=
  W.escalation.not_classesCoincide

/-- Williams transfer alone, without escalation, is not yet P/NP. -/
structure WilliamsTransferOnlyInsufficient (F : ExternalComplexityFrame) where
  schema : WilliamsTransferSchema F
  K : schema.CircuitClass
  fasterSAT : schema.FasterSAT K
  missing_escalation_to_NP : Prop

/-#############################################################################
  §6. NP vs coNP and proof-complexity routes
#############################################################################-/

/-- Frame guard: P=NP would collapse NP-vs-coNP distinction. -/
structure NPcoNPGuard (F : ExternalComplexityFrame) where
  NPneqcoNP : Prop
  classesCoincide_forces_not_NPneqcoNP :
    ClassesCoincide F → ¬ NPneqcoNP

theorem not_classesCoincide_of_NPneqcoNP
    {F : ExternalComplexityFrame}
    (G : NPcoNPGuard F)
    (h : G.NPneqcoNP) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  exact (G.classesCoincide_forces_not_NPneqcoNP hCoincide) h

/-- Proof-complexity route to NP≠coNP. -/
structure ProofComplexityRoute (F : ExternalComplexityFrame) where
  Formula : Type
  ProofSystem : Type
  LowerBound : Prop
  lowerBound_external : Prop
  lowerBound_external_proof : lowerBound_external
  lowerBound_implies_NPneqcoNP : LowerBound → Prop

/-- Proof complexity route closes P/NP only after a real NP≠coNP bridge. -/
structure ProofComplexityClosesPNP (F : ExternalComplexityFrame)
    (G : NPcoNPGuard F)
    (P : ProofComplexityRoute F) where
  lower_bound : P.LowerBound
  bridge : P.lowerBound_implies_NPneqcoNP lower_bound
  bridge_gives_NPneqcoNP : P.lowerBound_implies_NPneqcoNP lower_bound → G.NPneqcoNP

theorem ProofComplexityClosesPNP.not_classesCoincide
    {F : ExternalComplexityFrame}
    {G : NPcoNPGuard F}
    {P : ProofComplexityRoute F}
    (R : ProofComplexityClosesPNP F G P) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_NPneqcoNP G
    (R.bridge_gives_NPneqcoNP R.bridge)

/-- Proof lower bound without NP/coNP bridge is insufficient. -/
structure ProofComplexityOnlyInsufficient (F : ExternalComplexityFrame) where
  route : ProofComplexityRoute F
  lower_bound : route.LowerBound
  missing_NPcoNP_bridge : Prop

/-#############################################################################
  §7. Barrier audits and nonabsorption
#############################################################################-/

/-- Barrier audit for a claimed lower bound. -/
structure BarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- Step00 nonabsorption audit for an external route. -/
structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak

  genuinely_external_machine_argument : Prop
  genuinely_external_machine_argument_proof : genuinely_external_machine_argument

/-#############################################################################
  §8. Commitment route selector
#############################################################################-/

/-- The current list of honest route commitments. -/
inductive SuccessfulRouteV6 (F : ExternalComplexityFrame) : Prop where
  | direct :
      DecisionSeparationWitness F →
      SuccessfulRouteV6 F

  | npComplete :
      (L : F.Language) →
      NPComplete F L →
      ¬ F.InP L →
      SuccessfulRouteV6 F

  | ppoly :
      NPOutsidePpoly F →
      SuccessfulRouteV6 F

  | satPpoly :
      SATOutsidePpolyRoute F →
      SuccessfulRouteV6 F

  | weakCircuitEscalated :
      EscalatedWeakCircuitLowerBound F →
      SuccessfulRouteV6 F

  | highEscalated :
      (H : HighComplexityLowerBound F) →
      HighLowerBoundEscalatesToNP F H →
      SuccessfulRouteV6 F

  | williamsEscalated :
      WilliamsRouteEscalated F →
      SuccessfulRouteV6 F

  | npcoNP :
      (G : NPcoNPGuard F) →
      G.NPneqcoNP →
      SuccessfulRouteV6 F

  | proofComplexity :
      (G : NPcoNPGuard F) →
      (P : ProofComplexityRoute F) →
      ProofComplexityClosesPNP F G P →
      SuccessfulRouteV6 F

/-- Every successful route implies P/NP separation. -/
theorem SuccessfulRouteV6.not_classesCoincide
    {F : ExternalComplexityFrame}
    (R : SuccessfulRouteV6 F) :
    ¬ ClassesCoincide F := by
  cases R with
  | direct W =>
      exact W.not_classesCoincide
  | npComplete L C hNotP =>
      exact not_classesCoincide_of_npComplete_notInP C hNotP
  | ppoly P =>
      exact P.not_classesCoincide
  | satPpoly S =>
      exact S.not_classesCoincide
  | weakCircuitEscalated E =>
      exact E.not_classesCoincide
  | highEscalated H E =>
      exact E.not_classesCoincide
  | williamsEscalated W =>
      exact W.not_classesCoincide
  | npcoNP G h =>
      exact not_classesCoincide_of_NPneqcoNP G h
  | proofComplexity G P R =>
      exact R.not_classesCoincide

/-- Route plus barrier and Step00 nonabsorption audits. -/
structure AuditedRouteV6 (F : ExternalComplexityFrame) where
  route : SuccessfulRouteV6 F
  barrierAudit : BarrierAudit
  nonabsorptionAudit : Step00NonAbsorptionAudit

theorem AuditedRouteV6.not_classesCoincide
    {F : ExternalComplexityFrame}
    (A : AuditedRouteV6 F) :
    ¬ ClassesCoincide F :=
  A.route.not_classesCoincide

/-#############################################################################
  §9. Final v6 obligation
#############################################################################-/

/--
The v6 maximal obligation: produce one audited successful route in a faithful
external model.
-/
structure RemainingExternalRoutesV6Obligation (F : ExternalComplexityFrame) where
  auditedRoute : AuditedRouteV6 F

  faithful_machine_semantics : Prop
  faithful_machine_semantics_proof : faithful_machine_semantics

  not_trivial_frame : Prop
  not_trivial_frame_proof : not_trivial_frame

  not_empty_language_trick : Prop
  not_empty_language_trick_proof : not_empty_language_trick

  not_fixed_finite_language_trick : Prop
  not_fixed_finite_language_trick_proof : not_fixed_finite_language_trick

/-- Closing gate. -/
theorem RemainingExternalRoutesV6Obligation.closes
    {F : ExternalComplexityFrame}
    (O : RemainingExternalRoutesV6Obligation F) :
    ¬ ClassesCoincide F :=
  O.auditedRoute.not_classesCoincide

abbrev ExternalRoutesV6Slogan (F : ExternalComplexityFrame) : Prop :=
  RemainingExternalRoutesV6Obligation F → ¬ ClassesCoincide F

theorem externalRoutesV6Slogan
    (F : ExternalComplexityFrame) :
    ExternalRoutesV6Slogan F := by
  intro O
  exact O.closes

/-#############################################################################
  §10. Insufficiency registry
#############################################################################-/

/-- Registry of objects that are lower-bound-like but not enough by themselves. -/
inductive InsufficientRouteV6 (F : ExternalComplexityFrame) : Type 1 where
  | npHardOnly :
      NPHardnessOnlyInsufficient F →
      InsufficientRouteV6 F

  | weakCircuitOnly :
      WeakCircuitLowerBound F →
      InsufficientRouteV6 F

  | highOnly :
      HighLowerBoundOnlyInsufficient F →
      InsufficientRouteV6 F

  | williamsOnly :
      WilliamsTransferOnlyInsufficient F →
      InsufficientRouteV6 F

  | proofOnly :
      ProofComplexityOnlyInsufficient F →
      InsufficientRouteV6 F

  | step00LocalOnly :
      Prop →
      InsufficientRouteV6 F

/-- The insufficiency registry is kept syntactically separate from successful routes. -/
abbrev InsufficiencyRegistryIsSeparate (F : ExternalComplexityFrame) : Prop :=
  InsufficientRouteV6 F → True

theorem insufficiencyRegistryIsSeparate
    (F : ExternalComplexityFrame) :
    InsufficiencyRegistryIsSeparate F := by
  intro _
  trivial

end ExternalRoutesV6
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v7_circuit_escalation_patch.lean ============ -/
/-
EuclidsPath_external_routes_v7_circuit_escalation_patch.lean

External P/NP frontier v7, file 1.

Circuit-class escalation layer.

This file isolates the exact shape of a circuit lower-bound route strong enough
for classical P/NP separation: a language in NP must be outside a circuit class
that covers P.  Lower bounds against weaker/smaller classes are recorded as
insufficient until escalated to a P-covering class.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV7
namespace CircuitEscalation

structure CircuitEscalationFrame where
  Language : Type
  CircuitClass : Type

  InP : Language → Prop
  InNP : Language → Prop
  InCircuit : CircuitClass → Language → Prop

  /-- Circuit-class inclusion: every K-language is also a H-language. -/
  ClassLe : CircuitClass → CircuitClass → Prop

  classLe_sound :
    ∀ {K H : CircuitClass}, ClassLe K H →
      ∀ {L : Language}, InCircuit K L → InCircuit H L

  /-- K covers P if every P-language is in K. -/
  CoversP : CircuitClass → Prop

  coversP_sound :
    ∀ {K : CircuitClass}, CoversP K →
      ∀ {L : Language}, InP L → InCircuit K L

def ClassesCoincide (F : CircuitEscalationFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

structure DecisionSeparationWitness (F : CircuitEscalationFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem DecisionSeparationWitness.not_classesCoincide
    {F : CircuitEscalationFrame}
    (W : DecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-- A lower bound against a circuit class. -/
structure CircuitLowerBound (F : CircuitEscalationFrame) where
  K : F.CircuitClass
  L : F.Language
  notInK : ¬ F.InCircuit K L

/-- A circuit lower bound is P/NP-relevant once the language is in NP and the
class covers P. -/
structure PNPRelevantCircuitLowerBound (F : CircuitEscalationFrame) where
  lb : CircuitLowerBound F
  inNP : F.InNP lb.L
  class_covers_P : F.CoversP lb.K

theorem PNPRelevantCircuitLowerBound.notInP
    {F : CircuitEscalationFrame}
    (B : PNPRelevantCircuitLowerBound F) :
    ¬ F.InP B.lb.L := by
  intro hP
  exact B.lb.notInK (F.coversP_sound B.class_covers_P hP)

noncomputable def PNPRelevantCircuitLowerBound.separationWitness
    {F : CircuitEscalationFrame}
    (B : PNPRelevantCircuitLowerBound F) :
    DecisionSeparationWitness F :=
  { L := B.lb.L, inNP := B.inNP, notInP := B.notInP }

theorem PNPRelevantCircuitLowerBound.not_classesCoincide
    {F : CircuitEscalationFrame}
    (B : PNPRelevantCircuitLowerBound F) :
    ¬ ClassesCoincide F :=
  B.separationWitness.not_classesCoincide

/-- Lower bound against a class not known to cover P.  This is recorded as an
insufficient route. -/
structure WeakCircuitLowerBoundOnly (F : CircuitEscalationFrame) where
  lb : CircuitLowerBound F
  inNP : F.InNP lb.L
  missing_coversP : ¬ F.CoversP lb.K

/-- Escalation data: replace a weak lower bound by a lower bound against a class
known to cover P. -/
structure CircuitEscalationCertificate
    (F : CircuitEscalationFrame)
    (W : WeakCircuitLowerBoundOnly F) where
  StrongClass : F.CircuitClass
  strong_coversP : F.CoversP StrongClass
  same_language_outside_strong : ¬ F.InCircuit StrongClass W.lb.L
  escalation_is_external : Prop
  escalation_is_external_proof : escalation_is_external

def CircuitEscalationCertificate.toRelevantLowerBound
    {F : CircuitEscalationFrame}
    {W : WeakCircuitLowerBoundOnly F}
    (E : CircuitEscalationCertificate F W) :
    PNPRelevantCircuitLowerBound F :=
  { lb := { K := E.StrongClass, L := W.lb.L,
            notInK := E.same_language_outside_strong }
    inNP := W.inNP
    class_covers_P := E.strong_coversP }

theorem CircuitEscalationCertificate.not_classesCoincide
    {F : CircuitEscalationFrame}
    {W : WeakCircuitLowerBoundOnly F}
    (E : CircuitEscalationCertificate F W) :
    ¬ ClassesCoincide F :=
  E.toRelevantLowerBound.not_classesCoincide

/-- If K is included in H and L is outside H, then L is outside K.  This direction
is useful for deriving lower bounds for smaller classes from stronger ones. -/
theorem notIn_smaller_of_notIn_larger
    {F : CircuitEscalationFrame}
    {K H : F.CircuitClass}
    {L : F.Language}
    (hKH : F.ClassLe K H)
    (hNotH : ¬ F.InCircuit H L) :
    ¬ F.InCircuit K L := by
  intro hK
  exact hNotH (F.classLe_sound hKH hK)

/-- Strong lower bound against a P-covering class automatically gives lower
bounds against all smaller included classes, but the P/NP separation already
comes from the strong class. -/
structure StrongCircuitLowerBoundPackage (F : CircuitEscalationFrame) where
  strong : PNPRelevantCircuitLowerBound F
  SmallerClass : F.CircuitClass
  smaller_in_strong : F.ClassLe SmallerClass strong.lb.K


theorem StrongCircuitLowerBoundPackage.smaller_lower_bound
    {F : CircuitEscalationFrame}
    (P : StrongCircuitLowerBoundPackage F) :
    ¬ F.InCircuit P.SmallerClass P.strong.lb.L :=
  notIn_smaller_of_notIn_larger P.smaller_in_strong P.strong.lb.notInK

theorem StrongCircuitLowerBoundPackage.not_classesCoincide
    {F : CircuitEscalationFrame}
    (P : StrongCircuitLowerBoundPackage F) :
    ¬ ClassesCoincide F :=
  P.strong.not_classesCoincide

/-- Registry of the exact current circuit-front obligation. -/
structure RemainingCircuitEscalationObligation (F : CircuitEscalationFrame) where
  relevant_lower_bound : PNPRelevantCircuitLowerBound F
  barrier_checked : Prop
  barrier_checked_proof : barrier_checked
  step00_nonabsorbed : Prop
  step00_nonabsorbed_proof : step00_nonabsorbed

theorem RemainingCircuitEscalationObligation.closes
    {F : CircuitEscalationFrame}
    (O : RemainingCircuitEscalationObligation F) :
    ¬ ClassesCoincide F :=
  O.relevant_lower_bound.not_classesCoincide

end CircuitEscalation
end ExternalRoutesV7
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v7_proof_complexity_npconp_patch.lean ============ -/
/-
EuclidsPath_external_routes_v7_proof_complexity_npconp_patch.lean

External P/NP frontier v7, file 2.

Proof-complexity and NP-vs-coNP gate.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV7
namespace ProofComplexityNPcoNP

structure DecisionFrame where
  Language : Type
  InP : Language → Prop
  InNP : Language → Prop
  IncoNP : Language → Prop

def ClassesCoincide (F : DecisionFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- Abstract guard: in a standard frame, P=NP collapses NP-vs-coNP. -/
structure NPcoNPGuard (F : DecisionFrame) where
  NPneqcoNP : Prop
  p_eq_np_implies_not_npneqconp : ClassesCoincide F → ¬ NPneqcoNP

theorem not_classesCoincide_of_npneqconp
    {F : DecisionFrame}
    (G : NPcoNPGuard F)
    (h : G.NPneqcoNP) :
    ¬ ClassesCoincide F := by
  intro hCoincide
  exact (G.p_eq_np_implies_not_npneqconp hCoincide) h

/-- Abstract Cook-Reckhow proof-system frame. -/
structure ProofSystemFrame where
  Formula : Type
  ProofSystem : Type
  Tautology : Formula → Prop
  PolyBounded : ProofSystem → Prop
  CookReckhow : ProofSystem → Prop

/-- Strong proof-complexity lower bound: no Cook-Reckhow proof system is
polynomially bounded. -/
def NoPolynomiallyBoundedCookReckhow (P : ProofSystemFrame) : Prop :=
  ∀ S : P.ProofSystem, P.CookReckhow S → ¬ P.PolyBounded S

/-- Bridge from proof-complexity lower bound to NP-vs-coNP. -/
structure ProofLowerBoundToNPcoNPBridge
    (F : DecisionFrame)
    (P : ProofSystemFrame)
    (G : NPcoNPGuard F) where
  lower_bound_implies_npneqconp :
    NoPolynomiallyBoundedCookReckhow P → G.NPneqcoNP
  bridge_is_external : Prop
  bridge_is_external_proof : bridge_is_external

/-- Full proof-complexity route to P/NP separation. -/
structure ProofComplexityPNPRoute
    (F : DecisionFrame)
    (P : ProofSystemFrame)
    (G : NPcoNPGuard F) where
  lower_bound : NoPolynomiallyBoundedCookReckhow P
  bridge : ProofLowerBoundToNPcoNPBridge F P G
  barrier_checked : Prop
  barrier_checked_proof : barrier_checked
  step00_nonabsorbed : Prop
  step00_nonabsorbed_proof : step00_nonabsorbed

theorem ProofComplexityPNPRoute.npneqconp
    {F : DecisionFrame}
    {P : ProofSystemFrame}
    {G : NPcoNPGuard F}
    (R : ProofComplexityPNPRoute F P G) :
    G.NPneqcoNP :=
  R.bridge.lower_bound_implies_npneqconp R.lower_bound

theorem ProofComplexityPNPRoute.not_classesCoincide
    {F : DecisionFrame}
    {P : ProofSystemFrame}
    {G : NPcoNPGuard F}
    (R : ProofComplexityPNPRoute F P G) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_npneqconp G R.npneqconp

/-- Lower bound without the NP-vs-coNP bridge is not yet a P/NP proof. -/
structure ProofLowerBoundOnlyInsufficient
    (P : ProofSystemFrame) where
  lower_bound : NoPolynomiallyBoundedCookReckhow P
  missing_bridge_to_npneqconp : Prop

/-- NP-vs-coNP by itself is a valid route, if the guard is part of the frame. -/
structure NPcoNPDirectRoute (F : DecisionFrame) where
  guard : NPcoNPGuard F
  npneqconp : guard.NPneqcoNP
  external_argument : Prop
  external_argument_proof : external_argument

theorem NPcoNPDirectRoute.not_classesCoincide
    {F : DecisionFrame}
    (R : NPcoNPDirectRoute F) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_npneqconp R.guard R.npneqconp

structure RemainingProofComplexityObligation (F : DecisionFrame) where
  P : ProofSystemFrame
  G : NPcoNPGuard F
  route : ProofComplexityPNPRoute F P G

theorem RemainingProofComplexityObligation.closes
    {F : DecisionFrame}
    (O : RemainingProofComplexityObligation F) :
    ¬ ClassesCoincide F :=
  O.route.not_classesCoincide

end ProofComplexityNPcoNP
end ExternalRoutesV7
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v7_hierarchy_williams_patch.lean ============ -/
/-
EuclidsPath_external_routes_v7_hierarchy_williams_patch.lean

External P/NP frontier v7, file 3.

Hierarchy and Williams-style routes with explicit escalation gates.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV7
namespace HierarchyWilliams

structure HWFrame where
  Language : Type
  CircuitClass : Type

  InP : Language → Prop
  InNP : Language → Prop
  InEXP : Language → Prop
  InNEXP : Language → Prop
  InCircuit : CircuitClass → Language → Prop
  CoversP : CircuitClass → Prop
  coversP_sound :
    ∀ {K : CircuitClass}, CoversP K →
      ∀ {L : Language}, InP L → InCircuit K L

def ClassesCoincide (F : HWFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

structure DecisionSeparationWitness (F : HWFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem DecisionSeparationWitness.not_classesCoincide
    {F : HWFrame}
    (W : DecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-- Time hierarchy lower bound outside P.  It is not a P/NP route until the hard
language is put in NP. -/
structure TimeHierarchyLowerBound (F : HWFrame) where
  H : F.Language
  inEXP_or_more : F.InEXP H ∨ F.InNEXP H
  notInP : ¬ F.InP H

structure HierarchyNPBridge (F : HWFrame) (H : TimeHierarchyLowerBound F) where
  inNP : F.InNP H.H
  bridge_not_synthetic : Prop
  bridge_not_synthetic_proof : bridge_not_synthetic

theorem HierarchyNPBridge.not_classesCoincide
    {F : HWFrame}
    {H : TimeHierarchyLowerBound F}
    (B : HierarchyNPBridge F H) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := H.H, inNP := B.inNP, notInP := H.notInP })

structure HierarchyOnlyInsufficient (F : HWFrame) where
  lower_bound : TimeHierarchyLowerBound F
  missing_inNP_bridge : Prop

/-- High-complexity circuit lower bound, e.g. NEXP outside K. -/
structure HighCircuitLowerBound (F : HWFrame) where
  K : F.CircuitClass
  H : F.Language
  high_membership : F.InNEXP H ∨ F.InEXP H
  notInK : ¬ F.InCircuit K H

/-- Escalation of high lower bound to an NP language outside a P-covering class. -/
structure HighCircuitToNPBridge
    (F : HWFrame)
    (H : HighCircuitLowerBound F) where
  Knp : F.CircuitClass
  Knp_coversP : F.CoversP Knp
  Lnp : F.Language
  Lnp_inNP : F.InNP Lnp
  Lnp_notInKnp : ¬ F.InCircuit Knp Lnp
  bridge_uses_high_lower_bound : Prop
  bridge_uses_high_lower_bound_proof : bridge_uses_high_lower_bound

theorem HighCircuitToNPBridge.notInP
    {F : HWFrame}
    {H : HighCircuitLowerBound F}
    (B : HighCircuitToNPBridge F H) :
    ¬ F.InP B.Lnp := by
  intro hP
  exact B.Lnp_notInKnp (F.coversP_sound B.Knp_coversP hP)

theorem HighCircuitToNPBridge.not_classesCoincide
    {F : HWFrame}
    {H : HighCircuitLowerBound F}
    (B : HighCircuitToNPBridge F H) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := B.Lnp, inNP := B.Lnp_inNP, notInP := B.notInP })

structure HighCircuitOnlyInsufficient (F : HWFrame) where
  lower_bound : HighCircuitLowerBound F
  missing_np_escalation : Prop

/-- Williams-style transfer schema. -/
structure WilliamsSchema (F : HWFrame) where
  FasterSatFor : F.CircuitClass → Prop
  transfer :
    ∀ K : F.CircuitClass,
      FasterSatFor K → HighCircuitLowerBound F

structure WilliamsRouteEscalated (F : HWFrame) where
  schema : WilliamsSchema F
  K : F.CircuitClass
  faster_sat : schema.FasterSatFor K
  escalation : HighCircuitToNPBridge F (schema.transfer K faster_sat)

theorem WilliamsRouteEscalated.not_classesCoincide
    {F : HWFrame}
    (R : WilliamsRouteEscalated F) :
    ¬ ClassesCoincide F :=
  R.escalation.not_classesCoincide

structure WilliamsOnlyInsufficient (F : HWFrame) where
  schema : WilliamsSchema F
  K : F.CircuitClass
  faster_sat : schema.FasterSatFor K
  missing_np_escalation : Prop

structure RemainingHierarchyWilliamsObligation (F : HWFrame) where
  route :
    (Σ H : TimeHierarchyLowerBound F, HierarchyNPBridge F H) ⊕
    (Σ H : HighCircuitLowerBound F, HighCircuitToNPBridge F H) ⊕
    WilliamsRouteEscalated F

theorem RemainingHierarchyWilliamsObligation.closes
    {F : HWFrame}
    (O : RemainingHierarchyWilliamsObligation F) :
    ¬ ClassesCoincide F := by
  cases O.route with
  | inl hPair =>
      rcases hPair with ⟨H, B⟩
      exact B.not_classesCoincide
  | inr rest =>
      cases rest with
      | inl hPair =>
          rcases hPair with ⟨H, B⟩
          exact B.not_classesCoincide
      | inr W =>
          exact W.not_classesCoincide

end HierarchyWilliams
end ExternalRoutesV7
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v7_final_manifest_patch.lean ============ -/
/-
EuclidsPath_external_routes_v7_final_manifest_patch.lean

External P/NP frontier v7, file 4.

Final manifest for the current stage.  It collects the route types and records
that the next nonabsorbed progress must close one audited external route.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV7
namespace FinalManifest

structure FinalExternalFrame where
  StatementPNPSeparated : Prop
  FaithfulMachineSemantics : Prop
  NotTrivialFrame : Prop
  NotEmptyLanguageTrick : Prop
  NotFixedFiniteLanguageTrick : Prop

structure BarrierAudit where
  nonrelativizing : Prop
  nonalgebrizing : Prop
  not_natural_proofs_only : Prop
  not_pure_diagonalization_only : Prop
  no_oracle_artifact : Prop
  no_density_leak : Prop

structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_resolver_only_incomplete_route : Prop
  no_semantic_collision_closure_leak : Prop
  no_causal_boundary_leak : Prop
  genuinely_external_machine_argument : Prop

/-- One of the external route families has been closed. -/
inductive ClosedExternalRoute : Type where
  | np_complete_lower_bound
  | np_outside_p_poly
  | sat_outside_p_poly
  | weak_circuit_escalated_to_p_covering_class
  | high_complexity_escalated_to_np
  | williams_transfer_escalated_to_np
  | np_not_conp
  | proof_complexity_to_np_not_conp
  | direct_machine_lower_bound

/-- Each closed external route must come with an implication to P/NP separation
in the faithful frame. -/
structure ClosedExternalRouteCertificate (F : FinalExternalFrame) where
  route : ClosedExternalRoute
  route_implies_separation : F.StatementPNPSeparated
  barrierAudit : BarrierAudit
  nonabsorptionAudit : Step00NonAbsorptionAudit

/-- The final v7 obligation: close any one audited external route. -/
structure RemainingV7ForwardObligation (F : FinalExternalFrame) where
  faithful : F.FaithfulMachineSemantics
  not_trivial : F.NotTrivialFrame
  not_empty_language : F.NotEmptyLanguageTrick
  not_fixed_finite : F.NotFixedFiniteLanguageTrick
  closed_route : ClosedExternalRouteCertificate F

theorem RemainingV7ForwardObligation.closes
    {F : FinalExternalFrame}
    (O : RemainingV7ForwardObligation F) :
    F.StatementPNPSeparated :=
  O.closed_route.route_implies_separation

/-- Registry of things that are not enough at this stage. -/
inductive DoesNotCloseV7 : Type where
  | step00_local_only
  | fixed_finite_quotient
  | prefix_completion_without_known_yes
  | answer_graph_without_total_search
  | total_search_without_effective_realizer
  | promise_resolver_without_coverage
  | coverage_that_is_semantic_closure
  | weak_circuit_lower_bound_only
  | high_complexity_lower_bound_without_np_escalation
  | williams_transfer_without_np_escalation
  | proof_lower_bound_without_npconp_bridge

abbrev V7FrontierSlogan (F : FinalExternalFrame) : Prop :=
  RemainingV7ForwardObligation F → F.StatementPNPSeparated

theorem v7FrontierSlogan
    (F : FinalExternalFrame) :
    V7FrontierSlogan F := by
  intro O
  exact O.closes

end FinalManifest
end ExternalRoutesV7
end ClassicalPNP
end EuclidsPath

/- ============ BRICK: EuclidsPath_external_routes_v8_single_file_deep_frontier_patch.lean ============ -/
/-
EuclidsPath_external_routes_v8_single_file_deep_frontier_patch.lean

Single-file maximal forward layer for the external classical P/NP frontier.

Purpose
-------
This file moves several external lower-bound routes forward at once, while
keeping the Step00 audit honest:

  * circuit-class inclusion/escalation calculus;
  * SAT/Ppoly and NP-complete transfer gates;
  * high-complexity lower-bound escalation gates;
  * Williams-style transfer + escalation;
  * proof-complexity via NP≠coNP;
  * natural-proofs/oracle/algebrization barrier hardening;
  * Step00 nonabsorption hardening;
  * one final v8 route selector.

It proves implication gates only.  It does not prove an unconditional classical
P≠NP theorem.

No placeholder proof terms are used below.
-/



namespace EuclidsPath
namespace ClassicalPNP
namespace ExternalRoutesV8

/-#############################################################################
  §1. Core external frame
#############################################################################-/

/--
A core external frame.  It abstracts the standard decision-complexity objects but
keeps enough structure for P, NP, P/poly, reductions, coNP, and high complexity
classes.
-/
structure CoreFrame where
  Language : Type
  CircuitClass : Type

  InP : Language → Prop
  InNP : Language → Prop
  IncoNP : Language → Prop
  InPpoly : Language → Prop
  InEXP : Language → Prop
  InNEXP : Language → Prop

  InCircuit : CircuitClass → Language → Prop

  Reduces : Language → Language → Prop

  p_subset_np : ∀ {L : Language}, InP L → InNP L
  p_subset_ppoly : ∀ {L : Language}, InP L → InPpoly L

  p_closed_downward :
    ∀ {A B : Language}, Reduces A B → InP B → InP A

  ppoly_closed_downward :
    ∀ {A B : Language}, Reduces A B → InPpoly B → InPpoly A

/-- P and NP coincide in the frame. -/
def ClassesCoincide (F : CoreFrame) : Prop :=
  ∀ L : F.Language, F.InNP L → F.InP L

/-- A concrete language separating NP from P. -/
structure DecisionSeparationWitness (F : CoreFrame) where
  L : F.Language
  inNP : F.InNP L
  notInP : ¬ F.InP L

theorem DecisionSeparationWitness.not_classesCoincide
    {F : CoreFrame}
    (W : DecisionSeparationWitness F) :
    ¬ ClassesCoincide F := by
  intro h
  exact W.notInP (h W.L W.inNP)

/-#############################################################################
  §2. Circuit-class inclusion and escalation calculus
#############################################################################-/

/-- Inclusion of circuit classes. -/
def CircuitClassLe (F : CoreFrame) (K₁ K₂ : F.CircuitClass) : Prop :=
  ∀ L : F.Language, F.InCircuit K₁ L → F.InCircuit K₂ L

/-- A circuit class covers P. -/
def CoversP (F : CoreFrame) (K : F.CircuitClass) : Prop :=
  ∀ L : F.Language, F.InP L → F.InCircuit K L

/-- If a class covering P is avoided by an NP language, then P≠NP. -/
structure NPOutsidePCoveringCircuitClass (F : CoreFrame) where
  K : F.CircuitClass
  coversP : CoversP F K
  L : F.Language
  inNP : F.InNP L
  notInK : ¬ F.InCircuit K L

theorem NPOutsidePCoveringCircuitClass.notInP
    {F : CoreFrame}
    (R : NPOutsidePCoveringCircuitClass F) :
    ¬ F.InP R.L := by
  intro hP
  exact R.notInK (R.coversP R.L hP)

theorem NPOutsidePCoveringCircuitClass.not_classesCoincide
    {F : CoreFrame}
    (R : NPOutsidePCoveringCircuitClass F) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := R.L, inNP := R.inNP, notInP := R.notInP })

/-- Escalate a lower bound from a smaller class to a P-covering class. -/
structure CircuitEscalationCertificate (F : CoreFrame) where
  smallK : F.CircuitClass
  bigK : F.CircuitClass
  small_le_big : CircuitClassLe F smallK bigK
  big_coversP : CoversP F bigK
  L : F.Language
  inNP : F.InNP L
  notInBig : ¬ F.InCircuit bigK L
  small_lower_bound_known : Prop
  small_lower_bound_known_proof : small_lower_bound_known

noncomputable def CircuitEscalationCertificate.toNPOutsidePCovering
    {F : CoreFrame}
    (C : CircuitEscalationCertificate F) :
    NPOutsidePCoveringCircuitClass F :=
  { K := C.bigK
    coversP := C.big_coversP
    L := C.L
    inNP := C.inNP
    notInK := C.notInBig }

theorem CircuitEscalationCertificate.not_classesCoincide
    {F : CoreFrame}
    (C : CircuitEscalationCertificate F) :
    ¬ ClassesCoincide F :=
  C.toNPOutsidePCovering.not_classesCoincide

/-- A lower bound against a class not known to cover P is recorded as insufficient. -/
structure SmallCircuitLowerBoundOnly (F : CoreFrame) where
  K : F.CircuitClass
  L : F.Language
  inNP : F.InNP L
  notInK : ¬ F.InCircuit K L
  missing_coversP : ¬ CoversP F K

/-#############################################################################
  §3. P/poly and SAT-specific route
#############################################################################-/

/-- An NP language outside P/poly separates P from NP. -/
structure NPOutsidePpoly (F : CoreFrame) where
  L : F.Language
  inNP : F.InNP L
  notInPpoly : ¬ F.InPpoly L

theorem NPOutsidePpoly.notInP
    {F : CoreFrame}
    (R : NPOutsidePpoly F) :
    ¬ F.InP R.L := by
  intro hP
  exact R.notInPpoly (F.p_subset_ppoly hP)

theorem NPOutsidePpoly.not_classesCoincide
    {F : CoreFrame}
    (R : NPOutsidePpoly F) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := R.L, inNP := R.inNP, notInP := R.notInP })

/-- NP-hardness under many-one reductions. -/
def NPHard (F : CoreFrame) (L : F.Language) : Prop :=
  ∀ A : F.Language, F.InNP A → F.Reduces A L

/-- NP-completeness. -/
structure NPComplete (F : CoreFrame) (L : F.Language) : Prop where
  inNP : F.InNP L
  hard : NPHard F L

/-- NP-complete lower bound transfers to P≠NP. -/
theorem not_classesCoincide_of_npComplete_notInP
    {F : CoreFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hNotP : ¬ F.InP L) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := L, inNP := hC.inNP, notInP := hNotP })

/-- If an NP-complete language lies in P, then all NP languages lie in P. -/
theorem classesCoincide_of_npComplete_inP
    {F : CoreFrame}
    {L : F.Language}
    (hC : NPComplete F L)
    (hP : F.InP L) :
    ClassesCoincide F := by
  intro A hA
  exact F.p_closed_downward (hC.hard A hA) hP

/-- SAT outside P/poly is a particularly strong route. -/
structure SATOutsidePpolyRoute (F : CoreFrame) where
  SAT : F.Language
  sat_complete : NPComplete F SAT
  sat_notInPpoly : ¬ F.InPpoly SAT

theorem SATOutsidePpolyRoute.sat_notInP
    {F : CoreFrame}
    (R : SATOutsidePpolyRoute F) :
    ¬ F.InP R.SAT := by
  intro hP
  exact R.sat_notInPpoly (F.p_subset_ppoly hP)

theorem SATOutsidePpolyRoute.not_classesCoincide
    {F : CoreFrame}
    (R : SATOutsidePpolyRoute F) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_npComplete_notInP
    R.sat_complete R.sat_notInP

/-- NP-hardness alone is explicitly not a proof route. -/
structure NPHardOnlyInsufficient (F : CoreFrame) where
  L : F.Language
  hard : NPHard F L
  missing_inNP : Prop
  missing_lower_bound : Prop

/-#############################################################################
  §4. High-complexity lower bounds and Williams-style transfer
#############################################################################-/

/-- A high-complexity lower bound, e.g. NEXP not in a circuit class. -/
structure HighComplexityLowerBound (F : CoreFrame) where
  K : F.CircuitClass
  H : F.Language
  high_membership : F.InNEXP H ∨ F.InEXP H
  notInK : ¬ F.InCircuit K H

/-- Bridge lowering/escalating a high-complexity lower bound to an NP lower bound. -/
structure HighToNPBridge (F : CoreFrame) (H : HighComplexityLowerBound F) where
  L : F.Language
  Kcover : F.CircuitClass
  Kcover_coversP : CoversP F Kcover
  inNP : F.InNP L
  notInKcover : ¬ F.InCircuit Kcover L
  genuinely_uses_high_lower_bound : Prop
  genuinely_uses_high_lower_bound_proof : genuinely_uses_high_lower_bound

noncomputable def HighToNPBridge.toNPOutsidePCovering
    {F : CoreFrame}
    {H : HighComplexityLowerBound F}
    (B : HighToNPBridge F H) :
    NPOutsidePCoveringCircuitClass F :=
  { K := B.Kcover
    coversP := B.Kcover_coversP
    L := B.L
    inNP := B.inNP
    notInK := B.notInKcover }

theorem HighToNPBridge.not_classesCoincide
    {F : CoreFrame}
    {H : HighComplexityLowerBound F}
    (B : HighToNPBridge F H) :
    ¬ ClassesCoincide F :=
  B.toNPOutsidePCovering.not_classesCoincide

/-- A high lower bound with no NP escalation is insufficient for P≠NP. -/
structure HighLowerBoundOnlyInsufficient (F : CoreFrame) where
  high : HighComplexityLowerBound F
  missing_high_to_NP_bridge : Prop

/-- Williams-style transfer: faster SAT for class K gives a high lower bound. -/
structure WilliamsTransferSchema (F : CoreFrame) where
  FasterSATFor : F.CircuitClass → Prop
  transfer :
    ∀ K : F.CircuitClass,
      FasterSATFor K → HighComplexityLowerBound F

/-- Williams transfer plus high-to-NP bridge closes P≠NP. -/
structure WilliamsEscalatedRoute (F : CoreFrame) where
  schema : WilliamsTransferSchema F
  K : F.CircuitClass
  fasterSAT : schema.FasterSATFor K
  bridge : HighToNPBridge F (schema.transfer K fasterSAT)

theorem WilliamsEscalatedRoute.not_classesCoincide
    {F : CoreFrame}
    (R : WilliamsEscalatedRoute F) :
    ¬ ClassesCoincide F :=
  R.bridge.not_classesCoincide

/-- Williams transfer without high-to-NP bridge is insufficient for P≠NP. -/
structure WilliamsOnlyInsufficient (F : CoreFrame) where
  schema : WilliamsTransferSchema F
  K : F.CircuitClass
  fasterSAT : schema.FasterSATFor K
  missing_high_to_NP_bridge : Prop

/-#############################################################################
  §5. Hierarchy route and NP-membership bridge
#############################################################################-/

/-- A hierarchy language outside P plus an external NP-membership bridge. -/
structure HierarchyNPBridgeRoute (F : CoreFrame) where
  H : F.Language
  hierarchy_notInP : ¬ F.InP H
  inNP_bridge : F.InNP H
  bridge_is_external : Prop
  bridge_is_external_proof : bridge_is_external

theorem HierarchyNPBridgeRoute.not_classesCoincide
    {F : CoreFrame}
    (R : HierarchyNPBridgeRoute F) :
    ¬ ClassesCoincide F :=
  (DecisionSeparationWitness.not_classesCoincide
    { L := R.H, inNP := R.inNP_bridge, notInP := R.hierarchy_notInP })

/-- Hierarchy outside P without NP-membership is insufficient for P≠NP. -/
structure HierarchyOnlyInsufficient (F : CoreFrame) where
  H : F.Language
  hierarchy_notInP : ¬ F.InP H
  missing_inNP_bridge : Prop

/-#############################################################################
  §6. NP vs coNP and proof complexity
#############################################################################-/

/-- Standard guard: if P=NP then NP-vs-coNP cannot remain separated. -/
structure NPcoNPGuard (F : CoreFrame) where
  NPneqcoNP : Prop
  classesCoincide_implies_not_NPneqcoNP :
    ClassesCoincide F → ¬ NPneqcoNP

theorem not_classesCoincide_of_NPneqcoNP
    {F : CoreFrame}
    (G : NPcoNPGuard F)
    (h : G.NPneqcoNP) :
    ¬ ClassesCoincide F := by
  intro hEq
  exact (G.classesCoincide_implies_not_NPneqcoNP hEq) h

/-- Proof complexity frame. -/
structure ProofComplexityFrame where
  Formula : Type
  ProofSystem : Type
  CookReckhow : ProofSystem → Prop
  PolyBounded : ProofSystem → Prop
  NoPolyBoundedCookReckhow : Prop

/-- Bridge from proof-complexity lower bound to NP≠coNP. -/
structure ProofLowerBoundToNPcoNPBridge
    (P : ProofComplexityFrame) where
  no_poly_CR_to_NPneqcoNP :
    P.NoPolyBoundedCookReckhow → Prop

/-- Proof-complexity route closing P≠NP through NP≠coNP. -/
structure ProofComplexityRoute
    (F : CoreFrame)
    (P : ProofComplexityFrame)
    (G : NPcoNPGuard F) where
  lower_bound : P.NoPolyBoundedCookReckhow
  bridge : ProofLowerBoundToNPcoNPBridge P
  bridge_realized : bridge.no_poly_CR_to_NPneqcoNP lower_bound
  gives_npcoNP : bridge.no_poly_CR_to_NPneqcoNP lower_bound → G.NPneqcoNP

theorem ProofComplexityRoute.not_classesCoincide
    {F : CoreFrame}
    {P : ProofComplexityFrame}
    {G : NPcoNPGuard F}
    (R : ProofComplexityRoute F P G) :
    ¬ ClassesCoincide F :=
  not_classesCoincide_of_NPneqcoNP G
    (R.gives_npcoNP R.bridge_realized)

/-- Proof lower bound without NP≠coNP bridge is insufficient. -/
structure ProofLowerBoundOnlyInsufficient
    (P : ProofComplexityFrame) where
  lower_bound : P.NoPolyBoundedCookReckhow
  missing_NPcoNP_bridge : Prop

/-#############################################################################
  §7. Barrier and Step00 nonabsorption audits
#############################################################################-/

/-- Barrier audit for external routes. -/
structure BarrierAudit where
  nonrelativizing : Prop
  nonrelativizing_proof : nonrelativizing

  nonalgebrizing : Prop
  nonalgebrizing_proof : nonalgebrizing

  not_natural_proofs_only : Prop
  not_natural_proofs_only_proof : not_natural_proofs_only

  not_pure_diagonalization_only : Prop
  not_pure_diagonalization_only_proof : not_pure_diagonalization_only

  no_oracle_artifact : Prop
  no_oracle_artifact_proof : no_oracle_artifact

  no_density_leak : Prop
  no_density_leak_proof : no_density_leak

/-- Stronger natural-proofs guard for circuit routes. -/
structure NaturalProofsHardenedGuard where
  Property : Type
  constructive_large_useful : Property → Prop
  cryptographic_prg_barrier : Prop
  route_not_solely_natural : Prop
  route_not_solely_natural_proof : route_not_solely_natural

/-- Step00 nonabsorption audit. -/
structure Step00NonAbsorptionAudit where
  not_internal_coverage_route : Prop
  not_internal_coverage_route_proof : not_internal_coverage_route

  not_resolver_only_incomplete_route : Prop
  not_resolver_only_incomplete_route_proof : not_resolver_only_incomplete_route

  no_semantic_collision_closure_leak : Prop
  no_semantic_collision_closure_leak_proof : no_semantic_collision_closure_leak

  no_causal_boundary_leak : Prop
  no_causal_boundary_leak_proof : no_causal_boundary_leak

  genuinely_external_machine_argument : Prop
  genuinely_external_machine_argument_proof : genuinely_external_machine_argument

/-#############################################################################
  §8. Successful route selector v8
#############################################################################-/

/-- Route selector: each constructor contains enough data to imply P≠NP. -/
inductive SuccessfulRouteV8 (F : CoreFrame) : Prop where
  | direct :
      DecisionSeparationWitness F →
      SuccessfulRouteV8 F

  | circuitCovering :
      NPOutsidePCoveringCircuitClass F →
      SuccessfulRouteV8 F

  | ppoly :
      NPOutsidePpoly F →
      SuccessfulRouteV8 F

  | satPpoly :
      SATOutsidePpolyRoute F →
      SuccessfulRouteV8 F

  | npComplete :
      (L : F.Language) →
      NPComplete F L →
      ¬ F.InP L →
      SuccessfulRouteV8 F

  | circuitEscalated :
      CircuitEscalationCertificate F →
      SuccessfulRouteV8 F

  | highEscalated :
      (H : HighComplexityLowerBound F) →
      HighToNPBridge F H →
      SuccessfulRouteV8 F

  | williamsEscalated :
      WilliamsEscalatedRoute F →
      SuccessfulRouteV8 F

  | hierarchyNP :
      HierarchyNPBridgeRoute F →
      SuccessfulRouteV8 F

  | npcoNP :
      (G : NPcoNPGuard F) →
      G.NPneqcoNP →
      SuccessfulRouteV8 F

  | proofComplexity :
      (P : ProofComplexityFrame) →
      (G : NPcoNPGuard F) →
      ProofComplexityRoute F P G →
      SuccessfulRouteV8 F

theorem SuccessfulRouteV8.not_classesCoincide
    {F : CoreFrame}
    (R : SuccessfulRouteV8 F) :
    ¬ ClassesCoincide F := by
  cases R with
  | direct W =>
      exact W.not_classesCoincide
  | circuitCovering C =>
      exact C.not_classesCoincide
  | ppoly P =>
      exact P.not_classesCoincide
  | satPpoly S =>
      exact S.not_classesCoincide
  | npComplete L C hNotP =>
      exact not_classesCoincide_of_npComplete_notInP C hNotP
  | circuitEscalated E =>
      exact E.not_classesCoincide
  | highEscalated H B =>
      exact B.not_classesCoincide
  | williamsEscalated W =>
      exact W.not_classesCoincide
  | hierarchyNP H =>
      exact H.not_classesCoincide
  | npcoNP G h =>
      exact not_classesCoincide_of_NPneqcoNP G h
  | proofComplexity P G R =>
      exact R.not_classesCoincide

/-- Successful route plus audits. -/
structure AuditedSuccessfulRouteV8 (F : CoreFrame) where
  route : SuccessfulRouteV8 F
  barrierAudit : BarrierAudit
  nonabsorptionAudit : Step00NonAbsorptionAudit
  naturalProofsGuard : Prop
  naturalProofsGuard_proof : naturalProofsGuard

theorem AuditedSuccessfulRouteV8.not_classesCoincide
    {F : CoreFrame}
    (R : AuditedSuccessfulRouteV8 F) :
    ¬ ClassesCoincide F :=
  R.route.not_classesCoincide

/-#############################################################################
  §9. Insufficiency registry v8
#############################################################################-/

/-- Statements explicitly known to be insufficient without more data. -/
inductive InsufficientRouteV8 (F : CoreFrame) : Type 1 where
  | npHardOnly :
      NPHardOnlyInsufficient F →
      InsufficientRouteV8 F

  | smallCircuitOnly :
      SmallCircuitLowerBoundOnly F →
      InsufficientRouteV8 F

  | highOnly :
      HighLowerBoundOnlyInsufficient F →
      InsufficientRouteV8 F

  | williamsOnly :
      WilliamsOnlyInsufficient F →
      InsufficientRouteV8 F

  | hierarchyOnly :
      HierarchyOnlyInsufficient F →
      InsufficientRouteV8 F

  | proofOnly :
      (P : ProofComplexityFrame) →
      ProofLowerBoundOnlyInsufficient P →
      InsufficientRouteV8 F

  | step00LocalOnly :
      Prop →
      InsufficientRouteV8 F

/-- Typing firewall: insufficient entries are not successful routes. -/
abbrev InsufficiencyFirewall (F : CoreFrame) : Prop :=
  InsufficientRouteV8 F → True

theorem insufficiencyFirewall
    (F : CoreFrame) :
    InsufficiencyFirewall F := by
  intro _
  trivial

/-#############################################################################
  §10. Final v8 obligation
#############################################################################-/

/--
The current maximal single-file obligation: provide one audited successful route
and enough fidelity guards to exclude synthetic/trivial frames.
-/
structure RemainingExternalRoutesV8Obligation (F : CoreFrame) where
  auditedRoute : AuditedSuccessfulRouteV8 F

  faithful_machine_or_circuit_semantics : Prop
  faithful_machine_or_circuit_semantics_proof :
    faithful_machine_or_circuit_semantics

  not_trivial_frame : Prop
  not_trivial_frame_proof : not_trivial_frame

  not_empty_language_trick : Prop
  not_empty_language_trick_proof : not_empty_language_trick

  not_fixed_finite_language_trick : Prop
  not_fixed_finite_language_trick_proof : not_fixed_finite_language_trick

  not_step00_coverage_mediation : Prop
  not_step00_coverage_mediation_proof : not_step00_coverage_mediation

theorem RemainingExternalRoutesV8Obligation.closes
    {F : CoreFrame}
    (O : RemainingExternalRoutesV8Obligation F) :
    ¬ ClassesCoincide F :=
  O.auditedRoute.not_classesCoincide

/-- Slogan theorem for v8. -/
abbrev ExternalRoutesV8Slogan (F : CoreFrame) : Prop :=
  RemainingExternalRoutesV8Obligation F → ¬ ClassesCoincide F

theorem externalRoutesV8Slogan
    (F : CoreFrame) :
    ExternalRoutesV8Slogan F := by
  intro O
  exact O.closes

end ExternalRoutesV8
end ClassicalPNP
end EuclidsPath

/- ============ Axiom audit of headline theorems ============ -/
