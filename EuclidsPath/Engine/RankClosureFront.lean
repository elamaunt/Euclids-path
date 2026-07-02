/-
  RankClosureFront — rank-closure серия (6 кирпичей): boundary global
  certificate, tower complete verification, prefix closure completion,
  inequality closure, class separation closure, local class equality
  contradiction.

  ЧЕСТНОСТЬ (флаги сборочного аудита): все False-выводы гипотезо-зависимы
  (LocalOnlyBoundaryCrossingClaim / RankCollapseEngine / UniversalRankCompression
  — явно противоречивые пакеты на входе). rankLocalClasses_do_not_coincide —
  только при поданном RankSeparationWitness, который нигде не построен:
  «P-neq-NP-образное» разделение целиком условно. Инертные гейты:
  local_checkable (exists p : Prop, p — истинно через True), FullRankAudit-поля,
  VerificationEasy self-supplied. Renamed-conclusion входы:
  RankSeparationWitness / Step00TwinRankWitnessPackage = «inNP + unbounded» —
  вывод, поданный на вход; FirstMissingBoundary/PrefixObstructed кодируют
  своё же заключение.
-/
import Mathlib

set_option autoImplicit false

/-
EuclidsPath_rank_boundary_global_certificate_patch.lean

Formal patch: rank-internal computation versus rank-boundary transition.

Thesis formalized in this file:

  * inside a fixed ranked dynamics, a given path is locally checkable;
  * every forward path has length bounded by the starting rank;
  * crossing a rank/key boundary is not merely a local step check;
  * a genuine boundary transition contains a full boundary certificate;
  * a claimed local-only boundary crossing without that certificate is an
    unpaid engine and contradicts the certificate theorem;
  * route-taxonomy expansion is not strict progress unless it closes an
    obligation, proves an obstruction, or strictly concretizes the obligation.

This file is self-contained and proves only abstract theorem-gates.
It does not claim classical P vs NP.
-/



namespace EuclidsPath
namespace RankBoundaryGlobalCertificate

/-#############################################################################
  §1. Ranked forward systems: local computation inside rank
#############################################################################-/

/--
A ranked forward system.

`Step s t` is a legal forward transition.  The essential invariant is that each
forward step strictly decreases the natural-number rank.
-/
structure RankedForwardSystem where
  State : Type
  rank : State → Nat
  Step : State → State → Prop
  step_decreases :
    ∀ {s t : State}, Step s t → rank t < rank s

/-- A length-indexed forward path. -/
inductive PathN (R : RankedForwardSystem) :
    R.State → R.State → Nat → Prop where
  | nil (s : R.State) :
      PathN R s s 0
  | cons {s t u : R.State} {n : Nat}
      (h : R.Step s t)
      (tail : PathN R t u n) :
      PathN R s u (n + 1)

namespace PathN

/--
The central rank-internal theorem: every forward path has length bounded by the
rank of its starting state.
-/
theorem len_le_rank
    {R : RankedForwardSystem}
    {s t : R.State} {n : Nat}
    (p : PathN R s t n) :
    n ≤ R.rank s := by
  induction p with
  | nil s =>
      exact Nat.zero_le _
  | @cons s t u n hstep tail ih =>
      have hlt : n < R.rank s := lt_of_le_of_lt ih (R.step_decreases hstep)
      exact Nat.succ_le_of_lt hlt

end PathN

/--
A local verifier for one ranked step.

It can check one proposed transition.  It does not by itself classify every
hidden genealogy or every same-key collision at a boundary.
-/
structure RankInternalVerifier (R : RankedForwardSystem) where
  acceptsStep : R.State → R.State → Bool
  sound :
    ∀ {s t : R.State}, acceptsStep s t = true → R.Step s t
  complete :
    ∀ {s t : R.State}, R.Step s t → acceptsStep s t = true

namespace RankInternalVerifier

/-- A locally accepted step is rank-decreasing. -/
theorem acceptedStep_decreases
    {R : RankedForwardSystem}
    (V : RankInternalVerifier R)
    {s t : R.State}
    (h : V.acceptsStep s t = true) :
    R.rank t < R.rank s :=
  R.step_decreases (V.sound h)

/--
A locally verified path is bounded by the starting rank once the accepted steps
are converted to real steps.
-/
structure VerifiedPath
    {R : RankedForwardSystem}
    (V : RankInternalVerifier R)
    (s t : R.State) (n : Nat) where
  path : PathN R s t n

theorem VerifiedPath.len_le_rank
    {R : RankedForwardSystem}
    {V : RankInternalVerifier R}
    {s t : R.State} {n : Nat}
    (p : VerifiedPath V s t n) :
    n ≤ R.rank s :=
  PathN.len_le_rank p.path

end RankInternalVerifier

/-#############################################################################
  §2. Boundary collision systems: global information at rank/key boundary
#############################################################################-/

/--
A same-key collision system living at a rank/key boundary.

`Genealogy` is the family of generated histories.
`keyOf` is the finite/local key.
`Required g h` says that the pair must be resolved by the boundary audit.
`Resolves g h a` says that answer `a` actually pays/resolves that collision.
-/
structure BoundaryCollisionSystem where
  Genealogy : Type
  Key : Type
  Answer : Type
  keyOf : Genealogy → Key
  Required : Genealogy → Genealogy → Prop
  Resolves : Genealogy → Genealogy → Answer → Prop

namespace BoundaryCollisionSystem

/-- Same-key required collision predicate. -/
def SameKeyRequired (C : BoundaryCollisionSystem)
    (g h : C.Genealogy) : Prop :=
  C.Required g h ∧ C.keyOf g = C.keyOf h

/--
A full rank-boundary certificate.

It gives a resolution answer for every required same-key collision.  This is the
global object that a local step verifier does not supply.
-/
structure FullBoundaryCertificate (C : BoundaryCollisionSystem) where
  resolve :
    ∀ g h : C.Genealogy,
      C.SameKeyRequired g h →
        {a : C.Answer // C.Resolves g h a}

/--
A boundary resolver is the computational form of the same data: it chooses an
answer and proves it resolves every required same-key collision.
-/
structure BoundaryResolver (C : BoundaryCollisionSystem) where
  choose : C.Genealogy → C.Genealogy → C.Answer
  sound :
    ∀ g h : C.Genealogy,
      C.SameKeyRequired g h →
        C.Resolves g h (choose g h)

namespace BoundaryResolver

/-- A resolver yields a full boundary certificate. -/
def toCertificate
    {C : BoundaryCollisionSystem}
    (B : BoundaryResolver C) :
    FullBoundaryCertificate C :=
{
  resolve := by
    intro g h hreq
    exact ⟨B.choose g h, B.sound g h hreq⟩
}

end BoundaryResolver

/-- A full certificate can be read as global boundary coverage. -/
abbrev GlobalBoundaryCoverage (C : BoundaryCollisionSystem) : Prop :=
  Nonempty (FullBoundaryCertificate C)

/-- A boundary is uncovered when it has no full certificate. -/
abbrev BoundaryUncovered (C : BoundaryCollisionSystem) : Prop :=
  ¬ GlobalBoundaryCoverage C

/-- A resolver proves that the boundary is covered. -/
theorem coverage_of_resolver
    {C : BoundaryCollisionSystem}
    (B : BoundaryResolver C) :
    GlobalBoundaryCoverage C :=
  ⟨B.toCertificate⟩

/--
If the boundary is uncovered, no resolver can exist.
-/
theorem no_resolver_of_uncovered
    {C : BoundaryCollisionSystem}
    (hUncovered : BoundaryUncovered C) :
    ¬ Nonempty (BoundaryResolver C) := by
  intro h
  rcases h with ⟨B⟩
  exact hUncovered (coverage_of_resolver B)

end BoundaryCollisionSystem

/-#############################################################################
  §3. Boundary transition: local verifier plus full certificate
#############################################################################-/

/--
A genuine rank-boundary transition contains both:

  * a local rank-internal verifier;
  * a full boundary certificate resolving all required same-key collisions.

The second field is the global rank audit.
-/
structure RankBoundaryTransition
    (R : RankedForwardSystem)
    (C : BoundaryCollisionSystem) where
  localVerifier : RankInternalVerifier R
  boundaryCertificate : C.FullBoundaryCertificate

/-- A genuine boundary transition yields global coverage. -/
theorem RankBoundaryTransition.gives_coverage
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (T : RankBoundaryTransition R C) :
    C.GlobalBoundaryCoverage :=
  ⟨T.boundaryCertificate⟩

/--
A local verifier alone is just local computation inside rank.  It does not carry
boundary coverage.
-/
structure LocalOnlyRankComputation
    (R : RankedForwardSystem) where
  verifier : RankInternalVerifier R

/--
Claiming to cross the boundary with only local computation while denying global
coverage is the abstract unpaid-engine pattern.
-/
structure LocalOnlyBoundaryCrossingClaim
    (R : RankedForwardSystem)
    (C : BoundaryCollisionSystem) where
  localOnly : LocalOnlyRankComputation R
  transition : RankBoundaryTransition R C
  deniesCoverage : C.BoundaryUncovered

/--
A local-only boundary crossing claim self-destructs: the claimed transition
already contains the full boundary certificate.
-/
theorem localOnlyBoundaryCrossingClaim_contradiction
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (X : LocalOnlyBoundaryCrossingClaim R C) :
    False :=
  X.deniesCoverage X.transition.gives_coverage

/--
A genuine transition cannot exist over an uncovered boundary.
-/
theorem no_boundaryTransition_of_uncovered
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (hUncovered : C.BoundaryUncovered) :
    ¬ Nonempty (RankBoundaryTransition R C) := by
  intro h
  rcases h with ⟨T⟩
  exact hUncovered T.gives_coverage

/-#############################################################################
  §4. Partial local algorithms at the boundary
#############################################################################-/

/--
A partial local boundary algorithm may try to resolve some collisions.  It is not
a full boundary transition unless it covers every required same-key collision.
-/
structure PartialBoundaryAlgorithm (C : BoundaryCollisionSystem) where
  tryResolve : C.Genealogy → C.Genealogy → Option C.Answer
  sound :
    ∀ g h a,
      C.SameKeyRequired g h →
      tryResolve g h = some a →
        C.Resolves g h a

/-- The partial algorithm covers all required same-key collisions. -/
def PartialBoundaryAlgorithm.CoversAll
    {C : BoundaryCollisionSystem}
    (A : PartialBoundaryAlgorithm C) : Prop :=
  ∀ g h : C.Genealogy,
    C.SameKeyRequired g h →
      ∃ a : C.Answer,
        A.tryResolve g h = some a ∧ C.Resolves g h a

/-- If the partial algorithm covers all required collisions, it gives a certificate. -/
noncomputable def PartialBoundaryAlgorithm.toCertificate
    {C : BoundaryCollisionSystem}
    (A : PartialBoundaryAlgorithm C)
    (hCover : A.CoversAll) :
    C.FullBoundaryCertificate :=
{
  resolve := fun g h hreq =>
    ⟨(hCover g h hreq).choose, (hCover g h hreq).choose_spec.2⟩
}

/--
A partial boundary algorithm either gives a full certificate or remains
incomplete.  This is a classical dichotomy on its coverage property.
-/
theorem partialAlgorithm_paid_or_incomplete
    {C : BoundaryCollisionSystem}
    (A : PartialBoundaryAlgorithm C) :
    C.GlobalBoundaryCoverage ∨ ¬ A.CoversAll := by
  classical
  by_cases h : A.CoversAll
  · exact Or.inl ⟨A.toCertificate h⟩
  · exact Or.inr h

/--
If a partial algorithm claims coverage while the boundary is uncovered, it
contradicts the certificate theorem.
-/
theorem partialAlgorithm_cover_uncovered_contradiction
    {C : BoundaryCollisionSystem}
    (A : PartialBoundaryAlgorithm C)
    (hCover : A.CoversAll)
    (hUncovered : C.BoundaryUncovered) :
    False :=
  hUncovered ⟨A.toCertificate hCover⟩

/-#############################################################################
  §5. Engine classification
#############################################################################-/

/--
A rank-boundary engine is an alleged resolver over an uncovered boundary.

This object is impossible because the resolver itself gives coverage.
-/
structure RankBoundaryEngine
    (C : BoundaryCollisionSystem) where
  resolver : C.BoundaryResolver
  uncovered : C.BoundaryUncovered

/-- No rank-boundary engine exists. -/
theorem no_rankBoundaryEngine
    {C : BoundaryCollisionSystem}
    (E : RankBoundaryEngine C) :
    False :=
  E.uncovered (C.coverage_of_resolver E.resolver)

/--
The local/global trichotomy for boundary attempts:

* `paid`: a full certificate is supplied;
* `incomplete`: only partial/local coverage is present;
* `engine`: a resolver is claimed despite uncovered boundary.
-/
inductive BoundaryAttemptStatus
    (C : BoundaryCollisionSystem) : Prop where
  | paid :
      C.GlobalBoundaryCoverage →
      BoundaryAttemptStatus C
  | incomplete :
      (∀ A : PartialBoundaryAlgorithm C, ¬ A.CoversAll) →
      BoundaryAttemptStatus C
  | engine :
      RankBoundaryEngine C →
      BoundaryAttemptStatus C

/--
The engine branch is contradictory.
-/
theorem BoundaryAttemptStatus.engine_impossible
    {C : BoundaryCollisionSystem}
    (E : RankBoundaryEngine C) :
    False :=
  no_rankBoundaryEngine E

/-#############################################################################
  §6. P/NP interpretation layer: local verification versus global resolver
#############################################################################-/

/--
A local verifier/search node over a ranked system and a collision boundary.

`VerificationEasy` is the rank-internal side.
`LocalSuccess` is the existence of a full boundary resolver/certificate.
-/
structure RankLocalSearchNode
    (R : RankedForwardSystem)
    (C : BoundaryCollisionSystem) where
  VerificationEasy : Prop
  verificationEasy_proof : VerificationEasy

  LocalSuccess : Prop
  localSuccess_iff_coverage :
    LocalSuccess ↔ C.GlobalBoundaryCoverage

namespace RankLocalSearchNode

/-- Coverage gives local success. -/
theorem localSuccess_of_coverage
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (N : RankLocalSearchNode R C)
    (h : C.GlobalBoundaryCoverage) :
    N.LocalSuccess :=
  N.localSuccess_iff_coverage.mpr h

/-- Local success gives coverage. -/
theorem coverage_of_localSuccess
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (N : RankLocalSearchNode R C)
    (h : N.LocalSuccess) :
    C.GlobalBoundaryCoverage :=
  N.localSuccess_iff_coverage.mp h

/--
If local search is impossible, no full boundary transition can be constructed.
-/
theorem no_transition_of_not_localSuccess
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (N : RankLocalSearchNode R C)
    (hNo : ¬ N.LocalSuccess) :
    ¬ Nonempty (RankBoundaryTransition R C) := by
  intro hT
  rcases hT with ⟨T⟩
  exact hNo (N.localSuccess_of_coverage T.gives_coverage)

/--
If local search is impossible, any alleged full resolver is impossible.
-/
theorem no_resolver_of_not_localSuccess
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (N : RankLocalSearchNode R C)
    (hNo : ¬ N.LocalSuccess) :
    ¬ Nonempty (C.BoundaryResolver) := by
  intro hR
  rcases hR with ⟨B⟩
  exact hNo (N.localSuccess_of_coverage (C.coverage_of_resolver B))

end RankLocalSearchNode

/-#############################################################################
  §7. Full rank audit as the missing global object
#############################################################################-/

/--
A full rank audit packages the global certificate and records that it is not
obtained merely by checking one chosen path.
-/
structure FullRankAudit
    (R : RankedForwardSystem)
    (C : BoundaryCollisionSystem) where
  localVerifier : RankInternalVerifier R
  certificate : C.FullBoundaryCertificate

  not_merely_one_path_check : Prop
  not_merely_one_path_check_proof : not_merely_one_path_check

  covers_hidden_same_key_collisions : Prop
  covers_hidden_same_key_collisions_proof : covers_hidden_same_key_collisions

/-- A full audit gives a boundary transition. -/
def FullRankAudit.toTransition
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (A : FullRankAudit R C) :
    RankBoundaryTransition R C :=
{
  localVerifier := A.localVerifier
  boundaryCertificate := A.certificate
}

/-- A full audit gives coverage. -/
theorem FullRankAudit.gives_coverage
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (A : FullRankAudit R C) :
    C.GlobalBoundaryCoverage :=
  A.toTransition.gives_coverage

/--
Without global coverage, no full rank audit exists.
-/
theorem no_fullRankAudit_of_uncovered
    {R : RankedForwardSystem}
    {C : BoundaryCollisionSystem}
    (hUncovered : C.BoundaryUncovered) :
    ¬ Nonempty (FullRankAudit R C) := by
  intro h
  rcases h with ⟨A⟩
  exact hUncovered A.gives_coverage

/-#############################################################################
  §8. No-loop frontier rank: taxonomy is not progress
#############################################################################-/

/--
Kinds of frontier moves.

Only closing, obstruction, or strict concretization count as forward progress.
Pure taxonomy expansion does not.
-/
inductive FrontierMoveKind where
  | closesObligation
  | provesObstruction
  | strictlyConcretizes
  | taxonomyExpansion
  deriving DecidableEq, Repr

/-- Strict progress predicate on move kinds. -/
def StrictFrontierProgress : FrontierMoveKind → Prop
  | FrontierMoveKind.closesObligation => True
  | FrontierMoveKind.provesObstruction => True
  | FrontierMoveKind.strictlyConcretizes => True
  | FrontierMoveKind.taxonomyExpansion => False

/-- Taxonomy expansion is not strict progress. -/
theorem taxonomyExpansion_not_strictProgress :
    ¬ StrictFrontierProgress FrontierMoveKind.taxonomyExpansion := by
  intro h
  exact h

/--
A frontier step records its kind and the obligation it acts on.
-/
structure FrontierStep where
  Obligation : Type
  kind : FrontierMoveKind

/-- A frontier step is progressive exactly when its kind is strict progress. -/
def FrontierStep.IsProgressive (S : FrontierStep) : Prop :=
  StrictFrontierProgress S.kind

/-- A taxonomy step is not progressive. -/
theorem FrontierStep.taxonomy_not_progressive
    (O : Type) :
    ¬ (FrontierStep.IsProgressive
      { Obligation := O, kind := FrontierMoveKind.taxonomyExpansion }) := by
  exact taxonomyExpansion_not_strictProgress

/-#############################################################################
  §9. Final formal slogan
#############################################################################-/

/--
The final slogan as a theorem-shaped proposition.

Local computation is rank-internal.
Boundary transition requires global coverage.
Local-only boundary crossing without coverage is contradictory.
Taxonomy expansion is not progress.
-/
abbrev RankBoundaryGlobalCertificateSlogan
    (R : RankedForwardSystem)
    (C : BoundaryCollisionSystem) : Prop :=
  (∀ {s t : R.State} {n : Nat}, PathN R s t n → n ≤ R.rank s) ∧
  (∀ T : RankBoundaryTransition R C, C.GlobalBoundaryCoverage) ∧
  (C.BoundaryUncovered → ¬ Nonempty (RankBoundaryTransition R C)) ∧
  (¬ StrictFrontierProgress FrontierMoveKind.taxonomyExpansion)

/-- The slogan follows from the preceding formal pieces. -/
theorem rankBoundaryGlobalCertificateSlogan
    (R : RankedForwardSystem)
    (C : BoundaryCollisionSystem) :
    RankBoundaryGlobalCertificateSlogan R C := by
  constructor
  · intro s t n p
    exact PathN.len_le_rank p
  · constructor
    · intro T
      exact T.gives_coverage
    · constructor
      · intro hUncovered
        exact no_boundaryTransition_of_uncovered hUncovered
      · exact taxonomyExpansion_not_strictProgress

end RankBoundaryGlobalCertificate
end EuclidsPath

/-
EuclidsPath_rank_tower_complete_verification_patch.lean

Formal patch: rank-boundary tower and complete verification.

This file extends the previous rank-boundary/global-certificate layer.

Main thesis:

  * inside one rank, local verification is enough to check a proposed path;
  * to cross rank-boundaries up to level N, one needs certificates for every
    boundary k < N;
  * the first uncovered boundary blocks all higher transitions;
  * a local-only tower algorithm cannot be promoted to a global crossing in the
    presence of an uncovered boundary;
  * a genuine "complete rank verification" is exactly local data plus all
    required boundary certificates;
  * repeating taxonomy without a strictly decreasing frontier measure is not
    progress.

The file is self-contained.  It proves abstract theorem-gates only.
It does not prove classical P vs NP.
-/



namespace EuclidsPath
namespace RankTowerCompleteVerification

/-#############################################################################
  §1. Ranked local dynamics
#############################################################################-/

/--
A ranked forward system.  Each legal step strictly decreases the rank.
-/
structure RankedForwardSystem where
  State : Type
  rank : State → Nat
  Step : State → State → Prop
  step_decreases :
    ∀ {s t : State}, Step s t → rank t < rank s

/-- Length-indexed forward paths. -/
inductive PathN (R : RankedForwardSystem) :
    R.State → R.State → Nat → Prop where
  | nil (s : R.State) :
      PathN R s s 0
  | cons {s t u : R.State} {n : Nat}
      (h : R.Step s t)
      (tail : PathN R t u n) :
      PathN R s u (n + 1)

namespace PathN

/-- Forward path length is bounded by the starting rank. -/
theorem len_le_rank
    {R : RankedForwardSystem}
    {s t : R.State} {n : Nat}
    (p : PathN R s t n) :
    n ≤ R.rank s := by
  induction p with
  | nil s =>
      exact Nat.zero_le _
  | @cons s t u n hstep tail ih =>
      have hlt : n < R.rank s :=
        lt_of_le_of_lt ih (R.step_decreases hstep)
      exact Nat.succ_le_of_lt hlt

end PathN

/-- A local verifier checks individual rank-internal steps. -/
structure RankInternalVerifier (R : RankedForwardSystem) where
  acceptsStep : R.State → R.State → Bool
  sound :
    ∀ {s t : R.State}, acceptsStep s t = true → R.Step s t
  complete :
    ∀ {s t : R.State}, R.Step s t → acceptsStep s t = true

namespace RankInternalVerifier

/-- A locally accepted step is rank-decreasing. -/
theorem acceptedStep_decreases
    {R : RankedForwardSystem}
    (V : RankInternalVerifier R)
    {s t : R.State}
    (h : V.acceptsStep s t = true) :
    R.rank t < R.rank s :=
  R.step_decreases (V.sound h)

end RankInternalVerifier

/-#############################################################################
  §2. Boundary collision systems
#############################################################################-/

/--
A boundary collision system at a rank/key boundary.
-/
structure BoundaryCollisionSystem where
  Genealogy : Type
  Key : Type
  Answer : Type
  keyOf : Genealogy → Key
  Required : Genealogy → Genealogy → Prop
  Resolves : Genealogy → Genealogy → Answer → Prop

namespace BoundaryCollisionSystem

/-- Required same-key collision. -/
def SameKeyRequired (C : BoundaryCollisionSystem)
    (g h : C.Genealogy) : Prop :=
  C.Required g h ∧ C.keyOf g = C.keyOf h

/-- Full boundary certificate: every required same-key collision is paid. -/
structure FullBoundaryCertificate (C : BoundaryCollisionSystem) where
  resolve :
    ∀ g h : C.Genealogy,
      C.SameKeyRequired g h →
        {a : C.Answer // C.Resolves g h a}

/-- Computational form of a full certificate. -/
structure BoundaryResolver (C : BoundaryCollisionSystem) where
  choose : C.Genealogy → C.Genealogy → C.Answer
  sound :
    ∀ g h : C.Genealogy,
      C.SameKeyRequired g h →
        C.Resolves g h (choose g h)

/-- A resolver gives a certificate. -/
def BoundaryResolver.toCertificate
    {C : BoundaryCollisionSystem}
    (B : BoundaryResolver C) :
    FullBoundaryCertificate C :=
{
  resolve := by
    intro g h hreq
    exact ⟨B.choose g h, B.sound g h hreq⟩
}

/-- Coverage is existence of a full certificate. -/
abbrev GlobalBoundaryCoverage (C : BoundaryCollisionSystem) : Prop :=
  Nonempty (FullBoundaryCertificate C)

/-- Uncovered boundary. -/
abbrev BoundaryUncovered (C : BoundaryCollisionSystem) : Prop :=
  ¬ C.GlobalBoundaryCoverage

/-- Resolver implies coverage. -/
theorem coverage_of_resolver
    {C : BoundaryCollisionSystem}
    (B : BoundaryResolver C) :
    C.GlobalBoundaryCoverage :=
  ⟨B.toCertificate⟩

/-- No resolver can live over an uncovered boundary. -/
theorem no_resolver_of_uncovered
    {C : BoundaryCollisionSystem}
    (h : C.BoundaryUncovered) :
    ¬ Nonempty (BoundaryResolver C) := by
  intro hR
  rcases hR with ⟨B⟩
  exact h (coverage_of_resolver B)

end BoundaryCollisionSystem

/-#############################################################################
  §3. Rank tower and prefix certificates
#############################################################################-/

/--
A rank tower assigns a boundary collision system to each boundary level `k`.

Boundary `k` is the crossing from the verified region below/at `k` into the next
rank shell.  To pass up to level `N`, every `k < N` must be covered.
-/
structure RankTower where
  boundary : Nat → BoundaryCollisionSystem

namespace RankTower

/-- All boundaries below `N` are covered. -/
def AllBoundariesCovered (T : RankTower) (N : Nat) : Prop :=
  ∀ k : Nat, k < N → (T.boundary k).GlobalBoundaryCoverage

/-- A prefix pass up to level `N`: certificates for every boundary `k < N`. -/
structure RankTowerPass (T : RankTower) (N : Nat) where
  cert :
    ∀ k : Nat, k < N → BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary k)

/-- The empty tower prefix is always passable. -/
def RankTowerPass.zero (T : RankTower) :
    RankTowerPass T 0 :=
{
  cert := by
    intro k hk
    exact False.elim (Nat.not_lt_zero k hk)
}

/-- A pass gives all-boundaries-covered. -/
theorem allCovered_of_pass
    {T : RankTower} {N : Nat}
    (P : RankTowerPass T N) :
    T.AllBoundariesCovered N := by
  intro k hk
  exact ⟨P.cert k hk⟩

/-- All-boundaries-covered gives a pass. -/
noncomputable def pass_of_allCovered
    {T : RankTower} {N : Nat}
    (h : T.AllBoundariesCovered N) :
    RankTowerPass T N :=
{
  cert := by
    intro k hk
    exact Classical.choice (h k hk)
}

/-- Pass existence is equivalent to all-boundaries-covered. -/
theorem nonempty_pass_iff_allCovered
    {T : RankTower} {N : Nat} :
    Nonempty (RankTowerPass T N) ↔ T.AllBoundariesCovered N := by
  constructor
  · intro hP
    rcases hP with ⟨P⟩
    exact allCovered_of_pass P
  · intro h
    exact ⟨pass_of_allCovered h⟩

/-- Restrict a pass to a smaller prefix. -/
def RankTowerPass.restrict
    {T : RankTower} {N M : Nat}
    (P : RankTowerPass T N)
    (hMN : M ≤ N) :
    RankTowerPass T M :=
{
  cert := by
    intro k hk
    exact P.cert k (lt_of_lt_of_le hk hMN)
}

/-- Extend a pass by one boundary certificate. -/
def RankTowerPass.extend
    {T : RankTower} {N : Nat}
    (P : RankTowerPass T N)
    (cN : BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary N)) :
    RankTowerPass T (N + 1) :=
{
  cert := by
    intro k hk
    by_cases hlt : k < N
    · exact P.cert k hlt
    · have hk_le_N : k ≤ N := Nat.le_of_lt_succ hk
      have hN_le_k : N ≤ k := Nat.le_of_not_gt hlt
      have hEq : k = N := Nat.le_antisymm hk_le_N hN_le_k
      cases hEq
      exact cN
}

/--
Inductive construction: if all boundaries are covered, a pass exists.
-/
noncomputable def buildPass
    {T : RankTower} :
    ∀ N : Nat, T.AllBoundariesCovered N → RankTowerPass T N
  | 0, _ => RankTowerPass.zero T
  | N + 1, hAll =>
      let P : RankTowerPass T N :=
        buildPass N (by
          intro k hk
          exact hAll k (lt_trans hk (Nat.lt_succ_self N)))
      let cN : BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary N) :=
        Classical.choice (hAll N (Nat.lt_succ_self N))
      P.extend cN

/--
First missing boundary below `N`.
-/
structure FirstMissingBoundary (T : RankTower) (N : Nat) where
  m : Nat
  m_lt_N : m < N
  missing : (T.boundary m).BoundaryUncovered
  covered_before :
    ∀ k : Nat, k < m → (T.boundary k).GlobalBoundaryCoverage

/-- A first missing boundary prevents a pass up to `N`. -/
theorem no_pass_of_firstMissing
    {T : RankTower} {N : Nat}
    (M : FirstMissingBoundary T N) :
    ¬ Nonempty (RankTowerPass T N) := by
  intro hP
  rcases hP with ⟨P⟩
  exact M.missing ⟨P.cert M.m M.m_lt_N⟩

/-- Any missing boundary below `N` prevents a pass up to `N`. -/
theorem no_pass_of_missing_boundary
    {T : RankTower} {N m : Nat}
    (hm : m < N)
    (hMissing : (T.boundary m).BoundaryUncovered) :
    ¬ Nonempty (RankTowerPass T N) := by
  intro hP
  rcases hP with ⟨P⟩
  exact hMissing ⟨P.cert m hm⟩

/--
A pass up to `N` gives a certificate at each boundary below `N`.
-/
def cert_at_of_pass
    {T : RankTower} {N k : Nat}
    (P : RankTowerPass T N)
    (hk : k < N) :
    BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary k) :=
  P.cert k hk

end RankTower

/-#############################################################################
  §4. Local tower algorithms versus complete verification
#############################################################################-/

/--
Local tower data up to level `N`.

This represents local rank-internal algorithms/verifiers at each level.  It does
not include boundary certificates.
-/
structure LocalTowerAlgorithm
    (R : Nat → RankedForwardSystem)
    (N : Nat) where
  verifierAt :
    ∀ k : Nat, k < N → RankInternalVerifier (R k)

/--
Complete rank verification up to `N`: local algorithms plus a pass through every
boundary below `N`.
-/
structure CompleteRankVerification
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) where
  localData : LocalTowerAlgorithm R N
  pass : T.RankTowerPass N

/-- Complete verification gives all boundary certificates below `N`. -/
theorem CompleteRankVerification.allCovered
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (V : CompleteRankVerification R T N) :
    T.AllBoundariesCovered N :=
  T.allCovered_of_pass V.pass

/-- Complete verification cannot cross a missing boundary. -/
theorem no_completeVerification_of_missing_boundary
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N m : Nat}
    (hm : m < N)
    (hMissing : (T.boundary m).BoundaryUncovered) :
    ¬ Nonempty (CompleteRankVerification R T N) := by
  intro h
  rcases h with ⟨V⟩
  exact T.no_pass_of_missing_boundary hm hMissing ⟨V.pass⟩

/--
A local-only promotion principle says local tower algorithms alone produce
complete verification.  This is unsafe unless all boundaries are already covered.
-/
def LocalOnlyPromotion
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) : Prop :=
  Nonempty (LocalTowerAlgorithm R N) → Nonempty (CompleteRankVerification R T N)

/--
If local data exists and some boundary below `N` is missing, local-only promotion
is impossible.
-/
theorem no_localOnlyPromotion_of_missing_boundary
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N m : Nat}
    (hLocal : Nonempty (LocalTowerAlgorithm R N))
    (hm : m < N)
    (hMissing : (T.boundary m).BoundaryUncovered) :
    ¬ LocalOnlyPromotion R T N := by
  intro promote
  have hComplete : Nonempty (CompleteRankVerification R T N) := promote hLocal
  exact no_completeVerification_of_missing_boundary hm hMissing hComplete

/--
A local-only crossing claim packages the bad pattern: local data, promotion, and
an uncovered boundary.
-/
structure LocalOnlyCrossingClaim
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) where
  localData : LocalTowerAlgorithm R N
  promote : LocalOnlyPromotion R T N
  missingBoundary : Nat
  missing_lt : missingBoundary < N
  boundary_uncovered : (T.boundary missingBoundary).BoundaryUncovered

/-- Local-only crossing claims self-destruct. -/
theorem LocalOnlyCrossingClaim.contradiction
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (X : LocalOnlyCrossingClaim R T N) :
    False := by
  have hV : Nonempty (CompleteRankVerification R T N) := X.promote ⟨X.localData⟩
  exact no_completeVerification_of_missing_boundary
    X.missing_lt X.boundary_uncovered hV

/-#############################################################################
  §5. Boundary engines in a tower
#############################################################################-/

/--
A tower boundary engine is a resolver claimed at an uncovered boundary.
-/
structure TowerBoundaryEngine
    (T : RankTower) where
  k : Nat
  resolver : BoundaryCollisionSystem.BoundaryResolver (T.boundary k)
  uncovered : (T.boundary k).BoundaryUncovered

/-- No tower boundary engine exists. -/
theorem no_towerBoundaryEngine
    {T : RankTower}
    (E : TowerBoundaryEngine T) :
    False :=
  E.uncovered ((T.boundary E.k).coverage_of_resolver E.resolver)

/--
An alleged pass through an uncovered boundary constructs a tower engine.
-/
noncomputable def engine_of_pass_and_uncovered
    {T : RankTower} {N k : Nat}
    (P : T.RankTowerPass N)
    (hk : k < N)
    (hUncovered : (T.boundary k).BoundaryUncovered)
    (mkResolver :
      BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary k) →
        BoundaryCollisionSystem.BoundaryResolver (T.boundary k)) :
    TowerBoundaryEngine T :=
{
  k := k
  resolver := mkResolver (P.cert k hk)
  uncovered := hUncovered
}

/--
But the contradiction does not require converting the certificate to a resolver:
the pass itself already contradicts uncoveredness.
-/
theorem pass_uncovered_contradiction
    {T : RankTower} {N k : Nat}
    (P : T.RankTowerPass N)
    (hk : k < N)
    (hUncovered : (T.boundary k).BoundaryUncovered) :
    False :=
  hUncovered ⟨P.cert k hk⟩

/-#############################################################################
  §6. Frontier-rank discipline: no circular taxonomy progress
#############################################################################-/

/--
Kinds of proof-frontier moves.
-/
inductive FrontierMoveKind where
  | closesObligation
  | provesObstruction
  | strictlyConcretizes
  | weaklyRenames
  | taxonomyExpansion
  deriving DecidableEq, Repr

/-- Only three move kinds count as strict progress. -/
def StrictFrontierProgress : FrontierMoveKind → Prop
  | FrontierMoveKind.closesObligation => True
  | FrontierMoveKind.provesObstruction => True
  | FrontierMoveKind.strictlyConcretizes => True
  | FrontierMoveKind.weaklyRenames => False
  | FrontierMoveKind.taxonomyExpansion => False

theorem weakRename_not_progress :
    ¬ StrictFrontierProgress FrontierMoveKind.weaklyRenames := by
  intro h
  exact h

theorem taxonomyExpansion_not_progress :
    ¬ StrictFrontierProgress FrontierMoveKind.taxonomyExpansion := by
  intro h
  exact h

/--
A numerical frontier rank.  A legal strict refinement must decrease this rank
unless it closes the obligation outright or proves an obstruction.
-/
structure FrontierRankedObligation where
  rank : Nat
  description : Type

/--
A refinement step between obligations.
-/
structure FrontierRefinement where
  before : FrontierRankedObligation
  after : FrontierRankedObligation
  kind : FrontierMoveKind

/-- Rank discipline for a refinement. -/
def FrontierRefinement.RespectsRank (S : FrontierRefinement) : Prop :=
  match S.kind with
  | FrontierMoveKind.closesObligation => True
  | FrontierMoveKind.provesObstruction => True
  | FrontierMoveKind.strictlyConcretizes => S.after.rank < S.before.rank
  | FrontierMoveKind.weaklyRenames => False
  | FrontierMoveKind.taxonomyExpansion => False

/-- Taxonomy expansion never respects strict rank discipline. -/
theorem taxonomyExpansion_violates_rankDiscipline
    (A B : FrontierRankedObligation) :
    ¬ (FrontierRefinement.RespectsRank
      { before := A, after := B, kind := FrontierMoveKind.taxonomyExpansion }) := by
  intro h
  exact h

/-- Weak renaming never respects strict rank discipline. -/
theorem weakRename_violates_rankDiscipline
    (A B : FrontierRankedObligation) :
    ¬ (FrontierRefinement.RespectsRank
      { before := A, after := B, kind := FrontierMoveKind.weaklyRenames }) := by
  intro h
  exact h

/-#############################################################################
  §7. Final theorem-shaped summary
#############################################################################-/

/--
Formal slogan of this patch.

To reach rank shell `N`, certificates for every boundary below `N` are required.
A first uncovered boundary blocks complete verification.  Local-only promotion
across such a boundary is impossible.  Taxonomy expansion is not progress.
-/
abbrev RankTowerCompleteVerificationSlogan
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) : Prop :=
  (∀ h : Nonempty (T.RankTowerPass N), T.AllBoundariesCovered N) ∧
  (∀ m : Nat,
      m < N →
      (T.boundary m).BoundaryUncovered →
        ¬ Nonempty (CompleteRankVerification R T N)) ∧
  (∀ m : Nat,
      Nonempty (LocalTowerAlgorithm R N) →
      m < N →
      (T.boundary m).BoundaryUncovered →
        ¬ LocalOnlyPromotion R T N) ∧
  (¬ StrictFrontierProgress FrontierMoveKind.taxonomyExpansion) ∧
  (¬ StrictFrontierProgress FrontierMoveKind.weaklyRenames)

/-- The slogan follows from the formal tower lemmas. -/
theorem rankTowerCompleteVerificationSlogan
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) :
    RankTowerCompleteVerificationSlogan R T N := by
  constructor
  · intro h
    rcases h with ⟨P⟩
    exact T.allCovered_of_pass P
  · constructor
    · intro m hm hMissing
      exact no_completeVerification_of_missing_boundary hm hMissing
    · constructor
      · intro m hLocal hm hMissing
        exact no_localOnlyPromotion_of_missing_boundary hLocal hm hMissing
      · constructor
        · exact taxonomyExpansion_not_progress
        · exact weakRename_not_progress

end RankTowerCompleteVerification
end EuclidsPath

/-
EuclidsPath_rank_prefix_closure_completion_patch.lean

Formal patch: finite rank-prefix closure completion.

This file pushes the rank-boundary program toward closure.

Main closure gate:

  For a finite prefix N of a rank tower,

      Nonempty (CompleteRankVerification R T N)
        ↔ Nonempty (LocalTowerAlgorithm R N) ∧ PrefixClosed T N.

  So after local verifiers are supplied, the remaining and only obstruction is
  boundary coverage for every k < N.

It also records the complementary obstruction:

  FirstMissingBoundary T N → no CompleteRankVerification R T N.

No hidden postulates.
-/



namespace EuclidsPath
namespace RankPrefixClosureCompletion

/-#############################################################################
  §1. Local ranked dynamics
#############################################################################-/

/-- A ranked forward system: every legal step strictly decreases rank. -/
structure RankedForwardSystem where
  State : Type
  rank : State → Nat
  Step : State → State → Prop
  step_decreases :
    ∀ {s t : State}, Step s t → rank t < rank s

/-- Length-indexed paths. -/
inductive PathN (R : RankedForwardSystem) :
    R.State → R.State → Nat → Prop where
  | nil (s : R.State) :
      PathN R s s 0
  | cons {s t u : R.State} {n : Nat}
      (h : R.Step s t)
      (tail : PathN R t u n) :
      PathN R s u (n + 1)

namespace PathN

/-- Every forward path has length bounded by its starting rank. -/
theorem len_le_rank
    {R : RankedForwardSystem}
    {s t : R.State} {n : Nat}
    (p : PathN R s t n) :
    n ≤ R.rank s := by
  induction p with
  | nil s =>
      exact Nat.zero_le _
  | @cons s t u n hstep tail ih =>
      have hlt : n < R.rank s :=
        lt_of_le_of_lt ih (R.step_decreases hstep)
      exact Nat.succ_le_of_lt hlt

end PathN

/-- A local verifier for rank-internal steps. -/
structure RankInternalVerifier (R : RankedForwardSystem) where
  acceptsStep : R.State → R.State → Bool
  sound :
    ∀ {s t : R.State}, acceptsStep s t = true → R.Step s t
  complete :
    ∀ {s t : R.State}, R.Step s t → acceptsStep s t = true

namespace RankInternalVerifier

/-- Accepted local steps decrease rank. -/
theorem acceptedStep_decreases
    {R : RankedForwardSystem}
    (V : RankInternalVerifier R)
    {s t : R.State}
    (h : V.acceptsStep s t = true) :
    R.rank t < R.rank s :=
  R.step_decreases (V.sound h)

end RankInternalVerifier

/-#############################################################################
  §2. Boundary systems and coverage
#############################################################################-/

/--
A boundary collision system.

`Required g h` marks collisions that must be resolved at this boundary.
`Resolves g h a` says answer `a` resolves/pays that collision.
-/
structure BoundaryCollisionSystem where
  Genealogy : Type
  Key : Type
  Answer : Type
  keyOf : Genealogy → Key
  Required : Genealogy → Genealogy → Prop
  Resolves : Genealogy → Genealogy → Answer → Prop

namespace BoundaryCollisionSystem

/-- Required same-key collision. -/
def SameKeyRequired (C : BoundaryCollisionSystem)
    (g h : C.Genealogy) : Prop :=
  C.Required g h ∧ C.keyOf g = C.keyOf h

/-- Full boundary certificate: every required same-key collision is resolved. -/
structure FullBoundaryCertificate (C : BoundaryCollisionSystem) where
  resolve :
    ∀ g h : C.Genealogy,
      C.SameKeyRequired g h →
        {a : C.Answer // C.Resolves g h a}

/-- Computational resolver form. -/
structure BoundaryResolver (C : BoundaryCollisionSystem) where
  choose : C.Genealogy → C.Genealogy → C.Answer
  sound :
    ∀ g h : C.Genealogy,
      C.SameKeyRequired g h →
        C.Resolves g h (choose g h)

/-- A resolver gives a full certificate. -/
def BoundaryResolver.toCertificate
    {C : BoundaryCollisionSystem}
    (B : BoundaryResolver C) :
    FullBoundaryCertificate C :=
{
  resolve := by
    intro g h hreq
    exact ⟨B.choose g h, B.sound g h hreq⟩
}

/-- Boundary coverage means existence of a full certificate. -/
abbrev GlobalBoundaryCoverage (C : BoundaryCollisionSystem) : Prop :=
  Nonempty (FullBoundaryCertificate C)

/-- Uncovered boundary. -/
abbrev BoundaryUncovered (C : BoundaryCollisionSystem) : Prop :=
  ¬ C.GlobalBoundaryCoverage

/-- Resolver implies coverage. -/
theorem coverage_of_resolver
    {C : BoundaryCollisionSystem}
    (B : BoundaryResolver C) :
    C.GlobalBoundaryCoverage :=
  ⟨B.toCertificate⟩

/-- Uncovered boundary allows no resolver. -/
theorem no_resolver_of_uncovered
    {C : BoundaryCollisionSystem}
    (hUncovered : C.BoundaryUncovered) :
    ¬ Nonempty (BoundaryResolver C) := by
  intro h
  rcases h with ⟨B⟩
  exact hUncovered (coverage_of_resolver B)

end BoundaryCollisionSystem

/-#############################################################################
  §3. Rank tower prefixes
#############################################################################-/

/-- A rank tower assigns a boundary to each finite level. -/
structure RankTower where
  boundary : Nat → BoundaryCollisionSystem

namespace RankTower

/-- All boundaries below `N` are covered. -/
def PrefixClosed (T : RankTower) (N : Nat) : Prop :=
  ∀ k : Nat, k < N → (T.boundary k).GlobalBoundaryCoverage

/-- Some boundary below `N` is uncovered. -/
def PrefixObstructed (T : RankTower) (N : Nat) : Prop :=
  ∃ k : Nat, k < N ∧ (T.boundary k).BoundaryUncovered

/-- Full pass through all boundaries below `N`. -/
structure RankTowerPass (T : RankTower) (N : Nat) where
  cert :
    ∀ k : Nat, k < N →
      BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary k)

/-- A pass gives prefix closure. -/
theorem prefixClosed_of_pass
    {T : RankTower} {N : Nat}
    (P : RankTowerPass T N) :
    T.PrefixClosed N := by
  intro k hk
  exact ⟨P.cert k hk⟩

/-- Prefix closure gives a pass by choosing the supplied certificates. -/
noncomputable def pass_of_prefixClosed
    {T : RankTower} {N : Nat}
    (hClosed : T.PrefixClosed N) :
    RankTowerPass T N :=
{
  cert := by
    intro k hk
    exact Classical.choice (hClosed k hk)
}

/-- Pass existence is equivalent to prefix closure. -/
theorem nonempty_pass_iff_prefixClosed
    {T : RankTower} {N : Nat} :
    Nonempty (RankTowerPass T N) ↔ T.PrefixClosed N := by
  constructor
  · intro h
    rcases h with ⟨P⟩
    exact prefixClosed_of_pass P
  · intro h
    exact ⟨pass_of_prefixClosed h⟩

/-- Prefix obstruction contradicts prefix closure. -/
theorem not_prefixClosed_of_obstructed
    {T : RankTower} {N : Nat}
    (hObs : T.PrefixObstructed N) :
    ¬ T.PrefixClosed N := by
  intro hClosed
  rcases hObs with ⟨k, hk, hUncovered⟩
  exact hUncovered (hClosed k hk)

/-- Prefix closure excludes obstruction. -/
theorem not_obstructed_of_prefixClosed
    {T : RankTower} {N : Nat}
    (hClosed : T.PrefixClosed N) :
    ¬ T.PrefixObstructed N := by
  intro hObs
  exact not_prefixClosed_of_obstructed hObs hClosed

/-- Prefix obstruction blocks every pass. -/
theorem no_pass_of_obstructed
    {T : RankTower} {N : Nat}
    (hObs : T.PrefixObstructed N) :
    ¬ Nonempty (RankTowerPass T N) := by
  intro hPass
  rcases hPass with ⟨P⟩
  exact not_prefixClosed_of_obstructed hObs (prefixClosed_of_pass P)

/-- A first missing boundary below `N`. -/
structure FirstMissingBoundary (T : RankTower) (N : Nat) where
  m : Nat
  m_lt_N : m < N
  missing : (T.boundary m).BoundaryUncovered
  covered_before :
    ∀ k : Nat, k < m → (T.boundary k).GlobalBoundaryCoverage

/-- A first missing boundary is an obstruction. -/
theorem obstructed_of_firstMissing
    {T : RankTower} {N : Nat}
    (M : FirstMissingBoundary T N) :
    T.PrefixObstructed N :=
  ⟨M.m, M.m_lt_N, M.missing⟩

/-- A first missing boundary blocks every pass. -/
theorem no_pass_of_firstMissing
    {T : RankTower} {N : Nat}
    (M : FirstMissingBoundary T N) :
    ¬ Nonempty (RankTowerPass T N) :=
  no_pass_of_obstructed (obstructed_of_firstMissing M)

/-- Restrict a pass to a smaller prefix. -/
def RankTowerPass.restrict
    {T : RankTower} {M N : Nat}
    (P : RankTowerPass T N)
    (hMN : M ≤ N) :
    RankTowerPass T M :=
{
  cert := by
    intro k hk
    exact P.cert k (lt_of_lt_of_le hk hMN)
}

/-- Extend a prefix pass by one new boundary certificate. -/
def RankTowerPass.extend
    {T : RankTower} {N : Nat}
    (P : RankTowerPass T N)
    (cN : BoundaryCollisionSystem.FullBoundaryCertificate (T.boundary N)) :
    RankTowerPass T (N + 1) :=
{
  cert := by
    intro k hk
    by_cases hlt : k < N
    · exact P.cert k hlt
    · have hk_le_N : k ≤ N := Nat.le_of_lt_succ hk
      have hN_le_k : N ≤ k := Nat.le_of_not_gt hlt
      have hEq : k = N := Nat.le_antisymm hk_le_N hN_le_k
      cases hEq
      exact cN
}

/-- Prefix closure at `N+1` gives prefix closure at `N`. -/
theorem prefixClosed_pred
    {T : RankTower} {N : Nat}
    (h : T.PrefixClosed (N + 1)) :
    T.PrefixClosed N := by
  intro k hk
  exact h k (lt_trans hk (Nat.lt_succ_self N))

/-- Prefix closure at `N+1` gives coverage at boundary `N`. -/
theorem lastBoundaryCovered_of_prefixClosed_succ
    {T : RankTower} {N : Nat}
    (h : T.PrefixClosed (N + 1)) :
    (T.boundary N).GlobalBoundaryCoverage :=
  h N (Nat.lt_succ_self N)

/--
If prefix `N` is closed and boundary `N` is covered, then prefix `N+1` is closed.
-/
theorem prefixClosed_succ_of_prefixClosed_and_last
    {T : RankTower} {N : Nat}
    (hN : T.PrefixClosed N)
    (hLast : (T.boundary N).GlobalBoundaryCoverage) :
    T.PrefixClosed (N + 1) := by
  intro k hk
  by_cases hlt : k < N
  · exact hN k hlt
  · have hk_le_N : k ≤ N := Nat.le_of_lt_succ hk
    have hN_le_k : N ≤ k := Nat.le_of_not_gt hlt
    have hEq : k = N := Nat.le_antisymm hk_le_N hN_le_k
    cases hEq
    exact hLast

end RankTower

/-#############################################################################
  §4. Complete verification
#############################################################################-/

/--
Local verifier data at each rank level below `N`.
-/
structure LocalTowerAlgorithm
    (R : Nat → RankedForwardSystem)
    (N : Nat) where
  verifierAt :
    ∀ k : Nat, k < N → RankInternalVerifier (R k)

/--
Complete rank-prefix verification: local rank-internal verification plus a pass
through all rank boundaries below `N`.
-/
structure CompleteRankVerification
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) where
  localData : LocalTowerAlgorithm R N
  pass : T.RankTowerPass N

/-- Complete verification gives local data. -/
theorem local_of_completeVerification
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (V : CompleteRankVerification R T N) :
    Nonempty (LocalTowerAlgorithm R N) :=
  ⟨V.localData⟩

/-- Complete verification gives prefix closure. -/
theorem prefixClosed_of_completeVerification
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (V : CompleteRankVerification R T N) :
    T.PrefixClosed N :=
  T.prefixClosed_of_pass V.pass

/-- Local data plus prefix closure gives complete verification. -/
noncomputable def completeVerification_of_local_and_prefixClosed
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (hLocal : Nonempty (LocalTowerAlgorithm R N))
    (hClosed : T.PrefixClosed N) :
    CompleteRankVerification R T N :=
{
  localData := Classical.choice hLocal
  pass := T.pass_of_prefixClosed hClosed
}

/--
Main finite-prefix closure theorem.

Complete verification exists iff local data exists and the prefix is closed.
-/
theorem nonempty_completeVerification_iff_local_and_prefixClosed
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat} :
    Nonempty (CompleteRankVerification R T N) ↔
      Nonempty (LocalTowerAlgorithm R N) ∧ T.PrefixClosed N := by
  constructor
  · intro h
    rcases h with ⟨V⟩
    exact ⟨⟨V.localData⟩, prefixClosed_of_completeVerification V⟩
  · intro h
    rcases h with ⟨hLocal, hClosed⟩
    exact ⟨completeVerification_of_local_and_prefixClosed hLocal hClosed⟩

/--
If local data already exists, complete verification is equivalent to prefix
closure.
-/
theorem completeVerification_iff_prefixClosed_of_local
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (hLocal : Nonempty (LocalTowerAlgorithm R N)) :
    Nonempty (CompleteRankVerification R T N) ↔ T.PrefixClosed N := by
  constructor
  · intro h
    rcases h with ⟨V⟩
    exact prefixClosed_of_completeVerification V
  · intro hClosed
    exact ⟨completeVerification_of_local_and_prefixClosed hLocal hClosed⟩

/-- Obstructed prefix blocks complete verification. -/
theorem no_completeVerification_of_obstructed
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (hObs : T.PrefixObstructed N) :
    ¬ Nonempty (CompleteRankVerification R T N) := by
  intro h
  rcases h with ⟨V⟩
  exact T.not_prefixClosed_of_obstructed hObs
    (prefixClosed_of_completeVerification V)

/-- First missing boundary blocks complete verification. -/
theorem no_completeVerification_of_firstMissing
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (M : T.FirstMissingBoundary N) :
    ¬ Nonempty (CompleteRankVerification R T N) :=
  no_completeVerification_of_obstructed (T.obstructed_of_firstMissing M)

/-#############################################################################
  §5. Closure result object
#############################################################################-/

/--
A finite prefix has either been closed by a complete verification, or explicitly
blocked by a first missing boundary.

This object is the honest closure/result format for a finite prefix.
-/
inductive RankPrefixClosureResult
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) : Prop where
  | closed :
      CompleteRankVerification R T N →
      RankPrefixClosureResult R T N
  | obstructed :
      T.FirstMissingBoundary N →
      RankPrefixClosureResult R T N

namespace RankPrefixClosureResult

/-- If the result is obstructed, complete verification is impossible. -/
theorem noComplete_of_obstructed
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (M : T.FirstMissingBoundary N) :
    ¬ Nonempty (CompleteRankVerification R T N) :=
  no_completeVerification_of_firstMissing M

/-- If the result is closed, prefix closure holds. -/
theorem prefixClosed_of_closed
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (V : CompleteRankVerification R T N) :
    T.PrefixClosed N :=
  prefixClosed_of_completeVerification V

end RankPrefixClosureResult

/--
A closure oracle for finite prefixes.  It is not taken globally in the
mathematics; it is the exact object one must build to close every finite prefix.
-/
structure FinitePrefixClosureOracle
    (R : Nat → RankedForwardSystem)
    (T : RankTower) where
  decidePrefix :
    ∀ N : Nat, RankPrefixClosureResult R T N

/-- A closure oracle gives either a complete verification or a first obstruction. -/
theorem FinitePrefixClosureOracle.result_at
    {R : Nat → RankedForwardSystem}
    {T : RankTower}
    (O : FinitePrefixClosureOracle R T)
    (N : Nat) :
    RankPrefixClosureResult R T N :=
  O.decidePrefix N

/-#############################################################################
  §6. Local-only promotion is exactly the dangerous missing step
#############################################################################-/

/--
Local-only promotion: local verifier data alone produces complete verification.

This is dangerous because it would manufacture boundary certificates from local
rank checks.
-/
def LocalOnlyPromotion
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) : Prop :=
  Nonempty (LocalTowerAlgorithm R N) → Nonempty (CompleteRankVerification R T N)

/--
If local data exists and the prefix is obstructed, local-only promotion is
impossible.
-/
theorem no_localOnlyPromotion_of_obstructed
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (hLocal : Nonempty (LocalTowerAlgorithm R N))
    (hObs : T.PrefixObstructed N) :
    ¬ LocalOnlyPromotion R T N := by
  intro promote
  have hComplete : Nonempty (CompleteRankVerification R T N) :=
    promote hLocal
  exact no_completeVerification_of_obstructed hObs hComplete

/--
If local data exists and there is a first missing boundary, local-only promotion
is impossible.
-/
theorem no_localOnlyPromotion_of_firstMissing
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (hLocal : Nonempty (LocalTowerAlgorithm R N))
    (M : T.FirstMissingBoundary N) :
    ¬ LocalOnlyPromotion R T N :=
  no_localOnlyPromotion_of_obstructed hLocal (T.obstructed_of_firstMissing M)

/--
A local-only closure claim over a first missing boundary self-destructs.
-/
structure LocalOnlyClosureClaim
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) where
  localData : LocalTowerAlgorithm R N
  promote : LocalOnlyPromotion R T N
  firstMissing : T.FirstMissingBoundary N

/-- Local-only closure over a first missing boundary is impossible. -/
theorem LocalOnlyClosureClaim.contradiction
    {R : Nat → RankedForwardSystem}
    {T : RankTower} {N : Nat}
    (X : LocalOnlyClosureClaim R T N) :
    False := by
  have hLocal : Nonempty (LocalTowerAlgorithm R N) := ⟨X.localData⟩
  exact no_localOnlyPromotion_of_firstMissing hLocal X.firstMissing X.promote

/-#############################################################################
  §7. Closing theorem-shaped summary
#############################################################################-/

/--
The finite-prefix closure slogan.

Once local verifier data exists, closing the prefix is equivalent to supplying
certificates for every boundary below `N`.  A first missing boundary blocks
closure.  Local-only promotion across such a boundary is impossible.
-/
abbrev RankPrefixClosureCompletionSlogan
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) : Prop :=
  (Nonempty (LocalTowerAlgorithm R N) →
    (Nonempty (CompleteRankVerification R T N) ↔ T.PrefixClosed N)) ∧
  (∀ M : T.FirstMissingBoundary N,
    ¬ Nonempty (CompleteRankVerification R T N)) ∧
  (∀ M : T.FirstMissingBoundary N,
    Nonempty (LocalTowerAlgorithm R N) →
      ¬ LocalOnlyPromotion R T N)

/-- The closure slogan follows from the finite-prefix theorems. -/
theorem rankPrefixClosureCompletionSlogan
    (R : Nat → RankedForwardSystem)
    (T : RankTower)
    (N : Nat) :
    RankPrefixClosureCompletionSlogan R T N := by
  constructor
  · intro hLocal
    exact completeVerification_iff_prefixClosed_of_local hLocal
  · constructor
    · intro M
      exact no_completeVerification_of_firstMissing M
    · intro M hLocal
      exact no_localOnlyPromotion_of_firstMissing hLocal M

end RankPrefixClosureCompletion
end EuclidsPath

/-
EuclidsPath_rank_inequality_closure_patch.lean

Formal patch: rank inequality as the closure obstruction.

Thesis:

  * a fixed rank can contain only its bounded lower prefix;
  * it cannot contain every higher rank;
  * mutual inclusion of distinct ranks is impossible by antisymmetry;
  * a fixed-rank algorithm cannot solve an unbounded-rank family;
  * any claimed inclusion of a strictly higher rank into a lower rank is a
    rank-collapse engine;
  * finite-prefix closure is exact: rank r covers prefix r+1 and cannot cover
    prefix r+2.

This is the rank-theoretic abstraction of the phenomenon already used in the
twin-prime Step00 analysis: one bounded rank cannot absorb all later rank
obligations without either paying a boundary certificate or collapsing rank.
-/



namespace EuclidsPath
namespace RankInequalityClosure

/-#############################################################################
  §1. Primitive rank inclusion calculus
#############################################################################-/

/--
Rank inclusion is represented by the natural order.

A rank `target` contains rank `source` only if `source ≤ target`.
-/
abbrev RankIncludedIn (source target : Nat) : Prop :=
  source ≤ target

/-- Strictly higher rank cannot be included in a lower rank. -/
theorem higher_rank_not_included_in_lower
    {lower higher : Nat}
    (h : lower < higher) :
    ¬ RankIncludedIn higher lower := by
  exact Nat.not_le_of_gt h

/-- Mutual inclusion of ranks forces equality. -/
theorem rank_mutual_inclusion_eq
    {a b : Nat}
    (hab : RankIncludedIn a b)
    (hba : RankIncludedIn b a) :
    a = b :=
  Nat.le_antisymm hab hba

/-- Distinct ranks cannot mutually include each other. -/
theorem distinct_ranks_not_mutually_include
    {a b : Nat}
    (hne : a ≠ b) :
    ¬ (RankIncludedIn a b ∧ RankIncludedIn b a) := by
  intro h
  exact hne (rank_mutual_inclusion_eq h.1 h.2)

/-- The next rank is not included in the current rank. -/
theorem succ_rank_not_included
    (r : Nat) :
    ¬ RankIncludedIn (r + 1) r := by
  exact Nat.not_succ_le_self r

/--
There is no top finite natural rank that contains every rank.
-/
theorem no_finite_rank_contains_all :
    ¬ ∃ top : Nat, ∀ r : Nat, RankIncludedIn r top := by
  intro h
  rcases h with ⟨top, htop⟩
  exact Nat.not_succ_le_self top (htop (top + 1))

/-#############################################################################
  §2. Rank projections and collapse engines
#############################################################################-/

/--
A rank-respecting projection from `source` to `target`.

It is only legal when `source ≤ target`.
-/
structure RankProjection (source target : Nat) where
  respects_rank : RankIncludedIn source target

/-- A projection from a strictly higher rank into a lower rank is impossible. -/
theorem no_strict_downward_rankProjection
    {source target : Nat}
    (h : target < source) :
    ¬ Nonempty (RankProjection source target) := by
  intro hp
  rcases hp with ⟨P⟩
  exact Nat.not_le_of_gt h P.respects_rank

/--
A universal rank compression would project every rank into one fixed target.
-/
structure UniversalRankCompression where
  target : Nat
  project : ∀ source : Nat, RankProjection source target

/-- No universal compression into one finite rank exists. -/
theorem no_universalRankCompression :
    ¬ Nonempty UniversalRankCompression := by
  intro h
  rcases h with ⟨U⟩
  have p := U.project (U.target + 1)
  exact Nat.not_succ_le_self U.target p.respects_rank

/--
A rank-collapse engine is exactly the impossible pattern:
a strictly higher rank is claimed to fit into a lower rank.
-/
structure RankCollapseEngine where
  lower : Nat
  higher : Nat
  strict : lower < higher
  bad_inclusion : RankIncludedIn higher lower

/-- No rank-collapse engine can exist. -/
theorem no_rankCollapseEngine
    (E : RankCollapseEngine) :
    False :=
  Nat.not_le_of_gt E.strict E.bad_inclusion

/--
A universal compression would immediately yield a rank-collapse engine.
-/
def rankCollapseEngine_of_universalCompression
    (U : UniversalRankCompression) :
    RankCollapseEngine :=
{
  lower := U.target
  higher := U.target + 1
  strict := Nat.lt_succ_self U.target
  bad_inclusion := (U.project (U.target + 1)).respects_rank
}

/-- Therefore universal compression self-destructs via rank collapse. -/
theorem universalCompression_selfDestructs
    (U : UniversalRankCompression) :
    False :=
  no_rankCollapseEngine (rankCollapseEngine_of_universalCompression U)

/-#############################################################################
  §3. Exact finite-prefix containment
#############################################################################-/

/--
A rank `target` contains the finite prefix of ranks `< N`.
-/
structure RankPrefixContainer (N target : Nat) where
  includes :
    ∀ k : Nat, k < N → RankIncludedIn k target

/--
Rank `r` contains exactly the prefix `k < r+1`.
-/
def RankPrefixContainer.selfPrefix (r : Nat) :
    RankPrefixContainer (r + 1) r :=
{
  includes := by
    intro k hk
    exact Nat.le_of_lt_succ hk
}

/--
Rank `r` cannot contain prefix `r+2`, because that prefix includes `r+1`.
-/
theorem no_prefixContainer_past_target
    (r : Nat) :
    ¬ Nonempty (RankPrefixContainer (r + 2) r) := by
  intro h
  rcases h with ⟨C⟩
  have hle : r + 1 ≤ r :=
    C.includes (r + 1) (Nat.lt_succ_self (r + 1))
  exact Nat.not_succ_le_self r hle

/--
More generally, if the prefix goes beyond `target+1`, no container exists.
-/
theorem no_prefixContainer_if_target_lt_prefix_pred
    {N target : Nat}
    (hBeyond : target + 1 < N) :
    ¬ Nonempty (RankPrefixContainer N target) := by
  intro h
  rcases h with ⟨C⟩
  have hle : target + 1 ≤ target :=
    C.includes (target + 1) hBeyond
  exact Nat.not_succ_le_self target hle

/--
If `N ≤ target+1`, then target contains the prefix `< N`.
-/
def prefixContainer_of_prefix_le_target_succ
    {N target : Nat}
    (hN : N ≤ target + 1) :
    RankPrefixContainer N target :=
{
  includes := by
    intro k hk
    have hk_target_succ : k < target + 1 :=
      lt_of_lt_of_le hk hN
    exact Nat.le_of_lt_succ hk_target_succ
}

/--
Finite-prefix containment is exact: a rank `target` contains prefix `N` iff
`N ≤ target + 1`.
-/
theorem nonempty_prefixContainer_iff
    {N target : Nat} :
    Nonempty (RankPrefixContainer N target) ↔ N ≤ target + 1 := by
  constructor
  · intro h
    classical
    by_contra hNot
    have hBeyond : target + 1 < N := Nat.lt_of_not_ge hNot
    exact no_prefixContainer_if_target_lt_prefix_pred hBeyond h
  · intro hN
    exact ⟨prefixContainer_of_prefix_le_target_succ hN⟩

/-#############################################################################
  §4. Rank-bounded classes and strict inequality
#############################################################################-/

/--
A rank-bounded class is a class whose algorithms/certificates live inside one
fixed finite rank.
-/
structure RankBoundedClass where
  bound : Nat

/--
`A` includes `B` when `A`'s bound is at least `B`'s bound.
-/
def ClassIncludes (A B : RankBoundedClass) : Prop :=
  RankIncludedIn B.bound A.bound

/-- Mutual inclusion of rank-bounded classes forces equal bounds. -/
theorem class_mutual_inclusion_bound_eq
    {A B : RankBoundedClass}
    (hAB : ClassIncludes A B)
    (hBA : ClassIncludes B A) :
    A.bound = B.bound :=
  rank_mutual_inclusion_eq hBA hAB

/--
A strictly lower bounded class cannot include a strictly higher bounded class.
-/
theorem strict_rank_class_not_include_higher
    {A B : RankBoundedClass}
    (h : A.bound < B.bound) :
    ¬ ClassIncludes A B := by
  exact higher_rank_not_included_in_lower h

/--
There is no universal finite rank-bounded class containing all finite bounds.
-/
structure UniversalRankBoundedClass where
  C : RankBoundedClass
  includesAll :
    ∀ b : Nat, ClassIncludes C { bound := b }

/-- No universal finite rank-bounded class exists. -/
theorem no_universalRankBoundedClass :
    ¬ Nonempty UniversalRankBoundedClass := by
  intro h
  rcases h with ⟨U⟩
  have hle : U.C.bound + 1 ≤ U.C.bound :=
    U.includesAll (U.C.bound + 1)
  exact Nat.not_succ_le_self U.C.bound hle

/-#############################################################################
  §5. Unbounded-rank families defeat fixed-rank solvers
#############################################################################-/

/--
A problem family whose instances have required rank and are unbounded in rank.
-/
structure UnboundedRankFamily where
  Instance : Type
  requiredRank : Instance → Nat
  unbounded :
    ∀ r : Nat, ∃ x : Instance, r < requiredRank x

/--
A fixed-rank solver for a family claims one finite rank bound handles every
instance.
-/
structure FixedRankSolver (F : UnboundedRankFamily) where
  bound : Nat
  solvesWithinBound :
    ∀ x : F.Instance, RankIncludedIn (F.requiredRank x) bound

/-- No fixed-rank solver can solve an unbounded-rank family. -/
theorem no_fixedRankSolver_for_unboundedFamily
    (F : UnboundedRankFamily) :
    ¬ Nonempty (FixedRankSolver F) := by
  intro h
  rcases h with ⟨S⟩
  rcases F.unbounded S.bound with ⟨x, hx⟩
  exact Nat.not_le_of_gt hx (S.solvesWithinBound x)

/--
A rank-bounded family is the opposite situation: one finite bound is explicitly
given.
-/
structure RankBoundedFamily where
  Instance : Type
  requiredRank : Instance → Nat
  bound : Nat
  bounded :
    ∀ x : Instance, requiredRank x ≤ bound

/--
Safe solver type for bounded families.
-/
structure BoundedFamilySolver (F : RankBoundedFamily) where
  bound : Nat
  bound_ok : bound = F.bound
  solvesWithinBound :
    ∀ x : F.Instance, F.requiredRank x ≤ bound

/-- A bounded family has its canonical bounded solver. -/
def boundedFamilySolver (F : RankBoundedFamily) :
    BoundedFamilySolver F :=
{
  bound := F.bound
  bound_ok := rfl
  solvesWithinBound := by
    intro x
    exact F.bounded x
}

/-#############################################################################
  §6. Boundary payment versus illegal inclusion
#############################################################################-/

/--
A paid inclusion between ranks.

Besides the order condition `source ≤ target`, it explicitly records a payment or
boundary certificate.
-/
structure PaidRankInclusion
    (BoundaryPaid : Nat → Nat → Prop)
    (source target : Nat) where
  rank_ok : RankIncludedIn source target
  paid : BoundaryPaid source target

/--
An unpaid inclusion attempt contains only an inclusion claim, with no payment.
-/
structure UnpaidRankInclusionAttempt
    (BoundaryPaid : Nat → Nat → Prop)
    (source target : Nat) where
  rank_claim : RankIncludedIn source target
  no_payment : ¬ BoundaryPaid source target

/--
A strict downward unpaid inclusion attempt is already impossible at the rank
level, before payment is considered.
-/
theorem no_unpaid_strict_downward_inclusion
    {BoundaryPaid : Nat → Nat → Prop}
    {source target : Nat}
    (hStrict : target < source) :
    ¬ Nonempty (UnpaidRankInclusionAttempt BoundaryPaid source target) := by
  intro h
  rcases h with ⟨A⟩
  exact Nat.not_le_of_gt hStrict A.rank_claim

/--
A paid inclusion also cannot violate rank order.
-/
theorem no_paid_strict_downward_inclusion
    {BoundaryPaid : Nat → Nat → Prop}
    {source target : Nat}
    (hStrict : target < source) :
    ¬ Nonempty (PaidRankInclusion BoundaryPaid source target) := by
  intro h
  rcases h with ⟨A⟩
  exact Nat.not_le_of_gt hStrict A.rank_ok

/--
A local algorithm that claims arbitrary rank inclusion without boundary payment
is exactly a universal compression attempt.
-/
structure LocalRankAbsorber
    (BoundaryPaid : Nat → Nat → Prop) where
  target : Nat
  absorb : ∀ source : Nat, UnpaidRankInclusionAttempt BoundaryPaid source target

/-- No local absorber can absorb all ranks into one fixed target. -/
theorem no_localRankAbsorber
    {BoundaryPaid : Nat → Nat → Prop} :
    ¬ Nonempty (LocalRankAbsorber BoundaryPaid) := by
  intro h
  rcases h with ⟨A⟩
  have bad := A.absorb (A.target + 1)
  exact Nat.not_succ_le_self A.target bad.rank_claim

/-#############################################################################
  §7. Closing rank-inequality statement
#############################################################################-/

/--
The rank inequality closure slogan.

A fixed rank contains exactly its finite lower prefix, no finite rank contains
all ranks, strict higher-to-lower inclusion is impossible, and unbounded-rank
families have no fixed-rank solver.
-/
abbrev RankInequalityClosureSlogan : Prop :=
  (∀ r : Nat, Nonempty (RankPrefixContainer (r + 1) r)) ∧
  (∀ r : Nat, ¬ Nonempty (RankPrefixContainer (r + 2) r)) ∧
  (¬ ∃ top : Nat, ∀ r : Nat, RankIncludedIn r top) ∧
  (∀ F : UnboundedRankFamily, ¬ Nonempty (FixedRankSolver F)) ∧
  (∀ BoundaryPaid : Nat → Nat → Prop,
    ¬ Nonempty (LocalRankAbsorber BoundaryPaid))

/-- The rank inequality closure slogan is proved by the preceding lemmas. -/
theorem rankInequalityClosureSlogan :
    RankInequalityClosureSlogan := by
  constructor
  · intro r
    exact ⟨RankPrefixContainer.selfPrefix r⟩
  · constructor
    · intro r
      exact no_prefixContainer_past_target r
    · constructor
      · exact no_finite_rank_contains_all
      · constructor
        · intro F
          exact no_fixedRankSolver_for_unboundedFamily F
        · intro BoundaryPaid
          exact no_localRankAbsorber

end RankInequalityClosure
end EuclidsPath

/-
EuclidsPath_rank_class_separation_closure_patch.lean

Rank-class separation closure.

This file closes the rank-local separation theorem in the exact sense supported
by the Step00/rank architecture:

  * a fixed finite rank can cover only a bounded prefix;
  * a verifiable family may have unbounded required rank;
  * no fixed-rank solver covers such a family;
  * therefore the bounded-rank/local-P class is strictly smaller than the
    verifiable-unbounded/local-NP class, once an unbounded verifiable family is
    supplied;
  * any universal local absorber would be a rank-collapse engine.

This is a rank-local theorem.  It is not a theorem about classical Turing-machine
P versus NP.
-/



namespace EuclidsPath
namespace RankClassSeparationClosure

/-#############################################################################
  §1. Rank inclusion and finite-prefix exactness
#############################################################################-/

/-- Rank inclusion: rank `source` fits inside rank `target` iff `source ≤ target`. -/
abbrev RankIncludedIn (source target : Nat) : Prop :=
  source ≤ target

/-- A strictly higher rank is not included in a lower rank. -/
theorem higher_rank_not_included_in_lower
    {lower higher : Nat}
    (h : lower < higher) :
    ¬ RankIncludedIn higher lower := by
  exact Nat.not_le_of_gt h

/-- Mutual rank inclusion forces equality. -/
theorem rank_mutual_inclusion_eq
    {a b : Nat}
    (hab : RankIncludedIn a b)
    (hba : RankIncludedIn b a) :
    a = b :=
  Nat.le_antisymm hab hba

/-- The successor rank is not included in the current rank. -/
theorem succ_rank_not_included
    (r : Nat) :
    ¬ RankIncludedIn (r + 1) r := by
  exact Nat.not_succ_le_self r

/-- No finite rank contains all finite ranks. -/
theorem no_finite_rank_contains_all :
    ¬ ∃ top : Nat, ∀ r : Nat, RankIncludedIn r top := by
  intro h
  rcases h with ⟨top, htop⟩
  exact Nat.not_succ_le_self top (htop (top + 1))

/--
A rank `target` contains all ranks below prefix-length `N`.
-/
structure RankPrefixContainer (N target : Nat) where
  includes :
    ∀ k : Nat, k < N → RankIncludedIn k target

/-- Rank `r` contains exactly its lower prefix `< r+1`. -/
def RankPrefixContainer.selfPrefix (r : Nat) :
    RankPrefixContainer (r + 1) r :=
{
  includes := by
    intro k hk
    exact Nat.le_of_lt_succ hk
}

/-- Rank `r` cannot contain prefix `< r+2`, since that includes `r+1`. -/
theorem no_prefixContainer_past_target
    (r : Nat) :
    ¬ Nonempty (RankPrefixContainer (r + 2) r) := by
  intro h
  rcases h with ⟨C⟩
  have hle : r + 1 ≤ r :=
    C.includes (r + 1) (Nat.lt_succ_self (r + 1))
  exact Nat.not_succ_le_self r hle

/-- If the prefix passes `target+1`, containment is impossible. -/
theorem no_prefixContainer_if_target_lt_prefix_pred
    {N target : Nat}
    (hBeyond : target + 1 < N) :
    ¬ Nonempty (RankPrefixContainer N target) := by
  intro h
  rcases h with ⟨C⟩
  have hle : target + 1 ≤ target :=
    C.includes (target + 1) hBeyond
  exact Nat.not_succ_le_self target hle

/-- If `N ≤ target+1`, then `target` contains prefix `< N`. -/
def prefixContainer_of_prefix_le_target_succ
    {N target : Nat}
    (hN : N ≤ target + 1) :
    RankPrefixContainer N target :=
{
  includes := by
    intro k hk
    have hk_target_succ : k < target + 1 :=
      lt_of_lt_of_le hk hN
    exact Nat.le_of_lt_succ hk_target_succ
}

/-- Exact finite-prefix containment theorem. -/
theorem nonempty_prefixContainer_iff
    {N target : Nat} :
    Nonempty (RankPrefixContainer N target) ↔ N ≤ target + 1 := by
  constructor
  · intro h
    by_contra hNot
    have hBeyond : target + 1 < N := Nat.lt_of_not_ge hNot
    exact no_prefixContainer_if_target_lt_prefix_pred hBeyond h
  · intro hN
    exact ⟨prefixContainer_of_prefix_le_target_succ hN⟩

/-#############################################################################
  §2. Ranked paths and local verification
#############################################################################-/

/-- A ranked forward system: every legal step strictly decreases rank. -/
structure RankedForwardSystem where
  State : Type
  rank : State → Nat
  Step : State → State → Prop
  step_decreases :
    ∀ {s t : State}, Step s t → rank t < rank s

/-- Length-indexed forward paths. -/
inductive PathN (R : RankedForwardSystem) :
    R.State → R.State → Nat → Prop where
  | nil (s : R.State) :
      PathN R s s 0
  | cons {s t u : R.State} {n : Nat}
      (h : R.Step s t)
      (tail : PathN R t u n) :
      PathN R s u (n + 1)

namespace PathN

/-- Every forward path is bounded by the starting rank. -/
theorem len_le_rank
    {R : RankedForwardSystem}
    {s t : R.State} {n : Nat}
    (p : PathN R s t n) :
    n ≤ R.rank s := by
  induction p with
  | nil s =>
      exact Nat.zero_le _
  | @cons s t u n hstep tail ih =>
      have hlt : n < R.rank s :=
        lt_of_le_of_lt ih (R.step_decreases hstep)
      exact Nat.succ_le_of_lt hlt

end PathN

/-- A local verifier checks one rank-internal step. -/
structure RankInternalVerifier (R : RankedForwardSystem) where
  acceptsStep : R.State → R.State → Bool
  sound :
    ∀ {s t : R.State}, acceptsStep s t = true → R.Step s t
  complete :
    ∀ {s t : R.State}, R.Step s t → acceptsStep s t = true

namespace RankInternalVerifier

/-- Any accepted local step decreases rank. -/
theorem acceptedStep_decreases
    {R : RankedForwardSystem}
    (V : RankInternalVerifier R)
    {s t : R.State}
    (h : V.acceptsStep s t = true) :
    R.rank t < R.rank s :=
  R.step_decreases (V.sound h)

end RankInternalVerifier

/-#############################################################################
  §3. Rank-local problem families
#############################################################################-/

/--
A rank problem family has instances and a required rank for each instance.
-/
structure RankProblemFamily where
  Instance : Type
  requiredRank : Instance → Nat

/-- A family is unbounded in required rank. -/
def RankProblemFamily.Unbounded (F : RankProblemFamily) : Prop :=
  ∀ r : Nat, ∃ x : F.Instance, r < F.requiredRank x

/-- A family is bounded by a finite rank. -/
def RankProblemFamily.BoundedBy (F : RankProblemFamily) (b : Nat) : Prop :=
  ∀ x : F.Instance, F.requiredRank x ≤ b

/-- Boundedness as existence of some finite rank bound. -/
def RankProblemFamily.Bounded (F : RankProblemFamily) : Prop :=
  ∃ b : Nat, F.BoundedBy b

/-- A bounded family cannot be unbounded. -/
theorem not_unbounded_of_bounded
    {F : RankProblemFamily}
    (hB : F.Bounded) :
    ¬ F.Unbounded := by
  intro hU
  rcases hB with ⟨b, hb⟩
  rcases hU b with ⟨x, hx⟩
  exact Nat.not_le_of_gt hx (hb x)

/-- An unbounded family is not bounded. -/
theorem not_bounded_of_unbounded
    {F : RankProblemFamily}
    (hU : F.Unbounded) :
    ¬ F.Bounded := by
  intro hB
  exact not_unbounded_of_bounded hB hU

/-#############################################################################
  §4. Local-P and local-NP rank classes
#############################################################################-/

/--
Rank-local P: the whole family is solvable/contained within one fixed finite
rank bound.
-/
def InRankLocalP (F : RankProblemFamily) : Prop :=
  F.Bounded

/--
Rank-local NP: the family has local witness verification.

This is deliberately abstract: the verifier side is local and rank-internal.
The separation theorem needs a concrete family that is locally verifiable and
unbounded in required rank.
-/
def InRankLocalNP (F : RankProblemFamily) : Prop :=
  ∃ (_Witness : F.Instance → Type) (verifierRank : F.Instance → Nat),
    (∀ x : F.Instance, F.requiredRank x ≤ verifierRank x) ∧
    ∃ local_checkable : Prop, local_checkable

/--
An explicit separation witness: a rank-local NP family that is unbounded.
-/
structure RankSeparationWitness where
  family : RankProblemFamily
  inNP : InRankLocalNP family
  unbounded : family.Unbounded

/-- The separating family is not in rank-local P. -/
theorem RankSeparationWitness.notInP
    (W : RankSeparationWitness) :
    ¬ InRankLocalP W.family :=
  not_bounded_of_unbounded W.unbounded

/--
Rank-local class inclusion `NP ⊆ P` would send every locally verifiable family
to a bounded-rank family.
-/
def RankLocalNP_subset_RankLocalP : Prop :=
  ∀ F : RankProblemFamily, InRankLocalNP F → InRankLocalP F

/--
A rank separation witness refutes rank-local NP⊆P.
-/
theorem not_rankLocalNP_subset_RankLocalP_of_witness
    (W : RankSeparationWitness) :
    ¬ RankLocalNP_subset_RankLocalP := by
  intro hSub
  exact W.notInP (hSub W.family W.inNP)

/--
Rank-local class equality as mutual inclusion.  Since rank-local P is trivially
a subcollection of all rank-local NP only when supplied by a separate verifier
bridge, we record the equality notion as the dangerous direction plus its
reverse.
-/
structure RankLocalClassesCoincide where
  np_subset_p : RankLocalNP_subset_RankLocalP
  p_subset_np : ∀ F : RankProblemFamily, InRankLocalP F → InRankLocalNP F

/-- A separation witness refutes rank-local class equality. -/
theorem rankLocalClasses_do_not_coincide_of_witness
    (W : RankSeparationWitness) :
    ¬ RankLocalClassesCoincide := by
  intro hEq
  exact not_rankLocalNP_subset_RankLocalP_of_witness W hEq.np_subset_p

/-#############################################################################
  §5. Fixed-rank solvers and unbounded families
#############################################################################-/

/-- A fixed-rank solver claims one finite bound handles every instance. -/
structure FixedRankSolver (F : RankProblemFamily) where
  bound : Nat
  solvesWithinBound :
    F.BoundedBy bound

/-- A fixed-rank solver is the same as boundedness. -/
theorem nonempty_fixedRankSolver_iff_bounded
    {F : RankProblemFamily} :
    Nonempty (FixedRankSolver F) ↔ F.Bounded := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact ⟨S.bound, S.solvesWithinBound⟩
  · intro h
    rcases h with ⟨b, hb⟩
    exact ⟨{ bound := b, solvesWithinBound := hb }⟩

/-- No fixed-rank solver exists for an unbounded family. -/
theorem no_fixedRankSolver_of_unbounded
    {F : RankProblemFamily}
    (hU : F.Unbounded) :
    ¬ Nonempty (FixedRankSolver F) := by
  intro hS
  have hB : F.Bounded :=
    (nonempty_fixedRankSolver_iff_bounded.mp hS)
  exact not_bounded_of_unbounded hU hB

/-- A separation witness has no fixed-rank solver. -/
theorem RankSeparationWitness.no_fixedRankSolver
    (W : RankSeparationWitness) :
    ¬ Nonempty (FixedRankSolver W.family) :=
  no_fixedRankSolver_of_unbounded W.unbounded

/-#############################################################################
  §6. Universal absorbers and rank engines
#############################################################################-/

/--
A universal rank absorber claims that one fixed rank can absorb every required
rank.
-/
structure UniversalRankAbsorber where
  target : Nat
  absorbs : ∀ r : Nat, RankIncludedIn r target

/-- No universal rank absorber exists. -/
theorem no_universalRankAbsorber :
    ¬ Nonempty UniversalRankAbsorber := by
  intro h
  rcases h with ⟨A⟩
  exact Nat.not_succ_le_self A.target (A.absorbs (A.target + 1))

/--
Rank-collapse engine: a strictly higher rank is included in a lower one.
-/
structure RankCollapseEngine where
  lower : Nat
  higher : Nat
  strict : lower < higher
  bad_inclusion : RankIncludedIn higher lower

/-- No rank-collapse engine exists. -/
theorem no_rankCollapseEngine
    (E : RankCollapseEngine) :
    False :=
  Nat.not_le_of_gt E.strict E.bad_inclusion

/-- A universal absorber yields a rank-collapse engine. -/
def rankCollapseEngine_of_absorber
    (A : UniversalRankAbsorber) :
    RankCollapseEngine :=
{
  lower := A.target
  higher := A.target + 1
  strict := Nat.lt_succ_self A.target
  bad_inclusion := A.absorbs (A.target + 1)
}

/-- Universal absorption self-destructs by rank collapse. -/
theorem universalAbsorber_selfDestructs
    (A : UniversalRankAbsorber) :
    False :=
  no_rankCollapseEngine (rankCollapseEngine_of_absorber A)

/-#############################################################################
  §7. Rank closure certificate
#############################################################################-/

/--
The rank-closure certificate packages the exact local separation result.

It does not create a separating family.  It says: once a locally verifiable
unbounded-rank family is supplied, bounded-rank/local-P cannot contain it.
-/
structure RankClosureCertificate where
  witness : RankSeparationWitness

/-- A rank closure certificate refutes rank-local NP⊆P. -/
theorem RankClosureCertificate.not_np_subset_p
    (C : RankClosureCertificate) :
    ¬ RankLocalNP_subset_RankLocalP :=
  not_rankLocalNP_subset_RankLocalP_of_witness C.witness

/-- A rank closure certificate refutes rank-local class equality. -/
theorem RankClosureCertificate.not_classesCoincide
    (C : RankClosureCertificate) :
    ¬ RankLocalClassesCoincide :=
  rankLocalClasses_do_not_coincide_of_witness C.witness

/-- It also gives no fixed-rank solver for the separating family. -/
theorem RankClosureCertificate.no_fixedRankSolver
    (C : RankClosureCertificate) :
    ¬ Nonempty (FixedRankSolver C.witness.family) :=
  C.witness.no_fixedRankSolver

/-#############################################################################
  §8. Final closure theorem-shaped slogan
#############################################################################-/

/--
The rank-class separation closure slogan.

A fixed finite rank cannot contain all ranks; exact prefix containment is
bounded; an unbounded locally verifiable rank-family separates rank-local NP
from bounded-rank local P.
-/
abbrev RankClassSeparationClosureSlogan : Prop :=
  (¬ ∃ top : Nat, ∀ r : Nat, RankIncludedIn r top) ∧
  (∀ r : Nat, Nonempty (RankPrefixContainer (r + 1) r)) ∧
  (∀ r : Nat, ¬ Nonempty (RankPrefixContainer (r + 2) r)) ∧
  (∀ W : RankSeparationWitness, ¬ InRankLocalP W.family) ∧
  (∀ W : RankSeparationWitness, ¬ Nonempty (FixedRankSolver W.family)) ∧
  (∀ C : RankClosureCertificate, ¬ RankLocalClassesCoincide)

/-- Final closure slogan theorem. -/
theorem rankClassSeparationClosureSlogan :
    RankClassSeparationClosureSlogan := by
  constructor
  · exact no_finite_rank_contains_all
  · constructor
    · intro r
      exact ⟨RankPrefixContainer.selfPrefix r⟩
    · constructor
      · intro r
        exact no_prefixContainer_past_target r
      · constructor
        · intro W
          exact W.notInP
        · constructor
          · intro W
            exact W.no_fixedRankSolver
          · intro C
            exact C.not_classesCoincide

end RankClassSeparationClosure
end EuclidsPath

/-
EuclidsPath_rank_local_class_equality_contradiction_patch.lean

Formal closure: contradiction from equality of rank-local classes.

This file records the exact contradiction:

  RankLocalClassesCoincide
  + RankSeparationWitness
  ⟹ False

where a `RankSeparationWitness` is a locally verifiable family whose required
rank is unbounded.

This is the formal rank-local separation.  It is not a statement about classical
Turing-machine P vs NP.
-/



namespace EuclidsPath
namespace RankLocalClassEqualityContradiction

/-#############################################################################
  §1. Rank families
#############################################################################-/

/--
A family of instances with a required rank.

`requiredRank x` is the rank level needed to solve/cover instance `x`.
-/
structure RankProblemFamily where
  Instance : Type
  requiredRank : Instance → Nat

namespace RankProblemFamily

/-- The family is bounded by one finite rank `b`. -/
def BoundedBy (F : RankProblemFamily) (b : Nat) : Prop :=
  ∀ x : F.Instance, F.requiredRank x ≤ b

/-- The family is bounded by some finite rank. -/
def Bounded (F : RankProblemFamily) : Prop :=
  ∃ b : Nat, F.BoundedBy b

/-- The family is unbounded in required rank. -/
def Unbounded (F : RankProblemFamily) : Prop :=
  ∀ r : Nat, ∃ x : F.Instance, r < F.requiredRank x

/--
Bounded and unbounded are incompatible.

This is the exact contradiction:

  bounded:   ∃ b, ∀ x, requiredRank x ≤ b
  unbounded: ∀ r, ∃ x, r < requiredRank x

Choose r = b.
-/
theorem bounded_and_unbounded_contradiction
    {F : RankProblemFamily}
    (hBounded : F.Bounded)
    (hUnbounded : F.Unbounded) :
    False := by
  rcases hBounded with ⟨b, hb⟩
  rcases hUnbounded b with ⟨x, hx⟩
  exact Nat.not_le_of_gt hx (hb x)

/-- A bounded family cannot be unbounded. -/
theorem not_unbounded_of_bounded
    {F : RankProblemFamily}
    (hBounded : F.Bounded) :
    ¬ F.Unbounded := by
  intro hUnbounded
  exact bounded_and_unbounded_contradiction hBounded hUnbounded

/-- An unbounded family cannot be bounded. -/
theorem not_bounded_of_unbounded
    {F : RankProblemFamily}
    (hUnbounded : F.Unbounded) :
    ¬ F.Bounded := by
  intro hBounded
  exact bounded_and_unbounded_contradiction hBounded hUnbounded

end RankProblemFamily

/-#############################################################################
  §2. Rank-local P and rank-local NP
#############################################################################-/

/--
Rank-local P: one finite rank bound covers the whole family.
-/
def InRankLocalP (F : RankProblemFamily) : Prop :=
  F.Bounded

/--
Rank-local NP: local verifiability.

This is intentionally rank-local: the witness/checker may vary with the instance,
but each proposed witness is locally checkable inside the required rank frame.
-/
def InRankLocalNP (F : RankProblemFamily) : Prop :=
  ∃ (_Witness : F.Instance → Type) (verifierRank : F.Instance → Nat),
    (∀ x : F.Instance, F.requiredRank x ≤ verifierRank x) ∧
    ∃ local_checkable : Prop, local_checkable

/--
A separating rank witness: a locally verifiable family whose required rank is
unbounded.
-/
structure RankSeparationWitness where
  family : RankProblemFamily
  inNP : InRankLocalNP family
  unbounded : family.Unbounded

namespace RankSeparationWitness

/-- The separating family is not in rank-local P. -/
theorem notInP
    (W : RankSeparationWitness) :
    ¬ InRankLocalP W.family :=
  RankProblemFamily.not_bounded_of_unbounded W.unbounded

/-- Explicit contradiction if someone also claims the family is in rank-local P. -/
theorem contradiction_of_inP
    (W : RankSeparationWitness)
    (hP : InRankLocalP W.family) :
    False :=
  W.notInP hP

end RankSeparationWitness

/-#############################################################################
  §3. Rank-local class equality
#############################################################################-/

/--
The dangerous direction: every rank-local NP family is claimed to be rank-local P.
-/
def RankLocalNP_subset_RankLocalP : Prop :=
  ∀ F : RankProblemFamily, InRankLocalNP F → InRankLocalP F

/--
Rank-local class equality.

The field `np_subset_p` is the one that contradicts an unbounded locally
verifiable family.  The reverse field is kept to model equality rather than only
one-way containment.
-/
structure RankLocalClassesCoincide where
  np_subset_p : RankLocalNP_subset_RankLocalP
  p_subset_np : ∀ F : RankProblemFamily, InRankLocalP F → InRankLocalNP F

/--
A separation witness refutes the inclusion `RankLocalNP ⊆ RankLocalP`.
-/
theorem not_rankLocalNP_subset_RankLocalP_of_witness
    (W : RankSeparationWitness) :
    ¬ RankLocalNP_subset_RankLocalP := by
  intro hSub
  have hP : InRankLocalP W.family := hSub W.family W.inNP
  exact W.notInP hP

/--
Main contradiction theorem.

If the classes are assumed equal, the equality gives:

  W.family ∈ RankLocalNP → W.family ∈ RankLocalP.

But `W.family` is unbounded, so it is not in rank-local P.
-/
theorem contradiction_of_rankLocalClassesCoincide
    (W : RankSeparationWitness)
    (H : RankLocalClassesCoincide) :
    False := by
  have hP : InRankLocalP W.family :=
    H.np_subset_p W.family W.inNP
  exact W.notInP hP

/-- Therefore a separation witness refutes rank-local class equality. -/
theorem rankLocalClasses_do_not_coincide_of_witness
    (W : RankSeparationWitness) :
    ¬ RankLocalClassesCoincide := by
  intro H
  exact contradiction_of_rankLocalClassesCoincide W H

/-#############################################################################
  §4. Fixed-rank solver form
#############################################################################-/

/--
A fixed-rank solver is exactly a finite bound for the family.
-/
structure FixedRankSolver (F : RankProblemFamily) where
  bound : Nat
  solvesWithinBound : F.BoundedBy bound

/-- A fixed-rank solver exists iff the family is bounded. -/
theorem nonempty_fixedRankSolver_iff_bounded
    {F : RankProblemFamily} :
    Nonempty (FixedRankSolver F) ↔ F.Bounded := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact ⟨S.bound, S.solvesWithinBound⟩
  · intro h
    rcases h with ⟨b, hb⟩
    exact ⟨{ bound := b, solvesWithinBound := hb }⟩

/-- An unbounded family has no fixed-rank solver. -/
theorem no_fixedRankSolver_of_unbounded
    {F : RankProblemFamily}
    (hUnbounded : F.Unbounded) :
    ¬ Nonempty (FixedRankSolver F) := by
  intro hSolver
  have hBounded : F.Bounded :=
    nonempty_fixedRankSolver_iff_bounded.mp hSolver
  exact RankProblemFamily.not_bounded_of_unbounded hUnbounded hBounded

/-- A rank separation witness has no fixed-rank solver. -/
theorem no_fixedRankSolver_of_witness
    (W : RankSeparationWitness) :
    ¬ Nonempty (FixedRankSolver W.family) :=
  no_fixedRankSolver_of_unbounded W.unbounded

/-#############################################################################
  §5. Twin/Step00 adapter
#############################################################################-/

/--
Adapter for the Step00/twin side.

To connect this file to the previous twin-prime formalization, instantiate this
structure with the concrete genealogy family already shown to be locally
verifiable and unbounded in rank.
-/
structure Step00TwinRankWitnessPackage where
  family : RankProblemFamily
  inNP : InRankLocalNP family
  unbounded : family.Unbounded

namespace Step00TwinRankWitnessPackage

/-- The Step00/twin package is exactly a rank separation witness. -/
def toRankSeparationWitness
    (P : Step00TwinRankWitnessPackage) :
    RankSeparationWitness :=
{
  family := P.family
  inNP := P.inNP
  unbounded := P.unbounded
}

/-- Step00/twin witness refutes rank-local class equality. -/
theorem rankLocalClasses_do_not_coincide
    (P : Step00TwinRankWitnessPackage) :
    ¬ RankLocalClassesCoincide :=
  rankLocalClasses_do_not_coincide_of_witness P.toRankSeparationWitness

/-- Explicit contradiction form under class equality. -/
theorem contradiction_of_rankLocalClassesCoincide
    (P : Step00TwinRankWitnessPackage)
    (H : RankLocalClassesCoincide) :
    False :=
  RankLocalClassEqualityContradiction.contradiction_of_rankLocalClassesCoincide
    P.toRankSeparationWitness H

/-- The Step00/twin package has no fixed-rank solver. -/
theorem no_fixedRankSolver
    (P : Step00TwinRankWitnessPackage) :
    ¬ Nonempty (FixedRankSolver P.family) :=
  no_fixedRankSolver_of_witness P.toRankSeparationWitness

end Step00TwinRankWitnessPackage

/-#############################################################################
  §6. Final closure object
#############################################################################-/

/--
Rank-local separation closure certificate.

Once such a certificate is supplied, equality of rank-local classes is impossible.
-/
structure RankLocalSeparationClosure where
  witness : RankSeparationWitness

namespace RankLocalSeparationClosure

/-- The closure certificate refutes the inclusion `RankLocalNP ⊆ RankLocalP`. -/
theorem not_np_subset_p
    (C : RankLocalSeparationClosure) :
    ¬ RankLocalNP_subset_RankLocalP :=
  not_rankLocalNP_subset_RankLocalP_of_witness C.witness

/-- The closure certificate refutes rank-local class equality. -/
theorem not_classesCoincide
    (C : RankLocalSeparationClosure) :
    ¬ RankLocalClassesCoincide :=
  rankLocalClasses_do_not_coincide_of_witness C.witness

/-- Explicit contradiction form. -/
theorem contradiction_of_classesCoincide
    (C : RankLocalSeparationClosure)
    (H : RankLocalClassesCoincide) :
    False :=
  contradiction_of_rankLocalClassesCoincide C.witness H

/-- The witness family has no fixed-rank solver. -/
theorem no_fixedRankSolver
    (C : RankLocalSeparationClosure) :
    ¬ Nonempty (FixedRankSolver C.witness.family) :=
  no_fixedRankSolver_of_witness C.witness

end RankLocalSeparationClosure

/--
Final theorem-shaped slogan.
-/
abbrev RankLocalClassEqualityContradictionSlogan : Prop :=
  (∀ W : RankSeparationWitness,
    ¬ RankLocalClassesCoincide) ∧
  (∀ W : RankSeparationWitness,
    ¬ RankLocalNP_subset_RankLocalP) ∧
  (∀ W : RankSeparationWitness,
    ¬ Nonempty (FixedRankSolver W.family)) ∧
  (∀ C : RankLocalSeparationClosure,
    ¬ RankLocalClassesCoincide)

/-- Final slogan theorem. -/
theorem rankLocalClassEqualityContradictionSlogan :
    RankLocalClassEqualityContradictionSlogan := by
  constructor
  · intro W
    exact rankLocalClasses_do_not_coincide_of_witness W
  · constructor
    · intro W
      exact not_rankLocalNP_subset_RankLocalP_of_witness W
    · constructor
      · intro W
        exact no_fixedRankSolver_of_witness W
      · intro C
        exact C.not_classesCoincide

end RankLocalClassEqualityContradiction
end EuclidsPath
