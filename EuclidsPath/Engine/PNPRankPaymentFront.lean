/-
  PNPRankPaymentFront — the GREEN (axiom-free) module for the author's P/NP
  reading: «an NP-problem = FULL PAYMENT of all rank certificates; P = the
  engine's motion, quickly traversing the rank WITHOUT visiting every state» —
  and the inequality between them AS A THEOREM under the standard axioms.

  Architecture:
    * P-side: `RankFastTraversal` — every legal motion is bounded by the
      STARTING rank (a law of every ranked graph, `len_le_lexRank`);
    * NP-side: `FullRankCertificatePayment` — the search is solved only when
      EVERY certificate of the family is accounted for by an injective finite key;
    * HEART (L5): a rank-fast finite-key motion cannot fully pay an unbounded
      family of certificates — pigeonhole;
    * PAYMENT DICHOTOMY (L8/L9): LocalPSuccess ⟺ FullRankCertificatePayment at
      EVERY scale — both resolution alternatives burnt green
      (`no_extendedFlowResolutionAlternative`), «NP = full payment» — a theorem;
    * GREEN SEPARATION (L10, A ≤ 4): fast traversal ∧ easy verification ∧
      unbounded supply (5-adics) ∧ ¬full payment ∧ incompressibility.

  SPLIT BY SCALES (machine-wise, L14–L16): the accepted causal boundary
  (`TheStrictLastStep00Obligation`, as a HYPOTHESIS — the module does NOT import
  the quarantine) on its own scale A ≥ 5 gives LocalPSuccess on every M0 — there
  the decree PAYS all certificates and bounds the supply; the separation lives on
  A ≤ 4.
  INVERTED ASYMMETRY against Riemann (disclosed, not forged): the separation does
  NOT need the boundary — the killer is green; the unused hBoundary in essence has
  NOT been added.

  HONESTY (machine-wise, mandatory audits):
    * TRILEMMA of candidates for «the third boundary of the decree» — all
      verdicts theorems: V1 universal form REFUTABLE (allPFrame — the decree
      would be inconsistent); V3 decider-gated form REFUTABLE (PDecider is
      classically free); V2 existential form ALREADY PROVEN (constantsFrame —
      the decree would be vacuous). An honest third field DOES NOT EXIST; what is
      genuinely missing is a data-anchored real machine model (the lesson of
      SpectralAnchorAudit: Prop-non-vacuity is the wrong criterion).
    * VACUITY №4 (EXPOSED, A3–A5): the decider-gated extraction fronts of the
      EXISTING code (`FaithfulSelfReductionFront`, `CurrentExtractionFront`) are
      classically EMPTY — `PDecider` carries no complexity-content and is built
      classically for any language, so the link «extraction + incompressibility»
      is uninhabited; their `gives_classicalSeparation` are vacuous. The InP-gated
      bridge (`Step00ToClassicalBridge`) is NOT affected — InP is abstract.
    * PLASTICITY OF FRAMES (A6/A7): `allPFrame` faithful + the classes coincide
      for free; `constantsFrame` faithful + P⊆NP + separates for free — the
      abstract frame layer forges in any direction; no statement about the REAL
      P/NP follows from here and is NOT declared.
  This module does NOT import the quarantine; there are no axiom/sorry — the
  verifier is obliged to show all declarations untainted.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.LocalPNPNode
import EuclidsPath.Engine.CanonicalSelfReduction

set_option autoImplicit false

namespace EuclidsPath
namespace PNPRankPayment

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.LocalPNP
open EuclidsPath.LocalPNP.Concrete
open EuclidsPath.ClassicalPNPBridge
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction.CanonicalSelfReduction

-- Do NOT open ConcreteStep00Graph.PvsNPAnalogy: name collisions
-- (PolyCertificateSuffices, VerificationEasy) with LocalPNP.

/-#############################################################################
  §1. The author's language: certificate payment and rank-fast traversal
#############################################################################-/

/-- **D1. FULL PAYMENT OF RANK CERTIFICATES (NP-reading):** the search is
    solved only when EVERY certificate of the family is accounted for
    individually — an injective finite-key compression of the whole family of
    genealogies. -/
def FullRankCertificatePayment {G : RankedForwardGraph}
    (F : GenealogyFamily G) : Prop :=
  ∃ C : FiniteKeyCompression F, C.Injective

/-- **D2. RANK-FAST TRAVERSAL (P-reading):** every legal motion of the engine
    is bounded by the STARTING rank — the engine traverses the rank without
    visiting every state. -/
def RankFastTraversal (G : RankedForwardGraph) : Prop :=
  ∀ (x y : G.State) (n : Nat), PathN G x y n → n ≤ G.lexRank x

/-- **D3. Unbounded certificate supply:** the family of genealogies is
    infinite. -/
def UnboundedCertificateSupply {G : RankedForwardGraph}
    (F : GenealogyFamily G) : Prop :=
  Infinite F.Index

/-#############################################################################
  §2. Green witnesses: the P-law, easy verification, pigeonhole
#############################################################################-/

/-- **L1: rank-fast traversal — a LAW of every ranked graph**
    (`PathN.len_le_lexRank`). -/
theorem rankFastTraversal_holds (G : RankedForwardGraph) : RankFastTraversal G :=
  fun _ _ _ p => p.len_le_lexRank

/-- **L2: the concrete Step00-graph traverses the rank fast.** -/
theorem concrete_rankFastTraversal (A M0 : ℕ) :
    RankFastTraversal (concreteGraph A M0) :=
  rankFastTraversal_holds _

/-- **L3: checking ONE certificate is always easy** — the verification side. -/
theorem certificate_check_easy {G : RankedForwardGraph}
    (c : GenealogyCertificate G) : GenealogyCertificate.VerificationEasy c :=
  GenealogyCertificate.verificationEasy_always c

/-- **L4: unbounded supply ⟹ pigeonhole principle** — every finite key
    collides. -/
theorem collisionPrinciple_of_unboundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} (hInf : UnboundedCertificateSupply F) :
    FiniteKeyCollisionPrinciple F := by
  intro C
  haveI : Infinite F.Index := hInf
  obtain ⟨i, j, hne, hkey⟩ := Finite.exists_ne_map_eq_of_infinite C.keyOf
  exact ⟨⟨i, j, hne, hkey⟩⟩

/-- **L5 — HEART OF THE INEQUALITY (abstract):** a rank-fast finite-key motion
    CANNOT fully pay an unbounded family of certificates — pigeonhole. -/
theorem no_fullPayment_of_unboundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} (hInf : UnboundedCertificateSupply F) :
    ¬ FullRankCertificatePayment F := by
  rintro ⟨C, hInj⟩
  exact no_injective_finiteKeyCompression_of_collisionPrinciple
    (collisionPrinciple_of_unboundedSupply hInf) C hInj

/-- **L6: the concrete supply is UNBOUNDED for A ≤ 4** — a 5-adic chain,
    without a single twin-hypothesis. -/
theorem concreteSupply_unbounded_smallScale {A : ℕ} (hA : A ≤ 4) :
    UnboundedCertificateSupply (concreteFamily A 1) :=
  Infinite.of_injective (fiveAdicChainFlow hA) (fiveAdicChainFlow_injective hA)

/-- **L7: full payment of the concrete family for A ≤ 4 is IMPOSSIBLE.** -/
theorem concrete_noFullPayment_smallScale {A : ℕ} (hA : A ≤ 4) :
    ¬ FullRankCertificatePayment (concreteFamily A 1) :=
  no_fullPayment_of_unboundedSupply (concreteSupply_unbounded_smallScale hA)

/-#############################################################################
  §3. Payment dichotomy: «NP = full payment» as a theorem
#############################################################################-/

/-- **L8 (abstract): when there are NO resolution alternatives, local P-success
    IS full payment** — the finite key is obliged to account for every
    certificate injectively. -/
theorem localPSuccess_iff_fullPayment_of_noResolution {G : RankedForwardGraph}
    {P : Step00LocalSearchProblem G}
    (hNoRes : ∀ i j : P.family.Index, ¬ P.CollisionResolution i j) :
    LocalPSuccess P ↔ FullRankCertificatePayment P.family := by
  constructor
  · rintro ⟨S⟩
    refine ⟨S.compression, ?_⟩
    intro i j hkey
    by_contra hne
    exact hNoRes i j (S.resolves hne hkey)
  · rintro ⟨C, hInj⟩
    exact ⟨{ compression := C
             resolves := fun {i j} hne hkey => absurd (hInj hkey) hne }⟩

/-- **L9 (concrete, EVERY scale):** in the Step00-world both resolution
    alternatives (a legal cycle, impossible payment) are burnt green
    (`no_extendedFlowResolutionAlternative`) — so local P-success ⟺ full payment
    of certificates. «An NP-problem = full payment» — a theorem. -/
theorem concrete_localPSuccess_iff_fullPayment (A M0 : ℕ) :
    LocalPSuccess (concreteProblem A M0) ↔
      FullRankCertificatePayment (concreteFamily A M0) :=
  localPSuccess_iff_fullPayment_of_noResolution
    (fun _ _ => no_extendedFlowResolutionAlternative A M0)

/-#############################################################################
  §4. GREEN SEPARATION in the rank model
#############################################################################-/

/-- **L10 — GREEN SEPARATION (the strongest unconditional form, A ≤ 4):**
    the engine traverses the rank fast; each certificate is verified easily;
    the certificate supply is unbounded; full payment is impossible; so the
    rank-fast searcher fails — the local search is incompressible.
    The author's inequality in a single theorem, under the standard axioms. -/
theorem pnp_rank_separation_smallScale {A : ℕ} (hA : A ≤ 4) :
    RankFastTraversal (concreteGraph A 1) ∧
    (∀ i : (concreteFamily A 1).Index,
      GenealogyCertificate.VerificationEasy ((concreteFamily A 1).cert i)) ∧
    UnboundedCertificateSupply (concreteFamily A 1) ∧
    ¬ FullRankCertificatePayment (concreteFamily A 1) ∧
    LocalSearchIncompressible (concreteProblem A 1) :=
  ⟨concrete_rankFastTraversal A 1,
   fun _ => GenealogyCertificate.verificationEasy_always _,
   concreteSupply_unbounded_smallScale hA,
   concrete_noFullPayment_smallScale hA,
   fun hP => concrete_noFullPayment_smallScale hA
     ((concrete_localPSuccess_iff_fullPayment A 1).mp hP)⟩

/-- **L11 (scale-uniform, conditional):** unbounded supply ⟹
    incompressibility — at ANY scale. -/
theorem localSearchIncompressible_of_unboundedSupply (A M0 : ℕ)
    (hInf : UnboundedCertificateSupply (concreteFamily A M0)) :
    LocalSearchIncompressible (concreteProblem A M0) :=
  fun hP => no_fullPayment_of_unboundedSupply hInf
    ((concrete_localPSuccess_iff_fullPayment A M0).mp hP)

/-- **L12: twin-bound ⟹ unbounded supply** — at any scale
    (the closed flow factory). -/
theorem concreteSupply_unbounded_of_twinBound {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0) :
    UnboundedCertificateSupply (concreteFamily A M0) := by
  obtain ⟨𝓕, h𝓕⟩ := twinBoundForcesInfiniteExtendedGeneratedFlows_closed
    (A := A) (M0 := M0) hTwinBound
  haveI := h𝓕.1.to_subtype
  exact Infinite.of_injective (Subtype.val : 𝓕 → _) Subtype.val_injective

/-- **L13 (green dichotomy at every scale):** EITHER a twin above M0,
    OR full payment is impossible. -/
theorem twin_or_noFullPayment (A M0 : ℕ) :
    (∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m) ∨
    ¬ FullRankCertificatePayment (concreteFamily A M0) := by
  by_cases h : ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m
  · exact Or.inl h
  · refine Or.inr (no_fullPayment_of_unboundedSupply
      (concreteSupply_unbounded_of_twinBound ?_))
    intro m hm hTwin
    exact h ⟨m, hm, hTwin⟩

/-#############################################################################
  §5. Split by scales (the boundary as a HYPOTHESIS — machine-visible)
#############################################################################-/

/-- **L14: the accepted boundary gives LOCAL P-SUCCESS on its own scale**
    (necessarily A ≥ 5) on every M0 — the decree and the small scale live on
    disjoint scales. -/
theorem boundary_forces_localPSuccess_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ, LocalPSuccess (concreteProblem A M0) := by
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hA : 5 ≤ A := by
    by_contra hlt
    exact no_projection_resolves_at_smallScale (by omega) (projOf 1)
      (strictSemanticExtended_resolves_old (hres 1))
  refine ⟨A, hA, fun M0 => ?_⟩
  exact ((concreteSemanticInterface A M0).localPSuccess_iff_semanticFlowLedgerCollisionResolves).mpr
    ⟨projOf M0, strictSemanticExtended_resolves_old (hres M0)⟩

/-- **L15: on the decreed scale the boundary PAYS ALL CERTIFICATES.** -/
theorem boundary_forces_fullPayment_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      FullRankCertificatePayment (concreteFamily A M0) := by
  obtain ⟨A, hA, hLP⟩ := boundary_forces_localPSuccess_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 =>
    (concrete_localPSuccess_iff_fullPayment A M0).mp (hLP M0)⟩

/-- **L16: on the decreed scale the certificate supply is BOUNDED** — the books
    there reconcile, because the supply is finite-key accountable. -/
theorem boundary_bounds_supply_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      ¬ UnboundedCertificateSupply (concreteFamily A M0) := by
  obtain ⟨A, hA, hPay⟩ := boundary_forces_fullPayment_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 hInf => no_fullPayment_of_unboundedSupply hInf (hPay M0)⟩

/-#############################################################################
  §6. The classical honesty block: PDecider is free, the fronts are empty,
      the frames are plastic
#############################################################################-/

/-- **A1 (finding): `PDecider` is classically FREE** — an extensional decider
    exists for every language; there is no complexity-content in it, all the
    complexity lives in the abstract InP. -/
noncomputable def classicalPDecider (L : ClassicalProblem) : PDecider L := by
  classical
  exact
    { run := fun x => decide (L.Accepts x)
      sound := fun x hx => of_decide_eq_true hx
      complete := fun x hx => decide_eq_true hx }

theorem pdecider_free (L : ClassicalProblem) : Nonempty (PDecider L) :=
  ⟨classicalPDecider L⟩

/-- **A2: `ConcretePAccess` is free** — this leg of the extraction field is contentless. -/
theorem concretePAccess_free (C : ClassicalComplexityFrame) :
    Nonempty (ConcretePAccess C) :=
  ⟨⟨fun L _ => ⟨classicalPDecider L⟩⟩⟩

/-- **A3 (VACUITY №4, core):** over an incompressible node there is NO
    `CanonicalResolverReconstruction` — a free decider would immediately give
    LocalPSuccess. -/
theorem isEmpty_canonicalResolverReconstruction_of_incompressible
    {N : Step00LocalNode} (hInc : N.LocalSearchIncompressible)
    (L : ClassicalProblem) (Target : LocalResolverTarget N) :
    IsEmpty (CanonicalResolverReconstruction L Target) :=
  ⟨fun R => hInc (Target.realizes (R.reconstruct (classicalPDecider L)))⟩

/-- **A4: the same for `DeciderGuidedSelfReduction`.** -/
theorem isEmpty_deciderGuidedSelfReduction_of_incompressible
    {N : Step00LocalNode} (hInc : N.LocalSearchIncompressible)
    (L : ClassicalProblem) (Target : LocalResolverTarget N) :
    IsEmpty (DeciderGuidedSelfReduction L Target) :=
  ⟨fun S => hInc (S.localSuccessOfDecider (classicalPDecider L))⟩

/-- **A5 (VACUITY №4, disclosure about an EXISTING front):**
    `FaithfulSelfReductionFront` links decider-gated extraction WITH
    incompressibility — classically EMPTY for any frame and node; its
    `gives_classicalSeparation` is vacuous. -/
theorem faithfulSelfReductionFront_isEmpty
    (C : ClassicalComplexityFrame) (N : Step00LocalNode) :
    IsEmpty (FaithfulSelfReductionFront C N) :=
  ⟨fun F => F.local_incompressible
    (F.selfReduction.localSuccessOfDecider
      (classicalPDecider F.encoding.genealogyLanguage))⟩

/-- **A5b: `CurrentExtractionFront` is empty for the same reason.** -/
theorem currentExtractionFront_isEmpty
    (C : ClassicalComplexityFrame) (N : Step00LocalNode) :
    IsEmpty (CurrentExtractionFront C N) :=
  ⟨fun F => F.local_incompressible
    (F.strictEncoding.extraction.target.realizes
      (F.strictEncoding.extraction.reconstruction.reconstruct
        (classicalPDecider F.strictEncoding.encoding.genealogyLanguage)))⟩

/-- **A6 (plasticity of frames, the «coincide» side):** the «everything in P»
    frame is faithful by the repository's criterion, and the classes in it
    COINCIDE for free. -/
def allPFrame : ClassicalComplexityFrame where
  InP := fun _ => True
  InNP := fun _ => True
  P_closed_under_poly_preimage := fun _ _ => trivial

theorem allPFrame_faithful : Nonempty (FaithfulPFrame allPFrame) :=
  ⟨{ concreteP := ⟨fun L _ => ⟨classicalPDecider L⟩⟩
     true_inP := trivial
     false_inP := trivial }⟩

theorem allPFrame_coincides : allPFrame.ClassesCoincide := fun _ => Iff.rfl

/-- A universal «faithful ⟹ separation» does NOT exist — machine-wise. -/
theorem no_universal_faithful_separation :
    ¬ ∀ C : ClassicalComplexityFrame,
        Nonempty (FaithfulPFrame C) → C.ClassesSeparate := by
  intro h
  rcases h allPFrame allPFrame_faithful with ⟨L, _, hNotP⟩
  exact hNotP trivial

/-- **A7 (plasticity, the «separate» side):** the constants frame is faithful,
    P ⊆ NP, and it SEPARATES for free. -/
def constantsFrame : ClassicalComplexityFrame where
  InP := fun L => (∀ x : L.Instance, L.Accepts x) ∨ (∀ x : L.Instance, ¬ L.Accepts x)
  InNP := fun _ => True
  P_closed_under_poly_preimage := by
    intro A B R hB
    rcases hB with hAll | hNone
    · exact Or.inl (fun x => (R.preserves x).mpr (hAll (R.map x)))
    · exact Or.inr (fun x hx => hNone (R.map x) ((R.preserves x).mp hx))

theorem constantsFrame_faithful : Nonempty (FaithfulPFrame constantsFrame) :=
  ⟨{ concreteP := ⟨fun L _ => ⟨classicalPDecider L⟩⟩
     true_inP := Or.inl (fun _ => trivial)
     false_inP := Or.inr (fun _ h => h) }⟩

/-- A non-constant witness language. -/
def boolLanguage : ClassicalProblem := ⟨Bool, fun b => b = true⟩

theorem boolLanguage_not_inP_constantsFrame :
    ¬ constantsFrame.InP boolLanguage := by
  rintro (h | h)
  · exact Bool.false_ne_true (h false)
  · exact h true rfl

theorem some_faithful_frame_separates_greenly :
    ∃ C : ClassicalComplexityFrame, Nonempty (FaithfulPFrame C) ∧
      (∀ L, C.InP L → C.InNP L) ∧ C.ClassesSeparate :=
  ⟨constantsFrame, constantsFrame_faithful, fun _ _ => trivial,
   ⟨boolLanguage, trivial, boolLanguage_not_inP_constantsFrame⟩⟩

/-- **A8: the condemnation of trivialFrame is instantiated** — the freely
    separating frame does not pass the faithfulness gate. -/
theorem trivialFrame_blocked :
    ¬ Nonempty (FaithfulPFrame ClassicalPNPBridge.trivialFrame) :=
  fun ⟨F⟩ => trivialFrame_not_faithful F

/-#############################################################################
  §7. TRILEMMA of candidates for «the third boundary of the decree» — all verdicts machine-wise
#############################################################################-/

/-- **D5a. CANDIDATE 1 (universal form):** in every faithful frame the small
    scale manifests as an NP-language whose P-decider would extract a local
    resolver. -/
def PnpManifestationLawUniversal : Prop :=
  ∀ C : ClassicalComplexityFrame, Nonempty (FaithfulPFrame C) →
    ∀ A : ℕ, A ≤ 4 →
      ∃ L : ClassicalProblem, C.InNP L ∧
        (C.InP L → LocalPSuccess (concreteProblem A 1))

/-- **D5b. CANDIDATE 2 (existential form):** SOME faithful frame with
    P ⊆ NP carries a manifestation. -/
def PnpManifestationLawExistential : Prop :=
  ∃ C : ClassicalComplexityFrame,
    Nonempty (FaithfulPFrame C) ∧ (∀ L, C.InP L → C.InNP L) ∧
    ∀ A : ℕ, A ≤ 4 →
      ∃ L : ClassicalProblem, C.InNP L ∧
        (C.InP L → LocalPSuccess (concreteProblem A 1))

/-- A concrete resolver target (an instantiation of LocalResolverTarget). The
    resolver is a Type-0 wrapper of local P-success (`PolyCertificateSuffices`
    lives in Type 1 and does not fit into the field `Resolver : Type` — a PLift
    of the Prop-success honestly preserves the semantics: the resolver = a
    witness of the resolving key). -/
def concreteResolverTarget (A M0 : ℕ) :
    LocalResolverTarget (ClassicalPNPBridge.concreteNode A M0) where
  Resolver := PLift (LocalPSuccess (concreteProblem A M0))
  realizes := fun S => S.down
  finite_key_sound := fun _ => True
  finite_key_sound_proof := fun _ => trivial
  rank_bounded := fun _ => True
  rank_bounded_proof := fun _ => trivial
  collision_sound := fun _ => True
  collision_sound_proof := fun _ => trivial

/-- **D5c. CANDIDATE 3 (decider-gated form):** reconstruction from bare
    deciders. -/
def PnpManifestationLawDeciderGated : Prop :=
  ∀ A : ℕ, A ≤ 4 →
    ∃ L : ClassicalProblem,
      Nonempty (CanonicalResolverReconstruction L (concreteResolverTarget A 1))

/-- **V1: CANDIDATE 1 is GREEN-REFUTABLE** — its decree would make the
    quarantine inconsistent. Witness: allPFrame. -/
theorem pnpLawUniversal_refuted : ¬ PnpManifestationLawUniversal := by
  intro hLaw
  obtain ⟨L, _, hExtract⟩ := hLaw allPFrame allPFrame_faithful 4 (le_refl 4)
  exact concrete_localSearchIncompressible_smallScale (le_refl 4)
    (hExtract trivial)

/-- **V2: CANDIDATE 2 is GREEN-PROVABLE** — its decree would add NOTHING
    (a vacuous decree). Witness: constantsFrame with empty extraction. -/
theorem pnpLawExistential_green : PnpManifestationLawExistential :=
  ⟨constantsFrame, constantsFrame_faithful, fun _ _ => trivial,
   fun _ _ => ⟨boolLanguage, trivial,
     fun hP => absurd hP boolLanguage_not_inP_constantsFrame⟩⟩

/-- **V3: CANDIDATE 3 is GREEN-REFUTABLE** — bare deciders exist classically,
    the extracted resolver contradicts the incompressibility for A ≤ 4. -/
theorem pnpLawDeciderGated_refuted : ¬ PnpManifestationLawDeciderGated := by
  intro hLaw
  obtain ⟨L, ⟨R⟩⟩ := hLaw 4 (le_refl 4)
  exact ClassicalPNPBridge.concreteNode_incompressible_smallScale (le_refl 4)
    ((concreteResolverTarget 4 1).realizes
      (R.reconstruct (classicalPDecider L)))

/-#############################################################################
  §8. The conditional classical layer (the bridge as a hypothesis) — green mirrors
#############################################################################-/

/-- Sufficiency in bridge form: any InP-gated bridge over the small node
    separates its frame. -/
theorem classesSeparate_of_bridge {C : ClassicalComplexityFrame} {A : ℕ}
    (hA : A ≤ 4)
    (B : Step00ToClassicalBridge C (ClassicalPNPBridge.concreteNode A 1)) :
    C.ClassesSeparate :=
  B.classicalSeparation_of_localIncompressible
    (ClassicalPNPBridge.concreteNode_incompressible_smallScale hA)

/-- Essence-mirror: the existential law gives a faithful frame with separation.
    ⚠️ HONESTY: the law itself is already proven green (V2) — so this corollary
    too is contentless as a «promotion»; it merely fixes the shape of the chain. -/
theorem classesSeparate_of_manifestation
    (hLaw : PnpManifestationLawExistential) :
    ∃ C : ClassicalComplexityFrame,
      Nonempty (FaithfulPFrame C) ∧ C.ClassesSeparate := by
  obtain ⟨C, hFaithful, _hPNP, hMan⟩ := hLaw
  obtain ⟨L, hNP, hExtract⟩ := hMan 4 (le_refl 4)
  exact ⟨C, hFaithful, L, hNP,
    fun hP => concrete_localSearchIncompressible_smallScale (le_refl 4)
      (hExtract hP)⟩

/-- The vacuous reverse side (disclosed): separation recovers the law by an
    ex-falso extraction. -/
theorem manifestationLaw_of_separation
    (hSep : ∃ C : ClassicalComplexityFrame,
      Nonempty (FaithfulPFrame C) ∧ (∀ L, C.InP L → C.InNP L) ∧
        C.ClassesSeparate) :
    PnpManifestationLawExistential := by
  obtain ⟨C, hF, hPNP, L, hNP, hNotP⟩ := hSep
  exact ⟨C, hF, hPNP, fun _ _ => ⟨L, hNP, fun hP => absurd hP hNotP⟩⟩

/-- **The cost mirror (and its collapse):** the law ⟺ faithful-separation —
    and, unlike Riemann, this iff is GREEN (needs no boundary), while both
    sides are ALREADY theorems (V2, A7): there is nothing to decree here. -/
theorem pnpLaw_asserts_separation :
    PnpManifestationLawExistential ↔
      ∃ C : ClassicalComplexityFrame,
        Nonempty (FaithfulPFrame C) ∧ (∀ L, C.InP L → C.InNP L) ∧
          C.ClassesSeparate := by
  constructor
  · rintro ⟨C, hF, hPNP, hMan⟩
    obtain ⟨L, hNP, hExtract⟩ := hMan 4 (le_refl 4)
    exact ⟨C, hF, hPNP, L, hNP,
      fun hP => concrete_localSearchIncompressible_smallScale (le_refl 4)
        (hExtract hP)⟩
  · exact manifestationLaw_of_separation

/-- Bundling-audit (the mirror of Riemann's L9): only the Bridge could be
    decreed; the Impossible side is the green theorem
    `concreteNode_incompressible_smallScale`, never a decree. -/
theorem pnp_bundling_audit {C : ClassicalComplexityFrame} {A : ℕ}
    (hA : A ≤ 4) :
    (Nonempty (Step00ToClassicalBridge C (ClassicalPNPBridge.concreteNode A 1)) →
      C.ClassesSeparate) ∧
    (ClassicalPNPBridge.concreteNode A 1).LocalSearchIncompressible :=
  ⟨fun ⟨B⟩ => classesSeparate_of_bridge hA B,
   ClassicalPNPBridge.concreteNode_incompressible_smallScale hA⟩

-- Machine visibility of purity right in the build log: all key declarations
-- are axiom-free (expected [propext, Classical.choice, Quot.sound]).
#print axioms pnp_rank_separation_smallScale
#print axioms concrete_localPSuccess_iff_fullPayment
#print axioms boundary_forces_localPSuccess_at_decreed_scale
#print axioms pnpLawUniversal_refuted
#print axioms pnpLawExistential_green
#print axioms faithfulSelfReductionFront_isEmpty

end PNPRankPayment
end EuclidsPath
