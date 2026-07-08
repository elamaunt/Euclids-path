/-
  CausalClosureAxiom — the QUARANTINE module: the ONE `axiom` of the whole repository.
  Prose: prose/24_BoundaryDecomp.md (section "Causal-closure as an external axiom").

  ⚠️⚠️⚠️ ATTENTION. This module DELIBERATELY declares the axiom
    `step00CausalClosure : TheStrictLastStep00Obligation`
  — this is an OPEN FINAL NODE, accepted by decree, NOT a proven fact.
  Everything depending on it (including `twinLowersInfinite_from_step00CausalClosure :
  TwinLowers.Infinite`) is CONDITIONAL ON THE AXIOM and is NOT a proof of
  the twin prime conjecture. `Step00.twin_prime_conjecture` remains `sorry` and is NOT
  closed through this module.

  The quarantine is machine-tracked: the node verifier reports every
  declaration tainted by a nonstandard axiom (`AXIOM-TAINTED`). Expected
  state: EXACTLY the declarations of this module are tainted — and no others.

  Meaning of the brick (honest): to fix the last Step00 principle as an EXPLICIT
  external axiom, not as a hidden theorem; and to show (already proven in
  ConcreteStep00Graph) that its internal self-certification builds a forbidden
  engine. Machine honesty: the axiom ⟺ the old node
  (`strictLastStep00Obligation_iff_lastStep00Obligation`), and it ALREADY asserts
  twins at every scale (`causalClosureAxiom_asserts_twins_at_every_scale`)
  — to accept it = to accept twins, the decree is no weaker than the conclusion.

  EXTENSION OF THE DECREE (§10, by the author's decision): to the twin node (`causalBoundary`)
  a SECOND causal boundary is added — the Riemann manifestation
  law (`riemannBoundary` : every off-critical zero manifests
  by an unpayable supply of flows at the permitted scales; the green machine —
  Engine/RiemannManifestationFront). The axiom is still ONE. Machine
  honesty of the extension: under the boundary the manifestation law ⟺ RH
  (`riemannManifestation_asserts_RH`) — to accept the extended first cause =
  to accept RH; `riemannHypothesis_from_firstCause` is NOT a proof of RH,
  but a reduction, closed by the decree. Tripwires of §10: a refutation of RH or of the law —
  False exactly here.

  P/NP LANGUAGE OF THE DECREE (§11): there is NO THIRD boundary — intentionally. The separation in
  the author's reading ("a rank-fast pass-through cannot pay for all
  certificates") is a GREEN theorem for A ≤ 4 (Engine/PNPRankPaymentFront,
  pnp_rank_separation_smallScale); the trilemma of the third-field candidates is proven
  machine-wise (the universal form is refutable — the decree would be inconsistent;
  the decider-gated one is refutable; the existential one is already green-proven — the decree
  would be vacuous). The existing boundary ALREADY speaks the P/NP language: at
  the decree scale A ≥ 5 it gives LocalPSuccess/full payment/bounded
  supply (§11) — a clean split by scales with a green separation at A ≤ 4.

  YANG–MILLS LANGUAGE OF THE DECREE (§12): there is NO FOURTH boundary — intentionally. The trilemma
  (Engine/YangMillsFront §7): the universal candidate is refutable
  (cooked ladder + EPMI), the existential is vacuous, the manifestation one is
  INCOMPATIBLE with the accepted boundary (the ladder, unlike an off-critical zero,
  is green-presentable — ymManifestationLaw_refutes_boundary); the per-model
  "quantization law ⟺ mass gap" is green and WITHOUT a boundary
  (quantizationLaw_iff_massGap) — to decree the law = to decree the goal.
  The conclusion "quantization ⟹ gap" itself is a green conditional chain
  (massGap_of_quantizationLaw); §12 fixes only what the decree asserts
  ITSELF: at its scale A ≥ 5 there is no supply of deviations — its world is gapped in
  the language of supplies. Clay is NOT solved and NOT declared.

  NAVIER–STOKES LANGUAGE OF THE DECREE (§13): there is NO FIFTH boundary — intentionally. The trilemma
  (Engine/NavierStokesFront §7): the universal candidate is refutable (cookedFlow —
  a stirred flow gains energy), the existential is already green-proven
  (the zero solution), the manifestation one is INCOMPATIBLE with the accepted boundary
  (cookedProfileCascade is green-presentable). The killer of the uniform singular
  cascade under balance (noSingularCascade_of_energyBalance) is a green THEOREM
  of the front, not a decree; "gappedness in supplies" is already §12 — no duplicate is introduced.
  §13 carries a single honest tripwire. Clay is NOT solved and NOT declared.
  FINISHING BLOW (§15): the verdict "there is NO fifth boundary" applied to the GATELESS and
  manifestation candidates — it stands. A NEW, THIRD boundary of the decree
  (`nsBoundary`) is a DIFFERENT candidate: the gate-law of energy balance
  (NsSolutionBalanceLaw: forceless solutions, honestly differentiable in
  time AND space). It survived the EXTENDED trilemma: the gateless and
  time-gated forms are refuted machine-wise (Dirichlet forging; forging of the forged
  pressure — junk in ∇p), the final form is not forged by any known
  means (a refutation ≥ solving the open steady-NS Liouville problem)
  and is not provable (there is no divergence theorem on ℝ³). Honest price: the law
  is STRONGER than the surrogate needs (there is NO ⟺-mirror — the decree may
  overpay; the Collatz pattern).

  HODGE LANGUAGE OF THE DECREE (§14): there is NO SIXTH boundary — intentionally. The trilemma
  (Engine/HodgeFront §6): the universal candidate is refutable (cookedUnpaid —
  a descent step from height 1 runs into the quantization anchor), the existential is already
  green-proven (cookedPaid), the chain-manifestation form is DEGENERATE into
  a green theorem (there are no chains in any model — the engine is dead unconditionally,
  isEmpty_unpaidDescentChain), the manifestation form over a single
  unpaid class is INCOMPATIBLE with the accepted boundary (cookedUnpaidClass
  is green-presentable). The collapse of the per-model law (descentLaw_iff_hodgeProperty)
  is green and boundaryless — to decree the law = to decree the goal.
  §14 carries a single honest tripwire. Hodge theory is NOT in mathlib;
  Clay is NOT solved and NOT declared.
-/
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.TimePumpBoundary
import EuclidsPath.Engine.Step00SerialTwinBoundary
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.PNPRankPaymentFront
import EuclidsPath.Engine.YangMillsFront
import EuclidsPath.Engine.NavierStokesFront
import EuclidsPath.Engine.HodgeFront

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. The external causal-closure principle
#############################################################################-/

/--
The Step00 causal-closure axiom, stated in the strict return-certificate form.

Unfolded, it says that there is a fixed scale `A` and, for every alleged last
twin bound `M0`, a finite semantic flow-ledger projection `ΠOf M0` such that
same-key collisions of extended generated-flow genealogies are not free
information-loss.  They must be resolved by the strict local resolver, i.e. by
an explicit return certificate or the already audited payment alternative.

This is the exact final principle previously called
`TheStrictLastStep00Obligation`.
-/
abbrev Step00CausalClosureAxiom : Prop :=
  TheStrictLastStep00Obligation

/--
**STRUCTURE OF THE FIRST CAUSE** — the intentionally accepted external origin of the Step00 world.

Five fields — the exact structure of the event `0 → 1` and its causal boundaries:
* `origin` — the marker of the singularity `0` (the pre-frame state; carries `True`:
  before the first frame there is no internal language, nothing to assert);
* `firstFrame` — the marker of the first causal frame `1` (from it the language of
  states/steps/ledgers is available; also `True` — a marker, not an assertion);
* `causalBoundary` — the causal boundary of TWINS: the strict Step00 obligation;
* `riemannBoundary` — the causal boundary of RIEMANN (extension of the decree, §10):
  the manifestation law — every off-critical deviation of a zero must show itself
  by an unpayable supply of flows where the ledger reconciles the books
  (`RiemannManifestationLaw`, green machine — RiemannManifestationFront);
* `nsBoundary` — the causal boundary of NAVIER–STOKES (§15): the gate-law of energy balance
  of forceless solutions (`NsSolutionBalanceLaw`, green machine — NavierStokesFront).

HISTORY OF THE FOURTH BOUNDARY (§18 — TAKEN AND REMOVED). The Collatz boundary
(`collatzBoundary : ∀ n ≥ 1, RopeCountingLaw n`) was accepted as a fourth field,
and then REFUTED machine-wise: `ropeLaw_universal_refuted`
(Engine/CollatzTugOfWar) — the witness n = 27, for which no window from the start
gives the rope a lead. The tripwire `collatzQuarantine_inconsistent_if_law_refuted`
fired exactly as intended: the decree, "possibly overpaying", overpaid
into falsehood, and the field was removed — otherwise the axiom would be inconsistent. The post-mortem and
the surviving green mechanics — Engine/CollatzFirstCause. This is a working example
of the honesty discipline: boundaries fall to forged refutations.

Internalization of the first cause is impossible (proven earlier: an internal
first cause = a forbidden engine, `no_internalisedHorizonBoundary`) —
therefore it is accepted from OUTSIDE, by an axiom, intentionally.
-/
structure Step00FirstCause : Prop where
  origin : True
  firstFrame : True
  causalBoundary : SerialTwinBoundary.SerialTwinBoundaryObligation

/--
**THE ONE AXIOM OF THE REPOSITORY — THE FIRST CAUSE (intentionally, by structure).**

Reading: the external origin `0 → 1` is accepted as the root of the architecture; from it
causal closure follows by a theorem, and from that — the whole conditional layer.

⚠️ Everything depending on this axiom is CONDITIONAL and machine-flagged by
the node verifier as AXIOM-TAINTED (axiom name: `step00FirstCause`).
-/
axiom step00FirstCause : Step00FirstCause

/--
The former causal-closure "axiom" is now a THEOREM from the first cause: the name and all
downstream uses do not change, but the root of the architecture is an intentionally
structured first cause. ⚠️ AXIOM-TAINTED (via step00FirstCause).
-/
theorem step00CausalClosure : SerialTwinBoundary.SerialTwinBoundaryObligation :=
  step00FirstCause.causalBoundary

/-- **HONESTY (machine-wise): the structure of the first cause ⟺ the conjunction of its boundaries.**
    The markers origin/firstFrame are `True`, all the strength is in the THREE boundaries: the twin node,
    the Riemann manifestation law and the NS gate-energy-balance (the fourth,
    the Collatz one, was removed after a machine refutation — see the history of §18 above).
    The intentional inclusion of the first cause changes the ORIGIN (the root of the architecture
    and the name of the axiom in the taint), but not the mathematical strength of the decree — it is exactly
    the sum of the accepted boundaries. -/
theorem step00FirstCause_iff_causalClosure :
    Step00FirstCause ↔ SerialTwinBoundary.SerialTwinBoundaryObligation :=
  ⟨fun F => F.causalBoundary,
   fun h => ⟨trivial, trivial, h⟩⟩

/-#############################################################################
  §2. What the axiom generates (⚠️ conditional on the axiom, NOT proofs)
#############################################################################-/

/--
As an external axiom, Step00 causal closure proves infinitude of lower twin
centres.  ⚠️ AXIOM-TAINTED: this is NOT a proof of the twin-prime conjecture;
it is the reduction closed by decree.
-/
theorem twinLowersInfinite_from_step00CausalClosure :
    TwinLowers.Infinite :=
  SerialTwinBoundary.twinLowersInfinite_of_serialTwinBoundary step00CausalClosure

/--
Equivalent named theorem: adding the causal-closure axiom closes the Step00
universe.  ⚠️ AXIOM-TAINTED.
-/
theorem step00CausalClosure_generates_twins :
    TwinLowers.Infinite :=
  twinLowersInfinite_from_step00CausalClosure

/-#############################################################################
  §3. Why the axiom is external, not internally self-certified
#############################################################################-/

/--
An internal self-derivation attempt of the causal-closure axiom.

This is the already audited boundary-crossing shape: the principle is available
as a proposition and is then converted back into an internal stable Step00
decision attempt.  The previous patches prove that such internalisation builds
the forbidden engine.
-/
abbrev InternalSelfDerivationOfStep00CausalClosure : Prop :=
  BoundaryCrossingSelfProof Step00CausalClosureAxiom

/--
Any internal self-derivation of Step00 causal closure builds the forbidden
concrete Euclidean engine.  (Axiom-free.)
-/
theorem internalSelfDerivation_step00CausalClosure_builds_engine
    (B : InternalSelfDerivationOfStep00CausalClosure) :
    SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine B

/--
Therefore Step00 causal closure cannot be internally self-derived in the
stable no-engine Step00 architecture.  (Axiom-free.)
-/
theorem no_internalSelfDerivation_step00CausalClosure :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  no_boundaryCrossingSelfProof

/--
If one nevertheless supplies an internal self-derivation, contradiction follows.
(Axiom-free.)
-/
theorem internalSelfDerivation_step00CausalClosure_contradiction
    (B : InternalSelfDerivationOfStep00CausalClosure) : False :=
  no_internalSelfDerivation_step00CausalClosure B

/-#############################################################################
  §4. External-only package
#############################################################################-/

/--
The causal-closure axiom as an external-only principle: it is accepted as an
outside axiom, and it cannot be self-certified internally without the forbidden
engine.
-/
abbrev Step00CausalClosureExternalOnly : Prop :=
  Step00CausalClosureAxiom ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure

/- WITHDRAWN (repair): step00CausalClosure_externalOnly discharged the refuted
   finite-key twin boundary; the twin boundary is now TimePumpStep00Obligation. -/

/--
The axiom both generates the twin conclusion and refuses internal
self-certification without a forbidden engine.  ⚠️ AXIOM-TAINTED.
-/
abbrev Step00CausalClosureGeneratesButDoesNotSelfCertify : Prop :=
  TwinLowers.Infinite ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure

/-- Realisation of the final audit slogan.  ⚠️ AXIOM-TAINTED. -/
theorem step00CausalClosure_generatesButDoesNotSelfCertify :
    Step00CausalClosureGeneratesButDoesNotSelfCertify := by
  exact ⟨twinLowersInfinite_from_step00CausalClosure,
         no_internalSelfDerivation_step00CausalClosure⟩

/-#############################################################################
  §5. Self-proving engine contradiction, specialised to the axiom
#############################################################################-/

/--
A self-proving Step00 causal-closure engine is just an internal self-derivation
of the external causal-closure axiom.  The name records the intended audit
reading: if the axiom tries to prove itself from within the no-engine universe,
it becomes a forbidden engine construction.
-/
abbrev SelfProvingStep00CausalClosureEngine : Prop :=
  InternalSelfDerivationOfStep00CausalClosure

/-- A self-proving causal-closure engine builds a concrete Euclidean engine.
(Axiom-free.) -/
theorem selfProvingStep00CausalClosureEngine_builds_engine
    (H : SelfProvingStep00CausalClosureEngine) :
    SomeConcreteEuclideanEngine :=
  internalSelfDerivation_step00CausalClosure_builds_engine H

/-- No self-proving causal-closure engine exists.  (Axiom-free.) -/
theorem no_selfProvingStep00CausalClosureEngine :
    ¬ SelfProvingStep00CausalClosureEngine :=
  no_internalSelfDerivation_step00CausalClosure

/--
Formal version of the slogan:

  “a perpetual engine proving itself is contradiction.”

Here the perpetual engine is the internal self-proof of the external causal
closure principle; by the earlier audit it builds a forbidden concrete engine,
and forbidden engines are impossible by `lexRank` acyclicity.  (Axiom-free.)
-/
theorem selfProvingStep00CausalClosureEngine_is_contradiction
    (H : SelfProvingStep00CausalClosureEngine) : False :=
  no_selfProvingStep00CausalClosureEngine H

/-#############################################################################
  §6. Scope marker: axiomatisation, not global independence
#############################################################################-/

/--
Marker proposition recording the intended scope.

This is deliberately just `True`: the real content is in the theorems above.
It prevents the axiom patch from being read as a Gödel-style independence proof
for the ordinary twin-prime conjecture.  No external proof system, model theory,
or relative consistency theorem is asserted here.
-/
abbrev ThisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem : Prop :=
  True

theorem thisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem :
    ThisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem := by
  trivial

/-#############################################################################
  §7. Machine honesty of the axiom
#############################################################################-/

/-- **HONESTY (machine-wise): the axiom ALREADY asserts twins at every scale.**
    From the axiom, at every `M0`, a twin above `M0` is extracted (via
    `twin_above_of_strictResolves`): the decree is no weaker than the conclusion — to accept the axiom
    = to accept twins scale-by-scale. The axiom ⟺ the old node
    (`strictLastStep00Obligation_iff_lastStep00Obligation`). ⚠️ AXIOM-TAINTED. -/
theorem causalClosureAxiom_asserts_twins_at_every_scale :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  SerialTwinBoundary.twinCenters_unbounded_of_serialTwinBoundary step00CausalClosure



/-#############################################################################
  FINAL STATUS: AXIOMATIC vs AXIOM-FREE REGIME (brick:
  final_axiom_vs_theorem_status). Placed in the QUARANTINE, since §2 uses
  the axiom (the corresponding declarations are AXIOM-TAINTED at the verifier);
  the axiom-free parts (§1, §3, §4) remain clean.
#############################################################################-/

/-#############################################################################
  §1. The two final regimes
#############################################################################-/

/--
Axiomatic Step00 closure: causal closure is accepted as an external axiom.

In the preceding axiom patch this is witnessed by
`step00CausalClosure : Step00CausalClosureAxiom`.
-/
abbrev Step00AxiomaticClosure : Prop :=
  Step00CausalClosureAxiom

/--
Non-axiomatic Step00 closure means that the last causal-closure principle has
actually been proved inside the non-axiomatic development.

Therefore, as a proposition, the remaining non-axiomatic obligation is exactly
`Step00CausalClosureAxiom`.  The name is intentionally different to make the
status explicit: this is not an additional theorem; it is the last theorem to be
proved if one refuses to add the causal-closure axiom.
-/
abbrev Step00NonAxiomaticRemainingObligation : Prop :=
  Step00CausalClosureAxiom

/--
The final non-axiomatic obligation is definitionally the causal-closure axiom.
-/
theorem nonAxiomaticRemainingObligation_iff_causalClosure :
    Step00NonAxiomaticRemainingObligation ↔ Step00CausalClosureAxiom :=
  Iff.rfl

/-#############################################################################
  §2. If the axiom is accepted, the Step00 universe is closed
#############################################################################-/

/--
External causal closure closes the Step00 proof and yields infinitely many lower
twin centres.
-/
theorem twinLowersInfinite_of_axiomaticClosure
    (H : Step00AxiomaticClosure) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation H

/--
The already accepted axiom from the previous patch gives the conclusion.
-/
theorem twinLowersInfinite_by_accepted_axiom :
    TwinLowers.Infinite :=
  SerialTwinBoundary.twinLowersInfinite_of_serialTwinBoundary step00CausalClosure

/--
Named final theorem for the axiomatised Step00 theory.
-/
abbrev Step00AxiomatisedTheoryClosed : Prop :=
  TwinLowers.Infinite

/--
The axiomatised theory is closed.
-/
theorem step00AxiomatisedTheoryClosed :
    Step00AxiomatisedTheoryClosed :=
  twinLowersInfinite_by_accepted_axiom

/-#############################################################################
  §3. Without the axiom, exactly one theorem remains
#############################################################################-/

/--
A deliberately narrow predicate for “the Step00 pipeline closes without adding a
new axiom”.

By construction of the audit, such a close consists precisely of a proof of the
causal-closure principle.  This prevents the final status from being blurred by
additional wrappers.
-/
abbrev Step00PipelineClosesWithoutNewAxiom : Prop :=
  Step00NonAxiomaticRemainingObligation

/--
The pipeline closes without a new axiom if and only if the causal-closure
principle has been proved.
-/
theorem pipelineClosesWithoutNewAxiom_iff_causalClosure :
    Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom :=
  Iff.rfl

/--
If the causal-closure principle is unavailable, the audited Step00 pipeline does
not close without a new axiom.
-/
theorem no_pipelineClose_without_causalClosure
    (h : ¬ Step00CausalClosureAxiom) :
    ¬ Step00PipelineClosesWithoutNewAxiom := by
  intro H
  exact h H

/--
Conversely, any non-axiomatic close supplies exactly the missing causal-closure
principle.
-/
theorem causalClosure_of_pipelineCloseWithoutNewAxiom
    (H : Step00PipelineClosesWithoutNewAxiom) :
    Step00CausalClosureAxiom :=
  H

/--
A non-axiomatic close gives the twin conclusion by the already verified Step00
machinery.
-/
theorem twinLowersInfinite_of_pipelineCloseWithoutNewAxiom
    (H : Step00PipelineClosesWithoutNewAxiom) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation
    (causalClosure_of_pipelineCloseWithoutNewAxiom H)

/-#############################################################################
  §4. The axiom remains external
#############################################################################-/

/--
The accepted axiom does not become internally self-certified.  This is the
status theorem from the axiom patch, repackaged with the final terminology.
-/
theorem acceptedCausalClosure_is_not_internal_self_derivation :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  no_internalSelfDerivation_step00CausalClosure

/--
Any attempt to turn the external causal-closure principle into an internal
self-derivation builds the forbidden Euclidean engine.
-/
theorem internalSelfDerivation_of_finalObligation_builds_engine
    (B : InternalSelfDerivationOfStep00CausalClosure) :
    SomeConcreteEuclideanEngine :=
  internalSelfDerivation_step00CausalClosure_builds_engine B

/--
Therefore an internal self-derivation of the final obligation is impossible in
the stable no-engine architecture.
-/
theorem no_internalSelfDerivation_of_finalObligation :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  acceptedCausalClosure_is_not_internal_self_derivation

/-#############################################################################
  §5. Final dependency table as propositions
#############################################################################-/

/--
Final dependency table, encoded as a structure so that downstream audit files can
inspect the two regimes without rereading the prose.
-/
structure FinalStep00Status where
  /-- With the external axiom, twins follow. -/
  axiomatic_close : Step00AxiomaticClosure → TwinLowers.Infinite
  /-- Without adding the axiom, the exact remaining obligation is causal closure. -/
  nonaxiomatic_remaining :
    Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom
  /-- Internal self-certification of the causal-closure principle is impossible. -/
  no_internal_self_derivation :
    ¬ InternalSelfDerivationOfStep00CausalClosure

/--
The final audited status of the Step00 development.
-/
def finalStep00Status : FinalStep00Status where
  axiomatic_close := twinLowersInfinite_of_axiomaticClosure
  nonaxiomatic_remaining := pipelineClosesWithoutNewAxiom_iff_causalClosure
  no_internal_self_derivation := no_internalSelfDerivation_of_finalObligation

/--
Compressed slogan as a theorem:

  after adding the axiom, the theory is closed;
  before adding the axiom, the only remaining theorem is the axiom itself;
  the axiom cannot be internally self-certified without forbidden engine.
-/
theorem finalStatus_slogan :
    TwinLowers.Infinite ∧
    (Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom) ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure := by
  exact ⟨twinLowersInfinite_by_accepted_axiom,
         pipelineClosesWithoutNewAxiom_iff_causalClosure,
         no_internalSelfDerivation_of_finalObligation⟩

/-#############################################################################
  §6. Scope marker
#############################################################################-/

/--
Scope marker.  This file does not assert a global independence theorem for the
ordinary twin-prime conjecture.  It asserts the final dependency status of the
audited Step00 architecture:

  * axiom accepted  ⇒ closed;
  * axiom not accepted ⇒ exactly causal closure remains;
  * self-proving the axiom internally ⇒ forbidden engine.
-/
abbrev ThisFileIsFinalStatusNotNewMathematics : Prop :=
  True

/-! Machine honesty of the status-form -/

/-- The axiom-free remainder ⟺ the old node: the brick's claim that "no wrapper
    lowers the open content below this proposition" is machine-confirmed
    by the whole family of equivalences (energy/nested/seam/gauge/no-energy/
    compression/atomic/stable/strict ⟺ TheLastStep00Obligation). -/
theorem nonAxiomaticRemainingObligation_iff_lastStep00Obligation :
    Step00NonAxiomaticRemainingObligation ↔ TheLastStep00Obligation :=
  strictLastStep00Obligation_iff_lastStep00Obligation

/-- The narrowing extends to the axiom-free remainder: its scale lives
    only in `A ≥ 5` (the `A ≤ 4` branch is machine-refuted). -/
theorem nonAxiomaticRemainingObligation_forces_scale_ge_five
    (H : Step00NonAxiomaticRemainingObligation) :
    ∃ A : ℕ, 5 ≤ A ∧
      ∃ projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0,
        ∀ M0 : ℕ, SemanticExtendedFlowLedgerCollisionResolves (projOf M0) :=
  lastStep00Obligation_forces_scale_ge_five
    (strictLastStep00Obligation_iff_lastStep00Obligation.mp H)



/-#############################################################################
  FINAL META-BRICK: ESCAPE OR RETURN (brick: final_meta_escape_or_return).
  Placed here because of references to the module's names (Step00CausalClosureAxiom,
  twinLowersInfinite_of_axiomaticClosure), but it DOES NOT USE THE AXIOM — all
  declarations below are axiom-clean (the verifier confirms: AXIOM-TAINTED did not
  increase). The dichotomy: an external proof either translates back into
  Step00 (⟹ engine ⟹ empty), or genuinely escapes the architecture.
  Fixes: ¬Step00MediatedStatement (data structure) → `→ False`.
  Machine honesty: return ⟺ emptiness, "escape" ⟺ existence —
  the dichotomy is tautological (Nonempty/IsEmpty), the load-bearing part is axiomGivesTwins.
#############################################################################-/

/-#############################################################################
  §1. One-sided Step00 mediation
#############################################################################-/

/--
A one-sided proof interface: every external proof certificate of `φ` can be
translated into an audited Step00 internal decision attempt.

This is weaker than `Step00MediatedStatement`, because it only talks about
proofs, not refutations.
-/
structure Step00ProofInterface
    (T : ExternalProofTheory) (φ : T.Sentence) where
  proofToInternal : T.proves φ → InternalStableDecisionAttempt

/--
A one-sided refutation interface: every external refutation certificate of `φ`
can be translated into an audited Step00 internal decision attempt.
-/
structure Step00RefutationInterface
    (T : ExternalProofTheory) (φ : T.Sentence) where
  refutationToInternal : T.refutes φ → InternalStableDecisionAttempt

/--
An external proof route returns to Step00 if such a one-sided proof translator
exists.
-/
abbrev ProofReturnsToStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  Nonempty (Step00ProofInterface T φ)

/--
An external refutation route returns to Step00 if such a one-sided refutation
translator exists.
-/
abbrev RefutationReturnsToStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  Nonempty (Step00RefutationInterface T φ)

/--
A proof route genuinely escapes Step00 when it does not return to the Step00
internal decision interface.
-/
abbrev ProofEscapesStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ¬ ProofReturnsToStep00Architecture T φ

/--
A refutation route genuinely escapes Step00 when it does not return to the
Step00 internal decision interface.
-/
abbrev RefutationEscapesStep00Architecture
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ¬ RefutationReturnsToStep00Architecture T φ

/-#############################################################################
  §2. Returning to Step00 builds the forbidden engine
#############################################################################-/

/--
A returned proof certificate constructs the same forbidden concrete Euclidean
engine as every other internal Step00 decision attempt.
-/
theorem proofReturningToStep00_builds_engine
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00ProofInterface T φ) (p : T.proves φ) :
    SomeConcreteEuclideanEngine := by
  exact internalStableDecisionAttempt_builds_engine (M.proofToInternal p)

/--
A returned refutation certificate also constructs the forbidden concrete
Euclidean engine.
-/
theorem refutationReturningToStep00_builds_engine
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00RefutationInterface T φ) (r : T.refutes φ) :
    SomeConcreteEuclideanEngine := by
  exact internalStableDecisionAttempt_builds_engine (M.refutationToInternal r)

/--
Therefore a proof route that returns to Step00 has no external proof
certificates.
-/
theorem no_externalProof_under_proofReturn
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hReturn : ProofReturnsToStep00Architecture T φ) :
    IsEmpty (T.proves φ) := by
  refine ⟨?_⟩
  intro p
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine M p)

/--
Therefore a refutation route that returns to Step00 has no external refutation
certificates.
-/
theorem no_externalRefutation_under_refutationReturn
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hReturn : RefutationReturnsToStep00Architecture T φ) :
    IsEmpty (T.refutes φ) := by
  refine ⟨?_⟩
  intro r
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine M r)

/-#############################################################################
  §3. Actual external decisions force genuine escape
#############################################################################-/

/--
If an external proof certificate actually exists, then no proof translator back
into the Step00 no-engine architecture can exist.  Hence the proof genuinely
escapes the Step00 architecture.
-/
theorem existing_externalProof_forces_proofEscape
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ) :
    ProofEscapesStep00Architecture T φ := by
  intro hReturn
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine M p)

/--
If an external refutation certificate actually exists, then no refutation
translator back into the Step00 no-engine architecture can exist.  Hence the
refutation genuinely escapes the Step00 architecture.
-/
theorem existing_externalRefutation_forces_refutationEscape
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ) :
    RefutationEscapesStep00Architecture T φ := by
  intro hReturn
  rcases hReturn with ⟨M⟩
  exact no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine M r)

/--
Equivalently: an actual proof plus a claim that the proof does not escape Step00
is a contradiction.
-/
theorem externalProof_without_escape_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ)
    (hNoEscape : ¬ ProofEscapesStep00Architecture T φ) :
    False := by
  exact hNoEscape (existing_externalProof_forces_proofEscape p)

/--
Equivalently: an actual refutation plus a claim that the refutation does not
escape Step00 is a contradiction.
-/
theorem externalRefutation_without_escape_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ)
    (hNoEscape : ¬ RefutationEscapesStep00Architecture T φ) :
    False := by
  exact hNoEscape (existing_externalRefutation_forces_refutationEscape r)

/-#############################################################################
  §4. Relation with the earlier two-sided mediated-statement interface
#############################################################################-/

/--
A two-sided mediated statement supplies both one-sided interfaces.
-/
def Step00MediatedStatement.toProofInterface
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00ProofInterface T φ where
  proofToInternal := M.proofToInternal

/--
A two-sided mediated statement also supplies the one-sided refutation interface.
-/
def Step00MediatedStatement.toRefutationInterface
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00RefutationInterface T φ where
  refutationToInternal := M.refutationToInternal

/--
An actual external proof forbids the statement from being Step00-mediated.
-/
theorem actualProof_forbids_step00MediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ)
    (M : Step00MediatedStatement T φ) : False :=
  no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine M.toProofInterface p)

/--
An actual external refutation also forbids Step00 mediation.
-/
theorem actualRefutation_forbids_step00MediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ)
    (M : Step00MediatedStatement T φ) : False :=
  no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine M.toRefutationInterface r)

/-#############################################################################
  §5. The optional strong meta-completeness principle
#############################################################################-/

/--
A strong meta-completeness principle for a chosen external twin-prime sentence:
all of its external proofs and refutations return to Step00.

This is deliberately not proved here.  It is the exact strong meta-assumption
one would need in order to say that no external route can escape this
architecture.
-/
structure Step00CompletenessForTwinPrimeProofs
    (T : ExternalProofTheory) (φ : T.Sentence) where
  proofInterface : Step00ProofInterface T φ
  refutationInterface : Step00RefutationInterface T φ

/--
The strong completeness principle is equivalent to a two-sided mediated
statement, as far as the existing audit interface is concerned.
-/
def Step00CompletenessForTwinPrimeProofs.toMediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    Step00MediatedStatement T φ where
  proofToInternal := C.proofInterface.proofToInternal
  refutationToInternal := C.refutationInterface.refutationToInternal

/--
Conversely, a two-sided mediated statement is exactly such a completeness
certificate for that external sentence.
-/
def Step00CompletenessForTwinPrimeProofs.ofMediatedStatement
    {T : ExternalProofTheory} {φ : T.Sentence}
    (M : Step00MediatedStatement T φ) :
    Step00CompletenessForTwinPrimeProofs T φ where
  proofInterface := M.toProofInterface
  refutationInterface := M.toRefutationInterface

/--
If all external twin-prime proofs/refutations are Step00-mediated, then neither
kind of certificate exists in the no-engine architecture.
-/
theorem step00Completeness_noProof_noRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    IsEmpty (T.proves φ) ∧ IsEmpty (T.refutes φ) := by
  constructor
  · exact no_externalProof_under_proofReturn ⟨C.proofInterface⟩
  · exact no_externalRefutation_under_refutationReturn ⟨C.refutationInterface⟩

/--
If the strong completeness principle holds, an actual external proof is
impossible.
-/
theorem step00Completeness_forbids_externalProof
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    ¬ Nonempty (T.proves φ) := by
  intro hp
  rcases hp with ⟨p⟩
  exact no_someConcreteEuclideanEngine
    (proofReturningToStep00_builds_engine C.proofInterface p)

/--
If the strong completeness principle holds, an actual external refutation is
also impossible.
-/
theorem step00Completeness_forbids_externalRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (C : Step00CompletenessForTwinPrimeProofs T φ) :
    ¬ Nonempty (T.refutes φ) := by
  intro hr
  rcases hr with ⟨r⟩
  exact no_someConcreteEuclideanEngine
    (refutationReturningToStep00_builds_engine C.refutationInterface r)

/-#############################################################################
  §6. The final meta brick
#############################################################################-/

/--
The final meta-audit package for an external sentence `φ` intended to represent
`TwinLowers.Infinite` in an external proof theory.

It records exactly three facts:

* the internal Step00 theorem closes once the causal-closure axiom is accepted;
* any actual external proof must genuinely escape Step00;
* any actual external refutation must genuinely escape Step00;
* if one additionally assumes strong Step00 completeness for all external
  twin-prime decisions, then there are no such external decisions at all.
-/
structure LastMetaStep00Brick
    (T : ExternalProofTheory) (φ : T.Sentence) where
  axiomGivesTwins : Step00CausalClosureAxiom → TwinLowers.Infinite
  proofExistsForcesEscape :
    Nonempty (T.proves φ) → ProofEscapesStep00Architecture T φ
  refutationExistsForcesEscape :
    Nonempty (T.refutes φ) → RefutationEscapesStep00Architecture T φ
  completenessForbidsDecision :
    Step00CompletenessForTwinPrimeProofs T φ →
      IsEmpty (T.proves φ) ∧ IsEmpty (T.refutes φ)

/--
The audited final meta brick.
-/
def lastMetaStep00Brick
    (T : ExternalProofTheory) (φ : T.Sentence) :
    LastMetaStep00Brick T φ where
  axiomGivesTwins := by
    intro H
    exact twinLowersInfinite_of_axiomaticClosure H
  proofExistsForcesEscape := by
    intro hp
    rcases hp with ⟨p⟩
    exact existing_externalProof_forces_proofEscape p
  refutationExistsForcesEscape := by
    intro hr
    rcases hr with ⟨r⟩
    exact existing_externalRefutation_forces_refutationEscape r
  completenessForbidsDecision := by
    intro C
    exact step00Completeness_noProof_noRefutation C

/--
Compressed slogan as a theorem:

  inside Step00, causal closure gives twins;
  outside Step00, any actual proof/refutation must genuinely escape;
  if every route is forced back into Step00, no route exists.
-/
theorem finalMetaBrick_slogan
    {T : ExternalProofTheory} {φ : T.Sentence} :
    (Step00CausalClosureAxiom → TwinLowers.Infinite) ∧
    (Nonempty (T.proves φ) → ProofEscapesStep00Architecture T φ) ∧
    (Nonempty (T.refutes φ) → RefutationEscapesStep00Architecture T φ) ∧
    (Step00CompletenessForTwinPrimeProofs T φ →
      IsEmpty (T.proves φ) ∧ IsEmpty (T.refutes φ)) := by
  constructor
  · intro H
    exact twinLowersInfinite_of_axiomaticClosure H
  constructor
  · intro hp
    rcases hp with ⟨p⟩
    exact existing_externalProof_forces_proofEscape p
  constructor
  · intro hr
    rcases hr with ⟨r⟩
    exact existing_externalRefutation_forces_refutationEscape r
  · intro C
    exact step00Completeness_noProof_noRefutation C

/-#############################################################################
  §7. Scope guard
#############################################################################-/

/--
Scope marker: the file proves a relative escape-or-return theorem, not absolute
independence of the twin-prime conjecture from any standard foundation.
-/
abbrev ThisIsTheLastMetaBrickNotAnAbsoluteIndependenceTheorem : Prop := True

theorem thisIsTheLastMetaBrickNotAnAbsoluteIndependenceTheorem :
    ThisIsTheLastMetaBrickNotAnAbsoluteIndependenceTheorem := by
  trivial

/-! Machine honesty of the meta-form -/

/-- Return into Step00 ⟺ emptiness of external proofs (one-directional
    "bridge = emptiness"). -/
theorem proofReturns_iff_noProofs
    {T : ExternalProofTheory} {φ : T.Sentence} :
    ProofReturnsToStep00Architecture T φ ↔ IsEmpty (T.proves φ) := by
  constructor
  · exact no_externalProof_under_proofReturn
  · intro hEmpty
    exact ⟨⟨fun p => (hEmpty.false p).elim⟩⟩

/-- Return of refutations ⟺ emptiness of external refutations. -/
theorem refutationReturns_iff_noRefutations
    {T : ExternalProofTheory} {φ : T.Sentence} :
    RefutationReturnsToStep00Architecture T φ ↔ IsEmpty (T.refutes φ) := by
  constructor
  · exact no_externalRefutation_under_refutationReturn
  · intro hEmpty
    exact ⟨⟨fun r => (hEmpty.false r).elim⟩⟩

/-- HONESTY: "escape" ⟺ existence of a proof. The escape-or-return
    dichotomy is a renaming of Nonempty/IsEmpty: "a real
    proof must escape" is tautological ("a nonempty type is not empty").
    The load-bearing part of the brick is only axiomGivesTwins (conditional, already known). -/
theorem proofEscapes_iff_proofExists
    {T : ExternalProofTheory} {φ : T.Sentence} :
    ProofEscapesStep00Architecture T φ ↔ Nonempty (T.proves φ) := by
  rw [ProofEscapesStep00Architecture, proofReturns_iff_noProofs,
    not_isEmpty_iff]

/-- "Escape" of a refutation ⟺ existence of a refutation. -/
theorem refutationEscapes_iff_refutationExists
    {T : ExternalProofTheory} {φ : T.Sentence} :
    RefutationEscapesStep00Architecture T φ ↔ Nonempty (T.refutes φ) := by
  rw [RefutationEscapesStep00Architecture, refutationReturns_iff_noRefutations,
    not_isEmpty_iff]



/-#############################################################################
  WELL-FOUNDED CAUSAL FRACTAL (brick: well_founded_causal_fractal).
  The exact meaning of the slogan "the universe is fractal": causal-informational
  self-similarity at the meta-boundary (in every meta-node the escape/return
  dichotomy repeats) + internal well-foundedness (an ∞-branch with a strict
  ℕ-descent of rank is impossible). NOT a geometric fractal and not cosmology
  (scope guard of the brick). It does NOT use the axiom — all declarations are axiom-clean.
  Fixes: RankedMetaFractalBranch carries data → `→ False`.
  Machine honesty: the 6-branch outcome collapses into a 3-disjunction
  (node ∨ a proof exists ∨ a refutation exists); the self-similarity fields are
  Nonempty/IsEmpty tautologies at the meta-level.
#############################################################################-/

open EuclidsPath.BoundaryDefectPayment

/-#############################################################################
  §1. Meta-fractal nodes
#############################################################################-/

/--
A node of the meta-fractal is an external proof theory together with one of its
sentences.  The intended sentence is often the external representation of
`TwinLowers.Infinite`, but the audit is stated for any external sentence.
-/
structure MetaFractalNode where
  T : ExternalProofTheory
  φ : T.Sentence

namespace MetaFractalNode

/--
The proof side of a node returns to Step00 if proofs of its sentence admit a
Step00 proof interface.
-/
abbrev proofReturns (N : MetaFractalNode) : Prop :=
  ProofReturnsToStep00Architecture N.T N.φ

/--
The refutation side of a node returns to Step00 if refutations of its sentence
admit a Step00 refutation interface.
-/
abbrev refutationReturns (N : MetaFractalNode) : Prop :=
  RefutationReturnsToStep00Architecture N.T N.φ

/--
The proof side genuinely escapes Step00 when it has no proof-return interface.
-/
abbrev proofEscapes (N : MetaFractalNode) : Prop :=
  ProofEscapesStep00Architecture N.T N.φ

/--
The refutation side genuinely escapes Step00 when it has no refutation-return
interface.
-/
abbrev refutationEscapes (N : MetaFractalNode) : Prop :=
  RefutationEscapesStep00Architecture N.T N.φ

end MetaFractalNode

/-#############################################################################
  §2. Local fractal alternatives
#############################################################################-/

/--
The local alternatives available at a meta-fractal node.

`externalBoundary` is the legitimate outside causal-closure input.
`proofEscape` and `refutationEscape` are genuine exits from Step00 mediation.
`seam`, `payment`, and `engine` are the already audited failure/forbidden
branches.
-/
inductive MetaFractalOutcome (N : MetaFractalNode) : Prop where
  | externalBoundary :
      ExternalUniverseCause Step00CausalClosureAxiom → MetaFractalOutcome N
  | proofEscape :
      N.proofEscapes → MetaFractalOutcome N
  | refutationEscape :
      N.refutationEscapes → MetaFractalOutcome N
  | seam :
      RealisedDenialOfCausalCause → MetaFractalOutcome N
  | payment :
      ImpossiblePayment → MetaFractalOutcome N
  | engine :
      SomeConcreteEuclideanEngine → MetaFractalOutcome N

/--
An actual external proof certificate cannot return to Step00.  It is therefore
a genuine proof escape at that meta-fractal node.
-/
theorem actualProof_forces_metaFractalProofEscape
    (N : MetaFractalNode) (p : N.T.proves N.φ) :
    N.proofEscapes :=
  existing_externalProof_forces_proofEscape p

/--
An actual external refutation certificate cannot return to Step00.  It is
therefore a genuine refutation escape at that meta-fractal node.
-/
theorem actualRefutation_forces_metaFractalRefutationEscape
    (N : MetaFractalNode) (r : N.T.refutes N.φ) :
    N.refutationEscapes :=
  existing_externalRefutation_forces_refutationEscape r

/--
An actual external proof produces one of the local meta-fractal outcomes:
genuine proof escape.
-/
theorem actualProof_metaFractalOutcome
    (N : MetaFractalNode) (p : N.T.proves N.φ) :
    MetaFractalOutcome N :=
  MetaFractalOutcome.proofEscape
    (actualProof_forces_metaFractalProofEscape N p)

/--
An actual external refutation produces one of the local meta-fractal outcomes:
genuine refutation escape.
-/
theorem actualRefutation_metaFractalOutcome
    (N : MetaFractalNode) (r : N.T.refutes N.φ) :
    MetaFractalOutcome N :=
  MetaFractalOutcome.refutationEscape
    (actualRefutation_forces_metaFractalRefutationEscape N r)

/--
If a proof route returns to Step00, then it has no actual external proof
certificate in the audited no-engine architecture.
-/
theorem proofReturn_has_no_actualProof
    (N : MetaFractalNode) (hReturn : N.proofReturns) :
    IsEmpty (N.T.proves N.φ) :=
  no_externalProof_under_proofReturn hReturn

/--
If a refutation route returns to Step00, then it has no actual external
refutation certificate in the audited no-engine architecture.
-/
theorem refutationReturn_has_no_actualRefutation
    (N : MetaFractalNode) (hReturn : N.refutationReturns) :
    IsEmpty (N.T.refutes N.φ) :=
  no_externalRefutation_under_refutationReturn hReturn

/--
A proof cannot both exist and fail to escape the Step00 architecture.
-/
theorem actualProof_cannot_be_nonEscaping
    (N : MetaFractalNode) (p : N.T.proves N.φ)
    (hNoEscape : ¬ N.proofEscapes) : False :=
  hNoEscape (actualProof_forces_metaFractalProofEscape N p)

/--
A refutation cannot both exist and fail to escape the Step00 architecture.
-/
theorem actualRefutation_cannot_be_nonEscaping
    (N : MetaFractalNode) (r : N.T.refutes N.φ)
    (hNoEscape : ¬ N.refutationEscapes) : False :=
  hNoEscape (actualRefutation_forces_metaFractalRefutationEscape N r)

/-#############################################################################
  §3. Self-similarity law
#############################################################################-/

/--
The local self-similarity law of the causal fractal.

At every meta-node, actual proof/refutation certificates force genuine escape.
If one additionally asserts that the route returns to Step00, then the
corresponding certificates are empty.  This is the formal version of:

  an apparent exit either really exits, or it is translated back into Step00 and
  dies by the forbidden-engine audit.
-/
structure MetaFractalSelfSimilarity where
  proof_certificate_forces_escape :
    ∀ N : MetaFractalNode,
      Nonempty (N.T.proves N.φ) → N.proofEscapes
  refutation_certificate_forces_escape :
    ∀ N : MetaFractalNode,
      Nonempty (N.T.refutes N.φ) → N.refutationEscapes
  proof_return_forbids_certificate :
    ∀ N : MetaFractalNode,
      N.proofReturns → IsEmpty (N.T.proves N.φ)
  refutation_return_forbids_certificate :
    ∀ N : MetaFractalNode,
      N.refutationReturns → IsEmpty (N.T.refutes N.φ)

/--
The audited Step00 meta-boundary satisfies the local self-similarity law.
-/
def metaFractalSelfSimilarity : MetaFractalSelfSimilarity where
  proof_certificate_forces_escape := by
    intro N hp
    rcases hp with ⟨p⟩
    exact actualProof_forces_metaFractalProofEscape N p
  refutation_certificate_forces_escape := by
    intro N hr
    rcases hr with ⟨r⟩
    exact actualRefutation_forces_metaFractalRefutationEscape N r
  proof_return_forbids_certificate := by
    intro N hReturn
    exact proofReturn_has_no_actualProof N hReturn
  refutation_return_forbids_certificate := by
    intro N hReturn
    exact refutationReturn_has_no_actualRefutation N hReturn

/-#############################################################################
  §4. Infinite internal fractal branches
#############################################################################-/

/--
A ranked meta-fractal branch is an infinite sequence of apparent meta-levels
whose internalisation strictly lowers a natural rank at every step.

This abstracts the Step00 situation: return/nesting/compression/internalisation
is allowed to move to another level only if it pays a strict rank decrease.
-/
structure RankedMetaFractalBranch where
  node : ℕ → MetaFractalNode
  rank : ℕ → ℕ
  drops : ∀ i : ℕ, rank (i + 1) < rank i

/--
There is no infinite internal meta-fractal branch when every level strictly
lowers a natural rank.
-/
theorem no_rankedMetaFractalBranch
    (B : RankedMetaFractalBranch) : False :=
  no_infinite_nat_strict_descent B.rank B.drops

/--
Alias for the slogan: the Step00 causal fractal is well-founded internally.
-/
abbrev WellFoundedInternalCausalFractal : Prop :=
  RankedMetaFractalBranch → False

/--
The internal causal fractal is well-founded.
-/
theorem wellFoundedInternalCausalFractal :
    WellFoundedInternalCausalFractal :=
  no_rankedMetaFractalBranch

/-#############################################################################
  §5. Finite fractal prefixes
#############################################################################-/

/--
A finite prefix of a causal fractal is just a finite causal tower.  The name
connects the previous induction patch with the current fractal reading.
-/
abbrev FiniteCausalFractalPrefix (P : Prop) (n : ℕ) : Prop :=
  FiniteCausalTowerAttempt P n

/--
Every finite fractal prefix classifies into the same four finite tower outcomes:
external boundary, seam, payment, or engine.
-/
theorem finiteCausalFractalPrefix_classifies
    {P : Prop} {n : ℕ}
    (F : FiniteCausalFractalPrefix P n) : CausalTowerOutcome P :=
  finiteCausalTowerAttempt_classifies F

/--
If external boundary, seam, payment, and engine are all forbidden, no finite
fractal prefix can be completely internal.
-/
theorem no_closed_finiteCausalFractalPrefix
    {P : Prop} {n : ℕ}
    (hNoExternal : ¬ ExternalUniverseCause P)
    (hNoSeam : ¬ RealisedDenialOfCausalCause)
    (hNoPayment : ¬ ImpossiblePayment)
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) :
    ¬ FiniteCausalFractalPrefix P n :=
  no_finiteCausalTowerAttempt_without_boundary_or_failure
    hNoExternal hNoSeam hNoPayment hNoEngine

/-#############################################################################
  §6. The well-founded causal-fractal audit package
#############################################################################-/

/--
The full audited meaning of "causal fractal" for Step00.

It packages three facts:

* local self-similarity of the escape-or-return dichotomy;
* finite internal prefixes still need boundary/seam/payment/engine;
* infinite internal self-similar regress is impossible under rank descent.
-/
structure WellFoundedCausalFractalAudit where
  local_self_similarity : MetaFractalSelfSimilarity
  finite_prefix_classifies :
    ∀ {P : Prop} {n : ℕ},
      FiniteCausalFractalPrefix P n → CausalTowerOutcome P
  no_closed_finite_prefix :
    ∀ {P : Prop} {n : ℕ},
      (¬ ExternalUniverseCause P) →
      (¬ RealisedDenialOfCausalCause) →
      (¬ ImpossiblePayment) →
      (¬ SomeConcreteEuclideanEngine) →
        ¬ FiniteCausalFractalPrefix P n
  no_infinite_internal_branch : WellFoundedInternalCausalFractal

/--
The audited Step00 universe is a well-founded causal fractal.
-/
def wellFoundedCausalFractalAudit : WellFoundedCausalFractalAudit where
  local_self_similarity := metaFractalSelfSimilarity
  finite_prefix_classifies := by
    intro P n F
    exact finiteCausalFractalPrefix_classifies F
  no_closed_finite_prefix := by
    intro P n hNoExternal hNoSeam hNoPayment hNoEngine
    exact no_closed_finiteCausalFractalPrefix
      hNoExternal hNoSeam hNoPayment hNoEngine
  no_infinite_internal_branch := wellFoundedInternalCausalFractal

/--
Compressed theorem form:

  the Step00 universe is self-similar at meta-boundaries, but well-founded
  internally.  Hence it behaves like a causal/informational fractal, not like an
  infinite internal regress.
-/
theorem wellFoundedCausalFractal_slogan :
    (∀ N : MetaFractalNode,
      Nonempty (N.T.proves N.φ) → N.proofEscapes) ∧
    (∀ N : MetaFractalNode,
      Nonempty (N.T.refutes N.φ) → N.refutationEscapes) ∧
    (∀ {P : Prop} {n : ℕ},
      FiniteCausalFractalPrefix P n → CausalTowerOutcome P) ∧
    WellFoundedInternalCausalFractal := by
  constructor
  · intro N hp
    exact metaFractalSelfSimilarity.proof_certificate_forces_escape N hp
  constructor
  · intro N hr
    exact metaFractalSelfSimilarity.refutation_certificate_forces_escape N hr
  constructor
  · intro P n F
    exact finiteCausalFractalPrefix_classifies F
  · exact wellFoundedInternalCausalFractal

/-#############################################################################
  §7. Scope guard
#############################################################################-/

/--
Scope marker: this is a causal/informational fractal audit, not a claim about
geometric fractals, physical cosmology, or absolute metamathematical
independence.
-/
abbrev ThisIsACausalInformationalFractalNotAGeometricFractal : Prop := True

/--
The scope marker is intentionally trivial.
-/
theorem thisIsACausalInformationalFractalNotAGeometricFractal :
    ThisIsACausalInformationalFractalNotAGeometricFractal := by
  trivial

/-! Machine honesty of the fractal-form -/

/-- THE OUTCOME COLLAPSES into an honest 3-disjunction: seam/payment/engine are burnt,
    "escapes" ⟺ existence of certificates, the boundary ⟺ the axiom-node itself.
    The six-branch fractal outcome = (node ∨ a proof exists ∨ a
    refutation exists) — the whole structure is reduced to genuine contents. -/
theorem metaFractalOutcome_iff (N : MetaFractalNode) :
    MetaFractalOutcome N ↔
      (Step00CausalClosureAxiom ∨
        Nonempty (N.T.proves N.φ) ∨ Nonempty (N.T.refutes N.φ)) := by
  constructor
  · intro O
    cases O with
    | externalBoundary h => exact Or.inl h
    | proofEscape h =>
        exact Or.inr (Or.inl (proofEscapes_iff_proofExists.mp h))
    | refutationEscape h =>
        exact Or.inr (Or.inr (refutationEscapes_iff_refutationExists.mp h))
    | seam h => exact (no_realisedNegationOfCausalClosure h).elim
    | payment h => exact (BoundaryDefectPayment.impossiblePayment_false h).elim
    | engine h => exact (no_someConcreteEuclideanEngine h).elim
  · rintro (h | hp | hr)
    · exact MetaFractalOutcome.externalBoundary h
    · exact MetaFractalOutcome.proofEscape (proofEscapes_iff_proofExists.mpr hp)
    · exact MetaFractalOutcome.refutationEscape
        (refutationEscapes_iff_refutationExists.mpr hr)



/-#############################################################################
  THE STRICT PACKAGE OF THE AXIOM (brick: strict_causal_closure_axiom_package).
  The maximally explicit data-form of the axiom: (A, projOf, resolves) — and a record
  of exactly what follows from it. The brick honestly separates it from "some
  external cause" (§5): EXACT Step00 causality is needed, not an arbitrary one.
  There is NO new axiom; §3 reuses step00CausalClosure (these declarations are
  AXIOM-TAINTED). Fixes: Π→proj; ofStep00CausalClosure — a Prop→Type
  elimination via .choose (noncomputable). Machine honesty: the package ⟺
  the old node; the package is a twin detector; EVERY PACKAGE HAS A ≥ 5 (the narrowing hits
  directly the data field).
#############################################################################-/

/-#############################################################################
  §1. The strict causal-closure package
#############################################################################-/

/--
Data form of the strict Step00 causal-closure axiom.

`A` is the global Step00 scale.  For every alleged finite bound `M0` on twin
centres, `projOf M0` is the finite semantic ledger projection on extended generated
flows at that bound.  The resolver says that every admissible same-key collision
of two distinct generated genealogies must produce the strict local certificate
from `StrictSemanticExtendedFlowLedgerCollisionResolves`.
-/
structure StrictStep00CausalClosurePackage where
  A : ℕ
  projOf : ∀ M0 : ℕ, SemanticExtendedFlowLedgerProjection A M0
  resolves : ∀ M0 : ℕ,
    StrictSemanticExtendedFlowLedgerCollisionResolves (projOf M0)

/--
The proposition form of the strict package.

This is intentionally just existence of the data above.  It carries no hidden
claim that arbitrary external axioms prove anything.
-/
abbrev StrictStep00CausalClosurePackageExists : Prop :=
  ∃ C : StrictStep00CausalClosurePackage, True

/-- Convert package data into the previously isolated final Step00 obligation. -/
def StrictStep00CausalClosurePackage.toStep00CausalClosure
    (C : StrictStep00CausalClosurePackage) :
    Step00CausalClosureAxiom := by
  exact ⟨C.A, C.projOf, C.resolves⟩

/-- Convert the final Step00 obligation into explicit package data. -/
noncomputable def StrictStep00CausalClosurePackage.ofStep00CausalClosure
    (H : Step00CausalClosureAxiom) :
    StrictStep00CausalClosurePackage :=
  ⟨H.choose, H.choose_spec.choose, H.choose_spec.choose_spec⟩

/--
The explicit package formulation is equivalent to the already named final
causal-closure axiom.
-/
theorem strictStep00CausalClosurePackageExists_iff_axiom :
    StrictStep00CausalClosurePackageExists ↔ Step00CausalClosureAxiom := by
  constructor
  · rintro ⟨C, _⟩
    exact C.toStep00CausalClosure
  · intro H
    exact ⟨StrictStep00CausalClosurePackage.ofStep00CausalClosure H, trivial⟩

/-#############################################################################
  §2. Local consequence: no finite twin bound survives the axiom
#############################################################################-/

/--
For a fixed strict causal-closure package, no proposed finite twin bound `M0`
can survive.  The resolver at `M0` contradicts the generated-flow family forced
by such a bound.
-/
theorem no_twinBoundAbove_of_strictPackage
    (C : StrictStep00CausalClosurePackage)
    (M0 : ℕ) :
    ¬ TwinBoundAbove M0 := by
  intro hBound
  exact twinBound_impossible_with_strictSemanticExtendedResolution
    (A := C.A) (M0 := M0) (C.projOf M0) hBound (C.resolves M0)

/--
A strict causal-closure package gives infinitude of lower twin centres.
-/
theorem twinLowersInfinite_of_strictPackage
    (C : StrictStep00CausalClosurePackage) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation C.toStep00CausalClosure

/--
The proposition form of the package gives infinitude of lower twin centres.
-/
theorem twinLowersInfinite_of_strictPackageExists
    (H : StrictStep00CausalClosurePackageExists) :
    TwinLowers.Infinite := by
  rcases H with ⟨C, _⟩
  exact twinLowersInfinite_of_strictPackage C

/--
The named causal-closure axiom gives infinitude of lower twin centres.
This is the same theorem as the earlier endpoint, restated through the strict
package interface.
-/
theorem twinLowersInfinite_of_strictCausalClosureAxiom
    (H : Step00CausalClosureAxiom) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictPackage
    (StrictStep00CausalClosurePackage.ofStep00CausalClosure H)

/-#############################################################################
  §3. The accepted external axiom closes the Step00 universe
#############################################################################-/

/- WITHDRAWN (repair): these discharged the refuted finite-key twin boundary
   (twins are now supplied by twinLowersInfinite_from_step00CausalClosure via TimePump). -/

/-#############################################################################
  §4. What exactly follows from the axiom
#############################################################################-/

/--
The audited list of final Step00 consequences of the causal-closure axiom.

This is the precise meaning of "from the axiom everything follows" in this
project:

  * the lower twin centres are infinite;
  * every finite twin bound is impossible once the package data are fixed;
  * the non-axiomatic remaining obligation is exactly this same axiom;
  * the axiom is external-only: an internal self-derivation would be a forbidden
    engine and is therefore impossible in the stable no-engine architecture.
-/
abbrev FinalConsequencesOfStep00CausalClosure
    (C : StrictStep00CausalClosurePackage) : Prop :=
  TwinLowers.Infinite ∧
  (∀ M0 : ℕ, ¬ TwinBoundAbove M0) ∧
  (Step00PipelineClosesWithoutNewAxiom ↔ Step00CausalClosureAxiom) ∧
  ¬ InternalSelfDerivationOfStep00CausalClosure

/--
All audited Step00 consequences follow from one strict causal-closure package.
-/
theorem finalConsequences_of_strictPackage
    (C : StrictStep00CausalClosurePackage) :
    FinalConsequencesOfStep00CausalClosure C := by
  exact ⟨
    twinLowersInfinite_of_strictPackage C,
    no_twinBoundAbove_of_strictPackage C,
    pipelineClosesWithoutNewAxiom_iff_causalClosure,
    no_internalSelfDerivation_step00CausalClosure
  ⟩

/--
All audited Step00 consequences follow from the named causal-closure axiom.
-/
theorem finalConsequences_of_step00CausalClosureAxiom
    (H : Step00CausalClosureAxiom) :
    FinalConsequencesOfStep00CausalClosure
      (StrictStep00CausalClosurePackage.ofStep00CausalClosure H) :=
  finalConsequences_of_strictPackage
    (StrictStep00CausalClosurePackage.ofStep00CausalClosure H)

/- WITHDRAWN (repair): finalConsequences_from_acceptedExternalAxiom discharged the
   refuted finite-key twin boundary. -/

/-#############################################################################
  §5. Negative boundary: why this does not mean "any axiom proves everything"
#############################################################################-/

/--
A marker for arbitrary external causes.  It is deliberately independent from
`Step00CausalClosureAxiom`: a mere external cause is not enough to run the
Step00 proof.
-/
abbrev ArbitraryExternalCause : Prop :=
  True

/--
What is needed is not arbitrary causality, but causality in the precise Step00
same-key generated-flow sense.
-/
abbrev ArbitraryCauseIsNotTheStep00Axiom : Prop :=
  ArbitraryExternalCause ∧
  (Step00CausalClosureAxiom → TwinLowers.Infinite)

/--
The project uses the second conjunct, not the first.
-/
theorem arbitraryCause_marker_and_preciseAxiom_suffices :
    ArbitraryCauseIsNotTheStep00Axiom := by
  exact ⟨trivial, twinLowersInfinite_of_strictCausalClosureAxiom⟩

/-#############################################################################
  §6. Final slogan theorem
#############################################################################-/

/--
Final strict formulation:

  a precise Step00 causal-closure package is equivalent to the last axiom;
  from it every audited Step00 consequence follows;
  in particular, lower twin centres are infinite.
-/
theorem strictCausalClosureAxiom_final_slogan :
    (StrictStep00CausalClosurePackageExists ↔ Step00CausalClosureAxiom) ∧
    TwinLowers.Infinite ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure := by
  exact ⟨
    strictStep00CausalClosurePackageExists_iff_axiom,
    twinLowersInfinite_from_step00CausalClosure,
    no_internalSelfDerivation_step00CausalClosure
  ⟩

/-! Machine honesty of the package-form -/

/-- The package ⟺ the old node (via the family of equivalences). -/
theorem strictPackageExists_iff_lastStep00Obligation :
    StrictStep00CausalClosurePackageExists ↔ TheLastStep00Obligation :=
  strictStep00CausalClosurePackageExists_iff_axiom.trans
    strictLastStep00Obligation_iff_lastStep00Obligation

/-- The package presents a twin at every scale (detector). -/
theorem twin_above_of_strictPackage
    (C : StrictStep00CausalClosurePackage) (M0 : ℕ) :
    ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m :=
  twin_above_of_strictResolves (C.projOf M0) (C.resolves M0)

/-- THE NARROWING HITS THE FIELD: EVERY strict package has scale A ≥ 5
    (the A ≤ 4 branch is machine-refuted by a 5-adic chain). -/
theorem strictPackage_scale_ge_five
    (C : StrictStep00CausalClosurePackage) : 5 ≤ C.A := by
  by_contra hA
  exact no_projection_resolves_at_smallScale (by omega) (C.projOf 1)
    (strictSemanticExtended_resolves_old (C.resolves 1))



/-#############################################################################
  EVENT HORIZON + SINGULARITY OF THE ORIGIN (bricks: step00_event_horizon +
  step00_origin_singularity). The boundary of Step00 interpretability: inside —
  return into the interface (⟹ engine ⟹ empty), beyond the horizon — genuinely
  new non-Step00 information; "0 → 1" is an external boundary event, not a
  RealStep; internalization of the boundary = a forbidden self-cause. The Accepted branches
  use the axiom (AXIOM-TAINTED). Machine honesty: the horizon =
  a renaming of emptiness/nonemptiness of certificates; the alternative collapses
  into a 3-disjunction; the "event 0→1" ⟺ the axiom itself (the markers are True).
#############################################################################-/

/-#############################################################################
  §1. The Step00 event horizon
#############################################################################-/

/--
A proof route is inside the Step00 event horizon exactly when it returns to the
Step00 internal proof interface.
-/
abbrev InsideStep00ProofHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ProofReturnsToStep00Architecture T φ

/--
A refutation route is inside the Step00 event horizon exactly when it returns to
the Step00 internal refutation interface.
-/
abbrev InsideStep00RefutationHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  RefutationReturnsToStep00Architecture T φ

/--
A proof route is beyond the Step00 event horizon exactly when it genuinely
escapes the Step00 proof interface.
-/
abbrev BeyondStep00ProofHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  ProofEscapesStep00Architecture T φ

/--
A refutation route is beyond the Step00 event horizon exactly when it genuinely
escapes the Step00 refutation interface.
-/
abbrev BeyondStep00RefutationHorizon
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop :=
  RefutationEscapesStep00Architecture T φ

/--
Being inside and being beyond the proof horizon are definitionally exclusive.
-/
theorem not_inside_and_beyond_proof_horizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00ProofHorizon T φ)
    (hBeyond : BeyondStep00ProofHorizon T φ) : False := by
  exact hBeyond hInside

/--
Being inside and being beyond the refutation horizon are definitionally
exclusive.
-/
theorem not_inside_and_beyond_refutation_horizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00RefutationHorizon T φ)
    (hBeyond : BeyondStep00RefutationHorizon T φ) : False := by
  exact hBeyond hInside

/-#############################################################################
  §2. What happens inside the horizon
#############################################################################-/

/--
An actual proof that remains inside the Step00 proof horizon constructs the
forbidden engine; hence no such proof certificate exists in the audited
no-engine architecture.
-/
theorem insideProofHorizon_has_no_actualProof
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00ProofHorizon T φ) :
    IsEmpty (T.proves φ) :=
  no_externalProof_under_proofReturn hInside

/--
An actual refutation that remains inside the Step00 refutation horizon also
constructs the forbidden engine; hence no such refutation certificate exists in
the audited no-engine architecture.
-/
theorem insideRefutationHorizon_has_no_actualRefutation
    {T : ExternalProofTheory} {φ : T.Sentence}
    (hInside : InsideStep00RefutationHorizon T φ) :
    IsEmpty (T.refutes φ) :=
  no_externalRefutation_under_refutationReturn hInside

/--
Explicit contradiction form for an actual proof inside the Step00 horizon.
-/
theorem actualProof_insideHorizon_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ)
    (hInside : InsideStep00ProofHorizon T φ) : False := by
  have hEmpty := insideProofHorizon_has_no_actualProof hInside
  exact (IsEmpty.false p)

/--
Explicit contradiction form for an actual refutation inside the Step00 horizon.
-/
theorem actualRefutation_insideHorizon_contradiction
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ)
    (hInside : InsideStep00RefutationHorizon T φ) : False := by
  have hEmpty := insideRefutationHorizon_has_no_actualRefutation hInside
  exact (IsEmpty.false r)

/--
Equivalently: any actual external proof must live beyond the Step00 proof
horizon.
-/
theorem actualProof_must_cross_eventHorizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ) :
    BeyondStep00ProofHorizon T φ :=
  existing_externalProof_forces_proofEscape p

/--
Equivalently: any actual external refutation must live beyond the Step00
refutation horizon.
-/
theorem actualRefutation_must_cross_eventHorizon
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ) :
    BeyondStep00RefutationHorizon T φ :=
  existing_externalRefutation_forces_refutationEscape r

/-#############################################################################
  §3. The external causal boundary
#############################################################################-/

/--
The precise external boundary condition that closes Step00 is not a vague
"external cause".  It is exactly `Step00CausalClosureAxiom` accepted from outside
the internal no-engine derivation interface.
-/
abbrev Step00CausalClosureBeyondHorizon : Prop :=
  ExternalUniverseCause Step00CausalClosureAxiom

/--
Crossing the horizon by accepting the precise causal-closure boundary gives
infinitude of lower twin centres.
-/
theorem causalClosureBeyondHorizon_generates_twins
    (H : Step00CausalClosureBeyondHorizon) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation H

/- WITHDRAWN (repair): acceptedStep00CausalClosure_is_beyondHorizon asserted the
   refuted finite-key twin boundary from the axiom. -/

/--
Therefore the accepted external boundary generates infinitude of lower twin
centres.
-/
theorem acceptedBoundary_generates_twins :
    TwinLowers.Infinite :=
  SerialTwinBoundary.twinLowersInfinite_of_serialTwinBoundary step00CausalClosure

/-#############################################################################
  §4. Why the boundary cannot be internalised
#############################################################################-/

/--
Trying to make the horizon boundary into an internal cause is exactly the
forbidden self-supporting case already audited.
-/
abbrev InternalisedStep00HorizonBoundary : Prop :=
  InternalUniverseCause Step00CausalClosureAxiom

/--
Any internalised horizon boundary builds the forbidden Euclidean engine.
-/
theorem internalisedHorizonBoundary_builds_engine
    (H : InternalisedStep00HorizonBoundary) :
    SomeConcreteEuclideanEngine :=
  internalUniverseCause_builds_engine H

/--
Therefore the Step00 horizon boundary cannot be internalised in the stable
no-engine architecture.
-/
theorem no_internalisedHorizonBoundary :
    ¬ InternalisedStep00HorizonBoundary :=
  no_internalUniverseCause

/--
If the external causal boundary is also claimed to be internally caused, the
claim self-destructs by the forbidden-engine contradiction.
-/
theorem boundary_insideHorizon_selfDestructs
    (H : InternalisedStep00HorizonBoundary) : False :=
  no_internalisedHorizonBoundary H

/-#############################################################################
  §5. Complete local alternative at the horizon
#############################################################################-/

/--
The local alternatives at the Step00 event horizon for an external sentence.

`acceptedBoundary` is the precise causal-closure axiom route.
`proofBeyond` and `refutationBeyond` are genuine non-Step00 escapes.
`engine` is the forbidden returned route.
-/
inductive Step00EventHorizonAlternative
    (T : ExternalProofTheory) (φ : T.Sentence) : Prop where
  | acceptedBoundary :
      Step00CausalClosureBeyondHorizon →
      Step00EventHorizonAlternative T φ
  | proofBeyond :
      BeyondStep00ProofHorizon T φ →
      Step00EventHorizonAlternative T φ
  | refutationBeyond :
      BeyondStep00RefutationHorizon T φ →
      Step00EventHorizonAlternative T φ
  | engine :
      SomeConcreteEuclideanEngine →
      Step00EventHorizonAlternative T φ

/--
An actual external proof gives the horizon alternative `proofBeyond`.
-/
theorem actualProof_gives_eventHorizonAlternative
    {T : ExternalProofTheory} {φ : T.Sentence}
    (p : T.proves φ) :
    Step00EventHorizonAlternative T φ :=
  Step00EventHorizonAlternative.proofBeyond
    (actualProof_must_cross_eventHorizon p)

/--
An actual external refutation gives the horizon alternative `refutationBeyond`.
-/
theorem actualRefutation_gives_eventHorizonAlternative
    {T : ExternalProofTheory} {φ : T.Sentence}
    (r : T.refutes φ) :
    Step00EventHorizonAlternative T φ :=
  Step00EventHorizonAlternative.refutationBeyond
    (actualRefutation_must_cross_eventHorizon r)

/- WITHDRAWN (repair): acceptedBoundary_gives_eventHorizonAlternative used the
   withdrawn acceptedStep00CausalClosure_is_beyondHorizon (refuted finite-key boundary). -/

/--
No forbidden-engine branch can actually be realised.
-/
theorem no_eventHorizon_engine_branch
    {T : ExternalProofTheory} {φ : T.Sentence}
    (E : SomeConcreteEuclideanEngine) : False :=
  no_someConcreteEuclideanEngine E

/-#############################################################################
  §6. Slogan theorem
#############################################################################-/

/--
Formal slogan of this patch.

Inside the horizon, returning proof/refutation mechanisms construct the
forbidden engine.  The Step00-internal successful route is therefore the precise
external causal-closure boundary, and any actual non-axiomatic proof/refutation
must be beyond the Step00 horizon.
-/
abbrev Step00EventHorizonSlogan : Prop :=
  (∀ {T : ExternalProofTheory} {φ : T.Sentence},
      InsideStep00ProofHorizon T φ → IsEmpty (T.proves φ)) ∧
  (∀ {T : ExternalProofTheory} {φ : T.Sentence},
      InsideStep00RefutationHorizon T φ → IsEmpty (T.refutes φ)) ∧
  (Step00CausalClosureBeyondHorizon → TwinLowers.Infinite) ∧
  (¬ InternalisedStep00HorizonBoundary)

/-- The Step00 event-horizon slogan is exactly the already proved audit facts. -/
theorem step00EventHorizon_slogan :
    Step00EventHorizonSlogan := by
  constructor
  · intro T φ hInside
    exact insideProofHorizon_has_no_actualProof hInside
  · constructor
    · intro T φ hInside
      exact insideRefutationHorizon_has_no_actualRefutation hInside
    · constructor
      · intro H
        exact causalClosureBeyondHorizon_generates_twins H
      · exact no_internalisedHorizonBoundary

/--
Scope guard: this is an architecture-relative event horizon, not a claim that
ordinary mathematics itself has an absolute event horizon.
-/
abbrev EventHorizonIsArchitectureRelative : Prop := True

theorem eventHorizonIsArchitectureRelative :
    EventHorizonIsArchitectureRelative := by
  trivial

/-#############################################################################
  §1. Origin markers: zero is not an internal Step00 state
#############################################################################-/

/--
`OriginZero` is a marker for the absence of an already available internal
Step00 causal frame.  It is not a constructor of the concrete Step00 `State`.
-/
abbrev OriginZero : Prop := True

/--
`FirstCausalOne` is a marker for the first admitted causal frame: from this
point on the Step00 language of states, legal steps, ledgers, and ranks is
available.
-/
abbrev FirstCausalOne : Prop := True

/--
The origin singularity is the pre-frame marker.  It carries no internal Step00
edge relation.
-/
abbrev Step00OriginSingularity : Prop := OriginZero

/--
The first causal frame is the post-boundary marker.  It is the first place where
Step00 can speak internally.
-/
abbrev Step00FirstCausalFrame : Prop := FirstCausalOne

/--
The statement that the origin marker is not itself an ordinary internal causal
mechanism is represented by the impossibility of internalising the Step00
horizon boundary.
-/
abbrev OriginZeroIsNotInternalMechanism : Prop :=
  ¬ InternalisedStep00HorizonBoundary

/--
The origin marker is not an internal mechanism of the already-formed Step00
world.
-/
theorem originZero_is_not_internalMechanism :
    OriginZeroIsNotInternalMechanism :=
  no_internalisedHorizonBoundary

/-#############################################################################
  §2. The 0 → 1 transition as an external boundary event
#############################################################################-/

/--
A Step00 origin boundary event consists of the origin marker, the first causal
frame marker, and the precise external causal-closure boundary beyond the
Step00 event horizon.

This is the formal version of: `0 → 1` is a boundary event, not an internal
`RealStep`.
-/
structure Step00OriginBoundaryEvent : Prop where
  origin : Step00OriginSingularity
  firstFrame : Step00FirstCausalFrame
  causalBoundary : Step00CausalClosureBeyondHorizon

/- WITHDRAWN (repair): acceptedStep00OriginBoundaryEvent used the withdrawn
   acceptedStep00CausalClosure_is_beyondHorizon (refuted finite-key boundary). -/

/--
The origin boundary event generates infinitude of lower twin centres, because
its causal content is exactly the already audited external causal-closure
boundary.
-/
theorem step00OriginBoundaryEvent_generates_twins
    (H : Step00OriginBoundaryEvent) : TwinLowers.Infinite :=
  causalClosureBeyondHorizon_generates_twins H.causalBoundary

/--
Therefore the accepted origin boundary generates infinitude of lower twin
centres.
-/
theorem acceptedOriginBoundary_generates_twins :
    TwinLowers.Infinite :=
  SerialTwinBoundary.twinLowersInfinite_of_serialTwinBoundary step00CausalClosure

/-#############################################################################
  §3. Internalising 0 → 1 is the forbidden self-cause
#############################################################################-/

/--
To internalise the origin event is to claim that the Step00 horizon boundary is
caused by an internal Step00 mechanism.  This is exactly the dangerous
self-cause case.
-/
abbrev InternalisedStep00OriginEvent : Prop :=
  InternalisedStep00HorizonBoundary

/--
Any internalised origin event builds the forbidden concrete Euclidean engine.
-/
theorem internalisedOriginEvent_builds_engine
    (H : InternalisedStep00OriginEvent) : SomeConcreteEuclideanEngine :=
  internalisedHorizonBoundary_builds_engine H

/--
No internalised origin event exists in the audited no-engine Step00
architecture.
-/
theorem no_internalisedOriginEvent :
    ¬ InternalisedStep00OriginEvent :=
  no_internalisedHorizonBoundary

/--
The explicit contradiction form: if `0 → 1` is treated as an ordinary internal
Step00 causal step, the horizon-boundary self-cause contradiction follows.
-/
theorem internalisedOriginEvent_contradiction
    (H : InternalisedStep00OriginEvent) : False :=
  no_internalisedOriginEvent H

/--
No forbidden-engine branch can be realised from an internalised origin event.
-/
theorem internalisedOriginEngine_impossible
    (H : InternalisedStep00OriginEvent) : False := by
  exact internalisedOriginEvent_contradiction H

/-#############################################################################
  §4. Boundary event versus internal step
#############################################################################-/

/--
The origin transition is external/boundary-like when it is supplied as a
`Step00OriginBoundaryEvent` and is not internalised.
-/
abbrev OriginTransitionIsBoundaryEvent : Prop :=
  Step00OriginBoundaryEvent ∧ ¬ InternalisedStep00OriginEvent

/- WITHDRAWN (repair): acceptedOriginTransition_is_boundaryEvent used the withdrawn
   acceptedStep00OriginBoundaryEvent (refuted finite-key boundary). -/

/--
The origin transition cannot be both boundary-initialised and internally
self-caused, because the internalised part is already impossible.
-/
theorem originTransition_cannot_be_internal_selfCause
    (H : OriginTransitionIsBoundaryEvent)
    (I : InternalisedStep00OriginEvent) : False :=
  H.2 I

/--
If one insists that the first causal frame causes itself internally, one has not
explained the origin; one has built the forbidden engine.
-/
theorem selfCausedFirstFrame_builds_engine
    (H : InternalisedStep00OriginEvent) : SomeConcreteEuclideanEngine :=
  internalisedOriginEvent_builds_engine H

/--
Consequently, a self-caused first causal frame is impossible.
-/
theorem no_selfCausedFirstFrame :
    ¬ InternalisedStep00OriginEvent :=
  no_internalisedOriginEvent

/-#############################################################################
  §5. Origin slogan
#############################################################################-/

/--
Formal slogan of the patch.

`0` is not an internal Step00 state/mechanism; `1` is the first causal frame;
`0 → 1` is an external boundary-origin event; making it internal produces the
forbidden engine; the accepted boundary gives `TwinLowers.Infinite`.
-/
abbrev Step00OriginSlogan : Prop :=
  Step00OriginSingularity ∧
  Step00FirstCausalFrame ∧
  OriginTransitionIsBoundaryEvent ∧
  (InternalisedStep00OriginEvent → SomeConcreteEuclideanEngine) ∧
  (¬ InternalisedStep00OriginEvent) ∧
  TwinLowers.Infinite

/- WITHDRAWN (repair): step00Origin_slogan asserts OriginTransitionIsBoundaryEvent,
   which needs the withdrawn accepted origin boundary event (refuted finite-key boundary). -/

/--
Scope guard: the `0 → 1` terminology is architecture-relative causal-ledger
language, not a theorem of physical cosmology.
-/
abbrev OriginInterpretationIsArchitectureRelative : Prop := True

/-- The scope guard is immediate. -/
theorem originInterpretationIsArchitectureRelative :
    OriginInterpretationIsArchitectureRelative := by
  trivial

/-! Machine honesty of the horizon/origin-forms -/

/-- "Inside the horizon" ⟺ emptiness of proofs (renaming). -/
theorem insideProofHorizon_iff_noProofs
    {T : ExternalProofTheory} {φ : T.Sentence} :
    InsideStep00ProofHorizon T φ ↔ IsEmpty (T.proves φ) :=
  proofReturns_iff_noProofs

/-- "Beyond the horizon" ⟺ existence of a proof (renaming). -/
theorem beyondProofHorizon_iff_proofExists
    {T : ExternalProofTheory} {φ : T.Sentence} :
    BeyondStep00ProofHorizon T φ ↔ Nonempty (T.proves φ) :=
  proofEscapes_iff_proofExists

/-- The horizon-alternative COLLAPSES into a 3-disjunction (the engine is burnt):
    the axiom ∨ a proof exists ∨ a refutation exists. -/
theorem eventHorizonAlternative_iff
    {T : ExternalProofTheory} {φ : T.Sentence} :
    Step00EventHorizonAlternative T φ ↔
      (Step00CausalClosureAxiom ∨
        Nonempty (T.proves φ) ∨ Nonempty (T.refutes φ)) := by
  constructor
  · intro H
    cases H with
    | acceptedBoundary h => exact Or.inl h
    | proofBeyond h => exact Or.inr (Or.inl (proofEscapes_iff_proofExists.mp h))
    | refutationBeyond h =>
        exact Or.inr (Or.inr (refutationEscapes_iff_refutationExists.mp h))
    | engine h => exact (no_someConcreteEuclideanEngine h).elim
  · rintro (h | hp | hr)
    · exact Step00EventHorizonAlternative.acceptedBoundary h
    · exact Step00EventHorizonAlternative.proofBeyond
        (proofEscapes_iff_proofExists.mpr hp)
    · exact Step00EventHorizonAlternative.refutationBeyond
        (refutationEscapes_iff_refutationExists.mpr hr)

/-- "The event 0 → 1" ⟺ the axiom itself: the markers origin/firstFrame are True,
    the content of the boundary event is exactly causal-closure. -/
theorem step00OriginBoundaryEvent_iff :
    Step00OriginBoundaryEvent ↔ Step00CausalClosureAxiom :=
  ⟨fun H => H.causalBoundary, fun h => ⟨trivial, trivial, h⟩⟩



/-#############################################################################
  §8. EPISTEMICS OF THE FIRST CAUSE: it exists — cannot be known — knowledge finitizes
  (by the author's design; the whole section, except two flagged theorems, is AXIOM-FREE)
#############################################################################-/

/-- "Internal knowledge of the cause" = internal derivation of the boundary (self-proof). -/
abbrev InternalKnowledgeOfCause : Prop := InternalisedStep00HorizonBoundary

/-- **"CANNOT BE KNOWN" — A THEOREM (axiom-free):** internal knowledge
    of the first cause would build a perpetual engine — and there are none (lexRank). -/
theorem cause_unknowable : ¬ InternalKnowledgeOfCause :=
  no_internalisedHorizonBoundary

/-- Knowledge of the cause builds a perpetual engine (axiom-free). -/
theorem knowledge_builds_perpetualEngine :
    InternalKnowledgeOfCause → SomeConcreteEuclideanEngine :=
  internalisedHorizonBoundary_builds_engine

/-- **TARGET THEOREM (the author's design):** knowledge of the cause finitizes twins.
    ⚠️ HONESTY: the proof goes THROUGH the impossible engine (ex falso) —
    see the mandatory companion below. -/
theorem knowledge_finitizes_twins :
    InternalKnowledgeOfCause → ¬ EuclidsPath.TwinLowers.Infinite :=
  fun hK _ => no_someConcreteEuclideanEngine (knowledge_builds_perpetualEngine hK)

/-- COMPANION (machine honesty): from knowledge, infinity also follows —
    knowledge explodes everything; the load-bearing part of the construction is the unknowability itself. -/
theorem knowledge_proves_anything :
    InternalKnowledgeOfCause → EuclidsPath.TwinLowers.Infinite :=
  fun hK => (no_someConcreteEuclideanEngine (knowledge_builds_perpetualEngine hK)).elim

/-- SUBSTANTIVE DICHOTOMY (without ex falso in the statement): either the cause
    is unknowable, or twins are finite. The left disjunct is a theorem. -/
theorem unknowable_or_twins_finite :
    ¬ InternalKnowledgeOfCause ∨ ¬ EuclidsPath.TwinLowers.Infinite :=
  Or.inl cause_unknowable

/-- "No engines ⟹ cannot be known" — a genuine contraposition (not an explosion). -/
theorem unknowable_of_noEngine
    (hNoEngine : ¬ SomeConcreteEuclideanEngine) : ¬ InternalKnowledgeOfCause :=
  fun hK => hNoEngine (knowledge_builds_perpetualEngine hK)

/-- **THE ESSENCE, machine-wise (axiom-free): "twins are infinite, because they cannot
    be known".** The absence of engines (= unknowability) + the accepted causal
    boundary ⟹ twins are infinite. The hypothesis hNoEngine is CONSUMED
    genuinely: from the twin-bound an ∞-family is built, from it — a collision, from
    the collision — an engine-WITNESS, and it is exactly hNoEngine that kills it. -/
theorem twins_infinite_of_noEngine_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : Step00CausalClosureAxiom) :
    EuclidsPath.TwinLowers.Infinite := by
  by_contra hfin
  obtain ⟨M0, hBound⟩ := exists_twinBoundAbove_of_not_twinLowersInfinite hfin
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hStable : NoEnergyStableUniverse (projOf M0) :=
    (noEnergyStableUniverse_iff_resolves (projOf M0)).mpr
      (strictSemanticExtended_resolves_old (hres M0))
  obtain ⟨𝓕, h𝓕⟩ := twinBoundForcesInfiniteExtendedGeneratedFlows_closed hBound
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hNoEngine ⟨A, M0, hEngine⟩

/-- "This is the essence": lexRank supplies the absence of engines as a theorem —
    unknowability and twins are TWO CONSEQUENCES OF ONE CAUSE, and the derivation
    of twins visibly passes through unknowability. ⚠️ AXIOM-TAINTED
    (via the accepted boundary; the load-bearing lemma is axiom-free above). -/
theorem twins_because_unknowable : EuclidsPath.TwinLowers.Infinite :=
  SerialTwinBoundary.twinLowersInfinite_of_serialTwinBoundary step00CausalClosure

/-- The final epistemic status of the first cause: it EXISTS (axiom, accepted),
    it CANNOT be known (theorem), ACCEPTANCE gives twins (conditionally),
    KNOWLEDGE would finitize them (via the collapse of the engine).
    ⚠️ AXIOM-TAINTED (the first and third conjuncts are the decree). -/
theorem epistemicFirstCauseStatus :
    Step00FirstCause ∧
    (¬ InternalKnowledgeOfCause) ∧
    EuclidsPath.TwinLowers.Infinite ∧
    (InternalKnowledgeOfCause → ¬ EuclidsPath.TwinLowers.Infinite) :=
  ⟨step00FirstCause, cause_unknowable,
   twinLowersInfinite_from_step00CausalClosure, knowledge_finitizes_twins⟩

/-#############################################################################
  §9. Consistency tripwires: the explosion point is machine-visible
#############################################################################-/

/- WITHDRAWN (repair): §9–§14 below (the twin/RH/PNP/YM/NS/Hodge consistency
   tripwires and the RH-off-critical reduction) all discharged the refuted
   finite-key twin boundary via `step00CausalClosure`. They are withdrawn: the
   sound twin boundary is now `TimePumpStep00Obligation`, which does not carry the
   finite-key resolution structure these consumed. Twins survive via TimePump; the
   NS gate-law (§15, from the `nsBoundary` field) and the RH manifestation-law field
   are separate axiom fields and are unaffected. See Engine/Step00CompletePatch
   (post-mortem: the finite-key obligation is provably false).

/-- **TRIPWIRE:** if the node is ever refuted (the `A ≤ 4` attack is
    extended to all `A`), the quarantine is inconsistent — False is derivable EXACTLY here.
    The consistency of `T + step00FirstCause` ⟺ the irrefutability of the node in the base.
    ⚠️ AXIOM-TAINTED (intentionally: this is the explosion detector). -/
theorem quarantine_inconsistent_if_node_refuted
    (h : ¬ TheStrictLastStep00Obligation) : False :=
  h step00CausalClosure

/-- The same tripwire via the old node (closes the family of forms). ⚠️ AXIOM-TAINTED. -/
theorem quarantine_inconsistent_if_lastObligation_refuted
    (h : ¬ TheLastStep00Obligation) : False :=
  h (strictLastStep00Obligation_iff_lastStep00Obligation.mp step00CausalClosure)

/-#############################################################################
  §10. RIEMANN THROUGH THE FIRST CAUSE: the second boundary of the decree
  (the same machine as twins: deviation → manifestation → collision →
  engine → lexRank; the green chain — Engine/RiemannManifestationFront)
#############################################################################-/

/-- The Riemann manifestation law, projected from the first cause:
    every off-critical deviation must show itself by an unpayable supply of
    flows where the ledger reconciles the books. ⚠️ AXIOM-TAINTED (this is
    the accepted second boundary of the decree). -/
theorem riemannManifestationLaw : RiemannManifestationLaw :=
  step00FirstCause.riemannBoundary

/-- **RH FROM THE SINGLE EXTENDED DECREE.** ⚠️ AXIOM-TAINTED: this is NOT
    a proof of the Riemann hypothesis — it is a reduction, closed by the extended
    first cause. The chain is honestly rank-based (the same as for twins): a zero off
    the critical line — an unpaid deviation; the accepted twin boundary
    reconciles the books at the scale of the zero's height; the manifestation law forces
    the deviation to show itself by an infinite supply of flows; the collision
    of the finite-key projection builds a forbidden engine; lexRank
    kills it — there is no zero. The classification of trivial zeros is a proven theorem
    (`trivialBelowZeroClassification`). -/
theorem riemannHypothesis_from_firstCause : RiemannHypothesis :=
  riemannHypothesis_of_manifestation_and_boundary
    no_someConcreteEuclideanEngine step00CausalClosure riemannManifestationLaw

/-- **HONESTY (machine-wise, mirror of
    `causalClosureAxiom_asserts_twins_at_every_scale`):** under the accepted twin
    boundary the Riemann boundary ⟺ RH — the second boundary of the decree is exactly of RH strength:
    to accept the extended first cause = to accept RH. The decree is no weaker than the conclusion.
    ⚠️ AXIOM-TAINTED (via the twin boundary). -/
theorem riemannManifestation_asserts_RH :
    RiemannManifestationLaw ↔ RiemannHypothesis :=
  manifestationLaw_iff_RH_of_boundary step00CausalClosure

/-- **TRIPWIRE (Riemann):** if an off-critical zero is ever presented,
    the quarantine is inconsistent — False is derivable EXACTLY here. ⚠️ AXIOM-TAINTED
    (intentionally: the explosion detector). -/
theorem quarantine_inconsistent_if_offCriticalZero_exhibited
    (Z : RiemannOffCriticalZero) : False :=
  noOffCriticalZero_of_manifestation_and_boundary
    no_someConcreteEuclideanEngine step00CausalClosure riemannManifestationLaw
    ⟨Z⟩

/-- **TRIPWIRE (Riemann):** if ¬RH is ever proven, the quarantine is
    inconsistent. The consistency of `T + step00FirstCause` now requires
    also the irrefutability of RH in the base. ⚠️ AXIOM-TAINTED. -/
theorem quarantine_inconsistent_if_RH_refuted
    (h : ¬ RiemannHypothesis) : False := by
  obtain ⟨Z⟩ :=
    EuclidsPath.RiemannImpossibleEngineOff.offCriticalZero_of_not_RH h
  exact quarantine_inconsistent_if_offCriticalZero_exhibited Z

/-- **TRIPWIRE (Riemann):** a refutation of the manifestation law itself — False
    exactly here. ⚠️ AXIOM-TAINTED. -/
theorem quarantine_inconsistent_if_manifestation_refuted
    (h : ¬ RiemannManifestationLaw) : False :=
  h riemannManifestationLaw

-- Machine visibility of the new taint directly in the build log: the RH reduction's
-- axiom list MUST contain step00FirstCause (and only it, beyond the standard ones).
#print axioms riemannHypothesis_from_firstCause

/-#############################################################################
  §11. P/NP LANGUAGE OF THE DECREE: split by scales (there is NO third boundary — intentionally)

  The separation in the author's reading is a GREEN theorem for A ≤ 4
  (`pnp_rank_separation_smallScale`, Engine/PNPRankPaymentFront) and does
  NOT belong to the decree. Below is only what the decree ALREADY asserts at ITS
  scale A ≥ 5 via the existing twin boundary, plus a tripwire.
  The trilemma (same place, green): the universal/decider-gated candidates of the third
  field are refutable, the existential is already proven — an honest third field
  does not exist.
#############################################################################-/

/-- ⚠️ AXIOM-TAINTED: the decree ALREADY gives local P-success at its scale
    (necessarily A ≥ 5) at every M0 — there the finite key resolves collisions. -/
theorem decreedScale_localPSuccess :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      EuclidsPath.LocalPNP.LocalPSuccess
        (EuclidsPath.LocalPNP.Concrete.concreteProblem A M0) :=
  EuclidsPath.PNPRankPayment.boundary_forces_localPSuccess_at_decreed_scale
    step00CausalClosure

/-- ⚠️ AXIOM-TAINTED: at the decree scale the first cause PAYS ALL
    rank certificates (full payment in the author's sense). -/
theorem decreedScale_fullPayment :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      EuclidsPath.PNPRankPayment.FullRankCertificatePayment
        (EuclidsPath.LocalPNP.Concrete.concreteFamily A M0) :=
  EuclidsPath.PNPRankPayment.boundary_forces_fullPayment_at_decreed_scale
    step00CausalClosure

/-- ⚠️ AXIOM-TAINTED: at the decree scale the supply of certificates is BOUNDED —
    the books reconcile, because the supply is finite-key accountable. -/
theorem decreedScale_supply_bounded :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      ¬ EuclidsPath.PNPRankPayment.UnboundedCertificateSupply
        (EuclidsPath.LocalPNP.Concrete.concreteFamily A M0) :=
  EuclidsPath.PNPRankPayment.boundary_bounds_supply_at_decreed_scale
    step00CausalClosure

/-- **TRIPWIRE (P/NP):** if the small incompressibility is ever extended
    to ALL scales, the quarantine is inconsistent — False is derivable EXACTLY here.
    ⚠️ AXIOM-TAINTED (intentionally: the explosion detector). -/
theorem quarantine_inconsistent_if_incompressible_at_all_scales
    (h : ∀ A M0 : ℕ, EuclidsPath.LocalPNP.LocalSearchIncompressible
      (EuclidsPath.LocalPNP.Concrete.concreteProblem A M0)) : False := by
  obtain ⟨A, _, hLP⟩ := decreedScale_localPSuccess
  exact h A 0 (hLP 0)

-- Machine visibility: the P/NP language of the decree is tainted by exactly step00FirstCause.
#print axioms decreedScale_localPSuccess

/-#############################################################################
  §12. YANG–MILLS LANGUAGE OF THE DECREE: the gap of its own world
  (there is NO fourth boundary — intentionally; the trilemma: Engine/YangMillsFront §7;
  the per-model law ⟺ gap is green — to decree it would be = to decree the goal;
  the world of the decree is intrinsically quantized (lexRank : ℕ) — below is only what
  the decree asserts ITSELF.)
#############################################################################-/

/-- ⚠️ AXIOM-TAINTED: at the decree scale (necessarily A ≥ 5) the supply of
    deviations is ABSENT at every M0 — in the world of the first cause there is no infinite
    tower of arbitrarily-cheap excitations: the decree is gapped in the language of supplies. -/
theorem decreedScale_no_deviationSupply :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ, ¬ DeviationFlowSupply A M0 :=
  EuclidsPath.YangMills.boundary_refuses_deviationSupply_at_decreed_scale
    step00CausalClosure

/-- **TRIPWIRE (Yang–Mills):** if a supply of deviations is ever presented
    at ALL scales (including the decree scale A ≥ 5), the quarantine is inconsistent —
    False is derivable EXACTLY here. Safety of the tripwire: the green world knows
    the supply only at A ≤ 4 (`smallScale_deviationSupply`); the forged
    spectral Yang–Mills models live in the spectral world and do not touch this
    statement. ⚠️ AXIOM-TAINTED (intentionally: the explosion detector). -/
theorem quarantine_inconsistent_if_supply_at_every_scale
    (h : ∀ A M0 : ℕ, DeviationFlowSupply A M0) : False := by
  obtain ⟨A, _, hNo⟩ := decreedScale_no_deviationSupply
  exact hNo 0 (h A 0)

-- Machine visibility: the YM language of the decree is tainted by exactly step00FirstCause.
#print axioms decreedScale_no_deviationSupply

/-#############################################################################
  §13. NAVIER–STOKES LANGUAGE OF THE DECREE: there is NO FIFTH boundary — intentionally
  (the trilemma: Engine/NavierStokesFront §7 — the universal is refutable (cookedFlow),
  the existential is already green-proven (the zero solution), the manifestation one
  is incompatible with the accepted boundary (cookedProfileCascade is green-presentable).
  The "gappedness" of the decree's world in the language of supplies — this is already §12
  (decreedScale_no_deviationSupply), no NS duplicate is added. The green
  killer of the uniform singular cascade under balance
  (noSingularCascade_of_energyBalance) — a THEOREM of the front, NOT a decree: the taint
  is not forged. Clay is NOT solved and NOT declared.)
#############################################################################-/

/-- **TRIPWIRE (Navier–Stokes):** if the manifestation form of the fifth field
    is ever accepted or proven, the quarantine is inconsistent — False is derivable
    EXACTLY here (the forged profile cascade is green-presentable; the accepted
    boundary burns the supply at its scale). Safety: the law is not
    green-provable — it is ⟺ the global freezing of all ledgers
    (nsManifestationLaw_iff_no_resolution), and the small scales A ≤ 4 do not
    decide the scales A ≥ 5. ⚠️ AXIOM-TAINTED (intentionally: the explosion detector). -/
theorem quarantine_inconsistent_if_nsManifestationLaw_decreed
    (h : EuclidsPath.NavierStokesFront.NsManifestationLaw) : False :=
  EuclidsPath.NavierStokesFront.nsManifestationLaw_refutes_boundary h
    step00CausalClosure

-- Machine visibility: the NS tripwire is tainted by exactly step00FirstCause.
#print axioms quarantine_inconsistent_if_nsManifestationLaw_decreed

/-#############################################################################
  §14. HODGE LANGUAGE OF THE DECREE: there is NO SIXTH boundary — intentionally
  (the trilemma: Engine/HodgeFront §6 — the universal is refutable (cookedUnpaid),
  the existential is already green-proven (cookedPaid), the chain form is degenerate to
  the green V2 (isEmpty_unpaidDescentChain — the engine is dead unconditionally),
  the manifestation form over the presentable class is incompatible with the accepted
  boundary. The collapse descentLaw_iff_hodgeProperty is green and boundaryless —
  to decree the law = to decree the goal. The "gappedness" of the decree's world in
  the language of supplies — this is already §12, no duplicate is introduced. Clay is NOT solved and NOT
  declared; there is no algebraic geometry in mathlib — the model is abstract.)
#############################################################################-/

/-- **TRIPWIRE (Hodge):** if the manifestation form of the sixth field is ever
    accepted or proven, the quarantine is inconsistent — False is derivable EXACTLY here
    (the forged unpaid class is green-presentable; the accepted boundary burns
    the supply at its scale). Safety of the tripwire: the law is not
    green-provable — it is ⟺ the global freezing of ALL ledgers
    (hodgeManifestationLaw_iff_no_resolution), and the green world knows freezing
    only at A ≤ 4 (no_projection_resolves_at_smallScale); the scales A ≥ 5
    are genuinely open. ⚠️ AXIOM-TAINTED (intentionally: the explosion detector). -/
theorem quarantine_inconsistent_if_hodgeManifestationLaw_decreed
    (h : EuclidsPath.Hodge.HodgeManifestationLaw) : False :=
  EuclidsPath.Hodge.hodgeManifestationLaw_refutes_boundary h
    step00CausalClosure

-- Machine visibility: the Hodge tripwire is tainted by exactly step00FirstCause.
#print axioms quarantine_inconsistent_if_hodgeManifestationLaw_decreed
-/

/-#############################################################################
  §15. THIRD BOUNDARY OF THE DECREE: the gate-law of NS energy balance (finishing blow)
  (the verdict of §13 "there is NO fifth boundary" stands for the gateless and
  manifestation forms; nsBoundary — the surviving gate-candidate: the extended
  trilemma in Engine/NavierStokesFront §§9–11 — the Dirichlet forging kills f=0,
  the forging of forged pressure kills f=0+time; the final gate (time AND
  space) is not forged — its refutation ≥ solving the open steady-NS
  Liouville problem. The HONEST PRICE is disclosed: there is NO "law ⟺ goal" mirror,
  the decree may overpay. Clay is NOT solved and NOT declared.)
#############################################################################-/

/- WITHDRAWN (Option A): NS is no longer a field of the decree — the `nsBoundary` field is
   dropped. The GREEN NS core (`noSingularCascade_of_energyBalance`, conditional on the
   energy-balance law as an explicit hypothesis, NOT the axiom) lives in NavierStokesFront and
   is unaffected. NS is an open/conditional front, not a decree result.
/-- Projection of the THIRD boundary of the decree. ⚠️ AXIOM-TAINTED. -/
theorem nsSolutionBalanceLaw : EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw :=
  step00FirstCause.nsBoundary

/-- ⚠️ AXIOM-TAINTED: the cascade smoothness (a surrogate, NOT C^∞ — disclosed)
    of EVERY gate-solution — from the decree. NOT a solution of Clay. -/
theorem noSingularCascade_from_firstCause
    (ν : ℝ) (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3)
    (p : ℝ → EuclidsPath.NavierStokes.E3 → ℝ) (hν : 0 ≤ ν)
    (sol : EuclidsPath.NavierStokes.IsNSSolution ν (fun _ _ => 0) u p)
    (hdt : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hdx : ∀ t x, DifferentiableAt ℝ (u t) x) :
    EuclidsPath.NavierStokesFront.NoSingularCascade ν u :=
  EuclidsPath.NavierStokesFront.noSingularCascade_of_nsSolutionBalanceLaw
    nsSolutionBalanceLaw ν u p hν sol hdt hdx

/-- ⚠️ AXIOM-TAINTED: the energy identity of gate-solutions from the decree (the integral
    is taken by decree). -/
theorem energyIdentity_from_firstCause
    (ν : ℝ) (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3)
    (p : ℝ → EuclidsPath.NavierStokes.E3 → ℝ) (hν : 0 ≤ ν)
    (sol : EuclidsPath.NavierStokes.IsNSSolution ν (fun _ _ => 0) u p)
    (hdt : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hdx : ∀ t x, DifferentiableAt ℝ (u t) x) (t₁ t₂ : ℝ) :
    EuclidsPath.NavierStokes.kineticEnergy (u t₂)
      = EuclidsPath.NavierStokes.kineticEnergy (u t₁)
        - ∫ s in t₁..t₂, EuclidsPath.NavierStokes.dissipationRate ν (u s) :=
  EuclidsPath.NavierStokesFront.energyIdentity_of_nsSolutionBalanceLaw
    nsSolutionBalanceLaw ν u p hν sol hdt hdx t₁ t₂

/-- **TRIPWIRE (NS gate):** exhibiting a gate-violation (a forceless solution,
    honestly differentiable in t and x, with a failed balance OR
    a non-integrable dissipation) — False exactly here. Safety: such an
    exhibition ≥ solving the open steady-NS Liouville problem; both
    known forgings are killed by the gates machine-wise (dirichletFlow_fails_time_gate,
    cookedFlow_fails_space_gate). ⚠️ AXIOM-TAINTED (intentionally: the explosion
    detector). -/
theorem quarantine_inconsistent_if_nsGatedViolation_exhibited
    (ν : ℝ) (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3)
    (p : ℝ → EuclidsPath.NavierStokes.E3 → ℝ) (hν : 0 ≤ ν)
    (sol : EuclidsPath.NavierStokes.IsNSSolution ν (fun _ _ => 0) u p)
    (hdt : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hdx : ∀ t x, DifferentiableAt ℝ (u t) x)
    (hviol : ¬ (EuclidsPath.NavierStokes.EnergyBalanceLaw ν u ∧
      ∀ t₁ t₂ : ℝ, IntervalIntegrable
        (fun s => EuclidsPath.NavierStokes.dissipationRate ν (u s))
        MeasureTheory.volume t₁ t₂)) : False :=
  hviol (nsSolutionBalanceLaw ν u p hν sol hdt hdx)

-- Machine visibility: the third boundary is tainted by exactly step00FirstCause.
#print axioms noSingularCascade_from_firstCause
-/

/-#############################################################################
  §16. MERSENNE: there is NO FOURTH boundary — INTENTIONALLY, BY THE SIGN OF THE HEURISTIC
  (comment only; there are no declarations — the taint does not change)

  The green machine — Engine/MersenneManifestationFront: the absence witness
  MersenneTwinAbsenceAbove (Π-form, any witness ≥ 29), the gated manifestation
  law, essence M3 (no engines + boundary + law ⟹ Mersenne
  twins are unbounded), the readable form M3⁺ ("a refutation exhibits an
  engine"), audits M5–M9. THE TRILEMMA IS PASSED: the witness is green-
  unpresentable (presentation ≥ solving the open problem about the tail of
  Mersenne twins), the law is not green-decidable, a forged witness does
  not exist (isEmpty_properCenterPeel_five_one — the chain 4c+1 does not peel).
  By the machine criterion the field mersenneBoundary is ADMISSIBLE.

  BUT DEFERRED: ⚠️ the first boundary-candidate with an INVERTED sign of the
  heuristic. Under the boundary the law ⟺ MersenneTwinCentersUnbounded (M7), and
  the heuristic points AGAINST unboundedness (the convergence of Σ over the twin-pairs
  of Mersenne; only p = 3, 5 are known; for p ≡ 3 mod 4 always 5 ∣ 2^p − 3).
  Riemann was a bet on the expectedly-true (RH); Mersenne would be a bet
  against expectations — the consistency of the quarantine is not staked on it.
  The whole strict chain is nonetheless green and lives in the front (the boundary — as a hypothesis).
#############################################################################-/

/-#############################################################################
  §17. THE ARITHMETIC ZOO: SIX FRONTS — there are NO BOUNDARIES, INTENTIONALLY
  (comment only; there are no declarations — the quarantine's taint does not change)

  The green machines: Engine/PolignacManifestationFront (cousins p+4 and sexy p+6),
  Engine/SophieGermainManifestationFront (SG-pairs p, 2p+1 + the 3 mod 4 restriction),
  Engine/GoldbachManifestationFront, Engine/LegendreDesertFront,
  Engine/OddPerfectManifestationFront, Engine/FermatManifestationFront —
  each with a Π- or object-witness, a gated (or object-quantified)
  law, an essence-theorem "no engines + boundary + law ⟹ goal" and
  price audits (X7: under the boundary the law ⟺ the goal).

  THE TRILEMMAS ARE PASSED EVERYWHERE. And yet the FIELDS ARE NOT ADDED:

  * Cousins/sexy, Sophie Germain, Goldbach, Legendre, odd perfect:
    the sign of the heuristic is POSITIVE (Hardy–Littlewood; consensus) — as with Riemann.
    But a SERIAL extension of the decree would devalue the quarantine: an axiom growing
    a field for every passed trilemma stops being an exception and
    becomes a trick. The laws live as definitions in the green fronts
    (the precedent of §16); the consistency of the quarantine is not staked on them.
  * Fermat: the sign is INVERTED STRONGER than Mersenne (only F₀–F₄ are known, F₅–F₃₂
    composite) — the verdict of §16 verbatim.
  * For Goldbach, Legendre and the perfect ones the witness is POINTWISE DECIDABLE
    (Decidable; a forgery is killed by decide) — the strongest form
    of series unpresentability: to present a genuine one = to solve an open problem.
  * There are no forged witnesses anywhere: isEmpty_properCenterPeel_two_one (chain 2c),
    isEmpty_properCenterPeel_three_one (chain 6c²−4c+1); for cousins/sexy/
    Goldbach/Legendre/the perfect ones there is no distinguished chain at all — there is nothing to peel.

  The pearl of the series — GREEN and living in the branch (SophieGermainBranch):
  SG-primes for p ≡ 3 (mod 4) divide and compromise mersenne p — a formal
  fragment of that very heuristic by whose sign §16 deferred mersenneBoundary.
  See prose/44–48.
#############################################################################-/

/-#############################################################################
  §18. COLLATZ: THE FOURTH BOUNDARY — TAKEN AND REMOVED (a post-mortem of the decree)

  HISTORY. The boundary was ACCEPTED as a fourth field
  (`collatzBoundary : ∀ n ≥ 1, RopeCountingLaw n`) by the sign of the heuristic
  (mean drift ×0.864 < 1, halvings/triplings = 2.016 > log₂3) — and the trilemma
  looked passed at the moment of acceptance: a forged refutation was not
  known. The HONEST PRICE was disclosed immediately: "the decree may OVERPAY"
  (only the arrow law ⟹ conjecture is proven; the converse is unknown).

  REFUTATION (machine). It overpaid into falsehood: the prefix-form of the law is FALSE —
  `not_ropeCountingLaw_27` and `ropeLaw_universal_refuted`
  (Engine/CollatzTugOfWar, kernel [propext, Quot.sound]): for the climbing
  trajectory n = 27 there are 41 engine moves versus 29 rope tugs leading to one,
  and no window from the start gives an advantage; the tail in the cycle 1→2→1 does not
  win back the deficit. The heuristic measured the TOTAL balance — but the law required an advantage
  in the window FROM EVERY position, which the climbing orbits violate.

  CONSEQUENCE. The tripwire `collatzQuarantine_inconsistent_if_law_refuted`
  fired exactly as intended: the field is REMOVED from `Step00FirstCause` (otherwise
  the axiom would be inconsistent). Now the Collatz trilemma is closed by a FORGED
  refutation — as with Yang–Mills: the decree path is impossible machine-wise.
  Collatz returns to the status of a green front with an open conjecture:
  the window budget, the HERO reaches_one_of_countingLaw (conditional, per-n),
  "a refutation = a perpetual engine" nonHalting_carries_perpetual_engine —
  everything green is alive. The post-mortem — Engine/CollatzFirstCause. This is a working
  example of the discipline: boundaries fall to forged refutations, and the repository
  records the fall by a theorem, not by oblivion.
#############################################################################-/

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
