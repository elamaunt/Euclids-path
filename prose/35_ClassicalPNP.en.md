# 35. P/NP: the local node and the classical bridge

<!--navtop-->
[← 34. The Mersenne branch](34_MersenneBranch.md) · [Table of contents](00_Overview.md) · [36. Navier–Stokes: the equation →](36_NavierStokes.md)
<!--/navtop-->



> Lean: `Engine/LocalPNPNode.lean` (the abstract node + a concrete instantiation),
> `Engine/ClassicalPNPBridge.lean` (the classical frame, the bridge, the extraction layer),
> `Engine/CanonicalSelfReduction.lean` (faithful frames, the fuel protocol, generic closure of run),
> `Engine/RankClosureFront.lean` (the rank-closure series, 6 bricks),
> `Engine/ClassicalFrontierRoutes.lean` (the classical front, 42 bricks in a single assembly),
> §12/§12bis `PvsNPAnalogy` in `Engine/ConcreteStep00Graph.lean`.
> Prose predecessor: [24. BoundaryDecomp](24_BoundaryDecomp.md), the section "The structural P/NP analogy".
> This chapter contains *no* yellow declarations: the axiom `step00FirstCause` is used nowhere;
> everything is either 🟢 proven under the standard axioms or 🔴 open.

In [24](24_BoundaryDecomp.md) we noticed that the twin wall has a recognisable computational anatomy: the engine's
forward motion is cheap to verify, while the backward search for a genealogy does not compress into
a finite key. Back then this was an observation inside a single file.

The present chapter takes apart what it has grown into: the asymmetry
has become a theorem of a concrete graph (and, at small scales, an unconditional one), the final
twin node has acquired an exact P/NP form, an abstract local node has been built around it, and
from the node runs an honest conditional bridge to the classical complexity classes.

Let us fix the frame at once, so as not to raise false
expectations: **nothing about the real P and NP is proven here** — there are no Turing machines,
no encodings, no theorem "P ≠ NP" in the repository, and this is recorded machine-wise
(`localPNP_scopeGuard`, `bridgeScopeGuard`, see the final section).

## The asymmetry as a theorem of a concrete graph

On the `6m±1` graph both sides of the analogy are proven (🟢, `PvsNPAnalogy` in `ConcreteStep00Graph.lean`).
The P-side: `pathN_len_le_lexRank` — any forward path of length $n$ from a state $X$ has
$n \le \mathrm{lexRank}(X)$, so every genealogy "is verified cheaply" (`VerificationEasy`,
`verificationEasy_always` — a property of *all* flows, not a hypothesis).

The NP-side:
`search_not_compressible_of_infinite` — on an infinite family of states a finite projection key
loses information (`finite_key_cannot_determine_state_on_infinite`), that is, the backward search
does not compress into a finite certificate. Both sides at once are given by
`verify_easy_but_search_not_compressible` — the asymmetry "verification is easy / search is
incompressible" is here not a slogan but a conjunction of two machine facts.

Moreover, at small scales the incompressibility is **unconditional**: `concrete_localSearchIncompressible_smallScale`
(🟢, `LocalPNPNode.lean`) proves for $A \le 4$ that no finite-key resolver
exists — the infinite 5-adic chain of flows (`fiveAdicChainFlow`) produces, by pigeonhole (a finite
key cannot injectively label an infinite family, see the [glossary](GLOSSARY.md)), a
same-key collision, while both resolution alternatives at $A \le 4$ are already refuted
(`no_extendedFlowResolutionAlternative`).

An irony that must be spoken out loud honestly: this is the very same
5-adic chain that in [24](24_BoundaryDecomp.md) narrowed the final twin node down to $A \ge 5$. The unconditional
incompressibility theorem lives exactly on the scale that is *dead* for the twins; on the live
scale $A \ge 5$ the question is open 🔴.

## The twin node is a P/NP node

§12bis pins down the link: `twin_reduction_is_pnp_node` (🟢) — `TheLastStep00Obligation`
("a finite certificate of genealogy collision resolution suffices") implies `TwinLowers.Infinite`.

This is a restatement of the already known `twinLowersInfinite_of_lastStep00Obligation`, but it
gives the node a name in the new language: the sole remaining input of the whole twin branch (an
input, or gate, is an honestly named red statement still missing on the way to the goal, see the
[glossary](GLOSSARY.md)) — the question "does a polynomial certificate of the backward path
suffice", that is, `PolyCertificateSuffices` =
`SemanticFlowLedgerCollisionResolves` in P/NP clothing.

The conditional side is proven too:
`branch_closes_if_polyCertificateSuffices` — if the certificate suffices AND the family of
genealogies is infinite, the branch collapses. The node itself is neither presented nor refuted
(🔴), and the §2 theorem explains why it does not come for free: the certificate loses
information, so "the certificate suffices" is additional fan-in arithmetic, not a consequence of
compression.

## The local node: the abstraction and its habitability

`LocalPNPNode.lean` extracts this structure into an abstract brick: `RankedForwardGraph` (the rank
strictly drops at a step), genealogy certificates with the P-side proven (`PathN.len_le_lexRank`,
`GenealogyCertificate.verificationEasy_always`), the pigeonhole principle `FiniteKeyCollisionPrinciple`.

On top of that — the local P-success `LocalPSuccess` and its negation `LocalSearchIncompressible`, a twin
detector (`localP_success_detects_twin`, `twinBound_forces_localSearchIncompressible`) and the
semantic interface `localPSuccess_iff_semanticFlowLedgerCollisionResolves`. The resulting
package is `localPNP_status_slogan` (🟢).

The key question for any such abstraction is whether it is inhabited. Here it is, and not in a toy
way: the graph of the instantiation is the repo's Step00 graph **itself** (`concreteGraph` =
`State`/`RealStep`/`lexRank`), the certificates are injective (`concreteCertificate_injective` —
data fields plus proof irrelevance).

Further down the list: local P-success is equivalent to the existence of the repo's resolving
projection (`concreteSemanticInterface`), the detector is `twin_above_of_resolves` from
[24](24_BoundaryDecomp.md) (`concreteTwinDetector`). At $A \le 4$ a full status package is
assembled, `concreteLocalPNPStatus_smallScale` (🟢), where the collision principle is an
unconditional theorem (`concrete_collisionPrinciple_smallScale`), not a parameter.

## The classical frame: honesty before the bridge

`ClassicalPNPBridge.lean` introduces `ClassicalComplexityFrame`: the predicates `InP`/`InNP` on
languages plus closure of P under poly-preimages. And here the module exposes its own chief
weakness itself: **InP and InNP are abstract**. The theorem `trivialFrame_separates_for_free`
(🟢, a deliberate anti-theorem) shows that a frame with `InP := False`, `InNP := True` "separates
the classes" *for free* — that is, `ClassesSeparate` relative to an arbitrary frame costs nothing.

The loop of honesty is closed in
`CanonicalSelfReduction.lean`: `FaithfulPFrame` demands concrete deciders behind `InP` and
membership of `TrueLanguage`/`FalseLanguage` in the class P — and `trivialFrame_not_faithful` (🟢)
proves that the degenerate frame does not satisfy this. The degeneracy is cut off machine-wise,
but the other side of the coin must be said aloud: until `FaithfulClassicalFrame` is instantiated
with a real model of machines, no `ClassesSeparate` in these files speaks of the real P/NP.

## The bridge and its load-bearing field

The bridge itself is `Step00ToClassicalBridge`: an encoding of the local node as a classical
language, where the NP-side (`verifier_yields_NP`) is the easy half, and the load-bearing field is
**`P_decider_extracts_local_success`**: any P-solver of the encoded language is obliged to yield
a local resolver.

Given that field, the conditional theorems are proven (🟢):
`classicalSeparation_of_localIncompressible`, `classicalSeparation_under_twinBound`,
`classicalSeparation_at_smallScale` — the node's incompressibility plus the bridge yield a
separating language (relative to the frame!). The remainder is honestly named:
`RemainingClassicalBridgeObligation`.

The extraction layer unfolds the load-bearing field into a construction: `PDecider` (a
sound/complete solver), `ConcretePAccess` (from the abstract `InP` — a real solver),
`LocalResolverTarget`, `CanonicalResolverReconstruction`, and
`PDeciderExtractionField.extracts_local_success` (🟢) assembles out of them exactly the missing
`C.InP L → N.LocalPSuccess`.

Then `CanonicalSelfReduction.lean` turns the
reconstruction into an algorithm: a bounded adaptive query protocol
(`BoundedAdaptiveQueryProtocol`, the fuel strictly drops at a step), a terminal decoder
(`TerminalResolverDecoder`), and — an important generic fact — the termination of the fuel
executor is **proven**: `runSteps_done_of_fuel` (🟢, strict fuel descent + descent in ℕ), so the
fields `run`/`run_done` are closed by the constructor `selfReduction_of_protocol_and_decoder`
once and for all.

The live remainder of the front is `FaithfulSelfReductionFront`: a protocol + a decoder + a
faithful frame + the node's incompressibility; all of this is 🔴 not instantiated on the live
scale.

## The front v2–v8 and its audit

The repository then unrolls a wide front of routes. `RankClosureFront.lean`: all
False-conclusions are hypothesis-dependent, and the "P-neq-NP-shaped" `rankLocalClasses_do_not_coincide`
is conditional on `RankSeparationWitness`, **which is constructed nowhere** — and is itself a
renamed-conclusion input ("inNP + unbounded" fed in as an input); in the house dialect this is a
goal renaming — a "law" equivalent to the goal itself (see the [glossary](GLOSSARY.md)).

`ClassicalFrontierRoutes.lean` (42 bricks:
the frontier manifests v2–v8, circuit ladder, proof complexity, FP/FNP, bitwise decision-to-search)
went through an assembly audit with explicit flags in the header: `falseDecider` was removed —
the brick claimed a decider of any language by the constant false and was false as stated; a
duplicate was excluded; two Prop-as-proof defects were repaired by strengthening the inputs.

Further along the flags: about 30 slogan-abbrevs are literally
`Prop := True` (markers, not theorems), the audit gates `gate/gate_proof` are everywhere
instantiable by `True` (the same is honestly shown for the bridge too:
`PDeciderExtraction.regateReconstruction`); the renamed-conclusion inputs
(`BitwiseClassicalBridgeFront` and its kin) carry `local_incompressible` as a ready-made field —
their `ClassesSeparate` is a repackaging of the hypothesis. The audit's outcome: **there are no
unconditional `ClassesSeparate`/`False` in the front; there is no `sorry`/`axiom`.**

## Scope and the place in the greater arc

The boundaries of the claims are recorded as theorems: `localPNP_is_architecture_local` and `bridgeScopeGuard_ok`
(🟢, trivial by construction — and that is honest: they document the absence of a claim, they do
not prove its impossibility). The repository has no model of Turing machines, no encodings and no
polynomial time bounds; the words "P" and "NP" everywhere mean the Step00-local roles
"rank-bounded verification" and "incompressible backward search".

What the chapter adds to the programme's greater arc: the twin wall is now
not only an arithmetic fact ([24](24_BoundaryDecomp.md)) and an energetic one (the energy-ledger forms there as
well) but also a computational one — the sole input `TheLastStep00Obligation` is isomorphic to the
question "does a finite certificate suffice against a branching search", and on the refuted scale
$A \le 4$ the answer is machine-checked "no". Should the node ever fall at $A \ge 5$, the bridge
will immediately turn that into a separation of classes — but only relative to a frame that is
yet to be made faithful.

**Conclusion.** Until then: the analogy is a theorem,
the bridge is a conditionality, the classical P/NP are untouched. `twin_prime_conjecture` remains
a `sorry`.

## Postscript (chapter 39, vacuity no. 4)

The adversarial audit of chapter 39 exposed, about the fronts of *this* chapter: `PDecider`
carries no complexity content and is classically constructed for any language
(`classicalPDecider` 🟢), so the decider-gated extraction fronts
(`FaithfulSelfReductionFront`, `CurrentExtractionFront`), which tie the
reconstruction to incompressibility, are *classically empty* (`IsEmpty` — theorems) —
their `gives_classicalSeparation` are vacuous, that is, they hold for free while asserting
nothing (for vacuity, see the [glossary](GLOSSARY.md)). This is the programme's **vacuity no. 4**.

The InP-gated bridge (`Step00ToClassicalBridge`) is not affected — `InP` is abstract;
but the layer of frames is plastic in both directions (`allPFrame` is faithful and coincides for
free, `constantsFrame` is faithful and separates for free). The inequality itself, in the rank
model, is a 🟢 theorem: see [39_PNPRankPayment.md](39_PNPRankPayment.md)
("NP = full payment of rank certificates" — `concrete_localPSuccess_iff_fullPayment`;
the separation — `pnp_rank_separation_smallScale`; the trilemma — a decree bypass is
machine-impossible).

<!--navbot-->

---

[← 34. The Mersenne branch](34_MersenneBranch.md) · [Table of contents](00_Overview.md) · [36. Navier–Stokes: the equation →](36_NavierStokes.md)
<!--/navbot-->
