# Riemann through the first cause: a deviation the engine cannot afford

<!--navtop-->
[← 37. Riemann fronts](37_RiemannFronts.md) · [Table of contents](00_Overview.md) · [39. P/NP: paying for certificates →](39_PNPRankPayment.md)
<!--/navtop-->



> Lean source: `Engine/RiemannManifestationFront.lean` — the green chain (the module does not import
> the quarantine); `Engine/RiemannLawEpistemic.lean` — the epistemic route;
> `Engine/Step00FrontClosureAudit.lean` — the machine record of why Riemann was WITHDRAWN from the
> decree (Option A); `Engine/RiemannDualEngineFront.lean` — the dual companion route.
> Status notation: 🟢 — proven under the standard
> axioms; 🟡 — proven **conditionally on the axiom** `step00FirstCause`; 🔴 — an open input.
>
> **Status update (Option A).** Riemann is no longer a boundary of the decree. Earlier drafts hung a
> `riemannBoundary` field on `step00FirstCause` and projected RH out of it (🟡); that field and its
> projection have been **withdrawn**, and no Riemann declaration is axiom-tainted any more. What
> survives is a **green conditional reduction**: RH follows from the manifestation law *plus* the twin
> boundary — a reduction, never a decree result. The reason, and the honest asymmetry with the twins,
> is spelled out in "The Riemann boundary, withdrawn (Option A)" below.

## Where we are

The twins went through one and the same machine: green arithmetic on the integers (genealogies, the
rank `lexRank`, the double carry `XY − ZW = 2`, descent, finite-key projections, the pigeonhole —
the boxes principle, see the [glossary](GLOSSARY.md)) reduced everything to a single node of causal
form, and the node we accepted by an intentional axiom — the first cause ([chapter 33](33_CausalFirstCause.md)). The Riemann
Hypothesis looks like a problem from an entirely different world — complex analysis, the zeta
function, nontrivial zeros.

All the more striking, then, that **the very same route runs here too**.

Everything rests on one reformulation. A zeta zero that has slipped off the critical line is an
**unpaid deviation**, of exactly the sort Euclid's engine cannot afford.
The chapter's short formula: *the engine can afford no deviations of the nontrivial zeros.*

## What a zero's deviation is

Let us recall the setting. The nontrivial zeros of the Riemann zeta function lie in the critical
strip `0 < Re s < 1`. The Riemann Hypothesis asserts that all of them sit exactly on the middle line `Re s = 1/2`.
A **deviation** is a zero that has slipped off the line: a nontrivial zero with `Re s ≠ 1/2`. In Lean it has
the precise mathlib type `OffCriticalZero`: it carries `ζ(s) = 0`, a witness of nontriviality, `s ≠ 1` and,
crucially, `Re s ≠ 1/2`. In these terms the Riemann Hypothesis is simply "deviations do not exist".

Our goal is not to study a deviation, but to show that it **cannot exist wherever the books are
reconciled**. The strategy mirrors the twin one:

1. a deviation is obliged to *manifest itself* — at every scale no lower than its "height", wherever
   the ledger (the bookkeeping of flows, see the [glossary](GLOSSARY.md)) reconciles the books, it
   manifests as an infinite family of generated flows;
2. but no such infinite family **exists** at a book-reconciling scale — this is a green theorem: an
   infinite family collides under a finite key and builds a forbidden engine;
3. hence there are no deviations; and together with the already-proven classification of the
   trivial zeros, that is the Riemann Hypothesis.

The first point is a causal law — once the Riemann boundary of the decree, now **withdrawn** (Option A);
what survives is a green conditional reduction. The second is a green theorem.
Let us take them in order.

## The manifestation law: how a deviation gives itself away

What does "a deviation manifests itself" mean? First, assign every zero the natural scale at which it
lives: `zeroHeight Z = ⌊|Im s|⌋` — the integer part of the modulus of the imaginary part. Then we
introduce the key object.

**Definition 38.1** (`DeviationFlowSupply A M0`). An "unpaid supply" at the ledger scale `(A, M0)` is
an infinite admissible family of extended generated flows:
$$\mathrm{DeviationFlowSupply}(A, M_0) \;:=\; \exists\,\mathcal{F} \subseteq \mathrm{ExtProperFlow}(A, M_0),\ \mathrm{InfiniteFamily}(A, M_0, \mathcal{F}). \tag{38.1}$$

Here one detail matters, the detail that makes everything work: this is **exactly the same object**
that the conjecture about the last boundary of twin centres builds in the twin branch. The supply is
no empty abstraction — it is delivered by the genuine rank machine:

**Theorem 38.2** (`deviationFlowSupply_of_twinBound`, 🟢 — a witness of substance). *For any
$A, M_0$, from the bound on twin centres above scale $M_0$ (`TwinBoundAbove M0`), `DeviationFlowSupply A M0`
follows greenly:* $\mathrm{TwinBoundAbove}(M_0) \Rightarrow \mathrm{DeviationFlowSupply}(A, M_0).$

Now the law itself. It says that a deviation is obliged to give itself away by such a supply
wherever the books are reconciled:

**Definition 38.3** (`RiemannManifestationLaw`). For every deviation $Z$ and every scale
$M_0 \ge \mathrm{zeroHeight}(Z)$: wherever the projection $\mathrm{proj}$ reconciles the books
(resolves collisions), there is an unpaid supply `DeviationFlowSupply`:
$$\forall Z\ \forall A, M_0\ \big(\mathrm{zeroHeight}(Z) \le M_0 \Rightarrow \forall \mathrm{proj}\ (\mathrm{Resolves}(\mathrm{proj}) \Rightarrow \mathrm{DeviationFlowSupply}(A, M_0))\big). \tag{38.2}$$

Note the form: the law asserts a *positive event* — "the deviation manifests itself", the causal
link "zero → manifestation". It does **not** assert "there are no zeros". This is essential: the
strength and honesty of the decree depend entirely on the fact that what we put into it is a cause,
not a conclusion.

> **Note (why a deviation is obliged to give itself away).** The supply `DeviationFlowSupply A M0` is
> not a new abstraction but *exactly the same* infinite admissible family of extended generated flows
> that the twin boundary builds greenly (`deviationFlowSupply_of_twinBound`, see above). Both
> storylines are fed by one rank machine. And *why* an off-critical zero is forced to produce it can
> be seen from the balance intuition of the carry of two in [chapter 30](30_RiemannBranch.md): equilibrium at `Re s = 1/2` is
> the point where the gain and loss of mass along the descent compensate each other. The asymmetry `Re s ≠ 1/2` removes
> the compensation and yields a "free" directed pumping of mass — and to pump mass indefinitely is
> precisely to supply flows indefinitely. That is why the law speaks of an *event*: a zero off the
> line leaves a trace — not "there are no zeros".

## The green impossibility: the "cannot" side is a theorem, not a decree

Here is the load-bearing green theorem of the whole chapter. It says that where the books are
reconciled, an unpaid supply cannot exist.

**Theorem 38.4** (`no_deviationFlowSupply_at_resolved_scale`, 🟢). *For any projection
$\mathrm{proj}$ at scale $(A, M_0)$ that resolves collisions, the supply does not exist:*
$\mathrm{Resolves}(\mathrm{proj}) \Rightarrow \neg\,\mathrm{DeviationFlowSupply}(A, M_0).$

**Why this is true.** A resolving projection yields a stable, energy-free universe. Throw an
infinite family of flows into it — the finite key is forced to collide them (pigeonhole), the
collision assembles a witness engine, and engines do not exist (`no_someConcreteEuclideanEngine`).
Exactly the same three-move combination that killed the finiteness of the twins.

> **Note (pigeonhole step by step).** Let us walk through the chain in words. At a scale where the
> projection *reconciles the books*, the universe is stable and without free energy. An infinite
> family of flows, however, does not fit under a finite key — by the boxes principle (pigeonhole) two
> flows must coincide under the projection, and this collision is not harmless: a concrete witness
> engine assembles from it. But no such engine exists — it is killed by
> `no_someConcreteEuclideanEngine`. Hence **no infinite supply survives at a book-reconciling
> scale**: the "cannot" side is a theorem.

This is exactly the watershed of honesty. The **"cannot"** side — that the supply does not exist —
we *prove* greenly. Only the side *"is obliged to manifest"* is decreed. We never postulate the
impossibility of a zero; we postulate only that a zero, if it exists, leaves traces — and the
absence of traces at a book-reconciling scale we derive from the engine prohibition.

## Assembly: no deviations, hence the Riemann Hypothesis holds

Let us join the law, the boundary and the engine prohibition. What emerges is a precise mirror of
the twin essence lemma.

**Theorem 38.5** (`noOffCriticalZero_of_manifestation_and_boundary`, 🟢). *The absence of engines
($\neg\,\mathrm{SomeConcreteEuclideanEngine}$) plus the accepted twin boundary
($\mathrm{TheStrictLastStep00Obligation}$) plus the manifestation law ($\mathrm{RiemannManifestationLaw}$)
imply $\neg\,\mathrm{Nonempty}\ \mathrm{RiemannOffCriticalZero}$ — deviations do not exist.*

All three hypotheses do real work, not through explosion: the boundary yields a resolving projection
exactly at the scale of the zero's height; the law turns the zero into an infinite supply; from the
supply a witness engine is assembled; and it is killed precisely by "engines do not exist". And then
it is a short step to the goal:

**Theorem 38.6** (`riemannHypothesis_of_manifestation_and_boundary`, 🟢). *The same triple of
hypotheses implies $\mathrm{RiemannHypothesis}$ (in the precise mathlib sense).*

Here the only heavy analysis enters, and it has already been done in the preceding chapters: the
classification of the trivial zeros `trivialBelowZeroClassification` is proven by honest mathlib
analysis. Resting on it, RH is extracted from "there are no deviations". Note something important:
this entire chain is **green** — it lives in a module that does not import the quarantine, the only
place where the axiom lives
(see the [glossary](GLOSSARY.md)); the axiom has not yet appeared here.

> **Note (three hypotheses do the work, not an explosion).** In `noOffCriticalZero_of_manifestation_and_boundary`
> every premise carries its own load, and none is smuggled through falsehood. The twin boundary
> yields a *resolving projection* exactly at the zero's height `zeroHeight Z` — where the books can
> be reconciled. The manifestation law turns the zero into an infinite supply `DeviationFlowSupply`.
> From the supply, as in the previous section, a witness engine is assembled. And it is killed by
> `hNoEngine` — "engines do not exist". Remove any of the three — and the conclusion does not
> assemble. The only heavy analysis,
> `trivialBelowZeroClassification`, is honest mathlib work, already done in [chapter 37](37_RiemannFronts.md).
> And "in the precise mathlib sense" means literally: the goal is not a home-made predicate but
> `RiemannHypothesis` from mathlib (the quantifier over all nontrivial zeros of `riemannZeta`, see [chapter 30](30_RiemannBranch.md)).

## The Riemann boundary, withdrawn (Option A)

For one draft the axiom appeared at exactly one further step — when the manifestation law was placed
into the first cause as a Riemann boundary. Under **Option A that field was withdrawn**: the structure
`Step00FirstCause` now carries **only** the twin boundary `causalBoundary` (`SerialTwinBoundaryObligation`),
and `step00FirstCause_iff_causalClosure` reads `Step00FirstCause ↔ SerialTwinBoundaryObligation` — a
single conjunct. The `riemannBoundary` field and its projection `riemannHypothesis_from_firstCause` are
now **dead code**, living inside a `/- WITHDRAWN -/` comment block; no Riemann declaration is
axiom-tainted any more. What we describe next is the historical projection, kept as a record of what
was detached.

**Theorem 38.7** (`riemannHypothesis_from_firstCause`, 🔵 — WITHDRAWN dead code, not axiom-tainted).
*From the single extended decree the Riemann Hypothesis would have followed:*
$\mathrm{riemannHypothesis\_from\_firstCause} : \mathrm{RiemannHypothesis}$ — obtained by applying
Theorem 38.6 (`riemannHypothesis_of_manifestation_and_boundary`) to `no_someConcreteEuclideanEngine`,
the first-cause projection `step00CausalClosure`, and the field `riemannManifestationLaw`. Under
Option A this declaration is withdrawn; it is no longer a live boundary of the decree.

Had it stayed live, the machine axiom list of this theorem would have carried
`[propext, Classical.choice, Quot.sound, step00FirstCause]`, the last word betraying a taint — a
reduction closed by decree, never a proof of the Riemann Hypothesis. Under Option A the field is gone,
so no live Riemann declaration carries `step00FirstCause` at all; the repository taint (16, all
asserting twins) does not include RH.

What survives untouched is the **green conditional reduction**: RH follows from the manifestation law
*plus* the twin boundary (Theorem 38.6), a reduction that never was and never is a decree result.

> **Note (what to read in the axiom list).** After Option A the structure `Step00FirstCause` carries a
> single substantive field, `causalBoundary` (`SerialTwinBoundaryObligation`, the twin boundary); the
> old `riemannBoundary` and the Navier–Stokes gate were detached and now sit in `/- WITHDRAWN -/`
> blocks. In a list such as `[propext, Classical.choice, Quot.sound, step00FirstCause]` the first three are
> the standard axioms of Lean itself (propositional extensionality, choice, quotient soundness);
> almost every ordinary theorem carries them, and only `step00FirstCause` — the repository's single
> decree — stands out. The "taint" is a machine label: a declaration *inherits* the axiom if it stands
> in its dependency list (see [chapter 33](33_CausalFirstCause.md)); the current tainted set is 16, all asserting twins.
> `riemannHypothesis_from_firstCause`, being withdrawn dead code, is **not** among them.

## The honest price: a decree of exactly RH strength — yet not a tautology

A legitimate suspicion arises: have we not hidden the Riemann Hypothesis inside the manifestation
law by simply renaming it? The answer is given machine-wise, and it is subtle.

**Theorem 38.8** (`riemannManifestation_asserts_RH`, 🟢 — a green conditional equivalence). *Under the
twin boundary taken as a hypothesis, the manifestation law is equivalent to RH:*
$\mathrm{RiemannManifestationLaw} \iff \mathrm{RiemannHypothesis}.$

So yes: *the manifestation law, under the twin boundary, is exactly RH strength* — the reduction is no
weaker than the conclusion, and we do not hide this, we prove it. Note that under Option A this is a
green conditional (the twin boundary enters as a hypothesis, not as the axiom); Riemann is no longer
placed into the decree, so no extended first cause is asserted here.

But here lies the difference between an honest law and a forgery. There is the condemned "bridge"
`OffCriticalRiemannEngineBridge`, for which `offCriticalBridge_iff_RH` is proven — it is equivalent
to RH **on its own, greenly, with no hypotheses whatsoever**. Such a bridge would be a verbatim
renaming of the goal, and decreeing it would be dishonest. Our manifestation law is built
differently: the implication "law ⟹ RH" *does not assemble at all without the boundary* — the
essence lemma requires the boundary.

**Conclusion.** The law is a causal condition *on top of*
the already-accepted twin boundary; its RH strength shows itself only paired with it, never alone.

> **Note (what exactly the difference in price is).** Both objects are equivalent to RH — but
> differently, and the difference is honest. `offCriticalBridge_iff_RH` holds *alone*: the condemned bridge `OffCriticalRiemannEngineBridge`
> is equivalent to RH by itself, without a single hypothesis — that is, it is a literal renaming of
> the goal, and decreeing it would be hiding RH under another name. `riemannManifestation_asserts_RH` holds
> *only in a pair*: the law is equivalent to RH only *under the already-accepted* twin boundary —
> without the boundary the essence lemma does not assemble. What we decree is not a renamed goal but
> a causal condition on top of a boundary we have already accepted anyway. Exactly the same
> architecture as with the twins: the node yields the twins not by itself, but only once accepted by
> decree.

This is exactly the same construction as with the twins: the node by itself does not yield the
twins — they are yielded by the node *accepted by decree*. The symmetry of the two branches is no
accident: it is one architecture, applied twice.

> **Note (zeros as energy levels: the Hilbert–Pólya conjecture).** Our reformulation has a deep
> physical shadow. Hilbert and Pólya conjectured that the nontrivial zeros of zeta are the
> eigenvalues of some self-adjoint operator — that is, the **energy levels** of a quantum system.
> The spectrum of a self-adjoint operator is *real* — and that would drive all the zeros exactly
> onto the critical line: RH would become a statement about the realness of the spectrum, about the
> stability of an equilibrium. A zero's deviation from the line, in this picture, is a complex
> eigenvalue — a *resonance with nonzero imaginary part*, an unstable mode pumping energy. Our
> language says literally the same thing: an off-critical zero is a deviation that would have to be
> "paid for" indefinitely by a supply of flows — that is, a perpetual engine. The stability of the
> spectrum and the impossibility of a perpetual engine turn out to be one and the same prohibition,
> read in two languages.

> **Note (the spectral anchor).** Hilbert–Pólya is now more than an image: `Engine/RiemannSpectralAnchor.lean`
> formalises it in two layers — and the difference between them is itself a lesson in honesty. The
> naive realisation of the zeros by a "bare" real spectrum — a set `E ⊆ ℝ` giving every zero the form `1/2 + t·I`
> (`SpectralRealisation`) — assembles *for free*: under RH take `E := Set.univ`, `t := ρ.im`, and the audit
> `spectralRealisation_iff_RH` proves that this input is verbatim equivalent to RH — a mirror of the
> condemned bridge `offCriticalBridge_iff_RH`, a renaming of the goal without a carrier. A
> substantive anchor is therefore obliged to carry **the operator itself**: `OperatorSpectralAnchor`
> — a self-adjoint operator on a Hilbert space whose spectrum is real *for a reason*, not by decree
> (the bridge
> `operatorAnchor_implies_realisation` via mathlib's `IsSelfAdjoint.mem_spectrum_eq_re`). This is a
> red input: the operator itself mathematics must present, and it is not in mathlib v4.31 — nor is
> the spectral theory of unbounded operators, which an honest Hilbert–Pólya requires.

## The dual companion route

Alongside lies `Engine/RiemannDualEngineFront.lean` — three abstract cores awaiting future
instantiation: synchronisation of the payments of the "phantom" (spectral) and the "genuine"
(rank-flow) engines (a one-sided payment = a perpetual engine, hence the payments are synchronous);
the law "meeting ⟺ rank change at the seam"; and the counting bridge "twins ↔ meetings ↔ zeros"
with built-in protection against degeneration (infinity is transported only along injective bridges
with a decoder).

The honest boundary: all the laws of this series are
🔴 field-inputs; there are no unconditional strong conclusions in it; moreover, the bridge counts
*nontrivial* zeros, not off-critical ones, so filling it would carry no RH information directly.
This is a language and scaffolding, not a bridge.

## Riemann beyond the same horizon

The wall against which internal solutions shatter ([chapter 56](56_CollatzFirstCause.md)) has a
Riemann slope too. Let us ask directly: what would "solving Riemann from inside" mean in our
language? Not presenting a zero, and not deriving RH, but *self-grounding the manifestation law*:
carrying simultaneously the law itself and a witness that it was obtained from beyond one's own
horizon.

The module `Engine/RiemannLawEpistemic.lean`
records this literally: the bundle `InternalisedRiemannGround` holds the field `ground` — the law
itself — and the field `beyondOwnHorizon`. And such a bundle self-destructs:

**Theorem 38.9** (`no_internalisedRiemannGround`, 🟢). *Internal self-grounding of the manifestation
law is impossible:* $\mathrm{InternalisedRiemannGround} \Rightarrow \mathrm{False}$, whence
`riemannCause_unknowable` 🟢 — $\neg\,\mathrm{InternalKnowledgeOfRiemannCause}$ (the mirror of
`collatzCause_unknowable` and `pnpCause_unknowable`). **"It cannot be known from inside" is here a
theorem, not a slogan.**

Honesty at once: the bundle is formal,
`beyondOwnHorizon` is simply `¬ground`, a tautological pair of the form P ∧ ¬P, exactly as with
Collatz, and we do not hide this.

What pays for the form is a genuine construction. The only internal trace of a deviation is a
perpetual engine:

**Theorem 38.10** (`deviation_carries_engine_at_resolved_scale`, 🟢). *From the deviation's supply at
a resolving scale a concrete Euclidean engine is assembled:*
$\mathrm{Resolves}(\mathrm{proj}) \wedge \mathrm{DeviationFlowSupply}(A, M_0) \Rightarrow
\mathrm{SomeConcreteEuclideanEngine}$ (a stable energy-free universe, an infinite family, the
pigeonhole collision of a finite key), consuming its hypotheses genuinely, not through falsehood. It
is the same chain as inside Theorem 38.4 (`no_deviationFlowSupply_at_resolved_scale`), but with the
engine made explicit in the conclusion.

(There is also the ex-falso companion `internalisedRiemannGround_builds_engine` — a route whose only
strength is the inconsistency of its premise (see the [glossary](GLOSSARY.md)) — but the
load-bearing part is not it.)

A caveat
is obligatory: unlike the object-level unconditional Collatz `nonHalting_carries_perpetual_engine`,
the Riemann engine is *gated* by the resolving scale — and the resolution is precisely the open twin
node (for
A ≤ 4 it is refuted by `no_projection_resolves_at_smallScale`). This is exactly the Collatz level —
and below the P/NP benchmark, where `beyondOwnHorizon` is inhabited greenly.

The summary is the three-way fork:

**Theorem 38.11** (`riemann_no_internal_decision_without_engine`, 🟢). *A conjunction of three
statements:* (1) to refute on reconciled books is to build an engine
($\mathrm{Resolves}(\mathrm{proj}) \wedge \mathrm{DeviationFlowSupply}(A, M_0) \Rightarrow
\mathrm{SomeConcreteEuclideanEngine}$, killed by the lexRank); (2) to self-ground is to self-destruct
($\mathrm{InternalisedRiemannGround} \Rightarrow \mathrm{False}$); (3) only the external decree
decides — the law under the boundary yields RH ($\mathrm{TheStrictLastStep00Obligation} \Rightarrow
\mathrm{RiemannManifestationLaw} \Rightarrow \mathrm{RiemannHypothesis}$). **Both internal paths cost
an engine; one door is open, and it is external.**

Moreover, in this module the boundary figures as
the hypothesis `h : TheStrictLastStep00Obligation`,
not as an axiom: the conjunct remains a green implication, the module does not import the
quarantine, and the repository's taint does not grow. The final status is collected in
`riemann_locked_behind_engine_status` 🟢.

And the difference from the neighbours along the horizon. P/NP had no decree boundary, the Collatz one
fell — and under **Option A the Riemann boundary was withdrawn as well**: the field `riemannBoundary`
was detached from the first cause and no longer stands there. What remains is the green conditional
reduction, whose price is disclosed above (`riemannManifestation_asserts_RH` — the law is equivalent to
RH *only under* the twin boundary, never on its own). The one boundary the decree still carries is the
twins.

The epistemics neither cancels this nor props it up: it says only that a self-grounding of the
manifestation law can have no *internal* footing — the engine that would decide for us is forbidden by
the same machine with which we prove everything. The external door remains the only one, and it opens
through the twin boundary alone.

> **Note (what we do NOT claim).** This is not a solution of the Riemann Hypothesis and NOT Gödel:
> no independence, no fixed point — only the pigeonhole wall, and all the epistemics is
> model-internal. About RH itself the theorems of this section say nothing — it remains open, and
> this status does not move it. The conditionality is single and named: the third prong of the fork
> works only under the twin boundary (`TheStrictLastStep00Obligation`
> as a hypothesis) — in the quarantine it is accepted by decree with the price disclosed, here it
> remains an implication.

## Place in the greater arc

After this chapter the picture is asymmetric, and Option A names the asymmetry. The twins enter the
decree through the single boundary `causalBoundary` (`SerialTwinBoundaryObligation`); Riemann *once*
entered through `riemannBoundary`, but that field was **withdrawn** — it lives now in a `/- WITHDRAWN -/`
block, detached from the first cause. What both branches still share is the green rank machine; what
only the twins still carry is a live decree boundary. The Riemann side keeps its green conditional
reduction (law + twin boundary ⟹ RH), whose price is disclosed machine-wise, but it is no longer a
boundary of the decree and adds nothing to the taint.

`twin_prime_conjecture` remains `sorry`; the open 🔴 inputs of the remaining Riemann fronts
([chapter 37](37_RiemannFronts.md)) are untouched and remain honest maps of obligations. Next, the
same machine meets a problem where the decree unexpectedly turns out to be *unnecessary* — P/NP
([chapter 39](39_PNPRankPayment.md)): there the inequality is proven greenly, without any first
cause.

<!--navbot-->

---

[← 37. Riemann fronts](37_RiemannFronts.md) · [Table of contents](00_Overview.md) · [39. P/NP: paying for certificates →](39_PNPRankPayment.md)
<!--/navbot-->
