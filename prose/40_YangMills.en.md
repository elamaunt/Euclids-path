# Yang–Mills: a massless spectrum as a perpetual engine

<!--navtop-->
[← 39. P/NP: paying for certificates](39_PNPRankPayment.md) · [Table of contents](00_Overview.md) · [41. Navier–Stokes: smoothness →](41_NSSmoothness.md)
<!--/navtop-->



> Lean source: `Engine/YangMillsFront.lean` — the green chain and the trilemma, all 🟢;
> `Engine/CausalClosureAxiom.lean` §12 — the YM language of the decree.
> Status legend: 🟢 — proven under the standard axioms;
> 🟡 — proven conditionally on the axiom `step00FirstCause`; 🔴 — an open input.

## The reading: masslessness is a perpetual engine

The Yang–Mills mass-gap problem asks us to prove that a quantum gauge theory has a **gap** — a minimal positive price of excitation above the vacuum. The negation of the gap is *masslessness*: excitations of arbitrarily small positive energy.

And here is the observation around which the whole chapter is built: *a massless spectrum is a perpetual engine.* If above the vacuum there are excitations of any, arbitrarily small energy, then work can be drawn from the vacuum with no lower limit — an infinite tower of ever cheaper modes, an infinite pumping out of "nothing".

The existence of the gap is exactly the prohibition of such a tower.

Let us at once draw the honest boundary, as in [chapter 36](36_NavierStokes.md) on Navier–Stokes: *we do NOT solve the millennium problem and do NOT declare it solved.* There is no gauge theory in mathlib — no Hamiltonian, no spectrum of a genuine QFT.

We work with an abstract spectral model and prove the half that does not depend on the concrete theory.

## Spectrum, gap, masslessness

We abstract down to the necessary. A **spectral model** `SpectralModel` is a set of energy levels `Energy : Set ℝ` with vacuum `0` and nonnegativity (no Yang–Mills content beyond a future instantiation — disclosed in the docstring).

On it, two notions. The **mass gap** `MassGap S` — the existence of a `Δ > 0` below all nonzero levels. **Masslessness** `Gapless S` — the presence of levels of arbitrarily small positive energy. They are exact negations of each other:

**Theorem 40.1** (`not_massGap_iff_gapless`, 🟢). *The absence of a gap is equivalent to masslessness* (and,
pleasingly, without any choice): $\neg\,\mathrm{MassGap}(S) \iff \mathrm{Gapless}(S)$, where $\mathrm{MassGap}(S) := \exists\,\Delta>0,\ \forall E\in S.\mathrm{Energy},\ E\neq 0 \Rightarrow \Delta \le E$ and $\mathrm{Gapless}(S) := \forall \varepsilon>0,\ \exists E\in S.\mathrm{Energy},\ 0<E<\varepsilon$.

## The engine: the ladder of masslessness

What exactly makes masslessness an engine? From it one builds a **ladder** — a halving chain of levels,
dropping by no less than half at each step: `2·E(n+1) ≤ E(n)`, all terms positive. This is nothing
other than the ℝ-counterexample `real_positive_work_not_wellfounded` from the cascade warning of [chapter 36](36_NavierStokes.md):
positive work with no lower limit, an infinite multiplicative descent in the real numbers,
where acyclicity *does not work*.

**Theorem 40.2** (`gapless_iff_nonempty_ladder`, 🟢). *Masslessness is equivalent to the existence of a ladder:* $\mathrm{Gapless}(S) \iff$ the type of ladders $\mathrm{GaplessLadder}(S)$ is nonempty, where a ladder is a sequence $E:\mathbb{N}\to\mathbb{R}$ with $E(n)\in S.\mathrm{Energy}$, $E(n)>0$ and $2\cdot E(n+1)\le E(n)$ for all $n$.
The forward direction builds the ladder by choice — a mirror of the zero extraction in the Riemann branch; the converse shows
that a ladder refutes any candidate `Δ` (by a geometric majorant). The ladder is the engine, and
as long as it lives in the real numbers, acyclicity cannot touch it.

## The quantization law and the hero: quantization ⟹ gap

The engine is killed exactly when the ladder can be *reflected into the natural numbers*. This is
the physical input of the branch — the quantization law.

**Definition 40.3** (`QuantizationLaw`, 🔴 — an input, the `EnergyBalanceLaw` pattern). Every positive
state carries a natural rank, and multiplicative descent of energy is reflected into a *strict* descent
of rank: $\mathrm{QuantizationLaw}(S) := \exists\,\mathrm{rank} : \mathrm{PositiveState}(S)\to\mathbb{N},\ \forall x,y,\ 2\cdot(y:\mathbb{R})\le(x:\mathbb{R}) \Rightarrow \mathrm{rank}(y) < \mathrm{rank}(x)$.

Once this is in hand, the ladder turns from real into natural — and breaks off:

**Theorem 40.4** (`no_quantizedLadder`, 🟢). *A quantized ladder does not exist:* $\mathrm{QuantizationLaw}(S) \wedge \mathrm{GaplessLadder}(S) \Rightarrow \bot$. It would be an infinite
strictly descending chain of natural ranks — that is, Euclid's perpetual engine — and that is killed by the root
of the whole repository, `no_infinite_descent` ([chapter 01](01_EPMI.md)). Note the honestly inverted asymmetry: the killer
here is the pure well-foundedness of the natural numbers, and we did not mix in a fake "there are no
engines" hypothesis for the sake of beauty.

**Theorem 40.5** (`massGap_of_quantizationLaw`, 🟢 — the hero of the chapter). *Quantization ⟹ mass gap:* $\mathrm{QuantizationLaw}(S) \Rightarrow \mathrm{MassGap}(S)$. No gap →
masslessness → a ladder is built → quantization turns it into a natural descent → an EPMI contradiction.

## Why there is no Yang–Mills boundary of the decree

As with P/NP, the temptation arises to add a Yang–Mills boundary to the first cause. And again — no, machine-verified. The reason runs deeper than for P/NP, and a single theorem exposes it.

**Theorem 40.6** (`quantizationLaw_iff_massGap`, 🟢). *For every model, the quantization law is equivalent
to the presence of a gap — green and without any boundary:* $\mathrm{QuantizationLaw}(S) \iff \mathrm{MassGap}(S)$.

This is the shape of the *condemned* bridge (`offCriticalBridge_iff_RH`), not of the honest Riemann mirror. In the Riemann branch the equivalence "law ⟺ goal" was reached only *under* the boundary; here it is green on its own.

Hence, to decree the quantization law for the model would be to decree its gap verbatim — to rename the goal, not to add a cause. The trilemma — the mandatory three-part test of a boundary candidate (see the [glossary](GLOSSARY.md)) — confirms this from every side:

- the universal form of the law is *refutable* — the forged (that is, machine-built as a counterexample) massless model `{0} ∪ {2⁻ⁿ}` carries an explicit ladder `cookedLadder`, and the decree would blow up the quarantine;
- the existential form is *already proven* — the forged gapped model `{0,1}`, the decree would be empty;
- the manifestation form is *incompatible with the boundary already accepted*.

The last point deserves emphasis — it holds the exact asymmetry with Riemann. An off-critical zero is greenly unpresentable (presenting it would refute RH), and that is why in the Riemann branch the manifestation law was an honest second boundary (subsequently withdrawn from the decree, Option A).

But the forged massless ladder is presented by construction — and therefore the same move here blows up the quarantine: `ymManifestationLaw_refutes_boundary` 🟢.

**Conclusion.** The same as in P/NP: there is no honest decree field; what is missing is not a proposition but a data anchor — a constructed spectrum or Hamiltonian, which mathlib does not have.

## The split by scales and §12

The branch's only 🟡 content is what the decree asserts *itself*, on its own scale. At `A ≤ 4` the supply of deviations — what a deviation "pays" with (see the [glossary](GLOSSARY.md)) — is real (`smallScale_deviationSupply` 🟢, a five-adic chain — an object of manifestation, not an empty form).

But at the decreed `A ≥ 5` there is no supply at any threshold (`decreedScale_no_deviationSupply` 🟡): **the world of the first cause is gapped in the language of supplies** — it contains no infinite tower of arbitrarily cheap excitations.

We deliberately did not add a fake 🟡 "mass gap of the rank world": the natural gap of the rank world is trivially green. The stretch — an intentional explosion detector (see the [glossary](GLOSSARY.md)) — `quarantine_inconsistent_if_supply_at_every_scale` 🟡 keeps the point of explosion visible.

## The bridge to Navier–Stokes: two rescues from one warning

The counterexample of the cascade warning — `(1/2)^n`, positive work with no finiteness — is *literally* the Yang–Mills ladder. But the two branches are rescued from it differently, and this is worth seeing side by side.

Navier–Stokes is rescued by δ-quantization of dissipation: a uniformly dissipative ladder is impossible (`no_uniformlyDissipative_ladder` 🟢). Yet the real ladder `(1/2)^n` is not uniformly dissipative — its steps decrease below every `δ` (`cookedLadder_not_uniformlyDissipative` 🟢) — and so the NS certificate does *not* kill it. Only rank quantization through EPMI kills it.

Both branches share one root — the impossibility of a perpetual engine; but the certificates differ: for NS — an energy balance with δ-dissipation, for YM — quantization of the spectrum.

## Yang–Mills beyond the same horizon

The wall against which the internal solutions of Collatz and P/NP shatter ([chapter 56](56_CollatzFirstCause.md)) has a spectral slope as well — the epistemic complement of the branch is gathered in `Engine/YangMillsEpistemic.lean`.

"To solve Yang–Mills from inside", in our language, would mean self-grounding the quantization law: carrying the per-model law itself (the field `ground`) and along with it a refutation of the gap, obtained from beyond one's own horizon (the field `beyondOwnHorizon`).

Such a bundle (`InternalisedYMGround`) self-destructs: `no_internalisedYMGround` 🟢, whence `ymCause_unknowable` 🟢 — a mirror of `collatzCause_unknowable` and `pnpCause_unknowable` — and therefore **"it cannot be known from inside" is here too a theorem, not a slogan**. From inside a spectral model the quantization law cannot be self-grounded: the attempt costs exactly a perpetual engine.

What pays for the contradiction — a construction, and in Yang–Mills it is more vivid than anywhere else: the refutation of the gap is not passive, it *presents an object*. From the absence of a gap a halving ladder is built (the exact characterization — `not_massGap_iff_nonempty_ladder` 🟢), and the ladder by itself is a genuine perpetual engine on the real numbers: `not_massGap_carries_real_engine` 🟢, the witness being the sequence of levels itself, without a single `False.elim`.

On ℝ such an engine is lawful (`perpetualEngine_on_real` 🟢) — the continuum erects no wall. The wall arises only when the quantization law translates energy into a natural rank: the composition "rank ∘ ladder" becomes an infinite ℕ-descent (`quantizedLadder_carries_perpetual_engine` 🟢) and burns up against `no_perpetual_engine_on_nat` — the second route, `quantizedLadder_impossible_via_engine` 🟢.

A caveat is mandatory: the pair "law + ladder" is jointly refuted in the repository (`no_quantizedLadder`), so logically this carrier is a repackaging of the killer; genuineness here is a property of the witness term, not of the antecedent, which for Collatz remained open.

And the third pane of the fork, `ym_no_internal_decision_without_engine` 🟢, is the signature feature of this very branch. Only the per-model law decides the question, but Theorem 40.6 (`quantizationLaw_iff_massGap`) 🟢 is green without any boundary: the law decides the question precisely because it *is* the question.

Through this equivalence (together with `not_massGap_iff_nonempty_ladder`) the self-grounding bundle semantically collapses into `MassGap S ∧ ¬ MassGap S` — for Collatz and P/NP the sides were not greenly equivalent to the goal and its negation; for Yang–Mills they are.

Hence the decree door is closed twice: the universal form is refuted by a forged witness (`ymGround_universal_refuted` 🟢, verbatim `ymLawUniversal_refuted`), and a per-model decree would rename the goal without adding a cause. **The only entrance left is external — a data anchor, a constructed spectrum of a genuine non-abelian theory, which mathlib does not have.**

**Section takeaway.** Everything is gathered in `ym_locked_behind_engine_status` 🟢: the universal is refuted, internal knowledge is impossible, the law entails the gap, the forged witnesses of both sides are alive, the ℕ-engine is forbidden — the module is entirely green, the quarantine is not imported, the repository's taint does not grow.

> **Note (what we do NOT claim).** This is NOT a solution of the Clay problem and NOT Gödel: no incompleteness, no fixed point — only well-foundedness, and all the epistemics is model-internal: about the genuine quantum Yang–Mills theory the theorems of this section say nothing; it remains open 🔴. The conditionality is named: the quantization law itself is a 🔴 per-model input, and everything "under the law" here is an implication; and the tautologization of the bundle through `quantizationLaw_iff_massGap` is not hidden — it is precisely the reason why there is only one exit and it is external.

## Philosophical digression: mass as a gap, the vacuum as a refusal of free work

This chapter is the closest of all to real physics, and the connection here is not metaphorical but literal. The Yang–Mills mass gap is not an abstract "`Δ > 0` below the levels"; it is a statement about **why matter has mass**.

The proton weighs ≈ 938 MeV, and only about one percent of that is the rest mass of the quarks (the Higgs contribution); all the rest is confinement energy, the energy of the imprisoned gluon field. The mass of a hadron *is* the gap: the minimal price of excitation above the vacuum.

No gap — no mass: the universe would be a transparent soup of massless gluons, with no protons, no nuclei, no us.

Why must nature have a gap? Because a gapless spectrum is a perpetual engine, in the most physical sense. Excitations of arbitrarily small energy above the vacuum mean that work can be drawn from the vacuum with no lower limit: infinitely many ever cheaper modes, an infinite pumping of energy out of "nothing".

Our halving ladder `2·E(n+1) ≤ E(n)` is exactly the "arbitrarily soft gluon", the tower of ever cheaper excitations that a gapless theory would permit. Quantization of the spectrum — the fact that energy comes in discrete portions ranked by a natural number — cuts the ladder off exactly the way a guitar string cannot sound arbitrarily quietly above its state of rest: it has a fundamental tone. A massless field is a string without a lowest note.

Here lies the meaning of the central result Theorem 40.5 (`massGap_of_quantizationLaw`): **quantization forbids the perpetual engine, and the prohibition of the perpetual engine is mass**. The rank quantization that kills the ℝ-ladder through EPMI is the mathematical shadow of the physical fact that energy is quantized.

Clay asks us to prove that for a genuine non-abelian gauge theory this quantization really holds (our 🔴 data anchor — a constructed QFT Hamiltonian). We have proven the structural half, the one that does not depend on the concrete theory: wherever there is a quantized rank, there is no gapless ladder — there is mass.

The universe is stable because the vacuum charges a price for the first excitation — and that price, translated into the programme's language, is the impossibility of Euclid's perpetual engine.

<!--navbot-->

---

[← 39. P/NP: paying for certificates](39_PNPRankPayment.md) · [Table of contents](00_Overview.md) · [41. Navier–Stokes: smoothness →](41_NSSmoothness.md)
<!--/navbot-->
