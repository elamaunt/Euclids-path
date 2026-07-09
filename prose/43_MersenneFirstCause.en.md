# Mersenne through manifestation: a refutation presents an engine — and the boundary we did not take

<!--navtop-->
[← 42. Hodge](42_Hodge.md) · [Table of contents](00_Overview.md) · [44. Sides and Polignac →](44_SidesAndPolignac.md)
<!--/navtop-->



> Lean source: `Engine/MersenneManifestationFront.lean` — the green chain, all 🟢;
> `Engine/CausalClosureAxiom.lean` §16 — a verdict-comment (no declarations).
> Prose context: [34. The Mersenne branch](34_MersenneBranch.md),
> [38. Riemann through the first cause](38_RiemannFirstCause.md). Status notation: 🟢 — proven under the standard
> axioms; 🟡 — conditional on the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

Chapter [34](34_MersenneBranch.md) left the Mersenne branch deliberately modest: the honest bridge "Mersenne twins ⟹ twins",
the prohibition of the reverse temptation, and the exposed vacuity No. 3. But after Riemann had passed through
the manifestation architecture ([38](38_RiemannFirstCause.md)), and Collatz through the tail engine, Mersenne was left
with the same unresolved question they had faced: **what would a refutation cost?** If Mersenne twins
are finite in number — what exactly does that finiteness present to the world?

This chapter's answer: under the manifestation law and with the books reconciled — **a perpetual engine, as an object**.

Let us recall the language: a manifestation law is the principle "a deviation must show itself by a supply-trace", and
"the books are reconciled" means the ledger resolves collisions at the given scale (see the [glossary](GLOSSARY.md)).

And its second, no less important piece of news concerns honesty: the fourth boundary of the decree is here *admissible* by
every machine criterion, and we *deliberately did not take it*. For the first time in the whole programme.

## The absence witness: a deviation without an object

For Riemann the deviation was an object-as-data — a concrete zero off the line. For Mersenne a refutation
is built differently: it is *finiteness*, the claim that above some threshold there are no more twins among
the Mersenne numbers. The witness here is not a point but a bound:

**Definition 43.1** (`MersenneTwinAbsenceAbove P`). *Absence of Mersenne twins above `P`: every
pair `(2^p − 3, 2^p − 1)` of primes sits with its lower side no higher than `P`. Formally:*
$$\mathrm{MersenneTwinAbsenceAbove}(P)\ :\equiv\ \forall p\in\mathbb{N},\ (2^p-3)\text{ prime}\ \wedge\ (2^p-1)\text{ prime}\ \Rightarrow\ 2^p-3\le P. \tag{43.1}$$

This is a Π-statement — the mirror of the twin boundary `TwinBoundAbove`, and the plumbing ties it to the branch's
goal exactly: unboundedness of Mersenne twins is equivalent to the absence of such witnesses.

**Theorem 43.2** (`mersenneTwinCentersUnbounded_iff_no_absence`, 🟢). *The centres of the Mersenne
numbers are unbounded if and only if no absence witness exists at any `P`:*
$$\mathrm{MersenneTwinCentersUnbounded}\ \iff\ \forall P\in\mathbb{N},\ \neg\,\mathrm{MersenneTwinAbsenceAbove}(P). \tag{43.2}$$

About the witness's domain we also know a lower bound:

**Theorem 43.3** (`mersenneAbsenceBound_ge_29`, 🟢). *Every absence bound is at least 29:*
$$\mathrm{MersenneTwinAbsenceAbove}(P)\ \Rightarrow\ 29\le P. \tag{43.3}$$

**Why this is true.** The pair `(29, 31)` at `p = 5` greenly exists — both numbers are prime, and no
witness can cut it off from below. Past 29, however, the true darkness begins: presenting an absence
witness would mean settling the open problem of the Mersenne-twin tail.

## Why there is no forging here: a chain that will not saw

Before decreeing a law, the programme is obliged to check the trilemma — the mandatory triple
test of a boundary candidate (see the [glossary](GLOSSARY.md)) — and its decisive clause we
remember from Yang–Mills and Navier–Stokes: manifestation candidates exploded wherever the witness
could be *forged* — a counterexample to the universal form of the law built machine-wise (the ladder
`{2⁻ⁿ}`, the profile cascade). Does Mersenne have a forged witness?

The centres of Mersenne numbers form an explicit chain — the base-4 repunits `0, 1, 5, 21, 85, …` with the recurrence
`m → 4m + 1`; it is strictly monotone and injective. Outwardly it is
a twin of the pentadic chain `c → 5c + 1`, which in [24](24_BoundaryDecomp.md) forged an infinite family of genealogies and
refuted the node's minor branch.

**Theorem 43.4** (`mersenneCenterChain_strictMono`, 🟢). *The centre function `mersenneCenter`
is strictly monotone (hence injective):*
$$\forall k\in\mathbb{N},\ \mathrm{mersenneCenter}(k)<\mathrm{mersenneCenter}(k+1). \tag{43.4}$$

But the resemblance is deceptive, and the difference is arithmetic:

**Theorem 43.5** (`isEmpty_properCenterPeel_five_one`, 🟢 — even without Classical.choice). *The first step
of the base-4 chain, `5 → 1`, carries no proper peel at any scale:*
$$\forall A\in\mathbb{N},\ \mathrm{ProperCenterPeel}(A,5,1)\ \text{is empty}. \tag{43.5}$$

**Why this is true.** The pentadic chain has the identity `6(5x+1) − 1 = 5(6x+1)` with a *prime*
constant divisor 5 — every step saws honestly. The chain `4m+1` has no such identity and cannot have
one: the leading coefficients force the divisor 4, which is neither prime nor congruent to ±1 modulo 6 —
sides do not map onto sides. And already at the first step everything is visible with bare hands: the sides of centre 5 are
29 and 31, both prime, while the sides of centre 1 are merely 5 and 7; no factorisation exists.

The corollary is fundamental: **the Mersenne chain builds no unconditional supply of flows — a forged witness
does not exist in this branch.** Exactly the Riemann situation (a zero cannot be presented without refuting RH), and
the precise opposite of Yang–Mills and Navier–Stokes. The door for an honest law stands open.

## The manifestation law — gated by a witness

**Definition 43.6** (`MersenneManifestationLaw`). *For every threshold `P` with an absence witness:
at every ledger scale no lower than `P`, wherever the projection reconciles the books, the absence manifests
as an unpayable infinite supply of flows (`DeviationFlowSupply` — the same object as Riemann's):*
$$\mathrm{MersenneManifestationLaw}\ :\equiv\ \forall P,\ \mathrm{MersenneTwinAbsenceAbove}(P)\Rightarrow\ \forall A, M_0,\ P\le M_0\Rightarrow\ \forall\,\mathrm{proj},\ \mathrm{Resolves}(\mathrm{proj})\Rightarrow\ \mathrm{DeviationFlowSupply}(A,M_0). \tag{43.6}$$

The witness gate is not an ornament but a load-bearing wall. The ungated form "∀ P, absence manifests"
at `P = 0`, together with the accepted boundary, would yield a supply at a resolved scale — and that contradicts
the green impossibility (the same `no_deviationFlowSupply_at_resolved_scale` that killed the Riemann
supply). This is exactly how the manifestation candidates of Yang–Mills and Navier–Stokes failed. The gate by
a greenly-unpresentable witness is what separates the honest form from the explosive one.

## The refutation presents an engine

Now the main theorems — both green, both with genuine consumption of hypotheses.

**Theorem 43.7** (`mersenneRefutation_carries_engine`, 🟢 — readable form). *An absence witness +
the manifestation law + reconciled books at a scale no lower than `P` present a perpetual engine — as
an object,* `ConcreteEuclideanEngineWitness`, *prior to any killing:*
$$\mathrm{MersenneManifestationLaw}\ \wedge\ \mathrm{MersenneTwinAbsenceAbove}(P)\ \wedge\ P\le M_0\ \wedge\ \mathrm{Resolves}(\mathrm{proj})\ \Rightarrow\ \mathrm{ConcreteEuclideanEngineWitness}(A,M_0). \tag{43.7}$$

**Why this is true.** The resolving projection yields a stable, energy-free universe; the law
turns the absence into an infinite family of flows; the finite key is forced to collide two of its members
(pigeonhole); from the collision an engine-witness is assembled. To refute Mersenne twins where
the books are reconciled is, literally, to build a perpetual engine.

**Theorem 43.8** (`mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation`, 🟢 — essence).
*No engines + the accepted boundary + the manifestation law ⟹ Mersenne twins are unbounded:*
$$\neg\,\mathrm{SomeConcreteEuclideanEngine}\ \wedge\ \mathrm{TheStrictLastStep00Obligation}\ \wedge\ \mathrm{MersenneManifestationLaw}\ \Rightarrow\ \mathrm{MersenneTwinCentersUnbounded}. \tag{43.8}$$

A mirror of the twin and Riemann essence lemmas, held to the same standard of honesty: from finiteness
a witness `P` is extracted; the boundary grants resolution exactly at scale `P`; the law delivers the family —
not ex falso, but as data; and the engine so built is killed precisely by the hypothesis "there are no engines". Through
the honest bridge of [34](34_MersenneBranch.md) the same triple is carried all the way to the twins:

**Theorem 43.9** (`twinLowersInfinite_of_noEngine_boundary_and_mersenneManifestation`, 🟢). *The same
triple of hypotheses forces the lower sides of the twins to be infinite:*
$$\neg\,\mathrm{SomeConcreteEuclideanEngine}\ \wedge\ \mathrm{TheStrictLastStep00Obligation}\ \wedge\ \mathrm{MersenneManifestationLaw}\ \Rightarrow\ \mathrm{TwinLowers.Infinite}. \tag{43.9}$$

## The price — and why we did not pay it

The trilemma is passed: the witness is unpresentable, the law is not greenly decidable in either direction, there is no forging.
By the machine criterion — the very one that admitted the Riemann boundary and rejected the candidates of Yang–Mills,
Navier–Stokes, P/NP and Hodge — the fourth field `mersenneBoundary` is **admissible**. And here is its price:

**Theorem 43.10** (`mersenneManifestationLaw_iff_unbounded_of_boundary`, 🟢 — the chief audit M7). *Under
the accepted boundary, the manifestation law is equivalent to the unboundedness of Mersenne twins:*
$$\mathrm{TheStrictLastStep00Obligation}\ \Rightarrow\ \bigl(\mathrm{MersenneManifestationLaw}\ \iff\ \mathrm{MersenneTwinCentersUnbounded}\bigr). \tag{43.10}$$

The decree would be of exactly Mersenne-twin strength — no weaker and no stronger, just as with Riemann. But here,
for the first time in the programme, something appears that no previous trilemma had: **the sign of the heuristic
is inverted.** To accept the Riemann boundary was to bet on RH — a statement the consensus believes in.

To accept the Mersenne one would be to bet on the unboundedness of Mersenne twins — while the
heuristic looks the other way: the expected number of pairs `(2^p−3, 2^p−1)` of primes is given by a convergent
sum, only `p = 3` and `p = 5` are known, and moreover for every `p ≡ 3 (mod 4)` the number `2^p − 3`
is divisible by 5 — half the exponents drop out at once.

**Conclusion.** The bet would be not on the expectedly-true, but against
the expectations; and the consistency of the entire quarantine would rest upon it.

We decided otherwise: **the field is not added — deliberately.** The law lives as a definition in the green front (as
the Riemann law lived before §10), the whole rigorous chain is proven with the boundary as a hypothesis, the quarantine's taint
is unchanged, and the verdict is fixed in the comment of §16: *admissible, but deferred by the sign of the heuristic*.
The machine criterion says "you may"; honesty says "may does not mean should".

> **Note.** Let us also note what this chapter does not fix: vacuity No. 3 from [34](34_MersenneBranch.md) remains exposed —
> the forward series is as uninhabited as it ever was, and the new front shares not a single
> definition with it. The witness here is a named arithmetic statement of absence, the supply is
> the same rigorous object as Riemann's, and there is not one free Prop-field in the module.

## Philosophical digression: a bet in plain sight

Chapter [34](34_MersenneBranch.md) ended with the Euclid–Euler theorem: Mersenne primes and even perfect numbers are one
object, and the question of their infinitude has stood open since the *Elements*. This chapter adds to that
thread its last turn — on the nature of bets in mathematics.

An axiom is always a bet. In accepting the Riemann boundary we bet on RH — the way a physicist builds into
a theory a symmetry the whole community believes in. The Mersenne boundary passed all the same honesty
checks — the witness cannot be presented, the law cannot be decided, there is no forging — and still we did not take it,
because the honesty criteria answer the question "*may* one bet", not "*should* one".

Betting
against one's own heuristic is a player's right; but a programme whose storefront is honesty must at the very
least show the player the odds table. We have shown it: M7 says what the bet is worth,
the heuristic says which way the wind blows, and §16 records the decision not to play.

Herein, perhaps, lies the most mature lesson of the entire causal line. The strength of the axiomatic method is not that
an axiom can close anything whatsoever — but that *one can see exactly what is being closed and at what price*. For the first
time in the programme a machine-admissible boundary was left untaken — and this refusal says more about the honesty
of the architecture than any of the accepted fields. The perfect numbers can wait: they waited for Euclid two
thousand years — they will wait for a decision made with open eyes.

## Place in the greater arc

Now every major branch has an answer to the question "what would a refutation cost": the twins and Riemann —
boundaries of the decree (🟡); Collatz — a decree taken and *withdrawn* (the rope law machine-refuted, chapter 56),
the tail engine from the orbit minimum stays 🟢; Mersenne —
a manifestation engine under the law and the books (🟢, conditionally), with an admissible but deferred boundary.

The rule of the series has sharpened: an honest boundary requires a greenly-unpresentable witness — *and* a bet
one need not be ashamed of. `twin_prime_conjecture` remains `sorry`; the quarantine's taint — the same 16
declarations; not a single open problem has been declared solved.

<!--navbot-->

---

[← 42. Hodge](42_Hodge.md) · [Table of contents](00_Overview.md) · [44. Sides and Polignac →](44_SidesAndPolignac.md)
<!--/navbot-->
