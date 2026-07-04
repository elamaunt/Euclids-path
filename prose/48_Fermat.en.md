# Fermat numbers: a second bet against expectations — a boundary machine-admissible and once again not taken

<!--navtop-->
[← 47. Perfect numbers](47_PerfectNumbers.md) · [Table of contents](00_Overview.md) · [49. The geometry of the path →](49_Geometry.md)
<!--/navtop-->


> Lean source: `Engine/FermatBranch.lean` — the honest Fermat ↔ twins bridge, all 🟢;
> `Engine/FermatManifestationFront.lean` — the green manifestation front, all 🟢;
> `Engine/FermatMersenneEpistemic.lean` — the epistemic complement of both branches, all 🟢;
> `Engine/CausalClosureAxiom.lean` §16–§17 — a verdict-comment (no declarations).
> Prose context: [34. The Mersenne branch](34_MersenneBranch.md),
> [43. Mersenne through the first cause](43_MersenneFirstCause.md). Status notation: 🟢 — proven under
> the standard axioms; 🟡 — conditional on the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

Chapter [43](43_MersenneFirstCause.md) did something the programme had never done before: it carried the trilemma —
the mandatory triple test of a boundary candidate (see the [glossary](GLOSSARY.md)) —
all the way through, recognised a fourth boundary of the decree as *machine-admissible* — and still did *not take it*.

The reason is that, for the first time, the sign of the heuristic came out inverted. To accept the Mersenne boundary would
have been to bet against expectations, and §16 recorded the refusal: admissible does not mean advisable.

This chapter is that one's mirror. The Fermat numbers $F_k = 2^{2^k} + 1$ pass through the same architecture, yield the same
green front, the same readable theorem "a refutation presents an engine" — and run into the same
verdict, only here the sign of the heuristic is sharper still.

For Mersenne the sum over twin pairs merely converged. For Fermat the known tail of composites is enormous,
only the first five are known to be prime, and the consensus expects that there are no new Fermat primes at all. So the second
bet against expectations comes out heavier than the first — and once again we do not place it.

For the first time in the programme, refusal by the sign of the heuristic becomes a *rule*, not a one-off decision.

## The minus side: Mersenne's mirror on the other side of the grid

Mersenne lived on the plus side: $2^p - 1 = 6m + 1$ ([34](34_MersenneBranch.md)). Fermat lives exactly opposite.

**Theorem** (`six_mul_fermatCenter`, 🟢). *For $k \ge 1$ the division at the centre $c_k = (F_k + 1)/6$ is exact:*
$\;6\,c_k = F_k + 1$, *that is,* $F_k = 6\,c_k - 1$ — *a Fermat number is the* minus *side of the centre, the lower
member of the pair.*

**Why this is true.** For $k \ge 1$ the exponent $2^k$ is even, and $2^{2^k} = 4^{2^{k-1}} \equiv 1 \pmod 3$;
hence $F_k \equiv 2 \pmod 3$, and by oddness $F_k \equiv 1 \pmod 2$ — together these give
$F_k \equiv 5 \pmod 6$ (`fermatNumber_mod_six`). Five modulo six is exactly the minus side
$6m - 1$, mirror to Mersenne's plus side.

The case $k = 0$ is excluded deliberately: $F_0 = 3$ does not lie on the grid $6m \pm 1$ at all, and the bridge begins at
$k = 1$. The twin criterion then mirrors the Mersenne one word for word: the centre $c_k$ is a twin centre $\iff$ both $F_k$
and $F_k + 2$ are prime (`isTwinCenter_fermatCenter_iff` 🟢).

And the only honest arrow between the themes, as with Mersenne, points the other way — Fermat twins
$\Rightarrow$ twins (`twinLowersInfinite_of_fermatTwins` 🟢): a subsequence of twins is still
twins, and not a word about Fermat primes follows from the twin conjecture.

## The chain that cannot be sawed — and this time quadratically

Mersenne's centres grew linearly, base-4 repunits $m \to 4m + 1$; the five-adic chain of
[24](24_BoundaryDecomp.md) had $c \to 5c + 1$. Fermat breaks even this linearity.

**Theorem** (`fermatCenter_chain`, 🟢). *The chain of centres is* quadratic: $c_{k+1} = 6\,c_k^2 - 4\,c_k + 1$,
*written without subtraction as* $c_{k+1} + 4\,c_k = 6\,c_k^2 + 1$.

**Why this is true.** The mathlib recurrence $F_{k+1} = (F_k - 1)^2 + 1$, translated through $6c = F + 1$,
gives exactly this nonlinear law — and that is the whole point.

The five-adic chain had the identity $6(5x+1) - 1 = 5(6x+1)$ with a *prime* constant divisor 5, and so
it forged flows at small $A$. Mersenne's linear $4m+1$ no longer had such a divisor. The quadratic
$6c^2 - 4c + 1$ has none and can have none: the nonlinear leading term leaves no constant prime
factor, sides do not map onto sides.

There is nothing to forge — the chain can grow (`fermatCenter_strictMono_from_one` 🟢), but it cannot saw.

**Theorem** (`isEmpty_properCenterPeel_three_one`, 🟢). *The chain step $3 \to 1$ carries no proper peel
at any scale.*

**Why this is true.** Everything is visible with bare hands already at the first step, just as with Mersenne, only the numbers
differ: the sides of centre 3 are 17 and 19, both prime; the sides of the target, centre 1, are only 5 and 7. No
factorisation from the former into the latter exists, at any $A$.

The consequence is the same as for Riemann, Mersenne, Sophie Germain: **no forged witness exists in the Fermat
branch** — no machine-built counterexample to the law, a "forging" (see the [glossary](GLOSSARY.md)) — the exact opposite of Yang–Mills (`cookedLadder`) and Navier–Stokes
(`cookedProfileCascade`), where precisely a forged ladder blew up the manifestation candidates. The door for
an honest law stands open.

## An absence witness — and the strongest concrete localisation in the programme

As with Mersenne, the deviation here is not a data point but a $\Pi$-witness: `FermatTwinAbsenceAbove P`,
the assertion that every Fermat twin sits as the lower member no higher than $P$. The plumbing ties it to the goal
exactly: Fermat twins are unbounded $\iff$ there are no absence witnesses
(`fermatTwinCentersUnbounded_iff_no_absence` 🟢). About the witness's domain we know a lower bound — and it
is a record.

**Theorem** (`fermatAbsenceBound_ge_65537`, 🟢). *Every absence bound is at least 65537.*

**Why this is true.** Here the Fermat branch delivers the strongest concrete localisation of twins in the entire
programme. The concrete Fermat twins (`fermat_twin_instances` 🟢) are $k = 1$: the pair $(5, 7)$;
$k = 2$: the pair $(17, 19)$; and — the record — $k = 4$: $F_4 = 65537$ and $F_4 + 2 = 65539$, both prime. The pair at
$k = 4$ greenly exists, and no absence witness can cut it off from below — hence every
bound is $\ge 65537$.

Note also the honest gap between them: $k = 3$ yields no pair, $F_3 + 2 = 259 = 7 \cdot 37$ is composite
(`fermat_twin_non_instance` 🟢) — Fermat twins are not automatic, and that too is a green theorem. Beyond 65537,
however, the real darkness begins: to present an absence witness would be to solve the open problem of the
Fermat-twin tail.

## The manifestation front — Mersenne's mirror, word for word

From here the front repeats the Mersenne one letter by letter, only on Fermat data. The manifestation law
`FermatManifestationLaw` is gated by the absence witness: the ungated form "$\forall P$, absence
manifests" at $P = 0$, together with an accepted boundary, would yield a supply — an infinite admissible
family of flows with which the deviation "pays" (see the [glossary](GLOSSARY.md)) — at a resolved scale —
contradicting the green impossibility (`no_deviationFlowSupply_at_resolved_scale`, taken from Riemann and
not re-proven).

The gate by a greenly-unpresentable witness is a load-bearing wall, not an ornament; it was exactly on its absence
that the Yang–Mills and Navier–Stokes candidates blew up. And now — the two main theorems, both green, both with
genuine consumption of hypotheses.

**Theorem** (`fermatRefutation_carries_engine`, 🟢 — the readable form). *An absence witness + the manifestation
law + reconciled books at a scale no lower than $P$ present a perpetual engine — as an object,*
`ConcreteEuclideanEngineWitness`, *before any killing.*

**Why this is true.** The resolving projection yields a stable no-energy universe; the law
turns the absence into an infinite family of flows; a finite key is forced to collide two of its members;
from the collision an engine-witness is assembled. To refute Fermat twins where the books are reconciled is —
literally — to build a perpetual engine.

**Theorem** (`fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation`, 🟢 — essence). *No
engines + an accepted boundary + the manifestation law $\Rightarrow$ Fermat twins are unbounded.*

The mirror of the Mersenne and Riemann essence lemmas, with the same standard of honesty: from finiteness
a witness $P$ is extracted; the boundary grants resolution exactly at scale $P$; the law supplies the family — not
ex falso, but as data; and it is precisely the hypothesis "there are no engines" that kills the assembled engine. Through the honest
direction of the branch the same triple is carried all the way to the twins
(`twinLowersInfinite_of_noEngine_boundary_and_fermatManifestation` 🟢).

## The price — and why once again we did not pay it

The trilemma has been passed: the witness is unpresentable (every bound is $\ge 65537$, and presenting one = solving an open
problem), the law is not greenly decidable in either direction, there is no forging
(`isEmpty_properCenterPeel_three_one`). By the same machine criterion that admitted the Riemann boundary and
rejected the Yang–Mills, Navier–Stokes, P/NP and Hodge candidates, the field `fermatBoundary` is **admissible**.

And here is its price:

**Theorem** (`fermatManifestationLaw_iff_unbounded_of_boundary`, 🟢 — the main price audit). *Under
an accepted boundary the manifestation law is equivalent to the unboundedness of Fermat twins.*

The decree would be of exactly Fermat-twin strength — no weaker and no stronger, as with Riemann and Mersenne. But the sign
of the heuristic here is inverted *harder* than Mersenne's.

For Mersenne the sum $\sum$ over twin pairs merely converged, not directly forbidding infinitude. For Fermat
the standard heuristic sum $\sum 2^{-2^k}$ converges almost instantly, and — what decides the matter —
the known tail of composite Fermat numbers is enormous: only $F_0$ through $F_4$ are known to be prime, while $F_5$ through
$F_{32}$ are all provably composite. The consensus expects that there are no new Fermat primes at all.

So the right-hand side of this $\iff$ is not merely "against expectations" but against expectations *with the most negative
expected truth in the entire programme*. To stake the consistency of the whole quarantine on it would be
a bet even farther from reason than the Mersenne one.

We decided as in §16: **the field is not added — deliberately.** The law lives as a definition in the green
front (as the Riemann law lived before §10), the entire rigorous chain is proven with the boundary as a hypothesis, the quarantine taint —
the machine trace of the axiom in the dependencies (see the [glossary](GLOSSARY.md)) — is unchanged, and the verdict is recorded in §16 word for word and entered in the register of §17: *admissible, but deferred by
the sign of the heuristic*.

**Section takeaway.** The machine criterion says "admissible"; honesty says "admissible does not mean advisable", and for Fermat this "advisable"
is more negative than anywhere else.

> **Note.** Let us record what this chapter does not claim and what it exposes on its own. The implication "twins
> $\Rightarrow$ Fermat" is not written, not proven, and not known to mathematics — the coverage marker
> `noTwinsToFermatImplicationClaimed` stands in the branch explicitly, so that this cannot quietly be forgotten.
>
> The front upholds vacuity prohibition no. 3: not a single free Prop field, not a single free gate, not
> a single renamed conclusion — every hypothesis is named arithmetically. The witness here is
> a named $\Pi$-statement about absence, the supply is the same strict object `DeviationFlowSupply`
> as Riemann's, and the module does not even import the quarantine.

## Philosophical digression: betting against a convergent heuristic

This chapter has a historical patron, and he is instructive in exactly the opposite direction to where the
machine leads us. Fermat himself believed that *all* the numbers $F_k$ would be prime — a beautiful conjecture that Euler
refuted with a single division: $641 \mid F_5$. Fermat bet against a convergent heuristic, bet on
the "expectedly false" — and lost.

Our boundary `fermatBoundary` is the same bet, only formalised: to accept it would be to
decree the unboundedness of Fermat twins, that is, to bet exactly where Fermat once bet
and where no reasonable count of coefficients has gone since.

And here is what is beautiful in the machine itself. The same architecture that admitted the Riemann boundary — a bet on
the *expectedly true*, on RH, in which the consensus believes — here, on the same criteria of honesty,
*refuses* Fermat — a bet on the *expectedly false*. The criterion is not blind to the coefficients: it sees
the table and, having seen it, declines.

Riemann passed not because his trilemma was easier — it was exactly the same — but because the sign
of the heuristic pointed in a direction where one is not ashamed to bet. Fermat passes the trilemma just as cleanly (the witness
is unpresentable, the law undecidable, nothing to forge) — and still the machine honestly says "no", because
honesty answers the question "*is it worth* betting", not only "*is it possible*".

Herein lies the architecture's maturity: a machine-admissible boundary can be left untaken, and this refusal says
more about it than any accepted field would. The coda will name this in a single line — that an admissible boundary is more honestly
kept open than closed by a bet one is ashamed of; Fermat is the second and purest confirmation of that.

## Fermat and Mersenne beyond the same horizon

Both bets of this series — the Mersenne one ([43](43_MersenneFirstCause.md)) and the local, Fermat one — are deferred
by the sign of the heuristic: the boundaries are machine-admissible, and both are deliberately not taken. One question still hung in
the air: is there no path *from inside* — to ground the manifestation law without asking for a decree at all? The module
`Engine/FermatMersenneEpistemic.lean` (all 🟢) closes this question for both fronts at once — by the same
horizon beyond which, in [56](56_CollatzFirstCause.md), Collatz and P/NP remained.

The mechanics are familiar. To refute under the law with the books reconciled is to present an engine as an object:
these are the already-proven `fermatRefutation_carries_engine` and `mersenneRefutation_carries_engine`.

To self-ground the law on top of one's own refutation witness, meanwhile, is to assemble that same engine
inside oneself and perish against the `lexRank` wall: the package `InternalisedFermatGround` builds the witness
(`internalisedFermatGround_builds_engine` 🟢) and self-destructs (`no_internalisedFermatGround` 🟢);
the Mersenne mirror `InternalisedMersenneGround` builds and perishes word for word the same
(`internalisedMersenneGround_builds_engine`, `no_internalisedMersenneGround` — both 🟢).

**"Cannot be known from inside" is now a theorem of both branches**: `fermatCause_unknowable` and `mersenneCause_unknowable`, mirrors
of the Collatz and P/NP versions.

The summaries gather this into a single statement. `fermatMersenne_no_internal_decision_without_engine` 🟢 — three
panels: refutation presents an engine; self-grounding self-destructs; the only
engine-free path is the external boundary `TheStrictLastStep00Obligation`, and precisely that has deliberately not been granted
to these branches (§16/§17).

The final status `fermatMersenne_locked_behind_engine_status` 🟢 holds it all
together: the domain localisations (absence bound $\ge 65537$ for Fermat, $\ge 29$ for Mersenne), both unknowability
theorems, the price audit — conditional on that very untaken boundary — and the wall
`no_someConcreteEuclideanEngine`.

**Conclusion.** Both doors — the decree door and the internal one — are closed greenly, and the epistemics
explains why, with the boundaries untaken, there are no internal paths either: both doors lead into the same wall.

> **Note (what we do not claim).** This is NOT a resolution of the Fermat- and Mersenne-twin questions and NOT
> Gödel: no incompleteness theorem — only model-internal epistemics, a pigeonhole self-destruction against
> well-foundedness. The panels in which the boundary participates are conditional on `TheStrictLastStep00Obligation`,
> which the branches have deliberately not been granted.
>
> And a caveat of strength: the bundle is weaker than the P/NP benchmark, where `beyondOwnHorizon`
> is greenly instantiable at small scales (`concreteSupply_unbounded_smallScale`) — here not one field
> of the package is greenly realisable: an absence witness would cost the solution of an open problem, reconciled
> books — the content of an untaken decree. But it is stronger than the Collatz tautological ground/¬ground pair:
> `beyondOwnHorizon` is not a negation of the law, and the contradiction is paid for by a genuine engine construction.
>
> The substantive dichotomies `unknowable_or_fermat_books_never_resolve` and
> `unknowable_or_mersenne_books_never_resolve` keep both hands honest — the left one is proven. The module does not
> import the quarantine; the repository's taint does not change.

## Place in the greater arc

Now *two* branches with an inverted sign — Mersenne and Fermat — stand as fronts without fields: the trilemmas are
passed (the witness unpresentable, the law undecidable, no forging), the boundaries are machine-admissible, and both are
deliberately not taken.

What for Mersenne was a one-off decision by the sign of the heuristic becomes, with Fermat, a *rule of the series*, and
§17 fixes it for the whole arithmetic zoo: an honest boundary demands a greenly-unpresentable
witness — *and* a bet one is not ashamed of. With Fermat the second condition is violated more sharply than anywhere else: it
has the most negative expected truth in the programme, and so it is not an exception to the rule but its
clearest case.

`twin_prime_conjecture` remains `sorry`; the quarantine taint is as before; not a single open problem has been
declared solved. The Fermat primes will wait for their divisor 641 or their eternity — but the decision about them,
as about the Mersenne perfect numbers, has been made with open eyes.

<!--navbot-->

---

[← 47. Perfect numbers](47_PerfectNumbers.md) · [Table of contents](00_Overview.md) · [49. The geometry of the path →](49_Geometry.md)
<!--/navbot-->
