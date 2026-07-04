# Grid sides and Polignac patterns: singletons green, pairs — conjectures

<!--navtop-->
[← 43. Mersenne via first cause](43_MersenneFirstCause.md) · [Table of contents](00_Overview.md) · [45. Sophie Germain →](45_SophieGermain.md)
<!--/navtop-->


> Lean source: `Engine/SideInfinitude.lean` — the spine of honesty, all 🟢 (Dirichlet from mathlib);
> `Engine/PolignacBranch.lean` — classification of cousins and sexies in the grid, all 🟢;
> `Engine/PolignacManifestationFront.lean` — two manifestation branches, all 🟢 (no declarations).
> Prose context: [43. Mersenne via first cause](43_MersenneFirstCause.md),
> [38. Riemann via first cause](38_RiemannFirstCause.md). Status notation: 🟢 — proven under
> standard axioms; 🟡 — conditional on the axiom `step00FirstCause`; 🔴 — open input.

## Where we are

Chapter [43](43_MersenneFirstCause.md) was the first to leave a machine-admissible decree boundary
untaken — on the sign of a heuristic. Mersenne twins governed one rare subsequence of exponents;
here we turn to the broadest class of open pair problems — small even gaps between primes, the
Polignac conjecture. And we begin not with the conjecture, but with what is **honestly separated**
from it.

Pair problems carry a treacherous ease: it seems as though "there are infinitely many primes of the
form `6m ± 1`" almost settles everything. It does not, and drawing the line between the settled and
the open is the chapter's first duty. Singletons are green; reconciling singletons into a pair is
the entire open substance.

Around that spine we build two new manifestation branches (manifestation is the principle "a
deviation must show itself", see the [glossary](GLOSSARY.md)) — cousins (gap 4) and sexies (gap 6)
— exact mirrors of the Mersenne one, with one new turn of honesty that neither Riemann nor Mersenne
had.

## The spine of honesty: each side is separately infinite

The `6m ± 1` grid gives every centre `m` two sides — the minus-side `6m − 1` (class `5 mod 6`) and
the plus-side `6m + 1` (class `1 mod 6`). The question "are there infinitely many primes on each
side separately" has long been closed, and closed by heavy analysis:

**Theorem** (`minusSide_primes_unbounded`, `plusSide_primes_unbounded`, 🟢). *Above any `n` there
is a prime `p > n` with `p % 6 = 5`; and there is a prime `p > n` with `p % 6 = 1`.*

**Why this is true.** This is Dirichlet's theorem on primes in arithmetic progressions, borrowed
from mathlib whole — `Nat.forall_exists_prime_gt_and_modEq`, backed by the full machinery of
L-series and the non-vanishing of `L(1, χ)`. The classes `1` and `5` modulo `6` are coprime to
`6`, so each carries infinitely many primes.

In set form these are `minusSide_primes_infinite` and `plusSide_primes_infinite` (🟢): both sets
`{p : p.Prime ∧ p % 6 = 5}` and `{p % 6 = 1}` are `Set.Infinite`. We prove no new number theory
here — we borrow a finished result and translate it into the programme's central language
(`minusSide_center_unbounded`, `plusSide_center_unbounded`): above any `n` there is a centre with a
prime minus-side, and, separately, a centre with a prime plus-side.

And here is the load-bearing wall for whose sake the module exists. About one and the same centre
these theorems say nothing.

> **Note.** The marker `NoPairingClaimed` (🟢, `abbrev … := True`) is a signature of honesty, not a
> theorem with content. Dirichlet gives two independent infinite columns of primes — along the
> minus-side and along the plus-side — but is silent on whether they line up *opposite each other*
> infinitely often, at a shared centre `m`.

> Simultaneous primality of `6m − 1` and `6m + 1` is the twin prime conjecture, and here it is
> neither asserted, nor proven, nor derived from anything. The entire open weight of pair problems
> lies precisely in this gap between "each side is infinite" and "the sides coincide infinitely
> often".

> **Note (anchor of bounded gaps).** The same gap is also visible from the other side — the side of
> bounded prime gaps. The module `Engine/BoundedGapsAnchor.lean` names the predicate `BoundedGaps B`
> ("infinitely many prime pairs with gap ≤ B") and two honestly unformalised inputs:
> `ZhangAnchor` (Zhang 2013, `B = 7·10⁷`) and `MaynardTaoAnchor` (Maynard–Tao 2014, `B = 246`) —
> humanity's best unconditional result, absent from mathlib.

> The renaming audit `boundedGaps_two_iff_twins` exposes machine-wise that the edge case `B = 2` is
> literally equivalent to the twin prime conjecture: naming `BoundedGaps 2` is naming twins, and the
> renaming is exposed by an iff-theorem, not hidden. The descent `246 → 2` is open mathematics,
> honestly *not* claimed: the monotonicity `boundedGaps_mono` works only upward in the threshold;
> below 6 the sieves run into Selberg's parity problem.

## Cousins: a cross-pair of adjacent centres

The grid encodes small gaps geometrically, and the encoding is transparent. Gap 2 (twins) is one
centre `m`, the pair `(6m − 1, 6m + 1)`.

Gap 4 (cousins, `p` and `p + 4`) is adjacent centres and different sides: the pair `(6m + 1, 6m + 5)`,
where the larger member is recognised by the identity `6m + 5 = 6(m + 1) − 1`
(`cousin_upper_eq_minusSide`, 🟢). In other words, the junior cousin is the plus-side of centre
`m`, the senior cousin is the minus-side of the next centre `m + 1`. The pair bridges the boundary
between two centres.

This geometry imposes a rigid classification:

**Theorem** (`cousin_mod_six`, 🟢). *Every junior member of a cousin pair with `p > 3` lies on the
plus-side of the grid: `p % 6 = 1`.*

**Why this is true.** A prime `p > 3` is divisible by neither `2` nor `3`, so `p % 6` is either
`1` or `5`. The case `p % 6 = 5` is excluded by the arithmetic of the pair itself: then
`p + 4 ≡ 0 (mod 3)`, meaning `p + 4` would be divisible by `3` — yet it is prime and greater than
three, a contradiction. What remains is `p % 6 = 1`. Cousins are born exclusively on the plus-side
— and specific centres confirm it (`cousin_instances`, 🟢): `m = 1` gives `(7, 11)`, `m = 2` gives
`(13, 17)`, `m = 3` gives `(19, 23)`.

## Sexies: a one-sided pair of adjacent centres

Gap 6 (sexies, `p` and `p + 6`) is structured differently. A shift of `6` does not change the
residue modulo `6` (`sexy_preserves_side`, 🟢), so a sexy pair always sits on one side: either a
minus-pair `(6m − 1, 6m + 5)` on the minus-sides of centres `m` and `m + 1`, or a plus-pair
`(6m + 1, 6m + 7)` on their plus-sides. A sexy centre carries a pair on at least one side
(`sexy_instances`, 🟢: minus-pairs `(5, 11)`, `(11, 17)`; plus-pair `(7, 13)`).

And when two geometries meet at one point, a constellation occurs:

**Theorem** (`constellation_of_adjacent_twinCenters`, 🟢 — even without `Classical.choice`). *Two
adjacent twin-centres `m` and `m + 1` simultaneously yield all three patterns: cousins on `m` and
both sexy pairs on `m`.*

**Why this is true.** If both `m` and `m + 1` are twin centres, then all four sides are prime:
`6m − 1`, `6m + 1`, `6(m + 1) − 1 = 6m + 5`, `6(m + 1) + 1 = 6m + 7`. From these one assembles
at once the cousins `(6m + 1, 6m + 5)`, the minus-sexy `(6m − 1, 6m + 5)`, and the plus-sexy
`(6m + 1, 6m + 7)` — by pure rearrangement, without any choice. At `m = 1` this is the famous
constellation `5, 7, 11, 13`: cousins `(7, 11)`, sexies `(5, 11)` and `(7, 13)` all at once.

What matters here is what the proof does *not* do: it does not construct adjacent twin-centres, it
only unpacks them when they are given. That adjacent twin-centres exist arbitrarily high is a
conjecture — and a stronger one than the twin prime conjecture.

## The manifestation front — twice

We now run both branches through the same architecture as Mersenne in [43](43_MersenneFirstCause.md):
a refutation must exhibit a perpetual engine. The deviation here is not a data object (like an
off-critical zero for Riemann), but a Π-witness of absence — the mirror of the Mersenne one:
`CousinAbsenceAbove P` (all cousin-centres sit no higher than `P`) and `SexyAbsenceAbove P` (all
sexy-centres sit no higher than `P`).

The plumbing connects them to the goal exactly — unboundedness of centres is equivalent to the
absence of absence-witnesses (`cousinCentersUnbounded_iff_no_absence`,
`sexyCentersUnbounded_iff_no_absence`, 🟢) — and the witness domain is localised from below:

**Theorem** (`cousinAbsenceBound_ge_37`, `sexyAbsenceBound_ge_17`, 🟢). *Every absence-bound for
cousins is at least 37; every absence-bound for sexies is at least 17.*

**Why this is true.** The cousin-centre `m = 37` exists greenly — the pair `(223, 227)` of primes;
no witness can cut it off from below, so its bound is no lower than 37. For sexies the same holds
with centre `m = 17`: on the minus-side this is the pair `(101, 107)`. Beyond that lies darkness:
to exhibit an absence-witness would be to settle the open case of the Polignac conjecture for gap 4
or 6.

The manifestation law is gated by this witness (`CousinManifestationLaw`, `SexyManifestationLaw`;
a gate, recall, is an honestly named missing input), and the gate is a load-bearing wall, as with
Mersenne: the un-gated form at `P = 0`, together with an accepted boundary, would yield a flow
supply — an infinite admissible family with which the deviation "pays" — at a resolved scale, and
that contradicts the green impossibility (`no_deviationFlowSupply_at_resolved_scale`) — the very
mechanism by which the Yang–Mills and Navier–Stokes manifestation candidates exploded.

The manifestation object `DeviationFlowSupply` is borrowed from the Riemann front wholesale,
together with its substantiveness witness; it is not re-proved here. The main theorems — both green,
for each family:

**Theorem** (`cousinCentersUnbounded_of_noEngine_and_boundary_and_manifestation`, and its sexy
twin, 🟢 — essence). *No engines + accepted boundary + manifestation law ⟹ cousin-centres (resp.
sexy-centres) are unbounded.*

**Why this is true.** A mirror of the Mersenne and Riemann essence-lemmas, to the same standard of
honesty. From finiteness a witness `P` is extracted; the boundary gives resolution at precisely the
scale `M0 := P`; the law supplies an infinite family of flows — not ex falso, but as data; from
collisions among its members an engine-witness is assembled (the readable forms
`cousinRefutation_carries_engine` / `sexyRefutation_carries_engine`, 🟢); and it is precisely the
hypothesis "no engines" that kills the constructed engine.

Through honest bridges in the branches (`cousinLowersInfinite_of_unbounded`,
`sexyLowersInfinite_of_unbounded`) the same triple is carried all the way to the goal — the
infinitude of the pairs themselves.

**Conclusion.** To refute cousins or sexies where the books are reconciled (that is, where the
projection resolves collisions at the given scale, see the [glossary](GLOSSARY.md)) is literally to
build a perpetual engine.

## Why there is neither forging nor a decree here

The trilemma — the mandatory triple test of a boundary candidate (see the [glossary](GLOSSARY.md))
— is passed for the fourth field by both families: the witness is not exhibitable (V1), the law is
not greenly decidable in either direction (V2), the law does not explode the boundary (V3). By the
machine criterion — the very one that admitted the Riemann boundary — the fields `cousinBoundary`
and `sexyBoundary` are admissible. And yet they are absent. Two reasons, and the first is new to
the programme.

For Mersenne, V3 rested on a subtle argument: the chain of centres `4m + 1` exists, but cannot be
sawed — the largest factor of 4 is neither prime nor congruent to ±1 modulo 6. For cousins and
sexies the argument is simpler and deeper: **there is no chain at all, and so nothing to saw.**

Cousins and sexies are a full-density pattern of adjacent centres `(m, m + 1)`, not a distinguished
subsequence like the Mersenne `4m + 1`, Sophie Germain `2m`, or Fermat `6m² − 4m + 1`. The chain
section is absent from this module for substantive reasons, not from oversight: a forged witness
(the pattern by which Yang–Mills and Navier–Stokes exploded) does not exist in these branches,
because the forging substrate itself is absent. The door for an honest law stands wide open — and
here the second reason arises.

**Theorem** (`cousinManifestationLaw_iff_unbounded_of_boundary`, and its sexy twin, 🟢 — the
principal M7 price audit). *Given an accepted boundary, the manifestation law is equivalent to the
unboundedness of centres.*

A decree would carry exactly the force of the corresponding Polignac case — as with Riemann and
Mersenne. And the heuristic sign here is positive: Hardy–Littlewood expects every class of pairs to
be infinite, as consensus awaits RH. The stake, in other words, would be on the expected-true —
for the first time with a positive sign, unlike Mersenne. It would seem one should take it. But we
did not — and here is why.

First, there is nothing to forge, and therefore nothing to prepare: the Mersenne decree peeled off
a rare chain, whereas for cousins we face the full density of adjacent centres — no substrate for
the kitchen.

Second, and decisively: **serial extension of the decree would devalue the quarantine.** The entire
content of the quarantine is the uniqueness of the single accepted boundary; adding a field for
every trilemma cleared would turn the exception into a rule and erase the very meaning for which the
quarantine was established.

> **Note.** The sexy witness deserves a separate caveat. The gate `IsSexyCenter` is two-sided (a
> minus-pair or a plus-pair via `Or`), so `SexyAbsenceAbove P` is a witness stronger than either
> side individually: it bounds both minus- and plus-pairs simultaneously.
>
> This does not compromise any of the theorems — but it is precisely why the lower bound of 17 is
> supplied by the minus-side, whereas the plus-side would yield a different threshold; the witness
> must survive both.

**Section summary.** The fields were not added — by design. The laws live as definitions in the
green front, the full rigorous chain is proved with a hypothesis-boundary, the quarantine taint is
not shifted by a single declaration, and the verdict is recorded in a §17-comment of the quarantine:
*admissible, but deferred — this time not by the sign of the heuristic, but by the cost to the
quarantine itself*. There is no free Prop-field in the module; every hypothesis is named
arithmetically.

## Philosophical digression: why pairs resist while singletons do not

De Polignac's conjecture asserts that every even gap appears between primes infinitely often. Read
through the grid, it breaks into a clear geometric question: gaps 2, 4, and 6 are exactly the three
ways two primes can sit on adjacent centres — one centre (twins), adjacent centres on different
sides (cousins), adjacent centres on the same side (sexies). Polignac for larger gaps continues the
same count further along the grid.

This is where what makes pair problems stubborn, and singleton problems solved, becomes visible.
The arrow of difficulty does not point at the primes themselves. About the distribution of
singletons we know a great deal: Dirichlet distributes primes evenly across all admissible classes,
each side of the grid is infinite, and this is proven by the analytics of L-series without any
conjecture.

What is hard is not the density of primes — what is hard is their **correlation**: their joint
appearance on adjacent centres. A singleton is one event; a pair is the coincidence of two events,
and all the weight lies in showing that the coincidences do not run dry. Dirichlet governs each
column separately and is silent on how two columns line up opposite each other.

This is the lesson of the spine of honesty. The temptation of pair problems is to accept "each side
is infinite" as "the sides coincide infinitely often"; the entire programme holds by virtue of that
step *not* being taken covertly. We proved the singletons greenly and signed, with the marker
`NoPairingClaimed`, that the reconciliation of sides remains open.

Progress here is measured not by how much of the paired world we declared proven, but by how cleanly
we separated the proven from the conjectural — and how honestly we named the price at which the
conjecture could, but should not, be bought.

## Polignac behind the same horizon

The wall against which internal solutions shatter ([chapter 56](56_CollatzFirstCause.md)) has a
Polignac slope as well — the module `Engine/PolignacEpistemic.lean`, entirely green. "Settling case
4 or 6 from inside" in our language would mean self-grounding the manifestation law: the bundle
`InternalisedCousinGround` (and its sexy mirror `InternalisedSexyGround`) holds three fields at
once — the law itself, an absence-witness for centres no higher than the ledger-scale, and
reconciled books at that scale.

No field is the negation of another — that is the P/NP style, not the tautological pair of Collatz
(what it shares with P/NP is precisely the style, not the arity: the P/NP template is two-field,
our bundle is three-field); and, unlike P/NP, none of the three is greenly inhabited. Together,
however, the triple is greenly incompatible: `no_internalisedCousinGround` and
`no_internalisedSexyGround`, from which `cousinCause_unknowable` and `sexyCause_unknowable` (🟢) —
**"cannot be known from inside" is here a theorem, not a slogan**.

What pays for this — a genuine construction, not ex falso. The theorems
`internalisedCousinGround_builds_engine` and `internalisedSexyGround_builds_engine` are a direct
composition of the readable forms of the front (`cousinRefutation_carries_engine`,
`sexyRefutation_carries_engine`): the law supplies a family of flows, the stable universe assembles
an engine-witness from their collisions — and what is built perishes against the green wall
`no_someConcreteEuclideanEngine`, where lexRank strictly drops.

The price of honesty is named: the construction is **conditional on the gated, non-decreed law and
on reconciled books** — both fields are individually unknown. This is weaker than the unconditional
Collatz route and the green pigeonhole of P/NP, and we do not conceal this.

The summary — `polignac_no_internal_decision_without_engine` (🟢), both families in one theorem:
to self-ground is to build an engine; what is built self-destructs; what remains is an external
decree, and its price has already been reckoned — under the hypothesis-boundary
`TheStrictLastStep00Obligation` the law is equivalent to the unboundedness of centres.

But here lies the difference from the neighbours on the horizon: for Riemann the external door was
taken, for Collatz the decree fell, while for Polignac **there is no field and there will not be
one** — `cousinBoundary` and `sexyBoundary` are not decreed under the §17 verdict, because a serial
decree would erase the uniqueness in which the entire meaning of the quarantine resides, as we
worked out above.

The outcome is collected in `polignac_locked_behind_engine_status` (🟢) — without a
decree-conjunct, not because the decree fell, but because it was never taken at all: from inside
— an engine, from outside — a non-decreed law of exactly conjecture strength.

> **Note (what we do not claim).** This is not a solution to cases 4 and 6 of the Polignac
> conjecture — both remain open 🔴, and the theorems of this section do not move their status. This
> is not Gödel either: no independence, no fixed point — self-destruction against the lexRank
> wall, and all the epistemics are model-internal. The conditionalities are named: the engine
> construction is conditional on the law and on reconciled books; the boundary figures only as a
> hypothesis in conjuncts; the quarantine is not imported by the module, the repository taint does
> not change.

## Place in the greater arc

Polignac has joined Mersenne and Riemann in one rank: in all three a refutation exhibits a perpetual
engine under the law and reconciled books (🟢, conditional on the boundary), and in all three the
decree boundary remained — or would have remained — a conjecture.

But the rule of the series has been refined once more. For Riemann we took the boundary — a stake
on RH, in which the consensus believes. For Mersenne we deferred by the sign of the heuristic. For
Polignac the heuristic sign is positive, as with Riemann — and we deferred nonetheless, on a new
ground: where there is no chain there is nothing to prepare, and a serial decree would erase the
uniqueness in which the entire meaning of the quarantine lies.

An honest boundary now requires not only a greenly-unpresentable witness and a stake one need not be
ashamed of, but also that its acceptance does not devalue the exception itself.

`twin_prime_conjecture` remains `sorry`; the Polignac conjecture for gaps 4 and 6 — open; the
quarantine taint — unchanged. Singletons are green, pairs are conjectures, and no open problem has
been declared solved.

<!--navbot-->

---

[← 43. Mersenne via first cause](43_MersenneFirstCause.md) · [Table of contents](00_Overview.md) · [45. Sophie Germain →](45_SophieGermain.md)
<!--/navbot-->
