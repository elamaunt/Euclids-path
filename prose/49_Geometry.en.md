# The Geometry of Euclid's Path: the Arrow, the Curvature, and the Meeting of Lines

<!--navtop-->
[← 48. Fermat numbers](48_Fermat.md) · [Table of contents](00_Overview.md) · [50. Coda →](50_Coda.md)
<!--/navtop-->


> Lean source: `Engine/GeometryFront` — the green part, all of it 🟢 (capstone
> `geometry_of_euclids_path`); the §6 coda — exactly two declarations, 🟡.
> Prose context: [01. EPMI](01_EPMI.md), [33. First cause and the main theorem](33_CausalFirstCause.md),
> [23. Clean graph](23_CleanGraph.md). Status notation: 🟢 — proven under the
> standard axioms; 🟡 — conditional on the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

We have built the concrete descent graph of Step00 — states (centres, defects, absorbers), edges
(clean, boundary, peel, absorb) — and led the seven great problems through it. All that time the
graph was a *machine* for us: it forged witnesses, paid in rank, killed engines. Now let us look at
the same construction differently — not as a mechanism but as a **place**. A place has a shape. And
if the path bears Euclid's name, it is only honest to put to it the three questions with which all
of geometry began.

First: does time flow — is there a direction on this path that tells "before" from "after", and is
it irreversible? Second: what is the shape of the space — flat, spherical, saddle-like; and can
that shape be *computed* rather than postulated? Third, the most ancient: do straight lines meet —
does Euclid's own fifth postulate hold on Euclid's path, are there parallels, do all lines converge
at a single point?

The answers, as will become clear, can be read straight off the edges of the graph — and each of
them turns out to be a theorem, not a postulate. And the last answer turns Euclid himself upside
down.

## The arrow of time: a direction that is proven

Let us begin with time, because without it geometry has no orientation. On Euclid's path the role
of proper time is played by `lexRank` — the lexicographic rank of a state, its "height" in the
well-ordered line. And this time is not chosen but computed: it strictly drops along every edge.

**Theorem 49.1** (`timeArrow_step`, 🟢). *Every real step strictly decreases `lexRank`:
from `RealStep A M0 U V` it follows that `lexRank V < lexRank U`.*

**Why this is true.** This is a re-export of the carrying theorem of the concrete graph: any of the
four step constructors — clean, boundary, peel, absorb — drops the rank. Out of a local fact about
a single edge the whole kinematics unfolds.

Along any non-empty path the rank strictly decreases (`timeArrow_path`); no state is reachable from
itself (`no_return` — time is not looped); an infinite run does not exist at all
(`no_eternal_run` — a direct consequence of the root EPMI, `no_infinite_descent`). And more than
that — time does not merely move forward, it is bounded above by its own start:

**Theorem 49.2** (`every_journey_halts`, 🟢). *Every journey halts no later than the `lexRank` of the
starting state: `k` real steps are possible only when `k ≤ lexRank (run 0)`.*

**Why this is true.** This is the qualified "second law", carried through
`Engine.turned_engine_halts`: a strictly decreasing sequence of natural numbers cannot take more
steps than its initial value.

The arrow of time here is neither a philosophical image nor an assumption about thermodynamics: it
is a **theorem about a finite graph**, and it comes with an exact numerical bound. Every journey
along Euclid's path begins high and ends at the bottom, and its length is measured out in advance.

## Curvature, computed: the spectrum of the space's shape

Now the shape of the space. Curvature is usually specified by a metric and tensors; we have no
metric — only edges. But a directed graph has a curvature of its own, combinatorial, and it can be
*computed*:

**Definition 49.3** (`curvature`). *The curvature of a vertex is `κ(v) = 1 − outdeg(v)`, an integer,
where `outdeg` is the out-degree — the number of geodesic segments leaving `v` downward.*

Let us say it at once and loudly, as in every chapter of the programme: this is the
**combinatorial** curvature of a graph, the deficit or excess of the outgoing geodesic flow, an
analogue of Euler's formula. It is not Riemannian curvature, not sectional, not Ricci–Ollivier;
there is no metric here, no tensors, no smooth structure, and the word "curvature" is legitimate
exactly in the sense of discrete graph theory — and in that sense only.

But within that sense everything is honest: the out-set of every vertex is exhibited as a `Finset`
and proven to coincide exactly with `RealStep` (the carrying lemma `mem_outTargets`), so `outdeg`
counts real edges, not an abstraction.

Why the curvature is oriented forward is likewise not a convenience but a theorem:

**Theorem 49.4** (`inDegree_infinite_at_origin`, 🟢). *An infinite family of edges flows into the origin
`absorber 0`: every defect of the form `defect 0 q minus`, over all `q`, flows into the grave of
zero.*

**Why this is true.** An absorb-edge into `absorber 0` requires only `0 ≤ M0`, and there are
infinitely many such defects. Hence the in-degree of the origin is infinite, the symmetric "total
degree" does not exist as a `Finset`, and undirected curvature is uncomputable in principle. The
directed `κ = 1 − outdeg` is the only computable version; the shape of the space is *obliged* to
look forward, along the arrow of time.

And the computed spectrum — at scale `(A, M0) = (5, 4)`, every value checked by the kernel via
`decide` — is in itself a portrait of the world.

The absorbers carry positive curvature `κ = +1` (`curvature_absorber`): these are the poles where
the flow dies out, where geodesics focus, as meridians converge to a point on a globe.

Defects with
a single exit are flat corridors `κ = 0` (`curvature_defect_0_2`, `curvature_defect_6_5`): a pipe
with no branching.

The defect `(4, 5, +)`, which has both a peel and an absorb, is a branching
`κ = −1` (`curvature_defect_4_5`). And the clean centres are ever more hyperbolic funnels: centre 2
gives `κ = −3`, centre 3 gives `κ = −4`, centre 7 gives `κ = −8` (`curvature_center_2`,
`curvature_center_3`, `curvature_center_7`).

The pattern can be read with bare hands: the higher the centre, the more roads lead down from it,
the more negative the curvature. **The genealogy is hyperbolic; the bottom is spherical.** And the
whole picture is drawn together by a discrete analogue of Gauss–Bonnet:

**Theorem 49.5** (`gaussBonnet_cone3`, 🟢). *On the forward-closed light cone under centre 3 the total
curvature equals the Euler characteristic: `χ(cone3) = Σκ = −5`.*

**Why this is true.** The combinatorial identity `Σκ = |W| − Σ outdeg` (`gaussBonnet_sum`) on the
forward-closed window `cone3` (its closedness checked by the kernel, `cone3_forwardClosed`) yields
`−5`: the two poles and centre 0, at `κ = +1` each, do not outweigh the branchings of the funnels
`−3` and `−4`. The total curvature of the cone is negative — the cone as a whole is hyperbolic,
despite the spherical bottom.

The normalisation `κ = 1 − outdeg` is, of course, a choice, and the link to the genuine
Gauss–Bonnet formula is an analogy, not a theorem of differential geometry; but within the chosen
normalisation the characteristic is computed exactly, by the kernel, without a single assumption.

## A flat world is a perpetual engine: curvature is not an ornament but a necessity

Here geometry joins hands with the programme's central prohibition. Let us ask: could the space of
Euclid's path have been flat everywhere — `κ ≡ 0`, an even corridor with no poles? The answer is
no, and the reason runs deep.

**Theorem 49.6** (`nonpositive_curvature_forces_engine`, 🟢). *If the curvature were nowhere positive
(`∀ v, κ(v) ≤ 0`), a step would lead out of every vertex, iterating the choice would build an
infinite run — the forbidden perpetual engine. Such a world does not exist.*

**Why this is true.** `κ(v) ≤ 0` means `outdeg(v) ≥ 1` — the vertex has a continuation
(`hasStep_of_curvature_nonpos`). If this holds everywhere, the axiom of choice glues those
continuations into an infinite geodesic, and that is exactly Euclid's perpetual engine, killed by
`no_eternal_run`. Hence a conclusion worth setting apart:

**Theorem 49.7** (`space_positively_curved_somewhere`, 🟢). *The space of Euclid's path is positively
curved somewhere: `∃ v, 0 < κ(v)`.*

Curvature here is **not decorative — it is forced**. A positively curved point (a pole, a bottom,
an absorber) is obliged to exist, or else the descent would have no floor and would run forever.
The shape of the space is dictated not by a choice of coordinates but by the impossibility of the
engine: the world must have somewhere to stop.

And a closed geodesic — a legal non-empty cycle — would likewise be an engine witness
(`closedGeodesic_is_engineWitness`), already killed by the acyclicity of `lexRank`
(`no_closedGeodesic`). Flatness and closedness are two faces of one forbidden machine.

## The irony of the postulates: Euclid's path breaks Euclid

Now the third and most ancient question — about straight lines. Let us define a **straight line**
just as Euclid conceived it: a maximal descent path, extended as long as there is anywhere to step.
And let us ask whether the fifth postulate holds on this path.


**Theorem 49.8** (`every_line_ends`, 🟢). *Every straight line runs into a terminal: from any state, in
a finite number of steps you reach a vertex with no exit.*

**Why this is true.** Strong induction on proper time `lexRank v`: if `v` is already terminal — the
path is empty; otherwise the first step strictly drops the rank (the arrow of time!), and by the
induction hypothesis the tail is finite. The arrow of time directly begets the finiteness of
straight lines. And from this:

**Theorem 49.9** (`no_infinite_line`, 🟢). *There are no infinite straight lines at all: no line can be
extended without bound.*

And here is the genuine irony of the entire programme. The statement "a straight line can be
extended without bound" is Euclid's **second postulate**, the one humbler and older than the famous
fifth. On Euclid's path it is precisely this one that falls (`euclid_postulate_two_fails`): the
path named after him violates his own axiom — and not the fifth, about parallels, but the deeper
second, about the very extendability of a straight line.

There are no parallels either (`no_parallel_lines`) — but for a degenerate reason: parallels are
two infinite straight lines, and not even one exists.

Here one must be scrupulously honest, and the Lean source insists on this loudest of all. This is a
degenerate geometry, not an elliptic one. The naive "all lines meet" is false:

**Theorem 49.10** (`bottom_not_unique` and `two_disjoint_lines`, 🟢). *The bottom is not unique —
`absorber 0` and `absorber 1` are both legal and terminal; and there exist two entirely disjoint
finite lines (at `(5,4)`: the route `center 7 → defect 4 5 plus → absorber 4` and the route
`center 3 → defect 0 2 minus → absorber 0`), all nine states of which are pairwise distinct.*

So "all lines converge at a single point", taken head-on, is untrue. There are two distinct meeting
points, and there are pairs of lines that meet nowhere. Whoever wants to read the degeneration of
the second postulate as "ellipticity" is bound to read it through this honest boundary — otherwise
it becomes a lie.

## Meeting through the grave of zero

But there is also an honest, qualified form of meeting — and it is more beautiful than the naive
one. It passes through the single special point of the graph.

**Theorem 49.11** (`zeroPoint_absorbs_all_divisors`, 🟢). *The point 0 absorbs all divisors:
`sideValue minus 0 = 6·0 − 1 = 0` in ℕ, and everything divides zero; hence every `q` divides the
side of zero.*

Let us unpack this loudly, as the source demands: what we have before us is **an artefact and a
marker at once**.

An artefact — because truncated subtraction in ℕ gives `6·0 − 1 = 0`, whereas in ℤ it would be
`−1`; we do not claim that arithmetic "knows" this identity outside the ℕ-model.

A marker — because 0 is the only point whose sides absorb all divisors at once, the only one
through which every downward road passes; it is the ℕ-trace of that very event `0 → 1` from the
first cause, the beginning of the arrow of time. The grave of zero lives on the ℕ-truncation — and
it is also the mark of origin.

**Theorem 49.12** (`line_to_origin`, 🟢). *From any clean centre `m ≥ 1` (given `2 ≤ A`) there is a path
of length 2 into the grave of zero: a boundary step into the defect `(0, 2, −)` — legal, since
`2 ∣ 0` — then an absorb into `absorber 0`.*

Two clean lines that arrived from arbitrarily far above meet in two steps at the common bottom. And
clean sources exist above **every** horizon:

**Theorem 49.13** (`web_above_every_horizon`, 🟢). *For `2 ≤ A` and any `N` there exists a clean centre
`m > N` whose path leads into the grave of zero.*

**Why this is true.** No density is needed — the primorial carrier
`Residuals.carrier_nonempty_above` exhibits a clean centre above any bound, and the bridge
`clean_of_cleanZ` transfers its cleanness from ℤ to ℕ. Hence the only lawful sense of "the lines
meet":

**Theorem 49.14** (`lines_meet_at_origin`, 🟢). *Any two clean starts (given `2 ≤ A`) share a common
terminal — the grave of zero, `absorber 0`.*

Not "a unique meeting point" and not "any two paths intersect" — but: any pair of clean lines has a
**common bottom** at which both arrive. All downward roads pass through zero, and that is where all
clean lines meet.

The fifth postulate is refuted in its honest form, not the naive one: straight lines do meet — at
the grave of zero.

## By the same axiom: the meeting exists, but cannot be known from inside

What remains is the epistemic summary — and here stand the only yellow lines in the whole chapter.
Everything above is green; the coda carries exactly two tainted declarations, and the taint runs
not through a new axiom but through the already accepted causal boundary of the twins
(`twinLowersInfinite_from_step00CausalClosure`), translated into the language of the graph's
vertices.

**Theorem 49.15** (`twin_vertices_beyond_every_horizon`, 🟡). *Above every horizon there is a twin
vertex: for any `N` there exists a twin centre `m > N` both of whose sides `6m ± 1` are prime.*

**Why this is true.** The bridge `twinCenter_of_twinLower` (itself 🟢, axiom-free) shows, by a case
split on the residue modulo 6, that the lower member of any twin pair `p > 3` is `6m − 1` for a
twin centre `m`; and the infinitude of the twin lowers is exactly the accepted boundary. No new
decree content: the same first-cause axiom that holds the infinitude of the twins is here merely
fitted onto the vertices.

**Theorem 49.16** (`lines_meet_but_unknowable_from_inside`, 🟡). *The full summary in four facts: (1) the
fact of the meeting is green; (2) twin vertices exist above every horizon (this line carries the
taint); (3) there is no internal ground for the fact of the meeting; (4) were there one, it would
be a forbidden Euclid engine.*

**Why this is true.** The meeting fact `IntersectionFact` is proven green
(`intersectionFact_green` — the common terminal is the grave of zero). But an attempt to derive
this fact as an internal first cause of the Step00 world — `InternalisedIntersectionGround` — is,
by architecture, exactly a boundary-crossing self-proof, the forbidden engine. It does not exist
(`no_internalisedIntersectionGround`, 🟢), and to know it from inside would be to build an engine
(`knowing_meeting_costs_engine`).

Moreover, this internal ground is itself tautological: it is equivalent to `P ∧ ¬P`
(`internalisedIntersectionGround_iff` — disclosed honestly); there is no substantive content in it,
all the content lives in the green fact.

The summary fits into one phrase: **the lines meet, but this cannot be known from inside.** The
geometric fact is green; its internal grounding costs a perpetual engine.

The twin pair this coda names carries one further green symmetry: the ± flip exchanging its two members
is orthogonal to proper time (`lexRank_side_invariant`, [44](44_SidesAndPolignac.md)) — a fixed-time
involution, not a reversal of time. Fixing one twin places its partner at the same instant.

> **Note (honest boundaries, all six).** Let us gather what must not be inflated.
>
> 1. `κ` here is combinatorial, not Riemannian, and "curvature" is legitimate only in the sense of
>    graph theory.
> 2. Gauss–Bonnet is an analogy under the chosen normalisation `κ = 1 − outdeg`, not a theorem of
>    differential geometry.
> 3. The grave of zero lives on the ℕ-truncation: `6·0 − 1 = 0` in ℕ, but `−1` in ℤ.
> 4. Naive ellipticity is false: the bottom is not unique, disjoint lines exist; only the qualified
>    form of Theorem 49.14 (`lines_meet_at_origin`) holds.
> 5. The carrying theorem for the absence of parallels is the fall of the **second** postulate
>    (Theorem 49.9, `no_infinite_line`), not the fifth; the geometry is degenerate, not elliptic.
> 6. The coda is exactly two 🟡 declarations, the taint through the existing twins boundary, with
>    no new axiom.
>
> The capstone `geometry_of_euclids_path` gathers the whole green half in a single theorem with no
> user axioms (the expected triple: `propext`, `Classical.choice`, `Quot.sound`).

## Generalization: total curvature is the Euler characteristic, and nowhere is flat

We close the green half by generalizing its two pillars — the discrete Gauss–Bonnet (Theorem 49.5)
and forced positivity (Theorems 49.6–49.7) — from a single concrete cone and from the whole graph to
**any** forward-closed region.

**Theorem 49.17** (`gaussBonnet_eq_euler`, 🟢). *On any forward-closed window `W` the total curvature
equals the Euler characteristic: `Σκ = |V| − |E| = χ(W)`, where `|E|` is the number of edges of the
induced subgraph (`inducedEdges`).*

**Why this is true.** The combinatorial identity `Σκ = |W| − Σ outdeg` (`gaussBonnet_sum`) holds
always; forward-closedness adds exactly what turns the right-hand side into a characteristic: every
edge out of `W` lands back in `W`, so `Σ outdeg` counts precisely the internal edges
(`forwardClosed_inducedEdges_eq`). And since the graph is acyclic (`no_closedGeodesic`) there are no
antiparallel edges, so the directed count coincides with the undirected one — and `|V| − |E|` is a
bona-fide Euler characteristic of the 1-complex. This remains an analogy under the normalisation
`κ = 1 − outdeg` (honest boundary 1), not a theorem of differential geometry; but within it `χ` is
computed exactly. The concrete cone of 49.5 is a special case: `eulerChar 5 4 cone3 = −5`
(`eulerChar_cone3`).

**Theorem 49.18** (`forwardClosed_has_pole`, 🟢). *Every nonempty forward-closed region has a pole: a
terminal vertex with `κ = +1`.*

**Why this is true.** From any vertex of the window a line reaches a terminal in finitely many steps
(`every_line_ends`), and forward-closedness keeps the whole path inside `W`
(`pathN_stays_in_forwardClosed`), so the terminal too lies in `W`; a terminal has no exits, hence
`outdeg = 0` and `κ = +1` (`curvature_one_of_terminal`). This is the local form of Theorem 49.7:
positive curvature is forced not "somewhere in the whole graph" but **in every bounded region**.

**Theorem 49.19** (`forwardClosed_not_flat`, 🟢). *No nonempty forward-closed region is flat: `κ ≤ 0`
everywhere within it is impossible.*

**Why this is true.** The pole `κ = +1` of Theorem 49.18 contradicts `κ ≤ 0`. This is the local form
of Theorem 49.6: not only the whole world cannot be flat, but neither can any of its
downstream-closed pieces — each has a floor.

Thus the pressure on flat space is pushed to the limit: existence has a bottom not only globally, but
in every region closed along the arrow. Curvature is forced not as decoration and not as a single
pole for the whole world, but locally, everywhere.

## Philosophical digression

There is a peculiar bitterness and a peculiar beauty in the fact that the path named after Euclid
violates a postulate of Euclid himself. For twenty-three centuries geometers wrestled with the
fifth postulate — the one about parallels — and out of that struggle were born Lobachevsky,
Riemann, the whole non-Euclidean revolution. Yet Euclid's path breaks not the fifth but the
second — the one that seemed so obvious that it went almost unnoticed: "a bounded straight line can
be continuously extended".

On a well-ordered line with an arrow of time this modest postulate is false: one cannot extend
forever, because eternal extension is precisely the forbidden perpetual engine. The most
inconspicuous of the axioms of the *Elements* turned out to be the most fragile — and it falls not
to a change of metric, but to thermodynamics.

Herein lies, perhaps, the deepest irony of the entire programme: we returned to the most ancient
proof-object of mathematics, to infinite descent, going back to those same *Elements* — and found
that it cancels one of the postulates with which the *Elements* began.

The shape of the resulting space is not accidental but *recognisable*. It is wound inward: a
hyperbolic genealogy at the top, where each centre splits into ever more descending roads, and a
focusing, spherical bottom below, where everything draws together toward the absorber-poles.

This is exactly the discrete face of that inverted, contracting self-similarity which the coda will
name the principal shape of Euclid's path: a classical fractal scatters outward, toward infinity,
while this one winds in toward the beginning. Our computed curvature spectrum is a numerical
portrait of the same spiral: negative branching curvature above, positive converging curvature
below, and the total characteristic of the cone `χ = −5`, pulling toward a saddle, toward a funnel,
not toward a sphere. The geometry does not run away — it returns.

And this shape is stitched together by the two most fundamental prohibitions acting jointly. The
arrow of time — the irreversibility of `lexRank` — fixes the orientation: the space has an up and a
down, a "before" and an "after", and there is no way back. The impossibility of the engine — the
prohibition of infinite descent — fixes *completedness*: the shape has a bottom, and the curvature
is obliged to turn positive somewhere so that this bottom can exist.

Neither of these properties is postulated; both are proven, and out of the two of them the geometry
is moulded. Space here is not a stage on which the engine prohibition is played out, but its
shadow: directedness, curvature, the finiteness of lines, the common meeting point — all of these
are facets of one impossibility, read geometrically.

This places Euclid's path beside the boldest programme of modern physics — **causal set theory**,
where spacetime is modelled as a locally finite partially ordered set: the order is
causality-time, the discreteness is space. Our well-ordered line with its strict arrow is exactly
such an object.

And the most striking thing here is the epistemic limit. The fact that all clean lines meet at the
grave of zero is green and provable. But to ground this fact *from within* the world, to make the
meeting an internal first cause of itself, is impossible, for that self-enclosed grounding is
tautologically `P ∧ ¬P` and would cost a perpetual engine.

Knowledge of the shape of one's own space has a price, and the price is forbidden. An observer
inside Euclid's path can prove that the lines converge, but cannot ground it while standing inside;
the grounding comes only from outside, by the single accepted first cause. The geometry is
knowable; its self-grounding is not. And in this "cannot be known from inside" lives the same
infinitude of twins that holds the entire programme: the one thing that cannot be certified from
the depths of the contracting order.

Hence the final irony, subtler than the postulational one. Euclid's path is *finite*: its second
postulate has fallen, and every straight line breaks off at the grave of zero — for infinite
extension is precisely the forbidden perpetual engine.

And the same path is *infinite* — for its
end cannot be seen from inside: to certify that the twins run dry would be to start up that very
engine, and for the one walking within, the road always stretches on. Finite by thermodynamics and
infinite by unknowing; closed to the gaze from outside and open for the one who walks. Both truths
are rigorous — and they live in one and the same straight line.

## Place in the greater arc

Euclid's three questions have received their answers, and all three are theorems, not postulates.
Time flows and is irreversible (`timeArrow_step`, `every_journey_halts`). Space is curved, and its
curvature is computed by the kernel, with a positive bottom and a hyperbolic genealogy, drawn
together by the Gauss–Bonnet formula. Straight lines are finite — Euclid's second postulate
falls — and all clean lines meet at the grave of zero, though this cannot be known from inside.

The green half is bundled into a single theorem by the capstone `geometry_of_euclids_path`; the
yellow coda is carried by exactly two declarations, by the same accepted axiom of the twins, with
no new decree.

We now possess not only the seven masks of one prohibition, but also the **shape** of the place
where they all live. The arrow, the curvature, the meeting point — these are no longer properties
of an individual problem, but properties of the very spacetime of Euclid's path.

Everything is
ready for the last step: the [coda (chapter 50)](50_Coda.md) will gather the arrow of time, the
forced curvature, the contracting fractal, and the impossibility of self-grounding into a single
synthesis — a reading of Euclid's path as a possible structure of spacetime, where the most ancient
proof-object of mathematics turns out to be the skeleton of physics' youngest question.

<!--navbot-->

---

[← 48. Fermat numbers](48_Fermat.md) · [Table of contents](00_Overview.md) · [50. Coda →](50_Coda.md)
<!--/navbot-->
