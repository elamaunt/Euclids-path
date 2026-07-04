# Goldbach and Legendre: the witness that can be checked but cannot be presented

<!--navtop-->
[← 45. Sophie Germain](45_SophieGermain.md) · [Table of contents](00_Overview.md) · [47. Perfect numbers →](47_PerfectNumbers.md)
<!--/navtop-->


> Lean source: `Engine/GoldbachManifestationFront` — a green chain, all 🟢;
> `Engine/LegendreDesertFront` — a green chain, all 🟢 (plus a unique unconditional companion —
> Bertrand's postulate). Status legend: 🟢 — proven under the standard axioms; 🟡 — conditional on
> the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

Riemann and Mersenne have taught us to read a refutation as an engine, and we already distinguish two
sorts of witnesses.

Mersenne's witness was a Π-statement — a bound, a whole class of numbers, an
absence stretched into infinity; it cannot be presented, because presenting it would mean surveying the
entire tail at once.

Riemann's witness was a data object — a concrete zero off the line; it cannot be
presented, because constructing such a zero would mean refuting RH.

These two fronts — Goldbach and
Legendre — follow the Riemann line, but carry it to its limit, and therein lies their shared trait,
rare in the series.

Their witness is a data object, and moreover **pointwise decidable**. Not a Π-form that must be
proven; not an analytic zero whose vanishing must be established by analysis — but a concrete natural
number about which the machine says "yes" or "no" in finite time.

This is the strongest form of unpresentability in the entire series, and its paradox is visible at
once: each individual candidate is the *easiest of all* to check, while presenting a genuine witness
is *impossible*.

Let us work through both fronts, and then also why the ease of checking and the impossibility of
presenting do not contradict each other here, but are two sides of a single quantifier.

## Goldbach: a fake dies instantly, a genuine one would refute the conjecture

The binary Goldbach conjecture asserts that every even `E ≥ 4` is a sum of two primes. The deviation
here is a concrete even number that admits no such decomposition: `GoldbachViolationAt E`
means `4 ≤ E`, `E` is even, and `¬ GoldbachRep E`.

The key property of this predicate is that it is decidable through and through. The existential "`E`
is a sum of two primes" reduces to a bounded search over a single prime `p < E` with a primality check
on the complement `E − p`. The kernel-level `Nat.decidableExistsLT` together with `Nat.decidablePrime`
yield the instance automatically, and `decide` works over this form directly. The negation of a
decidable statement is decidable, `Even` and `4 ≤ ·` are too — hence the violation itself is
decidable.

From this comes the first pair of green theorems, both about pointwise decidability in action.

**Theorem 46.1** (`goldbach_upTo_52`, 🟢). *Every even `E` in the range `4 ≤ E < 52` is a sum of two
primes.*

**Why this is true.** `decide` iterates over all such `E` over the decidable bounded form and finds a
decomposition for each; the result is transported to `GoldbachRep` through a proven equivalence. Not a
single hypothesis, not a trace of the axiom — pure machine verification.

**Theorem 46.2** (`goldbachViolation_ge_52`, 🟢). *Every witness of a Goldbach violation sits at
`E ≥ 52`.*

**Why this is true.** The smaller even candidates have already been screened out by the previous
theorem: if a violation lived below 52, `goldbach_upTo_52` would hand it a decomposition, while the
witness denies any decomposition — a contradiction. This is how the domain is localised: a fake
planted anywhere below 52 dies by `decide` on the spot.

But above 52 the real darkness begins. The literature has verified the conjecture up to `4·10^18`
(Oliveira e Silva and others) — that bound is not formalised, and our green covers only `≥ 52`.
Presenting a genuine witness would mean refuting Goldbach.

The manifestation front over this witness is built the Riemann way — object-quantified, without a
gate (a gate is a named open red input still missing on the way to the goal; see the
[glossary](GLOSSARY.md)). The law `GoldbachManifestationLaw` ranges over the witness type
`GoldbachViolation` and says: every concrete violation manifests.

At every ledger scale not below the number itself, wherever the projection reconciles the books —
that is, resolves the collisions of flows at the given scale — the deviation shows itself as an
unpayable infinite supply of flows (`DeviationFlowSupply`
— the same object that the Riemann front builds).

No gate is needed for the witness here: the scale anchor `M0 := E` is tied to the number itself — the
height of the deviation is the deviation itself — and an ungated "explosive" form simply does not
exist. And here is the load-bearing assembly.

**Theorem 46.3** (`noGoldbachViolation_of_manifestation_and_boundary`, 🟢 — essence). *No engines + an
accepted boundary + the manifestation law ⟹ there are no Goldbach violations — that is, the Goldbach
conjecture holds.*

**Why this is true.** A hypothetical witness `V` yields the scale `M0 := V.1`. The accepted boundary
supplies a resolving projection exactly at it (via `le_refl`). The law turns the violation into an
infinite family of flows — not ex falso (not by deriving "anything from falsehood"), but as data. A
finite key collides two of its members, an engine-witness is assembled from the collision — and it is
killed precisely by the hypothesis "there are no engines". Through the bridge
`goldbachConjecture_iff_no_violation` the same triple is carried all the way to the Goldbach
conjecture itself.

The reading is direct: an unpaid even number would manifest a perpetual engine. The heuristic sign
here points in favour of the conjecture: the law's quantifier ranges over an expectedly empty witness
type, the law is expectedly vacuously true, and this is an exact mirror of Riemann, not of an
inverted Mersenne.

As with Mersenne, we add no decree fields — the law lives as a definition inside the green front.

## Legendre: the only green companion — and the honest admission that it does not save

Legendre's conjecture (1808) asserts that between any consecutive squares `n²` and `(n+1)²`, for
`n ≥ 1`, there lies a prime. The deviation is a prime desert in this interval: `LegendreViolationAt n`
means `1 ≤ n` and `PrimeDesertBetween (n²) ((n+1)²)`, that is, not a single prime strictly between
the squares.

The predicate is again decidable — through a bounded-ball form (`Nat.decidableBallLT`, reducible under
`decide`) — and everything repeats, mirroring the Goldbach pair.

**Theorem 46.4** (`legendre_holds_upTo_10`, 🟢). *For all `n` with `1 ≤ n < 11` there is no Legendre
violation: $\forall n,\ 1 \le n < 11 \Rightarrow \neg\,\mathrm{LegendreViolationAt}(n)$.*

**Why this is true.** `decide` iterates over all candidates `1 ≤ n < 11` over the decidable
bounded-ball form and finds, for each, a prime strictly between `n²` and `(n+1)²`; no axiom, no
`native_decide`.

**Theorem 46.5** (`legendreViolation_ge_11`, 🟢). *Every witness of a Legendre violation sits at
`n ≥ 11`: $\forall V:\mathrm{LegendreViolation},\ 11 \le V.1$.*

**Why this is true.** The smaller points are screened out by Theorem 46.4 (`legendre_holds_upTo_10`):
a witness below 11 would receive a prime in its interval, while the witness denies it — a
contradiction. The literature bound far beyond `10^18` is not formalised; only `≥ 11` is green. All
just as with Goldbach.

But this front has something found nowhere else in the series — a green unconditional companion.

**Theorem 46.6** (`no_desert_doubles`, 🟢). *A prime desert cannot survive a doubling: between `n` and `2n`
(for `n ≠ 0`) there is always a prime.*

**Why this is true.** This is a direct repackaging of Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`, mathlib, unconditional). No open problem, no gate:
between `n` and `2n` a prime exists — a proven theorem, not a decree. The only place in the entire
front where the vacuum genuinely, unconditionally has no crack.

And exactly here comes the honest disclosure without which the green Bertrand would turn into an
inflated claim. Bertrand covers the doubling `[n, 2n]`, while Legendre needs the interval
`(n², (n+1)²)`. Does the former suffice for the latter?

**Theorem 46.7** (`legendre_interval_shorter_than_bertrand`, 🟢). *For `n ≥ 3` we have `(n+1)² < 2n²`.*

**Why this is true.** A pure inequality, `nlinarith`. But the consequence is fundamental: Legendre's
interval is **shorter** than Bertrand's doubling. Hence the green "a desert does not double" is
powerless on the quadratic crack — Bertrand does not solve Legendre.

The module records this with an explicit flag `NoBertrandToLegendreImplicationClaimed = True`: no
implication Bertrand ⟹ Legendre is claimed or proven here. The green strength of the Bertrand block
remains strictly weaker than the open Legendre, and we do not hide this but write it out
machine-checkably.

From there the object front repeats the Riemann architecture verbatim. `LegendreManifestationLaw`
is object-quantified over witnesses, the scale anchor `M0 := V.1²` is tied to the desert itself.

**Theorem 46.8** (`noLegendreViolation_of_manifestation_and_boundary`, 🟢 — essence). *No engines + an
accepted boundary + the manifestation law ⟹ there are no Legendre witnesses:
$\neg\,\mathrm{SomeConcreteEuclideanEngine} \wedge \mathrm{TheStrictLastStep00Obligation} \wedge
\mathrm{LegendreManifestationLaw} \Rightarrow \neg\,\mathrm{Nonempty}\ \mathrm{LegendreViolation}$.*

**Why this is true.** The same triple as in Theorem 46.3 (`noGoldbachViolation_of_manifestation_and_boundary`):
a hypothetical witness `V` yields the scale `M0 := V.1²`, the boundary supplies a resolving projection
exactly at it (via `le_refl`), the law supplies the family of flows, an engine-witness is assembled
from the collision — and it is killed by the hypothesis "there are no engines". Through the bridge
`legendreConjecture_iff_no_violation` the same triple is carried all the way to Legendre's conjecture
itself. The witness is anchored exactly where the desert lives — at `n²`.

> **Note.** Neither front has a single free Prop field, free gate, or renamed conclusion —
> every hypothesis is named arithmetically, the supply is the same strict object
> `DeviationFlowSupply` as Riemann's, and the Impossible side at resolved scales is the reused
> green theorem `no_deviationFlowSupply_at_resolved_scale`, never a decree.
>
> Neither module imports the quarantine — the only module where the axiom `step00FirstCause` lives;
> no `axiom`, no `sorry`, no `native_decide`. And both heuristic signs point in favour of the
> conjecture: the witness types are expectedly empty, the laws expectedly vacuously true — the
> Riemann orientation, not Mersenne's. Decree fields are deliberately not added: serial expansion
> would devalue the quarantine.

## Philosophical digression: a witness verifiable but not producible

One image runs through the whole causal line — a witness that can be checked but cannot be presented.
In the twin, Riemann, and Mersenne branches this unpresentability had an analytic or infinite root: to
present a zero off the line, one would have to hold it as the outcome of analysis; to present the
Mersenne-twin bound, one would have to survey the entire infinite tail. The witness could not even be
*written down* as a finite object.

Here the unpresentability is subtler — and therefore sharper. Every candidate witness is finite and
machine-checkable: an even number `E`, a point `n`. Hand us any concrete pretender — and in finite
time we shall say, by `decide`, whether it is a witness or a fake.

The difficulty is not in checking *any single one*; it lies entirely in the **quantifier**. The
conjecture says "for all `E`" and "for all `n`", and no finite search closes such a claim: however
much we check — `4·10^18` for Goldbach, even further for Legendre — beyond the verified edge there
remains an infinite tail of the unverified, and it is exactly there that the lone counterexample could
be hiding.

This is precisely the boundary between decidability and undecidability, read on arithmetic: pointwise
everything is decidable, while quantified over all of `ℕ` it no longer is, and no machine will
traverse infinity in finite time.

The engine reading gives this an exact form. A counterexample would be a crack in the vacuum — the
single even hole, the single quadratic desert. And finding it would cost the same impossible thing: an
unpaid deviation would manifest a perpetual engine.

**Conclusion.** We may check as long as we please that the vacuum is *so far* without cracks, and we
cannot present a crack — not because it exists somewhere and is hard to reach, but because its
existence is, by construction, the forbidden engine. The checkability of every candidate and the
unpresentability of the witness are not in contradiction: the first lives at the level of a point, the
second at the level of the quantifier, and the bridge between them is precisely the engine
prohibition.

And here it is worth being honest to the end — for the sake of the one place where the vacuum has no
crack by a genuine theorem. Bertrand is green and unconditional: between `n` and `2n` there is always
a prime, without any decree, without a gate, without a wager. It is the hardest arithmetic in the
whole chapter — and exactly for that reason it is so instructive that it falls short of Legendre.

The interval `(n², (n+1)²)` is shorter than the doubling `[n, 2n]` (for `n ≥ 3` strictly,
`(n+1)² < 2n²`), and on this quadratic crack Bertrand's unconditional strength ends. The temptation
would be great — to pass Bertrand off as an "almost Legendre" — and we renounced it with an explicit
flag.

**Section takeaway.** A green theorem next to an open problem does not make the open problem green; it
merely delineates sharply where the proven ends and the wager begins. That is the front's lesson: even
where we hold a genuine unconditional fact, honesty demands showing exactly what it does *not* close.

## Goldbach and Legendre beyond the same horizon

This chapter, like Collatz and P/NP, has an epistemic slope — `Engine/GoldbachLegendreEpistemic`,
entirely green. Assemble an "internal self-grounding of the solution": a carrier anchors a scale not
below its own witness (`E ≤ M0` for Goldbach, `n² ≤ M0` for Legendre), reconciles the books, and
carries the manifestation of this one witness — the structures `InternalisedGoldbachGround` and
`InternalisedLegendreGround`.

From such a premise the engine-witness is built as an object — `internalisedGoldbachGround_builds_engine`
and `internalisedLegendreGround_builds_engine`, not ex falso, but the same chain as in the load-bearing
assembly, only fuelled by the manifestation of a single witness rather than the whole law. **A
violation with the books reconciled is itself an engine**, now written out as a construction.

And then the assembly self-destructs. At a resolved scale there is no supply — the contradiction is
delivered by the green engine theorem `no_deviationFlowSupply_at_resolved_scale`, and so that the form
is not an empty excuse, its non-emptiness is exhibited by the green `deviationFlowSupply_of_twinBound`.

Hence `no_internalisedGoldbachGround` and `no_internalisedLegendreGround`, and from them the theorems
`goldbachCause_unknowable` and `legendreCause_unknowable`: **the cause cannot be known from inside — a
theorem, not a slogan**.

The forks `goldbach_no_internal_decision_without_engine` and
`legendre_no_internal_decision_without_engine` lay this out panel by panel: to refute from inside =
to present an engine (conditional on the law-as-definition — an unconditional analogue of
`nonHalting_carries_perpetual_engine` does not and cannot exist for these fronts without solving the
open problem itself); to self-ground = to self-destruct; only the external boundary decides — the
hypothesis `TheStrictLastStep00Obligation` — together with the law.

For Legendre a fourth panel is added to the three, an
unconditional one: Bertrand's Theorem 46.6 (`no_desert_doubles`) with the honest flag
`NoBertrandToLegendreImplicationClaimed` — strong, yet still not closing the quadratic crack.

And here "verification, not derivation" sounds in its purest form in the whole series. For Collatz the
check is a run of the orbit, for P/NP a finite-fuel budget; here it is literally `decide`: the witness
is pointwise decidable, and about every candidate the machine answers in finite time.

The theorems `goldbach_verification_not_derivation` and `legendre_verification_not_derivation` place
three facts side by side: internal knowledge of the cause is impossible; the check is machine-swept
(Theorem 46.1 `goldbach_upTo_52`, Theorem 46.4 `legendre_holds_upTo_10`); and therefore the witness is
pushed back exactly to
the depth of the sweep — `≥ 52` and `≥ 11`, not a step further (the literature's `4·10^18` is not
formalised; only this much is green). **The solution is findable exactly as far as the check reaches**
— here this is not a figure of speech but the very structure of the theorem.

The overall summary is `goldbachLegendre_locked_behind_engine_status`, a mirror of
`pnp_locked_behind_engine_status` and, like it, without a decree conjunct: there are no Goldbach or
Legendre fields in the decree — serial expansion would devalue the quarantine.

> **Note (what we are not claiming).** This is NOT a solution of the 1742 conjecture nor of the
> 1808 problem, and NOT Gödel — no incompleteness, no fixed point, only a model-internal engine wall.
> The layer is honestly weaker than the P/NP benchmark: the field `beyondOwnHorizon` is faith in a
> law-as-definition, with no green instance of it (the witness types are expectedly empty), whereas
> for P/NP the analogous layer (`concreteSupply_unbounded_smallScale`) is green-true. The module does
> not import the quarantine, the repository's taint does not change; both conjectures remain open
> 🔴 inputs behind a door locked from inside.

## Place in the greater arc

The line "what a refutation would cost" now covers the two oldest questions about primes as well.
Goldbach and Legendre enter with the same manifestation architecture as Riemann: an object witness,
the heuristic sign in favour of the conjecture, the decree field not taken — yet with their own
limiting property, pointwise decidability, which makes them the strongest form of unpresentability in
the series.

The series' rule has gained one more distinction: the unpresentability of a witness need not have an
infinite or analytic root. It can sit entirely in the quantifier over a decidable predicate, and then
the ease of checking any candidate and the impossibility of presenting a witness turn out to be two
readings of one "for all".

Bertrand remains the only green unconditional support of this front — and honestly marked as
insufficient for Legendre. `GoldbachConjecture` and `LegendreConjecture` remain open inputs; the
quarantine's taint has not shifted; not a single open problem has been declared solved.

<!--navbot-->

---

[← 45. Sophie Germain](45_SophieGermain.md) · [Table of contents](00_Overview.md) · [47. Perfect numbers →](47_PerfectNumbers.md)
<!--/navbot-->
