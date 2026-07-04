# Sophie Germain: doubling of the centre and the pearl of the series

<!--navtop-->
[← 44. Sides and Polignac](44_SidesAndPolignac.md) · [Table of contents](00_Overview.md) · [46. Goldbach and Legendre →](46_GoldbachLegendre.md)
<!--/navtop-->


> Lean source: `Engine/SophieGermainBranch.lean` — the branch with the classical theorem, all 🟢;
> `Engine/SophieGermainManifestationFront.lean` — the green manifestation front (a mirror of Mersenne)
> with a restricted section 3 (mod 4). Status legend: 🟢 — proven under the standard axioms;
> 🟡 — conditional on the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

The whole arithmetic zoo of this part — Mersenne, the pentadic branch, Collatz — rested on a single device: every
branch has a chain of centres with the recurrence `m → am + b`, it grows strictly, and the only question is whether
it can be sawn through (whether it builds a forged witness — a machine counterexample, see the [glossary](GLOSSARY.md)) or not. The Mersenne `4m+1` would not saw, the pentadic `5m+1`
would, and on that contrast the entire honesty of the manifestation architecture rested.

Yet in all those branches the arithmetic facts themselves were modest — vacuous series, half-line identities,
growth by `omega`. Not a single *substantive* classical theorem was among them.

The Sophie Germain branch is different. It brings the same chain of centres — but with it comes the one genuinely
non-trivial classical theorem of the whole addition: **a Sophie Germain prime kills the primality of a
Mersenne number.** This is a result of Euler and Lagrange, and here it is not retold but machine-proven down to the
last step.

Around this pearl the chapter is built: first the geometry of the pair in the programme's language, then the theorem
itself, and then — the reason it matters to the greater arc at all. It turns out to be a formal shard of the very
heuristic by which quarantine §16 (chapter 43) justified declining to take the Mersenne boundary.

## Geometry of the pair: why SG primes live only on the minus side

A Sophie Germain pair is `(p, 2p+1)`, both prime (`IsSophieGermain`). In the programme's coordinates, where
every prime `> 3` sits on a side `6m ± 1`, this pair displays a rigid one-sidedness.

**Theorem 45.1** (`not_sophieGermain_of_plusSide`, 🟢). *If `p = 6m + 1` with `m ≥ 1`, then `2p + 1` is not
prime.*

**Why this is true.** We compute directly: `2(6m+1) + 1 = 12m + 3 = 3(4m+1)`, and three divides the companion
exactly. For `m ≥ 1` the companion exceeds three — hence composite. The plus side drops out entirely: an SG prime
`p > 3` cannot have the form `6m+1`.

The minus side remains, and it does not merely survive — it forces a residue:

**Theorem 45.2** (`sophieGermain_minusSide`, 🟢). *An SG prime `p > 3` must satisfy `p ≡ 5 (mod 6)`.*

**Why this is true.** A prime `p > 3` is divisible by neither 2 nor 3, so `p % 6` is either 1 or 5.
The first has just been excluded by the plus side (Theorem 45.1). Hence `p ≡ 5 (mod 6)`, that is, `p = 6m − 1`.

And now — the essence for whose sake the branch entered this series at all. On the minus side the SG map, in the
coordinates of centres, is pure **doubling**:

**Theorem 45.3** (`sg_center_doubling`, 🟢). *`2(6m − 1) + 1 = 6(2m) − 1`.*

**Why this is true.** Expand the brackets — the identity checks in one's head. But its meaning lies not in the
arithmetic but in the lineage: the companion `2p+1` of a pair with centre `m` itself sits on the minus side, and its
centre is exactly `2m`. The SG map of centres is `m → 2m`. This is the third sibling of those chains: the Mersenne
`4m+1`, the pentadic `5m+1`, and now the SG doubling `2m`. The first SG primes lay this chain out visibly —
`5, 11, 29, 89` (`sg_instances`): centres `1, 2, 5, 15`, companions `11, 23, 59, 179`, each next
member of the family growing from the doubled centre of the previous rank.

> **Note.** The criterion `isSGCenter_iff` closes the picture symmetrically: `m` is an SG centre (both numbers
> `6m−1` and `6(2m)−1` are prime) exactly when `6m−1` is an SG prime. The language of centres and the language of
> pairs are here one and the same, rewritten through doubling.

## The pearl: a Sophie Germain prime extinguishes a Mersenne

Now — the only substantive classical theorem of the whole addition, machine-proven in its
entirety.

**Theorem 45.4** (`sophieGermain_divides_mersenne`, 🟢). *If `p` is prime, `p ≡ 3 (mod 4)`, `p > 3`, and
`q = 2p + 1` is prime, then `q ∣ M_p` and the Mersenne number `M_p = 2^p − 1` is composite.*

**Why this is true.** The route is the classical Euler–Lagrange one, and it hangs on a single meshing of residues.
Since `p ≡ 3 (mod 4)`, we get `q = 2p + 1 ≡ 7 (mod 8)`. But `q ≡ ±1 (mod 8)` is exactly the condition under which `2`
is a quadratic residue modulo `q` (`ZMod.exists_sq_eq_two_iff`); seven lands in the admissible
class.

Hence `2` is a square in `ZMod q`, and by Euler's criterion `2^((q−1)/2) ≡ 1 (mod q)`. And the exponent
here is exactly `p`, because `(q−1)/2 = (2p)/2 = p`. Altogether `2^p ≡ 1 (mod q)`, that is, `q ∣ 2^p − 1 = M_p`.
It remains to make sure the divisor is proper: for `p ≥ 4` we have `2p + 1 < 2^p − 1`
(`two_mul_add_one_lt_mersenne` — a simple induction on the exponent), so `1 < q < M_p`, and `M_p` cannot
be prime.

The demonstration is not abstract:

**Theorem 45.5** (`mersenne_composite_examples`, 🟢). *`23 ∣ M_11 = 2047`, and `M_11` is composite.*

Here `p = 11 ≡ 3 (mod 4)`, the companion `q = 23` is prime, and indeed `2047 = 23 · 89` — it splits into
exactly the predicted divisor. The theorem does not merely deny primality; it points a finger at the
factor.

> **Note.** The proviso about `p = 3` is not pedantry but an honest edge that the formalisation respects.
> The condition `p > 3` is not decorative: for `p = 3` the companion is `q = 7`, but `7 = M_3` is itself the Mersenne
> number, and it is *prime*. The divisor would coincide with the dividend — there is no "proper" decomposition. On
> exactly this one exponent Euler's route yields a divisor but not compositeness; and `hgt : 3 < p` in the
> theorem's signature is the machine record of precisely this exception. The programme does not sweep the edge under
> the rug: it names it.

## Two bets facing each other

The pearl is beautiful in its own right, but it enters the programme's greater arc through one coincidence that is
hard to call accidental. Recall chapter 43: there the Mersenne boundary passed every machine honesty check
and yet remained *not taken* — for the single reason that the sign of the heuristic was inverted.

To take it would have meant betting on the unboundedness of Mersenne twins, whereas the heuristic looks the other
way. And one of that heuristic's arguments against the primality of Mersenne numbers is exactly this: Sophie Germain
primes extinguish candidates one by one.

The branch's manifestation front makes this argument formal. It is a mirror of the Mersenne front: the same
Π-witness of absence (`SGAbsenceAbove P`), the same doubling chain that does *not* saw
(`isEmpty_properCenterPeel_two_one`, 🟢 — the coefficient `2`, though prime, is not congruent to `±1` modulo 6 and
does not divide the odd sides `6n ∓ 1`; already the first step `2 → 1` is empty), the same law gated — that is, locked behind an honestly named input — by a witness,
the same essence "no engines + boundary + law ⟹ Sophie Germain pairs are unbounded".

All of this is an exact copy of the Riemann and Mersenne architecture, and there is no need to hold the spotlight on it.

But this front has a section that no other has. It can work not over the whole family
of SG primes but over the subfamily `p ≡ 3 (mod 4)` — exactly the one the pearl turns into killers of
Mersenne primality. And then its conclusion changes sign:

**Theorem 45.6** (`mersenneComposites_unbounded_of_noEngine_boundary_and_sgManifestation`, 🟢, conditional).
*No engines + an accepted boundary + the restricted 3 (mod 4) law ⟹ there are unboundedly many primes `p` with
composite `M_p`.*

**Why this is true.** The essence of the restricted front gives the unboundedness of SG primes of class `3 mod 4`
(`SGThreeMod4Unbounded`), and the branch's pearl — via `mersenneComposites_unbounded_of_sg` — turns
each such `p` into an exponent with composite `M_p`. This is where the two lines meet.

**Conclusion.** The Mersenne front declined to bet on the *prime* side of the quantity `M_p`. This front, by its
conclusion, manufactures the *composite* side of the same quantity. One bet was rejected by the sign of the heuristic;
the second — its reverse — assembles green, conditional on the same unboundedness hypothesis. Two bets on
`M_p`, facing each other across a single number.

Let us honestly note the limits of this construction as well. The restricted gate `SGThreeMod4AbsenceAbove` is *weaker*
than the full-family one, so the restricted law is unlocked by a weaker witness, and the full-family law does not yield
it directly. No implication between the two laws is asserted or consumed here: the corollary
feeds only on the restricted law.

And the unconditional infinitude of composite Mersenne numbers has itself long been known to the literature by other
methods; here only the SG route to it is honestly recorded.

As with its neighbours in the series, no boundary field has been added — but for the reason opposite to Mersenne's. The
sign of the Sophie Germain heuristic is *positive* (Hardy–Littlewood promises `~ 2C₂ · x / ln² x` pairs), so it would
have been a bet on the expectedly true, as with Riemann. And yet the verdict of §17 says that manifestation fields
beyond Riemann the programme does not multiply.

## Philosophical digression

Sophie Germain carried on her correspondence with Gauss under a man's name — "Monsieur Leblanc" — because the academy
of her century did not admit women to mathematics. When Gauss learned the truth, he wrote that surprise gives way to
admiration all the more strongly, the harder the path had been.

The primes bearing her name she introduced in her siege of Fermat's Last Theorem: for such `p` the first case of the
theorem yielded. Two centuries later the same numbers guard the security of digital communication. A "safe prime"
`q = 2p + 1` with its SG prime `p` gives a group in which the discrete logarithm does not fall apart into
small factors, and on this stands half of Diffie–Hellman cryptography.

A number born in the siege of one old problem protects secrets its author could never have imagined.

But something deeper lies here, and it is about the programme's grid itself. Sophie Germain's conjecture — the
infinitude of her primes — is open, just as the conjecture on the primality of infinitely many Mersenne numbers is
open. These are two different unsolved problems, from different corners of number theory.

And now the pearl of this chapter — together with the restricted front — builds a conditional bridge between them: *if*
there are infinitely many SG primes of class `3 mod 4`, *then* there are infinitely many composite Mersenne numbers. The
bridge is one-way, honest, deciding nothing by itself; but it makes visible a kinship that the usual
notation would never reveal.

The open problem of Sophie Germain turns out to be tied to the *composite* side of the open problem of Mersenne — and
tied by exactly the classical division Euler found two and a half centuries ago. The grid of centres does not
prove new theorems; it develops hidden arithmetic lineages, as a developer brings out a latent
image.

And the third sibling of the chains now stands in the row at its proper place. The Mersenne `4m+1`, the pentadic `5m+1`,
the SG doubling `2m` — three recurrences, three families of centres, of which only the pentadic saws. The programme
did not choose these chains for the beauty of the symmetry; they fell out of the branches independently, each from its own
problem. That all three fit into one language `m → am + b` and one question about the saw is not an ornament but
evidence that the language was fitted to the subject, not the subject bent to the language.

## Sophie Germain beyond the same horizon

The wall against which internal solutions shatter ([chapter 56](56_CollatzFirstCause.md)) has a Sophie Germain
slope too — the module `Engine/SophieGermainEpistemic.lean`, entirely green. "Solving the conjecture from inside"
would mean self-grounding the manifestation law: the bundle `InternalisedSGGround` holds three fields at once — the
law itself, a witness of the absence of pairs no higher than one's own horizon (the same `SGAbsenceAbove`), and the
reconciled books at that scale — that is, bookkeeping with no free energy (see the [glossary](GLOSSARY.md)).

None of the three is greenly inhabited; yet together they present a perpetual engine —
by a genuine construction, not ex falso, that is, not by "from falsehood, anything"
(`internalisedSGGround_builds_engine`, inside which the front's
`sgRefutation_carries_engine` does the work), — and what is built perishes against the lexRank wall
`no_someConcreteEuclideanEngine`.

Hence **the manifestation law cannot be self-grounded** — "cannot be known from inside" is, for Sophie
Germain too, a theorem and not a slogan.

**Theorem 45.7** (`no_internalisedSGGround`, `sgCause_unknowable`, 🟢). *At no scale `(A, M0)` is internal
self-grounding attainable: `InternalisedSGGround(A, M0) → False`, equivalently
`¬ InternalKnowledgeOfSGCause(A, M0)`. (The statement is not about the SG pairs themselves but about the
cost of an internal solution: the assembled bundle builds an engine-witness `SomeConcreteEuclideanEngine`
and perishes against the lexRank wall `no_someConcreteEuclideanEngine`.)*

The second internal path — to refute — costs the same. The summary `sg_no_internal_decision_without_engine`
(🟢) lays out the fork: refutation from inside — an absence witness under the law on reconciled books —
builds an engine; self-grounding self-destructs; only an external boundary would decide, but §17 did not issue one,
and it enters the conjuncts only as a hypothesis.

We state the caveat at once: **"refutation = engine" for Sophie
Germain is conditional on the law** — weaker than the unconditional Collatz tail, and we do not hide this.

The tally is assembled
in `sg_locked_behind_engine_status` (🟢) — as with Polignac, without the decree conjunct; and the restricted mirror
3 (mod 4) repeats the same epistemics for the pearl's subfamily (`InternalisedSGThreeMod4Ground`,
`sgThreeMod4Cause_unknowable`, 🟢) and in the summary `sgThreeMod4_locked_behind_engine_status` carries an
anti-Mersenne conjunct — doubly conditional, on the boundary-hypothesis and on the restricted law.

And the pearl does not cross this horizon. `23 ∣ M_11` and the entire Euler–Lagrange route
(`sophieGermain_divides_mersenne`, `mersenne_composite_examples`, 🟢) are proven unconditionally — without the law,
without the boundary, without the epistemic bundles. The horizon locks up internal solutions of an *open*
question; over a classical theorem, solved here by the machine down to the last step, it holds no sway.

> **Note (what we do NOT claim).** This is NOT a solution of Sophie Germain's conjecture — it remains open,
> 🔴 — and NOT Gödel: no independence, no fixed point, only the green incompatibility of three
> individually-unknown fields against the wall of well-foundedness; all the epistemics is model-internal. The grade
> is below the P/NP benchmark: there one field is greenly inhabited, here — none; the bundle is paid for by two genuine
> green facts — the construction of the engine-witness and the lexRank killer. The substantive form without
> explosion is the dichotomy below; we assert only the left disjunct. The quarantine is not imported by the
> module; the repository's taint does not change.

**Theorem 45.8** (`unknowable_or_sg_unbounded`, 🟢). *At any scale `(A, M0)` one has
`(¬ InternalKnowledgeOfSGCause(A, M0)) ∨ SophieGermainUnbounded`. The statement carries no ex falso; the
left disjunct is a theorem (Theorem 45.7), the right is an open conjecture, not asserted here.*

## Place in the greater arc

For the first time in the whole addition a substantive classical theorem has entered the series — Euler–Lagrange,
`sophieGermain_divides_mersenne` — and it entered green and unconditional: it is proven in full, with no hypotheses and
no boundaries, together with the honest exclusion of the exponent `p = 3`.

Everything else around it stayed at the previous standard: the manifestation front is an exact mirror of
Mersenne, the boundary field is not taken (this time with a positive sign of the heuristic), and the bridge to composite
Mersenne numbers is assembled only conditionally, on the open Sophie Germain conjecture.

That conjecture itself — the infinitude of her primes — was open and remains open; neither it nor the Mersenne
problem is declared solved. The pearl is green; the question it serves is still waiting. Exactly
as it should be for a programme whose storefront is honesty.

<!--navbot-->

---

[← 44. Sides and Polignac](44_SidesAndPolignac.md) · [Table of contents](00_Overview.md) · [46. Goldbach and Legendre →](46_GoldbachLegendre.md)
<!--/navbot-->
