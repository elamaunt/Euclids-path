# Perfect numbers: green Euclid–Euler and the odd witness

<!--navtop-->
[← 46. Goldbach and Legendre](46_GoldbachLegendre.md) · [Table of contents](00_Overview.md) · [48. Fermat numbers →](48_Fermat.md)
<!--/navtop-->


> Lean source: `Engine/PerfectNumberBranch.lean` — the green Euclid–Euler branch, all 🟢
> (both directions re-exported from the mathlib Archive: `Theorems100`, author Aaron Anderson, Apache 2.0);
> `Engine/OddPerfectManifestationFront.lean` — the manifestation front of the odd side, axiom-free, all 🟢.
> Prose context: [34. The Mersenne branch](34_MersenneBranch.md),
> [43. Mersenne through the first cause](43_MersenneFirstCause.md), [42. Hodge](42_Hodge.md). Status legend:
> 🟢 — proven under the standard axioms; 🟡 — conditional on the axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

Chapter [34](34_MersenneBranch.md) ended with the Euclid–Euler theorem as a promise: Mersenne primes and even
perfect numbers are one object seen from two sides, and the bridge between them stretches from Euclid to
Euler across the whole history of number theory. Back then we stated this in the words of prose; in the
repository, meanwhile, `MersennePrimesInfinite` stood as a named 🔴 input, and perfectness itself was neither
defined nor decided by the machine.

Chapter [43](43_MersenneFirstCause.md) added to the thread a coil about the stakes, but it too left perfect
numbers waiting: "they waited two thousand years for Euclid — they will wait for the solution as well."

This chapter closes what can be closed — and does not pass off as closed what is open. Both sides of the
Euclid–Euler theorem are now **green in the repository**, machine-checked, by re-export from mathlib. A
green equivalence has appeared that ties the oldest open question of the *Elements* to exactly the question
of Mersenne primes.

And an odd front has appeared — the very same manifestation engine ("a deviation must show itself", see the [glossary](GLOSSARY.md)), but with the deviation
on the other side of arithmetic than Mersenne's. No open problem is thereby declared
solved; the news is about *what exactly* has become machine-checkable, and *where* the geometry draws the
boundary of the open.

## Green Euclid, green Euler

Let us begin with what has ceased to be prose alone. Both halves of the most ancient theorem now stand in
the branch as proven, re-exported from the mathlib archive — and we say so honestly: the work of Aaron
Anderson on Wiedijk's hundred theorems, Apache 2.0 license. Our contribution here is not the proof but the
*embedding into the programme's language*: the linking with the Mersenne centres of [34](34_MersenneBranch.md) and with the manifestation
architecture of Riemann.

**Theorem 47.1** (`perfect_of_mersennePrime'`, 🟢). *For `2 ≤ p` with `mersenne p` prime, the number
`2^(p−1) · mersenne p` is perfect — Euclid's direction, Elements IX.36.*

**Why this is true.** This is exactly the construction Euclid wrote down twenty-three hundred years ago:
if `2^p − 1` is prime, the sum of the proper divisors of `2^(p−1)·(2^p−1)` equals the number itself, exactly.
We do not rewrite Euclid's geometry of sums — we take its machine-checked form from the archive and
translate it into the p-language of the Mersenne branch, where `2^p − 1 = 6m_p + 1` is the upper side of the centre.

**Theorem 47.2** (`evenPerfect_eq`, 🟢). *Every even perfect number has the form `2^k · (2^(k+1) − 1)`
with a prime Mersenne factor — Euler's direction.*

**Why this is true.** Euler closed the converse two thousand years later: even perfectness has no form
other than Euclid's. Hence it follows that Mersenne primes and even perfect numbers are one
object: every Mersenne prime builds a perfect number (Euclid), and every even perfect number arises
from exactly a Mersenne prime (Euler). Machine-wise these are two arrows, `perfect_of_mersennePrime'` and
`evenPerfect_eq`, and together they are the entire classical theorem, green, without a single `sorry`.

> **Note.** What is green here — and what is not. Green are *both sides of the Euclid–Euler theorem* and
> the pointwise decidability of perfectness: `instance DecidablePred Nat.Perfect`, and with it the
> machine-checked `perfect_6`, `perfect_28`. That even perfect numbers (equivalently, Mersenne primes)
> are infinitely many is *not* asserted: the marker `NoMersenneInfinitudeClaimed` stands as a document
> that this question remains open. We have closed the classical *theorem*, not the ancient *problem of
> infinitude*.

## The equivalence that tied the Elements to Mersenne

Now for the theorem for whose sake the branch exists as a bridge. The *Elements* posed a question that has
gone unanswered for two thousand years: do the perfect numbers continue without end? Through Euclid–Euler
this question about *even* perfect numbers turns out to be the very same as the question about Mersenne primes — and
now this is not the rhetoric of prose but a green theorem.

**Theorem 47.3** (`mersennePrimesInfinite_iff_evenPerfectUnbounded`, 🟢). *The goal marker
`MersennePrimesInfinite` is equivalent to the unboundedness of even perfect numbers
(`EvenPerfectUnbounded`).*

**Why this is true.** Forward — through Euclid's construction and a growth estimate. From a Mersenne prime
`mersenne p` we build the perfect number `2^(p−1)·mersenne p` (the same Theorem 47.1, `perfect_of_mersennePrime'`), and the
inequality `N < p < 2^p ≤ 2^(p−1)·mersenne p` drives the perfect numbers upward without a ceiling: each new
Mersenne prime yields a perfect number strictly larger than any threshold fixed in advance.

Backward — through Euler's classification plus Fermat's arithmetic. An unbounded even perfect number is
dissected by Theorem 47.2 (`evenPerfect_eq`) into the form `2^k·(2^(k+1)−1)`, and the primality of the Mersenne number `2^(k+1) − 1`
forces a prime exponent — this is `Nat.prime_of_pow_sub_one_prime` (a composite exponent would yield an
algebraic divisor). The estimate `2^k·mersenne(k+1) < 2^(2k+1)` shows that a growing
perfect number pulls a growing prime exponent behind it.

**Conclusion.** Two open problems have turned out to be literally one, and this sameness is machine-verified.

It is worth pausing on what exactly is green here. Not the infinitude — both sides of the `↔` are open and
will remain open. Green is the **equivalence** itself: it is proven that the oldest question of the *Elements* and the
question of Mersenne primes are not two kindred questions but one and the same, down to the last comma.

This is precisely the programme's honesty. We have not moved the boundary of knowledge by a single step — we
have shown that on both sides of that boundary stands one and the same unknown.

## The odd front: the witness-object and the side where the deviation lives

The even side, as we have just seen, has an engine in the literal sense: `perfect_of_mersennePrime'`
*builds* a perfect number out of a Mersenne prime. The deviation — if there is one — cannot live here:
the even side is green-constructive and locked by Euler into Euclid's form. So if the perfect
numbers do have an unknown inhabitant, it is *odd*. The geometry knows which side is closed.

The odd witness is built not like the Mersenne boundary (a Π-statement of absence) but like Riemann's
deviation — an **object-datum**: a concrete odd perfect number.

**Definition 47.4** (`OddPerfectNumber`). *The type of witnesses of the open problem: the subtype
`{N // Odd N ∧ Nat.Perfect N}` — an odd number together with proofs of both properties.* The hypothesis
"there are no odd perfect numbers" (`NoOddPerfect`) is exactly the emptiness of this type
(`noOddPerfect_iff_no_witness` 🟢).

The strength of unpresentability — that property of a witness whereby presenting it would cost a perpetual engine (see the [glossary](GLOSSARY.md)) — is here the strongest possible: **pointwise decidability**. Perfectness
is decidable, so every *fake* dies by computation:

**Theorem 47.5** (`not_perfect_945`, 🟢). *`945` — the smallest odd abundant number — is not perfect
(machine check `decide`).*

**Why this is true.** The sum of the proper divisors of `945` is computable; the machine computes and compares it —
and `945` fails. Any presented candidate for an odd perfect number is checked by the same
`decide`; a fake will not survive the computation. We also know a lower bound of the true witness's domain:

**Theorem 47.6** (`oddPerfect_ge_101`, 🟢). *Every odd perfect witness is ≥ 101 — all smaller
odd candidates are screened out by machine check.*

**Why this is true.** For each odd `M < 101`, decidability delivers the verdict `¬ Nat.Perfect M`
by a single `decide`; the witness cannot sit below 101.

Here lies the whole truth about the bounds. It is known in the literature that an odd perfect number, if
it exists, exceeds `10^2200`; but that bound is *not formalized* — green with us is only `≥ 101`. We do not
smuggle someone else's result in under our own name: to present a genuine witness would be to solve a
problem open since antiquity, and the pointwise checking of small cases is no substitute for such a solution.

On the odd front the manifestation law is arranged slightly differently than for Mersenne, and the difference
is fundamental. For Mersenne the law had to be *gated by an absence witness* — otherwise at `P = 0` it
would have exploded. Here the witness is the object itself, and the scale anchor is tied to the number itself: the law is
**object-quantified** (`∀ W, OddPerfectManifests W`), the height of the deviation is the deviation itself, and
an ungated explosive form simply does not exist. This is the mirror of Riemann, not of Mersenne.

**Theorem 47.7** (`oddPerfectWitness_carries_engine`, 🟢 — readable form). *A concrete odd
perfect number + the manifestation law + reconciled books at a scale no lower than the number itself
present a perpetual engine — as an object,* `ConcreteEuclideanEngineWitness`, *before any killing.*

**Theorem 47.8** (`noOddPerfect_of_manifestation_and_boundary`, 🟢 — essence). *No engines + an accepted
boundary + the manifestation law ⟹ there are no odd perfect numbers.*

**Why this is true.** The mirror of the Riemann and Mersenne essence lemmas, with the same standard of honesty.
A hypothetical witness `W` yields the scale `M0 := W.1`. The resolving projection turns the universe into an
energy-free stable one — this is exactly "the books are reconciled" (see the [glossary](GLOSSARY.md)) — and the law supplies an infinite family of flows — not ex falso (that is, not by a gratuitous "from falsehood, anything") but as
data. Out of the collision on a finite key an engine-witness is assembled, and what kills the assembled
engine is precisely the hypothesis "there are no engines."

All three hypotheses are genuinely consumed; none is decorative.

> **Note.** The contrast is disclosed machine-wise (`evenSide_constructible` 🟢): the even side is greenly
> *built* from Mersenne primes, so the front's deviation lives strictly on the odd side — there,
> where in two and a half thousand years nothing has been built. And the sign of the heuristic here points *toward*
> absence: the law's quantifier ranges over an expectedly empty type, the law is expectedly vacuously true — an exact
> mirror of RH, not Mersenne's inverted sign.
>
> The converse side of the law is vacuous, and this is exposed by audit. Under the boundary, law ⟺ `NoOddPerfect` — a field
> would be exactly as strong as the oldest open problem — and yet the field is not added, deliberately: the law lives
> as a definition (the precedent of [43](43_MersenneFirstCause.md)/§16); serial expansion of the decree would cheapen
> the quarantine.
>
> There is not a single free Prop field, free gate, or renamed conclusion in the module;
> there are no axioms and no `sorry`.

## Philosophical digression

Perfect numbers are the oldest object of number theory, older than the primes themselves as a subject of study.
Euclid wrote down their construction in IX.36 of the *Elements*; Nicomachus of Gerasa surrounded them with
number mysticism, ranking them by magnitude as a virtue between excess and deficiency; and since then humanity waited
two thousand years for Euler, to learn that Euclid's form is the only one possible for the even ones. No
object of mathematics has carried so simple an unsolved riddle for so long.

That riddle is about *balance*. A perfect number is defined by the condition `σ(N) = 2N`: the sum of all
divisors is exactly twice the number itself, that is, the sum of the proper divisors equals it exactly. This is
a conservation condition — a number in ideal equilibrium with its own parts, `6 = 1 + 2 + 3`,
`28 = 1 + 2 + 4 + 7 + 14`.

In the charge reading of [42](42_Hodge.md) we read a Hodge class as a quantized magnitude, and an
algebraic cycle as its payment. Here `σ(N) = 2N` is the condition of *charge conservation* of the number
itself: the divisors must, in sum, pay the doubled number exactly, with no surplus and no shortfall.
The abundant `945` overpays; deficient numbers fall short; a perfect one is in exact balance.

And the deviation — an odd perfect number, if it exists — would be an unpaid charge on the odd
side, a rupture in the vacuum, which the manifestation law turns into a perpetual engine. Exactly
the same motif that carries the programme's entire causal line: an imbalance that cannot exist where the
books are reconciled.

And there is a special fittingness in the fact that this particular riddle fell to an engine named after
Euclid. The even corner of his oldest theorem is now green in full — the construction and its uniqueness.
What remains open is one odd corner: does an odd perfect number exist?

This is the last
unclosed corner of Euclid's oldest theorem, and the geometry of the front tells us more about it than we can
prove: the even side is constructive and locked, the deviation can live only as an odd number, and every
forgery dies by computation. We know where to look, we know what it would amount to — and we do not know
whether anyone is there. The perfect numbers are still waiting; but now it is visible at exactly which door.

## Perfect numbers beyond the same horizon

And this door has an epistemic blueprint. The wall from [39](39_PNPRankPayment.md) and
[56](56_CollatzFirstCause.md) — the one against which the internal solutions of P/NP and Collatz shatter —
has turned out to have a third slope, and it falls here, into the odd front: `Engine/OddPerfectEpistemic.lean`,
an entirely green module, says two things.

First: **to present an odd witness is to
present a perpetual engine**, and therefore the witness is greenly unpresentable.

**Theorem 47.9** (`oddPerfectWitness_green_unpresentable`, 🟢 — conditional). *Under the accepted
`step00`-obligation boundary and the manifestation law the type of odd perfect witnesses is empty:*
$\text{TheStrictLastStep00Obligation} \to \text{OddPerfectManifestationLaw} \to \neg\,\text{Nonempty}\,\text{OddPerfectNumber}.$

The conditionality here is named as conditionality: both hypotheses are
explicit — the manifestation law lives as a definition (the field is not decreed), the boundary is supplied from outside;
a presented witness, under the law and with the books reconciled, would build an engine
(Theorem 47.7, `oddPerfectWitness_carries_engine`), and greenly there are no engines (`no_someConcreteEuclideanEngine`).
This front has no unconditional form and cannot have one — it would be a solution of the problem itself.

Second: self-grounding self-destructs. The structure `InternalisedOddPerfectGround` carries a witness
*inside* its own verified horizon — and a machine unfolding of that very horizon,
the kernel fact `oddPerfect_horizon_swept` 🟢, exactly the inside of the proof of `oddPerfect_ge_101`.

From this pair `False` is derived — **self-grounding is exactly ⊥** (`no_internalisedOddPerfectGround` 🟢):

**Theorem 47.10** (`oddPerfectCause_unknowable`, 🟢). *Internal knowledge of the cause for odd perfect
numbers is impossible:* $\neg\,\text{InternalKnowledgeOfOddPerfectCause}$ — *equivalently,*
$\text{InternalisedOddPerfectGround} \to \bot$ *(the structure carrying a witness inside its own verified
horizon is contradictory).*

"It cannot be known from inside" is not a slogan but a theorem, the mirror of
`collatzCause_unknowable` and `pnpCause_unknowable`. The structure's legs are not logical complements of each
other: the contradiction is mined by genuine mediation, by unpacking the witness and translating oddness into
the language of residues, and the kernel payment of the horizon enters the refutation itself.

And what remains when both internal paths are locked? Exactly what there was: **the green lower bar
remains `oddPerfect_ge_101`** — the witness, if it exists, is not below 101, and
`no_oddPerfectWitness_below_horizon` 🟢 closes the basement unconditionally.

The summary
`oddPerfect_verification_not_derivation` 🟢 adds a punchline unique to this front: "external
verification" here is literally the pointwise decidability of perfectness — every candidate is settled by
computation, and the solution is findable exactly as far as the kernel can count. The final status
is gathered in `oddPerfect_locked_behind_engine_status` 🟢: the witness is ≥ 101 — a theorem; internal knowledge is
impossible — a theorem; everything else is conditional, with the hypotheses left in plain view.

> **Note (what we do not claim).** This is not a solution of mathematics' oldest open problem and NOT
> Gödel: no independence and no fixed point — only computational screening and the wall of the
> perpetual engine; the whole construction is model-internal epistemics, and what it asserts is the impossibility
> of *self-grounding*, not the (non)existence of an odd perfect number.
>
> The third conjunct
> `oddPerfect_verification_not_derivation` is classically trivial — its machine content lies in the route
> through the deciding instance, not in the strength of the statement. The module does not import the quarantine and adds neither
> axioms nor `sorry`; the repository's taint does not change.

## Euler's form: the anatomy of a nonexistent witness

Until now the odd witness has been for us an object-riddle: a type that may be empty, or may not
be, with the green lower bar `≥ 101` and the wall of the perpetual engine around it. But this hypothetical
inhabitant has something the Mersenne absence witness did not have — a **machine-verified
anatomy**. Euler's classical theorem on odd perfect numbers is now green in full, in
`Engine/OddPerfectEulerForm.lean`.

**Theorem 47.11** (`odd_perfect_euler_form`, 🟢). *Every odd perfect `n` has the form `n = q^α · m²`,
where `q` is prime, `q ≡ 1 (mod 4)`, `α ≡ 1 (mod 4)`, and `q ∤ m`.* In the witness language the same form is
`oddPerfect_euler_form`: every `W : OddPerfectNumber` is obliged to carry exactly this structure.

**Why this is true.** Everything rests on one observation about the arithmetic of `σ(n) = 2n`. For odd `n`,
the two enters the right-hand side in exactly the first power, and σ, being multiplicative, factors along the
factorization: `σ(n) = ∏_p σ(p^{a_p})`. For an odd prime `p`, the sum `σ(p^a) = 1 + p + … + p^a`
consists of `a + 1` odd summands — it is even if and only if `a` is odd. So the
two in `σ(n)` is contributed by an exponent: it is forced to be odd for exactly *one* prime divisor.

A ladder of four steps takes this apart bone by bone: `exists_unique_odd_exponent` (exactly one
odd exponent — zero of them would give an odd `σ(n)`, two would give `4 ∣ 2n` against the oddness of `n`),
`special_prime_one_mod_four` (this special `q` is congruent to `1` modulo `4`), `exponent_one_mod_four`
(its exponent `α ≡ 1 (mod 4)`), and the packing of all the remaining, even, exponents into a square `m²`.

Let us dwell on the residues, for they are the very heart. Why `q ≡ 1 (mod 4)`? Were `q ≡ 3
(mod 4)`, the signless pairing `σ(q^α) = (1 + q)·∑(q²)^j` would give `4 ∣ σ(q^α)` (since `4 ∣ 1 + q`),
and this drives `4 ∣ 2n` — again against oddness. What remains is `q ≡ 1 (mod 4)`, and then `σ(q^α) ≡ α + 1
(mod 4)` pins down the exponent as well: `α ≡ 1 (mod 4)`. Mod-4 arithmetic fixes both the prime and its
power — by two short computations.

Here is what is new for the arc. The witness that must not be presented has acquired a machine-verified
portrait. Every future hunter of the odd perfect number now knows the exact shape of the prey:
not "some odd number" but `q^α·m²` with `q ≡ α ≡ 1 (mod 4)`.

And adjoining this portrait are two more
green domain restrictions (`Engine/OddPerfectThreePrimes.lean`): *no prime power is
perfect* — neither odd nor even (`not_perfect_prime_pow`: `σ(p^k) ≡ 1 (mod p)`, whereas
`2·p^k ≡ 0`, whence `p ∣ 1`), and every odd perfect number has *at least three distinct prime
divisors* (`odd_perfect_three_le_card_primeFactors`, in the witness language `oddPerfect_min_three_prime_factors`
— via the abundance estimate `2·∏(p−1) ≤ ∏p`).

**Section takeaway.** Three qualitative hoops — `≥ 101`, `≥ 3` primes, the form
`q^α·m²` — tighten the domain of the nonexistent witness from three sides at once.

> **Note (honesty of the form).** This is not a solution of the problem and NOT Gödel: neither the existence nor the
> nonexistence of an odd perfect number is asserted here. All the module's theorems are
> unconditional arithmetic, paid for by mathlib's multiplicativity of σ₁ and mod-2/mod-4 counting; there are no anchors and
> no boundaries in it. We have proven not that the witness exists, but *what form* it is obliged to have if
> it does — an eighteenth-century classic, embedded into the programme's language for the first time. Taint 47 does not change.

## Place in the greater arc

The thread opened by the closing line of [34](34_MersenneBranch.md) and continued by the stakes-honesty of [43](43_MersenneFirstCause.md) has received a
machine-verified body.

Both sides of Euclid–Euler are green by re-export; the ancient question of the *Elements* about the
infinitude of even perfect numbers is proven equivalent to the question of Mersenne primes
(`mersennePrimesInfinite_iff_evenPerfectUnbounded`); and the odd side has been run through
Riemann's manifestation architecture — with an object-deviation, pointwise decidability of forgeries, and
a disclosed contrast: the even corner is closed, the deviation lives on the odd one.

And exactly what this chapter did *not* do is its chief honesty. The infinitude of Mersenne primes (and
hence of even perfect numbers) is not asserted — both sides of the green equivalence are open.

The
existence of an odd perfect number is not settled — green is only `≥ 101`, and the literature's bound
`> 10^2200` is not formalized. The manifestation field of the odd side, like Mersenne's, is admissible
by the machine criterion but not taken — by the same verdict against serial decreeing.
`twin_prime_conjecture` remains `sorry`; the quarantine's taint is not moved; not a single open problem is
declared solved.

What is closed — machine-checked and with open eyes — is only the classical theorem that was a theorem already for
Euclid and Euler. The riddle of their perfect numbers waits on, now at one clearly indicated odd
door.

<!--navbot-->

---

[← 46. Goldbach and Legendre](46_GoldbachLegendre.md) · [Table of contents](00_Overview.md) · [48. Fermat numbers →](48_Fermat.md)
<!--/navbot-->
