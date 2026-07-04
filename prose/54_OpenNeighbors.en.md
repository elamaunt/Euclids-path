# 54. Neighbours beyond the horizon: shadows of open problems

<!--navtop-->
[← 53. Birch–Swinnerton-Dyer](53_BirchSwinnertonDyer.md) · [Table of contents](00_Overview.md) · [55. Collatz →](55_Collatz.md)
<!--/navtop-->

> Lean sources: `Engine/ChowlaFront.lean`, `Engine/AbcFront.lean`, `Engine/BealFront.lean`,
> `Engine/LehmerFront.lean`, `Engine/LandauFront.lean`. Each shadow is grounded on a **real proven
> mathlib theorem** (🟢), while the open conjecture itself remains an honest named 🔴 gate. None of
> them is solved; the quarantine toll does not change (47), and there is still exactly one `sorry`.
> The novelty is formalizational.

## Where we are

Eight masks have exhausted the millennium problems. But the perpetual-engine prohibition — descent,
height, rank parity — lives on in neighbouring open problems as well. Here we cast a shadow of five
of them with a single device: **a real mathlib anchor plus an honest gate**. The anchor is a proven
theorem (a polynomial analogue, a finiteness, a structure) which is itself the reading through the
engine; the gate is the open conjecture itself, named and not proven.

## Chowla and Sarnak: the same rank-parity node

The Liouville function `λ(n) = (−1)^Ω(n)` is precisely our rank-parity invariant, the one standing
behind Riemann. Chowla's conjecture says: the parity of `Ω` does not correlate across shifts,
`∑_{n≤x} λ(n)λ(n+h) = o(x)`. It is the same prohibition on parity collapsing into a single parity
class that guards both the twins and Riemann.

**Theorem 54.1** (`chowlaCorrelation_zero_eq_card`, 🟢). *The diagonal `h=0` yields perfect
self-correlation: `∑_{n≤x} λ(n)² = x`.*

"Why this is true." `λ(n)² = 1` for `n≥1` (`λ` takes values `±1`), so the diagonal degenerates into
a count. This stands in sharp contrast to what Chowla forbids at `h>0`: there the sum is obliged to
cancel. The sign flip under multiplication by a prime (`chowla_parity_flip`, a reuse of
`RiemannLiouville`) is the same descent move.

**Gate** (`ChowlaConjecture`, `SarnakConjecture`, 🔴). *The `o(x)` correlations and Möbius
orthogonality are open.* Tao proved only the logarithmically averaged and the odd cases; the full
statement — no.

> **Note.** This node also has an epistemic slope (`Engine/ChowlaEpistemic.lean`): a perfect parity
> collapse — a tail on which the Liouville sign is constant — is **impossible**, because doubling
> the argument flips the sign, and the constant perishes against that same flip wall
> (`no_parityCollapse_of_flip`). Hence the node is unknowable from inside (`chowlaCause_unknowable`),
> and the correlation itself is moreover pointwise rigid: on the odd slice it is never zero
> (`chowlaCorrelation_ne_zero_of_odd`), whereas both Liouville signs are attained cofinally
> (`liouville_two_pow`). We are honest about the coverage: the bundle covers only the collapse mode;
> there is no engine fact for Chowla in the repository — and the summary is named accordingly,
> `chowla_locked_behind_flip_wall`, without the word "engine". This is NOT a solution of Chowla and
> NOT Gödel; the red gates stay red.

## abc: the polynomial analogue is proven

The abc conjecture: for coprime `a+b=c` the number `c` is bounded by the radical,
`c < K_ε·rad(abc)^{1+ε}`. The polynomial analogue — the Mason–Stothers theorem — is **proven**, and
it is in mathlib.

**Theorem 54.2** (`polynomial_abc_shadow` = `Polynomial.abc`, 🟢). *For coprime polynomials `a+b+c=0`
over a field, the degree is bounded by the radical of the product (or else all the derivatives are
zero).*

"Why this is true." This is a ready-made mathlib theorem (the Wronskian plus coprimality). The
degree bound through the radical is exactly the engine reading: the quality of a triple cannot run
off to infinity — it is finite. The radical of an integer (`Int.radical`, `Nat.radical`) is real
too, not a stub.

**Gate** (`AbcConjecture`, 🔴). *The integral abc is open.* Mochizuki's claim (IUT) has not been
accepted by the community; the prize is unclaimed.

> **Note.** The epistemics (`Engine/AbcEpistemic.lean`) we build only around the **naive form
> `ε = 0`**, and this is important to spell out. The naive law is refuted by a single witness
> (`abc_exponent_one_counterexample`: `1 + 8 = 9`, `rad(72) = 6 < 9`), and the quality supply at
> `ε = 0` is unbounded — the LTE family `3^(2^k)` breaks through any linear horizon
> (`unboundedQualitySupplyExponentOne`). Hence there is no linear grounding from inside
> (`abcCause_unknowable`); along the way a radical toolkit grew on top of mathlib — `natRad_pow`,
> `natRad_mul_of_coprime`. The genuine abc gate (`ε > 0`) is **untouched** by all this: there such a
> supply does not exist and is under no obligation to, and all the openness lives in the `ε` slack.

## Beal and Fermat–Catalan: pure Fermat descent

Fermat's method of infinite descent is literally our engine. And its polynomial form is proven.

**Theorem 54.3** (`polynomial_fermat_catalan_shadow` = `Polynomial.flt_catalan`, 🟢). *When
`1/p+1/q+1/r<1`, the equation `u·aᵖ+v·bᵍ+w·cʳ=0` for coprime polynomials forces `a,b,c` to be
constants.*

"Why this is true." A ready-made mathlib theorem, whose proof is infinite descent on the
characteristic `p`. Nearby stand `fermatLastTheoremFour`/`Three` (`flt_four_is_descent`), proven by
the same descent; we honestly exhibit them and derive engine-free descent through
`EPMI`/`UniversalEngine`.

**Gate** (`BealConjecture`, `FermatCatalanConjecture`, 🔴). *The integral Beal (`Aˣ+Bʸ=Cᶻ`,
`x,y,z>2`, coprime ⟹ a common divisor) and the full Fermat–Catalan are open.* Darmon–Granville
proved finiteness only for fixed exponents (via Faltings); the $1M prize is unclaimed.

> **Note.** With this wave the front got repaired in several places. The Fermat–Catalan gate itself
> we rewrote in terms of **value triples**, and the previous tuple form was green-refuted
> (`fermatCatalan_tupleForm_refuted`: `1^m + 2^3 = 3^2` yields infinitely many tuples for the single
> triple `(1,8,9)`) — an honest formalization lesson. The diagonal exponent classes are closed via
> Fermat descent: at `(3,3,3)` and `(4,4,4)` there are no solutions at all
> (`beal_no_solution_exponent_three`, `beal_no_solution_exponent_four`), and the "Beal theorem over
> `k[X]`" is exhibited as `polynomial_beal_shadow`. The set is inhabited
> (`fermatCatalan_value_witness`), and the coprimality hypothesis is load-bearing
> (`beal_common_factor_witness`: `2^3 + 2^3 = 2^4`). The epistemic bundle `bealCause_unknowable` is
> honestly **formal** — a ground/¬ground pair with no engine payment; the substantive material lives
> next to it, in separate theorems, not inside it.

## Lehmer: height-finiteness as in BSD

The Mahler measure is a height, and the same Northcott that computed the rank in BSD works here.

**Theorem 54.4** (`mahler_northcott_shadow` = `finite_mahlerMeasure_le`, 🟢). *There are only finitely
many polynomials of bounded degree and bounded Mahler measure.*

"Why this is true." This is Northcott (a ready-made mathlib theorem): the height is well-founded,
there is no infinite height descent — the very core behind BSD and the universal engine. The lower
boundary is given by Kronecker (`kronecker_boundary`): the Mahler measure equals 1 if and only if
the roots are roots of unity (the cyclotomic case).

**Gate** (`LehmerConjecture`, 🔴). *A uniform gap `c>1` above one for the non-cyclotomic case is
open.* The smallest known value is Lehmer's number ≈ 1.17628; Kronecker closes only the boundary
`M=1`.

> **Note.** For this finiteness we also read the epistemic slope (`Engine/LehmerEpistemic.lean`):
> the Northcott box is green-finite (`mahlerBox_finite`), and therefore a genuinely infinite family
> of polynomials cannot be held under one such horizon from inside — an injection of the infinite
> into the finite perishes against the same pigeonhole wall of the perpetual engine, and here
> "cannot be known from inside" is a theorem, not a slogan (`lehmerCause_unknowable`). This is
> model-internal epistemics, not Gödel and not a solution: nothing is asserted about the gap `c>1`
> itself, the gate stays red, and there is no decree here and never was — the module is green
> throughout. **Without an engine only external verification remains**: on each finite degree
> horizon the gap is found by enumerating the Northcott catalogue (`lehmer_at_bounded_degree`); what
> remains open is only the degree escaping past every horizon.

> **Note (the green/red boundary is drawn by machine).** The module `Engine/LehmerBoundedDegree.lean`
> fixes this boundary exactly. Lehmer **at bounded degree** is already a green theorem: for each
> degree `n` there exists a `c > 1` with no Mahler measures in the interval `(1, c)`
> (`lehmer_at_bounded_degree`). The proof is folklore — the window `(1, 2]` is finite by Northcott,
> a finite set has a minimum, and below it there are no measures. But the constant `c = c(n)`
> **depends on the degree**: a single `c` for all degrees at once (`UniformLehmerGap`, 🔴) is the
> Lehmer conjecture itself. The renaming audit exposes this with machine precision:
> `uniformLehmerGap_iff_all_degrees` proves that the anchor is equivalent to "in
> `lehmer_gap_at_bounded_degree` one may take one constant for all degrees" — that is, the red input
> is exactly the uniform version of the green theorem, and its name smuggles in no progress
> whatsoever.

## Landau: primes n²+1

Dirichlet (in mathlib, for real) gives primes in arithmetic progressions — the "sides" `6m±1` stand
on it. But `n²+1` is not a progression, and its infinitude remains an honest gate.

**Theorem 54.5** (`landauPrimes_infinite_of_unbounded`, 🟢). *If the primes `n²+1` are unbounded, then
their set is infinite.* Plus `oddLandauPrime_even_k`: for odd `k` the number `k²+1` is even, so a
prime `k²+1 > 2` requires an even `k` — a genuine residue fact, not an ornament.

"Why this is true." A pure structural repackaging (as in the Polignac branch): unboundedness implies
infinitude. No new content whatsoever — the whole substance sits in the gate.

**Gate** (`Landau4thUnbounded`, 🔴). *The infinitude of primes `n²+1` (Hardy–Littlewood) is open.*
Iwaniec: infinitely many `n²+1` with at most two prime factors.

> **Note.** The epistemic layer (`Engine/LandauEpistemic.lean`) canonizes the gate: the
> unboundedness of primes `k²+1` is equivalent to the infinitude of the set
> (`landau4thUnbounded_iff_infinite`); the red input remains exactly one. The residue fact has
> ceased to be an ornament — the gate is localized on the even channel
> (`landauPrime_even_of_two_lt`), and the Landau primes themselves lie in the real Dirichlet class
> `1 mod 4`, which is infinite by mathlib (`landau_lives_in_dirichlet_class`); what is open is
> precisely the selection within the rank and file. Unlike Beal, here we **did build an engine
> fact** — `landauRefutation_carries_engine`: a refutation under the manifestation law exhibits a
> perpetual engine as an object. Honestly: the law (`LandauManifestationLaw`) is **not decreed** (a
> Polignac-class law, weaker than the unconditional walls), and `landauCause_unknowable` is neither
> a solution of the 4th problem nor Gödel.

## The common moral

Five shadows — one device: wherever people have a proven anchor (the polynomial abc and
Fermat–Catalan, Northcott and Kronecker, Dirichlet, the Liouville structure), we exhibit it in green
as a reading through the engine; wherever an open conjecture stands, we name it as an honest gate
and do not pretend to have closed it.

None of the five is solved, no first-cause decrees have been
added (just as in the arithmetic zoo), and the toll is the same 47.

As far as our searches go,
neither Chowla, nor abc, nor Beal, nor Lehmer, nor Landau has been read this way before; the novelty
is formalizational, not mathematical. One and the same prohibition is recognized beyond the horizon
of the eight masks as well.

<!--navbot-->

---

[← 53. Birch–Swinnerton-Dyer](53_BirchSwinnertonDyer.md) · [Table of contents](00_Overview.md) · [55. Collatz →](55_Collatz.md)
<!--/navbot-->
