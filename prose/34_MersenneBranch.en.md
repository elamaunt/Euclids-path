# 34. The Mersenne branch: an honest bridge and the price of the forward

<!--navtop-->
[← 33. First cause and the main theorem](33_CausalFirstCause.md) · [Table of contents](00_Overview.md) · [35. P/NP: the local node →](35_ClassicalPNP.md)
<!--/navtop-->



> Lean: `Engine/MersenneBranch.lean` (`mersenneCenter`, `mersenne_eq_sixCenter_add_one`,
> `isTwinCenter_mersenneCenter_iff`, `mersenne_twin_instances`, `twinLowersInfinite_of_mersenneTwins`,
> `NoTwinsToMersenneImplicationClaimed`), `Engine/MersennePaymentConflict.lean` (the payment route,
> `twinLowersInfinite_of_primePaymentRoute`, `pressure_iff_supply_for_everythingPrimeLedger`),
> `Engine/MersennePeelPressure.lean` (peel/debt splittings, `twinLowersInfinite_of_peelPaymentRoute`,
> `twinLowersInfinite_of_debtRoute`, `canonical_coverage_iff`), `Engine/MersenneForwardFront.lean`
> (the forward series of 34 bricks — ⚠️ vacuity No. 3, see below).
> The whole branch contains no `sorry` and no `axiom`; there are no AXIOM-TAINTED declarations
> either — the branch does not touch `step00FirstCause`. Everything green here is 🟢 under the
> standard axioms.

Mersenne primes are a standing temptation for the programme: numbers of the form $2^p-1$ look like
ready-made inhabitants of the $6m\pm 1$ language, and one is tempted to declare that the machine
chasing twins solves them "along the way". This chapter opens with a prohibition on that
temptation, continues with the little that is genuinely proven, and ends with the harshest episode
of machine honesty to date — vacuity No. 3
(vacuity is when a candidate law holds for free and the decree would be empty; see the [glossary](GLOSSARY.md)).

## An honest correction: twins do *not* give Mersenne

Let us fix at once what this branch does *not* claim.

> **Note.** The infinitude of Mersenne primes does not follow from the twin conjecture — neither
> trivially nor by any method known to mathematics. These are independent open problems: twins
> would give infinitely many twin centers, but say nothing about the exponentially rare Mersenne
> centers. The implication "twins ⟹ Mersenne" is **not recorded as a theorem** in the
> repository — and so that this cannot be quietly forgotten, `MersenneBranch.lean` carries an
> explicit coverage marker `NoTwinsToMersenneImplicationClaimed` (it is `True` — a document, not
> a result), while the goal marker `MersennePrimesInfinite` is declared and *derived from nowhere
> in the branch*. 🔴

The only trivial implication between the topics does exist — and it runs in the *opposite*
direction; we will reach it through the embedding.

## Embedding into the programme's language

The first genuine result: Mersenne lives on the plus side of the $6m+1$ grid. Define the Mersenne
center $m_p = (2^{p-1}-1)/3$ (for odd $p$ the division is exact). Then:

> 🟢 **`mersenne_eq_sixCenter_add_one`.** For odd $p$: $\;2^p - 1 = 6\,m_p + 1$.

That is, every odd Mersenne number is precisely the upper side of the center `mersenneCenter p`.
The lower side of the same center is $6m_p - 1 = 2^p - 3$, whence an immediate twin criterion:

> 🟢 **`isTwinCenter_mersenneCenter_iff`.** For odd $p \ge 2$ the center $m_p$ is a twin center
> $\iff$ both numbers $2^p-3$ and $2^p-1$ are prime.

Such "Mersenne twins" do exist: 🟢 **`mersenne_twin_instances`** verifies $p=3$ (center $1$,
pair $(5,7)$) and $p=5$ (center $5$, pair $(29,31)$). Further along $p$ the coincidences dry up
quickly — and nobody here promises that they will not dry up forever.

## The correct implication: Mersenne ⟹ twins

If there are infinitely many Mersenne twins (the input hypothesis `MersenneTwinCentersUnbounded` —
manifestly *stronger* than the ordinary twin conjecture), then the twin pairs $(2^p-3,\,2^p-1)$
are unbounded, and:

> 🟢 **`twinLowersInfinite_of_mersenneTwins`.** `MersenneTwinCentersUnbounded` ⟹
> `TwinLowers.Infinite`.

This is the only honest arrow between the topics: a subsequence of twins is still twins. The arrow
is trivial, points from the stronger to the weaker, and gives no new information about twins; its
value lies in the fact that all further routes of the branch are carried all the way to the
programme's genuine goal, not to a local surrogate.

## Payment routes: conflict, peel, debt

`MersennePaymentConflict.lean` transfers to Mersenne the bookkeeping of [17. Payment ledger](17_PaymentLedger.md)
(the ledger is the bookkeeping of paid flows; see the [glossary](GLOSSARY.md)). The centers are
written without division, as base-4 repunits $m_{k+1} = 4m_k + 1$ ($0,1,5,21,85,\dots$); the join
with the embedding is 🟢 `sixCenter_add_one_eq_mersenne` ($6c_k+1 = 2^{2k+1}-1$), and the
coincidence of the centers of all layers is 🟢 `peelCenter_eq_conflictCenter`, `coverageCenter_eq_conflictCenter`.

Over the abstract
ledger (`RawPrimePaymentLedger`: genealogies pay number-tokens) the entire assembly logic is
proven: a sound payment of both sides extracts a genuine Mersenne twin (🟢 `mersennePairPaid_extracts_twin`),
and the package `MersennePrimePaymentRoute` — ledger + `sound` + ordinary twin infinitude +
**cofinal pressure** `CofinalMersennePrimePaymentPressure` — yields 🟢
`infinite_mersenne_supply_of_primePaymentRoute` and then, across the bridge, 🟢
`twinLowersInfinite_of_primePaymentRoute`.

Under tail-absence of Mersenne twins a dichotomy of
defects is proven (🟢 `absence_forces_payment_cofinality_or_extraction_defect`): either the
cofinality of payments breaks, or the extraction — and the extraction cannot break under soundness.

`MersennePeelPressure.lean` splits the load-bearing input further. Layer 1: pressure = **coverage**
(`CofinalMersennePeelCoverage` — twins force genealogy hits into repunit centers) +
**payment law** (`PeelHitForcesPrimePayment` — a hit pays both sides $6m_k \mp 1$); the assembly is
🟢 `twinLowersInfinite_of_peelPaymentRoute`.

Layer 2: coverage = **debt pressure**
(`CofinalPeelDebtPressure` — unbounded peel-debt indices) + **realization**
(`PeelDebtRealizesHit`); the assembly is 🟢 `twinLowersInfinite_of_debtRoute`, and the full
trichotomy of defects under absence is 🟢 `absence_forces_debtCofinality_or_realization_or_payment_defect`.

## Canonical collapses as honesty

All this architecture is proven *conditionally on the load-bearing inputs*, and the branch itself
measures how much they weigh. For the canonical "pay every prime" ledger (`everythingPrimeLedger`,
whose soundness is definitional) it is proven:

> 🟢 **`pressure_iff_supply_for_everythingPrimeLedger`.** Pressure ⟺ the renamed **conclusion**
> (the infinitude of Mersenne twins).

Similarly for the canonical peel system `canonicalPeelSystem` ("hit = already a twin", the payment
law — 🟢 `canonical_paymentLaw` — definitional): 🟢 **`canonical_coverage_iff`** — coverage ⟺ the
same conclusion.

**Conclusion.** On an arbitrary ledger the inputs are empty: to assume pressure is to assume the
conclusion — the "goal renaming" familiar from the trilemmas (see the [glossary](GLOSSARY.md)).
The splittings have content only for a *genuine* Step00 ledger of genealogies, where the payments
are forced by the structure of the graph. No such ledger exists in the repository yet; all the
load-bearing inputs are 🔴.

## ⚠️ Vacuity No. 3: the forward series is uninhabited

`MersenneForwardFront.lean` — 34 bricks in a single assembly: peel-lift certificates and operators,
exact successor arithmetic, sparse routes and index-jump lift, debt firewalls, same-key pigeonhole,
resolver-payment decomposition, an admissible filter with a circularity audit, a side-payment
certificate, a semantic realizer, no-escape / full-closure / endgame and a bridge to twin-Step00.
The assembly audit exposed — and the module header records in full:

- **The noEngine packages are uninhabited.** In `LegacyStep00NoEscapeLayer` (four_defect),
  `TwinStep00NoEscapeLayer` / `AcceptedTwinStep00NoGoPackage` (twin_step00_bridge) and the whole
  family `NoForbiddenPrimePaymentEngine` (oversaturation / no_escape / full_closure_endgame) the
  field `noEngine` demands `Engine → False`, but the defect tokens (`Step00DefectToken` and its
  kin) carry a *free* field `witness : Prop` — the "forbidden engine" is built trivially
  (`witness := True`), the layer is internally contradictory, and the headline theorems
  (`produces_infinite_mersenne_twins` and its relatives, including `forbids_eventual_absence`) are
  **vacuous**: from an uninhabited premise anything follows. Routes in this form are
  uninstantiable.
- **`TwinStep00CausalClosureNode`** — a free gate (an arbitrary `Prop` plus its proof).
- **Renamed-conclusion inputs:** the fields `PrimePaymentSound` / `lower_sound`+`upper_sound` are
  the target conclusion repackaged as a "law"; `CofinalAdmissibleGenealogyHits` / `cofinal_filter`
  directly supply the cofinal admissible indices — exactly what the route was supposed to earn.
- **Free honesty gates:** `not_using_ordinary_twin_absence`, `cofinal_tail_scope`,
  `not_using_mersenne_twin_infinitude`, `not_using_classical_PNP`, `lower/upper_not_circular` —
  instantiated by `True`; one brick does exactly that itself.
- `tokenOfFinalDefect` has been rewritten (the original is untypeable) and does not pass through
  the four typed adapters; `twinTokenOfAbsence` — does.

**Audit verdict.** There are *no* unconditional strong conclusions in the series; `sorry`/`axiom` —
none. As in episodes No. 1 (twins) and No. 2 (Riemann), the emptiness was exposed machine-wise and
documented in the module itself, not painted over: the 34 bricks are a scaffolding of obligations,
not 34 results.

## The live front and its place in the greater arc

Repairing all three holes is one and the same job: **binding the witness to a real Step00
structure**. What is needed is a genuine ledger of genealogies in which `PaysPrime` is forced by
the boundary/ledger mechanics of the graph from [17](17_PaymentLedger.md)–[24](24_BoundaryDecomp.md), a hit is a genealogy's real landing
on a repunit center (the base-4 peel as a subsequence of peel steps), and the defect tokens carry
typed witnesses instead of a free `Prop`.

Then coverage/payment/debt will cease to be renamed conclusions, and the
noEngine layer will become inhabited — and the conditional 🟢 chains, carried all the way to
`TwinLowers.Infinite`, will get something to push against. Until then the branch's status is:
the embedding, the criterion and the reverse implication — 🟢; the load-bearing inputs of all the
routes and `MersennePrimesInfinite` — 🔴.

For the programme's greater arc the Mersenne branch is lateral and deliberately modest: it takes
part neither in the node `TheLastStep00Obligation` (narrowed to $A \ge 5$) nor in the main theorem
`higherEnergyIncompatibility_main`. Its contribution is different: it is the third case in a row
in which an adversarial audit found an empty wrapper before it could reach the showcase — and
thereby the best available argument for trusting the parts that did pass the showcase.

## Philosophical digression: Mersenne numbers and the path of Euclid himself

There is a particular fitness in the fact that Mersenne primes met precisely this programme. Our
engine is named after Euclid — and Mersenne leads straight to one of the most beautiful theorems
of the *Elements*. Euclid proved: if $2^p-1$ is prime, then $2^{p-1}(2^p-1)$ is a **perfect
number**, equal to the sum of its proper divisors (like $6 = 1+2+3$ or $28 = 1+2+4+7+14$).

Two thousand years later Euler closed the converse: every even
perfect number has exactly this form. Thus Mersenne primes and even perfect numbers turned out to
be *one and the same object*, seen from two sides — and the bridge between them stretches from
Euclid to Euler across the whole history of number theory.

Hence the honest lesson of this chapter, and philosophically it runs against the temptation.
Perfect numbers are the embodiment of the idea of *exact balance*, where the whole equals the sum
of its parts; it is tempting to believe that a machine about balance and payment would solve the
question of their infinitude "along the way". But the Euclid–Euler connection says nothing about
whether Mersenne primes (and hence even perfect numbers) are infinitely many — that remains open,
just as it was in Euclid's time.

Our branch honestly stops exactly where
knowledge stops: the embedding $2^p-1 = 6m+1$ and the twin criterion are proven, while the
infinitude is a named 🔴 input. The beauty of Euclid's theorem on perfect numbers gives no licence
to smuggle the unproven under its cover; and the fact that the programme of Euclid's engine
resisted this temptation is itself part of its honesty.

## Postscript (chapter 43): a refutation presents an engine

After this chapter the branch ceased to be merely "lateral". In [chapter 43](43_MersenneFirstCause.md)
its absence claim was carried through the Riemann manifestation architecture
(manifestation, unpresentable witness, forged refutation — see the [glossary](GLOSSARY.md)).

The absence witness
is greenly unpresentable (any bound ≥ 29), a forged witness does not exist — the chain
`4m+1`, unlike the five-adic one, provably cannot be peeled (`isEmpty_properCenterPeel_five_one`) —
and "refuting Mersenne twins on reconciled books = presenting a perpetual engine" became a green
theorem (`mersenneRefutation_carries_engine`).

The trilemma of the fourth boundary is passed, but the field is
**deliberately deferred**: under a boundary the law ⟺ unboundedness, and for the first time the
heuristic points against — see the honest signed price in [43](43_MersenneFirstCause.md). Vacuity No. 3 is not retouched by this: the
forward series remains uninhabited, and the new front shares not a single definition with it.

<!--navbot-->

---

[← 33. First cause and the main theorem](33_CausalFirstCause.md) · [Table of contents](00_Overview.md) · [35. P/NP: the local node →](35_ClassicalPNP.md)
<!--/navbot-->
