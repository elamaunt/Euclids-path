# 53. Birch–Swinnerton-Dyer: the eighth mask, where the engine is the descent itself

<!--navtop-->
[← 52. The dyadic model](52_DyadicModel.md) · [Table of contents](00_Overview.md) · [54. Neighbours beyond the horizon →](54_OpenNeighbors.md)
<!--/navtop-->

> Lean source: `Engine/BSDFront.lean` (the green descent core + the parity bridge + honest 🔴 gates +
> trilemma witnesses). It reuses `Engine/UniversalEngine` (the engine prohibition by rank) and
> `Engine/RiemannLiouville` (the rank-parity node). The core is grounded on **real** mathlib objects:
> `WeierstrassCurve.Affine.Point`, `WeierstrassCurve.LSeries`, the class `Northcott`, `AddCommGroup.fg_of_descent`.
> This is **not** a proof of BSD; the quarantine tax does not change (16), and the `sorry` is still one.

## Where we are

One millennium problem is left without a shadow of its own — the Birch–Swinnerton-Dyer conjecture. It, too, reads
through the perpetual-engine prohibition, but it enters the family differently, and therein lies all its interest.

For the seven earlier masks the engine **stands guard**: a deviation from the norm turns out to be an engine in
disguise, and the prohibition kills it. For BSD the engine does not stand guard — it **works as the method**. After
all, the algebraic rank of an elliptic curve is proven finite precisely by Fermat's infinite descent. The very
descent that lies at the foundation of the whole programme is here not a prohibition but a tool.

## Descent is the engine

The Mordell–Weil theorem says: the group of rational points `E(ℚ)` is finitely generated, `E(ℚ) ≅ ℤ^r ⊕ T`.
One proves it by descent: the Néron–Tate canonical height `ĥ` is a positive-definite quadratic
form, and by the Northcott property there are only finitely many points of bounded height. Hence the height descent
must break off — and the break-off yields finite generation.

This is exactly our prohibition: an infinite strictly descending chain of heights is a perpetual engine, and there is none.

**Theorem 53.1** (`bsd_descent_has_no_engine`, 🟢). *On the real group of points `W.toAffine.Point` of an elliptic curve, the height descent has no perpetual engine: for every height descent model $M$ there is no `PerpetualEngine M.descentStep`, that is, no infinite chain of points strictly decreasing under a height function $h\colon W.\text{toAffine.Point}\to\mathbb{N}$ can exist.*

"Why this is true." Height is an ℕ-rank, and rank imports the engine prohibition from the [universal
form](00_Overview.md): `UniversalEngine.no_perpetual_engine_of_natRank`. The carrier here is the **genuine**
`W.toAffine.Point` from mathlib (with its group law), and the mechanism is the same as in `Northcott` and
`AddCommGroup.fg_of_descent`: the well-foundedness of height cuts the descent short. The model is inhabited (not
vacuous) — a concrete witness over `ℚ` is presented.

> **Note (where exactly the licence ends).** The Néron–Tate canonical height is not yet in
> mathlib (there is the Weil height and an approximate parallelogram law — in progress), so our height is
> **named**. But the carrier and the group law are real, and the descent prohibition is derived rigorously. The
> grounding is honest: the shadow lies on a genuine curve, not on a mock-up.

## Parity — the same rank-parity node

The parity of the rank is tied to the analytics: the parity conjecture asserts `(−1)^rank = w(E)`, where `w(E)` is
the root number, the sign of the functional equation. And `(−1)^rank` is exactly the same rank-parity
invariant that stands behind Riemann: the Liouville function `λ(n) = (−1)^Ω(n)`.

**Theorem 53.2** (`bsd_parity_is_rankParity`, 🟢). *The parity of the rank coincides with Liouville's: for all $r, n \in \mathbb{N}$ with $n \neq 0$ and $\Omega(n) = r$ we have $(-1)^r = \lambda(n)$ in $\mathbb{Z}$.*

"Why this is true." A direct bridge to `RiemannLiouville.liouville_eq_neg_one_pow_rank` — the same sign
rule, the same flip when a prime factor is removed. BSD parity is not a new beast but our node, fitted
onto the rank of an elliptic curve.

It is natural to ask: should we not decree this parity as a first cause, the way we decreed Riemann's
law? We checked honestly — and **no**.

> **Note (the trilemma's verdict: there is no honest boundary).** The genuine root number `w(E)` is a deep
> analytic invariant that mathlib does not have. Over the available stub (`RootNumber w := w = ±1`,
> a free value) the law `(−1)^r = w` is satisfied by a choice of `w` (`bsd_parityLaw_satisfiable`), and the
> universal form is refutable (`bsd_parityLaw_not_universal`). Hence a parity decree would be
> **vacuous** — just as for P/NP, Yang–Mills and Hodge. Therefore we do **not** touch the axiom and leave the parity
> honestly open: the tie to the node remains conceptual, not a decree. The tax — the same 16.

## The analytic bridge — honestly open

The very heart of BSD is the equality of the algebraic and analytic ranks: `rank E(ℚ) = ord_{s=1} L(E,s)`.
mathlib **already defines** the curve's `L`-function (`WeierstrassCurve.LSeries`, via the Euler product),
and we honestly refer to it. But its analytic properties — continuation to `s=1`, the order of the zero, the
functional equation — are proven nowhere.

**Definition 53.3** (`WeakBSD`, 🔴). *Open input: for an elliptic curve $W/K$ and natural numbers $\text{algRank},\, \text{aRank}$, the predicate $\mathrm{WeakBSD}(W,\text{algRank},\text{aRank})$ is $\mathrm{AnalyticRank}(W,\text{aRank}) \wedge \text{algRank} = \text{aRank}$. We do not prove it: it is a named input, not a theorem.*

Humanity has covered only the edges: for analytic rank `≤ 1` (Gross–Zagier and Kolyvagin, via Heegner points and
Euler systems) BSD is proven and Sha is finite; on average — over 66% of curves (Bhargava–Skinner–Zhang). For
rank `≥ 2` everything is open. Our engine does not close the analytics: its role here is the descent, not the bridge.

## Philosophical digression: a tool, not a guard

In BSD the engine shows its second face. Everywhere before, it was a *prohibition* — a wall against which a
deviation shatters. Here it is a *method* — the very ladder of descent by which Fermat and Mordell counted points. One and
the same object: the impossibility of decreasing natural numbers forever. In six masks that impossibility
forbids; in BSD it computes.

And this honestly delimits the reading. The descent side (the rank is finite) and the parity side (the same node) we
read as a shadow of the prohibition — green, on a real curve. But the analytic heart — the agreement of the rank with the zero
of the `L`-function — does not depend on the engine prohibition and remains beyond the horizon. The shadow is there; the body lies outside it.

> **Note (the epistemics of BSD).** BSD has no epistemic axis of its own — and this is fixed machine-wise
> (`Engine/BSDEpistemic.lean`). The proposed ground/beyondOwnHorizon pair degenerates: the second leg is
> literally the field of height decrease, free by construction, so the whole bundle coincides with the already-proven
> prohibition of the descent engine (`bsdGround_coincides_with_engine`). This is not a weakness but a precise fact about where
> the content of BSD lives: not in the epistemics, but in the data anchor — in the open equality of ranks. Along the way one sees that
> the `AnalyticRank` gate is freely satisfiable (`analyticRank_gate_satisfiable`), and `WeakBSD` reduces to the bare
> `algRank = aRank` (`weakBSD_reduces_to_bare_equality`) — exactly there all the honest 🔴 openness remains.

> **Note (contentful gates).** The old free gates now have a contentful replacement —
> `Engine/BSDAnalyticAnchor.lean`. The analytic rank ceases to be a free parameter and becomes a
> genuine mathlib notion: `analyticRankOf L := analyticOrderAt L.Lambda 1` — the order of the zero of the continuation
> at the point `s = 1`. But this works only **when the datum itself is supplied**: the red input `ContinuedLFunction`
> carries a function `Λ` that agrees with `WeierstrassCurve.LSeries` wherever the Dirichlet series is absolutely summable
> (`agreement`) and is analytic at `s = 1` (`analyticAtOne`) — the very continuation that mathlib does not have
> (even with the Hasse bound the point `1` lies outside the half-plane of convergence, `1 < 3/2`). On these data the
> contentful gate `WeakBSDContentful` is built. The contrast is precisely the honest punchline: the old gates are satisfiable for free
> at **all** ranks at once, the new ones **pin** the rank (`contentfulGate_pins_rank` — at most one per
> anchor) and cost data. We assert nothing about the genuine L-function — we only name an input that is
> paid for with data, not with a decree.

## Place in the greater arc

Appendix C gives the eighth problem its shadow without embellishment. Formalizations of BSD, of Mordell–Weil, of the canonical
height, of the analytics of elliptic-curve `L`-functions exist nowhere (by our survey — Loeffler–Stoll 2025,
Angdinata–Xu 2023). Hence even a structural engine/rank-parity reading, grounded on real mathlib
objects, is the first of its kind. But it is **not** a solution of BSD: green are only the descent and the parity node; the analytic
bridge is honestly 🔴; no decree has been added (the trilemma). `twin_prime_conjecture` remains a `sorry`; the tax — the same 16.

<!--navbot-->

---

[← 52. The dyadic model](52_DyadicModel.md) · [Table of contents](00_Overview.md) · [54. Neighbours beyond the horizon →](54_OpenNeighbors.md)
<!--/navbot-->
