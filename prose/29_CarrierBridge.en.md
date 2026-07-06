# 29. The last link and its boundary

<!--navtop-->
[← 28. MkNode](28_MkNode.md) · [Table of contents](00_Overview.md) · [30. Riemann: contraposition →](30_RiemannBranch.md)
<!--/navtop-->



> Lean source: `EuclidsPath/Engine/CarrierBridge.lean` (namespace `EuclidsPath.CarrierBridge`),
> built on `EuclidsPath/Engine/ProductCore.lean` and `EuclidsPath/Engine/Residuals.lean`.
> Key names: `cleanCenters_infinite`, `exists_infinite_fiber`, `factorizationData_of_carrier`,
> `engine_of_carrier_and_factorize`, `product_core_engine_of_carrier`.

In the previous chapter (28, `mkNode`) we learned how to extract from a single clean side a concrete
core node `RankNode r`: factoring the composite side $6m\pm 1$ into primes `> A` gave us a sign and a
role-indexed set of factors, and `factor_rank_le_four` pinned the rank between `2` and `4`. In other
words, we possess a local map "center $m$ $\mapsto$ core node".

Now we assemble the last link: we join this map with the already proven infinitude of the carrier and
with the core's pump machine from the `ProductCore` chapter, in order to obtain Euclid's perpetual
engine (`Engine`) — the programme's central forbidden object (see the [glossary](GLOSSARY.md)). We
will show that the entire arithmetic of this link is proven — and honestly trace the single boundary
against which it rests.

## 29.1. What the carrier supplies: infinitely many clean centers

Let us introduce the set of clean centers at a fixed threshold $A$.

> **Definition 29.1** (CleanCenters). For $A\in\mathbb{N}$ we set
>
> $$
> \mathrm{CleanCenters}(A)\;:=\;\{\,m\in\mathbb{N}\;\mid\;\mathrm{CleanZ}\,A\,(m:\mathbb{Z})\,\},
> $$
>
> where `CleanZ A m` means that no prime $q\le A$ divides either of the sides $6m-1$, $6m+1$
> (in $\mathbb{Z}$). This is a clean center: a center free of the "old" primes $\le A$.

The first brick of the link is the infinitude of this set. It is not postulated: it follows from the
fact `carrier_nonempty_above`, already proven in `Residuals`, which for any $A,N$ exhibits a clean
center strictly above $N$ (constructively, $m=(N+1)\cdot\mathrm{oldPrimorial}\,A$; no density is needed).

> **Theorem 29.2** (`cleanCenters_infinite`). For every $A$ the set $\mathrm{CleanCenters}(A)$ is infinite:
>
> $$
> (\mathrm{CleanCenters}\,A).\mathrm{Infinite}.
> $$

The proof is simple in form and substantive in meaning. We apply
`Set.infinite_of_not_bddAbove`: it suffices to show that the set is not bounded above. For any
candidate upper bound $N$, the fact `carrier_nonempty_above A N` produces a clean center $m>N$, which
refutes the boundedness.

**Why** this works with no analysis at all: clean centers are built as multiples of the primorial
$\mathrm{oldPrimorial}\,A$ — the product of all primes $\le A$; such a multiple is congruent to $0$
modulo every small prime, hence $6m\pm 1\equiv \pm 1$, and no $q\le A$ divides it. There are
infinitely many multiples of the primorial, and they reach arbitrarily high — whence the infinitude.

**What this means:** the carrier of two
supplies an unbounded stock of starts free of small primes — precisely the "fuel" that the core's
pump machine demands.

## 29.2. The single real input: FactorizationData

The pump machine of `ProductCore` (theorem `product_core_engine_of_carrier`) accepts not "centers"
but already factorized core nodes. So we separate out exactly that structural input — in the house
sense: an honestly named but not yet proven missing statement (see the [glossary](GLOSSARY.md)) —
which must arrive from sieve arithmetic, and name it explicitly.

> **Definition 29.3** (`FactorizationData A X_A`). A data package consisting of:
> - a rank $r$ with $1\le r\le 4$;
> - an infinite set of starts $S\subseteq\mathbb{N}$ of one rank $r$;
> - a map `node : ℕ → RankNode r`, injective on $S$ (`hinj : Set.InjOn node S`);
> - a legality certificate `hamb : ∀ m ∈ S, AmbientLegal X_A (node m).factors`.
>
> Here `AmbientLegal X_A factors` means the existence of a common top-side $N_0$ with
> $0<N_0\le 6X_A+1$ and $\text{factors}\,i\mid N_0$ for all $i$.

This is not an axiom of the engine. Substantively, `FactorizationData` is the statement "infinitely
many clean starts of one fixed rank factor into legal core nodes, with distinct starts yielding
distinct nodes". The existence of the factorization and the bound `rank ≤ 4` come from the arithmetic
itself (chapter 28), while fixing a single rank comes from the pigeonhole — the boxes principle (see
below and the [glossary](GLOSSARY.md)). Once such a package is assembled, we
obtain an engine at once.

> **Theorem 29.4** (`engine_of_factorization`). Under the separating scale $6X_A+1<P_A$ and given
> $F:\mathrm{FactorizationData}\,A\,X_A$, `Engine` holds:
>
> $$
> 6X_A+1<P_A\;\wedge\;F\;\Longrightarrow\;\mathrm{Engine}.\tag{29.1}
> $$

This is literally `product_core_engine_of_carrier` with the fields of the package $F$ plugged in: the
rank `F.r`, the set `F.S`, the infinitude `F.hS`, the map `F.node`, the injectivity `F.hinj`, the
legality `F.hamb`.

**Why** this
suffices: an injective map from the infinite $S$ into the finite signature space `CoreSig P_A r`
(finite, since $A$, and with it $P_A$, are fixed) must produce a collision — two distinct nodes with
equal signature; then the descent-in-rank (`core_step_proved`) and the rank-1 base
(`rank_one_coreCollision_absurd`), both proven by pure arithmetic under the separating scale, close
everything down to `Engine`. That entire pump machine — descent, base, pigeonhole — is already proven
in the chapters on `ProductCore` and `SeparatingScale`; here we merely hand it its input.

> **Note.** The role of the separating scale $6X_A+1<P_A$ is exactly the same as in chapter 30: it
> makes the coarse passport `a mod P_A` injective on the legal layer (`ambient_factor_lt_primorial`:
> every factor is $<P_A$), thereby sidestepping the `UniqueLegalLift` trilemma. Here we already use
> this as an established fact.

## 29.3. Assembling the rank: infinite pigeonhole

To build `FactorizationData` from "raw" centers, one must carve out of the infinite carrier an
infinite subset of *one* rank. This is a purely combinatorial fact, and it is proven in full.

> **Theorem 29.5** (`exists_infinite_fiber`). Let $S$ be infinite and $f:S\to \mathrm{Fin}(n+1)$. Then some
> fiber is infinite:
>
> $$
> \exists c,\;\{x\mid x\in S\wedge f\,x=c\}.\mathrm{Infinite}.
> $$

The proof is the infinite pigeonhole principle by contradiction. If every fiber were finite, then
$S\subseteq\bigcup_c\{x\in S\mid f\,x=c\}$ would be a finite union of finite sets, hence finite —
contradicting the infinitude of $S$. **What this means for us:** there are only four ranks ($1..4$),
so among infinitely many clean centers, infinitely many share one and the same rank. That very fiber
becomes the set $S$ inside `FactorizationData`.

Now we glue the pigeonhole to the factorization maps.

> **Definition 29.6** (`factorizationData_of_carrier`). Given:
> - an infinite carrier $C\subseteq\mathbb{N}$ (`hC : C.Infinite`);
> - a rank function `rankOf : ℕ → Fin 4` (the number of large prime factors, shifted; the arithmetic of chapter 28);
> - a node map `mkNode : (r:ℕ) → ℕ → RankNode r`;
> - injectivity `hinj` of the map `mkNode (r+1)` on each rank fiber $\{x\in C\mid \mathrm{rankOf}\,x=r\}$;
> - legality `hamb`: $m\in C$, $\mathrm{rankOf}\,m=r\Rightarrow \mathrm{AmbientLegal}\,X_A\,(\mathrm{mkNode}\,(r{+}1)\,m).\text{factors}$.
>
> Then a `FactorizationData A X_A` is constructed: an infinite rank fiber $c$ is chosen (via
> `exists_infinite_fiber`), one sets $r=c+1$ (so $1\le r\le 4$), $S$ is that fiber, `node = mkNode (c+1)`,
> and `hinj`/`hamb` are taken on the chosen fiber.

Here the only unproven elements remaining are *the maps themselves* — `rankOf`, `mkNode`, `hinj`,
`hamb`: the binding of a rank to a center and the legal factorization $6m\pm 1=\prod a_i$. The
combinatorics (choosing an infinite fiber of one rank) we have already carried out rigorously.

## 29.4. The finale from the carrier and the factorization

Joining everything, we obtain the link's final theorem.

> **Theorem 29.7** (`engine_of_carrier_and_factorize`). Under the separating scale $6X_A+1<P_A$, an infinite
> carrier $C$, and given a rank function `rankOf` and a node map `mkNode` that is injective and
> `AmbientLegal` on each rank — `Engine` holds:
>
> $$
> 6X_A+1<P_A,\;C.\mathrm{Infinite},\;\mathrm{rankOf},\;\mathrm{mkNode},\;\mathrm{hinj},\;\mathrm{hamb}\;\Longrightarrow\;\mathrm{Engine}.\tag{29.2}
> $$

It is the composition `engine_of_factorization ∘ factorizationData_of_carrier` (Theorem 29.4 ∘ Definition 29.6). **What is proven in
full inside the link:** the infinitude of the carrier (Theorem 29.2, `cleanCenters_infinite`), the choice of an
infinite fiber of one rank (Theorem 29.5, `exists_infinite_fiber`), and the entire pump machine we plug into
(`product_core_engine_of_carrier`).

**The single input** is the factorization maps `rankOf`/`mkNode`/`hinj`/`hamb`. In other words, the
link translates the problem "prove the infinitude of twins" into the problem "exhibit an infinite
family of clean centers factorizable into legal nodes of a fixed rank, injectively".

## 29.5. The boundary: why a direct splice is impossible

Full honesty is required here, or else a reduction gets passed off as a proof. Between the two proven
ends of the link — `cleanCenters_infinite` on the left and the pump machine on the right — there is a
seam that does *not* splice directly.

**Observation (the scale barrier).** The legality `AmbientLegal X_A` requires the factors to divide a
common top-side $N_0\le 6X_A+1$. But the factors of a center $m$ are divisors of its own sides
$6m\pm 1$. Hence `node m` can be `AmbientLegal X_A` only when the side fits into the window, that is,
essentially when
$$6m\pm 1\;\le\;6X_A+1,\qquad\text{that is,}\quad m\;\lesssim\;X_A.$$
This is a finite segment of centers $m\le X_A$ — exactly the region where `mkNode`/`nodeable` from
chapter 28 apply (there `rank ≤ 4` holds precisely because the product of the factors is bounded by
$6X_A+1<A^5$).

On the other hand, `cleanCenters_infinite` gives infinitude *in $m$*: clean centers reach arbitrarily
high, inevitably *above* $X_A$. And there the side $6m\pm 1>6X_A+1$, and the certificate
`AmbientLegal X_A` is no longer available; with it the rank bound $\le 4$ breaks down as well (the
product of the factors is no longer locked under $A^5$).

> **Note (where exactly the seam lies).** The infinitude of the carrier is infinitude along the
> vertical $m\to\infty$; the legality of a node is membership in a finite horizontal window
> $m\le X_A$. The intersection "infinitely many $m$" $\cap$ "$m\le X_A$" is empty for fixed $X_A$.
> Therefore one cannot take the ready-made infinitude from `cleanCenters_infinite` and feed it
> directly into `factorizationData_of_carrier`: almost none of those centers has an
> `AmbientLegal X_A` node. The hypotheses `hamb` of §29.3 are, for fixed $X_A$, not satisfiable on
> the whole carrier — they are satisfiable only on a finite slice.

**Conclusion.** This is exactly why the maps `mkNode`/`hinj`/`hamb` are left as an *input* rather than
derived: they cannot be obtained from `cleanCenters_infinite` alone. What is required is a mechanism
that supplies infinitely many legal nodes *at a growing scale* — not at a single $X_A$, but
coherently, with $X_A$ and $A$ growing together with $m$.

## 29.6. The irreducible node: GlobalOldAbsorption

That mechanism is `GlobalOldAbsorption`: a statement about genealogies at a growing scale that absorb
the old primes. The comment of the final theorem of `ProductCore` states it plainly: what remains
open is exactly the carrier structure `CarrierData`, "that which must come from `GlobalOldAbsorption`
(the factorization of $6m+\sigma$, `rank ≤ 4`, the infinitude of starts)".

An honest assessment: `GlobalOldAbsorption` is **irreducible** — in strength it equals the twin prime
conjecture itself. It demands exhibiting an infinite family of centers, each of which (i) is clean,
(ii) has a composite side with a legal factorization of fixed rank, and (iii) yields distinguishable
nodes — and all this coherently as $m\to\infty$. This, in essence, is control over an infinite number
of "absorbed" genealogies. No finite arithmetic (we have already exhausted it in chapters 28 and 30)
reaches this far: the barrier of §29.5 shows that any finite $X_A$ gets cut off.

> **Hypothesis (descent-forest control).** From the intuition of the carrying of two, it is natural
> to conjecture the following. Consider the descent forest over the clean centers: the edges are
> steps of strict height descent along active factors. Then control of the branching of this forest —
> bounded fan-in together with the impossibility of infinite descent (the already proven
> `no_infinite_descent`) — implies that infinitely many genealogies are "absorbed": their old primes
> are fully absorbed, and their sides become legally factorizable at their own scale. Formally:
>
> $$
> \text{descent-forest bounded}\;\Longrightarrow\;\{\,m\;\mid\;m\ \text{absorbed, rank}\le 4,\ \text{node injective}\,\}\ \text{is infinite}.
> $$

> **Closure plan.** (1) Define a scale function $A(m),X_A(m)$ growing together with $m$ so that the
> side $6m\pm 1$ falls into the window $\le 6X_A(m)+1$ while the separating scale $6X_A(m)+1<P_{A(m)}$
> is preserved (by chapter 30 this is achievable with room to spare: $\log P_A\sim A/\ln 10$ outruns
> $4.5\log A$). (2) At this growing scale, apply the arithmetic of chapter 28 (`mkNode_of_composite`)
> to the absorbed centers, obtaining `AmbientLegal` nodes of rank $2..4$ **at their own scale**.
> (3) Via `exists_infinite_fiber`, fix one rank on an infinite subfamily. (4) Reduce everything to
> `engine_of_carrier_and_factorize`, feeding the absorbed subfamily as the carrier $C$ and the
> constructed nodes as `mkNode`. The key missing step is precisely (1)+(2): the scale-coherent
> absorption of the old primes, that is, `GlobalOldAbsorption`.

**Section takeaway.** The `CarrierBridge` link is closed at both ends by proven mathematics, and between them there
remains exactly one named, irreducible node. We do not pass this reduction off as a proof of the
twins: it honestly restates them as `GlobalOldAbsorption` and points out a closure plan via
descent-forest control.

## Bridge to the next chapter

The final node of the twins turned out to be comparable in difficulty to the conjecture itself — the
typical boundary of deep reductions.

In the next chapter (30, Riemann) we shall see that the same
scheme "by contradiction through Euclid's engine" carries over to a side branch: `¬RH` is fed into
the very same proven EPMI, and all the analysis is once again isolated in a single bridge,
`EngineBridge` — the analogue of `GlobalOldAbsorption`, but now for the zeros of $\zeta$.

The
structure of the limiting node will repeat itself, which explains why both problems run up against
one and the same mechanism of the carrying of two.

<!--navbot-->

---

[← 28. MkNode](28_MkNode.md) · [Table of contents](00_Overview.md) · [30. Riemann: contraposition →](30_RiemannBranch.md)
<!--/navbot-->
