# 32. The single rank-parity node: twins and Riemann (an epilogue)

<!--navtop-->
[← 31. Riemann via Liouville](31_RiemannLiouville.md) · [Table of contents](00_Overview.md) · [33. First cause and the main theorem →](33_CausalFirstCause.md)
<!--/navtop-->



> Lean: `Engine/RiemannLiouville.lean` (`liouville_eq_neg_one_pow_rank`,
> `liouville_flip_of_mul_prime`, `riemann_of_liouville_bound`), `Engine/MkNode.lean`,
> `Engine/CarrierBridge.lean`, `Engine/ProductCore.lean`. Numbers: `tools/RESULTS_final_gap.md`,
> `prose/51_NumericalEvidence.md`. This is the final chapter of the prose.

In [27. ProductCore](27_ProductCore.md) we carried the twin reduction all the way to a finite product-rank descent, and in
[30. RiemannBranch](30_RiemannBranch.md) we built an independent branch towards the Riemann hypothesis through the same engine —
the forbidden infinite descending chain (see the [glossary](GLOSSARY.md)); the audit
of both left one irreducible node each.

Here we take the last step of the entire prose — not closing the
nodes, but **showing that they are one and the same node**, written in the common language of rank parity. The chapter's goal
is honest and limited: to exhibit a mechanism shared by both hypotheses, to separate within it
the proven part from the hypothetical one, and to leave a precise plan — without passing the unity off as a proof.

## Where we are: two nodes, one shape

Let us gather what we have arrived at, one line each. The twins (after [24](24_BoundaryDecomp.md), [30](30_RiemannBranch.md), [31](31_RiemannLiouville.md)) have been reduced to the claim
that an infinite carrier of pure centres yields an engine — provided the descent flow generates
infinitely many factorable starts **of fixed rank** (`GlobalOldAbsorption`, the sole
remainder of `RESULTS_final_gap.md`). Riemann (after [28](28_MkNode.md) and its arithmetic reformulation) has been reduced to
a bound on the Liouville summatory function

$$L(x) \;=\; \sum_{n\le x} \lambda(n), \qquad \lambda(n) = (-1)^{\Omega(n)},$$

where `LiouvilleBound` demands $|L(x)| = O\!\bigl(x^{1/2+\varepsilon}\bigr)$. At first sight these are
two unrelated difficulties — the combinatorial fan-in wall and the analytic $\sqrt{x}$ wall. The thesis of this
chapter: both are **control of the rank-parity balance** at a growing scale, and our rank apparatus
(`RankNode`, `cardFactors`, `deleteFactor`) is their common language.

## The apparatus: rank as the number of prime factors

Let us introduce exactly the objects on which the generalisation rests. A descent state at rank $r$ is

> **Definition 32.1** (`RankNode`). `RankNode r` is a structure with a field `sign : Sign` (the carrier of two
> $\sigma\in\{+1,-1\}$, the side $6m+\sigma$) and a field `factors : Fin r → ℕ` (an ordered tuple
> of $r$ prime factors of the active side, all $> A$ on the legal layer). The type is *extensional* in
> the pair `(sign, factors)` (`RankNode.ext` in `ProductCore.lean`): two nodes are equal if and only if
> their sign and all their factors coincide.

The rank of a node is exactly the number of prime factors with multiplicity, that is, the arithmetic function
$\Omega$. In mathlib it is called `cardFactors`, and this identity is not an analogy but an equality of functions:

$$\mathrm{rank}(6m+\sigma) \;=\; \Omega(6m+\sigma) \;=\; \texttt{cardFactors}\,(6m+\sigma).$$

From [28. MkNode](28_MkNode.md) we know that on the legal layer the rank is bounded: `factor_rank_le_four` gives $r\le 4$
(factors $>A$, product $\le 6X_A+1 < A^5$), and `composite_rank_ge_two` — that an impure composite
side has $r\ge 2$. So on the carrier the rank lives in the finite range $1\le r\le 4$ — which is exactly
`FactorizationData.hr` from [29. CarrierBridge](29_CarrierBridge.md).

The second object is rank lowering. Removing one factor is

> **Definition 32.2** (`deleteFactor`). `deleteFactor : RankNode (r+1) → Fin (r+1) → RankNode r`,
> $X \mapsto \langle X.\mathrm{sign},\ i\mapsto X.\mathrm{factors}(k.\mathrm{succAbove}\,i)\rangle$ —
> it discards the $k$-th factor, preserving the sign and the order of the rest. This is precisely the product-rank descent step
> $r\to r-1$ from [27](27_ProductCore.md).

The key observation that closes the apparatus onto Liouville: **removing a factor flips the sign of the rank**. If
$n = p\cdot m$ with $p$ prime, then $\Omega(n) = \Omega(m)+1$, hence

$$\lambda(n) \;=\; (-1)^{\Omega(n)} \;=\; -(-1)^{\Omega(m)} \;=\; -\lambda(m).$$

In Lean these are two theorems.

> **Theorem 32.3** (`liouville_eq_neg_one_pow_rank`). For every $n\ne 0$
>
> $$
> \lambda(n) \;=\; (-1)^{\texttt{cardFactors}\,n}. \tag{32.1}
> $$
>
> Proven with no inputs of ours, as a consequence of `liouville_apply` from mathlib. 🟢

> **Theorem 32.4** (`liouville_flip_of_mul_prime`). For a prime $p$ and every $m$
>
> $$
> \lambda(p\cdot m) \;=\; -\,\lambda(m). \tag{32.2}
> $$
>
> Proven via `cardFactors_mul` + `cardFactors_apply_prime`. 🟢

> **Note.** The meaning of these two lines is larger than their proof. They say that **the Liouville
> sign is the rank parity of our `RankNode`**, and `deleteFactor` is the operator that flips the Liouville
> sign. That is, the product-rank descent we built for the twins as a purely structural
> height dynamics turns out to be exactly the dynamics of the sign of $\lambda$. Two apparatuses, invented for different
> problems, are one and the same operator on one and the same carrier.

## The twin wall as a balance of side ranks

Let us return to the twins and write their wall in rank terms. The block statistics of [chapter 51](51_NumericalEvidence.md)
classify the centres by the pair $(\mathrm{rank}_{-},\mathrm{rank}_{+})$ of the ranks of the two sides
$6m-1,\ 6m+1$, coarsened to $\{0,3\}$ (prime side / "rich" composite). The cells:

$$N_{00}\ (\text{both prime} = \text{twin}),\quad N_{33}\ (\text{both richly composite}),\quad
N_{03},\ N_{30}\ (\text{mixed}).$$

The programme's target inequality is `B₅ = N₀₀ − N₃₃ > 0` (twins no fewer than "double
composites"), and the four-corner form

$$R_{\mathrm{fc}} \;=\; \frac{N_{00}\,N_{33}}{N_{03}\,N_{30}} \;<\; 1,$$

that is, a negative correlation between the ranks of the sides: primality of one side and primality of the other
"attract" each other. Numerically (table [A]) $R_{\mathrm{fc}}\in[0.86,0.98]$ and it grows towards $1$ with the block —
this is exactly the **wall of the margin going to zero**: the reserve $1 - R_{\mathrm{fc}}\to 0^+$ as the scale grows. The twin
wall is a statement about the *balance of the distribution of the two sides' ranks*: that the cell $N_{00}$ does not
empty out relative to $N_{33}$ as $N$ grows.

> **Note.** It is precisely here that [12–16] ran into the "parity wall": the model four-corner
> $20\binom{n}{6} < \binom{n}{3}^2$ is proven (`ModelFourCorner`), but the transfer model$\to$reality
> requires control of the joint distribution of the ranks $(\mathrm{rank}_-,\mathrm{rank}_+)$, not of a single
> marginal. This is a distributional, not a pointwise fact — exactly the same type of statement as the bound
> on $L(x)$.

## The Riemann wall as a balance of Liouville signs

Now Riemann in the same terms. By the identity $\lambda = (-1)^{\mathrm{rank}}$ the sum

$$L(x) \;=\; \sum_{n\le x} (-1)^{\mathrm{rank}(n)}
\;=\; \bigl\lvert\{n\le x:\ \mathrm{rank}(n)\ \text{even}\}\bigr\rvert \;-\; \bigl\lvert\{n\le x:\ \mathrm{rank}(n)\ \text{odd}\}\bigr\rvert$$

is exactly the **rank-parity imbalance** on the interval $[1,x]$: the difference between the number of integers with an even and
an odd number of prime factors. `LiouvilleBound` — $|L(x)| = O(\sqrt{x}\cdot x^{\varepsilon})$ —
says that this imbalance grows no faster than $\sqrt{x}$: the rank parities are almost balanced,
the deviation of "square-root" size, as in a random $\pm1$ walk.

And this is not a heuristic:
`LiouvilleRHBridge` is the classical equivalence $\texttt{LiouvilleBound}\iff\mathrm{RH}$, and
`riemann_of_liouville_bound` proves (conditionally on the bridge) $\mathrm{RH}$ from the bound. All the analytic content of RH
is isolated in the sign-balance estimate.

Let us set the two walls side by side, literally:

| | twin wall | Riemann wall |
|---|---|---|
| object | $R_{\mathrm{fc}} = N_{00}N_{33}/(N_{03}N_{30})$ | $L(x) = \sum_{n\le x}(-1)^{\mathrm{rank}(n)}$ |
| controlled quantity | balance of the **side ranks** $(\mathrm{rank}_-,\mathrm{rank}_+)$ | balance of the **rank parity** $\mathrm{rank}(n)\bmod 2$ |
| threshold | margin $1 - R_{\mathrm{fc}} \to 0^+$ | $|L(x)| = O(\sqrt{x})$ |
| loss of control | $N_{00}$ empties out $\Rightarrow$ twins are finite | $L(x)$ grows $\gg\sqrt{x}$ $\Rightarrow$ a zero off $1/2$ |
| common language | `RankNode`, `cardFactors` | `RankNode`, `cardFactors` |

**Section takeaway.** Both lines are about how $\mathrm{rank}(n) = \texttt{cardFactors}\,n$ is distributed as $n\to\infty$,
and both demand that this distribution not "collapse" into a single parity. This is the chapter's thesis.

> **Note.** There is exactly one difference, and it does not obstruct the unity. The twins look at the *joint*
> distribution of the ranks of two shifted sides $6m\pm1$ (a 2D balance of the cells $N_{ij}$); Riemann — at the
> *marginal* parity balance of a single $n$ (a 1D balance of the signs of $\lambda$). The marginal is a shadow of
> the joint: control of the 2D distribution of side ranks dominates control of the 1D parity. It is therefore
> natural to expect that the mechanism yielding the first also yields the second, and not the other way round.

## What is already shared in Lean (proven)

So as not to pass the wished-for off as done, let us separate the proven part. Shared by both hypotheses,
**already proven** are precisely the connecting links, not the bounds themselves:

- `liouville_eq_neg_one_pow_rank`, `liouville_flip_of_mul_prime` — the identity "Liouville sign = rank
  parity" and the flip under `deleteFactor` (from mathlib, with no inputs of ours);
- `RankNode.ext`, `deleteFactor` (`ProductCore.lean`) — the common carrier and the rank-lowering operator,
  used both in the twins' product-rank descent and as the sign operator of $\lambda$;
- `factor_rank_le_four`, `composite_rank_ge_two`, `mkNode_of_composite` (`MkNode.lean`) — the finiteness
  of the rank range $1\le r\le 4$ on the legal layer and the construction of a `RankNode` from a composite side — pure
  arithmetic;
- `engine_of_carrier_and_factorize`, `exists_infinite_fiber` (`CarrierBridge.lean`) —
  the infinite pigeonhole over rank (pigeonhole — the boxes principle, see the [glossary](GLOSSARY.md)):
  an infinite carrier splits over $\mathrm{Fin}\,4$ into rank
  classes, one of which is infinite; the whole pump machine (descent, the rank-1 base, pigeonhole) is assembled;
- `riemann_of_liouville_bound` (`RiemannLiouville.lean`) — RH from `LiouvilleBound` through the classical
  bridge, conditionally.

**Section takeaway.** All of this is *language and assembly*, not bounds. It is proven that if one controls the rank distribution
of the carrier (for the twins) or the parity balance of $\lambda$ (for Riemann), then both hypotheses close
through the already-proven machines (the EPMI engine / the classical bridge). What is **not proven** is the control itself.

## The unity conjecture (honestly: a conjecture, not a theorem)

Now — the chapter's central statement, presented as what it is.

> **Conjecture 32.5** (Rank-Parity Unity). There exists a single mechanism controlling the distribution of the rank
> $\mathrm{rank}(n) = \texttt{cardFactors}\,n$ at a growing scale — the same one required for
> `GlobalOldAbsorption` from [29](29_CarrierBridge.md)/[24](24_BoundaryDecomp.md) (the fan-in $570\to 1$ yields an engine) — from which
> *both* bounds follow:
> $$\underbrace{N_{00} - N_{33} > 0\ \text{uniformly}}_{\text{twins}}
> \qquad\text{and}\qquad
> \underbrace{|L(x)| = O(\sqrt{x}\cdot x^{\varepsilon})}_{\text{Riemann}}.$$
> The mechanism: control of the **descent-forest** (the forest of descent pedigrees) yields the distribution of rank over
> the absorber fibers, and this distribution simultaneously yields the twins' carrier balance ($N_{00}$ does not
> empty out) and the balance of Liouville signs ($L(x)$ is small).

Let us underline the honesty boundary in three points.

1. **Both bounds are open.** Neither `GlobalOldAbsorption` (twins, `RESULTS_final_gap.md`: "irreducible
   node") nor `LiouvilleBound` (Riemann, `RiemannLiouville.lean`: "arithmetic input") is proven.
   The conjecture asserts not their truth but their *commonality* — that one and the same control closes them both.
2. **The unity is a conjecture, not a reduction.** We have *not* proven the implication
   `GlobalOldAbsorption ⟹ LiouvilleBound` or its converse; had it been proven, RH would follow from the twins'
   node, and we explicitly rejected that back in [30](30_RiemannBranch.md) (the statements are independent). The unity is about the *nature
   of the difficulty* (both are rank-parity control), not about the logical derivability of one from the other.
3. **The final node is comparable in difficulty to the hypotheses themselves.** As noted in [30](30_RiemannBranch.md) and [24](24_BoundaryDecomp.md),
   the last analytic/combinatorial input of each branch is comparable in difficulty to the hypothesis itself.
   The common language does *not* make the node easier — it makes it *one*: a single wall instead of two.

## The closing plan (descent-forest ⟹ rank distribution ⟹ both balances)

The plan is inherited from [24, §Pigeonhole] and [27](27_ProductCore.md) and is now written down as a single programme for both walls.

**Step 1 — descent-forest.** Define the forest of descent pedigrees over the carrier: the vertices are states
`RankNode r`, the edges are `deleteFactor`/old-peel steps ([19](19_OldPeel.md), [24](24_BoundaryDecomp.md)), the roots are absorbers $\le M_0$.
The fan-in $570\to 1$ ([24](24_BoundaryDecomp.md)) is the branching of the forest: up to 570 pedigrees into one root. Control of the forest
is control of how $r$ decreases along the branches from the leaves to the root.

**Step 2 — rank distribution over the fiber.** From the structure of the forest, extract the distribution of
$\mathrm{rank}(n)\bmod 2$ over the fiber of each absorber. Here the already-proven
`exists_infinite_fiber` does the work: an infinite fiber splits over the $\mathrm{Fin}\,4$ rank classes.
The key that must be exhibited: **how `deleteFactor` along a branch changes the parity** (the proven flip
$\lambda\mapsto-\lambda$, Theorem 32.4 (`liouville_flip_of_mul_prime`)) induces an almost-uniform distribution of parities on the fiber — this is
exactly the shared rank-parity control.

**Step 3a — twins.** From the rank distribution over the fiber, derive the carrier balance: that the fraction of centres with
both sides prime ($N_{00}$) is not suppressed by the fraction of double composites ($N_{33}$), that is,
$R_{\mathrm{fc}}<1$ uniformly. This is the transfer of the model four-corner to reality through the **distribution
of side ranks**, not through a single marginal ([16](16_FiniteContradiction.md)).

**Step 3b — Riemann.** From the same rank distribution, derive $|L(x)| = O(\sqrt{x})$: the almost-uniformity
of the rank parities is exactly the "random-walk" size of the partial sum of the signs of $\lambda$.
Formally — plug the balance control into `riemann_of_liouville_bound` via `LiouvilleRHBridge`.

> **Note (a single point of failure).** Both steps 3 feed off the one step 2 — the distribution of
> rank parity over the descent-forest fiber. If this control is exhibited, both hypotheses close;
> if not — both are open. That is the operational meaning of the unity: **not two independent proofs, but
> one rank-parity control with two consequences**. The critical fork is the same normal-form trilemma
> from [24](24_BoundaryDecomp.md)/[29](29_CarrierBridge.md): the fiber signature must *distinguish* pedigrees (otherwise the balance is trivially false)
> and *glue* them into a finite key (otherwise the pigeonhole is empty). Until this fork is resolved, the unity
> remains a conjecture.

## Epilogue of the prose

Here the map of the path closes. We began ([00](00_Overview.md)–[11](11_TwoTransport.md)) with Euclid's engine and its laws — the conservation
of two, irreversibility, the impossibility of a perpetual engine (EPMI, proven) — and reduced the twins to the block
core.

We walked ([12](12_FourCorner.md)–[21](21_Regeneration.md)) the attack lines on the bound, each of which honestly ran into the one parity
wall, and decomposed the exit from the pure graph ([24](24_BoundaryDecomp.md)) down to a single global node. We closed
by arithmetic what could be closed: `ProductHall` via the separating scale ([26](26_SeparatingScale.md)), the rank-descent logic
([27](27_ProductCore.md)), `mkNode` and carrier infinitude ([28](28_MkNode.md)–[29](29_CarrierBridge.md)) — lifting all the earlier walls (parity, the trilemma,
steering, payment).

We built an independent branch to Riemann ([30](30_RiemannBranch.md)) and translated it into Liouville arithmetic
([31](31_RiemannLiouville.md)). And in this final chapter we saw that the remaining twins node and the remaining Riemann node are
**one and the same**, written as control of the rank-parity balance: `RankNode`, `cardFactors`,
`deleteFactor` — the common language of both.

The honest summary of the whole prose: **the machine is proven, the node is one, and it is open.** The twins and Riemann are not derived
and not passed off as derived; nowhere does the reduction substitute for a proof.

But two questions that stood apart for
centuries stand here side by side — on one carrier, with one wall, with one plan.

From the intuition
that guided the entire path, it is natural to expect that the wall to be taken is the rank-parity
wall, and that taking it once means closing both. Proving this is work beyond this
prose. Here we have named it precisely, localised it in a single node, and left it open.

<!--navbot-->

---

[← 31. Riemann via Liouville](31_RiemannLiouville.md) · [Table of contents](00_Overview.md) · [33. First cause and the main theorem →](33_CausalFirstCause.md)
<!--/navbot-->
