# SNOL: reduction to the rank-1 neighbour

<!--navtop-->
[← 17. Payment law](17_PaymentLedger.md) · [Table of contents](00_Overview.md) · [19. Old-peel →](19_OldPeel.md)
<!--/navtop-->



In [17 Payment] we sharpened "the engine does not stop for free" into a precise *defect law*: a free pass to a prime $p$ requires that $a-\theta$ be divisible by the entire primorial of the small primes, and as soon as the primorial outgrows the active divisor, such a pass is impossible for a nontrivial $a$.

But there the single distributional input — that is, a named missing statement, a gate (see the [glossary](GLOSSARY.md)) — remained isolated in a scalar: the balance of shifted-charge and tax, pulling in opposite directions and refusing to close simultaneously without counting. The present chapter changes the angle of attack: instead of trying to defeat that scalar budget by counting, we reduce the *entire* programme to a single algebraic node and show why that node is **non-counting by construction**.

## Change of strategy: from the counting wall to a single node

All the previous final routes — four-corner ([12](12_FourCorner.md), [14](14_RealFourCorner.md)) and payment budget ([17](17_PaymentLedger.md)) — ran into one and the same **counting** wall: to close them, one had to control the distribution of the shift's divisors (Mertens, Brun/Selberg), that is, to cross the parity barrier. Intuition suggests trying not to break through this wall, but to *walk around* it structurally.

The observation underlying the reduction: the defects of a product-state are organised by **rank** (the number of primes $>A$ in the factorisation of the active side), and along the rank one can *descend*. Rank descent reduces every defect to *rank-1* — a state in which one side of the wedge is the active prime $a$ itself. And rank-1, as we show below by pure algebra, reduces to *one* neighbour lemma:

$$\boxed{\ \text{finiteness of twins}\ \Longrightarrow\ \text{carrier-scale terminal shifted-neighbour obstruction}\ (\,p\mid a-2\varepsilon,\ p\le A\,).\ }$$

We call this implication **SNOL** (Shifted-Neighbour Obstruction Lemma). The key property of SNOL — the very point of undertaking the whole reduction — is that it is **non-counting by construction**. Below we prove all the surrounding algebra machine-checked and present numerical evidence that counting is powerless here *in both directions*.

> **Note.** Nowhere do we pass this reduction off as a proof of the twin conjecture. What is proven is the *algebra* of rank-1 and the *conditional* theorem "SNOL $\Rightarrow$ infinitude of twins". SNOL itself is the single open node; the chapter honestly localises it — it does not close it.

## The provable rank-1 algebra

### Carrying the two across to the opposite side

Introduce the rank-1 configuration: the active prime $a$ occupies one side of the wedge with centre $n$ and sign $\varepsilon\in\{-1,+1\}$, that is,

$$6n+\varepsilon = a.$$

Then the opposite side of the same centre is computed with nothing left over.

> **Theorem** (`rank1_opposite`). If $6n+\varepsilon=a$, then
> $$6n-\varepsilon = a - 2\varepsilon.$$

The proof is pure carry-the-two arithmetic (`omega`): subtracting $2\varepsilon$ from both sides of the equality $6n+\varepsilon=a$, we obtain $6n-\varepsilon=a-2\varepsilon$. Substantively this means: as soon as one side of a rank-1 wedge *is* the active prime, the second side is **rigidly fixed** as the shifted neighbour $a-2\varepsilon$. It is precisely this shifted neighbour that becomes the arena of all the ensuing struggle — not $a$ itself, but its neighbour $a-2\varepsilon$ (for $\varepsilon=+1$ this is $a-2$, for $\varepsilon=-1$ it is $a+2$).

### Saturation of the neighbour corridor

Now suppose the active prime lies in the neighbour corridor with respect to a finite set $Q$ of pairwise coprime small moduli: for every $q\in Q$ we have $a\equiv 2\varepsilon\pmod q$, equivalently $q\mid a-2\varepsilon$. Then the divisibility lifts to the primorial.

> **Theorem** (`neighbour_saturation`). Suppose $(Q)_{\mathrm{Set}}$ are pairwise coprime and $q\mid a-2\varepsilon$ for all $q\in Q$. Then
> $$\Bigl(\prod_{q\in Q} q\Bigr)\ \Big|\ a-2\varepsilon,$$
> that is, $a = k\!\cdot\!\prod_{q\in Q} q + 2\varepsilon$ for some $k$.

The proof lifts the pairwise divisibility to divisibility by the product via pairwise coprimality (`Finset.prod_dvd_of_coprime`, with coprimality translated into `IsCoprime` over $\mathbb Z$). This is exactly the Euclidean twin-neighbour shift of the form $kP\pm 2$: an active prime whose entire neighbour has been "eaten up" by the small primes is forced to have the form $a=kP+2\varepsilon$. There is no distribution anywhere here — this is a divisibility identity.

### The threshold: the corridor is out of reach for small $a$

The saturation $P\mid a-2\varepsilon$ comes into conflict with size as soon as the corridor's primorial outgrows the magnitude of the shift.

> **Theorem** (`neighbour_corridor_bound`). If $P\mid a-2\varepsilon$ and $|a-2\varepsilon|<P$, then $a=2\varepsilon$.

The proof splits into two cases. If $a-2\varepsilon=0$, the claim is trivial. Otherwise $a-2\varepsilon\neq 0$, and from $P\mid a-2\varepsilon$ we get $P\le|a-2\varepsilon|$ (`Int.le_of_dvd` applied to a nonzero dividend) — contradicting $|a-2\varepsilon|<P$, so the remaining case is closed by `omega`.

Substantively: a nontrivial active prime **cannot saturate an entire corridor** whose primorial has exceeded its shift. This is exactly the same defect law as in [17 Payment] (`shifted_primorial_bound`, `late_boundary_not_free`), but for the neighbour shift $2\varepsilon$ instead of the compatibility shift $\theta$.

> **Note.** The three theorems above — the whole of the rank-1 algebra — are proven **without a single distributional assumption**. Numerically the rank descent is short: the old-free composite sides $6m\pm1$ exhibit *100% rank 2* (exactly two primes $>A$), so in practice the chain $4\to3\to2\to1$ degenerates into a single step $2\to1$; and the neighbour corridor $kP\pm2$ is confirmed by an exact identity ($Q=\{5,7,11\}$, $P=385$: $a=385k\pm2\Rightarrow a\mp2\equiv0\pmod{385}$).

## The final conditional theorem

To connect the rank-1 algebra with the twin conjecture, we fix the **SNOL input** — the same typed block predicate that closes the whole programme in [15 ToTwins].

> **Definition** (`SNOLInput`). The statement
> $$\forall N,\ \exists\,\text{carrier},\text{bad}:\ (\forall m\in\text{carrier},\ N<m)\ \wedge\ |\text{bad}|<|\text{carrier}|\ \wedge\ (\forall m\in\text{carrier},\ m\notin\text{bad}\Rightarrow \mathrm{IsTwinCenter}\,m).$$

That is: at every scale $N$ there exists a carrier above $N$ in which the "bad" elements (carriers of the terminal shifted-neighbour obstruction) are strictly fewer than the whole, and every survivor is a twin centre. SNOL as a substantive claim says exactly this: the terminal shifted-neighbour current **cannot be carrier-scale**, so the block input holds.

> **Theorem 21.1** (`twin_primes_of_SNOL`). If `SNOLInput` holds, then `TwinLowers.Infinite` — there are infinitely many twin primes.

The proof is the direct bridge `twin_prime_conjecture_of_blocks`: the same capstone passage "block dominance of the survivors $\Rightarrow$ unboundedness of twin centres $\Rightarrow$ infinitude" as in [15 ToTwins], only with the input supplied in the form of SNOL rather than the genuine four-corner. Contraposition completes the picture.

> **Theorem** (`finite_contradicts_SNOL`). If `TwinLowers` is finite and `SNOLInput` holds, then `False`.

Proof: `finite_contradicts_SNOL hfin H := hfin (twin_primes_of_SNOL H)`. The single open node of the whole programme is thus SNOL itself: everything else is machine-verified.

## Why SNOL is not the same wall

Here lies the fundamental difference from the previous inputs. Earlier the input $H$ (four-corner) was a *distribution in disguise*: it could not be checked without estimating the density of ranks. SNOL is built differently, and the numbers confirm it.

The neighbour audit (`tools/RESULTS_snol.md`, harness `snol_harness.py`) measures the fraction of primes $a\in(A,A^2]$ whose neighbour $a\pm2$ already has a small divisor $\le A$ — that is, the fraction where CRT "catches" the neighbour:

| $A$ | $a-2$ caught | $a+2$ caught |
|---|---|---|
| 50 | 0.617 | 0.628 |
| 200 | 0.705 | 0.706 |
| 1000 | 0.778 | 0.778 |

The fraction is large and **grows** with $A$ following the law $1-\prod_{q\le A}(1-1/q)$. Hence a two-sided conclusion:

- **SNOL cannot be proven by counting/CRT capacity.** For 62–78% of active primes the neighbour is *already caught* by a small prime — this is not an anomaly but the norm. So the "catch $p\mid a-2\varepsilon$" is in itself typical, and no capacity estimate will forbid it.
- Consequently, SNOL is *bound* to rest not on distribution but on the **Euclidean pedigree** of the active $a$: on the fact that $a$ arrived from the descent of a wedge centre, rather than being drawn from the general population of primes.

**Conclusion.** The route does not cross the red line precisely because where the previous inputs secretly summoned distribution, SNOL **forbids** it (counting is powerless in both directions) and demands the *structure of the pedigree* in its place.

> **Conjecture (SNOL, open).** The terminal shifted-neighbour obstruction cannot be carrier-scale: at every scale, the fraction of active primes $a$ (arrived via descent) whose neighbour $a-2\varepsilon$ is *systematically* caught by an old prime $p\le A$ in such a way that $a$ becomes a terminal, is strictly smaller than the carrier — that is, the survivors are the majority.
>
> **Closure plan.** Tie the active prime $a$ to its descent ancestor so that the structure of the pedigree *forbids* systematic landing in the neighbour corridor $p\mid a-2\varepsilon$. Since counting is powerless here by construction, the argument must be about the provenance of $a$, not about its arithmetic modulo the small primes. The first step of this plan is to show that the "catch" $p\mid a-2\varepsilon$ is not a terminal but a descent step, regenerating a smaller centre.

## Where we are now

The entire programme has been reduced to *one* machine-pinned node — SNOL. Unlike the previous inputs, it is **non-counting** (we checked: counting is powerless both for and against) and points to the exact site of future work — the pedigree of the active prime.

It is natural to expect that the final step of the closure plan — unfolding the "catch" into descent — must likewise rest not on distribution but on the already proven impossibility of Euclid's engine — the prohibition of infinite strictly decreasing descent (see the [glossary](GLOSSARY.md)). It is precisely this unfolding that we take apart next: in [19 Old-peel] the terminal shifted-neighbour obstruction ceases to be a terminal and turns out to be yet another step of strict descent, closing the finale onto EPMI without a single counting argument.

<!--navbot-->

---

[← 17. Payment law](17_PaymentLedger.md) · [Table of contents](00_Overview.md) · [19. Old-peel →](19_OldPeel.md)
<!--/navbot-->
