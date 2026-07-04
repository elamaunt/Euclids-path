# 31. The Riemann Hypothesis via the Liouville function

<!--navtop-->
[← 30. Riemann: contraposition](30_RiemannBranch.md) · [Table of contents](00_Overview.md) · [32. The rank-parity node →](32_RankParityUnity.md)
<!--/navtop-->



> Lean: `Engine/RiemannLiouville.lean`. Numbers: `|L(x)|/\sqrt{x}` is bounded (the classical
> Liouville equivalent of RH). Link to the engine: the Liouville sign = `(−1)^rank`, flipped by `deleteFactor`.

## Where we are

In chapters 30–31 (`SeparatingScale`, `RankDescent`, `ProductCore`) we closed `ProductHall` by pure
arithmetic and shifted the whole burden onto the concrete product core `RankNode r` — a structure with a sign and
`r` factors, along which a correct `rank descent` `r \to r-1 \to \dots \to 1` runs. The logic of the descent
is sound; what remained open were the stitching nodes (extensionality on residual ranks, finiteness of `ProdSig` against
the pigeonhole).

Before continuing to storm these nodes head-on, let us take a step sideways and see *onto
what exactly* our rank apparatus (rank — the "height" of a state, strictly decreasing along descent steps;
see the [glossary](GLOSSARY.md)) maps in classical analytic number theory. The answer will turn out to be
unexpectedly precise: the dynamics of the sign under rank descent is literally the sign dynamics of the **Liouville
function**, and its balance is equivalent to the Riemann Hypothesis.

## The idea of this branch: take a ready-made equivalent of RH

The `RiemannBranch` line (ch. 28) went straight from "engine \Rightarrow zeros of \zeta" and ran into the
analytic bridge `EngineBridge`, comparable in difficulty to RH itself. Here we proceed differently.
It is natural to suppose: instead of building our own bridge to the zeros of the zeta function, take a **ready-made
arithmetic statement equivalent to RH** and decompose *it* within our theory. Then its
truth automatically yields RH — all the analysis is already packed into the known equivalence, and what remains
for us is a purely arithmetic goal.

We choose the **Liouville equivalence**. It is convenient because it speaks of a sign that depends exactly on the number
of prime factors — and the number of prime factors is precisely our rank.

## Definitions

Let us introduce the Liouville function and its summatory function.

> **Definition (Liouville function).** For $n \ge 1$
> $$\lambda(n) \;=\; (-1)^{\Omega(n)},$$
> where $\Omega(n)$ is the number of prime factors of $n$ *counted with multiplicity* (for instance $\Omega(12)=\Omega(2^2\cdot 3)=3$).
> In mathlib this is `ArithmeticFunction.liouville`, and $\Omega(n)$ is `cardFactors n`.

> **Definition (summatory function).** $$L(x) \;=\; \sum_{n=1}^{x} \lambda(n).$$
> In Lean: `def L (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, liouville n`.

The function $\lambda$ is completely multiplicative and takes values $\pm 1$; $L(x)$ is an alternating
sum, the accumulated imbalance between the numbers with an even and an odd number of prime factors up to $x$.

> **Definition (Liouville-bound).** $$\texttt{LiouvilleBound} \;:\!\!\iff\; \forall\,\varepsilon>0\ \exists\,C>0\ \forall x:\quad |L(x)| \le C\,x^{1/2+\varepsilon}.$$
> In Lean this is `LiouvilleBound : Prop`. In substance: a sum of $\pm 1$ of length $x$ behaves like
> a random walk — growing no faster than $\sqrt{x}$ (up to $x^\varepsilon$), not linearly.

> **The Riemann Hypothesis — from mathlib.** Following the principle "everything external comes from mathlib", `RiemannHypothesis` here is
> the **official mathlib formulation** (a quantifier over all zeros of `riemannZeta`, excluding the trivial ones
> `-2(n+1)` and `s = 1`), and *not* a home-made `def`. The same goal as in `RiemannBranch`.

## The classical bridge: `LiouvilleBound \iff RH`

The supporting fact is a well-known theorem of analytic number theory (mathlib does not yet have it, so we
introduce it as an **explicit input-bridge** — an input, or gate, is an honestly named unproven statement
(see the [glossary](GLOSSARY.md)) — rather than postulating RH):

> **Definition-input (the Liouville bridge $H_L$).** $$\texttt{LiouvilleRHBridge} \;:\!\!\iff\; \bigl(\texttt{LiouvilleBound} \iff \texttt{RiemannHypothesis}\bigr).$$
> In Lean — `LiouvilleRHBridge : Prop`.

This is the classical equivalence: the bound $L(x)=O(x^{1/2+\varepsilon})$ is equivalent to the absence of zeros
of $\zeta$ to the right of the line $\mathrm{Re}=1/2$. We do *not* prove it here and do not pass it off as our own — we make
the branch conditional on it. This is more honest than postulating RH: what is postulated is merely a known, recognized
fact about the connection between two objects, not the thing sought.

Given the bridge, the branch closes by a trivial implication.

> **Theorem** (`riemann_of_liouville_bound`)**.** If the bridge `LiouvilleRHBridge` is given and
> `LiouvilleBound` is proven, then `RiemannHypothesis`.
> $$\texttt{LiouvilleRHBridge} \;\wedge\; \texttt{LiouvilleBound} \;\Rightarrow\; \texttt{RiemannHypothesis}.$$
> The Lean proof is a single line, `bridge.mp hbound`: all the analysis is isolated in the bridge,
> and the arithmetic (`LiouvilleBound`) is the only substantive goal.

Thus the branch's only open arithmetic node is `LiouvilleBound`. It is precisely this node that our
rank apparatus must decompose. Let us show *why* it fits our theory at all.

## Why this is our apparatus: $\lambda = (-1)^{\text{rank}}$

The key observation is a coincidence of objects. The number of prime factors $\Omega(n)=$ `cardFactors n` is
exactly **our rank** `RankNode`: with us, `RankNode r` has `factors : Fin r → ℕ`, so the rank $r$ is
the node's number of factors. From this, instantly:

> **Theorem** (`liouville_eq_neg_one_pow_rank`)**.** For $n\ne 0$
> $$\lambda(n) \;=\; (-1)^{\mathrm{cardFactors} n} \;=\; (-1)^{\text{rank}}.$$
> In Lean this is simply `liouville_apply hn`: the Liouville sign is the parity of the rank.

So $L(x)$ is the accumulated sum of the signs $(-1)^{\text{rank}}$ over all nodes up to $x$. `LiouvilleBound`
says that this sum is small (of order $\sqrt{x}$): **the signs of our rank are balanced**.

## The sign flip under `deleteFactor`: descent = the sign dynamics of Liouville

The second observation ties our **descent step** to the change of sign. With us, `deleteFactor` lowers the rank
$r\to r-1$ by removing one role. In terms of numbers this is the passage from $n=p\cdot m$ to $m$ (stripping one
prime factor). What happens to the sign?

> **Theorem** (`liouville_flip_of_mul_prime`)**.** For a prime $p$ and $m\ne 0$
> $$\lambda(p\cdot m) \;=\; -\,\lambda(m).$$
> Proof (Lean): $\mathrm{cardFactors}(p\cdot m)=\mathrm{cardFactors} m + 1$
> (via `cardFactors_mul` and `cardFactors_apply_prime`), whence $(-1)^{\Omega(m)+1}=-(-1)^{\Omega(m)}$.

The meaning. Our `deleteFactor` (`RankNode (r+1) → RankNode r`, stripping one factor while keeping the same sign
field) at the level of numbers *flips* the Liouville sign. Hence **product-rank descent is exactly
the sign dynamics of $\lambda$**: every rank-descent step turns $\lambda$ into its opposite. The descent
$r\to r-1\to\dots\to 1$, which in chapters 30–31 drives the collision toward the rank-1 base, in arithmetic language
is a sequence of Liouville sign flips along the factorization.

> **Note.** Here two different "descents" meet on one object. Our dynamical descent is
> a downward walk along a single lineage ($p\cdot m \to m$), and it is strictly sign-alternating. The sum
> $L(x)$, on the other hand, runs over *all* $n\le x$ horizontally. The connection between the "vertical" flip and the
> "horizontal" balance is precisely the substantive work the rank apparatus must
> perform: to show that the pairwise flips along lineages force the horizontal sum
> to cancel down to $O(\sqrt{x})$.

## Numbers: $|L(x)|/\sqrt{x}$ is bounded

What exactly must be proven is best seen in normalized form. `LiouvilleBound` is equivalent to the statement that the
quantity
$$\frac{|L(x)|}{\sqrt{x}}$$
remains bounded (up to the correction $x^{\varepsilon}$). Numerically $L(x)$ does indeed behave
like a $\sqrt{x}$-sized swing: the signs $(-1)^{\text{rank}}$ split almost evenly between even and odd
rank, and the accumulated imbalance never leaves the square-root scale. This is exactly the `separating scale`
$\sqrt{x}$ which in chapter 30 separated the legal layer; here it surfaces as the growth scale of $L$.

> **Note (historical caution).** The stronger claim $L(x)\le 0$ for $x\ge 2$ — Pólya's
> conjecture — is **refuted** (the first counterexample near $x\approx 906{,}150{,}257$). Therefore our goal is
> precisely the bound $O(x^{1/2+\varepsilon})$, not a definite sign of $L$: the rank balance must be
> statistical (the sum is small), not pointwise (the sign is fixed). This matters: our descent
> strictly flips the sign along a lineage, but the horizontal balance is probabilistic, and the two must not
> be confused.

## Honestly: `LiouvilleBound \equiv RH` is the parity wall

Now let us say plainly where the wall is, and not pass the reduction off as a proof. We have *not* proven
`LiouvilleBound`. We have shown only that this equivalent of RH is expressible in our language and that our operation
`deleteFactor` governs exactly the sign whose sum must be bounded.

The essence of the difficulty is **parity**. The Liouville sign $\lambda(n)=(-1)^{\Omega(n)}$ is the parity of
$\Omega(n)$, that is, the parity of the rank. The bound $L(x)=O(x^{1/2+\varepsilon})$ asserts that this parity
is distributed almost uniformly (numbers with an even and an odd number of factors occur almost equally
often, with a square-root fluctuation).

This is the classical **parity wall**: control of the parity of $\Omega$ is a
well-known obstruction, inaccessible to sieve methods and, in substance, equivalent to RH itself.

**Conclusion.** Our rank apparatus supplies *vertical* information (one flip per one stripped factor), but `LiouvilleBound`
demands a *horizontal* statistical balance of parities over all $n\le x$. The passage from the first to the
second is exactly the unresolved node.

## Conjecture and a plan for closing the `LiouvilleBound` node

Let us state the open node explicitly.

> **Conjecture (rank balance).** The sign dynamics of the descent (`liouville_flip_of_mul_prime`) combined with
> our `no_infinite_descent` (the impossibility of a perpetual engine, ch. 28) entails a statistical balance
> of rank parities, that is, `LiouvilleBound`.

The closing plan, step by step, with an honest assessment of each:

1. **Pair the lineages into flip-pairs.** Every node of rank $r$, via `deleteFactor`, produces
   a parent of rank $r-1$ with opposite $\lambda$. The idea: organize the contribution to $L(x)$ as a sum over
   pairs $(m,\ p\cdot m)$ in which the two terms cancel. The difficulty: the pairs leave the segment $[1,x]$
   asymmetrically (boundary effects of order $\sqrt{x}$) — and this is exactly where the square-root
   scale, and not a linear one, must arise.
2. **Tie the flip balance to the impossibility of the engine.** If the rank parities were
   systematically skewed (for instance $L(x)\gg \sqrt{x}$), that would give a "free" directed
   pumping of mass along the descent — the very perpetual engine forbidden by `no_infinite_descent`
   (EPMI — the impossibility core for the perpetual engine, see the [glossary](GLOSSARY.md)). This is exactly the logic of the `RiemannBranch` line, but expressed through the Liouville sign rather than through the
   height $H$. The task is to make this implication precise: `parity skew \Rightarrow Engine`.
3. **Fold it into the bound.** From the boundedness of the skew — derive $O(x^{1/2+\varepsilon})$.

> **Note.** Step 2 is the heart of the plan and, at the same time, the boundary of honesty. It repeats the structure of
> `EngineBridge` (ch. 28) on a new object: "asymmetry \Rightarrow engine". In all likelihood, its
> difficulty is comparable to RH itself — and that is precisely what it means to have run into the parity wall rather than gone around it.
> We record this as a conjecture, not a theorem: `Step00` remains a `sorry`. The progress is real —
> the node's exact arithmetic face has been found (the Liouville sign = the parity of the rank), along with the exact operation
> governing it (`deleteFactor` = flip) — but the balance itself has not been presented.

## Conclusion

The Liouville branch gives the shortest honest formulation of RH in our theory: we take the ready-made
equivalence `LiouvilleBound \iff RH` (the bridge `LiouvilleRHBridge`), and RH reduces to a single
arithmetic goal — the bound $|L(x)|=O(x^{1/2+\varepsilon})$ (`riemann_of_liouville_bound`).

This goal
fits our apparatus perfectly: $\lambda=(-1)^{\text{rank}}$ (`liouville_eq_neg_one_pow_rank`), and our
`deleteFactor` flips the sign (`liouville_flip_of_mul_prime`), so that product-rank descent is
literally the sign dynamics of Liouville.

But `LiouvilleBound` is not proven: it is the control of the parity of $\Omega$,
the classical parity wall, and the passage from the vertical flip to the horizontal balance remains
an open conjecture (the plan runs through `no_infinite_descent`).

## Bridge to the next chapter

So we now have two independent inputs to RH — the analytic `EngineBridge` (ch. 28, via the zeros of
$\zeta$) and the arithmetic `LiouvilleBound` (this chapter, via the parity of the rank) — and both run into one
and the same wall, "asymmetry \Rightarrow engine", merely dressed differently.

In the next chapter we
return to the concrete product core and examine `ProductCore` in detail: how `RankNode`,
`coreSigOf`, and `deleteFactor` assemble into an honest descent `core_step_proved`, and exactly where (the stitching with
`deleteFactor` on residual ranks) an input remains — that is, we look at the same parity/extensionality wall
no longer through $\lambda$, but from inside the structure of the core itself.

<!--navbot-->

---

[← 30. Riemann: contraposition](30_RiemannBranch.md) · [Table of contents](00_Overview.md) · [32. The rank-parity node →](32_RankParityUnity.md)
<!--/navbot-->
