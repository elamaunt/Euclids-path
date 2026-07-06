# 10. Survivor means twin: the bridge to infinity

<!--navtop-->
[← 09. Factor-repeat rigidity](09_Cycle.md) · [Table of contents](00_Overview.md) · [11. The block core →](11_TwoTransport.md)
<!--/navtop-->



> Lean: `EuclidsPath/Engine/NonCover.lean` (`survivor_of_not_covered`, `infinite_of_unbounded_centers`);
> `EuclidsPath/Engine/TwoTransport.lean` (`prime_of_no_small_prime_factor`, `isTwinCenter_of_root_sieve`).

In the previous chapter [09](09_Cycle.md) we established the rigidity of a repeated divisor: if a prime `ℓ`
returns as a divisor at two centers, it divides their difference, so the hits of a single divisor are
rigidly periodic. This makes the total coverage by "bad" centers short and controllable.

Now we
gather the fruit: we show that as soon as the "bad" ones are strictly fewer than the carriers, a
*survivor* falls out of the block, and that the survivor is not merely a not-bad center but a genuine
twin center; from an unbounded supply of such centers we honestly, in a machine-verified way, derive
the infinitude of twin primes.

## Setup: three links of one bridge

The whole chapter is an examination of three lemmas, each elementary on its own, but together they
form a non-circular bridge from block combinatorics to the arithmetic goal of the programme. Let us
fix the basic definitions we rely on (step 00).

> **Definition 10.1** (twin center and `TwinLowers`). The index (center) form of a twin pair: a center $m$ defines a pair if both
> neighbours of the sextuple are prime. Formally `IsTwinCenter`:
> $$\mathrm{IsTwinCenter}(m) \;:\Longleftrightarrow\; (6m-1)\ \text{prime}\ \wedge\ (6m+1)\ \text{prime}.$$
> The target set is the lower members of the pairs, `TwinLowers` $= \{\,p \mid p\ \text{and}\ p+2\ \text{prime}\,\}$;
> the twin conjecture is exactly `TwinLowers.Infinite`.

The three links are these:

1. **Non-cover $\Rightarrow$ survivor** (`survivor_of_not_covered`): pure cardinality
   combinatorics of Finset.
2. **Sieve-to-the-root $\Rightarrow$ primality** (`prime_of_no_small_prime_factor`), whence
   **survivor $\Rightarrow$ twin** (`isTwinCenter_of_root_sieve`): elementary divisibility theory.
3. **Unboundedness of centers $\Rightarrow$ infinitude** (`infinite_of_unbounded_centers`):
   the order-theoretic passage from "arbitrarily high" to "infinite".

Let us take them in turn — what is proven, why exactly this way, and what each link means for the programme.

## Link 1. Non-cover yields a survivor

Suppose at some scale we have singled out a finite *carrier* set of centers $\Omega$ and a
finite set $\mathrm{bad}$ of "bad" centers — those that are certainly unfit (one of the sides
$6m\pm1$ is composite, because some forbidding divisor has covered it). The only thing we need
from the combinatorial core is a strict inequality of cardinalities.

> **Definition 10.2** (non-cover). We say that `bad` *does not cover* `Ω` if
> $$|\mathrm{bad}| < |\Omega|.$$

**Theorem 10.3** (`survivor_of_not_covered`). *If $|\mathrm{bad}| < |\Omega|$, then there exists
$m \in \Omega$ with $m \notin \mathrm{bad}$.*

$$ |\mathrm{bad}| < |\Omega| \;\Longrightarrow\; \exists\, m \in \Omega,\; m \notin \mathrm{bad}. \tag{10.1}$$

The proof is the pigeonhole principle in its purest form. By contradiction: if every $m \in \Omega$
lay in $\mathrm{bad}$, then $\Omega \subseteq \mathrm{bad}$, whence by monotonicity of cardinality
$|\Omega| \le |\mathrm{bad}|$ — contradicting the premise. In Lean this is exactly three moves: `by_contra`,
constructing the inclusion $\Omega \subseteq \mathrm{bad}$, then `Finset.card_le_card` and `omega`.

> **Note.** Observe that there is no analysis here, no distribution of primes, no analytic
> sieve — only `Finset` and the order on $\mathbb{N}$. This is a matter of principle: *all* the analytic
> difficulty of the programme has been pushed outside, into the estimation of two cardinalities ($|\Omega|$
> from below, $|\mathrm{bad}|$ from above). The mere existence of a survivor once the inequality holds
> costs us nothing.

Why exactly a strict inequality, and not, say, a positive density of survivors? Because for the
bridge to infinity (link 3), *one* survivor at each scale suffices. The frugality of the premise
is not a weakness but precision: we ask of the open core exactly as much as the conclusion carries, and
not a gram more. This makes the reduction maximally "cheap" in its input and therefore maximally honest.

## Link 2. The sieve to the root yields primality; a survivor is a twin

The survivor $m \notin \mathrm{bad}$ is a center neither of whose sides was covered by forbidding
divisors *within the scale*. To turn "not covered" into "prime", one needs the classical fact:
trial division up to the square root settles the question of primality.

**Theorem 10.4** (`prime_of_no_small_prime_factor`). *Let $n \ge 2$ and suppose no prime $p$ with
$p^2 \le n$ divides $n$. Then $n$ is prime.*

$$ n \ge 2 \;\wedge\; \bigl(\forall p\ \text{prime},\; p^2 \le n \Rightarrow p \nmid n\bigr)
\;\Longrightarrow\; n\ \text{prime}. \tag{10.2}$$

The proof goes by contradiction via the minimal prime divisor `Nat.minFac`. If $n$ is composite, then
$p := \mathrm{minFac}(n)$ is prime and divides $n$; by minimality $p \le n/p$, whence
$p \cdot p \le p \cdot (n/p) \le n$, that is, $p^2 \le n$. But then $p$ is a prime divisor of $n$ with
$p^2 \le n$, contradicting the premise. The key step in Lean is `Nat.minFac_le_div`
(the minimal divisor does not exceed the quotient), giving $p \le n/p$; from there `Nat.mul_le_mul` and
`Nat.mul_div_le` assemble the inequality $p^2 \le n$.

> **Note.** This is precisely why the sieve runs "to the root" and not all the way to $n$: the least divisor
> of a composite number is never greater than $\sqrt{n}$. Having checked all primes up to the root and found no divisor,
> we have exhausted every candidate — the number has nothing left to be but prime.

Applying this to both sides of the center, we obtain the target implication **survivor $\Rightarrow$ twin**.

**Theorem 10.5** (`isTwinCenter_of_root_sieve`). *If $6m-1 \ge 2$ and $6m+1 \ge 2$, and no prime up to
the root divides the corresponding side, then $m$ is a twin center:*

$$ \Bigl(\forall p\ \text{prime},\; p^2 \le 6m-1 \Rightarrow p \nmid (6m-1)\Bigr)
   \;\wedge\;
   \Bigl(\forall p\ \text{prime},\; p^2 \le 6m+1 \Rightarrow p \nmid (6m+1)\Bigr)
   \;\Longrightarrow\; \mathrm{IsTwinCenter}(m). \tag{10.3}$$

The proof is simply a pair of appeals to Theorem 10.4 (`prime_of_no_small_prime_factor`) for $6m-1$ and $6m+1$,
packaged into the conjunction `IsTwinCenter`. In substance this is exactly the claim "survivor means twin"
from the title: if the sieve of the engine's active part has reached the root without felling either side, both
sides are prime — and that is, by definition, a twin center.

> **Note.** This step fixes an important boundary of difficulty. The direction
> survivor $\Rightarrow$ twin is *elementary* — it contains no hypothesis at all. Hence
> all the substantive work of the programme is concentrated not here, but in guaranteeing
> that the survivor found by link 1 is genuinely "sieved to the root" (that is, `bad` accounts for
> *all* divisors up to $\sqrt{6m+1}$, not just the small ones). It is natural to suppose that this is
> the true carrier/bad condition; exactly this remains an open node and is passed on.

## Link 3. Unboundedness of centers yields infinitude

It remains to pass from "at every scale there is a twin center above $N$" to the unconditional
infinitude of the set `TwinLowers`.

**Theorem 10.6** (`infinite_of_unbounded_centers`). *If for every $N$ there is a center $m > N$ with
$\mathrm{IsTwinCenter}(m)$, then `TwinLowers` is infinite:*

$$ \bigl(\forall N,\ \exists m,\ N < m \wedge \mathrm{IsTwinCenter}(m)\bigr)
   \;\Longrightarrow\; \texttt{TwinLowers.Infinite}. \tag{10.4}$$

The proof is order-theoretic, via `Set.infinite_of_not_bddAbove`: a set of natural numbers is
infinite if and only if it is not bounded above. Unfolding `not_bddAbove_iff`,
for an arbitrary $N$ we take a center $m > N$ and present the witness $6m-1 \in \texttt{TwinLowers}$: it is
greater than $N$ (since $6m-1 > m > N$), and it is the lower member of a pair, for $6m-1$ is prime, and
$(6m-1)+2 = 6m+1$ is prime as well (both parts are supplied by `IsTwinCenter`). The identity $6m-1+2 = 6m+1$ and the bound
$6m-1 > N$ are closed off by `omega`.

> **Note.** A subtlety worth spelling out: the unboundedness of the *centers* $m$ automatically
> yields the unboundedness of the *lower members* $6m-1$, because $6m-1$ grows monotonically with $m$. Thus
> "an arbitrarily high center" turns into "an arbitrarily large element of `TwinLowers`", and for a
> set in $\mathbb{N}$ this suffices for infinitude. No counting or injection needs
> to be constructed — the absence of an upper bound is enough.

## What has been assembled and where the honest boundary runs

Let us assemble the three links into one conclusion. Suppose the block core: for every $N$ there exist finite
$\mathrm{carrier}$ and $\mathrm{bad}$ such that all carrier centers lie above $N$,
$|\mathrm{bad}| < |\mathrm{carrier}|$, and every carrier survivor is a twin center.

Then
Theorem 10.3 (`survivor_of_not_covered`) yields a survivor $m$, the block condition makes it a twin center above $N$
(this is `twin_center_of_block`), and Theorem 10.6 (`infinite_of_unbounded_centers`) turns the arbitrariness of $N$ into
`TwinLowers.Infinite`. This very assembly is `twin_prime_conjecture_of_blocks` — the subject of the
next chapter.

> **Note.** Let us stress what we did *not* do. We did not prove the twin conjecture. We showed
> that it follows from the block statement, and that all the "transit" steps (survivor, primality,
> infinitude) are machine-verified and elementary. We never pass this reduction off as a proof:
> what remains open is exactly the combinatorial core.

Let us state the open node explicitly.

> **Conjecture 10.7** (block non-cover, open). At arbitrarily large scales $N$ there exists a
> carrier set of centers $\mathrm{carrier}$ above $N$ for which the set of "bad" centers
> $\mathrm{bad}$ (those with one of the sides $6m\pm1$ having a divisor up to the root) is strictly smaller in
> cardinality: $|\mathrm{bad}| < |\mathrm{carrier}|$.

**Closing plan.** The node splits in two, and both parts are the subject of lines [12–18]:
a *lower* bound on $|\mathrm{carrier}|$ (density of carrier classes, `CarrierInput`) and an *upper* bound on
$|\mathrm{bad}|$ via the rigidity of repeated divisors from [09](09_Cycle.md) and the shortness of coverage from
[07](07_Squeeze.md)–[08](08_BK.md). From the observation of link 2 comes the added requirement of sieve completeness: `bad` must account for all
divisors up to $\sqrt{6m+1}$, otherwise the survivor is not guaranteed to be a twin.

As soon as both counts converge to a
strict inequality of cardinalities on at least one sequence of scales, all three links of this chapter
fire automatically and yield infinitude.

The three proven links are the bridge's ready reinforcement; what is lacking is the guarantee that the span
$|\mathrm{bad}| < |\mathrm{carrier}|$ bears the load at every scale.

How exactly this
reinforcement is assembled into a single machine-verified non-circular bridge "conjecture $\Longleftarrow$
block core" is the subject of the next chapter [11 TwoTransport](11_TwoTransport.md), where `twin_prime_conjecture_of_blocks`
isolates the open core and passes it further down the chain.

<!--navbot-->

---

[← 09. Factor-repeat rigidity](09_Cycle.md) · [Table of contents](00_Overview.md) · [11. The block core →](11_TwoTransport.md)
<!--/navbot-->
