# 09. Factor-repeat rigidity

<!--navtop-->
[← 08. Bounded cycle](08_BK.md) · [Table of contents](00_Overview.md) · [10. survivor ⇒ twin →](10_NonCover.md)
<!--/navtop-->



In [08. Bounded cycle](08_BK.md) we extracted from the pigeonhole (the boxes principle, see the [glossary](GLOSSARY.md)) on symmetric sums a bounded additive cycle: given enough mass of repeats, the divisors cannot sit arbitrarily — they close up into a finite additive structure.

It remains to understand *how rigidly* each individual repeat of a divisor is arranged — and here we pass from statistics (how many repeats are possible at all) to the geometry of a single repeat (where exactly it is forced to stand). The present chapter shows: the reuse of a divisor along a linear train is **rigid** — its positions are pinned to the step of an arithmetic progression, not free.

Lean source: `EuclidsPath/Engine/Cycle.lean` (`factor_repeat_rigidity`, `cross_side_fuel`).

## Setup: a divisor on a linear train

Let us recall the configuration inherited from the carrier of [02. Carrier of two](02_Carrier.md) and the descent of [04. Descent](04_Descent.md).

The centres of the engine (the engine is the forbidden infinite descent, see the [glossary](GLOSSARY.md)) along a single affine line form an arithmetic progression: the value "scanned" by a prime divisor at the point with coordinate $n$ has the form
$$
V(n) = N_0 + q\cdot n, \tag{9.1}
$$
where $N_0$ is the base offset (the shift of the line) and $q$ is the step of the train (the common multiplier of the coordinate). This is a linear train in the programme's terminology: a single line in $\mathbb{Z}$, parametrised by an integer $n$, along which we ask which primes divide it and at which centres.

It is natural to expect that a "large" divisor, once used, cannot repeat cheaply: if it divides $V(n)$ at two distinct centres, those centres are not free relative to each other. It is precisely this statement that we make precise.

> **Note.** The word "large" is made concrete here by the coprimality condition $\gcd(\ell,q)=1$. All active divisors in the programme's clean core exceed the threshold $A$ (see the boundary-exit of [06. No way back](06_NoBackward.md)), whereas the step $q$ is built from the already removed, "small" part; hence the coprimality of $\ell$ and $q$ is not an artificial assumption but a structural property of the configuration.

## Definition (repeat rigidity)

**Definition 9.1** (repeat rigidity). Let a prime (or, more broadly, an integer) $\ell$ divide the values of the train at two centres $n_1, n_2$:
$$
\ell \mid N_0 + q\,n_1,\qquad \ell \mid N_0 + q\,n_2,
$$
and let $\ell$ be coprime to the step, $\mathrm{IsCoprime}(\ell,q)$. We say that the repeat of the divisor $\ell$ is **rigid** if the difference of the centres is a multiple of $\ell$:
$$
\ell \mid (n_2 - n_1).
$$
In other words, the set of centres at which $\ell$ "fires" is itself an arithmetic progression with step $\ell$ in the coordinate $n$.

## The repeat-rigidity theorem

**Theorem 9.2** (`factor_repeat_rigidity`). For integers $\ell, q, N_0, n_1, n_2$
$$
\ell \mid N_0 + q\,n_1 \ \wedge\ \ell \mid N_0 + q\,n_2 \ \wedge\ \mathrm{IsCoprime}(\ell,q)
\ \Longrightarrow\ \ell \mid (n_2 - n_1). \tag{9.2}
$$

*Walking through the proof.* It is elementary and fully constructive; in Lean it takes three lines. Subtracting one divisibility condition from the other, we find that $\ell$ divides the difference of the train's values, while the base offset $N_0$ cancels:
$$
(N_0 + q\,n_2) - (N_0 + q\,n_1) = q\,(n_2 - n_1),
$$
whence $\ell \mid q\,(n_2 - n_1)$. Now coprimality goes to work: $\ell$ divides the product $q\cdot(n_2-n_1)$ but shares no factors with $q$, so the entire "divisibility" is carried over to the second factor — $\ell \mid (n_2 - n_1)$. In Lean this step is exactly `hcop.dvd_of_dvd_mul_left hd` (Euclid's lemma in `IsCoprime` form).

*Why this is true.* The key is the cancellation of $N_0$ under subtraction. The linearity of the train means that the divisibility $\ell \mid V(n)$ is a condition on $n$ modulo $\ell$: $q\,n \equiv -N_0 \pmod{\ell}$. Since $q$ is invertible modulo $\ell$ (coprimality), this equation has a *unique* residue class of solutions $n \bmod \ell$. Two solutions $n_1, n_2$ therefore lie in the same class — their difference is a multiple of $\ell$. The condition $\gcd(\ell,q)=1$ is not a technicality here: without it $q$ is non-invertible, the class of solutions may be empty or "smeared", and rigidity collapses.

*What it means.* A large divisor "pins" its repeats to the lattice of step $\ell$. On a segment of the train of length $L$ (the coordinate $n$ ranging over an interval of length $L$), a prime $\ell > A$ can repeat at most $\lfloor L/\ell\rfloor + 1$ times. Divisibility thus becomes a *countable* resource: the larger the divisor, the more rarely it can return. This is the fuel-law in its pure form — the "fuel" of a repeat is spent in proportion to the divisor's size.

> **Note.** Rigidity explains why the ban on "perpetual repetition" from [08. Bounded cycle](08_BK.md) closes up. BK bounds the *number* of repeats through the additive cycle; Theorem 9.2 (`factor_repeat_rigidity`) constrains their *placement* — every repeat of a large divisor stands on a fixed step $\ell$. Together with the cubic squeeze of [07. Short train](07_Squeeze.md), which pinches the very length of a valid train segment down to $L < \sqrt{A/72}$, this makes the coverage by large divisors *finite and short*: a short segment, rare repeats, a countable budget.

## Transport of the two between sides (cross-side fuel)

Repeat rigidity describes a single linear train. But a link of the engine is the Euclidean equation $XY - ZW = 2$ (the rank-$(3,3)$ form `abv + 2 = qrs`, see [05. Irreversibility](05_Irreversibility.md)), which has two sides, and the constant $+2$ lives precisely in the coupling between them. The second law of this chapter tracks how divisibility is transported through the two from one side of the star rectangle to the opposite one.

**Definition 9.3** (fuel-law, divisibility form). Consider a prime $p$ dividing linear forms on opposite sides, differing by exactly the constant $2$ (the legacy of the $+2$ of the det-form). In its pure form: suppose that for parameters $a, c, \alpha, \beta$ we have
$$
p \mid a\,\alpha + c,\qquad p \mid a\,\beta + c - 2.
$$
The first is $p$ landing on the side $\alpha$; the second, on the opposite side $\beta$, shifted by $-2$ by the two of the equation.

**Theorem 9.4** (`cross_side_fuel`). Under these conditions
$$
p \mid \bigl(a\,(\beta - \alpha) - 2\bigr). \tag{9.3}
$$

*Walking through the proof.* The mechanics are the same as for rigidity: subtract and cancel the free term $c$. Namely,
$$
(a\,\beta + c - 2) - (a\,\alpha + c) = a\,(\beta - \alpha) - 2,
$$
and the left-hand side is divisible by $p$ as a difference of two multiples of $p$. In Lean this is `dvd_sub h2 h1`, rewritten via the `ring` identity. No additional coprimality is needed here — the two does not cancel and remains explicitly on the right-hand side.

*Why this is true, and what it means.* Unlike Theorem 9.2 (`factor_repeat_rigidity`), where after cancellation a "clean" $q\,(n_2-n_1)$ remained and the Euclidean transfer applied, here after cancelling $c$ a hard trace of $-2$ remains. Hence Theorem 9.4 (`cross_side_fuel`) yields not the congruence $a(\beta-\alpha)\equiv 0$ but the *shifted* congruence
$$
a\,(\beta - \alpha) \equiv 2 \pmod{p}.
$$
The two of the Euclidean equation "travels" between the sides: for a divisor $p$ to stand on both sides of the star rectangle at once, it must reconcile the cross-side difference $\beta-\alpha$ with $2/a \bmod p$. This is the transport of the $+2$ fuel across the sides (the transport mechanism is dissected in detail in [11. Block core](11_TwoTransport.md) and synthesised as "the first law — conservation of the two").

**Conclusion.** Geometrically (see the doc-string in `Cycle.lean`) this is a form of the condition $p \mid 2 + a\,q\,(\beta-\alpha)$ on the det-form of the star rectangle: two opposite sides cannot "catch" the same $p$ independently — their positions are tied through the two.

> **Note.** Both theorems — 9.2 and 9.4 — share the same elementary heart: "subtract and cancel the free term". The difference lies in the remainder: for Theorem 9.2 (`factor_repeat_rigidity`) it is zero (after which coprimality finishes the job), for Theorem 9.4 (`cross_side_fuel`) it equals $-2$ (and stays visible as the transport of the two). The first constrains a repeat *within* a side; the second ties *different* sides together. Both are about the fact that divisibility on a linear structure is not free but pinned to the step and to the constant $+2$.

## Status

- 🟢 **Rigorous and compiler-checked.** Both theorems — Theorem 9.2 (`factor_repeat_rigidity`) and Theorem 9.4 (`cross_side_fuel`) — are proven in `EuclidsPath/Engine/Cycle.lean` elementarily (divisibility + coprimality), with no `sorry` and no non-standard axioms. These are solid tool-lemmas: rigidity of a repeat's placement and the cross-side congruence $a(\beta-\alpha)\equiv 2$.
- 🔴 **Open (at the level of application).** The local rigidity of a single divisor does not by itself yield the global non-cover: it remains to show that the total budget of all large divisors on a short train is strictly less than the carrier. The explicit **hypothesis**: at every scale, the number of centres covered by old/large divisors is bounded above by $\sum_{\ell > A} (\lfloor L/\ell\rfloor + 1)$, and this sum over a short segment ($L < \sqrt{A/72}$ from [07. Short train](07_Squeeze.md)) stays below the size of the carrier. **Closure plan**: join the counting estimate of repeats (this chapter) with the carrier estimate and the bad-upper of [10. survivor ⇒ twin](10_NonCover.md), passing them on to the block bridge of [11. Block core](11_TwoTransport.md). We do NOT pass rigidity off as non-cover here — it merely makes the coverage budget finite and countable, rather than infinite.

## Bridge to the next chapter

So: the repeat of a large divisor is rigid, and the two is rigidly transported between the sides — the coverage of the train by old divisors is **finite and short**. It remains to take the decisive step from "the coverage is small" to "there is an uncovered centre — and it is a twin".

In [10. survivor ⇒ twin](10_NonCover.md) we will show: if a block has strictly fewer "bad" centres than the carrier, a survivor remains, and the sieve-to-the-root turns it into a twin centre (`survivor_of_not_covered`, `prime_of_no_small_prime_factor`); and if such twin centres are unbounded in $N$, the twin primes are infinite in number (`infinite_of_unbounded_centers`). This is the bridge from the finiteness of the coverage — to the infinitude of twins.

<!--navbot-->

---

[← 08. Bounded cycle](08_BK.md) · [Table of contents](00_Overview.md) · [10. survivor ⇒ twin →](10_NonCover.md)
<!--/navbot-->
