# Descent and the boundary law

<!--navtop-->
[← 03. Conservation of the two](03_TwoGap.md) · [Table of contents](00_Overview.md) · [05. Irreversibility →](05_Irreversibility.md)
<!--/navtop-->



> Lean source: `EuclidsPath/Engine/Descent.lean`
> Theorems of the chapter: `two_carry_opposite`, `no_small_divisor`, `obstruction_on_opposite`.

In the previous chapter we established the carrier of two: the sides of a twin centre `6m−1` and `6m+1`
differ by exactly `2`, so their common divisor divides that difference, and every prime `p>2`
divides at most one side. The two is what *separates* the sides.

Now we show where
that two goes when the engine — the forbidden infinite chain of strict descent (see the [glossary](GLOSSARY.md)) — takes a step: descent does not destroy the gap, it **carries** it over to the
opposite side of the descended centre. From this carry-over the boundary law is born —
the single divisibility by which the purity of a descended state can be violated.

## The setup: pure descent and height

Let us recall the working configuration. A centre `m` lies in the pure core `Ω_A` when both of its sides
factor into primes strictly greater than the threshold `A`. Suppose one side — say,
`6m+σ` with `σ∈{±1}` — turns out to be *composite* within the layer and carries an active factor `a>A`:
$$6m+\sigma = a\,(6n+\varepsilon),\qquad a>A,\ \varepsilon\in\{-1,+1\}.\tag{4.1}$$
Removing the active factor `a`, we declare the descended centre to be that `n` for which the remainder
`6n+ε` equals the second bracket. This is one tick of the engine: from the scale `m` we pass to the
scale `n`.

The first observation is strict descent in height (the height is the rank of a state, the engine's finite fuel; see the [glossary](GLOSSARY.md)). Since `a>A` and `6m+σ = a(6n+ε)`, the factor `a`
eats up at least a factor of `A` from the magnitude of the side, and hence from the centre:
$$n < \frac{m}{A}.\tag{4.2}$$

> **Note.** By the height `H` we mean the centre `m` itself (equivalently, the magnitude of the side on
> a logarithmic scale). The strict inequality `n<m/A` is not an "on average" estimate but pointwise
> divisibility arithmetic: if `a·(6n+ε) = 6m+σ` and `a>A`, then `6n+ε ≤ (6m+σ)/A`. It is exactly this
> inequality that yields irreversibility in the next chapter: descent cannot last forever, for
> `m/A^t<1` for large `t`, and a positive integer centre `<1` is impossible.

## Carrying the two to the opposite side

Having descended to `n`, we obtain a new centre with two sides: `6n+ε` (the bracket that remained
after removing `a`) and the opposite one, `6n−ε`. The key identity of the chapter says that the
opposite side differs from the remaining one *by exactly twice the sign* — that is, by the very
two that carries the gap.

For brevity, introduce `U := 6n+ε` — the remainder side of the descended centre.

**Theorem 4.1** (`two_carry_opposite`). If $U = 6n+\varepsilon$, then
$$6n-\varepsilon = U - 2\varepsilon.\tag{4.3}$$

The proof in Lean takes one line (`linear_combination -hU`) and is entirely algebraic:
$$6n-\varepsilon = (6n+\varepsilon) - 2\varepsilon = U - 2\varepsilon.$$

Substantively this means the following. The gap `2` between the sides of a twin is *invariant* under
descent: it neither appears nor disappears, but merely changes its carrier. There was a difference `(6n+ε)−(6n−ε)=2ε`
between the sides of the descended centre — and it reproduces exactly the doubled sign `2ε`. We
say that the two has been "carried forward": the active factor `a` is taken away from the product side,
while the separating two migrates to the opposite side `U−2ε`.

> **Note.** The sign `ε` is the parity "spin" of the remainder side (`+1` for the upper bracket, `−1`
> for the lower). The magnitude of the carry, `2ε∈{−2,+2}`, agrees in absolute value with the carrier of
> two from the previous chapter. This is how descent is stitched to the carrier: what separates the sides
> above (`gcd ∣ 2`) is the same thing that is carried below (`U−2ε`).

## A small prime does not spoil the product side

Now let us ask: what could violate the purity of the descended centre at all? Purity requires that both of
its sides consist of primes `>A`. The remainder side `U` is inherited from the factorization of `6m+σ`, and its
factors are greater than `A` by construction — removing the active `a>A` leaves a remainder `U=b·v` of primes
`b,v>A`. So the danger can come only from an *old small* prime `p≤A`. The next
statement excludes such a prime from the product side.

**Theorem 4.2** (`no_small_divisor`). Let $b, v$ be primes with $A < b$, $A < v$, and let $p$ be a prime with $p \le A$. Then
$$p \nmid (b\cdot v).\tag{4.4}$$

The proof is direct (in Lean, via `Nat.Prime.dvd_mul` and `Nat.prime_dvd_prime_iff_eq`): if
`p ∣ b·v`, then by Euclid's lemma `p∣b` or `p∣v`; but a prime dividing a prime means
equality, `p=b` or `p=v`, contradicting `p≤A<b` and `p≤A<v` (in Lean both cases are closed by
`omega`).

The point of this lemma is a separation of responsibilities. The product side `U=b·v` *cannot* be
spoiled by any old prime `p≤A`: its factors lie above the threshold, out of the reach of small
primes. Therefore, if the purity of the descended centre is nevertheless violated by some `p≤A`, the culprit is not
the remainder side but *only* the opposite side.

> **Note.** What matters here is not merely the "two-factor" shape `U=b·v`, but precisely that both factors
> have passed the `>A` filter. This is guaranteed by pedigree: `U` is a bracket from the factorization of the original
> side, all of whose primes are greater than `A` by the definition of `Ω_A`. In this programme a small prime
> is never a defect of the *original* centre — it can only appear as the absorbing exit
> of the descended centre from the pure core.

## The boundary law: the obstruction lives on the opposite side

Let us assemble the two previous observations. The descended centre has a product side `sideProd = U`,
which small primes do not touch, and the opposite side `sideOpp = U−2ε` — the carried
two. By an obstruction we mean the event "some prime `p` divides one of the sides" (an exit to the boundary
of the pure core, a boundary-exit). The following theorem shows that when `p∤U` this disjunction
collapses into a *single* divisibility.

**Theorem 4.3** (`obstruction_on_opposite`). Let $\mathit{sideProd} = U$, $\mathit{sideOpp} = U - 2\varepsilon$ and $p \nmid U$. Then
$$\bigl(p \mid \mathit{sideProd} \ \lor\ p \mid \mathit{sideOpp}\bigr)\ \Longleftrightarrow\ p \mid \mathit{sideOpp}.\tag{4.5}$$

The proof is elementary. Left to right: if `p∣sideProd`, then `p∣U` (since `sideProd=U`) —
a contradiction with `p∤U`; so `p∣sideOpp` remains. Right to left is trivial (the right disjunct). In
Lean this is an `rintro` case split with `absurd h hpU` in the impossible branch.

Combining with Theorem 4.2 (`no_small_divisor`) (which yields exactly `p∤U` for a small `p≤A`, since `U=b·v` with
`b,v>A`) and with Theorem 4.1 (`two_carry_opposite`) (which identifies `sideOpp = U−2ε` as the carried two),
we obtain the programme's **boundary law**:

$$\boxed{\ p\mid 6n-\varepsilon\ }\qquad(\text{equivalently } p\mid U-2\varepsilon).\tag{4.6}$$

**Conclusion.** The only divisibility capable of knocking the descended centre out of the pure core is the divisibility
of the *opposite side* `6n−ε` by an old prime `p≤A`. The obstruction cannot sit on the
product side: there all factors are above the threshold. All responsibility for the exit to the boundary is
concentrated in a single point — on the carried two.

> **Note.** Hence the name "boundary law". The dichotomy of pure descent
> is utterly simple: either the descended centre stays in `Ω_A` and the engine makes its next tick, or
> it exits to the boundary — and then the cause is strictly unique, `p∣6n−ε`. There are no other exit
> mechanisms. This is a reduction of the entire combinatorics of the obstruction to a single arithmetic divisibility,
> tied to the carry-over of the two.

## What is proven and what it means

Three machine-checked theorems — Theorem 4.1 (`two_carry_opposite`), Theorem 4.2 (`no_small_divisor`),
and Theorem 4.3 (`obstruction_on_opposite`) — together establish that one tick of the engine works as follows:

1. **strict descent in height** — from `6m+σ=a(6n+ε)` with an active `a>A` it follows that `n<m/A`
   (divisibility arithmetic, with no distributional assumptions whatsoever);
2. **conservation of the gap** — the two is not lost but carried over: $6n-\varepsilon = U-2\varepsilon$ (Theorem 4.1);
3. **localization of the obstruction** — a small prime does not spoil the product side (Theorem 4.2), so the boundary
   is reached exactly when $p\mid 6n-\varepsilon$ (Theorem 4.3, equation (4.6)).

The whole proof is elementary — ring arithmetic and divisibility; no analysis, no distribution, no sieve. This
matters methodologically: descent and the boundary law are atomic facts on which the entire subsequent
construction stands, and they depend on no open conjecture.

> **Note (what remains open here).** The impossibility of infinite *local* pure
> descent is proven (next chapter). But a finite tree of descents, where each branch ends in a boundary
> leaf (`p∣6n−ε`), is combinatorially possible: the local law does not give a global non-cover. This is
> the honest boundary of the present chapter — it closes the *mechanics* of a single tick, but not the global structure
> of the tree. The plan for closing the global node unfolds later (multi-rank non-cover, and in the limit
> — the rank-1 shifted-neighbour obstruction `p∣a−2ε`, a direct descendant of the boundary law).

So we now have a precisely described tick: the active factor departs, the height strictly falls, the two is
carried forward, and any exit to the boundary is recognized by a single divisibility of the opposite
side. The strict inequality `n<m/A` from the first point is already an arrow: the scale can only
shrink, and every tick multiplies it by a factor smaller than `1/A`. In the next chapter we will turn
this observation into a law of irreversibility — showing that Euclid's engine can neither return
nor run forever.

<!--navbot-->

---

[← 03. Conservation of the two](03_TwoGap.md) · [Table of contents](00_Overview.md) · [05. Irreversibility →](05_Irreversibility.md)
<!--/navbot-->
