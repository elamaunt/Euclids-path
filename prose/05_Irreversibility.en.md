# The second law: irreversibility and the arrow of time

<!--navtop-->
[← 04. Descent and the boundary-law](04_Descent.md) · [Table of contents](00_Overview.md) · [06. No way back →](06_NoBackward.md)
<!--/navtop-->



> Lean source: `EuclidsPath/Engine/Irreversibility.lean` (on top of `EuclidsPath/Engine/EPMI.lean`).
> Key theorems of the chapter: `engine_never_returns`, `no_infinite_engine_descent`,
> `fuel_ascent_strictMono`, `turned_engine_halts`. No analysis, no distribution, no sieve —
> only the order-completeness of `ℕ`.

## Where we came from

In the previous chapter [04 Descent] we established the mechanics of a *single* engine step: if for a
centre `m∈Ω_A` one side of the pair `(6m-1,\,6m+1)` is composite and is cracked open by an active
factor `a>A`, then the height drops strictly — the new centre `n` satisfies `A\cdot n < m`, and the two
is carried over to the opposite side via the boundary-law. Back then we regarded the descent as a
*local* event: one turn of the wheel, one push downward.

Now we climb one level higher and ask about the
*global* dynamics: what happens to the engine's trajectory as a whole? The answer is two statements
which together form the second law of thermodynamics for Euclid's engine: **irreversibility** (the
engine does not return) and **finiteness of descent** (the engine always halts).

Both halves are machine-proven, without a single axiom beyond the standard ones.

## Height as thermodynamic time

Let us recall the state model. The state of the engine is encoded entirely by a single natural number
— its *height*.

> **Definition 5.1** (height). To a state `S`, substantively corresponding to the centre `m` of the pair `(6m-1,\,6m+1)`,
> we assign the height `H(S) := m \in \mathbb{N}`. A trajectory of the engine is a sequence of
> heights `H : \mathbb{N} \to \mathbb{N}`, where the argument `t` plays the role of discrete time and `H(t)`
> is the state at moment `t`.

In Lean the state is formalized by the structure `State` with the single field `height : Nat`
(`EuclidsPath/Engine/EPMI.lean`); all the substantive richness of the pair is collapsed into this
scalar, because for the second law only *monotonicity in height* matters, not the arithmetic nature of
the centre.

One successful clean descent is a step that reduces the height by at least a factor of `A`.

> **Definition 5.2** (descent step). For `A,h,h' \in \mathbb{N}`
> $$\mathrm{DescentStep}(A,h,h') \;:\Longleftrightarrow\; A\cdot h' < h. \tag{5.1}$$
> Substantively: from a state of height `h` the engine passes to a state of height `h'`, with
> `A\cdot h' < h`, that is, the height falls by at least a factor of `A` (`Engine/EPMI`).

The key lemma on which everything else rests is that for `A\ge 1` such a step *strictly* lowers the
height.

> **Lemma 5.3** (`descent_strict`, `Engine/EPMI`). If `1 \le A` and `\mathrm{DescentStep}(A,h,h')`, then
> `h' < h`.
>
> **Why.** For `A\ge 1` we have `h' \le A\cdot h'` (multiplying by a positive factor does not
> decrease), and by the definition of the step `A\cdot h' < h`; the chain `h' \le A\cdot h' < h` gives `h' < h`.

It is precisely the strictness `h' < h`, not merely `A\cdot h' < h`, that turns height into an arrow
of time: every step of the engine irreversibly shifts it into a new, lower state.

## Irreversibility: the engine will not turn back

The local strictness ("every next step is lower than the previous one") integrates into a global
statement about the whole trajectory.

> **Theorem 5.4** (`engine_never_returns`). Let `1 \le A` and let `H : \mathbb{N} \to \mathbb{N}` be a trajectory
> in which every step is a successful descent: `\forall t,\; \mathrm{DescentStep}(A,\,H(t),\,H(t+1))`.
> Then `H` is **strictly antitone**:
> $$\mathrm{StrictAnti}\,H \;:\Longleftrightarrow\; \bigl(\forall s\,t,\; s < t \Rightarrow H(t) < H(s)\bigr). \tag{5.2}$$

**What is proven.** Not merely that "adjacent states decrease", but that *any* later state is strictly
lower than *any* earlier one. The engine never returns to any of the states already passed
(the higher ones) — neither on the next step, nor a million steps later.

**Why this is true.** The proof in Lean is a single line: `strictAnti_nat_of_succ_lt` lifts the
*local* strict decrease `H(n+1) < H(n)` (which Lemma 5.3 (`descent_strict`) supplies for every `n`) to
*global* strict antitonicity. This is a standard fact about `\mathbb{N}`: decrease on every
unit step is equivalent to decrease over any interval, because the order on the natural numbers is
discrete and transitive. Substantively: irreversibility at a single step, accumulated over all steps,
is irreversibility of the trajectory.

**What this means.** The height `H` is the coordinate of thermodynamic time, and `\mathrm{StrictAnti}\,H`
is the formal expression of the *arrow of time*: the direction "down in height" is physically
distinguished, and there is no travel back along it. Euclid's engine, once it has set off on a descent,
cannot restore a previous state — exactly as a closed system cannot spontaneously lower its entropy.

> **Note.** `engine_never_returns` does not assume the *existence* of an infinite trajectory — it
> merely describes a property of *any* chain of successful descents, should one be given. Whether such
> a chain can be infinite is the subject of the next section, and the answer is negative. The two facts
> are independent in formulation, but together they close the second law.

## Finiteness of descent: the engine always halts

The second half of the law asserts that there is no infinite descent. This is the abstract form of
the impossibility of a perpetual engine (EPMI — the programme's core, proven on the bare Lean kernel; see the [glossary](GLOSSARY.md)), proven in the neighbouring module, and here we apply it to pure
monotonicity.

> **Theorem 5.5** (`no_infinite_engine_descent`). There is no strictly decreasing sequence of
> natural numbers: if `f : \mathbb{N} \to \mathbb{N}` and `\mathrm{StrictAnti}\,f`, then `\bot`
> (contradiction).

**Why this is true.** A strictly decreasing `f` is a descent with parameter `A=1`: the condition `\mathrm{StrictAnti}\,f`
gives `f(t+1) < f(t)`, which is exactly `\mathrm{DescentStep}(1,\,f(t),\,f(t+1))` after `1\cdot h' = h'`.
Then the base theorem `no_infinite_descent` (`Engine/EPMI`) applies, whose proof is
pure order-completeness of `\mathbb{N}`: the quantity `f(t) + t` does not grow along the chain (each step
loses at least `1` in height and gains `1` in time), hence `f(t) + t \le f(0)` for all `t`; but
at `t = f(0)+1` this gives `f(t) + f(0) + 1 \le f(0)` — impossible.

Formally:
$$H(S_t) \;<\; \frac{H(S_0)}{A^{\,t}} \;<\; 1 \quad\text{for large } t,$$
while the height is a positive integer and cannot be less than `1`. The descent is bound to break off.

**What this means.** Euclid's engine *always halts*. There is no perpetual engine: an infinite
sequence of successful clean descents is impossible. This is precisely Fermat's infinite descent, rewritten
as thermodynamics: the system cannot lower its height forever, because the height is bounded below by zero.

## Directional asymmetry: infinitely up, finitely down

Here the very essence of the arrow of time comes into view — the *asymmetry* of the two directions.
Downward, the engine cannot ride forever (just shown). Upward, it can.

> **Theorem 5.6** (`fuel_ascent_strictMono`). The map `n \mapsto n+1` is strictly monotone:
> `\mathrm{StrictMono}\,(\lambda n.\,n+1)`.

**Why this is true.** Trivially: `n < n+1` for all `n`, and adding `+1` preserves the strict order. But
the triviality of the form should not obscure the substance of the statement. The successor chain
`0,1,2,3,\dots` is an *infinite strictly increasing* trajectory. Adding `+1` is "fuel":
larger centres never run out, and upward the engine can ride without stopping.

> **Observation.** From the intuition: `+1` is fuel, `+2` is cargo (the conserved two, the first law,
> [03 TwoGap]). It is natural to suppose that precisely this difference of directions is the source of
> irreversibility: upward, the state space is unbounded (`no_infinite_engine_descent` does not apply,
> because the chain does not decrease), downward it runs into a floor (`no_infinite_engine_descent` forbids
> infinitude). The engine rides infinitely **in one direction only** — upward; every descent
> is finite.

**Conclusion.** Setting the two theorems side by side — `no_infinite_engine_descent` and `fuel_ascent_strictMono` — is the rigorous
expression of the fact that the thermodynamic axis has a distinguished direction. Up and down are *not*
interchangeable: one is infinite, the other breaks off. This is an asymmetry, not a symmetry — and that
is why there is an arrow.

## To turn is to halt: an exact bound

The last theorem of the chapter makes "always halts" quantitative: it gives an *explicit bound* on
the length of any descent.

> **Theorem 5.7** (`turned_engine_halts`). Let `H : \mathbb{N} \to \mathbb{N}` and suppose the engine has made `k`
> strict steps downward, that is, `H(t+1) < H(t)` for all `t < k`. Then
> $$k \;\le\; H(0). \tag{5.3}$$

**What is proven.** If the engine has turned into a descent, it will halt within at most `H(0)` steps — exactly
as many as its initial height. The descent is not merely finite; it is finite *with an explicit, easily
computable upper bound*.

**Why this is true.** By induction on `t` one proves the invariant
$$\forall\, t \le k,\qquad H(t) + t \;\le\; H(0).$$
Base (`t=0`): `H(0)+0 = H(0)`. Step: from `H(n+1) < H(n)`, that is `H(n+1)+1 \le H(n)`, and from
the hypothesis `H(n)+n \le H(0)` we get `H(n+1)+(n+1) \le H(n)+n \le H(0)`. Substituting `t=k` and
dropping the nonnegative `H(k)\ge 0`, we obtain `k \le H(k)+k \le H(0)`. This is the same balance "height plus
time does not grow" as in `no_infinite_descent`, but read as a *finite* bound rather than as a route
to contradiction.

**What this means.** "If it turns, it halts" — and with a receipt: the cost of the descent is bounded by the starting height.
No analysis, no distribution, no sieve — only the order-completeness of `\mathbb{N}`. This is exactly why
the second law in this programme is *atomic* and proven unconditionally: it lives entirely in the combinatorics of the order
on the natural numbers.

## Chapter takeaway

The second law of thermodynamics for Euclid's engine consists of two unconditionally proven halves and
their asymmetry:

- **irreversibility** — `engine_never_returns` (`\mathrm{StrictAnti}\,H`): the engine does not return to
  any earlier state;
- **finiteness of descent** — `no_infinite_engine_descent` (no infinite strictly decreasing chain): the engine
  always halts, with the explicit bound `turned_engine_halts` (`k \le H(0)`);
- **asymmetry of directions** — `fuel_ascent_strictMono` versus `no_infinite_engine_descent`: infinitely
  up, finitely down; this is the arrow of time.

All of this is machine-proven, without `sorry`, on the standard axioms alone, and with no appeal to the
distribution of primes.

## Bridge to the next chapter

We have established that the engine does not turn back *in time* — along its trajectory in height. In
the next chapter [06 NoBackward] we shall discover a kindred but different irreversibility — a *spatial* one, at
the level of the two points of a pair.

There, the source of the prohibition on going back will turn out to be the carrier of two [02 Carrier]: one and
the same prime cannot sit on both sides of a pair (`\text{shared gcd} \mid 2`), which makes the diagonal
`\sum_p X_p Y_p` vanish, and the product of ranks — rank here, as always, being the "height" of a state,
falling along permitted steps (see the [glossary](GLOSSARY.md)) — turns out to be entirely off-diagonal.

If in this chapter
irreversibility forbade a return along the arrow of time, in the next one exclusivity will forbid "working backwards"
on the pair — and it is precisely this vanished diagonal that will become the exact source of the negative association `(r_-,r_+)`
later exploited by the four-corner [12](12_FourCorner.md).

<!--navbot-->

---

[← 04. Descent and the boundary-law](04_Descent.md) · [Table of contents](00_Overview.md) · [06. No way back →](06_NoBackward.md)
<!--/navbot-->
