# 55. Collatz as a perpetual engine on limited fuel

<!--navtop-->
[← 54. Neighbours beyond the horizon](54_OpenNeighbors.md) · [Table of contents](00_Overview.md) · [56. The Collatz first cause →](56_CollatzFirstCause.md)
<!--/navtop-->

> Lean source: `Engine/CollatzEngine.lean` (structural facts: `even_marginal`, `odd_accel_ascends`,
> `not_descent_on_odd`, `trivial_halt_cycle`), `Engine/CollatzFuel.lean` (`k1_step_grows`,
> `k2_step_drops`, `no_monotone_height`), `Engine/CollatzTugOfWar.lean` (**verified**, core Lean, axioms
> `[propext, Quot.sound]`; the section "Refutation = engine" is the standard triple via `Classical.em`):
> `engine_at_most_one_rank`, `rope_pulls_one`, `rope_pulls_two`, `window_budget`, `window_descends`,
> HERO `reaches_one_of_countingLaw`, `nonDescendingOrbit_is_perpetual_engine`; the universal form
> `RopeCountingLaw` is *refuted* 🟢 (`not_ropeCountingLaw_27`, `ropeLaw_universal_refuted`; the witness n = 27
> is closed by the computation `counts_le_70_at_27`, `counts_at_70_at_27` and the cycle lemma `cycle_counts` via
> `oddCount_add`/`evenCount_add`); the per-n form is alive (`countingLaw_4`).
> Numbers: `tools/RESULTS_collatz.md` (harnesses `collatz_engine_harness.py`, `collatz_fuel_harness.py`).
> Legend: 🟢 — machine-proven; 🔴 — an open named input.

## Where we are

The main line has carried the single prohibition `no_infinite_descent` through its masks (a mask is a great
problem read through the engine prohibition; see the [glossary](GLOSSARY.md)) and the arithmetic zoo.
Collatz is the strangest of them: here the "engine" is not a surrogate but a *literal* object on ℕ.

This appendix
translates the conjecture into the language of the engine and the rope, shows exactly where it breaks our laws (and
why that makes it hard), and drives the green mechanics all the way to a named rope law — which, in its
universal form, we **refute** right here by the witness n = 27. What became of the decree resting on this law —
in [chapter 56](56_CollatzFirstCause.md).

## The map: Collatz through the engine lens

**Definition 55.1** (the accelerated Collatz map). The map $T\colon\mathbb N\to\mathbb N$ is given by
$$T(n)=\begin{cases}n/2,&n\equiv 0\ (\mathrm{mod}\ 2),\\ (3n+1)/2,&n\equiv 1\ (\mathrm{mod}\ 2)\end{cases}\tag{55.1}$$
— the forced division by 2 after an odd step is folded into the map itself. The match-up with Euclid's engine:

| Engine element | Collatz | Status |
|---|---|---|
| descent (`A·h' < h`) | even step `n ↦ n/2` (height ×½) | descent by exactly 2 — the edge (`2·(n/2) = n`, not strict at A=2) |
| the "+1" fuel (ascent) | odd step `3n+1` (×3 and +1) | ascent `n < 3n+1` — literally "+1 = a fuel injection" |
| halting (always) | reaching `1` (the minimum) | open (the Collatz conjecture) |
| cycle = return | a nontrivial cycle | open (none up to ~10²⁰) |
| irreversibility | deterministic forward | yes, but with no strict Lyapunov |

## Where Collatz breaks our law — and why that makes it hard

Euclid's engine halts with a guarantee, because every step is a strict descent
(`A·h' < h`), and then `no_infinite_descent` yields `H(t) < H₀/Aᵗ < 1`. Collatz has no such law.

**Theorem 55.2** (`odd_accel_ascends`). For odd $n\ge 1$ the accelerated step strictly raises the height:
$$n<\frac{3n+1}{2}=T(n)\qquad (n\equiv 1\ \mathrm{mod}\ 2).\tag{55.2}$$

**Theorem 55.3** (`not_descent_on_odd`). For odd $n\ge 1$ the step is not a descent: $\neg\,(T(n)<n)$.
Hence the height along the orbit is not `StrictAnti`, and the law `no_infinite_descent` does not apply.

- numerically (`RESULTS_collatz.md`): peak/start reaches 53930× (n = 159487) — the height wanders upward by
  4–5 orders of magnitude before descending. There is no strict monotone Lyapunov function.

**Conclusion 1.** Collatz is a Euclid perpetual engine whose 2nd law is broken in the strict form:
the fuel injection (+1 in `3n+1`) temporarily raises the height, so `no_infinite_descent` does not
apply to it. This is exactly why the halting of Collatz is open, while Euclid's engine's is proven.

## Is the fuel finite? — Yes, on average (but not for each one)

"The fuel is finite" ⟺ the trajectory is bounded (does not escape to ∞). We measure the balance (`RESULTS_collatz.md`):

- halvings / triplings = 2.016 > the threshold `log₂3 = 1.585`: to quench one `×3` takes ≥ 2 divisions
  (`one_tripling_needs_two_halvings`: `2 < 3 ≤ 4`); the actual 2.016 means descents with room to spare. The fuel
  is **net-consumed**;
- the geometric drift per step = 0.864 (= √(3)/2 ≈ 0.866) < 1: each step on average multiplies the height by
  0.864 — a contraction. On average the engine drives downhill;
- all n ∈ [2, 200000] reach 1 — no alien cycles (perpetual engines) exist in the range.

But this is a law of the *average*, while the conjecture demands "every trajectory halts". And there is no monotone
height even after compressing the odd blocks: the compressed step `n ↦ (3n+1)/2^k` at `k = 1` (≈50%, `n ≡ 1 mod 4`)
grows the value (`k1_step_grows`), and at `k ≥ 2` it drops (`k2_step_drops`).

**Theorem 55.4** (`no_monotone_height`). Ascending positions are unbounded: for every $N$ there is $n>N$
with $n\equiv 1\ (\mathrm{mod}\ 4)$ and $n<(3n+1)/2$ (witness $n=4N+5$). Hence there is no monotone
$\log_2$-height 🟢.

**Conclusion.** So there is no Lyapunov function, and our EPMI (which requires strict descent at every step) does not apply to Collatz. Collatz is
an engine on limited fuel *by energy*, but not an EPMI engine. This is the exact boundary between
the proven laws and the openness.

## Tug of war (multiplicative, no logarithms)

We read it in the author's words: **"the engine advances by at most 1 rank forward per step, the rope pulls
1 or 2 ranks back; when the fuel runs out — the engine is dragged back to the start"**. Rank = binary order;
"+1 rank" = at most a doubling, "−1" = exactly a halving. The green mechanics:

| Metaphor element | Lemma | Status |
|---|---|---|
| engine ≤ +1 rank per step | `engine_at_most_one_rank : T n ≤ 2n` | 🟢 |
| the engine's honest price (×1.5, not ×2) | `engine_exact_fuel : 2·T n = 3n+1` | 🟢 |
| the rope pulls by 1 | `rope_pulls_one : 2·T n = n` (even) | 🟢 |
| the rope pulls by 2 | `rope_pulls_two : 4·T²n = n` (n ≡ 0 mod 4) | 🟢 |
| window fuel budget | `window_budget : 2^e·T^k(n) ≤ 2^t·n` | 🟢 |
| the rope won the pull ⟹ descent | `window_descends : t < e ⟹ T^k(n) < n` | 🟢 |
| "the fuel runs out — dragged back to the start" | `reaches_one_of_countingLaw` (HERO) | 🟢 conditional (per-n) |
| the rope dominance law (universal) | `RopeCountingLaw` | 🟢 REFUTED (n = 27) |

**The window budget.** Each pull of the rope multiplies the value by exactly ½; each move of the engine — by at most 2.

**Theorem 55.5** (`engine_at_most_one_rank`). One move of the engine advances by at most a rank:
$T(n)\le 2n$ for all $n$ 🟢.

**Theorem 55.6** (`window_budget`). Over a window of $k$ steps, among which $t=\mathrm{oddCount}(k,n)$ are odd
and $e=\mathrm{evenCount}(k,n)$ are even, the bounds multiply under any order of steps:
$$2^{e}\cdot T^{k}(n)\;\le\;2^{t}\cdot n.\tag{55.3}$$
This is pure $\mathbb N$-arithmetic: the floor-divisions are absorbed by the precision of the per-step bounds, no logarithms needed 🟢.

**Theorem 55.7** (`window_descends`). If the rope won the window strictly ($t<e$) and $n\ge 1$, then the value
strictly dropped: $T^{k}(n)<n$ 🟢. (From (55.3): $2^{t+1}\le 2^{e}$ gives $2\cdot T^{k}(n)\le n$.)

**The hero's ladder.** The hero here is in the house sense: the central conditional theorem of the branch,
carrying the law all the way to the goal (see the [glossary](GLOSSARY.md)).

**Definition 55.8** (`RopeCountingLaw`, the rope dominance law, counting form). For $n$ the law states: at
every orbit position above the absorbing cycle there is a window with an even surplus,
$$\mathrm{RopeCountingLaw}(n)\;:\equiv\;\forall j,\ \bigl(2<T^{j}(n)\ \Rightarrow\ \exists k,\ \mathrm{oddCount}(k,T^{j}(n))<\mathrm{evenCount}(k,T^{j}(n))\bigr).\tag{55.4}$$

The ladder `RopeCountingLaw n` → (window budget, Theorem 55.6) → `ValueDescentLaw n` → (induction on the
value ceiling) → reaching 1.

**Theorem 55.9** (`reaches_one_of_countingLaw`, HERO). If $n\ge 1$ and $\mathrm{RopeCountingLaw}(n)$ holds,
then $\exists K,\ T^{K}(n)=1$ 🟢. It is a **conditional** theorem about a specific $n$ — "give the law for
this $n$, and you get the halting"; the ladder itself is green in its entirety.

What is no longer allowed is handing the
premise to all n at once: the universal form of the law is refuted below (n = 27).

The hero remains an honest
conditional engine; what proved false was not the mechanics, but the promise that *every* n's fuel would lose the pull from the start.

## Three honesties (what is green, and what is not)

1. **The condemned man's bridge.**

   **Theorem 55.10** (`valueLaw_iff_reaches_one`). For $n\ge 1$ the value form of the law is equivalent to
   convergence: $\mathrm{ValueDescentLaw}(n)\iff \exists K,\ T^{K}(n)=1$ 🟢. By itself it adds no content.
   Only the counting form (Definition 55.8) is substantive; its converse (convergence ⟹ counting law) is
   not asserted — the window budget is one-sided.
2. **Rejecting "the rope is twice as strong".** The form `2·odd < even` is rejected: empirically, on the accelerated map
   `e ≈ 1.016·t` (halvings/triplings = 2.016, minus 1 halving eaten by the acceleration) — the threshold `e > 2t`
   is false on average. The exact threshold `e > t` is taken — precisely the one that the green ×2 bound converts into descent.
   The ~1.6% margin is the price of renouncing `log₂3` (true descent needs only `e > 0.585·t`, but that is already logarithms,
   not core Lean).
3. **The k=1 wall and the tail trap.** `single_window_fails`/`no_single_step_law` 🟢: a window of length 1
   fails at every odd position (the family 2N+1) — in full agreement with the wall
   `no_monotone_height`; the law must live on windows ≥ 2. The guard "value > 2" is mandatory: in the cycle 1→2→1
   `t ≥ e` in all windows (`countingLaw_1` — vacuous truth: the law holds for free,
   see the [glossary](GLOSSARY.md)) — without the guard the law would be false for
   every convergent trajectory.

   **Theorem 55.11** (`countingLaw_4`). The rope law holds for $n=4$ genuinely (non-vacuously):
   $\mathrm{RopeCountingLaw}(4)$; the only position above the cycle is the start, where the window $k=2$
   (4→2→1) gives $t=0<e=2$ 🟢.

## Refuting the law: the climbing orbit of 27

We no longer extend credit to the universal form of the rope law: it is **false**, and the witness —
a concrete object certifying a statement (see the [glossary](GLOSSARY.md)) — is the most
famous number in Collatz folklore, n = 27. Its orbit climbs for a long time: from 27 it rises to
a peak of 4616 before giving in.

And here is the snag. The rope law demands that at *every* position
above the cycle — including from the very start, from position j = 0 — there be a window where the even steps strictly
outnumber the odd ones. The orbit of 27 has not a single such window from the start: while the number is climbing, the steps
are odd-heavy, and the difference `evenCount − oddCount` in the prefix windows never becomes
positive.

**Theorem 55.12** (`counts_at_70_at_27`). The orbit of 27 reaches one in 70 accelerated steps:
$$\mathrm{oddCount}(70,27)=41,\quad \mathrm{evenCount}(70,27)=29,\quad T^{70}(27)=1.\tag{55.5}$$
That is, **41 moves of the engine** against only 29 pulls of the rope; the rope trails by 12 in total — and
never once pulls ahead from the start 🟢 (machine check).

Nor does the tail claw the deficit back. After step 70 the orbit falls into the absorbing cycle 1→2→1, where the steps go
strictly in pairs — one odd, one even. Each pair adds one to each side, so the rope's
lag of −12 freezes forever: no window from the start will ever flip it. The beautiful metaphor
"the fuel runs out — the engine is dragged back to the start" is true in *outcome* (27 does reach 1 after all), but not for
the strong **stepwise** reason the law was stating.

The kernel checks this without taking anyone's word. The prefix up to and including k = 70 is closed by direct computation
(`counts_le_70_at_27`: in all these windows `even ≤ odd`; `counts_at_70_at_27`: exactly 41 against 29 and the finish
at 1). The tail is closed in vacuo by the cycle lemma `cycle_counts` — via the additivity of the counters under concatenation
of windows (`oddCount_add`, `evenCount_add`).

**Section takeaway.**

**Theorem 55.13** (`not_ropeCountingLaw_27`). The rope law is false for $n=27$: $\neg\,\mathrm{RopeCountingLaw}(27)$.
From position $j=0$ (value $27>2$) no window gives a rope surplus — the prefix up to $k=70$ is closed by
computation, the tail by the cycle lemma 🟢.

**Theorem 55.14** (`ropeLaw_universal_refuted`). The universal form of the law is false:
$\neg\,\forall n\ (1\le n\Rightarrow \mathrm{RopeCountingLaw}(n))$; witness $n=27$ (Theorem 55.13) 🟢.
A decree boundary on this law is impossible. And 27 is not alone: the harness finds a whole family of
violators — 27, 31, 41, 47, 54, 55, … All of them climb, and for all of them the rope never wins the pull
from the start.

> **Note.** The lesson is an honest one, and it does not cancel the numbers. The average drift ×0.864 remains a law — but
> a law of the *orbit average*. The prefix-window form demanded more: dominance of the rope from
> every position, the ascent included — and the climbing orbits do not deliver that. An early warning
> light had already been blinking: the "k = 1 wall" (`single_window_fails`) showed that at an odd position a window
> can fail. The orbit of 27 is the same wall, only grown to the size of an entire ascent. What became of the decree
> that stood on this law as the fourth boundary of the first cause — in [chapter 56](56_CollatzFirstCause.md).

## A non-descending orbit = a perpetual engine

By the author's directive this is proven green and will serve as the bridge to [chapter 56](56_CollatzFirstCause.md):

**Theorem 55.15** (`nonDescending_engine_never_loses`). Let $n\ge 1$ and the orbit be non-descending
($n\le T^{k}(n)$ for all $k$). Then the engine wins or draws every window forever:
$\mathrm{evenCount}(k,n)\le \mathrm{oddCount}(k,n)$ for all $k$ 🟢 — straight from the window budget
(Theorem 55.6). An infinite feed with not a single lost window — that is precisely a perpetual engine.

**Theorem 55.16** (`nonDescendingOrbit_is_perpetual_engine`). For $n\ge 3$ a non-descending orbit loses no
windows ($\forall k,\ \mathrm{evenCount}(k,n)\le \mathrm{oddCount}(k,n)$) and never halts
($\forall K,\ T^{K}(n)\neq 1$) 🟢.

**Theorem 55.17** (`no_nonDescendingOrbit_under_countingLaw`). For $n\ge 3$, under
$\mathrm{RopeCountingLaw}(n)$ there are no non-descending orbits: the very first position gives a window with
a rope surplus and a strict descent below the start 🟢. That is, the rope law forbids such an engine from the
first position.

## The bottom rank: why +1 confuses 2 and 3

**Theorem 55.18** (`plus_one_full_rank_only_at_one`). For $n\ge 1$ the +1 addition weighs a full rank only at
the bottom: $3n+1=4n\iff n=1$ 🟢. Above the bottom ($n\ge 3$) it is strictly sub-rank, $3n+1<4n$
(`plus_one_subrank_above_one`).

**Theorem 55.19** (`engine_confused_at_bottom`). Exactly at the bottom the engine's shot lands on a pure power
of the rope: $3\cdot 1+1=2^{2}$, with $T(1)=2$ and $T(2)=1$ 🟢 (with no axioms at all). The rope hauls it in
two steps in a row — the absorbing cycle 1→2→1 is born. At the bottom rank the engine's three and the rope's
two are indistinguishable to +1: down there it makes up a whole rank.

## Philosophical digression: the decaying drift and the quantum floor

The tug of war is a thermodynamic image, more honest than logarithms. The map drives the number like a damped
random walker: the engine (×3) injects fuel, the rope (÷2) drains it, the average drift is
negative (×0.866 < 1). It is a particle in a potential well with friction: however high it gets tossed, on
average it slides toward the bottom.

A damped oscillator returns to rest not because each swing
is smaller than the last (there are surges), but because *on average* the energy leaves faster than it is
pumped in. And here stands the same wall as in turbulence and in the primes: **the average is solved, the fate of each
trajectory is open**.

`RopeCountingLaw` tried to name it more strongly — "at every position there is a window where the rope
won the pull" — and it is exactly this strong form that proved false: the climbing orbit of 27 keeps the rope behind
from the very start. The open heart is convergence itself, and no counting name known to us
substitutes for it. How the decree standing on this law ended, and why convergence still cannot be settled
from inside — in [chapter 56](56_CollatzFirstCause.md).

<!--navbot-->

---

[← 54. Neighbours beyond the horizon](54_OpenNeighbors.md) · [Table of contents](00_Overview.md) · [56. The Collatz first cause →](56_CollatzFirstCause.md)
<!--/navbot-->
