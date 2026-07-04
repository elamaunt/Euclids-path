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

The main line has carried the single prohibition `no_infinite_descent` through seven masks (a mask is a great
problem read through the engine prohibition; see the [glossary](GLOSSARY.md)) and the arithmetic zoo.
Collatz is the eighth and a special one: here the "engine" is not a surrogate but a *literal* object on ℕ.

This appendix
translates the conjecture into the language of the engine and the rope, shows exactly where it breaks our laws (and
why that makes it hard), and drives the green mechanics all the way to a named rope law — which, in its
universal form, we **refute** right here by the witness n = 27. What became of the decree resting on this law —
in [chapter 56](56_CollatzFirstCause.md).

## The map: Collatz through the engine lens

The accelerated map `T`: even `n ↦ n/2`, odd `n ↦ (3n+1)/2` (the forced division is folded in).
The match-up with Euclid's engine:

| Engine element | Collatz | Status |
|---|---|---|
| descent (`A·h' < h`) | even step `n ↦ n/2` (height ×½) | descent by exactly 2 — the edge (`2·(n/2) = n`, not strict at A=2) |
| the "+1" fuel (ascent) | odd step `3n+1` (×3 and +1) | ascent `n < 3n+1` — literally "+1 = a fuel injection" |
| halting (always) | reaching `1` (the minimum) | open (the Collatz conjecture) |
| cycle = return | a nontrivial cycle | open (none up to ~10²⁰) |
| irreversibility | deterministic forward | yes, but with no strict Lyapunov |

## Where Collatz breaks our law — and why that makes it hard

Euclid's engine halts with a guarantee, because every step is a strict descent
(`A·h' < h`), and then `no_infinite_descent` yields `H(t) < H₀/Aᵗ < 1`. Collatz has no such law:

- `odd_accel_ascends` 🟢: on odd `n ≥ 1` the step raises the height (`T n > n`);
- `not_descent_on_odd` 🟢: hence `¬ (T n < n)` — the step is not a descent, the height is not `StrictAnti`;
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
grows the value (`k1_step_grows`), and at `k ≥ 2` it drops (`k2_step_drops`); while `no_monotone_height` 🟢
supplies arbitrarily large ascending `n`.

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
The bounds multiply under any order of steps: over a window of `k` steps with `t` odd and `e` even —
`2^e · T^k(n) ≤ 2^t · n`. Pure ℕ-arithmetic: the floor-divisions are absorbed by the precision of the per-step bounds,
no logarithms needed. If the rope won the pull (`e > t`) — the value has strictly dropped.

**The hero's ladder.** The hero here is in the house sense: the central conditional theorem of the branch,
carrying the law all the way to the goal (see the [glossary](GLOSSARY.md)). `RopeCountingLaw n` → (window budget) → `ValueDescentLaw n` → (induction on the value
ceiling) → reaching 1. The ladder itself is green in its entirety (`reaches_one_of_countingLaw`): it is a **conditional**
theorem about a specific n — "give the law for this n, and you get the halting".

What is no longer allowed is handing the
premise to all n at once: the universal form of the law is refuted below (n = 27).

The hero remains an honest
conditional engine; what proved false was not the mechanics, but the promise that *every* n's fuel would lose the pull from the start.

## Three honesties (what is green, and what is not)

1. **The condemned man's bridge.** `valueLaw_iff_reaches_one` 🟢: the value form of the law is equivalent to
   convergence — by itself it adds no content. Only the counting form is substantive; its converse
   (convergence ⟹ counting law) is not asserted — the window budget is one-sided.
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
   every convergent trajectory. Non-vacuity: `countingLaw_4` 🟢 — for n = 4 the law holds genuinely.

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

The orbit reaches one in 70 accelerated steps, of which **41 are moves of the engine** against
only 29 pulls of the rope. The rope trails by 12 in total — and never once pulls ahead from the start.

Nor does the tail claw the deficit back. After step 70 the orbit falls into the absorbing cycle 1→2→1, where the steps go
strictly in pairs — one odd, one even. Each pair adds one to each side, so the rope's
lag of −12 freezes forever: no window from the start will ever flip it. The beautiful metaphor
"the fuel runs out — the engine is dragged back to the start" is true in *outcome* (27 does reach 1 after all), but not for
the strong **stepwise** reason the law was stating.

The kernel checks this without taking anyone's word. The prefix up to and including k = 70 is closed by direct computation
(`counts_le_70_at_27`: in all these windows `even ≤ odd`; `counts_at_70_at_27`: exactly 41 against 29 and the finish
at 1). The tail is closed in vacuo by the cycle lemma `cycle_counts` — via the additivity of the counters under concatenation
of windows (`oddCount_add`, `evenCount_add`).

**Section takeaway.** Together: `not_ropeCountingLaw_27` (`¬ RopeCountingLaw 27`) and
the universal verdict `ropeLaw_universal_refuted` — `∀ n ≥ 1, RopeCountingLaw n` is a falsehood. And 27 is not
alone: the harness finds a whole family of violators — 27, 31, 41, 47, 54, 55, … All of them climb, and for
all of them the rope never wins the pull from the start.

> **Note.** The lesson is an honest one, and it does not cancel the numbers. The average drift ×0.864 remains a law — but
> a law of the *orbit average*. The prefix-window form demanded more: dominance of the rope from
> every position, the ascent included — and the climbing orbits do not deliver that. An early warning
> light had already been blinking: the "k = 1 wall" (`single_window_fails`) showed that at an odd position a window
> can fail. The orbit of 27 is the same wall, only grown to the size of an entire ascent. What became of the decree
> that stood on this law as the fourth boundary of the first cause — in [chapter 56](56_CollatzFirstCause.md).

## A non-descending orbit = a perpetual engine

By the author's directive this is proven green and will serve as the bridge to [chapter 56](56_CollatzFirstCause.md):

- `nonDescending_engine_never_loses` 🟢 — for the orbit not to descend, the engine must win or
  draw every window forever (`evenCount k ≤ oddCount k` for all k) — straight from the window budget.
  An infinite feed with not a single lost window — that is precisely a perpetual engine;
- `nonDescendingOrbit_is_perpetual_engine` 🟢 — the summary: loses no windows ∧ never halts;
- `no_nonDescendingOrbit_under_countingLaw` 🟢 — the rope law forbids such an engine from the first position.

## The bottom rank: why +1 confuses 2 and 3

- `plus_one_full_rank_only_at_one` 🟢 — the +1 addition weighs a full rank only at n = 1: `3n+1 = 4n ⟺ n = 1`;
  above the bottom it is strictly sub-rank (`plus_one_subrank_above_one`);
- `engine_confused_at_bottom` 🟢 (with no axioms at all) — exactly at the bottom the engine's shot lands on a pure
  power of the rope: `3·1 + 1 = 2²`, and the rope hauls it in two steps in a row — the absorbing cycle
  1→2→1 is born. At the bottom rank the engine's three and the rope's two are indistinguishable to +1: down there it makes up a whole rank.

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
