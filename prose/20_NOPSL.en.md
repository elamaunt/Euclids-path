# 20. NOPSL: no sink means twin

<!--navtop-->
[← 19. Old-peel](19_OldPeel.md) · [Table of contents](00_Overview.md) · [21. Regeneration →](21_Regeneration.md)
<!--/navtop-->



> Source: `snol_old_peel_closure_ru_2026-06-30.md` (§5–14). Lean: `Engine/NOPSL.lean`
> (`OldPeelLedger`, `no_old_peel_sink`, `snol_of_nopsl`, `twin_primes_of_nopsl`; standard axioms).

In [19 Old-peel] we resolved the programme's last node: the carrier-scale catch $p\mid a-2\varepsilon$
turned out to be not a terminal but a descent step — old-peel spawns a new, strictly smaller centre $t<n$, and
the proven algebra (`old_peel_sign`, `old_peel_height_drop`) guarantees a strict drop in height.

It remains to turn this local drop into a global statement: the old-peel flow **must stop
somewhere**, and that stop is a twin. This is precisely the closure we formalise here under
the name NOPSL (No Old-Peel Sink Lemma): we show that the abstract core — strict descent with
regeneration — by itself, without a single appeal to the distribution of primes, entails the infinitude of twins.

## The abstraction: what exactly we fix

Before proving anything, we must honestly isolate the structure that old-peel supplies and separate
it from all the illustrative scenery. From the intuition of the old descent it is natural to extract exactly four
pieces of data: the height of a state, the predicate of correct stopping, the step relation, and two laws binding
them together. We gather these into a single structure.

> **Definition 20.1** (`OldPeelLedger`). An old-peel ledger over a type of states $\sigma$ is a tuple
> $$L=\bigl(h,\ \mathrm{Sink},\ \mathrm{Step},\ \texttt{step\_drops},\ \texttt{regenerate}\bigr), \tag{20.1}$$
> where
> - $h:\sigma\to\mathbb N$ is the **height** of a state (the scale of the current centre);
> - $\mathrm{Sink}:\sigma\to\mathrm{Prop}$ is the predicate of **correct stopping** (a twin centre or
>   a halted clean return that does not continue downward);
> - $\mathrm{Step}:\sigma\to\sigma\to\mathrm{Prop}$ is the **old-peel successor** relation;
> - $\texttt{step\_drops}:\ \mathrm{Step}\,s\,s'\Rightarrow h(s')<h(s)$ is the **old-peel law**: every
>   step strictly decreases the height;
> - $\texttt{regenerate}:\ \neg\,\mathrm{Sink}(s)\Rightarrow\exists\,s',\ \mathrm{Step}\,s\,s'$ is
>   **regeneration**: every non-sink state has an old-peel successor.

In Lean this is literally `structure OldPeelLedger` with fields `h`, `Sink`, `Step`, `step_drops`,
`regenerate`. Note that the structure knows nothing about primes, about divisibility, or about the concrete
shape of the catch — it is purely combinatorial. This is a matter of principle: all the arithmetic of old-peel has already been spent
on securing the two law fields, and the reasoning that follows is conducted exclusively in the language of
"the height falls" and "the flow does not hang".

Let us trace where each law comes from.

The field `step_drops` is a direct repackaging of the theorem `OldPeel.old_peel_height_drop` from the previous chapter:
the old-peel quotient satisfies $t<n/5<n$, that is, the height of the new centre is strictly smaller than the height
of the old one. There is no hypothesis here — this is proven algebra, confirmed on 100% of real rank-1
catches.

The field `regenerate` is the substantive node of NOPSL. It asserts: a state that is *not* a
correct stop necessarily has an outgoing descent edge. Visually this is the dichotomy of §10–11: every
non-twin centre $t$ falls into one of the classes —

1. a clean return into the rigid ledger ($t\in\Omega_A$, but $t\ge A^2$, i.e. not yet a twin sink);
2. the next old-peel ($t\notin\Omega_A$: there is a $q\le A$ with $q\mid 6t\pm1$);
3. fan-in / Hall (many pedigrees converge into a single $t$);
4. an already classified defect,

— and in each of them there is a correct successor. The key negative claim: **there is no fifth
class** — no "hanging" terminal that has neither sink status nor a successor. It is precisely
the non-existence of such a hanging terminal that we encode as `regenerate`.

> **Note.** The split into two fields is not cosmetic: `step_drops` is proven arithmetic
> (it cannot be weakened), while `regenerate` is a structural hypothesis about the closedness of the ledger. The abstraction
> `OldPeelLedger` exists precisely to localise the matter: everything still to be justified outside
> the Lean core sits in the single field `regenerate` and nowhere else.

## NOPSL: the flow reaches a sink

Now the main statement. It says that the abstract structure closes itself.

> **Theorem 20.2** (`no_old_peel_sink`, §11.1/13.1). For every old-peel ledger $L$ over $\sigma$ and every
> start $\mathrm{start}\in\sigma$ there exists a state $s$ with $\mathrm{Sink}(s)$:
> $$\forall L,\ \forall\,\mathrm{start},\quad \exists\,s,\ L.\mathrm{Sink}(s). \tag{20.2}$$

Let us show why this is true, and follow the Lean proof at the same time — it is short and contains
not a single loophole.

We argue by contradiction. Suppose there is no sink at all: $\neg\,\exists s,\ \mathrm{Sink}(s)$. Then
*every* state is a non-sink, and by `regenerate` every $s$ has a successor:
$$\forall s,\ \exists s',\ \mathrm{Step}\,s\,s'.$$
In Lean this is the line `have hstep : ∀ s, ∃ s', L.Step s s'`, where the non-sink status of any $s$ is obtained
from the negation of the existence of a sink.

Using a choice function (`choose next hnext`) we turn "every $s$ has a successor" into a concrete
function $\mathrm{next}:\sigma\to\sigma$ with $\mathrm{Step}\,s\,(\mathrm{next}\,s)$ for all $s$. From
it, by recursion, we build an infinite trajectory
$$z(0)=\mathrm{start},\qquad z(k+1)=\mathrm{next}\,(z(k)), \tag{20.3}$$
each link of which is a genuine old-peel step: $\mathrm{Step}\,(z\,k)\,(z\,(k{+}1))$.

Applying `step_drops` to each link, we obtain a strictly decreasing sequence of heights:
$$\forall k,\quad h\bigl(z(k+1)\bigr)<h\bigl(z(k)\bigr). \tag{20.4}$$
This is a sequence of natural numbers decreasing at every step, forever. No such thing
exists — and this is exactly what `OldPeel.old_peel_terminates` asserts, which is in turn a
repackaging of `no_infinite_engine_descent` (no infinite strict descent in $\mathbb N$ =
the impossibility of Euclid's perpetual engine, EPMI; see the [glossary](GLOSSARY.md)). Contradiction,
and the assumption that no sink exists is false. $\qquad\blacksquare$

Why this way and not another: the substantive force of the theorem lies not in the choice of successor (that is standard
technique), but in the fact that *the very same* fact — "no infinite strict descent" — with which we previously
forbade the perpetual engine now forbids perpetual evasion of a sink. The engine and NOPSL are two
projections of one prohibition. That is why the closure requires no new mathematics: it inherits an impossibility
already proven.

> **Note.** Observe that the proof uses neither `IsTwinCenter`, nor
> divisibility, nor $\Omega_A$ — only `step_drops`, `regenerate` and the terminality of descent in $\mathbb N$.
> NOPSL is a theorem about *height and regeneration*, not about prime numbers. Primes will enter only at
> the next step, when we say *what exactly* a sink is.

## SNOL as an immediate consequence

Before tying the sink to twins, let us record formally the disappearance of the former obstacle.
In [18 SNOL] the final node was the "terminal shifted-neighbour obstruction": a hypothetical
carrier-scale catch that leads nowhere. Now we can say why it does not exist.

> **Theorem 20.3** (`snol_of_nopsl`, §13). For every old-peel ledger $L$ and start there exists a sink:
> $$\exists\,s,\ L.\mathrm{Sink}(s). \tag{20.5}$$

Formally `snol_of_nopsl` is exactly Theorem 20.2 (`no_old_peel_sink`) applied to $L$ and `start`; the separate name is there to
emphasise the substantive reading. If the terminal SN-obstruction existed, its states
would be simultaneously non-sink (no twin) and without regeneration (nowhere to go) — which directly contradicts
the field `regenerate`. Hence the obstruction is impossible, and the flow is guaranteed to reach a correct
stop. In other words, SNOL is not an independent hypothesis but a shadow of NOPSL: once we have accepted
`regenerate`, "no hanging terminal" is proved automatically.

## The final closure: no sink means twin

It remains to name the sink a twin. Here the abstraction meets Polignac's conjecture. We hang
a ledger of its own on every scale $N$ and demand that its correct stops be twin centres above
$N$.

> **Theorem 20.4** (`twin_primes_of_nopsl`, §14.1). Suppose we are given
> - a family of ledgers $L(N)$ and starts $\mathrm{start}(N)$ for every scale $N\in\mathbb N$;
> - a centre function $\mathrm{center}(N,\cdot):\sigma\to\mathbb N$;
> - a stop-on-twin condition
>   $$\texttt{sink\_is\_twin}:\quad \forall N,s,\ \ L(N).\mathrm{Sink}(s)\ \Rightarrow\ N<\mathrm{center}(N,s)\ \wedge\ \mathrm{IsTwinCenter}\bigl(\mathrm{center}(N,s)\bigr). \tag{20.6}$$
>
> Then $\mathrm{TwinLowers.Infinite}$ — there are infinitely many twin primes.

The proof unfolds in three moves, literally as in Lean. We reduce the goal to the unboundedness of
twin centres via `infinite_of_unbounded_centers` (the §NonCover bridge: if for every $N$ there is a
twin centre $m>N$, then the set of twins is infinite).

Next we fix an arbitrary $N$ and apply
Theorem 20.2 (`no_old_peel_sink`) to the ledger $L(N)$ with start $\mathrm{start}(N)$ — obtaining a sink $s$.

Finally,
by `sink_is_twin` this sink yields the centre $\mathrm{center}(N,s)$, which lies above $N$ and is a
twin centre. Hence on every scale there is a twin above it — that is, there are unboundedly many.
$\qquad\blacksquare$

**Section takeaway.** The programme's logical chain is fully closed. Every link —

$$\underbrace{\texttt{step\_drops}}_{\text{proven algebra}}\ +\ \underbrace{\texttt{regenerate}}_{\text{structural input}}\ \xRightarrow{\ \texttt{no\_old\_peel\_sink}\ }\ \text{sink}\ \xRightarrow{\ \texttt{sink\_is\_twin}\ }\ \text{twin centre}>N\ \xRightarrow{\ \texttt{infinite\_of\_unbounded\_centers}\ }\ \text{infinitude of twins}$$

— is checked by the compiler. The single input into the theorem (an "input" is an honestly named, not-yet-
proven assumption, see the [glossary](GLOSSARY.md)) is the structure `OldPeelLedger`, not the
distribution of primes.

## What is proven and what is assumed — honestly

Let us separate the strictly verified from the remaining input, without passing the reduction off as a proof.

**Machine-proven.** The full implication $\texttt{OldPeelLedger}\ \Rightarrow\ \mathrm{TwinLowers.Infinite}$
on the pure logic of strict descent, without a single counting or distributional argument. This
turns SNOL/NOPSL from prose into a verified **reduction**: supply a ledger with its two
laws, and the infinitude of twins follows automatically.

**Still to justify.** Exactly two premises of the structure `OldPeelLedger`, and neither is a counting one:

1. `step_drops` — *proven* by old-peel algebra (`old_peel_height_drop`, the numbers 100%). Here
   the question is closed.
2. `regenerate` — the **structural hypothesis of NOPSL**: the quotient centre $t$ is always classified
   (clean return / next peel / fan-in / known defect), that is, the extended rigid ledger is closed
   under old-peel quotients with no unclassifiable terminal.

> **Hypothesis (regenerate).** The extended rigid ledger is closed under old-peel quotients: every
> non-twin centre $t$ has a correct successor in one of the four classes of §10–11. Equivalently:
> no hanging carrier-scale terminal exists.

**Closure plan.** The dichotomy of classes (1)–(3) is already formalised in the next chapter as the theorem
`regeneration_dichotomy` (unconditional, standard axioms). The non-trivial remainder is localised in
class (4) — fan-in / Hall — and in the requirement that the cycle of §11 carries a genuine rigid signature
of an engine. This remainder is precisely the substantive content of the field `regenerate`; its closure
proceeds not through the distribution of primes but through a payment-ledger argument on carrier-scale mass (audit §13.C–D
of the source).

> **Note.** The key difference between `regenerate` and all the programme's previous inputs (for instance, the
> counting `H`): it lies *in the logic of the engine*, not of the distribution. Vividly: "the flow has nowhere
> to go except downward or into a twin". It is the single point left outside the Lean core, and it is also
> the central point of the audit.

## Bridge to what comes next

So the finale has been compressed to a single structural fact: the field `regenerate`, the closedness of the ledger under old-peel
quotients. Everything else — from the strict drop in height to the infinitude of twins — is checked
by the compiler.

It is natural to ask: can `regenerate` itself be proven, at least in parts? In
[21 Dichotomy] we formalise Lemma 6.1 on regeneration and show that its elementary core
— the full dichotomy of the quotient centre plus the sign law — is proven in Lean without the distribution, leaving
as explicit inputs only fan-in/Hall and the rigid signature of the cycle.

<!--navbot-->

---

[← 19. Old-peel](19_OldPeel.md) · [Table of contents](00_Overview.md) · [21. Regeneration →](21_Regeneration.md)
<!--/navbot-->
