# 21. The Regeneration Dichotomy

<!--navtop-->
[← 20. NOPSL](20_NOPSL.md) · [Table of contents](00_Overview.md) · [22. Residuals →](22_Residuals.md)
<!--/navtop-->



> Source: `old_peel_regeneration_formal_proof_ru_2026-06-30.md` (Lemma 6.1 on regeneration). Lean:
> `Engine/Regeneration.lean` (5 theorems, standard axioms, no `sorry`). Relies on
> `Engine/OldPeel.lean` (`old_peel_height_drop`) and feeds `Engine/NOPSL.lean` (the `regenerate` field).

In [20 NOPSL] we reduced the entire programme to a single structural fact — the premise `regenerate`
of the abstract `OldPeelLedger`: every non-sink state is obliged to have an old-peel successor, that is,
the flow of quotient centres has "nowhere to go except downward or into a twin". The closure was proven
by machine, but `regenerate` itself remained an input — an honestly named unproven statement, a gate in
the sense of the [glossary](GLOSSARY.md).

In this chapter we open it up from the inside: we show that behind the
abstract word "regenerates" stands an **elementary and unconditional dichotomy** of any centre `t`
into three classes, and we honestly localize exactly which part of regeneration remains a structural
input rather than a consequence of algebra.

## The setup: what we classify

After the old-peel step of [19](19_OldPeel.md) we obtain a quotient centre — a natural number $t>0$ encoding the pair
of active neighbours $6t-1$ and $6t+1$. The regeneration question is: *what happens to this centre next* —
is there an outgoing descent edge from it, or does it turn out to be a legitimate sink (a twin centre)? We
want to show that a third option — a "dangling terminal" in which the flow gets stuck with no edge and no
twin — does not arise under the elementary case analysis.

Fix a threshold $A$ (the scale of the "old" primes already peeled off) and introduce two predicates.

> **Definition (old-free centre).** A centre $t$ is called *old-free* relative to the threshold $A$ if
> no prime $q$ with $5\le q\le A$ divides either of the sides $6t\pm1$:
> $$\mathrm{OldFree}(A,t)\ :\Longleftrightarrow\ \forall q\ \text{prime},\ 5\le q\le A\ \Longrightarrow\ \neg\bigl(q\mid 6t-1\ \lor\ q\mid 6t+1\bigr).$$
> In Lean this is `def OldFree (A t : ℕ) : Prop`. Substantively, $\mathrm{OldFree}(A,t)$ is
> membership of the centre in the "clean zone" $\Omega_A$: it is not caught by any of the primes already passed.

> **Definition (twin centre).** A centre $t$ is a *twin* if both sides are prime:
> $$\mathrm{Twin}(t)\ :\Longleftrightarrow\ (6t-1)\ \text{prime}\ \land\ (6t+1)\ \text{prime}.$$
> In Lean this is `def Twin (t : ℕ) : Prop`. This is the only kind of legitimate sink: a pair of
> twin primes $(6t-1,6t+1)$.

Note at once that the lower bound $q\ge5$ is no accident. By the construction of the carrier, the primes
$2$ and $3$ never divide $6t\pm1$ (these numbers are coprime to $6$), so the "old" candidates for
division are exactly the primes $\ge5$. That is where the sieve begins, and that is what the threshold $A$
keeps track of.

## Case (3) resolved: not-old-free yields an old-peel edge

We begin with the logically simplest link — the negation of old-free.

**Theorem (`not_oldfree_gives_peel`).** *If $\neg\,\mathrm{OldFree}(A,t)$, then there exists an old
divisor that generates an old-peel:*
$$\neg\,\mathrm{OldFree}(A,t)\ \Longrightarrow\ \exists\,q\ \text{prime},\ 5\le q\le A\ \land\ \bigl(q\mid 6t-1\ \lor\ q\mid 6t+1\bigr).$$

The proof here is pure unfolding of the definition: $\neg\forall$ yields $\exists$, and we
extract a witness $q$ — a concrete object certifying the statement (see the [glossary](GLOSSARY.md)). No counting, no distribution of primes — only the logical
structure of the quantifier in the definition of $\Omega_A$. Formally, in Lean this is `unfold OldFree` followed by
`simp only [not_forall, not_not]` and the extraction of the quintuple `⟨q, hq, h5, hA, hdvd⟩`.

Why this matters substantively. The $q\le A$ we found is an "old" prime: it already belongs to the traversed
scale, and the division $q\mid 6t+\eta$ means that the side $6t+\eta$ factors as
$q\cdot(6t_1+\eta_1)$ with a smaller centre $t_1$. This is exactly the old-peel configuration of [19](19_OldPeel.md), and hence by
`old_peel_height_drop` we have a **descent edge** $t_1<t$. That is, case (3) does not merely
classify the centre — it immediately supplies an outgoing downward edge with a proven height drop.

## Cases (1)+(2) resolved: old-free yields a twin or a composite side

Now the opposite branch: an old-free centre. Here we need a case split on the primality of the sides.

**Theorem (`oldfree_twin_or_composite`).** *For every $t$*
$$\mathrm{Twin}(t)\ \lor\ \neg\,(6t-1)\ \text{prime}\ \lor\ \neg\,(6t+1)\ \text{prime}.$$

This is a constructive tautology: by the law of the excluded middle for the primality of each side, either
both are prime (and then $\mathrm{Twin}(t)$), or at least one is composite. In Lean — a double `by_cases` on
`(6*t-1).Prime` and `(6*t+1).Prime`. It is stated without the hypothesis $\mathrm{OldFree}$: the disjunction
itself is unconditional, and old-free is brought in only in order to *read* "composite side" as
active descent (the next theorem).

> **Note.** The separation of (1) and (2) is the separation of "sink" and "descent" inside the clean zone.
> Twin is the receiving terminal we are aiming for. A composite old-free side is not a terminal: as
> we are about to show, it must have a divisor *above* the threshold $A$, that is, a new edge.

## Active descent: a composite old-free side has a large divisor

The key to case (2) being a descent rather than a dead end lies in the following observation.

**Theorem (`composite_oldfree_has_big_divisor`).** *Let the side $side=6t+\eta\ge2$ be composite and
old-free (no prime $q\le A$ divides it). Then it has a prime divisor $b$ with $b>A$:*
$$\exists\,b\ \text{prime},\ A<b\ \land\ b\mid side.$$

The proof is transparent and appeals to no analysis whatsoever. A composite number $side\ge2$ has a
minimal prime divisor $b=\mathrm{minFac}(side)$ (`Nat.minFac_prime`, `Nat.minFac_dvd`). If
we had $b\le A$, then $b$ would be a prime $\le A$ dividing $side$, directly contradicting old-free. Hence
$b>A$. In Lean this is `by_contra hle; exact holdfree side.minFac hb (by omega) hbd` — a one-line
proof by contradiction.

Why this is precisely "active Euclidean descent". The divisor $b>A$ factors the side as
$6t+\eta=b\cdot U$ with a new factor $U<side$. This is the start of a new sieve step, now at a larger scale:
the centre is reprocessed rather than vanishing. Thus both non-twin branches of the clean zone are equipped
with an outgoing edge.

> **Note.** Here one sees why exactly the old-free hypothesis is needed. Without it, "composite side"
> says nothing about the size of the divisor — it could be small and already traversed. Old-free
> excludes all small primes, so the minimal divisor of the composite number is *forced* to
> be new (`>A`). This is a purely threshold argument, without a single appeal to the density of primes.

## The sign law of repeated old-peel

A separate link, yet necessary for gluing the chain together, is how the sign $\eta$ behaves upon passing to
a smaller centre. It fixes that reprocessing a centre preserves the "polarity" of the neighbour predictably.

**Theorem (`peel_sign`).** *Let $6t+\eta=q\,(6t_1+\eta_1)$ with $\eta,\eta_1,\omega\in\{\pm1\}$ and
$q\equiv\omega\pmod 6$. Then*
$$\eta_1=\omega\cdot\eta.$$

The proof is modular algebra. From $q\equiv\omega\pmod6$ we write $q=\omega+6k$, substitute into the
peel equation, and obtain $6t+\eta-\omega\eta_1\equiv0\pmod6$. Since $\eta,\eta_1,\omega$
range only over $\pm1$, a finite check of the eight sign combinations (`rcases ... <;> omega`)
closes the identity $\eta_1=\omega\eta$. No analysis — only a residue modulo $6$.

Substantively this is the sign-agreement law (7.1): upon division by an old prime $q$, its class
$\omega=q\bmod6\in\{\pm1\}$ transfers the sign of the active side from parent to child. It is a fact of the same
spirit as `old_peel_sign` ($\delta=-\pi\varepsilon$) in [19](19_OldPeel.md), but written in the language of quotient centres.
It guarantees that the chain of old-peels does not "lose" the orientation of the sides — a necessary condition
for the correctness of the ledger's entire rigid signature.

## Assembly: the full dichotomy of the centre

The three elementary links assemble into one unconditional theorem — the heart of Lemma 6.1 on regeneration.

**Theorem (`regeneration_dichotomy`).** *For every centre $t$ and threshold $A$, exactly one
of the following outcomes holds:*
$$
\mathrm{Twin}(t)
\ \lor\
\Bigl(\neg\,\mathrm{OldFree}(A,t)\ \land\ \exists\,q,\ q\ \text{prime},\ 5\le q\le A,\ q\mid 6t\pm1\Bigr)
\ \lor\
\Bigl(\mathrm{OldFree}(A,t)\ \land\ \bigl(\neg(6t-1)\ \text{prime}\ \lor\ \neg(6t+1)\ \text{prime}\bigr)\Bigr).
$$

The proof is `by_cases hof : OldFree A t`, and each branch is closed by a link already proven:

- if the centre is *not* old-free — we take case (3) via `not_oldfree_gives_peel` (there is an old-peel edge);
- if the centre is old-free — via `oldfree_twin_or_composite` either it is a twin (a sink), or one side
  is composite (case (2), where `composite_oldfree_has_big_divisor` yields an active-descent edge).

The upshot: `regeneration_dichotomy` is **complete and unconditional** (standard axioms, no `sorry`).
Every quotient centre falls into exactly one of the three elementary classes, and in two of them — (2) and
(3) — we have explicitly exhibited an outgoing descent edge, while in the third — (1) — a legitimate twin
sink. This is precisely the elementary core for whose sake the whole reduction was undertaken: a
classification of the centre *without counting, without distribution, without the PNT*.

> **Note.** Let us stress what is proven and what is not. `regeneration_dichotomy` proves
> the *classification* of $t$. From it the *existence of an edge* in cases (2), (3) follows immediately: for (3) the height
> drop $t_1<t$ is `old_peel_height_drop` from [19](19_OldPeel.md), already proven; for (2) the edge
> $6t+\eta=b\cdot U$ exists by `composite_oldfree_has_big_divisor`, and its strict height drop
> is a separate elementary lemma of Euclidean descent (of the same type as the height drop, and requiring no
> counting). In none of (1), (2), (3) is there a dangling terminal.

## Where the input remains: case (4), fan-in

The dichotomy exhausts three classes. But the full picture of regeneration in NOPSL included a *fourth*
outcome — the one we honestly do not derive from the definition of $\Omega_A$.

> **Hypothesis (fan-in / Hall, audit §13.C).** At the bounded scale, where the carrier-scale mass
> of pedigrees condenses into a bounded set of centres, a *fan-in defect* is possible: many distinct
> pedigrees map to one and the same centre $t$. This is a statement *about the set of pedigrees*, not
> about the divisibility of a single side, and therefore it is **not derivable** from the predicate $\mathrm{OldFree}(A,t)$.

It is exactly this case (4) that remains the `regenerate` field of the abstract `OldPeelLedger` of [20](20_NOPSL.md). The difference
is fundamental: cases (1)–(3) are a theorem (`regeneration_dichotomy`, proven by the compiler), while case
(4) is a structural premise of the payment ledger, requiring that the rigid cycle of [09](09_Cycle.md)/[11](11_TwoTransport.md) be
a genuine engine — that very forbidden object of infinite descent (see the [glossary](GLOSSARY.md)) — with a rigid signature (audit §13.D).

> **Closure plan.** It is natural to conjecture that fan-in is controlled not by counting but by a **Hall
> condition** on the bipartite correspondence "pedigree — centre": if the carrier mass nowhere exceeds
> the capacity of the receiving centres, there is no fan-in defect and `regenerate` holds structurally. This leads
> to the Product/Hall construction (see later [29](29_CarrierBridge.md)) and to a separating scale, but already outside the elementary
> algebraic core of this chapter.
>
> The observation from the numbers ([19](19_OldPeel.md), `RESULTS_oldpeel.md`): regeneration
> $t>0$, the sign law, and the height drop are confirmed on 100% of 3000 real rank-1 catches — that is,
> the regeneration mechanism is observed, and what remains open is exactly the control of its *multiplicity*, not of its
> very existence.

## Summary and a bridge to the next chapter

We have opened up the premise `regenerate` from the inside. The author's Lemma 6.1 is formalized: the elementary core
— the full dichotomy of the centre (`regeneration_dichotomy`), the sign law (`peel_sign`), and
the active-divisor lemma (`composite_oldfree_has_big_divisor`) — is proven in Lean without distribution.

**Conclusion.** Regeneration in cases (1)–(3) is a genuine theorem, not a reduction: a twin sink or an explicit descent edge
at every centre. The nontrivial remainder is localized in exactly case (4) — fan-in/Hall — and in
the rigid-cycle requirement; it remains an explicit structural input, just as the source itself declares (§13: "under
A–E, regeneration is proven"). The dichotomy closes items A, B of the audit; C, D remain an input.

Thereby fan-in — the only thing that now separates us from full regeneration — turns out to be a
question of the **multiplicity** of the map from pedigrees to centres, that is, a question of the *filling density*
of the receiving centres. In [22](22_Residuals.md) we take the next step: we show how to lift the density assumption —
to transfer the control of fan-in from a hypothesis about mass to a structural covering condition — and thus bring
case (4) closer to the same elementary regime in which cases (1)–(3) already live.

<!--navbot-->

---

[← 20. NOPSL](20_NOPSL.md) · [Table of contents](00_Overview.md) · [22. Residuals →](22_Residuals.md)
<!--/navbot-->
