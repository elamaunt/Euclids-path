# 56. The Collatz first cause: the decree that fell

<!--navtop-->
[← 55. Collatz](55_Collatz.md) · [Table of contents](00_Overview.md)
<!--/navtop-->

> Lean source: `Engine/CollatzFirstCause.lean` — now **entirely green**: the decree's post-mortem
> plus the surviving epistemics, with no quarantine import; the taint does not grow. The green front is
> `Engine/CollatzTugOfWar.lean` ([chapter 55](55_Collatz.md)), where the refutation witness
> `ropeLaw_universal_refuted` was forged. The historical record of the removed field `collatzBoundary` —
> `Engine/CausalClosureAxiom.lean` §18. The P/NP epistemic complement — `Engine/PNPFirstCause.lean`.
> Notation: 🟢 — machine-proven (axioms stated explicitly); 🟡 — AXIOM-TAINTED, conditional on the repository's
> single axiom `step00FirstCause`; 🔴 — an open input.

## Where we are

In [chapter 55](55_Collatz.md) Collatz was translated into the language of a tug of war and brought to an honest
fork: the green mechanics (the window budget, descent under rope advantage, the HERO "law ⟹ halting") and one
named 🔴 input — the universal law of rope dominance.

This chapter tells the story not of a static boundary but of its **life cycle**. We accepted a decree — and
through the very tripwire (an intentional explosion detector — see the [glossary](GLOSSARY.md)) that we had planted
in advance, we watched it fall. The order of events is this:

1. the boundary is *taken* — the rope law becomes the fourth field of the single axiom;
2. the decree discloses its *honest price* — only one arrow is proven, "the decree may overpay";
3. the universal form of the law is machine-*refuted* (witness `n = 27`);
4. the tripwire *fires* — keeping the field any longer would make the axiom inconsistent;
5. the field is *removed* — the boundaries are three again (twins, Riemann, Navier–Stokes).

There remained a second, deeper question as well: *why* does the problem resist solution so stubbornly — is there a
rigorous reason why Collatz can be neither proven nor refuted from inside the system? This answer survives the
decree's fall entirely: both internal decisions still cost a perpetual engine.
To refute Collatz is literally to build a perpetual engine (a theorem with a genuine construction);
to self-ground the law from inside is to cross one's own boundary, which self-destructs. The only key to the
solution has remained external: verification.

Let us say it at once and plainly: **the decree fell**, and this is not a defeat of the programme but its best
result. The discipline — the disclosed price and the armed tripwire — worked exactly as designed. Below is the
whole story.

## The story of the fourth boundary: how the decree was taken and removed

The universal law of rope dominance was accepted **by decree** — not as a separate axiom, but as a new field of
the repository's single axiom `step00FirstCause`. At the moment of acceptance the structure looked like this:

```
structure Step00FirstCause : Prop where
  origin, firstFrame          : True                       -- markers of the event 0 → 1
  causalBoundary              : …                           -- the twin node
  riemannBoundary             : RiemannManifestationLaw     -- Riemann (§10)
  nsBoundary                  : NsSolutionBalanceLaw        -- Navier–Stokes (§15)
  collatzBoundary             : ∀ n ≥ 1, RopeCountingLaw n  -- Collatz (§18) ← the fourth
```

### Why the boundary was taken

The heuristic sign was favourable — as with Riemann and Navier–Stokes, which is why the boundary was taken at all
(unlike Mersenne §16, where the sign is inverted and the field was deferred). The harnesses (`RESULTS_collatz.md`)
showed a contracting engine: a mean geometric per-step drift of `0.864 < 1`, a balance `halvings/triplings = 2.016`
against the threshold `log₂3 = 1.585`, and the absorbing bottom `1 → 2 → 1`.

And — the crucial point for the honesty of the moment — **no forged refutation** (a machine-built counterexample
to the universal form of the law) **was known at that hour**. For
`RopeCountingLaw` there was neither a green proof (that would have entailed Collatz) nor a witness of falsehood. In
this respect the decree seemed to have exactly the same epistemic status as the twin node and the Riemann
manifestation law: unknown in either direction, sign favourable — take it as a boundary.

### The honest price, disclosed at once

As with Navier–Stokes (§15), the price was disclosed at the same moment as the decree. Only the arrow
"boundary ⟹ conjecture" was proven; the converse was unknown. The counting law could turn out strictly *stronger*
than the conjecture: the window budget is one-sided, and only the value law (the "condemned man's bridge") enjoyed
an ⟺-form. The conclusion was recorded plainly: **the decree may overpay.**

### The tripwires: detectors planted in advance

Together with the field, two 🟡 tripwires were laid into the theory — intentional explosion detectors (both were
deleted together with the field and are therefore named here in italics, as history rather than as living code):

- *collatzQuarantine_inconsistent_if_law_refuted* — a refutation of the law ⟹ `False` exactly here;
- *collatzQuarantine_inconsistent_if_nonconvergence_exhibited* — a non-converging trajectory ⟹ `False` here.

Their meaning was one and the same: consistency of the extended theory ⟺ irrefutability of the conjecture. If the
law should ever prove false, this construction was meant not to stay silent but to *burn first* — and point a finger.

### The refutation and the removal

"May overpay" proved prophetic: the decree overpaid **into falsehood**. The mechanics is dissected in
[chapter 55](55_Collatz.md); in brief — for the climbing trajectory `n = 27`, the road to one takes 41 engine
moves against 29 rope pulls, and no window *from the start* gives the rope an advantage (the tail in the cycle
`1 → 2 → 1` never recovers the deficit).

The heuristic measured the *aggregate* balance, while the law demanded an
advantage in a window from *every* position — which climbing orbits violate. This is machine-recorded:
`not_ropeCountingLaw_27` 🟢 and `ropeLaw_universal_refuted` 🟢 (kernel `[propext, Quot.sound]`, witness
`n = 27`).

The tripwire fired exactly as designed. `collatzQuarantine_inconsistent_if_law_refuted` showed: to keep the
field any longer is to make the single axiom inconsistent. Therefore **the field and the tripwires left the axiom
together** — the detector and the object it guarded were removed in one motion. In `Step00FirstCause` there are
again three boundaries:

```
structure Step00FirstCause : Prop where
  origin, firstFrame  : True
  causalBoundary      : Step00CausalClosureAxiom
  riemannBoundary     : RiemannManifestationLaw
  nsBoundary          : NsSolutionBalanceLaw          -- collatzBoundary removed
```

> **Note (what exactly is proven).** What was refuted is the *universal* form of the law —
> `∀ n ≥ 1, RopeCountingLaw n`. This is not a refutation of the Collatz conjecture: the law was strictly stronger
> than it, and its fall says only that Collatz cannot be closed by *such* a decree. The conjecture itself remains open.

The decree's post-mortem is gathered in a single green summary, with three leaves:
(1) the universal rope law is false (`ropeLaw_universal_refuted`) — a decree boundary on it is impossible;
(2) the per-n law still entails halting (`reaches_one_of_countingLaw`, the conditional mechanics is alive);
(3) a refutation of the conjecture itself still carries a perpetual engine (`nonHalting_carries_perpetual_engine`).

**Theorem 56.1** (`collatz_decree_postmortem`). 🟢 Three statements at once: (1) the universal law is false,
$\neg\,\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)$; (2) under the law an orbit converges,
$\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)\Rightarrow \exists K,\ \mathrm{iter}\,K\,n = 1$; (3) every
non-converging orbit carries a perpetual tail, $\forall n,\ (\forall K,\ \mathrm{iter}\,K\,n\neq 1)\Rightarrow
\exists j,\ \mathrm{NonDescendingOrbit}(\mathrm{iter}\,j\,n)\wedge \forall K,\ \mathrm{iter}\,K\,(\mathrm{iter}\,j\,n)\neq 1$.

The implication that "may have overpaid" survived as true and useless: "the universal law ⟹ convergence
everywhere" holds, but its premise is now machine-false, so it can no longer be fed universally. All the
content has moved into the per-n form `reaches_one_of_countingLaw`.

**Theorem 56.2** (`ropeLaw_would_imply_collatz`). 🟢 $\bigl(\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)\bigr)
\Rightarrow \forall n\ge 1,\ \exists K,\ \mathrm{iter}\,K\,n = 1$. The implication holds, but by Theorem 56.1
its premise is machine-false.

## The vacuum and its missing gap

Below are the cross-sections that the decree's fall **did not touch**: they were green and remain green.

At the bottom of the rope world lies the cycle `1 → 2 → 1` — an absorbing state with no way out. Let us call it
the **vacuum**: the ground state of the dynamics, its lowest note. `vacuum_has_no_gap` 🟢 (even without Classical.choice):
there is no leaving the vacuum, ever — `iter d 1 ∈ {1, 2}` for all `d`.

The conjecture asserts that the vacuum is unique and everything falls into it. To refute it is to exhibit a gap in
the vacuum: a second bottom, another cycle, an orbit living forever without touching the ground state. What does
such a gap cost?

## The orbit minimum and the tail engine

The answer is obtained by one look at the minimum. `exists_min_position` 🟢 (the standard triple): every orbit has
a position of global minimum of its value — the natural numbers are well-ordered.

The only non-constructivity is the choice itself of "is there a smaller one" (`Classical.em` does the work here),
and we disclose this honestly: one cannot learn the position of the minimum without walking the orbit; but it
*exists* unconditionally.

The tail of the orbit from the minimum **never dips below its start** — and that is exactly the perpetual engine
of [chapter 55]: a non-descending orbit which (by `nonDescendingOrbit_is_perpetual_engine`) loses not a single
window to the rope and never halts.

`nonHalting_carries_perpetual_engine` 🟢 (the central one). If an orbit never reaches 1, then its tail
from the minimum position is a non-descending, never-halting orbit. The construction is *genuine*, not by
contradiction: the tail is exhibited explicitly. Let us read it aloud: **every Collatz counterexample carries a
perpetual engine within it.** A gap in the vacuum costs exactly a perpetual engine.

**Conclusion.** The Collatz conjecture does not *resemble* a statement about the impossibility of a perpetual engine —
it *is* one, word for word, for the map `T`: an orbit reaches 1 ⟺ it has no perpetual tail.

## The narrative: perpetual information extraction, which does not exist

Here is the spine of the chapter, and it explains ninety years of unsolvedness by a single physical "cannot". Note:
all of this was proven *without* the decree and survives the decree's fall entirely.

**Collatz is perpetual information extraction.** A counterexample — an orbit living forever above its bottom and
never falling into the vacuum — is a machine that *draws endlessly*: it loses not a single window to the rope,
moves forever, never surrendering itself to the cycle (`nonHalting_carries_perpetual_engine`).

And "learning the cause from inside" — deriving the universal rope law by an internal proof — would mean
extracting from the system an infinite fact about the whole number line without ever leaving it.

**Infinite information extraction is impossible.** Define an internal self-grounding of the law's foundation:
a construction carrying the law itself AND a witness that it was derived from inside — crossing its own boundary.

**Definition 56.3** (`InternalisedCollatzGround`). A structure with two fields: `ground` — the law itself,
$\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)$; `beyondOwnHorizon` — a witness of crossing the boundary,
$\neg\,\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)$. The abbreviation `InternalKnowledgeOfCollatzCause`
identifies "internal knowledge of the cause" with this self-grounding.

As with the twins, the form is honestly tautological ("to prove P while crossing the boundary of P" collapses into $P\wedge\neg P$);
substantively it is an *identification*: the attempt at internal grounding is already a burnt engine
construction. Formally the self-grounding self-destructs by its very form — `no_internalisedCollatzGround` —
and this yields the unknowability of the first cause.

**Theorem 56.4** (`collatzCause_unknowable`). 🟢 (with no axioms at all) $\neg\,\mathrm{InternalKnowledgeOfCollatzCause}$:
internal knowledge of the Collatz first cause is impossible. The proof is direct: the two fields of Definition 56.3
contradict each other, $\texttt{beyondOwnHorizon}\ \texttt{ground} : \mathrm{False}$.

And after the decree's fall — stronger still.

**Theorem 56.5** (`internalGround_impossible_a_fortiori`). 🟢 $\mathrm{InternalisedCollatzGround}\Rightarrow
\mathrm{False}$, but now *by content*: the field `ground` is refuted directly (`ropeLaw_universal_refuted`),
not through the self-destruction of the form. Unknowability now holds doubly — both as an impossible form
(Theorem 56.4) and as false content.

This is the same law that forbids a perpetual engine on ℕ (`no_infinite_descent`) and that in the main programme
takes the shape "knowledge from inside costs infinite energy" (the finite-knowledge barrier,
`Engine/FiniteKnowledgeBarrier`, chapter 33; read via Landauer — knowledge is physical, and extracting the cause
from inside would violate the same balance that forbids the engine).

**That is why the engine is "perpetual" — as an object irremovable from inside.** Since the conjecture is
identified with "there is no perpetual engine", and internal knowledge of the cause is impossible, exactly the
perpetual engine remains the thing that can be neither exhibited nor excluded by internal derivation: if a
counterexample exists — it is genuinely perpetual; and that none exists cannot be proven from inside.

**Hence — verification only.**

**Theorem 56.6** (`unknowable_or_collatz_fails`). 🟢 The substantive dichotomy (no ex falso in the statement):
$\neg\,\mathrm{InternalKnowledgeOfCollatzCause}\ \vee\ \exists n\ge 1,\ \forall K,\ \mathrm{iter}\,K\,n\neq 1$ —
*either the cause is unknowable, or Collatz is false*. The left disjunct is proven (Theorem 56.4). The right one
is discovered not by derivation but by verification — by exhibiting a concrete non-converging orbit. All of this
is gathered in one green theorem that machine-encodes the narrative:

**Theorem 56.7** (`collatz_verification_not_derivation`). 🟢 A conjunction of three links in a single statement:
1. infinite internal extraction of the rope law is impossible, $\neg\,\mathrm{InternalKnowledgeOfCollatzCause}$
   (Theorem 56.4);
2. therefore the only internal trace of a counterexample is a perpetual engine
   (`nonHalting_carries_perpetual_engine`);
3. hence the solution is either unknowable from inside, or accessible only by *verification* of an orbit
   (Theorem 56.6).

**And verification finds-or-does-not-find exactly as far as we look.** The harnesses
(`RESULTS_collatz.md`) are precisely the "how far": `n ∈ [2, 200000]`, a divergence guard at 100000 steps.
In this window there are no counterexamples; but no finite window can *prove* the universal law — it can
only fail to find a refutation within its own horizon. (And — as we now know — *in the limit* the universal form
of the rope law is false after all: not because an orbit diverges, but because the law demanded more than is
true. Verifying convergence and verifying the law are not the same thing.)

This is the same horizon of the finite observer as in chapter 33: a finite system sees only the pure classes of
its own scale, and knowledge of the infinite requires cofinal (not finite) information. The answer exists; it can
be found only by verification, and only up to the edge that the gaze can reach.

## Summary: the solution is locked behind the engine

**Theorem 56.8** (`collatz_no_internal_decision_without_engine`). 🟢 (green, axiom-free) A conjunction of three
leaves: (1) *to refute = to build a perpetual engine* — $\forall n,\ (\forall K,\ \mathrm{iter}\,K\,n\neq 1)
\Rightarrow \exists j,\ \mathrm{NonDescendingOrbit}(\mathrm{iter}\,j\,n)\wedge\forall K,\ \mathrm{iter}\,K\,(\mathrm{iter}\,j\,n)\neq 1$
(a genuine construction); (2) *to prove from inside = to self-ground* — $\mathrm{InternalisedCollatzGround}\Rightarrow\mathrm{False}$,
it self-destructs; (3) *the per-n rope law would entail per-n halting* — $\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)
\Rightarrow\exists K,\ \mathrm{iter}\,K\,n = 1$. But the universal feed is gone: the universal law is refuted
(Theorem 56.1), the decree door is closed by a forged witness.

**Theorem 56.9** (`collatz_open_status`). 🟢 The final epistemic status of Collatz after the decree's fall
(the mirror of `pnp_locked_behind_engine_status`, but now **without the decree conjunct**) — a conjunction of four:
$\neg\,\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)$ (the universal law is refuted, theorem) $\wedge$
$\neg\,\mathrm{InternalKnowledgeOfCollatzCause}$ (internal knowledge is impossible, theorem) $\wedge$
$\bigl(\forall n\ge 1,\ \mathrm{RopeCountingLaw}(n)\Rightarrow\exists K,\ \mathrm{iter}\,K\,n = 1\bigr)$
(the per-n law entails halting, conditional) $\wedge$ $\bigl(\forall n,\ (\forall K,\ \mathrm{iter}\,K\,n\neq 1)
\Rightarrow\exists j,\ \mathrm{NonDescendingOrbit}(\mathrm{iter}\,j\,n)\wedge\forall K,\ \mathrm{iter}\,K\,(\mathrm{iter}\,j\,n)\neq 1\bigr)$
(a refutation of the conjecture would build a perpetual engine, theorem).

> **Note (what we do not claim).** This is not Gödelian independence: we have not proven that Collatz is
> unprovable in Peano arithmetic. What is proven is something else, inside our system and rigorously: both paths
> of internal decision — refutation and self-grounding — run into one and the same forbidden object, and the
> decree third path is machine-closed (`ropeLaw_universal_refuted`). The Collatz conjecture remains **open** 🔴.

## P/NP beyond the same horizon

This wall has a second slope, and it falls not into Collatz but into P/NP. The verifying machine there is not a
metaphor: it is literally a **pure computer on finite fuel with strict rules**. In the repository
it is assembled as `RankedForwardGraph` — the rules are its `Step`, the fuel is `lexRank`, the law of fuel
consumption is `RankFastTraversal` — and launched from an arbitrary, "random" initial position
(the 5-adic chain at A ≤ 4). This is exactly the "system with random initial conditions but strict rules"
that was spoken of ([chapter 39](39_PNPRankPayment.md), the rank-payment machine).

To decide P/NP *from inside* means to pay with one finite key, injectively, for every certificate of an
*unbounded* supply — `FullRankCertificatePayment` for `UnboundedCertificateSupply`
(the supply is the infinite admissible family of certificates with which a deviation pays; see
the [glossary](GLOSSARY.md)). It is the same perpetual-engine contradiction as with Collatz, translated word for
word: "a non-falling tail = an engine" becomes "full payment of an unbounded supply =
an engine".

Both perish against the same wall of well-foundedness — the pigeonhole: **there is no injection of an infinite
index into a finite key, hence no ℕ-descent.**

This is recorded by the green theorems of `Engine/PNPFirstCause`: `no_internalisedPNPGround`,
`pnpCause_unknowable` ("cannot be known from inside" — not a slogan but a theorem) and
`internalPNPDecision_carries_perpetual_engine`, where the internal decision and the perpetual engine on ℕ are
brought to a single wall through `no_perpetual_engine_on_nat`. The summaries are `pnp_no_internal_decision_without_engine` and
`pnp_locked_behind_engine_status`.

The event horizon reads especially vividly here. The machine's finite fuel (its rank budget) is precisely its
**event horizon**; a decision that needs to reach *past* it — to pay for an unbounded
supply — is unattainable from inside. The answer is accessible only by *verification* and is found exactly as far
as the finite-fuel gaze reaches. That is why P/NP becomes unprovable-from-inside in the very same
sense in which the cause of Collatz is unknowable — "as far as the gaze reaches" here is not a figure of speech
but the edge of the budget.

Let us say plainly what is **not** here. This is not a proof of classical P≠NP: the frame layer is plastic
(`allPFrame`/`constantsFrame`), and nothing about the real P/NP follows from it. And this is not Gödel — neither an
incompleteness theorem nor a fixed point, but a pigeonhole self-destruction.

And here is the difference that the decree's fall rewrote: previously P/NP had no decree boundary while Collatz
had one. **Now neither has one** — both trilemmas, the mandatory tests of a boundary candidate, are closed
machine-wise. For P/NP it is split (`pnpLawUniversal_refuted`, `pnpLawExistential_green`
proved that no honest third field of `step00FirstCause` exists); for Collatz it has just been closed by the
forged refutation `ropeLaw_universal_refuted` (the decree taken and removed).

Therefore this entire result is green, adds not a single axiom, and **the repository's taint does not grow**
(after the removal of the fourth boundary it returned to 47). Everything holds at A ≤ 4.

**Section takeaway.** Thus the same prohibition closes, read now through a finite-fuel verifier:
**the machine that verifies any conjecture is itself the object it cannot surpass.**

## Philosophical digression: the decree that fell honestly

This chapter has a direct physical twin — **the stability of the ground state**. The vacuum of quantum theory is
not "nothing" but the lowest energy state; all the stability of the world rests on the fact that one cannot sink
below the vacuum. To find a "gap in the vacuum" — a state beneath the ground state — would bring everything down:
from such a gap one could draw energy endlessly, and that is precisely a perpetual engine. Physics forbids it not
by ordinance but by the very structure of the spectrum: there is a bottom, and it is unique.

But deeper than the physical analogy here lies a methodological one. We took a boundary by decree, disclosed its
price, planted a tripwire — and the tripwire fired. **A decree that fell honestly is worth more than a decree that
stands unexamined.**

The programme neither hid the overpayment nor forgot it: it *recorded the fall as a
theorem*, not as oblivion. It was exactly the discipline one might have dismissed as pedantry — the disclosed
asymmetry of the arrows, the armed detector `collatzQuarantine_inconsistent_if_law_refuted`, the demand for
machine verification — that caught the falsehood. Honesty here is not an ornament but a working organ.

And here is where this places Collatz. It is no longer "a problem with an honest decree" but a problem with a
**closed trilemma** — alongside Yang–Mills (chapter 40), where the universal candidate likewise fell to a forged
refutation. In neither case is a decree possible: not because we failed to find a way to feed it, but because
feeding it would mean feeding a falsehood, and the machine sees that.

What remains open is the heart itself: convergence. `1 → 2 → 1` is the vacuum of the rope world; a second bottom, a
foreign cycle, a diverging orbit would cost exactly a perpetual engine. Whether there is a gap or not — this cannot
be certified from inside: the attempt to walk the entire infinite line is the very forbidden engine. The one
honest key has remained external — **to verify exactly as far as the gaze can reach.**

## Place in the greater arc

Collatz completes the eighth mask differently from how it began it. It entered as a mirror of the
[first cause (ch. 33)](33_CausalFirstCause.md), of [Riemann (38)](38_RiemannFirstCause.md) and of
[Mersenne (43)](43_MersenneFirstCause.md): a green impossibility of the engine from inside plus an external
boundary accepted by decree at an honestly disclosed price. And it exits with the same green impossibility, but
**without a boundary**: the decree taken and removed, the trilemma closed by a forged refutation, as with Yang–Mills.

What sets Collatz apart, and what the decree's fall only sharpened, is that the engine here is **literal** (the
tail of a non-converging orbit *is* perpetual motion on ℕ, not a surrogate), and that is why the narrative
"verification, not derivation" reads most clearly on it: `no_infinite_descent` — one prohibition — turns out to be
also a prohibition on infinite information extraction. For the eighth time it brings us right up to the boundary
of the knowable — and this time it shows that even the boundary itself, set too generously, honestly collapses
under its own price.

<!--navbot-->

---

[← 55. Collatz](55_Collatz.md) · [Table of contents](00_Overview.md)
<!--/navbot-->
