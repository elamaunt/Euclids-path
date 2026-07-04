# Hodge: quantised charges and payment by cycles

<!--navtop-->
[← 41. Navier–Stokes: smoothness](41_NSSmoothness.md) · [Table of contents](00_Overview.md) · [43. Mersenne through the first cause →](43_MersenneFirstCause.md)
<!--/navtop-->



> Lean source: `Engine/HodgeFront.lean` — the green chain and the trilemma, all 🟢;
> `Engine/CausalClosureAxiom.lean` §14 — one tripwire.
> Status legend: 🟢 — proven under the standard axioms;
> 🟡 — proven conditionally on the axiom `step00FirstCause`; 🔴 — an open input.

## The reading: charge, payment, completeness

We read a Hodge class as a **quantised charge**: a rational cohomology class of the aligned type
`(p,p)` — a "permitted quantity". An algebraic cycle is the **payment** of a charge, its realisation
by a genuine geometric object. The Hodge conjecture is then a completeness statement: *every quantised
aligned charge is paid*. And an unpaid charge, were it to exist, would open an infinite strict
descent along a natural height (the denominator, or the complexity of the remainder) — that is, a forbidden perpetual engine.

The honest boundary — stated at once and out loud, as in the previous three chapters. There is *no*
Hodge theory in mathlib: we checked this literally — the word "Hodge" occurs in the pin exactly three
times, and all three miss (a citation of Hodges's book on *model* theory and mentions of p-adic Hodge
theory in the comments of the period rings). There are no Hodge classes, no algebraic cycles, no
cohomology of varieties, no hodge-star operator.

Therefore `HodgeLedger` is an abstract ledger, a bookkeeping of charges (see the [glossary](GLOSSARY.md)):
classes, the predicates `IsHodge` and `IsAlgebraic`, a height `height : Cls → ℕ` and the quantisation
anchor "paid ⟺ height 0". **We do not solve the Millennium Problem and do not declare it solved**; the
remainder is a named input, `DescentLaw` — a gate: an honestly named missing statement.

## The engine is dead unconditionally — and that is the branch's headline

Hodge brings news that none of the other branches had, and it is worth starting there. The engine here
is dead **always**, without a single hypothesis.

**Theorem** (`isEmpty_unpaidDescentChain`, 🟢). *An infinite strictly descending chain of unpaid
charges exists in no model whatsoever.* The axiom list is just `[propext, Quot.sound]`, without even
choice: this is pure EPMI at `A = 1`.

Compare with Yang–Mills to see the asymmetry. There the real-valued ladder *lived* precisely at
masslessness and was killed by a *decreeable* quantisation law — quantisation was a separate input.
Here quantisation is **built into the model itself**: the height is a natural number, `height : ℕ`, and
so the engine is dead in every model, unconditionally. The whole substance of the branch has shifted
accordingly: what remains contested is not "is the charge quantised" (yes, by construction), but the
existence of the payment *steps* themselves — that is, the law.

## The hero and the collapse of the cost mirror

The descent law is precisely the substantive input: every unpaid charge admits a *payment step* — a
transition to an unpaid charge of strictly smaller height. As soon as it holds, the conjecture follows:

**Theorem** (`hodgeProperty_of_descentLaw`, 🟢 — the hero). *Descent law ⟹ the model's Hodge
conjecture.* The proof is strong induction on the height (no choice needed); the same can be done by
the chain route through `descentSeq` — the mirror of Yang–Mills's ladderSeq. And symmetrically, a model
of "the law plus an unpaid charge" does not exist (`no_unpaid_lawful_model` 🟢).

The converse is honestly vacuous: `descentLaw_of_hodgeProperty` is proven by an empty quantifier (if
everything is paid, there are no unpaid charges) — unlike Yang–Mills, where the reverse rank was built
for real. And from here — the decisive audit:

**Theorem** (`descentLaw_iff_hodgeProperty`, 🟢). *For every model the descent law is equivalent to
the Hodge conjecture — green, and with no boundary anywhere.*

This is once again the form of the condemned man's bridge: to decree the law for a model would be to
decree its conjecture verbatim. There can be no sixth field of the decree; what is missing is not a
proposition but a data anchor — genuine rational `(p,p)`-classes.

## Why there is no sixth boundary — and the branch's unique point

The trilemma — the mandatory three-sided check of a boundary candidate (see the [glossary](GLOSSARY.md)) —
confirms the verdict from every side, and one of its faces here is special.

The universal form of the
law is *refutable*: the forged model `cookedUnpaid` carries an unpaid charge of height 1, and a descent
step from it would run into paidness at height zero (that very quantisation anchor) — the decree would
blow up the quarantine.

The existential form is *already proven* and depends on no axioms at all
(`cookedPaid`: the law is vacuous, the conjecture verbatim) — the decree would be empty.

The third face, though, is unique. Mechanically transplant the manifestation form from Yang–Mills, but
over *chains* (over the engine). It **degenerates into a green theorem** (`hodgeChainManifestationLaw_green`
🟢): chains simply do not exist in any model, so the law over them is vacuously true.

This is a verdict of V2 type, not V3 — and here is why it matters not to confuse them: from an *empty*
type of witnesses one cannot assemble a V3 ("incompatible with the boundary"), because V3 needs a
witness *presented* in green.

The honest V3 witness
here must be not a chain but a single unpaid class, `cookedUnpaidClass` — it is presented by
construction, without choice, and with it the manifestation form is already incompatible with the
accepted boundary (`hodgeManifestationLaw_refutes_boundary` 🟢). The subtle difference between "the
engine is presentable" and "the deviation is presentable" surfaces here more distinctly than anywhere else.

The branch's single honest 🟡 is a tripwire (an intentional explosion detector, see the [glossary](GLOSSARY.md)),
`quarantine_inconsistent_if_hodgeManifestationLaw_decreed` (§14): a decree of the manifestation form would blow up the quarantine exactly here; its safety has been verified (the law
is equivalent to a global freeze, and the green world knows the freeze only at `A ≤ 4`).

## Philosophical digression: charge quantisation and completeness of the spectrum

The Hodge conjecture looks purely geometric, but its physical meaning is about charge quantisation and
about every permitted charge being carried by someone. In physics many quantities come only in integer
multiples: electric charge — in units of `e`; magnetic flux in a superconductor is quantised,
`Φ = n·h/2e`; and Dirac's argument shows that the mere existence of a magnetic monopole forces charge
to be quantised, `eg = n·ℏc/2`.

A Hodge class is exactly a **quantised charge of geometry**: a cohomology
class of rational type `(p,p)`, a "permitted quantity". And the conjecture says: every such charge is
*realised* by a genuine geometric object — an algebraic cycle. Every permitted charge has
a real carrier.

There is a precise physical analogue of this — the principle of **completeness of the charge spectrum**:
in a consistent theory (the "swampland" conjectures of quantum gravity, the absence of global
symmetries) every permitted gauge charge must be occupied by some state — there are no "empty"
permitted charges with no particle to carry them. Hodge is the geometric mirror of that completeness:
no empty `(p,p)`-charge without a carrier cycle. An unpaid Hodge class is a permitted charge without
a carrier, a hole in the spectrum of realisations.

And that is why the engine here is dead unconditionally, unlike Yang–Mills. Our quantisation is built
into the model: the height is a natural number. In physics this corresponds to charge quantisation
being a given of the setup, not a matter of dispute; only completeness is disputed — whether every
permitted level is occupied.

An unpaid charge would launch an infinite strict descent along the denominator, an eternal regress of
ever smaller "residual charges" — and infinite descent in an integer lattice is impossible. Hence the
whole substance of the conjecture has shifted exactly to where it stands in physics too: not "is the
charge quantised" (yes, by construction), but "is every permitted charge occupied".

**Conclusion.** The discreteness of the lattice is the same prohibition of the
perpetual engine that holds up the entire programme; and the completeness of its filling is the open
heart, which can neither be honestly decreed (the law is equivalent to the goal) nor proven without
genuine `(p,p)`-classes, of which the formalisation so far has none.

## Hodge beyond the same horizon

The wall against which the internal solutions of Collatz and P/NP shattered has a Hodge slope as well —
the branch's epistemic complement is assembled in `Engine/HodgeEpistemic.lean`. To solve the front *from
inside* would be to self-ground the per-model descent law: the machine would carry the law itself and,
along with it, the testimony that it derived it, crossing
its own horizon.

Such a pair (`InternalisedHodgeGround`) self-destructs in a single line
(`no_internalisedHodgeGround`), and therefore **"cannot be known from inside" is a theorem, not a
slogan**: `hodgeCause_unknowable` 🟢, with no axioms at all. Neither the status of the conjecture
itself nor its independence is thereby asserted — only the impossibility of internal self-grounding.

The contradiction is paid for by more than the mere shape of the pair — it has a second, engine route.
Under the per-model law an unpaid charge unfolds into a genuine infinite descent chain
(`unpaidDescentChain_of_descentLaw`) and is projected by the height into a perpetual engine on ℕ
(`unpaidClass_under_law_carries_perpetual_engine`).

From the pair itself the engine is also built **genuinely, not
ex falso** (`internalisedHodgeGround_builds_engine`) — and it is burnt by the same well-foundedness wall
`no_perpetual_engine_on_nat` as with Collatz and P/NP. Let us say honestly where the condition sits: the
engine rises from a deviation *under the law* — for Collatz a bare counterexample sufficed, whereas here,
without the law, a single unpaid charge does not even have a first step.

And the third leaf is familiar verbatim: the universal form of the law has already been refuted by
forging — `hodgeUniversal_forged_refutation` (a re-export of `hodgeLawUniversal_refuted`), that very
`cookedUnpaid` where the step from height 1 runs into the quantisation anchor. As with Yang–Mills and
now Collatz, the decree path through the universal is closed machine-wise; the only living option is
the per-model input — and it, by the collapse
`descentLaw_iff_hodgeProperty`, equals the goal verbatim.

The summary is gathered in `hodge_locked_behind_engine_status` 🟢:
the universal refuted / chains empty in every model / internal knowledge impossible / per-model law ⟺
the model's conjecture — **entirely green, the repository's taint does not grow**.

> **Note (what we do NOT claim).** This is NOT a solution of the Hodge conjecture and NOT Gödel: no
> incompleteness, no fixed point — only model-internal epistemics and ℕ-descent. The self-grounding
> pair is formally "ground + its negation"; its substance is paid for by the green identification of
> both sides with content (the law ⟺ the model's conjecture; the negation ⟺ the presentability of an
> unpaid charge, `not_hodgeProperty_iff_unpaidClass`) and by the genuine engine route. The pair carries
> no dichotomous novelty — its value is architectural: Hodge takes its place in the same "locked behind
> the engine" row as P/NP and Collatz
> (`hodge_no_internal_decision_without_engine`).

## Place in the greater arc

Hodge is the sixth front of one machine (twins → Riemann → P/NP → Yang–Mills → Navier–Stokes → Hodge),
and the root of all is the same: the impossibility of a perpetual engine. The series of trilemmas is
stable and settles into a distinct rule.

**Section takeaway.** An honest boundary of the decree exists only where the deviation witness is greenly *unpresentable* —
such are the twin node and the off-critical zero. And everywhere the deviation can be *forged* — frames
for P/NP, spectra for Yang–Mills, profiles for Navier–Stokes, unpaid charges here — the decree either
explodes or is empty, and what remains is a green conditional theorem with an honestly named input.

Hodge added its own colour to
this rule: when quantisation is built into the very model, the engine is dead unconditionally, and the
conjecture shrinks to a single question — do the payment steps exist.

<!--navbot-->

---

[← 41. Navier–Stokes: smoothness](41_NSSmoothness.md) · [Table of contents](00_Overview.md) · [43. Mersenne through the first cause →](43_MersenneFirstCause.md)
<!--/navbot-->
