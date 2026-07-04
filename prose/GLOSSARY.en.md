# Programme glossary

<!--navtop-->
[Table of contents](00_Overview.md)
<!--/navtop-->

> Every key notion of "Euclid's Path" in one place — briefly, with a pointer to the chapter where
> the notion is properly introduced. Chapters remind the reader of terms at first use, but this
> page can be revisited from anywhere.

## The machine and its laws

**Perpetual engine (Euclid's)** — an infinite strictly descending chain on a well-ordered line;
the programme's central forbidden object. It does not exist (`no_infinite_descent`) — this is
Fermat's infinite descent, rewritten multiplicatively. Everything else is a shadow of this
prohibition. See [chapter 01](01_EPMI.md).

**EPMI** — the impossibility core (Engine Perpetual Motion Impossibility);
proven on the bare Lean kernel, without even mathlib. See [chapter 01](01_EPMI.md).

**Rank / `lexRank`** — the "height" of a state: a natural number that strictly drops along
permitted steps. Finiteness of rank is "finite fuel": strict descent cannot last forever.
See [chapters 01](01_EPMI.md) and [24](24_BoundaryDecomp.md).

**Engine as method** — contraposition through the engine: to prove a goal `P`, we show
`¬P ⟹ engine`; engines do not exist — hence `P`. The common strategy of every branch.
See [chapter 00](00_Overview.md).

**Pigeonhole** — the boxes principle: a finite key cannot injectively label an infinite family.
The favourite form of contradiction in the P/NP branch and in the epistemics.
See [chapter 39](39_PNPRankPayment.md).

**Window / window budget** — a trajectory segment of length `k`; the window budget is the
multiplicative bound on growth/decline of the value over a window. The language of the Collatz
branch. See [chapter 55](55_Collatz.md).

## The honesty discipline

**🟢 / 🟡 / 🔴** — the three statuses of every declaration: 🟢 machine-proven under the standard
Lean/mathlib axioms; 🟡 AXIOM-TAINTED — conditional on the single axiom `step00FirstCause`;
🔴 — an open node or a named input. The legend lives in the [prologue](00_Overview.md).

**First cause / `step00FirstCause`** — the repository's single axiom: the intentional event
`0 → 1` with three causal boundaries (twins, Riemann, Navier–Stokes). It is accepted from
outside, because self-ignition from within would cost a perpetual engine.
See [chapter 33](33_CausalFirstCause.md).

**Boundary (of the decree)** — a substantive field of the first cause: a law accepted by decree
under an honestly disclosed price. Boundaries fall to forged refutations — that is how the
fourth, Collatz boundary fell. See [chapters 33](33_CausalFirstCause.md) and [56](56_CollatzFirstCause.md).

**Decree** — the intentional acceptance of a law by axiom (as opposed to proving it). An honest
decree must survive the trilemma and disclose its price ("the decree may overpay").

**Quarantine** — the module `Engine/CausalClosureAxiom.lean`, the only place where the axiom
lives; everything depending on it is machine-flagged.

**Taint / AXIOM-TAINTED** — the axiom's trace in a declaration's dependency list. The verifier
(`scripts/VerifyAll.lean`) recounts tainted declarations on every check; there are currently 47,
and nothing leaks into the green line.

**Tripwire** — an intentional explosion detector: a theorem of the form "if the boundary's law is
refuted, `False` is derivable exactly here". Tripwires are planted together with the boundary —
and they work: the Collatz one fired. See [chapter 56](56_CollatzFirstCause.md).

**Trilemma** — the mandatory test of a boundary candidate: is the universal form refutable, is
the existential form provable for free (vacuity), is the law a renaming of the goal. Failure of
any branch closes the decree path. See [chapters 39](39_PNPRankPayment.md)–[42](42_Hodge.md).

**Forged refutation** — a machine-built counterexample to the universal form of a law
("forging"). A forging in hand means: the boundary must not be taken. Examples: the Yang–Mills
ladder, orbit 27 for Collatz. See [chapters 40](40_YangMills.md) and [55](55_Collatz.md).

**Vacuity** — the situation where a candidate law holds for free (by a stub witness), so that
decreeing it would be pointless: the decree would be empty. See the trilemmas of chapters 39–42.

**Goal renaming** — a dishonest form of law, equivalent to the goal itself with no hypotheses at
all; exposed machine-wise by an iff-audit (the model case is `offCriticalBridge_iff_RH`). Such a
"law" must not be decreed: it is not a cause but a signboard. See [chapter 38](38_RiemannFirstCause.md).

**Ex falso** — "from falsehood, anything": a theorem whose only strength is the inconsistency of
its premise. Honesty requires flagging such routes and never passing them off as substantive.

**Data anchor** — the missing real object (a Turing machine, an operator, an analytic
continuation) without which a propositional law is not attached to the genuine problem. Anchors
are named as red inputs, with a disclosure of exactly what mathematics must supply.
See [chapter 39](39_PNPRankPayment.md).

## Witnesses and manifestation

**Witness** — a concrete object certifying a statement: a twin pair, an off-critical zero, an odd
perfect number. Checking a witness is usually cheap (sometimes literally `decide`); presenting
one is another matter entirely.

**Unpresentable witness** — a witness whose presentation would cost a perpetual engine: a
refutation "under the law with the books reconciled" builds an engine out of it. The foundation
of honest boundaries and manifestation fronts. See [chapter 43](43_MersenneFirstCause.md).

**Absence witness** — a witness that above a threshold there are *no* objects (for instance,
`CousinAbsenceAbove`); it gates the manifestation laws of the zoo. See [chapter 44](44_SidesAndPolignac.md).

**Manifestation / manifestation law** — the principle "a deviation must show itself": an
off-critical zero, a Goldbach violation, the absence of cousins — each must leave an unpayable
trace (a supply) wherever the books are reconciled. See [chapter 38](38_RiemannFirstCause.md).

**Ledger / "the books are reconciled"** — the bookkeeping of flows; "the books are reconciled"
means the projection resolves collisions at the given scale (a stable universe with no free
energy). On reconciled books an infinite supply is impossible — an engine is assembled from it.
See [chapter 24](24_BoundaryDecomp.md).

**Supply** — an infinite admissible family of flows/certificates: what a deviation "pays" with.
An unpayable supply on reconciled books = an engine. See [chapter 38](38_RiemannFirstCause.md).

**Front** — a branch module reading one problem through the engine prohibition: a green
structural half plus an honest gate (input). **Mask** — one of the great problems read this way;
there are seven of them plus an eighth (BSD). See the [coda](50_Coda.md).

**Gate / input** — a named 🔴 statement still missing on the way to the goal: `RopeCountingLaw`
(fallen), `DescentLaw`, `EngineBridge`. A gate is honestly named, not proven and not hidden.

**Hero** — the central conditional theorem of a branch, carrying the law all the way to the goal
("give the law — get the halting"): `reaches_one_of_countingLaw` for Collatz. Marked HERO in the
sources.

## Epistemics

**"Cannot be known" / `*Cause_unknowable`** — theorems on the impossibility of internal
self-grounding: proving the law from inside, crossing one's own boundary, is a self-destructing
construction (`P ∧ ¬P`), substantively identified with an already-burnt engine construction.
NOT Gödel: this is model-internal epistemics, not an incompleteness theorem.
See [chapter 33](33_CausalFirstCause.md).

**"The solution is locked behind the engine"** — the three-pronged summary: refuting from inside
= building an engine; proving from inside = self-grounding; only external verification or decree
decides. See [chapter 56](56_CollatzFirstCause.md).

**"Verification, not derivation"** — the closing epistemic formula: the answer is accessible only
by checking a witness, found exactly as far as the finite-fuel gaze reaches (the machine's event
horizon). See [chapters 55](55_Collatz.md)–[56](56_CollatzFirstCause.md).

**Event horizon (of the machine)** — the reach limit of a finite-fuel observer: its rank budget.
To reach past the horizon from inside = a perpetual engine. See [chapter 56](56_CollatzFirstCause.md).

<!--navbot-->

---

[Table of contents](00_Overview.md)
<!--/navbot-->
