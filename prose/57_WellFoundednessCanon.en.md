# 57. The well-foundedness canon: the engine reaches classical termination

<!--navtop-->
[← 56. The Collatz first cause](56_CollatzFirstCause.md) · [Table of contents](00_Overview.md)
<!--/navtop-->

The engine is one prohibition: no infinite strictly descending chain on a well-founded carrier
(`no_perpetual_engine_of_wellFounded`), and it transfers along **any** rank into a well-founded order
(`no_perpetual_engine_of_rank`, [01](01_EPMI.md)). Every front so far has been a corollary of that one
theorem. Here we turn it on the place where it is most at home — the classical **termination canon**,
results whose whole content is *there is no infinite descent*. Each becomes a green instance reusing
machinery already in mathlib; none adds an axiom, and the taint does not move.

## The hydra dies

The Kirby–Paris hydra: cut off a head, and it grows finitely many new ones lower down; does the battle
always end? Here the answer is a two-line corollary.

**Theorem 57.1** (`hydra_no_perpetual_engine`, 🟢). *The hydra battle carries no perpetual engine: for
any well-founded `r`, the cut-relation `Relation.CutExpand r` admits no infinite descending sequence.*

**Why this is true.** A hydra cut is exactly one `Relation.CutExpand` step — remove a head `a`, add
finitely many `a'` with `r a' a`. Mathlib proves `WellFounded r → WellFounded (CutExpand r)`
(`WellFounded.cutExpand`); feed that to `no_perpetual_engine_of_wellFounded`. The hydra dies because
its state descends on a well-founded order — the engine, verbatim.

## The ω-worm: a transfinite rank

Until now every rank was a natural number. But the engine transfers along a rank into **any**
well-founded order, and ordinals are the archetype. Here is the first transfinite instance, and it
captures the deepest trick in the canon.

**Theorem 57.2** (`omega_worm_no_perpetual_engine`, 🟢). *Read a state as `(a, b)` — a big register
`a`, a small register `b`. A step lowers `a` by one and lets `b` jump to ANY value whatsoever. The
process still terminates — it carries no perpetual engine — under the ORDINAL rank `ω·a + b`.*

**Why this is true.** Even though `b` may explode arbitrarily, the ordinal strictly drops: `ω·a + k <
ω·(a+1) + b'` for every `k`, because `k < ω`. So `no_perpetual_engine_of_rank` with codomain `Ordinal`
(not `ℕ`) closes it — the first transfinite rank in the programme. This is precisely the mechanism
behind **Goodstein's theorem** and the hydra: the natural-number value grows without bound while the
ordinal rank falls, and falling ordinals cannot fall forever. Full weak Goodstein — the base-`b`
digits read as an ordinal below `ω^ω` — is the natural extension of this same rank, and we record it
as the next step (not yet formalized here).

## Markov descent: a green wall and a red gate

**Theorem 57.3** (`markov_no_perpetual_engine`, 🟢). *The Markov tree of triples `x²+y²+z²=3xyz`
reduces to its root: no infinite chain of Vieta jumps `z ↦ 3xy−z`, because the height `x+y+z` is a
strictly decreasing ℕ-rank (`markov_vieta_lt`).*

**Why this is true.** From an ordered non-root triple `x ≤ y ≤ z` with `y < z`, the Vieta jump replaces
`z` by `z' = 3xy − z`, and `z' ≤ y < z` — because `y` lies between the two roots of `t² − 3xy·t +
(x²+y²)`, so the top strictly falls and with it the height. Vieta closure (`isMarkov_vieta`) keeps the
new triple Markov; the height, a natural number, cannot descend forever.

This is a **mask**: the termination/finiteness half is green, but it says nothing about the **Frobenius
uniqueness conjecture** — that every Markov number is the largest coordinate of a *unique* triple, open
since 1913. Uniqueness is injectivity of the max-label, orthogonal to well-foundedness; the hammer has
no purchase on it. Green wall, honest red gate — the same shape as the millennium fronts.

## The reversibility dividing line

The engine has a flip side, and the canon names it. Where a strict descent never returns, a
**reversible** system always does.

**Theorem 57.4** (`poincare_dividing_line`, 🟢). *Two halves on a measure space. (i) Every well-founded
relation forbids the perpetual engine — a descending chain, hence any return. (ii) A conservative map
(for instance a finite-measure measure-preserving, reversible one) satisfies Poincaré recurrence:
almost every point of a set returns to it infinitely often.*

**Why this is true.** The first half is the engine (`no_perpetual_engine_of_wellFounded`); the second
is mathlib's `Conservative.ae_mem_imp_frequently_image_mem`. Together they are the exact contraries
`universal_engine_dividing_line` names on ℝ, now on a dynamical system: strict descent on a
well-founded carrier never returns; measure-preserving reversibility always does. This closes the
reversibility axis the quantum reading opened (ch. [50](50_Coda.md)): closed, unitary, reversible
evolution *recurs*; our irreversible descent *cannot*.

> **Note (what is proved, what is deferred, what does not fit).**
>
> 1. The ω-worm (57.2) is the transfinite-rank *mechanism* of Goodstein and the hydra, not the full
>    weak Goodstein theorem; the base-`b` digit ordinal is the natural next step, deferred.
> 2. Deferred green: full weak Goodstein (via `Nat.digits` and the ordinal Cantor normal form),
>    Newman's lemma (termination ⇒ confluence, absent from mathlib as an abstract result), the
>    Higman/Dickson well-quasi-order instances.
> 3. Documented **non-fits** — the hammer explicitly does *not* reach these: aliquot sequences
>    (Catalan–Dickson), which have no well-founded order and whose boundedness is *expected false*;
>    Erdős–Straus `4/n = 1/a+1/b+1/c`, a covering obstruction, not a descent; the 15-puzzle and parity
>    games, a conserved invariant orthogonal to a decreasing rank; stability of matter, KAM, sphere
>    packing — genuine analysis with no discrete well-founded carrier in the Lean.
> 4. The Gödel placement is sharpened in the Coda ([50](50_Coda.md)): this lane is exactly where "not a
>    Gödelian phenomenon" must be read precisely — *well-foundedness, not self-reference*.

## Place in the greater arc

The seven masks read hard analytic objects as shadows of the prohibition; here the prohibition meets
the objects that *are* the prohibition, stated plainly. The hydra, the worm, the Markov tree are
termination theorems, and termination is well-foundedness, and well-foundedness is the engine. The
only new mathematics is the framing — and the one transfinite rank, which shows the engine was never
bound to the number line: it works wherever a descent can be measured by an ordinal that cannot fall
forever.

<!--navbot-->

---

[← 56. The Collatz first cause](56_CollatzFirstCause.md) · [Table of contents](00_Overview.md)
<!--/navbot-->
