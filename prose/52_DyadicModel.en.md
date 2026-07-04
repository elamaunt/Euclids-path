# 52. A discrete fluid model: where the engine works and where it blows up

<!--navtop-->
[← 51. Numerical evidence](51_NumericalEvidence.md) · [Table of contents](00_Overview.md) · [53. Birch–Swinnerton-Dyer →](53_BirchSwinnertonDyer.md)
<!--/navtop-->

> Lean source: `Engine/CascadeBudget.lean` (the budget lemma + a finite shell model), `Engine/DyadicBlowup.lean`
> (the blow-up core + the Katz–Pavlović model + the derivation of the drive from the couplings), `Engine/DyadicFirstCause.lean` (the 🟡 layer:
> the origin of the cascade is decreed by the first cause). The blow-up core and the drive derivation are 🟢 under the standard axioms,
> with neither `sorry` nor any new axiom. One 🟡 layer is added deliberately: it attaches the origin of the cascade to
> the first cause and grows the taint by two declarations (45 → 47). This is an **appendix-epilogue**, not a branch
> of the main line.

## Where we are

The main line read the turbulent cascade as a perpetual engine: a singularity is an infinite tower of ever finer vortices, and engines are impossible, hence there is no singularity either.

Chapter [41](41_NSSmoothness.md) has already honestly stipulated that the green machine catches only a *uniformly* quantised cascade (a surrogate), not a genuine singularity.

This appendix pushes the honesty to its limit: it tests the engine reading against rigorous discrete fluid models — and shows by machine where it is valid and where it is false.

Before we begin — a loud framing. No fluid model had ever been formalised in any proof assistant before (not Navier–Stokes, not Euler, not the dyadic one, not a shell model).

What is formalised here is *known* mathematics (the budget principle; the Katz–Pavlović model, 2005; Cheskidov–Friedlander). It is the first formalisation of its kind, but it **solves** nothing and, more importantly, delineates and partially refutes the engine reading. The novelty here is formalisational, not mathematical.

## Where the engine works: the budget versus uniform dissipation

**Theorem 52.1** (`finite_budget_bounds_uniform_dissipation`, 🟢). *If the energy `E(t)` decreases at a rate no
less than `β > 0` on all of `[0, T]` (i.e. `E'(t) ≤ −β`), and is still nonnegative at the endpoint, then `T ≤ E₀/β`.*
"Why this is true." Pure calculus: a one-sided mean-value estimate gives `E(T) ≤ E₀ − βT`, and `0 ≤ E(T)` closes it. This is the machine form of our slogan: **a finite budget cannot sustain perpetual uniform dissipation** — the same principle that killed `ns_no_infinite_dissipative_cascade`.

We tied it to a genuine finite shell model (of GOY/Sabra type): amplitudes `a : Fin N → ℝ → ℝ` with nonlinear energy transfer between neighbouring shells (conserving the total energy — a telescope) and dyadic dissipation `ν·λ^{2αn}`.

**Theorem 52.2** (`no_uniform_dissipation_forever_on_shell`, 🟢). *On this model, uniform dissipation ≥ β
entails `T ≤ E₀/β`.* The model is inhabited (the zero solution is an honest `ShellSolution`), the hypotheses are genuinely consumed. The engine reading is **valid** here — but only in the uniform regime.

> **Note (an honest boundary — also by machine).** The budget does not catch a *nonuniform* cascade.
> `budget_misses_nonuniform` (🟢) refers directly to `cookedProfileCascade_not_uniform` from the NS branch:
> on the forged profile the dips in dissipation slip below every `β > 0`. That is, the uniformity premise
> of the budget lemma is *false* for genuine nonuniform cascades — and that is the whole point.

## Where the engine breaks: dyadic blow-up

Now a genuine model with no artificial uniformity. In Katz–Pavlović, under weak dissipation (`α < 1/4`) the energy cascades up the shells *super-linearly* and the solution blows up in finite time — proven (Katz–Pavlović 2005; Cheskidov–Friedlander, blow-up in `H^{5/6}` for the inviscid model). We formalised the core of this mechanism.

**Theorem 52.3** (`superlinear_blowup_sq`, 🟢 — the rigorous core). *No global positive `C¹` function
can satisfy `y'(t) ≥ C·y(t)²` (`C > 0`): the assumption of a global solution yields `False`.*
"Why this is true." Take `w(t) := 1/y(t) + C·t`; then `w'(t) = −y'/y² + C ≤ −C + C = 0`, so `w` is non-increasing, and `1/y = w − Ct` must go negative in finite time — a contradiction with `y > 0`. This is the machine transcript of the fact that **a super-linear cascade is a realised perpetual engine**: it exists exactly until the moment of blow-up.

**Theorem 52.4** (`dyadic_blowup`, 🟢). *The Katz–Pavlović model `DyadicSolution` is globally empty — blow-up
is inevitable.* We defined the genuine KP equations `aₙ' = λⁿaₙ₋₁² − λⁿ⁺¹aₙaₙ₊₁ − dₙaₙ` and proved the telescope of energy conservation for the nonlinear transfer; the blow-up follows from the core.

## The drive is no longer postulated: it is derived from the couplings

Previously the linking property `y' ≥ C·y²` lived as a named hypothesis `superlinearDrive` of the structure
`DyadicSolution` — honestly named, but not derived from the λⁿ-couplings. Now we have derived it, in two steps.

**Theorem 52.5** (`ssLead_drive`, 🟢 — the drive from the coupling). *The exact self-similar solution
`aₙ(t) = λ⁻ⁿ/((λ²−1)(T−t))` solves the bulk KP equations; for the leading mode `y = a₁` the drive holds
with equality: `y' = C·y²` with `C = λ(λ²−1)`.*

"Why this is true." Substituting `g(t) = 1/(T−t)` gives `g' = g²`. On the profile `βₙ = λ⁻ⁿ/(λ²−1)` the equation
of shell `n=1` (`a₁' = λa₀² − λ²a₁a₂`) reduces to `β₁g² = (1/β₁)(β₁g)²`. The drive is not postulated — it is
computed from the right-hand side `kpRHS`.

> **Note (homogeneity — a necessity, not an ornament).** The leading functional must be linear
> in the amplitudes (`a₁` or `∑wₙaₙ`). A quadratic `∑wₙaₙ²` would give `y' ∼ g³` while `y² ∼ g⁴` — the inequality
> `y' ≥ C·y²` is false for it as `t → T`. The linear functional is chosen deliberately.

**Theorem 52.6** (`frontDrive_of_invariant`, 🟢 — the drive for a whole class). *Suppose a KP solution has one
front shell pinched from below by its two neighbours — the invariant `FrontDomination`: `ρ·a_{J+1} ≤ a_J`,
`a_{J+2} ≤ κ·a_{J+1}`, `m ≤ a_{J+1}`. Then the drive `C·y² ≤ y'` is derived directly from the λⁿ-couplings.*

"Why this is true." The three estimates are substituted into `kpRHS(J+1)`: the inflow `λ^{J+1}a_J²` produces `y²`, the outflow and
the dissipation are subtracted under control, and what remains is `C·y²` with `C = λ^{J+1}ρ² − λ^{J+2}κ − d_{J+1}/m`. Thus the
monolithic hypothesis is replaced by a smaller, coordinate-closer invariant, and the drive becomes its
consequence. The bridge `DyadicSolution.ofFrontDominated` fills the formerly free field `superlinearDrive`
with exactly this derivation.

> **Note (what remains open — honestly).** One input still remains named: the preservation
> of the invariant `FrontDomination` for *infinitely* many modes over the whole lifespan. This is the moving
> Katz–Pavlović front (Barbato–Morandin–Romito; Cheskidov; Kiselev–Zlatoš) — a research frontier, not
> proven here. But the gap has narrowed: from "the whole drive is postulated" — to "the drive is derived from the couplings for
> the self-similar solution and for a class; only one isolated input remains open". Non-vacuity is confirmed
> by the fact that the self-similar profile satisfies the invariant (`ssMode_frontDomination`).

## The origin of the cascade is the first cause

The self-similar solution demanded one honest concession: the bottom shell `n=0` needs an external
pumping term. And this concession has an exact name.

The largest shell `n=0` can only give: its inflow is zero (`kpInflow 0 = 0`), there is only an
outflow up the cascade. Hence it cannot start itself — its origin cannot be begotten from inside the couplings.

**Theorem 52.7** (`dyadicOrigin_uncausable_from_inside`, 🟢). *The self-similar origin does not satisfy
the unforced equation of shell `n=0`: its true dynamics carries a strictly positive surplus
`bottomForcing > 0` on top of `kpRHS`.*

"Why this is true." The remainder `F₀ = (β₀ + λβ₀β₁)/(T−t)²` is strictly positive; were the derivative equal to
the unforced right-hand side, uniqueness of the derivative would yield `bottomForcing = 0` —
a contradiction. External pumping is obligatory.

This is word for word the same figure that sits at the foundation of the whole programme: the event `0 → 1`, which cannot be caused
from inside, since self-ignition would be a perpetual engine (`no_internalisedOriginEvent`). The origin of the cascade is
the first cause, and its `0` is the very singularity of the cosmological reading of the [coda](50_Coda.md).

Hence — the single deliberate yellow layer of this appendix.

**Theorem 52.8** (`dyadicBlowup_is_firstCauseManifestation`, 🟡 — ⚠️ AXIOM-TAINTED). *The same
first-cause decree that decrees the seven masks also supplies the origin of the cascade: the supply at scale
`n=0` is drawn from the boundary `nsBoundary` of the axiom `step00FirstCause`.*

The scheme is "two walls": a green wall of impossibility (the origin is uncausable from inside) plus a supply
decreed from outside. Thus the fluid blow-up joins the masks — but **only through its origin**. The green derivation
of the drive (the self-similar solution and the class) is self-contained and does not depend on this layer: remove the first cause —
the mathematics of the blow-up stays intact, and all that disappears is the answer to the question "who lit the pump `n=0`". This is exactly why
the taint grows by precisely two declarations (45 → 47), and not a single one more.

## Philosophical digression: a map of the boundary, not a solution

Thus the discrete model passes verdict on the engine reading — a double and honest one. Where dissipation is uniform — the engine works (the budget forbids a perpetual cascade). Where the cascade is genuine — **the engine is realised** (the blow-up happens), and the naive "the engine is impossible ⟹ there is no singularity" is refuted.

Why this is not a solution of Navier–Stokes is explained by Tao's supercriticality barrier (2016): he constructed an averaged NS that preserves the energy identity and blows up all the same.

Hence any argument of the form "energy/budget ⟹ regularity" that does not use the fine structure of the nonlinearity is doomed — and our engine is exactly such. Regularity, as Onsager and Isett showed, is governed by the Hölder exponent `1/3`, not by the total energy.

What is there, then? The world's first formalisation of a fluid model in a proof assistant — of known mathematics — and a **machine map of the boundary** of our own idea: an exact indication of where the engine reading is valid and where it breaks.

This is more honest than any closure: we did not hide the gap in a metaphor, but exhibited it as a line of code. A cascade that reaches the bottom in finite time is not a forbidden engine but a realised one; and the water blows up in the model exactly where the arithmetic of twins stays silent.

## Place in the greater arc

Appendix B closes the honest question "what does our theory give for fluids": new mathematics — none
(Tao's barrier), but the first formalisation of a discrete model — yes, together with a machine delineation of the limits
of the engine reading, the derivation of the drive from the couplings, and the attachment of the origin of the cascade to the first cause.
`twin_prime_conjecture` remains `sorry`; the taint grew by exactly two declarations of the yellow origin layer
(45 → 47); not a single open problem is solved or declared solved.

<!--navbot-->

---

[← 51. Numerical evidence](51_NumericalEvidence.md) · [Table of contents](00_Overview.md) · [53. Birch–Swinnerton-Dyer →](53_BirchSwinnertonDyer.md)
<!--/navbot-->
