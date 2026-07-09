# Navier–Stokes: smoothness via the cascade and the integral, taken

<!--navtop-->
[← 40. Yang–Mills](40_YangMills.md) · [Table of contents](00_Overview.md) · [42. Hodge →](42_Hodge.md)
<!--/navtop-->



> Lean source: `Engine/NavierStokesFront.lean` — the green chain, the finishing-off and the trilemma, all 🟢;
> `Engine/Step00FrontClosureAudit.lean` — the machine record of why Navier–Stokes was WITHDRAWN from
> the decree (Option A).
> Status notation: 🟢 — proven under the standard axioms;
> 🟡 — proven conditionally on the axiom `step00FirstCause`; 🔴 — an open input.
>
> **Status update (Option A).** Navier–Stokes is no longer a boundary of the decree. Earlier drafts
> hung an `nsBoundary` field on `step00FirstCause` and projected 🟡-theorems out of it; that field and
> its projections have been **withdrawn**, and no Navier–Stokes declaration is axiom-tainted any more.
> What survives is the green structural half: the surrogate `NoSingularCascade`, the energy identity,
> and — on the box class — an unconditional energy balance. The reason for the withdrawal is spelled
> out in "The Navier–Stokes boundary, withdrawn (Option A)" below.

## The reading: a singularity is a perpetual engine, and the solution is an integral, taken

The engine's motion inside its rank is smooth everywhere, with no points of rupture; the appearance of such a point would create
a perpetual engine; and since the motion is smooth, the solution can be derived — take the integral. This is how we read the problem
of existence and smoothness for Navier–Stokes solutions, and both halves of this reading are realised exactly.

The hypothetical singularity is a **singular cascade** `SingularCascade`: infinitely many
δ-dissipative stages compressed towards a single finite moment `T`. An infinite quantised ladder —
the same perpetual engine as in the preceding chapters. Its impossibility under the energy balance is a green
theorem. And "taking the integral" we perform literally, and twice.

As with Yang–Mills, the honest boundary is drawn immediately and loudly: *we do not solve the Millennium problem and do not declare it solved.* Leray existence, uniqueness, genuine `C^∞`-regularity and the law
`EnergyBalanceLaw` itself remain open ([chapter 36](36_NavierStokes.md)); we prove the structural half.

## The integral is taken — twice

The first taking of the integral turns the old inequality into an *exact equality*.

**Theorem 41.1** (`energy_identity_of_energyBalance`, 🟢). *The energy obeys the identity
`E(t₂) = E(t₁) − ∫ D(s) ds`* — as an equality, not an inequality, via the second fundamental theorem of calculus.
The two-time inequality of [chapter 36](36_NavierStokes.md) turns out to be a mere coarsening of this equality derived
by integration.

The second taking of the integral recovers the solution itself from the equation.

**Theorem 41.2** (`isNSSolution_integral_form`, 🟢). *The solution is expressed as the integral of its right-hand side:*
`u(t,x) = u(0,x) + ∫₀ᵗ (νΔu − ∇p + f − (u·∇)u) ds`. This is the FTC for functions with values in `E3` (the Bochner
integral, the Banach-space version). The caveat is honest: three hypotheses — that `u` is a solution, is differentiable in
time, and the right-hand side is integrable — are named explicitly; non-vacuity is checked on the zero solution.
"To derive the solution, take the integral" has ceased to be a slogan and become a theorem.

## The engine and its killer

Now the singular cascade and its death.

**Theorem 41.3** (`no_singularCascade_of_energyInequality`, 🟢). *Under the energy inequality,
singular cascades do not exist.* A direct application of the budget machine already built
(`ns_no_infinite_dissipative_cascade`, [chapter 36](36_NavierStokes.md)): the budget forbids an infinite δ-cascade altogether, and
one compressed to a finite time all the more so.

Hence the honest smoothness surrogate `NoSingularCascade`: for no quantisation `δ > 0` and towards no finite `T` does the ladder compress. Let us stress (disclosed in the module): this is not `C^∞`, but the absence of an infinite uniformly quantised dissipative ladder.

And the hero of the chapter:

**Theorem 41.4** (`noSingularCascade_of_energyBalance`, 🟢). *The pointwise energy balance `dE/dt = −D` plus
integrability ⟹ there are no rupture points of cascade type.* "The motion is smooth everywhere" — in the programme's language.

## An ℝ-warning: why the surrogate is precisely about uniformity

At the level of abstract energy profiles `E : ℝ → ℝ` (not the NS solutions themselves — nontrivial solutions are out of
reach, and this is disclosed) one can see where the dividing line runs. A uniform profile cascade with a
nonnegative profile is killed by the general machine (`no_uniform_profileCascade_of_nonneg` 🟢).

But a forged — that is, machine-built as a counterexample (see the [glossary](GLOSSARY.md)) —
cascade on `tₙ = 1 − 2⁻ⁿ` with profile `max(1−t, 0)` — infinite, compressed to `T = 1` — is not uniform:
its drops `2⁻⁽ⁿ⁺¹⁾` slip under every `δ` (`cookedProfileCascade_not_uniform` 🟢), and the budget cannot
take it.

This is the same lesson the Yang–Mills ladder taught: the surrogate speaks precisely of *uniform*
quantisation — exactly what a genuine regularity certificate must supply.

## The finishing-off: the gate law and the impostor in the pressure

Here the most interesting part begins. We tried to *finish off* the branch — that is, to check whether the
energy balance can be made an honest boundary of the decree, a gated form of the law. The extended trilemma — the mandatory
triple test of a boundary candidate: refutability, vacuity, goal renaming
(see the [glossary](GLOSSARY.md)) — yielded a nontrivial and instructive picture.

The first thing exposed was the **danger of degeneration**. If the force `f` is allowed to be arbitrary, the predicate "to be a solution" degenerates: mathlib's total operators absorb anything, and any field turns out to be a
"solution" under a suitably forged force (`isNSSolution_of_cooked_force` 🟢). Hence the gate —
the named input condition that an honest formulation requires (see the [glossary](GLOSSARY.md)) —
must demand `f = 0` — a forceless solution.

But `f = 0` is not enough either. We built **two impostors**, each of them a forceless solution that breaks the balance.

The first, `dirichletFlow`, is a Dirichlet flicker of an indicator field. It solves the equation via a *junk time derivative*: the Dirichlet function is nowhere differentiable, and the total operator swallows this. It wrecks the energy balance (`dirichletFlow_not_energyBalance` 🟢). The lesson: the gate `f = 0` must be strengthened with differentiability in time.

The second impostor turned out to be the main find of the finishing-off. Take the indicator pressure `2 − y₀` inside the unit ball. It makes the flow `cookedFlow` a forceless solution, fully differentiable in time (`cookedFlow_isNSSolution_unforced` 🟢) — and still breaking the balance. This time the junk is hidden not in the time derivative but in the pressure gradient on the sphere (`nsTimeGatedBalanceLaw_refuted` 🟢): the discontinuous pressure gives an honest gradient inside and a junk zero on the boundary. The gate "`f = 0` + time" is not enough either.

Hence the final gate `NsSolutionBalanceLaw`: `f = 0` plus differentiability both in time and in space. Both impostors are killed by it machine-wise: the first fails the time gate, the second the spatial one. The gate class is inhabited — the zero solution passes both gates and the conclusion.

**Conclusion.** And the law itself is not provable: its derivation needs the divergence theorem on `ℝ³`, which mathlib lacks — nor has it been forged by any known means. More than that, refuting it would settle Galdi's open problem on the Liouville property of stationary Navier–Stokes. This is exactly the epistemic status of the twin node: not provable and not refutable — hence an honest boundary candidate.

## The Navier–Stokes boundary, withdrawn (Option A)

For one draft the first cause acquired a third substantive field `nsBoundary : NsSolutionBalanceLaw`,
from which followed the 🟡-theorems: cascade smoothness of every gated solution
(`noSingularCascade_from_firstCause` — a surrogate, not `C^∞`), the energy identity
(`energyIdentity_from_firstCause`) and the tripwire — an intentional explosion detector for the case
the law is refuted (see the [glossary](GLOSSARY.md)) — `quarantine_inconsistent_if_nsGatedViolation_exhibited`.

Under **Option A that field was withdrawn**. The structure `Step00FirstCause` now carries **only** the
twin boundary `causalBoundary` (`SerialTwinBoundaryObligation`); the field `nsBoundary`, the law
`NsSolutionBalanceLaw` itself, and the projections
`noSingularCascade_from_firstCause`/`energyIdentity_from_firstCause` are now **dead code**, living
inside a `/- WITHDRAWN -/` comment block (🔵). No Navier–Stokes declaration is axiom-tainted any more;
the repository taint (16, all asserting twins) does not include it. What follows is the historical
projection, kept as a record of what was detached.

The peculiarity that had to be named honestly even then. For Riemann the decree was of *exactly* RH strength: "the law ⟺ the goal" at the boundary. Here there was no such mirror.

**Conclusion.** The smoothness surrogate would be satisfied even by an *inequality* (`noSingularCascade_of_twoTimeInequality` 🟢), while the gate law asserted the stronger *equality* `dE/dt = −D`. The converse implication is unknown — that is, **the decree, had it stayed live, might overpay** for its goal. It is the same pattern we shall honestly note for Collatz: the price may exceed the cost. Under Option A the question is moot along with the field.

The earlier verdict of §13 — "there is no fifth boundary" — stands for the ungated and manifestational forms; `nsBoundary` had survived as a *different* candidate, gated, with the overpayment disclosed — but it too is detached under Option A.

## Philosophical digression: turbulence, the Kolmogorov cascade and the prohibition of singularity

Navier–Stokes is the equation of real water: of weather, of blood in vessels, of flow past a wing, of smoke above a candle. And the "singularity of the solution" that we refute as a perpetual engine has a direct physical image.

Richardson and Kolmogorov described turbulence as an **energy cascade**: large eddies break into smaller ones, energy flows down the scales until, at the Kolmogorov microscale, viscosity eats it. "Big whorls have little whorls that feed on their velocity; and little whorls have lesser whorls, and so on to viscosity" — this is literally our `SingularCascade`. A finite-time singularity would be this cascade reaching infinitely small scales in a finite span: an infinite tower of ever smaller eddies, compressed towards a single instant.

Such an event is a perpetual engine in the most physical sense. It would mean infinite energy density at a finite moment out of finite initial energy: work out of nothing.

Viscosity does not permit this — it is the rope, the δ-dissipation pulling energy out at every transition to a smaller scale; the energy balance law says the books are reconciled, `dE/dt = −D`. A whirlpool in a draining bathtub may spin fast, but not infinitely fast: friction quietly bleeds away its energy. Real fluids empirically never blow up precisely because viscosity always arrives in time at the smallest scales — the rope always wins at the bottom of the cascade.

Our find from the finishing-off — the forged pressure — deserves separate mention. The flow `cookedFlow` gains energy out of nothing (it stirs itself up, `E = c·t²`), and this is exactly the portrait of a perpetual engine: a field pumping energy without a source. For a genuine forceless solution this is impossible — but mathlib's total operators (junk derivatives) let the impostor in through the pressure gradient on the sphere.

The differentiability gate is the physical demand of "genuine smoothness of the flow", exorcising the impostor. Thus mathematical honesty (closing the junk) and physical intuition (real flows are smooth) turn out to be one and the same gesture.

Navier–Stokes smoothness is, philosophically, the physical impossibility of extracting infinite energy from the vacuum of scales. Turbulence is the visible tug of war; regularity is the rope, invariably winning at the very bottom.

And as with Collatz and with the primes, the same wall stands here: on average the cascade decays — this we see — but the guarantee for *each* individual trajectory remains the open heart, the named input `EnergyBalanceLaw`; under Option A it is no longer paid for by decree (the boundary is withdrawn), and is carried greenly only on the box class.

## Postscript: the passage to ℝ³ — the integral assembled on the box

Above, the energy lived as an abstract profile `E : ℝ → ℝ`, handed over by hypothesis. The module
`Engine/NavierStokesR3Assembly` brings this abstraction down to earth: it works on the genuine `E3 = EuclideanSpace ℝ (Fin 3)` and *assembles the spatial integral for real*, engaging mathlib's divergence theorem and differentiation under the integral sign.

**Theorem 41.5** (`hasDerivAt_kineticEnergy_of_dominated`, 🟢). *Under honest domination gates,
the derivative of the kinetic energy equals `dE/dt = ∫ ⟪u, ∂ₜu⟫` — an integral over all of space, not a
profile.* "Why this is true." This is genuine differentiation under the integral sign
(mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) plus the componentwise derivative
of the density `‖u‖²` (`HasDerivAt.norm_sq`, exactly `2⟪u, ∂ₜu⟫`).

**Theorem 41.6** (`divergence_integral_eq_zero`, 🟢). *For a C¹ field supported in an open box, the integral
of the divergence over all of ℝ³ equals zero.* "Why this is true." Here *the divergence theorem is engaged for real* (`integral_divergence_of_hasFDerivAt_off_countable`): the six face integrals
die by support — the face coordinate equals `aᵢ` or `bᵢ`, outside the open box, where the field is zero — while
the complement of the closed box is open, and there the derivative is honestly zero.

Hence the head result, lifting part of the overpayment from the previous section:

**Theorem 41.7** (`noSingularCascade_of_r3Assembly`, 🟢). *For a box-supported C² solution (force `f = 0`), cascade smoothness is derived in green — without the decree `nsBoundary`.* "Why this is true." On the box the energy balance law is no longer postulated: `energyBalance_of_boxSupported` *derives* `dE/dt = −D` from the derivative under the integral and three integrations by parts (pressure and convection die by divergence-freeness, viscosity yields `−`enstrophy), after which the already-proven budget machine takes over. On this class the decree `nsBoundary` is redundant (`nsBoundary_redundant_on_boxClass`).

And — the "exactly so" completion: the three integration-by-parts identities are no longer inputs but theorems.

**Theorem 41.8** (`integral_e3_divergence_eq_zero`, 🟢 — the carrying lemma). *The integral of the E3-divergence
of a box-supported `C¹` field over all of ℝ³ equals zero.* "Why this is true." The field is transported from `E3` to
`Fin 3 → ℝ` by the linear isometry `eL3` (transport of the derivative — the chain rule
`ContinuousLinearEquiv.hasFDerivAt` + `HasFDerivAt.comp`, the identity `eL3.symm (Pi.single i 1) = e3 i`),
where the green divergence theorem of §2 lives. This is precisely the `fderiv` bridge that was missing.

**Theorem 41.9** (`pressureKills_of_boxSupported` / `transportKills_of_boxSupported` /
`viscosityIBP_of_boxSupported`, all 🟢). *For a box-supported `C²` solution, `∫ ⟪u, ∇p⟫ = 0`,
`∫ ⟪u, (u·∇)u⟫ = 0`, `∫ ⟪u, Δu⟫ = −∫ ∑ᵢ ‖∂ᵢu‖²`.*

"Why this is true." Each integrand is
the E3-divergence of a suitable field (`p·u`; `½‖u‖²·u`; componentwise `uⱼ·∇uⱼ`), reduced
by divergence-freeness and chain identities; the carrying lemma quenches the integral to zero. The viscous one is componentwise integration by parts with a rearrangement of the sum `∑ⱼ‖∇uⱼ‖² = ∑ᵢ‖∂ᵢu‖²`. From here `killerBundle_of_boxSupported` assembles the energy balance *unconditionally* for the box class: `#print axioms` shows the standard triple, no `sorry`, no axioms.

> **Note (what remains beyond the honest boundary).** Exactly three integration-by-parts identities have been
> discharged; other things are not closed: the assembly lives on the class of spatially compactly supported solutions, and the limiting
> passage box → ℝ³ for merely decaying (not compactly supported) fields is absent from mathlib — this is an external gap.
> `TimeDomination` (the local majorant for the derivative under the integral) and interval integrability
> of the dissipation remain honest analytic inputs; `NoSingularCascade` is a surrogate, not `C^∞`;
> the Millennium problem is not being solved. But precisely the "taking of the integral" on ℝ³ — the derivative under it and the three
> integrations by parts — is now proven, not assumed.

And one quiet victory of honesty: the gate `BoxSupportedC2Flow` *for the first time requires smoothness of the pressure*
(`pressDiff`, `contP'`) — which means the impostor `cookedFlow` with its discontinuous pressure on the sphere
(the Forge-B channel from the "finishing-off" above) is now excluded structurally, machine-wise
(`cookedFlow_fails_assemblyGates`). The engine's motion inside its rank is smooth everywhere — and on ℝ³ we
have verified this one layer closer to real water.

## Postscript: reduction to a single theorem — and why the engine does not close it

The module `Engine/NavierStokesClayReduction` takes the last honest step: it *encodes the exact Clay-(A) statement* (Schwartz data, divergence-freeness, `∃` a smooth global solution with finite energy — via `ContDiff ℝ ⊤` and explicit decay estimates) and machine-checks the logical reduction to a single open statement.

**Theorem 41.10** (`clayA_of_regularityTransfer_and_vorticityControl`, 🟢). *The known transfer theory
(Kato's local strong existence + the Beale–Kato–Majda continuation) plus the single criterion
`GlobalVorticityControl` ⟹ Clay-(A).*

"Why this is true." Pure modus ponens: a local smooth
solution exists; the criterion keeps the vorticity from blowing up; BKM extends the solution to all time. The theorem
is green and *not vacuous* (that is, it does not hold for free, by a stub witness): the conclusion is inhabited (`globalSmoothSolution_zero` — the zero field is a
global smooth solution), and both inputs are genuinely consumed (remove either — it does not compile).

The point is **isolation**. Everything left for (A) has been pulled into one named theorem `GlobalVorticityControl`: *for every smooth solution of Schwartz data, the vorticity stays bounded on each finite interval.* This is the open core — the supercriticality barrier, Fields-medal level; no one knows how to prove it.

The known transfer theory (`RegularityTransfer`, `RegularityNecessity`) we honestly name as 🔴-inputs: these are real theorems of the literature, simply not formalised in mathlib (tier 1). The tier map: 🟢 proven (the box-class energy balance, the reduction); known-but-not-formalised (Leray, Sobolev, BKM); 🔴 open (the vorticity criterion itself).

> **Note (why the engine reading does not close it — machine-checked).** It is tempting to reduce (A) to
> the engine, as with Collatz: "to refute = to build a perpetual engine, hence it cannot be known". But for
> Collatz that bridge is a *genuine theorem* (a non-halting orbit is discrete and *literally* is an
> engine on ℕ). For Navier–Stokes it provably tears: the green surrogate `NoSingularCascade`
> kills only the *uniformly* quantised cascade, while `cookedProfileCascade_not_uniform` exhibits a
> *non-uniform* cascade that slips away. The module records this machine-wise —
> `greenBudget_strictly_weaker_than_vorticityControl`: the green engine machine is strictly weaker than
> the criterion and does not prove it. A genuine blow-up is a continuum phenomenon; the discrete engine
> prohibition does not reach it. That is why we name the open core analytically (the vorticity), not
> engine-wise: honesty demands naming the gap, not hiding it in a metaphor.

The upshot: this work brings the NS solution **not one step closer** mathematically. It gives the exact formulation, a verified reduction skeleton and the exact name of the single missing theorem — and honestly shows the barrier that puts it out of reach. No `sorry`, no new axiom; the repository taint — the axiom's trace in the declarations' dependency lists (see the [glossary](GLOSSARY.md)) — is unchanged.

<!--navbot-->

---

[← 40. Yang–Mills](40_YangMills.md) · [Table of contents](00_Overview.md) · [42. Hodge →](42_Hodge.md)
<!--/navbot-->
