# 36. Navier–Stokes: the equation and honest integrals

<!--navtop-->
[← 35. P/NP: the local node](35_ClassicalPNP.md) · [Table of contents](00_Overview.md) · [37. Riemann fronts →](37_RiemannFronts.md)
<!--/navtop-->



> Lean: `Engine/NavierStokes.lean` (the equation itself, mathlib analysis; everything proven is 🟢 under
> the standard axioms, without step00), the NS part of `Engine/DissipativeCascade.lean` (§2: the ℝ-warning
> `real_positive_work_not_wellfounded`; the quantization `no_infinite_uniform_dissipative_cascade`).
> Prose context: [24. Boundary decomposition](24_BoundaryDecomp.md), the section "Navier–Stokes: the equation itself + honesty of the integrals".

Why does hydrodynamics live at all in a repository about prime numbers? Because `DissipativeCascade` is
a single blueprint for three branches (Step00, Riemann, Navier–Stokes) with one motto: *the defect does
not vanish; if it did not close — pay*. For the twins the "payment" is regeneration of the carrier, for
Riemann — the paid dynamics of the engine, and for Navier–Stokes the payment is literal: viscous
dissipation of energy.

But for the analogy not to remain a metaphor, one must exhibit the equation itself — not an abstract
interface of "some dissipative system", but the classical strong form of NS in mathlib terms. This
chapter is about what could be done here honestly, and where the boundary runs.

A red line right away: *no connection to prime numbers exists here, and none is claimed*. The NS branch
neither feeds the twins nor feeds off them; it is a proving ground for the same budget discipline on a
genuine analytic object.

## The equation itself

`Engine/NavierStokes.lean` works in `E3 := EuclideanSpace ℝ (Fin 3)` and assembles the differential
operators from bare `fderiv`: the divergence `NSdiv` (the trace of the Jacobian, $\sum_i \partial_i u_i$),
the vector Laplacian `vectorLaplacian` ($\sum_i \partial_i(\partial_i u)$), the convective term
`convectiveTerm` (the derivative of $u$ along $u$ itself, i.e. $(u\cdot\nabla)u$). From these, a predicate.

**Definition 36.1** (`IsNSSolution`). For viscosity $\nu$, external force $f$, velocity field $u$ and pressure $p$,

$$\texttt{IsNSSolution}\ \nu\ f\ u\ p \;:=\; \Bigl[\partial_t u + (u\cdot\nabla)u = \nu\,\Delta u - \nabla p + f\Bigr] \;\wedge\; \bigl[\mathrm{div}\,u = 0\bigr]. \tag{36.1}$$

These are the incompressible Navier–Stokes equations in the classical strong form — a velocity field
`u : ℝ → E3 → E3`, a pressure `p : ℝ → E3 → ℝ`, a viscosity `ν`, an external force `f`. No weak
solutions and no distributions: the strong form is chosen deliberately, so that the predicate can be
read with the eyes.

The first obligatory question to any such predicate is whether it is empty. The answer is by machine.

**Theorem 36.2** (`zero_is_NSSolution`). $\texttt{IsNSSolution}\ \nu\ 0\ 0\ 0$ for every $\nu\in\mathbb{R}$: the zero field with zero pressure and no force is a solution at any viscosity. 🟢

Modest, but this is exactly the inoculation against vacuity — the situation where a predicate holds for
free, by a stub witness (see the [glossary](GLOSSARY.md)) — that the twin branch lacked
before fix no. 1: the predicate is inhabited, the equation is real.

## Bochner honesty: the silent zero

The energetics is given by Bochner integrals over the volume: the kinetic energy
`kineticEnergy` $= \tfrac12\int\|u\|^2$ and the dissipation rate `dissipationRate`
$= \nu\int\sum_i\|\partial_i u\|^2$ (the enstrophy form); the nonnegativity of both is
`kineticEnergy_nonneg` and `dissipationRate_nonneg` 🟢.

A trap is hidden here, and the repository exposes it by machine. The Bochner integral in mathlib is
*silently equal to zero* on a non-integrable function (`MeasureTheory.integral_undef`).

**Theorem 36.3** (`kineticEnergy_of_not_integrable`). If $\|u\|^2$ is not integrable (the predicate `FiniteKineticEnergy` fails; the paired predicate for the gradients is `FiniteEnstrophy`), then $\texttt{kineticEnergy}\ u = 0$. 🟢 The equality `kineticEnergy u = 0`
may therefore mean not "the energy is zero" but "the energy is infinite or undefined". The "zero energy"
of a non-integrable field is an artifact of the definition, not physics.

For contrast, the honest zero of the zero field.

**Theorem 36.4** (`kineticEnergy_zero_field`). $\texttt{kineticEnergy}\ (\lambda x.\,0) = 0$. 🟢

The moral is the same as in the vacuity episodes of [24](24_BoundaryDecomp.md): every
energy statement is obliged to travel in a pair with a named integrability — otherwise it is
fragile-vacuous. Here this is not a wish but a proven warning.

## Narrowing the input: from a monolith to a pointwise balance

The analytic core of the branch is the energy inequality. In its monolithic form it is a named input —
a gate in the programme's terms: an honestly named red statement still missing on the way to the goal (see the [glossary](GLOSSARY.md)) —
`TwoTimeEnergyInequality`:

$$E(u(t_2)) + \int_{t_1}^{t_2} D(u(s))\,ds \le E(u(t_1)). \tag{36.2}$$

The session did not prove it — it *narrowed* it.

All the analysis is compressed into one pointwise input `EnergyBalanceLaw`:
the `HasDerivAt` identity $dE/dt = -D(t)$, the classical energy balance of a smooth rapidly decaying
solution (convection and pressure do no work thanks to $\mathrm{div}\,u=0$).

The glue from it is proven.

**Theorem 36.5** (`twoTimeEnergyInequality_of_energyBalance`). If the pointwise balance $\texttt{EnergyBalanceLaw}\ \nu\ u$ holds and the dissipation $s\mapsto D(u(s))$ is interval-integrable on every $[t_1,t_2]$, then $(36.2)$ holds: $\texttt{TwoTimeEnergyInequality}\ \nu\ u$. 🟢

The proof: the pointwise balance plus integrability
of the dissipation yield the two-time inequality (in fact an equality) via the FTC
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`). The input has become strictly narrower: not an integral
inequality over all pairs of times, but a single differential identity.

## The chain up to the cascade

Why the budget programme needs all this: `DissipativeStage ν u δ t₁ t₂` is a time interval on which
at least $\delta$ of dissipation has accumulated.

**Theorem 36.6** (`ns_no_infinite_dissipative_cascade`). Let $\delta>0$ and suppose the two-time inequality $\texttt{TwoTimeEnergyInequality}\ \nu\ u$ holds. Then there is no sequence of times $(t_k)_{k\in\mathbb{N}}$ with $\texttt{DissipativeStage}\ \nu\ u\ \delta\ t_k\ t_{k+1}$ for all $k$: an infinite sequence of $\delta$-dissipating steps does not exist. 🟢 (conditional on the inequality input) — the accumulated payment would exceed the starting energy $E(u(t_0))$.

This is a direct application of
`no_infinite_uniform_dissipative_cascade` from `DissipativeCascade` — quantization in action on
the genuine equation, not on an interface. The full chain from the narrow input glues Theorem 36.5 (`twoTimeEnergyInequality_of_energyBalance`) to Theorem 36.6 (`ns_no_infinite_dissipative_cascade`).

**Theorem 36.7** (`ns_no_infinite_dissipative_cascade_of_balance`). Let $\delta>0$, suppose $\texttt{EnergyBalanceLaw}\ \nu\ u$ holds and the dissipation is interval-integrable. Then there is no sequence $(t_k)$ with $\texttt{DissipativeStage}\ \nu\ u\ \delta\ t_k\ t_{k+1}$ for all $k$: `EnergyBalanceLaw` + integrability ⟹ no infinite $\delta$-cascade. 🟢

"No infinite cascade toward small scales under quantized
dissipation" — in form, this is exactly the certificate that regularity demands; for the substance, see
the boundary below.

## The ℝ-warning: why quantization is needed

The word "quantized" above carries all the weight, and this too is recorded by machine.

**Theorem 36.8** (`real_positive_work_not_wellfounded`). There exists $a:\mathbb{N}\to\mathbb{R}$ with $a_{n+1}<a_n$, $a_n>0$ and $a_n-a_{n+1}>0$ for all $n$ (`DissipativeCascade`, §2): an ℝ-sequence with strictly positive work at every step yet a finite total descent — the banal $a_n = 1/2^n$. 🟢

For the ℕ-engine of the twins, `Total y + Work ≤ Total x` with `0 < Work` yields
strict descent and well-foundedness for free; for ℝ, strictly positive work does *not* forbid
an infinite series of decreases. Hence the NS analogy with the ℕ-engine is only structural: the finiteness
of the cascade is bought by a uniform lower bound $\delta > 0$, not by positivity as such.

The question "where to
get $\delta$ for a real solution" is analysis, not structure, and it remains open here.

## The honest boundary

What is *not* proven — explicitly, without embellishment:

- 🔴 Existence and regularity of NS solutions — the millennium problem. The equation and the
  budget scaffolding over it are formalized; not a single step toward regularity itself is here. The cascade
  theorems say "*if* the solution satisfies the balance, *then* there is no infinite uniform cascade" —
  nobody has exhibited the premise for a nontrivial solution.
- 🔴 `EnergyBalanceLaw` is a named input. Its honest cost: differentiation under the integral
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + integration by parts + $\mathrm{div}\,u=0$;
  moreover, the divergence theorem in mathlib exists only in box form
  (`integral_divergence_of_hasFDerivAt_off_countable`), and the limit passage from boxes to $\mathbb{R}^3$
  is not formalized. The input is narrow and classical, but it is an input.
- The red line: the file does not mention prime numbers, and no transfer of NS results to the twins
  is implied. The only thing shared is the `DissipativeCascade` blueprint.

**Section takeaway.** Everything listed as proven (Theorem 36.2 (`zero_is_NSSolution`), Theorem 36.3 (`kineticEnergy_of_not_integrable`),
Theorem 36.5 (`twoTimeEnergyInequality_of_energyBalance`), both cascade theorems 36.6–36.7, Theorem 36.8 (`real_positive_work_not_wellfounded`))
is 🟢: standard Lean axioms, without `step00FirstCause`, without sorry.

The NS branch is a rare case in this
repository where honesty cost less than ambition: the equation is real, the integrals are under
supervision, the input is single and named, and the million-dollar problem stayed where it was.

## Postscript (chapter 40): two rescues of one warning

The ℝ-counterexample of the cascade's §2 warning — the sequence `(1/2)^n` with
positive work yet no finiteness — is literally the massless Yang–Mills
ladder (chapter 40, `GaplessLadder`/`cookedLadder`).

The rescues diverged.
NS is rescued by δ-quantization of the dissipation (`no_infinite_uniform_dissipative_cascade` —
and `no_uniformlyDissipative_ladder` 🟢 of chapter 40 shows that a uniformly
dissipative ladder is impossible). Yang–Mills — by rank quantization of the spectrum
(`massGap_of_quantizationLaw` 🟢: the ladder is not uniformly dissipative —
`cookedLadder_not_uniformlyDissipative` — and is killed only by the ℕ-rank through EPMI).

The common root of both physical branches is the impossibility of a perpetual engine;
the certificates differ and both are honestly named.

## Postscript (chapter 41): the integral is taken

The FTC glue of §5ter has been lifted to an identity.

**Theorem 36.9** (`energy_identity_of_energyBalance`). Under $\texttt{EnergyBalanceLaw}\ \nu\ u$ and interval-integrability of the dissipation, for all $t_1,t_2$ one has $E(u(t_2)) = E(u(t_1)) - \int_{t_1}^{t_2} D(u(s))\,ds$. 🟢 That is, `E(t₂) = E(t₁) − ∫D` as an equality (the two-time inequality $(36.2)$ of this chapter is a coarsening).

The solution is derived by integrating the equation.

**Theorem 36.10** (`isNSSolution_integral_form`). If $\texttt{IsNSSolution}\ \nu\ f\ u\ p$, each $s\mapsto u(s)(x)$ is differentiable and the right-hand side is interval-integrable, then for all $t,x$

$$u(t)(x) = u(0)(x) + \int_0^t \bigl(\nu\,\Delta u - \nabla p + f - (u\cdot\nabla)u\bigr)(s)(x)\,ds. \tag{36.3}$$

🟢 (the mild form, Banach-valued FTC).

Singularity as a perpetual engine
(the singular cascade) and the trilemma of the decree's fifth boundary — the mandatory three-branch test
of a boundary candidate before the intentional acceptance of a law by axiom (see the [glossary](GLOSSARY.md)) — are in chapter
[41_NSSmoothness.md](41_NSSmoothness.md). `EnergyBalanceLaw` remains
the named 🔴 input of that chapter.

<!--navbot-->

---

[← 35. P/NP: the local node](35_ClassicalPNP.md) · [Table of contents](00_Overview.md) · [37. Riemann fronts →](37_RiemannFronts.md)
<!--/navbot-->
