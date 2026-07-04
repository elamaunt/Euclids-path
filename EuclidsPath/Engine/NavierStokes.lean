/-
  NavierStokes — the Navier–Stokes equation itself, formalised via mathlib analysis.
  Prose: prose/24_BoundaryDecomp.md (section «Dissipative cascade»).

  FORMALISED HERE (genuine PDE predicate, mathlib fderiv/gradient/∫):
    * `NSdiv` (divergence = trace of Jacobian componentwise), `vectorLaplacian`, `convectiveTerm` ((u·∇)u);
    * `IsNSSolution ν f u p` — incompressible NS equations in classical strong form:
        ∂ₜu + (u·∇)u = ν·Δu − ∇p + f,   div u = 0;
    * NON-VACUITY: `zero_is_NSSolution` (zero field is a solution) — predicate is inhabited;
    * `kineticEnergy` (½∫‖u‖²), `dissipationRate` (ν∫Σᵢ‖∂ᵢu‖²) — Bochner integrals;
    * LINK TO CASCADE: `ns_no_infinite_dissipative_cascade` — under the energy inequality
      (named input) an infinite sequence of δ-dissipating time intervals is impossible
      (via `DissipativeCascade.no_infinite_uniform_dissipative_cascade`);
    * INTEGRAL HONESTY (§5bis): `FiniteKineticEnergy`/`FiniteEnstrophy` + `kineticEnergy_of_not_integrable`
      — Bochner integral is SILENTLY zero on a non-integrable field (`integral_undef`); warning proved;
    * INPUT DECOMPOSITION (§5ter): `twoTimeEnergyInequality_of_energyBalance` — PROVED (FTC glue);
      the monolithic inequality reduced to the NARROW pointwise named input `EnergyBalanceLaw` (`dE/dt = −D`);
      full chain `ns_no_infinite_dissipative_cascade_of_balance` — from narrow input to cascade.

  HONEST BOUNDARY. The EQUATION and scaffolding are formalised; NOT proved: existence/regularity of solutions
  (millennium problem) and the pointwise energy balance `EnergyBalanceLaw` (= differentiation under the integral
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` + integration by parts + div u = 0; in mathlib
  the divergence theorem exists only in box form `integral_divergence_of_hasFDerivAt_off_countable`,
  the limiting passage to ℝ³ is not formalised — named input). No connection to prime numbers —
  the red line is untouched.
-/
import Mathlib
import EuclidsPath.Engine.DissipativeCascade

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.NavierStokes

open MeasureTheory
open scoped BigOperators

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Standard basis vector. -/
def e3 (i : Fin 3) : E3 := EuclideanSpace.single i 1

/-! ### §1. Differential operators -/

/-- Divergence of a vector field: `div u = Σᵢ ∂ᵢuᵢ` (trace of Jacobian). -/
def NSdiv (u : E3 → E3) (x : E3) : ℝ :=
  ∑ i, fderiv ℝ u x (e3 i) i

/-- Vector Laplacian: `Δu = Σᵢ ∂ᵢ(∂ᵢu)` (componentwise second directional derivatives). -/
def vectorLaplacian (u : E3 → E3) (x : E3) : E3 :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (e3 i)) x (e3 i)

/-- Convective term `(u·∇)u`: derivative of `u` along `u` itself. -/
def convectiveTerm (u : E3 → E3) (x : E3) : E3 :=
  fderiv ℝ u x (u x)

/-! ### §2. Navier–Stokes equations (incompressible, classical strong form) -/

/--
**Navier–Stokes equations.** `u : ℝ → E3 → E3` — velocity field, `p : ℝ → E3 → ℝ` — pressure,
`ν` — viscosity, `f` — external force:

  `∂ₜu + (u·∇)u = ν·Δu − ∇p + f`   (momentum balance)
  `div u = 0`                       (incompressibility)
-/
structure IsNSSolution (ν : ℝ) (f : ℝ → E3 → E3)
    (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop where
  momentum : ∀ t x,
    deriv (fun s => u s x) t + convectiveTerm (u t) x
      = ν • vectorLaplacian (u t) x - gradient (p t) x + f t x
  incompressible : ∀ t x, NSdiv (u t) x = 0

/-! ### §3. Non-vacuity: zero solution -/

/-- **`zero_is_NSSolution` — PROVED (non-vacuity).** The zero field with zero pressure and no
    force is a NS solution for any viscosity. The predicate is inhabited — this is a genuine equation, not a dummy. -/
theorem zero_is_NSSolution (ν : ℝ) :
    IsNSSolution ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  constructor
  · intro t x
    have hconv : convectiveTerm (fun _ : E3 => (0 : E3)) x = 0 := by
      simp [convectiveTerm, fderiv_const]
    have hlap : vectorLaplacian (fun _ : E3 => (0 : E3)) x = 0 := by
      simp [vectorLaplacian, fderiv_const]
    have hgrad : gradient (fun _ : E3 => (0 : ℝ)) x = 0 := by
      simp [gradient_const]
    simp [hconv, hlap, hgrad]
  · intro t x
    simp [NSdiv, fderiv_const]

/-! ### §4. Energy and dissipation (Bochner integrals over volume) -/

/-- Kinetic energy: `E(u) = ½∫‖u(x)‖² dx`. -/
def kineticEnergy (u : E3 → E3) : ℝ :=
  (1 / 2) * ∫ x : E3, ‖u x‖ ^ 2

/-- Dissipation rate: `D(u) = ν·∫ Σᵢ ‖∂ᵢu(x)‖² dx` (enstrophy form). -/
def dissipationRate (ν : ℝ) (u : E3 → E3) : ℝ :=
  ν * ∫ x : E3, ∑ i, ‖fderiv ℝ u x (e3 i)‖ ^ 2

/-- Energy is non-negative. -/
theorem kineticEnergy_nonneg (u : E3 → E3) : 0 ≤ kineticEnergy u := by
  unfold kineticEnergy
  have : 0 ≤ ∫ x : E3, ‖u x‖ ^ 2 :=
    integral_nonneg (fun x => by positivity)
  linarith

/-! ### §5. Energy inequality — named input

For smooth rapidly decaying solutions (f = 0): `E(u(t₂)) + ∫_{t₁}^{t₂} D(u(s)) ds ≤ E(u(t₁))`.
Proof — integration by parts + `div u = 0` (convection and pressure do no work).
This is an ANALYTIC INPUT: it is NOT proved here. -/

/-- Two-time energy inequality (cocycle form) — named input. -/
def TwoTimeEnergyInequality (ν : ℝ) (u : ℝ → E3 → E3) : Prop :=
  ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
    kineticEnergy (u t₂) + ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s)
      ≤ kineticEnergy (u t₁)

/-! ### §5bis. INTEGRAL HONESTY: integrability and the Bochner «silent zero»

⚠️ The Bochner integral in mathlib **silently equals zero** on a non-integrable function
(`MeasureTheory.integral_undef`). Hence `kineticEnergy u = 0` may mean NOT «energy is zero»
but «energy is infinite/undefined». Every energy statement must be paired with a
named integrability hypothesis — otherwise it is fragile-vacuous. -/

/-- Finite kinetic energy: `‖u‖²` is integrable (Bochner is honest). -/
def FiniteKineticEnergy (u : E3 → E3) : Prop :=
  Integrable (fun x : E3 => ‖u x‖ ^ 2)

/-- Finite enstrophy: `Σᵢ‖∂ᵢu‖²` is integrable. -/
def FiniteEnstrophy (u : E3 → E3) : Prop :=
  Integrable (fun x : E3 => ∑ i, ‖fderiv ℝ u x (e3 i)‖ ^ 2)

/-- **`kineticEnergy_of_not_integrable` — PROVED (silent-zero warning).** Without
    `FiniteKineticEnergy` the Bochner integral SILENTLY returns `0`: the «zero energy» of a non-integrable field is
    an artefact of the definition, not physics. Therefore integrability is a mandatory part of any named input. -/
theorem kineticEnergy_of_not_integrable {u : E3 → E3}
    (h : ¬ FiniteKineticEnergy u) : kineticEnergy u = 0 := by
  unfold kineticEnergy
  rw [integral_undef h]
  ring

/-- Zero field: energy is genuinely `0` (not a silent zero — honest). -/
theorem kineticEnergy_zero_field : kineticEnergy (fun _ : E3 => (0 : E3)) = 0 := by
  simp [kineticEnergy]

/-- Zero field: dissipation is `0`. -/
theorem dissipationRate_zero_field (ν : ℝ) :
    dissipationRate ν (fun _ : E3 => (0 : E3)) = 0 := by
  simp [dissipationRate, fderiv_const]

/-- Dissipation is non-negative (when `ν ≥ 0`). -/
theorem dissipationRate_nonneg {ν : ℝ} (hν : 0 ≤ ν) (u : E3 → E3) :
    0 ≤ dissipationRate ν u := by
  unfold dissipationRate
  have : 0 ≤ ∫ x : E3, ∑ i, ‖fderiv ℝ u x (e3 i)‖ ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => by positivity
  positivity

/-! ### §5ter. INPUT DECOMPOSITION: pointwise energy balance ⟹ two-time inequality

The monolithic input §5 is split: all analysis (differentiation under the integral —
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; integration by parts / divergence theorem —
in mathlib only the box form `integral_divergence_of_hasFDerivAt_off_countable` exists, the limiting
passage to ℝ³ is not formalised) is compressed into ONE pointwise named input `EnergyBalanceLaw`: `dE/dt = −D`.
The glue from it to `TwoTimeEnergyInequality` — PROVED (FTC). The input became strictly narrower:
not an integral inequality but the classical balance identity. -/

/-- Pointwise energy balance `dE/dt = −D(t)` — named input (narrow form).
    For smooth rapidly decaying solutions this identity = differentiation under the integral +
    integration by parts + `div u = 0` (convection and pressure do no work). -/
def EnergyBalanceLaw (ν : ℝ) (u : ℝ → E3 → E3) : Prop :=
  ∀ t : ℝ, HasDerivAt (fun s => kineticEnergy (u s)) (-(dissipationRate ν (u t))) t

/-- **`twoTimeEnergyInequality_of_energyBalance` — PROVED (FTC glue).** Pointwise balance
    `dE/dt = −D` + integrability of dissipation ⟹ two-time energy INEQUALITY (in fact —
    equality). The old monolithic input §5 is reduced to the narrower pointwise named input `EnergyBalanceLaw`. -/
theorem twoTimeEnergyInequality_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    TwoTimeEnergyInequality ν u := by
  intro t₁ t₂ hle
  -- FTC: E(t₂) − E(t₁) = ∫_{t₁}^{t₂} (−D)
  have hftc :
      (∫ s in t₁..t₂, -(dissipationRate ν (u s)))
        = kineticEnergy (u t₂) - kineticEnergy (u t₁) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hBal s) ((hInt t₁ t₂).neg)
  -- interval integral = integral over Icc (boundary has measure zero)
  have hIcc :
      (∫ s in t₁..t₂, dissipationRate ν (u s))
        = ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s) := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_neg, hIcc] at hftc
  linarith [hftc]

/-! ### §6. LINK TO CASCADE: inequality ⟹ finiteness of the δ-dissipating cascade -/

/-- δ-dissipating time step: interval over which accumulated dissipation ≥ δ. -/
def DissipativeStage (ν : ℝ) (u : ℝ → E3 → E3) (δ : ℝ) (t₁ t₂ : ℝ) : Prop :=
  t₁ ≤ t₂ ∧ δ ≤ ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s)

/--
**`ns_no_infinite_dissipative_cascade` — PROVED (conditional on the energy-inequality input).** If a NS solution
satisfies the energy inequality, then there does NOT exist an infinite sequence of time instants
each successive step of which dissipates ≥ δ > 0: the accumulated dissipation would exceed `E(u t₀)`.
Direct application of `DissipativeCascade.no_infinite_uniform_dissipative_cascade` — quantisation in action
on the GENUINE equation. This is the form «no infinite cascade to small scales under quantised
dissipation» — exactly the certificate required for regularity. -/
theorem ns_no_infinite_dissipative_cascade
    (ν : ℝ) (u : ℝ → E3 → E3) (δ : ℝ) (hδ : 0 < δ)
    (hE : TwoTimeEnergyInequality ν u) :
    ¬ ∃ times : ℕ → ℝ, ∀ k, DissipativeStage ν u δ (times k) (times (k + 1)) := by
  rintro ⟨times, hstage⟩
  exact EuclidsPath.DissipativeCascade.no_infinite_uniform_dissipative_cascade
    (State := ℝ) (Step := fun t₁ t₂ => DissipativeStage ν u δ t₁ t₂)
    (fun t => kineticEnergy (u t))
    (fun t₁ t₂ => ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s))
    δ hδ
    (fun {t₁ t₂} h => hE t₁ t₂ h.1)
    (fun {t₁ t₂} h => h.2)
    (fun t => kineticEnergy_nonneg (u t))
    ⟨times, hstage⟩

/-- **`ns_no_infinite_dissipative_cascade_of_balance` — PROVED (full chain from the narrow input).**
    Pointwise energy balance `dE/dt = −D` + integrability of dissipation ⟹ no infinite
    δ-cascade. Composition of the FTC glue (§5ter) and quantisation (§6): the entire analytic remainder of the NS branch
    compressed into ONE pointwise named input `EnergyBalanceLaw`. -/
theorem ns_no_infinite_dissipative_cascade_of_balance
    (ν : ℝ) (u : ℝ → E3 → E3) (δ : ℝ) (hδ : 0 < δ)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    ¬ ∃ times : ℕ → ℝ, ∀ k, DissipativeStage ν u δ (times k) (times (k + 1)) :=
  ns_no_infinite_dissipative_cascade ν u δ hδ
    (twoTimeEnergyInequality_of_energyBalance ν u hBal hInt)

end EuclidsPath.NavierStokes
