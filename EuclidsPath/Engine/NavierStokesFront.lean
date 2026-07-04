/-
  NavierStokesFront — GREEN (axiom-free) module of the Navier–Stokes smoothness
  branch in the perpetual-engine programme: "the engine's motion inside a rank
  is smooth everywhere — a point of discontinuity would create a perpetual
  engine; the solution is derived BY TAKING THE INTEGRAL".

  Architecture:
    * engine: `SingularCascade` — infinitely many δ-dissipative stages,
      compressed into a finite time T (a hypothetical singularity as an
      infinite quantized ladder); the green killer is the existing
      budget machine (`ns_no_infinite_dissipative_cascade`);
    * smoothness surrogate `NoSingularCascade` — HERO
      `noSingularCascade_of_energyBalance`: energy balance + integrability ⟹
      surrogate (green conditional chain, NS pattern);
    * "THE INTEGRAL IS TAKEN" twice: the energy IDENTITY as an equality
      (`energy_identity_of_energyBalance`, FTC-2 — the old §5 inequality
      turns out to be a coarsening of the equality derived by integration) and
      the integral form of the solution (`isNSSolution_integral_form`, E3-valued
      FTC: u t x = u 0 x + ∫₀ᵗ (νΔu − ∇p + f − (u·∇)u)).

  HONEST BOUNDARY (loudly): `NoSingularCascade` is a surrogate in the cascade
  language, NOT C^∞ regularity; Leray existence, uniqueness, and regularity are
  NOT proven; `EnergyBalanceLaw` remains a named 🔴 input; the millennium
  problem is NOT solved and NOT declared. The forged witnesses live at the level
  of fields/flows/energy PROFILES — none is a nontrivial
  IsNSSolution (disclosed).

  TRILEMMA of the decree's fifth boundary — all verdicts are machine (§7):
    V1 the universal form is REFUTABLE (cookedFlow — a stirred flow
       gains energy: the balance fails through HasDerivAt.unique);
    V2 the existential form is ALREADY PROVEN (the zero solution) — the decree is vacuous;
    V3 the manifestation (Riemann-mirror) form is INCOMPATIBLE with the accepted
       boundary: the forged profile cascade (tₙ = 1 − 2⁻ⁿ) is greenly PRESENTABLE,
       unlike an off-critical zero.
  ℝ-warning (the cookedLadder lesson of YM): the uniform profile cascade is killed
  by the budget (L10), but a forged NON-uniform one exists even under a nonnegative
  bounded profile (L11) — the surrogate speaks precisely about UNIFORM
  quantization. The module does NOT import the quarantine; no axiom/sorry.
-/
import Mathlib
import EuclidsPath.Engine.NavierStokes
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

noncomputable section

namespace EuclidsPath
namespace NavierStokesFront

open MeasureTheory
open EuclidsPath.NavierStokes
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-#############################################################################
  §1. Engine: the singular cascade and its green killers
#############################################################################-/

/-- **D1. SINGULAR CASCADE = PERPETUAL ENGINE:** an infinite
    sequence of moments before time `T`, each step of which is a
    δ-dissipating stage (`DissipativeStage`): infinitely many quantized
    dissipations, compressed into a hypothetical singular time. The field `before`
    carries the "before the singularity" semantics; DISCLOSED: killer L1 does not
    consume it — the budget forbids an infinite δ-cascade AT ALL, and a compressed
    one all the more (inertness disclosed, the vacuum_mem mirror of YM). -/
structure SingularCascade (ν : ℝ) (u : ℝ → E3 → E3) (δ T : ℝ) where
  times : ℕ → ℝ
  before : ∀ n, times n < T
  stage : ∀ n, DissipativeStage ν u δ (times n) (times (n + 1))

/-- **L1 — GREEN KILLER (direct application of the existing machine):**
    under the energy inequality there are no singular cascades. -/
theorem no_singularCascade_of_energyInequality
    (ν : ℝ) (u : ℝ → E3 → E3) (δ T : ℝ) (hδ : 0 < δ)
    (hE : TwoTimeEnergyInequality ν u) :
    IsEmpty (SingularCascade ν u δ T) :=
  ⟨fun C => ns_no_infinite_dissipative_cascade ν u δ hδ hE ⟨C.times, C.stage⟩⟩

/-- **D2. Honest smoothness surrogate** in the cascade language: under no
    quantization δ > 0 and to no finite time T does the singular cascade
    compress. DISCLOSED LOUDLY: this is NOT C^∞ regularity and NOT the Clay
    statement — only "there is no infinite uniformly-quantized dissipative
    ladder up to a finite time". -/
def NoSingularCascade (ν : ℝ) (u : ℝ → E3 → E3) : Prop :=
  ∀ δ T : ℝ, 0 < δ → IsEmpty (SingularCascade ν u δ T)

/-- **L2 — HERO (full chain from a narrow input, NS pattern):**
    the pointwise energy balance `dE/dt = −D` + integrability ⟹ smoothness
    surrogate: there are NO discontinuity points of the cascade type. -/
theorem noSingularCascade_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂) :
    NoSingularCascade ν u :=
  fun δ T hδ => no_singularCascade_of_energyInequality ν u δ T hδ
    (twoTimeEnergyInequality_of_energyBalance ν u hBal hInt)

/-#############################################################################
  §2. "Take the integral" I: the energy IDENTITY (FTC equality)
#############################################################################-/

/-- **L3 — ENERGY IDENTITY (the integral is TAKEN; an equality, not an
    inequality):** `E(t₂) = E(t₁) − ∫_{t₁}^{t₂} D` — FTC-2 from the energy balance.
    Time orientation is free (interval integral). -/
theorem energy_identity_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    (t₁ t₂ : ℝ) :
    kineticEnergy (u t₂)
      = kineticEnergy (u t₁) - ∫ s in t₁..t₂, dissipationRate ν (u s) := by
  have hftc :
      (∫ s in t₁..t₂, -(dissipationRate ν (u s)))
        = kineticEnergy (u t₂) - kineticEnergy (u t₁) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hBal s) ((hInt t₁ t₂).neg)
  rw [intervalIntegral.integral_neg] at hftc
  linarith

/-- **L4 — Icc form of the identity** (the same shape as `TwoTimeEnergyInequality`,
    but as an EQUALITY): the old §5 inequality is a coarsening of the identity
    derived by integration. -/
theorem energy_identity_Icc_of_energyBalance
    (ν : ℝ) (u : ℝ → E3 → E3)
    (hBal : EnergyBalanceLaw ν u)
    (hInt : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)
    {t₁ t₂ : ℝ} (hle : t₁ ≤ t₂) :
    kineticEnergy (u t₂) + ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s)
      = kineticEnergy (u t₁) := by
  have h := energy_identity_of_energyBalance ν u hBal hInt t₁ t₂
  have hIcc :
      (∫ s in t₁..t₂, dissipationRate ν (u s))
        = ∫ s in Set.Icc t₁ t₂, dissipationRate ν (u s) := by
    rw [intervalIntegral.integral_of_le hle,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc] at h
  linarith

/-#############################################################################
  §3. "Take the integral" II: the integral (mild) form of the solution
#############################################################################-/

/-- **L5 — ABSTRACT INTEGRAL RECONSTRUCTION (E3-valued FTC):**
    the trajectory is recovered by integrating its derivative:
    `F t = F 0 + ∫₀ᵗ f`. The Bochner integral is Banach-valued; `E3` is complete —
    the mathlib FTC applies verbatim. -/
theorem trajectory_eq_integral_of_hasDerivAt
    (F f : ℝ → E3)
    (hF : ∀ t : ℝ, HasDerivAt F (f t) t)
    (hInt : ∀ t₁ t₂ : ℝ, IntervalIntegrable f volume t₁ t₂)
    (t : ℝ) :
    F t = F 0 + ∫ s in (0:ℝ)..t, f s := by
  have h : (∫ s in (0:ℝ)..t, f s) = F t - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) (hInt 0 t)
  rw [h]
  abel

/-- The right-hand side of NS, solved for ∂ₜu (the exact form falling out
    of `momentum` via `eq_sub_of_add_eq`). -/
def nsTimeDerivative (ν : ℝ) (f : ℝ → E3 → E3) (u : ℝ → E3 → E3)
    (p : ℝ → E3 → ℝ) (t : ℝ) (x : E3) : E3 :=
  ν • vectorLaplacian (u t) x - gradient (p t) x + f t x - convectiveTerm (u t) x

/-- **L6:** NS solution + differentiability in time ⟹ the derivative of
    each point's trajectory is the right-hand side of the equation. -/
theorem hasDerivAt_of_isNSSolution
    {ν : ℝ} {f : ℝ → E3 → E3} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (sol : IsNSSolution ν f u p)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (t : ℝ) (x : E3) :
    HasDerivAt (fun s => u s x) (nsTimeDerivative ν f u p t x) t := by
  have h := (hdiff t x).hasDerivAt
  rw [eq_sub_of_add_eq (sol.momentum t x)] at h
  exact h

/-- **L7 — "DERIVE THE SOLUTION" (integral/mild form, honestly conditional):**
    a classical solution with differentiable and integrable time
    dynamics is RECOVERED by integrating the equation:
    `u t x = u 0 x + ∫₀ᵗ (νΔu − ∇p + f − (u·∇)u)`.
    DISCLOSED: this is NOT existence of a solution (conditional on sol/hdiff/hInt) —
    but the link "differential form ⟹ integral form" is machine-checked. -/
theorem isNSSolution_integral_form
    {ν : ℝ} {f : ℝ → E3 → E3} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (sol : IsNSSolution ν f u p)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hInt : ∀ (x : E3) (t₁ t₂ : ℝ),
      IntervalIntegrable (fun s => nsTimeDerivative ν f u p s x) volume t₁ t₂)
    (t : ℝ) (x : E3) :
    u t x = u 0 x + ∫ s in (0:ℝ)..t, nsTimeDerivative ν f u p s x :=
  trajectory_eq_integral_of_hasDerivAt (fun s => u s x)
    (fun s => nsTimeDerivative ν f u p s x)
    (fun s => hasDerivAt_of_isNSSolution sol hdiff s x) (hInt x) t

/-- The right-hand side on the zero solution is zero (fuel for the non-vacuity of L7). -/
theorem nsTimeDerivative_zero (ν : ℝ) (t : ℝ) (x : E3) :
    nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) t x = 0 := by
  simp [nsTimeDerivative, vectorLaplacian, convectiveTerm]

/-- Non-vacuity of L7: on the zero solution all three hypotheses are inhabited. -/
theorem zero_integral_form_inhabited (ν : ℝ) (t : ℝ) (x : E3) :
    (fun _ _ => (0:E3)) t x
      = (fun _ _ => (0:E3)) 0 x + ∫ s in (0:ℝ)..t,
          nsTimeDerivative ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) s x :=
  isNSSolution_integral_form (zero_is_NSSolution ν)
    (fun _ _ => differentiableAt_const _)
    (fun x t₁ t₂ => by
      simp only [nsTimeDerivative_zero]
      exact (continuous_const : Continuous fun _ : ℝ => (0:E3)).intervalIntegrable t₁ t₂)
    t x

/-#############################################################################
  §4. The zero solution: balance + surrogate (fuel for V2)
#############################################################################-/

/-- **L8: the energy balance of the zero solution — PROVEN** (`E ≡ 0`, `D ≡ 0`,
    `hasDerivAt_const`). The existential form of the fifth field is hence vacuous. -/
theorem zero_energyBalance (ν : ℝ) : EnergyBalanceLaw ν (fun _ _ => 0) := by
  intro t
  simpa [dissipationRate_zero_field] using
    hasDerivAt_const t (kineticEnergy (fun _ : E3 => (0 : E3)))

theorem zero_noSingularCascade (ν : ℝ) :
    NoSingularCascade ν (fun _ _ => 0) :=
  noSingularCascade_of_energyBalance ν _ (zero_energyBalance ν)
    (fun t₁ t₂ => by
      simp only [dissipationRate_zero_field]
      exact (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable t₁ t₂)

/-#############################################################################
  §5. Forged unbalanced flow — witness V1
      (ball indicator: the silent Bochner zero honestly bypassed)
#############################################################################-/

/-- Forged field: a unit vector inside the unit ball, zero outside.
    Integrable HONESTLY (not a silent zero — constant fields are unfit for
    forging, their energy silently collapses to 0). -/
def cookedField : E3 → E3 :=
  Set.indicator (Metric.ball (0 : E3) 1) (fun _ => e3 0)

theorem cookedField_normSq (x : E3) :
    ‖cookedField x‖ ^ 2
      = Set.indicator (Metric.ball (0 : E3) 1) (fun _ => (1 : ℝ)) x := by
  unfold cookedField
  by_cases hx : x ∈ Metric.ball (0 : E3) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simp [e3]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

theorem cookedField_energy :
    kineticEnergy cookedField
      = (1 / 2) * (volume (Metric.ball (0 : E3) 1)).toReal := by
  unfold kineticEnergy
  simp only [cookedField_normSq]
  rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]

theorem cookedField_energy_pos : 0 < kineticEnergy cookedField := by
  rw [cookedField_energy]
  have h0 : volume (Metric.ball (0 : E3) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : E3) one_pos).ne'
  have htop : volume (Metric.ball (0 : E3) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have := ENNReal.toReal_pos h0 htop
  linarith

/-- Forged "stirred" flow: `u t x = t • cookedField x` — the energy
    GROWS (external stirring), the balance must fail. -/
def cookedFlow : ℝ → E3 → E3 := fun t x => t • cookedField x

theorem cookedFlow_energy (t : ℝ) :
    kineticEnergy (cookedFlow t) = t ^ 2 * kineticEnergy cookedField := by
  unfold kineticEnergy cookedFlow
  have h : ∀ x : E3, ‖t • cookedField x‖ ^ 2 = t ^ 2 * ‖cookedField x‖ ^ 2 := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [h]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **L9 — FORGED BALANCE FAILURE (without computing D!):** `E(t) = c·t²` with
    `c > 0`; at `t = 1` the derivative `2c > 0`, whereas the balance would require `−D ≤ 0` —
    uniqueness of the derivative (`HasDerivAt.unique`) burns it. -/
theorem cookedFlow_not_energyBalance : ¬ EnergyBalanceLaw 1 cookedFlow := by
  intro hBal
  have h1 := hBal 1
  have hfun : (fun s => kineticEnergy (cookedFlow s))
      = fun s => kineticEnergy cookedField * s ^ 2 :=
    funext fun s => by rw [cookedFlow_energy]; ring
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℝ => kineticEnergy cookedField * s ^ 2)
      (kineticEnergy cookedField * 2) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).const_mul (kineticEnergy cookedField)
  have huniq : kineticEnergy cookedField * 2
      = -(dissipationRate 1 (cookedFlow 1)) := h2.unique h1
  have hD : 0 ≤ dissipationRate 1 (cookedFlow 1) :=
    dissipationRate_nonneg zero_le_one _
  have hc := cookedField_energy_pos
  linarith

/-- **L9b:** the same witness also refutes the monolithic ∀-form of the INEQUALITY. -/
theorem cookedFlow_not_twoTimeEnergyInequality :
    ¬ TwoTimeEnergyInequality 1 cookedFlow := by
  intro h
  have h01 := h 0 1 zero_le_one
  have hD : 0 ≤ ∫ s in Set.Icc (0:ℝ) 1, dissipationRate 1 (cookedFlow s) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun s _ => dissipationRate_nonneg zero_le_one _)
  have h0 : kineticEnergy (cookedFlow 0) = 0 := by rw [cookedFlow_energy]; ring
  have h1 : kineticEnergy (cookedFlow 1) = kineticEnergy cookedField := by
    rw [cookedFlow_energy]; ring
  have hc := cookedField_energy_pos
  rw [h0, h1] at h01
  linarith

/-#############################################################################
  §6. Profile level: ℝ-warning (the uniform cascade is killed,
      a forged non-uniform one exists)
#############################################################################-/

/-- **D3. Profile cascade (abstract; NO NS content — the forged
    witnesses live at the level of energy profiles, not solutions; disclosed):**
    infinitely many stages with a positive profile drop, all before `T`. -/
structure ProfileCascade (E : ℝ → ℝ) (T : ℝ) where
  times : ℕ → ℝ
  mono : ∀ n, times n ≤ times (n + 1)
  before : ∀ n, times n < T
  drop_pos : ∀ n, 0 < E (times n) - E (times (n + 1))

/-- **L10 — the UNIFORM profile cascade under a nonnegative profile is KILLED**
    (budget, the generic cascade machine; the `no_uniformlyDissipative_ladder`
    mirror of YM). -/
theorem no_uniform_profileCascade_of_nonneg
    (E : ℝ → ℝ) (T δ : ℝ) (hδ : 0 < δ) (hE : ∀ t, 0 ≤ E t)
    (C : ProfileCascade E T)
    (huniform : ∀ n, δ ≤ E (C.times n) - E (C.times (n + 1))) : False :=
  EuclidsPath.DissipativeCascade.no_infinite_uniform_dissipative_cascade
    (State := ℕ) (Step := fun m n => n = m + 1)
    (fun n => E (C.times n)) (fun m n => E (C.times m) - E (C.times n)) δ hδ
    (fun {m n} h => by subst h; exact le_of_eq (by ring))
    (fun {m n} h => by subst h; exact huniform m)
    (fun n => hE (C.times n))
    ⟨fun k => k, fun _ => rfl⟩

/-- Forged NONNEGATIVE profile `max (1−t) 0`. -/
def cookedProfile : ℝ → ℝ := fun t => max (1 - t) 0

theorem cookedProfile_at_stage (n : ℕ) :
    cookedProfile (1 - (1 / 2 : ℝ) ^ n) = (1 / 2 : ℝ) ^ n := by
  unfold cookedProfile
  have h : (1 : ℝ) - (1 - (1 / 2) ^ n) = (1 / 2) ^ n := by ring
  rw [h, max_eq_left (by positivity)]

/-- Forged cascade on `tₙ = 1 − 2⁻ⁿ`: drops `2⁻⁽ⁿ⁺¹⁾ > 0` — an infinite
    cascade compressed into `T = 1`, under a nonnegative bounded profile. -/
def cookedProfileCascade : ProfileCascade cookedProfile 1 where
  times := fun n => 1 - (1 / 2 : ℝ) ^ n
  mono := fun n => by
    have hp : (0:ℝ) < (1/2) ^ n := by positivity
    have h : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
    nlinarith
  before := fun n => by
    have : (0:ℝ) < (1/2) ^ n := by positivity
    linarith
  drop_pos := fun n => by
    rw [cookedProfile_at_stage n, cookedProfile_at_stage (n + 1)]
    have hp : (0:ℝ) < (1/2) ^ n := by positivity
    have h : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
    nlinarith

@[simp] theorem cookedProfileCascade_times (n : ℕ) :
    cookedProfileCascade.times n = 1 - (1 / 2 : ℝ) ^ n := rfl

/-- **L11 — ℝ-WARNING (the cookedLadder lesson of YM, machine):** the forged
    cascade is NOT uniform — its drops `2⁻⁽ⁿ⁺¹⁾` slip under every δ.
    Hence the budget (L10) does NOT kill it: `NoSingularCascade` is a surrogate about
    UNIFORM quantization; non-uniform profile cascades exist even
    under a nonnegative bounded profile. The surrogate ≠ C^∞ — disclosed. -/
theorem cookedProfileCascade_not_uniform (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n, δ ≤ cookedProfile (cookedProfileCascade.times n)
              - cookedProfile (cookedProfileCascade.times (n + 1)) := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
  have hstep := h n
  rw [cookedProfileCascade_times, cookedProfileCascade_times,
      cookedProfile_at_stage n, cookedProfile_at_stage (n + 1)] at hstep
  have hp : (0:ℝ) < (1/2) ^ n := by positivity
  have heq : (1/2 : ℝ) ^ n - (1/2) ^ (n + 1) = (1/2) ^ (n + 1) := by ring
  rw [heq] at hstep
  have hlt : ((1:ℝ)/2) ^ (n + 1) < (1/2) ^ n := by
    calc ((1:ℝ)/2) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
      _ < (1/2) ^ n := by nlinarith
  linarith

/-#############################################################################
  §7. TRILEMMA of the decree's fifth boundary — all verdicts are machine
#############################################################################-/

/-- **D4a. CANDIDATE 1 (universal form of the fifth field):** every flow
    obeys the energy balance. -/
def NsBalanceLawUniversal : Prop :=
  ∀ (ν : ℝ) (u : ℝ → E3 → E3), EnergyBalanceLaw ν u

/-- **D4b. CANDIDATE 2 (existential form):** SOME NS solution
    is balanced and free of singular cascades. -/
def NsBalanceLawExistential : Prop :=
  ∃ (ν : ℝ) (u : ℝ → E3 → E3),
    (∃ (f : ℝ → E3 → E3) (p : ℝ → E3 → ℝ), IsNSSolution ν f u p) ∧
    EnergyBalanceLaw ν u ∧ NoSingularCascade ν u

/-- **D4c. CANDIDATE 3 (manifestation form, Riemann mirror):** the cascade
    manifests through an unpayable supply of flows at all admissible
    ledger scales (the same object `DeviationFlowSupply` as in
    riemannBoundary and the YM ladder). The family is FREE of C — D-inertness
    exposed by the audits of §8. -/
def CascadeManifests {E : ℝ → ℝ} {T : ℝ} (_C : ProfileCascade E T) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def NsManifestationLaw : Prop :=
  ∀ (E : ℝ → ℝ) (T : ℝ) (C : ProfileCascade E T), CascadeManifests C

/-- **V1: CANDIDATE 1 GREEN-REFUTABLE** — the decree would be contradictory.
    Witness: cookedFlow (a stirred flow gains energy). -/
theorem nsLawUniversal_refuted : ¬ NsBalanceLawUniversal :=
  fun h => cookedFlow_not_energyBalance (h 1 cookedFlow)

/-- **V2: CANDIDATE 2 GREEN-PROVABLE** — the decree would be vacuous.
    Witness: the zero solution. -/
theorem nsLawExistential_green : NsBalanceLawExistential :=
  ⟨1, fun _ _ => 0,
   ⟨fun _ _ => 0, fun _ _ => 0, zero_is_NSSolution 1⟩,
   zero_energyBalance 1, zero_noSingularCascade 1⟩

/-- **V3: CANDIDATE 3 INCOMPATIBLE WITH THE ACCEPTED BOUNDARY** (green conditional
    form, mirror of YM-V3): the forged profile cascade — unlike an
    off-critical zero — is greenly PRESENTABLE; law + boundary ⟹ False. -/
theorem nsManifestationLaw_refutes_boundary
    (hLaw : NsManifestationLaw) : ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hres⟩
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf 1) :=
    strictSemanticExtended_resolves_old (hres 1)
  exact no_deviationFlowSupply_at_resolved_scale (projOf 1) hResolves
    (hLaw cookedProfile 1 cookedProfileCascade A 1 (projOf 1) hResolves)

theorem not_nsManifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) : ¬ NsManifestationLaw :=
  fun hLaw => nsManifestationLaw_refutes_boundary hLaw hBoundary

/-- **V3-characterization (unconditional — the quantifier is greenly inhabited):** law ⟺
    global freeze of all ledgers. -/
theorem nsManifestationLaw_iff_no_resolution :
    NsManifestationLaw ↔
      ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw A M0 proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw cookedProfile 1 cookedProfileCascade A M0 proj hres)
  · intro hFreeze E T C A M0 proj hres
    exact ((hFreeze A M0 proj) hres).elim

/-#############################################################################
  §8. Origin-anchor audits (instantiation of the condemning machine)
#############################################################################-/

theorem ns_bundling_audit (E : ℝ → ℝ) (T : ℝ) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun C : ProfileCascade E T => CascadeManifests C) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun C : ProfileCascade E T => CascadeManifests C)) ↔
      ¬ Nonempty (ProfileCascade E T) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

theorem ns_bundle_refuted_at_cooked :
    ¬ (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
         (fun C : ProfileCascade cookedProfile 1 => CascadeManifests C) ∧
       EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
         (fun C : ProfileCascade cookedProfile 1 => CascadeManifests C)) :=
  fun h => (ns_bundling_audit cookedProfile 1).mp h ⟨cookedProfileCascade⟩

theorem nsLaw_freeCollapse (E : ℝ → ℝ) (T : ℝ) :
    EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.FreeLawCollapse
      (fun C : ProfileCascade E T => CascadeManifests C)
      (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
          DeviationFlowSupply A M0) :=
  fun _C => Iff.rfl

theorem nsLaw_cannot_separate (E : ℝ → ℝ) (T : ℝ) :
    ¬ EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.ZeroSeparating
        (fun C : ProfileCascade E T => CascadeManifests C) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.no_zero_separation_under_freeCollapse
    (nsLaw_freeCollapse E T)

/-#############################################################################
  §9. FINISHING BLOW: junk-calculus of the indicator field (common to two forgings)
#############################################################################-/

/-- Helper: 1 − 1/(n+1) → 1. -/
theorem tendsto_one_sub_one_div :
    Filter.Tendsto (fun n : ℕ => (1 - 1/(n+1) : ℝ)) Filter.atTop (nhds 1) := by
  have hc : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have h1 := hc.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h1
  exact h1

/-- Helper: the radial sequence (1 − 1/(n+1))•x → x. -/
theorem tendsto_radial (x : E3) :
    Filter.Tendsto (fun n : ℕ => (1 - 1/(n+1) : ℝ) • x)
      Filter.atTop (nhds x) := by
  have h2 : Filter.Tendsto (fun n : ℕ => (1 - 1/(n+1) : ℝ) • x)
      Filter.atTop (nhds ((1:ℝ) • x)) := tendsto_one_sub_one_div.smul_const x
  rwa [one_smul] at h2

/-- Helper: the radial sequence of a sphere point lies in the ball. -/
theorem radial_mem_ball {x : E3} (hx : ‖x‖ = 1) (n : ℕ) :
    ((1 - 1/(n+1) : ℝ) • x) ∈ Metric.ball (0 : E3) 1 := by
  rw [Metric.mem_ball, dist_zero_right, norm_smul, hx, mul_one, Real.norm_eq_abs]
  have h1 : (0:ℝ) < 1/(n+1 : ℝ) := by positivity
  have h2 : (1:ℝ) ≤ (n:ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h3 : 1/(n+1 : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h2
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Discontinuity of `c • cookedField` on the sphere: the limit from inside `c • e3 0 ≠ 0` = the value. -/
theorem smul_cookedField_not_continuousAt_sphere
    {c : ℝ} (hc : c ≠ 0) {x : E3} (hx : ‖x‖ = 1) :
    ¬ ContinuousAt (fun y => c • cookedField y) x := by
  intro hcont
  have hx_not : x ∉ Metric.ball (0 : E3) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hx]
    exact lt_irrefl 1
  have hcomp : Filter.Tendsto (fun n : ℕ => c • cookedField ((1 - 1/(n+1) : ℝ) • x))
      Filter.atTop (nhds (c • cookedField x)) :=
    (hcont.tendsto).comp (tendsto_radial x)
  have hval : (fun n : ℕ => c • cookedField ((1 - 1/(n+1) : ℝ) • x))
      = fun _ => c • e3 0 :=
    funext fun n => by
      show c • cookedField ((1 - 1/(n+1) : ℝ) • x) = c • e3 0
      unfold cookedField
      rw [Set.indicator_of_mem (radial_mem_ball hx n)]
  rw [hval] at hcomp
  have hlim : c • cookedField x = c • e3 0 :=
    tendsto_nhds_unique hcomp tendsto_const_nhds
  rw [show cookedField x = 0 from by
        unfold cookedField; rw [Set.indicator_of_notMem hx_not],
      smul_zero] at hlim
  rcases smul_eq_zero.mp hlim.symm with h | h
  · exact hc h
  · exact absurd h (by simp [e3])

/-- **Junk-calculus:** the fderiv of the field `c • cookedField` is zero EVERYWHERE: inside and
    outside the ball honestly (local constant), on the sphere — a junk-zero of mathlib
    (the total fderiv of a non-differentiable function). -/
theorem smul_cookedField_fderiv (c : ℝ) (x : E3) :
    fderiv ℝ (fun y => c • cookedField y) x = 0 := by
  rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
  · have hx : x ∈ Metric.ball (0 : E3) 1 := by
      rwa [Metric.mem_ball, dist_zero_right]
    have h : (fun y => c • cookedField y) =ᶠ[nhds x] fun _ => c • e3 0 :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx)
        fun y hy => by
          show c • cookedField y = c • e3 0
          unfold cookedField
          rw [Set.indicator_of_mem hy]
    rw [h.fderiv_eq]
    exact fderiv_const_apply _
  · by_cases hc : c = 0
    · subst hc
      have h : (fun y => (0:ℝ) • cookedField y) = fun _ => (0 : E3) :=
        funext fun y => zero_smul ℝ _
      rw [h]
      exact fderiv_const_apply _
    · exact fderiv_zero_of_not_differentiableAt fun hd =>
        smul_cookedField_not_continuousAt_sphere hc heq hd.continuousAt
  · have hx : x ∈ (Metric.closedBall (0 : E3) 1)ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
      exact hgt
    have h : (fun y => c • cookedField y) =ᶠ[nhds x] fun _ => (0 : E3) :=
      Filter.eventuallyEq_of_mem
        (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx)
        fun y hy => by
          show c • cookedField y = 0
          unfold cookedField
          rw [Set.indicator_of_notMem
            (fun hb => hy (Metric.ball_subset_closedBall hb)), smul_zero]
    rw [h.fderiv_eq]
    exact fderiv_const_apply _

/-- All three spatial operators of the equation are zero on `c • cookedField`. -/
theorem smul_cookedField_NSdiv (c : ℝ) (x : E3) :
    NSdiv (fun y => c • cookedField y) x = 0 := by
  simp [NSdiv, smul_cookedField_fderiv]

theorem smul_cookedField_laplacian (c : ℝ) (x : E3) :
    vectorLaplacian (fun y => c • cookedField y) x = 0 := by
  have h : ∀ i : Fin 3,
      (fun y => fderiv ℝ (fun z => c • cookedField z) y (e3 i))
        = fun _ => (0 : E3) :=
    fun i => funext fun y => by rw [smul_cookedField_fderiv]; rfl
  simp only [vectorLaplacian, h]
  simp [fderiv_const_apply]

theorem smul_cookedField_convective (c : ℝ) (x : E3) :
    convectiveTerm (fun y => c • cookedField y) x = 0 := by
  simp [convectiveTerm, smul_cookedField_fderiv]

/-- General smul-energy (a generalization of `cookedFlow_energy`, the same skeleton). -/
theorem kineticEnergy_smul (c : ℝ) (w : E3 → E3) :
    kineticEnergy (fun x => c • w x) = c ^ 2 * kineticEnergy w := by
  unfold kineticEnergy
  have h : ∀ x : E3, ‖c • w x‖ ^ 2 = c ^ 2 * ‖w x‖ ^ 2 := fun x => by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [h]
  rw [MeasureTheory.integral_const_mul]
  ring

/-#############################################################################
  §10. TWO FORGINGS: degeneration under a forged force, junk-time (Dirichlet),
       forged pressure (the MAIN finding of the finishing blow)
#############################################################################-/

/-- **DANGER 1 (disclosure, machine): with a universally quantified
    force the solution predicate DEGENERATES** — any field with junk-zero
    divergence "solves" NS under a forged force (the total mathlib operators
    absorb everything). Hence f = 0 in the gate is MANDATORY. -/
theorem isNSSolution_of_cooked_force (ν : ℝ) (u : ℝ → E3 → E3)
    (hdiv : ∀ t x, NSdiv (u t) x = 0) :
    IsNSSolution ν
      (fun t x => deriv (fun s => u s x) t + convectiveTerm (u t) x
        - ν • vectorLaplacian (u t) x + gradient ((fun _ _ => (0:ℝ)) t) x)
      u (fun _ _ => 0) :=
  ⟨fun t x => by simp, hdiv⟩

/-- The Dirichlet function: indicator of the rationals. Nowhere continuous. -/
noncomputable def dirichlet : ℝ → ℝ :=
  Set.indicator (Set.range ((↑) : ℚ → ℝ)) fun _ => 1

theorem dirichlet_sq (t : ℝ) : dirichlet t ^ 2 = dirichlet t := by
  unfold dirichlet
  by_cases h : t ∈ Set.range ((↑) : ℚ → ℝ)
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

theorem dirichlet_nowhere_continuousAt (t : ℝ) : ¬ ContinuousAt dirichlet t := by
  intro h
  obtain ⟨a, ha, hat⟩ := mem_closure_iff_seq_limit.mp
    (Rat.denseRange_cast (𝕜 := ℝ) t)
  have h1 : dirichlet t = 1 := by
    have hcomp := (h.tendsto).comp hat
    rw [show (dirichlet ∘ a) = fun _ => (1:ℝ) from
      funext fun n => by
        show dirichlet (a n) = 1
        unfold dirichlet
        exact Set.indicator_of_mem (ha n) _] at hcomp
    exact tendsto_nhds_unique hcomp tendsto_const_nhds
  obtain ⟨b, hb, hbt⟩ := mem_closure_iff_seq_limit.mp (dense_irrational t)
  have h0 : dirichlet t = 0 := by
    have hcomp := (h.tendsto).comp hbt
    rw [show (dirichlet ∘ b) = fun _ => (0:ℝ) from
      funext fun n => by
        show dirichlet (b n) = 0
        unfold dirichlet
        exact Set.indicator_of_notMem (hb n) _] at hcomp
    exact tendsto_nhds_unique hcomp tendsto_const_nhds
  exact one_ne_zero (h1 ▸ h0)

/-- Forged junk-time flow: Dirichlet flicker of the indicator field. -/
noncomputable def dirichletFlow : ℝ → E3 → E3 :=
  fun t x => dirichlet t • cookedField x

/-- The trajectory `dirichlet • e3 0` is non-differentiable at every point of time:
    the projection onto the 0-th coordinate recovers Dirichlet, and differentiability
    would yield continuity. -/
theorem dirichlet_smul_not_differentiableAt (t : ℝ) :
    ¬ DifferentiableAt ℝ (fun s => dirichlet s • e3 0) t := by
  intro hd
  have hp := ((EuclideanSpace.proj (0 : Fin 3) :
      E3 →L[ℝ] ℝ).differentiableAt).comp t hd
  rw [show ((EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)
        ∘ fun s => dirichlet s • e3 0) = dirichlet from
    funext fun s => by
      show (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)
        (dirichlet s • e3 0) = dirichlet s
      simp [e3, smul_eq_mul]] at hp
  exact dirichlet_nowhere_continuousAt t hp.continuousAt

/-- **FORGING-A (junk-time): dirichletFlow — a FORCE-FREE NS solution with p = 0.**
    Momentum: junk-deriv in time (non-differentiability of Dirichlet), junk-zeros
    in space; incompressibility — junk. -/
theorem dirichletFlow_isNSSolution (ν : ℝ) :
    IsNSSolution ν (fun _ _ => 0) dirichletFlow (fun _ _ => 0) := by
  constructor
  · intro t x
    have hderiv : deriv (fun s => dirichletFlow s x) t = 0 := by
      by_cases hx : x ∈ Metric.ball (0 : E3) 1
      · have h : (fun s => dirichletFlow s x) = fun s => dirichlet s • e3 0 := by
          funext s
          show dirichlet s • cookedField x = _
          unfold cookedField
          rw [Set.indicator_of_mem hx]
        rw [h]
        exact deriv_zero_of_not_differentiableAt
          (dirichlet_smul_not_differentiableAt t)
      · have h : (fun s => dirichletFlow s x) = fun _ => (0 : E3) := by
          funext s
          show dirichlet s • cookedField x = 0
          unfold cookedField
          rw [Set.indicator_of_notMem hx, smul_zero]
        rw [h, deriv_const]
    show deriv (fun s => dirichletFlow s x) t
        + convectiveTerm (fun y => dirichlet t • cookedField y) x
      = ν • vectorLaplacian (fun y => dirichlet t • cookedField y) x
        - gradient (fun _ => (0:ℝ)) x + 0
    rw [hderiv, smul_cookedField_convective, smul_cookedField_laplacian]
    simp
  · intro t x
    exact smul_cookedField_NSdiv _ x

/-- **FORGING-A breaks the balance for any ν:** the energy = c₀·dirichlet — nowhere
    continuous, whereas HasDerivAt would yield continuity. -/
theorem dirichletFlow_not_energyBalance (ν : ℝ) :
    ¬ EnergyBalanceLaw ν dirichletFlow := by
  intro hBal
  have hE : (fun s => kineticEnergy (dirichletFlow s))
      = fun s => dirichlet s * kineticEnergy cookedField := funext fun s => by
    show kineticEnergy (fun x => dirichlet s • cookedField x) = _
    rw [kineticEnergy_smul, dirichlet_sq]
  have hcont : ContinuousAt (fun s => dirichlet s * kineticEnergy cookedField) 0 :=
    hE ▸ ((hBal 0).differentiableAt.continuousAt)
  have hc := cookedField_energy_pos
  have hdc : ContinuousAt dirichlet 0 := by
    have h2 := hcont.mul (continuousAt_const (y := (kineticEnergy cookedField)⁻¹))
    have h2' : ContinuousAt (fun s => dirichlet s * kineticEnergy cookedField
        * (kineticEnergy cookedField)⁻¹) 0 := h2
    have h3 : (fun s => dirichlet s * kineticEnergy cookedField
        * (kineticEnergy cookedField)⁻¹) = dirichlet := funext fun s => by
      field_simp
    rwa [h3] at h2'
  exact dirichlet_nowhere_continuousAt 0 hdc

/-- Forged pressure: `2 − y₀` inside the ball (honest gradient `−e3 0`),
    zero outside, jump ≥ 1 on the whole sphere (junk-gradient 0). -/
noncomputable def cookedPressure : E3 → ℝ :=
  Set.indicator (Metric.ball (0 : E3) 1) fun y => 2 - y 0

theorem hasGradientAt_two_sub_coord (x : E3) :
    HasGradientAt (fun y : E3 => 2 - y 0) (-(e3 0)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hf : HasFDerivAt (fun y : E3 => 2 - y 0)
      ((0 : E3 →L[ℝ] ℝ) - (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)) x :=
    (hasFDerivAt_const (2:ℝ) x).sub
      (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt
  have hdual : ((InnerProductSpace.toDual ℝ E3) (-(e3 0)) : E3 →L[ℝ] ℝ)
      = (0 : E3 →L[ℝ] ℝ) - (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ) := by
    refine ContinuousLinearMap.ext fun y => ?_
    simp [InnerProductSpace.toDual_apply_apply, inner_neg_left, e3,
      EuclideanSpace.inner_single_left]
  rw [hdual]
  exact hf

theorem cookedPressure_gradient_ball {x : E3} (hx : x ∈ Metric.ball (0:E3) 1) :
    gradient cookedPressure x = -(e3 0) :=
  ((hasGradientAt_two_sub_coord x).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx)
      fun y hy => by
        show cookedPressure y = 2 - y 0
        unfold cookedPressure
        exact Set.indicator_of_mem hy _)).gradient

theorem cookedPressure_gradient_notMem {x : E3}
    (hx : x ∉ Metric.ball (0:E3) 1) :
    gradient cookedPressure x = 0 := by
  have hge : 1 ≤ ‖x‖ := by
    by_contra h
    exact hx (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  rcases eq_or_lt_of_le hge with heq | hgt
  · -- sphere: discontinuity (from inside 2 − x₀ ≥ 1, value 0) ⟹ junk-gradient
    apply gradient_eq_zero_of_not_differentiableAt
    intro hd
    have hcont := hd.continuousAt
    have hxnorm : ‖x‖ = 1 := heq.symm
    have hcomp : Filter.Tendsto
        (fun n : ℕ => cookedPressure ((1 - 1/(n+1) : ℝ) • x))
        Filter.atTop (nhds (cookedPressure x)) :=
      (hcont.tendsto).comp (tendsto_radial x)
    have hval : (fun n : ℕ => cookedPressure ((1 - 1/(n+1) : ℝ) • x))
        = fun n : ℕ => 2 - (1 - 1/(n+1) : ℝ) * x 0 := funext fun n => by
      show cookedPressure ((1 - 1/(n+1) : ℝ) • x) = _
      unfold cookedPressure
      rw [Set.indicator_of_mem (radial_mem_ball hxnorm n)]
      rw [PiLp.smul_apply, smul_eq_mul]
    rw [hval] at hcomp
    have hlim : Filter.Tendsto (fun n : ℕ => 2 - (1 - 1/(n+1) : ℝ) * x 0)
        Filter.atTop (nhds (2 - x 0)) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (1 - 1/(n+1) : ℝ) * x 0)
          Filter.atTop (nhds ((1:ℝ) * x 0)) :=
        tendsto_one_sub_one_div.mul_const (x 0)
      have hc2 : Filter.Tendsto (fun _ : ℕ => (2:ℝ)) Filter.atTop (nhds 2) :=
        tendsto_const_nhds
      have h3 := hc2.sub h2
      rw [one_mul] at h3
      exact h3
    have heq2 : cookedPressure x = 2 - x 0 := tendsto_nhds_unique hcomp hlim
    have h0 : cookedPressure x = 0 := by
      unfold cookedPressure
      rw [Set.indicator_of_notMem hx]
    have hinner : @inner ℝ E3 _ (e3 0) x = x 0 := by
      simp [e3, EuclideanSpace.inner_single_left]
    have hnorm1 : ‖e3 0‖ = 1 := by simp [e3]
    have habs := abs_real_inner_le_norm (e3 0) x
    rw [hinner, hnorm1, one_mul, hxnorm] at habs
    have hx0 : x 0 = 2 := by
      rw [h0] at heq2
      linarith
    rw [hx0] at habs
    norm_num at habs
  · have hx' : x ∈ (Metric.closedBall (0 : E3) 1)ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
      exact hgt
    have hev : cookedPressure =ᶠ[nhds x] fun _ => (0:ℝ) :=
      Filter.eventuallyEq_of_mem
        (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx')
        fun y hy => by
          show cookedPressure y = 0
          unfold cookedPressure
          exact Set.indicator_of_notMem
            (fun hb => hy (Metric.ball_subset_closedBall hb)) _
    rw [hev.gradient_eq]
    simp [gradient_const]

/-- **FORGING-B (forged pressure — the MAIN finding of the finishing blow): cookedFlow —
    a FORCE-FREE NS solution, fully differentiable in time.**
    Disclosure: the f = 0 + time gate is NOT enough — the junk sits in ∇p on the sphere. -/
theorem cookedFlow_isNSSolution_unforced (ν : ℝ) :
    IsNSSolution ν (fun _ _ => 0) cookedFlow (fun _ => cookedPressure) := by
  constructor
  · intro t x
    by_cases hx : x ∈ Metric.ball (0 : E3) 1
    · have hderiv : deriv (fun s => cookedFlow s x) t = e3 0 := by
        have h : (fun s : ℝ => cookedFlow s x) = fun s => s • e3 0 := by
          funext s
          show s • cookedField x = _
          unfold cookedField
          rw [Set.indicator_of_mem hx]
        rw [h]
        simpa using ((hasDerivAt_id t).smul_const (e3 0)).deriv
      show deriv (fun s => cookedFlow s x) t
          + convectiveTerm (fun y => t • cookedField y) x
        = ν • vectorLaplacian (fun y => t • cookedField y) x
          - gradient cookedPressure x + 0
      rw [hderiv, smul_cookedField_convective, smul_cookedField_laplacian,
          cookedPressure_gradient_ball hx]
      simp
    · have hderiv : deriv (fun s => cookedFlow s x) t = 0 := by
        have h : (fun s : ℝ => cookedFlow s x) = fun _ => (0 : E3) := by
          funext s
          show s • cookedField x = 0
          unfold cookedField
          rw [Set.indicator_of_notMem hx, smul_zero]
        rw [h, deriv_const]
      show deriv (fun s => cookedFlow s x) t
          + convectiveTerm (fun y => t • cookedField y) x
        = ν • vectorLaplacian (fun y => t • cookedField y) x
          - gradient cookedPressure x + 0
      rw [hderiv, smul_cookedField_convective, smul_cookedField_laplacian,
          cookedPressure_gradient_notMem hx]
      simp
  · intro t x
    exact smul_cookedField_NSdiv _ x

/-- cookedFlow is fully differentiable in time (the time gate passes!). -/
theorem cookedFlow_time_differentiable (t : ℝ) (x : E3) :
    DifferentiableAt ℝ (fun s => cookedFlow s x) t :=
  ((hasDerivAt_id t).smul_const (cookedField x)).differentiableAt

/-#############################################################################
  §11. Gate-trilemma of the finishing blow: the final law and its verdicts
#############################################################################-/

/-- D7a. Candidate "only f = 0". -/
def NsUnforcedBalanceLaw : Prop :=
  ∀ (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ),
    0 ≤ ν → IsNSSolution ν (fun _ _ => 0) u p → EnergyBalanceLaw ν u

/-- D7b. Candidate "f = 0 + differentiability in time". -/
def NsTimeGatedBalanceLaw : Prop :=
  ∀ (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ),
    0 ≤ ν → IsNSSolution ν (fun _ _ => 0) u p →
    (∀ t x, DifferentiableAt ℝ (fun s => u s x) t) → EnergyBalanceLaw ν u

/-- **D8. FINAL GATE-LAW (candidate for the decree's third boundary):** every
    FORCE-FREE NS solution with honest differentiability of trajectories in time
    AND of the field in space obeys the pointwise energy balance, and its
    dissipation is interval-integrable. Both gates are MANDATORY — the weakened
    variants are refuted machine-wise (V1-a, V1-b below). Integrability is included
    in the decree (without it the yellow derivation would not reach the smoothness surrogate);
    the residual forging-risk of this conjunct is small and disclosed. ν = 0 (Euler)
    is covered by the decree — disclosed. -/
def NsSolutionBalanceLaw : Prop :=
  ∀ (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ),
    0 ≤ ν →
    IsNSSolution ν (fun _ _ => 0) u p →
    (∀ t x, DifferentiableAt ℝ (fun s => u s x) t) →
    (∀ t x, DifferentiableAt ℝ (u t) x) →
    EnergyBalanceLaw ν u ∧
    (∀ t₁ t₂ : ℝ, IntervalIntegrable (fun s => dissipationRate ν (u s)) volume t₁ t₂)

/-- **V1-a: the f=0-gate is REFUTABLE via the junk-time channel** (Dirichlet; p ≡ 0). -/
theorem nsUnforcedBalanceLaw_refuted_by_junk_time : ¬ NsUnforcedBalanceLaw :=
  fun h => dirichletFlow_not_energyBalance 1
    (h 1 dirichletFlow (fun _ _ => 0) zero_le_one (dirichletFlow_isNSSolution 1))

/-- **V1-b: the f=0 + TIME-gate is ALSO REFUTABLE — via the forged-pressure channel**
    (the main finding of the finishing blow: the junk sits in ∇p, not in ∂ₜ). -/
theorem nsTimeGatedBalanceLaw_refuted : ¬ NsTimeGatedBalanceLaw :=
  fun h => cookedFlow_not_energyBalance
    (h 1 cookedFlow (fun _ => cookedPressure) zero_le_one
      (cookedFlow_isNSSolution_unforced 1) cookedFlow_time_differentiable)

theorem nsUnforcedBalanceLaw_refuted : ¬ NsUnforcedBalanceLaw :=
  fun h => nsTimeGatedBalanceLaw_refuted fun ν u p hν sol _ => h ν u p hν sol

/-- The gates SEPARATE the forgings (machine honesty of the final gate):
    cookedField is non-differentiable in space on the sphere. -/
theorem cookedField_not_space_differentiable :
    ¬ DifferentiableAt ℝ cookedField (e3 0) := by
  intro hd
  have h1 : (fun y => (1:ℝ) • cookedField y) = cookedField :=
    funext fun y => one_smul ℝ _
  exact smul_cookedField_not_continuousAt_sphere one_ne_zero
    (by simp [e3]) (h1 ▸ hd.continuousAt)

/-- Forging-B fails the spatial gate. -/
theorem cookedFlow_fails_space_gate :
    ¬ ∀ t x, DifferentiableAt ℝ (cookedFlow t) x := by
  intro h
  have h1 : cookedFlow 1 = cookedField := funext fun y => one_smul ℝ _
  exact cookedField_not_space_differentiable (h1 ▸ h 1 (e3 0))

/-- Forging-A fails the time gate. -/
theorem dirichletFlow_fails_time_gate :
    ¬ ∀ t x, DifferentiableAt ℝ (fun s => dirichletFlow s x) t := by
  intro h
  have h0 : (0:E3) ∈ Metric.ball (0:E3) 1 := by simp
  have hd := h 0 0
  rw [show (fun s => dirichletFlow s (0:E3)) = fun s => dirichlet s • e3 0 from
    funext fun s => by
      show dirichlet s • cookedField 0 = _
      unfold cookedField
      rw [Set.indicator_of_mem h0]] at hd
  exact dirichlet_smul_not_differentiableAt 0 hd

/-- **V2-fuel: the gate class is INHABITED** — the zero solution passes both gates
    and satisfies the conclusion: the final law is not vacuous, but is also not derived
    (its derivation needs the divergence theorem on ℝ³ — absent, see
    the header of Engine/NavierStokes.lean). -/
theorem zero_passes_gates_and_conclusion (ν : ℝ) :
    IsNSSolution ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) ∧
    (∀ (t : ℝ) (x : E3),
      DifferentiableAt ℝ (fun s : ℝ => (fun _ _ => (0:E3)) s x) t) ∧
    (∀ (t : ℝ) (x : E3), DifferentiableAt ℝ ((fun _ _ => (0:E3)) t) x) ∧
    EnergyBalanceLaw ν (fun _ _ => 0) ∧
    (∀ t₁ t₂ : ℝ, IntervalIntegrable
      (fun s => dissipationRate ν ((fun _ _ => (0:E3)) s)) volume t₁ t₂) := by
  refine ⟨zero_is_NSSolution ν, ?_, ?_, zero_energyBalance ν, ?_⟩
  · intro t x
    exact differentiableAt_const (0:E3)
  · intro t x
    exact differentiableAt_const (0:E3)
  · intro t₁ t₂
    simp only [dissipationRate_zero_field]
    exact (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).intervalIntegrable t₁ t₂

/-- **YELLOW FUEL (green lemma):** the gate-law ⟹ smoothness surrogate of
    EVERY gate-solution. -/
theorem noSingularCascade_of_nsSolutionBalanceLaw
    (hLaw : NsSolutionBalanceLaw) (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ)
    (hν : 0 ≤ ν) (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (hdt : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hdx : ∀ t x, DifferentiableAt ℝ (u t) x) :
    NoSingularCascade ν u :=
  noSingularCascade_of_energyBalance ν u
    (hLaw ν u p hν sol hdt hdx).1 (hLaw ν u p hν sol hdt hdx).2

/-- Energy identity of every gate-solution from the law (FTC). -/
theorem energyIdentity_of_nsSolutionBalanceLaw
    (hLaw : NsSolutionBalanceLaw) (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ)
    (hν : 0 ≤ ν) (sol : IsNSSolution ν (fun _ _ => 0) u p)
    (hdt : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t)
    (hdx : ∀ t x, DifferentiableAt ℝ (u t) x) (t₁ t₂ : ℝ) :
    kineticEnergy (u t₂)
      = kineticEnergy (u t₁) - ∫ s in t₁..t₂, dissipationRate ν (u s) :=
  energy_identity_of_energyBalance ν u
    (hLaw ν u p hν sol hdt hdx).1 (hLaw ν u p hν sol hdt hdx).2 t₁ t₂

/-- **OVERPAYMENT DISCLOSED (green, honest price):** the surrogate would have
    sufficed even with an INEQUALITY (not the identity) — there is NO "law ⟺ goal" here (unlike
    riemannManifestation_asserts_RH): the reverse implication is unknown,
    the decree may pay more than the goal is worth. -/
theorem noSingularCascade_of_twoTimeInequality
    (ν : ℝ) (u : ℝ → E3 → E3) (hE : TwoTimeEnergyInequality ν u) :
    NoSingularCascade ν u :=
  fun δ T hδ => no_singularCascade_of_energyInequality ν u δ T hδ hE

end NavierStokesFront
end EuclidsPath

end

-- Machine visibility of purity in the build log
-- (expected [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.NavierStokesFront.energy_identity_of_energyBalance
#print axioms EuclidsPath.NavierStokesFront.isNSSolution_integral_form
#print axioms EuclidsPath.NavierStokesFront.noSingularCascade_of_energyBalance
#print axioms EuclidsPath.NavierStokesFront.nsLawUniversal_refuted
#print axioms EuclidsPath.NavierStokesFront.nsLawExistential_green
#print axioms EuclidsPath.NavierStokesFront.nsManifestationLaw_refutes_boundary
#print axioms EuclidsPath.NavierStokesFront.nsUnforcedBalanceLaw_refuted_by_junk_time
#print axioms EuclidsPath.NavierStokesFront.nsTimeGatedBalanceLaw_refuted
#print axioms EuclidsPath.NavierStokesFront.cookedFlow_isNSSolution_unforced
#print axioms EuclidsPath.NavierStokesFront.dirichletFlow_isNSSolution
#print axioms EuclidsPath.NavierStokesFront.noSingularCascade_of_nsSolutionBalanceLaw
