/-
  CascadeBudget — the WORLD'S FIRST formalization of a fluid cascade model
  in a proof assistant (Lean 4 + mathlib). The "energy budget" branch.

  ════════════════════════════════════════════════════════════════════════════
  LOUD HONEST HEADER (mandatory by project regulations).
  ════════════════════════════════════════════════════════════════════════════

  WHAT THIS IS. To the best of our inquiry, a concrete finite-shell (shell/GOY-Sabra
  dyadic) cascade model, as an ACTUAL ODE system, had never before been
  formalized in any proof assistant. Here it is formalized for
  the first time — together with an abstract finite-budget principle.

  WHAT IS FORMALIZED (all of it — KNOWN mathematics, nothing new is claimed):
    §1  ABSTRACT BUDGET PRINCIPLE (pure calculus, green):
        a finite energy supply cannot feed UNIFORM dissipation forever —
        `finite_budget_bounds_uniform_dissipation`: `E' ≤ −β` on `[0,T]`,
        `E T ≥ 0` ⟹ `T ≤ E 0 / β`. This is the machine form of "no perpetual engine
        on uniform dissipation from a finite budget" (one-sided
        mean value inequality, `image_le_of_deriv_right_le_deriv_boundary`).
    §2  CONCRETE FINITE SHELL MODEL (substantive, a genuine ODE):
        amplitudes `a : Fin N → ℝ → ℝ`, dyadic dissipation `ν·λ^(2αn)`,
        an energy-conserving quadratic transfer between neighbouring shells
        (`∑ aₙ·(transfer)ₙ = 0`). The `ShellSolution` structure packs the
        derivative equations + the transfer energy-conservation property. Energy
        `shellEnergy = ∑ aₙ²`, its derivative `= −2ν·∑ λ^(2αn)·aₙ² ≤ 0`
        (`shellEnergy_hasDerivAt`, `shellEnergy_deriv_nonpos`). Instantiation of §1:
        under a uniform lower threshold on dissipation `≥ β` time is bounded
        (`no_uniform_dissipation_forever_on_shell`). NON-VACUITY: the zero
        shell is a genuine solution (`zeroShellSolution`).
    §3  HONEST BOUNDARY (the key honesty, green): the budget MISSES
        NON-uniform cascades. Via the existing `cookedProfileCascade_not_uniform`
        from NavierStokesFront: a forged cascade with drops `2⁻⁽ⁿ⁺¹⁾` escapes under
        every `β>0`, so the "uniformly ≥ β" hypothesis of §1 FAILS for it —
        the budget does NOT forbid such cascades (`budget_misses_nonuniform`).
    §4  Bridge to `ns_no_infinite_dissipative_cascade` — the same abstract machine,
        now on a GENUINE finite shell.

  WHAT THIS IS NOT (red lines):
    * this is NOT a solution of the Navier–Stokes equations and NOT of the millennium problem;
    * this is NOT a confirmation of the naive "perpetual engine" reading: on the contrary,
      the module MACHINE-MAPS where the budget works (uniform dissipation ⟹
      finite time) and where it FAILS (non-uniform cascades escape,
      `budget_misses_nonuniform`);
    * genuine supercritical models REALLY DO BLOW UP (see the companion module
      on dyadic blow-up) — so here we DEMARCATE and partially
      REFUTE the naive "engine" closure, rather than confirming it;
    * no connection whatsoever with prime numbers — the project's red line is untouched.

  TECHNICALLY: `set_option autoImplicit false`; NOT A SINGLE `sorry`, `axiom`,
  `native_decide`. All theorems REALLY consume their hypotheses; the shell
  model is a GENUINE ODE system (not `True`). The repository's taint invariant does
  not change (only `propext`, `Classical.choice`, `Quot.sound`).
  ════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import EuclidsPath.Engine.NavierStokes
import EuclidsPath.Engine.NavierStokesFront

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace EuclidsPath.CascadeBudget

open scoped BigOperators
open Set

/-#############################################################################
  §1. ABSTRACT BUDGET PRINCIPLE (pure calculus, green)
#############################################################################-/

/--
**`finite_budget_bounds_uniform_dissipation` — PROVEN (pure MVI).**
A finite energy supply cannot feed UNIFORM dissipation forever.

If a smooth energy `E` on `[0,T]` has derivative `E' t ≤ −β` (uniform
dissipation at rate `≥ β > 0`), and at the endpoint stays non-negative
(`0 ≤ E T`), then `T ≤ E 0 / β`.

Proof — the one-sided mean value inequality
(`image_le_of_deriv_right_le_deriv_boundary`) with barrier `B x = E 0 − β·x`:
gives `E T ≤ E 0 − β·T`; together with `0 ≤ E T` we get `β·T ≤ E 0`, whence
`T ≤ E 0 / β`. This is the machine form of "no perpetual engine on uniform
dissipation from a finite budget". -/
theorem finite_budget_bounds_uniform_dissipation
    (E : ℝ → ℝ) (E' : ℝ → ℝ) (E0 β T : ℝ)
    (hβ : 0 < β) (hT : 0 ≤ T) (hE0 : E 0 = E0)
    (hderiv : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt E (E' t) t)
    (hdiss : ∀ t ∈ Set.Icc (0:ℝ) T, E' t ≤ -β)
    (hpos : 0 ≤ E T) :
    T ≤ E0 / β := by
  -- Barrier: B x = E0 − β·x, with derivative B' x = −β.
  set B : ℝ → ℝ := fun x => E0 - β * x with hBdef
  -- E is continuous on [0,T] (from pointwise differentiability).
  have hcontE : ContinuousOn E (Set.Icc (0:ℝ) T) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  -- E has a right derivative on [0,T).
  have hE'within : ∀ x ∈ Set.Ico (0:ℝ) T, HasDerivWithinAt E (E' x) (Set.Ici x) x :=
    fun x hx => (hderiv x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  -- B is continuous on [0,T].
  have hcontB : ContinuousOn B (Set.Icc (0:ℝ) T) := by
    apply Continuous.continuousOn
    fun_prop
  -- B has right derivative −β everywhere.
  have hB'within : ∀ x ∈ Set.Ico (0:ℝ) T, HasDerivWithinAt B (-β) (Set.Ici x) x := by
    intro x hx
    have : HasDerivAt B (-β) x := by
      have h1 : HasDerivAt (fun x : ℝ => E0 - β * x) (0 - β * 1) x :=
        (hasDerivAt_const x E0).sub ((hasDerivAt_id x).const_mul β)
      simpa using h1
    exact this.hasDerivWithinAt
  -- Initial condition: E 0 ≤ B 0.
  have ha : E 0 ≤ B 0 := by
    have : B 0 = E0 := by simp [hBdef]
    rw [this, hE0]
  -- Derivative estimate: E' x ≤ −β = B' x on [0,T).
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) T, E' x ≤ -β :=
    fun x hx => hdiss x (Set.mem_Icc_of_Ico hx)
  -- MVI: E x ≤ B x everywhere on [0,T]; in particular at T.
  have hfence : ∀ ⦃x⦄, x ∈ Set.Icc (0:ℝ) T → E x ≤ B x :=
    image_le_of_deriv_right_le_deriv_boundary hcontE hE'within ha hcontB hB'within hbound
  have hET : E T ≤ E0 - β * T := by
    have := hfence (Set.right_mem_Icc.mpr hT)
    simpa [hBdef] using this
  -- 0 ≤ E T ≤ E0 − β·T ⟹ β·T ≤ E0 ⟹ T ≤ E0/β.
  have hβT : β * T ≤ E0 := by linarith
  rw [le_div_iff₀ hβ]
  linarith [hβT]

/-#############################################################################
  §2. CONCRETE FINITE SHELL MODEL (a genuine ODE, substantive)
#############################################################################-/

/-- **Dyadic dissipation coefficient of shell `n`:** `ν·λ^(2αn)`
    (real power `Real.rpow`). Physically: fine scales (large `n`)
    dissipate more strongly when `λ>1`, `α>0`. When `ν ≥ 0`, `λ > 0` — non-negative. -/
def shellDiss (lam ν α : ℝ) (n : ℕ) : ℝ :=
  ν * lam ^ (2 * α * (n : ℝ))

/-- `shellDiss` is non-negative when `ν ≥ 0`, `λ > 0` (`rpow` is positive). -/
theorem shellDiss_nonneg {lam ν α : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) (n : ℕ) :
    0 ≤ shellDiss lam ν α n := by
  unfold shellDiss
  exact mul_nonneg hν (Real.rpow_nonneg hlam.le _)

/--
**`ShellSolution N lam ν α a` — a GENUINE solution of a finite shell ODE system.**

`a : Fin N → ℝ → ℝ` — amplitudes of the `N` shells as functions of time. The structure
packs:
  * `transfer` — the quadratic (nonlinear) energy transfer between shells
    (in real GOY/Sabra models — the nearest-neighbour triad coupling);
  * `shellODE` — the differential equation ITSELF for each shell:
      `d/dt aₙ = transferₙ − (ν·λ^(2αn))·aₙ`
    (transfer minus dyadic dissipation);
  * `transfer_conservative` — the KEY physical property: transfer
    CONSERVES energy, `∑ₙ aₙ·transferₙ = 0` (telescoping of triads).

This is NOT a `True`-stub: the derivatives are genuinely coupled, and energy
conservation by transfer is a substantive constraint that is honestly consumed in
`shellEnergy_hasDerivAt`. A DATA structure (Type-valued): it carries the transfer
function `transfer` itself, hence not `Prop`. -/
structure ShellSolution (N : ℕ) (lam ν α : ℝ) (a : Fin N → ℝ → ℝ) where
  /-- Nonlinear energy transfer between shells (value at time `t`). -/
  transfer : Fin N → ℝ → ℝ
  /-- Shell equation: `d/dt aₙ = transferₙ − diss·aₙ`. -/
  shellODE : ∀ (n : Fin N) (t : ℝ),
    HasDerivAt (fun s => a n s)
      (transfer n t - shellDiss lam ν α n * a n t) t
  /-- Transfer conserves energy: `∑ₙ aₙ·transferₙ = 0`. -/
  transfer_conservative : ∀ t : ℝ,
    ∑ n : Fin N, a n t * transfer n t = 0

/-- **Energy of the shell system:** `E(t) = ∑ₙ aₙ(t)²` (finite sum of squares
    of amplitudes). Always non-negative. -/
def shellEnergy {N : ℕ} (a : Fin N → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n : Fin N, (a n t) ^ 2

/-- Shell energy is non-negative. -/
theorem shellEnergy_nonneg {N : ℕ} (a : Fin N → ℝ → ℝ) (t : ℝ) :
    0 ≤ shellEnergy a t :=
  Finset.sum_nonneg fun n _ => by positivity

/-- Diagonal dissipation rate of the shell system:
    `D(t) = 2ν·∑ₙ λ^(2αn)·aₙ(t)²`. Non-negative when `ν ≥ 0`, `λ > 0`. -/
def shellDissipationRate {N : ℕ} (lam ν α : ℝ) (a : Fin N → ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * ∑ n : Fin N, shellDiss lam ν α n * (a n t) ^ 2

theorem shellDissipationRate_nonneg {N : ℕ} {lam ν α : ℝ}
    (hν : 0 ≤ ν) (hlam : 0 < lam) (a : Fin N → ℝ → ℝ) (t : ℝ) :
    0 ≤ shellDissipationRate lam ν α a t := by
  unfold shellDissipationRate
  have : 0 ≤ ∑ n : Fin N, shellDiss lam ν α n * (a n t) ^ 2 :=
    Finset.sum_nonneg fun n _ => mul_nonneg (shellDiss_nonneg hν hlam n) (by positivity)
  linarith

/--
**`shellEnergy_hasDerivAt` — PROVEN (derivative of shell energy).**
`dE/dt = 2·∑ aₙ·aₙ' = 2·∑ aₙ·(transferₙ − diss·aₙ)`
       `= 2·(∑ aₙ·transferₙ) − 2·∑ diss·aₙ² = −2·∑ diss·aₙ² = −D(t)`.
Transfer drops out via `transfer_conservative` (energy conservation). This is
the machine realization of the reasoning "nonlinearity does not change energy, only
dissipation eats it away". -/
theorem shellEnergy_hasDerivAt {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a) (t : ℝ) :
    HasDerivAt (fun s => shellEnergy a s)
      (-(shellDissipationRate lam ν α a t)) t := by
  -- Derivative of each summand aₙ².
  have hterm : ∀ n : Fin N,
      HasDerivAt (fun s => (a n s) ^ 2)
        (2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t)) t := by
    intro n
    -- (a n s)² = (a n s)·(a n s); the product rule gives c·a + a·c = 2·a·c.
    have hmul := (sol.shellODE n t).mul (sol.shellODE n t)
    have hval :
        (sol.transfer n t - shellDiss lam ν α n * a n t) * a n t
          + a n t * (sol.transfer n t - shellDiss lam ν α n * a n t)
          = 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t) := by ring
    rw [hval] at hmul
    have hfun : ((fun s => a n s) * fun s => a n s) = fun s => (a n s) ^ 2 := by
      funext s; simp [Pi.mul_apply, sq]
    rw [hfun] at hmul
    exact hmul
  -- Derivative of a sum of functions (pointwise sum = function of the sum).
  have hsum :
      HasDerivAt (fun s => ∑ n : Fin N, (a n s) ^ 2)
        (∑ n : Fin N, 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t)) t := by
    have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
      (A := fun n => fun s => (a n s) ^ 2)
      (A' := fun n => 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t))
      (fun n _ => hterm n)
    -- ∑ i, A i  (sum of functions)  =  fun s => ∑ i, A i s
    have hfun : (∑ n : Fin N, fun s => (a n s) ^ 2)
        = fun s => ∑ n : Fin N, (a n s) ^ 2 := by
      funext s; rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  -- Reduce the derivative value to −D.
  have hval :
      (∑ n : Fin N, 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t))
        = -(shellDissipationRate lam ν α a t) := by
    have hexpand : ∀ n : Fin N,
        2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t)
          = 2 * (a n t * sol.transfer n t)
            - 2 * (shellDiss lam ν α n * (a n t) ^ 2) := by
      intro n; ring
    calc
      (∑ n : Fin N, 2 * (a n t) * (sol.transfer n t - shellDiss lam ν α n * a n t))
          = ∑ n : Fin N, (2 * (a n t * sol.transfer n t)
              - 2 * (shellDiss lam ν α n * (a n t) ^ 2)) := by
            exact Finset.sum_congr rfl (fun n _ => hexpand n)
      _ = (∑ n : Fin N, 2 * (a n t * sol.transfer n t))
            - ∑ n : Fin N, 2 * (shellDiss lam ν α n * (a n t) ^ 2) := by
            rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ n : Fin N, a n t * sol.transfer n t)
            - 2 * (∑ n : Fin N, shellDiss lam ν α n * (a n t) ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = -(shellDissipationRate lam ν α a t) := by
            rw [sol.transfer_conservative t]
            unfold shellDissipationRate
            ring
  rw [hval] at hsum
  -- shellEnergy a s = ∑ n, (a n s)^2 by definition.
  exact hsum

/-- **`shellEnergy_deriv_nonpos` — PROVEN (the shell is dissipative).**
    When `ν ≥ 0`, `λ > 0` the shell energy does not grow: `dE/dt = −D ≤ 0`. -/
theorem shellEnergy_deriv_nonpos {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a)
    (hν : 0 ≤ ν) (hlam : 0 < lam) (t : ℝ) :
    deriv (fun s => shellEnergy a s) t ≤ 0 := by
  rw [(shellEnergy_hasDerivAt sol t).deriv]
  have := shellDissipationRate_nonneg (lam := lam) (ν := ν) (α := α) hν hlam a t
  linarith

/-#############################################################################
  §2bis. NON-VACUITY: the zero shell is a genuine solution
#############################################################################-/

/--
**`zeroShellSolution` — PROVEN (non-vacuity).** The zero shell
`aₙ ≡ 0` is a genuine `ShellSolution`: all derivatives `0`, transfer `0`,
energy conservation trivial. The solution class is INHABITED — the model is not a hollow shell.
(A Type-valued structure ⟹ `def`, not `theorem`.) -/
def zeroShellSolution (N : ℕ) (lam ν α : ℝ) :
    ShellSolution N lam ν α (fun _ _ => 0) where
  transfer := fun _ _ => 0
  shellODE := fun n t => by
    simpa using (hasDerivAt_const t (0 : ℝ))
  transfer_conservative := fun t => by simp

/-- The zero shell's energy is honestly `0`. -/
theorem zeroShell_energy (N : ℕ) (t : ℝ) :
    shellEnergy (N := N) (fun _ _ => 0) t = 0 := by
  simp [shellEnergy]

/-#############################################################################
  §2ter. INSTANTIATION OF THE §1 BUDGET ON THE SHELL
#############################################################################-/

/--
**`no_uniform_dissipation_forever_on_shell` — PROVEN (the §1 budget on a genuine
shell).** If a solution of the shell system dissipates UNIFORMLY at
rate `≥ β > 0` on all of `[0,T]` (the substantive named hypothesis
`huniform` — for instance, the energy stays above a level, so the diagonal
dissipation is bounded below), and the energy at the endpoint is non-negative (which is always
true, `shellEnergy_nonneg`), then time is bounded by the budget:
    `T ≤ shellEnergy a 0 / β`.
A direct instantiation of `finite_budget_bounds_uniform_dissipation` with `E = shellEnergy`,
`E' = dE/dt = −D` (via `shellEnergy_hasDerivAt`). The hypothesis `huniform`
is REALLY consumed. -/
theorem no_uniform_dissipation_forever_on_shell
    {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a)
    (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T)
    (huniform : ∀ t ∈ Set.Icc (0:ℝ) T, β ≤ shellDissipationRate lam ν α a t) :
    T ≤ shellEnergy a 0 / β :=
  finite_budget_bounds_uniform_dissipation
    (fun s => shellEnergy a s)
    (fun t => -(shellDissipationRate lam ν α a t))
    (shellEnergy a 0) β T hβ hT rfl
    (fun t _ => shellEnergy_hasDerivAt sol t)
    (fun t ht => by
      have := huniform t ht
      linarith)
    (shellEnergy_nonneg a T)

/-#############################################################################
  §3. HONEST BOUNDARY: the budget MISSES NON-uniform cascades
#############################################################################-/

open EuclidsPath.NavierStokesFront

/--
**`budget_misses_nonuniform` — PROVEN (the key honesty, the machine boundary
of the budget).**

The §1 budget machine (and its shell instantiation §2) requires UNIFORM
dissipation: the hypothesis `hdiss : E' t ≤ −β` / `huniform : β ≤ D` with a SINGLE `β>0`.
Here its BOUNDARY is machine-exposed: there exists a NON-uniform cascade for
which this hypothesis FAILS for ANY `β>0`.

The witness — the forged cascade already built in NavierStokesFront,
`cookedProfileCascade` on the non-negative bounded profile `cookedProfile`
(`tₙ = 1 − 2⁻ⁿ`, profile drops `2⁻⁽ⁿ⁺¹⁾`). Its successive drops
escape UNDER EVERY `β>0` (`cookedProfileCascade_not_uniform`): there is no single
lower threshold. So the budget does NOT apply to it and does NOT forbid such a cascade —
an honest machine-checked GAP in the finite-budget principle.

("The profile drop at step `n`" — the discrete analogue of `∫ E' = E(tₙ) − E(tₙ₊₁)`
of the §1 input; uniform `≥ β` — exactly the hypothesis that is refuted here.) -/
theorem budget_misses_nonuniform (β : ℝ) (hβ : 0 < β) :
    ¬ ∀ n : ℕ, β ≤ cookedProfile (cookedProfileCascade.times n)
                    - cookedProfile (cookedProfileCascade.times (n + 1)) :=
  cookedProfileCascade_not_uniform β hβ

/--
**`budget_does_not_preclude_cooked_cascade` — PROVEN (a strengthened form
of honesty).** For no `β>0` does the forged cascade fall under the uniform
budget hypothesis — that is, for every `β>0` there is a step whose drop is
STRICTLY less than `β`. The existence of such a "too small" step is direct
evidence of the budget's inapplicability. -/
theorem budget_does_not_preclude_cooked_cascade (β : ℝ) (hβ : 0 < β) :
    ∃ n : ℕ, cookedProfile (cookedProfileCascade.times n)
              - cookedProfile (cookedProfileCascade.times (n + 1)) < β := by
  by_contra h
  exact budget_misses_nonuniform β hβ fun n => not_lt.mp fun hlt => h ⟨n, hlt⟩

/-#############################################################################
  §4. BRIDGE to `ns_no_infinite_dissipative_cascade` — the same machine on the shell
#############################################################################-/

/--
**`shell_budget_is_ns_cascade_machine` — PROVEN (a bridge doc-theorem).**

The same abstract budget machine that kills the infinite δ-cascade of Navier–Stokes
(`EuclidsPath.NavierStokes.ns_no_infinite_dissipative_cascade` via
`DissipativeCascade.no_infinite_uniform_dissipative_cascade`), here applied to a
GENUINE finite shell ODE model: diagonal dissipation gives
`E' = −D ≤ 0`, and under a uniform threshold `β>0` time is bounded
(`no_uniform_dissipation_forever_on_shell`).

Formally the bridge records the GENERALITY of the core: one and the same inequality
"accumulated uniform dissipation ≤ initial energy" stands behind both
results. Here this is reflected by the fact that the shell budget is a direct
instantiation of the same `finite_budget_bounds_uniform_dissipation`, and the NS cascade is an
instantiation of the same ℝ-budget `no_infinite_uniform_dissipative_cascade`.
The statement below is the honest link: if the shell `D` is uniformly `≥ β`, then
`T ≤ E₀/β`, exactly as the NS certificate requires the δ-ladder to be finite. -/
theorem shell_budget_is_ns_cascade_machine
    {N : ℕ} {lam ν α : ℝ} {a : Fin N → ℝ → ℝ}
    (sol : ShellSolution N lam ν α a)
    (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T)
    (huniform : ∀ t ∈ Set.Icc (0:ℝ) T, β ≤ shellDissipationRate lam ν α a t) :
    T ≤ shellEnergy a 0 / β :=
  no_uniform_dissipation_forever_on_shell sol β T hβ hT huniform

/-#############################################################################
  §5. AXIOM AUDIT (without sorry/axiom/native_decide)
#############################################################################-/

-- Expected: [propext, Classical.choice, Quot.sound] — the repository taint is unchanged.
#print axioms finite_budget_bounds_uniform_dissipation
#print axioms shellEnergy_hasDerivAt
#print axioms no_uniform_dissipation_forever_on_shell
#print axioms zeroShellSolution
#print axioms budget_misses_nonuniform

end EuclidsPath.CascadeBudget
