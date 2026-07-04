/-
  ContinuousEngine — the FIRST formal CONTINUOUS-TIME perpetual engine over ℝ
  and an HONEST, machine-checked MAP of where the engine reading carries over to
  the continuum, and where it PRINCIPLY FAILS TO REACH the genuine Navier–Stokes.

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS HERE AND WHAT IS NOT.                                       │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  WHAT THIS MODULE ACHIEVES (green, machine-checked, no sorry/axiom/native_decide):
    • M1 — the FIRST formal CONTINUOUS-TIME perpetual engine. Over ℝ the function
        `H(t) = r^t` (`0 < r < 1`) decays STRICTLY-MULTIPLICATIVELY
        (`H s ≤ r^(s−t)·H t` for `t ≤ s`), while remaining ETERNALLY POSITIVE and never
        terminating at any moment: `continuous_engine_exists`. This is the ℝ-analogue of
        the fact that the discrete impossibility `EPMI.no_infinite_descent` (ℕ FORBIDS infinite
        descent) is FALSE on the continuum: the engine runs forever. What is NEW here is continuous
        time `r^t` over ALL of ℝ via `Real.rpow`; the discrete-index form `(1/2)^n` already
        exists as `DissipativeCascade.real_positive_work_not_wellfounded` (cited,
        not re-derived).
    • M2 — CONVERGENCE ≠ CONTRADICTION. A bounded-below antitone budget
        `H : ℕ → ℝ` CONVERGES (to `⨅ n, H n ≥ 0`), and does NOT yield `False`:
        `boundedBelow_antitone_converges`. The descent CONVERGES, it does not "well-found".
    • M3 — FINITE-TIME SUPERTASK. The scale of the forged cascade
        `NavierStokesFront.cookedProfileCascade` goes TO ZERO (`→ 0`) BEFORE the finite `T=1`:
        `cascade_scale_tendsto_zero`. A completed infinite descent to scale 0 in
        finite time — what ℝ permits but ℕ (`no_infinite_descent`) forbids.
        The witnesses are reused from `NavierStokesFront` (not re-derived).
    • M4 — THE CLAY LINK AS A LINGUISTIC IDENTITY. "The engine runs up to T" ⟺ "BKM vorticity
        control is violated" — this is `Iff.rfl` (`continuousEngine_runs_iff_not_vorticityControl`),
        LOUDLY disclosed as definition-through-definition, WITHOUT new mathematics (a mirror of
        the existing `NavierStokesClay.vorticityBlowup_is_deviation`). Plus — a map of FOUR
        rigorous blowup criteria as CONDITIONAL characterizations (see §M4).
    • M5 — HONEST ENDPOINT. The continuous engine exists UNCONDITIONALLY
        (`continuous_engine_exists_unconditionally`), hence from "∃ engine" (a true
        statement) NOTHING about the open core `GlobalVorticityControl` follows: a true
        premise carries no directional content. The machine-checked
        `NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl` ("the budget
        machine is STRICTLY WEAKER than the open core") is reused.

  WHAT THIS MODULE DOES NOT ACHIEVE (RED LINES — LOUD):
    • This is NOT a solution and NOT a "strike" at the millennium problem. The genuine 3D
      Navier–Stokes is NOT touched by a single step.
    • To prove BLOWUP of the genuine NS (statement C of the Clay formulation) is JUST AS OPEN
      as regularity (A). The abstract engine is DECOUPLED from the NONLINEARITY of NS:
      its forcing input `superlinearDrive` is NAMED and lives ONLY in the discrete
      Katz–Pavlović model (`DyadicBlowup.DyadicSolution.superlinearDrive`), not in the NS
      equations themselves.
    • Tao's SUPERCRITICALITY barrier (Tao, J. Amer. Math. Soc. 29 (2016) 601–674): the averaged
      NS PRESERVES the energy identity yet BLOWS UP ⟹ no purely
      energy/descent argument can SOLVE the genuine NS. This is exactly why the
      engine reading FAILS TO REACH the NS continuum.
    • The open core `NavierStokesClay.GlobalVorticityControl` remains the SOLE 🔴
      barrier, UNTOUCHED. We do NOT forge a proof of independence and do NOT
      invent a `Prop` pretending to solve NS.

  No `sorry`, no new axiom, no `native_decide`; the repository taint
  (propext / Classical.choice / Quot.sound) is unchanged — 45. The red line (the link to
  prime numbers) is untouched.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/ContinuousEngine.lean → zero errors.

  Kinship: EuclidsPath/Engine/EPMI.lean (`no_infinite_descent` — the discrete contrast);
    EuclidsPath/Engine/DissipativeCascade.lean (`real_positive_work_not_wellfounded` — ℝ-(1/2)ⁿ);
    EuclidsPath/Engine/NavierStokesFront.lean (`cookedProfileCascade` — supertask witness);
    EuclidsPath/Engine/NavierStokesClayReduction.lean (`GlobalVorticityControl` — the open core);
    EuclidsPath/Engine/DyadicBlowup.lean (`superlinearDrive` — named forcing + Tao's barrier).
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.DissipativeCascade
import EuclidsPath.Engine.NavierStokesFront
import EuclidsPath.Engine.NavierStokesClayReduction
import EuclidsPath.Engine.DyadicBlowup
import EuclidsPath.Engine.CascadeBudget

set_option autoImplicit false
set_option linter.dupNamespace false

noncomputable section

namespace EuclidsPath.ContinuousEngine

open Filter Topology
open scoped BigOperators

/-!
################################################################################
  M1. GENUINELY-NEW CONTINUOUS-TIME ENGINE (green, small)
################################################################################

The discrete engine `EPMI` is impossible precisely because the heights live in ℕ, and ℕ
is well-founded: any strict `A`-descent drops below 1 in finitely many steps —
a contradiction (`no_infinite_descent`). CONTINUOUS time over ℝ does NOT have
this barrier: `H(t) = r^t` decays strictly-multiplicatively yet remains
ETERNALLY positive. This is exactly the "continuous perpetual engine" — its first
formalization over ALL of ℝ. -/

/-- **Continuous-time perpetual engine.** A "height/energy" function
    `H : ℝ → ℝ` is an engine with decay rate `r` if:
      (i)   `H` is everywhere STRICTLY positive (the engine never stalls);
      (ii)  `0 < r < 1` (a strict decay rate);
      (iii) STRICTLY-MULTIPLICATIVE descent: over an interval `[t,s]` the height drops
            no slower than by a factor `r^(s−t)`, `H s ≤ r^(s−t) · H t` for `t ≤ s`.
    The exponent `s − t` is REAL, hence `Real.rpow` is used. This is
    the continuous-time analogue of the discrete `DescentStep`/`no_perpetual_engine`
    from `EPMI`: there descent is FORBIDDEN (ℕ is well-founded), here it RUNS ETERNALLY. -/
def ContinuousEngine (H : ℝ → ℝ) (r : ℝ) : Prop :=
  (∀ t, 0 < H t) ∧ 0 < r ∧ r < 1 ∧ ∀ t s, t ≤ s → H s ≤ r ^ (s - t) * H t

/-- **🟢 `continuous_engine_exists` — PROVEN (CORE of M1, genuinely new).**
    For every `0 < r < 1` the function `H(t) = r^t` (rpow) is a continuous-time
    perpetual engine with rate `r`. Positivity — `Real.rpow_pos_of_pos`;
    descent — actually an EQUALITY `r^s = r^(s−t) · r^t` (via `Real.rpow_add` after
    `s = (s − t) + t`), so `≤` is taken via `le_of_eq`. This is the ℝ-realization of the fact
    that the discrete `EPMI.no_infinite_descent` over ℕ is FALSE: the engine runs forever. -/
theorem continuous_engine_exists {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ContinuousEngine (fun t => r ^ t) r := by
  refine ⟨fun t => Real.rpow_pos_of_pos hr0 t, hr0, hr1, ?_⟩
  intro t s hts
  -- r^s = r^((s-t)+t) = r^(s-t) * r^t  (equality), hence ≤ via le_of_eq
  have hsplit : s = (s - t) + t := by ring
  have heq : r ^ s = r ^ (s - t) * r ^ t := by
    calc r ^ s = r ^ ((s - t) + t) := by rw [← hsplit]
      _ = r ^ (s - t) * r ^ t := Real.rpow_add hr0 _ _
  exact le_of_eq heq

/-- **🟢 `continuous_engine_exists_unconditionally` — PROVEN (unconditional
    inhabitation).** A continuous-time perpetual engine EXISTS unconditionally —
    take `r = 1/2`, `H(t) = (1/2)^t`. This is a true statement WITHOUT any
    NS hypotheses; it ANCHORS the honest endpoint M5: from the true premise "∃ engine"
    nothing about the open core of NS is derivable. -/
theorem continuous_engine_exists_unconditionally :
    ∃ (H : ℝ → ℝ) (r : ℝ), ContinuousEngine H r :=
  ⟨fun t => (1 / 2 : ℝ) ^ t, 1 / 2,
    continuous_engine_exists (by norm_num) (by norm_num)⟩

/-- **🟢 `discrete_forbids_continuous_realizes` — PROVEN (THE MAIN CONTRAST).**
    An exact juxtaposition of two readings:
      • left  — `EPMI.no_infinite_descent`: over ℕ an infinite `A`-descent (`A ≥ 1`)
        yields `False` — the engine is IMPOSSIBLE (ℕ is well-founded);
      • right — `continuous_engine_exists`: over ℝ `H(t)=r^t` REALIZES an eternal
        strictly-multiplicative descent — the engine RUNS.
    The point: the impossibility of the engine IS the well-foundedness of ℕ, which ℝ lacks.
    The discrete-index (1/2)ⁿ-form already exists as
    `DissipativeCascade.real_positive_work_not_wellfounded` — here the NEW content
    is continuous time `r^t` over all of ℝ. -/
theorem discrete_forbids_continuous_realizes :
    (∀ {A : Nat}, 1 ≤ A → ∀ (H : Nat → Nat),
        (∀ t, EuclidsPath.Engine.DescentStep A (H t) (H (t + 1))) → False)
    ∧ (∀ {r : ℝ}, 0 < r → r < 1 → ContinuousEngine (fun t => r ^ t) r) := by
  refine ⟨?_, ?_⟩
  · intro A hA H hchain
    exact EuclidsPath.Engine.no_infinite_descent hA H hchain
  · intro r hr0 hr1
    exact continuous_engine_exists hr0 hr1

/-- An explicit echo of the existing ℝ-(1/2)ⁿ-form: the discrete-index eternal
    descent over ℝ is already machine-recorded in `DissipativeCascade`. We cite it
    (do NOT re-derive), to emphasize: what is NEW in M1 is CONTINUOUS time `r^t`. -/
theorem cite_discrete_index_real_descent :
    ∃ a : ℕ → ℝ, (∀ n, a (n + 1) < a n) ∧ (∀ n, 0 < a n) ∧
      (∀ n, 0 < a n - a (n + 1)) :=
  EuclidsPath.DissipativeCascade.real_positive_work_not_wellfounded

/-!
################################################################################
  M2. CONVERGENCE ≠ CONTRADICTION (green)
################################################################################

A bounded-below antitone ℝ-budget is NOT obliged to "well-found" and yield `False`.
It CONVERGES. This complements `CascadeBudget.finite_budget_bounds_uniform_dissipation`
(which needs a UNIFORM lower bound β per step) and `budget_misses_nonuniform`:
without uniformity the descent is not finite, but neither is it contradictory — it simply converges. -/

/-- **🟢 `boundedBelow_antitone_converges` — PROVEN (M2).** Every bounded-below
    (`0 ≤ H n`) antitone `H : ℕ → ℝ` CONVERGES to a limit `L ≥ 0`. The limit —
    `⨅ n, H n`; `Tendsto` is given by `tendsto_atTop_ciInf`, and `0 ≤ ⨅` by `le_ciInf`.
    Moral: a decaying energy budget does NOT produce `False`, it HAS a limit; the descent
    CONVERGES rather than well-founding — exactly what the discrete ℕ-engine lacks. -/
theorem boundedBelow_antitone_converges (H : ℕ → ℝ)
    (hanti : Antitone H) (hbdd : ∀ n, 0 ≤ H n) :
    ∃ L, 0 ≤ L ∧ Tendsto H atTop (𝓝 L) := by
  have hBdd : BddBelow (Set.range H) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hbdd n
  refine ⟨⨅ n, H n, ?_, ?_⟩
  · exact le_ciInf (fun n => hbdd n)
  · exact tendsto_atTop_ciInf hanti hBdd

/-!
################################################################################
  M3. FINITE-TIME SUPERTASK (green, reuse)
################################################################################

The forged cascade `NavierStokesFront.cookedProfileCascade` lives at times
`tₙ = 1 − 2⁻ⁿ < T = 1`; its scale (profile) equals `cookedProfile(tₙ) = 2⁻ⁿ`.
Hence the scale goes TO ZERO BEFORE the finite moment `T = 1` — a completed
infinite descent in finite time, which ℝ permits but ℕ
(`EPMI.no_infinite_descent`) forbids. The witnesses are reused. -/

/-- **🟢 `cascade_scale_tendsto_zero` — PROVEN (M3, supertask).** The scale of the
    forged cascade at stages `n` is `cookedProfile (times n) = 2⁻ⁿ` (via
    the existing `cookedProfileCascade_times` + `cookedProfile_at_stage`), and it
    `→ 0` as `n → ∞` (`tendsto_pow_atTop_nhds_zero_of_lt_one`, base `1/2`).
    Since all `times n < 1`, this is a COMPLETED infinite descent to scale 0 BEFORE
    the finite `T = 1` — a supertask. Reuse of `NavierStokesFront`. -/
theorem cascade_scale_tendsto_zero :
    Tendsto
      (fun n => NavierStokesFront.cookedProfile
        (NavierStokesFront.cookedProfileCascade.times n))
      atTop (𝓝 0) := by
  -- at stage n the scale equals (1/2)^n
  have hval : (fun n => NavierStokesFront.cookedProfile
        (NavierStokesFront.cookedProfileCascade.times n))
      = (fun n => (1 / 2 : ℝ) ^ n) := by
    funext n
    rw [NavierStokesFront.cookedProfileCascade_times,
        NavierStokesFront.cookedProfile_at_stage n]
  rw [hval]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- M3 companion: the forged cascade is NOT uniform (the drops `2⁻⁽ⁿ⁺¹⁾` slip below
    any `δ`). We re-export `cookedProfileCascade_not_uniform` — it is precisely
    NON-uniformity that lets the supertask slip past the budget machine (M2
    kills only uniform descents). This is the M2↔M3↔M5 linkage. -/
theorem cascade_scale_not_uniform (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n, δ ≤ NavierStokesFront.cookedProfile
              (NavierStokesFront.cookedProfileCascade.times n)
            - NavierStokesFront.cookedProfile
              (NavierStokesFront.cookedProfileCascade.times (n + 1)) :=
  NavierStokesFront.cookedProfileCascade_not_uniform δ hδ

/-!
################################################################################
  M4. ENGINE ⟺ VORTICITY AS A LINGUISTIC IDENTITY + BLOWUP CRITERIA (green, Prop)
################################################################################

The negation of BKM vorticity control is exactly "the engine runs up to T". We LOUDLY
disclose: the link is definition-through-definition (`Iff.rfl`), NO new
mathematics (a mirror of `NavierStokesClay.vorticityBlowup_is_deviation`). -/

/-- **`ContinuousEngineRuns u T`** — "the continuous engine RUNS up to time
    `T` on the solution `u`": the BKM vorticity quantity is NOT bounded on `[0,T]`, i.e.
    `¬ VorticityTimeIntegrable u T`. This is the engine-branch language for the same
    finite-time singular deviation as in `NavierStokesClay`. -/
def ContinuousEngineRuns (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3)
    (T : ℝ) : Prop :=
  ¬ EuclidsPath.NavierStokesClay.VorticityTimeIntegrable u T

/-- **🟢 `continuousEngine_runs_iff_not_vorticityControl` — PROVEN (`Iff.rfl`).**
    LOUDLY DISCLOSED: "the engine runs up to T" ⟺ "BKM vorticity control is violated" —
    this is definition-through-definition, WITHOUT new mathematical content
    (a mirror of the existing `NavierStokesClay.vorticityBlowup_is_deviation`).
    The Clay link here is a LINGUISTIC IDENTITY, not a bridge-theorem and not an advance on NS. -/
theorem continuousEngine_runs_iff_not_vorticityControl
    (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3) (T : ℝ) :
    ContinuousEngineRuns u T ↔
      ¬ EuclidsPath.NavierStokesClay.VorticityTimeIntegrable u T :=
  Iff.rfl

/-!
### §M4bis. FOUR RIGOROUS BLOWUP CRITERIA AS CONDITIONAL CHARACTERIZATIONS

ATTENTION (LOUD): each of the four below is a GENUINE theorem of the literature, but it is
CONDITIONAL: it characterizes/excludes blowup GIVEN its own premise and does NOT
assert that blowup OCCURS. They all point to the repository BKM surrogate —
`NavierStokesClay.VorticityTimeIntegrable` (a uniform estimate of sup vorticity on [0,T]).

  (1) Beale–Kato–Majda (Comm. Math. Phys. 94 (1984) 61–66):
        blowup at T ⟺ ∫₀ᵀ ‖ω(t)‖_{L^∞} dt = ∞.
      CONDITIONALLY: this is a CONTINUATION criterion, NOT a statement about the presence of blowup.
      Repo surrogate: `VorticityTimeIntegrable` — finiteness of sup vorticity on [0,T].

  (2) Prodi–Serrin–Ladyzhenskaya (regularity):
        u ∈ L^s_t L^r_x with 2/s + 3/r ≤ 1, r > 3  ⟹  the solution is regular.
      CONDITIONALLY: the integrability hypothesis is NOT proven for arbitrary data.

  (3) Escauriaza–Seregin–Šverák (Uspekhi Mat. Nauk 58 (2003); endpoint L^∞_t L^3_x):
        u ∈ L^∞_t L^3_x  ⟹  regularity (the critical endpoint of (2)).
      CONDITIONALLY: the premise is a strong assumption, not a consequence.

  (4) Constantin–Fefferman (Indiana Univ. Math. J. 42 (1993) 775–789):
        Lipschitz continuity of the vorticity DIRECTION ξ = ω/‖ω‖ in a region of intense vorticity
        ⟹  absence of singularity.
      CONDITIONALLY: a geometric condition on the direction, not guaranteed.

We do NOT formalize these four as theorems (they require analytic
infrastructure beyond the module's scope) — we NAME them and honestly mark them as
CONDITIONAL, pointing to `VorticityTimeIntegrable` as the repository BKM surrogate.
None of them ASSERTS that blowup occurs — just like the whole module. -/

/-- **`bkm_surrogate_is_vorticity_integrable` — PROVEN (`Iff.rfl`, labeling).**
    The repository surrogate of the Beale–Kato–Majda criterion is exactly
    `VorticityTimeIntegrable`: the existence of a uniform majorant of sup vorticity on
    `[0,T]`. We fix this identity of definitions (without new content) so that
    all four criteria of §M4bis have a SINGLE repo anchor point. The criterion is CONDITIONAL:
    it asserts NEITHER blowup nor its absence. -/
theorem bkm_surrogate_is_vorticity_integrable
    (u : ℝ → EuclidsPath.NavierStokes.E3 → EuclidsPath.NavierStokes.E3) (T : ℝ) :
    EuclidsPath.NavierStokesClay.VorticityTimeIntegrable u T ↔
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        (⨆ x : EuclidsPath.NavierStokes.E3,
          ‖EuclidsPath.NavierStokesClay.vorticity (u t) x‖) ≤ M :=
  Iff.rfl

/-!
################################################################################
  M5. HONEST ENDPOINT (green witnesses + DISCLOSED doctrine; NO fake)
################################################################################

The machine-checked half of the endpoint — the green witnesses M1–M3 plus
the reuse of `greenBudget_strictly_weaker_than_vorticityControl`. The open
core `GlobalVorticityControl` we do NOT touch and do NOT forge independence. -/

/-- **🟢 `engineBudget_strictly_weaker_than_open_core` — REUSED (M5).**
    A direct reuse of the machine-checked `NavierStokesClay.
    greenBudget_strictly_weaker_than_vorticityControl`: the green engine BUDGET
    machine is STRICTLY WEAKER than the open core. The witness — the same forged
    non-uniform cascade: for any `δ>0` its drops slip away, so the budget
    (which kills only uniform cascades) does NOT prove `GlobalVorticityControl`.
    This is an anti-theorem (a boundary), NOT a bridge. -/
theorem engineBudget_strictly_weaker_than_open_core (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n : ℕ, δ ≤
        NavierStokesFront.cookedProfile
            (NavierStokesFront.cookedProfileCascade.times n)
          - NavierStokesFront.cookedProfile
            (NavierStokesFront.cookedProfileCascade.times (n + 1)) :=
  EuclidsPath.NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl δ hδ

/--
**🟢 `millennium_endpoint_unreachable_by_engine` — PROVEN (the honest CORE of M5).**

This is NOT a proof of independence and NOT a solution of NS — it is an HONEST green anchor.
The conclusion — a CONJUNCTION of three TRUE green facts:
  (a) a continuous perpetual engine exists UNCONDITIONALLY (`∃ H r, ContinuousEngine H r`);
  (b) a bounded-below antitone budget CONVERGES, it does not yield `False` (M2);
  (c) the supertask cascade's scale goes to 0 before the finite T (M3).

LOUDLY AND HONESTLY (see the header and doctrine below): from the TRUE premise "∃ engine"
NOTHING about `GlobalVorticityControl` is derivable — a true premise is logically
INERT relative to the open core (it is neither its cause nor its
consequence). The abstract engine is DECOUPLED from the nonlinearity of NS: the forcing
`superlinearDrive` is NAMED and lives only in the discrete Katz–Pavlović model
(`DyadicBlowup.DyadicSolution.superlinearDrive`). Tao's barrier (JAMS 2016) blocks
any energy/descent argument. The open core remains the SOLE 🔴,
untouched. We do NOT invent a `Prop` pretending to solve NS or prove
independence. -/
theorem millennium_endpoint_unreachable_by_engine :
    (∃ (H : ℝ → ℝ) (r : ℝ), ContinuousEngine H r)
    ∧ (∀ (H : ℕ → ℝ), Antitone H → (∀ n, 0 ≤ H n) →
        ∃ L, 0 ≤ L ∧ Tendsto H atTop (𝓝 L))
    ∧ Tendsto
        (fun n => NavierStokesFront.cookedProfile
          (NavierStokesFront.cookedProfileCascade.times n))
        atTop (𝓝 0) := by
  refine ⟨continuous_engine_exists_unconditionally, ?_, cascade_scale_tendsto_zero⟩
  intro H hanti hbdd
  exact boundedBelow_antitone_converges H hanti hbdd

/-- Explicit evidence that "the forcing is NAMED and locked in the discrete model": the sole
    source of superlinear drive in the repository is the field `superlinearDrive` of the structure
    `DyadicBlowup.DyadicSolution` (the Katz–Pavlović model), NOT the NS equations. We
    cite its type, confirming the decoupling of the abstract engine from the nonlinearity of NS.
    (Inhabitation of `DyadicSolution` would yield `False` — `dyadic_blowup` — so
    the forcing itself is locally realizable but globally blows up, and does NOT carry over to NS.) -/
theorem named_forcing_lives_only_in_discrete_model
    (sol : EuclidsPath.DyadicBlowup.DyadicSolution) :
    ∀ t, 0 ≤ t →
      sol.driveConst * (sol.leadFunctional t) ^ 2 ≤ sol.leadDeriv t :=
  sol.superlinearDrive

/-!
################################################################################
  M6. WHERE THE ENGINE IS IMPOSSIBLE: UNIFORM DRAIN ON FINITE FUEL (green)
################################################################################

M1 showed: the continuous engine `H(t)=r^t` RUNS forever. But NOT EVERY decay is
eternal, and here is the exact demarcation of WHERE the engine is IMPOSSIBLE.

The key (machine-wise): "to decay on finite fuel" by itself does NOT guarantee an endpoint —
`r^t` decays on finite fuel `H 0 = 1` yet is eternally positive (M1), merely
CONVERGING (M2), never reaching zero. What makes the endpoint inevitable is the UNIFORMITY of drain:
if the instantaneous rate `H' ≤ −β` holds with a SINGLE threshold `β > 0`, then from finite
fuel `H 0` the height must cross zero in finite `T ≤ H 0 / β` — eternal
positivity BECOMES IMPOSSIBLE. Hence the engine is impossible exactly in the UNIFORM
regime, and survives solely by NON-uniformity (the drain rate must decay to
zero). The core — a reuse of `CascadeBudget.finite_budget_bounds_uniform_dissipation`.

THE HONEST BOUNDARY (the same one as the whole module's): this is precisely why the engine reading does NOT
reach the genuine NS — the real dissipation is NON-uniform (the forged cascade
`cookedProfileCascade` slips below any `β`, M3/`budget_misses_nonuniform`), that is,
NS sits on the POSSIBLE, non-uniform side of the demarcation, where a finite budget does NOT decide
the outcome (Tao's barrier, JAMS 2016). M6 maps the boundary, it does not close the problem. -/

/-- **🟢 `uniform_drain_forbids_eternal_engine` — PROVEN (M6, the core of the remark).**
    There is NO function `H` that SIMULTANEOUSLY:
      (i)   is eternally strictly positive on `[0,∞)` (the engine does not stall);
      (ii)  is differentiable with derivative `H' t`;
      (iii) decays UNIFORMLY: `H' t ≤ −β` with a SINGLE `β > 0`.
    The reason: uniform drain from finite fuel `H 0` crosses zero in
    `T ≤ H 0 / β` (the budget lemma `finite_budget_bounds_uniform_dissipation`), which at
    `T := H 0 / β + 1` contradicts `0 < H T`. The exact record of the remark "the endpoint
    is INEVITABLE under uniform decay on finite fuel": the engine is impossible
    EXACTLY here. All three hypotheses are genuinely consumed. -/
theorem uniform_drain_forbids_eternal_engine
    (H H' : ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt H (H' t) t)
    (hdrain : ∀ t, 0 ≤ t → H' t ≤ -β)
    (hpos : ∀ t, 0 ≤ t → 0 < H t) :
    False := by
  have hH0 : 0 < H 0 := hpos 0 le_rfl
  set T : ℝ := H 0 / β + 1 with hTdef
  have hT0 : 0 ≤ T := by
    have hpos' : 0 < H 0 / β := div_pos hH0 hβ
    simp only [hTdef]; linarith
  have hbound : T ≤ H 0 / β :=
    CascadeBudget.finite_budget_bounds_uniform_dissipation
      H H' (H 0) β T hβ hT0 rfl
      (fun t ht => hderiv t (Set.mem_Icc.mp ht).1)
      (fun t ht => hdrain t (Set.mem_Icc.mp ht).1)
      (le_of_lt (hpos T hT0))
  simp only [hTdef] at hbound
  linarith

/-- **🟢 `continuous_engine_is_nonuniform` — PROVEN (M6, BY WHAT the engine survives).**
    The engine `H(t)=r^t` (`0<r<1`), being eternally positive (M1), CANNOT drain
    uniformly: there is no single threshold `β>0` and derivative `H'` for which
    `H' ≤ −β` on all of `[0,∞)`. It is precisely NON-uniformity (the drain rate must decay
    to zero) that is BY WHICH the engine evades the inevitable endpoint of the uniform regime.
    A consequence of `uniform_drain_forbids_eternal_engine` + the positivity
    `Real.rpow_pos_of_pos`. (The condition `r<1` is part of the engine specification; the
    non-uniformity itself holds without it, so here it is marked as unused.) -/
theorem continuous_engine_is_nonuniform {r : ℝ} (hr0 : 0 < r) (_hr1 : r < 1) :
    ¬ ∃ (β : ℝ) (H' : ℝ → ℝ), 0 < β ∧
        (∀ t, 0 ≤ t → HasDerivAt (fun s => r ^ s) (H' t) t) ∧
        (∀ t, 0 ≤ t → H' t ≤ -β) := by
  rintro ⟨β, H', hβ, hderiv, hdrain⟩
  exact uniform_drain_forbids_eternal_engine (fun s => r ^ s) H' β hβ hderiv hdrain
    (fun t _ => Real.rpow_pos_of_pos hr0 t)

/-- **🟢 `continuous_engine_dividing_line` — PROVEN (M6, the CROWN of the answer "where impossible").**
    The exact demarcation of the two sides:
      (A) IMPOSSIBLE on the UNIFORM side — no eternally-positive `H` with
          uniform drain `H' ≤ −β` (`β>0`) exists (the endpoint is inevitable within
          `T ≤ H 0/β`);
      (B) POSSIBLE on the NON-uniform side — the engine exists unconditionally
          (`continuous_engine_exists_unconditionally`), and it is the multiplicative
          `r^t`, whose drain rate decays to zero (`continuous_engine_is_nonuniform`).
    The demarcator — the UNIFORMITY of drain: a single threshold `β>0` kills eternity, its
    absence permits it. This is the machine answer to the question "where is the engine impossible". -/
theorem continuous_engine_dividing_line :
    (∀ (H H' : ℝ → ℝ) (β : ℝ), 0 < β →
        (∀ t, 0 ≤ t → HasDerivAt H (H' t) t) →
        (∀ t, 0 ≤ t → H' t ≤ -β) →
        (∀ t, 0 ≤ t → 0 < H t) → False)
    ∧ (∃ (H : ℝ → ℝ) (r : ℝ), ContinuousEngine H r) := by
  refine ⟨?_, continuous_engine_exists_unconditionally⟩
  intro H H' β hβ hderiv hdrain hpos
  exact uniform_drain_forbids_eternal_engine H H' β hβ hderiv hdrain hpos

/-!
################################################################################
  SUMMARY (LOUD HONEST): what is proven, what is reused, what REMAINS OPEN
################################################################################

  🟢 GENUINELY NEW (machine-checked, in this module):
     · `ContinuousEngine` / `continuous_engine_exists` — the FIRST formal
       continuous-time perpetual engine `H(t)=r^t` over all of ℝ (M1);
     · `continuous_engine_exists_unconditionally` — unconditional inhabitation (M5 anchor);
     · `discrete_forbids_continuous_realizes` — the exact contrast ℕ-prohibition ↔ ℝ-realization;
     · `boundedBelow_antitone_converges` — convergence ≠ contradiction (M2);
     · `cascade_scale_tendsto_zero` — supertask: scale → 0 before T (M3, atop the reuse);
     · `ContinuousEngineRuns` / `continuousEngine_runs_iff_not_vorticityControl` —
       the Clay linguistic identity `Iff.rfl` (M4);
     · `millennium_endpoint_unreachable_by_engine` — the honest conjunctive anchor (M5);
     · `uniform_drain_forbids_eternal_engine` — WHERE the engine is IMPOSSIBLE: uniform
       drain on finite fuel forces the endpoint within `T ≤ H0/β` (M6);
     · `continuous_engine_is_nonuniform` — `r^t` survives only by NON-uniformity (M6);
     · `continuous_engine_dividing_line` — the crown: the demarcator is uniformity (M6).

  🟢 REUSED (cited/re-exported, NOT re-derived):
     · `DissipativeCascade.real_positive_work_not_wellfounded` (ℝ-(1/2)ⁿ, M1);
     · `EPMI.no_infinite_descent` (the discrete prohibition, M1 contrast);
     · `NavierStokesFront.cookedProfileCascade` + `cookedProfile_at_stage` (M3);
     · `NavierStokesClay.greenBudget_strictly_weaker_than_vorticityControl` (M5);
     · `NavierStokesClay.VorticityTimeIntegrable` / `vorticity` (M4);
     · `DyadicBlowup.DyadicSolution.superlinearDrive` (M5, named forcing).

  🔴 REMAINS OPEN (UNTOUCHED, the SOLE barrier):
     · `NavierStokesClay.GlobalVorticityControl` — the supercritical a-priori estimate
       of vorticity. This module does NOT prove it, does NOT weaken it, and does NOT bypass it.

  THE MAIN POINT (LOUD): the module does NOT solve and does NOT "strike" the millennium problem. Blowup
  of the genuine NS (C) is just as OPEN as regularity (A). The engine is DECOUPLED from
  the nonlinearity of NS; Tao's barrier (JAMS 2016) blocks the energy/descent route.
  No `sorry`, no new axiom, no `native_decide`; the taint 45
  is unchanged; the red line is untouched. M5 forges NEITHER independence NOR a solution.
-/

#print axioms continuous_engine_exists
#print axioms boundedBelow_antitone_converges
#print axioms cascade_scale_tendsto_zero
#print axioms continuousEngine_runs_iff_not_vorticityControl
#print axioms uniform_drain_forbids_eternal_engine
#print axioms continuous_engine_dividing_line

end EuclidsPath.ContinuousEngine
