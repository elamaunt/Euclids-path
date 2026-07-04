/-
  DyadicFrontWindow — T-RELATIVE WINDOW OF THE KATZ–PAVLOVICH FRONT INVARIANT (🟢, NO TAINT).

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  LOUD HONEST HEADER — WHAT IS HERE, WHAT IS NOT.                                          │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  CONTEXT. In `DyadicBlowup.lean` (§2ter) the red input of the dyadic branch is named openly:
  `FrontPreservedForever` — preservation of the front domination invariant `FrontDomination`
  on ALL `[0,∞)` for the infinite cascade. This is a research frontier (moving front;
  Barbato–Morandin–Romito 2011, Cheskidov 2008, Kiselev–Zlatoš 2005), and we do NOT prove it.
  Here the red input is HONESTLY NARROWED from three sides, without being closed:

  WHAT IS HERE (all 🟢: standard axiom triple, no sorry/native_decide, NO quarantine):
    • §1 `FrontPreservedUntil T` — the T-RELATIVE TWIN of the red input: preservation of
      `FrontDomination` on the finite window `[0,T)`. Bridge `frontPreservedForever_iff_forall_until`:
      "forever" ⟺ "up to any T". HONESTY: the bridge is a FORMAL CONNECTOR, paid for by pure
      quantifier logic (instantiation `T := t+1`), and NOT by new analysis.
    • §2 HABITABILITY (anti-vacuity witnesses): `ssMode_frontPreservedUntil` — the self-similar
      profile of §2bis satisfies the T-relative form over ALL of its lifetime `[0,T)` with
      FIXED lower bound `m₀ := β_{J+1}/T`. Cost: `ssMode_frontDomination` gives only a
      t-DEPENDENT `m = a_{J+1}(t)`; fixing `m₀` is paid for by the monotonicity of
      `g(t) = (T−t)⁻¹` (`inv_anti₀`) at `0 < T` — this is the CORR-correction of the report
      ("NOT a direct composition", the only genuine work of the unit). CONTRAST
      `ssMode_not_frontPreservedForever`: the same profile with the same `m₀` does NOT satisfy
      `FrontPreservedForever` (at `t = T` the amplitude vanishes under the Lean convention `0⁻¹ = 0`) —
      the gap between "up to T" and "forever" is INHABITED, the forms do NOT coincide.
    • §3 FINITE-WINDOW MVT STEP `frontDomination_persists_on_window`: if the invariant at `t₀`
      holds with a STRICT MARGIN `δ` and the rates of the three front gaps are bounded by `C` on the window,
      then `FrontDomination` holds over all `[t₀, t₀+ε]` at `C·ε ≤ δ`. Cost — the MVT estimate
      from mathlib `norm_image_sub_le_of_norm_deriv_le_segment'` + `HasDerivAt`-bricks of the KP dynamics
      (`DyadicBlowup`). Rate bounds `C` — NAMED LOCAL INPUT (window form
      of the "non-intersection hypothesis" announced in §2ter as a consciously omitted step).
      The stationary witness `frontWindow_realizable` confirms CONSISTENCY of the window hypotheses.

  WHAT IS NOT HERE (RED LINES — LOUD):
    • `FrontPreservedForever` is NOT proved and NOT closed: the T-relative form is STRICTLY WEAKER,
      and the gap is machine-inhabited (`ssMode_not_frontPreservedForever`). The red input REMAINS.
    • The MVT step is NOT iterated here to `[0,∞)`: the margin `δ` and bound `C` are LOCAL; their
      uniform retention under a moving front of an infinite cascade is the ESSENCE of the open
      difficulty. Window iteration is not a formality but the frontier itself; we do NOT claim it is done.
    • This is NOT a Navier–Stokes solution, NOT a finite-energy KP theorem, NOT Gödel.
      The stationary witness of §3 carries TRIVIAL dynamics (all rates zero): it
      witnesses only the consistency of the window hypotheses, and NOT a substantive moving front.

  Compilation: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/DyadicFrontWindow.lean
-/
import Mathlib
import EuclidsPath.Engine.DyadicBlowup

set_option autoImplicit false

noncomputable section

namespace EuclidsPath.DyadicFrontWindow

open EuclidsPath.DyadicBlowup

/-! ### §1. T-relative form of the red input and the bridge to "forever"

`FrontPreservedForever` (DyadicBlowup §2ter) requires the invariant on all `[0,∞)`. Here the same
invariant is placed on a finite window `[0,T)` — this is a NAMED HONEST NARROWING, not a substitution:
the §1 bridge shows that "forever" is exactly equivalent to "up to any T". -/

/-- **T-relative twin of the red input.** Preservation of the front domination invariant
    `FrontDomination` on the finite window `[0,T)` (instead of all `[0,∞)` in `FrontPreservedForever`).
    Unlike the infinite mode, this form is SUBSTANTIVELY INHABITED: the self-similar profile
    `ssMode` satisfies it over all of its lifetime (`ssMode_frontPreservedUntil`),
    and the gap with "forever" is inhabited (`ssMode_not_frontPreservedForever`). -/
def FrontPreservedUntil (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) (T : ℝ) : Prop :=
  ∀ t, 0 ≤ t → t < T → FrontDomination lam d a J ρ κ m t

/-- **Zero window — boundary of the scale (HONEST: vacuous truth).** At `T = 0` the window `[0,0)`
    is empty, and `FrontPreservedUntil` holds for ANY parameters. This is NOT an anti-vacuity
    witness (that is in §2, `ssMode_frontPreservedUntil`), but an honest mark of the lower end of the scale:
    the T-relative form starts from a trivial window and grows in content together with T. -/
theorem frontPreservedUntil_zero (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) :
    FrontPreservedUntil lam d a J ρ κ m 0 :=
  fun _ ht ht0 => absurd ht0 (not_lt.mpr ht)

/-- **Antitonicity in the window.** Preservation up to a larger time implies preservation up to a smaller one:
    windows are nested. Formal connector (quantifier restriction), paid for by `lt_of_lt_of_le`. -/
theorem frontPreservedUntil_mono {lam : ℝ} {d : ℕ → ℝ} {a : ℕ → ℝ → ℝ}
    {J : ℕ} {ρ κ m : ℝ} {T T' : ℝ} (hTT' : T ≤ T')
    (h : FrontPreservedUntil lam d a J ρ κ m T') :
    FrontPreservedUntil lam d a J ρ κ m T :=
  fun t ht htT => h t ht (lt_of_lt_of_le htT hTT')

/-- **BRIDGE: "forever" ⟺ "up to any T".** The red input `FrontPreservedForever` is equivalent to
    the family of all its T-relative twins.
    HONESTY: this is a FORMAL CONNECTOR, paid for by pure quantifier logic (in the reverse direction —
    instantiation `T := t+1`), and NOT by analysis. It does NOT close the red input, but precisely
    localises it: what remains open is exactly UNIFORM IN T retention of the invariant, whereas
    each finite window is the subject of §2 (habitability) and §3 (MVT step). -/
theorem frontPreservedForever_iff_forall_until (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) :
    FrontPreservedForever lam d a J ρ κ m ↔
      ∀ T : ℝ, FrontPreservedUntil lam d a J ρ κ m T := by
  constructor
  · intro h T t ht _
    exact h t ht
  · intro h t ht
    exact h (t + 1) t ht (by linarith)

#print axioms FrontPreservedUntil
#print axioms frontPreservedUntil_zero
#print axioms frontPreservedUntil_mono
#print axioms frontPreservedForever_iff_forall_until

/-! ### §2. Habitability: the self-similar profile lives in the T-relative form and does NOT live in the eternal one

The CORR-correction of the report is carried out verbatim: `ssMode_frontDomination` gives a t-DEPENDENT
`m = a_{J+1}(t)`, while the correct twin `FrontPreservedForever` requires a FIXED `m`.
Fixing `m₀ := β_{J+1}/T` is paid for by the monotonicity of `g(t) = (T−t)⁻¹` on `[0,T)` at `0 < T`. -/

/-- **ANTI-VACUITY WITNESS (🟢): the self-similar profile inhabits the T-relative form.**

The §2bis profile `ssMode` (the very one that REALLY blows up at time `T`) satisfies
`FrontPreservedUntil T` over all of its lifetime `[0,T)` with `ρ = 1`, `κ = 1` and a FIXED
lower bound `m₀ := β_{J+1}/T`. Cost of fixing: `a_{J+1}(t) = β_{J+1}·(T−t)⁻¹`, and
`(T−t)⁻¹ ≥ T⁻¹` on `[0,T)` (`inv_anti₀`), so `m₀ = β_{J+1}·T⁻¹` is an honest lower bound.
This strengthens the non-vacuity of §2ter from POINTWISE (`ssMode_frontDomination` at fixed `t`)
to INTERVAL-WIDE. Preservation beyond the profile's lifetime is NOT claimed — see the contrast below. -/
theorem ssMode_frontPreservedUntil {lam T : ℝ} (hlam : 1 < lam) (hT : 0 < T) (J : ℕ) :
    FrontPreservedUntil lam (fun _ => 0) (ssMode lam T) J 1 1 (ssBeta lam (J+1) / T) T := by
  intro t ht htT
  have hb : 0 < ssBeta lam (J+1) := ssBeta_pos hlam (J+1)
  have hm0 : 0 < ssBeta lam (J+1) / T := div_pos hb hT
  -- t-dependent components of the ordering of the three modes — from the pointwise non-vacuity of §2ter.
  obtain ⟨_, _, hρle, hκle, hκ⟩ := ssMode_frontDomination hlam J htT
  -- Fixing the lower bound: `β_{J+1}/T ≤ β_{J+1}·(T−t)⁻¹`, since `(T−t)⁻¹ ≥ T⁻¹` on `[0,T)`.
  have hTt : 0 < T - t := by linarith
  have hinv : T⁻¹ ≤ (T - t)⁻¹ := inv_anti₀ hTt (by linarith)
  have hmle : ssBeta lam (J+1) / T ≤ ssMode lam T (J+1) t := by
    simp only [ssMode, ssG, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hb.le
  exact ⟨hm0, hmle, hρle, hκle, hκ⟩

/-- **CONTRAST (🟢): the same witness does NOT live in "forever" — the gap between forms is inhabited.**

The self-similar profile with the same fixed bound `m₀ = β_{J+1}/T` does NOT satisfy
`FrontPreservedForever`: at time `t = T` the amplitude `a_{J+1}(T) = β_{J+1}·(T−T)⁻¹` vanishes
(Lean convention `0⁻¹ = 0`), and the requirement `m₀ ≤ a_{J+1}(T)` collapses against `m₀ > 0`. Together with
`ssMode_frontPreservedUntil` this MACHINE-CERTIFIES: the T-relative form is STRICTLY weaker than
the red input — their difference is inhabited, and no verbal gluing of "up to T" with "forever"
will pass this pair of theorems. -/
theorem ssMode_not_frontPreservedForever {lam T : ℝ} (hlam : 1 < lam) (hT : 0 < T) (J : ℕ) :
    ¬ FrontPreservedForever lam (fun _ => 0) (ssMode lam T) J 1 1 (ssBeta lam (J+1) / T) := by
  intro h
  obtain ⟨_, hmle, _, _, _⟩ := h T hT.le
  have hzero : ssMode lam T (J+1) T = 0 := by
    simp [ssMode, ssG, sub_self]
  rw [hzero] at hmle
  have hm0 : 0 < ssBeta lam (J+1) / T := div_pos (ssBeta_pos hlam (J+1)) hT
  linarith

#print axioms ssMode_frontPreservedUntil
#print axioms ssMode_not_frontPreservedForever

/-! ### §3. Finite-window MVT step of invariant preservation

In §2ter this step was announced and CONSCIOUSLY OMITTED ("finite-window preservation via
MVT estimates of bounds is possible under the named local non-intersection hypothesis"). Here it is CLOSED:
from a strict margin `δ` at the initial moment and rate bounds `C` on the three front gaps over the window,
the invariant is retained on `[t₀, t₀+ε]` at `C·ε ≤ δ`. The rate bounds are the NAMED
LOCAL INPUT (window form of the "non-intersection hypothesis"); the MVT estimate is supplied by mathlib
(`norm_image_sub_le_of_norm_deriv_le_segment'`), the derivatives come from the KP dynamics. The step is LOCAL:
iteration to `[0,∞)` would require uniform `δ`, `C` under a moving front — that is the
open frontier, which is NOT closed here. -/

/-- **MVT core of the step (🟢): a lower bound with a margin survives the window under a bounded rate.**

If `f` is differentiable on `[t₀, t₀+ε]` with rate bounded by `C` in norm, starts
with margin `c + δ ≤ f(t₀)` and `C·ε ≤ δ`, then `c ≤ f(t)` over the whole window. Cost — the one-sided
MVT estimate from mathlib `norm_image_sub_le_of_norm_deriv_le_segment'`:
`|f(t) − f(t₀)| ≤ C·(t−t₀) ≤ C·ε ≤ δ`, and the margin absorbs the drift. Non-negativity of `C`
follows from the rate bound itself at `t₀` (norm is non-negative). -/
theorem lowerBound_persists_of_deriv_bound
    {f f' : ℝ → ℝ} {t0 ε C δ c : ℝ}
    (hε : 0 < ε) (hCε : C * ε ≤ δ)
    (hf : ∀ x ∈ Set.Icc t0 (t0 + ε), HasDerivWithinAt f (f' x) (Set.Icc t0 (t0 + ε)) x)
    (hbound : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖f' x‖ ≤ C)
    (hinit : c + δ ≤ f t0) :
    ∀ t ∈ Set.Icc t0 (t0 + ε), c ≤ f t := by
  intro t ht
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hbound t0 ⟨le_refl t0, by linarith⟩)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound t ht
  have habs : |f t - f t0| ≤ C * (t - t0) := by
    simpa [Real.norm_eq_abs] using hmvt
  have hup : C * (t - t0) ≤ C * ε :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1, ht.2]) hC0
  have hlow := (abs_le.mp habs).1
  linarith

/-- **FINITE-WINDOW PRESERVATION OF `FrontDomination` (🟢, MVT step of §2ter — closed).**

If at time `t₀` the front domination invariant holds with a STRICT MARGIN `δ` over all three
gaps (`m + δ ≤ a_{J+1}`, `ρ·a_{J+1} + δ ≤ a_J`, `a_{J+2} + δ ≤ κ·a_{J+1}`), the dynamics are the TRUE
KP ODEs (`HasDerivAt`-bricks of `DyadicBlowup`), and the rates of the three gaps are bounded by `C` on the window
(NAMED LOCAL INPUT — the window form of the "non-intersection hypothesis" of §2ter: `‖kpRHS(J+1)‖ ≤ C`,
`‖kpRHS(J) − ρ·kpRHS(J+1)‖ ≤ C`, `‖κ·kpRHS(J+1) − kpRHS(J+2)‖ ≤ C`), then at `C·ε ≤ δ`
the invariant holds over ALL `[t₀, t₀+ε]`.

HONESTY: the step is LOCAL and does NOT close `FrontPreservedForever` — under a moving front of an
infinite cascade, uniform-in-time retention of the margin `δ` and bound `C` is the essence of the
open difficulty (Barbato–Morandin–Romito, Cheskidov, Kiselev–Zlatoš); the dissipation `d` in this
step need not be non-negative — the sign is needed only for the drive derivation (`frontDrive_of_invariant`),
not for window retention. -/
theorem frontDomination_persists_on_window
    (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (J : ℕ) (ρ κ m : ℝ)
    (t0 ε δ C : ℝ)
    (ht0 : 0 ≤ t0) (hε : 0 < ε) (hCε : C * ε ≤ δ)
    (hm : 0 < m) (hκ0 : 0 ≤ κ)
    (dynamics : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s => a n s) (kpRHS lam d a n t) t)
    (hgap1 : m + δ ≤ a (J+1) t0)
    (hgap2 : ρ * a (J+1) t0 + δ ≤ a J t0)
    (hgap3 : a (J+2) t0 + δ ≤ κ * a (J+1) t0)
    (hb1 : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖kpRHS lam d a (J+1) x‖ ≤ C)
    (hb2 : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖kpRHS lam d a J x - ρ * kpRHS lam d a (J+1) x‖ ≤ C)
    (hb3 : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖κ * kpRHS lam d a (J+1) x - kpRHS lam d a (J+2) x‖ ≤ C) :
    ∀ t ∈ Set.Icc t0 (t0 + ε), FrontDomination lam d a J ρ κ m t := by
  -- All window points lie in the dynamics domain `[0,∞)`.
  have hx0 : ∀ x ∈ Set.Icc t0 (t0 + ε), (0:ℝ) ≤ x := fun x hx => le_trans ht0 hx.1
  -- Gap 1: the leading mode stays above the fixed `m`.
  have hpers1 : ∀ t ∈ Set.Icc t0 (t0 + ε), m ≤ a (J+1) t := by
    refine lowerBound_persists_of_deriv_bound
      (f := fun s => a (J+1) s)
      (f' := fun x => kpRHS lam d a (J+1) x)
      (c := m) hε hCε ?_ hb1 hgap1
    intro x hx
    exact (dynamics (J+1) x (hx0 x hx)).hasDerivWithinAt
  -- Gap 2: inflow feed from below (`ρ·a_{J+1} ≤ a_J`).
  have hpers2 : ∀ t ∈ Set.Icc t0 (t0 + ε), (0:ℝ) ≤ a J t - ρ * a (J+1) t := by
    refine lowerBound_persists_of_deriv_bound
      (f := fun s => a J s - ρ * a (J+1) s)
      (f' := fun x => kpRHS lam d a J x - ρ * kpRHS lam d a (J+1) x)
      (c := 0) hε hCε ?_ hb2
      (by show (0:ℝ) + δ ≤ a J t0 - ρ * a (J+1) t0; linarith)
    intro x hx
    exact ((dynamics J x (hx0 x hx)).sub
      ((dynamics (J+1) x (hx0 x hx)).const_mul ρ)).hasDerivWithinAt
  -- Gap 3: outflow control from above (`a_{J+2} ≤ κ·a_{J+1}`).
  have hpers3 : ∀ t ∈ Set.Icc t0 (t0 + ε), (0:ℝ) ≤ κ * a (J+1) t - a (J+2) t := by
    refine lowerBound_persists_of_deriv_bound
      (f := fun s => κ * a (J+1) s - a (J+2) s)
      (f' := fun x => κ * kpRHS lam d a (J+1) x - kpRHS lam d a (J+2) x)
      (c := 0) hε hCε ?_ hb3
      (by show (0:ℝ) + δ ≤ κ * a (J+1) t0 - a (J+2) t0; linarith)
    intro x hx
    exact (((dynamics (J+1) x (hx0 x hx)).const_mul κ).sub
      (dynamics (J+2) x (hx0 x hx))).hasDerivWithinAt
  -- Assembling the invariant from the three retained gaps.
  intro t ht
  refine ⟨hm, hpers1 t ht, ?_, ?_, hκ0⟩
  · have := hpers2 t ht
    linarith
  · have := hpers3 t ht
    linarith

/-- **Corollary: the MVT step from zero produces an inhabitant of the T-relative form.**
The same hypotheses at `t₀ = 0` give `FrontPreservedUntil` on window `ε` — finite-window
preservation and the T-relative twin of §1 connect literally. Formal connector
(repacking the `Icc`-conclusion into `[0,ε)`-form), paid for by `zero_add`. -/
theorem frontPreservedUntil_of_deriv_bound
    (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (J : ℕ) (ρ κ m : ℝ)
    (ε δ C : ℝ)
    (hε : 0 < ε) (hCε : C * ε ≤ δ)
    (hm : 0 < m) (hκ0 : 0 ≤ κ)
    (dynamics : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s => a n s) (kpRHS lam d a n t) t)
    (hgap1 : m + δ ≤ a (J+1) 0)
    (hgap2 : ρ * a (J+1) 0 + δ ≤ a J 0)
    (hgap3 : a (J+2) 0 + δ ≤ κ * a (J+1) 0)
    (hb1 : ∀ x ∈ Set.Ico (0:ℝ) ε, ‖kpRHS lam d a (J+1) x‖ ≤ C)
    (hb2 : ∀ x ∈ Set.Ico (0:ℝ) ε, ‖kpRHS lam d a J x - ρ * kpRHS lam d a (J+1) x‖ ≤ C)
    (hb3 : ∀ x ∈ Set.Ico (0:ℝ) ε, ‖κ * kpRHS lam d a (J+1) x - kpRHS lam d a (J+2) x‖ ≤ C) :
    FrontPreservedUntil lam d a J ρ κ m ε := by
  intro t ht htε
  have hwin := frontDomination_persists_on_window lam d a J ρ κ m 0 ε δ C
    le_rfl hε hCε hm hκ0 dynamics hgap1 hgap2 hgap3
    (fun x hx => hb1 x (by rwa [zero_add] at hx))
    (fun x hx => hb2 x (by rwa [zero_add] at hx))
    (fun x hx => hb3 x (by rwa [zero_add] at hx))
  exact hwin t ⟨ht, by rw [zero_add]; exact le_of_lt htε⟩

/-! #### Non-vacuity of the MVT step: the stationary witness

The window hypotheses are CONSISTENT: the stationary cascade (all amplitudes `≡ 1`, dissipation chosen so that
`kpRHS ≡ 0`) satisfies them with `C = 0`. HONESTY: the witness dynamics are trivial (zero
rates) — it confirms only that the MVT step is not vacuously true, and does NOT model a moving front. -/

/-- Dissipation of the stationary witness: chosen so that `kpRHS 2 steadyD (≡1) n t = 0`
    (shell `n` has inflow `[n=0 ? 0 : 2ⁿ]` and outflow `2ⁿ⁺¹` at unit amplitudes).
    HONESTY: `steadyD n < 0` for all `n` — this is NOT physical dissipation but an ENERGY PUMP,
    compensating the net outflow; window §3 does not require the sign of `d` (see the theorem docstring),
    but a witness with `d ≥ 0` would be more expensive. -/
def steadyD (n : ℕ) : ℝ := (if n = 0 then 0 else (2:ℝ) ^ n) - 2 ^ (n + 1)

/-- The right-hand side of KP on the stationary witness is identically zero. -/
theorem steady_kpRHS_zero (n : ℕ) (t : ℝ) :
    kpRHS 2 steadyD (fun _ _ => (1:ℝ)) n t = 0 := by
  cases n with
  | zero => simp [kpRHS, kpInflow, kpOutflow, steadyD]
  | succ k =>
    simp only [kpRHS, kpInflow, kpOutflow, steadyD, Nat.succ_ne_zero, if_false]
    ring

/-- **Non-vacuity of the MVT step (🟢):** the hypotheses of `frontDomination_persists_on_window` are consistent —
    the stationary witness passes them with `J = 1`, `ρ = 1/2`, `κ = 2`, `m = 1/2`, `δ = 1/4`,
    `C = 0`, `ε = 1`, and the invariant holds over all `[0,1]`. HONESTY: all rates are zero —
    a consistency witness, not a moving front. -/
theorem frontWindow_realizable :
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      FrontDomination 2 steadyD (fun _ _ => (1:ℝ)) 1 (1/2) 2 (1/2) t := by
  have h := frontDomination_persists_on_window 2 steadyD (fun _ _ => (1:ℝ)) 1
    (1/2) 2 (1/2) 0 1 (1/4) 0
    le_rfl one_pos (by norm_num) (by norm_num) (by norm_num)
    (fun n t _ => by
      have hz := steady_kpRHS_zero n t
      rw [hz]
      exact hasDerivAt_const t 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun x _ => by simp [steady_kpRHS_zero])
    (fun x _ => by simp [steady_kpRHS_zero])
    (fun x _ => by simp [steady_kpRHS_zero])
  intro t ht
  exact h t (by simpa using ht)

#print axioms lowerBound_persists_of_deriv_bound
#print axioms steadyD
#print axioms frontDomination_persists_on_window
#print axioms frontPreservedUntil_of_deriv_bound
#print axioms steady_kpRHS_zero
#print axioms frontWindow_realizable

/-! ### §4. Summary and axiom audit

The red input `FrontPreservedForever` is HONESTLY NARROWED but NOT closed: (1) the T-relative twin
`FrontPreservedUntil` is named and connected by a bridge to "forever" (pure quantifier logic);
(2) the twin is inhabited by the blowing-up profile over all of its lifetime with a fixed lower
bound (monotonicity of `g`), and the gap with "forever" is machine-inhabited; (3) the finite-window
MVT step consciously omitted in §2ter is closed by a mathlib estimate under a named local input
(rate bounds on gaps) and is non-vacuous. What remains open is exactly what was the essence of the
difficulty: UNIFORM in time retention of the margin under a moving front of an infinite cascade.
No sorry, no new axioms, no native_decide; quarantine is not imported. -/

end EuclidsPath.DyadicFrontWindow
