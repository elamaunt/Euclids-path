/-
  EngineTower — tower formalisation WITHOUT traversal: inverse-limit via compactness of finite prefixes.
  Source: engine_tower_without_traversal_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "EngineTower without traversal").

  THE KEY SHIFT (correct). Instead of proving that a finite engine TRAVERSES the infinite tower (that is
  the orientation wall = perpetual engine), we argue: NoTwinAbove ⟹ all finite level prefixes ⟹ (compactness)
  EngineTower ⟹ RecurrentCenter ∨ CrossLevelCollision. RecurrentCenter is impossible (center clean on
  unbounded levels), CrossLevelCollision yields Close; both are forbidden under NoEngine/NoTwin.

  PROVED HERE (real arithmetic + honest assembly, std axioms, no sorry):
    * `unboundedClean_forces_side_le_one` — a center clean on UNBOUNDED levels cannot have side
      `≥ 2` (take `B = q`); this is the key non-counting fact;
    * `no_recurrentEngineTower` — a recurrent center is impossible;
    * `engineTower_recurrent_or_escapes` — dichotomy (classical);
    * `no_engineTower_of_crossLevel_collision`, `twin_above_of_engineTower_contradiction` — assembly.

  HONEST BOUNDARY (key, revealed during formalisation — the same trap as HigherTower). The brick
  HOPED that recurrence (center on unbounded levels) is WEAKER than fixed-center clean-forever and
  therefore NOT vacuous. This is NOT so: for a prime divisor `p` of the side, take `B = p`, obtain `A ≥ p`
  with `CleanZ A m`; `p ≤ A` ⟹ cleanness forbids `p ∣ side`. Hence unbounded-clean ALSO forbids ANY
  prime divisor ⟹ side ≤ 1. Therefore `no_recurrentEngineTower` is VACUOUS just like `no_badTower`:
  the contradiction is "recurrent ⟹ side ≤ 1", NOT "recurrent ⟹ twin"; the field `bad` is not used.

  CONCLUSION: the recurrence branch is vacuous and carries no twin content. ALL the route's content lies in the escape/
  CrossLevelCollision branch (named inputs C/D/E of the brick: `hRepeat` = pigeonhole on finite signature, `hSig`
  = recurrence-or-collision, `hCollisionClose` = cross-level labelled-fan-in). By prior audits this is
  the same counting/pigeonhole + labelled-fan-in wall. The compactness bridge also requires finite branching
  = counting. Here C/D/E are named inputs. `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.EngineTower

open EuclidsPath.Residuals

/-! ### §3. Arithmetic: clean on unbounded levels ⟹ side ≤ 1 (the same non-counting fact)

The brick wanted `clean_for_unbounded_A_implies_twin` as a non-vacuous replacement for fixed-center. But the hypothesis
is EQUALLY unsatisfiable: unbounded-clean forbids any prime divisor. -/

/--
  **`unboundedClean_forces_no_prime_divisor` — PROVED.** If `m` is clean on unbounded levels
  (`∀ B, ∃ A ≥ B, CleanZ A m`), then NO prime `q` divides `6m+1`: take `B = q`, obtain `A ≥ q`
  with `CleanZ A m`; `q ≤ A` ⟹ forbidden. Same as fixed-center — recurrence is NOT weaker. -/
theorem unboundedClean_forces_no_prime_divisor {m : ℕ}
    (hUnb : ∀ B, ∃ A, B ≤ A ∧ CleanZ A (m : ℤ)) :
    ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ (6 * (m : ℤ) + 1) := by
  intro q hq hdvd
  obtain ⟨A, hqA, hClean⟩ := hUnb q
  exact hClean q hq hqA (Or.inr hdvd)

/--
  **`unboundedClean_forces_side_le_one` — PROVED (reveals the vacuity of the recurrence branch).** If
  `m` is clean on unbounded levels, then `6m+1 ≤ 1` (side is NOT `≥ 2`): `minFac` would be a forbidden
  prime divisor. Hence recurrence + side ≥ 2 are incompatible — JUST LIKE fixed-center. -/
theorem unboundedClean_forces_side_le_one {m : ℕ}
    (hUnb : ∀ B, ∃ A, B ≤ A ∧ CleanZ A (m : ℤ)) : ¬ (2 ≤ 6 * m + 1) := by
  intro hge
  have hp : (6 * m + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hd : (6 * m + 1).minFac ∣ (6 * m + 1) := Nat.minFac_dvd _
  have hdZ : ((6 * m + 1).minFac : ℤ) ∣ (6 * (m : ℤ) + 1) := by
    have hcast : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by push_cast; ring
    rw [← hcast]; exact_mod_cast hd
  exact unboundedClean_forces_no_prime_divisor hUnb _ hp hdZ

/-! ### §4–6. EngineShadow and EngineTower (moving-center inverse limit)

`EngineShadow A` — the finite shadow of the engine at level `A`, having reached the bad-terminal: center clean at `A`,
sides `≥ 2`, not twin. We abstractly fix ONLY the arithmetic fields (the actual restriction maps are
a project interface, not needed here for the recurrence branch). The center MAY vary between levels. -/

/-- Shadow of the engine at level `A`: center clean at `A`, sides `≥ 2`, not twin. -/
structure EngineShadow (A : ℕ) where
  center : ℕ
  clean : CleanZ A (center : ℤ)
  side_hi : 2 ≤ 6 * center + 1
  bad : ¬ TwinCenterZ center

/-- EngineTower: a shadow at every level (moving-center; compatibility is a project interface,
    the shadows alone suffice for the recurrence branch). -/
structure EngineTower where
  shadow : ∀ A, EngineShadow A

/-! ### §10–11. Recurrence: dichotomy + impossibility of a recurrent center (VACUOUS) -/

/-- Center `m` is recurrent: it repeats on unbounded levels. -/
def CenterRecursUnbounded (T : EngineTower) (m : ℕ) : Prop :=
  ∀ B, ∃ A, B ≤ A ∧ (T.shadow A).center = m

/-- The tower has a recurrent center. -/
def HasRecurrentCenter (T : EngineTower) : Prop := ∃ m, CenterRecursUnbounded T m

/-- The tower "escapes": every center has a bounded level of appearance. -/
def NoRecurrentCenter (T : EngineTower) : Prop :=
  ∀ m, ∃ B, ∀ A, B ≤ A → (T.shadow A).center ≠ m

/-- **`engineTower_recurrent_or_escapes` — PROVED (classical dichotomy).** -/
theorem engineTower_recurrent_or_escapes (T : EngineTower) :
    HasRecurrentCenter T ∨ NoRecurrentCenter T := by
  by_cases h : HasRecurrentCenter T
  · exact Or.inl h
  · refine Or.inr (fun m => ?_)
    by_contra hNoBound
    push_neg at hNoBound
    exact h ⟨m, fun B => hNoBound B⟩

/-- A recurrent center is clean on unbounded levels. -/
theorem recurrent_unboundedClean (T : EngineTower) {m : ℕ}
    (hRec : CenterRecursUnbounded T m) : ∀ B, ∃ A, B ≤ A ∧ CleanZ A (m : ℤ) := by
  intro B
  obtain ⟨A, hBA, hCenter⟩ := hRec B
  exact ⟨A, hBA, hCenter ▸ (T.shadow A).clean⟩

/-- A recurrent center has side `≥ 2`. -/
theorem recurrent_side_hi (T : EngineTower) {m : ℕ}
    (hRec : CenterRecursUnbounded T m) : 2 ≤ 6 * m + 1 := by
  obtain ⟨A, _, hCenter⟩ := hRec 0
  exact hCenter ▸ (T.shadow A).side_hi

/--
  **`no_recurrentEngineTower` — PROVED, but VACUOUSLY (honest remark).** A recurrent center is
  impossible. REASON (degenerate, as in `HigherTower.no_badTower`): recurrence gives clean on
  unbounded levels (`recurrent_unboundedClean`), which forbids the side from being `≥ 2`
  (`unboundedClean_forces_side_le_one`) — against `recurrent_side_hi`. The contradiction is "recurrent ⟹
  side ≤ 1", NOT "recurrent ⟹ twin"; the field `bad` is NOT used. The brick hoped that recurrence
  is weaker than fixed-center — but it is not. Hence the recurrence branch carries no twin content. -/
theorem no_recurrentEngineTower (T : EngineTower) (hHasRec : HasRecurrentCenter T) : False := by
  obtain ⟨m, hRec⟩ := hHasRec
  exact unboundedClean_forces_side_le_one (recurrent_unboundedClean T hRec) (recurrent_side_hi T hRec)

/-! ### §15, §17. Assembly: tower + collision named input ⟹ Close; final theorem

The recurrence branch is closed (vacuously). The escape branch requires NAMED INPUTS C/D/E (cross-level collision) that
the brick itself names: `hRepeat` (∞ levels with the same signature — pigeonhole), `hSig` (recurrence-or-collision),
`hCollisionClose` (collision ⟹ Close = cross-level labelled-fan-in). This is the same counting/labelled-fan-in
wall; here they are named inputs. -/

/-- Abstract `Close` and `CrossLevelCollision` (project type). -/
def CloseAt (Engine : ℕ → Prop) (N : ℕ) : Prop := (∃ A, Engine A) ∨ ∃ t, N < t ∧ TwinCenterZ t

/--
  **`no_engineTower_of_crossLevel_collision` — PROVED (assembly §15).** If the tower always yields
  an infinitely-repeating signature (`hRepeat`), signature ⟹ recurrence ∨ collision (`hSig`), collision ⟹
  Close (`hCollisionClose`), and Close is forbidden (`hNoClose`), then there is no tower. Recurrence is defeated by
  `no_recurrentEngineTower` (vacuously), collision by `hCollisionClose` + `hNoClose`.

  ALL the content lies in `hSig`/`hRepeat`/`hCollisionClose` (named inputs = counting/labelled-fan-in wall). -/
theorem no_engineTower_of_crossLevel_collision {Sig : Type*} {Engine : ℕ → Prop} {N : ℕ}
    {CrossLevelCollision : EngineTower → Prop}
    (hNoClose : ¬ CloseAt Engine N)
    (hRepeat : ∀ T : EngineTower, HasRecurrentCenter T ∨ CrossLevelCollision T)
    (hCollisionClose : ∀ T : EngineTower, CrossLevelCollision T → CloseAt Engine N) :
    ¬ Nonempty EngineTower := by
  rintro ⟨T⟩
  rcases hRepeat T with hRec | hCol
  · exact no_recurrentEngineTower T hRec
  · exact hNoClose (hCollisionClose T hCol)

/--
  **`twin_above_of_engineTower_contradiction` — PROVED (final assembly §17).** Under `¬Engine` and
  `¬(twin above N)`: if NoTwin forces a tower (`hForce`, via prefixes+compactness — named input), and
  the tower is impossible (recurrence is vacuous + collision closes), then `∃ twin > N`.

  HONESTLY: the recurrence branch is vacuous (0 content). The real load is `hForce` (A+B: prefix force +
  compactness, requires finite branching = counting) and the collision named inputs (C/D/E = labelled-fan-in wall).
  There is no traversal/orientation wall here — this is the formal gain; but the counting/collision wall
  remains. -/
theorem twin_above_of_engineTower_contradiction {Engine : ℕ → Prop} {N : ℕ}
    {CrossLevelCollision : EngineTower → Prop}
    (hNoEngine : ¬ ∃ A, Engine A)
    (hForce : ¬ (∃ t, N < t ∧ TwinCenterZ t) → Nonempty EngineTower)
    (hRepeat : ∀ T : EngineTower, HasRecurrentCenter T ∨ CrossLevelCollision T)
    (hCollisionClose : ∀ T : EngineTower, CrossLevelCollision T → CloseAt Engine N) :
    ∃ t, N < t ∧ TwinCenterZ t := by
  by_contra hNoTwin
  have hNoClose : ¬ CloseAt Engine N := by
    rintro (hE | hT)
    · exact hNoEngine hE
    · exact hNoTwin hT
  exact no_engineTower_of_crossLevel_collision (Sig := Unit) hNoClose hRepeat hCollisionClose
    (hForce hNoTwin)

end EuclidsPath.EngineTower
