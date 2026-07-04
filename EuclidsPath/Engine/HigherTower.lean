/-
  HigherTower — Euclidean Tower / BadTower: the engine as an inverse limit of compatible finite shadows.
  Source: higher_energy_incompatibility_full_formal_ru_2026-07-01.md (Euclidean Tower / BadTower).
  Prose: prose/24_BoundaryDecomp.md (section «Euclidean Tower»).

  IDEA. It is not a finite engine traveling through ∞ levels; rather, the ENGINE ITSELF is an infinite
  compatible tower of finite shadows: level `A` yields shadow `State A`, restriction `B→A` (A≤B) forgets
  information, and the tower is a compatible choice of `(state A)` with `restrict (state B) = state A`.

  MAIN ARITHMETIC FACT (real, NOT counting, proven). A center `m` that is clean at ALL levels
  (`∀ A, CleanZ A m`) cannot have sides `≥ 2`: clean-forever forbids ANY prime divisor of the sides
  (`allClean_forces_no_prime_divisor` — take `A = q`), yet any number `≥ 2` has a prime divisor
  (`minFac`). This is finiteness of the set of prime divisors, not density.

  HONEST BOUNDARY (key, uncovered during formalisation). It follows that a fixed-center BadTower is
  VACUOUS: fields `clean` (⟹ `∀A CleanZ`) and `side_gt` (sides `≥ 2`) are MUTUALLY CONTRADICTORY,
  so `no_badTower` is proven, but for a DEGENERATE reason — the tower does not exist not because
  «clean-forever ⟹ twin», but because «clean-forever ⟹ side ≤ 1» against `side ≥ 2`. The blueprint
  itself suspected (§16) that fixed-center was «too strong»; here the reason is SHARPER. (The lemma
  «clean-for-all-A ⟹ twin» envisioned by the blueprint is NOT defined in the code — it is formally
  true, but its hypothesis is UNSATISFIABLE for sides `≥ 2`, so «twin» would be derived vacuously;
  we do not introduce it and instead prove the direct cause `allClean_forces_side_le_one`.)

  WHAT REMAINS (§17–19 of the blueprint — NOT proven, likely the same wall): the real hope is a
  moving-center relational tower (`RelTower`), where `center` CHANGES with `A` (`m_A → ∞`), and the
  theorem `relTower_stabilizes_or_forces_twin`. But without stabilisation/cross-level collision, a
  tower of moving centers is again the orientation/carrier wall (descent keeps producing new clean
  non-twin centers). Here the moving part is the INPUT. `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.HigherTower

open EuclidsPath.Residuals

/-! ### §2–3. Main arithmetic fact: clean-forever ⟹ no prime divisor ⟹ side ≤ 1 -/

/--
  **`allClean_forces_no_prime_divisor` — PROVEN.** If `m` is clean at all levels (`∀ A, CleanZ A m`),
  then NO prime `q` divides the side `6m+1`. Mechanism: take level `A = q`; `CleanZ q m`
  forbids `q ∣ (6m±1)`. This is finiteness of prime divisors, not density. -/
theorem allClean_forces_no_prime_divisor {m : ℕ} (hAll : ∀ A, CleanZ A (m : ℤ)) :
    ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ (6 * (m : ℤ) + 1) :=
  fun q hq hdvd => (hAll q) q hq (le_refl q) (Or.inr hdvd)

/-- Same for the side `6m−1`. -/
theorem allClean_forces_no_prime_divisor_minus {m : ℕ} (hAll : ∀ A, CleanZ A (m : ℤ)) :
    ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ (6 * (m : ℤ) - 1) :=
  fun q hq hdvd => (hAll q) q hq (le_refl q) (Or.inl hdvd)

/--
  **`allClean_forces_side_le_one` — PROVEN (reveals the vacuity of the tower).** If `∀ A, CleanZ A m`,
  then the side `6m+1 ≤ 1` (i.e. `6m+1` CANNOT be `≥ 2`). Otherwise `minFac` is a prime divisor,
  which is forbidden. Corollary: the hypothesis «clean at all levels» is INCOMPATIBLE with side `≥ 2`. -/
theorem allClean_forces_side_le_one {m : ℕ} (hAll : ∀ A, CleanZ A (m : ℤ)) :
    ¬ (2 ≤ 6 * m + 1) := by
  intro hge
  have hp : (6 * m + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hd : (6 * m + 1).minFac ∣ (6 * m + 1) := Nat.minFac_dvd _
  have hdZ : ((6 * m + 1).minFac : ℤ) ∣ (6 * (m : ℤ) + 1) := by
    have hcast : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by push_cast; ring
    rw [← hcast]; exact_mod_cast hd
  exact allClean_forces_no_prime_divisor hAll _ hp hdZ

/-! ### §5–6. Abstract level system and tower (inverse limit) -/

/-- Level system: shadow `State A` at each level + restriction `B→A` with the laws of an inverse system. -/
structure LevelSystem where
  State : ℕ → Type
  restrict : ∀ {A B : ℕ}, A ≤ B → State B → State A
  restrict_id : ∀ A (x : State A), restrict (le_refl A) x = x
  restrict_comp : ∀ {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (x : State C),
    restrict hAB (restrict hBC x) = restrict (le_trans hAB hBC) x

/-- Tower: a compatible choice of state at each level (element of the inverse limit). -/
structure Tower (S : LevelSystem) where
  state : ∀ A, S.State A
  compat : ∀ {A B : ℕ} (hAB : A ≤ B), S.restrict hAB (state B) = state A

/-! ### §7–11. Fixed-center BadState and BadTower

`BadState A` — a center clean at level `A`, with sides `≥ 2` and NOT twin. Restriction preserves
the center (and drops the cleanliness level via `CleanZ`-monotonicity). -/

/-- Fixed-center bad-state: clean at level `A`, sides `≥ 2`, not twin. -/
structure BadState (A : ℕ) where
  center : ℕ
  clean : CleanZ A (center : ℤ)
  side_lo : 2 ≤ 6 * center - 1
  side_hi : 2 ≤ 6 * center + 1
  bad : ¬ TwinCenterZ center

/-- `CleanZ` is monotone downward: `A ≤ B`, `CleanZ B m` ⟹ `CleanZ A m` (fewer prohibitions). -/
theorem cleanZ_mono_down {A B : ℕ} {m : ℤ} (hAB : A ≤ B) (hB : CleanZ B m) : CleanZ A m :=
  fun q hq hqA => hB q hq (le_trans hqA hAB)

/-- Restriction for BadState: same center, cleanness at the lower level. -/
def badRestrict {A B : ℕ} (hAB : A ≤ B) (x : BadState B) : BadState A where
  center := x.center
  clean := cleanZ_mono_down hAB x.clean
  side_lo := x.side_lo
  side_hi := x.side_hi
  bad := x.bad

/-- Level system for bad-states (fixed-center). -/
def BadLevelSystem : LevelSystem where
  State := fun A => BadState A
  restrict := fun {A B} hAB x => badRestrict hAB x
  restrict_id := by intro A x; rfl
  restrict_comp := by intro A B C hAB hBC x; rfl

/-- Fixed-center BadTower. -/
def BadTower : Type := Tower BadLevelSystem

/-! ### §12–14. Extracting the fixed center and impossibility of the tower (VACUOUS) -/

/-- **`badTower_center_const` — PROVEN.** In a fixed-center tower the center is constant at all levels
    (`badRestrict` preserves center; compatibility gives equality). -/
theorem badTower_center_const (T : BadTower) : ∀ A, (T.state A).center = (T.state 0).center := by
  intro A
  have hc := T.compat (Nat.zero_le A)
  -- badRestrict preserves center, so (state 0).center = (state A).center
  have hcc : (badRestrict (Nat.zero_le A) (T.state A)).center = (T.state 0).center :=
    congrArg BadState.center hc
  -- badRestrict preserves center: LHS = (state A).center
  simpa [badRestrict] using hcc

/--
  **`badState_inhabited_single_level` — PROVEN (vacuity belongs to the ∞-tower, not to the shadows).**
  At a SINGLE level a bad-state exists: center `4` (side `23` is prime, `25 = 5²` — not twin),
  clean at level `1` trivially (no primes `≤ 1`), sides `≥ 2`. So emptiness is a property of the
  INVERSE LIMIT specifically (compatibility over ALL levels fixes one center «clean forever»), not of
  each finite shadow. This makes the degeneracy of `no_badTower` precise. -/
theorem badState_inhabited_single_level : Nonempty (BadState 1) := by
  refine ⟨{ center := 4, clean := ?_, side_lo := by norm_num, side_hi := by norm_num, bad := ?_ }⟩
  · intro q hq hq1
    interval_cases q <;> simp_all [Nat.Prime]
  · intro htwin
    have := htwin.2
    norm_num [Nat.Prime] at this

/--
  **`no_badTower` — PROVEN, but VACUOUSLY (honest label).** A fixed-center BadTower does not exist.
  REASON (degenerate, uncovered during formalisation): for any tower state `clean : CleanZ A center`
  at ALL levels yields `∀A CleanZ`, which forbids the side from being `≥ 2` (`allClean_forces_side_le_one`)
  — contradicting field `side_hi`. So the contradiction is NOT «clean-forever ⟹ twin» but
  «clean-forever ⟹ side ≤ 1». The `bad` field (not-twin) is not even used. Hence the tower is empty
  for a degenerate reason, and this no-go carries no twin content. -/
theorem no_badTower : ¬ Nonempty (@BadTower) := by
  rintro ⟨T⟩
  -- state 0 clean at level 0; but we need ∀A CleanZ at the shared center
  have hconst := badTower_center_const T
  set m := (T.state 0).center with hm
  have hAll : ∀ A, CleanZ A (m : ℤ) := by
    intro A
    have hcl : CleanZ A ((T.state A).center : ℤ) := (T.state A).clean
    rw [hconst A] at hcl
    exact hcl
  -- side_hi: 2 ≤ 6m+1, but allClean forbids it
  exact allClean_forces_side_le_one hAll (T.state 0).side_hi

/-! ### §15–16. Conditional theorem + HONEST warning about vacuity

The blueprint (§15) gives: if `NoTwinAbove N ⟹ Nonempty BadTower`, then `TwinAbove N`. But since
`BadTower` is empty VACUOUSLY (not because of twin), the force-lemma `NoTwinAbove ⟹ Nonempty BadTower`
requires constructing a state with `∀A CleanZ ∧ side ≥ 2` — which is IMPOSSIBLE. So the force-lemma
is FALSE (not «too strong», but simply wrong), and the conditional theorem, though logically valid,
rests on a false premise. -/

/--
  **`twinAbove_of_badTower_forcing` — PROVEN, but a DEAD CONDITIONAL (premise unreachable).** If `¬TwinAbove N`
  entails non-emptiness of a fixed-center BadTower, then `TwinAbove N`. Logically valid (`no_badTower`),
  BUT the premise `hForce` is UNREACHABLE: `Nonempty BadTower` is always false (vacuously), and deriving
  false from `¬TwinAbove` means proving `TwinAbove` directly. This is NOT a path forward. -/
theorem twinAbove_of_badTower_forcing {N : ℕ}
    (hForce : (¬ ∃ t, N < t ∧ TwinCenterZ t) → Nonempty (@BadTower)) :
    ∃ t, N < t ∧ TwinCenterZ t := by
  by_contra hNo
  exact no_badTower (hForce hNo)

/-! ### §17–19. Moving-center relational tower — the real (unproven) target

To avoid baking in the goal, we weaken the tower: the center CHANGES with the level (`m_A`),
compatibility is a relation, not a function. Then impossibility is NOT automatic: `m_A → ∞` keeps
producing new clean non-twin centers, and without stabilisation/cross-level collision this is again
the orientation/carrier wall. -/

/-- Moving bad-state: same fields, but center may vary between levels. -/
structure MovingBadState (A : ℕ) where
  center : ℕ
  clean : CleanZ A (center : ℤ)
  side_hi : 2 ≤ 6 * center + 1
  bad : ¬ TwinCenterZ center

/-- Relational tower: states at each level + compatibility relation (center not fixed). -/
structure RelTower (Compatible : ∀ {A B : ℕ}, A ≤ B → MovingBadState B → MovingBadState A → Prop) where
  state : ∀ A, MovingBadState A
  compat : ∀ {A B : ℕ} (hAB : A ≤ B), Compatible hAB (state B) (state A)

/--
  **`relTower_contradiction_yields_twin` — PROVEN (conditional wrapper §21).** If `¬TwinAbove N`
  entails a moving-tower, and a moving-tower is impossible, then `TwinAbove N`. BUT `hNoRelTower`
  (impossibility of the moving tower) is `relTower_stabilizes_or_forces_twin`, which is NOT proven
  and, per §19, is likely the same orientation/carrier wall (moving centers `m_A → ∞` yield no
  contradiction without stabilisation). -/
theorem relTower_contradiction_yields_twin {N : ℕ}
    {Compatible : ∀ {A B : ℕ}, A ≤ B → MovingBadState B → MovingBadState A → Prop}
    (hForce : (¬ ∃ t, N < t ∧ TwinCenterZ t) → Nonempty (RelTower @Compatible))
    (hNoRelTower : ¬ Nonempty (RelTower @Compatible)) :
    ∃ t, N < t ∧ TwinCenterZ t := by
  by_contra hNo
  exact hNoRelTower (hForce hNo)

end EuclidsPath.HigherTower
