/-
  Step00 closure attempt — assembling the concrete graph over centers.
  Goal: build a HeightGraph over ℕ-centers, prove Regenerates in full, and attempt to close
  `Step00.twin_prime_conjecture`.

  Architectural check (honest): `reaches_twin` descends the height ⟹ the found twin is BELOW the start.
  For infinitude we need a twin ABOVE every N. This gap is exposed explicitly here.

  VERDICT (3 independent audits + numerics, tools/RESULTS_descent_gap.md): ASSEMBLY DOES NOT CLOSE.
  The carrier hole is `sink-is-clean`: `Twin` here = `TwinCenterZ` WITHOUT the conjunct `CleanZ`, and `Step` is
  abstract `t'<t` with no clean-ness certificate and no `<A²`. Therefore `clean_twin_above` is NOT
  applicable to the sink (the precondition "sink clean" is absent), and the descent may terminate at a SMALL twin ≤ M₀
  (counterexample: center 166698 → 18 → sides (107,109), not clean at A=200; in the limit m=1 ↔ (5,7)).
  This is compatible with "M₀ is the last twin" ⟹ NO contradiction. The missing link is the invariant
  "Step preserves CleanZ A along the descent" — which in complexity equals the conjecture itself. `Step00` is NOT closed.
-/
import Mathlib
import EuclidsPath.Engine.RigidClose
import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.Regeneration

set_option autoImplicit false

namespace EuclidsPath.Step00Close

open EuclidsPath.RigidClose EuclidsPath.Residuals EuclidsPath.Regeneration

/--
  **State:** center `t` with side sign `η` (direction of the current old-peel/active step).
  Height = center. -/
structure CState where
  t : ℕ
  η : ℤ

/--
  **Descent graph over centers.** `Twin` = twin center; `Step` = transition to a strictly smaller center
  `t' < t` (old-peel/active via `cofactor_is_center`). Height = center `t`. -/
def descentGraph : HeightGraph CState where
  height := fun s => s.t
  Twin := fun s => TwinCenterZ s.t
  Step := fun s s' => s'.t < s.t   -- abstract "descent to a smaller center" (the concrete edge is built by cofactor)
  step_drops := fun {s s'} h => h

/--
  **Regenerates for descentGraph — HONEST check.** A non-twin center must have a descending
  successor. From the dichotomy (`regeneration_dichotomy`) + `cofactor_is_center` we can build
  a smaller center WHEN the side has a divisor `q ≥ 5`. But `Step` here is `s'.t < s.t`, and to
  supply it we need a CONCRETE smaller center `t' < t`.

  Subtlety: for `t = 0` or small `t` the divisor/cofactor may fail to give `t' < t` strictly. Therefore
  `Regenerates descentGraph` in pure form is NOT universal — a lower bound (carrier scale) is required.
  That is precisely the remaining input. -/
theorem regenerates_iff_has_smaller (hbuild : ∀ s : CState, ¬ TwinCenterZ s.t → ∃ t' : ℕ, t' < s.t) :
    Regenerates descentGraph := by
  intro s hs
  obtain ⟨t', ht'⟩ := hbuild s hs
  exact ⟨⟨t', 1⟩, ht'⟩

/--
  **Architectural gap (exposed explicitly).** `reaches_twin descentGraph` yields a twin AT SOME height
  `≤ height(start)` — i.e., a twin BELOW the start. For infinitude (twin above every `N`) a downward
  descent is insufficient: one must either (a) start high enough and show the twin sink is still
  `> N`, or (b) change direction (upward search). This is a REAL open point of the assembly.
-/
theorem reaches_some_twin (hregen : Regenerates descentGraph) (s₀ : CState) :
    ∃ s : CState, TwinCenterZ s.t :=
  reaches_twin descentGraph hregen s₀

end EuclidsPath.Step00Close
