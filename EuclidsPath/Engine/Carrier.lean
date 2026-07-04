/-
  Carrier — elementary strictly provable facts of the old-free layer.
  Self-contained: only Lean 4 core (no mathlib). Check:  lean EuclidsPath/Engine/Carrier.lean

  Formalises §3.2 of the new file (`twin_prime_new_layers_after_BE_update_…`):
  «shared active gcd = 0» — no prime p > 2 divides both sides of the pair (6m-1, 6m+1),
  because their difference equals 2.

  Prose: prose/16_MultiRankFanCycle.md (section «Exact rank ≤ 4 and necessary removals»).
-/
set_option autoImplicit false

namespace EuclidsPath.Engine

/-- Any common divisor of the sides `6m+1` and `6m-1` (for `m ≥ 1`) divides their difference `2`. -/
theorem twin_sides_shared_dvd_two {m p : Nat} (hm : 1 ≤ m)
    (hp1 : p ∣ (6 * m + 1)) (hp2 : p ∣ (6 * m - 1)) : p ∣ 2 := by
  have e : 6 * m + 1 = (6 * m - 1) + 2 := by omega
  rw [e] at hp1
  exact (Nat.dvd_add_right hp2).mp hp1

/--
  **§3.2 (shared active gcd = 0).** No prime `p > 2` can divide both sides
  of the twin pair `(6m-1, 6m+1)`. In particular, for `p > A ≥ 2` the shared-active class is empty.
-/
theorem no_large_shared_divisor {m p : Nat} (hm : 1 ≤ m) (hp : 2 < p)
    (hp1 : p ∣ (6 * m + 1)) (hp2 : p ∣ (6 * m - 1)) : False := by
  have hd : p ∣ 2 := twin_sides_shared_dvd_two hm hp1 hp2
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

end EuclidsPath.Engine
