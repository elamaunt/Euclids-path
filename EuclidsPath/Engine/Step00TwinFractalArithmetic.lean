import EuclidsPath.Engine.Step00GenealogicalOrnament

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Step00 twin-fractal arithmetic — prime-clock survivors in the active window (green §8.1)

The arithmetic core of the fractal induction.  A center `m` is a twin center iff `6m-1` and
`6m+1` are both prime.  Each prime clock `p ≥ 5` forbids two residue phases of `m`; a center that
survives every prime clock up to `z`, and lies in the active window `6m+1 ≤ z²` (so `z` reaches the
square-root certification bound), is a genuine twin.  Note `2` and `3` never divide `6m ± 1`
(`6m ± 1 ≡ ±1 mod 6`), so checking primes `≥ 5` suffices.

This file is GREEN arithmetic: it reuses the committed sieve lemma `safeHole_implies_twin` by
converting the prime-clock survivor condition into `ActiveSieveSafe`.  It proves NOTHING about the
existence of survivors — that (`ShortSurvivor z M0` for every horizon) is exactly the twin lower
bound / parity barrier, left open (see `Step00RelativeCurvatureInstance`).
-/

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace GenealogicalOrnament
namespace Fractal

open EuclidsPath.Residuals

/-- A prime clock `p` forbids the center `m` if it divides either side `6m ± 1`. -/
def ForbiddenPhase (p m : ℕ) : Prop := p ∣ (6 * m - 1) ∨ p ∣ (6 * m + 1)

/-- `m` survives every prime clock `5 ≤ p ≤ z`. -/
def SurvivesUpTo (z m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ≤ z → ¬ ForbiddenPhase p m

/-- The active (triangular) window: `m` is above `M0`, and the clock horizon `z` reaches the
    square-root certification bound (`6m + 1 ≤ z²`). -/
def ActiveWindow (z M0 m : ℕ) : Prop := M0 < m ∧ 6 * m + 1 ≤ z * z

/-- A short survivor: a center in the active window that survives every prime clock `≤ z`. -/
def ShortSurvivor (z M0 : ℕ) : Prop := ∃ m : ℕ, ActiveWindow z M0 m ∧ SurvivesUpTo z m

/-- A prime dividing `6m ± 1` is `≥ 5` (it cannot be `2` or `3`). -/
private theorem five_le_of_prime_dvd_side {q m : ℕ} (hq : q.Prime)
    (hdvd : q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1)) (hm : 1 ≤ m) : 5 ≤ q := by
  have h2 := hq.two_le
  have hne2 : q ≠ 2 := by
    rintro rfl; rcases hdvd with h | h <;> omega
  have hne3 : q ≠ 3 := by
    rintro rfl; rcases hdvd with h | h <;> omega
  have hne4 : q ≠ 4 := by rintro rfl; exact absurd hq (by decide)
  omega

/-- **Green:** surviving every prime clock `≤ z` in the active window (`6m+1 ≤ z²`) gives the
    all-divisor sieve condition `ActiveSieveSafe m`.  Any `k ≤ √(6m+1) ≤ z` has a prime factor
    `q ≤ z` with `q ≥ 5`, which the survivor condition forbids. -/
theorem activeSieveSafe_of_survivesUpTo {z m : ℕ}
    (hm : 1 ≤ m) (hwin : 6 * m + 1 ≤ z * z) (hsurv : SurvivesUpTo z m) :
    ActiveSieveSafe m := by
  have hkz : Nat.sqrt (6 * m + 1) ≤ z := by
    have h := Nat.sqrt_le_sqrt hwin
    rwa [Nat.sqrt_eq] at h
  intro k hk2 hksqrt
  have hkz' : k ≤ z := le_trans hksqrt hkz
  have hk1 : k ≠ 1 := by omega
  have hk0 : 0 < k := by omega
  refine ⟨?_, ?_⟩
  · intro hdvd
    obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
    have hqdvd : q ∣ (6 * m - 1) := hqk.trans hdvd
    have hqz : q ≤ z := le_trans (Nat.le_of_dvd hk0 hqk) hkz'
    have hq5 : 5 ≤ q := five_le_of_prime_dvd_side hq (Or.inl hqdvd) hm
    exact hsurv q hq hq5 hqz (Or.inl hqdvd)
  · intro hdvd
    obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
    have hqdvd : q ∣ (6 * m + 1) := hqk.trans hdvd
    have hqz : q ≤ z := le_trans (Nat.le_of_dvd hk0 hqk) hkz'
    have hq5 : 5 ≤ q := five_le_of_prime_dvd_side hq (Or.inr hqdvd) hm
    exact hsurv q hq hq5 hqz (Or.inr hqdvd)

/-- **Green (the §8.1 arithmetic bridge): a short survivor is a twin center above `M0`.**  This is
    the honest sieve content of the fractal induction; it does NOT assert that a short survivor
    exists (that is the parity barrier). -/
theorem shortSurvivor_implies_twin {z M0 : ℕ} (h : ShortSurvivor z M0) :
    ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  obtain ⟨m, ⟨hM0, hwin⟩, hsurv⟩ := h
  have hm : 1 ≤ m := by omega
  exact ⟨m, hM0, safeHole_implies_twin hm (activeSieveSafe_of_survivesUpTo hm hwin hsurv)⟩

end Fractal
end GenealogicalOrnament
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
