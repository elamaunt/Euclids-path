/-
  SideInfinitude — each side is individually infinite (Dirichlet); aligning both sides —
  that is the entire open core.

  GREEN MODULE: everything below is fully proved (std axioms, no sorry).
  The engine is Dirichlet's theorem on primes in arithmetic progressions from mathlib
  (`Nat.forall_exists_prime_gt_and_modEq`, analytic L-series): each of the two
  sides of center `m` — the minus-side `6m − 1` (class `5 mod 6`) and the plus-side
  `6m + 1` (class `1 mod 6`) — INDIVIDUALLY ranges over infinitely many primes.

  ⚠️ MAIN HONESTY: the singletons are green, but ALIGNING both sides in ONE
  center `m` (both `6m − 1` and `6m + 1` simultaneously prime = twins) — that is THE ENTIRE
  open core of the program. Dirichlet gives two independent infinite columns,
  but says nothing about whether they line up opposite each other infinitely often.
  No pairing is claimed here (marker
  NoPairingClaimed). This module is the backbone of honesty that all
  paired fronts reference.

  WHAT IS PROVED (mathlib Dirichlet, std axioms, no sorry):
    * minusSide_primes_unbounded / plusSide_primes_unbounded — above any `n`
      there exists a prime `p` with `p % 6 = 5` (resp. `p % 6 = 1`);
    * minusSide_center_unbounded / plusSide_center_unbounded — center form:
      above any `n` there exists a center `m` with prime minus-side `6m − 1`
      (resp. plus-side `6m + 1`);
    * minusSide_primes_infinite / plusSide_primes_infinite — the same facts
      in the form `Set.Infinite`.
  Pairing of sides (twins) — NOT here and not derived from anything here.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.SideInfinitude

open EuclidsPath

/-- **MINUS-SIDE UNBOUNDED (proved, Dirichlet):** above any `n` there exists
    a prime `p ≡ 5 (mod 6)` — a prime of the form `6m − 1`. -/
theorem minusSide_primes_unbounded (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ p % 6 = 5 := by
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := 6) (a := 5) (by norm_num) (by decide)
  exact ⟨p, hgt, hp, by simpa [Nat.ModEq] using hmod⟩

/-- **PLUS-SIDE UNBOUNDED (proved, Dirichlet):** above any `n` there exists
    a prime `p ≡ 1 (mod 6)` — a prime of the form `6m + 1`. -/
theorem plusSide_primes_unbounded (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ p % 6 = 1 := by
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := 6) (a := 1) (by norm_num) (by decide)
  exact ⟨p, hgt, hp, by simpa [Nat.ModEq] using hmod⟩

/-- **CENTER FORM, MINUS (proved):** above any `n` there exists a center `m`
    whose minus-side `6m − 1` is prime. Nothing is claimed about the plus-side of THAT SAME `m`
    — that is the whole honesty. -/
theorem minusSide_center_unbounded (n : ℕ) :
    ∃ m, n < m ∧ (6 * m - 1).Prime := by
  obtain ⟨p, hgt, hp, hmod⟩ := minusSide_primes_unbounded (6 * n + 5)
  refine ⟨(p + 1) / 6, by omega, ?_⟩
  have h : 6 * ((p + 1) / 6) - 1 = p := by omega
  rwa [h]

/-- **CENTER FORM, PLUS (proved):** above any `n` there exists a center `m`
    whose plus-side `6m + 1` is prime. Nothing is claimed about the minus-side of THAT SAME `m`
    — that is the whole honesty. -/
theorem plusSide_center_unbounded (n : ℕ) :
    ∃ m, n < m ∧ (6 * m + 1).Prime := by
  obtain ⟨p, hgt, hp, hmod⟩ := plusSide_primes_unbounded (6 * n + 1)
  refine ⟨p / 6, by omega, ?_⟩
  have h : 6 * (p / 6) + 1 = p := by omega
  rwa [h]

/-- **MINUS-SIDE INFINITE (proved):** the set of primes `p ≡ 5 (mod 6)`
    is infinite — `Set.Infinite` form derived from unboundedness above. -/
theorem minusSide_primes_infinite :
    {p : ℕ | p.Prime ∧ p % 6 = 5}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, hp, hmod⟩ := minusSide_primes_unbounded B
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p % 6 = 5} := ⟨hp, hmod⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- **PLUS-SIDE INFINITE (proved):** the set of primes `p ≡ 1 (mod 6)`
    is infinite — `Set.Infinite` form derived from unboundedness above. -/
theorem plusSide_primes_infinite :
    {p : ℕ | p.Prime ∧ p % 6 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, hp, hmod⟩ := plusSide_primes_unbounded B
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p % 6 = 1} := ⟨hp, hmod⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- **HONESTY (scope):** both sides are individually green (Dirichlet, analytic
    mathlib), but ALIGNING both sides in a single center `m` — simultaneous
    primality of `6m − 1` and `6m + 1` — is the twin-prime conjecture, and it is NOT
    claimed here, NOT proved, and not derived from anything here. -/
abbrev NoPairingClaimed : Prop := True

theorem noPairingClaimed : NoPairingClaimed := trivial

#print axioms minusSide_primes_unbounded
#print axioms plusSide_primes_unbounded
#print axioms minusSide_primes_infinite
#print axioms minusSide_center_unbounded

end EuclidsPath.SideInfinitude
