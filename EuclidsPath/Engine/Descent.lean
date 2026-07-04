/-
  Descent and the "two-carry" (boundary-law).
  Prose: prose/18_Descent.md (after the green Lean).

  Author's idea: the descent branch "pays by carrying the two forward". Concretely: in a
  clean-descent, the side `6m−1 = a·U` loses the active factor `a>A`, leaving `U = b·v`
  (b,v>A primes), with `U = 6m'+ε`. The opposite side of the descended centre equals
  `U − 2ε` — that is the "carried two". A small old prime `p≤A` CANNOT divide `U`
  (its factors are > A), so the only obstruction (exit from the clean-core, boundary-exit ⊥)
  is divisibility `p ∣ (U − 2ε)`. The impossibility of an infinite such carry is EPMI
  (Engine/EPMI).

  Everything is elementary (divisibility + ring). Nothing forbidden (analysis/distribution/sieve).
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

/-- The opposite side of the descended centre: `6m'−ε = U − 2ε`, given `U = 6m'+ε`. "Two forward". -/
theorem two_carry_opposite {m' U ε : ℤ} (hU : U = 6 * m' + ε) :
    6 * m' - ε = U - 2 * ε := by
  linear_combination -hU

/-- A small prime `p ≤ A` does not divide the product of two primes larger than `A`. (`U = b·v`, `b,v>A`.) -/
theorem no_small_divisor {A b v p : ℕ} (hb : b.Prime) (hv : v.Prime)
    (hAb : A < b) (hAv : A < v) (hp : p.Prime) (hpA : p ≤ A) : ¬ p ∣ (b * v) := by
  intro hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · have : p = b := (Nat.prime_dvd_prime_iff_eq hp hb).mp h
    omega
  · have : p = v := (Nat.prime_dvd_prime_iff_eq hp hv).mp h
    omega

/--
  **Boundary-law = two-carry.** If `p` does not divide the product-side `U`, then any
  obstruction on the descended centre is divisibility of the opposite side `U − 2ε`
  (= "the carried two"), not a defect of the product-side itself.
-/
theorem obstruction_on_opposite {U twoε sideProd sideOpp p : ℤ}
    (hprod : sideProd = U) (_hopp : sideOpp = U - twoε) (hpU : ¬ p ∣ U) :
    (p ∣ sideProd ∨ p ∣ sideOpp) ↔ p ∣ sideOpp := by
  constructor
  · rintro (h | h)
    · rw [hprod] at h; exact absurd h hpU
    · exact h
  · intro h; exact Or.inr h

end EuclidsPath.Engine
