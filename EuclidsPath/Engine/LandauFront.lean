/-
  LandauFront — arithmetic zoo entry for Landau's 4th problem: primes of the form `n² + 1`.

  GREEN MODULE (in the repository sense): everything below is fully proven
  (std axioms, no sorry). But — as in `PolignacBranch` — the open problem is NOT solved here.
  The Dirichlet engine from mathlib (`SideInfinitude`) supplies primes
  in arithmetic progressions; however `n² + 1` is NOT an arithmetic
  progression but a quadratic form, so the infinitude of primes `n² + 1`
  is NOT covered by Dirichlet and remains an honest 🔴-gate `Landau4thUnbounded`
  (the Hardy–Littlewood heuristic predicts infinitude — a sign FOR, but NOT
  a proof).

  ⚠️ MAIN HONESTY: what is green here is ONLY the structural bridge
  "unboundedness ⟹ infinitude of the set" (a clean repackaging via
  `Set.Infinite`, like `cousinLowersInfinite_of_unbounded` in `PolignacBranch`)
  plus one genuine green fact about residues. No new number theory.
  The infinitude of primes `n² + 1` itself — is OPEN (marker `NoInfinitudeClaimed`).
  Best known (Iwaniec, 1978): infinitely many `n² + 1` with at most two prime
  factors — but this is NOT the infinitude of primes `n² + 1` themselves.

  WHAT IS PROVEN (std axioms, no sorry):
    * landauPrimes_infinite_of_unbounded — structural bridge: 🔴-gate
      `Landau4thUnbounded` ⟹ the set `LandauPrimes` is infinite
      (shape `Set.Infinite`, clean repackaging);
    * oddLandauPrime_even_k — green fact about residues: if `k` is odd, then
      `k² + 1` is even, so the only even prime of this form is
      `2` (at `k = 1`); every prime `k² + 1 > 2` requires EVEN `k`.
  The infinitude of primes `n² + 1` — is NOT here and is not derived from anything here.
-/
import Mathlib
set_option autoImplicit false

namespace EuclidsPath.LandauFront

/-- The set of Landau primes `n² + 1`. -/
def LandauPrimes : Set ℕ := {p | ∃ k : ℕ, p = k ^ 2 + 1 ∧ p.Prime}

/-- 🔴 GATE: infinitely many `k` yield a prime `k² + 1` (Hardy–Littlewood;
    Landau's 4th problem). OPEN — not derived from anything here. -/
def Landau4thUnbounded : Prop := ∀ N : ℕ, ∃ k : ℕ, N < k ∧ (k ^ 2 + 1).Prime

/-- 🟢 **STRUCTURAL BRIDGE (proven):** unboundedness ⟹ the set of Landau primes
    is infinite. Clean repackaging via `Set.Infinite`, no new number theory;
    shape analogous to `cousinLowersInfinite_of_unbounded`. -/
theorem landauPrimes_infinite_of_unbounded (H : Landau4thUnbounded) :
    LandauPrimes.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, hgt, hp⟩ := H B
  have hmem : (k ^ 2 + 1) ∈ LandauPrimes := ⟨k, rfl, hp⟩
  have hBlt : B < k ^ 2 + 1 := by nlinarith [hgt]
  exact absurd (hB hmem) (not_le.mpr hBlt)

/-- 🟢 **GREEN FACT ABOUT RESIDUES (proven):** if `k` is odd, then `k² + 1`
    is even, so any prime of this form equals `2`; therefore every prime
    `k² + 1 > 2` requires EVEN `k`. A genuine green fact about the structure of the form,
    with no connection to the open infinitude question. -/
theorem oddLandauPrime_even_k {k : ℕ} (hodd : Odd k) (hp : (k ^ 2 + 1).Prime) :
    k ^ 2 + 1 = 2 := by
  have h2dvd : 2 ∣ k ^ 2 + 1 := by
    obtain ⟨j, hj⟩ := hodd
    refine ⟨2 * j ^ 2 + 2 * j + 1, ?_⟩
    subst hj
    ring
  rcases (hp.eq_one_or_self_of_dvd 2 h2dvd) with h | h
  · omega
  · omega

/-- **HONESTY (coverage):** the infinitude of primes `n² + 1` is NOT
    claimed here, NOT proven, and is not derived from anything here. Dirichlet
    (mathlib, `SideInfinitude`) covers only arithmetic progressions;
    `n² + 1` is a quadratic form, beyond Dirichlet's reach. Landau's 4th problem
    is OPEN; the bridge proven above is conditional (input — 🔴-gate
    `Landau4thUnbounded`) and does not solve the open problem. -/
abbrev NoInfinitudeClaimed : Prop := True

theorem noInfinitudeClaimed : NoInfinitudeClaimed := trivial

#print axioms landauPrimes_infinite_of_unbounded
#print axioms oddLandauPrime_even_k

end EuclidsPath.LandauFront
