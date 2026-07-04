/-
  Assembly core of Multi-Rank Non-Cover (Wave 6). Prose: prose/22_NonCover.md.

  Here — a VERIFIED non-circular reduction:
  (1) `survivor_of_not_covered` — if the total "bad" class is smaller than the carrier, a survivor exists;
  (2) `infinite_of_unbounded_centers` — infinitely many twin-centers ⟹ twin-prime conjecture.

  This is an honest boundary "up to the conjecture": the logical chain is machine-verified, and what
  remains OPEN is exactly the combinatorial core — that the "bad" ranks do not cover the carrier
  (lower bound on carrier = `CarrierInput`, upper bound on bad — via fan/cycle), and that the
  survivor has rank (1,1). See prose/15, prose/22.

  Everything below is elementary Finset/order combinatorics. No analysis, distribution theory, or sieve.
-/
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath

/--
  **Non-cover ⟹ survivor.** If the size of the "bad" set is less than the size of the carrier `Ω`,
  then there exists an element of `Ω` not belonging to `bad` (a candidate twin-center).
  Pure Finset combinatorics (if `Ω ⊆ bad`, then `|Ω| ≤ |bad|`).
-/
theorem survivor_of_not_covered {Ω bad : Finset ℕ} (hlt : bad.card < Ω.card) :
    ∃ m ∈ Ω, m ∉ bad := by
  by_contra h
  have hsub : Ω ⊆ bad := by
    intro m hm
    by_contra hmb
    exact h ⟨m, hm, hmb⟩
  have := Finset.card_le_card hsub
  omega

/--
  **Bridge to the conjecture.** If twin-centers are unbounded (for every `N` there is a center `m > N`
  with both primes `6m±1`), then there are infinitely many twin primes (`TwinLowers.Infinite`).
-/
theorem infinite_of_unbounded_centers
    (h : ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m) : TwinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨m, hmN, hc⟩ := h N
  refine ⟨6 * m - 1, ?_, ?_⟩
  · refine ⟨hc.1, ?_⟩
    have e : 6 * m - 1 + 2 = 6 * m + 1 := by omega
    rw [e]; exact hc.2
  · omega

end EuclidsPath
