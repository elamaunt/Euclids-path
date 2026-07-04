/-
  B_K mechanism (acyclicity). Prose: prose/19_BK.md (after the green Lean).
  Source: new file §VI Lemma 6.1.1 — if 𝒜 ⊆ [1,T] contains no non-trivial equality of K-sums,
  then |𝒜| ≪_K T^{1/K}. Here — the load-bearing CONTRAPOSITION (what Fan-Cycle needs):
  if the number of K-multisets exceeds the number of possible sums, there exists a NON-TRIVIAL
  additive cycle (two distinct K-multisets with equal sum).

  Pure finite combinatorics (pigeonhole). No analysis / distribution / sieve.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

open Finset in
/--
  **B_K (contraposition).** Let `𝒜 ⊆ [1,T]` and suppose the number of K-multisets `|sym K 𝒜|`
  exceeds `K·T` (the number of possible sums). Then there exist two DISTINCT K-multisets from `𝒜`
  with equal sum — a non-trivial additive Euclidean cycle.
-/
theorem exists_additive_cycle {𝒜 : Finset ℕ} {K T : ℕ} (hK : 1 ≤ K)
    (hlb : ∀ a ∈ 𝒜, 1 ≤ a) (hub : ∀ a ∈ 𝒜, a ≤ T)
    (hcard : K * T < (𝒜.sym K).card) :
    ∃ s ∈ 𝒜.sym K, ∃ t ∈ 𝒜.sym K, s ≠ t ∧
      (s : Multiset ℕ).sum = (t : Multiset ℕ).sum := by
  have hmaps : ∀ s ∈ 𝒜.sym K, (s : Multiset ℕ).sum ∈ Finset.Icc K (K * T) := by
    intro s hs
    rw [Finset.mem_sym_iff] at hs
    have hcs : (s : Multiset ℕ).card = K := s.2
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h1 : (s : Multiset ℕ).card • 1 ≤ (s : Multiset ℕ).sum :=
        Multiset.card_nsmul_le_sum (fun x hx => hlb x (hs x hx))
      simpa [hcs] using h1
    · have h2 : (s : Multiset ℕ).sum ≤ (s : Multiset ℕ).card • T :=
        Multiset.sum_le_card_nsmul _ _ (fun x hx => hub x (hs x hx))
      simpa [hcs, smul_eq_mul] using h2
  have hcard_lt : (Finset.Icc K (K * T)).card < (𝒜.sym K).card := by
    rw [Nat.card_Icc]; omega
  obtain ⟨s, hs, t, ht, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hmaps
  exact ⟨s, hs, t, ht, hne, heq⟩

end EuclidsPath.Engine
