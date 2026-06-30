/-
  B_K-механизм (ацикличность). Проза: prose/19_BK.md (после зелёного Lean).
  Источник: новый файл §VI Лемма 6.1.1 — если в 𝒜 ⊆ [1,T] нет нетривиального равенства K-сумм,
  то |𝒜| ≪_K T^{1/K}. Здесь — load-bearing КОНТРАПОЗИЦИЯ (то, что нужно Fan-Cycle):
  если число K-мультимножеств превосходит число возможных сумм, существует НЕТРИВИАЛЬНЫЙ
  аддитивный цикл (два разных K-мультимножества с равной суммой).

  Чистая конечная комбинаторика (pigeonhole). Без анализа/распределения/сита.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Engine

open Finset in
/--
  **B_K (контрапозиция).** Пусть `𝒜 ⊆ [1,T]` и число K-мультимножеств `|sym K 𝒜|` больше `K·T`
  (числа возможных сумм). Тогда существуют два РАЗНЫХ K-мультимножества из `𝒜` с равной суммой —
  нетривиальный аддитивный евклидов цикл.
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
