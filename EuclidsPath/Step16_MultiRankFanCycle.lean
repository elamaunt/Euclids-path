/-
  Шаг 16 — Multi-rank descent и Universal Fan-Cycle.   Проза: prose/16_MultiRankFanCycle.md
  Источник: twin_prime_new_layers_after_BE_update_ru_2026-06-30.md (§I–§XV).

  Этот файл зависит от mathlib (Finset, арифметические функции). На момент написания
  открытые/исследовательские утверждения оставлены как `sorry` (🟡/🔴 в прозе); строго
  доказанные элементарные кирпичи вынесены в core-модули и УЖЕ проверены компилятором:
    * невозможность двигателя — `EuclidsPath/Engine/EPMI.lean` (без аксиом);
    * shared active gcd = 0 (§3.2) — `EuclidsPath/Engine/Carrier.lean`.

  TODO (формализовать против mathlib):
    * B_K-лемма (Лемма 6.1.1): |𝒜| ≪_K T^{1/K} при отсутствии нетривиальных K-сумм — 🟢 элементарно;
    * exact rank ≤ 4 (§2.1) при X = A^κ, κ < 5 — 🟢 элементарно;
    * Universal Fan-Cycle (Теор. 7.1.1) — 🟡 условно (boundary compression);
    * Multi-Rank Non-Cover (Теор. 10.4.1) — 🔴 условно (proof-local conventions, см. prose/15).
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.Carrier

namespace EuclidsPath.Step16

open scoped BigOperators

/-- Полный ранг стороны: число простых множителей с кратностью, `Ω(n)`. -/
noncomputable def fullRank (n : ℕ) : ℕ := (Nat.factorization n).sum (fun _ k => k)

/--
  **§2.1 Exact rank ≤ 4.** Если все простые делители `n` больше `A` и `n ≤ A^κ` с `κ < 5`
  (здесь — в форме `n < A^5`, `2 ≤ A`), то `Ω(n) ≤ 4`.
  🟢 элементарно. TODO: доказать против mathlib (через `Nat.factorization` и оценку `A^{rank} ≤ n`).
-/
theorem fullRank_le_four {A n : ℕ} (hA : 2 ≤ A) (hn : 0 < n) (hub : n < A ^ 5)
    (hfac : ∀ p ∈ n.primeFactors, A < p) : fullRank n ≤ 4 := by
  -- OPEN/TODO: A^{Ω(n)} ≤ n < A^5 ⇒ Ω(n) < 5 ⇒ Ω(n) ≤ 4
  sorry

/- **§VI Лемма 6.1.1 (B_K-альтернатива).** Если `𝒜 ⊆ [1,T]` не содержит нетривиального равенства
   `K`-сумм (двух различных мультимножеств с одинаковой суммой), то `|𝒜| ≤ C_K · T^{1/K}`.
   🟢 элементарно (число неубывающих `K`-наборов `≥ |𝒜| choose ...`, суммы различны в `[K, K·T]`).
   TODO: формализовать (формализация условия «нет K-суммы» уточняется). -/
-- theorem BK_bound ... := sorry

/- **§VII Теорема 7.1.1 (Universal Fan-Cycle).** Большой Euclidean fan над фиксированным `U` содержит
   bounded additive Euclidean cycle. 🟡 условно (boundary compression набирает carrier-массу). -/
-- theorem universal_fan_cycle ... := sorry   -- conditional, см. prose/16, prose/15

/- **§X Теорема 10.4.1 (Multi-Rank Non-Cover).** При гипотезах §10.4 union non-twin clean rank
   supports не покрывает carrier ⇒ существует twin center. 🔴 условно на proof-local conventions
   (β-sieve вход, path-selection bookkeeping, local bounded-cycle convention). См. prose/15. -/
-- theorem multi_rank_non_cover ... := sorry   -- conditional

end EuclidsPath.Step16
