/-
  Шаг 16 — Multi-rank descent и Universal Fan-Cycle.   Проза: prose/16_MultiRankFanCycle.md
  Источник: twin_prime_new_layers_after_BE_update_ru_2026-06-30.md (§I–§XV).

  Этот файл зависит от mathlib (Finset, арифметические функции). На момент написания
  открытые/исследовательские утверждения оставлены как `sorry` (🟡/🔴 в прозе); строго
  доказанные элементарные кирпичи вынесены в core-модули и УЖЕ проверены компилятором:
    * невозможность двигателя — `EuclidsPath/Engine/EPMI.lean` (без аксиом);
    * shared active gcd = 0 (§3.2) — `EuclidsPath/Engine/Carrier.lean`.

  Доказано в этом файле (без sorry):
    * exact rank ≤ 4 (§2.1): `fullRank_le_four` — 🟢 строго, проверено компилятором.

  TODO (формализовать против mathlib):
    * B_K-лемма (Лемма 6.1.1): |𝒜| ≪_K T^{1/K} при отсутствии нетривиальных K-сумм — 🟢 элементарно;
    * Universal Fan-Cycle (Теор. 7.1.1) — 🟡 условно (boundary compression);
    * Multi-Rank Non-Cover (Теор. 10.4.1) — 🔴 условно (proof-local conventions, см. prose/15).
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.Carrier

namespace EuclidsPath.Step16

open scoped BigOperators

/-- Полный ранг стороны: число простых множителей с кратностью, `Ω(n) = |primeFactorsList n|`. -/
def fullRank (n : ℕ) : ℕ := n.primeFactorsList.length

/-- Вспомогательная: если все элементы списка ≥ `c`, то `c^|L| ≤ ∏ L`. -/
private theorem pow_length_le_prod {c : ℕ} :
    ∀ L : List ℕ, (∀ x ∈ L, c ≤ x) → c ^ L.length ≤ L.prod
  | [], _ => by simp
  | a :: t, h => by
      have ha : c ≤ a := h a (List.mem_cons.mpr (Or.inl rfl))
      have ht : ∀ x ∈ t, c ≤ x := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      have ih := pow_length_le_prod t ht
      calc c ^ (a :: t).length = c ^ t.length * c := by rw [List.length_cons, pow_succ]
        _ ≤ t.prod * a := Nat.mul_le_mul ih ha
        _ = (a :: t).prod := by rw [List.prod_cons]; exact Nat.mul_comm t.prod a

/--
  **§2.1 Exact rank ≤ 4.** Если все простые делители `n` больше `A` (`A ≥ 2`) и `n < A^5`, то `Ω(n) ≤ 4`.
  🟢 строго: `(A+1)^{Ω(n)} ≤ ∏ простых множителей = n < A^5 < (A+1)^5`, значит `Ω(n) < 5`.
-/
theorem fullRank_le_four {A n : ℕ} (hA : 2 ≤ A) (hn : 0 < n) (hub : n < A ^ 5)
    (hfac : ∀ p ∈ n.primeFactors, A < p) : fullRank n ≤ 4 := by
  by_contra hcon
  have hlen : 5 ≤ fullRank n := by omega
  have hge : ∀ x ∈ n.primeFactorsList, A + 1 ≤ x := by
    intro x hx
    have hxp : x ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨Nat.prime_of_mem_primeFactorsList hx, Nat.dvd_of_mem_primeFactorsList hx, hn.ne'⟩
    have hlt := hfac x hxp
    omega
  have hpow : (A + 1) ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
    pow_length_le_prod _ hge
  rw [Nat.prod_primeFactorsList hn.ne'] at hpow
  have hpow' : (A + 1) ^ fullRank n ≤ n := hpow
  have h1 : (A + 1) ^ 5 ≤ (A + 1) ^ fullRank n := Nat.pow_le_pow_right (by omega) hlen
  have h3 : A ^ 5 < (A + 1) ^ 5 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  exact absurd (lt_of_le_of_lt (le_trans h1 hpow') (lt_trans hub h3)) (lt_irrefl _)

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
