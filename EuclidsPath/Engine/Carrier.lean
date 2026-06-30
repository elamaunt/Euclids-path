/-
  Carrier — элементарные строго доказуемые факты old-free слоя.
  Самодостаточно: только ядро Lean 4 (без mathlib). Проверка:  lean EuclidsPath/Engine/Carrier.lean

  Здесь формализован §3.2 нового файла (`twin_prime_new_layers_after_BE_update_…`):
  «shared active gcd = 0» — никакой простой p > 2 не делит обе стороны пары (6m-1, 6m+1),
  потому что их разность равна 2.

  Проза: prose/16_MultiRankFanCycle.md (раздел «Exact rank ≤ 4 и необходимые удаления»).
-/
set_option autoImplicit false

namespace EuclidsPath.Engine

/-- Общий делитель сторон `6m+1` и `6m-1` (при `m ≥ 1`) делит их разность `2`. -/
theorem twin_sides_shared_dvd_two {m p : Nat} (hm : 1 ≤ m)
    (hp1 : p ∣ (6 * m + 1)) (hp2 : p ∣ (6 * m - 1)) : p ∣ 2 := by
  have e : 6 * m + 1 = (6 * m - 1) + 2 := by omega
  rw [e] at hp1
  exact (Nat.dvd_add_right hp2).mp hp1

/--
  **§3.2 (shared active gcd = 0).** Ни один простой `p > 2` не может делить обе стороны
  пары близнецов `(6m-1, 6m+1)`. В частности при `p > A ≥ 2` shared-active класс пуст.
-/
theorem no_large_shared_divisor {m p : Nat} (hm : 1 ≤ m) (hp : 2 < p)
    (hp1 : p ∣ (6 * m + 1)) (hp2 : p ∣ (6 * m - 1)) : False := by
  have hd : p ∣ 2 := twin_sides_shared_dvd_two hm hp1 hp2
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

end EuclidsPath.Engine
