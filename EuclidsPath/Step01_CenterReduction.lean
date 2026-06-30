/-
  Шаг 01 — Центровая редукция: форма `6m ± 1`.
  Проза: prose/01_CenterReduction.md

  Содержание (всё доказывается элементарно, без `sorry`):
    * `twin_center_mod_six`  — простое `p>3` из пары близнецов даёт `p % 6 = 5`;
    * `twin_center_dvd_six`  — центр `p+1` делится на 6 (Лемма 1.1);
    * `twin_index_form`      — индексная форма `p = 6m-1`, `p+2 = 6m+1` (Следствие 1.2);
    * `isTwinCenter_of_isTwinPair` — связь `IsTwinPair` (шаг 00) с `IsTwinCenter`.

  Статус: 🟢 строго. NB: проект ещё не компилировался (Lean не установлен) — тактики
  (`omega`, имена лемм mathlib) подлежат проверке при первой сборке. См. lakefile.toml.
-/
import EuclidsPath.Step00_Overview

namespace EuclidsPath

/-- Простое `p > 3`, для которого `p+2` тоже простое, удовлетворяет `p ≡ 5 (mod 6)`. -/
theorem twin_center_mod_six {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime) (h : 3 < p) :
    p % 6 = 5 := by
  -- p не делится на 2 (иначе делитель 2 примарного p даёт 2 = 1 или 2 = p)
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 2 hd with h' | h' <;> omega
  -- p не делится на 3
  have h3 : ¬ (3 ∣ p) := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 3 hd with h' | h' <;> omega
  -- p+2 не делится на 3 (иначе при p ≡ 1 (mod 6) число p+2 было бы кратно 3)
  have h3' : ¬ (3 ∣ (p + 2)) := by
    intro hd
    rcases hp2.eq_one_or_self_of_dvd 3 hd with h' | h' <;> omega
  omega

/-- **Лемма 1.1.** Центр `p+1` нетривиальной пары близнецов делится на 6. -/
theorem twin_center_dvd_six {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime) (h : 3 < p) :
    6 ∣ (p + 1) := by
  have hmod := twin_center_mod_six hp hp2 h
  omega

/-- **Следствие 1.2.** Индексная форма пары близнецов: существует `m ≥ 1` с `p = 6m-1`, `p+2 = 6m+1`. -/
theorem twin_index_form {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime) (h : 3 < p) :
    ∃ m : ℕ, 1 ≤ m ∧ p = 6 * m - 1 ∧ p + 2 = 6 * m + 1 := by
  have hmod := twin_center_mod_six hp hp2 h
  exact ⟨(p + 1) / 6, by omega, by omega, by omega⟩

/-- Связь `IsTwinPair` (шаг 00) с центровой формой `IsTwinCenter`. -/
theorem isTwinCenter_of_isTwinPair {p : ℕ} (h : IsTwinPair p) (hp3 : 3 < p) :
    ∃ m : ℕ, 6 * m - 1 = p ∧ IsTwinCenter m := by
  obtain ⟨hp, hp2⟩ := h
  obtain ⟨m, _hm1, hmp, hmp2⟩ := twin_index_form hp hp2 hp3
  refine ⟨m, by omega, ?_, ?_⟩
  · have h' : 6 * m - 1 = p := by omega
    rw [h']; exact hp
  · have h' : 6 * m + 1 = p + 2 := by omega
    rw [h']; exact hp2

end EuclidsPath
