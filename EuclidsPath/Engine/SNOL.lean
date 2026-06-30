/-
  SNOL: Shifted-Neighbour Obstruction Lemma — финальная редукция.
  Источник: euclidean_crt_payment_ledger_full_ru_2026-06-30.md (§18–22).
  Проза: prose/27_SNOL.md.

  Новая, более сильная редукция (rank descent → rank-1 → SNOL) сводит ВСЁ к ОДНОМУ узлу:
    «finite twins ⟹ carrier-scale terminal shifted-neighbour obstruction (`p ∣ a−2ε`, `p ≤ A`)».

  ВАЖНО (численно подтверждено, аудит §22): SNOL НЕ следует из CRT-ёмкости — у ~62–78% простых
  `a>A` сосед `a±2` уже пойман малым простым `≤A`. Поэтому SNOL ОБЯЗАНА опираться на Euclidean-
  родословную активного `a` (descent ancestry), а НЕ на распределение. Это точка, где маршрут НЕ
  переходит красную линию: он её ЗАПРЕЩАЕТ (счёт бессилен) и требует структуру родословной.

  Здесь — доказуемая алгебра rank-1 (§19) + neighbour saturation (§20), и финальная УСЛОВНАЯ
  теорема (`finite ⟹ SNOL-violation`), с SNOL как явным входом (как `H` у four-corner).

  Алгебра элементарна. SNOL — единственный открытый узел.
-/
import Mathlib
import EuclidsPath.Engine.ToTwins

set_option autoImplicit false

namespace EuclidsPath.SNOL

open EuclidsPath

/-! ### §19–20. Доказуемая алгебра rank-1: перенос двойки и neighbour-коридор -/

/--
  **Rank-1 opposite side (§19).** Если `6n + ε = a` (одна сторона — само активное простое `a`),
  то противоположная сторона ровно `6n − ε = a − 2ε`. Чистая алгебра переноса двойки.
-/
theorem rank1_opposite {n a ε : ℤ} (h : 6 * n + ε = a) : 6 * n - ε = a - 2 * ε := by
  omega

/--
  **Neighbour saturation (§20).** Если активное простое лежит в neighbour-коридоре по примориалу
  `Q`: `a ≡ 2ε (mod q)` для всех `q ∈ Q` (попарно взаимно простых), то `P_Q ∣ a − 2ε`, т.е.
  `a = k·P_Q + 2ε`. Это евклидов twin-neighbour сдвиг `kP ± 2`. Чистая алгебра.
-/
theorem neighbour_saturation {Q : Finset ℕ} {a ε : ℤ}
    (hcop : (Q : Set ℕ).Pairwise Nat.Coprime)
    (hsat : ∀ q ∈ Q, (q : ℤ) ∣ a - 2 * ε) :
    (Q.prod (fun q => (q : ℤ))) ∣ a - 2 * ε :=
  Finset.prod_dvd_of_coprime
    (fun {_i} hi {_j} hj hij => (hcop hi hj hij).isCoprime.intCast) hsat

/--
  **Neighbour-коридор недостижим для малого `a` (порог, §20/§17).** Если примориал `P` соседского
  коридора превосходит `|a − 2ε|`, то `a = 2ε`: нетривиальное активное простое не может насыщать
  весь коридор. (Тот же закон дефекта, но для соседского сдвига `2ε` вместо `θ`.)
-/
theorem neighbour_corridor_bound {P a ε : ℤ}
    (hdvd : P ∣ a - 2 * ε) (hZ : |a - 2 * ε| < P) : a = 2 * ε := by
  rcases eq_or_ne (a - 2 * ε) 0 with h0 | h0
  · omega
  · have := Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs P (a - 2 * ε)).mpr hdvd)
    omega

/-! ### §21. Финальная условная теорема: SNOL ⟹ бесконечно много близнецов -/

/--
  **SNOL-вход.** Ровно тот же типизированный четырёхугольный/блочный вход, что замыкает гипотезу:
  на каждом масштабе `N` есть carrier выше `N`, в котором «плохое» (terminal shifted-neighbour
  obstruction) строго меньше carrier, и каждый выживший — twin-центр. SNOL утверждает, что
  terminal shifted-neighbour current НЕ carrier-scale — т.е. этот блочный вход выполнен.
-/
abbrev SNOLInput : Prop :=
  ∀ N : ℕ, ∃ carrier bad : Finset ℕ,
      (∀ m ∈ carrier, N < m) ∧ bad.card < carrier.card ∧
      (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)

/--
  **Финальная редукция (Теорема 21.1).** SNOL (terminal shifted-neighbour obstruction не может
  быть carrier-scale, в блочной форме) ⟹ простых-близнецов бесконечно много. Машинно: это прямой
  мост `twin_prime_conjecture_of_blocks`. Открыт ровно SNOL.
-/
theorem twin_primes_of_SNOL (H : SNOLInput) : TwinLowers.Infinite :=
  twin_prime_conjecture_of_blocks H

/--
  **Контрапозиция: «близнецов конечно» противоречит SNOL.** Если `TwinLowers` конечно и выполнен
  SNOL-вход, то `False`. Единственный открытый узел всей программы — SNOL.
-/
theorem finite_contradicts_SNOL (hfin : ¬ TwinLowers.Infinite) (H : SNOLInput) : False :=
  hfin (twin_primes_of_SNOL H)

end EuclidsPath.SNOL
