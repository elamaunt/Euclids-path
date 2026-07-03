/-
  FermatBranch — честный мост Ферма ↔ близнецы: минус-сторона, квадратичная
  цепь, twin-инстансы до 65537.

  ⚠️ ГЛАВНАЯ ЧЕСТНОСТЬ: бесконечность простых Ферма НЕ следует из гипотезы
  близнецов — ни тривиально, ни известным способом. Более того, знак эвристики
  здесь ОБРАТНЫЙ к Мерсенну: простыми известны лишь F₀–F₄, а F₅–F₃₂ доказуемо
  составны, так что вход FermatTwinCentersUnbounded скорее всего ЛОЖЕН.
  Импликация «близнецы ⟹ Ферма» здесь НЕ утверждается
  (маркер NoTwinsToFermatImplicationClaimed).

  ЧТО ДОКАЗАНО (mathlib Nat.fermatNumber, std аксиомы, без sorry):
    * fermatNumber_mod_six / six_mul_fermatCenter — ВЛОЖЕНИЕ в язык программы:
      при k ≥ 1 число Ферма F_k = 2^(2^k) + 1 ≡ 5 (mod 6) — МИНУС-сторона
      центра c_k = (F_k + 1)/6 (контраст с Мерсенном: там плюс-сторона);
      k = 0 исключён (F₀ = 3 не лежит на сетке 6m ± 1);
    * isTwinCenter_fermatCenter_iff — twin-критерий центра Ферма:
      c_k — twin-центр ⟺ F_k и F_k + 2 оба просты;
    * fermat_twin_instances — конкретные Ферма-близнецы: k = 1 даёт (5, 7),
      k = 2 даёт (17, 19), k = 4 даёт (65537, 65539) — оба просты; это самая
      сильная конкретная локализация близнецов в программе;
    * fermat_twin_non_instance — k = 3 НЕ даёт пары: F₃ + 2 = 259 = 7·37;
    * fermatCenter_chain — цепь центров КВАДРАТИЧНА: c' = 6c² − 4c + 1,
      записано без вычитания как c' + 4c = 6c² + 1; в отличие от линейной
      цепи 5c + 1 у простых делителей, она не несёт тождества с постоянным
      простым делителем;
    * twinLowersInfinite_of_fermatTwins — ЕДИНСТВЕННОЕ честное направление,
      и оно в ОБРАТНУЮ сторону: ∞ Ферма-близнецов ⟹ гипотеза близнецов.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.FermatBranch

open EuclidsPath

/-- Центр Ферма: `c_k = (F_k + 1) / 6` (для `k ≥ 1` деление точное). -/
def fermatCenter (k : ℕ) : ℕ := (Nat.fermatNumber k + 1) / 6

/-- **МИНУС-СТОРОНА (доказано):** при `k ≥ 1` число Ферма `F_k ≡ 5 (mod 6)` —
    оно живёт на минус-стороне сетки `6m − 1` (контраст с Мерсенном: плюс). -/
theorem fermatNumber_mod_six {k : ℕ} (hk : 1 ≤ k) :
    Nat.fermatNumber k % 6 = 5 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpow : (2 : ℕ) ^ 2 ^ (j + 1) = 4 ^ 2 ^ j := by
    have hexp : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
    rw [hexp, pow_mul]
    norm_num
  have h43 : 4 ^ 2 ^ j % 3 = 1 := by
    have h := Nat.pow_mod 4 (2 ^ j) 3
    simpa using h
  have hmod3 : Nat.fermatNumber (j + 1) % 3 = 2 := by
    show (2 ^ 2 ^ (j + 1) + 1) % 3 = 2
    rw [hpow]
    omega
  have hmod2 : Nat.fermatNumber (j + 1) % 2 = 1 :=
    Nat.odd_iff.mp (Nat.odd_fermatNumber _)
  omega

/-- **ВЛОЖЕНИЕ В ЯЗЫК ПРОГРАММЫ (доказано):** при `k ≥ 1` деление в центре
    точное: `6·c_k = F_k + 1`. -/
theorem six_mul_fermatCenter {k : ℕ} (hk : 1 ≤ k) :
    6 * fermatCenter k = Nat.fermatNumber k + 1 := by
  have h5 := fermatNumber_mod_six hk
  unfold fermatCenter
  omega

/-- Число Ферма как МИНУС-сторона центра: `F_k = 6·c_k − 1` при `k ≥ 1`. -/
theorem fermatNumber_eq_sixCenter_sub_one {k : ℕ} (hk : 1 ≤ k) :
    Nat.fermatNumber k = 6 * fermatCenter k - 1 := by
  have h := six_mul_fermatCenter hk
  omega

/-- Положительность центра: `c_k ≥ 1` при `k ≥ 1`. -/
theorem fermatCenter_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ fermatCenter k := by
  have h := six_mul_fermatCenter hk
  have h3 := Nat.three_le_fermatNumber k
  omega

/-- **TWIN-КРИТЕРИЙ ЦЕНТРА ФЕРМА (доказано):** центр `c_k` — twin-центр ⟺
    `F_k` и `F_k + 2` оба просты. Число Ферма — МЛАДШИЙ член пары. -/
theorem isTwinCenter_fermatCenter_iff {k : ℕ} (hk : 1 ≤ k) :
    IsTwinCenter (fermatCenter k) ↔
      (Nat.fermatNumber k).Prime ∧ (Nat.fermatNumber k + 2).Prime := by
  have heq := six_mul_fermatCenter hk
  have h3 := Nat.three_le_fermatNumber k
  unfold IsTwinCenter
  have hlo : 6 * fermatCenter k - 1 = Nat.fermatNumber k := by omega
  have hhi : 6 * fermatCenter k + 1 = Nat.fermatNumber k + 2 := by omega
  rw [hlo, hhi]

/-- `c_1 = 1`: пара `(5, 7)`. -/
theorem fermatCenter_one : fermatCenter 1 = 1 := by
  norm_num [fermatCenter, Nat.fermatNumber]

/-- `c_2 = 3`: пара `(17, 19)`. -/
theorem fermatCenter_two : fermatCenter 2 = 3 := by
  norm_num [fermatCenter, Nat.fermatNumber]

/-- `c_3 = 43`: НЕ twin-центр (259 = 7·37, см. ниже). -/
theorem fermatCenter_three : fermatCenter 3 = 43 := by
  norm_num [fermatCenter, Nat.fermatNumber]

/-- Конкретные Ферма-близнецы: `k = 1` даёт пару `(5, 7)`, `k = 2` — `(17, 19)`,
    `k = 4` — `(65537, 65539)`: оба просты, самая сильная конкретная
    локализация близнецов в программе. -/
theorem fermat_twin_instances :
    IsTwinCenter (fermatCenter 1) ∧ IsTwinCenter (fermatCenter 2) ∧
      IsTwinCenter (fermatCenter 4) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isTwinCenter_fermatCenter_iff (by norm_num)]
    constructor <;> norm_num [Nat.fermatNumber]
  · rw [isTwinCenter_fermatCenter_iff (by norm_num)]
    constructor <;> norm_num [Nat.fermatNumber]
  · rw [isTwinCenter_fermatCenter_iff (by norm_num)]
    constructor <;> norm_num [Nat.fermatNumber]

/-- **ЧЕСТНОСТЬ (провал при `k = 3`):** `c_3 = 43` — НЕ twin-центр:
    `F_3 + 2 = 259 = 7·37` составное. Ферма-близнецы не автоматичны. -/
theorem fermat_twin_non_instance : ¬ IsTwinCenter (fermatCenter 3) := by
  rw [isTwinCenter_fermatCenter_iff (by norm_num)]
  rintro ⟨-, h⟩
  norm_num [Nat.fermatNumber] at h

/-- **КВАДРАТИЧНАЯ ЦЕПЬ ЦЕНТРОВ (доказано):** `c_{k+1} = 6·c_k² − 4·c_k + 1`,
    записано без вычитания: `c_{k+1} + 4·c_k = 6·c_k² + 1`. В отличие от
    линейной цепи `5c + 1` у простых делителей, квадратичная цепь не несёт
    тождества с постоянным простым делителем. -/
theorem fermatCenter_chain {k : ℕ} (hk : 1 ≤ k) :
    fermatCenter (k + 1) + 4 * fermatCenter k = 6 * fermatCenter k ^ 2 + 1 := by
  have h1 := six_mul_fermatCenter hk
  have h2 := six_mul_fermatCenter (show 1 ≤ k + 1 by omega)
  have h4 := Nat.three_le_fermatNumber k
  -- Переходим в ℤ: рекурсия mathlib `F_{k+1} = (F_k − 1)² + 1` содержит
  -- Nat-вычитание, снимаем его через `1 ≤ F_k`.
  have h3 : (Nat.fermatNumber (k + 1) : ℤ) =
      ((Nat.fermatNumber k : ℤ) - 1) ^ 2 + 1 := by
    have h := Nat.fermatNumber_succ k
    zify [show 1 ≤ Nat.fermatNumber k by omega] at h
    exact h
  have h1' : 6 * (fermatCenter k : ℤ) = (Nat.fermatNumber k : ℤ) + 1 := by
    exact_mod_cast h1
  have h2' : 6 * (fermatCenter (k + 1) : ℤ) =
      (Nat.fermatNumber (k + 1) : ℤ) + 1 := by
    exact_mod_cast h2
  have hFk : (Nat.fermatNumber k : ℤ) = 6 * (fermatCenter k : ℤ) - 1 := by
    linarith
  have hFk1 : (Nat.fermatNumber (k + 1) : ℤ) =
      6 * (fermatCenter (k + 1) : ℤ) - 1 := by
    linarith
  rw [hFk, hFk1] at h3
  have hZ : (fermatCenter (k + 1) : ℤ) + 4 * (fermatCenter k : ℤ) =
      6 * (fermatCenter k : ℤ) ^ 2 + 1 := by
    nlinarith [h3]
  exact_mod_cast hZ

/-- Строгий рост центров начиная с `k = 1` (из строгого роста чисел Ферма). -/
theorem fermatCenter_strictMono_from_one {k : ℕ} (hk : 1 ≤ k) :
    fermatCenter k < fermatCenter (k + 1) := by
  have h1 := six_mul_fermatCenter hk
  have h2 := six_mul_fermatCenter (show 1 ≤ k + 1 by omega)
  have hlt : Nat.fermatNumber k < Nat.fermatNumber (k + 1) :=
    Nat.fermatNumber_strictMono (by omega)
  omega

/-- Неограниченность Ферма-близнецов (гипотеза-ВХОД, много сильнее близнецов;
    эвристически скорее всего ЛОЖНА: просты лишь F₀–F₄, F₅–F₃₂ составны). -/
def FermatTwinCentersUnbounded : Prop :=
  ∀ N : ℕ, ∃ k : ℕ, 1 ≤ k ∧ N < Nat.fermatNumber k ∧
    (Nat.fermatNumber k).Prime ∧ (Nat.fermatNumber k + 2).Prime

/-- **ЧЕСТНОЕ НАПРАВЛЕНИЕ (доказано):** Ферма-близнецы ⟹ близнецы.
    Это ЕДИНСТВЕННАЯ тривиальная импликация между темами — и она в ЭТУ сторону. -/
theorem twinLowersInfinite_of_fermatTwins
    (H : FermatTwinCentersUnbounded) : TwinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, hk1, hgt, h1, h2⟩ := H B
  have hmem : Nat.fermatNumber k ∈ TwinLowers := by
    show IsTwinPair (Nat.fermatNumber k)
    exact ⟨h1, h2⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- **ЧЕСТНОСТЬ (охват):** импликация `близнецы ⟹ Ферма` НЕ утверждается,
    НЕ доказана и НЕ известна математике: близнецы дают ∞ twin-центров, но
    ничего не говорят о дважды экспоненциально редких центрах Ферма; более
    того, эвристика здесь с ОБРАТНЫМ знаком (F₅–F₃₂ составны). Обратная
    импликация тривиальна и доказана выше. -/
abbrev NoTwinsToFermatImplicationClaimed : Prop := True

theorem noTwinsToFermatImplicationClaimed :
    NoTwinsToFermatImplicationClaimed := trivial

#print axioms six_mul_fermatCenter
#print axioms isTwinCenter_fermatCenter_iff
#print axioms fermat_twin_instances
#print axioms fermatCenter_chain
#print axioms twinLowersInfinite_of_fermatTwins

end EuclidsPath.FermatBranch
