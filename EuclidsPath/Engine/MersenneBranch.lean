/-
  MersenneBranch — честный мост Мерсенн ↔ близнецы.

  ⚠️ ГЛАВНАЯ ЧЕСТНОСТЬ: бесконечность простых Мерсенна НЕ следует из гипотезы
  близнецов — ни тривиально, ни известным способом. Это НЕЗАВИСИМЫЕ открытые
  проблемы: близнецы дают ∞ twin-центров, но ничего не говорят об экспоненциально
  редких центрах Мерсенна. Импликация «близнецы ⟹ Мерсенн» здесь НЕ утверждается
  (маркер NoTwinsToMersenneImplicationClaimed).

  ЧТО ДОКАЗАНО (mathlib mersenne, std аксиомы, без sorry):
    * mersenne_eq_sixCenter_add_one — ВЛОЖЕНИЕ в язык программы: при нечётном p
      число Мерсенна 2^p − 1 = 6·m_p + 1 — ПЛЮС-сторона центра
      m_p = (2^(p−1) − 1)/3;
    * isTwinCenter_mersenneCenter_iff — twin-критерий центра Мерсенна:
      m_p — twin-центр ⟺ 2^p − 3 и 2^p − 1 оба просты;
    * mersenne_twin_instances — конкретные Мерсенн-близнецы: p = 3 даёт (5, 7),
      p = 5 даёт (29, 31);
    * twinLowersInfinite_of_mersenneTwins — ЕДИНСТВЕННАЯ тривиальная импликация,
      и она в ОБРАТНУЮ сторону: ∞ Мерсенн-близнецов ⟹ гипотеза близнецов.
  MersennePrimesInfinite — цель-маркер, ниоткуда здесь не выводится.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.MersenneBranch

open EuclidsPath

/-- Центр Мерсенна: `m_p = (2^(p−1) − 1)/3` (для нечётного `p` деление точное). -/
def mersenneCenter (p : ℕ) : ℕ := (2 ^ (p - 1) - 1) / 3

/-- **ВЛОЖЕНИЕ В ЯЗЫК ПРОГРАММЫ (доказано):** при нечётном `p` число Мерсенна —
    ПЛЮС-сторона центра: `2^p − 1 = 6·m_p + 1`. -/
theorem mersenne_eq_sixCenter_add_one {p : ℕ} (hp : Odd p) :
    mersenne p = 6 * mersenneCenter p + 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h4 : 4 ^ k % 3 = 1 := by
    have h := Nat.pow_mod 4 k 3
    simpa using h
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨c, hcc⟩ : 3 ∣ 4 ^ k - 1 := by omega
  have hexp : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    ring
  have h2pow : (2 : ℕ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  have hc : mersenneCenter (2 * k + 1) = c := by
    unfold mersenneCenter
    rw [Nat.add_sub_cancel, h2pow, hcc]
    exact Nat.mul_div_cancel_left c (by norm_num)
  have hval : 2 * 4 ^ k - 1 = 6 * c + 1 := by omega
  calc mersenne (2 * k + 1)
      = 2 ^ (2 * k + 1) - 1 := rfl
    _ = 2 * 4 ^ k - 1 := by rw [hexp]
    _ = 6 * c + 1 := hval
    _ = 6 * mersenneCenter (2 * k + 1) + 1 := by rw [hc]

/-- **TWIN-КРИТЕРИЙ ЦЕНТРА МЕРСЕННА (доказано):** центр `m_p` — twin-центр ⟺
    `2^p − 3` и `2^p − 1` оба просты. -/
theorem isTwinCenter_mersenneCenter_iff {p : ℕ} (hp : Odd p) (h2 : 2 ≤ p) :
    IsTwinCenter (mersenneCenter p) ↔
      (2 ^ p - 3).Prime ∧ (mersenne p).Prime := by
  have heq := mersenne_eq_sixCenter_add_one hp
  have hpow : 4 ≤ 2 ^ p := by
    calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h2
  unfold mersenne at heq ⊢
  unfold IsTwinCenter
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have : 6 * mersenneCenter p - 1 = 2 ^ p - 3 := by omega
      rwa [this] at hlo
    · have : 6 * mersenneCenter p + 1 = 2 ^ p - 1 := by omega
      rwa [this] at hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · have : 6 * mersenneCenter p - 1 = 2 ^ p - 3 := by omega
      rw [this]; exact hlo
    · have : 6 * mersenneCenter p + 1 = 2 ^ p - 1 := by omega
      rw [this]; exact hhi

/-- Конкретные Мерсенн-близнецы: `p = 3` даёт пару `(5, 7)`, `p = 5` — `(29, 31)`. -/
theorem mersenne_twin_instances :
    IsTwinCenter (mersenneCenter 3) ∧ IsTwinCenter (mersenneCenter 5) := by
  constructor
  · rw [isTwinCenter_mersenneCenter_iff ⟨1, by norm_num⟩ (by norm_num)]
    constructor <;> norm_num [mersenne]
  · rw [isTwinCenter_mersenneCenter_iff ⟨2, by norm_num⟩ (by norm_num)]
    constructor <;> norm_num [mersenne]

/-- Неограниченность Мерсенн-близнецов (гипотеза-ВХОД, много сильнее близнецов). -/
def MersenneTwinCentersUnbounded : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < 2 ^ p - 3 ∧ (2 ^ p - 3).Prime ∧ (mersenne p).Prime

/-- **ЧЕСТНОЕ НАПРАВЛЕНИЕ (доказано):** Мерсенн-близнецы ⟹ близнецы.
    Это ЕДИНСТВЕННАЯ тривиальная импликация между темами — и она в ЭТУ сторону. -/
theorem twinLowersInfinite_of_mersenneTwins
    (H : MersenneTwinCentersUnbounded) : TwinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, h1, h2⟩ := H B
  have h5 : 5 ≤ 2 ^ p := by
    have := h1.two_le
    omega
  have hmem : (2 ^ p - 3) ∈ TwinLowers := by
    show IsTwinPair (2 ^ p - 3)
    refine ⟨h1, ?_⟩
    have hstep : 2 ^ p - 3 + 2 = mersenne p := by
      unfold mersenne
      omega
    rw [hstep]
    exact h2
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- Цель-маркер: бесконечность простых Мерсенна. НЕ выводится здесь ниоткуда. -/
def MersennePrimesInfinite : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (mersenne p).Prime

/-- **ЧЕСТНОСТЬ (охват):** импликация `близнецы ⟹ Мерсенн` НЕ утверждается,
    НЕ доказана и НЕ известна математике: близнецы дают ∞ twin-центров, но
    ничего не говорят о центрах Мерсенна (экспоненциально редких). Обратная
    тривиальна и доказана выше. -/
abbrev NoTwinsToMersenneImplicationClaimed : Prop := True

theorem noTwinsToMersenneImplicationClaimed :
    NoTwinsToMersenneImplicationClaimed := trivial

end EuclidsPath.MersenneBranch
