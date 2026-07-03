/-
  PolignacBranch — Полиньяк в сетке: кузены (p, p+4) и секси (p, p+6).

  Сетка 6m±1 кодирует малые чётные зазоры между простыми > 3:
    * зазор 2 (близнецы) — ОДИН центр m: пара (6m−1, 6m+1);
    * зазор 4 (кузены)   — СОСЕДНИЕ центры, РАЗНЫЕ стороны:
      пара (6m+1, 6m+5), где 6m+5 = 6(m+1)−1 — минус-сторона центра m+1;
    * зазор 6 (секси)    — СОСЕДНИЕ центры, ОДНА сторона:
      (6m−1, 6(m+1)−1 = 6m+5) на минус-стороне или
      (6m+1, 6(m+1)+1 = 6m+7) на плюс-стороне.

  Гипотеза Полиньяка (в частности, для зазоров 4 и 6) ОТКРЫТА. Эвристика
  Харди–Литтлвуда предсказывает бесконечность каждого класса пар — знак ЗА,
  но НЕ доказательство.

  ⚠️ ГЛАВНАЯ ЧЕСТНОСТЬ: никакая импликация близнецы ⇄ кузены/секси здесь
  НЕ утверждается — ни в одну сторону (маркер
  NoTwinsToPolignacImplicationClaimed). Открытые задачи не решаются.

  ЧТО ДОКАЗАНО (std аксиомы, без sorry):
    * cousin_upper_eq_minusSide — вложение в язык программы: старший кузен —
      минус-сторона СЛЕДУЮЩЕГО центра, 6m+5 = 6(m+1)−1;
    * cousin_mod_six — классификация: младший член пары кузенов p > 3 всегда
      на ПЛЮС-стороне (p % 6 = 1);
    * cousin_instances, sexy_instances — конкретные пары: кузены (7,11),
      (13,17), (19,23); секси (5,11), (11,17), (7,13);
    * cousinLowersInfinite_of_unbounded, sexyLowersInfinite_of_unbounded —
      условные мосты «неограниченность центров ⟹ бесконечность пар»
      (форма как у twinLowersInfinite_of_mersenneTwins в MersenneBranch);
    * constellation_of_adjacent_twinCenters — два СОСЕДНИХ twin-центра дают
      одновременно кузенов и оба вида секси (m = 1: созвездие 5, 7, 11, 13).
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.PolignacBranch

open EuclidsPath

/-! ## Кузены: зазор 4 — соседние центры, разные стороны -/

/-- Кузен-центр: `m` задаёт пару кузенов `(6m+1, 6m+5)` — плюс-сторона центра
    `m` и минус-сторона центра `m+1` (см. `cousin_upper_eq_minusSide`). -/
def IsCousinCenter (m : ℕ) : Prop := (6 * m + 1).Prime ∧ (6 * m + 5).Prime

/-- Множество младших членов пар кузенов `(p, p+4)`. -/
def CousinLowers : Set ℕ := { p | p.Prime ∧ (p + 4).Prime }

/-- **ВЛОЖЕНИЕ В ЯЗЫК ПРОГРАММЫ (доказано):** старший кузен `6m+5` — это
    МИНУС-сторона следующего центра: `6m+5 = 6(m+1) − 1`. Пара кузенов —
    перекрёстная пара соседних центров. -/
theorem cousin_upper_eq_minusSide (m : ℕ) : 6 * m + 5 = 6 * (m + 1) - 1 := by
  omega

/-- **КЛАССИФИКАЦИЯ (доказано):** младший член пары кузенов `p > 3` всегда
    лежит на ПЛЮС-стороне сетки: `p % 6 = 1`. Иначе (при `p % 6 = 5`)
    число `p + 4` делилось бы на 3. -/
theorem cousin_mod_six {p : ℕ} (hp : p.Prime) (hp4 : (p + 4).Prime)
    (h3 : 3 < p) : p % 6 = 1 := by
  have h2 : ¬ (2 ∣ p) := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 2 h with h' | h' <;> omega
  have h3' : ¬ (3 ∣ p) := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h' | h' <;> omega
  have hcases : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases hcases with h | h
  · exact h
  · exfalso
    have hdvd : 3 ∣ p + 4 := ⟨(p + 4) / 3, by omega⟩
    have heq : 3 = p + 4 :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp4).mp hdvd
    omega

/-- Конкретные кузен-центры: `m = 1` даёт `(7, 11)`, `m = 2` — `(13, 17)`,
    `m = 3` — `(19, 23)`. -/
theorem cousin_instances :
    IsCousinCenter 1 ∧ IsCousinCenter 2 ∧ IsCousinCenter 3 := by
  unfold IsCousinCenter
  norm_num

/-- Неограниченность кузен-центров (гипотеза-ВХОД: случай 4 гипотезы
    Полиньяка; ОТКРЫТА, здесь ниоткуда не выводится). -/
def CousinCentersUnbounded : Prop := ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsCousinCenter m

/-- **УСЛОВНЫЙ МОСТ (доказано):** неограниченность кузен-центров ⟹
    бесконечность пар кузенов. Чистая перепаковка сетки, без новой теории
    чисел; форма — как у `twinLowersInfinite_of_mersenneTwins`. -/
theorem cousinLowersInfinite_of_unbounded (H : CousinCentersUnbounded) :
    CousinLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hgt, h1, h2⟩ := H B
  have hmem : (6 * m + 1) ∈ CousinLowers := by
    show (6 * m + 1).Prime ∧ (6 * m + 1 + 4).Prime
    refine ⟨h1, ?_⟩
    have hstep : 6 * m + 1 + 4 = 6 * m + 5 := by omega
    rw [hstep]
    exact h2
  have hBlt : B < 6 * m + 1 := by omega
  exact absurd (hB hmem) (not_le.mpr hBlt)

/-! ## Секси: зазор 6 — соседние центры, одна сторона -/

/-- Секси-пара на МИНУС-стороне: `(6m−1, 6m+5)` — минус-стороны центров
    `m` и `m+1`. -/
def IsSexyMinusPair (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * m + 5).Prime

/-- Секси-пара на ПЛЮС-стороне: `(6m+1, 6m+7)` — плюс-стороны центров
    `m` и `m+1`. -/
def IsSexyPlusPair (m : ℕ) : Prop := (6 * m + 1).Prime ∧ (6 * m + 7).Prime

/-- Секси-центр: `m` несёт секси-пару хотя бы на одной из сторон. -/
def IsSexyCenter (m : ℕ) : Prop := IsSexyMinusPair m ∨ IsSexyPlusPair m

/-- Множество младших членов секси-пар `(p, p+6)`. -/
def SexyLowers : Set ℕ := { p | p.Prime ∧ (p + 6).Prime }

/-- **СОХРАНЕНИЕ СТОРОНЫ (доказано):** сдвиг на 6 не меняет вычет по модулю 6 —
    секси-пара всегда лежит на ОДНОЙ стороне сетки. -/
theorem sexy_preserves_side {p : ℕ} (_hp : p.Prime) (_h3 : 3 < p) :
    (p + 6) % 6 = p % 6 := by
  omega

/-- Конкретные секси-пары: минус-сторона `m = 1` даёт `(5, 11)`, `m = 2` —
    `(11, 17)`; плюс-сторона `m = 1` даёт `(7, 13)`. -/
theorem sexy_instances :
    IsSexyMinusPair 1 ∧ IsSexyMinusPair 2 ∧ IsSexyPlusPair 1 := by
  unfold IsSexyMinusPair IsSexyPlusPair
  norm_num

/-- Неограниченность секси-центров (гипотеза-ВХОД: случай 6 гипотезы
    Полиньяка; ОТКРЫТА, здесь ниоткуда не выводится). -/
def SexyCentersUnbounded : Prop := ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSexyCenter m

/-- **УСЛОВНЫЙ МОСТ (доказано):** неограниченность секси-центров ⟹
    бесконечность секси-пар. Для минус-стороны из простоты `6m − 1`
    извлекается `1 ≤ m` (иначе в ℕ было бы `6·0 − 1 = 0` — не простое),
    что охраняет все переписывания с усечённым вычитанием. -/
theorem sexyLowersInfinite_of_unbounded (H : SexyCentersUnbounded) :
    SexyLowers.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hgt, hcen⟩ := H B
  rcases hcen with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- минус-сторона: младший член 6m − 1
    have hm1 : 1 ≤ m := by
      have := h1.two_le
      omega
    have hmem : (6 * m - 1) ∈ SexyLowers := by
      show (6 * m - 1).Prime ∧ (6 * m - 1 + 6).Prime
      refine ⟨h1, ?_⟩
      have hstep : 6 * m - 1 + 6 = 6 * m + 5 := by omega
      rw [hstep]
      exact h2
    have hBlt : B < 6 * m - 1 := by omega
    exact absurd (hB hmem) (not_le.mpr hBlt)
  · -- плюс-сторона: младший член 6m + 1
    have hmem : (6 * m + 1) ∈ SexyLowers := by
      show (6 * m + 1).Prime ∧ (6 * m + 1 + 6).Prime
      refine ⟨h1, ?_⟩
      have hstep : 6 * m + 1 + 6 = 6 * m + 7 := by omega
      rw [hstep]
      exact h2
    have hBlt : B < 6 * m + 1 := by omega
    exact absurd (hB hmem) (not_le.mpr hBlt)

/-- Сантехника: неограниченность минус-стороны достаточна. -/
theorem sexyUnbounded_of_minus
    (H : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSexyMinusPair m) : SexyCentersUnbounded := by
  intro N
  obtain ⟨m, hlt, hpair⟩ := H N
  exact ⟨m, hlt, Or.inl hpair⟩

/-- Сантехника: неограниченность плюс-стороны достаточна. -/
theorem sexyUnbounded_of_plus
    (H : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSexyPlusPair m) : SexyCentersUnbounded := by
  intro N
  obtain ⟨m, hlt, hpair⟩ := H N
  exact ⟨m, hlt, Or.inr hpair⟩

/-! ## Созвездие: два соседних twin-центра -/

/-- **СОЗВЕЗДИЕ (доказано):** два СОСЕДНИХ twin-центра `m` и `m+1` дают сразу
    всё: кузенов на `m` и обе секси-пары на `m`. При `m = 1` это созвездие
    `5, 7, 11, 13` — кузены `(7, 11)`, секси `(5, 11)` и `(7, 13)`. -/
theorem constellation_of_adjacent_twinCenters {m : ℕ}
    (h1 : IsTwinCenter m) (h2 : IsTwinCenter (m + 1)) :
    IsCousinCenter m ∧ IsSexyMinusPair m ∧ IsSexyPlusPair m := by
  obtain ⟨hm_lo, hm_hi⟩ := h1
  obtain ⟨hm1_lo, hm1_hi⟩ := h2
  have e1 : 6 * (m + 1) - 1 = 6 * m + 5 := by omega
  have e2 : 6 * (m + 1) + 1 = 6 * m + 7 := by omega
  rw [e1] at hm1_lo
  rw [e2] at hm1_hi
  exact ⟨⟨hm_hi, hm1_lo⟩, ⟨hm_lo, hm1_lo⟩, ⟨hm_hi, hm1_hi⟩⟩

/-! ## Честность -/

/-- **ЧЕСТНОСТЬ (охват):** никакая импликация `близнецы ⇄ кузены/секси`
    здесь НЕ утверждается — ни в одну сторону. Гипотеза Полиньяка для
    зазоров 4 и 6 и гипотеза близнецов — НЕЗАВИСИМЫЕ открытые проблемы;
    доказанные выше мосты условны (вход — неограниченность центров) и
    открытых задач не решают. -/
abbrev NoTwinsToPolignacImplicationClaimed : Prop := True

theorem noTwinsToPolignacImplicationClaimed :
    NoTwinsToPolignacImplicationClaimed := trivial

#print axioms cousin_mod_six
#print axioms cousinLowersInfinite_of_unbounded
#print axioms sexyLowersInfinite_of_unbounded
#print axioms constellation_of_adjacent_twinCenters

end EuclidsPath.PolignacBranch
