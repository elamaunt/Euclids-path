/-
  SophieGermainBranch — Софи Жермен: удвоение центра и жемчужина
  (SG-простые убивают Мерсенна).

  Пара Софи Жермен: (p, 2p+1), оба простые. Геометрия в языке программы:
    * ПЛЮС-сторона исключена: если p = 6m+1 (m ≥ 1), то 3 ∣ 2(6m+1)+1 = 12m+3,
      значит 2p+1 не простое — SG-простые p > 3 живут ТОЛЬКО на минус-стороне;
    * на минус-стороне SG-отображение — это УДВОЕНИЕ ЦЕНТРА m → 2m:
      2(6m−1)+1 = 6(2m)−1 — родня цепочек Мерсенна 4m+1 и пятиадической 5m+1.

  ⚠️ ЖЕМЧУЖИНА (Эйлер–Лагранж, классика, здесь ПОЛНОСТЬЮ доказана):
    p ≡ 3 (mod 4), p > 3, q = 2p+1 простое ⟹ q ∣ M_p и M_p СОСТАВНОЕ.
  Маршрут: q ≡ 7 (mod 8) ⟹ 2 — квадратичный вычет mod q
  (ZMod.exists_sq_eq_two_iff) ⟹ критерий Эйлера даёт 2^p ≡ 1 (mod q)
  ⟹ q ∣ 2^p − 1; при p ≥ 4 имеем 2p+1 < 2^p − 1, поэтому делитель собственный.
  Это формализует ФРАГМЕНТ той самой эвристики, которую карантин §16/гл.43
  выставлял против границы Мерсенна: SG-простые с p ≡ 3 (mod 4) поштучно
  ГАСЯТ кандидатов Мерсенна. Случай p = 3 честно исключён: q = 7 = M₃,
  которое само ПРОСТОЕ (делитель не собственный).

  ЧТО ДОКАЗАНО (std аксиомы, без sorry):
    * not_sophieGermain_of_plusSide — плюс-сторона исключена;
    * sophieGermain_minusSide — SG-простое p > 3 ⟹ p ≡ 5 (mod 6);
    * sg_center_doubling / isSGCenter_iff — SG-пара = удвоение центра;
    * sg_instances — пары (5,11), (11,23), (29,59), (89,179);
    * two_mul_add_one_lt_mersenne — рост: 2p+1 < M_p при p ≥ 4;
    * sophieGermain_divides_mersenne — ЖЕМЧУЖИНА (см. выше);
    * mersenne_composite_examples — 23 ∣ M₁₁ = 2047 = 23·89, M₁₁ составное;
    * mersenneComposites_unbounded_of_sg — УСЛОВНО: неограниченность
      SG-простых с p ≡ 3 (mod 4) ⟹ неограниченность p с M_p составным.

  ⚠️ ЧЕСТНОСТЬ: гипотеза Софи Жермен (SophieGermainUnbounded,
  SGThreeMod4Unbounded) ОТКРЫТА — здесь она только ВХОД-маркер, ниоткуда
  не выводится; никакие открытые задачи не решаются. БЕЗУСЛОВНАЯ
  бесконечность составных чисел Мерсенна — известная теорема литературы
  (другими методами); здесь она получена лишь УСЛОВНО из SG-неограниченности.
  Импликация «SG ⟹ близнецы» НЕ утверждается
  (маркер NoSGToTwinsImplicationClaimed).
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath.SophieGermainBranch

open EuclidsPath

/-- Пара Софи Жермен с младшим членом `p`: простые `p` и `2p+1`. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- **ПЛЮС-СТОРОНА ИСКЛЮЧЕНА (доказано):** если `p = 6m+1` (m ≥ 1), то
    `2p+1 = 12m+3` делится на 3 и не простое. SG-простые `p > 3` живут
    только на минус-стороне. -/
theorem not_sophieGermain_of_plusSide {m : ℕ} (hm : 1 ≤ m) :
    ¬ (2 * (6 * m + 1) + 1).Prime := by
  intro h
  have hdvd : (3 : ℕ) ∣ 2 * (6 * m + 1) + 1 := ⟨4 * m + 1, by ring⟩
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h).mp hdvd
  omega

/-- **МИНУС-СТОРОНА (доказано):** SG-простое `p > 3` обязано иметь вид
    `6m − 1`, т.е. `p ≡ 5 (mod 6)`. -/
theorem sophieGermain_minusSide {p : ℕ} (h : IsSophieGermain p) (h3 : 3 < p) :
    p % 6 = 5 := by
  have h2d : ¬ (2 ∣ p) := by
    intro hd
    rcases h.1.eq_one_or_self_of_dvd 2 hd with h' | h' <;> omega
  have h3d : ¬ (3 ∣ p) := by
    intro hd
    rcases h.1.eq_one_or_self_of_dvd 3 hd with h' | h' <;> omega
  have h15 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases h15 with h1 | h5
  · exfalso
    have hdvd : (3 : ℕ) ∣ 2 * p + 1 := ⟨(2 * p + 1) / 3, by omega⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h.2).mp hdvd
    omega
  · exact h5

/-- **УДВОЕНИЕ ЦЕНТРА (доказано):** на минус-стороне SG-отображение — это
    `m → 2m`: `2(6m−1)+1 = 6(2m)−1`. Родня цепочек Мерсенна `4m+1`
    и пятиадической `5m+1`. -/
theorem sg_center_doubling {m : ℕ} (hm : 1 ≤ m) :
    2 * (6 * m - 1) + 1 = 6 * (2 * m) - 1 := by omega

/-- SG-центр: `m` такой, что `6m−1` и `6(2m)−1` оба просты. -/
def IsSGCenter (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * (2 * m) - 1).Prime

/-- **КРИТЕРИЙ SG-ЦЕНТРА (доказано):** `m` — SG-центр ⟺ `6m−1` — SG-простое. -/
theorem isSGCenter_iff {m : ℕ} (hm : 1 ≤ m) :
    IsSGCenter m ↔ IsSophieGermain (6 * m - 1) := by
  unfold IsSGCenter IsSophieGermain
  have h1 : 2 * (6 * m - 1) + 1 = 6 * (2 * m) - 1 := by omega
  rw [h1]

/-- Конкретные SG-пары: (5,11), (11,23), (29,59), (89,179). -/
theorem sg_instances :
    IsSophieGermain 5 ∧ IsSophieGermain 11 ∧
      IsSophieGermain 29 ∧ IsSophieGermain 89 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num

/-- **РОСТ (доказано):** при `p ≥ 4` спутник `2p+1` строго меньше `M_p`,
    так что найденный ниже делитель — СОБСТВЕННЫЙ. -/
theorem two_mul_add_one_lt_mersenne {p : ℕ} (hp : 4 ≤ p) :
    2 * p + 1 < mersenne p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num [mersenne]
  | succ n hn ih => rw [mersenne_succ]; omega

/-- **ЖЕМЧУЖИНА (Эйлер–Лагранж, доказано):** если `p ≡ 3 (mod 4)`, `p > 3`
    и `q = 2p+1` простое, то `q ∣ M_p` и `M_p` СОСТАВНОЕ.

    Маршрут: `q ≡ 7 (mod 8)` ⟹ `2` — квадрат в `ZMod q` ⟹ по критерию
    Эйлера `2^((q−1)/2) = 2^p = 1` в `ZMod q` ⟹ `q ∣ 2^p − 1 = M_p`;
    при `p ≥ 4` имеем `q < M_p`, поэтому `M_p` не простое.
    Случай `p = 3` честно исключён: `q = 7 = M₃` само простое. -/
theorem sophieGermain_divides_mersenne {p : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 3) (hq : (2 * p + 1).Prime) (hgt : 3 < p) :
    (2 * p + 1) ∣ mersenne p ∧ ¬ (mersenne p).Prime := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  -- `p.Prime` — часть классической формулировки (M_p осмысленно для простых p);
  -- для самого вывода делимости хватает p ≡ 3 (mod 4), p > 3 и простоты q.
  have _ := hp.two_le
  -- q = 2p+1 ≡ 7 (mod 8), т.к. p ≡ 3 (mod 4)
  have h8 : (2 * p + 1) % 8 = 7 := by omega
  -- значит 2 — квадратичный вычет mod q
  have hsq : IsSquare (2 : ZMod (2 * p + 1)) :=
    (ZMod.exists_sq_eq_two_iff (by omega : 2 * p + 1 ≠ 2)).mpr (Or.inr h8)
  have h2ne : (2 : ZMod (2 * p + 1)) ≠ 0 := by
    intro h0
    have hcast : ((2 : ℕ) : ZMod (2 * p + 1)) = 0 := by exact_mod_cast h0
    have hdvd2 : (2 * p + 1) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * p + 1)).mp hcast
    have := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  -- критерий Эйлера: 2^((q−1)/2) = 1 в ZMod q, а (q−1)/2 = p
  have heuler : (2 : ZMod (2 * p + 1)) ^ ((2 * p + 1) / 2) = 1 :=
    (ZMod.euler_criterion (2 * p + 1) h2ne).mp hsq
  have hdiv2 : (2 * p + 1) / 2 = p := by omega
  rw [hdiv2] at heuler
  -- возврат в ℕ: 2^p ≡ 1 (mod q)
  have hmodeq : 2 ^ p ≡ 1 [MOD 2 * p + 1] := by
    have hcast : ((2 ^ p : ℕ) : ZMod (2 * p + 1)) = ((1 : ℕ) : ZMod (2 * p + 1)) := by
      push_cast
      exact heuler
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- значит q ∣ 2^p − 1 = M_p
  have hdvd : (2 * p + 1) ∣ mersenne p := by
    have h1le : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
    have := (Nat.modEq_iff_dvd' h1le).mp hmodeq.symm
    simpa [mersenne] using this
  -- делитель собственный: 1 < q < M_p при p ≥ 4
  refine ⟨hdvd, fun hMp => ?_⟩
  have hlt := two_mul_add_one_lt_mersenne (by omega : 4 ≤ p)
  rcases hMp.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega

/-- **ДЕМОНСТРАЦИЯ (доказано):** `p = 11 ≡ 3 (mod 4)`, `q = 23` простое,
    и действительно `23 ∣ M₁₁ = 2047 = 23·89` — `M₁₁` составное. -/
theorem mersenne_composite_examples :
    (2 * 11 + 1) ∣ mersenne 11 ∧ ¬ (mersenne 11).Prime :=
  sophieGermain_divides_mersenne (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Неограниченность SG-простых с `p ≡ 3 (mod 4)` (гипотеза-ВХОД, открыта). -/
def SGThreeMod4Unbounded : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 4 = 3 ∧ (2 * p + 1).Prime

/-- **УСЛОВНАЯ БЕСКОНЕЧНОСТЬ СОСТАВНЫХ МЕРСЕННОВ (доказано как импликация):**
    из SG-неограниченности (класс `3 mod 4`) следует неограниченность простых
    `p` с составным `M_p`. Безусловно этот вывод известен литературе другими
    методами; здесь честно фиксируется только SG-маршрут. -/
theorem mersenneComposites_unbounded_of_sg (H : SGThreeMod4Unbounded) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬ (mersenne p).Prime := by
  intro N
  obtain ⟨p, h1, h2, h3, h4⟩ := H (max N 3)
  have hN : N ≤ max N 3 := le_max_left N 3
  have h3le : 3 ≤ max N 3 := le_max_right N 3
  exact ⟨p, by omega, h2, (sophieGermain_divides_mersenne h2 h3 h4 (by omega)).2⟩

/-- Гипотеза Софи Жермен (ВХОД-маркер, открыта): SG-простых бесконечно много. -/
def SophieGermainUnbounded : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsSophieGermain p

/-- **ЧЕСТНОСТЬ (охват):** импликация `SG ⟹ близнецы` НЕ утверждается,
    НЕ доказана и НЕ известна математике: SG-гипотеза и гипотеза близнецов —
    независимые открытые проблемы (родственные лишь по форме `p, p+2` против
    `p, 2p+1`). Здесь никакие открытые задачи не решаются: обе
    неограниченности выше — только маркеры-ВХОДЫ, а безусловная бесконечность
    СОСТАВНЫХ чисел Мерсенна (известная теорема литературы) получена лишь
    УСЛОВНО из SG-неограниченности. -/
abbrev NoSGToTwinsImplicationClaimed : Prop := True

theorem noSGToTwinsImplicationClaimed : NoSGToTwinsImplicationClaimed := trivial

#print axioms sophieGermain_divides_mersenne
#print axioms mersenne_composite_examples
#print axioms sophieGermain_minusSide
#print axioms mersenneComposites_unbounded_of_sg

end EuclidsPath.SophieGermainBranch
