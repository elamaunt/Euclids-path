/-
  OddPerfectThreePrimes — три простых делителя нечётного свидетеля.
  Раздел отчёта: «Совершенные числа (нечётный свидетель)», кандидат 2 [medium].
  Тип свидетеля и decide-граница: Engine/PerfectNumberBranch.lean (oddPerfect_ge_101).

  ЗЕЛЁНЫЙ МОДУЛЬ (всё доказано, без sorry/axiom, карантин НЕ импортируется):
    * pred_mul_geomSum_add_one — геометрическая сумма в беззнаковой форме:
      (p−1)·(1 + p + … + p^a) + 1 = p^(a+1);
    * pred_mul_sigma_prime_pow_add_one — та же форма для σ₁(p^a): вместо дроби
      (p^(a+1)−1)/(p−1) — целочисленное тождество без вычитания;
    * not_perfect_prime_pow / not_perfect_prime — НИКАКАЯ степень простого
      (включая чётные 2^k!) не совершенна: σ₁(p^k) ≡ 1 (mod p), а 2·p^k ≡ 0,
      и p ∣ 1 — противоречие;
    * perfect_two_mul_prod_pred_le_prod — оценка изобилия для ЛЮБОГО совершенного
      n ≠ 0: 2·∏(p−1) ≤ ∏p по всем простым делителям n (мультипликативность σ₁
      по факторизации + геометрическое тождество по каждому простому);
    * odd_perfect_three_le_card_primeFactors — нечётное совершенное число имеет
      не меньше трёх различных простых делителей (классика);
    * oddPerfect_not_prime / oddPerfect_not_primePow /
      oddPerfect_min_three_prime_factors — те же факты в языке свидетеля
      OddPerfectNumber.

  МАТЕМАТИКА (классическая, известна со времён Эйлера). Для совершенного n
  выполняется σ(n) = 2n. По мультипликативности σ(n) = ∏_p σ(p^{a_p}), и для
  каждого простого p:  (p−1)·σ(p^{a_p}) = p^{a_p+1} − 1 < p·p^{a_p}.
  Перемножая: (∏(p−1))·σ(n) ≤ (∏p)·n, откуда 2·∏(p−1) ≤ ∏p. Если у нечётного n
  один простой делитель p ≥ 3, получаем 2(p−1) ≤ p, т.е. p ≤ 2 — противоречие;
  если два различных нечётных p, q ≥ 3 (один из них ≥ 5), то 2(p−1)(q−1) ≤ pq
  противоречит (p−2)(q−2) ≥ 3. В привычной записи это σ(n)/n < p/(p−1) · q/(q−1)
  ≤ (3/2)·(5/4) = 15/8 < 2. Значит простых делителей минимум три.

  ЧЕСТНОСТЬ: это НЕ решение проблемы нечётного совершенного числа — она открыта
  с античности, и здесь НЕ утверждается ни существование, ни несуществование
  свидетеля. Это КАЧЕСТВЕННОЕ зелёное сужение домена типа OddPerfectNumber —
  первое не-числовое (в дополнение к decide-отсеву oddPerfect_ge_101): всякий
  гипотетический свидетель обязан иметь ≥ 3 различных простых делителей.
  Формальных связок-декретов в модуле нет: все теоремы — безусловная
  арифметика, оплаченная mathlib-мультипликативностью σ и kernel-проверкой.
  Таинт-леджер репозитория не меняется.
-/
import Mathlib
import EuclidsPath.Engine.PerfectNumberBranch

set_option autoImplicit false

namespace EuclidsPath.PerfectNumberBranch

/-! ### Геометрическое тождество без вычитания -/

/-- Геометрическая сумма в беззнаковой форме: `(p − 1)·(1 + p + … + p^a) + 1 = p^(a+1)`.
    Обычная запись `∑ p^i = (p^(a+1) − 1)/(p − 1)` в ℕ неудобна (усечённые вычитание
    и деление); эта форма — точное целочисленное тождество. -/
theorem pred_mul_geomSum_add_one {p : ℕ} (hp : 1 ≤ p) (a : ℕ) :
    (p - 1) * (∑ i ∈ Finset.range (a + 1), p ^ i) + 1 = p ^ (a + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ, ← ih]
    ring

/-- Сумма делителей степени простого, беззнаковая форма:
    `(p − 1)·σ₁(p^a) + 1 = p^(a+1)` — это в точности `σ(p^a) = (p^(a+1)−1)/(p−1)`
    без дроби. Ключевой кирпич оценки изобилия. -/
theorem pred_mul_sigma_prime_pow_add_one {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * (ArithmeticFunction.sigma 1 (p ^ a)) + 1 = p ^ (a + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  exact pred_mul_geomSum_add_one hp.one_lt.le a

/-! ### Степень простого не бывает совершенной (mod p) -/

/-- **Классика (доказано): никакая степень простого не совершенна** — включая
    чётные `2^k`. Аргумент: σ₁(p^k) = 1 + p·(1 + … + p^(k−1)) ≡ 1 (mod p),
    тогда как совершенность требует σ₁(p^k) = 2·p^k ≡ 0 (mod p); выходит p ∣ 1. -/
theorem not_perfect_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ¬ Nat.Perfect (p ^ k) := by
  intro hperf
  have hσ : ArithmeticFunction.sigma 1 (p ^ k) = 2 * p ^ k := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (pow_pos hp.pos k)).mp hperf
  have hgeom : ArithmeticFunction.sigma 1 (p ^ k)
      = p * (∑ i ∈ Finset.range k, p ^ i) + 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
      Finset.mul_sum]
    simp [pow_succ']
  have hkey : p * (∑ i ∈ Finset.range k, p ^ i) + 1 = 2 * p ^ k := by
    rw [← hgeom]; exact hσ
  have hp_dvd : p ∣ 1 := by
    have h1 : p ∣ 2 * p ^ k := (dvd_pow_self p hk).mul_left 2
    have h2 : p ∣ p * (∑ i ∈ Finset.range k, p ^ i) := dvd_mul_right p _
    have h3 := Nat.dvd_sub h1 h2
    rwa [← hkey, Nat.add_sub_cancel_left] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp hp_dvd)

/-- Простое число не совершенно: σ₁(p) = p + 1 ≠ 2p. Частный случай `k = 1`. -/
theorem not_perfect_prime {p : ℕ} (hp : p.Prime) : ¬ Nat.Perfect p := by
  intro h
  exact not_perfect_prime_pow hp one_ne_zero (by rwa [pow_one])

/-! ### Оценка изобилия: 2·∏(p−1) ≤ ∏p для совершенного n -/

/-- **Оценка изобилия (доказано):** для любого совершенного `n ≠ 0`
    `2·∏(p−1) ≤ ∏p` по всем простым делителям `n`. Это целочисленная форма
    классического `2 = σ(n)/n < ∏ p/(p−1)`: мультипликативность σ₁ по
    факторизации + геометрическое тождество по каждому простому. -/
theorem perfect_two_mul_prod_pred_le_prod {n : ℕ} (hn : n ≠ 0) (hperf : Nat.Perfect n) :
    2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
  have hσ : ArithmeticFunction.sigma 1 n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn)).mp hperf
  have hfac : ArithmeticFunction.sigma 1 n
      = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    simpa using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) hn
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.prod_factorization_pow_eq_self hn
  have hchain :
      (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) ≤ (∏ p ∈ n.primeFactors, p) * n := by
    calc (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n)
        = (∏ p ∈ n.primeFactors, (p - 1)) * ArithmeticFunction.sigma 1 n := by rw [hσ]
      _ = ∏ p ∈ n.primeFactors,
            ((p - 1) * ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) := by
          rw [hfac, Finset.prod_mul_distrib]
      _ ≤ ∏ p ∈ n.primeFactors, p ^ (n.factorization p + 1) :=
          Finset.prod_le_prod' fun p hp =>
            Nat.le.intro
              (pred_mul_geomSum_add_one
                (Nat.prime_of_mem_primeFactors hp).one_lt.le _)
      _ = ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) :=
          Finset.prod_congr rfl fun p _ => pow_succ p _
      _ = (∏ p ∈ n.primeFactors, p ^ n.factorization p) * ∏ p ∈ n.primeFactors, p :=
          Finset.prod_mul_distrib
      _ = n * ∏ p ∈ n.primeFactors, p := by rw [hself]
      _ = (∏ p ∈ n.primeFactors, p) * n := Nat.mul_comm _ _
  have hfin :
      (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n ≤ (∏ p ∈ n.primeFactors, p) * n := by
    have hre : (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n
        = (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by ring
    rw [hre]; exact hchain
  exact Nat.le_of_mul_le_mul_right hfin (Nat.pos_of_ne_zero hn)

/-! ### Счётная часть: два нечётных простых не оплачивают изобилие -/

/-- Арифметический факт: для различных нечётных `p, q ≥ 3` (один из них тогда ≥ 5)
    выполнено `pq < 2(p−1)(q−1)` — эквивалент `(p−2)(q−2) ≥ 3 > 2`. -/
private theorem two_mul_pred_mul_pred_gt {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hne : p ≠ q) (hpo : p % 2 = 1) (hqo : q % 2 = 1) :
    p * q < 2 * ((p - 1) * (q - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 3 := ⟨p - 3, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 3 := ⟨q - 3, by omega⟩
  have e1 : a + 3 - 1 = a + 2 := by omega
  have e2 : b + 3 - 1 = b + 2 := by omega
  rw [e1, e2]
  -- различие + нечётность ⟹ один из хвостов ≥ 2 (т.е. одно простое ≥ 5)
  have h5 : 2 ≤ a ∨ 2 ≤ b := by omega
  have hid : (a + 3) * (b + 3) + (a * b + a + b) = 2 * ((a + 2) * (b + 2)) + 1 := by
    ring
  rcases h5 with h | h
  · nlinarith [Nat.zero_le (a * b), hid]
  · nlinarith [Nat.zero_le (a * b), hid]

/-! ### Главная теорема: три различных простых делителя -/

/-- **КЛАССИКА (доказано): нечётное совершенное число имеет не меньше трёх
    различных простых делителей.** Маршрут: оценка изобилия
    `2·∏(p−1) ≤ ∏p` (`perfect_two_mul_prod_pred_le_prod`); при одном нечётном
    простом делителе `p ≥ 3` она даёт `p ≤ 2`, при двух различных нечётных —
    противоречит `pq < 2(p−1)(q−1)`. НЕ решение открытой проблемы: лишь
    качественное сужение домена гипотетического свидетеля. -/
theorem odd_perfect_three_le_card_primeFactors {n : ℕ}
    (hodd : Odd n) (hperf : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact (by decide : ¬ Nat.Perfect 1) hperf
  -- все простые делители нечётного n нечётны и ≥ 3
  have hodd_p : ∀ p ∈ n.primeFactors, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    have hne2 : p ≠ 2 := by
      rintro rfl
      have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    have h2 := hpp.two_le
    exact ⟨by omega, Nat.odd_iff.mp (hpp.odd_of_ne_two hne2)⟩
  by_contra hlt
  have hlt3 : n.primeFactors.card < 3 := Nat.not_le.mp hlt
  have key := perfect_two_mul_prod_pred_le_prod hn0 hperf
  have hpos : 0 < n.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  have hc : n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by omega
  rcases hc with hc | hc
  · -- один простой делитель: 2(p−1) ≤ p при p ≥ 3 невозможно
    obtain ⟨p, hs⟩ := Finset.card_eq_one.mp hc
    have hp := hodd_p p (by rw [hs]; exact Finset.mem_singleton_self p)
    rw [hs, Finset.prod_singleton, Finset.prod_singleton] at key
    omega
  · -- два различных простых делителя: 2(p−1)(q−1) ≤ pq против pq < 2(p−1)(q−1)
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hc
    have hp := hodd_p p (by rw [hs]; exact Finset.mem_insert_self p {q})
    have hq := hodd_p q
      (by rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    rw [hs, Finset.prod_pair hpq, Finset.prod_pair hpq] at key
    exact absurd key
      (Nat.not_le.mpr (two_mul_pred_mul_pred_gt hp.1 hq.1 hpq hp.2 hq.2))

/-! ### Следствия в языке свидетеля OddPerfectNumber -/

/-- Гипотетический нечётный совершенный свидетель не простое число. -/
theorem oddPerfect_not_prime (W : OddPerfectNumber) : ¬ W.1.Prime :=
  fun hp => not_perfect_prime hp W.2.2

/-- Гипотетический нечётный совершенный свидетель не степень простого
    (кандидат вида `p^k` исключён безусловным `not_perfect_prime_pow`). -/
theorem oddPerfect_not_primePow (W : OddPerfectNumber) : ¬ IsPrimePow W.1 := by
  intro h
  obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff _).mp h
  refine not_perfect_prime_pow hp hk.ne' ?_
  rw [heq]
  exact W.2.2

/-- **Три простых делителя нечётного свидетеля (доказано):** всякий
    `W : OddPerfectNumber` имеет ≥ 3 различных простых делителей. Первое
    КАЧЕСТВЕННОЕ (не decide-числовое) зелёное сужение домена свидетеля —
    рядом с числовой границей `oddPerfect_ge_101`. -/
theorem oddPerfect_min_three_prime_factors (W : OddPerfectNumber) :
    3 ≤ W.1.primeFactors.card :=
  odd_perfect_three_le_card_primeFactors W.2.1 W.2.2

#print axioms pred_mul_geomSum_add_one
#print axioms pred_mul_sigma_prime_pow_add_one
#print axioms not_perfect_prime_pow
#print axioms not_perfect_prime
#print axioms perfect_two_mul_prod_pred_le_prod
#print axioms odd_perfect_three_le_card_primeFactors
#print axioms oddPerfect_not_prime
#print axioms oddPerfect_not_primePow
#print axioms oddPerfect_min_three_prime_factors

end EuclidsPath.PerfectNumberBranch
