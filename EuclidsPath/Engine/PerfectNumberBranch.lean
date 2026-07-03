/-
  PerfectNumberBranch — совершенные числа: зелёный Евклид–Эйлер и нечётный свидетель.

  ЗЕЛЁНЫЙ МОДУЛЬ (всё доказано, без sorry/axiom):
    * Евклид (гл. 34 нити «Начал», IX.36): простое Мерсенна ⟹ чётное совершенное —
      perfect_of_mersennePrime / perfect_of_mersennePrime';
    * Эйлер (гл. 43 нити): чётное совершенное ⟹ вид 2^k · (2^(k+1) − 1) с простым
      Мерсенна — evenPerfect_eq. Обе стороны — реэкспорт из mathlib Archive
      (Archive.Wiedijk100Theorems.PerfectNumbers, автор Aaron Anderson, Apache 2.0);
    * поточечная разрешимость совершенности: instance DecidablePred Nat.Perfect,
      perfect_6, perfect_28, not_perfect_945 (машинная проверка);
    * нечётный свидетель: OddPerfectNumber — тип свидетелей открытой проблемы;
      noOddPerfect_iff_no_witness; oddPerfect_ge_101 — любой нечётный совершенный
      свидетель ≥ 101 (машинная проверка малых случаев);
    * мост к MersenneBranch: mersennePrimesInfinite_iff_evenPerfectUnbounded —
      цель-маркер MersennePrimesInfinite ⟺ неограниченность чётных совершенных.

  ⚠️ ЧЕСТНОСТЬ: обе стороны эквивалентности — ОТКРЫТЫЕ проблемы. Зелёное здесь —
  только САМА эквивалентность: вопрос «Начал» о бесконечности чётных совершенных
  чисел = вопрос о бесконечности простых Мерсенна, машинно. Бесконечность простых
  Мерсенна НЕ утверждается (маркер NoMersenneInfinitudeClaimed); существование или
  несуществование нечётного совершенного числа НЕ утверждается — но сам предикат
  поточечно разрешим, и каждый конкретный кандидат проверяется вычислением.
-/
import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers
import EuclidsPath.Engine.MersenneBranch

set_option autoImplicit false

namespace EuclidsPath.PerfectNumberBranch

open EuclidsPath

/-! ### Поточечная разрешимость совершенности -/

/-- Совершенность разрешима: `Nat.Perfect n` — это по определению
    `∑ i ∈ properDivisors n, i = n ∧ 0 < n`, и обе части вычислимы. -/
instance : DecidablePred Nat.Perfect :=
  fun n => decidable_of_iff (∑ i ∈ Nat.properDivisors n, i = n ∧ 0 < n) Iff.rfl

/-- `6 = 2^1 · (2^2 − 1)` — первое совершенное число (машинная проверка). -/
theorem perfect_6 : Nat.Perfect 6 := by decide

/-- `28 = 2^2 · (2^3 − 1)` — второе совершенное число (машинная проверка). -/
theorem perfect_28 : Nat.Perfect 28 := by decide

set_option maxRecDepth 4000 in
/-- `945` — наименьшее нечётное избыточное — не совершенно (машинная проверка). -/
theorem not_perfect_945 : ¬ Nat.Perfect 945 := by decide

/-! ### Нечётный совершенный свидетель -/

/-- Гипотеза «нечётных совершенных чисел нет» (открытая проблема, ВХОД). -/
def NoOddPerfect : Prop := ∀ N : ℕ, Odd N → ¬ Nat.Perfect N

/-- Тип свидетелей открытой проблемы: нечётное совершенное число вместе
    с доказательствами обоих свойств. -/
abbrev OddPerfectNumber : Type := {N : ℕ // Odd N ∧ Nat.Perfect N}

/-- Гипотеза `NoOddPerfect` ⟺ тип свидетелей пуст. -/
theorem noOddPerfect_iff_no_witness :
    NoOddPerfect ↔ ¬ Nonempty OddPerfectNumber := by
  constructor
  · rintro h ⟨⟨N, hodd, hperf⟩⟩
    exact h N hodd hperf
  · intro h N hodd hperf
    exact h ⟨⟨N, hodd, hperf⟩⟩

/-- Любой нечётный совершенный свидетель ≥ 101: все меньшие нечётные числа
    отсеиваются машинной проверкой (поточечная разрешимость в действии). -/
theorem oddPerfect_ge_101 (W : OddPerfectNumber) : 101 ≤ W.1 := by
  obtain ⟨N, hodd, hperf⟩ := W
  show 101 ≤ N
  by_contra h
  exact (by decide : ∀ M, M < 101 → M % 2 = 1 → ¬ Nat.Perfect M) N (by omega)
    (Nat.odd_iff.mp hodd) hperf

/-! ### Евклид: простое Мерсенна ⟹ чётное совершенное (зелёное, «Начала» IX.36) -/

/-- **ЕВКЛИД (доказано, реэкспорт из mathlib Archive):** если `2^(k+1) − 1` просто,
    то `2^k · (2^(k+1) − 1)` совершенно. -/
theorem perfect_of_mersennePrime {k : ℕ} (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) :=
  Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k pr

/-- Евклид в p-форме: при `2 ≤ p` и простом `mersenne p` число
    `2^(p−1) · mersenne p` совершенно. -/
theorem perfect_of_mersennePrime' {p : ℕ} (hp : 2 ≤ p) (pr : (mersenne p).Prime) :
    Nat.Perfect (2 ^ (p - 1) * mersenne p) := by
  have h : p - 1 + 1 = p := by omega
  simpa [h] using perfect_of_mersennePrime (k := p - 1) (by rwa [h])

/-! ### Эйлер: чётное совершенное ⟹ форма Евклида (зелёное) -/

/-- **ЭЙЛЕР (доказано, реэкспорт из mathlib Archive):** каждое чётное совершенное
    число имеет вид `2^k · (2^(k+1) − 1)` с простым множителем Мерсенна. -/
theorem evenPerfect_eq {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf

/-! ### Мост к MersenneBranch: маркер ⟺ неограниченность чётных совершенных -/

/-- Неограниченность чётных совершенных чисел (вопрос «Начал», открыт). -/
def EvenPerfectUnbounded : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Even n ∧ Nat.Perfect n

/-- **МОСТ (доказан):** цель-маркер `MersennePrimesInfinite` из MersenneBranch ⟺
    неограниченность чётных совершенных чисел. Обе стороны открыты; зелёное —
    сама эквивалентность: два вопроса — один и тот же, машинно. -/
theorem mersennePrimesInfinite_iff_evenPerfectUnbounded :
    MersenneBranch.MersennePrimesInfinite ↔ EvenPerfectUnbounded := by
  constructor
  · -- бесконечность простых Мерсенна ⟹ чётные совершенные не ограничены
    intro H N
    obtain ⟨p, hNp, hp, hmp⟩ := H N
    refine ⟨2 ^ (p - 1) * mersenne p, ?_, ?_, perfect_of_mersennePrime' hp.two_le hmp⟩
    · -- N < p < 2^p = 2^(p−1)·2 ≤ 2^(p−1)·mersenne p
      have hm2 : 2 ≤ mersenne p := hmp.two_le
      have hsplit : 2 ^ p = 2 ^ (p - 1) * 2 := by
        conv_lhs => rw [show p = p - 1 + 1 from by omega]
        rw [pow_succ]
      calc N < p := hNp
        _ < 2 ^ p := p.lt_two_pow_self
        _ = 2 ^ (p - 1) * 2 := hsplit
        _ ≤ 2 ^ (p - 1) * mersenne p := Nat.mul_le_mul (Nat.le_refl _) hm2
    · -- p ≥ 2 ⟹ 2^(p−1) чётно ⟹ произведение чётно
      have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
      exact (Nat.even_pow.mpr ⟨even_two, h1⟩).mul_right _
  · -- чётные совершенные не ограничены ⟹ бесконечность простых Мерсенна
    intro H N
    obtain ⟨n, hn, hev, hperf⟩ := H (2 ^ (2 * N + 2))
    obtain ⟨k, hkpr, rfl⟩ := evenPerfect_eq hev hperf
    have hk0 : k ≠ 0 := Theorems100.Nat.ne_zero_of_prime_mersenne k hkpr
    -- показатель k+1 прост (Ферма: простота 2^m − 1 требует простого m)
    have hpow : (2 ^ (k + 1) - 1).Prime := hkpr
    have hkp : (k + 1).Prime :=
      (Nat.prime_of_pow_sub_one_prime (a := 2) (n := k + 1) (by omega) hpow).2
    refine ⟨k + 1, ?_, hkp, hkpr⟩
    -- N < k+1: иначе n = 2^k·(2^(k+1)−1) < 2^(2k+1) ≤ 2^(2N+2) < n
    by_contra hle
    have h1 : mersenne (k + 1) < 2 ^ (k + 1) :=
      Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
    have h2 : 2 ^ k * mersenne (k + 1) < 2 ^ k * 2 ^ (k + 1) :=
      mul_lt_mul_of_pos_left h1 (Nat.two_pow_pos k)
    have h3 : 2 ^ k * 2 ^ (k + 1) = 2 ^ (2 * k + 1) := by
      rw [← pow_add, show k + (k + 1) = 2 * k + 1 from by omega]
    have h4 : 2 ^ (2 * k + 1) ≤ 2 ^ (2 * N + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcontra : (2 : ℕ) ^ (2 * N + 2) < 2 ^ (2 * N + 2) :=
      calc (2 : ℕ) ^ (2 * N + 2) < 2 ^ k * mersenne (k + 1) := hn
        _ < 2 ^ k * 2 ^ (k + 1) := h2
        _ = 2 ^ (2 * k + 1) := h3
        _ ≤ 2 ^ (2 * N + 2) := h4
    exact absurd hcontra (lt_irrefl _)

/-! ### Честность -/

/-- **ЧЕСТНОСТЬ (охват):** бесконечность простых Мерсенна (⟺ неограниченность
    чётных совершенных, мост выше) НЕ утверждается и НЕ доказана — обе стороны
    эквивалентности открыты. Существование нечётного совершенного числа также
    открыто: здесь лишь показано, что свидетель поточечно проверяем и ≥ 101. -/
abbrev NoMersenneInfinitudeClaimed : Prop := True

theorem noMersenneInfinitudeClaimed : NoMersenneInfinitudeClaimed := trivial

#print axioms perfect_of_mersennePrime'
#print axioms not_perfect_945
#print axioms oddPerfect_ge_101
#print axioms evenPerfect_eq
#print axioms mersennePrimesInfinite_iff_evenPerfectUnbounded

end EuclidsPath.PerfectNumberBranch
