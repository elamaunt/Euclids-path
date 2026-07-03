/-
  ChowlaFront — «инженерная тень» гипотез ЧАУЛЫ и САРНАКА, заземлённая на РЕАЛЬНОЙ функции
  Лиувилля `λ = (−1)^Ω` и на узле чётности-ранга проекта.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК. ЧТО ЗДЕСЬ ЗЕЛЁНОЕ И ЧТО ЧЕСТНО ОСТАЁТСЯ ОТКРЫТЫМ. │
  └───────────────────────────────────────────────────────────────────────────┘

  ИНЖЕНЕРНАЯ ТЕНЬ ЧАУЛЫ — ЭТО САМ УЗЕЛ ЧЁТНОСТИ-РАНГА. Лиувилль `λ(n) = (−1)^Ω(n)` — это НАШ
  инвариант чётности ранга (`Ω = cardFactors = rank` у RankNode, см. `RiemannLiouville`). Гипотеза
  Чаулы утверждает, что эта чётность НЕ КОРРЕЛИРУЕТ поперёк сдвигов: знак `λ(n)` и знак `λ(n+h)`
  ведут себя «как независимые», их произведение суммируется в `o(x)`. Это ровно та же стена «чётность
  ранга не имеет права схлопнуться в одно значение», что стоит за близнецами и за Риманом. Здесь мы
  переиспользуем `RiemannLiouville` (флип знака при умножении на простое, `λ² = 1`, диагональная
  корреляция) и предъявляем ЧЕСТНЫЙ красный вход — сама оценка `o(x)` (Чаула) и Сарнак.

  🟢 ЗЕЛЁНОЕ (машинно, в этом файле, над РЕАЛЬНОЙ `ArithmeticFunction.liouville`):
   · `liouvilleSum` — суммирующая функция `L(x) = Σ_{n≤x} λ(n)` (тот же объект, что `RiemannLiouville.L`,
     здесь переизложен под именем корреляции сдвига 0).
   · `chowlaCorrelation h x` — двухточечная корреляция `Σ_{n≤x} λ(n)·λ(n+h)` над РЕАЛЬНОЙ `λ`.
   · `liouville_sq_eq_one` — `λ(n)² = 1` для `n ≠ 0` (знак `±1`): совершенная САМОкорреляция.
   · `chowla_zero_shift` — при сдвиге `h = 0` корреляция есть `Σ λ(n)²` (диагональ).
   · `chowlaCorrelation_zero_eq_card` — диагональ равна `x`: `chowlaCorrelation 0 x = x`. Совершенная
     самокорреляция чётности ранга (каждый терм `λ(n)² = 1` на `Icc 1 x`).
   · `chowla_parity_flip` — переизложение `RiemannLiouville.liouville_flip_of_mul_prime`: умножение
     аргумента на простое ФЛИПАЕТ `λ`. Это узел чётности-ранга (`deleteFactor`, `r → r−1`) в терминах `λ`.

  🔴 ЧЕСТНО ОТКРЫТОЕ (НЕ доказано здесь; названные предикаты, НЕ теоремы, НЕ `sorry`, НЕ аксиома):
   · `ChowlaConjecture` — гипотеза Чаулы (двухточечная форма): сдвинутая корреляция Лиувилля есть
     `o(x)`. ГЕНУИННО ОТКРЫТА. Тао доказал ЛИШЬ логарифмически-усреднённую версию (Chowla, 2016) и
     нечётные моменты (odd-order, Tao–Teräväinen 2017) — полная (неусреднённая) Чаула ОТКРЫТА. Мы это
     говорим прямо и НЕ выдаём усреднённый результат за полный.
   · `SarnakConjecture` — гипотеза Сарнака: ортогональность Мёбиуса `μ` любой ограниченной
     последовательности нулевой энтропии. Названа абстрактно над РЕАЛЬНОЙ `ArithmeticFunction.moebius`.
     ОТКРЫТА (известно: Чаула ⟹ Сарнак; обратное открыто; полная Сарнак не доказана).

  ЧЕСТНАЯ НОВИЗНА. Гипотеза Чаулы НИГДЕ не формализована. Здесь — ПЕРВОЕ структурное прочтение
  «Чаула = узел чётности-ранга не коррелирует поперёк сдвигов», ЗАЗЕМЛЁННОЕ на РЕАЛЬНОЙ `λ`/`μ` mathlib.
  ЭТО НЕ ДОКАЗАТЕЛЬСТВО ЧАУЛЫ И НЕ ДОКАЗАТЕЛЬСТВО САРНАКА.

  Никакого `sorry`, никакого `admit`, никакого `native_decide`, никакой новой аксиомы. Зелёные
  грузонесущие — стандартная тройка `propext` / `Classical.choice` / `Quot.sound`. Такса репозитория
  (47) этим файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/ChowlaFront.lean → ноль ошибок.

  Родство: EuclidsPath/Engine/RiemannLiouville.lean (`liouville_eq_neg_one_pow_rank`,
    `liouville_flip_of_mul_prime`, `L`); EuclidsPath/Engine/UniversalEngine.lean (движок/ранг).
-/
import Mathlib
import EuclidsPath.Engine.RiemannLiouville
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.ChowlaFront

open ArithmeticFunction

/-! ### 🟢 Зелёное ядро: РЕАЛЬНАЯ `λ` и узел чётности-ранга -/

/-- Суммирующая функция Лиувилля `L(x) = Σ_{n=1}^{x} λ(n)` (= сдвиг `h = 0` без квадрата;
    тот же объект, что `RiemannLiouville.L`). -/
def liouvilleSum (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.liouville n

/-- Двухточечная корреляция Лиувилля `Σ_{n=1}^{x} λ(n)·λ(n+h)` над РЕАЛЬНОЙ `λ`. Гипотеза Чаулы
    утверждает, что при `h > 0` эта сумма есть `o(x)`. -/
def chowlaCorrelation (h x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h)

/-- **`λ(n)² = 1` для `n ≠ 0` (знак `±1`).** Совершенная САМОкорреляция: чётность ранга, возведённая
    в квадрат, всегда `1`. Из `λ(n) = (−1)^Ω(n)` (mathlib `liouville_apply`). -/
theorem liouville_sq_eq_one {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.liouville n * ArithmeticFunction.liouville n = 1 := by
  rw [liouville_apply hn, ← pow_add, ← two_mul, pow_mul]
  simp

/-- **Сдвиг `h = 0` — это диагональ `Σ λ(n)²`.** Двухточечная корреляция при нулевом сдвиге
    вырождается в сумму квадратов Лиувилля. -/
theorem chowla_zero_shift (x : ℕ) :
    chowlaCorrelation 0 x
      = ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.liouville n ^ 2 := by
  unfold chowlaCorrelation
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Nat.add_zero, sq]

/-- **Диагональ равна `x`: `chowlaCorrelation 0 x = x`.** Совершенная самокорреляция чётности ранга:
    каждый терм `λ(n)² = 1` на диапазоне `Icc 1 x` (там `n ≥ 1 ≠ 0`), а их `x` штук. Это резкий
    контраст с гипотезой Чаулы для `h > 0` (там сумма обязана быть `o(x)`). -/
theorem chowlaCorrelation_zero_eq_card (x : ℕ) :
    chowlaCorrelation 0 x = (x : ℤ) := by
  have hpt : ∀ n ∈ Finset.Icc 1 x,
      ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + 0) = (1 : ℤ) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    rw [Nat.add_zero]
    exact liouville_sq_eq_one hn0
  unfold chowlaCorrelation
  rw [Finset.sum_congr rfl hpt, Finset.sum_const]
  simp [Nat.card_Icc]

/-- **Флип чётности при умножении на простое (узел чётности-ранга в терминах `λ`).** Переизложение
    `RiemannLiouville.liouville_flip_of_mul_prime`: умножение аргумента на простое `p` ФЛИПАЕТ знак
    Лиувилля, `λ(p·m) = −λ(m)`. Это ровно `RankNode.deleteFactor` (`r → r−1`), делающий шаг спуска в
    чётности ранга. Именно ЭТУ управляемую динамику знака Чаула запрещает коррелировать поперёк
    сдвигов. -/
theorem chowla_parity_flip {p m : ℕ} (hp : p.Prime) :
    ArithmeticFunction.liouville (p * m) = - ArithmeticFunction.liouville m :=
  EuclidsPath.RiemannLiouville.liouville_flip_of_mul_prime hp

/-- Связь с `RiemannLiouville.L`: наша `liouvilleSum` — тот же объект. -/
theorem liouvilleSum_eq_L (x : ℕ) :
    liouvilleSum x = EuclidsPath.RiemannLiouville.L x := rfl

/-! ### 🔴 Честные красные входы: НАЗВАННЫЕ предикаты над РЕАЛЬНОЙ `λ`/`μ`, НЕ теоремы -/

/-- 🔴 **Гипотеза Чаулы (двухточечная форма).** Сдвинутая корреляция Лиувилля есть `o(x)`: для любого
    `h > 0` и любого `ε > 0` найдётся порог `X`, за которым `|Σ_{n≤x} λ(n)λ(n+h)| ≤ ε·x`. ОТКРЫТА.
    (Тао 2016 доказал ЛИШЬ логарифмически-усреднённую версию; полная неусреднённая Чаула — открыта.)
    Это НАЗВАННЫЙ предикат над РЕАЛЬНОЙ `chowlaCorrelation`, а НЕ теорема. -/
def ChowlaConjecture : Prop :=
  ∀ h : ℕ, 0 < h → ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    |(chowlaCorrelation h x : ℝ)| ≤ ε * (x : ℝ)

/-- 🔴 **Гипотеза Сарнака (ортогональность Мёбиуса нулевой энтропии).** Для любой ограниченной
    последовательности `a : ℕ → ℝ` (константа границы `B`), которая «нулевой энтропии» в смысле
    заданного предиката `zeroEntropy`, средняя корреляция Мёбиуса `μ` с `a` стремится к нулю:
    `(1/x)·Σ_{n≤x} μ(n)·a(n) → 0`. Абстрактный НАЗВАННЫЙ предикат над РЕАЛЬНОЙ
    `ArithmeticFunction.moebius`; свойство «нулевой энтропии» оставлено параметром `zeroEntropy` —
    честно не вшито (динамическая часть — вне арифметики). ОТКРЫТА (Чаула ⟹ Сарнак; полная Сарнак не
    доказана). Это предикат, а НЕ теорема. -/
def SarnakConjecture (zeroEntropy : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a : ℕ → ℝ, zeroEntropy a → (∃ B : ℝ, ∀ n : ℕ, |a n| ≤ B) →
    ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      |(∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) * a n)| ≤ ε * (x : ℝ)

/-! ### Аудит аксиом зелёных грузонесущих -/

#print axioms liouville_sq_eq_one
#print axioms chowla_zero_shift
#print axioms chowlaCorrelation_zero_eq_card
#print axioms chowla_parity_flip
#print axioms liouvilleSum_eq_L

end EuclidsPath.ChowlaFront
