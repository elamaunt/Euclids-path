/-
  BealFront — «теневой фронт» гипотез БИЛА и ФЕРМА–КАТАЛАНА, заземлённый на
  РЕАЛЬНО ДОКАЗАННУЮ полиномиальную теорему Ферма–Каталана и на спуск Ферма для
  FLT n = 3 / n = 4 в mathlib. БЕСКОНЕЧНЫЙ СПУСК ФЕРМА — это буквально движок
  этого проекта (невозможность вечного двигателя).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК — ЧТО ЗДЕСЬ ЗЕЛЁНОЕ И ЧТО ЧЕСТНО ОТКРЫТО.          │
  └───────────────────────────────────────────────────────────────────────────┘

  1. ЗЕЛЁНЫЙ ЯКОРЬ (доказано в mathlib, цитируется дословно, НЕ пере-выводится):
     · `Polynomial.flt_catalan` — полиномиальная теорема Ферма–Каталана: при
       `1/p + 1/q + 1/r < 1` (в целочисленной форме `q*r + r*p + p*q ≤ p*q*r`),
       для взаимно простых `a, b` из `C u*a^p + C v*b^q + C w*c^r = 0` следует, что
       `a, b, c` — КОНСТАНТЫ (`natDegree = 0`). Это ДОКАЗАННЫЙ полиномиальный аналог
       Била/Ферма–Каталана; его характеристический бесконечный спуск ЕСТЬ чтение
       движка: нет вечного спуска нетривиальных решений.
     · `fermatLastTheoremFour` и `fermatLastTheoremThree` — доказанные частные
       случаи Великой теоремы Ферма, ПОЛУЧЕННЫЕ методом бесконечного спуска
       (Fermat42 minimal descent в `FLT/Four.lean`) — тот же движок EPMI.

  2. ЗЕЛЁНОЕ ПРОЧТЕНИЕ ДВИЖКА (репозиторий): «descent ⟹ вечный двигатель ⟹ ложь».
     Если бы Бил-подобное решение порождало бесконечный строгий спуск ранга-размера
     решения, это был бы вечный двигатель на ℕ — запрещённый
     `UniversalEngine.no_perpetual_engine_of_natRank` / `EPMI.no_infinite_descent`.
     Это СТРУКТУРНАЯ половина, честно заземлённая (не доказательство Била).

  3. 🔴 ОТКРЫТОЕ (названо, НЕ доказано): целочисленная гипотеза Била и полная
     гипотеза Ферма–Каталана. Дармон–Гранвилль (через Фалтингса) доказали лишь
     КОНЕЧНОСТЬ решений при ФИКСИРОВАННОЙ тройке показателей; полный Бил открыт
     (премия $1M). Здесь эти утверждения — честные `def`-гейты, они НЕ доказаны.

  ЧЕСТНАЯ НОВИЗНА: глубокая математика (полиномиальный Ферма–Каталан, FLT 3/4) —
  это mathlib; вклад модуля — ВЛОЖЕНИЕ этих реальных якорей в язык движка +
  честная демаркация зелёного и открытого. Формализация/унификация, не новая
  глубокая математика. Никакого `sorry`, никакой новой аксиомы, никакого
  `native_decide`; такса репозитория (47) неизменна. Зелёные обёртки — стандартная
  тройка `propext` / `Classical.choice` / `Quot.sound`.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/BealFront.lean → ноль ошибок.

  Родство: EuclidsPath/Engine/UniversalEngine.lean (`no_perpetual_engine_of_natRank`);
    EuclidsPath/Engine/EPMI.lean (`no_infinite_descent`, `DescentStep`);
    Mathlib/NumberTheory/FLT/Polynomial.lean (`Polynomial.flt_catalan`);
    Mathlib/NumberTheory/FLT/Four.lean (`fermatLastTheoremFour`);
    Mathlib/NumberTheory/FLT/Three.lean (`fermatLastTheoremThree`).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine
import EuclidsPath.Engine.EPMI

set_option autoImplicit false

namespace EuclidsPath.BealFront

open Polynomial

/-!
################################################################################
  🟢 ЗЕЛЁНОЕ ЯДРО — спуск Ферма ЕСТЬ движок; полиномиальный аналог ДОКАЗАН.
################################################################################
-/

/-- **🟢 ЗЕЛЁНАЯ ТЕНЬ (доказано, цитата `Polynomial.flt_catalan`):**
    полиномиальная теорема Ферма–Каталана над ЛЮБЫМ полем `k`. При условии
    `1/p + 1/q + 1/r < 1` (целочисленно `q*r + r*p + p*q ≤ p*q*r`), при
    взаимно простых `a, b` и ненулевых коэффициентах уравнение
    `C u*a^p + C v*b^q + C w*c^r = 0` вынуждает `a, b, c` быть КОНСТАНТАМИ.
    Это ДОКАЗАННЫЙ полиномиальный аналог Била/Ферма–Каталана — «зелёная тень».
    Обёртка НЕ добавляет математики: она дословно вызывает mathlib. -/
theorem polynomial_fermat_catalan_shadow
    {k : Type*} [Field k]
    {p q r : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : (p : k) ≠ 0) (chq : (q : k) ≠ 0) (chr : (r : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  Polynomial.flt_catalan hp hq hr hineq chp chq chr ha hb hc hab hu hv hw heq

/-- **🟢 НЕ-ВАКУУМНОСТЬ (свидетель над `ℚ`):** конкретная невырожденная
    инстанция зелёной тени. Возьмём `p = q = r = 3` (тогда
    `q*r + r*p + p*q = 27 = p*q*r`, условие выполнено), поле `ℚ`
    (характеристика 0, все `(3 : ℚ) ≠ 0`). Для любых взаимно простых ненулевых
    `a, b` и ненулевых `c, u, v, w` с `C u*a^3 + C v*b^3 + C w*c^3 = 0`
    получаем, что `a, b, c` — константы. Тень применима, а не пуста. -/
theorem polynomial_fermat_catalan_shadow_cubic
    {a b c : ℚ[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : ℚ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ 3 + C v * b ^ 3 + C w * c ^ 3 = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  polynomial_fermat_catalan_shadow
    (k := ℚ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ha hb hc hab hu hv hw heq

/-- **🟢 РЕАЛЬНЫЙ СПУСК ФЕРМА, n = 4 (доказано, цитата `fermatLastTheoremFour`):**
    ненулевые натуральные `a, b, c` не дают `a^4 + b^4 = c^4`. Доказано в mathlib
    БЕСКОНЕЧНЫМ СПУСКОМ (Fermat42 minimal descent) — тем же движком EPMI, что
    запрещает вечный двигатель. -/
theorem flt_four_is_descent : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

/-- **🟢 РЕАЛЬНЫЙ СПУСК ФЕРМА, n = 3 (доказано, цитата `fermatLastTheoremThree`):**
    ненулевые натуральные `a, b, c` не дают `a^3 + b^3 = c^3`. Тот же движок
    бесконечного спуска. -/
theorem flt_three_is_descent : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/-- **🟢 РАЗВЁРНУТАЯ ФОРМА n = 4:** для ненулевых `a, b, c : ℕ` имеем
    `a^4 + b^4 ≠ c^4`. Прямое чтение доказанного `flt_four_is_descent`. -/
theorem no_fermat_four (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 4 :=
  flt_four_is_descent a b c ha hb hc

/-!
################################################################################
  🟢 ЗЕЛЁНОЕ ПРОЧТЕНИЕ ДВИЖКА: descent-размера решения ⟹ вечный двигатель ⟹ ложь.
################################################################################
-/

/-- Ранг-модель Била: «размер» гипотетической цепи решений — натуральное число.
    `SolutionRank.size` — высота, которую спуск был бы обязан строго уменьшать. -/
structure SolutionRank where
  size : ℕ

/-- **🟢 DESCENT-НЕТ-ДВИГАТЕЛЯ (доказано, коралларий `no_perpetual_engine_of_natRank`):**
    если бы Бил-подобное решение порождало бесконечную цепь `sol : ℕ → SolutionRank`,
    в которой каждый шаг СТРОГО уменьшает `size` (модель бесконечного спуска
    размера решения), это был бы вечный двигатель на ℕ — невозможный. Это
    СТРУКТУРНАЯ половина: она честно не является доказательством Била, а фиксирует,
    что бесконечный спуск решений запрещён тем же движком, что и у Ферма. -/
theorem no_perpetual_solution_descent
    (sol : ℕ → SolutionRank)
    (hchain : ∀ t, (sol (t + 1)).size < (sol t).size) : False := by
  apply EuclidsPath.UniversalEngine.no_perpetual_engine_of_natRank
    (α := SolutionRank) (ρ := SolutionRank.size)
    (r := fun x y => x.size < y.size)
    (fun x y hxy => hxy)
  exact ⟨sol, hchain⟩

/-- **🟢 ЧЕРЕЗ EPMI (доказано, коралларий `EPMI.no_infinite_descent`):** та же
    невозможность в форме clean-descent EPMI. При `A ≥ 1` бесконечная цепь высот
    с шагом `DescentStep A (H t) (H (t+1))` (то есть `A · H(t+1) < H t`) даёт
    ложь — буквально спуск Ферма как невозможность вечного двигателя. -/
theorem no_perpetual_solution_descent_epmi
    {A : ℕ} (hA : 1 ≤ A) (H : ℕ → ℕ)
    (hchain : ∀ t, EuclidsPath.Engine.DescentStep A (H t) (H (t + 1))) : False :=
  EuclidsPath.Engine.no_infinite_descent hA H hchain

/-- **🟢 НЕ-ВАКУУМНОСТЬ ранг-модели:** свидетель убывающей КОНЕЧНОЙ цепи размеров
    (обрывается, а не бесконечна): `sol t = ⟨N - t⟩` строго убывает, пока `t < N`.
    Модель обитаема; движок запрещает именно БЕСКОНЕЧНЫЙ вариант. -/
theorem solution_rank_finite_descent_witness (N : ℕ) :
    ∀ t, t < N → (⟨N - (t + 1)⟩ : SolutionRank).size < (⟨N - t⟩ : SolutionRank).size := by
  intro t ht
  show N - (t + 1) < N - t
  omega

/-!
################################################################################
  🔴 ЧЕСТНЫЕ ГЕЙТЫ — ОТКРЫТЫЕ утверждения, НЕ доказаны (это `def`-Props).
################################################################################
-/

/-- 🔴 **Гипотеза Била (ОТКРЫТА, премия $1M).** Если `A^x + B^y = C^z` с
    положительными `A, B, C`, показателями `x, y, z > 2` и попарно взаимно
    простыми `A, B, C`, то такого решения НЕ существует (взаимная простота ведёт
    к противоречию). Эквивалентно: любое решение с `x, y, z > 2` вынуждает `A, B, C`
    иметь общий простой делитель. НЕ доказана; здесь лишь честно НАЗВАНА. -/
def BealConjecture : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z →
    Nat.Coprime A B → Nat.Coprime B C → Nat.Coprime A C → False

/-- 🔴 **Гипотеза Ферма–Каталана (ОТКРЫТА, каноническая форма).** Множество
    ТРОЕК СТЕПЕНЕЙ `(a^x, b^y, c^z)` — именно значений, не кортежей параметров —
    взаимно простых положительных `a, b, c` с показателями при
    `1/x + 1/y + 1/z < 1` (целочисленно `y*z + z*x + x*y < x*y*z`) и
    `a^x + b^y = c^z`, КОНЕЧНО. Известно ровно 10 решений (наименьшее —
    `1 + 2^3 = 3^2`); Дармон–Гранвилль доказали конечность лишь при
    ФИКСИРОВАННОЙ тройке показателей (через Фалтингса); равномерная конечность
    открыта. НЕ доказана; честно НАЗВАНА. (Почему значения, а не кортежи —
    см. `fermatCatalan_tupleForm_refuted` ниже.) -/
def FermatCatalanConjecture : Prop :=
  {t : ℕ × ℕ × ℕ |
      ∃ a b c x y z : ℕ, t = (a ^ x, b ^ y, c ^ z) ∧
        0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
        y * z + z * x + x * y < x * y * z ∧
        Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
        a ^ x + b ^ y = c ^ z}.Finite

/-- Прежняя (наивная) запись гейта: конечность множества 6-КОРТЕЖЕЙ
    `(a, b, c, x, y, z)`. Оставлена под отдельным именем как урок формализации —
    она ЛОЖНА (см. `fermatCatalan_tupleForm_refuted`). -/
def FermatCatalanTupleForm : Prop :=
  {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
      ∃ a b c x y z : ℕ, t = (a, b, c, x, y, z) ∧
        0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
        y * z + z * x + x * y < x * y * z ∧
        Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
        a ^ x + b ^ y = c ^ z}.Finite

/-- 🟢 **УРОК ФОРМАЛИЗАЦИИ: кортежная форма гейта ЛОЖНА.** Семейство
    `1^(m+7) + 2^3 = 3^2` (взаимная простота очевидна, условие показателей
    выполнено при всех m) даёт бесконечно много РАЗНЫХ 6-кортежей — при том,
    что тройка значений одна: `(1, 8, 9)`. Гейт обязан считать значения. -/
theorem fermatCatalan_tupleForm_refuted : ¬ FermatCatalanTupleForm := by
  intro hfin
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => ((1 : ℕ), (2 : ℕ), (3 : ℕ), m + 7, (3 : ℕ), (2 : ℕ)))
    ?_ ?_ hfin
  · intro m₁ m₂ h
    have h4 := congrArg (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2.2.1) h
    simp only [] at h4
    omega
  · intro m
    exact ⟨1, 2, 3, m + 7, 3, 2, rfl,
      one_pos, by omega, by omega, by omega, by omega, by omega,
      by omega,
      Nat.coprime_one_left 2, by decide, Nat.coprime_one_left 3,
      by simp⟩

/-- **🟢 ЧЕСТНОСТЬ ОХВАТА:** мы НЕ утверждаем и НЕ доказываем `BealConjecture` или
    `FermatCatalanConjecture` — это `def`-гейты. Доказаны только полиномиальная тень
    (`polynomial_fermat_catalan_shadow`) и реальный спуск Ферма n = 3/4
    (`flt_three_is_descent`, `flt_four_is_descent`), плюс структурная невозможность
    вечного спуска. Маркер охвата фиксирует границу честности. -/
abbrev NotAProofOfBeal : Prop := True

theorem notAProofOfBeal : NotAProofOfBeal := trivial

/-!
################################################################################
  🟢 ЗЕЛЁНЫЕ КЛАССЫ ПОКАЗАТЕЛЕЙ БИЛА — диагонали (3,3,3) и (4,4,4) закрыты.
################################################################################
-/

/-- **🟢 ЗЕЛЁНЫЙ КЛАСС БИЛА (3,3,3):** при показателях `x = y = z = 3` решений
    уравнения Била НЕТ ВООБЩЕ — даже без взаимной простоты: `A^3 + B^3 = C^3`
    невозможно для положительных `A, B, C`. Прямой вывод из
    `flt_three_is_descent` (спуск Ферма, mathlib). В частности, диагональный
    класс гейта `BealConjecture` при `(3,3,3)` зелёный: взаимно простых решений
    нет, потому что нет никаких. -/
theorem beal_no_solution_exponent_three
    (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (heq : A ^ 3 + B ^ 3 = C ^ 3) : False :=
  flt_three_is_descent A B C hA.ne' hB.ne' hC.ne' heq

/-- **🟢 ЗЕЛЁНЫЙ КЛАСС БИЛА (4,4,4):** при показателях `x = y = z = 4` решений
    нет вообще (из `flt_four_is_descent` — исторический бесконечный спуск Ферма).
    Диагональный класс гейта `BealConjecture` при `(4,4,4)` зелёный, взаимная
    простота не нужна. -/
theorem beal_no_solution_exponent_four
    (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (heq : A ^ 4 + B ^ 4 = C ^ 4) : False :=
  flt_four_is_descent A B C hA.ne' hB.ne' hC.ne' heq

/-!
################################################################################
  🟢 НЕВАКУУМНЫЕ СВИДЕТЕЛИ ГЕЙТОВ — множество обитаемо, гипотеза простоты несуща.
################################################################################
-/

/-- **🟢 НЕ-ВАКУУМНОСТЬ FC-ГЕЙТА:** тройка ЗНАЧЕНИЙ `(1, 8, 9)` — наименьшее
    решение Ферма–Каталана `1^7 + 2^3 = 3^2` — принадлежит множеству, конечность
    которого утверждает `FermatCatalanConjecture` (тот же сет-литерал дословно).
    Показатели `(x, y, z) = (7, 3, 2)`: `y·z + z·x + x·y = 41 < 42 = x·y·z`,
    попарная взаимная простота оснований `1, 2, 3` очевидна. Гейт говорит о
    НЕПУСТОМ множестве — вопрос о его конечности не вакуумен. -/
theorem fermatCatalan_value_witness :
    ((1, 8, 9) : ℕ × ℕ × ℕ) ∈
      {t : ℕ × ℕ × ℕ |
        ∃ a b c x y z : ℕ, t = (a ^ x, b ^ y, c ^ z) ∧
          0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
          y * z + z * x + x * y < x * y * z ∧
          Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
          a ^ x + b ^ y = c ^ z} :=
  ⟨1, 2, 3, 7, 3, 2, by norm_num,
    one_pos, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num,
    Nat.coprime_one_left 2, by decide, Nat.coprime_one_left 3,
    by norm_num⟩

/-- **🟢 ГИПОТЕЗА ВЗАИМНОЙ ПРОСТОТЫ — НЕСУЩАЯ:** без неё Бил-уравнение обитаемо:
    `2^3 + 2^3 = 2^4` (то есть 8 + 8 = 16) с показателями `x = y = 3 > 2`,
    `z = 4 > 2` и ОБЩИМ ДЕЛИТЕЛЕМ 2 у всех трёх оснований. Условие взаимной
    простоты в `BealConjecture` — не украшение: убрать его нельзя, контрпример
    предъявлен. -/
theorem beal_common_factor_witness :
    ∃ A B C x y z : ℕ,
      0 < A ∧ 0 < B ∧ 0 < C ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      A ^ x + B ^ y = C ^ z ∧
      ¬ Nat.Coprime A B ∧ 2 ∣ A ∧ 2 ∣ B ∧ 2 ∣ C :=
  ⟨2, 2, 2, 3, 3, 4, by decide⟩

/-!
################################################################################
  🟢 ПОЛИНОМИАЛЬНЫЙ БИЛ — именованная тень (все показатели ≥ 3, поле char 0).
################################################################################
-/

/-- **🟢 АРИФМЕТИКА БИЛ-ПОКАЗАТЕЛЕЙ:** при `3 ≤ p, q, r` выполнено
    FC-условие `q·r + r·p + p·q ≤ p·q·r` — каждое слагаемое слева не превышает
    трети правой части. Именно это неравенство отделяет Бил-показатели от
    сферических/эллиптических троек. -/
theorem fc_ineq_of_three_le {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    q * r + r * p + p * q ≤ p * q * r := by
  have h1 : 3 * (q * r) ≤ p * (q * r) := Nat.mul_le_mul hp le_rfl
  have h2 : 3 * (r * p) ≤ q * (r * p) := Nat.mul_le_mul hq le_rfl
  have h3 : 3 * (p * q) ≤ r * (p * q) := Nat.mul_le_mul hr le_rfl
  nlinarith [h1, h2, h3]

/-- **🟢 ПОЛИНОМИАЛЬНЫЙ БИЛ (доказано; специализация `Polynomial.flt_catalan`
    при `u = v = 1, w = −1`):** над полем характеристики 0 из `a^x + b^y = c^z`
    при взаимно простых `a, b`, ненулевых `a, b, c` и показателях
    `x, y, z ≥ 3` следует, что `a, b, c` — КОНСТАНТЫ. Буквально «теорема Била
    над `k[X]»`: нетривиальных полиномиальных решений нет. ЧЕСТНОСТЬ:
    целочисленный Бил отсюда НЕ следует (полиномиальная тень, не решение
    гейта); равные показатели `x = y = z = n ≥ 3` дают полиномиальный FLT
    как частный случай. -/
theorem polynomial_beal_shadow
    {k : Type*} [Field k] [CharZero k]
    {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ x + b ^ y = c ^ z) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have h0 : C (1 : k) * a ^ x + C (1 : k) * b ^ y + C (-1 : k) * c ^ z = 0 := by
    simp only [map_one, map_neg, one_mul, neg_one_mul]
    rw [heq]; ring
  exact polynomial_fermat_catalan_shadow (k := k)
    (p := x) (q := y) (r := z) (u := (1 : k)) (v := (1 : k)) (w := (-1 : k))
    (by omega) (by omega) (by omega)
    (fc_ineq_of_three_le hx hy hz)
    (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega))
    ha hb hc hab
    one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    h0

/-!
################################################################################
  ЭПИСТЕМИЧЕСКАЯ СВЯЗКА БИЛА — ФОРМА КОЛЛАТЦА, ЧЕСТНО ФОРМАЛЬНАЯ.
################################################################################
-/

/-- **Внутреннее самообоснование Била — форма Коллатца, ЧЕСТНО ФОРМАЛЬНАЯ.**
    Несёт сам гейт (`ground : BealConjecture`) и свидетельство собственной
    запредельности (`beyondOwnHorizon : ¬ BealConjecture`).

    ГРОМКАЯ ЧЕСТНОСТЬ (обязательная, по вердикту скептика «завышена на
    полступени»): это буквально пара `P` / `¬P` — та же вырожденная форма, что
    `InternalisedCollatzGround`, и НИЖЕ P/NP-механики (`InternalisedPNPGround`,
    где `beyondOwnHorizon` — независимо оплаченный зелёный факт). ОПЛАТЫ
    ДВИГАТЕЛЬНЫМ ФАКТОМ ЗДЕСЬ НЕТ И БЫТЬ НЕ МОЖЕТ в известной математике:
    опровержение Била — одиночный контрпример `(A, B, C, x, y, z)`, конечная
    точка; он не порождает ни нисходящей цепи (спуска Ферма для общего Била не
    существует), ни неограниченной поставки — если что и возникает, то
    ВОСХОДЯЩИЙ побег размеров, а не спуск, и стена
    `no_perpetual_solution_descent` его не кусает. Связка формальна;
    содержательное — РЯДОМ, отдельными теоремами: полиномиальная тень
    `polynomial_beal_shadow` и зелёные диагональные классы
    `beal_no_solution_exponent_three` / `beal_no_solution_exponent_four`. -/
structure InternalisedBealGround : Prop where
  ground : BealConjecture
  beyondOwnHorizon : ¬ BealConjecture

/-- «Внутреннее знание причины Била» = внутреннее самообоснование гейта
    (зеркало `InternalKnowledgeOfCollatzCause`; та же честная оговорка). -/
abbrev InternalKnowledgeOfBealCause : Prop := InternalisedBealGround

/-- Самообоснование самоуничтожается — ПО ФОРМЕ
    (`fun H => H.beyondOwnHorizon H.ground`), как у Коллатца; двигательной
    оплаты честно НЕТ — см. докстроку `InternalisedBealGround`. ЗЕЛЁНАЯ;
    из аксиом — только `propext` (тянется через `Nat.Coprime` внутри гейта
    `BealConjecture`), ни `Classical.choice`, ни `Quot.sound`. -/
theorem no_internalisedBealGround : InternalisedBealGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — теорема ФОРМЫ** (зеркало
    `collatzCause_unknowable`): внутреннее самообоснование Била невозможно.
    ЧЕСТНОСТЬ: в отличие от `pnpCause_unknowable`, противоречие не оплачено
    пижонхолом/поставкой — это формальная связка; её содержательные соседи —
    `polynomial_beal_shadow` и классы (3,3,3)/(4,4,4). НЕ Гёдель и НЕ решение
    Била. -/
theorem bealCause_unknowable : ¬ InternalKnowledgeOfBealCause :=
  no_internalisedBealGround

/-!
################################################################################
  ИТОГ (LOUD HONEST): что зелёное, что переиспользовано, что ОТКРЫТО.
################################################################################

  🟢 ЗЕЛЁНОЕ (доказано машинно в этом модуле — обёртки/корралларии):
     · `polynomial_fermat_catalan_shadow` — дословная цитата `Polynomial.flt_catalan`
       (ДОКАЗАННЫЙ полиномиальный Ферма–Каталан);
     · `polynomial_fermat_catalan_shadow_cubic` — не-вакуумная инстанция над `ℚ`;
     · `flt_four_is_descent` / `flt_three_is_descent` — цитаты `fermatLastTheoremFour`
       / `fermatLastTheoremThree` (ДОКАЗАНЫ бесконечным спуском);
     · `no_fermat_four` — развёрнутая форма n = 4;
     · `no_perpetual_solution_descent` — коралларий `no_perpetual_engine_of_natRank`;
     · `no_perpetual_solution_descent_epmi` — коралларий `EPMI.no_infinite_descent`;
     · `solution_rank_finite_descent_witness` — не-вакуумность ранг-модели;
     · `beal_no_solution_exponent_three` / `beal_no_solution_exponent_four` —
       зелёные диагональные классы Била (3,3,3)/(4,4,4): решений нет вовсе,
       взаимная простота не нужна (спуск Ферма);
     · `fermatCatalan_value_witness` — FC-гейт не вакуумен: (1,8,9) = 1^7+2^3=3^2
       лежит в множестве значений;
     · `beal_common_factor_witness` — гипотеза взаимной простоты несуща:
       2^3+2^3=2^4 с общим делителем 2;
     · `fc_ineq_of_three_le` + `polynomial_beal_shadow` — «теорема Била над k[X]»
       (специализация `flt_catalan`, u=v=1, w=−1, char 0);
     · `no_internalisedBealGround` / `bealCause_unknowable` — эпистемическая
       СВЯЗКА-ФОРМА (честно: пара ground/¬ground БЕЗ двигательной оплаты, форма
       Коллатца, ниже P/NP-механики — см. докстроку `InternalisedBealGround`).

  🟢 ПЕРЕИСПОЛЬЗОВАНО (цитируется, НЕ пере-выводится):
     · `Polynomial.flt_catalan` (полиномиальный Ферма–Каталан, mathlib);
     · `fermatLastTheoremFour` / `fermatLastTheoremThree` (FLT спуском, mathlib);
     · `UniversalEngine.no_perpetual_engine_of_natRank`, `EPMI.no_infinite_descent`.

  🔴 ОТКРЫТО (названо, НЕ доказано — `def`-гейты):
     · `BealConjecture` — целочисленная гипотеза Била (премия $1M);
     · `FermatCatalanConjecture` — полная (равномерная) гипотеза Ферма–Каталана
       (Дармон–Гранвилль: лишь конечность при ФИКСИРОВАННЫХ показателях).

  ЧЕСТНАЯ НОВИЗНА: глубокая математика — mathlib; вклад — вложение реальных якорей
  в язык движка и честная демаркация. НЕ доказательство Била. Никакого `sorry`,
  никакой новой аксиомы, никакого `native_decide`; такса 47 неизменна.
-/

#print axioms polynomial_fermat_catalan_shadow
#print axioms fermatCatalan_tupleForm_refuted
#print axioms polynomial_fermat_catalan_shadow_cubic
#print axioms flt_four_is_descent
#print axioms flt_three_is_descent
#print axioms no_fermat_four
#print axioms no_perpetual_solution_descent
#print axioms no_perpetual_solution_descent_epmi
#print axioms solution_rank_finite_descent_witness
#print axioms beal_no_solution_exponent_three
#print axioms beal_no_solution_exponent_four
#print axioms fermatCatalan_value_witness
#print axioms beal_common_factor_witness
#print axioms fc_ineq_of_three_le
#print axioms polynomial_beal_shadow
#print axioms no_internalisedBealGround
#print axioms bealCause_unknowable

end EuclidsPath.BealFront
