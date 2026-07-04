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
     · `solution_rank_finite_descent_witness` — не-вакуумность ранг-модели.

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

end EuclidsPath.BealFront
