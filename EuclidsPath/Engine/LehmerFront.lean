/-
  LehmerFront — «инженерная тень» гипотезы ЛЕМЕРА (мера Малера).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК. ЧТО ЗДЕСЬ ЗЕЛЁНОЕ И ЧТО ЧЕСТНО ОСТАЁТСЯ ОТКРЫТЫМ. │
  └───────────────────────────────────────────────────────────────────────────┘

  РОЛЬ ДВИГАТЕЛЯ ЗДЕСЬ — ТА ЖЕ, ЧТО В BSD. Мера Малера `mahlerMeasure` целочисленного
  многочлена — это ВЫСОТА. Конечность Норткотта (ДОКАЗАНА в mathlib!) —
  `Polynomial.finite_mahlerMeasure_le`: при ОГРАНИЧЕННОЙ степени и ОГРАНИЧЕННОЙ мере Малера
  целочисленных многочленов ЛИШЬ КОНЕЧНОЕ ЧИСЛО. Это ровно «высота фундирована = нет
  бесконечного высотного спуска» — ТОТ ЖЕ инструментарий, что у BSD и `UniversalEngine`
  (Морделл–Вейль через инфинитный спуск Ферма). Никакого нового высотного механизма мы не
  изобретаем: мы ЦИТИРУЕМ реальную теорему Норткотта.

  🟢 ЗЕЛЁНОЕ (машинно, в этом файле; ГРУЗОНЕСУЩИЕ цитируют РЕАЛЬНЫЕ теоремы mathlib):
   · `mahler_northcott_shadow` := `Polynomial.finite_mahlerMeasure_le` — ЦИТИРУЕМ ДОКАЗАННУЮ
     конечность Норткотта: ограниченная степень + ограниченная мера Малера ⟹ конечно много
     целочисленных многочленов. Это «высота фундирована, спуск терминируется» — движковое
     прочтение. `Mathlib/NumberTheory/MahlerMeasure.lean`.
   · `kronecker_boundary` := `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one` — ЦИТИРУЕМ
     содержание Кронекера: мера Малера = 1 ⟹ все ненулевые комплексные корни суть корни из
     единицы (граница круговых многочленов). Это ГРАНИЦА Лемера при M=1.
   · `kronecker_cyclotomic_dvd` := `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one` —
     тот же Кронекер в форме делимости на круговой многочлен.
   · `mahler_lower_bound` := `Polynomial.one_le_mahlerMeasure_of_ne_zero` — нижняя грань
     `1 ≤ mahlerMeasure` для ненулевого целочисленного многочлена (пол круга Лемера).
   · `cyclotomic_mahler_one` := `Polynomial.cyclotomic_mahlerMeasure_eq_one` — мера Малера
     кругового многочлена равна 1 (насыщение границы Кронекера).
   · `lehmer_descent_has_no_engine` — движковый КОРОЛЛАРИЙ: на любой высотной модели с
     ℕ-высотой (полученной из меры Малера) бесконечный строго нисходящий спуск НЕВОЗМОЖЕН.
     Переиспользует `UniversalEngine.no_perpetual_engine_of_natRank`. Заземлено на
     `finite_mahlerMeasure_le` идейно (конечность = нет спуска); машинно — тот же движок ранга.

  🔴 ЧЕСТНО ОТКРЫТОЕ (НЕ доказано здесь; движок его НЕ закрывает):
   · `LehmerConjecture` — САМА ГИПОТЕЗА ЛЕМЕРА: ∃ c>1 такое, что всякий НЕ-круговой
     целочисленный многочлен имеет меру Малера ≥ c. Кронекер закрывает ГРАНИЦУ M=1
     (мера Малера = 1 ⟺ круговой/корни из единицы); РАЗРЫВ выше 1 — равномерная константа
     c>1 — ОТКРЫТ. Наименьшее известное значение — число Лемера ≈ 1.17628. Это ОТКРЫТЫЙ ВХОД
     (named predicate над РЕАЛЬНОЙ `mahlerMeasure`), мы его НЕ доказываем.

  ЧЕСТНАЯ НОВИЗНА. Мы нигде не формализуем ни гипотезу Лемера, ни разрыв c>1. Мы ПРЕДЪЯВЛЯЕМ
  структурное прочтение «мера Малера = высота, Норткотт = фундированность = нет высотного
  спуска», ЗАЗЕМЛЁННОЕ на РЕАЛЬНЫХ теоремах `finite_mahlerMeasure_le` (Норткотт) и
  `pow_eq_one_of_mahlerMeasure_eq_one` (Кронекер). ЭТО НЕ ДОКАЗАТЕЛЬСТВО ЛЕМЕРА.

  Никакого `sorry`, никакого `admit`, никакого `native_decide`, никакой новой аксиомы.
  Зелёные грузонесущие — стандартная тройка `propext` / `Classical.choice` / `Quot.sound`.
  Такса репозитория (47) этим файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LehmerFront.lean → ноль ошибок.

  Родство: EuclidsPath/Engine/UniversalEngine.lean (`PerpetualEngine`, `of_natRank`);
    EuclidsPath/Engine/BSDFront.lean (тот же высотно-спусковой движок = Норткотт).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.LehmerFront

open Polynomial
open EuclidsPath.UniversalEngine

/-! ################################################################################
    §1  🟢 ЗЕЛЁНОЕ ЯДРО: Норткотт (конечность = нет высотного спуска) + Кронекер (граница)
    ################################################################################ -/

/-- 🟢 ТЕНЬ НОРТКОТТА (грузонесущее — ЦИТИРУЕМ ДОКАЗАННУЮ теорему mathlib).
    При ограниченной степени `n` и ограниченной мере Малера `B` целочисленных многочленов
    ЛИШЬ КОНЕЧНОЕ ЧИСЛО. Это машинная форма «высота фундирована, высотный спуск
    терминируется» — тот же инструментарий, что у BSD/`UniversalEngine`. -/
theorem mahler_northcott_shadow (n : ℕ) (B : NNReal) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} :=
  Polynomial.finite_mahlerMeasure_le n B

/-- 🟢 ГРАНИЦА КРОНЕКЕРА (грузонесущее — ЦИТИРУЕМ ДОКАЗАННУЮ теорему mathlib).
    Если мера Малера целочисленного многочлена равна 1, то всякий его НЕНУЛЕВОЙ комплексный
    корень есть корень из единицы. Это граница круговых многочленов при M=1 — то место, где
    гипотеза Лемера ЗАКРЫТА. -/
theorem kronecker_boundary {p : ℤ[X]}
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)
    {z : ℂ} (hz₀ : z ≠ 0) (hz : z ∈ p.aroots ℂ) :
    ∃ n, 0 < n ∧ z ^ n = 1 :=
  Polynomial.pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz

/-- 🟢 ГРАНИЦА КРОНЕКЕРА в форме делимости (грузонесущее — ЦИТИРУЕМ mathlib).
    Ненулевой некруговой целочисленный многочлен меры Малера 1 (не кратный `X`, степени ≠ 0)
    ДЕЛИТСЯ на круговой многочлен. -/
theorem kronecker_cyclotomic_dvd {p : ℤ[X]}
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)
    (hX : ¬ X ∣ p) (hpdeg : p.degree ≠ 0) :
    ∃ n, 0 < n ∧ cyclotomic n ℤ ∣ p :=
  Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one h hX hpdeg

/-- 🟢 НИЖНЯЯ ГРАНЬ (грузонесущее — ЦИТИРУЕМ mathlib).
    `1 ≤ mahlerMeasure` для всякого НЕНУЛЕВОГО целочисленного многочлена: пол круга Лемера. -/
theorem mahler_lower_bound {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
  Polynomial.one_le_mahlerMeasure_of_ne_zero hp

/-- 🟢 НАСЫЩЕНИЕ ГРАНИЦЫ (грузонесущее — ЦИТИРУЕМ mathlib).
    Мера Малера кругового многочлена равна 1 — граница Кронекера достигается. -/
theorem cyclotomic_mahler_one (n : ℕ) :
    ((cyclotomic n ℤ).map (algebraMap ℤ ℂ)).mahlerMeasure = 1 :=
  Polynomial.cyclotomic_mahlerMeasure_eq_one n

/-! ################################################################################
    §2  🟢 ДВИГАТЕЛЬ: высотный спуск по мере Малера терминируется (Норткотт-прочтение)
    ################################################################################ -/

/-- Абстрактная ВЫСОТНАЯ МОДЕЛЬ спуска по мере Малера: носитель `α`, ℕ-высота
    (пол меры Малера / глубина итерации), шаг спуска, строго уменьшающий высоту.
    Это тот же интерфейс, что `BSDHeightModel` в `BSDFront`. -/
structure MahlerHeightModel where
  /-- Носитель (например, ограниченное по степени семейство целочисленных многочленов). -/
  Carrier : Type
  /-- ℕ-высота, ПОРОЖДЁННАЯ мерой Малера (пол `mahlerMeasure` или глубина спуска). -/
  height : Carrier → ℕ
  /-- Шаг спуска. -/
  descentStep : Carrier → Carrier → Prop
  /-- Спуск строго уменьшает высоту. -/
  descent_decreases : ∀ x y, descentStep x y → height x < height y

/-- 🟢 ДВИГАТЕЛЬ (КОРОЛЛАРИЙ `no_perpetual_engine_of_natRank`).
    На всякой высотной модели по мере Малера ВЕЧНЫЙ ДВИГАТЕЛЬ (бесконечный строго
    нисходящий высотный спуск) НЕВОЗМОЖЕН: спуск терминируется. Это движковое прочтение
    конечности Норткотта `finite_mahlerMeasure_le`: где конечно много многочленов ниже
    границы, там бесконечного строгого высотного спуска нет. -/
theorem lehmer_descent_has_no_engine (M : MahlerHeightModel) :
    ¬ PerpetualEngine M.descentStep :=
  no_perpetual_engine_of_natRank M.height (fun x y h => M.descent_decreases x y h)

/-- Обитаемая высотная модель: носитель ℕ (глубина спуска), высота = тождество,
    шаг спуска — строгое убывание. Показывает, что интерфейс НЕ ВАКУУМЕН. -/
def mahlerHeightModel_inhabited : MahlerHeightModel where
  Carrier := ℕ
  height := id
  descentStep := fun x y => x < y
  descent_decreases := fun _ _ h => h

/-- 🟢 Обитаемый экземпляр: у конкретной высотной модели двигателя нет. -/
theorem inhabited_descent_has_no_engine :
    ¬ PerpetualEngine mahlerHeightModel_inhabited.descentStep :=
  lehmer_descent_has_no_engine mahlerHeightModel_inhabited

/-! ################################################################################
    §3  🔴 ЧЕСТНЫЙ ВЕНТИЛЬ: гипотеза Лемера (равномерная константа c>1) — ОТКРЫТА
    ################################################################################ -/

/-- 🔴 Гипотеза ЛЕМЕРА: ∃ c>1 такое, что всякий НЕ-круговой (мера Малера ≠ 1) целочисленный
    монический многочлен имеет меру Малера ≥ c. ОТКРЫТА.

    Кронекер (`kronecker_boundary`) закрывает ГРАНИЦУ M=1; РАЗРЫВ выше 1 — равномерная
    нижняя грань c>1 для НЕ-круговых — открыт. Наименьшее известное значение — число
    Лемера ≈ 1.17628. Это НАЗВАННЫЙ ПРЕДИКАТ над РЕАЛЬНОЙ `mahlerMeasure`; НЕ теорема. -/
def LehmerConjecture : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.Monic →
    ((p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1) →
    c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure

/-!
################################################################################
  ИТОГ (LOUD HONEST): что доказано, что переиспользовано, что ОСТАЁТСЯ ОТКРЫТЫМ
################################################################################

  🟢 ГРУЗОНЕСУЩИЕ ЗЕЛЁНЫЕ (цитируют РЕАЛЬНЫЕ доказанные теоремы mathlib):
     · `mahler_northcott_shadow`  := `Polynomial.finite_mahlerMeasure_le` (Норткотт);
     · `kronecker_boundary`       := `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one` (Кронекер);
     · `kronecker_cyclotomic_dvd` := `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`;
     · `mahler_lower_bound`       := `Polynomial.one_le_mahlerMeasure_of_ne_zero`;
     · `cyclotomic_mahler_one`    := `Polynomial.cyclotomic_mahlerMeasure_eq_one`;
     · `lehmer_descent_has_no_engine` := коралларий `no_perpetual_engine_of_natRank`.

  🟢 ПЕРЕИСПОЛЬЗОВАНО (цитируется, НЕ пере-выводится):
     · `UniversalEngine.no_perpetual_engine_of_natRank` (движок ранга);
     · `UniversalEngine.PerpetualEngine` (определение двигателя).

  🔴 ОТКРЫТО (НЕ доказано; НАЗВАННЫЙ вентиль над РЕАЛЬНОЙ мерой Малера):
     · `LehmerConjecture` — равномерный разрыв c>1 выше 1 для не-круговых.

  ЧЕСТНАЯ НОВИЗНА: структурное прочтение «мера Малера = высота, Норткотт = фундированность =
  нет высотного спуска», заземлённое на РЕАЛЬНЫХ `finite_mahlerMeasure_le` и
  `pow_eq_one_of_mahlerMeasure_eq_one`. Это ФОРМАЛИЗАЦИЯ/УНИФИКАЦИЯ, НЕ доказательство Лемера.
  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; такса 47 неизменна.
-/

#print axioms mahler_northcott_shadow
#print axioms kronecker_boundary
#print axioms kronecker_cyclotomic_dvd
#print axioms mahler_lower_bound
#print axioms cyclotomic_mahler_one
#print axioms lehmer_descent_has_no_engine
#print axioms inhabited_descent_has_no_engine

end EuclidsPath.LehmerFront
