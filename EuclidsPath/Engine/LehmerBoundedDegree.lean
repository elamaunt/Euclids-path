/-
  LehmerBoundedDegree — ЛЕМЕР ПРИ ОГРАНИЧЕННОЙ СТЕПЕНИ: разрыв над 1 существует
  для КАЖДОЙ фиксированной степени n (константа ЗАВИСИТ от n).

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК: ЭТО НЕ ГИПОТЕЗА ЛЕМЕРА.                        │
  │  Константа c = c(n) ЗАВИСИТ от степени n. РАВНОМЕРНОСТЬ ПО n —             │
  │  единая c > 1 для ВСЕХ степеней сразу — И ЕСТЬ открытая гипотеза Лемера.   │
  └───────────────────────────────────────────────────────────────────────────┘

  ИДЕЯ (полностью зелёная, машинная): при фиксированной степени n множество мер
  Малера в окне (1, 2] — образ КОНЕЧНОГО множества многочленов (Норткотт,
  `Polynomial.finite_mahlerMeasure_le`, граница B = 2). У конечного непустого
  множества вещественных чисел есть минимум; он строго больше 1 (каждый элемент
  окна > 1). Значит, ниже минимума мер нет: интервал (1, c(n)) ПУСТ. Если окно
  пусто — годится c = 2. Это КОМПАКТНОСТНОЕ соображение, известное классикам:
  «Лемер при ограниченной степени тривиален по Норткотту». Вся тяжесть гипотезы —
  в том, что c(n) может стремиться к 1 при n → ∞; запретить это НИКТО не умеет.

  🟢 ЗЕЛЁНОЕ (машинно, в этом файле; грузонесущие ЦИТИРУЮТ реальный mathlib):
   · `measureWindow_finite` — окно {natDegree ≤ n, 1 < мера ≤ 2} конечно;
     прямой королларий `LehmerFront.mahler_northcott_shadow` :=
     `Polynomial.finite_mahlerMeasure_le` (Норткотт, ДОКАЗАН в mathlib).
   · `lehmer_gap_at_bounded_degree` — ∃ c ∈ (1, 2]: НИ ОДИН целочисленный
     многочлен степени ≤ n не имеет меры Малера в интервале (1, c).
     Минимум конечного множества через `Set.exists_min_image`.
   · `lehmer_at_bounded_degree` — ЦЕЛЬ: ∀ n ∃ c > 1: всякий p с natDegree ≤ n
     и мерой > 1 имеет меру ≥ c ИЛИ меру > 2.
   · `mahlerMeasure_neg` — мера Малера не видит знака: M(-p) = M(p)
     (через `mahlerMeasure_mul` и `mahlerMeasure_const`; в mathlib v4.31 этой
     конкретной леммы нет, выводим на месте).
   · `uniformLehmerGap_iff_all_degrees` — АУДИТ НА ПЕРЕИМЕНОВАНИЕ ЦЕЛИ (машинный
     iff): якорь `UniformLehmerGap` РАВНОСИЛЕН «одна константа на все степени
     сразу» — т.е. якорь ЕСТЬ равномерная версия нашей теоремы, и его имя не
     провозит контрабандой никакого прогресса.
   · `uniformLehmerGap_of_lehmerConjecture` — мост: из монической формулировки
     `LehmerFront.LehmerConjecture` следует якорь `UniformLehmerGap` (разбор
     старшего коэффициента: |lc| ≥ 2 даёт меру ≥ 2 по
     `leadingCoeff_le_mahlerMeasure`; lc = ±1 сводится к монической ±p).

  🔴 ЧЕСТНО ОТКРЫТОЕ (НЕ доказано; named data-anchor):
   · `UniformLehmerGap` — РАВНОМЕРНЫЙ разрыв: ∃ c > 1 (одна на ВСЕ степени),
     без мер Малера в (1, c). Это и есть гипотеза Лемера в форме разрыва.
     ЧТО МАТЕМАТИКА ДОЛЖНА ПРЕДЪЯВИТЬ: нижнюю оценку c(n) ≥ c₀ > 1, НЕ зависящую
     от n; лучшее известное безусловное — Добровольский (1979):
     c(n) ≥ 1 + c·(log log n / log n)³ → 1, чего НЕДОСТАТОЧНО. В mathlib v4.31
     нет ни теоремы Добровольского, ни чего-либо сильнее; нет и имени вида
     `Polynomial.lehmer_conjecture` (proof_wanted). Кандидат-константа — мера
     многочлена Лемера ≈ 1.17628.

  ЧЕСТНАЯ НОВИЗНА. Мы НЕ доказываем Лемера и НЕ приближаемся к нему: теорема
  `lehmer_at_bounded_degree` — фольклорный королларий Норткотта, его ценность
  здесь — машинная фиксация ТОЧНОЙ границы между зелёным (каждое n по
  отдельности) и красным (все n сразу). Это НЕ решение и НЕ гёделевский трюк.

  Никакого `sorry`, никакого `admit`, никакого `native_decide`, никакой новой
  аксиомы. Все экспорты — стандартная тройка `propext` / `Classical.choice` /
  `Quot.sound`. Такса репозитория (47) этим файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LehmerBoundedDegree.lean
    → ноль ошибок.

  Родство: EuclidsPath/Engine/LehmerFront.lean (Норткотт-тень, Кронекер, вентиль
    `LehmerConjecture`); Mathlib/NumberTheory/MahlerMeasure.lean (Норткотт);
    Mathlib/Analysis/Polynomial/MahlerMeasure.lean (определение меры, тип ℝ).
-/
import Mathlib
import EuclidsPath.Engine.LehmerFront

set_option autoImplicit false

namespace EuclidsPath.LehmerBoundedDegree

open Polynomial

/-! ################################################################################
    §1  🟢 ОКНО НОРТКОТТА: многочлены степени ≤ n с мерой Малера в (1, 2] — конечно
    ################################################################################ -/

/-- ОКНО ЛЕМЕРА при степени ≤ `n`: целочисленные многочлены с мерой Малера строго
    между 1 и 2 (включая 2). Мера Малера здесь — РЕАЛЬНАЯ `Polynomial.mahlerMeasure`
    (тип ℝ) комплексификации, как в `LehmerFront`. Именно в этом окне живёт весь
    вопрос Лемера: ниже 1 мер нет (`mahler_lower_bound`), ровно 1 — Кронекер. -/
def measureWindow (n : ℕ) : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree ≤ n ∧
    1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2}

@[simp] theorem mem_measureWindow {n : ℕ} {p : ℤ[X]} :
    p ∈ measureWindow n ↔ p.natDegree ≤ n ∧
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 :=
  Iff.rfl

/-- 🟢 ОКНО КОНЕЧНО (грузонесущее — Норткотт). Прямой королларий
    `LehmerFront.mahler_northcott_shadow` := `Polynomial.finite_mahlerMeasure_le`
    при границе B = 2: ограниченная степень + мера ≤ 2 ⟹ конечно много. -/
theorem measureWindow_finite (n : ℕ) : (measureWindow n).Finite := by
  refine (LehmerFront.mahler_northcott_shadow n 2).subset ?_
  intro p hp
  rw [mem_measureWindow] at hp
  exact ⟨hp.1, by exact_mod_cast hp.2.2⟩

/-! ################################################################################
    §2  🟢 ЦЕЛЬ: разрыв над 1 при фиксированной степени (константа ЗАВИСИТ от n!)
    ################################################################################ -/

/-- 🟢 РАЗРЫВ ПРИ ОГРАНИЧЕННОЙ СТЕПЕНИ (форма «пустой интервал»).
    Для каждого `n` существует `c ∈ (1, 2]` такое, что НИ ОДИН целочисленный
    многочлен степени ≤ `n` не имеет меры Малера в открытом интервале `(1, c)`.

    ДОКАЗАТЕЛЬСТВО: окно `(1, 2]` конечно (Норткотт); если оно непусто, берём
    многочлен минимальной меры (`Set.exists_min_image`) — его мера и есть `c`;
    если пусто, годится `c = 2`.

    ⚠️ ЧЕСТНО: `c = c(n)` ЗАВИСИТ от `n`. Единая `c` для всех `n` — открытая
    гипотеза Лемера (`UniformLehmerGap` ниже). ЭТО НЕ ЛЕМЕР. -/
theorem lehmer_gap_at_bounded_degree (n : ℕ) :
    ∃ c : ℝ, 1 < c ∧ c ≤ 2 ∧ ∀ p : ℤ[X], p.natDegree ≤ n →
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ∉ Set.Ioo 1 c := by
  by_cases hne : (measureWindow n).Nonempty
  · -- окно непусто: минимум меры по конечному окну
    obtain ⟨p₀, hp₀, hmin⟩ :=
      Set.exists_min_image (measureWindow n)
        (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).mahlerMeasure)
        (measureWindow_finite n) hne
    rw [mem_measureWindow] at hp₀
    refine ⟨(p₀.map (Int.castRingHom ℂ)).mahlerMeasure, hp₀.2.1, hp₀.2.2, ?_⟩
    intro p hdeg hmem
    obtain ⟨h1, h2⟩ := hmem
    have hp_mem : p ∈ measureWindow n := by
      rw [mem_measureWindow]
      exact ⟨hdeg, h1, (h2.trans_le hp₀.2.2).le⟩
    exact absurd (hmin p hp_mem) (not_le.mpr h2)
  · -- окно пусто: любой многочлен с мерой в (1, 2) лежал бы в окне
    refine ⟨2, one_lt_two, le_refl 2, ?_⟩
    intro p hdeg hmem
    obtain ⟨h1, h2⟩ := hmem
    exact hne ⟨p, by rw [mem_measureWindow]; exact ⟨hdeg, h1, h2.le⟩⟩

/-- 🟢 ЦЕЛЬ МОДУЛЯ: для каждой степени `n` существует `c > 1` такое, что всякий
    целочисленный многочлен `p` с `natDegree p ≤ n` и мерой Малера > 1 имеет меру
    Малера ≥ `c` ИЛИ меру Малера > 2. Эквивалентно (см.
    `lehmer_gap_at_bounded_degree`): мер в интервале `(1, c)` НЕТ.

    ⚠️ ГРОМКО И ЧЕСТНО: ЭТО НЕ ГИПОТЕЗА ЛЕМЕРА. Константа `c = c(n)` зависит от
    степени `n`; факт при фиксированном `n` — фольклорный королларий конечности
    Норткотта (`Polynomial.finite_mahlerMeasure_le`). Гипотеза Лемера — это
    РАВНОМЕРНОСТЬ ПО `n`: одна `c > 1` на все степени сразу (якорь
    `UniformLehmerGap`); она ОТКРЫТА, и этот файл её НЕ закрывает. -/
theorem lehmer_at_bounded_degree (n : ℕ) :
    ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.natDegree ≤ n →
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure →
      c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure ∨
      2 < (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨c, hc1, _, hgap⟩ := lehmer_gap_at_bounded_degree n
  refine ⟨c, hc1, fun p hdeg h1 => ?_⟩
  by_cases hcle : c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure
  · exact Or.inl hcle
  · exact absurd (Set.mem_Ioo.mpr ⟨h1, not_le.mp hcle⟩) (hgap p hdeg)

/-! ################################################################################
    §3  🔴 ЯКОРЬ: равномерность по n (= сам Лемер) + машинный аудит на переименование
    ################################################################################ -/

/-- 🔴 ЯКОРЬ (data-anchor, ОТКРЫТ): РАВНОМЕРНЫЙ разрыв Лемера — существует ОДНА
    константа `c > 1` (не зависящая от степени!) такая, что ни один целочисленный
    многочлен не имеет меры Малера в `(1, c)`. Это гипотеза Лемера в форме разрыва.

    ЧТО МАТЕМАТИКА ДОЛЖНА ПРЕДЪЯВИТЬ: оценку снизу на `c(n)` из
    `lehmer_gap_at_bounded_degree`, НЕ зависящую от `n`. Лучшее безусловное —
    теорема Добровольского (1979): `c(n) ≥ 1 + c·(log log n / log n)³`, которая
    стремится к 1 и НЕ закрывает якорь. В mathlib v4.31 НЕТ ни Добровольского,
    ни Смита (для не-взаимных), ни какого-либо `Polynomial.lehmer_*`
    (proof_wanted). Кандидат — мера многочлена Лемера
    `X¹⁰+X⁹-X⁷-X⁶-X⁵-X⁴-X³+X+1` ≈ 1.17628. Мы этот Prop НЕ доказываем. -/
def UniformLehmerGap : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X],
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ∉ Set.Ioo 1 c

/-- 🟢 АУДИТ НА ПЕРЕИМЕНОВАНИЕ ЦЕЛИ (машинный iff, как `offCriticalBridge_iff_RH`).
    Якорь `UniformLehmerGap` РАВНОСИЛЕН утверждению «в `lehmer_gap_at_bounded_degree`
    можно взять одну константу на все степени сразу». То есть якорь — это В ТОЧНОСТИ
    равномерная версия нашей зелёной теоремы, никакого скрытого содержания в его
    имени нет: назвать его — не значит продвинуться. -/
theorem uniformLehmerGap_iff_all_degrees :
    UniformLehmerGap ↔
      ∃ c : ℝ, 1 < c ∧ ∀ n : ℕ, ∀ p : ℤ[X], p.natDegree ≤ n →
        (p.map (Int.castRingHom ℂ)).mahlerMeasure ∉ Set.Ioo 1 c := by
  constructor
  · rintro ⟨c, hc, hgap⟩
    exact ⟨c, hc, fun _ p _ => hgap p⟩
  · rintro ⟨c, hc, hgap⟩
    exact ⟨c, hc, fun p => hgap p.natDegree p le_rfl⟩

/-! ################################################################################
    §4  🟢 МОСТ К LehmerFront: моническая формулировка влечёт якорь
    ################################################################################ -/

/-- 🟢 Мера Малера не видит знака: `M(-p) = M(p)`. В mathlib v4.31 такой леммы нет
    (есть `mahlerMeasure_mul` и `mahlerMeasure_const`); выводим: `-p = C(-1)·p`,
    множитель даёт `‖-1‖ = 1`. -/
theorem mahlerMeasure_neg (p : ℂ[X]) : (-p).mahlerMeasure = p.mahlerMeasure := by
  have h : (-p : ℂ[X]) = Polynomial.C (-1 : ℂ) * p := by
    rw [map_neg, map_one, neg_one_mul]
  rw [h, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_const]
  simp

/-- 🟢 МОСТ (при якоре фронт закрывается — в обе стороны формулировок).
    Моническая формулировка гипотезы Лемера из `LehmerFront.LehmerConjecture`
    ВЛЕЧЁТ якорь `UniformLehmerGap` для ВСЕХ целочисленных многочленов.

    Разбор: у ненулевого `p` старший коэффициент `lc ≠ 0`. Если `|lc| ≥ 2`, то
    мера ≥ `‖lc‖` ≥ 2 (`Polynomial.leadingCoeff_le_mahlerMeasure`) — вне окна
    `(1, min c 2)`. Если `lc = 1`, `p` моничен — работает `LehmerConjecture`.
    Если `lc = -1`, моничен `-p`, а мера знака не видит (`mahlerMeasure_neg`). -/
theorem uniformLehmerGap_of_lehmerConjecture
    (h : LehmerFront.LehmerConjecture) : UniformLehmerGap := by
  obtain ⟨c, hc1, hLeh⟩ := h
  refine ⟨min c 2, lt_min hc1 one_lt_two, ?_⟩
  intro p hmem
  obtain ⟨h1, h2⟩ := hmem
  obtain ⟨h2c, h2two⟩ := lt_min_iff.mp h2
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, Polynomial.mahlerMeasure_zero] at h1
    linarith
  -- старший коэффициент комплексификации — каст целого старшего коэффициента
  have hlc_map : (p.map (Int.castRingHom ℂ)).leadingCoeff = (p.leadingCoeff : ℂ) := by
    rw [Polynomial.leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int]
    exact eq_intCast _ _
  have habs : (|p.leadingCoeff| : ℝ) ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
    have hnorm := Polynomial.leadingCoeff_le_mahlerMeasure (p.map (Int.castRingHom ℂ))
    rw [hlc_map] at hnorm
    calc (|p.leadingCoeff| : ℝ) = ‖(p.leadingCoeff : ℂ)‖ := by
          rw [Complex.norm_intCast]
      _ ≤ _ := hnorm
  rcases lt_or_ge |p.leadingCoeff| 2 with hsmall | hbig
  · -- |lc| = 1: p или -p моничен, применяем моническую формулировку
    have hlc1 : |p.leadingCoeff| = 1 := by
      have hge : 1 ≤ |p.leadingCoeff| :=
        Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp0)
      omega
    rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hlc1 with hlc | hlc
    · -- lc = 1: p моничен
      have hMon : p.Monic := hlc
      have := hLeh p hMon h1.ne'
      linarith
    · -- lc = -1: -p моничен, мера та же
      have hMon : (-p).Monic := by
        show (-p).leadingCoeff = 1
        rw [Polynomial.leadingCoeff_neg, hlc, neg_neg]
      have hmapneg : ((-p).map (Int.castRingHom ℂ)) = -(p.map (Int.castRingHom ℂ)) :=
        Polynomial.map_neg _
      have hμneg : ((-p).map (Int.castRingHom ℂ)).mahlerMeasure
          = (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
        rw [hmapneg, mahlerMeasure_neg]
      have hne1 : ((-p).map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1 := by
        rw [hμneg]; exact h1.ne'
      have hge := hLeh (-p) hMon hne1
      rw [hμneg] at hge
      linarith
  · -- |lc| ≥ 2: мера ≥ 2, окно (1, min c 2) недостижимо
    have h2le : (2 : ℝ) ≤ (|p.leadingCoeff| : ℝ) := by exact_mod_cast hbig
    linarith

/-!
################################################################################
  ИТОГ (LOUD HONEST): что доказано, что переиспользовано, что ОСТАЁТСЯ ОТКРЫТЫМ
################################################################################

  🟢 ГРУЗОНЕСУЩИЕ ЗЕЛЁНЫЕ (этот файл):
     · `measureWindow_finite`          — окно (1, 2] конечно (Норткотт);
     · `lehmer_gap_at_bounded_degree`  — ∃ c(n) ∈ (1, 2]: интервал (1, c(n)) пуст;
     · `lehmer_at_bounded_degree`      — ЦЕЛЬ: мера ≥ c(n) или мера > 2;
     · `mahlerMeasure_neg`             — M(-p) = M(p);
     · `uniformLehmerGap_iff_all_degrees` — аудит: якорь = равномерная версия;
     · `uniformLehmerGap_of_lehmerConjecture` — мост от монической формулировки.

  🟢 ПЕРЕИСПОЛЬЗОВАНО (цитируется, НЕ пере-выводится):
     · `LehmerFront.mahler_northcott_shadow` := `Polynomial.finite_mahlerMeasure_le`;
     · `Set.exists_min_image` (минимум конечного множества);
     · `Polynomial.mahlerMeasure_mul`, `mahlerMeasure_const`,
       `leadingCoeff_le_mahlerMeasure`, `leadingCoeff_map_of_injective`.

  🔴 ОТКРЫТО (named data-anchor; НЕ доказано, НЕ закрыто движком):
     · `UniformLehmerGap` — одна константа c > 1 на ВСЕ степени = гипотеза Лемера.
       Аудит `uniformLehmerGap_iff_all_degrees` показывает: якорь есть В ТОЧНОСТИ
       равномерная версия зелёной теоремы, переименование цели исключено машинно.

  ЧЕСТНАЯ НОВИЗНА: НУЛЕВАЯ математическая (фольклорный королларий Норткотта);
  ценность — машинная фиксация ТОЧНОЙ границы зелёное/красное: каждое n по
  отдельности — тривиально, все n сразу — Лемер. ЭТО НЕ РЕШЕНИЕ И НЕ ГЁДЕЛЬ.
  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`;
  такса репозитория (47) этим файлом НЕ меняется.
-/

#print axioms measureWindow_finite
#print axioms lehmer_gap_at_bounded_degree
#print axioms lehmer_at_bounded_degree
#print axioms uniformLehmerGap_iff_all_degrees
#print axioms mahlerMeasure_neg
#print axioms uniformLehmerGap_of_lehmerConjecture

end EuclidsPath.LehmerBoundedDegree
