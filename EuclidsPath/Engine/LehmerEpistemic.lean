/-
  LehmerEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ гипотезы Лемера (мера Малера).
  Зеркало PNPFirstCause (НЕ Коллатц-варианта: декрета у Лемера нет и не было —
  Лемер не входит в четыре границы step00FirstCause, файл целиком зелёный).
  Зелёный фронт: Engine/LehmerFront.lean (Норткотт, Кронекер, двигатель).

  ЧТО ЭТО. «Решить Лемера изнутри конечного горизонта» = удержать НЕОГРАНИЧЕННОЕ
  семейство многочленов под ОДНИМ конечным Норткотт-горизонтом `mahlerBox n B`
  (степень ≤ n, мера Малера ≤ B): поле `resolves` — инъективная оплата семейства
  конечным горизонтом, поле `beyondOwnHorizon` — подлинная бесконечность семейства.
  Противоречие оплачено ДВУМЯ настоящими теоремами: конечность горизонта — РЕАЛЬНЫЙ
  Норткотт (`mahler_northcott_shadow` = `Polynomial.finite_mahlerMeasure_le`,
  настоящая теория чисел, не сконструированный граф), а пижонхол — реальный
  `Set.infinite_of_injective_forall_mem` (нет инъекции бесконечного в конечное —
  та же стена вполне-фундированности, что `no_perpetual_engine_on_nat`).

  ЧЕСТНОСТЬ (CORR учтён). (1) Связка ГОЛЕЕ, чем у P/NP: там между полями стоит
  реальное понятие оплаты (`FullRankCertificatePayment`), здесь между полями ровно
  ОДИН шаг — пижонхол сворачивает их в «Infinite против Finite». Зато содержательнее
  Коллатца (там буквально `fun H => H.beyondOwnHorizon H.ground`): противоречие
  здесь несут ВНЕШНИЕ зелёные теоремы (Норткотт + пижонхол), а не сами поля.
  Груз содержательности несут безусловный `lehmer_supply_below_horizon_impossible`
  (сторона конечности РАЗРЯЖЕНА Норткоттом, не принята гипотезой) и
  conjecture-связанный `lehmer_refutation_escapes_every_horizon` (опровержение
  Лемера вынуждено пробегать ВСЕ степенные горизонты) — без них голый wrapper был
  бы тавтологией. (2) Это модель-внутренняя эпистемика, НЕ решение гипотезы Лемера:
  про открытый равномерный зазор c > 1 (`LehmerConjecture`, число Лемера ≈ 1.17628)
  здесь НЕ утверждается НИЧЕГО — красный гейт остаётся красным. (3) Это НЕ Гёдель:
  никакой независимости не заявляется — только пижонхол-самоуничтожение внутреннего
  самообоснования. (4) Бонус-содержание: `lehmer_at_bounded_degree` — честный
  ЧАСТНЫЙ СЛУЧАЙ гипотезы: на каждом конечном степенном горизонте зазор СУЩЕСТВУЕТ;
  вся открытость Лемера — побег степени за всякий горизонт.

  Никакого sorry, никакой новой аксиомы, никакого native_decide, карантин НЕ
  импортируется. Таинт репозитория (47) этим файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LehmerEpistemic.lean
-/

import EuclidsPath.Engine.LehmerFront

set_option autoImplicit false

namespace EuclidsPath.LehmerFront.Epistemic

open Polynomial
open EuclidsPath.LehmerFront
open EuclidsPath.UniversalEngine

/-! ## Горизонт: Норткотт-коробка (🟢) -/

/-- **Норткотт-коробка**: целочисленные многочлены степени ≤ `n` с мерой Малера ≤ `B` —
    конечнотопливный горизонт внутреннего решателя Лемера. -/
def mahlerBox (n : ℕ) (B : NNReal) : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B}

/-- 🟢 Коробка КОНЕЧНА — это реальный Норткотт (`mahler_northcott_shadow` =
    `Polynomial.finite_mahlerMeasure_le`), настоящая теория чисел, не конструкция. -/
theorem mahlerBox_finite (n : ℕ) (B : NNReal) : (mahlerBox n B).Finite :=
  mahler_northcott_shadow n B

/-! ## Пижонхол-стена: неограниченная поставка под горизонт не влезает (🟢) -/

/-- 🟢 **ПИЖОНХОЛ-СТЕНА (безусловная, грузонесущая).** Нет инъекции `ℕ` в Норткотт-коробку:
    неограниченную поставку многочленов НЕЛЬЗЯ удержать под одним конечным горизонтом.
    Здесь сторона конечности РАЗРЯЖЕНА реальным Норткоттом (не принята гипотезой), а
    противоречие поставляет реальный пижонхол `Set.infinite_of_injective_forall_mem` —
    аналог `no_fullPayment_of_unboundedSupply` у P/NP. -/
theorem lehmer_supply_below_horizon_impossible (n : ℕ) (B : NNReal) :
    ¬ ∃ f : ℕ → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B := by
  rintro ⟨f, hinj, hmem⟩
  exact (mahlerBox_finite n B).not_infinite
    (Set.infinite_of_injective_forall_mem hinj hmem)

/-! ## Частный случай гипотезы: зазор на каждом конечном горизонте (🟢) -/

/-- 🟢 **ЛЕМЕР НА ОГРАНИЧЕННОЙ СТЕПЕНИ (честный частный случай гипотезы).** На каждом
    степенном горизонте `n` зазор СУЩЕСТВУЕТ: есть `c > 1` такое, что всякий монический
    целочисленный многочлен степени ≤ `n` с мерой Малера ≠ 1 имеет меру ≥ `c`.
    Схема: Норткотт-каталог при крышке 2 конечен; минимум мер по каталогу строго
    больше 1 (пол `mahler_lower_bound` + ≠ 1); вне каталога мера > 2. Машинно видно:
    вся открытость Лемера — побег степени за ВСЯКИЙ конечный горизонт. -/
theorem lehmer_at_bounded_degree (n : ℕ) :
    ∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.Monic → p.natDegree ≤ n →
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1 →
      c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  classical
  -- конечный Норткотт-каталог кандидатов под крышкой 2
  have hfin : Set.Finite {p : ℤ[X] | p.Monic ∧ p.natDegree ≤ n ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1} := by
    apply (mahler_northcott_shadow n 2).subset
    rintro p ⟨-, hdeg, hle, -⟩
    exact ⟨hdeg, by simpa using hle⟩
  by_cases hne : Set.Nonempty {p : ℤ[X] | p.Monic ∧ p.natDegree ≤ n ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1}
  · -- каталог непуст: минимум мер по конечному каталогу даёт зазор
    obtain ⟨p₀, hp₀S, hp₀min⟩ := Set.exists_min_image _
      (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).mahlerMeasure) hfin hne
    obtain ⟨hp₀monic, -, -, hp₀ne⟩ := hp₀S
    have hp₀gt : 1 < (p₀.map (Int.castRingHom ℂ)).mahlerMeasure :=
      lt_of_le_of_ne (mahler_lower_bound hp₀monic.ne_zero) (Ne.symm hp₀ne)
    refine ⟨min ((p₀.map (Int.castRingHom ℂ)).mahlerMeasure) 2,
      lt_min hp₀gt one_lt_two, ?_⟩
    intro p hmonic hdeg hne1
    by_cases hle2 : (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2
    · exact le_trans (min_le_left _ _) (hp₀min p ⟨hmonic, hdeg, hle2, hne1⟩)
    · exact le_trans (min_le_right _ _) (not_le.mp hle2).le
  · -- каталог пуст: всякий кандидат имеет меру > 2, зазор c := 2
    refine ⟨2, one_lt_two, ?_⟩
    intro p hmonic hdeg hne1
    by_contra hlt
    exact hne ⟨p, hmonic, hdeg, (not_le.mp hlt).le, hne1⟩

/-- 🟢 **ОПРОВЕРЖЕНИЕ ПРОБЕГАЕТ ВСЯКИЙ ГОРИЗОНТ** (conjecture-связанный носитель;
    аналог `nonHalting_carries_perpetual_engine` у Коллатца). Если Лемер ложен, то
    для всякого `n` и всякого `ε > 0` найдётся монический многочлен степени > `n`
    с мерой Малера в `(1, 1+ε)`: опровергающие свидетели ВЫНУЖДЕНЫ бежать за каждый
    конечный степенной горизонт — под горизонтом зазор существует
    (`lehmer_at_bounded_degree`). -/
theorem lehmer_refutation_escapes_every_horizon (hL : ¬ LehmerConjecture) :
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ p : ℤ[X], p.Monic ∧ n < p.natDegree ∧
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure < 1 + ε := by
  intro n ε hε
  obtain ⟨c₀, hc₀, hgap⟩ := lehmer_at_bounded_degree n
  have hc : (1 : ℝ) < min c₀ (1 + ε) := lt_min hc₀ (by linarith)
  unfold LehmerConjecture at hL
  push Not at hL
  obtain ⟨p, hmonic, hne1, hlt⟩ := hL (min c₀ (1 + ε)) hc
  have h1lt : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
    lt_of_le_of_ne (mahler_lower_bound hmonic.ne_zero) (Ne.symm hne1)
  refine ⟨p, hmonic, ?_, h1lt, lt_of_lt_of_le hlt (min_le_right _ _)⟩
  by_contra hdeg
  push Not at hdeg
  exact absurd (hgap p hmonic hdeg hne1)
    (not_le.mpr (lt_of_lt_of_le hlt (min_le_left _ _)))

/-! ## Модель: внутреннее решение = самообоснование за собственным горизонтом -/

/-- **Внутреннее самообоснование решения Лемера на конечном горизонте.** Решатель
    одновременно (a) ОПЛАЧИВАЕТ инъективно конечным Норткотт-горизонтом всё семейство
    (`resolves`) и (b) это семейство ПОДЛИННО БЕСКОНЕЧНО (`beyondOwnHorizon`).

    ЧЕСТНАЯ ОГОВОРКА (CORR): связка ГОЛЕЕ, чем у P/NP — между полями ровно ОДИН шаг
    (пижонхол сворачивает их в «Infinite против Finite»); у P/NP между полями стоит
    реальное понятие оплаты. Содержательность оплачена не независимостью сторон, а
    ЦЕНОЙ противоречия: его несут внешние зелёные теоремы — реальный Норткотт
    (`mahler_northcott_shadow`) и реальный пижонхол
    (`Set.infinite_of_injective_forall_mem`), а не сами поля друг о друга (как у
    Коллатца). -/
structure InternalisedLehmerGround (ι : Type) (n : ℕ) (B : NNReal) : Prop where
  resolves : ∃ f : ι → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B
  beyondOwnHorizon : Infinite ι

/-- «Внутреннее знание причины Лемера» = внутреннее самообоснование решения. -/
abbrev InternalKnowledgeOfLehmerCause (ι : Type) (n : ℕ) (B : NNReal) : Prop :=
  InternalisedLehmerGround ι n B

/-- Конкретная честная инстанция: поставка индексирована `ℕ`. -/
abbrev InternalLehmerDecision (n : ℕ) (B : NNReal) : Prop :=
  InternalisedLehmerGround ℕ n B

/-! ## Ядро: самообоснование самоуничтожается = стена вечного двигателя (🟢) -/

/-- 🟢 Самообоснование самоуничтожается: бесконечное семейство не впихнуть инъективно
    в конечную Норткотт-коробку. Противоречие поставляют Норткотт + пижонхол
    (зеркало `no_internalisedPNPGround`, где его поставлял
    `no_fullPayment_of_unboundedSupply`). -/
theorem no_internalisedLehmerGround {ι : Type} {n : ℕ} {B : NNReal} :
    InternalisedLehmerGround ι n B → False := by
  rintro ⟨⟨f, hinj, hmem⟩, hinf⟩
  exact (mahlerBox_finite n B).not_infinite
    (@Set.infinite_of_injective_forall_mem ι _ hinf _ f hinj hmem)

/-- 🟢 **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `pnpCause_unknowable` /
    `collatzCause_unknowable`): внутреннее конечногоризонтное решение Лемера
    невозможно. НЕ утверждение о самой гипотезе: зазор `c > 1` остаётся открытым. -/
theorem lehmerCause_unknowable {ι : Type} {n : ℕ} {B : NNReal} :
    ¬ InternalKnowledgeOfLehmerCause ι n B :=
  no_internalisedLehmerGround

/-- 🟢 **ТО ЖЕ ПРОТИВОРЕЧИЕ ВЕЧНОГО ДВИГАТЕЛЯ:** невозможность внутреннего решения
    Лемера И невозможность вечного двигателя на ℕ — ОДНА стена вполне-фундированности
    (инъекция бесконечного в конечное = ℕ-спуск без дна). -/
theorem internalLehmerDecision_carries_perpetual_engine {ι : Type} {n : ℕ} {B : NNReal} :
    (InternalisedLehmerGround ι n B → False) ∧
      ¬ PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  ⟨no_internalisedLehmerGround, no_perpetual_engine_on_nat⟩

/-- Ex-falso companion («несёт двигатель»): из самообоснования (уже ложного) выводится
    и сам вечный двигатель на ℕ. ЧЕСТНОСТЬ: маршрут ex falso; несущая часть — сама
    невозможность (`no_internalisedLehmerGround`). -/
theorem internalisedLehmerGround_builds_engine {ι : Type} {n : ℕ} {B : NNReal} :
    InternalisedLehmerGround ι n B → PerpetualEngine (· < · : ℕ → ℕ → Prop) :=
  fun H => (no_internalisedLehmerGround H).elim

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина непознаваема
    изнутри, либо неограниченная поставка влезает под горизонт. Левый дизъюнкт —
    теорема. -/
theorem unknowable_or_lehmer_horizonPayable (n : ℕ) (B : NNReal) :
    (¬ InternalKnowledgeOfLehmerCause ℕ n B) ∨
      ∃ f : ℕ → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B :=
  Or.inl lehmerCause_unknowable

/-! ## Сводки: решение заперто за двигателем; проверка, а не вывод (🟢) -/

/-- 🟢 **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» (зеркало
    `pnp_no_internal_decision_without_engine`):**
    (1) ОПРОВЕРГНУТЬ под конечным горизонтом = инъекция бесконечного в конечное =
        стена двигателя (`lehmer_supply_below_horizon_impossible`);
    (2) САМООБОСНОВАТЬ решение изнутри — самоуничтожается
        (`no_internalisedLehmerGround`);
    (3) единственный без-двигательный путь — внешняя ПРОВЕРКА: на каждом горизонте
        зазор находится перебором конечного Норткотт-каталога
        (`lehmer_at_bounded_degree`); открыт лишь побег за ВСЕ горизонты
        (красный `LehmerConjecture`).
    НЕ утверждается гёделевская независимость и НЕ решается сама гипотеза. -/
theorem lehmer_no_internal_decision_without_engine (n : ℕ) (B : NNReal) :
    (¬ ∃ f : ℕ → ℤ[X], Function.Injective f ∧ ∀ k, f k ∈ mahlerBox n B) ∧
    (InternalisedLehmerGround ℕ n B → False) ∧
    (∃ c : ℝ, 1 < c ∧ ∀ p : ℤ[X], p.Monic → p.natDegree ≤ n →
        (p.map (Int.castRingHom ℂ)).mahlerMeasure ≠ 1 →
        c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure) :=
  ⟨lehmer_supply_below_horizon_impossible n B,
   no_internalisedLehmerGround,
   lehmer_at_bounded_degree n⟩

/-- 🟢 Итоговый эпистемический статус Лемера (зеркало `pnp_locked_behind_engine_status`,
    БЕЗ декрет-конъюнкта — у Лемера границы step00FirstCause нет):
    горизонт конечен (Норткотт, теорема) / двигателя на высотной модели нет (теорема) /
    решить изнутри нельзя (теорема) / опровержение гипотезы пробегало бы все горизонты
    (условная теорема; сам `LehmerConjecture` остаётся открытым красным гейтом). -/
theorem lehmer_locked_behind_engine_status (n : ℕ) (B : NNReal) :
    (mahlerBox n B).Finite ∧
    (¬ PerpetualEngine mahlerHeightModel_inhabited.descentStep) ∧
    (¬ InternalLehmerDecision n B) ∧
    (¬ LehmerConjecture → ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ p : ℤ[X],
        p.Monic ∧ m < p.natDegree ∧
        1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure ∧
        (p.map (Int.castRingHom ℂ)).mahlerMeasure < 1 + ε) :=
  ⟨mahlerBox_finite n B,
   inhabited_descent_has_no_engine,
   lehmerCause_unknowable,
   fun hL => lehmer_refutation_escapes_every_horizon hL⟩

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт репо НЕ меняется -/
#print axioms mahlerBox_finite
#print axioms lehmer_supply_below_horizon_impossible
#print axioms lehmer_at_bounded_degree
#print axioms lehmer_refutation_escapes_every_horizon
#print axioms no_internalisedLehmerGround
#print axioms lehmerCause_unknowable
#print axioms internalLehmerDecision_carries_perpetual_engine
#print axioms internalisedLehmerGround_builds_engine
#print axioms unknowable_or_lehmer_horizonPayable
#print axioms lehmer_no_internal_decision_without_engine
#print axioms lehmer_locked_behind_engine_status

end EuclidsPath.LehmerFront.Epistemic
