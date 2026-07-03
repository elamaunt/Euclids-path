/-
  DyadicFirstCause — 🟡 ЖЁЛТЫЙ СЛОЙ: ИСТОК ДЯДИЧЕСКОГО КАСКАДА ДЕКРЕТИРОВАН ПЕРВОПРИЧИНОЙ.

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК — ЧТО ЗДЕСЬ ЕСТЬ, ЧЕГО НЕТ, И ГДЕ ТАИНТ.                        │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  МАНИФЕСТАЦИЯ ПАТТЕРНА ПРОЕКТА. Этот файл присоединяет каскадный взрыв к «семи маскам»
  первопричины ТОЧНО ТАК ЖЕ, как GeometryFront присоединяет пересечение прямых: зелёная стена
  невозможности (исток каскада НЕ причиним изнутри) + жёлтый слой (тот же первопричинный декрет
  снабжает исток извне). Схема ДВЕ СТЕНЫ / ДЕКРЕТИРОВАННАЯ ПОСТАВКА, а не голое `True`.

  ЧТО ЗДЕСЬ ЕСТЬ:
    • 🟢 (в `DyadicBlowup.lean`, §2quater, БЕЗ таинта): `dyadicOrigin_uncausable_from_inside` —
      крупнейшая оболочка `n=0` (только отток, `kpInflow 0 = 0`) НЕ снабжает свой собственный
      исток: её истинная динамика несёт `bottomForcing > 0` сверх нефорсированной `kpRHS`. Внешняя
      закачка ОБЯЗАТЕЛЬНА. Это каскадный аналог `no_internalisedOriginEvent`.
    • 🟡 (ЗДЕСЬ, ТАИНТ через `step00FirstCause`): тот же первопричинный декрет, что декретирует
      семь масок, ДЕКРЕТИРУЕТ и поставку истока каскада (его `0` = сингулярность космологического
      прочтения). Реализуется потреблением поля `step00FirstCause.nsBoundary` (третья граница
      декрета — гейт-закон энергобаланса НС). Каждый 🟡-Prop несёт НАСТОЯЩЕЕ содержание (объект
      закона `NsSolutionBalanceLaw` и/или зелёную стену невозможности), а НЕ `True`.

  ЧЕГО ЗДЕСЬ НЕТ (КРАСНЫЕ ЛИНИИ — ГРОМКО):
    • Это НЕ решение Навье–Стокса и НЕ объявление Клэя. Гейт-граница `nsBoundary` — выживший
      кандидат декрета, чья ЧЕСТНАЯ ЦЕНА раскрыта в карантине (закон, возможно, переплачивает).
    • Это НЕ доказательство КОНЕЧНО-ЭНЕРГЕТИЧЕСКОГО взрыва КП: §2bis/§2ter в `DyadicBlowup.lean`
      дают ОДНО точное самоподобное решение + класс с инвариантом фронта, но НЕ полную теорему КП.
    • Каскадный взрыв ПРИСОЕДИНЯЕТСЯ к маскам ТОЛЬКО через свой ИСТОК (n=0-насос), декретированный
      извне. ЗЕЛЁНЫЙ ВЫВОД ДРАЙВА (STEP A/B: ядро §1, самоподобие §2bis, инвариант фронта §2ter)
      САМОДОСТАТОЧЕН и НЕ ЗАВИСИТ от этого жёлтого слоя. Убери первопричину — зелёная математика
      взрыва останется целой; исчезнет лишь ответ на вопрос «кто зажёг n=0-насос».
    • Никакой связи с простыми числами напрямую — красная линия проекта нетронута (декрет общий).

  ТАИНТ РАСТЁТ НАМЕРЕННО. Все 🟡-декларации помечены `⚠️ AXIOM-TAINTED` и потребляют ЕДИНСТВЕННУЮ
  аксиому репозитория `step00FirstCause`. Ниже `#print axioms` МАШИННО подтверждает: 🟡-декларации
  несут `step00FirstCause`, а зелёная стена `DyadicBlowup.dyadicOrigin_uncausable_from_inside` — НЕТ
  (только стандартная тройка). Ни sorry, ни native_decide, ни НОВОЙ аксиомы.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/DyadicFirstCause.lean
  (покажет таинт в `#print axioms` — это ОЖИДАЕМО, не ошибка).
-/
import Mathlib
import EuclidsPath.Engine.DyadicBlowup
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath.DyadicFirstCause

open EuclidsPath.DyadicBlowup
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-- **`DyadicOriginDecreed` — НЕ-ВАКУУМНЫЙ Prop декретированного истока каскада.**

Пакует ДВА содержательных компонента (НЕ `True`):
  • `nsLaw` — фактический гейт-закон энергобаланса НС `NsSolutionBalanceLaw` (третья граница
    декрета первопричины), который снабжает исток каскада поставкой на крупнейшем масштабе;
  • `originUncausable` — доступность зелёной стены невозможности
    (`DyadicBlowup.dyadicOrigin_uncausable_from_inside` для конкретных `λ>1`, `t<T`), т.е. факт,
    что исток НЕ причиним изнутри и потому НУЖДАЕТСЯ во внешнем декрете.

Тип обитаем ТОЛЬКО через реальный объект границы `nsLaw` — вакуумность исключена. -/
def DyadicOriginDecreed : Prop :=
  EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw ∧
    (∀ (lam T t : ℝ), 1 < lam → t < T →
      ¬ HasDerivAt (fun s => ssMode lam T 0 s)
          (kpRHS lam (fun _ => 0) (ssMode lam T) 0 t) t)

/-- **`dyadicOrigin_from_firstCause` — 🟡 ⚠️ AXIOM-TAINTED.**

Исток дядического каскада ДЕКРЕТИРОВАН первопричиной: поставка на крупнейшем масштабе `n=0`
берётся из поля `step00FirstCause.nsBoundary` (третья граница декрета — гейт-закон энергобаланса
НС). Вторая компонента — зелёная стена невозможности (`dyadicOrigin_uncausable_from_inside`), она
axiom-free, но здесь лишь ПРЕДЪЯВЛЯЕТСЯ как содержание, объясняющее НЕОБХОДИМОСТЬ декрета.

Таинт идёт РОВНО через `step00FirstCause` (первый конъюнкт). НОВОЙ аксиомы нет. -/
theorem dyadicOrigin_from_firstCause : DyadicOriginDecreed :=
  ⟨step00FirstCause.nsBoundary,
   fun _ _ _ hlam ht => dyadicOrigin_uncausable_from_inside hlam ht⟩

/-- **`dyadicBlowup_is_firstCauseManifestation` — 🟡 ⚠️ AXIOM-TAINTED (СЛОГАН, ДВЕ СТЕНЫ).**

Итоговый слоган манифестации, честно «две стены / декретированная поставка», а НЕ голое `True`.
Конъюнкция ссылается ОДНОВРЕМЕННО на:
  (1) 🟢 ЗЕЛЁНУЮ СТЕНУ невозможности `DyadicBlowup.dyadicOrigin_uncausable_from_inside` — исток
      каскада (n=0-насос) внутренне непричиним (axiom-free факт, здесь предъявлен);
  (2) 🟡 ДЕКРЕТИРОВАННУЮ ПОСТАВКУ `dyadicOrigin_from_firstCause` — тот же первопричинный декрет,
      что декретирует семь масок, снабжает этот исток извне (таинт `step00FirstCause`);
  (3) 🟡 сам объект третьей границы `step00FirstCause.nsBoundary` — что делает тип обитаемым лишь
      через принятую границу (никакой вакуумности).

Эпистемический итог: каскадный взрыв присоединяется к маскам ТОЛЬКО через свой исток; зелёная
математика драйва (STEP A/B) от этого слоя НЕ зависит. Таинт — только через (2) и (3). -/
theorem dyadicBlowup_is_firstCauseManifestation :
    (∀ (lam T t : ℝ), 1 < lam → t < T →
        ¬ HasDerivAt (fun s => ssMode lam T 0 s)
            (kpRHS lam (fun _ => 0) (ssMode lam T) 0 t) t) ∧
      DyadicOriginDecreed ∧
      EuclidsPath.NavierStokesFront.NsSolutionBalanceLaw :=
  ⟨fun _ _ _ hlam ht => dyadicOrigin_uncausable_from_inside hlam ht,
   dyadicOrigin_from_firstCause,
   step00FirstCause.nsBoundary⟩

/-!
  ### Машинная честность таинта (ожидания)

  * Обе 🟡-декларации ниже — сверх стандартной тройки `propext`, `Classical.choice`, `Quot.sound`
    несут РОВНО `step00FirstCause` (через `.nsBoundary`).
  * Для контраста: зелёная стена `DyadicBlowup.dyadicOrigin_uncausable_from_inside` (и
    `bottomForcing_pos`) — ТОЛЬКО стандартная тройка, БЕЗ `step00FirstCause`. Это подтверждает,
    что зелёный вывод самодостаточен, а таинт локализован в этом файле.
-/

-- 🟡 ДОЛЖНЫ показать step00FirstCause:
#print axioms dyadicOrigin_from_firstCause
#print axioms dyadicBlowup_is_firstCauseManifestation

-- 🟢 КОНТРОЛЬ (для сравнения): НЕ должны показывать step00FirstCause.
#print axioms dyadicOrigin_uncausable_from_inside
#print axioms bottomForcing_pos

end EuclidsPath.DyadicFirstCause
