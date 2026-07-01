/-
  Labelled fan-in patch для GlobalOldAbsorption — Step00 финальный узел, версия v2.
  Источник: step00_labelled_fanin_patch_ru_2026-07-01.md (словесная спецификация).
  Проза: prose/24_BoundaryDecomp.md (обновить), README.

  АРХИТЕКТУРНЫЙ ПАТЧ: заменить невозможный путь `InfiniteNodeableCenters ⟹ CoreCollision ⟹ Engine`
  (невозможен, т.к. separating scale делает CoreSig ИНЪЕКТИВНЫМ — коллизии нет) на путь через
  labelled fan-in по РЕАЛЬНЫМ арифметическим шагам:

    GlobalOldAbsorption ⟹ LabelledFanIn ∨ InfiniteLegalDescent      (дихотомия — König)
    ¬InfiniteLegalDescent                                            (EPMI)
    LabelledFanIn ⟹ EuclideanEngine                                 (local label determinism)

  ЧЕСТНЫЙ СТАТУС (аудит внутри файла):
  Что ДОКАЗАНО здесь (абстрактно, стандартные аксиомы):
    * дихотомия при ЯВНОМ входе `no_labelled_fanin ⟹ InfiniteLegalDescent` (König через
      dependent choice) — сама König-конструкция;
    * `labelledFanIn_to_engine` из `LocalLabelDeterminism` — чистая логика;
    * `localLabelDeterminism` из `BoundaryLabelDeterminism` + `SNOLLabelDeterminism` + separating scale
      — сборка case-split;
    * `globalAbsorption_to_engine` — финальная упаковка.
  Что ОСТАЁТСЯ ВХОДОМ (гипотезы, НЕ доказаны — новая локализация узла):
    * `BoundaryLabelDeterminism` — что boundary-код детерминирует предшественника ∨ engine
      (требует `boundaryStep_normalForm` — нормальную форму boundary-шага, НЕ доказана);
    * `SNOLLabelDeterminism` — то же для SNOL (= SNOLHall ⟹ engine, старая SNOL-стена);
    * finite `EdgeSig` — при фиксированном A: конечность кодов (правдоподобно, но каждый код-тип
      нужно предъявить конечным — не сделано абстрактно).

  ВЫВОД (подтверждён адверсариальным аудитом 8 агентов, 2026-07-01): патч НЕ закрывает Step00. Он
  ПЕРЕНОСИТ единственный узел с «fan-in ⟹ engine» (счётная стена) на «label determinism ⟹ engine»
  (boundary/SNOL нормальная форма). Это лучшая локализация (structural, не counting), НО:
    • `hComp`-вход содержит SNOL-случай, который есть РОВНО старая SNOL/Hall стена (`SNOLBoundary`
      неинъективен ⟹ engine) — та же нагрузка, что `pump` в `BoundaryDecomp.global_absorber_forces_engine`;
      переименована, не снята;
    • `hKonig` (König-ветвь §7.2, finitely-branching ∞ reverse-tree ⟹ ∞ ветвь) — недоказанная
      комбинаторика; discharge-цель — `Order.KonigLemma` (mathlib) при инстанциации reverse-tree;
    • эта машина АБСТРАКТНА: `σ`, `RealStep`, `edgeSig`, `EuclideanEngine` не привязаны к конкретному
      графу `6m±1`/`TwinCenterZ`; `globalAbsorption_refutes_under_epmi` (§17) даёт лишь СОВМЕСТИМОСТЬ
      формы с `no_global_absorption_under_epmi`, а не выводимость twin.
  Честно доказаны (axiom-free): `labelledFanIn_to_engine`, `descend_along_pred`, `localLabelDeterminism`
  (настоящая сборка через `hKindEq`, не алиас). Красная линия НЕ пересечена (нет вероятностей/плотности).
  Step00.twin_prime_conjecture остаётся `sorry` — узел не закрыт, а точнее локализован.

  ИСТОРИЯ ИСПРАВЛЕНИЙ v1→v2 (после аудита): (1) убрана ложная посылка `∀ s, {u // RealStep u s}`
  (absorber — корень без предшественника) → `KonigBranchInput` с премиссой `GlobalOldAbsorption`;
  (2) `descend_of_has_predecessor` переименован в `descend_along_pred` — это итерация, НЕ König;
  (3) `localLabelDeterminism` больше не `:= hComp`: настоящий case-split по тегу `kind`;
  (4) `ComponentDeterminism` — реальная конъюнкция пяти `KindDeterminism`, не алиас полного узла.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.BoundaryDecomp

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace EuclidsPath.LabelledFanIn

/-! ### §2–3. Абстрактный real-step граф и path-absorbed

Мы работаем в абстрактной модели: тип состояний `σ`, отношение реального шага `RealStep`,
предикат old-absorber `OldAbsorber`. Конкретная инстанциация (ActiveDelete/OldPeel/BoundaryExit/
SNOL/OldCorridor) даётся в прозе; здесь фиксируем только СВОЙСТВА, нужные для дихотомии.

`Absorbed` — это PATH-свойство (терминальное), а НЕ локальный конструктор шага: старт поглощён,
если из него есть конечный real-step путь в absorber. Это ключевой архитектурный пункт §1: убрать
примитивный `AbsorberStep`, который давал произвольный many-to-one collapse. -/

variable {σ : Type*}

/-- Рефлексивно-транзитивное замыкание `RealStep`: конечный путь `s → … → O`. -/
def Path (RealStep : σ → σ → Prop) : σ → σ → Prop := Relation.ReflTransGen RealStep

/-- `Absorbed s` — из `s` есть конечный real-step путь в старый absorber. Path-свойство, не шаг. -/
def Absorbed (RealStep : σ → σ → Prop) (OldAbsorber : σ → Prop) (s : σ) : Prop :=
  ∃ O, OldAbsorber O ∧ Path RealStep s O

/-- **`GlobalOldAbsorption`** — редукционная цель (§3): бесконечно много различных легальных свежих
    стартов, каждый из которых поглощается (есть конечный real-step путь в absorber). Это абстрактная
    форма `BoundaryDecomp.GlobalOldTwinAbsorption`; премисса König-ветви. -/
def GlobalOldAbsorption (RealStep : σ → σ → Prop) (OldAbsorber : σ → Prop) (Fresh : σ → Prop) : Prop :=
  { s : σ | Fresh s ∧ Absorbed RealStep OldAbsorber s }.Infinite

/-! ### §6. InfiniteLegalDescent -/

/-- Бесконечный строго-нисходящий real-step спуск: `X (n+1) → X n` для всех `n`. -/
def InfiniteLegalDescent (RealStep : σ → σ → Prop) : Prop :=
  ∃ X : ℕ → σ, ∀ n, RealStep (X (n + 1)) (X n)

/-! ### §5. LabelledFanIn -/

/-- `LabelledFanIn`: два РАЗНЫХ легальных предшественника `U₁ ≠ U₂` одного `V` с ОДИНАКОВОЙ меткой
    ребра. Это то, что должно порождать engine (через label determinism). -/
def LabelledFanIn {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) : Prop :=
  ∃ U₁ U₂ V, U₁ ≠ U₂ ∧ Legal U₁ ∧ Legal U₂ ∧ Legal V ∧
    RealStep U₁ V ∧ RealStep U₂ V ∧ edgeSig U₁ V = edgeSig U₂ V

/-! ### §14. LocalLabelDeterminism -/

/-- `LocalLabelDeterminism`: совпадение метки ребра у двух предшественников одного `V` влечёт
    их равенство ∨ engine. Это СОДЕРЖАТЕЛЬНЫЙ вход (boundary/SNOL/active нормальные формы). -/
def LocalLabelDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (EuclideanEngine : Prop) : Prop :=
  ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
    RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V →
    U₁ = U₂ ∨ EuclideanEngine

/-! ### §15. LabelledFanIn ⟹ Engine (ДОКАЗАНО — чистая логика) -/

/--
  **Theorem 15.1 (`labelledFanIn_to_engine`) — ДОКАЗАНА.** Если выполняется `LocalLabelDeterminism`,
  то `LabelledFanIn ⟹ EuclideanEngine`. Доказательство: из fan-in берём `U₁ ≠ U₂` с равной меткой;
  детерминизм даёт `U₁ = U₂ ∨ engine`; первое противоречит `U₁ ≠ U₂`, значит engine. -/
theorem labelledFanIn_to_engine {Lbl : Type*} {RealStep : σ → σ → Prop} {Legal : σ → Prop}
    {edgeSig : σ → σ → Lbl} {EuclideanEngine : Prop}
    (hDet : LocalLabelDeterminism RealStep Legal edgeSig EuclideanEngine)
    (hFan : LabelledFanIn RealStep Legal edgeSig) : EuclideanEngine := by
  obtain ⟨U₁, U₂, V, hne, hL1, hL2, hLV, hs1, hs2, hsig⟩ := hFan
  rcases hDet U₁ U₂ V hL1 hL2 hLV hs1 hs2 hsig with heq | heng
  · exact absurd heq hne
  · exact heng

/-! ### §7. Дихотомия — честная форма и точная локализация несводённого ядра

Утверждение §7.1: из `GlobalOldAbsorption` (∞ поглощённых стартов) + конечности absorbers + конечности
`EdgeSig` следует `LabelledFanIn ∨ InfiniteLegalDescent`.

Логический скелет §7.2:
  ¬LabelledFanIn ⟹ для каждой пары (target V, label λ) ≤ 1 предшественник ⟹ reverse-tree finitely
  branching ⟹ (bounded depth ⟹ finitely many sources, противоречие с ∞) ∨ (unbounded depth ⟹ König
  ⟹ InfiniteLegalDescent).

ЧЕСТНАЯ ГРАНИЦА ФОРМАЛИЗАЦИИ. Мы НЕ утверждаем, что «нет fan-in ⟹ у каждого состояния есть
предшественник»: absorber `O` — КОРЕНЬ reverse-tree и предшественника-вниз НЕ имеет, так что такая
посылка ложна-как-записана. Настоящее ядро König-ветви — не «total pred», а извлечение бесконечной
ветви из finitely-branching бесконечного дерева. Это в точности `Order.KonigLemma` в mathlib
(`exists_seq_forall_proj_of_forall_finite`), и именно на неё должна опираться правая ветвь.

Поэтому мы разделяем две вещи:
  1. `descend_along_pred` — axiom-free ХЕЛПЕР (dependent-choice спуск вдоль ДАННОЙ функции
     предшественников на ДОСТИЖИМОМ поддомене), НЕ König сам по себе;
  2. `KonigBranchInput` — ЯВНЫЙ вход, честно кодирующий недоказанную комбинаторику §7.2 case 2
     (finitely-branching ∞ reverse-tree ⟹ ∞ ветвь). Discharge-цель для него — mathlib König. -/

/--
  **`descend_along_pred` — ДОКАЗАНА (dependent-choice, axiom-free ХЕЛПЕР).** Если задан ИНВАРИАНТНЫЙ
  поддомен `D` (`s₀ ∈ D`) и на нём тотальная функция предшественника, возвращающая предшественника
  СНОВА в `D`, то строится бесконечный нисходящий real-step спуск. Это чистая рекурсия по `Nat`,
  БЕЗ König: ветвь нам уже дана функцией `pred`, мы её лишь итерируем.

  Замечание: это НЕ König. König извлекает такую ветвь из finitely-branching бесконечного дерева
  (см. `KonigBranchInput`); здесь ветвь предполагается заданной. -/
theorem descend_along_pred {RealStep : σ → σ → Prop} (D : σ → Prop) (s₀ : σ) (hs₀ : D s₀)
    (pred : ∀ s, D s → { u : σ // RealStep u s ∧ D u }) :
    InfiniteLegalDescent RealStep := by
  -- рекурсия с носителем инварианта D: строим ⟨состояние, доказательство D⟩
  let Y : ℕ → { s : σ // D s } :=
    fun n => Nat.rec ⟨s₀, hs₀⟩ (fun _ prev => ⟨(pred prev.val prev.property).val,
      (pred prev.val prev.property).property.2⟩) n
  refine ⟨fun n => (Y n).val, fun n => ?_⟩
  -- RealStep (Y (n+1)).val (Y n).val — из спецификации pred
  exact (pred (Y n).val (Y n).property).property.1

/--
  **`KonigBranchInput` — ЯВНЫЙ вход (§7.2 case 2, НЕ доказан здесь), ТЕПЕРЬ С ПРЕМИССОЙ.** Честная
  упаковка König-ветви: «ЕСЛИ бесконечно много поглощённых стартов (`GlobalOldAbsorption`) И labelled
  fan-in отсутствует, ТО извлекается бесконечный нисходящий real-step спуск». Без премиссы
  `GlobalOldAbsorption` импликация `¬fanin ⟹ InfiniteLegalDescent` была бы ЛОЖНА (конечный ацикличный
  граф: ни fan-in, ни спуска). Премисса восстанавливает верность: именно бесконечность источников +
  finitely-branching (из ¬fanin) даёт König-ветвь. Discharge-цель: `Order.KonigLemma` (mathlib) при
  инстанциации reverse-tree; конечность `EdgeSig` — тоже нужный, здесь не предъявленный вход. Пока — вход. -/
def KonigBranchInput {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop) (OldAbsorber : σ → Prop)
    (Fresh : σ → Prop) (edgeSig : σ → σ → Lbl) : Prop :=
  GlobalOldAbsorption RealStep OldAbsorber Fresh →
    ¬ LabelledFanIn RealStep Legal edgeSig → InfiniteLegalDescent RealStep

/--
  **Дихотомия (`absorption_labelled_dichotomy`) — ДОКАЗАНА при явном König-входе + `GlobalOldAbsorption`.**
  Тривиальный case-split: либо есть fan-in, либо König-вход (при бесконечности absorbed) даёт спуск.
  Вся НЕтривиальность — в `KonigBranchInput` (недоказанная комбинаторика §7.2), что отражено явно. -/
theorem absorption_labelled_dichotomy {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hKonig : KonigBranchInput RealStep Legal OldAbsorber Fresh edgeSig) :
    LabelledFanIn RealStep Legal edgeSig ∨ InfiniteLegalDescent RealStep := by
  by_cases hfan : LabelledFanIn RealStep Legal edgeSig
  · exact Or.inl hfan
  · exact Or.inr (hKonig hGlobal hfan)

/-! ### §8. Убираем ветвь бесконечного спуска (EPMI) -/

/--
  **`globalAbsorption_to_labelledFanIn` — ДОКАЗАНА при явных входах.** Если бесконечный спуск
  запрещён (EPMI, `hNoInf`), дихотомия схлопывается в `LabelledFanIn`. -/
theorem globalAbsorption_to_labelledFanIn {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hKonig : KonigBranchInput RealStep Legal OldAbsorber Fresh edgeSig)
    (hNoInf : ¬ InfiniteLegalDescent RealStep) :
    LabelledFanIn RealStep Legal edgeSig := by
  rcases absorption_labelled_dichotomy hGlobal hKonig with hfan | hinf
  · exact hfan
  · exact absurd hinf hNoInf

/-! ### §14.2. LocalLabelDeterminism из компонент (ДОКАЗАНА — сборка)

`localLabelDeterminism` собирается из детерминизмов подтипов шага. Чтобы сборка была НАСТОЯЩЕЙ (а не
переименованием), мы вводим классификатор шага `kind : σ → σ → Kind` (тег ребра: active/oldPeel/
boundary/snol/corridor), согласованный с `edgeSig` (равные метки ⟹ равные теги — `kind_of_edgeSig`),
и ПЯТЬ отдельных компонентных детерминизмов. Сборка `localLabelDeterminism` тогда — реальный
case-split по тегу с mixed-case, закрытым согласованностью тегов. Содержательная нагрузка — в пяти
компонентах (§11–13), особенно в `snol` (= старая SNOL/Hall стена); они здесь входы. -/

/-- Тег real-step ребра: пять взаимоисключающих сортов шага (§2). -/
inductive Kind | active | oldPeel | boundary | snol | corridor
deriving DecidableEq

/-- Один компонентный детерминизм: для ребер данного тега `k` равная метка ⟹ равенство ∨ engine. -/
def KindDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) (EuclideanEngine : Prop) (k : Kind) : Prop :=
  ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
    RealStep U₁ V → RealStep U₂ V → kind U₁ V = k → kind U₂ V = k →
    edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂ ∨ EuclideanEngine

/-- **`ComponentDeterminism` — настоящая конъюнкция пяти под-детерминизмов** (§11–13), а НЕ алиас
    полного утверждения. Каждый сорт шага обслуживается своим компонентом. -/
def ComponentDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) (EuclideanEngine : Prop) : Prop :=
  (∀ k, KindDeterminism RealStep Legal edgeSig kind EuclideanEngine k)

/--
  **`localLabelDeterminism` — ДОКАЗАНА (НАСТОЯЩАЯ сборка, не алиас).** Дан классификатор `kind`,
  согласованный с `edgeSig` (`hKindEq`: равные метки ⟹ равные теги), и пять компонентных детерминизмов
  (`hComp`). Тогда `LocalLabelDeterminism` выводится case-split'ом: для пары `U₁,U₂ → V` с равной
  меткой теги `kind U₁ V` и `kind U₂ V` РАВНЫ (из `hKindEq`), значит оба равны какому-то `k`, и
  компонент `hComp k` даёт `U₁ = U₂ ∨ engine`. Mixed-case (разные теги) исключён самим `hKindEq`.

  Это реальный вывод: он НЕ равен `hComp` синтаксически — он использует `hKindEq` и разбор тега.
  Нагрузка — в пяти компонентах (входы), но СБОРКА доказана. -/
theorem localLabelDeterminism {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} {EuclideanEngine : Prop}
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine) :
    LocalLabelDeterminism RealStep Legal edgeSig EuclideanEngine := by
  intro U₁ U₂ V hL1 hL2 hLV hs1 hs2 hsig
  -- теги совпадают из согласованности edgeSig↔kind
  have htag : kind U₁ V = kind U₂ V := hKindEq U₁ U₂ V hsig
  -- применяем компонент, отвечающий тегу kind U₁ V
  exact hComp (kind U₁ V) U₁ U₂ V hL1 hL2 hLV hs1 hs2 rfl htag.symm hsig

/-! ### §16. Global absorption ⟹ engine (ДОКАЗАНА при явных входах) -/

/--
  **Theorem 16.1 (`globalAbsorption_to_engine`) — ДОКАЗАНА при ТРЁХ явных входах.** Сборка всей цепи:
  дихотомия + EPMI (нет спуска) даёт `LabelledFanIn`; local label determinism превращает его в engine.
  Логика сборки тривиальна; вся математика — в трёх входах, ни один из которых здесь не доказан:

    * `hKonig : KonigBranchInput` — König-ветвь §7.2 (finitely-branching ∞ reverse-tree ⟹ ∞ спуск).
      Discharge-цель: `Order.KonigLemma` (mathlib) при инстанциации reverse-tree. НЕ доказан.
    * `hNoInf : ¬ InfiniteLegalDescent` — EPMI. ДОКАЗУЕМ через `no_infiniteLegalDescent_of_height`,
      если real-step строго уменьшает высоту (см. ниже). Здесь — вход.
    * `hComp : ComponentDeterminism` — компонентный label determinism (boundary/SNOL/active нормальные
      формы, §11–13). Его SNOL-случай — это СТАРАЯ SNOL/SNOLHall стена (`SNOLBoundary` неинъективен
      ⟹ engine). НЕ доказан.

  ВЫВОД: узел `GlobalOldAbsorption` НЕ закрыт — он ПЕРЕНЕСЁН на `hKonig ∧ hComp`. Это structural
  локализация вместо counting fan-in, но `hComp` содержит несведённую SNOL-стену. -/
theorem globalAbsorption_to_engine {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} {EuclideanEngine : Prop}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hKonig : KonigBranchInput RealStep Legal OldAbsorber Fresh edgeSig)
    (hNoInf : ¬ InfiniteLegalDescent RealStep)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine) :
    EuclideanEngine := by
  have hfan : LabelledFanIn RealStep Legal edgeSig :=
    globalAbsorption_to_labelledFanIn hGlobal hKonig hNoInf
  exact labelledFanIn_to_engine (localLabelDeterminism hKindEq hComp) hfan

/-! ### EPMI-мост: `¬InfiniteLegalDescent` из высоты (ДОКАЗАНО)

Показываем, что ветвь `hNoInf` — не гипотеза, а следствие двигателя: если каждый real-step строго
уменьшает натуральную высоту, бесконечного спуска нет (`no_infinite_descent`). -/

/--
  **`no_infiniteLegalDescent_of_height` — ДОКАЗАНА.** Если `RealStep u v ⟹ height u < height v`
  (шаг вниз уменьшает высоту), то `InfiniteLegalDescent` невозможен. Здесь `X (n+1) → X n` даёт
  `height (X (n+1)) < height (X n)` — строго убывающая цепь в ℕ, запрещена well-foundedness.

  (Замечание о направлении: в `InfiniteLegalDescent` ребро идёт `X (n+1) → X n`, т.е. `X (n+1)` —
  предшественник, поэтому его высота МЕНЬШЕ; убывает `height ∘ X`.) -/
theorem no_infiniteLegalDescent_of_height {RealStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v) :
    ¬ InfiniteLegalDescent RealStep := by
  rintro ⟨X, hX⟩
  -- height (X (n+1)) < height (X n): строго убывающая ℕ-цепь ⟹ противоречие через
  -- невозможность бесконечного спуска (тот же двигатель `no_infinite_descent`, A=1).
  refine EuclidsPath.Engine.no_infinite_descent (A := 1) (le_refl 1)
    (fun k => height (X k)) (fun n => ?_)
  -- DescentStep 1 (height (X n)) (height (X (n+1))) := 1 * height (X (n+1)) < height (X n)
  show 1 * height (X (n + 1)) < height (X n)
  have := hdrop (hX n)   -- height (X (n+1)) < height (X n)
  omega

/-! ### §17. Мост к живому пути Step00 (честная связь, НЕ закрытие)

Абстрактная машина выше сама по себе — остров: `EuclideanEngine` — свободная `Prop`, `σ` абстрактно.
Чтобы связь с реальным узлом была не декларацией, а типом, инстанциируем `EuclideanEngine := False`
(EPMI: двигатель НЕВОЗМОЖЕН, `no_perpetual_engine`). Тогда `globalAbsorption_to_engine` даёт `False`
из своих входов — то есть ОПРОВЕРГАЕТ `GlobalOldAbsorption`. Это ровно форма
`BoundaryDecomp.no_global_absorption_under_epmi`: «глобальное поглощение + запрет двигателя ⟹ ⊥».

Честный статус моста: он ЛОГИЧЕСКИ соединяет абстрактную машину с формой Step00-узла, но НЕ закрывает
его — три входа (`hKonig`, `hNoInf`, `hComp`) остаются недоказанными, а привязка `σ`/`RealStep`/`edgeSig`
к конкретному графу `6m±1` (`Residuals.TwinCenterZ`, `ProductCore.CoreSig`) здесь НЕ предъявлена.
Мост показывает СОВМЕСТИМОСТЬ формы, а не выводимость twin. -/

/--
  **`globalAbsorption_refutes_under_epmi` — ДОКАЗАНА при явных входах (мост-совместимость).**
  При `EuclideanEngine := False` (EPMI) абстрактная цепь опровергает `GlobalOldAbsorption`. Это
  та же контрапозиция, что `no_global_absorption_under_epmi`, но выраженная через labelled-fan-in
  машину. По-прежнему держится на трёх недоказанных входах — НЕ закрытие Step00. -/
theorem globalAbsorption_refutes_under_epmi {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hKonig : KonigBranchInput RealStep Legal OldAbsorber Fresh edgeSig)
    (hNoInf : ¬ InfiniteLegalDescent RealStep)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind (EuclideanEngine := False)) :
    False :=
  globalAbsorption_to_engine hGlobal hKonig hNoInf hKindEq hComp

end EuclidsPath.LabelledFanIn
