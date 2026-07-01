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

  ВЫВОД (v3, brick `step00_hkonig_label_tree_closure...`, 2026-07-01): патч по-прежнему НЕ закрывает
  Step00, НО узел СУЩЕСТВЕННО сузился. Ключевое отличие v3 от v2: **König-ветвь ТЕПЕРЬ ДОКАЗАНА**
  (`absorption_labelled_dichotomy` — настоящая теорема, не вход). Осталась ровно ОДНА содержательная
  стена — `hComp`, а точнее её SNOL-случай `hHallSeed`:
    • ДОКАЗАНО (König закрыт, §7): `GlobalOldAbsorption` + конечность absorber'ов + конечный алфавит
      меток ⟹ `LabelledFanIn ∨ InfiniteLegalDescent`. Способ — state-level backward König: инвариант
      `ManyRoute V` (∞ источников доходят до V), пигонхол по КОНЕЧНЫМ предшественникам (`preds_finite`
      из ¬fanin + finite Lbl), итерация через dependent choice. Mathlib-König НЕ нужен — только два
      инфинит-фиберных пигонхола. Ложная посылка v1 «у каждого состояния есть предшественник» больше
      не фигурирует нигде.
    • ОСТАЛОСЬ (единственный содержательный вход): `hComp = ComponentDeterminism`, чьи четыре
      exact-компонента (active/oldPeel/boundary/corridor) — арифметика инстанциации, а пятый (`snol`)
      сводится (§24, `snol_kindDeterminism_of_normalForm` — ДОКАЗАНА сборка) к `hHallSeed`: «SNOL
      hall-seed с различными предшественниками ⟹ engine». Это РОВНО старая SNOL/Hall стена, та же
      нагрузка, что `pump` в `BoundaryDecomp.global_absorber_forces_engine`.
    • НЕ предъявлено: привязка `σ`/`RealStep`/`edgeSig` к конкретному графу `6m±1`/`TwinCenterZ`
      (машина абстрактна); `hOldFin`/`[Finite Lbl]`/`hAll` — правдоподобные, но в этой абстрактной
      форме принятые допущения инстанциации.
  Доказаны без аксиом: `labelledFanIn_to_engine`, `descent_from_manyRoute`, `localLabelDeterminism`,
  `componentDeterminism_of_components`, `snol_kindDeterminism_of_normalForm`. Красная линия НЕ пересечена
  (нет вероятностей/плотности — König чисто комбинаторный). Step00.twin_prime_conjecture остаётся
  `sorry` — узел не закрыт, но сведён к одной SNOL-импликации.

  ВЫВОД v4 (brick `snol_hallseed_strict_closure`, 2026-07-01; уточнён аудитом): SNOL-стена сведена к
  ЛЕГЧЕ сформулированному закону `SNOLHallSeedRegenerates` (seed ⟹ return-path — строго легче старой
  seed⇒engine стены), но нагрузка НЕ сжимается «к одной лемме». Ключевые новые факты (§26–27):
    • МАШИННО-ПРОВЕРЕННЫЙ NO-GO (`snolHallSeed_bare_no_go`): голая неинъективность SNOL-метки НЕ даёт
      engine (конкретная 3-состояний модель, где seed есть, а спуска нет). Честность встроена в тип.
    • ДОКАЗАНО закрытие SNOL при законе regeneration: `snolHallSeed_to_engine_of_regeneration`
      (axiom-free), `snol_kindDeterminism_of_regeneration`. Механизм: seed `Uᵢ→V` + возврат `V→⁺Uᵢ`
      = непустой цикл `Uᵢ→⁺Uᵢ`, запрещённый двигателем (`no_cycle_of_height`, единая ориентация высоты).
    • ВАЖНАЯ ОГОВОРКА (`regen_under_hdrop_kills_seed`, ДОКАЗАНА): под тем же `hdrop`, что закрывает всё
      остальное, seed и его regeneration ВЗАИМОИСКЛЮЧАЮЩИ (цикл). Значит `SNOLHallSeedRegenerates`
      выполняется лишь ВАКУУМНО (seed-empty), а РЕАЛЬНОЕ арифметическое содержание МИГРИРУЕТ в сам
      `hdrop` — существование строго-монотонной ко-высоты на `6m±1` (= ацикличность/EPMI), НЕ предъявлено.
  Это НЕ закрытие Step00, и остаток ЧЕСТНО делится минимум на: (a) `SNOLHallSeedRegenerates`; (b) `hdrop`
  (ко-высота/ацикличность на реальном графе — истинный носитель арифметики); (c) четыре компонента
  инъективности (под `Engine:=False` не бесплатны); (d) инстанциация. Нельзя сжимать до «осталась только
  SNOL-стена»:
    • `hAll : ∀x, Legal x` — ЛОЖНО на конкретном графе `6m±1` (легальность там — реальное ограничение);
      абстрактная дихотомия не инстанциируется напрямую без legality-restricted König (не сделан);
    • `[Finite Lbl]` — это counting/fan-in содержание в обличье typeclass (правдоподобно при фикс. A);
    • четыре exact-компонента + `hKindEq` — заявлены как арифметика инстанциации, но НЕ доказаны
      (инстанциации нет);
    • ГЛАВНОЕ: машина АБСТРАКТНА и не подключена — `EuclideanEngine` свободная `Prop`, `σ`/`RealStep`/
      `edgeSig` не привязаны к `TwinCenterZ`/`CoreSig`/`6m±1`, и ни один файл вне этого модуля не
      потребляет его теоремы. Поэтому закрытие `SNOLHallSeedRegenerates` само по себе НЕ закрыло бы
      `twin_prime_conjecture` — нужна ещё инстанциация к реальному графу.
  Step00.twin_prime_conjecture остаётся `sorry`. Прогресс реальный (König-вход стал теоремой), но
  узел не закрыт — он сведён к одной SNOL-лемме ПЛЮС инстанциация абстрактной машины.

  ИСТОРИЯ: v1→v2 (аудит 8 агентов): убрана ложная `∀ s` посылка; `descend` переименован; настоящий
  `localLabelDeterminism`; реальная конъюнкция `ComponentDeterminism`. v2→v3: König-ветвь ДОКАЗАНА
  (state-level backward König); `hComp` локализован до SNOL hall-seed стены. v3→v4: SNOL-стена сведена
  к `SNOLHallSeedRegenerates` (regeneration ⟹ cycle ⟹ ⊥) + машинно-проверенный no-go для голого seed.
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

/-- Бесконечный real-step спуск: `X (n+1) → X n` для всех `n`. (Строгость/различность НЕ встроены —
    определение допускает циклы/self-loop; строгость реализуется ВНЕШНЕ гипотезой высоты, см.
    `no_infiniteLegalDescent_of_height`. Как лемма о строгом убывании нигде не используется.) -/
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

/-! ### §7. Дихотомия — ТЕПЕРЬ ДОКАЗАНА (state-level backward König)

Утверждение §7.1: из `GlobalOldAbsorption` (∞ поглощённых стартов) + конечности absorbers + конечности
`EdgeSig` следует `LabelledFanIn ∨ InfiniteLegalDescent`. В версии v2 это был вход `KonigBranchInput`;
здесь (v3, brick `step00_hkonig_label_tree_closure...`) König-ветвь **доказана** без ложной посылки
«у каждого состояния есть предшественник».

СПОСОБ. Вместо label-prefix-tree + `stateAtPrefix`-реконструкции (хрупкой) мы ведём König прямо на
состояниях, через инвариант `ManyRoute V` := «бесконечно много свежих источников имеют путь в `V`».
Ключ — что при `¬LabelledFanIn` **предшественники любого `V` конечны** (метка ребра инъективна на
предшественниках, `preds_finite`), поэтому из `ManyRoute V` пигонхолом получаем предшественника `U`
(`RealStep U V`) с `ManyRoute U` (`manyRoute_pred`). Итерация (dependent choice) даёт бесконечный
спуск. Начальный `ManyRoute O` — из пигонхола по конечным absorber'ам (`manyRoute_absorber`).
Никакой mathlib-König не нужен: вся комбинаторика — два инфинит-фиберных пигонхола + рекурсия. -/

/-- `PathR` — рефлексивно-транзитивное замыкание (тот же `Path`, локальный синоним для лемм König). -/
abbrev PathR (RealStep : σ → σ → Prop) : σ → σ → Prop := Path RealStep

/-- `ManyRoute V` — бесконечно много свежих источников имеют real-step путь в `V`. Инвариант König. -/
def ManyRoute (RealStep : σ → σ → Prop) (Fresh : σ → Prop) (V : σ) : Prop :=
  {s | Fresh s ∧ Path RealStep s V}.Infinite

/--
  **`preds_finite` — ДОКАЗАНА.** При `¬LabelledFanIn` (уникальность предшественника по метке) и
  конечном алфавите меток предшественники любого `V` образуют конечное множество: отображение
  `U ↦ edgeSig U V` инъективно на `{U | RealStep U V}`, а образ конечен. -/
theorem preds_finite {Lbl : Type*} [Finite Lbl] {RealStep : σ → σ → Prop} {edgeSig : σ → σ → Lbl}
    {V : σ}
    (huniq : ∀ U₁ U₂, RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂) :
    {U | RealStep U V}.Finite := by
  have hinj : Set.InjOn (fun U => edgeSig U V) {U | RealStep U V} := fun a ha b hb hab =>
    huniq a b ha hb hab
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-- Уникальность предшественника по метке — прямое переписывание `¬LabelledFanIn`. -/
theorem unique_predecessor_of_no_labelledFanIn {Lbl : Type*} {RealStep : σ → σ → Prop}
    {Legal : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hNoFan : ¬ LabelledFanIn RealStep Legal edgeSig)
    (hAll : ∀ x, Legal x) {U₁ U₂ V : σ}
    (hs1 : RealStep U₁ V) (hs2 : RealStep U₂ V) (hsig : edgeSig U₁ V = edgeSig U₂ V) : U₁ = U₂ := by
  by_contra hne
  exact hNoFan ⟨U₁, U₂, V, hne, hAll U₁, hAll U₂, hAll V, hs1, hs2, hsig⟩

/--
  **`manyRoute_pred` — ДОКАЗАНА (ключевой шаг спуска König).** Если бесконечно много источников
  доходят до `V` (`ManyRoute V`), то (при уникальности предшественника по метке и конечном алфавите)
  найдётся предшественник `U` (`RealStep U V`), до которого доходит тоже бесконечно много (`ManyRoute U`).
  Доказательство: источники `≠ V` факторизуются через предшественников `V` (`ReflTransGen.cases_tail`);
  предшественников конечно (`preds_finite`); пигонхол по конечному множеству предшественников. -/
theorem manyRoute_pred {Lbl : Type*} [Finite Lbl] {RealStep : σ → σ → Prop} {Fresh : σ → Prop}
    {edgeSig : σ → σ → Lbl}
    (huniq : ∀ V U₁ U₂, RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂)
    {V : σ} (hV : ManyRoute RealStep Fresh V) :
    ∃ U, RealStep U V ∧ ManyRoute RealStep Fresh U := by
  set S := {s | Fresh s ∧ Path RealStep s V} with hS
  have hpick : ∀ s ∈ S, s ≠ V → ∃ U, RealStep U V ∧ Path RealStep s U := by
    intro s hs hne
    rcases (Relation.ReflTransGen.cases_tail hs.2) with h | ⟨U, hsU, hUV⟩
    · exact absurd h.symm hne
    · exact ⟨U, hUV, hsU⟩
  have hS'inf : {s ∈ S | s ≠ V}.Infinite := by
    have hEq : {s ∈ S | s ≠ V} = S \ {V} := by
      ext s; constructor <;> intro h <;> simp_all
    rw [hEq]; exact hV.diff (Set.finite_singleton V)
  choose! pick hpick1 hpick2 using hpick
  have hpredfin : {U | RealStep U V}.Finite := preds_finite (huniq V)
  have hfiber : ∃ U ∈ {U | RealStep U V}, {s ∈ {s ∈ S | s ≠ V} | pick s = U}.Infinite := by
    by_contra h
    push_neg at h
    have hcov : {s ∈ S | s ≠ V} ⊆ ⋃ U ∈ {U | RealStep U V}, {s ∈ {s ∈ S | s ≠ V} | pick s = U} := by
      intro s hs
      simp only [Set.mem_iUnion]
      exact ⟨pick s, hpick1 s hs.1 hs.2, hs, rfl⟩
    exact hS'inf ((hpredfin.biUnion (fun U hU => h U hU)).subset hcov)
  obtain ⟨U, hUV, hUinf⟩ := hfiber
  refine ⟨U, hUV, hUinf.mono ?_⟩
  intro s hs
  refine ⟨hs.1.1.1, ?_⟩
  have hp := hpick2 s hs.1.1 hs.1.2
  rw [hs.2] at hp; exact hp

/--
  **`manyRoute_absorber` — ДОКАЗАНА (начальный узел König).** Из `GlobalOldAbsorption` (∞ поглощённых
  свежих источников) и конечности absorber'ов пигонхолом получаем ОДИН absorber `O`, до которого
  доходит бесконечно много источников (`ManyRoute O`). -/
theorem manyRoute_absorber {RealStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite) :
    ∃ O, OldAbsorber O ∧ ManyRoute RealStep Fresh O := by
  set G := {s | Fresh s ∧ Absorbed RealStep OldAbsorber s} with hG
  have hpick : ∀ s ∈ G, ∃ O, OldAbsorber O ∧ Path RealStep s O := fun s hs => hs.2
  choose! Ω hΩ1 hΩ2 using hpick
  have hfiber : ∃ O ∈ {O | OldAbsorber O}, {s ∈ G | Ω s = O}.Infinite := by
    by_contra h
    push_neg at h
    have hcov : G ⊆ ⋃ O ∈ {O | OldAbsorber O}, {s ∈ G | Ω s = O} := by
      intro s hs; simp only [Set.mem_iUnion]; exact ⟨Ω s, hΩ1 s hs, hs, rfl⟩
    exact hGlobal ((hOldFin.biUnion (fun O hO => h O hO)).subset hcov)
  obtain ⟨O, hO, hOinf⟩ := hfiber
  refine ⟨O, hO, hOinf.mono ?_⟩
  intro s hs
  exact ⟨hs.1.1, by have := hΩ2 s hs.1; rwa [hs.2] at this⟩

/--
  **`descent_from_manyRoute` — ДОКАЗАНА (итерация König через dependent choice).** Если у каждого `V`
  с `ManyRoute V` есть предшественник `U` с `ManyRoute U`, то из `ManyRoute O` строится бесконечный
  real-step спуск. Рекурсия по `Nat` с носителем инварианта `ManyRoute`. -/
theorem descent_from_manyRoute {RealStep : σ → σ → Prop} {Fresh : σ → Prop}
    (step : ∀ V, ManyRoute RealStep Fresh V → ∃ U, RealStep U V ∧ ManyRoute RealStep Fresh U)
    {O : σ} (hO : ManyRoute RealStep Fresh O) : InfiniteLegalDescent RealStep := by
  choose predOf hpred1 hpred2 using step
  let Y : ℕ → {V : σ // ManyRoute RealStep Fresh V} :=
    fun n => Nat.rec ⟨O, hO⟩ (fun _ prev => ⟨predOf prev.val prev.property,
      hpred2 prev.val prev.property⟩) n
  exact ⟨fun n => (Y n).val, fun n => hpred1 (Y n).val (Y n).property⟩

/--
  **Дихотомия (`absorption_labelled_dichotomy`) — ТЕПЕРЬ ДОКАЗАНА (не вход!).** Из `GlobalOldAbsorption`
  + конечности absorber'ов + конечности алфавита меток + всеобщей легальности следует
  `LabelledFanIn ∨ InfiniteLegalDescent`. Если fan-in есть — левая ветвь. Если нет — уникальность
  предшественника по метке (`unique_predecessor_of_no_labelledFanIn`) запускает state-level König:
  `manyRoute_absorber → manyRoute_pred (итер.) → descent_from_manyRoute`. Это строгое закрытие `hKonig`. -/
theorem absorption_labelled_dichotomy {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x) :
    LabelledFanIn RealStep Legal edgeSig ∨ InfiniteLegalDescent RealStep := by
  by_cases hfan : LabelledFanIn RealStep Legal edgeSig
  · exact Or.inl hfan
  · refine Or.inr ?_
    -- ¬fanin ⟹ уникальность предшественника по метке
    have huniq : ∀ V U₁ U₂, RealStep U₁ V → RealStep U₂ V → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂ :=
      fun V U₁ U₂ hs1 hs2 hsig => unique_predecessor_of_no_labelledFanIn hfan hAll hs1 hs2 hsig
    obtain ⟨O, _, hO⟩ := manyRoute_absorber hGlobal hOldFin
    exact descent_from_manyRoute (fun V hV => manyRoute_pred huniq hV) hO

/-! ### §8. Убираем ветвь бесконечного спуска (EPMI) -/

/--
  **`globalAbsorption_to_labelledFanIn` — ДОКАЗАНА (König закрыт).** Если бесконечный спуск запрещён
  (EPMI, `hNoInf`), доказанная дихотомия схлопывается в `LabelledFanIn`. König-ветвь больше не вход. -/
theorem globalAbsorption_to_labelledFanIn {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hNoInf : ¬ InfiniteLegalDescent RealStep) :
    LabelledFanIn RealStep Legal edgeSig := by
  rcases absorption_labelled_dichotomy hGlobal hOldFin hAll (edgeSig := edgeSig) with hfan | hinf
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
  **Theorem 16.1 (`globalAbsorption_to_engine`) — ДОКАЗАНА (König закрыт; остался ОДИН вход `hComp`).**
  Сборка всей цепи: доказанная дихотомия + EPMI (нет спуска) даёт `LabelledFanIn`; local label
  determinism превращает его в engine. König-ветвь БОЛЬШЕ НЕ ВХОД (доказана в §7).

  Входы теперь: `hGlobal` (редукционная цель), `hOldFin` (конечность absorber'ов — правдоподобно:
  absorber'ы `≤ M₀`), `[Finite Lbl]` (конечность алфавита меток при фиксированном A), `hAll`
  (всеобщая легальность в абстрактной модели), `hNoInf` (EPMI — ДОКАЗУЕМ через
  `no_infiniteLegalDescent_of_height`), `hKindEq` (согласованность edgeSig↔kind), и — ЕДИНСТВЕННЫЙ
  содержательный несведённый вход — `hComp : ComponentDeterminism`, чей SNOL-случай есть РОВНО старая
  SNOL/Hall стена (`SNOLBoundary` неинъективен ⟹ engine, см. §23–24 brick).

  ВЫВОД: узел сузился до `hComp` = `SNOLBoundaryLabelDeterminism`. König/counting часть — закрыта. -/
theorem globalAbsorption_to_engine {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} {EuclideanEngine : Prop}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hNoInf : ¬ InfiniteLegalDescent RealStep)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine) :
    EuclideanEngine := by
  have hfan : LabelledFanIn RealStep Legal edgeSig :=
    globalAbsorption_to_labelledFanIn hGlobal hOldFin hAll hNoInf
  exact labelledFanIn_to_engine (localLabelDeterminism hKindEq hComp) hfan

/-! ### §23–24. Локализация `hComp`: SNOL-стена как единственный содержательный вход

После закрытия König единственный содержательный несведённый вход — компонентный детерминизм.
Четыре из пяти компонентов (`active`, `oldPeel`, `corridor`, `boundary`-exact) — exact-детерминизмы:
метка хранит точные данные предшественника, поэтому равенство меток ⟹ равенство предшественников
(в конкретной инстанциации — арифметика separating scale / exact old-prime / exact corridor). Пятый,
`snol`, может быть неинъективным — и это РОВНО старая SNOL/Hall стена. Формализуем его нормальную форму.

`SNOLBoundaryLabelDeterminism` — то, что осталось: у SNOL-ребра равная метка ⟹ равенство ∨ engine. -/

/-- §23. Оставшийся SNOL-вход в явной форме: детерминизм метки SNOL-ребра (или engine). -/
def SNOLBoundaryLabelDeterminism {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) (EuclideanEngine : Prop) : Prop :=
  KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.snol

/--
  **§24 (`snol_kindDeterminism_of_normalForm`) — ДОКАЗАНА (нормальная форма SNOL).** SNOL-детерминизм
  СВОДИТСЯ к двум под-случаям: `snolExact` (метка хранит точного предшественника ⟹ равенство) и
  `snolHallSeed` (неинъективность ⟹ engine). Дан классификатор `snolMode : σ → σ → Bool`
  (`true` = exact, `false` = hall-seed) и два под-детерминизма — собираем полный SNOL-детерминизм.

  Это НАСТОЯЩАЯ сборка (case split по `snolMode`), а не алиас. Содержательная нагрузка — в
  `hHallSeed` (hall-seed ⟹ engine): это несведённая SNOL/Hall стена (brick §24). -/
theorem snol_kindDeterminism_of_normalForm {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop} (snolMode : σ → σ → Bool)
    -- exact/exact с равной меткой ⟹ равенство предшественников
    (hExact : ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
      RealStep U₁ V → RealStep U₂ V → kind U₁ V = Kind.snol → kind U₂ V = Kind.snol →
      snolMode U₁ V = true → snolMode U₂ V = true → edgeSig U₁ V = edgeSig U₂ V → U₁ = U₂)
    -- любой hall-seed-случай (различные предшественники с равной меткой) ⟹ engine
    (hHallSeed : ∀ U₁ U₂ V, Legal U₁ → Legal U₂ → Legal V →
      RealStep U₁ V → RealStep U₂ V → kind U₁ V = Kind.snol → kind U₂ V = Kind.snol →
      (snolMode U₁ V = false ∨ snolMode U₂ V = false) → edgeSig U₁ V = edgeSig U₂ V →
      U₁ = U₂ ∨ EuclideanEngine) :
    SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind EuclideanEngine := by
  intro U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig
  -- case split по snolMode обоих
  by_cases hm1 : snolMode U₁ V = true
  · by_cases hm2 : snolMode U₂ V = true
    · exact Or.inl (hExact U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 hm1 hm2 hsig)
    · exact hHallSeed U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 (Or.inr (by simpa using hm2)) hsig
  · exact hHallSeed U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 (Or.inl (by simpa using hm1)) hsig

/--
  **§25 (`componentDeterminism_of_components`) — ДОКАЗАНА (полная сборка `hComp`).** `ComponentDeterminism`
  собирается из детерминизма каждого из пяти тегов. Четыре exact-компонента (`active`/`oldPeel`/
  `boundary`/`corridor`) плюс SNOL-компонент (§24). Это финальная локализация: ЕДИНСТВЕННЫЙ содержательно
  несведённый кусок — `hHallSeed` внутри SNOL (стена), всё остальное — exact-арифметика инстанциации. -/
theorem componentDeterminism_of_components {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop}
    (hActive : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.active)
    (hOldPeel : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.oldPeel)
    (hBoundary : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.boundary)
    (hSnol : SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind EuclideanEngine)
    (hCorridor : KindDeterminism RealStep Legal edgeSig kind EuclideanEngine Kind.corridor) :
    ComponentDeterminism RealStep Legal edgeSig kind EuclideanEngine := by
  intro k
  cases k with
  | active => exact hActive
  | oldPeel => exact hOldPeel
  | boundary => exact hBoundary
  | snol => exact hSnol
  | corridor => exact hCorridor

/-! ### §26. Строгое закрытие SNOL-компонента через regeneration (brick `snol_hallseed_strict_closure`)

Здесь мы честно доводим SNOL-стену до её точной несводённой сердцевины. Сначала — **машинно-проверенный
no-go** (§1 brick): голая неинъективность SNOL-метки НЕ даёт engine. Затем — минимальный локальный
закон `SNOLHallSeedRegenerates`, которого достаточно, и который остаётся ЕДИНСТВЕННЫМ содержательным
арифметическим входом всей программы. -/

/-- Путь длины `n` (число real-step рёбер). `PathN 0 X Y := X = Y`. -/
def PathN (RealStep : σ → σ → Prop) : ℕ → σ → σ → Prop
  | 0,     X, Y => X = Y
  | (n+1), X, Y => ∃ Z, RealStep X Z ∧ PathN RealStep n Z Y

/-- Непустой путь `X →⁺ Y`: длина `≥ 1`. -/
def NonemptyPath (RealStep : σ → σ → Prop) (X Y : σ) : Prop := ∃ n, 0 < n ∧ PathN RealStep n X Y

/-- `SNOLHallSeed`: два РАЗНЫХ SNOL-предшественника одного `V` с одинаковой меткой `c`. -/
def SNOLHallSeed {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) : Prop :=
  ∃ U₁ U₂ V, U₁ ≠ U₂ ∧ Legal U₁ ∧ Legal U₂ ∧ Legal V ∧
    RealStep U₁ V ∧ RealStep U₂ V ∧ kind U₁ V = Kind.snol ∧ kind U₂ V = Kind.snol ∧
    edgeSig U₁ V = edgeSig U₂ V

/--
  **§1 (`snolHallSeed_bare_no_go`) — ДОКАЗАН NO-GO (машинно).** Голая неинъективность SNOL-метки
  НЕ влечёт engine. Формально: существует конкретная модель (три состояния `U₁,U₂,V`, два ребра
  `U₁→V`, `U₂→V` одной метки, строго убывающая высота), в которой `SNOLHallSeed` есть, но
  `InfiniteLegalDescent` НЕТ (высота строго падает ⟹ спуска нет). Значит из `SNOLHallSeed` в чистом
  виде нельзя вывести ни `InfiniteLegalDescent`, ни (при `Engine := InfiniteLegalDescent`) engine —
  нужна дополнительная арифметическая структура (§2). -/
theorem snolHallSeed_bare_no_go :
    ∃ (τ : Type) (RealStep : τ → τ → Prop) (Legal : τ → Prop)
      (edgeSig : τ → τ → Unit) (kind : τ → τ → Kind),
      SNOLHallSeed RealStep Legal edgeSig kind ∧ ¬ InfiniteLegalDescent RealStep := by
  -- модель: τ = Bool ⊕ Unit? Проще: τ := Fin 3 (0=U₁,1=U₂,2=V), рёбра 0→2, 1→2, высота 2↦0 иначе 1.
  refine ⟨Fin 3, fun a b => (a = 0 ∨ a = 1) ∧ b = 2, fun _ => True,
    fun _ _ => (), fun _ _ => Kind.snol, ?_, ?_⟩
  · -- SNOLHallSeed: U₁=0, U₂=1, V=2
    exact ⟨0, 1, 2, by decide, trivial, trivial, trivial,
      ⟨Or.inl rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, rfl, rfl, rfl⟩
  · -- нет бесконечного спуска: высота h(2)=0, h(_)=1 строго падает на каждом ребре;
    -- бесконечный спуск дал бы height (X 1) < height (X 0) и т.д., но множество высот {0,1} конечно —
    -- прямее: любой real-step ведёт в 2, а из 2 real-step'а нет, значит цепи длины 2 не бывает.
    rintro ⟨X, hX⟩
    -- hX 0 : (X 1 = 0 ∨ X 1 = 1) ∧ X 0 = 2  ;  hX 1 : (X 2 = 0 ∨ X 2 = 1) ∧ X 1 = 2
    have h0 := (hX 0).1   -- X 1 = 0 ∨ X 1 = 1
    have h1 := (hX 1).2   -- X 1 = 2
    rcases h0 with h | h <;> rw [h] at h1 <;> exact absurd h1 (by decide)

/-- `SNOLHallSeedRegenerates` (§2, форма A): всякий non-injective SNOL seed имеет return-путь от
    общего target `V` обратно к одному из предшественников. Минимальный достаточный локальный закон. -/
def SNOLHallSeedRegenerates {Lbl : Type*} (RealStep : σ → σ → Prop) (Legal : σ → Prop)
    (edgeSig : σ → σ → Lbl) (kind : σ → σ → Kind) : Prop :=
  ∀ U₁ U₂ V, U₁ ≠ U₂ → Legal U₁ → Legal U₂ → Legal V →
    RealStep U₁ V → RealStep U₂ V → kind U₁ V = Kind.snol → kind U₂ V = Kind.snol →
    edgeSig U₁ V = edgeSig U₂ V →
    NonemptyPath RealStep V U₁ ∨ NonemptyPath RealStep V U₂

/-- Ребро `U→V` плюс возвратный путь `V →⁺ U` дают непустой цикл `U →⁺ U`. -/
theorem cons_step_to_nonempty_cycle {RealStep : σ → σ → Prop} {U V : σ}
    (hStep : RealStep U V) (hBack : NonemptyPath RealStep V U) : NonemptyPath RealStep U U := by
  obtain ⟨n, hn, hpath⟩ := hBack
  exact ⟨n + 1, Nat.succ_pos n, ⟨V, hStep, hpath⟩⟩

/-- Путь длины `n` при СТРОГО РАСТУЩЕЙ вдоль ребра высоте (`RealStep u v ⟹ height u < height v`):
    `height X + n ≤ height Y`. (Та же ориентация, что у `no_infiniteLegalDescent_of_height`.) -/
theorem pathN_height_le {RealStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v) :
    ∀ n X Y, PathN RealStep n X Y → height X + n ≤ height Y := by
  intro n
  induction n with
  | zero => intro X Y h; have hxy : X = Y := h; subst hxy; simp
  | succ k ih =>
    intro X Y h
    obtain ⟨Z, hXZ, hZY⟩ := h
    have h1 := hdrop hXZ         -- height X < height Z
    have h2 := ih Z Y hZY        -- height Z + k ≤ height Y
    omega

/--
  **`no_cycle_of_height` — ДОКАЗАНА.** При строго растущей вдоль ребра высоте (та же ориентация, что
  запрещает бесконечный спуск) непустой цикл `W →⁺ W` невозможен: путь длины `n ≥ 1` дал бы
  `height W + n ≤ height W`. Один и тот же `hdrop` убивает И спуск, И цикл. -/
theorem no_cycle_of_height {RealStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v)
    (W : σ) (hcyc : NonemptyPath RealStep W W) : False := by
  obtain ⟨n, hn, hpath⟩ := hcyc
  have := pathN_height_le height hdrop n W W hpath
  omega

/-- Мост «цикл ⟹ engine»: непустой legal-цикл даёт `EuclideanEngine`. В EPMI-инстанциации
    (`EuclideanEngine := False`) это ровно `no_cycle_of_height` — см. `cycleBridge_of_height`. -/
def CycleBridge {RealStep : σ → σ → Prop} (Legal : σ → Prop) (EuclideanEngine : Prop) : Prop :=
  (∃ W, Legal W ∧ NonemptyPath RealStep W W) → EuclideanEngine

/-- **`cycleBridge_of_height` — ДОКАЗАНА.** При строго убывающей высоте мост «цикл ⟹ engine»
    выполняется для `EuclideanEngine := False` (цикла просто нет). Это делает `CycleBridge` не
    гипотезой, а следствием двигателя в реальной инстанциации. -/
theorem cycleBridge_of_height {RealStep : σ → σ → Prop} {Legal : σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v) :
    CycleBridge (RealStep := RealStep) Legal False := by
  rintro ⟨W, _, hcyc⟩
  exact no_cycle_of_height height hdrop W hcyc

/--
  **§5.1 (`snolHallSeed_to_engine_of_regeneration`) — ДОКАЗАНА при законе regeneration.** Если
  выполняется минимальный локальный закон `SNOLHallSeedRegenerates` и мост `CycleBridge`, то любой
  `SNOLHallSeed` даёт engine. Механизм: seed даёт два ребра `Uᵢ → V`; regeneration даёт возврат
  `V →⁺ Uᵢ`; вместе — непустой цикл `Uᵢ →⁺ Uᵢ` (`cons_step_to_nonempty_cycle`); мост даёт engine. -/
theorem snolHallSeed_to_engine_of_regeneration {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop}
    (hBridge : CycleBridge (RealStep := RealStep) Legal EuclideanEngine)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind)
    (hSeed : SNOLHallSeed RealStep Legal edgeSig kind) :
    EuclideanEngine := by
  obtain ⟨U₁, U₂, V, hne, hL1, hL2, hLV, hs1, hs2, hk1, hk2, hsig⟩ := hSeed
  rcases hRegen U₁ U₂ V hne hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig with hVU1 | hVU2
  · exact hBridge ⟨U₁, hL1, cons_step_to_nonempty_cycle hs1 hVU1⟩
  · exact hBridge ⟨U₂, hL2, cons_step_to_nonempty_cycle hs2 hVU2⟩

/--
  **§6.1 (`snol_kindDeterminism_of_regeneration`) — ДОКАЗАНА.** Из `SNOLHallSeedRegenerates` + моста
  следует полный SNOL-детерминизм (`SNOLBoundaryLabelDeterminism`): для пары SNOL-рёбер с равной меткой
  либо предшественники равны, либо (различны ⟹ `SNOLHallSeed`) engine через §5.1. -/
theorem snol_kindDeterminism_of_regeneration {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    {EuclideanEngine : Prop}
    (hBridge : CycleBridge (RealStep := RealStep) Legal EuclideanEngine)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind) :
    SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind EuclideanEngine := by
  intro U₁ U₂ V hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig
  by_cases hEq : U₁ = U₂
  · exact Or.inl hEq
  · exact Or.inr (snolHallSeed_to_engine_of_regeneration hBridge hRegen
      ⟨U₁, U₂, V, hEq, hL1, hL2, hLV, hs1, hs2, hk1, hk2, hsig⟩)

/--
  **§26bis (`regen_under_hdrop_kills_seed`) — ДОКАЗАНА (важная оговорка честности).** Под тем же `hdrop`
  (ко-высота растёт вдоль ребра), которым закрывается всё остальное, `SNOLHallSeedRegenerates` и
  СРАБОТАВШИЙ `SNOLHallSeed` ВЗАИМОИСКЛЮЧАЮЩИ: ребро seed'а `Uᵢ→V` даёт `height Uᵢ < height V`, а
  возврат regeneration `V →⁺ Uᵢ` даёт `height V < height Uᵢ` — противоречие (цикл запрещён).

  СЛЕДСТВИЕ (честное): в финальной сборке `hdrop` и `hRegen` совместимы лишь когда seed'ов НЕТ. То
  есть под `hdrop` закон `SNOLHallSeedRegenerates` выполняется лишь ВАКУУМНО (seed-emptiness), а НЕ как
  нетривиальный «fan-in ⟹ engine». Реальное арифметическое содержание при этом мигрирует в САМ `hdrop`
  — существование строго-монотонной ко-высоты на `RealStep` графа `6m±1` (= ацикличность/EPMI/
  well-foundedness), которая здесь НЕ предъявлена. Поэтому «узел сведён к ОДНОЙ лемме» — упрощение:
  нагрузка делится между `hRegen` (seed⇒return-path, строго ЛЕГЧЕ старой seed⇒engine стены) и `hdrop`. -/
theorem regen_under_hdrop_kills_seed {Lbl : Type*}
    {RealStep : σ → σ → Prop} {Legal : σ → Prop} {edgeSig : σ → σ → Lbl} {kind : σ → σ → Kind}
    (height : σ → ℕ) (hdrop : ∀ {u v}, RealStep u v → height u < height v)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind)
    (hSeed : SNOLHallSeed RealStep Legal edgeSig kind) : False := by
  obtain ⟨U₁, U₂, V, hne, hL1, hL2, hLV, hs1, hs2, hk1, hk2, hsig⟩ := hSeed
  rcases hRegen U₁ U₂ V hne hL1 hL2 hLV hs1 hs2 hk1 hk2 hsig with hback | hback
  · exact no_cycle_of_height height hdrop U₁ (cons_step_to_nonempty_cycle hs1 hback)
  · exact no_cycle_of_height height hdrop U₂ (cons_step_to_nonempty_cycle hs2 hback)

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
его — остаётся вход `hComp` (SNOL-стена), а привязка `σ`/`RealStep`/`edgeSig` к конкретному графу
`6m±1` (`Residuals.TwinCenterZ`, `ProductCore.CoreSig`) здесь НЕ предъявлена. Мост показывает
СОВМЕСТИМОСТЬ формы, а не выводимость twin. -/

/--
  **`globalAbsorption_refutes_under_epmi` — ДОКАЗАНА (König закрыт; остался `hComp`).**
  При `EuclideanEngine := False` (EPMI) абстрактная цепь опровергает `GlobalOldAbsorption`. Это
  та же контрапозиция, что `no_global_absorption_under_epmi`, но выраженная через labelled-fan-in
  машину, в которой König-ветвь уже доказана. Держится на одном содержательном входе `hComp` (SNOL). -/
theorem globalAbsorption_refutes_under_epmi {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hNoInf : ¬ InfiniteLegalDescent RealStep)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hComp : ComponentDeterminism RealStep Legal edgeSig kind (EuclideanEngine := False)) :
    False :=
  globalAbsorption_to_engine hGlobal hOldFin hAll hNoInf hKindEq hComp

/-! ### §27. Финальная сборка: всё сведено к ОДНОМУ закону `SNOLHallSeedRegenerates`

Собираем всю цепь под EPMI (`EuclideanEngine := False`, высота строго падает на real-step). Тогда:
König закрыт (§7), EPMI-мост даёт `hNoInf` и `CycleBridge`, четыре exact-компонента — арифметика
инстанциации, а пятый (SNOL) закрывается `SNOLHallSeedRegenerates` (§26). Итог: при строго падающей
высоте единственный содержательный вход — `SNOLHallSeedRegenerates`; он ОПРОВЕРГАЕТ `GlobalOldAbsorption`.

Это финальная локализация — но НЕ «к одной лемме»: см. честную оговорку в docstring теоремы. -/

/--
  **§8–9 (`globalAbsorption_refutes_of_snolRegeneration`) — ДОКАЗАНА (финальная сборка под EPMI).**
  При строго растущей вдоль ребра ко-высоте `GlobalOldAbsorption` невозможно, ЕСЛИ дан набор входов:
    • `SNOLHallSeedRegenerates` — SNOL-закон (seed ⟹ return-path);
    • четыре компонента `hActive/hOldPeel/hBoundary/hCorridor` — под `Engine := False` это НАСТОЯЩИЕ
      обязательства инъективности метки на каждом сорте ребра, НЕ бесплатные;
    • `hOldFin`, `[Finite Lbl]`, `hAll`, `hKindEq`, сам `hdrop` — допущения инстанциации графа.
  Высота даёт `hNoInf` (нет спуска) И `CycleBridge` (нет цикла) — оба из одного `hdrop`.

  ЧЕСТНАЯ ОГОВОРКА (подтверждена адверсариальным аудитом v4, `regen_under_hdrop_kills_seed`). Нельзя
  говорить «узел сведён к ОДНОЙ лемме `SNOLHallSeedRegenerates`». Под тем же `hdrop`, которым
  закрывается всё остальное, seed и его regeneration ВЗАИМОИСКЛЮЧАЮЩИ (ребро + возврат = цикл, запрещён).
  Значит `hRegen` под `hdrop` выполняется лишь ВАКУУМНО (когда seed'ов нет), а реальное арифметическое
  содержание МИГРИРУЕТ в сам `hdrop` — существование строго-монотонной ко-высоты на `6m±1` RealStep
  (= ацикличность/EPMI/well-foundedness), которая здесь НЕ предъявлена. Плюс `hAll` ЛОЖНО на реальном
  графе, а машина абстрактна и не подключена к `TwinCenterZ`/`CoreSig`.

  ВЫВОД: это редукция МОДУЛО нескольких принятых арифметических фактов на АБСТРАКТНОМ графе
  (`hRegen` — строго ЛЕГЧЕ старой seed⇒engine стены — ПЛЮС `hdrop`/ко-высота ПЛЮС четыре компонента
  ПЛЮС инстанциация), а не «к одной лемме». Реальный прогресс есть; закрытия Step00 нет. -/
theorem globalAbsorption_refutes_of_snolRegeneration {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {Legal OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {kind : σ → σ → Kind} (height : σ → ℕ)
    (hdrop : ∀ {u v}, RealStep u v → height u < height v)
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hAll : ∀ x, Legal x)
    (hKindEq : ∀ U₁ U₂ V, edgeSig U₁ V = edgeSig U₂ V → kind U₁ V = kind U₂ V)
    (hActive : KindDeterminism RealStep Legal edgeSig kind False Kind.active)
    (hOldPeel : KindDeterminism RealStep Legal edgeSig kind False Kind.oldPeel)
    (hBoundary : KindDeterminism RealStep Legal edgeSig kind False Kind.boundary)
    (hCorridor : KindDeterminism RealStep Legal edgeSig kind False Kind.corridor)
    (hRegen : SNOLHallSeedRegenerates RealStep Legal edgeSig kind) :
    False := by
  -- один и тот же hdrop (height растёт вдоль ребра) убивает И бесконечный спуск, И цикл
  have hNoInf : ¬ InfiniteLegalDescent RealStep := no_infiniteLegalDescent_of_height height hdrop
  have hBridge : CycleBridge (RealStep := RealStep) Legal False := cycleBridge_of_height height hdrop
  -- SNOL-компонент из regeneration
  have hSnol : SNOLBoundaryLabelDeterminism RealStep Legal edgeSig kind False :=
    snol_kindDeterminism_of_regeneration hBridge hRegen
  have hComp : ComponentDeterminism RealStep Legal edgeSig kind False :=
    componentDeterminism_of_components hActive hOldPeel hBoundary hSnol hCorridor
  exact globalAbsorption_refutes_under_epmi hGlobal hOldFin hAll hNoInf hKindEq hComp

end EuclidsPath.LabelledFanIn
