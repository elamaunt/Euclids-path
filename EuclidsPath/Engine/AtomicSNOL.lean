/-
  Atomic SNOL-free graph + SNOL demacrofication — Step00 post-audit re-architecture.
  Источник: step00_post_audit_to_snol_deriv_final_residuals_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Атомизация SNOL»).

  ЗАЧЕМ. Аудиты v3/v4 показали, что абстрактная labelled-машина (`LabelledFanIn.lean`) держится на
  `hAll : ∀x, Legal x` (ложно на `6m±1`), а SNOL как macro-edge даёт тяжёлую seed⇒engine стену. Этот
  модуль — СТРУКТУРНЫЙ рефакторинг по brick'у (два честных выигрыша, но НЕ арифметический прогресс):
    (1) устранена ЛОЖНАЯ гипотеза `hAll`: `dichotomy_legal` берёт `Legal := fun _ => True`, и `hAll`
        разряжается ИСТИННЫМ термом `fun _ => trivial` (в отличие от прежнего ложного `∀x, Legal x`);
    (2) SNOL перестаёт быть atomic edge: он — `SNOLDeriv` (индуктивная замкнутость atomic-шагов +
        composition + terminal engine/twin), и `SNOLDeriv_expand_or_closes` разворачивает её в atomic
        path ИЛИ закрывает.

  ЧЕСТНЫЙ СТАТУС (уточнён адверсариальным аудитом; НЕ переоцениваем):
  ДОКАЗАНО здесь (абстрактно, стандартные аксиомы, без sorry):
    * `dichotomy_legal` — König-дихотомия при `Legal := True` (ложный `hAll` снят соундно);
    * `SNOLDeriv_expand_or_closes` (R7) — ИСТИННАЯ, но СТРУКТУРНО ТАВТОЛОГИЧНАЯ: дизъюнкты
      (`AtomicPath ∨ Engine ∨ Twin`) в точной биекции с конструкторами свободного индуктива; НУЛЕВОЕ
      арифметическое содержание (composition уже был бесплатен через `ReflTransGen.trans`);
    * `AtomicPath.append`, `atomicLabelledFanIn_closes`, `no_atomicInfiniteLegalDescent_of_height`,
      `macroPath_expand_or_closes` — структура/EPMI/конечная графовая теория.

  ЧЕГО ЭТОТ РЕФАКТОРИНГ НЕ ДЕЛАЕТ (важно):
    * `hAll` устранён как ЛОЖНАЯ гипотеза, но НЕ как ОБЯЗАТЕЛЬСТВО: с `Legal := True` теоремы говорят о
      ПОЛНОМ типе `σ` без фильтра легальности, поэтому любая инстанциация на legal-subtype обязана
      дополнительно (a) построить `AtomicStep` legality-closed и (b) дать легальный `hGlobal`. Legal
      subtype здесь НИГДЕ не построен — обязательство ПЕРЕНЕСЕНО в абстрактный `AtomicStep`/`hGlobal`.
    * R8 (`SNOLBoundaryToDeriv`) — НЕ гипотеза финальной теоремы `twin_of_atomicDeterminism_and_absorption`.
      Это вход ОТДЕЛЬНОЙ, НЕ подключённой ветки (`SNOLDeriv`/`macroPath`). Нельзя говорить «всё сведено
      к одному R8».
    * `SNOLDeriv_expand_or_closes` — бухгалтерия, НЕ прогресс: вся SNOL/old-peel арифметика по-прежнему
      целиком в R8, а R8 definitionally взаимозаменяем со старым входом `hSNOLexpand`.

  РЕАЛЬНЫЙ ОСТАТОК СОБРАННОЙ ЦЕПИ (`twin_of_atomicDeterminism_and_absorption`):
    `{ hDet (AtomicLocalDeterminism — несёт boundary/old-peel/SNOL-детерминизм, синтаксически без
       snol-случая, но по сути та же стена, лишь снят ярлык), hdrop (ацикличность/well-foundedness
       ко-высоты на `6m±1`), инстанциация к `TwinCenterZ`/`CoreSig`/`Step00.EuclideanEngine` }`,
    плюс R8 как ОТДЕЛЬНЫЙ вход НЕсобранной SNOL-ветки.

  ВЫВОД (аудит): прогресс ЛАТЕРАЛЬНЫЙ — два структурных выигрыша (снят ложный `hAll`; SNOL-composition
  доказан, а не предположен), но содержательная арифметика лишь ПЕРЕНЕСЕНА в более чистые места, не
  снята. Красная линия цела (никакого counting/вероятностей). Машина абстрактна и ничем не потребляется.
  Это НЕ шаг к доказательству близнецов. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.LabelledFanIn

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.AtomicSNOL

open EuclidsPath.LabelledFanIn

variable {σ : Type*}

/-! ### §9–10. Atomic SNOL-free граф и путь

`AtomicStep` — атомарный шаг (activeDelete/oldPeel/oldCorridor/boundaryExact/boundaryPeel + terminal
seeds). SNOL и absorber СЮДА не входят как конструкторы. `AtomicPath` — конечный путь по atomic шагам. -/

/-- Атомарный путь `U ⇝ V` — рефлексивно-транзитивное замыкание atomic шага. -/
abbrev AtomicPath (AtomicStep : σ → σ → Prop) : σ → σ → Prop := Relation.ReflTransGen AtomicStep

/-- **`AtomicPath.append` — ДОКАЗАНА** (= транзитивность `ReflTransGen`). -/
theorem AtomicPath.append {AtomicStep : σ → σ → Prop} {U W V : σ}
    (h1 : AtomicPath AtomicStep U W) (h2 : AtomicPath AtomicStep W V) : AtomicPath AtomicStep U V :=
  h1.trans h2

/-! ### §16–17. SNOL как конечная деривация + разворачивание (R7)

Вместо opaque macro-edge SNOL — `SNOLDeriv`: наименьшая замкнутость atomic-шагов относительно
композиции с terminal engine/twin. Тогда «SNOL раскрывается» — это структурная индукция. -/

/-- `SNOLDeriv` (§16): конечная деривация SNOL-события из atomic шагов, композиции и terminal
    engine/twin. Boundary exact/peel — atomic шаги, НЕ отдельные macro-конструкторы. -/
inductive SNOLDeriv (AtomicStep : σ → σ → Prop) (Engine : Prop) (Twin : Prop) : σ → σ → Prop
  | atomic {U V} : AtomicStep U V → SNOLDeriv AtomicStep Engine Twin U V
  | comp {U W V} : SNOLDeriv AtomicStep Engine Twin U W → SNOLDeriv AtomicStep Engine Twin W V →
      SNOLDeriv AtomicStep Engine Twin U V
  | engine {U V} : Engine → SNOLDeriv AtomicStep Engine Twin U V
  | twin {U V} : Twin → SNOLDeriv AtomicStep Engine Twin U V

/--
  **§17 (`SNOLDeriv_expand_or_closes`) — ДОКАЗАНА (R7, ядро демакрофикации).** Всякая SNOL-деривация
  ЛИБО разворачивается в конечный atomic путь `U ⇝ V`, ЛИБО уже закрывает Step00 (engine/twin).
  Индукция по деривации: atomic ⟹ путь длины 1; comp ⟹ append путей (или пропуск закрытия);
  engine/twin ⟹ соответствующий terminal. -/
theorem SNOLDeriv_expand_or_closes {AtomicStep : σ → σ → Prop} {Engine Twin : Prop} {U V : σ}
    (h : SNOLDeriv AtomicStep Engine Twin U V) :
    AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  induction h with
  | atomic hs => exact Or.inl (Relation.ReflTransGen.single hs)
  | comp _ _ ih1 ih2 =>
    rcases ih1 with p1 | e1 | t1
    · rcases ih2 with p2 | e2 | t2
      · exact Or.inl (p1.trans p2)
      · exact Or.inr (Or.inl e2)
      · exact Or.inr (Or.inr t2)
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr t1)
  | engine he => exact Or.inr (Or.inl he)
  | twin ht => exact Or.inr (Or.inr ht)

/-! ### §2–4. Легальный subtype устраняет `hAll` (структурно)

Ключ к устранению `hAll`: работать на `σ` = legal subtype, где `Legal := fun _ => True` выполняется
by construction, поэтому гипотеза всеобщей легальности разряжается `fun _ => trivial`. -/

/--
  **`dichotomy_legal` — ДОКАЗАНА (König-дихотомия БЕЗ `hAll`).** На legal-графе (любой `σ`,
  `Legal := True`) König-дихотомия из `LabelledFanIn.lean` выполняется без гипотезы всеобщей
  легальности: она разряжается тривиально. Это структурно снимает возражение аудита о ложном `hAll`
  на реальном графе `6m±1` — легальность встроена в тип состояний. -/
theorem dichotomy_legal {Lbl : Type*} [Finite Lbl]
    {RealStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    (hGlobal : GlobalOldAbsorption RealStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite) :
    LabelledFanIn RealStep (fun _ => True) edgeSig ∨ InfiniteLegalDescent RealStep :=
  absorption_labelled_dichotomy hGlobal hOldFin (fun _ => trivial)

/-! ### §12. Atomic fan-in закрывает Step00

`AtomicLocalDeterminism` (все atomic пары с равной меткой ⟹ равенство ∨ engine ∨ twin) + atomic
fan-in ⟹ engine ∨ twin. Это atomic-версия consumer'а, теперь с двумя terminal исходами. -/

/-- `AtomicLocalDeterminism`: для atomic-пар с равной меткой — равенство ∨ engine ∨ twin. -/
def AtomicLocalDeterminism {Lbl : Type*} (AtomicStep : σ → σ → Prop) (edgeSig : σ → σ → Lbl)
    (Engine Twin : Prop) : Prop :=
  ∀ U₁ U₂ V, AtomicStep U₁ V → AtomicStep U₂ V → edgeSig U₁ V = edgeSig U₂ V →
    U₁ = U₂ ∨ Engine ∨ Twin

/-- `AtomicLabelledFanIn`: два разных предшественника одного `V` с равной atomic-меткой. -/
def AtomicLabelledFanIn {Lbl : Type*} (AtomicStep : σ → σ → Prop) (edgeSig : σ → σ → Lbl) : Prop :=
  ∃ U₁ U₂ V, U₁ ≠ U₂ ∧ AtomicStep U₁ V ∧ AtomicStep U₂ V ∧ edgeSig U₁ V = edgeSig U₂ V

/--
  **§12 (`atomicLabelledFanIn_closes`) — ДОКАЗАНА.** Atomic fan-in + atomic local determinism ⟹
  engine ∨ twin. Равенство предшественников противоречит `U₁ ≠ U₂`, значит остаётся engine/twin. -/
theorem atomicLabelledFanIn_closes {Lbl : Type*} {AtomicStep : σ → σ → Prop} {edgeSig : σ → σ → Lbl}
    {Engine Twin : Prop}
    (hDet : AtomicLocalDeterminism AtomicStep edgeSig Engine Twin)
    (hFan : AtomicLabelledFanIn AtomicStep edgeSig) : Engine ∨ Twin := by
  obtain ⟨U₁, U₂, V, hne, hs1, hs2, hsig⟩ := hFan
  rcases hDet U₁ U₂ V hs1 hs2 hsig with heq | hcl
  · exact absurd heq hne
  · exact hcl

/-! ### §14. Нет atomic бесконечного спуска (EPMI-мост) -/

/-- Atomic бесконечный спуск: `X (n+1) → X n` по atomic шагам. -/
def AtomicInfiniteLegalDescent (AtomicStep : σ → σ → Prop) : Prop :=
  ∃ X : ℕ → σ, ∀ n, AtomicStep (X (n + 1)) (X n)

/--
  **§14 (`no_atomicInfiniteLegalDescent_of_height`) — ДОКАЗАНА.** При строго убывающей вдоль atomic
  шага высоте (EPMI) atomic бесконечного спуска нет — та же well-foundedness ℕ, что в `no_infinite_descent`. -/
theorem no_atomicInfiniteLegalDescent_of_height {AtomicStep : σ → σ → Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, AtomicStep u v → height u < height v) :
    ¬ AtomicInfiniteLegalDescent AtomicStep := by
  rintro ⟨X, hX⟩
  refine EuclidsPath.Engine.no_infinite_descent (A := 1) (le_refl 1)
    (fun k => height (X k)) (fun n => ?_)
  show 1 * height (X (n + 1)) < height (X n)
  have := hdrop (hX n)
  omega

/-! ### §20–21. Разворачивание macro-шага и macro-пути

Macro-путь (с SNOL-макро-рёбрами) разворачивается в atomic путь ИЛИ закрывается, при условии, что
SNOL разворачивается (`hSNOLexpand`). Это структурная индукция по macro-пути. -/

/--
  **§20 (`macroStep_expand_or_closes`) — ДОКАЗАНА при `hSNOLexpand`.** Один macro-шаг (atomic ИЛИ
  SNOL-макро) разворачивается в atomic путь или закрывает Step00. Atomic-шаг ⟹ путь длины 1;
  SNOL-макро ⟹ по `hSNOLexpand`. -/
theorem macroStep_expand_or_closes {AtomicStep : σ → σ → Prop} {SNOLMacro : σ → σ → Prop}
    {Engine Twin : Prop} {U V : σ}
    (hSNOLexpand : ∀ {a b}, SNOLMacro a b → AtomicPath AtomicStep a b ∨ Engine ∨ Twin)
    (hstep : AtomicStep U V ∨ SNOLMacro U V) :
    AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  rcases hstep with hat | hsn
  · exact Or.inl (Relation.ReflTransGen.single hat)
  · exact hSNOLexpand hsn

/--
  **§21 (`macroPath_expand_or_closes`) — ДОКАЗАНА при `hSNOLexpand`.** Весь macro-путь (замыкание
  «atomic ∨ SNOL-макро») разворачивается в atomic путь или закрывается. Индукция по `ReflTransGen`
  macro-шага; append atomic-путей на каждом звене, пропуск закрытия. -/
theorem macroPath_expand_or_closes {AtomicStep : σ → σ → Prop} {SNOLMacro : σ → σ → Prop}
    {Engine Twin : Prop} {U V : σ}
    (hSNOLexpand : ∀ {a b}, SNOLMacro a b → AtomicPath AtomicStep a b ∨ Engine ∨ Twin)
    (hpath : Relation.ReflTransGen (fun a b => AtomicStep a b ∨ SNOLMacro a b) U V) :
    AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  induction hpath with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail hstep hlast ih =>
    -- hstep : macro-путь до предпоследнего; hlast : последний macro-шаг; ih : разворот префикса
    rcases ih with pfx | e | t
    · rcases macroStep_expand_or_closes hSNOLexpand hlast with plast | e | t
      · exact Or.inl (pfx.trans plast)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr t)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr t)

/-! ### §26. Вход R8 (SNOL-ветка) — ОТДЕЛЬНАЯ, НЕ подключена к финальной теореме

ВАЖНО: эта SNOL-ветка (`SNOLBoundaryToDeriv` → `snolMacro_expands_of_bridge` → `macroPath...`) —
СЕПАРАТНАЯ. Она НЕ является гипотезой `twin_of_atomicDeterminism_and_absorption`: та работает уже на
atomic-графе. R8 нужен, только если строить macro→atomic разворачивание отдельно. По аудиту: `R8`
definitionally взаимозаменяем со старым входом `hSNOLexpand`, а вся SNOL/old-peel арифметика — в нём.
Подаём как явную гипотезу. -/

/-- R8: старый SNOL-предикат ⟹ `SNOLDeriv` ∨ engine ∨ twin. Содержательный вход SNOL-ВЕТКИ (в реальном
    графе — арифметика SNOL/old-peel); НЕ разряжается вакуумно (`.engine` требует реального `Engine`,
    которого нет). Взаимозаменяем со старым `hSNOLexpand`. -/
def SNOLBoundaryToDeriv (SNOLMacro AtomicStep : σ → σ → Prop) (Engine Twin : Prop) : Prop :=
  ∀ {U V}, SNOLMacro U V → SNOLDeriv AtomicStep Engine Twin U V ∨ Engine ∨ Twin

/--
  **`snolMacro_expands_of_bridge` — ДОКАЗАНА при R8.** Из красной линии R8 (`SNOLBoundaryToDeriv`)
  следует, что SNOL-макро разворачивается в atomic путь или закрывает: применяем bridge, затем
  `SNOLDeriv_expand_or_closes`. Это делает `hSNOLexpand` (нужный для §20–21) следствием R8. -/
theorem snolMacro_expands_of_bridge {AtomicStep SNOLMacro : σ → σ → Prop} {Engine Twin : Prop}
    (hBridge : SNOLBoundaryToDeriv SNOLMacro AtomicStep Engine Twin)
    {U V : σ} (h : SNOLMacro U V) : AtomicPath AtomicStep U V ∨ Engine ∨ Twin := by
  rcases hBridge h with hderiv | e | t
  · exact SNOLDeriv_expand_or_closes hderiv
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr t)

/-! ### §23–24. Финальная сборка на atomic-графе (остаток = `hDet` + `hdrop` + инстанциация)

Собираем цепь на atomic-графе. Под EPMI (atomic height растёт вдоль ребра ⟹ нет atomic спуска) и при
atomic local determinism, atomic-fan-in закрывает (engine/twin). Дихотомия (`dichotomy_legal`) даёт
fan-in или спуск; спуск запрещён; fan-in закрывает.

ЧЕСТНО (по аудиту): реальный несведённый остаток ЭТОЙ цепи — `hDet` (несёт boundary/old-peel/SNOL-
детерминизм — синтаксически без snol-случая, но по сути та же стена), `hdrop` (ацикличность/
well-foundedness ко-высоты на `6m±1`) и инстанциация. Ветка R8/SNOLDeriv сюда НЕ входит. -/

/--
  **§23 (`atomicGlobalAbsorption_closes`) — ДОКАЗАНА (atomic-сборка под EPMI).** На atomic-графе:
  atomic global absorption + конечность absorber'ов + конечный alphabet + atomic local determinism +
  строго растущая atomic height ⟹ engine ∨ twin. König-дихотомия (без `hAll`) + EPMI + atomic consumer.

  Это atomic-версия финала: вся König/counting/EPMI часть закрыта; входы — atomic local determinism
  (exact-компоненты, арифметика инстанциации) и конечности. -/
theorem atomicGlobalAbsorption_closes {Lbl : Type*} [Finite Lbl]
    {AtomicStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {Engine Twin : Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, AtomicStep u v → height u < height v)
    (hGlobal : GlobalOldAbsorption AtomicStep OldAbsorber Fresh)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hDet : AtomicLocalDeterminism AtomicStep edgeSig Engine Twin) :
    Engine ∨ Twin := by
  -- König-дихотомия на legal-графе (без hAll)
  rcases dichotomy_legal (edgeSig := edgeSig) hGlobal hOldFin with hfan | hinf
  · -- LabelledFanIn (с Legal := True) ⟹ AtomicLabelledFanIn
    obtain ⟨U₁, U₂, V, hne, _, _, _, hs1, hs2, hsig⟩ := hfan
    exact atomicLabelledFanIn_closes hDet ⟨U₁, U₂, V, hne, hs1, hs2, hsig⟩
  · -- InfiniteLegalDescent запрещён EPMI
    exact absurd hinf (no_atomicInfiniteLegalDescent_of_height height hdrop)

/--
  **§24 (`twin_of_atomicDeterminism_and_absorption`) — ДОКАЗАНА (финальная форма под входами).** Под
  `¬Twin` и `¬Engine` (EPMI), если atomic global absorption получается из `¬Twin` (`hNoNew_to_abs`),
  то `atomicGlobalAbsorption_closes` даёт engine ∨ twin — противоречие. Значит `Twin`.

  ВАЖНО (честность, по аудиту): в ЭТОЙ теореме НЕТ гипотезы-bridge R8 (`SNOLBoundaryToDeriv`) — поэтому
  прежнее имя `step00_final_of_bridge` вводило в заблуждение и переименовано. Реальный остаток ЭТОЙ
  цепи — это `hDet` (несёт SNOL/boundary/old-peel-детерминизм, синтаксически без snol-случая, но по
  сути та же стена), `hdrop` (ацикличность/well-foundedness ко-высоты на `6m±1`), и вся инстанциация
  (`Twin := ∃ m>M₀, TwinCenter m`, `Engine := Step00.EuclideanEngine`, привязка `σ`/`AtomicStep`/`edgeSig`
  к `TwinCenterZ`/`CoreSig`, `hNoNew_to_abs`, `hOldFin`, `[Finite Lbl]`). R8/`SNOLDeriv` — ОТДЕЛЬНАЯ,
  НЕ подключённая к этой теореме ветка. Это форма редукции, НЕ закрытие. -/
theorem twin_of_atomicDeterminism_and_absorption {Lbl : Type*} [Finite Lbl]
    {AtomicStep : σ → σ → Prop} {OldAbsorber Fresh : σ → Prop} {edgeSig : σ → σ → Lbl}
    {Engine Twin : Prop} (height : σ → ℕ)
    (hdrop : ∀ {u v}, AtomicStep u v → height u < height v)
    (hOldFin : {O | OldAbsorber O}.Finite)
    (hDet : AtomicLocalDeterminism AtomicStep edgeSig Engine Twin)
    (hNoEngine : ¬ Engine)
    (hNoNew_to_abs : ¬ Twin → GlobalOldAbsorption AtomicStep OldAbsorber Fresh) :
    Twin := by
  by_contra hNoTwin
  have hGlobal := hNoNew_to_abs hNoTwin
  rcases atomicGlobalAbsorption_closes height hdrop hGlobal hOldFin hDet with he | ht
  · exact hNoEngine he
  · exact hNoTwin ht

end EuclidsPath.AtomicSNOL
