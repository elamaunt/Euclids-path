/-
  TwinScaleAdvances — два масштабных продвижения главного узла (близнецы) + мост скелетов.
  Раздел отчёта: «Гипотеза близнецов», кандидаты №4 (allM0) и №5 (растущий разделяющий
  масштаб, CORR-маршрут) + №6 (мост BoundaryDecomp ↔ CarrierBridge).
  Проза: prose/29_CarrierBridge.md §29.5–29.6 (масштабный барьер и план закрытия),
  prose/30 (SeparatingScale). Зелёные машины: Engine/ConcreteStep00Graph.lean,
  Engine/ProductCore.lean, Engine/CarrierBridge.lean, Engine/BoundaryDecomp.lean.

  ЧТО ЗДЕСЬ.
  (а) `no_projection_resolves_at_smallScale_allM0`: малошкальная полоса узла (A ≤ 4)
      мертва при ЛЮБОЙ базе M0 ≥ 1, а не только при M0 = 1. Оплата та же, что у
      `no_projection_resolves_at_smallScale`: 5-адическая цепь (инъективная поставка
      через `fiveAdicChain_strictMono`) + пижонхол `Finite.exists_ne_map_eq_of_infinite`;
      старт цепи берётся выше любого M0 (цепь неограничена: `fiveAdicChain_ge`),
      терминал `center 1` остаётся старым при 1 ≤ M0.
  (б) `exists_growing_separating_scale`: шаг (1) плана закрытия §29.6 — для каждого
      окна m ≥ 1 существует масштаб A (с явной верхней границей 12m+2), при котором
      сторона 6m+1 укладывается в окно (X_A := m) И разделяющий масштаб выполняется:
      6m+1 < oldPrimorial A. Оплата: постулат Бертрана
      (`Nat.exists_prime_lt_and_le_two_mul`, mathlib) + делимость примориала
      (`prime_dvd_oldPrimorial` + `Nat.le_of_dvd`). CORR-исправление учтено:
      oldPrimorial НЕ содержит 2 и 3, поэтому ход «2·p > 6m+1» недоступен — вместо
      него ОДИН Бертран на n = 6m+1 даёт простое p > 6m+1, p ≥ 5, A := p.
  (в) `factorization_collision_as_absorber_instance`: pump-цепь CarrierBridge
      (`engine_of_factorization`) машинно прогнана через пижонхол-скелет
      `BoundaryDecomp.global_absorber_forces_engine` (key := coreSigOf ∘ node,
      pump := ДОКАЗАННАЯ descent-машина ProductCore). Это отождествление ДВУХ
      СКЕЛЕТОВ, а НЕ «одна стена вместо двух»: красные входы (FactorizationData
      у CarrierBridge; pump/GlobalOldAbsorption у настоящих генеалогий) остаются оба.

  ЧЕСТНОСТЬ. Ничто здесь НЕ доказывает гипотезу близнецов и НЕ является Гёделем.
  (а) — усиление уже опровергнутой ветви A ≤ 4 (узел живёт только при A ≥ 5, где
  нужна арифметика дирихле-класса, отсутствующая в репо). (б) — зелёная конечная
  арифметика: она закрывает ровно шаг (1) плана §29.6 (существование масштаба)
  и НЕ трогает несводимое ядро GlobalOldAbsorption (шаг (2): согласованное с
  масштабом поглощение). Более того, барьер §29.5 здесь машинно виден:
  `fixedWindow_factorization_impossible_at_separating_scale` — при ФИКСИРОВАННОМ
  окне и разделяющем масштабе вход `FactorizationData` вообще пуст, т.е. недостающие
  карты обязаны жить на РАСТУЩЕМ масштабе, как и говорит проза. (в) — «двигатель»
  поставляется pump-контрадикцией (ex falso от rank-1 арифметики) — это принятая
  форма самого `engine_of_factorization`, здесь она лишь прогнана через второй скелет.

  Файл ЦЕЛИКОМ ЗЕЛЁНЫЙ: не импортирует Engine/CausalClosureAxiom (карантин),
  не добавляет аксиом и sorry, таинт-список из 47 деклараций не меняется.
-/

import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.SeparatingScale
import EuclidsPath.Engine.CarrierBridge
import EuclidsPath.Engine.BoundaryDecomp

set_option autoImplicit false

namespace EuclidsPath.TwinScaleAdvances

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.Residuals
open EuclidsPath.ProductCore

/-! ## (а) Малый масштаб мёртв при ВСЕХ базах M0 ≥ 1

Существующее `no_projection_resolves_at_smallScale` жёстко фиксировано на M0 = 1
(`fiveAdicChainFlow : ExtendedProperGeneratedFlow A 1`). Обобщаем: сама 5-адическая
цепь и её peel'ы от M0 не зависят (в `ProperRealStep` база входит только в
конструктор `absorb`, монотонно), терминал `center 1` — старый при любом M0 ≥ 1,
а старт берётся выше M0, потому что цепь растёт быстрее номера. -/

/-- **Монотонность собственного шага по базе.** `ProperRealStep A M0 ⊆ ProperRealStep A M1`
    при `M0 ≤ M1`: конструкторы `clean`/`boundary`/`peel` от базы не зависят, `absorb`
    требует `n ≤ M0 ≤ M1`. Чистая структурная лемма (разбор случаев). -/
theorem properRealStep_mono_basepoint {A M0 M1 : ℕ} (hM : M0 ≤ M1) {U V : State}
    (h : ProperRealStep A M0 U V) : ProperRealStep A M1 U V := by
  cases h with
  | clean hmClean hnClean hPeel => exact ProperRealStep.clean hmClean hnClean hPeel
  | boundary hmClean hBoundary => exact ProperRealStep.boundary hmClean hBoundary
  | peel hcert => exact ProperRealStep.peel hcert
  | absorb hOld => exact ProperRealStep.absorb (le_trans hOld hM)

/-- 5-адическая цепь не отстаёт от номера: `k ≤ c(k)`. Вместе со строгой
    монотонностью это неограниченность цепи — старт можно взять выше любого M0. -/
theorem fiveAdicChain_ge : ∀ k : ℕ, k ≤ fiveAdicChain k
  | 0 => Nat.zero_le _
  | k + 1 => by
      have ih := fiveAdicChain_ge k
      show k + 1 ≤ 5 * fiveAdicChain k + 1
      omega

/-- **Admissible-генеалогия при произвольной базе `M0 ≥ 1`** (обобщение
    `fiveAdicChainFlow` с M0 = 1). Старт — `c(M0+k+1) > M0` (свежесть через
    `fiveAdicChain_ge`), путь — тот же 5-адический (`fiveAdicChainPath`, поднятый
    по базе через `properRealStep_mono_basepoint`), терминал — старый clean-центр 1
    (`extendedLedgerTerminal_oldCleanCenter`, общий по M0). БЕЗ какой-либо twin-гипотезы. -/
def fiveAdicChainFlowAt {A M0 : ℕ} (hA : A ≤ 4) (hM0 : 1 ≤ M0) (k : ℕ) :
    ExtendedProperGeneratedFlow A M0 :=
  { start := fiveAdicChain (M0 + k + 1)
    terminal := State.center 1
    steps := M0 + k + 1
    nonempty := Nat.succ_pos _
    properPath := pathN_mono (R := ProperRealStep A 1) (S := ProperRealStep A M0)
      (fun hStep => properRealStep_mono_basepoint hM0 hStep)
      (fiveAdicChainPath hA (M0 + k + 1))
    startClean := clean_of_scale_le_four hA (fiveAdicChain_pos _)
    startFresh := by
      have h := fiveAdicChain_ge (M0 + k + 1)
      omega
    terminalLegal := clean_of_scale_le_four hA le_rfl
    ledgerTerminal := extendedLedgerTerminal_oldCleanCenter hM0
      (clean_of_scale_le_four hA le_rfl) }

/-- Семья инъективна по k — через строгую монотонность стартов
    (`fiveAdicChain_strictMono`), как и оригинал при M0 = 1. -/
theorem fiveAdicChainFlowAt_injective {A M0 : ℕ} (hA : A ≤ 4) (hM0 : 1 ≤ M0) :
    Function.Injective (fiveAdicChainFlowAt hA hM0) := by
  intro k₁ k₂ h
  have hstart : fiveAdicChain (M0 + k₁ + 1) = fiveAdicChain (M0 + k₂ + 1) :=
    congrArg ExtendedProperGeneratedFlow.start h
  have := fiveAdicChain_strictMono.injective hstart
  omega

/-- **МАЛЫЙ МАСШТАБ МЁРТВ ПРИ ВСЕХ БАЗАХ (кандидат №4).** Для `A ≤ 4` и ЛЮБОГО
    `M0 ≥ 1` никакая конечноключевая проекция не резолвит: инъективная 5-адическая
    поставка выше M0 + пижонхол `Finite.exists_ne_map_eq_of_infinite` дают same-key
    пару, а обе альтернативы резолюции сожжены (`no_extendedFlowResolutionAlternative`).
    Существующее `no_projection_resolves_at_smallScale` — частный случай M0 = 1.
    ЧЕСТНОСТЬ: при A ≥ 5 тот же приём требует чистых стартов с контролем peel-целей —
    арифметики дирихле-класса, которой в репо нет; узел там подлинно открыт. -/
theorem no_projection_resolves_at_smallScale_allM0 {A M0 : ℕ} (hA : A ≤ 4) (hM0 : 1 ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0) :
    ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  intro hRes
  letI : Finite proj.Key := proj.finiteKey
  obtain ⟨k₁, k₂, hne, hkey⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k => proj.keyFlow (fiveAdicChainFlowAt hA hM0 k))
  have hFne : fiveAdicChainFlowAt hA hM0 k₁ ≠ fiveAdicChainFlowAt hA hM0 k₂ :=
    fun h => hne (fiveAdicChainFlowAt_injective hA hM0 h)
  exact no_extendedFlowResolutionAlternative A M0
    (hRes _ _ hFne (extendedFlow_admissible _) (extendedFlow_admissible _) hkey)

/-- **Равномерное опровержение ветви A ≤ 4**: узел падает не «на всех M0 сразу
    через M0 = 1» (как `smallScale_branch_of_lastStep00Obligation_refuted`),
    а В КАЖДОЙ отдельной базе M0 ≥ 1 — резолвящей проекции нет ни при одной. -/
theorem smallScale_branch_refuted_at_every_basepoint {A M0 : ℕ}
    (hA : A ≤ 4) (hM0 : 1 ≤ M0) :
    ¬ ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj := by
  rintro ⟨proj, hRes⟩
  exact no_projection_resolves_at_smallScale_allM0 hA hM0 proj hRes

/-! ## (б) Растущий разделяющий масштаб (шаг (1) плана §29.6, CORR-маршрут)

План закрытия §29.6 начинается с масштаб-функции: для каждого окна m нужен масштаб A,
при котором сторона 6m+1 укладывается в окно (X_A := m — тривиально, равенством) и
выполняется разделяющий масштаб `6·X_A+1 < P_A` (гипотеза `hsep` всей pump-машины
ProductCore/CarrierBridge и `SeparatingScale.no_productHall`). CORR: примориал
`oldPrimorial A = ∏_{5≤p≤A} p` НЕ содержит 2 и 3, поэтому маршрут — один Бертран
на n = 6m+1: простое p с 6m+1 < p ≤ 12m+2 автоматически ≥ 5, и p само делит
oldPrimorial p. -/

/-- **РАСТУЩИЙ РАЗДЕЛЯЮЩИЙ МАСШТАБ (кандидат №5, CORR-маршрут).** Для каждого окна
    `m ≥ 1` существует масштаб `A` с явной границей `A ≤ 12m+2`, при котором
    `6m+1 < oldPrimorial A` — т.е. гипотеза разделяющего масштаба `hsep` выполнима
    с запасом на каждом окне, и масштаб-функция из шага (1) плана §29.6 существует.
    ОПЛАЧЕНО: постулат Бертрана (`Nat.exists_prime_lt_and_le_two_mul`: простое
    `6m+1 < p ≤ 12m+2`), `p ≥ 5` (т.к. `p > 6m+1 ≥ 7`), `p ∣ oldPrimorial p`
    (`prime_dvd_oldPrimorial`) и `Nat.le_of_dvd` + `oldPrimorial_pos`.
    ЧЕСТНОСТЬ: это конечная зелёная арифметика; несводимый шаг (2) плана —
    согласованное с масштабом поглощение (GlobalOldAbsorption) — НЕ затронут. -/
theorem exists_growing_separating_scale (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℕ, 5 ≤ A ∧ A ≤ 12 * m + 2 ∧ 6 * m + 1 < oldPrimorial A := by
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (6 * m + 1) (by omega)
  have hp5 : 5 ≤ p := by omega
  have hdvd : p ∣ oldPrimorial p := prime_dvd_oldPrimorial hp hp5 le_rfl
  have hlep : p ≤ oldPrimorial p := Nat.le_of_dvd (oldPrimorial_pos p) hdvd
  exact ⟨p, hp5, by omega, by omega⟩

/-- **Масштаб растёт вместе с окном**: разделяющий масштаб для окна `m` достижим
    ВЫШЕ любой наперёд заданной планки `B` — Бертран на `max (6m+1) B`. Это
    «согласованный рост A и X_A вместе с m» из §29.6 в существовательной форме. -/
theorem exists_growing_separating_scale_above (m B : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℕ, B ≤ A ∧ 5 ≤ A ∧ 6 * m + 1 < oldPrimorial A := by
  obtain ⟨p, hp, hlt, _⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (max (6 * m + 1) B) (by omega)
  have hp5 : 5 ≤ p := by omega
  have hdvd : p ∣ oldPrimorial p := prime_dvd_oldPrimorial hp hp5 le_rfl
  have hlep : p ≤ oldPrimorial p := Nat.le_of_dvd (oldPrimorial_pos p) hdvd
  exact ⟨p, by omega, hp5, by omega⟩

/-- **ProductHall мёртв на растущем окне** (стыковка с главой 30): для каждого
    окна `m ≥ 1` найдётся масштаб `A`, при котором legal ProductHall с
    `X_A := m`, `P_A := oldPrimorial A` невозможен — чистая арифметика
    `SeparatingScale.no_productHall`, гипотеза `hsep` которой оплачена
    `exists_growing_separating_scale`. -/
theorem no_legalProductHall_on_growing_window (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : ℕ, 5 ≤ A ∧
      (SeparatingScale.LegalProductHall m (oldPrimorial A) → False) := by
  obtain ⟨A, h5, _, hsep⟩ := exists_growing_separating_scale m hm
  exact ⟨A, h5, fun PH => SeparatingScale.no_productHall hsep PH⟩

/-- **Барьер §29.5 машинно виден.** При ФИКСИРОВАННОМ окне `X_A` и разделяющем
    масштабе вход `FactorizationData A X_A` ПУСТ: бесконечная инъективная
    AmbientLegal-семья на одном окне самоуничтожается pump-машиной (пижонхол по
    конечной `CoreSig` + доказанный descent + rank-1 арифметика) — это
    `engine_of_factorization` при `Engine := False`. ЧЕСТНОЕ следствие: недостающие
    карты `rankOf`/`mkNode`/`hinj`/`hamb` ОБЯЗАНЫ жить на растущем масштабе
    (шаг (2) плана §29.6, GlobalOldAbsorption), фиксированное окно исключено. -/
theorem fixedWindow_factorization_impossible_at_separating_scale
    {A X_A P_A : ℕ} [NeZero P_A] (hsep : 6 * X_A + 1 < P_A)
    (F : CarrierBridge.FactorizationData A X_A) : False :=
  CarrierBridge.engine_of_factorization (P_A := P_A) hsep F

/-! ## (в) Мост скелетов: CarrierBridge через пижонхол BoundaryDecomp

`BoundaryDecomp.global_absorber_forces_engine` — пижонхол-скелет Hall-узла
(бесконечные старты → конечный ключ → коллизия → pump). Ниже данные CarrierBridge
прогнаны через ЭТОТ скелет: key := coreSigOf ∘ node (конечный кодомен по
`coreSig_fintype`), pump := ДОКАЗАННАЯ машина ProductCore
(`product_core_pump_closed` = descent `core_step_proved` + rank-1 база). -/

/-- **МОСТ СКЕЛЕТОВ (кандидат №6).** `FactorizationData` + разделяющий масштаб дают
    `EuclideanEngine` РОВНО ЧЕРЕЗ пижонхол-скелет `global_absorber_forces_engine`:
    старты — subtype бесконечного `F.S`, ключ — `coreSigOf ∘ F.node` в конечную
    `CoreSig P_A F.r` (нужен фиксированный `P_A` с `[NeZero P_A]` и `hsep`; `hamb`
    обязателен для pump-направления), pump — доказанная descent-машина ProductCore.
    ЧЕСТНОСТЬ (CORR): это машинное ОТОЖДЕСТВЛЕНИЕ ДВУХ СКЕЛЕТОВ (Hall-pump узла
    BoundaryDecomp и цепи `engine_of_factorization`), а НЕ «одна стена вместо двух»:
    красные входы остаются оба — `FactorizationData` здесь по-прежнему гипотеза
    (при разделяющем масштабе она к тому же пуста, см. барьер выше, так что
    отождествление касается МАРШРУТА ДОКАЗАТЕЛЬСТВА, а не новых обитателей),
    а pump-гипотеза для настоящих генеалогий (GlobalOldTwinAbsorption) не закрыта. -/
theorem factorization_collision_as_absorber_instance
    {A X_A P_A : ℕ} {EuclideanEngine : Prop} [NeZero P_A]
    (hsep : 6 * X_A + 1 < P_A)
    (F : CarrierBridge.FactorizationData A X_A) : EuclideanEngine := by
  haveI : Infinite F.S := F.hS.to_subtype
  refine BoundaryDecomp.global_absorber_forces_engine
    (α := F.S) (Codom := CoreSig P_A F.r)
    Set.univ Set.infinite_univ
    (fun γ => coreSigOf (F.node γ.1))
    (fun γ₁ γ₂ hne hkey => ?_)
  refine product_core_pump_closed hsep ⟨F.r, F.hr.1, F.hr.2, ?_⟩
  exact ⟨F.node γ₁.1, F.node γ₂.1,
    fun h => hne (Subtype.ext (F.hinj γ₁.2 γ₂.2 h)),
    F.hamb γ₁.1 γ₁.2, F.hamb γ₂.1 γ₂.2, hkey⟩

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт репо НЕ меняется -/
#print axioms properRealStep_mono_basepoint
#print axioms fiveAdicChain_ge
#print axioms fiveAdicChainFlowAt
#print axioms fiveAdicChainFlowAt_injective
#print axioms no_projection_resolves_at_smallScale_allM0
#print axioms smallScale_branch_refuted_at_every_basepoint
#print axioms exists_growing_separating_scale
#print axioms exists_growing_separating_scale_above
#print axioms no_legalProductHall_on_growing_window
#print axioms fixedWindow_factorization_impossible_at_separating_scale
#print axioms factorization_collision_as_absorber_instance

end EuclidsPath.TwinScaleAdvances
