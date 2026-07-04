/-
  RiemannLawEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ закона манифестации Римана
  (зеркало CollatzFirstCause/PNPFirstCause по программе Яруса 1).
  Зелёная машина: Engine/RiemannManifestationFront.lean (цепь L1–L9).

  ЧТО ЭТО. «Решить Римана изнутри» = внутренне самообосновать закон манифестации
  (`RiemannManifestationLaw`, содержание декретного поля `riemannBoundary` —
  здесь НЕ принимаемого): нести одновременно сам закон и свидетельство, что он
  выведен из-за собственного горизонта. Самообоснование самоуничтожается
  (`riemannCause_unknowable`), а единственный внутренний след отклонения —
  вечный двигатель: поставка отклонения на разрешённом масштабе СТРОИТ
  двигатель-свидетель (`deviation_carries_engine_at_resolved_scale`), который
  убит lexRank'ом. Решает только внешний декрет: закон при границе даёт RH —
  здесь граница фигурирует ГИПОТЕЗОЙ (`h : TheStrictLastStep00Obligation`),
  НЕ аксиомой; модуль карантин не импортирует.

  ЧЕСТНОСТЬ (обязательные оговорки):
    * Это модель-внутренняя эпистемика, НЕ решение гипотезы Римана и НЕ Гёдель
      (никакой независимости/неподвижной точки — только пижонхол-стена).
    * Связка `InternalisedRiemannGround` ФОРМАЛЬНА — как у Коллатца после
      падения декрета: `beyondOwnHorizon = ¬ground` (форма P ∧ ¬P). Чем она
      оплачена: настоящим зелёным фактом «поставка в стабильной вселенной
      строит двигатель» (`infiniteFlows_in_stableNoEnergy_build_engine`,
      потреблённая в `no_deviationFlowSupply_at_resolved_scale`) — он
      потребляется НЕ ex falso в отдельной теореме
      `deviation_carries_engine_at_resolved_scale`.
    * Ни одно поле связки зелёно не заселяемо: нуль-свидетель = ¬RH,
      разрешающий леджер — открытый twin-узел (при A ≤ 4 разрешение
      опровергнуто `no_projection_resolves_at_smallScale`); по L6
      (`manifestationLaw_iff_no_resolution_above_zero`) `beyondOwnHorizon`
      при данном `ground` эквивалентен отрицанию его следствия. Это НИЖЕ
      эталона P/NP (там `beyondOwnHorizon` зелёно инстанцирован при A ≤ 4)
      и ровно уровень Коллатца.
    * В отличие от безусловного на объекте `nonHalting_carries_perpetual_engine`
      Коллатца, римановский двигатель ГЕЙТИРОВАН разрешающим масштабом:
      отклонение предъявляет двигатель только там, где книги сведены, — а
      разрешение и есть открытый twin-узел/граница.
  Модуль ЦЕЛИКОМ ЗЕЛЁНЫЙ: без axiom/sorry, без импорта карантина
  (CausalClosureAxiom), таинт репозитория (47 после снятия четвёртой границы,
  1936826) НЕ меняется.
-/

import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.RiemannLiouville

set_option autoImplicit false

namespace EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic

/-! ## Модель: внутреннее решение = самообоснование за собственным горизонтом -/

/-- **Внутреннее самообоснование закона манифестации Римана**: несёт сам закон
    (`ground`) И свидетельство, что тот выведен из-за собственного горизонта
    (`beyondOwnHorizon`). ФОРМА КАК У КОЛЛАТЦА (`InternalisedCollatzGround`):
    `beyondOwnHorizon = ¬ground` — тавтологическая пара P ∧ ¬P, и это сказано
    прямо. Содержательность оплачена отдельно: настоящий зелёный факт «поставка
    отклонения в стабильной вселенной строит двигатель»
    (`infiniteFlows_in_stableNoEnergy_build_engine` внутри
    `no_deviationFlowSupply_at_resolved_scale`) потребляется НЕ ex falso в
    `deviation_carries_engine_at_resolved_scale` ниже. Ни одно поле зелёно не
    заселяемо: нуль = ¬RH, разрешающий леджер — открытый twin-узел. -/
structure InternalisedRiemannGround : Prop where
  ground : RiemannManifestationLaw
  beyondOwnHorizon : ¬ RiemannManifestationLaw

/-- «Внутреннее знание причины Римана» = внутреннее самообоснование закона
    манифестации (зеркало `InternalKnowledgeOfCollatzCause`). -/
abbrev InternalKnowledgeOfRiemannCause : Prop := InternalisedRiemannGround

/-! ## Ядро: самообоснование самоуничтожается (🟢) -/

/-- Самообоснование самоуничтожается — ровно `fun H => H.beyondOwnHorizon
    H.ground` Коллатца. ЧЕСТНОСТЬ: несущая часть здесь — форма; содержание
    живёт в `deviation_carries_engine_at_resolved_scale`. ЗЕЛЁНАЯ, без аксиом. -/
theorem no_internalisedRiemannGround : InternalisedRiemannGround → False :=
  fun H => H.beyondOwnHorizon H.ground

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `collatzCause_unknowable`,
    `pnpCause_unknowable`): внутреннее самообоснование закона манифестации
    невозможно. НЕ утверждается ни гёделевская независимость, ни что-либо о
    самой RH — только невозможность внутреннего самообоснования. ЗЕЛЁНАЯ. -/
theorem riemannCause_unknowable : ¬ InternalKnowledgeOfRiemannCause :=
  no_internalisedRiemannGround

/-! ## Оплата: опровержение-несёт-двигатель для Римана (🟢, не ex falso) -/

/-- **«ОТКЛОНЕНИЕ НЕСЁТ ДВИГАТЕЛЬ» (подлинная конструкция, зеркало
    `nonHalting_carries_perpetual_engine`):** поставка отклонения на
    разрешённом масштабе СТРОИТ конкретный евклидов двигатель — стабильная
    no-energy вселенная + бесконечное семейство ⟹ пижонхол-коллизия конечного
    ключа ⟹ двигатель-свидетель. Гипотезы потребляются ПО-НАСТОЯЩЕМУ (не
    ex falso): это та самая цепь, что внутри L2
    (`no_deviationFlowSupply_at_resolved_scale`), с явным двигателем в выводе.
    ОГОВОРКА: в отличие от Коллатца факт гейтирован разрешающим масштабом
    (`hres`) — а разрешение и есть открытый twin-узел (при A ≤ 4 оно
    опровергнуто `no_projection_resolves_at_smallScale`). -/
theorem deviation_carries_engine_at_resolved_scale {A M0 : ℕ}
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj)
    (hSupply : DeviationFlowSupply A M0) :
    SomeConcreteEuclideanEngine := by
  obtain ⟨𝓕, h𝓕⟩ := hSupply
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact ⟨A, M0, hEngine⟩

/-- Ex-falso companion (зеркало `internalisedPNPGround_builds_engine`): из
    самообоснования (уже ложного) выводится и сам двигатель. ЧЕСТНОСТЬ:
    маршрут ex falso; несущая часть — `no_internalisedRiemannGround`, а
    НЕ-ex-falso двигатель Римана — `deviation_carries_engine_at_resolved_scale`. -/
theorem internalisedRiemannGround_builds_engine :
    InternalisedRiemannGround → SomeConcreteEuclideanEngine :=
  fun H => (no_internalisedRiemannGround H).elim

/-! ## Сводки: решение заперто за двигателем (🟢) -/

/-- **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» — 3-РАЗВИЛКА (зелёная; зеркало
    `collatz_no_internal_decision_without_engine`):**
    (1) ОТКЛОНЕНИЕ ПРИ СВЕДЁННЫХ КНИГАХ = ДВИГАТЕЛЬ — подлинная конструкция
        (`deviation_carries_engine_at_resolved_scale`), двигатель затем убит
        lexRank'ом (`no_someConcreteEuclideanEngine`);
    (2) САМООБОСНОВАТЬ закон изнутри — самоуничтожается
        (`no_internalisedRiemannGround`);
    (3) ВНЕШНИЙ ДЕКРЕТ решает: закон при границе даёт RH
        (`riemannHypothesis_of_manifestation_and_boundary` +
        `no_someConcreteEuclideanEngine`) — граница фигурирует ГИПОТЕЗОЙ
        `h : TheStrictLastStep00Obligation`, НЕ аксиомой: конъюнкт остаётся
        зелёной импликацией, таинт не растёт.
    НЕ утверждается ни RH, ни её независимость — только: оба внутренних пути
    стоят двигателя, а декретная дверь оценена (по L7 закон при границе ровно
    RH-силы: `manifestationLaw_iff_RH_of_boundary`). -/
theorem riemann_no_internal_decision_without_engine :
    (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0 → SomeConcreteEuclideanEngine) ∧
    (InternalisedRiemannGround → False) ∧
    (∀ _h : TheStrictLastStep00Obligation,
        RiemannManifestationLaw → RiemannHypothesis) :=
  ⟨fun _A _M0 proj hres hSupply =>
      deviation_carries_engine_at_resolved_scale proj hres hSupply,
   no_internalisedRiemannGround,
   fun h hLaw =>
      riemannHypothesis_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine h hLaw⟩

/-- Итоговый эпистемический статус римановского горизонта (зеркало
    `pnp_locked_behind_engine_status` / `collatz_open_status`; целиком в
    implication-форме — зелёный, декрет только гипотезой):
    внутреннее знание невозможно (теорема) / отклонение при сведённых книгах
    строит двигатель (теорема, подлинная конструкция) / поставки отклонения на
    разрешённом масштабе нет (теорема L2 — та же стена) / закон при границе
    даёт RH (условно, `TheStrictLastStep00Obligation` гипотезой). RH остаётся
    открытой; этот статус её НЕ двигает. -/
theorem riemann_locked_behind_engine_status :
    (¬ InternalKnowledgeOfRiemannCause) ∧
    (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0 → SomeConcreteEuclideanEngine) ∧
    (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
        ¬ DeviationFlowSupply A M0) ∧
    (TheStrictLastStep00Obligation →
        RiemannManifestationLaw → RiemannHypothesis) :=
  ⟨riemannCause_unknowable,
   fun _A _M0 proj hres hSupply =>
      deviation_carries_engine_at_resolved_scale proj hres hSupply,
   fun _A _M0 proj hres => no_deviationFlowSupply_at_resolved_scale proj hres,
   fun hBoundary hLaw =>
      riemannHypothesis_of_manifestation_and_boundary
        no_someConcreteEuclideanEngine hBoundary hLaw⟩

/-! ## Twin-сторона: twin-граница замораживает всякий разрешающий леджер (🟢) -/

/-- **Twin-граница замораживает разрешение**: если выше масштаба `M0` близнецов
    нет (`TwinBoundAbove M0`), то НИКАКАЯ леджер-проекция на этом масштабе не
    сводит книги — twin-bound зелёно поставляет бесконечное семейство потоков
    (L1, `deviationFlowSupply_of_twinBound`), а разрешённый масштаб такой
    поставки не терпит (L2, `no_deviationFlowSupply_at_resolved_scale`:
    коллизия ⟹ двигатель ⟹ lexRank). Именует twin-сторону характеризации L6
    (`manifestationLaw_iff_no_resolution_above_zero`) явной леммой.
    ЧЕСТНОСТЬ: логически это переупаковка композиции L1 ∘ L2 — НЕ
    `twins_infinite_of_noEngine_and_boundary` (та лемма живёт в карантинном
    модуле и выводит бесконечность близнецов из ¬двигателей + границы —
    другое утверждение). Про сами близнецы здесь НИЧЕГО не утверждается:
    `TwinBoundAbove` — гипотеза. ЗЕЛЁНАЯ, без аксиом. -/
theorem twinBound_freezes_resolution {M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0) :
    ∀ (A : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
      ¬ SemanticExtendedFlowLedgerCollisionResolves proj :=
  fun _A proj hres =>
    no_deviationFlowSupply_at_resolved_scale proj hres
      (deviationFlowSupply_of_twinBound hTwinBound)

/-! ## Лиувиллева ветвь: обе RH-ветви сходятся к одному декрету (🟢-условно) -/

/-- **Лиувилль вшит в декрет (зелёно-условная цепь):** классический мост
    Лиувилля (гипотезой) + ¬двигателей + граница (гипотезой) + закон
    манифестации ⟹ `LiouvilleBound` (`|L(x)| ≤ C·x^{1/2+ε}`). Композиция:
    тройка essence-гипотез даёт RH (L4,
    `riemannHypothesis_of_manifestation_and_boundary`), мост переносит RH в
    арифметический bound (`bridge.mpr`). ЧЕМ ОПЛАЧЕНО (честно, по слоям):
    (1) `LiouvilleRHBridge` — КРАСНЫЙ вход: классическая эквивалентность
        `LiouvilleBound ⟺ RH` аналитической теории чисел, в mathlib
        отсутствует — здесь строго ГИПОТЕЗОЙ;
    (2) граница — ГИПОТЕЗОЙ (`TheStrictLastStep00Obligation`), не аксиомой;
    (3) закон манифестации при границе ровно RH-силы (L7,
        `manifestationLaw_iff_RH_of_boundary`) — теорема НЕ добывает bound,
        а показывает СХОДИМОСТЬ обеих RH-ветвей (нулевой и лиувиллевой)
        к одному и тому же декрету. НЕ решение RH и не новый bound. -/
theorem liouvilleBound_of_manifestation_and_boundary
    (hBridge : EuclidsPath.RiemannLiouville.LiouvilleRHBridge)
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hManifest : RiemannManifestationLaw) :
    EuclidsPath.RiemannLiouville.LiouvilleBound :=
  hBridge.mpr
    (riemannHypothesis_of_manifestation_and_boundary
      hNoEngine hBoundary hManifest)

/-! ## Минимизация второй границы: закон только на собственной высоте нуля (🟢) -/

/-- **МИНИМАЛЬНЫЙ закон манифестации (law-at-own-height):** от каждого
    off-critical нуля требуется манифестация ТОЛЬКО на масштабе его
    собственной высоты `M0 = zeroHeight Z` — а не на всех масштабах
    `M0 ≥ zeroHeight Z`, как в полном `RiemannManifestationLaw`. Синтаксически
    строго слабее полного закона (тот навешивает ∀-хвост по масштабам);
    essence-лемма L3 содержательно использует РОВНО этот один масштаб
    (`le_refl` в `noOffCriticalZero_of_manifestation_and_boundary`) — поэтому
    минимальной формы достаточно (`minimalLaw_suffices` ниже). Документирует
    минимальное логическое содержание декретного поля `riemannBoundary`;
    здесь НЕ принимается — только определён. -/
def MinimalRiemannManifestationLaw : Prop :=
  ∀ (Z : RiemannOffCriticalZero) (A : ℕ)
    (proj : SemanticExtendedFlowLedgerProjection A (zeroHeight Z)),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A (zeroHeight Z)

/-- Полный закон влечёт минимальный: инстанциация `M0 := zeroHeight Z`,
    `le_refl`. Тривиальное направление — ослабление синтаксическое. -/
theorem minimalLaw_of_manifestationLaw
    (hLaw : RiemannManifestationLaw) : MinimalRiemannManifestationLaw :=
  fun Z A proj hres => hLaw Z A (zeroHeight Z) (le_refl _) proj hres

/-- Essence-лемма при МИНИМАЛЬНОМ законе (переигранное L3): ¬двигателей +
    граница (гипотезой) + минимальный закон ⟹ off-critical нулей нет.
    Дословно тот же вывод, что L3, — подтверждение, что полный закон нигде
    не использовался сверх собственной высоты нуля. Все гипотезы потребляются
    по-настоящему (двигатель-свидетель убит именно `hNoEngine`). -/
theorem noOffCriticalZero_of_minimalLaw_and_boundary
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hMinimal : MinimalRiemannManifestationLaw) :
    ¬ Nonempty RiemannOffCriticalZero := by
  rintro ⟨Z⟩
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves :
      SemanticExtendedFlowLedgerCollisionResolves (projOf (zeroHeight Z)) :=
    strictSemanticExtended_resolves_old (hres (zeroHeight Z))
  have hStable : NoEnergyStableUniverse (projOf (zeroHeight Z)) :=
    (noEnergyStableUniverse_iff_resolves (projOf (zeroHeight Z))).mpr hResolves
  obtain ⟨𝓕, h𝓕⟩ := hMinimal Z A (projOf (zeroHeight Z)) hResolves
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hNoEngine ⟨A, zeroHeight Z, hEngine⟩

/-- **Минимальной формы достаточно:** ¬двигателей + граница (гипотезой) +
    минимальный закон ⟹ RH. Зеркало L4 над `MinimalRiemannManifestationLaw`;
    экстракция нуля из ¬RH — mathlib-точная (`offCriticalZero_of_not_RH`).
    ГРАНИЦА ГИПОТЕЗОЙ, не аксиомой — конъюнкт зелёный, таинт не растёт. -/
theorem minimalLaw_suffices
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hMinimal : MinimalRiemannManifestationLaw) :
    RiemannHypothesis := by
  by_contra hNotRH
  exact noOffCriticalZero_of_minimalLaw_and_boundary
    hNoEngine hBoundary hMinimal
    (EuclidsPath.RiemannImpossibleEngineOff.offCriticalZero_of_not_RH hNotRH)

/-- **ОБЯЗАТЕЛЬНЫЙ АУДИТ ЦЕНЫ (зеркало L7):** при границе минимальный закон
    ⟺ RH — та же RH-сила, что у полного закона. -/
theorem minimalManifestationLaw_iff_RH_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    MinimalRiemannManifestationLaw ↔ RiemannHypothesis :=
  ⟨minimalLaw_suffices no_someConcreteEuclideanEngine hBoundary,
   fun hRH => minimalLaw_of_manifestationLaw (manifestationLaw_of_RH hRH)⟩

/-- **ЧЕСТНАЯ ОГОВОРКА МАШИННО:** при границе минимальный закон ⟺ полный —
    «ослабление» СИНТАКСИЧЕСКОЕ, не силовое (по L7 и аудиту выше обе формы
    ровно RH-силы). Это УТОЧНЕНИЕ цены декрета — какое именно логическое
    содержание поля `riemannBoundary` несёт всю нагрузку, — а НЕ снижение
    этой цены. БЕЗ границы доказана только тривиальная половина
    (`minimalLaw_of_manifestationLaw`). -/
theorem minimalLaw_iff_manifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    MinimalRiemannManifestationLaw ↔ RiemannManifestationLaw :=
  (minimalManifestationLaw_iff_RH_of_boundary hBoundary).trans
    (manifestationLaw_iff_RH_of_boundary hBoundary).symm

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка максимум),
таинт репозитория НЕ меняется -/
#print axioms InternalisedRiemannGround
#print axioms InternalKnowledgeOfRiemannCause
#print axioms no_internalisedRiemannGround
#print axioms riemannCause_unknowable
#print axioms deviation_carries_engine_at_resolved_scale
#print axioms internalisedRiemannGround_builds_engine
#print axioms riemann_no_internal_decision_without_engine
#print axioms riemann_locked_behind_engine_status
#print axioms twinBound_freezes_resolution
#print axioms liouvilleBound_of_manifestation_and_boundary
#print axioms MinimalRiemannManifestationLaw
#print axioms minimalLaw_of_manifestationLaw
#print axioms noOffCriticalZero_of_minimalLaw_and_boundary
#print axioms minimalLaw_suffices
#print axioms minimalManifestationLaw_iff_RH_of_boundary
#print axioms minimalLaw_iff_manifestationLaw_of_boundary

end EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.Epistemic
