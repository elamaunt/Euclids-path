/-
  FermatMersenneEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ ветвей Ферма и Мерсенна
  (зеркало CollatzFirstCause/PNPFirstCause, но для ДВУХ фронтов сразу).
  Зелёные машины: Engine/FermatManifestationFront.lean и
  Engine/MersenneManifestationFront.lean.

  ЧТО ЭТО. У обеих ветвей манифестационные границы СОЗНАТЕЛЬНО НЕ ВЗЯТЫ —
  вердикт §16/§17: знак эвристики инвертирован. У Ферма жёстче всего в
  программе (простыми известны лишь F₀–F₄, а F₅–F₃₂ ДОКАЗУЕМО составны —
  вход `FermatTwinCentersUnbounded` скорее всего ложен); у Мерсенна сумма по
  twin-парам сходится, известны лишь p = 3, 5, и 5 ∣ 2^p − 3 при p ≡ 3 (mod 4).
  Законы манифестации живут ОПРЕДЕЛЕНИЯМИ (`FermatManifestationLaw`,
  `MersenneManifestationLaw`), не декретами; M7-аудиты фронтов показывают, что
  декрет стоил бы ровно открытой гипотезы. Этот модуль добавляет к отказу от
  декрета эпистемическое объяснение: ВНУТРЕННИХ путей тоже нет. Самообосновать
  закон поверх собственного свидетеля опровержения = собрать вечный двигатель
  (`fermatRefutation_carries_engine` / `mersenneRefutation_carries_engine`
  строят `ConcreteEuclideanEngineWitness` как объект) — и погибнуть об
  `lexRank` (`no_someConcreteEuclideanEngine`); единственный без-двигательный
  путь — ВНЕШНЯЯ граница `TheStrictLastStep00Obligation`, которой этим ветвям
  намеренно не дано. Обе двери — декретная и внутренняя — закрыты, и обе
  закрыты ЗЕЛЕНО.

  ЧЕСТНОСТЬ (обязательные оговорки).
  (1) Это МОДЕЛЬ-ВНУТРЕННЯЯ эпистемическая непознаваемость (как
      `collatzCause_unknowable` и `pnpCause_unknowable`), НЕ решение вопроса о
      бесконечности Ферма- и Мерсенн-близнецов и НЕ Гёдель: никакой теоремы о
      неполноте — только пижонхол-самоуничтожение о стену вполне-фундированности.
  (2) Связка НЕ вырождается в голое `P ∧ ¬P`: `beyondOwnHorizon` — НЕ отрицание
      `ground`, а самостоятельный пакет «свидетель отсутствия + сведённые книги»,
      и False оплачен подлинной двигательной конструкцией (закон превращает
      отсутствие в поставку потоков, конечный ключ пижонхолом сталкивает два
      потока, из коллизии собирается двигатель-СВИДЕТЕЛЬ, убивает его lexRank).
      Вырожденную форму `beyondOwnHorizon := ¬FermatManifestationLaw` брать
      НЕЛЬЗЯ — она была бы тавтологией без оплаты (коллатцевская форма, честно
      помеченная таковой в CollatzFirstCause).
  (3) ОГОВОРКА СИЛЫ: связка СЛАБЕЕ P/NP-эталона — там `beyondOwnHorizon`
      (`UnboundedCertificateSupply`) зелёно ИНСТАНЦИРУЕМ при A ≤ 4
      (`concreteSupply_unbounded_smallScale`); здесь НИ ОДНО поле зелёно не
      реализуемо: свидетель отсутствия = решение открытой задачи о хвосте,
      сведённые книги = содержание сознательно не взятого декрета. Зато
      СИЛЬНЕЕ коллатцевской тавтологичной пары ground/¬ground. Гибрид:
      конструкция противоречия настоящая, обитаемость сторон — открытая.

  Модуль ЦЕЛИКОМ ЗЕЛЁНЫЙ: карантин (CausalClosureAxiom) НЕ импортируется,
  axiom/sorry/native_decide нет, таинт репозитория не меняется.
-/

import EuclidsPath.Engine.FermatManifestationFront
import EuclidsPath.Engine.MersenneManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation
namespace Epistemic

/-! ## Модель: внутреннее самообоснование ветви Ферма -/

/-- **Внутреннее самообоснование Ферма-ветви.** Несёт закон манифестации
    (`ground` = `FermatManifestationLaw` — точное содержание сознательно НЕ
    взятой границы, §16/§17) И пакет «свидетель опровержения внутри мира со
    сведёнными книгами» (`beyondOwnHorizon`): порог отсутствия `P`, масштаб
    `M0 ≥ P` и разрешающая проекция. Форма содержательна — `beyondOwnHorizon`
    НЕ есть `¬ground` (вырожденную форму `beyondOwnHorizon := ¬Law` брать
    нельзя — голое `P ∧ ¬P`); противоречие ниже оплачено подлинной двигательной
    конструкцией `fermatRefutation_carries_engine`. ЧЕСТНАЯ ОГОВОРКА: ни одно
    поле зелёно не инстанцируемо (свидетель = решение открытой задачи о хвосте
    Ферма-близнецов, resolves = содержание не взятого декрета) — слабее
    P/NP-эталона (`concreteSupply_unbounded_smallScale` при A ≤ 4), сильнее
    коллатцевской тавтологичной формы. -/
structure InternalisedFermatGround : Prop where
  ground : FermatManifestationLaw
  beyondOwnHorizon :
    ∃ (P A M0 : ℕ), FermatTwinAbsenceAbove P ∧ P ≤ M0 ∧
      ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj

/-- «Внутреннее знание причины Ферма-ветви» = внутреннее самообоснование. -/
abbrev InternalKnowledgeOfFermatCause : Prop := InternalisedFermatGround

/-- **Самообоснование Ферма СТРОИТ двигатель — как объект, НЕ ex falso:**
    закон (`ground`) превращает свидетеля отсутствия в неоплатимую поставку
    потоков на разрешённом масштабе, пижонхол конечного ключа сталкивает два
    потока, из коллизии собирается `ConcreteEuclideanEngineWitness` (вся
    механика внутри `fermatRefutation_carries_engine`). Двигатель предъявлен
    ДО всякого убийства — это несущая конструкция связки. -/
theorem internalisedFermatGround_builds_engine :
    InternalisedFermatGround → SomeConcreteEuclideanEngine := by
  intro H
  obtain ⟨P, A, M0, hAbs, hM, proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, fermatRefutation_carries_engine H.ground hAbs hM proj hres⟩

/-- Самообоснование самоуничтожается об стену вечного двигателя: построенный
    свидетель убит `lexRank` (`no_someConcreteEuclideanEngine`). ЗЕЛЁНАЯ. -/
theorem no_internalisedFermatGround : InternalisedFermatGround → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedFermatGround_builds_engine H)

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА ветви Ферма** (зеркало
    `collatzCause_unknowable` / `pnpCause_unknowable`): внутреннее
    самообоснование закона манифестации Ферма невозможно. Это НЕ утверждение
    о самих Ферма-близнецах — только о внутреннем пути к границе, которой
    ветви намеренно не дано (§16/§17). -/
theorem fermatCause_unknowable : ¬ InternalKnowledgeOfFermatCause :=
  no_internalisedFermatGround

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ (без ex falso в утверждении): либо причина
    непознаваема изнутри, либо при законе книги НИКОГДА не сводятся выше
    свидетеля отсутствия (правая рука — M6-заморозка
    `fermatManifestationLaw_iff_no_resolution_above_absence`).
    Левый дизъюнкт — теорема. -/
theorem unknowable_or_fermat_books_never_resolve :
    (¬ InternalKnowledgeOfFermatCause) ∨
      (FermatManifestationLaw →
        ∀ P : ℕ, FermatTwinAbsenceAbove P →
          ∀ (A M0 : ℕ), P ≤ M0 →
            ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
              ¬ SemanticExtendedFlowLedgerCollisionResolves proj) :=
  Or.inl fermatCause_unknowable

/-! ## Модель: внутреннее самообоснование ветви Мерсенна (зеркально) -/

/-- **Внутреннее самообоснование Мерсенн-ветви** — точное зеркало
    `InternalisedFermatGround` с `MersenneManifestationLaw` (граница также
    сознательно НЕ взята — §16: Σ по twin-парам сходится, 5 ∣ 2^p − 3 при
    p ≡ 3 (mod 4)). Все оговорки Ферма-версии дословно переносятся: поля
    зелёно не инстанцируемы, `beyondOwnHorizon ≠ ¬ground`, оплата —
    двигательная конструкция `mersenneRefutation_carries_engine`. -/
structure InternalisedMersenneGround : Prop where
  ground : MersenneManifestationLaw
  beyondOwnHorizon :
    ∃ (P A M0 : ℕ), MersenneTwinAbsenceAbove P ∧ P ≤ M0 ∧
      ∃ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj

/-- «Внутреннее знание причины Мерсенн-ветви» = внутреннее самообоснование. -/
abbrev InternalKnowledgeOfMersenneCause : Prop := InternalisedMersenneGround

/-- **Самообоснование Мерсенна СТРОИТ двигатель — как объект, НЕ ex falso**
    (зеркало `internalisedFermatGround_builds_engine`, механика внутри
    `mersenneRefutation_carries_engine`). -/
theorem internalisedMersenneGround_builds_engine :
    InternalisedMersenneGround → SomeConcreteEuclideanEngine := by
  intro H
  obtain ⟨P, A, M0, hAbs, hM, proj, hres⟩ := H.beyondOwnHorizon
  exact ⟨A, M0, mersenneRefutation_carries_engine H.ground hAbs hM proj hres⟩

/-- Самообоснование самоуничтожается об ту же стену (`lexRank`). ЗЕЛЁНАЯ. -/
theorem no_internalisedMersenneGround : InternalisedMersenneGround → False :=
  fun H => no_someConcreteEuclideanEngine (internalisedMersenneGround_builds_engine H)

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА ветви Мерсенна** (зеркало
    `fermatCause_unknowable`): внутреннее самообоснование закона манифестации
    Мерсенна невозможно. НЕ решение вопроса о Мерсенн-близнецах. -/
theorem mersenneCause_unknowable : ¬ InternalKnowledgeOfMersenneCause :=
  no_internalisedMersenneGround

/-- СОДЕРЖАТЕЛЬНАЯ ДИХОТОМИЯ Мерсенна (зеркало Ферма-версии; правая рука —
    M6-заморозка `mersenneManifestationLaw_iff_no_resolution_above_absence`).
    Левый дизъюнкт — теорема. -/
theorem unknowable_or_mersenne_books_never_resolve :
    (¬ InternalKnowledgeOfMersenneCause) ∨
      (MersenneManifestationLaw →
        ∀ P : ℕ, MersenneTwinAbsenceAbove P →
          ∀ (A M0 : ℕ), P ≤ M0 →
            ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
              ¬ SemanticExtendedFlowLedgerCollisionResolves proj) :=
  Or.inl mersenneCause_unknowable

/-! ## Сводки: обе ветви заперты за двигателем (🟢) -/

/-- **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» — обе ветви сразу** (зеркало
    `pnp_no_internal_decision_without_engine` /
    `collatz_no_internal_decision_without_engine`):
    (1) ОПРОВЕРГНУТЬ при законе и сведённых книгах = предъявить двигатель как
        объект (`fermatRefutation_carries_engine` /
        `mersenneRefutation_carries_engine` — подлинное потребление гипотез);
    (2) САМООБОСНОВАТЬ изнутри — самоуничтожается
        (`no_internalisedFermatGround` / `no_internalisedMersenneGround`);
    (3) единственный без-двигательный путь — ВНЕШНЯЯ граница
        `TheStrictLastStep00Obligation`: при ней закон даёт неограниченность
        (ESSENCE M3 обоих фронтов с зелёной стеной
        `no_someConcreteEuclideanEngine`) — но ровно этой границы ветвям
        намеренно НЕ дано (§16/§17, знак эвристики).
    НЕ утверждается гёделевская независимость и НЕ решаются сами гипотезы —
    только: оба внутренних пути стоят вечного двигателя, а декретная дверь
    сознательно не открыта. -/
theorem fermatMersenne_no_internal_decision_without_engine :
    ((FermatManifestationLaw → ∀ P : ℕ, FermatTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0) ∧
     (MersenneManifestationLaw → ∀ P : ℕ, MersenneTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            SemanticExtendedFlowLedgerCollisionResolves proj →
              ConcreteEuclideanEngineWitness A M0)) ∧
    ((InternalisedFermatGround → False) ∧
     (InternalisedMersenneGround → False)) ∧
    ((TheStrictLastStep00Obligation → FermatManifestationLaw →
        EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) ∧
     (TheStrictLastStep00Obligation → MersenneManifestationLaw →
        EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded)) :=
  ⟨⟨fun hLaw _P hAbs _A _M0 hM proj hres =>
        fermatRefutation_carries_engine hLaw hAbs hM proj hres,
    fun hLaw _P hAbs _A _M0 hM proj hres =>
        mersenneRefutation_carries_engine hLaw hAbs hM proj hres⟩,
   ⟨no_internalisedFermatGround, no_internalisedMersenneGround⟩,
   ⟨fun hB hLaw => fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
        no_someConcreteEuclideanEngine hB hLaw,
    fun hB hLaw => mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
        no_someConcreteEuclideanEngine hB hLaw⟩⟩

/-- Итоговый эпистемический статус обеих ветвей (зеркало
    `pnp_locked_behind_engine_status` — БЕЗ декрет-конъюнкта: полей
    fermatBoundary/mersenneBoundary в первопричине НЕТ, и это сознательное
    решение §16/§17 по знаку эвристики):
    (1) локализации доменов свидетелей — всякая граница отсутствия ≥ 65537
        (Ферма, пара F₄ = 65537) и ≥ 29 (Мерсенн, пара p = 5);
    (2) внутреннее знание невозможно — обе теоремы;
    (3) M7-аудит цены: при внешней границе закон ⟺ открытая неограниченность —
        декрет стоил бы ровно открытой гипотезы (потому и не взят);
    (4) стена: вечных двигателей нет ни на каком масштабе
        (`no_someConcreteEuclideanEngine`, lexRank).
    ЗЕЛЁНАЯ целиком; эпистемика объясняет, почему при не взятых границах нет
    и внутренних путей: обе двери ведут в одну стену. -/
theorem fermatMersenne_locked_behind_engine_status :
    ((∀ P : ℕ, FermatTwinAbsenceAbove P → 65537 ≤ P) ∧
     (∀ P : ℕ, MersenneTwinAbsenceAbove P → 29 ≤ P)) ∧
    ((¬ InternalKnowledgeOfFermatCause) ∧
     (¬ InternalKnowledgeOfMersenneCause)) ∧
    (TheStrictLastStep00Obligation →
      ((FermatManifestationLaw ↔
          EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) ∧
       (MersenneManifestationLaw ↔
          EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded))) ∧
    ¬ SomeConcreteEuclideanEngine :=
  ⟨⟨fun _ hAbs => fermatAbsenceBound_ge_65537 hAbs,
    fun _ hAbs => mersenneAbsenceBound_ge_29 hAbs⟩,
   ⟨fermatCause_unknowable, mersenneCause_unknowable⟩,
   fun hB => ⟨fermatManifestationLaw_iff_unbounded_of_boundary hB,
              mersenneManifestationLaw_iff_unbounded_of_boundary hB⟩,
   no_someConcreteEuclideanEngine⟩

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт не меняется -/
#print axioms InternalisedFermatGround
#print axioms InternalKnowledgeOfFermatCause
#print axioms internalisedFermatGround_builds_engine
#print axioms no_internalisedFermatGround
#print axioms fermatCause_unknowable
#print axioms unknowable_or_fermat_books_never_resolve
#print axioms InternalisedMersenneGround
#print axioms InternalKnowledgeOfMersenneCause
#print axioms internalisedMersenneGround_builds_engine
#print axioms no_internalisedMersenneGround
#print axioms mersenneCause_unknowable
#print axioms unknowable_or_mersenne_books_never_resolve
#print axioms fermatMersenne_no_internal_decision_without_engine
#print axioms fermatMersenne_locked_behind_engine_status

end Epistemic
end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
