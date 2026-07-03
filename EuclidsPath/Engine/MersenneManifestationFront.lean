/-
  MersenneManifestationFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль Мерсенн-ветви
  программы вечного двигателя: «опровергнуть Мерсенн-близнецов = предъявить
  вечный двигатель», проведённое манифестационной архитектурой Римана.

  Отклонение здесь — НЕ объект-данные (как off-critical нуль), а Π-свидетель:
  `MersenneTwinAbsenceAbove P` — отсутствие Мерсенн-близнецов выше порога P
  (зеркало TwinBoundAbove). Закон манифестации ГЕЙЧЕН этим свидетелем:
  негейченная форма (∀ P, Manifests P) взорвала бы принятую границу — как
  манифестационные кандидаты ЯМ/НС (раскрыто ниже).

  Архитектура (зеркало RiemannManifestationFront):
    * плумбинг отрицаний: свидетель отсутствия ⟺ ¬неограниченность;
    * арифметика базы-4 цепи центров (m→4m+1, репьюниты) — строго монотонна,
      инъективна; И КЛЮЧЕВОЕ РАСКРЫТИЕ: цепь НЕ ПИЛИТСЯ
      (`isEmpty_properCenterPeel_five_one`) — коэффициент 4 не прост и
      ≢ ±1 (mod 6), уже первый шаг 5→1 пуст (стороны 29/31 просты, цели 5/7).
      Потому КОВАНОГО свидетеля в этой ветви НЕ СУЩЕСТВУЕТ — в отличие от
      ЯМ (cookedLadder) и НС (cookedProfileCascade), в точности как у Римана;
    * закон манифестации `MersenneManifestationLaw` (якорь M0 := P,
      потребляется через le_refl); Impossible-сторона — зелёная теорема
      `no_deviationFlowSupply_at_resolved_scale` (переиспользована), НЕ декрет;
    * ESSENCE M3: нет двигателей + принятая граница + закон ⟹
      Мерсенн-близнецы неограничены (все три гипотезы подлинно потребляются);
    * ЧИТАЕМАЯ ФОРМА M3⁺ `mersenneRefutation_carries_engine`: свидетель
      отсутствия + закон + сведённые книги ⟹ двигатель-СВИДЕТЕЛЬ как объект.

  ТРИЛЕММА ЧЕТВЁРТОГО ПОЛЯ ПРОЙДЕНА (V1: не опровержим — любой свидетель
  отсутствия ≥ 29 (M8) и предъявление ≥ решения открытой задачи о хвосте;
  V2: не доказуем/не вакуумен — вакуумность ⟺ открытая неограниченность;
  V3: границу не взрывает — коваться нечему). НО ПОЛЕ НЕ ДОБАВЛЕНО — НАМЕРЕННО:
  ⚠️ ЗНАК ЭВРИСТИКИ ИНВЕРТИРОВАН. При границе закон ⟺
  MersenneTwinCentersUnbounded (M7), а эвристика направлена ПРОТИВ
  неограниченности (Σ по twin-парам Мерсенна сходится; известны лишь p = 3, 5;
  при p ≡ 3 (mod 4) всегда 5 ∣ 2^p−3). Риман был ставкой на ожидаемо-истинное;
  Мерсенн был бы первой границей, чья ожидаемая истинность отрицательна.
  Решение зафиксировано: закон живёт здесь определением (как
  RiemannManifestationLaw до §10), непротиворечивость карантина на него
  НЕ ставится. См. §16-комментарий карантина и prose/43.

  ЗАПРЕТ ВАКУУМНОСТИ №3: никаких свободных Prop-полей, свободных гейтов и
  переименованных выводов — каждая гипотеза именована арифметически.
  Модуль карантин НЕ импортирует; axiom/sorry нет.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.MersennePeelPressure
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Свидетель отклонения: отсутствие Мерсенн-близнецов выше порога
#############################################################################-/

/-- **Отсутствие Мерсенн-близнецов выше `P`** (Π-свидетель, зеркало
    `TwinBoundAbove`): каждый Мерсенн-близнец сидит по нижней стороне
    `2^p − 3` не выше `P`. ⚠️ НЕ путать с
    `Mersenne.PeelPaymentPressure.MersenneTwinAbsentAtOrAbove` — та форма
    по ИНДЕКСУ k цепи и параметрична по PrimeLike. -/
def MersenneTwinAbsenceAbove (P : ℕ) : Prop :=
  ∀ p : ℕ, (2 ^ p - 3).Prime → (mersenne p).Prime → 2 ^ p - 3 ≤ P

/-- Плумбинг: из ограниченности извлекается свидетель отсутствия. -/
theorem exists_mersenneAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded) :
    ∃ P : ℕ, MersenneTwinAbsenceAbove P := by
  unfold EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun p h1 h2 => by
    by_contra hgt
    exact hP p (by omega) h1 h2⟩

/-- Плумбинг: неограниченность ⟺ свидетелей отсутствия нет. -/
theorem mersenneTwinCentersUnbounded_iff_no_absence :
    EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded ↔
      ∀ P : ℕ, ¬ MersenneTwinAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨p, hlt, h1, h2⟩ := hU P
    have := hAbs p h1 h2
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_mersenneAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **M8 (локализация домена свидетеля, зеркало L8):** всякая граница
    отсутствия ≥ 29 — пара (29, 31) при p = 5 зелёно существует. -/
theorem mersenneAbsenceBound_ge_29 {P : ℕ}
    (hAbs : MersenneTwinAbsenceAbove P) : 29 ≤ P := by
  have h := hAbs 5 (by norm_num) (by norm_num [mersenne])
  norm_num at h
  exact h

/-#############################################################################
  §2. База-4 цепь центров: строго монотонна — и НЕ ПИЛИТСЯ (нет ковки)
#############################################################################-/

/-- Цепь центров строго растёт на каждом шаге (m → 4m+1). -/
theorem mersenneCenterChain_lt_succ (k : ℕ) :
    EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter k <
      EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter (k + 1) := by
  have h := EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter_base4PeelStep k
  unfold EuclidsPath.Mersenne.PeelPaymentPressure.Base4PeelStep at h
  omega

theorem mersenneCenterChain_strictMono :
    StrictMono EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter :=
  strictMono_nat_of_lt_succ mersenneCenterChain_lt_succ

theorem mersenneCenterChain_injective :
    Function.Injective EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter :=
  mersenneCenterChain_strictMono.injective

/-- Стыковка цепь ↔ ветвь: repunit-центр слоя = центр MersenneBranch при
    p = 2k+1. -/
theorem mersenneCenterChain_eq_branchCenter (k : ℕ) :
    EuclidsPath.Mersenne.PeelPaymentPressure.mersenneCenter k =
      EuclidsPath.MersenneBranch.mersenneCenter (2 * k + 1) := by
  have h1 := EuclidsPath.Mersenne.peelCenter_eq_conflictCenter k
  have h2 := EuclidsPath.Mersenne.sixCenter_add_one_eq_mersenne k
  have h3 := EuclidsPath.MersenneBranch.mersenne_eq_sixCenter_add_one
    (p := 2 * k + 1) ⟨k, by ring⟩
  unfold mersenne at h2 h3
  omega

/-- **КЛЮЧЕВОЕ РАСКРЫТИЕ (контраст с 5-адикой): база-4 цепь НЕ пилится.**
    У 5-адической цепи `c → 5c+1` есть тождество `6(5x+1)−1 = 5(6x+1)` с
    ПРОСТЫМ постоянным делителем 5 — потому она строит потоки при A ≤ 4.
    У цепи `c → 4c+1` такого тождества нет (коэффициент 4 не прост и
    ≢ ±1 mod 6), и уже ПЕРВЫЙ шаг 5 → 1 не несёт собственного пила НИ ПРИ
    КАКОМ масштабе: стороны 29 и 31 просты, стороны цели — лишь 5 и 7.
    Следствие: Мерсенн-цепь НЕ строит безусловной поставки потоков —
    КОВАНОГО свидетеля (паттерн V3 ЯМ/НС) в этой ветви не существует. -/
theorem isEmpty_properCenterPeel_five_one (A : ℕ) :
    IsEmpty (ProperCenterPeel A 5 1) := by
  constructor
  rintro ⟨inS, outS, q, _hq, _hA, hfac, _hsm, _hpos⟩
  cases inS <;> cases outS <;> simp only [sideValue] at hfac <;> omega

/-#############################################################################
  §3. Закон манифестации (гейченный свидетелем; поле НЕ декретировано)
#############################################################################-/

/-- Отсутствие выше `P` манифестирует арифметически: на каждом
    леджер-масштабе не ниже `P`, всюду где проекция сводит книги, отсутствие
    проявляется неоплатимой бесконечной поставкой потоков. Якорь `P ≤ M0`
    потребляется ниже только через `le_refl` (паттерн Римана). Причинная
    форма: «опровержение обязано проявиться там, где книги сведены» — НЕ
    утверждение о самих Мерсенн-близнецах. -/
def MersenneAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **ЗАКОН МАНИФЕСТАЦИИ МЕРСЕННА** — гейчен свидетелем отсутствия.
    Негейченная форма `∀ P, MersenneAbsenceManifests P` при P := 0 вместе с
    принятой границей дала бы поставку на разрешённом масштабе — противоречие
    с зелёной L2 (точный механизм провала манифестационных кандидатов ЯМ/НС).
    Гейт по зелёно-непредъявимому свидетелю — то, что отличает эту форму.
    ПОЛЕ НЕ ДЕКРЕТИРОВАНО (знак эвристики — см. шапку). -/
def MersenneManifestationLaw : Prop :=
  ∀ P : ℕ, MersenneTwinAbsenceAbove P → MersenneAbsenceManifests P

/-#############################################################################
  §4. ESSENCE и читаемая форма: опровержение предъявляет двигатель
#############################################################################-/

/-- **M3⁺ — ЧИТАЕМАЯ ФОРМА «опровержение = двигатель»:** свидетель отсутствия
    + закон + сведённые книги на масштабе не ниже P МАНИФЕСТИРУЮТ вечный
    двигатель — как ОБЪЕКТ, до убийства lexRank'ом. -/
theorem mersenneRefutation_carries_engine
    (hLaw : MersenneManifestationLaw)
    {P : ℕ} (hAbs : MersenneTwinAbsenceAbove P)
    {A M0 : ℕ} (hM : P ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw P hAbs A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- **M3 — ESSENCE (зеркало twins_infinite_of_noEngine_and_boundary и
    римановской L3):** двигателей нет + принятая граница + закон манифестации
    ⟹ Мерсенн-близнецы неограничены. Все три гипотезы потребляются
    ПО-НАСТОЯЩЕМУ: из конечности извлекается свидетель отсутствия P; граница
    даёт разрешение ровно на масштабе M0 := P; закон поставляет семью 𝓕
    (не ex falso); из коллизии строится двигатель-СВИДЕТЕЛЬ; убивает его
    именно hNoEngine. -/
theorem mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : MersenneManifestationLaw) :
    EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_mersenneAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    mersenneRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- Зелёное доведение до цели программы: та же тройка ⟹ близнецы бесконечны
    (через честный мост Мерсенн ⟹ близнецы). -/
theorem twinLowersInfinite_of_noEngine_boundary_and_mersenneManifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : MersenneManifestationLaw) :
    EuclidsPath.TwinLowers.Infinite :=
  EuclidsPath.MersenneBranch.twinLowersInfinite_of_mersenneTwins
    (mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-#############################################################################
  §5. Аудиты честности (M5–M9)
#############################################################################-/

/-- **M5 (вакуумная обратная сторона, зеркало L5):** неограниченность ⟹ закон
    вакуумно — гейт отсутствия пуст. Несущая сторона — M3, и ей нужна граница. -/
theorem mersenneManifestationLaw_of_unbounded
    (H : EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded) :
    MersenneManifestationLaw := fun P hAbs =>
  ((mersenneTwinCentersUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **M6 (точная зелёная характеризация, зеркало L6):** закон ⟺ «отсутствие
    выше P заморозило бы всякий разрешающий леджер на масштабах ≥ P».
    Обратное направление — ex falso от ¬resolves (раскрыто). Гейт-гипотеза
    потенциально пуста — потому характеризация НЕ коллапсирует в глобальную
    заморозку (асимметрия с негейченными формами ЯМ/НС). -/
theorem mersenneManifestationLaw_iff_no_resolution_above_absence :
    MersenneManifestationLaw ↔
      ∀ P : ℕ, MersenneTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **M7 — ГЛАВНЫЙ АУДИТ ЦЕНЫ (зеркало L7):** при границе закон ⟺
    неограниченность Мерсенн-близнецов — четвёртое поле было бы ровно
    Мерсенн-близнецовой силы. БЕЗ границы «закон ⟹ неограниченность» зелёно
    не собирается (M3 требует границу). ⚠️ ИМЕННО ЗДЕСЬ видно, почему поле
    отложено: эвристика направлена ПРОТИВ правой части этого ⟺. -/
theorem mersenneManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    MersenneManifestationLaw ↔
      EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded :=
  ⟨mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   mersenneManifestationLaw_of_unbounded⟩

/-- Тип-свидетель для bundling-аудита (subtype — front_pair работает с Type). -/
abbrev MersenneAbsenceWitness : Type := {P : ℕ // MersenneTwinAbsenceAbove P}

theorem nonempty_mersenneAbsenceWitness_iff :
    Nonempty MersenneAbsenceWitness ↔
      ¬ EuclidsPath.MersenneBranch.MersenneTwinCentersUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (mersenneTwinCentersUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_mersenneAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- Закон в Bridge-форме над типом свидетелей. -/
theorem mersenneManifestationLaw_iff_bridge :
    MersenneManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : MersenneAbsenceWitness => MersenneAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **M9 (bundling-аудит, инстанциация осуждающей машины):** связка
    Bridge∧Impossible ⟺ «свидетелей отсутствия нет» — декретироваться могла
    бы ТОЛЬКО Bridge-сторона; Impossible-сторона на разрешённых масштабах —
    зелёная L2, никогда не декрет. -/
theorem mersenneManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : MersenneAbsenceWitness => MersenneAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : MersenneAbsenceWitness => MersenneAbsenceManifests W.1)) ↔
      ¬ Nonempty MersenneAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Машинная видимость чистоты в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound] — БЕЗ step00FirstCause):
#print axioms mersenneTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms mersenneRefutation_carries_engine
#print axioms mersenneManifestationLaw_iff_unbounded_of_boundary
#print axioms isEmpty_properCenterPeel_five_one
#print axioms mersenneAbsenceBound_ge_29

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
