/-
  FermatManifestationFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль ветви Ферма
  программы вечного двигателя: «опровергнуть Ферма-близнецов = предъявить
  вечный двигатель», проведённое манифестационной архитектурой Римана —
  СТРУКТУРНОЕ ЗЕРКАЛО Софи-Жермен-фронта и Мерсенн-фронта (гл. 43), с
  данными Ферма (минус-сторона центра `c_k = (F_k + 1)/6`, квадратичная цепь).

  Отклонение здесь — НЕ объект-данные (как off-critical нуль), а Π-свидетель:
  `FermatTwinAbsenceAbove P` — отсутствие Ферма-близнецов выше порога P
  (зеркало `SGAbsenceAbove` и `MersenneTwinAbsenceAbove`). Закон манифестации
  ГЕЙЧЕН этим свидетелем: негейченная форма (∀ P, Manifests P) взорвала бы
  принятую границу — как манифестационные кандидаты ЯМ и НС (раскрыто ниже).

  Архитектура (зеркало SophieGermainManifestationFront, M1–M9):
    * плумбинг отрицаний: свидетель отсутствия ⟺ ¬неограниченность;
    * КВАДРАТИЧНАЯ цепь центров (минус-сторона: `c' + 4c = 6c² + 1`,
      раскрытие ветви `fermatCenter_chain`) строго растёт
      (`fermatCenter_strictMono_from_one`) — И КЛЮЧЕВОЕ РАСКРЫТИЕ: цепь НЕ
      ПИЛИТСЯ (`isEmpty_properCenterPeel_three_one`) — квадратичная цепь не
      несёт тождества с постоянным простым делителем (в отличие от линейной
      5c + 1 у 5-адики); уже шаг 3 → 1 пуст (стороны 17 и 19 просты, цели
      лишь 5 и 7). Потому КОВАНОГО свидетеля в этой ветви НЕ СУЩЕСТВУЕТ — в
      отличие от ЯМ (cookedLadder) и НС (cookedProfileCascade), в точности как
      у Римана, Мерсенна и Софи Жермен;
    * закон манифестации `FermatManifestationLaw` (якорь M0 := P, потребляется
      через le_refl); Impossible-сторона — зелёная теорема
      `no_deviationFlowSupply_at_resolved_scale` (переиспользована), НЕ декрет;
    * ESSENCE M3: нет двигателей + принятая граница + закон ⟹ Ферма-близнецы
      неограничены (все три гипотезы подлинно потребляются);
    * ЧИТАЕМАЯ ФОРМА M3⁺ `fermatRefutation_carries_engine`: свидетель
      отсутствия + закон + сведённые книги ⟹ двигатель-СВИДЕТЕЛЬ как объект.

  ТРИЛЕММА ЧЕТВЁРТОГО ПОЛЯ ПРОЙДЕНА (V1: не опровержим — любой свидетель
  отсутствия ≥ 65537 (M8) зелёно, а ПРЕДЪЯВИТЬ свидетеля = решить открытую
  задачу о хвосте Ферма-близнецов; V2: не доказуем и не вакуумен зелёно — при
  границе закон ⟺ открытая неограниченность (M7), вакуумность гейта ⟺ та же
  открытая задача; V3: границу не взрывает — коваться нечему, isEmpty зелёно).
  НО ПОЛЕ НЕ ДОБАВЛЕНО — НАМЕРЕННО: ⚠️ ЗНАК ЭВРИСТИКИ ИНВЕРТИРОВАН ЖЁСТЧЕ, ЧЕМ
  У МЕРСЕННА. Простыми известны лишь F₀–F₄, а F₅–F₃₂ ДОКАЗУЕМО составны, так что
  вход `FermatTwinCentersUnbounded` скорее всего ЛОЖЕН — тут ожидаемая
  истинность границы отрицательна ещё резче Мерсенна (там сумма по twin-парам
  сходится, но бесконечности прямо не запрещает; здесь известный хвост составных
  чисел Ферма огромен). Риман был ставкой на ожидаемо-истинное; Ферма был бы
  границей с самой отрицательной ожидаемой истинностью в программе. И ВСЁ ЖЕ
  ПОЛЯ НЕТ — вердикт §16 и §17: манифестационные поля за пределами Римана
  программа не умножает; закон живёт здесь ОПРЕДЕЛЕНИЕМ (как
  RiemannManifestationLaw до §10), непротиворечивость карантина на него НЕ
  ставится. См. §16-комментарий карантина и prose/43.

  РАСКРЫТИЕ ЗАИМСТВОВАНИЯ L1: объект поставки `DeviationFlowSupply` и его
  свидетель содержательности (римановская L1) ВЗЯТЫ у римановского фронта и
  здесь не передоказываются; Impossible-сторона на разрешённых масштабах —
  зелёная L2, никогда не декрет.

  ЗАПРЕТ ВАКУУМНОСТИ №3: никаких свободных Prop-полей, свободных гейтов и
  переименованных выводов — каждая гипотеза именована арифметически.
  Модуль карантин НЕ импортирует; axiom и sorry нет.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.FermatBranch

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Свидетель отклонения: отсутствие Ферма-близнецов выше порога
#############################################################################-/

/-- **Отсутствие Ферма-близнецов выше `P`** (Π-свидетель, зеркало
    `SGAbsenceAbove` и `MersenneTwinAbsenceAbove`): каждое число Ферма `F_k`
    (при `k ≥ 1`), у которого `F_k` и `F_k + 2` оба просты, сидит по младшему
    члену `F_k` не выше `P`. -/
def FermatTwinAbsenceAbove (P : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → (Nat.fermatNumber k).Prime →
    (Nat.fermatNumber k + 2).Prime → Nat.fermatNumber k ≤ P

/-- Плумбинг: из ограниченности извлекается свидетель отсутствия. -/
theorem exists_fermatAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) :
    ∃ P : ℕ, FermatTwinAbsenceAbove P := by
  unfold EuclidsPath.FermatBranch.FermatTwinCentersUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun k h1 h2 h3 => by
    by_contra hgt
    exact hP k h1 (by omega) h2 h3⟩

/-- Плумбинг: неограниченность ⟺ свидетелей отсутствия нет. -/
theorem fermatTwinCentersUnbounded_iff_no_absence :
    EuclidsPath.FermatBranch.FermatTwinCentersUnbounded ↔
      ∀ P : ℕ, ¬ FermatTwinAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨k, hk1, hlt, h1, h2⟩ := hU P
    have := hAbs k hk1 h1 h2
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_fermatAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **M8 (локализация домена свидетеля, зеркало SG8):** всякая граница
    отсутствия ≥ 65537 — пара `(F₄, F₄ + 2) = (65537, 65539)` при `k = 4`
    зелёно существует (`fermat_twin_instances` ветви — самая сильная
    конкретная локализация близнецов в программе). -/
theorem fermatAbsenceBound_ge_65537 {P : ℕ}
    (hAbs : FermatTwinAbsenceAbove P) : 65537 ≤ P := by
  have hF4 : Nat.fermatNumber 4 = 65537 := by norm_num [Nat.fermatNumber]
  have h := hAbs 4 (by norm_num)
    (by rw [hF4]; norm_num) (by rw [hF4]; norm_num)
  rw [hF4] at h
  omega

/-#############################################################################
  §2. Квадратичная цепь центров: строго растёт — и НЕ ПИЛИТСЯ (нет ковки)
#############################################################################-/

/-- Ремарка-стыковка с раскрытием ветви: на минус-стороне цепь центров Ферма
    КВАДРАТИЧНА (`fermatCenter_chain`: `c' + 4c = 6c² + 1`) и строго уходит
    вверх на каждом шаге при `k ≥ 1` (`fermatCenter_strictMono_from_one`) — как
    удвоение `m → 2m` у Софи Жермен и база-4 `m → 4m+1` у Мерсенна. Рост есть,
    но именно он делает раскрытие ниже содержательным: расти цепь умеет,
    ПИЛИТЬ — нет. -/
theorem fermatCenter_lt_succ {k : ℕ} (hk : 1 ≤ k) :
    EuclidsPath.FermatBranch.fermatCenter k <
      EuclidsPath.FermatBranch.fermatCenter (k + 1) :=
  EuclidsPath.FermatBranch.fermatCenter_strictMono_from_one hk

/-- **КЛЮЧЕВОЕ РАСКРЫТИЕ (контраст с 5-адикой, зеркало
    `isEmpty_properCenterPeel_two_one` и `isEmpty_properCenterPeel_five_one`):
    квадратичная цепь центров Ферма НЕ пилится.**
    У 5-адической цепи `c → 5c+1` есть тождество `6(5x+1)−1 = 5(6x+1)` с
    ПРОСТЫМ постоянным делителем 5 — потому она строит потоки при A ≤ 4.
    У квадратичной цепи Ферма `c' + 4c = 6c² + 1` такого тождества с постоянным
    простым делителем НЕТ (`fermatCenter_chain` раскрывает её без деления):
    уже шаг 3 → 1 не несёт собственного пила НИ ПРИ КАКОМ масштабе — стороны
    17 и 19 просты, стороны цели — лишь 5 и 7. Следствие: Ферма-цепь НЕ строит
    безусловной поставки потоков — КОВАНОГО свидетеля (паттерн V3 ЯМ и НС)
    в этой ветви не существует. -/
theorem isEmpty_properCenterPeel_three_one (A : ℕ) :
    IsEmpty (ProperCenterPeel A 3 1) := by
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
    утверждение о самих Ферма-близнецах. -/
def FermatAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **ЗАКОН МАНИФЕСТАЦИИ ФЕРМА** — гейчен свидетелем отсутствия.
    Негейченная форма `∀ P, FermatAbsenceManifests P` при P := 0 вместе с
    принятой границей дала бы поставку на разрешённом масштабе — противоречие
    с зелёной L2 (точный механизм провала манифестационных кандидатов ЯМ и НС).
    Гейт по зелёно-непредъявимому свидетелю — то, что отличает эту форму.
    ПОЛЕ НЕ ДЕКРЕТИРОВАНО — при том, что знак эвристики ИНВЕРТИРОВАН ЖЁСТЧЕ
    Мерсенна (F₅–F₃₂ составны; вердикт §16 и §17, см. шапку). -/
def FermatManifestationLaw : Prop :=
  ∀ P : ℕ, FermatTwinAbsenceAbove P → FermatAbsenceManifests P

/-#############################################################################
  §4. ESSENCE и читаемая форма: опровержение предъявляет двигатель
#############################################################################-/

/-- **M3⁺ — ЧИТАЕМАЯ ФОРМА «опровержение = двигатель»:** свидетель отсутствия
    + закон + сведённые книги на масштабе не ниже P МАНИФЕСТИРУЮТ вечный
    двигатель — как ОБЪЕКТ, до убийства lexRank'ом. -/
theorem fermatRefutation_carries_engine
    (hLaw : FermatManifestationLaw)
    {P : ℕ} (hAbs : FermatTwinAbsenceAbove P)
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

/-- **M3 — ESSENCE (зеркало SG3 и римановской L3):** двигателей нет +
    принятая граница + закон манифестации ⟹ Ферма-близнецы неограничены.
    Все три гипотезы потребляются ПО-НАСТОЯЩЕМУ: из конечности извлекается
    свидетель отсутствия P; граница даёт разрешение ровно на масштабе
    M0 := P; закон поставляет семью 𝓕 (не ex falso); из коллизии строится
    двигатель-СВИДЕТЕЛЬ; убивает его именно hNoEngine. -/
theorem fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : FermatManifestationLaw) :
    EuclidsPath.FermatBranch.FermatTwinCentersUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_fermatAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    fermatRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- Зелёное доведение до цели программы: та же тройка ⟹ близнецы бесконечны
    (через ЕДИНСТВЕННОЕ честное направление ветви Ферма ⟹ близнецы,
    `twinLowersInfinite_of_fermatTwins`). -/
theorem twinLowersInfinite_of_noEngine_boundary_and_fermatManifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : FermatManifestationLaw) :
    EuclidsPath.TwinLowers.Infinite :=
  EuclidsPath.FermatBranch.twinLowersInfinite_of_fermatTwins
    (fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-#############################################################################
  §5. Аудиты честности (M5–M9)
#############################################################################-/

/-- **M5 (вакуумная обратная сторона, зеркало SG5):** неограниченность ⟹
    закон вакуумно — гейт отсутствия пуст. Несущая сторона — M3, и ей
    нужна граница. -/
theorem fermatManifestationLaw_of_unbounded
    (H : EuclidsPath.FermatBranch.FermatTwinCentersUnbounded) :
    FermatManifestationLaw := fun P hAbs =>
  ((fermatTwinCentersUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **M6 (точная зелёная характеризация, зеркало SG6):** закон ⟺ «отсутствие
    выше P заморозило бы всякий разрешающий леджер на масштабах ≥ P».
    Обратное направление — ex falso от ¬resolves (раскрыто). Гейт-гипотеза
    потенциально пуста — потому характеризация НЕ коллапсирует в глобальную
    заморозку (асимметрия с негейченными формами ЯМ и НС). -/
theorem fermatManifestationLaw_iff_no_resolution_above_absence :
    FermatManifestationLaw ↔
      ∀ P : ℕ, FermatTwinAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **M7 — ГЛАВНЫЙ АУДИТ ЦЕНЫ (зеркало SG7 и M7 Мерсенна):** при границе закон
    ⟺ неограниченность Ферма-близнецов — четвёртое поле было бы ровно
    Ферма-гипотезной силы. БЕЗ границы «закон ⟹ неограниченность» зелёно не
    собирается (M3 требует границу). ⚠️ ИМЕННО ЗДЕСЬ видно, почему поле
    отложено: эвристика направлена ПРОТИВ правой части этого ⟺ ЖЁСТЧЕ, чем у
    Мерсенна — просты лишь F₀–F₄, а F₅–F₃₂ доказуемо составны. -/
theorem fermatManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    FermatManifestationLaw ↔
      EuclidsPath.FermatBranch.FermatTwinCentersUnbounded :=
  ⟨fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   fermatManifestationLaw_of_unbounded⟩

/-- Тип-свидетель для bundling-аудита (subtype — front_pair работает с Type). -/
abbrev FermatAbsenceWitness : Type := {P : ℕ // FermatTwinAbsenceAbove P}

theorem nonempty_fermatAbsenceWitness_iff :
    Nonempty FermatAbsenceWitness ↔
      ¬ EuclidsPath.FermatBranch.FermatTwinCentersUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (fermatTwinCentersUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_fermatAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- Закон в Bridge-форме над типом свидетелей. -/
theorem fermatManifestationLaw_iff_bridge :
    FermatManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : FermatAbsenceWitness => FermatAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **M9 (bundling-аудит, инстанциация осуждающей машины):** связка
    Bridge∧Impossible ⟺ «свидетелей отсутствия нет» — декретироваться могла
    бы ТОЛЬКО Bridge-сторона; Impossible-сторона на разрешённых масштабах —
    зелёная L2, никогда не декрет. -/
theorem fermatManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : FermatAbsenceWitness => FermatAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : FermatAbsenceWitness => FermatAbsenceManifests W.1)) ↔
      ¬ Nonempty FermatAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

-- Машинная видимость чистоты в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound] — БЕЗ step00FirstCause):
#print axioms fermatTwinsUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms fermatRefutation_carries_engine
#print axioms fermatManifestationLaw_iff_unbounded_of_boundary
#print axioms fermatAbsenceBound_ge_65537
#print axioms isEmpty_properCenterPeel_three_one

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
