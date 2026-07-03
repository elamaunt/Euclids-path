/-
  SophieGermainManifestationFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль ветви
  Софи Жермен программы вечного двигателя: «опровергнуть Софи Жермен =
  предъявить вечный двигатель», проведённое манифестационной архитектурой
  Римана — зеркало Мерсенн-фронта (гл. 43) ПЛЮС уникальная рестрикт-секция
  3 (mod 4), кормящая анти-Мерсенн-королларий.

  Отклонение здесь — НЕ объект-данные (как off-critical нуль), а Π-свидетель:
  `SGAbsenceAbove P` — отсутствие пар Софи Жермен выше порога P (зеркало
  `MersenneTwinAbsenceAbove`). Закон манифестации ГЕЙЧЕН этим свидетелем:
  негейченная форма (∀ P, Manifests P) взорвала бы принятую границу — как
  манифестационные кандидаты ЯМ/НС (раскрыто ниже).

  Архитектура (зеркало MersenneManifestationFront, M1–M9 ↦ SG1–SG9):
    * плумбинг отрицаний: свидетель отсутствия ⟺ ¬неограниченность;
    * цепь УДВОЕНИЯ центров (минус-сторона: 2(6m−1)+1 = 6(2m)−1, раскрытие
      ветви `sg_center_doubling`) строго растёт (`sg_doubling_lt`) — И
      КЛЮЧЕВОЕ РАСКРЫТИЕ: цепь НЕ ПИЛИТСЯ (`isEmpty_properCenterPeel_two_one`)
      — коэффициент 2 хоть и прост, но 2 ≢ ±1 (mod 6) и не делит нечётные
      стороны 6n∓1; уже первый шаг 2 → 1 пуст (стороны 11/13 просты, цели
      5/7). Потому КОВАНОГО свидетеля в этой ветви НЕ СУЩЕСТВУЕТ — в отличие
      от ЯМ (cookedLadder) и НС (cookedProfileCascade), в точности как у
      Римана и Мерсенна;
    * закон манифестации `SGManifestationLaw` (якорь M0 := P, потребляется
      через le_refl); Impossible-сторона — зелёная теорема
      `no_deviationFlowSupply_at_resolved_scale` (переиспользована), НЕ декрет;
    * ESSENCE SG3: нет двигателей + принятая граница + закон ⟹ пары Софи
      Жермен неограничены (все три гипотезы подлинно потребляются);
    * ЧИТАЕМАЯ ФОРМА SG3⁺ `sgRefutation_carries_engine`: свидетель отсутствия
      + закон + сведённые книги ⟹ двигатель-СВИДЕТЕЛЬ как объект.

  ТРИЛЕММА ЧЕТВЁРТОГО ПОЛЯ ПРОЙДЕНА (V1: не опровержим — любой свидетель
  отсутствия ≥ 89 (SG8) зелёно, а ПРЕДЪЯВИТЬ свидетеля = решить открытую
  задачу о хвосте Софи Жермен; V2: не доказуем/не вакуумен зелёно — при
  границе закон ⟺ открытая неограниченность (SG7), вакуумность гейта ⟺ та же
  открытая задача; V3: границу не взрывает — коваться нечему, isEmpty зелёно).
  НО ПОЛЕ НЕ ДОБАВЛЕНО — НАМЕРЕННО: ⚠️ ЗНАК ЭВРИСТИКИ ПОЛОЖИТЕЛЕН — в отличие
  от Мерсенна (знак инвертирован, гл. 43), пар Софи Жермен ожидаемо бесконечно
  много (Харди–Литтлвуд: ~ 2C₂ · x/ln²x), т.е. это была бы ставка на
  ожидаемо-истинное, как Риман. И ВСЁ ЖЕ ПОЛЯ НЕТ — вердикт §17:
  манифестационные поля за пределами Римана программа не умножает; закон
  живёт здесь ОПРЕДЕЛЕНИЕМ, непротиворечивость карантина на него НЕ ставится.

  ⚠️ ЖЕМЧУЖИНА-ПЕРЕКРЁСТОК (ветвь, `sophieGermain_divides_mersenne`,
  Эйлер–Лагранж, зелёно доказана): SG-простое p ≡ 3 (mod 4), p > 3 ⟹
  (2p+1) ∣ M_p и M_p СОСТАВНОЕ — формальный фрагмент той самой §16-эвристики,
  которую карантин выставлял против границы Мерсенна. Рестрикт-секция §6
  превращает это в «ДВЕ СТАВКИ, ГЛЯДЯЩИЕ ДРУГ НА ДРУГА»: вывод ЭТОГО фронта
  (essence рестрикт-закона) кормит СОСТАВНУЮ сторону величины M_p — той
  самой, на ПРОСТУЮ сторону которой Мерсенн-фронт (гл. 43) ставить отказался.

  РАСКРЫТИЕ ЗАИМСТВОВАНИЯ L1: объект поставки `DeviationFlowSupply` и его
  свидетель содержательности (римановская L1,
  `deviationFlowSupply_of_twinBound` — twin-bound строит тот же объект
  зелёно на каждом масштабе) ВЗЯТЫ у римановского фронта и здесь не
  передоказываются; Impossible-сторона на разрешённых масштабах — зелёная
  L2, никогда не декрет.

  ЗАПРЕТ ВАКУУМНОСТИ №3: никаких свободных Prop-полей, свободных гейтов и
  переименованных выводов — каждая гипотеза именована арифметически.
  Модуль карантин НЕ импортирует; axiom/sorry нет.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront
import EuclidsPath.Engine.SophieGermainBranch

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. Свидетель отклонения: отсутствие пар Софи Жермен выше порога
#############################################################################-/

/-- **Отсутствие пар Софи Жермен выше `P`** (Π-свидетель, зеркало
    `MersenneTwinAbsenceAbove`): каждое SG-простое (`p` и `2p+1` просты)
    сидит не выше `P`. -/
def SGAbsenceAbove (P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (2 * p + 1).Prime → p ≤ P

/-- Плумбинг: из ограниченности извлекается свидетель отсутствия. -/
theorem exists_sgAbsence_of_not_unbounded
    (h : ¬ EuclidsPath.SophieGermainBranch.SophieGermainUnbounded) :
    ∃ P : ℕ, SGAbsenceAbove P := by
  unfold EuclidsPath.SophieGermainBranch.SophieGermainUnbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun p h1 h2 => by
    by_contra hgt
    exact hP p (by omega) ⟨h1, h2⟩⟩

/-- Плумбинг: неограниченность ⟺ свидетелей отсутствия нет. -/
theorem sophieGermainUnbounded_iff_no_absence :
    EuclidsPath.SophieGermainBranch.SophieGermainUnbounded ↔
      ∀ P : ℕ, ¬ SGAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨p, hlt, hSG⟩ := hU P
    have := hAbs p hSG.1 hSG.2
    omega
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_sgAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- **SG8 (локализация домена свидетеля, зеркало M8):** всякая граница
    отсутствия ≥ 89 — пара Софи Жермен (89, 179) зелёно существует
    (ср. `sg_instances` ветви). -/
theorem sgAbsenceBound_ge_89 {P : ℕ}
    (hAbs : SGAbsenceAbove P) : 89 ≤ P := by
  have h := hAbs 89 (by norm_num) (by norm_num : (179 : ℕ).Prime)
  omega

/-#############################################################################
  §2. Цепь удвоения центров: строго растёт — и НЕ ПИЛИТСЯ (нет ковки)
#############################################################################-/

/-- Ремарка-стыковка с раскрытием ветви: на минус-стороне SG-отображение
    `p → 2p+1` в координатах центров — ровно УДВОЕНИЕ `m → 2m`
    (`sg_center_doubling`: `2(6m−1)+1 = 6(2m)−1`), и цепь центров строго
    уходит вверх на каждом шаге — как `4m+1` у Мерсенна и `5m+1` у
    пятиадики. Монотонность тривиальна, но именно она делает раскрытие
    ниже содержательным: расти цепь умеет, ПИЛИТЬ — нет. -/
theorem sg_doubling_lt (c : ℕ) (hc : 1 ≤ c) : c < 2 * c := by omega

/-- **КЛЮЧЕВОЕ РАСКРЫТИЕ (контраст с 5-адикой, зеркало
    `isEmpty_properCenterPeel_five_one`): цепь удвоения НЕ пилится.**
    У 5-адической цепи `c → 5c+1` есть тождество `6(5x+1)−1 = 5(6x+1)` с
    ПРОСТЫМ постоянным делителем 5 — потому она строит потоки при A ≤ 4.
    У цепи удвоения `c → 2c` такого тождества нет: коэффициент 2 хоть и
    прост, но 2 ≢ ±1 (mod 6) и не делит нечётные стороны 6n∓1; уже ПЕРВЫЙ
    шаг 2 → 1 не несёт собственного пила НИ ПРИ КАКОМ масштабе: стороны
    11 и 13 просты, стороны цели — лишь 5 и 7. Следствие: SG-цепь НЕ строит
    безусловной поставки потоков — КОВАНОГО свидетеля (паттерн V3 ЯМ/НС)
    в этой ветви не существует. -/
theorem isEmpty_properCenterPeel_two_one (A : ℕ) :
    IsEmpty (ProperCenterPeel A 2 1) := by
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
    утверждение о самих парах Софи Жермен. -/
def SGAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **ЗАКОН МАНИФЕСТАЦИИ СОФИ ЖЕРМЕН** — гейчен свидетелем отсутствия.
    Негейченная форма `∀ P, SGAbsenceManifests P` при P := 0 вместе с
    принятой границей дала бы поставку на разрешённом масштабе — противоречие
    с зелёной L2 (точный механизм провала манифестационных кандидатов ЯМ/НС).
    Гейт по зелёно-непредъявимому свидетелю — то, что отличает эту форму.
    ПОЛЕ НЕ ДЕКРЕТИРОВАНО — несмотря на ПОЛОЖИТЕЛЬНЫЙ знак эвристики
    (вердикт §17, см. шапку). -/
def SGManifestationLaw : Prop :=
  ∀ P : ℕ, SGAbsenceAbove P → SGAbsenceManifests P

/-#############################################################################
  §4. ESSENCE и читаемая форма: опровержение предъявляет двигатель
#############################################################################-/

/-- **SG3⁺ — ЧИТАЕМАЯ ФОРМА «опровержение = двигатель»:** свидетель отсутствия
    + закон + сведённые книги на масштабе не ниже P МАНИФЕСТИРУЮТ вечный
    двигатель — как ОБЪЕКТ, до убийства lexRank'ом. -/
theorem sgRefutation_carries_engine
    (hLaw : SGManifestationLaw)
    {P : ℕ} (hAbs : SGAbsenceAbove P)
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

/-- **SG3 — ESSENCE (зеркало M3 и римановской L3):** двигателей нет +
    принятая граница + закон манифестации ⟹ пары Софи Жермен неограничены.
    Все три гипотезы потребляются ПО-НАСТОЯЩЕМУ: из конечности извлекается
    свидетель отсутствия P; граница даёт разрешение ровно на масштабе
    M0 := P; закон поставляет семью 𝓕 (не ex falso); из коллизии строится
    двигатель-СВИДЕТЕЛЬ; убивает его именно hNoEngine. -/
theorem sophieGermainUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SGManifestationLaw) :
    EuclidsPath.SophieGermainBranch.SophieGermainUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_sgAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    sgRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-#############################################################################
  §5. Аудиты честности (SG5–SG9)
#############################################################################-/

/-- **SG5 (вакуумная обратная сторона, зеркало M5):** неограниченность ⟹
    закон вакуумно — гейт отсутствия пуст. Несущая сторона — SG3, и ей
    нужна граница. -/
theorem sgManifestationLaw_of_unbounded
    (H : EuclidsPath.SophieGermainBranch.SophieGermainUnbounded) :
    SGManifestationLaw := fun P hAbs =>
  ((sophieGermainUnbounded_iff_no_absence.mp H) P hAbs).elim

/-- **SG6 (точная зелёная характеризация, зеркало M6):** закон ⟺ «отсутствие
    выше P заморозило бы всякий разрешающий леджер на масштабах ≥ P».
    Обратное направление — ex falso от ¬resolves (раскрыто). Гейт-гипотеза
    потенциально пуста — потому характеризация НЕ коллапсирует в глобальную
    заморозку (асимметрия с негейченными формами ЯМ/НС). -/
theorem sgManifestationLaw_iff_no_resolution_above_absence :
    SGManifestationLaw ↔
      ∀ P : ℕ, SGAbsenceAbove P →
        ∀ (A M0 : ℕ), P ≤ M0 →
          ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
            ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw P hAbs A M0 hle proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw P hAbs A M0 hle proj hres)
  · intro hFreeze P hAbs A M0 hle proj hres
    exact ((hFreeze P hAbs A M0 hle proj) hres).elim

/-- **SG7 — ГЛАВНЫЙ АУДИТ ЦЕНЫ (зеркало M7):** при границе закон ⟺
    неограниченность пар Софи Жермен — четвёртое поле было бы ровно
    SG-гипотезной силы. БЕЗ границы «закон ⟹ неограниченность» зелёно не
    собирается (SG3 требует границу). ⚠️ Здесь и видна цена: в отличие от
    Мерсенна знак эвристики ЗА правую часть этого ⟺ (Харди–Литтлвуд), но
    поле всё равно не декретировано — вердикт §17. -/
theorem sgManifestationLaw_iff_unbounded_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) :
    SGManifestationLaw ↔
      EuclidsPath.SophieGermainBranch.SophieGermainUnbounded :=
  ⟨sophieGermainUnbounded_of_noEngine_and_boundary_and_manifestation
      no_someConcreteEuclideanEngine hBoundary,
   sgManifestationLaw_of_unbounded⟩

/-- Тип-свидетель для bundling-аудита (subtype — front_pair работает с Type). -/
abbrev SGAbsenceWitness : Type := {P : ℕ // SGAbsenceAbove P}

theorem nonempty_sgAbsenceWitness_iff :
    Nonempty SGAbsenceWitness ↔
      ¬ EuclidsPath.SophieGermainBranch.SophieGermainUnbounded := by
  constructor
  · rintro ⟨⟨P, hAbs⟩⟩ hU
    exact (sophieGermainUnbounded_iff_no_absence.mp hU) P hAbs
  · intro h
    obtain ⟨P, hAbs⟩ := exists_sgAbsence_of_not_unbounded h
    exact ⟨⟨P, hAbs⟩⟩

/-- Закон в Bridge-форме над типом свидетелей. -/
theorem sgManifestationLaw_iff_bridge :
    SGManifestationLaw ↔
      EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : SGAbsenceWitness => SGAbsenceManifests W.1) :=
  ⟨fun hLaw W => hLaw W.1 W.2, fun hB P hAbs => hB ⟨P, hAbs⟩⟩

/-- **SG9 (bundling-аудит, инстанциация осуждающей машины):** связка
    Bridge∧Impossible ⟺ «свидетелей отсутствия нет» — декретироваться могла
    бы ТОЛЬКО Bridge-сторона; Impossible-сторона на разрешённых масштабах —
    зелёная L2, никогда не декрет. -/
theorem sgManifestation_bundling_audit :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun W : SGAbsenceWitness => SGAbsenceManifests W.1) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun W : SGAbsenceWitness => SGAbsenceManifests W.1)) ↔
      ¬ Nonempty SGAbsenceWitness :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-#############################################################################
  §6. РЕСТРИКТ-ЗАКОН 3 (mod 4): анти-Мерсенн — «две ставки, глядящие
      друг на друга»

  Тот же фронт, но по подсемейству SG-простых с p ≡ 3 (mod 4) — ровно тому,
  которое жемчужина ветви (`sophieGermain_divides_mersenne`) превращает в
  убийц простоты Мерсенна. Essence рестрикт-закона кормит
  `mersenneComposites_unbounded_of_sg`: вывод фронта — бесконечность
  СОСТАВНЫХ M_p — составная сторона той самой величины, на ПРОСТУЮ сторону
  которой Мерсенн-фронт (гл. 43) не поставил.

  ⚠️ ЧЕСТНОЕ РАСКРЫТИЕ СООТНОШЕНИЯ ЗАКОНОВ: гейты различны —
  `SGThreeMod4AbsenceAbove P` СЛАБЕЕ `SGAbsenceAbove P` (ограничивает лишь
  класс 3 mod 4), потому рестрикт-закон открывается более слабым свидетелем
  и полносемейный закон НЕ даёт его напрямую (это было бы усиление гейта в
  посылке). Импликация между законами ни в одну сторону здесь НЕ утверждается
  и НЕ потребляется — королларий ниже кормится ТОЛЬКО рестрикт-законом.
#############################################################################-/

/-- **Отсутствие пар Софи Жермен класса 3 (mod 4) выше `P`** (Π-свидетель
    рестрикт-семейства — того самого, что гасит простоту Мерсенна). -/
def SGThreeMod4AbsenceAbove (P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → (2 * p + 1).Prime → p ≤ P

/-- Плумбинг: из ограниченности рестрикт-семейства извлекается свидетель. -/
theorem exists_sgThreeMod4Absence_of_not_unbounded
    (h : ¬ EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded) :
    ∃ P : ℕ, SGThreeMod4AbsenceAbove P := by
  unfold EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded at h
  push_neg at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun p h1 h2 h3 => by
    by_contra hgt
    exact hP p (by omega) h1 h2 h3⟩

/-- **Локализация рестрикт-домена:** всякая граница отсутствия ≥ 11 —
    пара (11, 23) с 11 ≡ 3 (mod 4) зелёно существует (и действительно
    23 ∣ M₁₁: `mersenne_composite_examples` ветви). -/
theorem sgThreeMod4AbsenceBound_ge_11 {P : ℕ}
    (hAbs : SGThreeMod4AbsenceAbove P) : 11 ≤ P := by
  have h := hAbs 11 (by norm_num) (by norm_num) (by norm_num : (23 : ℕ).Prime)
  omega

/-- Рестрикт-отсутствие выше `P` манифестирует арифметически (та же причинная
    форма, тот же объект поставки, якорь через le_refl). -/
def SGThreeMod4Manifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **РЕСТРИКТ-ЗАКОН МАНИФЕСТАЦИИ 3 (mod 4)** — гейчен СВОИМ свидетелем
    отсутствия (более слабым, чем полносемейный — см. раскрытие в шапке §6).
    ПОЛЕ НЕ ДЕКРЕТИРОВАНО. -/
def SGThreeMod4ManifestationLaw : Prop :=
  ∀ P : ℕ, SGThreeMod4AbsenceAbove P → SGThreeMod4Manifests P

/-- Читаемая форма рестрикт-фронта: свидетель отсутствия + закон + сведённые
    книги ⟹ двигатель-СВИДЕТЕЛЬ как объект. -/
theorem sgThreeMod4Refutation_carries_engine
    (hLaw : SGThreeMod4ManifestationLaw)
    {P : ℕ} (hAbs : SGThreeMod4AbsenceAbove P)
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

/-- **ESSENCE рестрикт-фронта:** нет двигателей + принятая граница +
    рестрикт-закон ⟹ SG-простые класса 3 (mod 4) неограничены. Потребление
    гипотез — то же подлинное, что в SG3. -/
theorem sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SGThreeMod4ManifestationLaw) :
    EuclidsPath.SophieGermainBranch.SGThreeMod4Unbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_sgThreeMod4Absence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    sgThreeMod4Refutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- **АНТИ-МЕРСЕНН-КОРОЛЛАРИЙ — «две ставки, глядящие друг на друга»:**
    нет двигателей + принятая граница + рестрикт-закон 3 (mod 4) ⟹ простых
    `p` с СОСТАВНЫМ `M_p` неограниченно много. Маршрут: essence рестрикт-фронта
    даёт `SGThreeMod4Unbounded`, а жемчужина ветви
    (`mersenneComposites_unbounded_of_sg`, Эйлер–Лагранж) превращает каждое
    такое `p` в убийцу простоты `M_p`. Вывод ЭТОГО фронта кормит СОСТАВНУЮ
    сторону величины `M_p` — той самой, на ПРОСТУЮ сторону которой
    Мерсенн-фронт (гл. 43) не поставил (знак его эвристики инвертирован
    в том числе ИЗ-ЗА этого механизма: p ≡ 3 (mod 4) с простым 2p+1 гасит
    M_p). Безусловно бесконечность составных Мерсеннов известна литературе
    другими методами; здесь честно фиксируется только SG-маршрут. -/
theorem mersenneComposites_unbounded_of_noEngine_boundary_and_sgManifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : SGThreeMod4ManifestationLaw) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬ (mersenne p).Prime :=
  EuclidsPath.SophieGermainBranch.mersenneComposites_unbounded_of_sg
    (sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

-- Машинная видимость чистоты в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound] — БЕЗ step00FirstCause):
#print axioms sophieGermainUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms sgThreeMod4Unbounded_of_noEngine_and_boundary_and_manifestation
#print axioms sgRefutation_carries_engine
#print axioms sgThreeMod4Refutation_carries_engine
#print axioms sgManifestationLaw_iff_unbounded_of_boundary
#print axioms sgAbsenceBound_ge_89
#print axioms isEmpty_properCenterPeel_two_one
#print axioms mersenneComposites_unbounded_of_noEngine_boundary_and_sgManifestation

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
