/-
  HodgeFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль ветви Ходжа в программе
  вечного двигателя: класс Ходжа = КВАНТОВАННЫЙ (рациональный) заряд
  когомологий выровненного типа (p,p); алгебраический цикл = ОПЛАТА;
  гипотеза = каждый квантованный выровненный заряд оплачен. НЕОПЛАЧЕННЫЙ
  заряд открыл бы бесконечный строгий спуск по ℕ-высоте (знаменатель /
  сложность) — запрещённый вечный двигатель (EPMI).

  ЧЕСТНАЯ ГРАНИЦА (громко, как в ЯМ/НС): в mathlib НЕТ теории Ходжа для
  проективных многообразий — ни классов Ходжа, ни алгебраических циклов,
  ни когомологий многообразий. Проверено по пину: слово «Hodge» встречается
  ровно трижды — цитата книги W. Hodges по теории МОДЕЛЕЙ
  (ModelTheory/Fraisse) и упоминания p-адической теории Ходжа в комментариях
  периодных колец (RingTheory/Perfectoid/BDeRham, FontaineTheta); hodge-star
  оператора тоже нет. `HodgeLedger` — АБСТРАКТНЫЙ ЛЕДЖЕР; НИКАКОГО
  содержания алгебраической геометрии сверх намеренной будущей инстанциации
  здесь нет. Проблема тысячелетия НЕ решается и НЕ заявляется.

  Архитектура:
    * модель: `HodgeLedger` — классы, оплата, ℕ-высота, якорь квантования
      «оплачен ⟺ высота 0» (`height_zero_iff`; потреблён по-настоящему:
      `unpaid_height_pos` + V1-опровержение);
    * двигатель: `UnpaidDescentChain` — бесконечная строго убывающая ℕ-цепь
      неоплаченных зарядов; УБИТ БЕЗУСЛОВНО (`isEmpty_unpaidDescentChain`,
      КОРЕНЬ репозитория — EPMI, A = 1). ИНВЕРСИЯ асимметрии ЯМ (раскрыта,
      не подделана): у ЯМ ℝ-лестница ЖИЛА до прихода закона квантования
      (gapless ⟺ Nonempty ladder), здесь квантование ВСТРОЕНО в модель
      (height : ℕ) — двигатель мёртв в любой модели; вся содержательность
      ветви — в существовании ШАГОВ спуска, т.е. в законе;
    * закон спуска `DescentLaw` (per-model 🔴 ВХОД, NS/ЯМ-паттерн): каждый
      неоплаченный ходжев заряд допускает платёжный шаг — строго меньший
      неоплаченный ходжев заряд; для НАМЕРЕННОЙ (не построенной!)
      инстанциации это и есть остаточный вход ветви;
    * ГЕРОЙ: `hodgeProperty_of_descentLaw` — сильная индукция по высоте
      (выбор НЕ нужен); цепной маршрут через выбор (зеркало ladderSeq) дан
      отдельно (`hodgeProperty_of_descentLaw'`).

  КОЛЛАПС стоимости (§4): `descentLaw_iff_hodgeProperty` — per-model закон
  ⟺ гипотеза ЗЕЛЁНО и БЕЗ ВСЯКОЙ границы (форма осуждённого моста, как
  `quantizationLaw_iff_massGap`); обратная сторона ВАКУУМНА (как римановская
  L5 `manifestationLaw_of_RH`, в ОТЛИЧИЕ от ЯМ L8 с настоящим рангом) —
  раскрыто. Потому ШЕСТОГО ПОЛЯ НЕТ: декретировать закон = декретировать
  цель дословно.

  ТРИЛЕММА шестой границы декрета — все вердикты машинны (§6):
    V1 универсальная форма ОПРОВЕРЖИМА (cookedUnpaid: заряд высоты 1 —
       шаг спуска упёрся бы в оплаченность нулевой высоты);
    V2 экзистенциальная форма УЖЕ ДОКАЗАНА (cookedPaid — закон вакуумен);
    V2′ chain-манифестационная форма ВЫРОЖДЕНА В ЗЕЛЁНУЮ ТЕОРЕМУ
       (`hodgeChainManifestationLaw_green`: цепей нет НИ В ОДНОЙ модели) —
       вердикт V2-типа, декрет был бы вакуумен; уникальная структурная
       точка ветви, раскрыта;
    V3 манифестационная форма над ПРЕДЪЯВИМЫМ свидетелем (одиночный
       неоплаченный класс, `cookedUnpaidClass`) НЕСОВМЕСТИМА с принятой
       границей — зеркало ЯМ/НС V3.
  Раскол по масштабам НЕ дублируется: он уже зафиксирован в §12 карантина
  (`decreedScale_no_deviationSupply`) и в `YangMills.smallScale_deviationSupply`.
  Модуль карантин НЕ импортирует; axiom/sorry нет — верификатор обязан
  показать все декларации незаражёнными.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace Hodge

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
-- EPMI и OriginAnchorAudit используем КВАЛИФИЦИРОВАННО (коллизии State/Step/Bridge).

/-#############################################################################
  §1. Абстрактный леджер когомологий, гипотеза, неоплаченные классы
#############################################################################-/

/-- **D1. Абстрактный леджер когомологий**: классы, выделенные квантованные
    (рациональные) заряды выровненного типа (p,p) (`IsHodge`), оплаченные
    циклами (`IsAlgebraic`), и ℕ-высота (знаменатель/сложность) с якорем
    квантования `height_zero_iff` («оплачен ⟺ высота 0»). `zero` —
    инвариантный якорь обитаемости (нулевой заряд оплачен нулевым циклом);
    групповая структура НЕ навешивается — цепь убийцы не вычитает
    (алгебра платежей принадлежит будущей инстанциации, раскрыто).
    `IsAlgebraic` определим из высоты через якорь — оставлен именованным
    полем ради леджер-прочтения. НИКАКОГО содержания алгебраической
    геометрии (раскрыто в шапке). -/
structure HodgeLedger where
  Cls : Type
  zero : Cls
  IsHodge : Cls → Prop
  IsAlgebraic : Cls → Prop
  height : Cls → ℕ
  zero_hodge : IsHodge zero
  zero_algebraic : IsAlgebraic zero
  height_zero_iff : ∀ c, height c = 0 ↔ IsAlgebraic c

/-- **D2. ГИПОТЕЗА ХОДЖА для модели** (направление Клэя; здесь — только
    абстрактная форма): каждый квантованный выровненный заряд оплачен. -/
def HodgeProperty (S : HodgeLedger) : Prop :=
  ∀ c : S.Cls, S.IsHodge c → S.IsAlgebraic c

/-- **D3. Неоплаченный ходжев класс** — объект отклонения (аналог
    off-critical нуля / положительного состояния): ровно этот тип кован и
    ПРЕДЪЯВИМ (топливо V3 и origin-anchor аудитов). -/
abbrev UnpaidClass (S : HodgeLedger) : Type :=
  {c : S.Cls // S.IsHodge c ∧ ¬ S.IsAlgebraic c}

/-- Нулевой заряд оплачен — обитаемость мира оплат в каждой модели. -/
theorem zero_paid (S : HodgeLedger) : S.IsHodge S.zero ∧ S.IsAlgebraic S.zero :=
  ⟨S.zero_hodge, S.zero_algebraic⟩

/-- Высота нулевого заряда — 0 (якорь потреблён). -/
theorem height_zero (S : HodgeLedger) : S.height S.zero = 0 :=
  (S.height_zero_iff S.zero).mpr S.zero_algebraic

/-- **L1 (квант неоплаченности):** неоплаченный заряд несёт СТРОГО
    положительную высоту — «квантованность» честна: между «оплачен» и
    «не оплачен» лежит целый квант. -/
theorem unpaid_height_pos {S : HodgeLedger} {c : S.Cls}
    (hna : ¬ S.IsAlgebraic c) : 0 < S.height c :=
  Nat.pos_of_ne_zero (fun h0 => hna ((S.height_zero_iff c).mp h0))

/-- **L2 — точная классическая характеризация гипотезы:** гипотеза ⟺
    неоплаченных классов нет (зеркало ЯМ `not_massGap_iff_gapless`). -/
theorem hodgeProperty_iff_no_unpaidClass (S : HodgeLedger) :
    HodgeProperty S ↔ ¬ Nonempty (UnpaidClass S) := by
  constructor
  · rintro hP ⟨⟨c, hc, hna⟩⟩
    exact hna (hP c hc)
  · intro hNo c hc
    by_contra hna
    exact hNo ⟨⟨c, hc, hna⟩⟩

theorem not_hodgeProperty_iff_unpaidClass (S : HodgeLedger) :
    ¬ HodgeProperty S ↔ Nonempty (UnpaidClass S) := by
  rw [hodgeProperty_iff_no_unpaidClass, not_not]

/-#############################################################################
  §2. ОБЪЕКТ-ДВИГАТЕЛЬ: цепь неоплаченного спуска — мертва БЕЗУСЛОВНО
#############################################################################-/

/-- **D4. ЦЕПЬ НЕОПЛАЧЕННОГО СПУСКА — вечный двигатель в ℕ**: бесконечная
    последовательность неоплаченных ходжевых зарядов со строго убывающей
    высотой (аналог `GaplessLadder` ЯМ, но над ℕ, где well-foundedness
    РАБОТАЕТ — потому тип пуст безусловно, см. L3). -/
structure UnpaidDescentChain (S : HodgeLedger) where
  seq : ℕ → S.Cls
  hodge : ∀ n, S.IsHodge (seq n)
  unpaid : ∀ n, ¬ S.IsAlgebraic (seq n)
  descent : ∀ n, S.height (seq (n + 1)) < S.height (seq n)

/-- **L3 — ЗЕЛЁНЫЙ УБИЙЦА (КОРЕНЬ РЕПОЗИТОРИЯ), БЕЗУСЛОВНЫЙ:** цепь
    неоплаченного спуска = бесконечный ℕ-спуск = вечный двигатель Евклида;
    убита `no_infinite_descent` (EPMI, A = 1). РАСКРЫТАЯ АСИММЕТРИЯ С ЯМ:
    там лестницы жили ровно при безмассовости (`gapless_iff_nonempty_ladder`),
    здесь квантование встроено в модель (height : ℕ) — двигатель мёртв В
    ЛЮБОЙ модели, никакой гипотезы не потреблено. -/
theorem no_unpaidDescentChain {S : HodgeLedger}
    (C : UnpaidDescentChain S) : False :=
  EuclidsPath.Engine.no_infinite_descent (le_refl 1)
    (fun t => S.height (C.seq t))
    (fun t => by
      show 1 * S.height (C.seq (t + 1)) < S.height (C.seq t)
      rw [Nat.one_mul]
      exact C.descent t)

/-- **L3′ — EPMI-резонанс формой:** тип цепей ПУСТ в каждой модели.
    (У ЯМ пустота лестниц была ⟺ гэпу; здесь — теорема без гипотез.) -/
theorem isEmpty_unpaidDescentChain (S : HodgeLedger) :
    IsEmpty (UnpaidDescentChain S) :=
  ⟨no_unpaidDescentChain⟩

/-#############################################################################
  §3. Закон спуска (per-model 🔴 ВХОД) и ГЕРОЙ
#############################################################################-/

/-- **D5. ЗАКОН СПУСКА/ПРИБЛИЖЕНИЯ — per-model 🔴 ВХОД (NS/ЯМ-паттерн, как
    `EnergyBalanceLaw`/`QuantizationLaw`):** каждый неоплаченный ходжев
    заряд допускает платёжный шаг — неоплаченный ходжев заряд СТРОГО
    меньшей высоты (оплата лучшего приближения строго уменьшает
    знаменатель остатка). Для НАМЕРЕННОЙ (не построенной!) инстанциации
    S = рациональные (p,p)-классы гладкого проективного многообразия
    это и есть остаточный математический вход ветви. -/
def DescentLaw (S : HodgeLedger) : Prop :=
  ∀ c : S.Cls, S.IsHodge c → ¬ S.IsAlgebraic c →
    ∃ c' : S.Cls, S.IsHodge c' ∧ ¬ S.IsAlgebraic c' ∧
      S.height c' < S.height c

/-- Один шаг выбора: следующий неоплаченный заряд строго меньшей высоты. -/
noncomputable def descentNext {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) : UnpaidClass S :=
  ⟨(hLaw p.1 p.2.1 p.2.2).choose,
   (hLaw p.1 p.2.1 p.2.2).choose_spec.1,
   (hLaw p.1 p.2.1 p.2.2).choose_spec.2.1⟩

theorem descentNext_height_lt {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) :
    S.height (descentNext hLaw p).1 < S.height p.1 :=
  (hLaw p.1 p.2.1 p.2.2).choose_spec.2.2

/-- Рекурсивная последовательность выбора (`Classical.choice` честно виден;
    зеркало `ladderSeq`). -/
noncomputable def descentSeq {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) : ℕ → UnpaidClass S
  | 0 => p
  | n + 1 => descentNext hLaw (descentSeq hLaw p n)

@[simp] theorem descentSeq_succ {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) (n : ℕ) :
    descentSeq hLaw p (n + 1) = descentNext hLaw (descentSeq hLaw p n) := rfl

/-- **L4 (свидетель содержательности, зеркало `gaplessLadder_of_gapless`):**
    из закона + неоплаченного класса цепь СТРОИТСЯ (выбором). Поскольку
    цепей не бывает (L3′), это уже приговор паре «закон + неоплаченность». -/
noncomputable def unpaidDescentChain_of_descentLaw {S : HodgeLedger}
    (hLaw : DescentLaw S) (p : UnpaidClass S) : UnpaidDescentChain S where
  seq := fun n => (descentSeq hLaw p n).1
  hodge := fun n => (descentSeq hLaw p n).2.1
  unpaid := fun n => (descentSeq hLaw p n).2.2
  descent := fun n => by
    show S.height (descentSeq hLaw p (n + 1)).1
        < S.height (descentSeq hLaw p n).1
    rw [descentSeq_succ]
    exact descentNext_height_lt hLaw (descentSeq hLaw p n)

/-- **L5:** закон спуска и неоплаченный класс НЕСОВМЕСТНЫ (цепной маршрут). -/
theorem no_descentLaw_with_unpaid {S : HodgeLedger}
    (hLaw : DescentLaw S) (p : UnpaidClass S) : False :=
  no_unpaidDescentChain (unpaidDescentChain_of_descentLaw hLaw p)

/-- Оплата на каждом этаже высоты: сильная индукция по ℕ-высоте (выбор НЕ
    нужен — вторая, прямая форма того же EPMI-корня). -/
theorem algebraic_at_height_of_descentLaw {S : HodgeLedger}
    (hLaw : DescentLaw S) :
    ∀ n : ℕ, ∀ c : S.Cls, S.height c = n → S.IsHodge c → S.IsAlgebraic c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hcn hc
    by_contra hna
    obtain ⟨c', hc', hna', hlt⟩ := hLaw c hc hna
    exact hna' (ih (S.height c') (by omega) c' rfl hc')

/-- **L6 — ГЕРОЙ (зелёная условная цепь, NS/ЯМ-паттерн):** закон спуска ⟹
    гипотеза Ходжа модели. Маршрут: сильная индукция по высоте. -/
theorem hodgeProperty_of_descentLaw {S : HodgeLedger}
    (hLaw : DescentLaw S) : HodgeProperty S :=
  fun c hc => algebraic_at_height_of_descentLaw hLaw (S.height c) c rfl hc

/-- **L6′ — тот же герой цепным маршрутом** (выбор + безусловная пустота
    цепей; обе формы, как у ЯМ — прямой убийца и лестница). -/
theorem hodgeProperty_of_descentLaw' {S : HodgeLedger}
    (hLaw : DescentLaw S) : HodgeProperty S := by
  intro c hc
  by_contra hna
  exact no_descentLaw_with_unpaid hLaw ⟨c, hc, hna⟩

/-- **L7 (аналог ЯМ L7):** модели с законом и неоплаченным зарядом НЕ
    существует. -/
theorem no_unpaid_lawful_model :
    ¬ ∃ S : HodgeLedger, DescentLaw S ∧ Nonempty (UnpaidClass S) := by
  rintro ⟨S, hLaw, ⟨p⟩⟩
  exact no_descentLaw_with_unpaid hLaw p

/-#############################################################################
  §4. Зеркало стоимости и его КОЛЛАПС (решающий аудит честности)
#############################################################################-/

/-- **L8 (обратная сторона — ВАКУУМНА, раскрыто):** гипотеза ⟹ закон:
    квантор по неоплаченным зарядам пуст. Как римановская L5
    (`manifestationLaw_of_RH`), в ОТЛИЧИЕ от ЯМ L8, где ранг строился
    по-настоящему (`Nat.log 2 ⌊E/Δ⌋₊`). -/
theorem descentLaw_of_hodgeProperty {S : HodgeLedger}
    (hP : HodgeProperty S) : DescentLaw S :=
  fun c hc hna => (hna (hP c hc)).elim

/-- **L9 — ГЛАВНЫЙ АУДИТ (коллапс зеркала стоимости):** per-model закон ⟺
    гипотеза Ходжа модели — ЗЕЛЁНО и БЕЗ ВСЯКОЙ ГРАНИЦЫ. Форма ОСУЖДЁННОГО
    моста (`offCriticalBridge_iff_RH`, `quantizationLaw_iff_massGap`):
    декретировать закон для модели = декретировать её гипотезу дословно.
    Потому per-model декретное поле невозможно ЧЕСТНО; недостающее —
    data anchor (настоящие рациональные (p,p)-классы; в mathlib их НЕТ —
    шапка), Prop-невакуумность — неверный критерий (SpectralAnchorAudit). -/
theorem descentLaw_iff_hodgeProperty (S : HodgeLedger) :
    DescentLaw S ↔ HodgeProperty S :=
  ⟨hodgeProperty_of_descentLaw, descentLaw_of_hodgeProperty⟩

/-#############################################################################
  §5. Кованые модели (свидетели трилеммы)
#############################################################################-/

/-- Кованая НЕОПЛАЧЕННАЯ модель: классы ℕ, ходжевы — `{0, 1}`, оплачен
    только `0`, высота тождественная. Заряд `1` — квантованный, выровненный,
    НЕОПЛАЧЕННЫЙ; шага спуска у него НЕТ. -/
def cookedUnpaid : HodgeLedger where
  Cls := ℕ
  zero := 0
  IsHodge := fun c => c ≤ 1
  IsAlgebraic := fun c => c = 0
  height := fun c => c
  zero_hodge := Nat.zero_le 1
  zero_algebraic := rfl
  height_zero_iff := fun _ => Iff.rfl

theorem cookedUnpaid_one_hodge : cookedUnpaid.IsHodge (1 : ℕ) := le_refl 1

theorem cookedUnpaid_one_unpaid : ¬ cookedUnpaid.IsAlgebraic (1 : ℕ) :=
  Nat.one_ne_zero

/-- Явный неоплаченный свидетель (зеркало `cookedLadder`: предъявлен
    КОНСТРУКЦИЕЙ, без выбора) — топливо V3 и аудитов §7. -/
def cookedUnpaidClass : UnpaidClass cookedUnpaid :=
  ⟨(1 : ℕ), cookedUnpaid_one_hodge, cookedUnpaid_one_unpaid⟩

theorem cookedUnpaid_not_hodgeProperty : ¬ HodgeProperty cookedUnpaid :=
  fun hP => cookedUnpaid_one_unpaid (hP (1 : ℕ) cookedUnpaid_one_hodge)

/-- У кованого заряда `1` НЕТ шага спуска: шаг с высоты 1 дал бы
    неоплаченный класс высоты 0 — оплаченный по якорю квантования
    (`height_zero_iff` потреблён ПО-НАСТОЯЩЕМУ). -/
theorem cookedUnpaid_no_descent_step :
    ¬ ∃ c' : cookedUnpaid.Cls, cookedUnpaid.IsHodge c' ∧
        ¬ cookedUnpaid.IsAlgebraic c' ∧
        cookedUnpaid.height c' < cookedUnpaid.height (1 : ℕ) := by
  rintro ⟨c', _, hna', hlt⟩
  apply hna'
  apply (cookedUnpaid.height_zero_iff c').mp
  have h1 : cookedUnpaid.height (1 : ℕ) = 1 := rfl
  omega

theorem cookedUnpaid_not_descentLaw : ¬ DescentLaw cookedUnpaid :=
  fun hLaw => cookedUnpaid_no_descent_step
    (hLaw (1 : ℕ) cookedUnpaid_one_hodge cookedUnpaid_one_unpaid)

/-- Кованая ПОЛНОСТЬЮ ОПЛАЧЕННАЯ модель: всё ходжево, всё оплачено,
    высота ≡ 0. -/
def cookedPaid : HodgeLedger where
  Cls := ℕ
  zero := 0
  IsHodge := fun _ => True
  IsAlgebraic := fun _ => True
  height := fun _ => 0
  zero_hodge := trivial
  zero_algebraic := trivial
  height_zero_iff := fun _ => ⟨fun _ => trivial, fun _ => rfl⟩

theorem cookedPaid_hodgeProperty : HodgeProperty cookedPaid :=
  fun _ _ => trivial

/-- Закон на оплаченной модели — ВАКУУМНО (неоплаченных зарядов нет).
    Раскрыто: вот почему V2-декрет ничего не добавил бы. -/
theorem cookedPaid_descentLaw : DescentLaw cookedPaid :=
  descentLaw_of_hodgeProperty cookedPaid_hodgeProperty

theorem cookedPaid_no_unpaidClass : ¬ Nonempty (UnpaidClass cookedPaid) :=
  (hodgeProperty_iff_no_unpaidClass cookedPaid).mp cookedPaid_hodgeProperty

/-#############################################################################
  §6. ТРИЛЕММА шестой границы декрета — все вердикты машинны
#############################################################################-/

/-- **D6a. КАНДИДАТ 1 (универсальная форма шестого поля).** -/
def HodgeDescentLawUniversal : Prop :=
  ∀ S : HodgeLedger, DescentLaw S

/-- **D6b. КАНДИДАТ 2 (экзистенциальная форма).** -/
def HodgeDescentLawExistential : Prop :=
  ∃ S : HodgeLedger, DescentLaw S ∧ HodgeProperty S

/-- **D6c. КАНДИДАТ 3 (манифестационная форма, риманово зеркало)** — над
    ПРЕДЪЯВИМЫМ типом свидетелей: одиночный неоплаченный класс
    (`UnpaidClass`), НЕ цепь — chain-форма вырождается в зелёную V2
    (`hodgeChainManifestationLaw_green` ниже). Тот же объект поставки
    `DeviationFlowSupply`, что у riemannBoundary/ЯМ/НС; семейство СВОБОДНО
    от c — D-инертность вскрыта аудитами §7. -/
def UnpaidClassManifests {S : HodgeLedger} (_c : UnpaidClass S) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def HodgeManifestationLaw : Prop :=
  ∀ (S : HodgeLedger) (c : UnpaidClass S), UnpaidClassManifests c

/-- **V1: КАНДИДАТ 1 ЗЕЛЁНО-ОПРОВЕРЖИМ** — его декрет сделал бы карантин
    противоречивым. Свидетель: cookedUnpaid (шаг спуска с высоты 1 упирается
    в якорь квантования). -/
theorem hodgeLawUniversal_refuted : ¬ HodgeDescentLawUniversal :=
  fun h => cookedUnpaid_not_descentLaw (h cookedUnpaid)

/-- **V2: КАНДИДАТ 2 ЗЕЛЁНО-ДОКАЗУЕМ** — декрет был бы вакуумен.
    Свидетель: cookedPaid (закон вакуумен, гипотеза дословно). -/
theorem hodgeLawExistential_green : HodgeDescentLawExistential :=
  ⟨cookedPaid, cookedPaid_descentLaw, cookedPaid_hodgeProperty⟩

/-- Chain-манифестационный кандидат (форма ЯМ D6c над лестницами,
    механически перенесённая на цепи). -/
def ChainManifests {S : HodgeLedger} (_C : UnpaidDescentChain S) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def HodgeChainManifestationLaw : Prop :=
  ∀ (S : HodgeLedger) (C : UnpaidDescentChain S), ChainManifests C

/-- **V2′: CHAIN-ФОРМА ВЫРОЖДЕНА — ЗЕЛЁНО-ДОКАЗУЕМА (вердикт V2-типа, НЕ
    V3!):** цепей не существует ни в одной модели (L3), потому закон над
    ними вакуумен. КЛЮЧЕВАЯ структурная асимметрия с ЯМ (раскрыта): там
    лестница была условно обитаема и её манифестационная форма давала
    настоящий V3; здесь квантованный двигатель мёртв безусловно — честный
    V3-свидетель обязан быть одиночным классом (D6c). -/
theorem hodgeChainManifestationLaw_green : HodgeChainManifestationLaw :=
  fun _S C => (no_unpaidDescentChain C).elim

/-- **V3: КАНДИДАТ 3 НЕСОВМЕСТИМ С ПРИНЯТОЙ ГРАНИЦЕЙ** (зелёная условная
    форма, taint-free, зеркало ЯМ/НС V3): кованый неоплаченный класс — в
    отличие от off-critical нуля — зелёно ПРЕДЪЯВИМ; закон + граница ⟹
    False (граница даёт разрешающую проекцию (M0 = 1) → закон поставляет
    `DeviationFlowSupply` → `no_deviationFlowSupply_at_resolved_scale`
    сжигает). Потому шестое поле этой формы ВЗОРВАЛО бы карантин. -/
theorem hodgeManifestationLaw_refutes_boundary
    (hLaw : HodgeManifestationLaw) : ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hres⟩
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf 1) :=
    strictSemanticExtended_resolves_old (hres 1)
  exact no_deviationFlowSupply_at_resolved_scale (projOf 1) hResolves
    (hLaw cookedUnpaid cookedUnpaidClass A 1 (projOf 1) hResolves)

/-- Контрапозиция для читаемости: при принятой границе закона НЕТ. -/
theorem not_hodgeManifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) : ¬ HodgeManifestationLaw :=
  fun hLaw => hodgeManifestationLaw_refutes_boundary hLaw hBoundary

/-- **V3-характеризация (безусловная — квантор зелёно обитаем,
    cookedUnpaidClass):** закон ⟺ глобальная заморозка всех леджеров. -/
theorem hodgeManifestationLaw_iff_no_resolution :
    HodgeManifestationLaw ↔
      ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw A M0 proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw cookedUnpaid cookedUnpaidClass A M0 proj hres)
  · intro hFreeze S c A M0 proj hres
    exact ((hFreeze A M0 proj) hres).elim

/-#############################################################################
  §7. Origin-anchor аудиты (инстанциация осуждающей машины)
#############################################################################-/

/-- **A1 (bundling-аудит, инстанциация `front_pair_iff_no_zero`):**
    Bridge∧Impossible для семейства манифестаций ⟺ неоплаченных классов нет. -/
theorem hodge_bundling_audit (S : HodgeLedger) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun c : UnpaidClass S => UnpaidClassManifests c) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun c : UnpaidClass S => UnpaidClassManifests c)) ↔
      ¬ Nonempty (UnpaidClass S) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-- **A1′ (заострение через L2):** связка — ровно ГИПОТЕЗА ХОДЖА модели
    (инстанциация `front_pair_iff_RH` при RH := HodgeProperty S). -/
theorem hodge_front_pair_iff_hodgeProperty (S : HodgeLedger) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun c : UnpaidClass S => UnpaidClassManifests c) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun c : UnpaidClass S => UnpaidClassManifests c)) ↔
      HodgeProperty S :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_RH
    (hodgeProperty_iff_no_unpaidClass S).symm

/-- **A2 (асимметрия с Риманом, машинно):** на кованой модели связка
    ОПРОВЕРГНУТА — неоплаченный класс предъявлен. Bridge-сторону
    декретировать НЕЛЬЗЯ. -/
theorem hodge_bundle_refuted_at_cooked :
    ¬ (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
         (fun c : UnpaidClass cookedUnpaid => UnpaidClassManifests c) ∧
       EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
         (fun c : UnpaidClass cookedUnpaid => UnpaidClassManifests c)) :=
  fun h => (hodge_bundling_audit cookedUnpaid).mp h ⟨cookedUnpaidClass⟩

/-- **A3 (Z-free collapse, урок SpectralAnchorAudit):** семейство
    манифестаций СВОБОДНО от класса — коллапсирует к одному c-независимому
    вопросу-«атому». -/
theorem hodgeLaw_freeCollapse (S : HodgeLedger) :
    EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.FreeLawCollapse
      (fun c : UnpaidClass S => UnpaidClassManifests c)
      (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
          DeviationFlowSupply A M0) :=
  fun _c => Iff.rfl

/-- **A4:** потому семейство не разделяет неоплаченных классов — свободный
    закон не несёт информации об отклонении (та же причина, по которой он
    не годится в декретное поле). -/
theorem hodgeLaw_cannot_separate (S : HodgeLedger) :
    ¬ EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.ZeroSeparating
        (fun c : UnpaidClass S => UnpaidClassManifests c) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.no_zero_separation_under_freeCollapse
    (hodgeLaw_freeCollapse S)

end Hodge
end EuclidsPath

-- Машинная видимость чистоты в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.Hodge.isEmpty_unpaidDescentChain
#print axioms EuclidsPath.Hodge.hodgeProperty_of_descentLaw
#print axioms EuclidsPath.Hodge.descentLaw_iff_hodgeProperty
#print axioms EuclidsPath.Hodge.hodgeLawUniversal_refuted
#print axioms EuclidsPath.Hodge.hodgeLawExistential_green
#print axioms EuclidsPath.Hodge.hodgeChainManifestationLaw_green
#print axioms EuclidsPath.Hodge.hodgeManifestationLaw_refutes_boundary
