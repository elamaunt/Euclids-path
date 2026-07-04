/-
  ChowlaEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ фронта Чоулы/Сарнака (глава 54).
  Зеркало PNPFirstCause / LehmerEpistemic (НЕ Коллатц-варианта: декрета у Чоулы нет
  и не было — Чоула не входит в четыре границы step00FirstCause, файл целиком зелёный).
  Зелёный фронт: Engine/ChowlaFront.lean (λ² = 1, диагональ = x, флип паритета).

  ЧТО ЭТО. «Решить узел чётности-сдвига изнутри» = предъявить ПОЛНОЕ внутреннее
  решение динамики знака λ, т.е. коллапс паритета: хвост, на котором знак Лиувилля
  ПОСТОЯНЕН (`PerfectParityCollapse`: ∃ N, ∀ m ≥ N, λ(m) = λ(N)) — единственная
  форма, в которой конечная внутренняя система может «знать» поведение чётности
  ранга целиком. Это самоуничтожается НЕ подстановкой P ∧ ¬P, а настоящей
  флип-стеной: удвоение аргумента ФЛИПАЕТ знак (λ(2m) = −λ(m), реюз
  `chowla_parity_flip` при p = 2 — НЕ третья копия `liouville_flip_of_mul_prime`,
  CORR §4), а λ² = 1 запрещает знаку быть нулём — хвостовая константа гибнет на
  первом же удвоении (`no_parityCollapse_of_flip`). Та же валюта, что пижонхол
  `no_fullPayment_of_unboundedSupply` у P/NP и Норткотт-стена у Лемера.

  ПОТРЕБЛЕНИЕ, НЕ ДЕКОРАЦИЯ (CORR §1). Лемма-стена `no_parityCollapse_of_flip`
  ПАРАМЕТРИЗОВАНА флип-поставкой: она берёт `flip : ∀ m, λ(2m) = −λ(m)` гипотезой
  и потребляет её в противоречии. Поэтому `no_internalisedChowlaGround` — это
  `fun H => no_parityCollapse_of_flip H.beyondOwnHorizon H.ground`: ОБА поля
  грузонесущие на уровне терма (точное зеркало
  `no_fullPayment_of_unboundedSupply H.beyondOwnHorizon H.resolves`).

  ЧЕСТНЫЕ ГРАНИЦЫ (обязательные, по вердикту скептика):
  (1) Поле `beyondOwnHorizon` — доказуемый зелёный факт (`liouville_doubling_flip`),
      поэтому структура `InternalisedChowlaGround` ЭКСТЕНСИОНАЛЬНО эквивалентна
      одному полю `ground` — раскрыто машинно леммой
      `internalisedChowlaGround_iff_collapse`. Оплата противоречия РЕАЛЬНА
      (флип + λ² = 1, не тавтология), но связка слабее эталона P/NP, где ОБЕ
      ноги — независимые нетривиальные предикаты.
  (2) Связка покрывает ТОЛЬКО коллапс-моду (детерминированную хвостовую
      константность знака). Для статистического опровержения Чоулы (корреляция
      порядка c·x БЕЗ детерминированного закона) связка вырождается: зелёного
      факта «отклонение ⟹ двигатель» НЕ существует, и его построение — открытая
      математика, по существу сама Чоула. Поэтому в имени сводки НЕТ «двигателя»:
      здесь честно флип-стена (`chowla_locked_behind_flip_wall`), двигательного
      факта у Чоулы в репо нет.
  (3) Это модель-внутренняя эпистемика узла чётности-сдвига, а НЕ доказательство
      и НЕ опровержение гипотез Чоулы/Сарнака: красные гейты `ChowlaConjecture` /
      `SarnakConjecture` остаются красными, о них не утверждается НИЧЕГО.
  (4) Это НЕ Гёдель: никакой независимости — только флип-самоуничтожение
      внутреннего самообоснования.

  🟢 ЗЕЛЁНОЕ ЗДЕСЬ (всё над РЕАЛЬНОЙ `ArithmeticFunction.liouville`):
   · `liouville_doubling_flip` — λ(2m) = −λ(m) (реюз `chowla_parity_flip`, p = 2);
   · `liouville_no_doubling_fixpoint` — НЕ существует m ≠ 0 с λ(2m) = λ(m);
   · `no_parityCollapse_of_flip` / `no_parityCollapse` — совершенный коллапс
     паритета (хвостовая константность λ) невозможен;
   · `chowlaCorrelation_parity` — корреляция ≡ x (mod 2): сумма x термов ±1;
     следствие `chowlaCorrelation_ne_zero_of_odd` — ноль НЕДОСТИЖИМ на нечётном
     срезе (точечная жёсткость величины красного гейта: «o(x)» принципиально
     не может быть тождественным нулём);
   · `liouville_two_pow` — λ(2^k) = (−1)^k: неограниченная поставка ОБОИХ знаков
     (`liouville_attains_both_signs_cofinally`) — знаковая динамика не вырождена;
   · эпистемический пакет: `no_internalisedChowlaGround`, `chowlaCause_unknowable`,
     сводка `chowla_locked_behind_flip_wall`.

  Никакого sorry, никакой новой аксиомы, никакого native_decide, карантин
  (CausalClosureAxiom) НЕ импортируется. Все зелёные грузонесущие — стандартная
  тройка propext / Classical.choice / Quot.sound. Таинт репозитория (47) этим
  файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/ChowlaEpistemic.lean

  Родство: Engine/ChowlaFront.lean (зелёное ядро + красные гейты),
    Engine/RiemannLiouville.lean (флип у истока), Engine/PNPFirstCause.lean и
    Engine/TwinNodeEpistemic.lean / Engine/LehmerEpistemic.lean (эталоны эпистемики).
-/
import EuclidsPath.Engine.ChowlaFront

set_option autoImplicit false

namespace EuclidsPath.ChowlaFront.Epistemic

open ArithmeticFunction

/-! ## Флип-стена: динамика знака λ на удвоении (🟢) -/

/-- 🟢 **Флип-поставка на удвоении.** Умножение аргумента на 2 ФЛИПАЕТ знак Лиувилля:
    `λ(2m) = −λ(m)` для ВСЕХ `m` (при `m = 0` обе части нули). Реюз
    `chowla_parity_flip` при `p = 2` (который сам — переизложение
    `RiemannLiouville.liouville_flip_of_mul_prime`; третья копия НЕ плодится, CORR §4).
    Роль: неисчерпаемое «топливо» флип-стены — поле `beyondOwnHorizon` ниже. -/
theorem liouville_doubling_flip (m : ℕ) :
    ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m :=
  chowla_parity_flip Nat.prime_two

/-- 🟢 **Совершенный коллапс на удвоении невозможен точечно.** НЕ существует `m ≠ 0`
    с `λ(2m) = λ(m)`: флип даёт `λ(2m) = −λ(m)`, а `λ² = 1` запрещает знаку быть
    нулём. Первый жёсткий факт чоула-типа: чётность ранга обязана осциллировать
    уже вдоль удвоений. -/
theorem liouville_no_doubling_fixpoint {m : ℕ} (hm : m ≠ 0) :
    ArithmeticFunction.liouville (2 * m) ≠ ArithmeticFunction.liouville m := by
  rw [liouville_doubling_flip m]
  intro hEq
  have hzero : ArithmeticFunction.liouville m = 0 := by omega
  have hsq := liouville_sq_eq_one hm
  rw [hzero] at hsq
  norm_num at hsq

/-! ## (а) Коллапс паритета и его невозможность (🟢) -/

/-- **Совершенный коллапс паритета** — «внутреннее полное решение» узла
    чётности-сдвига: существует хвост, на котором знак Лиувилля ПОСТОЯНЕН
    (`∃ N, ∀ m ≥ N, λ(m) = λ(N)`). Единственная форма, в которой конечная
    внутренняя система могла бы «знать» поведение чётности ранга целиком.
    Это ground эпистемической связки ниже; гипотеза Чоулы утверждает ГОРАЗДО
    больше (некоррелированность поперёк всех сдвигов), поэтому невозможность
    коллапса — лишь конечный зародыш, НЕ решение гипотезы. -/
def PerfectParityCollapse : Prop :=
  ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
    ArithmeticFunction.liouville m = ArithmeticFunction.liouville N

/-- 🟢 **ФЛИП-СТЕНА (грузонесущая, параметризована поставкой — CORR §1).** Любая
    флип-поставка `∀ m, λ(2m) = −λ(m)` уничтожает совершенный коллапс паритета:
    в хвосте константности берём `m ≥ max(N,1)` — тогда `λ(2m) = λ(N) = λ(m)`
    по константности, но `λ(2m) = −λ(m)` по флипу, значит `λ(m) = 0` против
    `λ(m)² = 1`. Флип-поставка ПОТРЕБЛЯЕТСЯ противоречием (не декорация) —
    точный аналог пижонхола `no_fullPayment_of_unboundedSupply` у P/NP. -/
theorem no_parityCollapse_of_flip
    (flip : ∀ m : ℕ,
      ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m) :
    PerfectParityCollapse → False := by
  rintro ⟨N, hN⟩
  have hm1 : 1 ≤ max N 1 := le_max_right N 1
  have hmN : N ≤ max N 1 := le_max_left N 1
  have hm0 : max N 1 ≠ 0 := by omega
  have e1 := hN (max N 1) hmN
  have e2 := hN (2 * max N 1) (by omega)
  have e3 := flip (max N 1)
  have hzero : ArithmeticFunction.liouville (max N 1) = 0 := by omega
  have hsq := liouville_sq_eq_one hm0
  rw [hzero] at hsq
  norm_num at hsq

/-- 🟢 **Совершенный коллапс паритета невозможен (безусловно).** Флип-поставка —
    теорема (`liouville_doubling_flip`), поэтому стена срабатывает без гипотез:
    хвостовой константности знака Лиувилля НЕ существует. -/
theorem no_parityCollapse : PerfectParityCollapse → False :=
  no_parityCollapse_of_flip liouville_doubling_flip

/-! ## (б) Зелёная арифметика корреляции: чётность и недостижимость нуля (🟢) -/

/-- 🟢 **Корреляция ≡ x (mod 2).** Каждый терм `λ(n)·λ(n+h)` на `Icc 1 x` есть `±1`
    (обе λ — знаки, `λ² = 1`), значит терм ≡ 1 (mod 2) и сумма `x` термов имеет
    чётность `x`. Точечная жёсткость величины красного гейта `ChowlaConjecture`. -/
theorem chowlaCorrelation_parity (h x : ℕ) :
    (2 : ℤ) ∣ (chowlaCorrelation h x - (x : ℤ)) := by
  have hdef : chowlaCorrelation h x
      = ∑ n ∈ Finset.Icc 1 x,
          ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) := rfl
  have hx : (x : ℤ) = ∑ _n ∈ Finset.Icc 1 x, (1 : ℤ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [hdef, hx, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  have hnh0 : n + h ≠ 0 := by omega
  have hsq : (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h))
      * (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h)) = 1 := by
    rw [mul_mul_mul_comm, liouville_sq_eq_one hn0, liouville_sq_eq_one hnh0, one_mul]
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hsq) with ht | ht
  · rw [ht]; exact ⟨0, by ring⟩
  · rw [ht]; exact ⟨-1, by ring⟩

/-- 🟢 Та же чётность в `Even`-форме: `chowlaCorrelation h x − x` чётна. -/
theorem chowlaCorrelation_sub_even (h x : ℕ) :
    Even (chowlaCorrelation h x - (x : ℤ)) := by
  obtain ⟨c, hc⟩ := chowlaCorrelation_parity h x
  exact ⟨c, by omega⟩

/-- 🟢 **Ноль недостижим на нечётном срезе.** При нечётном `x` корреляция НЕ равна
    нулю точно: сумма нечётного числа термов `±1` нечётна. «`o(x)`» красного гейта
    принципиально не может быть тождественным нулём — корреляция обязана
    осциллировать (дешёвый, но настоящий вычет; зеркало `oddLandauPrime_even_k`
    у Ландау). -/
theorem chowlaCorrelation_ne_zero_of_odd {h x : ℕ} (hx : Odd x) :
    chowlaCorrelation h x ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := chowlaCorrelation_parity h x
  obtain ⟨j, hj⟩ := hx
  rw [h0] at hc
  omega

/-! ## (в) Неограниченная поставка обоих знаков (🟢) -/

/-- 🟢 **`λ(2^k) = (−1)^k`.** Степени двойки поставляют оба знака Лиувилля в чистом
    виде: `Ω(2^k) = k` (mathlib `cardFactors_apply_prime_pow`), значит знак — точно
    `(−1)^k`. Стиль `liouville_prime` из `RiemannLiouville`. -/
theorem liouville_two_pow (k : ℕ) :
    ArithmeticFunction.liouville (2 ^ k) = (-1 : ℤ) ^ k := by
  rw [liouville_apply (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)),
    cardFactors_apply_prime_pow Nat.prime_two]

/-- 🟢 **Оба знака достигаются кофинально.** Сколь угодно далеко есть и `λ = 1`
    (чётные степени двойки), и `λ = −1` (нечётные): знаковая динамика не
    вырождена, поставка флипов бесконечна. Зелёный аналог
    `UnboundedCertificateSupply` у P/NP — честный контраст к невозможности
    коллапса (`no_parityCollapse`). -/
theorem liouville_attains_both_signs_cofinally (N : ℕ) :
    (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = 1) ∧
    (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = -1) := by
  constructor
  · refine ⟨2 ^ (2 * N), ?_, ?_⟩
    · exact le_trans (by omega : N ≤ 2 * N) (Nat.le_of_lt Nat.lt_two_pow_self)
    · rw [liouville_two_pow]
      exact Even.neg_one_pow ⟨N, by ring⟩
  · refine ⟨2 ^ (2 * N + 1), ?_, ?_⟩
    · exact le_trans (by omega : N ≤ 2 * N + 1) (Nat.le_of_lt Nat.lt_two_pow_self)
    · rw [liouville_two_pow]
      exact Odd.neg_one_pow ⟨N, by ring⟩

/-! ## (г) Модель: внутреннее решение = самообоснование за собственным горизонтом -/

/-- **Внутреннее самообоснование решения узла чётности-сдвига.** Система
    одновременно (a) держит ПОЛНОЕ внутреннее решение — коллапс паритета,
    хвостовую константность знака (`ground`), и (b) видит флип-динамику знака
    на удвоении (`beyondOwnHorizon`).

    СОДЕРЖАТЕЛЬНОСТЬ: противоречие поставляет флип-стена
    `no_parityCollapse_of_flip`, ПОТРЕБЛЯЮЩАЯ оба поля на уровне терма
    (CORR §1) — не `fun H => H.b H.g` Коллатца.
    ЧЕСТНАЯ ОГОВОРКА: `beyondOwnHorizon` — доказуемый зелёный факт
    (`liouville_doubling_flip`), поэтому структура экстенсионально эквивалентна
    голому `ground` (машинно: `internalisedChowlaGround_iff_collapse`) — оплата
    реальна, но вторая нога свободна по построению; это слабее эталона P/NP,
    где обе ноги — независимые нетривиальные предикаты. -/
structure InternalisedChowlaGround : Prop where
  ground : PerfectParityCollapse
  beyondOwnHorizon : ∀ m : ℕ,
    ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m

/-- «Внутреннее знание причины Чоулы» = внутреннее самообоснование решения узла. -/
abbrev InternalKnowledgeOfChowlaCause : Prop := InternalisedChowlaGround

/-- 🟢 Самообоснование самоуничтожается — флип-стена потребляет ОБА поля:
    `no_parityCollapse_of_flip H.beyondOwnHorizon H.ground` (точное зеркало
    `no_fullPayment_of_unboundedSupply H.beyondOwnHorizon H.resolves` у P/NP). -/
theorem no_internalisedChowlaGround : InternalisedChowlaGround → False :=
  fun H => no_parityCollapse_of_flip H.beyondOwnHorizon H.ground

/-- 🟢 **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `pnpCause_unknowable` /
    `lehmerCause_unknowable` / `collatzCause_unknowable`): внутреннее полное
    решение узла чётности-сдвига невозможно. НЕ утверждение о самих гипотезах
    Чоулы/Сарнака — их красные гейты не трогаются. -/
theorem chowlaCause_unknowable : ¬ InternalKnowledgeOfChowlaCause :=
  no_internalisedChowlaGround

/-- 🟢 **Машинная честность (раскрытие формы):** поле `beyondOwnHorizon` — теорема,
    поэтому связка экстенсионально эквивалентна одному полю `ground`.
    Содержательность живёт НЕ в независимости ног, а в ЦЕНЕ противоречия:
    флип + `λ² = 1` (`no_parityCollapse_of_flip`) — реальная арифметика, не
    тавтология P ∧ ¬P. Зеркало `internalisedPNPGround_semantically_selfNegating`. -/
theorem internalisedChowlaGround_iff_collapse :
    InternalisedChowlaGround ↔ PerfectParityCollapse :=
  ⟨fun H => H.ground, fun hg => ⟨hg, liouville_doubling_flip⟩⟩

/-! ## Сводка: узел заперт за флип-стеной (🟢) -/

/-- 🟢 **Итоговый эпистемический статус узла чётности-сдвига** (зеркало
    `pnp_locked_behind_engine_status` БЕЗ декрет-конъюнкта — у Чоулы границы
    step00FirstCause нет; в имени честно НЕТ «двигателя»: двигательного факта
    у Чоулы в репо не существует, стена здесь — флип + `λ² = 1`):
    (1) флип-поставка на удвоении неисчерпаема (теорема);
    (2) оба знака достигаются кофинально — поставка не вырождена (теорема);
    (3) узел непознаваем изнутри (теорема);
    (4) совершенный коллапс паритета невозможен (теорема);
    (5) корреляция никогда не равна нулю на нечётных срезах (теорема) —
        «o(x)» красного гейта не может быть тождественным нулём.
    Красные гейты `ChowlaConjecture`/`SarnakConjecture` остаются красными. -/
theorem chowla_locked_behind_flip_wall :
    (∀ m : ℕ,
      ArithmeticFunction.liouville (2 * m) = - ArithmeticFunction.liouville m) ∧
    (∀ N : ℕ, (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = 1) ∧
      (∃ m : ℕ, N ≤ m ∧ ArithmeticFunction.liouville m = -1)) ∧
    (¬ InternalKnowledgeOfChowlaCause) ∧
    (PerfectParityCollapse → False) ∧
    (∀ h x : ℕ, Odd x → chowlaCorrelation h x ≠ 0) :=
  ⟨liouville_doubling_flip,
   liouville_attains_both_signs_cofinally,
   chowlaCause_unknowable,
   no_parityCollapse,
   fun _h _x hx => chowlaCorrelation_ne_zero_of_odd hx⟩

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт репо НЕ меняется -/
#print axioms liouville_doubling_flip
#print axioms liouville_no_doubling_fixpoint
#print axioms no_parityCollapse_of_flip
#print axioms no_parityCollapse
#print axioms chowlaCorrelation_parity
#print axioms chowlaCorrelation_sub_even
#print axioms chowlaCorrelation_ne_zero_of_odd
#print axioms liouville_two_pow
#print axioms liouville_attains_both_signs_cofinally
#print axioms no_internalisedChowlaGround
#print axioms chowlaCause_unknowable
#print axioms internalisedChowlaGround_iff_collapse
#print axioms chowla_locked_behind_flip_wall

end EuclidsPath.ChowlaFront.Epistemic
