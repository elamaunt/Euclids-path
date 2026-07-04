/-
  AbcEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ abc-фронта (зеркало PNPFirstCause;
  НЕ Коллатц-вариант: декрета у abc нет и не было — abc не входит в четыре границы
  step00FirstCause, файл целиком зелёный). Зелёный фронт: Engine/AbcFront.lean
  (Мейсон–Стотерс, радикал, красный гейт AbcConjecture).

  ЧТО ЗДЕСЬ ЕСТЬ (четыре слоя):

  (а) 🟢 Радикальный инструментарий: `natRad_pow` (rad(n^k) = rad(n) при k ≠ 0),
      `natRad_mul_of_coprime` (мультипликативность на взаимно простых),
      `natRad_mul_dvd`, `natRad_prime` — тонкие обёртки над реальными
      `UniqueFactorizationMonoid.radical_pow` / `radical_mul` / `radical_mul_dvd`
      (Mathlib/RingTheory/Radical/Basic.lean) через `Nat.coprime_iff_isRelPrime`;
      `natRad_prime` идёт через `Nat.Prime.primeFactors` (без normalize-шага).

  (б) 🟢 НАИВНЫЙ abc (ε = 0) ЛОЖЕН — машинно: `abc_exponent_one_counterexample`
      (тройка 1 + 8 = 9, rad(1·8·9) = rad(72) = 6 < 9) и НЕОГРАНИЧЕННАЯ поставка
      качества `unboundedQualitySupplyExponentOne` — семейство a = 1,
      c = 3^(2^(k+1)), b = c − 1 с индукцией 2^(k+3) ∣ 3^(2^(k+1)) − 1 (база
      k = 0: 3² − 1 = 8 = 2³; CORR-сдвиг индекса учтён: при базе 2^(k+2) ∣ 3^(2^k)−1
      утверждение ложно в k = 0) и мультипликативностью радикала. Это оплаченный
      настоящей математикой зелёный факт: «c / rad(abc) неограничен» — точная
      целочисленная противоположность полиномиального `polynomial_abc_no_escape`.

  (в) 🟢 `polynomial_flt_shadow` — именованное полиномиальное зеркало стрелки
      abc ⟹ FLT: цитата РЕАЛЬНОЙ `Polynomial.flt` (mathlib выводит её из
      `Polynomial.flt_catalan`, а ту — из Мейсона–Стотерса `Polynomial.abc`).
      На полиномах стрелка зелёная; на целых та же стрелка заперта за красным
      гейтом `AbcConjecture` — здесь она НЕ заявляется.

  (г) 🟢 Эпистемическая связка (стиль PNPFirstCause): `LinearAbcLaw K` —
      равномерный ЛИНЕЙНЫЙ закон качества при ε = 0 (∀ тройки, c ≤ K·rad(abc));
      `InternalisedAbcGround` (ground : ∃ K, LinearAbcLaw K / beyondOwnHorizon :
      неограниченная поставка), `no_internalisedAbcGround`, `abcCause_unknowable`.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКАЯ ЧЕСТНОСТЬ — ОБЯЗАТЕЛЬНАЯ ШАПКА (по вердикту скептика).            │
  └───────────────────────────────────────────────────────────────────────────┘

  1. ЭТО ЭПИСТЕМИКА НАИВНОЙ ФОРМЫ (ε = 0), А НЕ САМОГО abc. `ground` здесь — НЕ
     открытый гейт `AbcConjecture`, а его наивное ε = 0-усиление (линейный закон
     `∃ K, LinearAbcLaw K`). Связка говорит: «линейное внутреннее заземление
     качества невозможно — вся открытость abc живёт в ε-слабине», и это ПРАВДА
     СЛАБЕЕ, чем эпистемика самого AbcConjecture. Для настоящего гейта (ε > 0)
     аналогичная связка ВЫРОЖДАЕТСЯ в тавтологию: зелёной (1+ε)-поставки не
     существует и существовать не обязана — классически известны лишь
     субполиномиальные побеги Стюарта–Тайдемана, а неограниченная (1+ε)-поставка
     противоречила бы самому abc. Настоящий красный гейт `AbcConjecture` этим
     файлом НЕ ТРОНУТ: не доказан, не опровергнут, не использован как факт.

  2. МАШИННАЯ ЧЕСТНОСТЬ ФОРМЫ (Чоула/PNP-стиль): поле `beyondOwnHorizon` —
     ДОКАЗУЕМЫЙ зелёный факт, поэтому структура `InternalisedAbcGround`
     семантически эквивалентна паре «закон ∧ ¬закон»
     (`internalisedAbcGround_semantically_selfNegating`). Содержательность живёт
     НЕ в форме структуры, а в том, чем контрадикция ОПЛАЧЕНА: индукция
     2^(k+3) ∣ 3^(2^(k+1)) − 1 + мультипликативность радикала + честная
     инстанциация-пижонхол `no_linearAbcLaw_of_unboundedSupply` — ровно механика
     P/NP (`no_fullPayment_of_unboundedSupply`), а не голое P ∧ ¬P.

  3. НЕ Гёдель (никакой независимости не заявляется — только
     пижонхол-самоуничтожение внутреннего самообоснования), НЕ решение abc,
     НЕ перенос Мейсона–Стотерса на ℤ (маркер `noPolynomialToIntegerAbcClaimed`
     остаётся в силе).

  Никакого `sorry`, никакой новой аксиомы, никакого `native_decide`; карантин
  (Engine/CausalClosureAxiom) НЕ импортируется. Всё — стандартная тройка
  (`propext` / `Classical.choice` / `Quot.sound`). Таинт репозитория (47) этим
  файлом НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/AbcEpistemic.lean
-/

import EuclidsPath.Engine.AbcFront

set_option autoImplicit false

namespace EuclidsPath.AbcFront

/-!
################################################################################
  (а) 🟢 Радикальный инструментарий — pow / mul, тонкие обёртки над mathlib
################################################################################
-/

/-- **🟢 (ДОКАЗАНО): радикал степени** — `rad(a^k) = rad(a)` при `k ≠ 0`. Тонкая
    обёртка над реальной `UniqueFactorizationMonoid.radical_pow`
    (Mathlib/RingTheory/Radical/Basic.lean). -/
theorem natRad_pow (a : ℕ) {k : ℕ} (hk : k ≠ 0) : natRad (a ^ k) = natRad a :=
  UniqueFactorizationMonoid.radical_pow a hk

/-- **🟢 (ДОКАЗАНО): мультипликативность радикала на взаимно простых** —
    `rad(a·b) = rad(a)·rad(b)` при `Nat.Coprime a b`. Обёртка над реальной
    `UniqueFactorizationMonoid.radical_mul` (та берёт `IsRelPrime` БЕЗ
    nonzero-гипотез); мост копримальностей — `Nat.coprime_iff_isRelPrime`. -/
theorem natRad_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    natRad (a * b) = natRad a * natRad b :=
  UniqueFactorizationMonoid.radical_mul (Nat.coprime_iff_isRelPrime.mp h)

/-- **🟢 (ДОКАЗАНО): субмультипликативность радикала (без всяких гипотез)** —
    `rad(a·b) ∣ rad(a)·rad(b)`. Цитата `UniqueFactorizationMonoid.radical_mul_dvd`. -/
theorem natRad_mul_dvd (a b : ℕ) : natRad (a * b) ∣ natRad a * natRad b :=
  UniqueFactorizationMonoid.radical_mul_dvd

/-- **🟢 (ДОКАЗАНО): радикал простого — оно само.** Идём через явную формулу
    `natRad_eq_prod_primeFactors` и `Nat.Prime.primeFactors` (`p.primeFactors = {p}`),
    минуя normalize-шаг `radical_of_prime` (CORR-замечание про `normalize = id` на ℕ). -/
theorem natRad_prime {p : ℕ} (hp : p.Prime) : natRad p = p := by
  rw [natRad_eq_prod_primeFactors, hp.primeFactors, Finset.prod_singleton]

/-!
################################################################################
  (б) 🟢 Наивный abc (ε = 0) машинно ложен: контрпример и неограниченная поставка
################################################################################
-/

/-- **🟢 (ДОКАЗАНО): наивный abc при ε = 0 ЛОЖЕН — конкретный контрпример.**
    Тройка `1 + 8 = 9`: `rad(1·8·9) = rad(72) = rad(2³·3²) = 2·3 = 6 < 9`.
    Граница `c ≤ rad(abc)` (без ε-запаса) опровергнута машинно: ε в красном
    гейте `AbcConjecture` — не украшение. Вычисление радикала — целиком через
    инструментарий (а), без `native_decide`. -/
theorem abc_exponent_one_counterexample :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b ∧
      natRad (a * b * c) < c := by
  refine ⟨1, 8, 9, Nat.one_pos, by norm_num, by norm_num,
    Nat.coprime_one_left 8, ?_⟩
  have hfac : (1 * 8 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
  have hcop : Nat.Coprime (2 ^ 3) (3 ^ 2) := by norm_num
  rw [hfac, natRad_mul_of_coprime hcop,
    natRad_pow 2 (by norm_num : (3 : ℕ) ≠ 0),
    natRad_pow 3 (by norm_num : (2 : ℕ) ≠ 0),
    natRad_prime Nat.prime_two, natRad_prime Nat.prime_three]
  norm_num

/-- **🟢 Двоичная накачка (индукция, несущая семейство):**
    `3^(2^(k+1)) = 2^(k+3)·m + 1` с положительным `m`. База `k = 0`:
    `3² = 2³·1 + 1`; шаг — квадрирование `(2^(k+3)·m + 1)² = 2^(k+4)·m' + 1` с
    `m' = 2^(k+2)·m² + m`. Аддитивная форма выбрана вместо ℕ-вычитания.
    CORR учтён: индекс сдвинут (у формы `2^(k+2) ∣ 3^(2^k) − 1` база `k = 0`
    ложна: `4 ∤ 2`). -/
theorem three_pow_two_pow_eq_two_pow_mul_add_one (k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ 3 ^ 2 ^ (k + 1) = 2 ^ (k + 3) * m + 1 := by
  induction k with
  | zero => exact ⟨1, Nat.one_pos, by norm_num⟩
  | succ n ih =>
    obtain ⟨m, hm, hEq⟩ := ih
    refine ⟨2 ^ (n + 2) * m ^ 2 + m,
      Nat.lt_of_lt_of_le hm (Nat.le_add_left m _), ?_⟩
    have hsplit : (3 : ℕ) ^ 2 ^ (n + 1 + 1) = (3 ^ 2 ^ (n + 1)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [hsplit, hEq]
    ring

/-- **🟢 Делимостная форма накачки (формулировка CORR):**
    `2^(k+3) ∣ 3^(2^(k+1)) − 1` при всех `k ≥ 0`. Прямое следствие аддитивной
    формы `three_pow_two_pow_eq_two_pow_mul_add_one`. -/
theorem two_pow_dvd_three_pow_two_pow_sub_one (k : ℕ) :
    2 ^ (k + 3) ∣ 3 ^ 2 ^ (k + 1) - 1 := by
  obtain ⟨m, -, hEq⟩ := three_pow_two_pow_eq_two_pow_mul_add_one k
  exact ⟨m, by rw [hEq, Nat.add_sub_cancel]⟩

/-- **Неограниченная поставка качества при ε = 0** (именованный Prop): для
    ВСЯКОГО линейного горизонта `K` существует честная abc-тройка, чьё качество
    пробивает горизонт — `K·rad(a·b·c) < c`. Аналог `UnboundedCertificateSupply`
    у P/NP: сторона `beyondOwnHorizon` эпистемической связки. -/
def UnboundedQualitySupplyExponentOne : Prop :=
  ∀ K : ℕ, ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b ∧
    K * natRad (a * b * c) < c

/-- **🟢 (ДОКАЗАНО): ПОСТАВКА КАЧЕСТВА ПРИ ε = 0 НЕОГРАНИЧЕНА.** Семейство
    `a = 1`, `c = 3^(2^(K+1))`, `b = c − 1 = 2^(K+3)·m`:
    `rad(b·c) = rad(b)·3 ≤ 2m·3`, значит `K·rad(abc) ≤ 6Km < 2^(K+3)·m < c`
    (последний строгий шаг — `6K < 2^(K+3)`, т.е. `K < 2^K`).
    Оплачено индукцией `three_pow_two_pow_eq_two_pow_mul_add_one` и
    мультипликативностью радикала — НЕ пустышка. Классика «c/rad(abc) неограничен»
    становится зелёной: на ℤ при ε = 0 побег качества РЕАЛЕН — точная
    противоположность полиномиального `polynomial_abc_no_escape`.
    ЧЕСТНО: против настоящего abc (ε > 0) это семейство НЕ работает и работать
    не обязано — вся открытость гейта живёт в ε-слабине. -/
theorem unboundedQualitySupplyExponentOne : UnboundedQualitySupplyExponentOne := by
  intro K
  obtain ⟨m, hm, hEq⟩ := three_pow_two_pow_eq_two_pow_mul_add_one K
  refine ⟨1, 2 ^ (K + 3) * m, 3 ^ 2 ^ (K + 1), Nat.one_pos,
    mul_pos (pow_pos (by norm_num) (K + 3)) hm, ?_,
    Nat.coprime_one_left _, ?_⟩
  · rw [hEq]; exact Nat.add_comm 1 _
  · -- K · rad(1·b·c) < c для b = 2^(K+3)·m, c = 3^(2^(K+1)) = b + 1
    have hbc : Nat.Coprime (2 ^ (K + 3) * m) (3 ^ 2 ^ (K + 1)) := by
      rw [hEq]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    have hcrad : natRad (3 ^ 2 ^ (K + 1)) = 3 := by
      rw [natRad_pow 3 (pow_ne_zero _ (by norm_num)),
        natRad_prime Nat.prime_three]
    have h2rad : natRad (2 ^ (K + 3)) = 2 := by
      rw [natRad_pow 2 (by omega : K + 3 ≠ 0), natRad_prime Nat.prime_two]
    -- rad(b) ≤ 2·m: субмультипликативность + rad(2^(K+3)) = 2 + rad(m) ≤ m
    have hbrad : natRad (2 ^ (K + 3) * m) ≤ 2 * m := by
      have hd : natRad (2 ^ (K + 3) * m) ∣ natRad (2 ^ (K + 3)) * natRad m :=
        natRad_mul_dvd _ _
      rw [h2rad] at hd
      have hle : natRad (2 ^ (K + 3) * m) ≤ 2 * natRad m :=
        Nat.le_of_dvd (mul_pos (by norm_num) (natRad_pos m)) hd
      exact hle.trans (Nat.mul_le_mul (Nat.le_refl 2) (natRad_le_self hm.ne'))
    -- строгий шаг горизонта: 6K < 2^(K+3) (из K < 2^K)
    have h6K : 6 * K < 2 ^ (K + 3) := by
      have h1 : K < 2 ^ K := Nat.lt_two_pow_self
      calc 6 * K ≤ 8 * K := Nat.mul_le_mul (by norm_num) (Nat.le_refl K)
        _ < 8 * 2 ^ K := mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 2 ^ (K + 3) := by rw [pow_add]; ring
    rw [one_mul, natRad_mul_of_coprime hbc, hcrad]
    calc K * (natRad (2 ^ (K + 3) * m) * 3)
        ≤ K * (2 * m * 3) :=
          Nat.mul_le_mul (Nat.le_refl K) (Nat.mul_le_mul hbrad (Nat.le_refl 3))
      _ = 6 * K * m := by ring
      _ < 2 ^ (K + 3) * m := mul_lt_mul_of_pos_right h6K hm
      _ < 2 ^ (K + 3) * m + 1 := Nat.lt_succ_self _
      _ = 3 ^ 2 ^ (K + 1) := hEq.symm

/-!
################################################################################
  (в) 🟢 Полиномиальное зеркало стрелки abc ⟹ FLT
################################################################################
-/

section PolynomialShadow

open Polynomial

/-- **🟢 ТЕНЬ FLT НА ПОЛИНОМАХ (ДОКАЗАНО; полиномиальное зеркало стрелки
    abc ⟹ FLT).** Над полем `k` с `(n : k) ≠ 0`, `n ≥ 3`: взаимно простые
    ненулевые `a, b, c : k[X]` с `a^n + b^n = c^n` вынуждены быть константами.
    Чистая цитата РЕАЛЬНОЙ `Polynomial.flt` (Mathlib/NumberTheory/FLT/Polynomial.lean);
    mathlib выводит её из `Polynomial.flt_catalan`, а ту — из Мейсона–Стотерса
    `Polynomial.abc` (наш зелёный якорь `polynomial_abc_shadow`).
    ЧЕСТНО: на полиномах стрелка «abc-мир ⟹ FLT» зелёная; на ℤ та же стрелка
    заперта за красным гейтом `AbcConjecture` и здесь НЕ заявляется
    (`noPolynomialToIntegerAbcClaimed`). Первый мост abc-фронта к соседней
    FLT-ветви (`BealFront.polynomial_fermat_catalan_shadow` — каталановская форма;
    здесь — именно FLT-спецслучай). -/
theorem polynomial_flt_shadow
    {k : Type*} [Field k]
    {n : ℕ} (hn : 3 ≤ n) (chn : (n : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  Polynomial.flt hn chn ha hb hc hab heq

end PolynomialShadow

/-!
################################################################################
  (г) 🟢 Эпистемическая связка (стиль PNPFirstCause) — для НАИВНОЙ ε = 0-формы
################################################################################
-/

namespace Epistemic

/-- **Равномерный линейный закон качества при ε = 0** (наивное ε = 0-усиление
    abc): ОДНА константа `K` линейно заземляет все взаимно простые тройки —
    `c ≤ K·rad(a·b·c)`. ЧЕСТНО: это НЕ гейт `AbcConjecture` (там `K(ε)` при
    показателе `1 + ε`, ε > 0) — это его наивная линейная форма, и ровно она
    ниже опровергается зелёно. -/
def LinearAbcLaw (K : ℕ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
    c ≤ K * natRad (a * b * c)

/-- **🟢 (ДОКАЗАНО): наивный закон `K = 1` опровергнут одним свидетелем** —
    тройкой `1 + 8 = 9` из `abc_exponent_one_counterexample`. -/
theorem naiveAbcLaw_refuted : ¬ LinearAbcLaw 1 := by
  intro hlaw
  obtain ⟨a, b, c, ha, hb, hsum, hcop, hlt⟩ := abc_exponent_one_counterexample
  have hle : c ≤ 1 * natRad (a * b * c) := hlaw a b c ha hb hsum hcop
  rw [one_mul] at hle
  exact absurd hle (not_le.mpr hlt)

/-- **🟢 ПИЖОНХОЛ-ИНСТАНЦИАЦИЯ (несущая, зеркало `no_fullPayment_of_unboundedSupply`
    у P/NP):** неограниченная поставка качества несовместима с ЛЮБЫМ равномерным
    линейным законом — поставка в горизонте `K` бьёт закон `K` в лоб.
    Оба аргумента грузонесущие: лемма параметризована поставкой (CORR-стиль
    Чоулы), а не зашита под доказанный факт. -/
theorem no_linearAbcLaw_of_unboundedSupply
    (hsup : UnboundedQualitySupplyExponentOne)
    (hlaw : ∃ K : ℕ, LinearAbcLaw K) : False := by
  obtain ⟨K, hK⟩ := hlaw
  obtain ⟨a, b, c, ha, hb, hsum, hcop, hlt⟩ := hsup K
  exact absurd (hK a b c ha hb hsum hcop) (not_le.mpr hlt)

/-- **🟢 (ДОКАЗАНО): линейного закона качества НЕТ ни при каком `K`** —
    оплачено доказанной поставкой `unboundedQualitySupplyExponentOne`.
    ЧЕСТНО: опровергнута НАИВНАЯ (ε = 0) форма; настоящий гейт `AbcConjecture`
    (ε > 0) не тронут — там такой поставки нет и быть не обязано. -/
theorem no_linearAbcLaw (K : ℕ) : ¬ LinearAbcLaw K :=
  fun hK => no_linearAbcLaw_of_unboundedSupply
    unboundedQualitySupplyExponentOne ⟨K, hK⟩

/-- **Внутреннее самообоснование линейного заземления качества.** Машина
    одновременно (a) держит равномерный линейный закон качества для КАКОГО-ТО
    горизонта `K` (`ground`) и (b) видит собственную неограниченную поставку
    качества за ВСЯКИЙ горизонт (`beyondOwnHorizon`).
    ЧЕСТНОСТЬ (обязательная, Чоула/PNP-стиль): `beyondOwnHorizon` — ДОКАЗУЕМЫЙ
    зелёный факт (`unboundedQualitySupplyExponentOne`), поэтому структура
    семантически эквивалентна паре «закон ∧ ¬закон»
    (`internalisedAbcGround_semantically_selfNegating` ниже). Содержательность
    живёт в ОПЛАТЕ контрадикции: индукция `2^(k+3) ∣ 3^(2^(k+1)) − 1` +
    мультипликативность радикала + пижонхол `no_linearAbcLaw_of_unboundedSupply`.
    И это эпистемика НАИВНОЙ ε = 0-формы: про сам `AbcConjecture` — ничего. -/
structure InternalisedAbcGround : Prop where
  ground : ∃ K : ℕ, LinearAbcLaw K
  beyondOwnHorizon : UnboundedQualitySupplyExponentOne

/-- «Внутреннее знание причины abc» = внутреннее самообоснование линейного
    заземления качества (наивная ε = 0-форма). -/
abbrev InternalKnowledgeOfAbcCause : Prop := InternalisedAbcGround

/-- **🟢 Самообоснование самоуничтожается** — оба поля грузонесущие: `ground`
    даёт горизонт `K`, `beyondOwnHorizon` бьёт ровно его (пижонхол
    `no_linearAbcLaw_of_unboundedSupply`, НЕ ex falso). ЗЕЛЁНАЯ. -/
theorem no_internalisedAbcGround : InternalisedAbcGround → False :=
  fun H => no_linearAbcLaw_of_unboundedSupply H.beyondOwnHorizon H.ground

/-- **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `pnpCause_unknowable`,
    `collatzCause_unknowable`, `twinNode_unknowable`): внутреннее линейное
    самообоснование качества невозможно. ЗЕЛЁНАЯ, без гипотез.
    ЧЕСТНАЯ ОГОВОРКА (обязательная): это эпистемика НАИВНОЙ формы (ε = 0);
    настоящий abc-гейт (`AbcConjecture`, ε > 0) этим НЕ решается, НЕ
    опровергается и никак НЕ затрагивается — для него аналогичная связка
    вырождается (Стюарт–Тайдеман: известны лишь субполиномиальные побеги;
    неограниченная (1+ε)-поставка противоречила бы самому abc). -/
theorem abcCause_unknowable : ¬ InternalKnowledgeOfAbcCause :=
  no_internalisedAbcGround

/-- **Самообоснование — семантически «закон ∧ ¬закон» (машинная честность,
    зеркало `internalisedPNPGround_semantically_selfNegating`):** поскольку
    `beyondOwnHorizon` доказуем, поля — доказуемо точные дополнения, и структура
    эквивалентна контрадикторной паре. Содержательность живёт НЕ в форме, а в
    оплате: семейство `3^(2^(k+1))` + мультипликативность радикала + пижонхол.
    Обратная стрелка — ex falso (честно). -/
theorem internalisedAbcGround_semantically_selfNegating :
    InternalisedAbcGround ↔
      ((∃ K : ℕ, LinearAbcLaw K) ∧ ¬ (∃ K : ℕ, LinearAbcLaw K)) :=
  ⟨fun H => ⟨H.ground, no_linearAbcLaw_of_unboundedSupply H.beyondOwnHorizon⟩,
   fun h => (h.2 h.1).elim⟩

/-- Итоговый эпистемический статус abc-горизонта (зеркало
    `pnp_locked_behind_engine_status`, БЕЗ декрет-конъюнкта — у abc границы в
    `step00FirstCause` нет и не должно быть): поставка качества при ε = 0
    неограниченна (теорема) / линейного закона нет ни при каком `K` (теорема) /
    внутреннее самообоснование невозможно (теорема) / импликация «полиномиальный
    abc ⟹ целочисленный» честно НЕ заявлена (маркер; сам красный гейт
    `AbcConjecture` живёт в AbcFront и остаётся ОТКРЫТЫМ). Полиномиальная
    сторона пары — `polynomial_abc_no_escape` (побег запрещён) против
    `unboundedQualitySupplyExponentOne` (на ℤ при ε = 0 побег РЕАЛЕН). -/
theorem abc_locked_behind_engine_status :
    UnboundedQualitySupplyExponentOne ∧
    (∀ K : ℕ, ¬ LinearAbcLaw K) ∧
    (¬ InternalKnowledgeOfAbcCause) ∧
    NoPolynomialToIntegerAbcClaimed :=
  ⟨unboundedQualitySupplyExponentOne, no_linearAbcLaw, abcCause_unknowable,
   noPolynomialToIntegerAbcClaimed⟩

end Epistemic

/-!
################################################################################
  ИТОГ (LOUD HONEST)

  🟢 ДОКАЗАНО ЗДЕСЬ (стандартная тройка аксиом):
     · инструментарий: natRad_pow, natRad_mul_of_coprime, natRad_mul_dvd, natRad_prime;
     · наивный abc (ε = 0) ложен: abc_exponent_one_counterexample (1+8=9),
       наивный закон K=1 опровергнут (naiveAbcLaw_refuted);
     · поставка качества неограниченна: unboundedQualitySupplyExponentOne
       (семейство 3^(2^(k+1)), индукция two_pow_dvd_three_pow_two_pow_sub_one);
     · линейного закона нет ни при каком K (no_linearAbcLaw);
     · полиномиальное зеркало abc ⟹ FLT: polynomial_flt_shadow (цитата Polynomial.flt);
     · эпистемика наивной формы: no_internalisedAbcGround, abcCause_unknowable,
       internalisedAbcGround_semantically_selfNegating, abc_locked_behind_engine_status.

  🔴 НЕ ТРОНУТО (открыто, как и было): AbcConjecture (целочисленный abc, ε > 0).
     Эпистемическая связка выше — про НАИВНУЮ ε = 0-форму; для настоящего гейта
     она вырождается (Стюарт–Тайдеман), и мы этого НЕ скрываем.

  Никакого sorry / native_decide / новой аксиомы; карантин не импортирован;
  таинт 47 неизменен.
################################################################################
-/

#print axioms natRad_pow
#print axioms natRad_mul_of_coprime
#print axioms natRad_mul_dvd
#print axioms natRad_prime
#print axioms abc_exponent_one_counterexample
#print axioms three_pow_two_pow_eq_two_pow_mul_add_one
#print axioms two_pow_dvd_three_pow_two_pow_sub_one
#print axioms unboundedQualitySupplyExponentOne
#print axioms polynomial_flt_shadow
#print axioms Epistemic.naiveAbcLaw_refuted
#print axioms Epistemic.no_linearAbcLaw_of_unboundedSupply
#print axioms Epistemic.no_linearAbcLaw
#print axioms Epistemic.no_internalisedAbcGround
#print axioms Epistemic.abcCause_unknowable
#print axioms Epistemic.internalisedAbcGround_semantically_selfNegating
#print axioms Epistemic.abc_locked_behind_engine_status

end EuclidsPath.AbcFront
