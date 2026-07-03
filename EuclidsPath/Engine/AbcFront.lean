/-
  AbcFront — «теневой двигатель» гипотезы ABC, посаженный на РЕАЛЬНУЮ доказанную
  теорему Мейсона–Стотерса (полиномиальный abc) в mathlib.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК — ЧТО ЗДЕСЬ ДОКАЗАНО И ЧТО ЧЕСТНО НЕ ДОКАЗАНО.    │
  └───────────────────────────────────────────────────────────────────────────┘

  1. 🟢 ПОЛИНОМИАЛЬНЫЙ abc ДОКАЗАН. Над полем `k` для НЕнулевых взаимно простых
     `a, b, c : k[X]` с `a + b + c = 0` теорема Мейсона–Стотерса даёт ЖЁСТКУЮ
     границу: либо степень каждого из `a, b, c` строго меньше степени радикала
     `rad(a·b·c)`, либо все три производные нулевые (вырожденный случай). Это
     ИМЕННО «двигательное чтение» abc: «качество» не может убежать в бесконечность —
     конечность/жёсткая граница встроена в саму алгебру. Мы НЕ доказываем это
     заново — мы ЦИТИРУЕМ реальную `Polynomial.abc` из
     `Mathlib/NumberTheory/FLT/MasonStothers.lean` (авторы: Jineon Baek, Seewoo Lee).
     Наш вклад — чистая обёртка `polynomial_abc_shadow`, дающая «двигательное»
     прочтение той же теоремы.

  2. 🟢 ЦЕЛОЧИСЛЕННЫЕ ОБЪЕКТЫ РЕАЛЬНЫ, НЕ ЗАГЛУШКИ. Радикал натурального числа —
     `natRad n = UniqueFactorizationMonoid.radical n` (совпадает с `Nat.radical`).
     Доказаны маленькие зелёные факты: `natRad` делит `n` (`radical_dvd_self`),
     `natRad n = ∏ p ∈ n.primeFactors, p` (`Nat.radical_eq_prod_primeFactors`),
     `0 < natRad n`. Целочисленная сторона (`Int.radical`) тоже реальна:
     `Int.radical_pos`, `Int.radical_natCast`.

  3. 🔴 ЦЕЛОЧИСЛЕННЫЙ abc ОТКРЫТ. Гипотеза ABC над ℤ (`AbcConjecture`) — это ЧЕСТНЫЙ
     именованный `Prop` над РЕАЛЬНЫМ `UniqueFactorizationMonoid.radical`, и он НЕ
     доказан. Заявление Мочидзуки (теория IUT) НЕ принято математическим
     сообществом как доказательство; премии за abc не присуждены; общего
     доказательства нет. Полиномиальный аналог формализован (это наш зелёный
     якорь) — целочисленный abc НЕ формализован и НЕ доказан.

  4. ЧЕСТНАЯ НОВИЗНА. Глубокая математика (Мейсон–Стотерс) — mathlib. Вклад модуля:
     «двигательное» прочтение доказанной полиномиальной границы + честный именованный
     шлюз для целочисленной открытой гипотезы над настоящим радикалом. Это
     ФОРМАЛИЗАЦИЯ/ЦИТИРОВАНИЕ, а НЕ доказательство abc.

  Никакого `sorry`, никакого `admit`, никакого `native_decide`, никакой новой
  аксиомы. Зелёные обёртки — стандартная тройка (`propext` / `Classical.choice` /
  `Quot.sound`). Шлюз `AbcConjecture` — это `def : Prop`, он НЕ доказывается. Такса
  репозитория (47) неизменна.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/AbcFront.lean → ноль ошибок.

  Родство: EuclidsPath/Engine/UniversalEngine.lean (`PerpetualEngine`, разделяющая
    линия управляющего — то же «двигательное» прочтение конечности/жёсткой границы).
-/
import Mathlib
import EuclidsPath.Engine.UniversalEngine

set_option autoImplicit false

namespace EuclidsPath.AbcFront

open Polynomial UniqueFactorizationMonoid

/-!
################################################################################
  🟢 ЗЕЛЁНОЕ ЯДРО — РЕАЛЬНЫЙ ЯКОРЬ: полиномиальный abc (Мейсон–Стотерс)
################################################################################
-/

/-- **🟢 ТЕНЬ abc НА ПОЛИНОМАХ (ДОКАЗАНО, Мейсон–Стотерс).**
    Над полем `k` для НЕнулевых взаимно простых `a, b, c : k[X]` с `a + b + c = 0`:
    либо степень КАЖДОГО из `a, b, c` строго меньше степени радикала `rad(a·b·c)`
    (жёсткая граница качества — «двигатель не может убежать»), либо все три
    производные нулевые (вырожденный случай).

    Это чистая обёртка над РЕАЛЬНОЙ `Polynomial.abc` из mathlib
    (`Mathlib/NumberTheory/FLT/MasonStothers.lean`): доказательство —
    `Polynomial.abc …`, мы лишь даём ему «двигательное» имя. Радикал —
    `Polynomial.radical = UniqueFactorizationMonoid.radical` на `k[X]`. -/
theorem polynomial_abc_shadow
    {k : Type*} [Field k] [DecidableEq k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree) ∨
      (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0) :=
  Polynomial.abc ha hb hc hab hsum

/-- **🟢 «Нет бесконечного побега» (двигательное прочтение).** В НЕвырожденном
    случае (хотя бы одна производная ненулевая) полиномиальный abc заставляет
    степень каждого слагаемого лежать СТРОГО НИЖЕ степени радикала произведения:
    жёсткая конечная граница, встроенная в алгебру. Тоже цитата `Polynomial.abc`. -/
theorem polynomial_abc_no_escape
    {k : Type*} [Field k] [DecidableEq k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hnondeg : ¬ (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0)) :
    a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree :=
  (polynomial_abc_shadow ha hb hc hab hsum).resolve_right hnondeg

/-!
################################################################################
  🟢 ЗЕЛЁНЫЕ ЦЕЛОЧИСЛЕННЫЕ ОБЪЕКТЫ — настоящий радикал, не заглушка
################################################################################
-/

/-- Радикал натурального числа как настоящий объект mathlib
    (`UniqueFactorizationMonoid.radical`, совпадает с `Nat.radical`). -/
noncomputable def natRad (n : ℕ) : ℕ := UniqueFactorizationMonoid.radical n

/-- **🟢 (ДОКАЗАНО):** радикал делит своё число — `natRad n ∣ n`. Цитата
    `UniqueFactorizationMonoid.radical_dvd_self`; радикал реален. -/
theorem natRad_dvd_self (n : ℕ) : natRad n ∣ n :=
  UniqueFactorizationMonoid.radical_dvd_self

/-- **🟢 (ДОКАЗАНО):** явная формула радикала — произведение простых делителей.
    Цитата `Nat.radical_eq_prod_primeFactors`. -/
theorem natRad_eq_prod_primeFactors (n : ℕ) :
    natRad n = ∏ p ∈ n.primeFactors, p :=
  Nat.radical_eq_prod_primeFactors

/-- **🟢 (ДОКАЗАНО):** положительность радикала — `0 < natRad n`. Цитата
    `Nat.radical_pos`. -/
theorem natRad_pos (n : ℕ) : 0 < natRad n :=
  Nat.radical_pos n

/-- **🟢 (ДОКАЗАНО):** для `n ≠ 0` радикал не превосходит само число — `natRad n ≤ n`.
    Цитата `Nat.radical_le_self_iff`. -/
theorem natRad_le_self {n : ℕ} (hn : n ≠ 0) : natRad n ≤ n :=
  Nat.radical_le_self_iff.mpr hn

/-- **🟢 (ДОКАЗАНО):** целочисленный радикал тоже реален — `0 < Int.radical z`.
    Цитата `Int.radical_pos`; ссылка на `Int.radical`. -/
theorem intRad_pos (z : ℤ) : 0 < UniqueFactorizationMonoid.radical z :=
  Int.radical_pos z

/-- **🟢 (ДОКАЗАНО):** согласованность целого и натурального радикалов —
    `radical (n : ℤ) = radical n`. Цитата `Int.radical_natCast`. -/
theorem intRad_natCast (n : ℕ) :
    UniqueFactorizationMonoid.radical (n : ℤ)
      = ((UniqueFactorizationMonoid.radical n : ℕ) : ℤ) :=
  Int.radical_natCast

/-!
################################################################################
  🔴 ЧЕСТНЫЙ ШЛЮЗ — ЦЕЛОЧИСЛЕННЫЙ abc (именованный Prop, НЕ доказан)
################################################################################
-/

/-- 🔴 **Гипотеза ABC (целые числа): ОТКРЫТА.** Для взаимно простых `a + b = c`
    при любом `ε > 0` число `c` ограничено `K · rad(a·b·c)^(1+ε)` с константой
    `K = K(ε)`. Радикал — РЕАЛЬНЫЙ `UniqueFactorizationMonoid.radical` на ℕ.

    ЧЕСТНО: это НЕ доказано. Заявление Мочидзуки (IUT) НЕ принято сообществом;
    премии не присуждены; общего доказательства нет. Полиномиальный аналог
    (Мейсон–Стотерс) доказан и процитирован выше как зелёный якорь — но
    целочисленный случай сюда НЕ переносится. Это `def : Prop`, мы его НЕ
    доказываем и НЕ используем как факт. -/
def AbcConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c →
    Nat.Coprime a b →
      (c : ℝ) ≤ K * ((UniqueFactorizationMonoid.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- **🟢 ЧЕСТНОСТЬ (охват):** мы НЕ утверждаем `AbcConjecture` как теорему и НЕ
    выводим его из полиномиального abc. Полиномиальная граница `polynomial_abc_shadow`
    ДОКАЗАНА; целочисленный `AbcConjecture` остаётся ОТКРЫТЫМ. Маркер того, что
    импликация «полиномиальный abc ⟹ целочисленный abc» здесь НЕ заявлена. -/
abbrev NoPolynomialToIntegerAbcClaimed : Prop := True

theorem noPolynomialToIntegerAbcClaimed : NoPolynomialToIntegerAbcClaimed := trivial

/-!
################################################################################
  ИТОГ (LOUD HONEST)
################################################################################

  🟢 РЕАЛЬНЫЙ ЯКОРЬ (цитируется, НЕ пере-выводится):
     · `Polynomial.abc` (Мейсон–Стотерс, `Mathlib/NumberTheory/FLT/MasonStothers.lean`)
       — обёрнута как `polynomial_abc_shadow` / `polynomial_abc_no_escape`;
     · `UniqueFactorizationMonoid.radical` / `Nat.radical` / `Int.radical`
       (`Mathlib/RingTheory/Radical/…`) — `natRad*`, `intRad*`.

  🟢 ГЕНУИННО НОВОЕ (в этом модуле, тонкий слой):
     · «двигательное» прочтение доказанной полиномиальной границы (нет бесконечного
       побега качества = конечность встроена в алгебру);
     · `natRad` и его маленькие зелёные факты (делимость, формула, положительность);
     · честный именованный шлюз `AbcConjecture` над НАСТОЯЩИМ радикалом.

  🔴 ОТКРЫТО (НЕ доказано, НЕ формализовано):
     · целочисленный abc (`AbcConjecture`). IUT-Мочидзуки НЕ принято; премии не
       присуждены. Это `def : Prop`, а не теорема.

  Никакого `sorry`/`admit`/`native_decide`/новой аксиомы. Такса 47 неизменна.
-/

#print axioms polynomial_abc_shadow
#print axioms polynomial_abc_no_escape
#print axioms natRad_dvd_self
#print axioms natRad_eq_prod_primeFactors
#print axioms natRad_pos
#print axioms natRad_le_self
#print axioms intRad_pos
#print axioms intRad_natCast
#print axioms noPolynomialToIntegerAbcClaimed

end EuclidsPath.AbcFront
