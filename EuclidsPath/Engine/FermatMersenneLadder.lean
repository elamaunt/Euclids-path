/-
  FermatMersenneLadder — арифметическая лестница Ферма ↔ Мерсенн:
  чётность индекса Ферма-близнецов, фрагмент эвристики §16 и
  мультипликативный мост между двумя ветвями.

  ЧТО ДОКАЗАНО (mathlib Nat.fermatNumber + mersenne, стандартные аксиомы,
  без sorry, без native_decide, карантин НЕ импортируется):

    (а) ЧЁТНОСТЬ ИНДЕКСА ФЕРМА-БЛИЗНЕЦОВ:
      * two_pow_mod_three_of_odd — 2^k ≡ 2 (mod 3) при нечётном k;
      * seven_dvd_fermatNumber_add_two_of_odd — 7 ∣ F_k + 2 при нечётном k
        (2^k ≡ 2 mod 3 ⟹ 2^(2^k) ≡ 4 mod 7 ⟹ F_k + 2 ≡ 0 mod 7);
        ⚠️ ОГОВОРКА k = 1: делимость выполняется и там, но F₁ + 2 = 7 —
        САМО простое, поэтому пара (5, 7) выживает; убивает делимость
        только при k ≥ 2 (тогда F_k + 2 > 7);
      * fermatNumber_add_two_not_prime_of_odd — при нечётном k ≥ 2 старший
        член F_k + 2 составной;
      * fermat_twin_index_eq_one_or_even — twin-центр Ферма возможен лишь
        при k = 1 или чётном k: ПОЛОВИНА индексов выбывает зелёно, домен
        свидетеля FermatTwinAbsenceAbove сужается вдвое;
      * fermat_twin_non_instance_of_parity — k = 3 (259 = 7·37) теперь
        СЛЕДСТВИЕ общего закона (ранее отдельная проверка
        FermatBranch.fermat_twin_non_instance).

    (б) ФРАГМЕНТ ЭВРИСТИКИ §16 (до сих пор жил ТОЛЬКО комментарием в
        CausalClosureAxiom:2606 и MersenneManifestationFront:35):
      * five_dvd_two_pow_sub_three_of_three_mod_four — 5 ∣ 2^p − 3 при
        p ≡ 3 (mod 4); зеркало жемчужины sophieGermain_divides_mersenne;
        ⚠️ ОГОВОРКА p = 3: 2³ − 3 = 5 делится на 5 И само просто —
        пара (5, 7) выживает; убивает только при p > 3;
      * two_pow_sub_three_not_prime_of_three_mod_four — при p > 3,
        p ≡ 3 (mod 4) число 2^p − 3 составное;
      * mersenneTwin_exponent_one_mod_four — показатель Мерсенн-близнеца
        выше p = 3 обязан быть ≡ 1 (mod 4): отказ §16 от декрета
        mersenneBoundary получает зелёное обоснование ВНУТРИ репо;
      * mersenne_twin_non_instance_seven — p = 7 не даёт пары (125 = 5³).

    (в) МУЛЬТИПЛИКАТИВНЫЙ МОСТ МЕЖДУ ВЕТВЯМИ:
      * mersenne_two_pow_eq_prod_fermatNumber — mersenne (2^n) = ∏_{k<n} F_k
        (телескоп (x−1)(x+1) = x²−1; переписывание Nat.prod_fermatNumber);
        минус-сторона сетки (Мерсенн) — произведение плюс-сторон (Ферма);
      * mersenne_two_pow_not_prime — при n ≥ 2 число mersenne (2^n)
        составное (делится на F₀ = 3): машинно видно, почему домен
        MersenneTwinAbsenceAbove фактически пробегает лишь простые p.
      ЧЕСТНОСТЬ (анти-дубль): обёртка «(mersenne n).Prime → n.Prime» НЕ
      заявляется — факт уже потребляется инлайн через
      Nat.prime_of_pow_sub_one_prime в PerfectNumberBranch.lean:136-138;
      именованный дубль запрещён вердиктом скептика.

    (г) ГОЛЬДБАХОВА ВЗАИМНАЯ ПРОСТОТА В ЯЗЫКЕ МОСТА:
      * fermatNumber_index_eq_of_prime_dvd — простое делит НЕ БОЛЕЕ одного
        числа Ферма (попарная взаимная простота,
        Nat.coprime_fermatNumber_fermatNumber — письмо Гольдбаха Эйлеру);
      * mersenne_two_pow_prime_dvd_iff — простые делители mersenne (2^n) =
        в точности простые делители чисел Ферма F₀ … F_{n−1};
      * mersenne_two_pow_prime_divisor_unique — каждый простой делитель
        mersenne (2^n) делит РОВНО ОДНО число Ферма: лестница слоёв
        не пересекается.

  ЧЕСТНОСТЬ (рамка). Это НЕ решение вопроса о бесконечности Ферма- или
  Мерсенн-близнецов и НЕ Гёдель — только элементарная модулярная
  арифметика, зелёно сужающая ОТКРЫТЫЕ входы FermatTwinCentersUnbounded /
  MersenneTwinCentersUnbounded: половина индексов Ферма и половина нечётных
  показателей Мерсенна выбывают. Всё оплачено kernel-вычислением по модулям
  3, 5, 7 (Nat.pow_mod) и готовыми фактами mathlib; новых аксиом нет,
  таинт репозитория не меняется.
-/
import Mathlib
import EuclidsPath.Engine.FermatBranch
import EuclidsPath.Engine.MersenneBranch

set_option autoImplicit false

namespace EuclidsPath.FermatMersenneLadder

open EuclidsPath
open EuclidsPath.FermatBranch
open EuclidsPath.MersenneBranch

/-! ## (а) Чётность индекса Ферма-близнецов: 7 ∣ F_k + 2 при нечётном k -/

/-- Период 2 по модулю 3: при нечётном `k` имеем `2^k ≡ 2 (mod 3)`
    (`2 ≡ −1`, нечётная степень остаётся `−1`). -/
theorem two_pow_mod_three_of_odd {k : ℕ} (hk : Odd k) : 2 ^ k % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hk
  have h4 : 4 ^ m % 3 = 1 := by
    have h := Nat.pow_mod 4 m 3
    simpa using h
  have hexp : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num [mul_comm]
  rw [hexp]
  omega

/-- **ЧЁТНОСТЬ ИНДЕКСА (доказано): `7 ∣ F_k + 2` при нечётном `k`.**
    Маршрут: `2^n mod 7` имеет цикл 3 (`2, 4, 1`); при нечётном `k`
    показатель `2^k ≡ 2 (mod 3)`, значит `2^(2^k) ≡ 4 (mod 7)` и
    `F_k + 2 = 2^(2^k) + 3 ≡ 0 (mod 7)`.
    ⚠️ ОГОВОРКА `k = 1`: делимость верна и там (`F₁ + 2 = 7`), но 7 —
    САМО простое, поэтому пара `(5, 7)` выживает; составность старшего
    члена начинается с `k ≥ 2` (см. следующую теорему). -/
theorem seven_dvd_fermatNumber_add_two_of_odd {k : ℕ} (hk : Odd k) :
    7 ∣ Nat.fermatNumber k + 2 := by
  have h3 := two_pow_mod_three_of_odd hk
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = 3 * q + 2 := ⟨2 ^ k / 3, by omega⟩
  have h8 : 8 ^ q % 7 = 1 := by
    have h := Nat.pow_mod 8 q 7
    simpa using h
  have hpow : (2 : ℕ) ^ 2 ^ k = 8 ^ q * 4 := by
    rw [hq, pow_add, pow_mul]
    norm_num
  have h7 : 2 ^ 2 ^ k % 7 = 4 := by
    rw [hpow, Nat.mul_mod, h8]
  show 7 ∣ 2 ^ 2 ^ k + 1 + 2
  omega

/-- При нечётном `k ≥ 2` старший член кандидата в пару, `F_k + 2`,
    СОСТАВНОЙ: он делится на 7 и строго больше 7 (`F_k ≥ F_2 = 17`). -/
theorem fermatNumber_add_two_not_prime_of_odd {k : ℕ} (hk : Odd k) (h2 : 2 ≤ k) :
    ¬ (Nat.fermatNumber k + 2).Prime := by
  intro hP
  have hdvd : 7 ∣ Nat.fermatNumber k + 2 := seven_dvd_fermatNumber_add_two_of_odd hk
  have hge : Nat.fermatNumber 2 ≤ Nat.fermatNumber k := Nat.fermatNumber_mono h2
  rw [Nat.fermatNumber_two] at hge
  rcases hP.eq_one_or_self_of_dvd 7 hdvd with h | h <;> omega

/-- **СУЖЕНИЕ ОТКРЫТОГО ВХОДА (доказано):** twin-центр Ферма возможен лишь
    при `k = 1` или ЧЁТНОМ `k` — половина индексов выбывает зелёно, домен
    свидетеля `FermatTwinAbsenceAbove` сужается вдвое. Машинное подкрепление
    тезиса §17 об инвертированном знаке эвристики (до сих пор он держался
    на прозе). НЕ утверждается ничего о чётных `k` — там вопрос ОТКРЫТ. -/
theorem fermat_twin_index_eq_one_or_even {k : ℕ} (hk : 1 ≤ k)
    (htwin : IsTwinCenter (fermatCenter k)) : k = 1 ∨ Even k := by
  rcases Nat.even_or_odd k with he | ho
  · exact Or.inr he
  · left
    by_contra hne
    have h2 : 2 ≤ k := by
      obtain ⟨m, hm⟩ := ho
      omega
    have hpair := (isTwinCenter_fermatCenter_iff hk).mp htwin
    exact fermatNumber_add_two_not_prime_of_odd ho h2 hpair.2

/-- Провал `k = 3` (259 = 7·37) — теперь СЛЕДСТВИЕ общего закона чётности,
    а не отдельная числовая проверка (`FermatBranch.fermat_twin_non_instance`
    доказывал то же прямым вычислением). -/
theorem fermat_twin_non_instance_of_parity :
    ¬ IsTwinCenter (fermatCenter 3) := by
  intro h
  rcases fermat_twin_index_eq_one_or_even (by norm_num) h with h1 | he
  · norm_num at h1
  · have h32 := Nat.even_iff.mp he
    omega

/-! ## (б) Фрагмент эвристики §16: 5 ∣ 2^p − 3 при p ≡ 3 (mod 4) -/

/-- **ФРАГМЕНТ ЭВРИСТИКИ §16 (доказано): `5 ∣ 2^p − 3` при `p ≡ 3 (mod 4)`.**
    `2^n mod 5` имеет цикл 4 (`2, 4, 3, 1`); при `p ≡ 3` получаем
    `2^p ≡ 3 (mod 5)`. До этой леммы факт жил ТОЛЬКО комментарием
    (CausalClosureAxiom:2606, MersenneManifestationFront:35) — отказ §16 от
    декрета `mersenneBoundary` теперь обоснован зелёно внутри репо.
    Зеркало жемчужины `sophieGermain_divides_mersenne`.
    ⚠️ ОГОВОРКА `p = 3`: `2³ − 3 = 5` делится на 5 И само просто —
    пара `(5, 7)` выживает; составность начинается с `p > 3`. -/
theorem five_dvd_two_pow_sub_three_of_three_mod_four {p : ℕ} (hp : p % 4 = 3) :
    5 ∣ 2 ^ p - 3 := by
  obtain ⟨q, hq⟩ : ∃ q, p = 4 * q + 3 := ⟨p / 4, by omega⟩
  have h16 : 16 ^ q % 5 = 1 := by
    have h := Nat.pow_mod 16 q 5
    simpa using h
  have hpow : (2 : ℕ) ^ p = 16 ^ q * 8 := by
    rw [hq, pow_add, pow_mul]
    norm_num
  have h5 : 2 ^ p % 5 = 3 := by
    rw [hpow, Nat.mul_mod, h16]
  have hge : 8 ≤ 2 ^ p := by
    rw [hpow]
    have h1 : 1 ≤ 16 ^ q := Nat.one_le_pow _ _ (by norm_num)
    omega
  omega

/-- При `p > 3`, `p ≡ 3 (mod 4)` число `2^p − 3` СОСТАВНОЕ: делится на 5
    и строго больше 5 (`2^p ≥ 2^7 = 128`). -/
theorem two_pow_sub_three_not_prime_of_three_mod_four {p : ℕ}
    (hp : p % 4 = 3) (h3 : 3 < p) : ¬ (2 ^ p - 3).Prime := by
  intro hP
  have hdvd := five_dvd_two_pow_sub_three_of_three_mod_four hp
  have hge : 128 ≤ 2 ^ p := by
    calc (128 : ℕ) = 2 ^ 7 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hP.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega

/-- **СУЖЕНИЕ ВТОРОГО ОТКРЫТОГО ВХОДА (доказано):** показатель
    Мерсенн-близнеца выше `p = 3` обязан быть `≡ 1 (mod 4)` — половина
    нечётных показателей выбывает зелёно (согласуется с известными
    инстансами: p = 5 ≡ 1, а p = 3 — граничное исключение `2³−3 = 5`).
    Гипотеза `Odd p` обязательна: критерий
    `isTwinCenter_mersenneCenter_iff` осмыслен лишь на нечётной сетке
    (при чётном p центр `m_p` — артефакт целочисленного деления). -/
theorem mersenneTwin_exponent_one_mod_four {p : ℕ} (hodd : Odd p) (h3 : 3 < p)
    (htwin : IsTwinCenter (mersenneCenter p)) : p % 4 = 1 := by
  have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h | h
  · exact h
  · exfalso
    have hpair := (isTwinCenter_mersenneCenter_iff hodd (by omega)).mp htwin
    exact two_pow_sub_three_not_prime_of_three_mod_four h h3 hpair.1

/-- Провал `p = 7` (2⁷ − 3 = 125 = 5³) — следствие закона `≡ 1 (mod 4)`;
    дополняет инстансы `mersenne_twin_instances` (p = 3, 5) с другой стороны. -/
theorem mersenne_twin_non_instance_seven :
    ¬ IsTwinCenter (mersenneCenter 7) := by
  intro h
  have h1 := mersenneTwin_exponent_one_mod_four ⟨3, by norm_num⟩ (by norm_num) h
  omega

/-! ## (в) Мост: mersenne (2^n) = произведение чисел Ферма -/

/-- **МУЛЬТИПЛИКАТИВНЫЙ МОСТ ВЕТВЕЙ (доказано):**
    `mersenne (2^n) = ∏_{k<n} F_k` — телескоп `(x−1)(x+1) = x²−1`,
    переписанный из `Nat.prod_fermatNumber` в язык ветви Мерсенна.
    Минус-сторона сетки (`2^(2^n) − 1`) — произведение плюс-сторон
    (`2^(2^k) + 1`): первый содержательный зелёный мост между ветвями.
    ФОРМАЛЬНАЯ СВЯЗКА: оплачена готовой индукцией mathlib
    (`Nat.prod_fermatNumber`) + kernel-переписыванием определений. -/
theorem mersenne_two_pow_eq_prod_fermatNumber (n : ℕ) :
    mersenne (2 ^ n) = ∏ k ∈ Finset.range n, Nat.fermatNumber k := by
  rw [Nat.prod_fermatNumber]
  show 2 ^ 2 ^ n - 1 = 2 ^ 2 ^ n + 1 - 2
  omega

/-- При `n ≥ 2` число `mersenne (2^n)` СОСТАВНОЕ (делится на `F₀ = 3` и
    строго больше: `mersenne (2^n) ≥ mersenne 4 = 15`). Машинно видно,
    почему домен `MersenneTwinAbsenceAbove` фактически пробегает лишь
    ПРОСТЫЕ показатели: степенные показатели зелёно выбывают.
    ЧЕСТНОСТЬ (анти-дубль): общая обёртка `(mersenne n).Prime → n.Prime`
    сознательно НЕ заявляется — она уже потребляется инлайн через
    `Nat.prime_of_pow_sub_one_prime` в PerfectNumberBranch.lean:136-138. -/
theorem mersenne_two_pow_not_prime {n : ℕ} (hn : 2 ≤ n) :
    ¬ (mersenne (2 ^ n)).Prime := by
  intro hP
  have h3 : (3 : ℕ) ∣ mersenne (2 ^ n) := by
    rw [mersenne_two_pow_eq_prod_fermatNumber]
    simpa using
      Finset.dvd_prod_of_mem Nat.fermatNumber
        (Finset.mem_range.mpr (show 0 < n by omega))
  have h4 : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hge : 15 ≤ mersenne (2 ^ n) := by
    calc (15 : ℕ) = mersenne 4 := by norm_num [mersenne]
    _ ≤ mersenne (2 ^ n) := mersenne_le_mersenne.mpr h4
  rcases hP.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega

/-! ## (г) Гольдбахова взаимная простота в языке моста -/

/-- **ЕДИНСТВЕННОСТЬ СЛОЯ (доказано):** простое число делит НЕ БОЛЕЕ одного
    числа Ферма — прямое следствие попарной взаимной простоты
    (`Nat.coprime_fermatNumber_fermatNumber`, письмо Гольдбаха Эйлеру 1730). -/
theorem fermatNumber_index_eq_of_prime_dvd {q i j : ℕ} (hq : q.Prime)
    (hi : q ∣ Nat.fermatNumber i) (hj : q ∣ Nat.fermatNumber j) : i = j := by
  by_contra hne
  have hco : Nat.Coprime (Nat.fermatNumber i) (Nat.fermatNumber j) :=
    Nat.coprime_fermatNumber_fermatNumber hne
  have h1 : q ∣ Nat.gcd (Nat.fermatNumber i) (Nat.fermatNumber j) :=
    Nat.dvd_gcd hi hj
  rw [hco.gcd_eq_one] at h1
  exact hq.ne_one (Nat.dvd_one.mp h1)

/-- **МОСТ ДЕЛИТЕЛЕЙ (доказано):** простые делители `mersenne (2^n)` — это
    В ТОЧНОСТИ простые делители чисел Ферма `F₀ … F_{n−1}`. Минус-сторона
    степенного индекса не приносит НИКАКИХ новых простых: весь её запас —
    лестница Ферма. -/
theorem mersenne_two_pow_prime_dvd_iff {q n : ℕ} (hq : q.Prime) :
    q ∣ mersenne (2 ^ n) ↔ ∃ i < n, q ∣ Nat.fermatNumber i := by
  rw [mersenne_two_pow_eq_prod_fermatNumber, hq.prime.dvd_finsetProd_iff]
  simp only [Finset.mem_range]

/-- **ЛЕСТНИЦА НЕ ПЕРЕСЕКАЕТСЯ (доказано):** каждый простой делитель
    `mersenne (2^n)` делит РОВНО ОДНО число Ферма `F_i`, `i < n` —
    существование даёт мост делителей, единственность — гольдбахова
    взаимная простота. Слои лестницы несут попарно свежие простые.
    ЧЕСТНОСТЬ: это зелёный факт о ДЕЛИТЕЛЯХ; бесконечность простых
    ЧИСЕЛ Ферма остаётся красным входом (знак эвристики против — §17). -/
theorem mersenne_two_pow_prime_divisor_unique {q n : ℕ} (hq : q.Prime)
    (hdvd : q ∣ mersenne (2 ^ n)) :
    ∃! i, i < n ∧ q ∣ Nat.fermatNumber i := by
  obtain ⟨i, hi, hqi⟩ := (mersenne_two_pow_prime_dvd_iff hq).mp hdvd
  refine ⟨i, ⟨hi, hqi⟩, ?_⟩
  intro j hj
  exact fermatNumber_index_eq_of_prime_dvd hq hj.2 hqi

/-! ## Аудит аксиом: весь модуль зелёный (стандартная тройка), таинт не меняется -/
#print axioms two_pow_mod_three_of_odd
#print axioms seven_dvd_fermatNumber_add_two_of_odd
#print axioms fermatNumber_add_two_not_prime_of_odd
#print axioms fermat_twin_index_eq_one_or_even
#print axioms fermat_twin_non_instance_of_parity
#print axioms five_dvd_two_pow_sub_three_of_three_mod_four
#print axioms two_pow_sub_three_not_prime_of_three_mod_four
#print axioms mersenneTwin_exponent_one_mod_four
#print axioms mersenne_twin_non_instance_seven
#print axioms mersenne_two_pow_eq_prod_fermatNumber
#print axioms mersenne_two_pow_not_prime
#print axioms fermatNumber_index_eq_of_prime_dvd
#print axioms mersenne_two_pow_prime_dvd_iff
#print axioms mersenne_two_pow_prime_divisor_unique

end EuclidsPath.FermatMersenneLadder
