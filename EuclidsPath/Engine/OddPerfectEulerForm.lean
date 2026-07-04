/-
  OddPerfectEulerForm — ФЛАГМАН ЯРУСА: теорема Эйлера о нечётных совершенных числах.
  Раздел отчёта: «Совершенные числа (нечётный свидетель)».
  Соседние ступени: Engine/PerfectNumberBranch.lean (тип свидетеля, oddPerfect_ge_101),
  Engine/OddPerfectThreePrimes.lean (≥ 3 простых делителей, оценка изобилия).

  ЗЕЛЁНЫЙ МОДУЛЬ (всё доказано, без sorry/axiom/native_decide, карантин НЕ импортируется):
    * exists_unique_odd_exponent — РОВНО ОДИН простой делитель нечётного совершенного
      числа имеет нечётный показатель (ступень 1);
    * special_prime_one_mod_four — этот особый простой q ≡ 1 (mod 4) (ступень 2);
    * exponent_one_mod_four — его показатель α ≡ 1 (mod 4) (ступень 3);
    * odd_perfect_euler_form — ПОЛНАЯ ФОРМА ЭЙЛЕРА: нечётное совершенное
      n = q^α · m² с q простым, q ≡ α ≡ 1 (mod 4), q ∤ m (ступень 4);
    * oddPerfect_euler_form — та же форма в языке свидетеля OddPerfectNumber.

  МАТЕМАТИКА (Эйлер, классика XVIII века). σ(n) = 2n, и при нечётном n двойка входит
  в 2n ровно в первой степени. σ мультипликативна: σ(n) = ∏_p σ(p^{a_p}) по
  факторизации. Для нечётного p сумма σ(p^a) = 1 + p + … + p^a состоит из a+1
  нечётных слагаемых, потому чётна ⟺ a нечётен. Значит нечётный показатель ровно
  у ОДНОГО простого q (нуль дал бы нечётное σ(n), два дали бы 4 ∣ σ(n) = 2n —
  обе ветви ломают нечётность n). Остальные показатели чётны — их часть собирается
  в полный квадрат m². Для самого q: σ(q^α) ∣ 2n влечёт σ(q^α) ≡ 2 (mod 4); если бы
  q ≡ 3 (mod 4), пары q^{2i} + q^{2i+1} давали бы 1 + 3 ≡ 0 (mod 4) — вся сумма
  делилась бы на 4 (беззнаковая форма: ∑_{i<2t} q^i = (1+q)·∑_{j<t} (q²)^j и
  4 ∣ 1+q); значит q ≡ 1 (mod 4), и тогда σ(q^α) ≡ α + 1 (mod 4) даёт α ≡ 1 (mod 4).

  ЧЕСТНОСТЬ: это НЕ решение проблемы нечётного совершенного числа (открыта с
  античности) и НЕ Гёдель — здесь не утверждается ни существование, ни
  несуществование свидетеля. Это доказанная КЛАССИКА об обусловленной форме
  гипотетического свидетеля: всякий он обязан быть q^α·m². Якорей-фронтов в модуле
  нет: все теоремы — безусловная арифметика, оплаченная mathlib-мультипликативностью
  σ₁ (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul,
  sigma_one_apply_prime_pow) и mod-2/mod-4 счётом. Таинт 47 не меняется.
-/
import Mathlib
import EuclidsPath.Engine.OddPerfectThreePrimes

set_option autoImplicit false

namespace EuclidsPath.PerfectNumberBranch

/-! ### Кирпичи: геометрические суммы по модулям 2 и 4 -/

/-- Сумма степеней нечётного `p` по модулю 2 — это число слагаемых по модулю 2:
    каждое `p^i` нечётно. -/
private theorem sum_pow_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  have h1 : (∑ i ∈ Finset.range k, p ^ i % 2) = ∑ _i ∈ Finset.range k, 1 :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.pow_mod, hp, one_pow]; omega
  rw [Finset.sum_nat_mod, h1]
  simp

/-- Сумма степеней `p ≡ 1 (mod 4)` по модулю 4 — это число слагаемых по модулю 4:
    каждое `p^i ≡ 1 (mod 4)`. -/
private theorem sum_pow_mod_four {p : ℕ} (hp : p % 4 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 4 = k % 4 := by
  have h1 : (∑ i ∈ Finset.range k, p ^ i % 4) = ∑ _i ∈ Finset.range k, 1 :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.pow_mod, hp, one_pow]; omega
  rw [Finset.sum_nat_mod, h1]
  simp

/-- Спаривание геометрической суммы чётной длины: `∑_{i<2m} p^i = (1+p)·∑_{j<m} (p²)^j`.
    Именно эта беззнаковая факторизация несёт «пары q^{2i}+q^{2i+1}» из маршрута Эйлера. -/
private theorem sum_pow_two_mul (p m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), p ^ i
      = (1 + p) * ∑ j ∈ Finset.range m, (p ^ 2) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-! ### σ-фактор простого делителя в факторизационном разложении -/

/-- σ₁-фактор простого `p` в разложении `σ₁(n) = ∏_p σ₁(p^{a_p})`:
    сумма `1 + p + … + p^{a_p}` по показателю факторизации. -/
private def sigmaFactor (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i

/-- Чётность σ-фактора нечётного простого управляется показателем:
    `σ₁(p^a) ≡ a + 1 (mod 2)`. -/
private theorem sigmaFactor_mod_two {n p : ℕ} (hp : p % 2 = 1) :
    sigmaFactor n p % 2 = (n.factorization p + 1) % 2 :=
  sum_pow_mod_two hp _

/-- Мультипликативное разложение совершенности: `∏_p σ₁(p^{a_p}) = 2n`
    (факторизационная форма `σ₁(n) = 2n`). -/
private theorem perfect_prod_sigmaFactor {n : ℕ} (hn : n ≠ 0) (hperf : Nat.Perfect n) :
    ∏ p ∈ n.primeFactors, sigmaFactor n p = 2 * n := by
  have hσ : ArithmeticFunction.sigma 1 n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn)).mp hperf
  have hfac : ArithmeticFunction.sigma 1 n
      = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    simpa using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) hn
  rw [← hσ, hfac]
  rfl

/-- Всякий простой делитель нечётного числа нечётен. -/
private theorem primeFactor_mod_two {n : ℕ} (hodd : Odd n) {p : ℕ}
    (hp : p ∈ n.primeFactors) : p % 2 = 1 := by
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have hne2 : p ≠ 2 := by
    rintro rfl
    have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  exact Nat.odd_iff.mp (hpp.odd_of_ne_two hne2)

/-- Два простых делителя нечётного совершенного числа с нечётными показателями
    совпадают: иначе оба σ-фактора чётны и `4 ∣ 2n` — против нечётности `n`. -/
private theorem not_two_odd_exponents {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q r : ℕ} (hq : q ∈ n.primeFactors) (hr : r ∈ n.primeFactors)
    (hqodd : Odd (n.factorization q)) (hrodd : Odd (n.factorization r)) : q = r := by
  by_contra hne
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hrq : r ∈ n.primeFactors.erase q :=
    Finset.mem_erase.mpr ⟨fun h => hne h.symm, hr⟩
  have hprod := perfect_prod_sigmaFactor hn0 hperf
  rw [← Finset.mul_prod_erase n.primeFactors (sigmaFactor n) hq,
    ← Finset.mul_prod_erase (n.primeFactors.erase q) (sigmaFactor n) hrq] at hprod
  have hgq : 2 ∣ sigmaFactor n q := by
    have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hq)
    have h1 := Nat.odd_iff.mp hqodd
    omega
  have hgr : 2 ∣ sigmaFactor n r := by
    have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hr)
    have h1 := Nat.odd_iff.mp hrodd
    omega
  have h4 : 2 * 2 ∣ 2 * n := by
    rw [← hprod]
    exact mul_dvd_mul hgq (hgr.mul_right _)
  obtain ⟨t, ht⟩ := h4
  omega

/-! ### СТУПЕНЬ 1: ровно один простой с нечётным показателем -/

/-- **Ступень 1 (доказано): у нечётного совершенного числа РОВНО ОДИН простой
    делитель с нечётным показателем.** Существование: будь все показатели чётны,
    все σ-факторы были бы нечётны и `σ(n) = 2n` было бы нечётным. Единственность:
    два чётных σ-фактора дали бы `4 ∣ 2n` — против нечётности `n`
    (`not_two_odd_exponents`). НЕ решение открытой проблемы: форма гипотетического
    свидетеля. -/
theorem exists_unique_odd_exponent {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ∃! q, q ∈ n.primeFactors ∧ Odd (n.factorization q) := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hex : ∃ q, q ∈ n.primeFactors ∧ Odd (n.factorization q) := by
    by_contra hno
    push Not at hno
    have hall : ∀ p ∈ n.primeFactors, sigmaFactor n p % 2 = 1 := by
      intro p hp
      have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hp)
      have hpe : n.factorization p % 2 = 0 :=
        Nat.even_iff.mp ((Nat.even_or_odd _).resolve_right (hno p hp))
      omega
    have hprod := perfect_prod_sigmaFactor hn0 hperf
    have hone : (∏ p ∈ n.primeFactors, sigmaFactor n p) % 2 = 1 := by
      have hcong : (∏ p ∈ n.primeFactors, sigmaFactor n p % 2)
          = ∏ _p ∈ n.primeFactors, 1 := Finset.prod_congr rfl hall
      rw [Finset.prod_nat_mod, hcong]
      simp
    rw [hprod] at hone
    omega
  obtain ⟨q, hq, hqodd⟩ := hex
  exact ⟨q, ⟨hq, hqodd⟩, fun r hrpair =>
    not_two_odd_exponents hodd hperf hrpair.1 hq hrpair.2 hqodd⟩

/-! ### СТУПЕНЬ 2: особый простой q ≡ 1 (mod 4) -/

/-- Ключевой mod-4 кирпич: σ-фактор особого простого сравним с 2 по модулю 4.
    Он чётен (нечётный показатель), а `4 ∣ σ(q^α)` дало бы `4 ∣ 2n` — против
    нечётности `n`; из `σ(q^α) ∣ 2n` остаётся ровно остаток 2. -/
private theorem sigmaFactor_special_mod_four {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hqodd : Odd (n.factorization q)) :
    sigmaFactor n q % 4 = 2 := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hprod := perfect_prod_sigmaFactor hn0 hperf
  rw [← Finset.mul_prod_erase n.primeFactors (sigmaFactor n) hq] at hprod
  have hgq : sigmaFactor n q % 2 = 0 := by
    have hpar := sigmaFactor_mod_two (n := n) (primeFactor_mod_two hodd hq)
    have h1 := Nat.odd_iff.mp hqodd
    omega
  by_contra hne
  have h40 : sigmaFactor n q % 4 = 0 := by omega
  have h4 : 4 ∣ 2 * n := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h40) _
  obtain ⟨t, ht⟩ := h4
  omega

/-- **Ступень 2 (доказано): особый простой Эйлера сравним с 1 по модулю 4.**
    Будь `q ≡ 3 (mod 4)`, пары `q^{2i} + q^{2i+1} ≡ 1 + 3 ≡ 0 (mod 4)` дали бы
    `4 ∣ σ(q^α)` (беззнаковое спаривание `sum_pow_two_mul` + `4 ∣ 1+q`) — против
    `σ(q^α) ≡ 2 (mod 4)`. -/
theorem special_prime_one_mod_four {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hqodd : Odd (n.factorization q)) :
    q % 4 = 1 := by
  have hq2 : q % 2 = 1 := primeFactor_mod_two hodd hq
  have hmod4 := sigmaFactor_special_mod_four hodd hperf hq hqodd
  by_contra hne
  have hq3 : q % 4 = 3 := by omega
  obtain ⟨t, ht⟩ : ∃ t, n.factorization q + 1 = 2 * t := by
    have h1 := Nat.odd_iff.mp hqodd
    exact ⟨(n.factorization q + 1) / 2, by omega⟩
  have hfac : sigmaFactor n q = (1 + q) * ∑ j ∈ Finset.range t, (q ^ 2) ^ j := by
    unfold sigmaFactor
    rw [ht]
    exact sum_pow_two_mul q t
  have h4 : 4 ∣ sigmaFactor n q := by
    rw [hfac]
    exact dvd_mul_of_dvd_left (by omega : (4 : ℕ) ∣ 1 + q) _
  omega

/-! ### СТУПЕНЬ 3: показатель α ≡ 1 (mod 4) -/

/-- **Ступень 3 (доказано): показатель особого простого сравним с 1 по модулю 4.**
    При `q ≡ 1 (mod 4)` сумма `σ(q^α)` из `α + 1` единиц по модулю 4 даёт
    `α + 1 ≡ 2 (mod 4)`, т.е. `α ≡ 1 (mod 4)`. -/
theorem exponent_one_mod_four {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hqodd : Odd (n.factorization q)) :
    n.factorization q % 4 = 1 := by
  have hq4 : q % 4 = 1 := special_prime_one_mod_four hodd hperf hq hqodd
  have hmod4 := sigmaFactor_special_mod_four hodd hperf hq hqodd
  have hsum : sigmaFactor n q % 4 = (n.factorization q + 1) % 4 :=
    sum_pow_mod_four hq4 _
  omega

/-! ### СТУПЕНЬ 4: полная форма Эйлера n = q^α · m² -/

/-- **ТЕОРЕМА ЭЙЛЕРА (доказано, полная форма): всякое нечётное совершенное число
    имеет вид `n = q^α · m²`, где `q` простое, `q ≡ 1 (mod 4)`, `α ≡ 1 (mod 4)`
    и `q ∤ m`.** Сборка ступеней: единственный нечётный показатель
    (`exists_unique_odd_exponent`) выделяет `q`; его вычеты — ступени 2–3;
    остальные показатели чётны, их произведение `∏ p^{a_p} = (∏ p^{a_p/2})²`
    упаковывается в `m²`; `q ∤ m`, потому что каждый сомножитель `m` — степень
    простого, отличного от `q`. НЕ решение открытой проблемы: обусловленная форма
    гипотетического свидетеля, известная с XVIII века. -/
theorem odd_perfect_euler_form {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ∃ q α m : ℕ, q.Prime ∧ q % 4 = 1 ∧ α % 4 = 1 ∧ n = q ^ α * m ^ 2 ∧ ¬ q ∣ m := by
  have hn0 : n ≠ 0 := hperf.2.ne'
  obtain ⟨q, ⟨hq, hqodd⟩, huniq⟩ := exists_unique_odd_exponent hodd hperf
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  refine ⟨q, n.factorization q,
    ∏ p ∈ n.primeFactors.erase q, p ^ (n.factorization p / 2),
    hqp, special_prime_one_mod_four hodd hperf hq hqodd,
    exponent_one_mod_four hodd hperf hq hqodd, ?_, ?_⟩
  · -- упаковка квадрата: все показатели вне q чётны
    have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
      Nat.prod_factorization_pow_eq_self hn0
    have hsplit :
        q ^ n.factorization q * ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p
          = n := by
      rw [Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) hq]
      exact hself
    have hsq : ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p
        = (∏ p ∈ n.primeFactors.erase q, p ^ (n.factorization p / 2)) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
      have hpe : n.factorization p % 2 = 0 := by
        by_contra hne0
        exact hpne (huniq p ⟨hpmem, Nat.odd_iff.mpr (by omega)⟩)
      rw [← pow_mul]
      congr 1
      omega
    rw [← hsq]
    exact hsplit.symm
  · -- q не делит m: каждый сомножитель m — степень простого p ≠ q
    intro hdvd
    obtain ⟨p, hp, hpdvd⟩ := (hqp.prime.dvd_finsetProd_iff _).mp hdvd
    obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have heq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow hpdvd)
    exact hpne heq.symm

/-! ### Форма Эйлера в языке свидетеля OddPerfectNumber -/

/-- **Форма Эйлера для гипотетического свидетеля (доказано):** всякий
    `W : OddPerfectNumber` обязан иметь вид `q^α · m²` с `q ≡ α ≡ 1 (mod 4)`
    и `q ∤ m` — рядом с `oddPerfect_ge_101` и `oddPerfect_min_three_prime_factors`
    это третье зелёное сужение домена свидетеля. -/
theorem oddPerfect_euler_form (W : OddPerfectNumber) :
    ∃ q α m : ℕ, q.Prime ∧ q % 4 = 1 ∧ α % 4 = 1 ∧ W.1 = q ^ α * m ^ 2 ∧ ¬ q ∣ m :=
  odd_perfect_euler_form W.2.1 W.2.2

#print axioms exists_unique_odd_exponent
#print axioms special_prime_one_mod_four
#print axioms exponent_one_mod_four
#print axioms odd_perfect_euler_form
#print axioms oddPerfect_euler_form

end EuclidsPath.PerfectNumberBranch
