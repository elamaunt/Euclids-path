/-
  Wave 5: вывод — условная редукция гипотезы близнецов к блочному ядру.
  Проза: prose/18_ReductionAndFrontier.md (после зелёного Lean).

  Здесь собирается ВЕРИФИЦИРОВАННАЯ нециркулярная редукция: гипотеза близнецов следует из
  блочного утверждения (на каждом масштабе carrier выше N, в котором bad < carrier, и каждый
  выживший — twin-центр). Это изолирует ровно открытое ядро (carrier-оценка = CarrierInput;
  bad-upper через fan/cycle; survivor⟹twin). Плюс показываем, что направление survivor⟹twin
  ЭЛЕМЕНТАРНО (сито до корня ⟹ простота) — значит вся трудность сосредоточена в carrier/bad-счёте.

  Всё элементарно (Finset + минимальная теория простых). Без анализа/распределения/сита.
-/
import EuclidsPath.Engine.NonCover

set_option autoImplicit false

namespace EuclidsPath

/-- Один блок: `carrier > bad` и `survivor ⟹ twin` дают twin-центр выше `N`. -/
theorem twin_center_of_block {N : ℕ} {carrier bad : Finset ℕ}
    (habove : ∀ m ∈ carrier, N < m)
    (hcov : bad.card < carrier.card)
    (htwin : ∀ m ∈ carrier, m ∉ bad → IsTwinCenter m) :
    ∃ m, N < m ∧ IsTwinCenter m := by
  obtain ⟨m, hm, hmb⟩ := survivor_of_not_covered hcov
  exact ⟨m, habove m hm, htwin m hm hmb⟩

/--
  **Условная редукция гипотезы близнецов к блочному ядру.**
  Если на каждом масштабе `N` существует carrier (центры выше `N`), в котором «плохое» множество
  строго меньше carrier и каждый выживший — twin-центр, то простых-близнецов бесконечно много.
  Это машинно проверенный нециркулярный мост: гипотеза ⟸ блочное ядро.
-/
theorem twin_prime_conjecture_of_blocks
    (h : ∀ N : ℕ, ∃ carrier bad : Finset ℕ,
           (∀ m ∈ carrier, N < m) ∧ bad.card < carrier.card ∧
           (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)) :
    TwinLowers.Infinite := by
  apply infinite_of_unbounded_centers
  intro N
  obtain ⟨carrier, bad, habove, hcov, htwin⟩ := h N
  exact twin_center_of_block habove hcov htwin

/--
  **Сито до корня ⟹ простота.** Если `n ≥ 2` и ни один простой `p` с `p² ≤ n` не делит `n`,
  то `n` простое. (Элементарно: иначе минимальный простой делитель `p=minFac n` даёт `p²≤n` и `p∣n`.)
-/
theorem prime_of_no_small_prime_factor {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ p, p.Prime → p * p ≤ n → ¬ p ∣ n) : n.Prime := by
  by_contra hnp
  have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hpd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hnp
  have hpsq : n.minFac * n.minFac ≤ n :=
    le_trans (Nat.mul_le_mul (le_refl _) hle) (Nat.mul_div_le n n.minFac)
  exact h n.minFac hpp hpsq hpd

/--
  **Survivor ⟹ twin (элементарно).** Если оба `6m−1, 6m+1 ≥ 2` и ни один простой до их корня не
  делит соответствующую сторону, то `m` — twin-центр. Значит трудность не здесь, а в carrier/bad-счёте.
-/
theorem isTwinCenter_of_root_sieve {m : ℕ} (h1 : 2 ≤ 6 * m - 1) (h2 : 2 ≤ 6 * m + 1)
    (s1 : ∀ p, p.Prime → p * p ≤ 6 * m - 1 → ¬ p ∣ (6 * m - 1))
    (s2 : ∀ p, p.Prime → p * p ≤ 6 * m + 1 → ¬ p ∣ (6 * m + 1)) :
    IsTwinCenter m :=
  ⟨prime_of_no_small_prime_factor h1 s1, prime_of_no_small_prime_factor h2 s2⟩

end EuclidsPath
