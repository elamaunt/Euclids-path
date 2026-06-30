/-
  Step00 residuals — формализация авторских закрывающих лемм.
  Источник: step00_residuals_formal_proofs_ru_2026-06-30-1.md. Проза: prose/22_Residuals.md.

  Закрывает остатки Lean-аудита БЕЗ распределения/плотности:
    ② start  — конструктивный clean-центр выше любого N (primorial), плотность НЕ нужна;
    ③ sink⇒twin — clean non-twin ⟹ active edge ⟹ sink = twin (чётность элементарна);
    sink above N — при A>6N+1 twin-центр автоматически выше N;
    ① height — active descent строго уменьшает высоту.

  Авторская идея ② (§2): m=(N+1)·P_A, где P_A — произведение простых 5≤p≤A, делает обе стороны
  6m±1 ≡ ±1 (mod q) для всех q≤A ⟹ Clean. Existential Step00 не требует carrier-density.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Residuals

/-- `CleanZ A m`: ни один простой `q ≤ A` не делит ни одну сторону `6m−1`, `6m+1` (в ℤ). -/
def CleanZ (A : ℕ) (m : ℤ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ A → ¬ ((q : ℤ) ∣ (6 * m - 1) ∨ (q : ℤ) ∣ (6 * m + 1))

/-- `TwinCenterZ m`: обе стороны `6m−1`, `6m+1` простые (в ℕ, для `m ≥ 1`). -/
def TwinCenterZ (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * m + 1).Prime

/-! ### Остаток ② — конструктивный clean-старт выше N (БЕЗ плотности) -/

/-- Старый примориал `P_A = ∏_{5≤p≤A, p prime} p` (как ℕ). -/
def oldPrimorial (A : ℕ) : ℕ :=
  (Finset.range (A + 1)).prod (fun p => if p.Prime ∧ 5 ≤ p then p else 1)

theorem oldPrimorial_pos (A : ℕ) : 0 < oldPrimorial A := by
  apply Finset.prod_pos
  intro p _
  by_cases h : p.Prime ∧ 5 ≤ p
  · simp [h]; exact h.1.pos
  · simp [h]

/-- Каждый простой `5 ≤ q ≤ A` делит `oldPrimorial A` (он — один из множителей). -/
theorem prime_dvd_oldPrimorial {A q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hqA : q ≤ A) :
    q ∣ oldPrimorial A := by
  unfold oldPrimorial
  have hmem : q ∈ Finset.range (A + 1) := Finset.mem_range.mpr (by omega)
  have hd := Finset.dvd_prod_of_mem (fun p => if p.Prime ∧ 5 ≤ p then p else 1) hmem
  -- фактор при q равен q (т.к. q.Prime ∧ 5 ≤ q)
  simpa [hq, hq5] using hd

/--
  **`primorial_multiple_clean` (Лемма 2.2.1).** Для `A`, `k ≥ 1`: центр `m = k·P_A` — clean
  (ни один простой `q ≤ A` не делит `6m±1`). Доказательство: для `q≥5` `q∣m` ⟹ `6m±1≡±1`;
  для `q=2,3` стороны нечётны и `≢0 mod 3`. -/
theorem primorial_multiple_clean (A k : ℕ) (_hk : 1 ≤ k) :
    CleanZ A ((k * oldPrimorial A : ℕ) : ℤ) := by
  intro q hq hqA
  rcases lt_or_ge q 5 with h5 | h5
  · -- q ∈ {2,3} (простые <5): 6m±1 не делится
    interval_cases q
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · -- q=2: 6m±1 нечётны
      rintro (h | h) <;> omega
    · -- q=3: 6m±1 ≡ ±1 (mod 3)
      rintro (h | h) <;> omega
    · exact absurd hq (by decide)
  · -- q ≥ 5: q ∣ P_A ∣ m ⟹ 6m ≡ 0 ⟹ 6m±1 ≡ ±1 ≢ 0
    have hdvd : q ∣ k * oldPrimorial A := Dvd.dvd.mul_left (prime_dvd_oldPrimorial hq h5 hqA) k
    have hqm : (q : ℤ) ∣ (6 * ((k * oldPrimorial A : ℕ) : ℤ)) := by
      have : (q : ℤ) ∣ ((k * oldPrimorial A : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
      exact Dvd.dvd.mul_left this 6
    have hq2 : 2 ≤ q := hq.two_le
    rintro (h | h)
    · -- q ∣ 6m−1 и q ∣ 6m ⟹ q ∣ 1
      have : (q : ℤ) ∣ 1 := by
        have := Int.dvd_sub hqm h; simpa using this
      have := Int.le_of_dvd (by norm_num) this; omega
    · have : (q : ℤ) ∣ 1 := by
        have := Int.dvd_sub h hqm; simpa using this
      have := Int.le_of_dvd (by norm_num) this; omega

/--
  **`carrier_nonempty_above` (Следствие 2.3.1).** Для любых `A,N`: существует clean-центр `m > N`.
  Берём `m=(N+1)·P_A`. Плотность НЕ нужна — это конструкция. -/
theorem carrier_nonempty_above (A N : ℕ) :
    ∃ m : ℕ, N < m ∧ CleanZ A (m : ℤ) := by
  refine ⟨(N + 1) * oldPrimorial A, ?_, ?_⟩
  · have hP : 1 ≤ oldPrimorial A := oldPrimorial_pos A
    calc N < N + 1 := by omega
      _ = (N + 1) * 1 := by ring
      _ ≤ (N + 1) * oldPrimorial A := by exact Nat.mul_le_mul_left _ hP
  · exact primorial_multiple_clean A (N + 1) (by omega)

/-! ### Остаток ③ — sink ⇒ twin (чётность элементарна) -/

/--
  **`clean_non_twin_has_active_edge` (Лемма 4.1.1), ядро.** Clean центр, который НЕ twin, имеет
  составную сторону, у которой простой делитель `> A`. Это active edge. Формализуем ключ:
  если сторона `side ≥ 2` НЕ простая и ни один `q ≤ A` её не делит, то её `minFac > A`. -/
theorem clean_side_composite_big_divisor {A side : ℕ}
    (hge : 2 ≤ side) (_hcomp : ¬ side.Prime)
    (hclean : ∀ q : ℕ, q.Prime → q ≤ A → ¬ q ∣ side) :
    ∃ b : ℕ, b.Prime ∧ A < b ∧ b ∣ side := by
  refine ⟨side.minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd side⟩
  by_contra hle
  exact hclean side.minFac (Nat.minFac_prime (by omega)) (by omega) (Nat.minFac_dvd side)

/--
  **Old-free число ниже `A²` простое (Лемма 6.1 источника / 6.1 движка).** Если `n ≥ 2`, `n < A·A`,
  и ни один простой `q ≤ A` не делит `n`, то `n` простое. Иначе минимальный простой делитель `p>A`,
  кофактор `n/p ≥ p > A`, и `n = p·(n/p) > A·A` — противоречие. -/
theorem oldfree_below_sq_prime {A n : ℕ} (h2 : 2 ≤ n) (hlt : n < A * A)
    (hof : ∀ q : ℕ, q.Prime → q ≤ A → ¬ q ∣ n) : n.Prime := by
  by_contra hnp
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpd : n.minFac ∣ n := Nat.minFac_dvd n
  have hpA : A < n.minFac := by
    by_contra hle; exact hof n.minFac hp (by omega) hpd
  -- кофактор n/minFac ≥ minFac (минимальность простого делителя у составного)
  have hcof : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hnp
  have hfac : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hpd
  have hsq : n.minFac * n.minFac ≤ n := by
    calc n.minFac * n.minFac ≤ n.minFac * (n / n.minFac) := by
          exact Nat.mul_le_mul_left _ hcof
      _ = n := hfac
  nlinarith [hpA, hsq, hlt]

/--
  **`sink_is_twin` (Теорема 4.2.1).** Если обе стороны `6m±1 ≥ 2`, `< A²`, и clean (ни один `q≤A`
  не делит ни одну сторону), то `m` — twin. (Чётность: old-free + `<A²` ⟹ простое.) -/
theorem sink_is_twin {A m : ℕ}
    (hlo : 2 ≤ 6 * m - 1) (hhi : 2 ≤ 6 * m + 1)
    (hlo2 : 6 * m - 1 < A * A) (hhi2 : 6 * m + 1 < A * A)
    (hcl : ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))) :
    TwinCenterZ m := by
  refine ⟨oldfree_below_sq_prime hlo hlo2 ?_, oldfree_below_sq_prime hhi hhi2 ?_⟩
  · exact fun q hq hqA hd => hcl q hq hqA (Or.inl hd)
  · exact fun q hq hqA hd => hcl q hq hqA (Or.inr hd)

/-! ### Привязка sink к центру выше N -/

/--
  **`clean_twin_above` (§5).** Если `6N+1 < A`, `m` clean и twin, то `m > N`. Простое `6m−1 > A`
  (иначе старое простое делило бы свою сторону, нарушая clean), а `A > 6N+1` ⟹ `m > N`. -/
theorem clean_twin_above {A N m : ℕ} (hAN : 6 * N + 1 < A) (hm : 1 ≤ m)
    (hcl : ∀ q : ℕ, q.Prime → q ≤ A → ¬ ((q : ℤ) ∣ (6 * (m:ℤ) - 1) ∨ (q : ℤ) ∣ (6 * (m:ℤ) + 1)))
    (htwin : TwinCenterZ m) : N < m := by
  have hp : (6 * m - 1).Prime := htwin.1
  have hgt : A < 6 * m - 1 := by
    by_contra hle
    have hcast : ((6 * m - 1 : ℕ) : ℤ) = 6 * (m:ℤ) - 1 := by
      have h1 : 1 ≤ 6 * m := by omega
      push_cast [Nat.cast_sub h1]; ring
    refine hcl (6 * m - 1) hp (by omega) (Or.inl ?_)
    rw [hcast]
  omega

/-! ### Остаток ① — active descent уменьшает высоту -/

/--
  **`active_descent_height` (§3).** Если `6m+σ = a(6n+ε)`, `a > A ≥ 5`, `σ,ε ∈ {±1}`, центры `≥ 1`,
  то `n < m`. (Из `6n+ε = (6m+σ)/a ≤ (6m+1)/5` и `(6m+1)/5 < 6m−1` при `m≥1`.) -/
theorem active_descent_height {A m n a σ ε : ℤ}
    (hA : 5 ≤ A) (hm : 1 ≤ m) (hn : 1 ≤ n) (haA : A < a)
    (hσ : σ = 1 ∨ σ = -1) (hε : ε = 1 ∨ ε = -1)
    (h : 6 * m + σ = a * (6 * n + ε)) : n < m := by
  have ha5 : 5 ≤ a := by omega
  have hside : 0 < 6 * n + ε := by rcases hε with rfl | rfl <;> omega
  -- a*(6n+ε) = 6m+σ ≤ 6m+1, a≥5 ⟹ 5*(6n+ε) ≤ 6m+1
  have h5 : 5 * (6 * n + ε) ≤ 6 * m + σ := by
    calc 5 * (6 * n + ε) ≤ a * (6 * n + ε) := by
          apply mul_le_mul_of_nonneg_right ha5 (le_of_lt hside)
      _ = 6 * m + σ := h.symm
  rcases hσ with rfl | rfl <;> rcases hε with rfl | rfl <;> nlinarith [h5, hm, hn]

end EuclidsPath.Residuals
