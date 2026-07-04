/-
  Step00 residuals — formalisation of the author's closing lemmas.
  Source: step00_residuals_formal_proofs_ru_2026-06-30-1.md. Prose: prose/22_Residuals.md.

  Closes the remaining items of the Lean audit WITHOUT distribution/density:
    ② start  — constructive clean center above any N (primorial), density NOT needed;
    ③ sink⇒twin — clean non-twin ⟹ active edge ⟹ sink = twin (parity is elementary);
    sink above N — when A>6N+1 the twin center is automatically above N;
    ① height — active descent strictly decreases height.

  Author's idea ② (§2): m=(N+1)·P_A, where P_A is the product of primes 5≤p≤A, makes both sides
  6m±1 ≡ ±1 (mod q) for all q≤A ⟹ Clean. Existential Step00 does not require carrier-density.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Residuals

/-- `CleanZ A m`: no prime `q ≤ A` divides either side `6m−1`, `6m+1` (in ℤ). -/
def CleanZ (A : ℕ) (m : ℤ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ A → ¬ ((q : ℤ) ∣ (6 * m - 1) ∨ (q : ℤ) ∣ (6 * m + 1))

/-- `TwinCenterZ m`: both sides `6m−1`, `6m+1` are prime (in ℕ, for `m ≥ 1`). -/
def TwinCenterZ (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * m + 1).Prime

/-! ### Residual ② — constructive clean start above N (WITHOUT density) -/

/-- Old primorial `P_A = ∏_{5≤p≤A, p prime} p` (as ℕ). -/
def oldPrimorial (A : ℕ) : ℕ :=
  (Finset.range (A + 1)).prod (fun p => if p.Prime ∧ 5 ≤ p then p else 1)

theorem oldPrimorial_pos (A : ℕ) : 0 < oldPrimorial A := by
  apply Finset.prod_pos
  intro p _
  by_cases h : p.Prime ∧ 5 ≤ p
  · simp [h]; exact h.1.pos
  · simp [h]

/-- Every prime `5 ≤ q ≤ A` divides `oldPrimorial A` (it is one of the factors). -/
theorem prime_dvd_oldPrimorial {A q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hqA : q ≤ A) :
    q ∣ oldPrimorial A := by
  unfold oldPrimorial
  have hmem : q ∈ Finset.range (A + 1) := Finset.mem_range.mpr (by omega)
  have hd := Finset.dvd_prod_of_mem (fun p => if p.Prime ∧ 5 ≤ p then p else 1) hmem
  -- the factor at q equals q (since q.Prime ∧ 5 ≤ q)
  simpa [hq, hq5] using hd

/--
  **`primorial_multiple_clean` (Lemma 2.2.1).** For `A`, `k ≥ 1`: center `m = k·P_A` is clean
  (no prime `q ≤ A` divides `6m±1`). Proof: for `q≥5` `q∣m` ⟹ `6m±1≡±1`;
  for `q=2,3` the sides are odd and `≢0 mod 3`. -/
theorem primorial_multiple_clean (A k : ℕ) (_hk : 1 ≤ k) :
    CleanZ A ((k * oldPrimorial A : ℕ) : ℤ) := by
  intro q hq hqA
  rcases lt_or_ge q 5 with h5 | h5
  · -- q ∈ {2,3} (primes <5): 6m±1 not divisible
    interval_cases q
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · -- q=2: 6m±1 are odd
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
    · -- q ∣ 6m−1 and q ∣ 6m ⟹ q ∣ 1
      have : (q : ℤ) ∣ 1 := by
        have := Int.dvd_sub hqm h; simpa using this
      have := Int.le_of_dvd (by norm_num) this; omega
    · have : (q : ℤ) ∣ 1 := by
        have := Int.dvd_sub h hqm; simpa using this
      have := Int.le_of_dvd (by norm_num) this; omega

/--
  **`carrier_nonempty_above` (Corollary 2.3.1).** For any `A,N`: there exists a clean center `m > N`.
  Take `m=(N+1)·P_A`. Density is NOT needed — this is a construction. -/
theorem carrier_nonempty_above (A N : ℕ) :
    ∃ m : ℕ, N < m ∧ CleanZ A (m : ℤ) := by
  refine ⟨(N + 1) * oldPrimorial A, ?_, ?_⟩
  · have hP : 1 ≤ oldPrimorial A := oldPrimorial_pos A
    calc N < N + 1 := by omega
      _ = (N + 1) * 1 := by ring
      _ ≤ (N + 1) * oldPrimorial A := by exact Nat.mul_le_mul_left _ hP
  · exact primorial_multiple_clean A (N + 1) (by omega)

/-! ### Residual ③ — sink ⇒ twin (parity is elementary) -/

/--
  **`clean_non_twin_has_active_edge` (Lemma 4.1.1), core.** A clean center that is NOT a twin has
  a composite side whose prime divisor is `> A`. That is an active edge. We formalise the key:
  if a side `side ≥ 2` is NOT prime and no `q ≤ A` divides it, then its `minFac > A`. -/
theorem clean_side_composite_big_divisor {A side : ℕ}
    (hge : 2 ≤ side) (_hcomp : ¬ side.Prime)
    (hclean : ∀ q : ℕ, q.Prime → q ≤ A → ¬ q ∣ side) :
    ∃ b : ℕ, b.Prime ∧ A < b ∧ b ∣ side := by
  refine ⟨side.minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd side⟩
  by_contra hle
  exact hclean side.minFac (Nat.minFac_prime (by omega)) (by omega) (Nat.minFac_dvd side)

/--
  **An old-free number below `A²` is prime (Lemma 6.1 of the source / 6.1 of the engine).** If `n ≥ 2`, `n < A·A`,
  and no prime `q ≤ A` divides `n`, then `n` is prime. Otherwise the minimal prime divisor `p>A`,
  cofactor `n/p ≥ p > A`, and `n = p·(n/p) > A·A` — contradiction. -/
theorem oldfree_below_sq_prime {A n : ℕ} (h2 : 2 ≤ n) (hlt : n < A * A)
    (hof : ∀ q : ℕ, q.Prime → q ≤ A → ¬ q ∣ n) : n.Prime := by
  by_contra hnp
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpd : n.minFac ∣ n := Nat.minFac_dvd n
  have hpA : A < n.minFac := by
    by_contra hle; exact hof n.minFac hp (by omega) hpd
  -- cofactor n/minFac ≥ minFac (minimality of the prime divisor for a composite)
  have hcof : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hnp
  have hfac : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hpd
  have hsq : n.minFac * n.minFac ≤ n := by
    calc n.minFac * n.minFac ≤ n.minFac * (n / n.minFac) := by
          exact Nat.mul_le_mul_left _ hcof
      _ = n := hfac
  nlinarith [hpA, hsq, hlt]

/--
  **`sink_is_twin` (Theorem 4.2.1).** If both sides `6m±1 ≥ 2`, `< A²`, and clean (no `q≤A`
  divides either side), then `m` is a twin. (Parity: old-free + `<A²` ⟹ prime.) -/
theorem sink_is_twin {A m : ℕ}
    (hlo : 2 ≤ 6 * m - 1) (hhi : 2 ≤ 6 * m + 1)
    (hlo2 : 6 * m - 1 < A * A) (hhi2 : 6 * m + 1 < A * A)
    (hcl : ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))) :
    TwinCenterZ m := by
  refine ⟨oldfree_below_sq_prime hlo hlo2 ?_, oldfree_below_sq_prime hhi hhi2 ?_⟩
  · exact fun q hq hqA hd => hcl q hq hqA (Or.inl hd)
  · exact fun q hq hqA hd => hcl q hq hqA (Or.inr hd)

/-! ### Anchoring the sink to a center above N -/

/--
  **`clean_twin_above` (§5).** If `6N+1 < A`, `m` is clean and twin, then `m > N`. The prime `6m−1 > A`
  (otherwise an old prime would divide its side, violating clean), and `A > 6N+1` ⟹ `m > N`. -/
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

/-! ### Residual ① — active descent decreases height -/

/--
  **`active_descent_height` (§3).** If `6m+σ = a(6n+ε)`, `a > A ≥ 5`, `σ,ε ∈ {±1}`, centers `≥ 1`,
  then `n < m`. (From `6n+ε = (6m+σ)/a ≤ (6m+1)/5` and `(6m+1)/5 < 6m−1` for `m≥1`.) -/
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
