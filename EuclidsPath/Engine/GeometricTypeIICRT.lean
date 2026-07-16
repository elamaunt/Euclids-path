/-
  GeometricTypeIICRT — the full CRT period margin and the literal Möbius–CRT residual.

  ORIGIN (parity_wall Prime-Chaos session dossier §2 / §3 / §4). On the full CRT period the
  two local wing prohibitions are COMPATIBLE with a fixed positive margin: writing
  `A = ∏(1−1/p)`, `B = ∏(1−2/p)`, one has the exact per-prime factorization
  `1 − 2/p = (1 − 1/p)² · (1 − 1/(p−1)²)`, and the product of the residual factors stays
  `> 3/4`.  So the wall is NOT the local incompatibility of the two wings — it is the transfer
  of that density to a short critical window, where the twin count equals a main term plus the
  exact alternating Möbius–CRT residual `R(H,z) = Σ_{(d,e)=1} μ(d)μ(e)Δ_{d,e}` (§3).  Splitting
  primes between `d` and `e` corresponds to a CRT root `C² ≡ 1 (mod de)` and `μ(d)μ(e)=μ(de)`
  (§4), tying the residual to the Type-II / Kloosterman / determinant branches.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `two_wing_ratio_factor` — the exact per-prime factorization `1 − 2/p = (1−1/p)²(1−1/(p−1)²)`;
    * `telescope_prod_Icc` — `∏_{n=4}^N (1−1/n²) = 3(N+1)/(4N)` (exact telescoping);
    * `crt_two_wing_margin` — for any finite set of primes `p ≥ 5`, `∏ (1−1/(p−1)²) > 3/4`
      (subset domination of the full-integer telescoping product);
    * `crt_margin_gap` — hence `A² − B < ¼ A²`: a fixed positive local margin;
    * `moeb_pair_coprime` — `μ(d)μ(e) = μ(de)` for coprime `d,e` (§4 CRT-root reduction).

  DISCLOSURE. The literal parity wall `MoebiusCRTResidual` is a named structural object, not a
  bound; estimating it by absolute values (`~3^{π(z)}` terms) is useless.  Nothing here proves
  twins. twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ## The exact per-prime two-wing factorization (§2) -/

/-- **Two-wing ratio factor (§2).** The joint-survival Euler factor `1 − 2/p` factors exactly as
    `(1 − 1/p)² · (1 − 1/(p−1)²)`, so `B/A² = ∏ (1 − 1/(p−1)²)`. -/
theorem two_wing_ratio_factor {p : ℕ} (hp : 5 ≤ p) :
    (1 - 2 / (p : ℝ)) = (1 - 1 / (p : ℝ)) ^ 2 * (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hpp : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Each residual factor `1 − 1/(p−1)²` lies in `(0, 1]` for `p ≥ 5`. -/
theorem residual_factor_mem {p : ℕ} (hp : 5 ≤ p) :
    0 ≤ 1 - 1 / ((p : ℝ) - 1) ^ 2 ∧ 1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
  have hpp : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  constructor
  · have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith)]; exact h1
    linarith
  · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith

/-! ## The telescoping full-integer product (§2) -/

/-- **Telescoping product (§2).** `∏_{n=4}^N (1 − 1/n²) = 3(N+1)/(4N)`. -/
theorem telescope_prod_Icc {N : ℕ} (hN : 4 ≤ N) :
    ∏ n ∈ Finset.Icc 4 N, (1 - 1 / (n : ℝ) ^ 2) = 3 * ((N : ℝ) + 1) / (4 * (N : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Finset.Icc_self]
  | succ N hN ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    push_cast
    field_simp
    ring

/-- `3/4 < 3(N+1)/(4N)` for `N ≥ 4`. -/
theorem telescope_gt_three_quarters {N : ℕ} (hN : 4 ≤ N) :
    (3 : ℝ) / 4 < 3 * ((N : ℝ) + 1) / (4 * (N : ℝ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hne : (N : ℝ) ≠ 0 := hN0.ne'
  have key : 3 * ((N : ℝ) + 1) / (4 * (N : ℝ)) - 3 / 4 = 3 / (4 * (N : ℝ)) := by
    field_simp; ring
  have hpos : 0 < 3 / (4 * (N : ℝ)) := by positivity
  linarith [key, hpos]

/-! ## The prime-product margin by subset domination (§2) -/

/-- **Full-CRT two-wing margin (§2).** For any finite set of primes `p ≥ 5`, the product of the
    residual factors stays strictly above `3/4`.  The two local prohibitions are compatible with
    a fixed positive margin; the wall is the transfer to a short window, not local incompatibility. -/
theorem crt_two_wing_margin (P : Finset ℕ) (hP : ∀ p ∈ P, 5 ≤ p) :
    (3 : ℝ) / 4 < ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  -- Reindex by `n = p − 1 ∈ {4, …}`; the image `S` is a subset of `Icc 4 N`.
  set S : Finset ℕ := P.image (fun p => p - 1) with hS
  have hinj : Set.InjOn (fun p => p - 1) P := by
    intro a ha b hb hab
    have ha5 := hP a ha; have hb5 := hP b hb
    simp only at hab; omega
  have hprod : ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) = ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2) := by
    rw [hS, Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro p hp
    have hp5 := hP p hp
    have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have : (1 : ℕ) ≤ p := by omega
      push_cast [this]; ring
    rw [this]
  rw [hprod]
  rcases Finset.eq_empty_or_nonempty S with hSe | hSne
  · simp [hSe]; norm_num
  -- `S ⊆ Icc 4 N` with `N = S.max'`.
  set N : ℕ := S.max' hSne with hN
  have hSsub : S ⊆ Finset.Icc 4 N := by
    intro n hn
    simp only [Finset.mem_Icc]
    obtain ⟨p, hpP, rfl⟩ := Finset.mem_image.mp (by rw [← hS]; exact hn)
    have hp5 := hP p hpP
    refine ⟨by omega, ?_⟩
    exact Finset.le_max' S (p - 1) (by rw [hS]; exact Finset.mem_image_of_mem _ hpP)
  have hN4 : 4 ≤ N := by
    obtain ⟨n, hn⟩ := hSne
    have := hSsub hn; simp only [Finset.mem_Icc] at this; omega
  -- Product over the larger `Icc 4 N` (all factors in `[0,1]`) is ≤ product over `S`.
  have hfac : ∀ n ∈ Finset.Icc 4 N, 0 ≤ 1 - 1 / (n : ℝ) ^ 2 ∧ 1 - 1 / (n : ℝ) ^ 2 ≤ 1 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      linarith
    constructor
    · have : 1 / (n : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by nlinarith)]; nlinarith
      linarith
    · have : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
      linarith
  have hdom : ∏ n ∈ Finset.Icc 4 N, (1 - 1 / (n : ℝ) ^ 2) ≤ ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2) := by
    rw [← Finset.prod_sdiff hSsub]
    have hle1 : ∏ n ∈ (Finset.Icc 4 N \ S), (1 - 1 / (n : ℝ) ^ 2) ≤ 1 := by
      apply Finset.prod_le_one
      · intro n hn; exact (hfac n (Finset.mem_sdiff.mp hn).1).1
      · intro n hn; exact (hfac n (Finset.mem_sdiff.mp hn).1).2
    have hnn : 0 ≤ ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2) := by
      apply Finset.prod_nonneg
      intro n hn; exact (hfac n (hSsub hn)).1
    calc (∏ n ∈ (Finset.Icc 4 N \ S), (1 - 1 / (n : ℝ) ^ 2)) * ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2)
        ≤ 1 * ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hle1 hnn
      _ = ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2) := one_mul _
  calc (3 : ℝ) / 4 < 3 * ((N : ℝ) + 1) / (4 * (N : ℝ)) := telescope_gt_three_quarters hN4
    _ = ∏ n ∈ Finset.Icc 4 N, (1 - 1 / (n : ℝ) ^ 2) := (telescope_prod_Icc hN4).symm
    _ ≤ ∏ n ∈ S, (1 - 1 / (n : ℝ) ^ 2) := hdom

/-- **Fixed local margin (§2).** With `A = ∏(1−1/p)`, `B = ∏(1−2/p)`, the two-wing deficit is a
    bounded fraction of `A²`: `A² − B < ¼ A²`.  (Here `B = A² · ∏(1−1/(p−1)²)` by
    `two_wing_ratio_factor`, and the residual product exceeds `3/4`.) -/
theorem crt_margin_gap (P : Finset ℕ) (hP : ∀ p ∈ P, 5 ≤ p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ^ 2 - ∏ p ∈ P, (1 - 2 / (p : ℝ))
      < (1 / 4) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) ^ 2 := by
  set A : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ)) with hA
  have hBfac : (∏ p ∈ P, (1 - 2 / (p : ℝ)))
      = A ^ 2 * ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [hA, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp; exact two_wing_ratio_factor (hP p hp)
  have hApos : 0 < A := by
    rw [hA]
    apply Finset.prod_pos
    intro p hp
    have hpp : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hp
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hAsq : 0 < A ^ 2 := by positivity
  have hmargin := crt_two_wing_margin P hP
  rw [hBfac]
  nlinarith [mul_lt_mul_of_pos_left hmargin hAsq]

/-! ## The Möbius–CRT residual and the CRT-root reduction (§3 / §4) -/

/-- **CRT-root Möbius reduction (§4).** Splitting the prime factors of `q = de` between the two
    wings is `μ(d)μ(e) = μ(de)`; combined with a CRT root `C² ≡ 1 (mod de)` this rewrites the
    residual as a signed sum over CRT roots. -/
theorem moeb_pair_coprime {d e : ℕ} (h : Nat.Coprime d e) :
    ArithmeticFunction.moebius d * ArithmeticFunction.moebius e = ArithmeticFunction.moebius (d * e) :=
  (isMultiplicative_moebius.map_mul_of_coprime h).symm

/-- The main-term density `ρ(z) = ∏_{5 ≤ p ≤ z} (1 − 2/p)` (§3). -/
noncomputable def rho (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 2 / (p : ℝ))

/-- **The literal Möbius–CRT residual (§3).** `R = Σ_{(d,e)=1} μ(d)μ(e)Δ_{d,e}`: the exact finite
    alternating sum equal to the twin count minus `H·ρ(z)`.  This is the parity wall in its most
    explicit form — a named structural object, NOT a bound (absolute values give `~3^{π(z)}`
    useless terms). -/
noncomputable def MoebiusCRTResidual (Δ : ℕ → ℕ → ℝ) (Pairs : Finset (ℕ × ℕ)) : ℝ :=
  ∑ de ∈ Pairs,
    (ArithmeticFunction.moebius de.1 : ℝ) * (ArithmeticFunction.moebius de.2 : ℝ) * Δ de.1 de.2

end TypeII
end Geometric
end EuclidsPath
