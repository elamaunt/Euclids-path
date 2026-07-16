/-
  GeometricTypeIISpecial — special coefficients are EASY: the elementary `v ≡ 1` bound (no period
  hypotheses at all) and the exact hyperbola box-count identity.

  ORIGIN (boundary-move program, strike R5, adversarially corrected). The verification pass showed:
  for `v ≡ 1` and GENERAL bounded `u`, the Kloosterman machinery is unnecessary and strictly worse
  than elementary counting — each row's inner sum is `L/(p−1) − p·N_row/(p−1)` with `N_row` a single
  residue-class interval count, so `|inner| ≤ p/(p−1) ≤ 3/2` per nonzero row, giving
  `|B_p| ≤ (3/2)R + (⌊R/p⌋+1)·L/(p−1)` with NO full-period hypothesis on either variable.  For
  `u = v ≡ 1` the block IS the hyperbola box count: `B = RL/(p−1) − (p/(p−1))·N_box` EXACTLY, where
  `N_box = #{(k,l) : A·k·l ≡ −2 (p)}` — the bilinear language and the repo's hyperbola/circle
  geometry are the same object.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `residue_class_card_ge` — the lower class-count bound `⌊L/p⌋ ≤ N` (companion to the upper);
    * `class_count_dev` — `|L − p·N| ≤ p` for any interval residue-class count;
    * `bilinear_v_one_elementary` — `|B_p| ≤ (3/2)R + (⌊R/p⌋+1)·L/(p−1)`, ALL `R, L`, `A ≠ 0`:
      NO period hypotheses (contrast `bilinear_block_bound`, which NEEDS `p ≤ R`, `p ≤ L`);
    * `box_count_identity` — `Σ_{k<R}Σ_{l<L}(Y_{Ak}(l) − 1) = RL/(p−1) − (p/(p−1))·N_box` EXACTLY;
    * `hyperbola_box_count` — `|N_box − RL/p| ≤ (3/2)R + (⌊R/p⌋+1)·L/p` unconditionally.

  CLOSED ROUTES (recorded per the §110 discipline — NOT to be re-tried as stated):
    * `OneShortVariableCauchySchwarz` — for ONE sub-period variable, Cauchy–Schwarz against the
      exact Gram form yields `≈ R√(2L/p)`, WORSE than the elementary `≈ 2RL/p` whenever `p > 2L`:
      the variance method loses below the period — the wall showing itself.
    * `GeneralCoefficientCompletion` — completing the short variable for general bounded real `u`
      gives only `≈ R(1+log p)` for the inner sums (no cancellation for adversarial `u`), needing
      `L ≳ p log p` — worse than full period.  The `p^{3/4}`-quality sub-period window needs BOTH
      coefficients special (`u = v ≡ 1`, the box count) via double completion; its thresholds are
      `RL ≫ p^{7/4}(log p)²` (symmetric window opens only for `p ≳ 10¹¹`) — deferred, asymptotic.

  DISCLOSURE (the wall is NOT moved, renamed, or hidden):
    * Special coefficients are EASY — that is the point and the warning: the sieve application
      requires general bounded μ-SIGNED coefficients, and for those NOTHING below full period
      (`p ≤ L`) is claimed here or anywhere; the sub-period general-coefficient regime IS the wall
      (`SemiprimeShortRestriction`, `CRE`).  `bilinear_block_bound` and its disclosure are
      untouched (byte-identical).
    * This module introduces ZERO new open `Prop`s.  Nothing here proves twins; the parity wall is
      localized, not moved. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIBilinear

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The class-count deviation `|L − p·N| ≤ p` -/

/-- **Lower class-count bound.** Every residue class meets `range L` at least `⌊L/p⌋` times. -/
theorem residue_class_card_ge {p : ℕ} [Fact p.Prime] (L : ℕ) (t : ZMod p) :
    L / p ≤ ((Finset.range L).filter (fun (l : ℕ) => ((l : ZMod p)) = t)).card := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmaps : ∀ j ∈ Finset.range (L / p),
      j * p + t.val ∈ (Finset.range L).filter (fun (l : ℕ) => ((l : ZMod p)) = t) := by
    intro j hj
    have hjlt : j < L / p := Finset.mem_range.mp hj
    have htval : t.val < p := ZMod.val_lt t
    have hlt : j * p + t.val < L := by
      have h1 : (j + 1) * p ≤ (L / p) * p := Nat.mul_le_mul_right p (by omega)
      have h2 : (L / p) * p ≤ L := Nat.div_mul_le_self L p
      nlinarith
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ?_⟩
    have hcast : ((j * p + t.val : ℕ) : ZMod p) = ((t.val : ℕ) : ZMod p) := by
      push_cast
      rw [ZMod.natCast_self]
      ring
    rw [hcast]
    exact ZMod.natCast_rightInverse t
  have hinj : Set.InjOn (fun j => j * p + t.val) (Finset.range (L / p)) := by
    intro j1 _ j2 _ heq
    simp only at heq
    have hp1 : 1 ≤ p := hp0
    nlinarith [heq]
  calc L / p = (Finset.range (L / p)).card := (Finset.card_range _).symm
    _ ≤ ((Finset.range L).filter (fun (l : ℕ) => ((l : ZMod p)) = t)).card :=
        Finset.card_le_card_of_injOn (fun j => j * p + t.val) hmaps hinj

/-- Scaled lower bound (invertible row scale permutes classes). -/
theorem scaled_class_card_ge {p : ℕ} [Fact p.Prime] (L : ℕ) {A : ZMod p} (hA : A ≠ 0)
    (t : ZMod p) :
    L / p ≤ ((Finset.range L).filter (fun (l : ℕ) => A * ((l : ZMod p)) = t)).card := by
  have hfe : (Finset.range L).filter (fun (l : ℕ) => A * ((l : ZMod p)) = t)
      = (Finset.range L).filter (fun (l : ℕ) => ((l : ZMod p)) = A⁻¹ * t) := by
    apply Finset.filter_congr
    intro l _
    constructor
    · intro h; rw [← h, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    · intro h; rw [h, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  rw [hfe]
  exact residue_class_card_ge L _

/-- **Class-count deviation.** `|L − p·N| ≤ p` for the scaled class count `N`. -/
theorem class_count_dev {p : ℕ} [Fact p.Prime] (L : ℕ) {A : ZMod p} (hA : A ≠ 0) (t : ZMod p) :
    |(L : ℝ) - (p : ℝ) *
        (((Finset.range L).filter (fun (l : ℕ) => A * ((l : ZMod p)) = t)).card : ℝ)| ≤ p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set N : ℕ := ((Finset.range L).filter (fun (l : ℕ) => A * ((l : ZMod p)) = t)).card with hN
  have hlow : L / p ≤ N := scaled_class_card_ge L hA t
  have hup : N ≤ L / p + 1 := scaled_class_card_le L hA t
  -- linear facts over ℤ with atoms p*(L/p), p*N, L%p
  have hdm := Nat.div_add_mod L p
  have hmod : L % p < p := Nat.mod_lt L hp0
  have h1 : p * (L / p) ≤ p * N := Nat.mul_le_mul_left p hlow
  have h2 : p * N ≤ p * (L / p) + p := by
    calc p * N ≤ p * (L / p + 1) := Nat.mul_le_mul_left p hup
      _ = p * (L / p) + p := by ring
  rw [abs_le]
  constructor
  · have hZ : p * N ≤ L + p := by omega
    have hR : (p : ℝ) * N ≤ (L : ℝ) + p := by exact_mod_cast hZ
    linarith
  · have hZ : L ≤ p * N + p := by omega
    have hR : (L : ℝ) ≤ (p : ℝ) * N + p := by exact_mod_cast hZ
    linarith

/-! ## The elementary `v ≡ 1` bound (NO period hypotheses) -/

/-- `Y_0 − 1 = 1/(p−1)` on the zero row. -/
private theorem Yrow_zero_sub_one {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (n : ZMod p) :
    Yrow (0 : ZMod p) n - 1 = 1 / ((p : ℝ) - 1) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  unfold Yrow
  rw [Drow_zero_left hp2 n]
  field_simp
  ring

/-- **Row sum (a ≠ 0).** `Σ_{l<L}(Y_a(l) − 1) = L/(p−1) − p·N_a/(p−1)` with `N_a` the interval
    count of the single forbidden class. -/
private theorem inner_row_sum {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {a : ZMod p} (ha : a ≠ 0)
    (L : ℕ) :
    ∑ l ∈ Finset.range L, (Yrow a ((l : ZMod p)) - 1)
      = (L : ℝ) / ((p : ℝ) - 1)
        - (p : ℝ) * (((Finset.range L).filter
            (fun (l : ℕ) => a * ((l : ZMod p)) = -2)).card : ℝ) / ((p : ℝ) - 1) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hterm : ∀ l : ℕ, Yrow a ((l : ZMod p)) - 1
      = 1 / ((p : ℝ) - 1) - ((p : ℝ) / ((p : ℝ) - 1)) * Drow a ((l : ZMod p)) := by
    intro l
    rw [Yrow_sub_one hp2]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.mul_sum, Finset.card_range, nsmul_eq_mul]
  have hfe : (Finset.range L).filter (fun (x : ℕ) => a * ((x : ZMod p)) + 2 = 0)
      = (Finset.range L).filter (fun (l : ℕ) => a * ((l : ZMod p)) = -2) := by
    apply Finset.filter_congr
    intro l _
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  have hD : ∑ l ∈ Finset.range L, Drow a ((l : ZMod p))
      = (((Finset.range L).filter (fun (l : ℕ) => a * ((l : ZMod p)) = -2)).card : ℝ) := by
    unfold Drow
    rw [Finset.sum_boole, hfe]
  rw [hD]
  field_simp

/-- **The elementary `v ≡ 1` bound.** For `A ≠ 0` and ANY window lengths `R, L` — NO full-period
    hypotheses (contrast `bilinear_block_bound`) — general bounded `u`:
    `|Σ_k Σ_l u_k (Y_{Ak}(l) − 1)| ≤ (3/2)R + (⌊R/p⌋+1)·L/(p−1)`.
    Special coefficients in one variable make the block ELEMENTARY. -/
theorem bilinear_v_one_elementary {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {A : ZMod p} (hA : A ≠ 0)
    (R L : ℕ) (u : ℕ → ℝ) (hu : ∀ k ∈ Finset.range R, |u k| ≤ 1) :
    |∑ k ∈ Finset.range R, u k *
        (∑ l ∈ Finset.range L, (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1))|
      ≤ (3 / 2) * R + ((R / p + 1 : ℕ) : ℝ) * L / ((p : ℝ) - 1) := by
  have hp1R : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have : 3 ≤ p := by omega
    exact_mod_cast this
  -- per-row bounds
  have hrow : ∀ k : ℕ, |∑ l ∈ Finset.range L, (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1)|
      ≤ if ((k : ZMod p)) = 0 then (L : ℝ) / ((p : ℝ) - 1) else 3 / 2 := by
    intro k
    by_cases hk : ((k : ZMod p)) = 0
    · rw [if_pos hk, hk, mul_zero]
      have : ∑ l ∈ Finset.range L, (Yrow (0 : ZMod p) ((l : ZMod p)) - 1)
          = (L : ℝ) / ((p : ℝ) - 1) := by
        rw [Finset.sum_congr rfl (fun l _ => Yrow_zero_sub_one hp2 _), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
      rw [this, abs_of_nonneg (by positivity)]
    · rw [if_neg hk]
      have ha : A * ((k : ZMod p)) ≠ 0 := mul_ne_zero hA hk
      rw [inner_row_sum hp2 ha L]
      have hdev := class_count_dev L (A := A * ((k : ZMod p))) ha (-2)
      have heq : (L : ℝ) / ((p : ℝ) - 1)
          - (p : ℝ) * (((Finset.range L).filter
              (fun (l : ℕ) => A * ((k : ZMod p)) * ((l : ZMod p)) = -2)).card : ℝ) / ((p : ℝ) - 1)
          = ((L : ℝ) - (p : ℝ) * (((Finset.range L).filter
              (fun (l : ℕ) => A * ((k : ZMod p)) * ((l : ZMod p)) = -2)).card : ℝ))
            / ((p : ℝ) - 1) := by
        ring
      rw [heq, abs_div, abs_of_pos hp1R]
      calc |(L : ℝ) - (p : ℝ) * (((Finset.range L).filter
              (fun (l : ℕ) => A * ((k : ZMod p)) * ((l : ZMod p)) = -2)).card : ℝ)|
              / ((p : ℝ) - 1)
          ≤ (p : ℝ) / ((p : ℝ) - 1) := by
            gcongr
        _ ≤ 3 / 2 := by
            rw [div_le_div_iff₀ hp1R (by norm_num : (0:ℝ) < 2)]
            linarith
  -- assemble
  calc |∑ k ∈ Finset.range R, u k *
        (∑ l ∈ Finset.range L, (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1))|
      ≤ ∑ k ∈ Finset.range R, |u k *
          (∑ l ∈ Finset.range L, (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range R,
          (if ((k : ZMod p)) = 0 then (L : ℝ) / ((p : ℝ) - 1) else 3 / 2) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        calc |u k| * |∑ l ∈ Finset.range L, (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1)|
            ≤ 1 * (if ((k : ZMod p)) = 0 then (L : ℝ) / ((p : ℝ) - 1) else 3 / 2) := by
              apply mul_le_mul (hu k hk) (hrow k) (abs_nonneg _) (by norm_num)
          _ = _ := one_mul _
    _ ≤ (3 / 2) * R + ((R / p + 1 : ℕ) : ℝ) * L / ((p : ℝ) - 1) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R)
          (fun k => ((k : ZMod p)) = 0)]
        have hzero : ∑ k ∈ (Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = 0),
            (if ((k : ZMod p)) = 0 then (L : ℝ) / ((p : ℝ) - 1) else 3 / 2)
            = (((Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = 0)).card : ℝ)
              * ((L : ℝ) / ((p : ℝ) - 1)) := by
          rw [Finset.sum_congr rfl (fun k hk => by
            rw [if_pos (Finset.mem_filter.mp hk).2]), Finset.sum_const, nsmul_eq_mul]
        have hnz : ∑ k ∈ (Finset.range R).filter (fun (k : ℕ) => ¬ ((k : ZMod p)) = 0),
            (if ((k : ZMod p)) = 0 then (L : ℝ) / ((p : ℝ) - 1) else 3 / 2)
            = (((Finset.range R).filter (fun (k : ℕ) => ¬ ((k : ZMod p)) = 0)).card : ℝ)
              * (3 / 2) := by
          rw [Finset.sum_congr rfl (fun k hk => by
            rw [if_neg (Finset.mem_filter.mp hk).2]), Finset.sum_const, nsmul_eq_mul]
        rw [hzero, hnz]
        have hc1 : (((Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = 0)).card : ℝ)
            ≤ ((R / p + 1 : ℕ) : ℝ) := by
          exact_mod_cast residue_class_card_le R (0 : ZMod p)
        have hc2 : (((Finset.range R).filter (fun (k : ℕ) => ¬ ((k : ZMod p)) = 0)).card : ℝ)
            ≤ (R : ℝ) := by
          have := Finset.card_filter_le (Finset.range R) (fun (k : ℕ) => ¬ ((k : ZMod p)) = 0)
          calc (((Finset.range R).filter (fun (k : ℕ) => ¬ ((k : ZMod p)) = 0)).card : ℝ)
              ≤ ((Finset.range R).card : ℝ) := by exact_mod_cast this
            _ = (R : ℝ) := by rw [Finset.card_range]
        have hLpos : (0 : ℝ) ≤ (L : ℝ) / ((p : ℝ) - 1) := by positivity
        have hbound1 : (((Finset.range R).filter (fun (k : ℕ) => ((k : ZMod p)) = 0)).card : ℝ)
            * ((L : ℝ) / ((p : ℝ) - 1))
            ≤ ((R / p + 1 : ℕ) : ℝ) * ((L : ℝ) / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hc1 hLpos
        have hbound2 : (((Finset.range R).filter (fun (k : ℕ) => ¬ ((k : ZMod p)) = 0)).card : ℝ)
            * (3 / 2) ≤ (R : ℝ) * (3 / 2) :=
          mul_le_mul_of_nonneg_right hc2 (by norm_num)
        have heq2 : ((R / p + 1 : ℕ) : ℝ) * ((L : ℝ) / ((p : ℝ) - 1))
            = ((R / p + 1 : ℕ) : ℝ) * L / ((p : ℝ) - 1) := by ring
        linarith [hbound1, hbound2]

/-! ## The hyperbola box-count identity (u = v ≡ 1) -/

/-- **The box-count identity.** The pure `u = v ≡ 1` bilinear block IS the hyperbola box count:
    `Σ_{k<R}Σ_{l<L}(Y_{Ak}(l) − 1) = RL/(p−1) − (p/(p−1))·N_box` EXACTLY, where
    `N_box = #{(k,l) : A·k·l + 2 ≡ 0 (p)}` — the bilinear frame and the repo's hyperbola/circle
    geometry meet in one formula.  (Holds for ALL `A`, including `A = 0`.) -/
theorem box_count_identity {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (A : ZMod p) (R L : ℕ) :
    ∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
        (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1)
      = (R : ℝ) * L / ((p : ℝ) - 1)
        - ((p : ℝ) / ((p : ℝ) - 1))
          * (((Finset.range R ×ˢ Finset.range L).filter
              (fun kl : ℕ × ℕ =>
                A * ((kl.1 : ZMod p)) * ((kl.2 : ZMod p)) + 2 = 0)).card : ℝ) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hterm : ∀ k l : ℕ, Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1
      = 1 / ((p : ℝ) - 1)
        - ((p : ℝ) / ((p : ℝ) - 1)) * Drow (A * (k : ZMod p)) ((l : ZMod p)) := by
    intro k l
    rw [Yrow_sub_one hp2]
    field_simp
    ring
  have hrow : ∀ k : ℕ, ∑ l ∈ Finset.range L,
      (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1)
      = (L : ℝ) * (1 / ((p : ℝ) - 1))
        - ((p : ℝ) / ((p : ℝ) - 1))
          * ∑ l ∈ Finset.range L, Drow (A * (k : ZMod p)) ((l : ZMod p)) := by
    intro k
    rw [Finset.sum_congr rfl (fun l _ => hterm k l), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul]
  have hexp : ∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
      (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1)
      = (R : ℝ) * L * (1 / ((p : ℝ) - 1))
        - ((p : ℝ) / ((p : ℝ) - 1)) * ∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
            Drow (A * (k : ZMod p)) ((l : ZMod p)) := by
    rw [Finset.sum_congr rfl (fun k _ => hrow k), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul]
    ring
  have hbox : ∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
      Drow (A * (k : ZMod p)) ((l : ZMod p))
      = (((Finset.range R ×ˢ Finset.range L).filter
          (fun kl : ℕ × ℕ =>
            A * ((kl.1 : ZMod p)) * ((kl.2 : ZMod p)) + 2 = 0)).card : ℝ) := by
    rw [← Finset.sum_product']
    unfold Drow
    rw [Finset.sum_boole]
  rw [hexp, hbox]
  ring

/-- **The elementary hyperbola box count.** `|N_box − RL/p| ≤ (3/2)R + (⌊R/p⌋+1)·L/p` —
    unconditional, ALL `R, L`; from the identity + the elementary `v ≡ 1` bound with `u ≡ 1`.
    The sub-`p^{3/4}` improvement of this deviation (double completion + Weil) is the deferred
    special-coefficient front; its thresholds are stated in the header. -/
theorem hyperbola_box_count {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {A : ZMod p} (hA : A ≠ 0)
    (R L : ℕ) :
    |(((Finset.range R ×ˢ Finset.range L).filter
        (fun kl : ℕ × ℕ =>
          A * ((kl.1 : ZMod p)) * ((kl.2 : ZMod p)) + 2 = 0)).card : ℝ)
      - (R : ℝ) * L / p|
      ≤ (3 / 2) * R + ((R / p + 1 : ℕ) : ℝ) * L / p := by
  have hp1R : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  -- the u ≡ 1 case of the elementary bound
  have hB := bilinear_v_one_elementary hp2 hA R L (fun _ => 1) (fun k _ => by norm_num)
  simp only [one_mul] at hB
  have hid := box_count_identity hp2 A R L
  set B : ℝ := ∑ k ∈ Finset.range R, ∑ l ∈ Finset.range L,
      (Yrow (A * (k : ZMod p)) ((l : ZMod p)) - 1) with hBdef
  set N : ℝ := (((Finset.range R ×ˢ Finset.range L).filter
      (fun kl : ℕ × ℕ =>
        A * ((kl.1 : ZMod p)) * ((kl.2 : ZMod p)) + 2 = 0)).card : ℝ) with hNdef
  -- N − RL/p = −B(p−1)/p
  have hNval : N - (R : ℝ) * L / p = -(B * ((p : ℝ) - 1) / p) := by
    have : B = (R : ℝ) * L / ((p : ℝ) - 1) - ((p : ℝ) / ((p : ℝ) - 1)) * N := hid
    field_simp at this ⊢
    linarith [this]
  rw [hNval, abs_neg, abs_div, abs_of_pos hpR, abs_mul,
    abs_of_pos hp1R]
  calc |B| * ((p : ℝ) - 1) / p
      ≤ ((3 / 2) * R + ((R / p + 1 : ℕ) : ℝ) * L / ((p : ℝ) - 1)) * ((p : ℝ) - 1) / p := by
        gcongr
    _ = (3 / 2) * R * ((p : ℝ) - 1) / p + ((R / p + 1 : ℕ) : ℝ) * L / p := by
        field_simp
    _ ≤ (3 / 2) * R + ((R / p + 1 : ℕ) : ℝ) * L / p := by
        have h1 : (3 / 2) * (R : ℝ) * ((p : ℝ) - 1) / p ≤ (3 / 2) * R := by
          rw [div_le_iff₀ hpR]
          nlinarith [Nat.cast_nonneg (α := ℝ) R]
        linarith

end TypeII
end Geometric
end EuclidsPath
