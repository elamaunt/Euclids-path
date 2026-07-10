import EuclidsPath.Engine.Step00OrnamentTwoComplex

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The gain layer — balance certifies twins; the confirmed T-fill law (all green)

The ℤ²-gain of a center is its graded distance from the twin state:
`wingGain m = (Ω(6m−1)−1, Ω(6m+1)−1)`; twins are EXACTLY the gain-zero centers.  Gate G1
(tools/gain_complex_harness.py) confirmed the T-fill interface law exactly on all 36 test
regions — `b₁(W/K) = E_SK + E_KS − 1` with `b₀ = 1`, `b₂ = 0` — and REFUTED the canonical-fill
contractibility conjecture as stated (I/Q-cells kill within-fan cycles but not cycles between
defects of different levels; ledger L21).  Gate G3 returned PARITY-BLIND-UNDER-ESCALATION for
all three window-level gain invariants against the de-mechanized parity load (ledger L22) —
the pre-registered honest outcome recorded, not adjusted.

This file formalizes the two green payoffs:

* **`balanced_window_has_twin`** — the counting bridge with the correct polarity: if every
  non-maximal survivor of a window has gain zero (`GainBalanced`) and there are at least two
  survivors, the window CONTAINS a twin center.  Balance certifies twins; frustration only
  certifies a non-twin transit survivor.
* **`tFill_relative_euler`** — the χ-level general form of the confirmed G1 law: on a
  forward-closed window the relative Euler characteristic of the T-filled quotient equals
  `1 − (E_SK + E_KS − 1)`, i.e. the whole quadratic tournament noise cancels against the
  cone-fill by Pascal's rule (`C(v,2) = C(v−1,2) + (v−1)`) — the structural halves
  (`b₀ = 1`, `b₂ = 0`) are certified per-window by `IntRankCert` (`Step00RankCertificate`).
-/

namespace EuclidsPath
namespace GainLayer

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.GeometryFront
open EuclidsPath.GradedWindowComplex
open EuclidsPath.OrnamentTwoComplex
open ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- The ℤ²-gain of a center: graded distance of the two wings from the prime line. -/
def wingGain (m : ℕ) : ℕ × ℕ := (Ω (6 * m - 1) - 1, Ω (6 * m + 1) - 1)

/-- Twins are exactly the gain-zero clean centers (pointwise, both directions). -/
theorem wingGain_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) :
    wingGain m = (0, 0) ↔ TwinCenterZ m := by
  rw [wingGain, Prod.mk.injEq]
  constructor
  · rintro ⟨hL, hR⟩
    have hposL : 0 < Ω (6 * m - 1) := cardFactors_pos_iff_one_lt.mpr (by omega)
    have hposR : 0 < Ω (6 * m + 1) := cardFactors_pos_iff_one_lt.mpr (by omega)
    exact ⟨cardFactors_eq_one_iff_prime.mp (by omega),
      cardFactors_eq_one_iff_prime.mp (by omega)⟩
  · intro h
    rw [cardFactors_eq_one_iff_prime.mpr h.1, cardFactors_eq_one_iff_prime.mpr h.2]
    exact ⟨rfl, rfl⟩

/-- A window is gain-balanced when every non-maximal survivor sits at gain zero. -/
def GainBalanced (A : ℕ) (W : Finset State) : Prop :=
  ∀ n ∈ survivorIdx A W, n ≠ (survivorIdx A W).sup id → wingGain n = (0, 0)

/-- **The counting bridge (green): balance certifies twins.**  Two survivors force a
    non-maximal one; balance puts it at gain zero; gain zero on a clean center is the twin
    state.  Frustration, by contrast, only certifies a NON-twin transit survivor — the
    polarity the assault must respect. -/
theorem balanced_window_has_twin {A : ℕ} {W : Finset State} (hA : 2 ≤ A)
    (h2 : 2 ≤ (survivors A W).card) (hbal : GainBalanced A W) :
    ∃ m ∈ survivorIdx A W, TwinCenterZ m := by
  have hcard : 2 ≤ (survivorIdx A W).card := by
    rw [card_survivorIdx]
    exact h2
  have hne : (survivorIdx A W).Nonempty := Finset.card_pos.mp (by omega)
  have hmin : (survivorIdx A W).min' hne ∈ survivorIdx A W := Finset.min'_mem _ _
  have hlt : (survivorIdx A W).min' hne < (survivorIdx A W).max' hne :=
    Finset.min'_lt_max'_of_card _ (by omega)
  have hsup : (survivorIdx A W).sup id = (survivorIdx A W).max' hne := by
    rw [Finset.max'_eq_sup' _ hne, Finset.sup'_eq_sup]
  have hnotmax : (survivorIdx A W).min' hne ≠ (survivorIdx A W).sup id := by
    rw [hsup]
    omega
  have hgain := hbal _ hmin hnotmax
  have hclean : Clean A ((survivorIdx A W).min' hne) :=
    (mem_survivorIdx.mp hmin).2
  have hm1 : 1 ≤ (survivorIdx A W).min' hne := by
    by_contra h0
    have hz : (survivorIdx A W).min' hne = 0 := by omega
    rw [hz] at hclean
    -- a center 0 cannot be clean once a prime ≤ A exists: 2 ∣ sideValue(minus, 0) = 0
    exact hclean 2 Nat.prime_two hA (Or.inl (by norm_num))
  exact ⟨_, hmin, (wingGain_eq_zero_iff hm1).mp hgain⟩

/-- **The confirmed T-fill law, χ-form (census gate G1: exact on all 36 regions).**
    Relative Euler characteristic of the T-filled quotient:
    `(V_S + 1) − (E_SS + E_SK + E_KS) + C(V_S − 1, 2) = 1 − (E_SK + E_KS − 1)` —
    the tournament noise `C(V_S,2)` cancels against the cone fill `C(V_S−1,2)` by Pascal. -/
theorem tFill_relative_euler {A M0 : ℕ} {W : Finset State}
    (hclosed : ForwardClosed A M0 W) (h1 : 1 ≤ (survivors A W).card) :
    ((survivors A W).card : ℤ) + 1
        - ((eSS A M0 W : ℤ) + (eSK A M0 W : ℤ) + (eKS A M0 W : ℤ))
        + (((survivors A W).card - 1).choose 2 : ℤ)
      = 1 - ((eSK A M0 W : ℤ) + (eKS A M0 W : ℤ) - 1) := by
  have hss := eSS_eq_choose_two hclosed
  obtain ⟨w, hw⟩ : ∃ w, (survivors A W).card = w + 1 :=
    ⟨(survivors A W).card - 1, by omega⟩
  rw [hss, hw]
  have hpascal : (w + 1).choose 2 = w.choose 2 + w := by
    simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ w 1
  have hsimp : (w + 1 - 1 : ℕ) = w := by omega
  rw [hpascal, hsimp]
  push_cast
  ring

end GainLayer
end EuclidsPath
