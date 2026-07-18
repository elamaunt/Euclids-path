/-
  Engine/GeometricTypeIIWingWindow — STAGE L-M1 of the Tauberian campaign
  (minus wing): the WING WINDOW BOOKKEEPING in `apCount` vocabulary.

  Everything here is UNCONDITIONAL and exact (identities and one-sided
  counts): the full rough minus window, its Liouville sum `Σλ = S − P`,
  the prime side as a DIFFERENCE OF `apCount`s (the landing's π(X;6,a)
  spelling, additive form — no ℕ-subtraction), and the semiprime side
  DOMINATED by the rung ladder `S ≤ Σ_p apCount(c_p, X/p)` — the exact
  consumable the wing-sign crown (M3) feeds into PNT-in-AP.

  Reuses (all read in source): the ladder fibering and cofactor lemmas
  (`GeometricTypeIILadderWindow`), the mod-6 strike rigidity
  (`GeometricTypeIIDilation`), the rough-window Liouville sum
  (`GeometricTypeIILiouville`), and the π-wing's `apCount`
  (`Analytic/PrimePiAP`).

  DISCLOSURES.
    * Identities and one-sided counts only; NOTHING is estimated here.
    * No face of the parity wall is touched, and no §110 event is
      claimed.  `OneWingTarget` is NOT touched (twin-strength by
      pigeonhole — the registered disclosure stands).
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTypeIILadderWindow
import EuclidsPath.Engine.GeometricTypeIIDilation
import EuclidsPath.Engine.GeometricTypeIILiouville
import EuclidsPath.Analytic.PrimePiAP

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction
open EuclidsPath.Analytic (apCount)

/-! ### The window objects -/

/-- The FULL rough minus window: `m` with `z < 6m−1 ≤ X` and
`minFac(6m−1) > z` (decidable roughness). -/
def minusRoughWindow (X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m =>
    z < 6 * m - 1 ∧ 6 * m - 1 ≤ X ∧ z < (6 * m - 1).minFac

/-- The prime count of the minus wing. -/
def wingP (X z : ℕ) : ℕ :=
  ((minusRoughWindow X z).filter fun m => (6 * m - 1).Prime).card

/-- The semiprime count of the minus wing. -/
def wingS (X z : ℕ) : ℕ :=
  ((minusRoughWindow X z).filter fun m => cardFactors (6 * m - 1) = 2).card

/-- The rung index set: primes `z < p` with `p² ≤ X`. -/
def rungPrimes (X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun p => p.Prime ∧ z < p ∧ p * p ≤ X

/-- The forced cofactor class of a minus-wing rung (`(1,5)/(5,1)` strike
rigidity). -/
def rungClass (p : ℕ) : ℕ := if p % 6 = 1 then 5 else 1

/-! ### The Ω-dichotomy on the window -/

theorem minusRoughWindow_omega {X z : ℕ} (hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∀ m ∈ minusRoughWindow X z,
      cardFactors (6 * m - 1) = 1 ∨ cardFactors (6 * m - 1) = 2 := by
  intro m hm
  obtain ⟨hmI, hzN, hNX, hmf⟩ := Finset.mem_filter.mp hm |>.imp id fun h => h
  have hN1 : 1 < 6 * m - 1 := by omega
  have hN3 : 6 * m - 1 < z ^ 3 := lt_of_le_of_lt hNX hXz
  have hle : cardFactors (6 * m - 1) ≤ 2 := by
    refine rough_omega_le_two hN1 hN3 fun p hp hdvd => ?_
    calc z < (6 * m - 1).minFac := hmf
      _ ≤ p := Nat.minFac_le_of_dvd hp.two_le hdvd
  have hge : 1 ≤ cardFactors (6 * m - 1) := by
    by_contra h
    have h0 : (6 * m - 1).primeFactorsList = [] := by
      rw [← List.length_eq_zero_iff]
      rw [← ArithmeticFunction.cardFactors_apply]
      omega
    rcases (Nat.primeFactorsList_eq_nil _).mp h0 with h | h <;> omega
  omega

/-! ### The Liouville identity `Σλ = S − P` -/

theorem minusWindow_liouville_eq {X z : ℕ} (hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∑ m ∈ minusRoughWindow X z, ((-1 : ℤ)) ^ (cardFactors (6 * m - 1))
      = (wingS X z : ℤ) - (wingP X z : ℤ) := by
  have hw := minusRoughWindow_omega hz hXz
  have hsum := rough_window_liouville_sum (minusRoughWindow X z)
    (fun m => 6 * m - 1) hw
  have hsplit := rough_window_prime_semiprime_split (minusRoughWindow X z)
    (fun m => 6 * m - 1) hw
  have hnot := Finset.card_filter_add_card_filter_not
    (s := minusRoughWindow X z) (fun m => (6 * m - 1).Prime)
  rw [hsum]
  unfold wingS wingP
  omega

/-! ### The prime side: `wingP` in `apCount` vocabulary (additive form) -/

theorem wingP_add_apCount {X z : ℕ} (hzX : z ≤ X) :
    wingP X z + apCount 5 z = apCount 5 X := by
  have h1 : wingP X z = ((Finset.Icc 1 X).filter
      fun n => n.Prime ∧ n % 6 = 5 ∧ z < n).card := by
    unfold wingP minusRoughWindow
    rw [Finset.filter_filter]
    apply Finset.card_nbij (i := fun m => 6 * m - 1)
    · intro m hm
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨h1m, hmX⟩, ⟨hzN, hNX, hmf⟩, hprime⟩ := hm
      show (6 * m - 1) ∈ _
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hNX⟩, hprime, by omega, hzN⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc]
        at hm₁ hm₂
      have h1 : 1 ≤ m₁ := hm₁.1.1
      have h2 : 1 ≤ m₂ := hm₂.1.1
      simp only at heq
      omega
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hn
      obtain ⟨⟨h1n, hnX⟩, hprime, hmod, hzn⟩ := hn
      have h6 : 6 * ((n + 1) / 6) - 1 = n := by omega
      refine ⟨(n + 1) / 6, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega, ?_⟩, ?_⟩
        · rw [h6, Nat.Prime.minFac_eq hprime]
          exact hzn
        · rw [h6]
          exact hprime
      · show 6 * ((n + 1) / 6) - 1 = n
        exact h6
  have h2 : apCount 5 X = ((Finset.Icc 1 X).filter
      fun n => n.Prime ∧ n % 6 = 5 ∧ z < n).card + apCount 5 z := by
    show ((Finset.Icc 1 X).filter fun n => n.Prime ∧ n % 6 = 5).card = _
      + ((Finset.Icc 1 z).filter fun n => n.Prime ∧ n % 6 = 5).card
    rw [← Finset.card_union_of_disjoint ?_]
    · congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
      constructor
      · rintro ⟨⟨h1n, hnX⟩, hp, hmod⟩
        by_cases hzn : z < n
        · exact Or.inl ⟨⟨h1n, hnX⟩, hp, hmod, hzn⟩
        · exact Or.inr ⟨⟨h1n, by omega⟩, hp, hmod⟩
      · rintro (⟨⟨h1n, hnX⟩, hp, hmod, _⟩ | ⟨⟨h1n, hnz⟩, hp, hmod⟩)
        · exact ⟨⟨h1n, hnX⟩, hp, hmod⟩
        · exact ⟨⟨h1n, by omega⟩, hp, hmod⟩
    · rw [Finset.disjoint_left]
      intro n hn hn'
      have h1 := (Finset.mem_filter.mp hn).2.2.2
      have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn').1).2
      omega
  omega

/-! ### The semiprime side: the rung-ladder majorant -/

/-- **THE CONSUMABLE LADDER**: the semiprime count of the minus wing is
dominated by `apCount`s at the rung scales `X/p` in the FORCED classes. -/
theorem wingS_le_rung_sum {X z : ℕ} :
    wingS X z ≤ ∑ p ∈ rungPrimes X z, apCount (rungClass p) (X / p) := by
  unfold wingS
  rw [minus_window_semiprime_rung_decomposition (minusRoughWindow X z)
    (fun m hm => (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1)]
  refine le_trans (Finset.sum_le_sum ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Nat.zero_le _)
  · -- per-rung: the fiber is dominated by the AP prime count at scale X/p
    intro p hp
    have hpp : p.Prime := rung_prime_of_mem_image hp
    rw [rung_count_eq_cofactor_count]
    show _ ≤ ((Finset.Icc 1 (X / p)).filter
      fun n => n.Prime ∧ n % 6 = rungClass p).card
    apply Finset.card_le_card
    intro q hq
    rw [mem_rung_cofactor_image _ hpp] at hq
    obtain ⟨hqp, hpq, m, hmI, hfact⟩ := hq
    have hmm := Finset.mem_filter.mp hmI
    have hmIcc := hmm.1
    obtain ⟨hzN, hNX, hmf⟩ := hmm.2
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hqp.one_lt.le, ?_⟩, hqp, ?_⟩
    · rw [Nat.le_div_iff_mul_le hpp.pos]
      calc q * p = p * q := Nat.mul_comm _ _
        _ = 6 * m - 1 := hfact.symm
        _ ≤ X := hNX
    · have hN5 : (6 * m - 1) % 6 = 5 := by
        have h1m := (Finset.mem_Icc.mp hmIcc).1
        omega
      rcases strike_congruence hN5 hfact.symm with ⟨hp1, hq5⟩ | ⟨hp5, hq1⟩
      · rw [rungClass, if_pos hp1]
        exact hq5
      · rw [rungClass, if_neg (by omega)]
        exact hq1
  · -- the minFac image sits inside the rung index set
    intro p hp
    have hpp : p.Prime := rung_prime_of_mem_image hp
    obtain ⟨m, hm, hpeq⟩ := Finset.mem_image.mp hp
    obtain ⟨hmWin, hOm⟩ := Finset.mem_filter.mp hm
    have hmm := Finset.mem_filter.mp hmWin
    have hmIcc := hmm.1
    obtain ⟨hzN, hNX, hmf⟩ := hmm.2
    have hN5 : (6 * m - 1) % 6 = 5 := by
      have h1m := (Finset.mem_Icc.mp hmIcc).1
      omega
    have hcrit := (minus_wing_rung_criterion hN5 hpp).mp ⟨hOm, hpeq⟩
    obtain ⟨hdvd, hqprime, hplt⟩ := hcrit
    have hppX : p * p ≤ X := by
      have h1 : p * p < p * ((6 * m - 1) / p) :=
        mul_lt_mul_of_pos_left hplt hpp.pos
      have h2 : p * ((6 * m - 1) / p) = 6 * m - 1 :=
        Nat.mul_div_cancel' hdvd
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hpp.one_lt.le, ?_⟩, hpp, ?_, hppX⟩
    · have : p * 1 ≤ p * p := Nat.mul_le_mul_left p hpp.one_lt.le
      omega
    · rw [← hpeq]
      exact hmf

end TypeII
end Geometric
end EuclidsPath
