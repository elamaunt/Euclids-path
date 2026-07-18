/-
  Engine/GeometricTypeIIPlusWing — the PLUS WING of the Tauberian
  landing: the `6m+1` mirror of stages L-M1 + L-M3, the two-wing
  display, and the per-wing `S < P` ratio form.

  The plus wing differs from the minus wing in exactly two places:
    * NO no-square asymmetry: `6m+1` CAN be `p²` (squares mod 6 land in
      `{0,1,3,4}`), so the rung criterion carries `p ≤ q` where the
      minus wing had `p < q` — the square stratum is ABSORBED into the
      one-sided rung majorant (`p·p ≤ p·q = N ≤ X` still bounds the
      rung, and `q = p` is still counted by `apCount` at scale `X/p`).
      The pointwise criterion is in fact mod-free.
    * The strike rigidity pairs classes `(1,1)/(5,5)` mod 6 (the minus
      wing had `(1,5)/(5,1)`): `plusRungClass p = p`'s own class.

  The analytic core (slices, weights, Mertens caps, budget) is REUSED
  verbatim from `GeometricTypeIIWingSign` — the machinery there is
  class-agnostic; only the class assignment changes.

  DISCLOSURES (mandatory, verbatim frame of the campaign):
    * `two_wing_sign` gives each wing's sign on ITS OWN window (the
      minus window ranges over `m` with `6m−1` rough, the plus window
      over `m` with `6m+1` rough — DIFFERENT `m`-sets).  This is NOT
      the OneWingTarget form: the target needs the SUMMED bias of BOTH
      wings against ONE PAIR-rough count `A` (both `6m±1` rough at the
      SAME `m`).  Three per-wing→pair-rough bridges were refuted;
      OneWingTarget is NOT discharged, NOT premise-shrunk, NOT
      reweighted (twin-strength by pigeonhole).
    * EVENTUAL, NOT EFFECTIVE — sign only, no explicit threshold.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import EuclidsPath.Engine.GeometricTypeIIWingSign

set_option maxHeartbeats 3200000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction Filter
open EuclidsPath.Analytic (apCount)

/-! ### The mod-free rung criterion (`≤`-form, squares absorbed) -/

/-- Forward core, MOD-FREE: a semiprime's smallest prime factor has a
prime cofactor at or above it (`p = q` allowed — the square case). -/
theorem semiprime_minFac_cofactor {N p : ℕ} (hOm2 : cardFactors N = 2)
    (hmf : N.minFac = p) :
    p ∣ N ∧ (N / p).Prime ∧ p ≤ N / p := by
  have hN0 : N ≠ 0 := by
    intro h
    rw [h] at hOm2
    simp at hOm2
  have hN1 : N ≠ 1 := by
    intro h
    rw [h] at hOm2
    simp [ArithmeticFunction.cardFactors_one] at hOm2
  subst hmf
  have hp : N.minFac.Prime := Nat.minFac_prime hN1
  have hdvd : N.minFac ∣ N := N.minFac_dvd
  have hfact : N.minFac * (N / N.minFac) = N := Nat.mul_div_cancel' hdvd
  have hq0 : N / N.minFac ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfact
    exact hN0 hfact.symm
  have hOm : cardFactors N
      = cardFactors N.minFac + cardFactors (N / N.minFac) := by
    conv_lhs => rw [← hfact]
    rw [cardFactors_mul hp.ne_zero hq0]
  rw [cardFactors_apply_prime hp] at hOm
  have hq1 : cardFactors (N / N.minFac) = 1 := by omega
  have hqprime : (N / N.minFac).Prime := cardFactors_eq_one_iff_prime.mp hq1
  have hqdvd : N / N.minFac ∣ N := Nat.div_dvd_of_dvd hdvd
  exact ⟨hdvd, hqprime, Nat.minFac_le_of_dvd hqprime.two_le hqdvd⟩

/-- Backward core, `≤`-form: a prime `p` with prime cofactor at or above
it makes `N` a semiprime with `minFac N = p` (the square case included). -/
theorem semiprime_of_prime_cofactor_le {N p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ N) (hq : (N / p).Prime) (hle : p ≤ N / p) :
    cardFactors N = 2 ∧ N.minFac = p := by
  have hNfact : p * (N / p) = N := Nat.mul_div_cancel' hdvd
  have hOm : cardFactors N = 2 := by
    conv_lhs => rw [← hNfact]
    rw [cardFactors_mul hp.ne_zero hq.ne_zero, cardFactors_apply_prime hp,
      cardFactors_apply_prime hq]
  have hN1 : N ≠ 1 := by
    have h4 : 2 * 2 ≤ p * (N / p) := Nat.mul_le_mul hp.two_le hq.two_le
    omega
  have hminle : N.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hdvd
  have hmem : N.minFac = p ∨ N.minFac = N / p := by
    have hd : N.minFac ∣ p * (N / p) := by
      rw [hNfact]
      exact N.minFac_dvd
    rcases (Nat.minFac_prime hN1).dvd_mul.mp hd with h | h
    · exact Or.inl
        ((Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hN1) hp).mp h)
    · exact Or.inr
        ((Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hN1) hq).mp h)
  refine ⟨hOm, ?_⟩
  rcases hmem with h | h
  · exact h
  · omega

/-- **THE PLUS-WING RUNG CRITERION** (mod-free, `≤`-form): "semiprime
with smallest prime `p`" is EXACTLY "prime cofactor at or above `p`". -/
theorem plus_wing_rung_criterion {N p : ℕ} (hp : p.Prime) :
    (cardFactors N = 2 ∧ N.minFac = p)
      ↔ (p ∣ N ∧ (N / p).Prime ∧ p ≤ N / p) :=
  ⟨fun ⟨h2, hmf⟩ => semiprime_minFac_cofactor h2 hmf,
    fun ⟨h1, h2, h3⟩ => semiprime_of_prime_cofactor_le hp h1 h2 h3⟩

/-- **Mod-6 rigidity of plus strikes**: `p·n ≡ 1 (mod 6)` forces the
paired classes `(1,1)` or `(5,5)` mod 6. -/
theorem plus_strike_congruence {p n N : ℕ} (hN1 : N % 6 = 1)
    (h : p * n = N) :
    (p % 6 = 1 ∧ n % 6 = 1) ∨ (p % 6 = 5 ∧ n % 6 = 5) := by
  have hmod : (p % 6) * (n % 6) % 6 = 1 := by
    rw [← Nat.mul_mod, h]
    exact hN1
  have hp6 : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hn6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases hp : p % 6 <;> interval_cases hn : n % 6 <;> omega

/-! ### The plus fibering (mirrors of the minus ladder, `≤`-form) -/

theorem plus_rung_prime_of_mem_image {I : Finset ℕ} {p : ℕ}
    (hp : p ∈ (I.filter fun m => cardFactors (6 * m + 1) = 2).image
      (fun m => (6 * m + 1).minFac)) : p.Prime := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
  have hOm2 : cardFactors (6 * m + 1) = 2 := (Finset.mem_filter.mp hm).2
  have hN1 : 6 * m + 1 ≠ 1 := by
    intro h
    rw [h] at hOm2
    simp [ArithmeticFunction.cardFactors_one] at hOm2
  exact Nat.minFac_prime hN1

theorem plus_window_rung_fiber (I : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    (I.filter fun m => cardFactors (6 * m + 1) = 2).filter
        (fun m => (6 * m + 1).minFac = p)
      = I.filter fun m => p ∣ (6 * m + 1) ∧ ((6 * m + 1) / p).Prime
          ∧ p ≤ (6 * m + 1) / p := by
  rw [Finset.filter_filter]
  exact Finset.filter_congr fun m _ => plus_wing_rung_criterion hp

theorem plus_window_semiprime_rung_decomposition (I : Finset ℕ) :
    (I.filter fun m => cardFactors (6 * m + 1) = 2).card
      = ∑ p ∈ (I.filter fun m => cardFactors (6 * m + 1) = 2).image
          (fun m => (6 * m + 1).minFac),
        (I.filter fun m => p ∣ (6 * m + 1) ∧ ((6 * m + 1) / p).Prime
          ∧ p ≤ (6 * m + 1) / p).card := by
  rw [Finset.card_eq_sum_card_image (fun m => (6 * m + 1).minFac)
    (I.filter fun m => cardFactors (6 * m + 1) = 2)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [plus_window_rung_fiber I (plus_rung_prime_of_mem_image hp)]

theorem plus_rung_count_eq_cofactor_count (I : Finset ℕ) {p : ℕ} :
    (I.filter fun m => p ∣ (6 * m + 1) ∧ ((6 * m + 1) / p).Prime
      ∧ p ≤ (6 * m + 1) / p).card
      = ((I.filter fun m => p ∣ (6 * m + 1) ∧ ((6 * m + 1) / p).Prime
          ∧ p ≤ (6 * m + 1) / p).image (fun m => (6 * m + 1) / p)).card := by
  refine (Finset.card_image_of_injOn ?_).symm
  intro m₁ hm₁ m₂ hm₂ heq
  have heq' : (6 * m₁ + 1) / p = (6 * m₂ + 1) / p := heq
  have hd₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hm₁)).2.1
  have hd₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hm₂)).2.1
  have h₁ := Nat.mul_div_cancel' hd₁
  have h₂ := Nat.mul_div_cancel' hd₂
  rw [← heq'] at h₂
  omega

theorem mem_plus_rung_cofactor_image (I : Finset ℕ) {p : ℕ} (hp : p.Prime)
    {q : ℕ} :
    q ∈ (I.filter fun m => p ∣ (6 * m + 1) ∧ ((6 * m + 1) / p).Prime
        ∧ p ≤ (6 * m + 1) / p).image (fun m => (6 * m + 1) / p)
      ↔ q.Prime ∧ p ≤ q ∧ ∃ m ∈ I, 6 * m + 1 = p * q := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hmI, hdvd, hqp, hle⟩ := Finset.mem_filter.mp hm
      |>.imp id fun h => h
    exact ⟨hqp, hle, m, hmI, (Nat.mul_div_cancel' hdvd).symm⟩
  · rintro ⟨hq, hle, m, hmI, hfact⟩
    refine ⟨m, Finset.mem_filter.mpr ⟨hmI, ⟨q, hfact⟩, ?_, ?_⟩, ?_⟩
    · rw [hfact, Nat.mul_div_cancel_left q hp.pos]
      exact hq
    · rw [hfact, Nat.mul_div_cancel_left q hp.pos]
      exact hle
    · rw [hfact, Nat.mul_div_cancel_left q hp.pos]

/-! ### The plus window objects (M1 mirror) -/

/-- The FULL rough plus window: `m` with `z < 6m+1 ≤ X` and
`minFac(6m+1) > z`. -/
def plusRoughWindow (X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m =>
    z < 6 * m + 1 ∧ 6 * m + 1 ≤ X ∧ z < (6 * m + 1).minFac

/-- The prime count of the plus wing. -/
def plusWingP (X z : ℕ) : ℕ :=
  ((plusRoughWindow X z).filter fun m => (6 * m + 1).Prime).card

/-- The semiprime count of the plus wing. -/
def plusWingS (X z : ℕ) : ℕ :=
  ((plusRoughWindow X z).filter fun m => cardFactors (6 * m + 1) = 2).card

/-- The forced cofactor class of a plus-wing rung (`(1,1)/(5,5)` strike
rigidity: the cofactor inherits the strike's own class). -/
def plusRungClass (p : ℕ) : ℕ := if p % 6 = 1 then 1 else 5

theorem plusRungClass_or (p : ℕ) : plusRungClass p = 1 ∨ plusRungClass p = 5 := by
  unfold plusRungClass
  split <;> simp

/-! ### The Ω-dichotomy and the Liouville identity -/

theorem plusRoughWindow_omega {X z : ℕ} (_hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∀ m ∈ plusRoughWindow X z,
      cardFactors (6 * m + 1) = 1 ∨ cardFactors (6 * m + 1) = 2 := by
  intro m hm
  obtain ⟨hmI, hzN, hNX, hmf⟩ := Finset.mem_filter.mp hm |>.imp id fun h => h
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
  have hN1 : 1 < 6 * m + 1 := by omega
  have hN3 : 6 * m + 1 < z ^ 3 := lt_of_le_of_lt hNX hXz
  have hle : cardFactors (6 * m + 1) ≤ 2 := by
    refine rough_omega_le_two hN1 hN3 fun p hp hdvd => ?_
    calc z < (6 * m + 1).minFac := hmf
      _ ≤ p := Nat.minFac_le_of_dvd hp.two_le hdvd
  have hge : 1 ≤ cardFactors (6 * m + 1) := by
    by_contra h
    have h0 : (6 * m + 1).primeFactorsList = [] := by
      rw [← List.length_eq_zero_iff]
      rw [← ArithmeticFunction.cardFactors_apply]
      omega
    rcases (Nat.primeFactorsList_eq_nil _).mp h0 with h | h <;> omega
  omega

theorem plusWindow_liouville_eq {X z : ℕ} (hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∑ m ∈ plusRoughWindow X z, ((-1 : ℤ)) ^ (cardFactors (6 * m + 1))
      = (plusWingS X z : ℤ) - (plusWingP X z : ℤ) := by
  have hw := plusRoughWindow_omega hz hXz
  have hsum := rough_window_liouville_sum (plusRoughWindow X z)
    (fun m => 6 * m + 1) hw
  have hsplit := rough_window_prime_semiprime_split (plusRoughWindow X z)
    (fun m => 6 * m + 1) hw
  have hnot := Finset.card_filter_add_card_filter_not
    (s := plusRoughWindow X z) (fun m => (6 * m + 1).Prime)
  rw [hsum]
  unfold plusWingS plusWingP
  omega

/-! ### The prime side in `apCount` vocabulary (additive form) -/

theorem plusWingP_add_apCount {X z : ℕ} (hzX : z ≤ X) :
    plusWingP X z + apCount 1 z = apCount 1 X := by
  have h1 : plusWingP X z = ((Finset.Icc 1 X).filter
      fun n => n.Prime ∧ n % 6 = 1 ∧ z < n).card := by
    unfold plusWingP plusRoughWindow
    rw [Finset.filter_filter]
    apply Finset.card_nbij (i := fun m => 6 * m + 1)
    · intro m hm
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨h1m, hmX⟩, ⟨hzN, hNX, hmf⟩, hprime⟩ := hm
      show (6 * m + 1) ∈ _
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hNX⟩, hprime, by omega, hzN⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc]
        at hm₁ hm₂
      simp only at heq
      omega
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hn
      obtain ⟨⟨h1n, hnX⟩, hprime, hmod, hzn⟩ := hn
      have hn7 : 7 ≤ n := by
        by_contra hlt
        push Not at hlt
        interval_cases n <;> revert hprime hmod <;> decide
      have h6 : 6 * (n / 6) + 1 = n := by omega
      refine ⟨n / 6, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega, ?_⟩, ?_⟩
        · rw [h6, Nat.Prime.minFac_eq hprime]
          exact hzn
        · rw [h6]
          exact hprime
      · show 6 * (n / 6) + 1 = n
        exact h6
  have h2 : apCount 1 X = ((Finset.Icc 1 X).filter
      fun n => n.Prime ∧ n % 6 = 1 ∧ z < n).card + apCount 1 z := by
    show ((Finset.Icc 1 X).filter fun n => n.Prime ∧ n % 6 = 1).card = _
      + ((Finset.Icc 1 z).filter fun n => n.Prime ∧ n % 6 = 1).card
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

/-! ### The semiprime side: the plus rung-ladder majorant -/

/-- **THE PLUS LADDER**: the semiprime count of the plus wing is
dominated by `apCount`s at the rung scales `X/p` in the FORCED classes
(the square stratum `q = p` is absorbed by the `≤` in the criterion). -/
theorem plusWingS_le_rung_sum {X z : ℕ} :
    plusWingS X z
      ≤ ∑ p ∈ rungPrimes X z, apCount (plusRungClass p) (X / p) := by
  unfold plusWingS
  rw [plus_window_semiprime_rung_decomposition (plusRoughWindow X z)]
  refine le_trans (Finset.sum_le_sum ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Nat.zero_le _)
  · -- per-rung: the fiber is dominated by the AP prime count at scale X/p
    intro p hp
    have hpp : p.Prime := plus_rung_prime_of_mem_image hp
    rw [plus_rung_count_eq_cofactor_count]
    show _ ≤ ((Finset.Icc 1 (X / p)).filter
      fun n => n.Prime ∧ n % 6 = plusRungClass p).card
    apply Finset.card_le_card
    intro q hq
    rw [mem_plus_rung_cofactor_image _ hpp] at hq
    obtain ⟨hqp, hpq, m, hmI, hfact⟩ := hq
    have hmm := Finset.mem_filter.mp hmI
    have hmIcc := hmm.1
    obtain ⟨hzN, hNX, hmf⟩ := hmm.2
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hqp.one_lt.le, ?_⟩, hqp, ?_⟩
    · rw [Nat.le_div_iff_mul_le hpp.pos]
      calc q * p = p * q := Nat.mul_comm _ _
        _ = 6 * m + 1 := hfact.symm
        _ ≤ X := hNX
    · have hN1 : (6 * m + 1) % 6 = 1 := by omega
      rcases plus_strike_congruence hN1 hfact.symm with ⟨hp1, hq1⟩ | ⟨hp5, hq5⟩
      · rw [plusRungClass, if_pos hp1]
        exact hq1
      · rw [plusRungClass, if_neg (by omega)]
        exact hq5
  · -- the minFac image sits inside the rung index set
    intro p hp
    have hpp : p.Prime := plus_rung_prime_of_mem_image hp
    obtain ⟨m, hm, hpeq⟩ := Finset.mem_image.mp hp
    obtain ⟨hmWin, hOm⟩ := Finset.mem_filter.mp hm
    have hmm := Finset.mem_filter.mp hmWin
    have hmIcc := hmm.1
    obtain ⟨hzN, hNX, hmf⟩ := hmm.2
    have hcrit := (plus_wing_rung_criterion (N := 6 * m + 1) hpp).mp
      ⟨hOm, hpeq⟩
    obtain ⟨hdvd, hqprime, hple⟩ := hcrit
    have hppX : p * p ≤ X := by
      have h1 : p * p ≤ p * ((6 * m + 1) / p) :=
        Nat.mul_le_mul_left p hple
      have h2 : p * ((6 * m + 1) / p) = 6 * m + 1 :=
        Nat.mul_div_cancel' hdvd
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hpp.one_lt.le, ?_⟩, hpp, ?_, hppX⟩
    · have : p * 1 ≤ p * p := Nat.mul_le_mul_left p hpp.one_lt.le
      omega
    · rw [← hpeq]
      exact hmf

/-! ### THE PLUS CROWN -/

/-- **THE WING SIGN THEOREM, PLUS WING (conditional form).**  Mirror of
`minus_wing_sign_of_apPNT` — same slices, same weights, same budget;
the prime side lives in class 1 mod 6, the rungs in classes `(1,1)/(5,5)`.

DISCLOSURE: per-wing count-level sign — OneWingTarget untouched. -/
theorem plus_wing_sign_of_apPNT
    (hAP : ∀ a : ℕ, a = 1 ∨ a = 5 →
      Tendsto (fun n : ℕ => (apCount a n : ℝ) * (2 * Real.log n) / n)
        atTop (nhds 1)) :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ plusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
        ≤ -(1 / 40) * X / Real.log X := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (interface_bounds (hAP 1 (Or.inl rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp
    (interface_bounds (hAP 5 (Or.inr rfl)) (by norm_num : (0 : ℝ) < 1 / 1000))
  have hlogT : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzsm : ∀ᶠ n : ℕ in atTop,
      Real.log n / (n : ℝ) ^ ((11 : ℝ) / 20) ≤ 1 / 200 := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ((11 : ℝ) / 20))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.comp tendsto_natCast_atTop_atTop
    have h3 := Metric.tendsto_nhds.mp h2 (1 / 200) (by norm_num)
    filter_upwards [h3] with n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hn
    exact hn.2.le
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (2 ^ 80),
    eventually_ge_atTop N₁, eventually_ge_atTop ((max N₁ N₅ + 2) ^ 3),
    hlogT.eventually_ge_atTop 8000, hzsm]
    with X h2X hbig hN1X hNc h8000 hzs
  intro z h7 h9
  obtain ⟨hz2, hXz3, hzzX, h14⟩ := z_facts h2X h7 h9
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by exact_mod_cast h2X)
  have hzN : max N₁ N₅ + 2 ≤ z := by
    have h1 : (max N₁ N₅ + 2) ^ 20 ≤ z ^ 20 := by
      calc (max N₁ N₅ + 2) ^ 20
          ≤ (max N₁ N₅ + 2) ^ 21 :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ = ((max N₁ N₅ + 2) ^ 3) ^ 7 := by ring
        _ ≤ X ^ 7 := Nat.pow_le_pow_left hNc 7
        _ ≤ z ^ 20 := h7
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hup : ∀ a : ℕ, a = 1 ∨ a = 5 → ∀ m : ℕ, z < m →
      (apCount a m : ℝ) * (2 * Real.log m) ≤ (1 + 1 / 1000) * m := by
    intro a ha m hzm
    rcases ha with rfl | rfl
    · exact (hN₁ m (by have := le_max_left N₁ N₅; omega)).2
    · exact (hN₅ m (by have := le_max_right N₁ N₅; omega)).2
  have hsum := plusWindow_liouville_eq (X := X) (z := z) (by omega) hXz3
  have hsumR : ((∑ m ∈ plusRoughWindow X z,
        ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
      = (plusWingS X z : ℝ) - (plusWingP X z : ℝ) := by
    rw [hsum]
    push_cast
    ring
  have hzX : z ≤ X := by
    calc z = z * 1 := by ring
      _ ≤ z * z := Nat.mul_le_mul_left z (by omega)
      _ ≤ X := hzzX
  have hPcast : (plusWingP X z : ℝ)
      = (apCount 1 X : ℝ) - (apCount 1 z : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (plusWingP_add_apCount (X := X) (z := z) hzX)
    push_cast at h
    linarith
  have hP1X : (1 - 1 / 1000) * X / (2 * Real.log X) ≤ (apCount 1 X : ℝ) :=
    apCount_lower_of_bound (hN₁ X hN1X).1 h2X
  have hz_apc : (apCount 1 z : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast apCount_le 1 z
  have hzrpow : (z : ℝ) ≤ (X : ℝ) ^ ((9 : ℝ) / 20) := by
    have h40 : ((X : ℝ) ^ ((9 : ℝ) / 20)) ^ (20 : ℕ) = (X : ℝ) ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ ((9 : ℝ) / 20)) 20,
        ← Real.rpow_mul hX0.le,
        show (((20 : ℕ) : ℝ)) = (20 : ℝ) from by norm_num,
        div_mul_cancel₀ _ (by norm_num : (20 : ℝ) ≠ 0),
        show ((9 : ℝ)) = (((9 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast]
    have hc : ((z : ℝ)) ^ (20 : ℕ) ≤ ((X : ℝ)) ^ (9 : ℕ) := by
      exact_mod_cast h9
    rw [← h40] at hc
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hX0.le _) hc
  have hzterm : (z : ℝ) ≤ (1 / 100) * ((X : ℝ) / (2 * Real.log X)) := by
    have hrp : (0 : ℝ) < (X : ℝ) ^ ((11 : ℝ) / 20) := by positivity
    have h200 : 200 * Real.log X ≤ (X : ℝ) ^ ((11 : ℝ) / 20) := by
      rw [div_le_iff₀ hrp] at hzs
      linarith
    have hsplit : (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20)
        = (X : ℝ) := by
      rw [← Real.rpow_add hX0,
        show (9 : ℝ) / 20 + 11 / 20 = 1 from by norm_num, Real.rpow_one]
    have hmul : (z : ℝ) * (200 * Real.log X) ≤ (X : ℝ) := by
      calc (z : ℝ) * (200 * Real.log X)
          ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (200 * Real.log X) :=
            mul_le_mul_of_nonneg_right hzrpow (by positivity)
        _ ≤ (X : ℝ) ^ ((9 : ℝ) / 20) * (X : ℝ) ^ ((11 : ℝ) / 20) :=
            mul_le_mul_of_nonneg_left h200 (by positivity)
        _ = (X : ℝ) := hsplit
    rw [show (1 / 100 : ℝ) * ((X : ℝ) / (2 * Real.log X))
      = (X : ℝ) / (200 * Real.log X) from by ring]
    rw [le_div_iff₀ (by positivity)]
    exact hmul
  have hScast : (plusWingS X z : ℝ)
      ≤ ∑ p ∈ rungPrimes X z, (apCount (plusRungClass p) (X / p) : ℝ) := by
    have h := plusWingS_le_rung_sum (X := X) (z := z)
    calc (plusWingS X z : ℝ)
        ≤ ((∑ p ∈ rungPrimes X z,
            apCount (plusRungClass p) (X / p) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = ∑ p ∈ rungPrimes X z, (apCount (plusRungClass p) (X / p) : ℝ) := by
          push_cast
          rfl
  have hSup := rung_sum_le (X := X) (z := z) plusRungClass plusRungClass_or
    (by norm_num : (0 : ℝ) < 1 / 1000) hbig h14 hup
  have h80 : 80 / Real.log X ≤ 1 / 100 := by
    rw [div_le_iff₀ hlogX]
    linarith
  have h80pos : (0 : ℝ) ≤ 80 / Real.log X := by positivity
  have hprod : (1 + 1 / 1000) * (wingK * (1 + 80 / Real.log X))
      ≤ 0.936 := by
    have hb1 : wingK * (1 + 80 / Real.log X) ≤ 0.925 * (1 + 1 / 100) :=
      mul_le_mul wingK_le (by linarith) (by linarith) (by norm_num)
    nlinarith
  have hA0 : (0 : ℝ) ≤ (X : ℝ) / (2 * Real.log X) := by positivity
  have hSfinal : (plusWingS X z : ℝ)
      ≤ 0.936 * ((X : ℝ) / (2 * Real.log X)) := by
    calc (plusWingS X z : ℝ)
        ≤ (1 + 1 / 1000) * ((X : ℝ) / (2 * Real.log X)) * wingK
            * (1 + 80 / Real.log X) := hScast.trans hSup
      _ = ((X : ℝ) / (2 * Real.log X))
            * ((1 + 1 / 1000) * (wingK * (1 + 80 / Real.log X))) := by ring
      _ ≤ ((X : ℝ) / (2 * Real.log X)) * 0.936 :=
          mul_le_mul_of_nonneg_left hprod hA0
      _ = 0.936 * ((X : ℝ) / (2 * Real.log X)) := by ring
  have hPfinal : 0.989 * ((X : ℝ) / (2 * Real.log X))
      ≤ (plusWingP X z : ℝ) := by
    have h999 : (1 - 1 / 1000) * X / (2 * Real.log X)
        = 0.999 * ((X : ℝ) / (2 * Real.log X)) := by ring
    rw [hPcast]
    rw [h999] at hP1X
    linarith
  rw [hsumR]
  have hfin : (plusWingS X z : ℝ) - (plusWingP X z : ℝ)
      ≤ -(1 / 20) * ((X : ℝ) / (2 * Real.log X)) := by linarith
  calc (plusWingS X z : ℝ) - (plusWingP X z : ℝ)
      ≤ -(1 / 20) * ((X : ℝ) / (2 * Real.log X)) := hfin
    _ = -(1 / 40) * X / Real.log X := by ring

/-- **THE PLUS CROWN (unconditional).**  Mirror of `minus_wing_sign`.

DISCLOSURES: per-wing count-level sign ONLY — OneWingTarget is NOT
discharged/shrunk/reweighted; the surviving core is the PAIR-rough
coupling.  Eventual, not effective.  twin sorry untouched. -/
theorem plus_wing_sign :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ plusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
        ≤ -(1 / 40) * X / Real.log X :=
  plus_wing_sign_of_apPNT fun _ ha =>
    EuclidsPath.Analytic.apCount_mul_log_div_tendsto ha

/-- Display form: the plus-window bias is eventually strictly negative. -/
theorem plus_wing_sign_neg :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      (∑ m ∈ plusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) < 0 := by
  filter_upwards [plus_wing_sign, eventually_ge_atTop 2] with X hX h2X
  intro z h7 h9
  have h := hX z h7 h9
  have hlogX : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast h2X)
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    linarith
  have hneg : ((∑ m ∈ plusRoughWindow X z,
      ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ) < 0 := by
    have : -(1 / 40 : ℝ) * X / Real.log X < 0 := by
      apply div_neg_of_neg_of_pos _ hlogX
      nlinarith
    linarith
  exact_mod_cast hneg

/-! ### The two-wing display and the `S < P` ratio forms -/

/-- **TWO-WING SIGN (unconditional).**  Eventually BOTH wings carry the
negative bias on the SAME `(X, z)` parameters.

DISCLOSURE (verbatim, load-bearing): the two windows are DIFFERENT
`m`-sets (minus: `6m−1` rough; plus: `6m+1` rough).  This is NOT the
OneWingTarget form, which needs the SUMMED bias of both wings against
ONE PAIR-rough count (both `6m±1` rough at the SAME `m`).  Three
per-wing→pair-rough bridges were refuted; OneWingTarget is NOT
discharged.  twin sorry untouched. -/
theorem two_wing_sign :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      ((∑ m ∈ minusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m - 1)) : ℤ) : ℝ)
        ≤ -(1 / 40) * X / Real.log X
      ∧ ((∑ m ∈ plusRoughWindow X z,
          ((-1 : ℤ)) ^ (cardFactors (6 * m + 1)) : ℤ) : ℝ)
        ≤ -(1 / 40) * X / Real.log X := by
  filter_upwards [minus_wing_sign, plus_wing_sign] with X h1 h2
  intro z h7 h9
  exact ⟨h1 z h7 h9, h2 z h7 h9⟩

/-- The §13 ratio, minus wing: eventually `S < P` on every full rough
minus window in the θ-range — the semiprime side LOSES to the prime
side (count level). -/
theorem minus_wing_S_lt_P :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      wingS X z < wingP X z := by
  filter_upwards [minus_wing_sign_neg, eventually_ge_atTop 2]
    with X hX h2X
  intro z h7 h9
  obtain ⟨hz2, hXz3, _, _⟩ := z_facts h2X h7 h9
  have hneg := hX z h7 h9
  rw [minusWindow_liouville_eq (by omega) hXz3] at hneg
  omega

/-- The §13 ratio, plus wing: eventually `S < P` on every full rough
plus window in the θ-range. -/
theorem plus_wing_S_lt_P :
    ∀ᶠ X : ℕ in atTop, ∀ z : ℕ, X ^ 7 ≤ z ^ 20 → z ^ 20 ≤ X ^ 9 →
      plusWingS X z < plusWingP X z := by
  filter_upwards [plus_wing_sign_neg, eventually_ge_atTop 2]
    with X hX h2X
  intro z h7 h9
  obtain ⟨hz2, hXz3, _, _⟩ := z_facts h2X h7 h9
  have hneg := hX z h7 h9
  rw [plusWindow_liouville_eq (by omega) hXz3] at hneg
  omega

end TypeII
end Geometric
end EuclidsPath
