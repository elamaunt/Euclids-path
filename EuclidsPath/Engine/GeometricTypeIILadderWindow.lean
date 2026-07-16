/-
  GeometricTypeIILadderWindow — the RUNG DECOMPOSITION of the minus-wing
  Liouville bias: on rough windows,

      Σ_{m∈I} λ(6m−1)  =  Σ_p R_p  −  P

  where `P` counts prime wings and each `R_p` counts, over the `p`-strike
  progression, wings whose COFACTOR `(6m−1)/p` is prime — a prime count at the
  dilated scale `X/p`.  Face B's bias premise (`oneWingTarget_of_liouville_bias`)
  becomes LITERALLY a comparison of prime counts across scales — the
  Buchstab/ladder form of the wall's face B, machine-checked at exact count
  level.

  ORIGIN.  Idea-generation session continuation (ladder × window composition —
  an in-repo idea: the dilation ladder of `GeometricTypeIIDilation` meets the
  window vocabulary of `GeometricTypeIILiouville`).  Design adversarially
  verified (wave-4 pre-pass) with corrections adopted:
    * the fibering and the rung criterion need NO roughness — they are mod-6
      facts (verified on ALL `N ≡ 5 (mod 6) < 3000` against all prime factors
      plus control primes); roughness is load-bearing EXACTLY in the dichotomy
      `P + S = |I|` of the headline;
    * `Nat.minFac_eq_of_prime` is a phantom — the route is `minFac_le_of_dvd` +
      `minFac_prime` + `Prime.dvd_mul` + `prime_dvd_prime_iff_eq`;
    * the fibering uses `Finset.card_eq_sum_card_image` (no MapsTo obligation);
    * the strict `p < N/p` is the minus wing's no-square asymmetry
      (`minus_wing_no_square`) riding inside `rough_minus_semiprime_factor`
      reused at `y := 0` (roughness hypothesis degenerates to `0 < p`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `minus_wing_rung_criterion` — **THE POINTWISE IFF**: for `N ≡ 5 (mod 6)`
      and `p` prime, `Ω(N) = 2 ∧ minFac N = p ⟺ p ∣ N ∧ (N/p).Prime ∧ p < N/p`
      (`p.Prime` load-bearing in ⟸: `N = 725, p = 25`; mod 6 load-bearing in ⟹:
      `N = 25, p = 5` — both counterexamples machine-recorded in the pre-pass);
    * `minus_window_semiprime_rung_decomposition` — **THE FIBERING**
      (roughness-free): the semiprime count of ANY minus-wing window splits
      exactly into rung counts by smallest prime factor;
    * `rough_window_prime_semiprime_split` — `P + S = |I|` on rough windows
      (abstract-wing style; NO repo lemma existed);
    * `rough_minus_window_rung_ladder` — **THE HEADLINE** displayed above, plus
      the grounded corollary discharging `Ω ∈ {1,2}` from real arithmetic
      (`6m−1 < y³`, all prime factors `> y`);
    * `rung_count_eq_cofactor_count` / `mem_rung_cofactor_image` — the q-form:
      each rung count IS a count of PRIMES `q` with `p < q` and `pq` on the
      wing (`m ↦ (6m−1)/p` injective on the rung; `m = (pq+1)/6` recovers).

  NUMERIC GROUNDING (wave-4 pre-pass): on the real rough window `y = 10`,
  `6m−1 ∈ [101, 995]`: `|I| = 103, P = 74, S = 29`, `Σλ = −45 = 29 − 74`; the
  rung fibering `29 = 9+8+4+4+3+1` over rung primes `{11,13,17,19,23,29}`;
  fiber = rung as SETS for every rung prime; the pointwise iff checked on
  17 304 instances; on a RAW (non-rough) window the fibering still holds but
  the headline fails (`Σλ = −24 ≠ −12`) — the dichotomy is load-bearing
  exactly where disclosed.

  DISCLOSURES (mandatory reading before quoting):
    * IDENTITY, NOT ESTIMATE.  The decomposition re-expresses the bias; NO rung
      prime count `R_p` and no window prime count `P` is estimated or bounded;
      the SIGN of `Σλ` (face B's premise) is exactly as open as before.
    * NOT a §110 event — no registered target (CRE, SemiprimeShortRestriction,
      HigherConductorDispersion, LowFreqRootCoherence, OneWingTarget) is
      touched, bounded, or reduced.  Visibility only: face B's premise now
      literally reads "primes at scale `~6·max I` versus cofactor primes at
      scales `~6·max I / p`" — the scales themselves live in prose (repo
      windows are abstract Finsets).
    * λ is the house bare-power convention `(−1)^Ω : ℤ`.
    * ZERO NEW OPEN PROPS.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIDilation

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### The pointwise rung criterion -/

/-- Forward core (mod-6 only, NO roughness): a minus-wing semiprime's smallest
    prime factor `p` has a PRIME cofactor strictly above it — the strictness is
    the wing's no-square asymmetry. -/
theorem minus_wing_minFac_semiprime {N p : ℕ} (hN5 : N % 6 = 5)
    (hOm2 : cardFactors N = 2) (hmf : N.minFac = p) :
    p ∣ N ∧ (N / p).Prime ∧ p < N / p := by
  have hN0 : N ≠ 0 := by omega
  have hN1 : N ≠ 1 := by omega
  obtain ⟨a, b, ha, hb, hne, hab, _, _⟩ :=
    rough_minus_semiprime_factor (y := 0) hN5 hN0 hOm2 fun q hq _ => hq.pos
  subst hmf
  have hadvd : a ∣ N := ⟨b, hab.symm⟩
  have hbdvd : b ∣ N := ⟨a, by rw [← hab]; ring⟩
  have hminle_a : N.minFac ≤ a := Nat.minFac_le_of_dvd ha.two_le hadvd
  have hminle_b : N.minFac ≤ b := Nat.minFac_le_of_dvd hb.two_le hbdvd
  have hmem : N.minFac = a ∨ N.minFac = b := by
    have hd : N.minFac ∣ a * b := by
      rw [hab]
      exact N.minFac_dvd
    rcases (Nat.minFac_prime hN1).dvd_mul.mp hd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hN1) ha).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hN1) hb).mp h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hma : N.minFac = a := by
      rcases hmem with h | h
      · exact h
      · omega
    have hq : N / N.minFac = b := by
      rw [hma]
      exact Nat.div_eq_of_eq_mul_left ha.pos (by rw [← hab]; ring)
    rw [hq]
    refine ⟨?_, hb, by omega⟩
    rw [hma]
    exact hadvd
  · have hmb : N.minFac = b := by
      rcases hmem with h | h
      · omega
      · exact h
    have hq : N / N.minFac = a := by
      rw [hmb]
      exact Nat.div_eq_of_eq_mul_left hb.pos hab.symm
    rw [hq]
    refine ⟨?_, ha, by omega⟩
    rw [hmb]
    exact hbdvd

/-- Backward core (pure arithmetic — no mod 6, no roughness; disclosed): a prime
    `p` with prime cofactor strictly above it makes `N` a semiprime with
    `minFac N = p`. -/
theorem semiprime_of_prime_cofactor {N p : ℕ} (hp : p.Prime) (hdvd : p ∣ N)
    (hq : (N / p).Prime) (hlt : p < N / p) :
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
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hN1) hp).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hN1) hq).mp h)
  refine ⟨hOm, ?_⟩
  rcases hmem with h | h
  · exact h
  · omega

/-- **THE POINTWISE RUNG CRITERION**: on the minus wing, "semiprime with
    smallest prime `p`" is EXACTLY "prime cofactor strictly above `p`". -/
theorem minus_wing_rung_criterion {N p : ℕ} (hN5 : N % 6 = 5) (hp : p.Prime) :
    (cardFactors N = 2 ∧ N.minFac = p)
      ↔ (p ∣ N ∧ (N / p).Prime ∧ p < N / p) :=
  ⟨fun ⟨h2, hmf⟩ => minus_wing_minFac_semiprime hN5 h2 hmf,
    fun ⟨h1, h2, h3⟩ => semiprime_of_prime_cofactor hp h1 h2 h3⟩

/-- Members of the minFac image are prime (no window hypotheses: `Ω = 2` forces
    the wing past `0, 1`). -/
theorem rung_prime_of_mem_image {I : Finset ℕ} {p : ℕ}
    (hp : p ∈ (I.filter fun m => cardFactors (6 * m - 1) = 2).image
      (fun m => (6 * m - 1).minFac)) : p.Prime := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
  have hOm2 : cardFactors (6 * m - 1) = 2 := (Finset.mem_filter.mp hm).2
  have hN1 : 6 * m - 1 ≠ 1 := by
    intro h
    rw [h] at hOm2
    simp [ArithmeticFunction.cardFactors_one] at hOm2
  exact Nat.minFac_prime hN1

/-! ### The fibering (roughness-free) -/

/-- The rung fiber, as a Finset EQUALITY: within the semiprimes, "minFac = p"
    is exactly the rung predicate. -/
theorem minus_window_rung_fiber (I : Finset ℕ) (hm1 : ∀ m ∈ I, 1 ≤ m) {p : ℕ}
    (hp : p.Prime) :
    (I.filter fun m => cardFactors (6 * m - 1) = 2).filter
        (fun m => (6 * m - 1).minFac = p)
      = I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
          ∧ p < (6 * m - 1) / p := by
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun m hm => ?_
  have hN5 : (6 * m - 1) % 6 = 5 := by
    have := hm1 m hm
    omega
  exact minus_wing_rung_criterion hN5 hp

/-- **THE FIBERING** (roughness-free): the semiprime count of ANY minus-wing
    window decomposes exactly into rung counts by smallest prime factor. -/
theorem minus_window_semiprime_rung_decomposition (I : Finset ℕ)
    (hm1 : ∀ m ∈ I, 1 ≤ m) :
    (I.filter fun m => cardFactors (6 * m - 1) = 2).card
      = ∑ p ∈ (I.filter fun m => cardFactors (6 * m - 1) = 2).image
          (fun m => (6 * m - 1).minFac),
        (I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
          ∧ p < (6 * m - 1) / p).card := by
  rw [Finset.card_eq_sum_card_image (fun m => (6 * m - 1).minFac)
    (I.filter fun m => cardFactors (6 * m - 1) = 2)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [minus_window_rung_fiber I hm1 (rung_prime_of_mem_image hp)]

/-! ### The dichotomy and the headline -/

/-- On a rough wing, "composite" is exactly "semiprime" (private congruence used
    by the split and the headline). -/
private theorem not_prime_filter_eq_semiprime_filter (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, cardFactors (w m) = 1 ∨ cardFactors (w m) = 2) :
    I.filter (fun m => ¬(w m).Prime)
      = I.filter fun m => cardFactors (w m) = 2 := by
  refine Finset.filter_congr fun m hm => ?_
  rcases hw m hm with h1 | h2
  · have hprime := cardFactors_eq_one_iff_prime.mp h1
    constructor
    · intro hnp
      exact absurd hprime hnp
    · intro h2'
      rw [h1] at h2'
      exact absurd h2' (by norm_num)
  · constructor
    · intro _
      exact h2
    · intro _ hp
      rw [cardFactors_eq_one_iff_prime.mpr hp] at h2
      exact absurd h2 (by norm_num)

/-- `P + S = |I|` on rough windows (abstract-wing style). -/
theorem rough_window_prime_semiprime_split (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, cardFactors (w m) = 1 ∨ cardFactors (w m) = 2) :
    (I.filter fun m => (w m).Prime).card
      + (I.filter fun m => cardFactors (w m) = 2).card = I.card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := I) (fun m => (w m).Prime)
  rw [not_prime_filter_eq_semiprime_filter I w hw] at hsplit
  exact hsplit

/-- **THE HEADLINE — THE RUNG LADDER**: on rough minus-wing windows,
    `Σ λ(6m−1) = Σ_p R_p − P` — the Liouville bias IS the excess of rung
    cofactor-prime counts (scales `X/p`) over the window prime count (scale
    `X`).  Face B's premise, in Buchstab form. -/
theorem rough_minus_window_rung_ladder (I : Finset ℕ) (hm1 : ∀ m ∈ I, 1 ≤ m)
    (hw : ∀ m ∈ I, cardFactors (6 * m - 1) = 1 ∨ cardFactors (6 * m - 1) = 2) :
    ∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (6 * m - 1))
      = (∑ p ∈ (I.filter fun m => cardFactors (6 * m - 1) = 2).image
            (fun m => (6 * m - 1).minFac),
          ((I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
            ∧ p < (6 * m - 1) / p).card : ℤ))
        - ((I.filter fun m => (6 * m - 1).Prime).card : ℤ) := by
  have h1 := rough_window_liouville_sum I (fun m => 6 * m - 1) hw
  rw [not_prime_filter_eq_semiprime_filter I (fun m => 6 * m - 1) hw] at h1
  have h2 := rough_window_prime_semiprime_split I (fun m => 6 * m - 1) hw
  have h3 := minus_window_semiprime_rung_decomposition I hm1
  have h3' : ((I.filter fun m => cardFactors (6 * m - 1) = 2).card : ℤ)
      = ∑ p ∈ (I.filter fun m => cardFactors (6 * m - 1) = 2).image
          (fun m => (6 * m - 1).minFac),
        ((I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
          ∧ p < (6 * m - 1) / p).card : ℤ) := by
    exact_mod_cast h3
  have h2' : ((I.filter fun m => (6 * m - 1).Prime).card : ℤ)
      + ((I.filter fun m => cardFactors (6 * m - 1) = 2).card : ℤ)
      = (I.card : ℤ) := by
    exact_mod_cast h2
  rw [h1, ← h3']
  linarith

/-- `Ω ≥ 1` past `1` (private helper for the grounded corollary). -/
private theorem one_le_cardFactors_of_one_lt {n : ℕ} (hn : 1 < n) :
    1 ≤ cardFactors n := by
  have hn0 : n ≠ 0 := by omega
  rw [cardFactors_apply]
  by_contra h
  have hlen : n.primeFactorsList.length = 0 := by omega
  have hnil : n.primeFactorsList = [] := List.length_eq_zero_iff.mp hlen
  have hprod := Nat.prod_primeFactorsList hn0
  rw [hnil, List.prod_nil] at hprod
  omega

/-- The headline, GROUNDED: the `Ω ∈ {1,2}` dichotomy discharged from real
    arithmetic (`6m−1 < y³`, all prime factors `> y` — house
    `rough_omega_le_two`). -/
theorem rough_minus_window_rung_ladder_grounded (I : Finset ℕ) (y : ℕ)
    (hm1 : ∀ m ∈ I, 1 ≤ m) (hy : ∀ m ∈ I, 6 * m - 1 < y ^ 3)
    (hrough : ∀ m ∈ I, ∀ p : ℕ, p.Prime → p ∣ (6 * m - 1) → y < p) :
    ∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (6 * m - 1))
      = (∑ p ∈ (I.filter fun m => cardFactors (6 * m - 1) = 2).image
            (fun m => (6 * m - 1).minFac),
          ((I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
            ∧ p < (6 * m - 1) / p).card : ℤ))
        - ((I.filter fun m => (6 * m - 1).Prime).card : ℤ) := by
  refine rough_minus_window_rung_ladder I hm1 fun m hm => ?_
  have hm' := hm1 m hm
  have hn1 : 1 < 6 * m - 1 := by omega
  have hle2 := rough_omega_le_two hn1 (hy m hm) (hrough m hm)
  have hge1 := one_le_cardFactors_of_one_lt hn1
  omega

/-! ### The q-form: rungs are literal prime windows -/

/-- The rung count IS an image count: `m ↦ (6m−1)/p` is injective on the rung
    (the cofactor recovers `m`). -/
theorem rung_count_eq_cofactor_count (I : Finset ℕ) {p : ℕ} :
    (I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
      ∧ p < (6 * m - 1) / p).card
      = ((I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
          ∧ p < (6 * m - 1) / p).image (fun m => (6 * m - 1) / p)).card := by
  refine (Finset.card_image_of_injOn ?_).symm
  intro m₁ hm₁ m₂ hm₂ heq
  have heq' : (6 * m₁ - 1) / p = (6 * m₂ - 1) / p := heq
  have hd₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hm₁)).2.1
  have hd₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hm₂)).2.1
  have h₁ := Nat.mul_div_cancel' hd₁
  have h₂ := Nat.mul_div_cancel' hd₂
  rw [← heq'] at h₂
  omega

/-- Membership in the cofactor image: the rung counts EXACTLY the primes `q`
    with `p < q` whose product `pq` sits on the window's wing. -/
theorem mem_rung_cofactor_image (I : Finset ℕ) {p : ℕ} (hp : p.Prime)
    {q : ℕ} :
    q ∈ (I.filter fun m => p ∣ (6 * m - 1) ∧ ((6 * m - 1) / p).Prime
        ∧ p < (6 * m - 1) / p).image (fun m => (6 * m - 1) / p)
      ↔ q.Prime ∧ p < q ∧ ∃ m ∈ I, 6 * m - 1 = p * q := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hmI, hdvd, hqp, hlt⟩ := Finset.mem_filter.mp hm
      |>.imp id fun h => h
    exact ⟨hqp, hlt, m, hmI, (Nat.mul_div_cancel' hdvd).symm⟩
  · rintro ⟨hq, hlt, m, hmI, hfact⟩
    refine ⟨m, Finset.mem_filter.mpr ⟨hmI, ⟨q, hfact⟩, ?_, ?_⟩, ?_⟩
    · rw [hfact, Nat.mul_div_cancel_left q hp.pos]
      exact hq
    · rw [hfact, Nat.mul_div_cancel_left q hp.pos]
      exact hlt
    · rw [hfact, Nat.mul_div_cancel_left q hp.pos]

/-! ### Kernel demo -/

/-- `209 = 11·19 = 6·35 − 1`: the rung criterion at a concrete semiprime wing. -/
theorem rung_demo_209 : cardFactors 209 = 2 ∧ (209 : ℕ).minFac = 11 := by
  have h209 : (209 : ℕ) = 11 * 19 := by norm_num
  refine semiprime_of_prime_cofactor (by norm_num) ⟨19, h209⟩ ?_ ?_
  · rw [show (209 : ℕ) / 11 = 19 by norm_num]
    norm_num
  · rw [show (209 : ℕ) / 11 = 19 by norm_num]
    norm_num

/-! ### Axiom audit -/

#print axioms minus_wing_rung_criterion
#print axioms minus_window_semiprime_rung_decomposition
#print axioms rough_window_prime_semiprime_split
#print axioms rough_minus_window_rung_ladder
#print axioms rough_minus_window_rung_ladder_grounded
#print axioms rung_count_eq_cofactor_count
#print axioms mem_rung_cofactor_image
#print axioms rung_demo_209

end TypeII
end Geometric
end EuclidsPath
