/-
  GeometricTypeIIWindow — the LITERAL parity-wall formula as a machine theorem (§2–3).

  ORIGIN (parity_wall Prime-Chaos session dossier §2 / §3). The parity wall's most explicit form
  is the twin-sieve window identity: over a finite window `I` in the critical range, the count of
  ACTUAL twin centers equals the exact alternating Möbius–CRT double sum
  `Σ_{S,T ⊆ P} (−1)^{|S|+|T|} · N_{S,T}(I)`,
  where `N_{S,T}` counts the window points struck by every prime of `S` on the lower wing and every
  prime of `T` on the upper wing.  This module proves that identity — previously only the
  free-standing def `MoebiusCRTResidual` — as a THEOREM about real prime counts.  The subset pairs
  `(S,T)` with sign `(−1)^{|S|+|T|}` are exactly the coprime Möbius pairs `(d,e)` via `d = ∏S`,
  `e = ∏T`, `μ(d)μ(e) = (−1)^{|S|+|T|}` (`prod_dvd_iff` provides the divisor dictionary).
  Beautifully, the vanishing of the overlapping pairs `S ∩ T ≠ ∅` in the expansion is EXACTLY the
  sieve fact that no prime `> 2` strikes both wings (`Engine.no_large_shared_divisor`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `prod_one_sub_expand` — the two-indicator product expansion over ALL subset pairs
      (overlapping pairs vanish via `a_p·b_p = 0`);
    * `survivorProd_eq` — the sieve product IS the survivor indicator (`Finset.prod_boole`);
    * `window_identity` — `Σ_{m∈I} ∏_p (1 − a_p − b_p) = Σ_{S,T} (−1)^{|S|+|T|} N_{S,T}(I)`;
    * `survivor_iff_twin` — in the critical range (`1 ≤ m`, `A < 6m−1`, `6m+1 < A²`) the survivor
      condition is EQUIVALENT to `(6m−1).Prime ∧ (6m+1).Prime` (reusing `Residuals.sink_is_twin`
      and the prime-side converse);
    * `twin_sieve_window_identity` — the HEADLINE: the actual twin-center count of the window
      equals the alternating double sum, exactly;
    * `prod_dvd_iff` — the divisor dictionary `∏_{p∈S} p ∣ n ↔ ∀ p ∈ S, p ∣ n`.

  DISCLOSURE (the wall is NOT moved, renamed, or hidden):
    * The window identity IS the parity wall's own formula, not an attack on it: it grounds the
      free-standing `MoebiusCRTResidual` as literal inclusion–exclusion arithmetic and provides
      NO bound on the residual.
    * No progress is made or claimed on residual C (`SemiprimeShortRestriction`), residual D
      (`HigherConductorDispersion`), residual E (`LowFreqRootCoherence`), or `CRE`: under the §110
      gate this module is a VISIBILITY step — neither exact annihilation (A), nor a summability
      gain (B), nor a dimension reduction (C).
    * `survivor_iff_twin` is the classical Legendre criterion, valid ONLY under the stated range
      hypotheses; it restates twin-primality exactly and reduces nothing.
    * This is a finite EXACT identity; no density or distribution claim is made or implied.  This
      module introduces ZERO new open `Prop`s.
    * Nothing here proves twins; the wall is localized, not defeated. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.Carrier
import EuclidsPath.Engine.Residuals

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The two-indicator product expansion (W1–W2) -/

/-- **Disjoint-pair expansion.** `∏_{p∈P}(1 − a_p − b_p)` expands over pairs of DISJOINT subsets;
    no hypothesis on `a, b` (pure `Finset.prod_add` algebra). -/
theorem prod_one_sub_expand_disjoint {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a b : ι → R) :
    ∏ p ∈ P, (1 - a p - b p)
      = ∑ S ∈ P.powerset, ∑ T ∈ (P \ S).powerset,
          (-1) ^ (S.card + T.card) * ((∏ p ∈ S, a p) * ∏ p ∈ T, b p) := by
  have h1 : ∏ p ∈ P, (1 - a p - b p) = ∏ p ∈ P, (-(a p) + (1 - b p)) :=
    Finset.prod_congr rfl fun p _ => by ring
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h2 : ∏ p ∈ P \ S, (1 - b p) = ∏ p ∈ P \ S, (-(b p) + 1) :=
    Finset.prod_congr rfl fun p _ => by ring
  rw [h2, Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_neg, Finset.prod_neg, pow_add]
  ring

/-- **All-pairs expansion (W2).** When `a_p · b_p = 0` pointwise, the expansion runs over ALL
    subset pairs: the overlapping pairs vanish — which, for the twin wings, is EXACTLY the sieve
    fact `no_large_shared_divisor`. -/
theorem prod_one_sub_expand {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a b : ι → R) (hab : ∀ p ∈ P, a p * b p = 0) :
    ∏ p ∈ P, (1 - a p - b p)
      = ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
          (-1) ^ (S.card + T.card) * ((∏ p ∈ S, a p) * ∏ p ∈ T, b p) := by
  rw [prod_one_sub_expand_disjoint P a b]
  refine Finset.sum_congr rfl fun S hS => ?_
  refine Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset) fun T hT hT' => ?_
  have hTP : T ⊆ P := Finset.mem_powerset.mp hT
  obtain ⟨p, hpT, hpS⟩ : ∃ p ∈ T, p ∈ S := by
    by_contra hcon
    push_neg at hcon
    exact hT' (Finset.mem_powerset.mpr fun x hx => Finset.mem_sdiff.mpr ⟨hTP hx, hcon x hx⟩)
  have hzero : a p * b p = 0 := hab p (Finset.mem_powerset.mp hS hpS)
  have hSsplit : ∏ x ∈ S, a x = a p * ∏ x ∈ S.erase p, a x :=
    (Finset.mul_prod_erase S a hpS).symm
  have hTsplit : ∏ x ∈ T, b x = b p * ∏ x ∈ T.erase p, b x :=
    (Finset.mul_prod_erase T b hpT).symm
  rw [hSsplit, hTsplit]
  have hfac : (a p * ∏ x ∈ S.erase p, a x) * (b p * ∏ x ∈ T.erase p, b x)
      = a p * b p * ((∏ x ∈ S.erase p, a x) * ∏ x ∈ T.erase p, b x) := by ring
  rw [hfac, hzero, zero_mul, mul_zero]

/-! ## The twin wing indicators (W3–W5) -/

/-- Indicator (in `ℤ`) that `p` strikes the lower wing `6m − 1`. -/
def aInd (m p : ℕ) : ℤ := if p ∣ 6 * m - 1 then 1 else 0

/-- Indicator (in `ℤ`) that `p` strikes the upper wing `6m + 1`. -/
def bInd (m p : ℕ) : ℤ := if p ∣ 6 * m + 1 then 1 else 0

/-- **No prime `> 2` strikes both wings** — the sieve fact powering the all-pairs expansion. -/
theorem aInd_mul_bInd {m p : ℕ} (hm : 1 ≤ m) (hp : 2 < p) : aInd m p * bInd m p = 0 := by
  unfold aInd bInd
  by_cases h1 : p ∣ 6 * m - 1
  · by_cases h2 : p ∣ 6 * m + 1
    · exact (Engine.no_large_shared_divisor hm hp h2 h1).elim
    · simp [h2]
  · simp [h1]

/-- Each sieve factor is a boolean: `1 − a − b ∈ {0, 1}`. -/
theorem one_sub_aInd_sub_bInd {m p : ℕ} (hm : 1 ≤ m) (hp : 2 < p) :
    (1 : ℤ) - aInd m p - bInd m p
      = if ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1 then 1 else 0 := by
  unfold aInd bInd
  by_cases h1 : p ∣ 6 * m - 1
  · by_cases h2 : p ∣ 6 * m + 1
    · exact (Engine.no_large_shared_divisor hm hp h2 h1).elim
    · simp [h1, h2]
  · by_cases h2 : p ∣ 6 * m + 1 <;> simp [h1, h2]

/-- **The sieve product is the survivor indicator (W5).** -/
theorem survivorProd_eq {m : ℕ} {P : Finset ℕ} (hm : 1 ≤ m) (hP : ∀ p ∈ P, 2 < p) :
    ∏ p ∈ P, (1 - aInd m p - bInd m p)
      = if ∀ p ∈ P, ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1 then (1 : ℤ) else 0 := by
  rw [Finset.prod_congr rfl fun p hp => one_sub_aInd_sub_bInd hm (hP p hp)]
  exact Finset.prod_boole

/-! ## The window identity (W6) -/

private theorem prod_aInd (m : ℕ) (S : Finset ℕ) :
    ∏ p ∈ S, aInd m p = if ∀ p ∈ S, p ∣ 6 * m - 1 then (1 : ℤ) else 0 := by
  unfold aInd
  exact Finset.prod_boole

private theorem prod_bInd (m : ℕ) (T : Finset ℕ) :
    ∏ p ∈ T, bInd m p = if ∀ p ∈ T, p ∣ 6 * m + 1 then (1 : ℤ) else 0 := by
  unfold bInd
  exact Finset.prod_boole

private theorem boole_mul_boole (A B : Prop) [Decidable A] [Decidable B] :
    (if A then (1 : ℤ) else 0) * (if B then 1 else 0) = if A ∧ B then 1 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- **The window identity (§3, W6).** The window sum of the sieve product equals the exact
    alternating double sum over subset pairs, with `N_{S,T}` the REAL strike counts. -/
theorem window_identity (I P : Finset ℕ) (hI : ∀ m ∈ I, 1 ≤ m) (hP : ∀ p ∈ P, 2 < p) :
    ∑ m ∈ I, ∏ p ∈ P, (1 - aInd m p - bInd m p)
      = ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
          (-1) ^ (S.card + T.card)
            * ((I.filter fun m =>
                  (∀ p ∈ S, p ∣ 6 * m - 1) ∧ ∀ p ∈ T, p ∣ 6 * m + 1).card : ℤ) := by
  rw [Finset.sum_congr rfl fun m hm =>
    prod_one_sub_expand P (aInd m) (bInd m) fun p hp => aInd_mul_bInd (hI m hm) (hP p hp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun m _ => by rw [prod_aInd, prod_bInd, boole_mul_boole]]
  rw [Finset.sum_boole]

/-! ## The divisor dictionary (W7) -/

/-- **The divisor dictionary.** For a set of primes, `∏_{p∈S} p ∣ n ↔ ∀ p ∈ S, p ∣ n`: the subset
    pairs `(S,T)` ARE the coprime squarefree Möbius pairs `(d,e) = (∏S, ∏T)` of the dossier's §3
    formula, with `μ(d)μ(e) = (−1)^{|S|+|T|}`. -/
theorem prod_dvd_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n :=
  ⟨fun h _p hp => (Finset.dvd_prod_of_mem _ hp).trans h,
   fun h => Finset.prod_primes_dvd n (fun p hp => (hS p hp).prime) h⟩

/-! ## The critical range: survivor ⟺ twin (W9–W12) -/

/-- All primes `5 ≤ q ≤ A` — the sieving window. -/
def windowPrimes (A : ℕ) : Finset ℕ :=
  (Finset.range (A + 1)).filter fun q => q.Prime ∧ 5 ≤ q

theorem mem_windowPrimes {A q : ℕ} :
    q ∈ windowPrimes A ↔ q.Prime ∧ 5 ≤ q ∧ q ≤ A := by
  simp only [windowPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

/-- **Cleanliness of the survivor (W9).** `q ∈ {2, 3}` never strike (both wings are coprime to 6);
    `5 ≤ q ≤ A` is covered by the survivor hypothesis. -/
theorem survivor_clean {A m : ℕ} (hm : 1 ≤ m)
    (hsurv : ∀ p ∈ windowPrimes A, ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1) :
    ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ 6 * m - 1 ∨ q ∣ 6 * m + 1) := by
  intro q hq hqA
  rcases lt_or_ge q 5 with h5 | h5
  · interval_cases q
    · exact absurd hq (by decide)
    · exact absurd hq (by decide)
    · rintro (h | h) <;> omega
    · rintro (h | h) <;> omega
    · exact absurd hq (by decide)
  · have hmem : q ∈ windowPrimes A := mem_windowPrimes.mpr ⟨hq, h5, hqA⟩
    rintro (h | h)
    · exact (hsurv q hmem).1 h
    · exact (hsurv q hmem).2 h

/-- **Survivor ⟹ twin (W10).** In the critical range the survivor is a twin center
    (reuse of `Residuals.sink_is_twin`). -/
theorem survivor_implies_twin {A m : ℕ} (hm : 1 ≤ m) (hcrit : 6 * m + 1 < A * A)
    (hsurv : ∀ p ∈ windowPrimes A, ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1) :
    (6 * m - 1).Prime ∧ (6 * m + 1).Prime :=
  Residuals.sink_is_twin (by omega) (by omega)
    (lt_of_le_of_lt (by omega : 6 * m - 1 ≤ 6 * m + 1) hcrit) hcrit
    (survivor_clean hm hsurv)

/-- **Twin ⟹ survivor (W11).** Above the sieve horizon (`A < 6m − 1`) a twin center survives:
    a prime `≤ A` dividing a prime wing would have to EQUAL that wing, which exceeds `A`. -/
theorem twin_implies_survivor {A m : ℕ} (hgt : A < 6 * m - 1)
    (htwin : (6 * m - 1).Prime ∧ (6 * m + 1).Prime) :
    ∀ p ∈ windowPrimes A, ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1 := by
  intro p hp
  obtain ⟨hprime, h5, hA⟩ := mem_windowPrimes.mp hp
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rcases (htwin.1.eq_one_or_self_of_dvd p hd) with h1 | hself
    · exact hprime.one_lt.ne' h1
    · omega
  · rcases (htwin.2.eq_one_or_self_of_dvd p hd) with h1 | hself
    · exact hprime.one_lt.ne' h1
    · omega

/-- **Survivor ⟺ twin (the Legendre criterion, W10+W11).** Valid ONLY under the stated range
    hypotheses; an exact restatement, reducing nothing. -/
theorem survivor_iff_twin {A m : ℕ} (hm : 1 ≤ m) (hcrit : 6 * m + 1 < A * A)
    (hgt : A < 6 * m - 1) :
    (∀ p ∈ windowPrimes A, ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1)
      ↔ ((6 * m - 1).Prime ∧ (6 * m + 1).Prime) :=
  ⟨survivor_implies_twin hm hcrit, twin_implies_survivor hgt⟩

/-- **Survivor count = twin count (W12)** on a window inside the critical range. -/
theorem window_survivor_eq_twin_count {A : ℕ} (I : Finset ℕ)
    (hI : ∀ m ∈ I, 1 ≤ m ∧ 6 * m + 1 < A * A ∧ A < 6 * m - 1) :
    (I.filter fun m => ∀ p ∈ windowPrimes A, ¬ p ∣ 6 * m - 1 ∧ ¬ p ∣ 6 * m + 1).card
      = (I.filter fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card := by
  congr 1
  refine Finset.filter_congr fun m hm => ?_
  obtain ⟨h1, h2, h3⟩ := hI m hm
  exact survivor_iff_twin h1 h2 h3

/-! ## The headline: the literal parity-wall formula (W13) -/

/-- **THE TWIN-SIEVE WINDOW IDENTITY (§3).** Over a window `I` in the critical range
    (`1 ≤ m`, `6m+1 < A²`, `A < 6m−1` for all `m ∈ I`), the count of ACTUAL twin centers equals
    the exact alternating Möbius–CRT double sum — the parity wall's own formula, as a machine
    theorem about real prime counts.  A visibility result: it bounds NOTHING; the residual after
    extracting main terms is the same open object as before. -/
theorem twin_sieve_window_identity {A : ℕ} (I : Finset ℕ)
    (hI : ∀ m ∈ I, 1 ≤ m ∧ 6 * m + 1 < A * A ∧ A < 6 * m - 1) :
    ((I.filter fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℤ)
      = ∑ S ∈ (windowPrimes A).powerset, ∑ T ∈ (windowPrimes A).powerset,
          (-1) ^ (S.card + T.card)
            * ((I.filter fun m =>
                  (∀ p ∈ S, p ∣ 6 * m - 1) ∧ ∀ p ∈ T, p ∣ 6 * m + 1).card : ℤ) := by
  have hI1 : ∀ m ∈ I, 1 ≤ m := fun m hm => (hI m hm).1
  have hP : ∀ p ∈ windowPrimes A, 2 < p := fun p hp => by
    have h := mem_windowPrimes.mp hp
    omega
  rw [← window_identity I (windowPrimes A) hI1 hP,
    Finset.sum_congr rfl fun m hm => survivorProd_eq (hI1 m hm) hP,
    Finset.sum_boole]
  exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (window_survivor_eq_twin_count I hI).symm

end TypeII
end Geometric
end EuclidsPath
