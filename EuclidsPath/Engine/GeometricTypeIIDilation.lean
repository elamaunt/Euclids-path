/-
  GeometricTypeIIDilation — the DILATION LADDER of the Liouville sign: the exact
  strike-pair identity `ω(N)·λ(N) = −Σ_{pn=N} λ(n)`, its window form (the ladder),
  the rough affine bridge `2Σ Ωλ = |I| + 3L`, the free squarefree-ness of the rough
  minus wing (`μ = λ` there), and the machine form of the wing asymmetry (no square
  ever lands on the minus wing; prime squares DO land on the plus wing).

  ORIGIN.  Idea-generation session (two-axes program, wave 1b: the algebra axis).
  The algebra panel's finding N-1: among the exact operations available on the wing,
  the dilation `n ↦ p·n` is the unique sign-ODD one — `λ(pn) = −λ(n)` — while the
  exchange `n ↦ (n/p)·q` is sign-EVEN (`neg_one_pow_cardFactors_exchange` in
  Step00OrderedExponentGeometry: exchange preserves `(−1)^Ω`, so exchange-invariant
  constructions cannot see parity).  The ladder identity below is the entry gate of
  the only sign-odd mechanism: it couples the wing sum at scale `X` to Liouville
  sums at the strike scales `X/p` with a FORCED sign flip on every rung — the
  algebraic skeleton on which the only known post-parity result (log-averaged
  two-point Chowla) climbs.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `strikePairs` + `mem_strikePairs` + `strikePairs_card` — the strike-pair set
      `{(p,n) : p prime, p·n = N}` as a Finset, with exactly `ω(N)` members
      (`N ≠ 0` LOAD-BEARING: at `N = 0` the pair set is infinite);
    * `strikePairs_lambda_sum` / `omega_lambda_strike` — **THE STRIKE IDENTITY**:
      `Σ_{(p,n)} λ(n) = −ω(N)·λ(N)` — each strike descends one rung with a sign flip;
    * `wing_dilation_identity` — **THE LADDER**: over ANY window `I` with wing
      `w : ℕ → ℕ`, `Σ_m Ω(w m)λ(w m) = −Σ_m Σ_{(p,n) strikes} λ(n) + correction`,
      the correction being EXPLICIT: `Σ (Ω−ω)(w m)·λ(w m)` — nonzero exactly on
      non-squarefree wings (the `Ω`-vs-`ω` gap is disclosed, never hidden);
    * `wing_dilation_identity_of_squarefree` — the correction VANISHES on squarefree
      wings: there the ladder is exact with no remainder;
    * `strike_congruence` — the mod-6 rigidity of minus-wing strikes: `p·n ≡ 5 (6)`
      forces `(p,n) ≡ (1,5)` or `(5,1) (mod 6)` — every strike pairs the two
      nontrivial classes, none lands in `{2,3}`;
    * `minus_wing_no_square` — **THE WING ASYMMETRY, minus side**: `x² ≡ 5 (mod 6)`
      is IMPOSSIBLE (any `x`, not just primes) — the minus wing carries no squares;
    * `rough_minus_squarefree` / `rough_minus_moebius_eq_liouville` — **μ = λ FOR
      FREE on the rough minus wing**: `Ω ≤ 2` (reuse `rough_omega_le_two`) + no
      squares ⟹ squarefree ⟹ `μ = λ` pointwise — face B's Liouville data and the
      Möbius data of the C/E frame are THE SAME on the rough minus wing;
    * `moebius_ne_liouville_125` — roughness is LOAD-BEARING: `125 = 5³ ≡ 5 (6)` has
      `μ = 0 ≠ −1 = λ` (the smallest witness on the minus wing, pre-pass verified);
    * `rough_minus_semiprime_factor` — the `Ω = 2` rough minus wing element factors
      as `p·q` with `p ≠ q`, BOTH factors rough — the semiprime wing is a genuine
      two-rough-prime object (the B ↔ C/E unification input);
    * `rough_window_omega_lambda_sum` — **THE ROUGH AFFINE BRIDGE**:
      `2·Σ Ω(w m)λ(w m) = |I| + 3·Σ λ(w m)` on rough windows (`Ω ∈ {1,2}` pointwise,
      abstract-wing style; integer-safe doubled form — no division);
    * `rough_window_ladder_cross_check` — `Σ Ωλ = 3·#composite − |I|`: the bridge and
      the house `rough_window_liouville_sum` agree exactly (the pre-pass cross-check
      `3B₋ − |I|` as a machine theorem);
    * `rough_plus_square_thin` + `plus_wing_square_exists` — the plus side of the
      asymmetry: prime squares DO land on the plus wing (`25 = 6·4+1`), and on rough
      windows they are confined to the thin range `y < p`, `p² < y³`.

  NUMERIC GROUNDING (wave-1 pre-pass, adversarial verifier): the strike identity
  exact for ALL `2 ≤ N ≤ 10⁴` (the `Ω`-version fails on exactly the 3917
  non-squarefree `N` — hence the explicit correction term); window forms exact at
  `A = 1,2,3, H = 50` and `A = 1000, H = 200`; the affine bridge exact on the rough
  window `z = 10, N ∈ [100,1000)` (`|I| = 103, P = 74, S = 29`) and on an arbitrary
  non-interval sub-window; `μ = λ` on all 103 rough minus-wing elements; smallest
  minus-wing failure without roughness: `125, 245, 275, …`.

  DISCLOSURES (mandatory reading before quoting):
    * IDENTITIES, NOT ESTIMATES.  The ladder is an entry gate: it re-expresses the
      `Ω`-weighted wing sum through strike scales exactly; it BOUNDS nothing.  The
      ceiling of known mathematics on this mechanism is the log-averaged two-point
      Chowla theorem; the cofinal sign of the wing sum (`OneWingTarget`'s bias
      premise, face B) remains exactly as open as before.
    * NOT A §110 EVENT — visibility only.  No registered target (CRE,
      SemiprimeShortRestriction, HigherConductorDispersion, LowFreqRootCoherence,
      OneWingTarget) is touched, bounded, or reduced.  What is new is that the ONE
      sign-odd exact mechanism now has its entry identity machine-checked, with the
      correction term explicit and the wing asymmetry in theorem form.
    * λ CONVENTION.  Throughout, `λ(n)` is spelled `(−1)^Ω(n)` with
      `Ω = ArithmeticFunction.cardFactors`; at `n = 0` this reads `(−1)^0 = 1` (the
      bare-power convention of the house Liouville module), and every theorem that
      needs it carries `N ≠ 0` explicitly.
    * ZERO NEW OPEN PROPS.  `strikePairs` is a named structural object, NOT a
      target.  The twin sorry is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIILiouville

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### Layer 1 — the strike-pair set and the strike identity -/

/-- **The strike-pair set** `{(p, n) : p prime, p·n = N}`, realized as the image of
    the prime-factor set under `p ↦ (p, N/p)`.  A named structural object, NOT a
    target.  (`N = 0` would make the honest pair set infinite — every theorem below
    carries `N ≠ 0`.) -/
def strikePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  N.primeFactors.map ⟨fun p => (p, N / p), fun a b h => by injection h⟩

/-- The strike-pair set has exactly `ω(N)` members — one rung per distinct prime. -/
theorem strikePairs_card (N : ℕ) : (strikePairs N).card = N.primeFactors.card :=
  Finset.card_map _

/-- Membership characterization: for `N ≠ 0`, the strike pairs are EXACTLY the
    factorizations `p·n = N` with `p` prime. -/
theorem mem_strikePairs {N : ℕ} (hN : N ≠ 0) {r : ℕ × ℕ} :
    r ∈ strikePairs N ↔ r.1.Prime ∧ r.1 * r.2 = N := by
  unfold strikePairs
  rw [Finset.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    exact ⟨hprime, Nat.mul_div_cancel' hdvd⟩
  · rintro ⟨hprime, hmul⟩
    refine ⟨r.1, Nat.mem_primeFactors.mpr ⟨hprime, ⟨r.2, hmul.symm⟩, hN⟩, ?_⟩
    have hdiv : N / r.1 = r.2 :=
      Nat.div_eq_of_eq_mul_left hprime.pos (by rw [← hmul]; ring)
    show (r.1, N / r.1) = r
    rw [hdiv]

/-- **THE STRIKE IDENTITY**: `Σ_{(p,n) ∈ strikes(N)} λ(n) = −ω(N)·λ(N)` — every
    strike descends one rung of the ladder with a forced sign flip
    (`λ(N/p) = −λ(N)`, complete multiplicativity at the prime `p`). -/
theorem strikePairs_lambda_sum {N : ℕ} (hN : N ≠ 0) :
    ∑ r ∈ strikePairs N, ((-1 : ℤ)) ^ (cardFactors r.2)
      = -(N.primeFactors.card : ℤ) * (-1) ^ (cardFactors N) := by
  unfold strikePairs
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hpt : ∀ p ∈ N.primeFactors,
      ((-1 : ℤ)) ^ (cardFactors (N / p)) = -(-1) ^ (cardFactors N) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hNfact : p * (N / p) = N := Nat.mul_div_cancel' hdvd
    have hn0 : N / p ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hNfact
      exact hN hNfact.symm
    have hOm : cardFactors N = 1 + cardFactors (N / p) := by
      conv_lhs => rw [← hNfact]
      rw [cardFactors_mul hprime.ne_zero hn0, cardFactors_apply_prime hprime]
    rw [hOm, pow_add, pow_one]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The strike identity, ladder-ordered: `ω(N)·λ(N) = −Σ_{strikes} λ(n)`. -/
theorem omega_lambda_strike {N : ℕ} (hN : N ≠ 0) :
    (N.primeFactors.card : ℤ) * (-1) ^ (cardFactors N)
      = -∑ r ∈ strikePairs N, ((-1 : ℤ)) ^ (cardFactors r.2) := by
  rw [strikePairs_lambda_sum hN]
  ring

/-! ### Layer 2 — the dilation ladder over a window -/

/-- **THE DILATION LADDER**: over any window `I` with wing `w`, the `Ω`-weighted
    Liouville sum re-expresses through the strike scales with a sign flip, plus the
    EXPLICIT non-squarefree correction `Σ (Ω−ω)λ` — the `Ω` vs `ω` gap is carried in
    the open, never absorbed.  (Pre-pass: the correction-free `Ω`-version is FALSE —
    it fails on exactly the non-squarefree wings, e.g. `N = 4`.) -/
theorem wing_dilation_identity (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, w m ≠ 0) :
    ∑ m ∈ I, (cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))
      = -(∑ m ∈ I, ∑ r ∈ strikePairs (w m), ((-1 : ℤ)) ^ (cardFactors r.2))
        + ∑ m ∈ I, ((cardFactors (w m) : ℤ) - ((w m).primeFactors.card : ℤ))
            * (-1) ^ (cardFactors (w m)) := by
  have hpt : ∀ m ∈ I,
      (cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))
        = -(∑ r ∈ strikePairs (w m), ((-1 : ℤ)) ^ (cardFactors r.2))
          + ((cardFactors (w m) : ℤ) - ((w m).primeFactors.card : ℤ))
              * (-1) ^ (cardFactors (w m)) := by
    intro m hm
    have h := omega_lambda_strike (hw m hm)
    linear_combination h
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_neg_distrib]

/-- On SQUAREFREE wings the correction vanishes: the ladder is exact with no
    remainder — `Σ Ωλ = −Σ Σ_{strikes} λ(n)`. -/
theorem wing_dilation_identity_of_squarefree (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, Squarefree (w m)) :
    ∑ m ∈ I, (cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))
      = -(∑ m ∈ I, ∑ r ∈ strikePairs (w m), ((-1 : ℤ)) ^ (cardFactors r.2)) := by
  have hzero : ∀ m ∈ I, w m ≠ 0 := fun m hm => (hw m hm).ne_zero
  rw [wing_dilation_identity I w hzero]
  have hcorr : ∀ m ∈ I,
      ((cardFactors (w m) : ℤ) - ((w m).primeFactors.card : ℤ))
          * (-1) ^ (cardFactors (w m)) = 0 := by
    intro m hm
    have homega : (w m).primeFactors.card = cardFactors (w m) := by
      have hsq := (cardDistinctFactors_eq_cardFactors_iff_squarefree
        (hw m hm).ne_zero).mpr (hw m hm)
      rw [← hsq, cardDistinctFactors_apply, ← Nat.toFinset_factors]
      exact List.card_toFinset _
    rw [homega]
    ring
  rw [Finset.sum_congr rfl hcorr, Finset.sum_const_zero, add_zero]

/-! ### Layer 3 — mod-6 rigidity of minus-wing strikes and the wing asymmetry -/

/-- **THE WING ASYMMETRY, minus side**: NO square (of anything) is `≡ 5 (mod 6)` —
    the minus wing carries no squares at all.  (Squares mod 6 land in `{0,1,3,4}`.) -/
theorem minus_wing_no_square {x N : ℕ} (hN5 : N % 6 = 5) : x * x ≠ N := by
  intro hEq
  have hmod : (x % 6) * (x % 6) % 6 = 5 := by
    rw [← Nat.mul_mod, hEq]
    exact hN5
  have hx6 : x % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : x % 6 <;> omega

/-- **Mod-6 rigidity of strikes**: a factorization `p·n ≡ 5 (mod 6)` forces the two
    factors into the paired classes `(1,5)` or `(5,1)` mod 6 — no factor is ever
    `≡ 0, 2, 3, 4`; in particular no strike prime is `2` or `3`. -/
theorem strike_congruence {p n N : ℕ} (hN5 : N % 6 = 5) (h : p * n = N) :
    (p % 6 = 1 ∧ n % 6 = 5) ∨ (p % 6 = 5 ∧ n % 6 = 1) := by
  have hmod : (p % 6) * (n % 6) % 6 = 5 := by
    rw [← Nat.mul_mod, h]
    exact hN5
  have hp6 : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hn6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases hp : p % 6 <;> interval_cases hn : n % 6 <;> omega

/-! ### Layer 4 — the rough minus wing is squarefree for free: μ = λ there -/

/-- **Free squarefree-ness of the rough minus wing**: `N ≡ 5 (mod 6)`, `1 < N < y³`,
    all prime factors `> y` ⟹ `N` is squarefree.  Mechanism: `Ω ≤ 2` (house
    `rough_omega_le_two`); `Ω = 1` is a prime; `Ω = 2` cannot be `p²` because the
    minus wing carries no squares (`minus_wing_no_square`). -/
theorem rough_minus_squarefree {y N : ℕ} (hN5 : N % 6 = 5) (hN1 : 1 < N)
    (hN3 : N < y ^ 3) (hrough : ∀ p : ℕ, p.Prime → p ∣ N → y < p) :
    Squarefree N := by
  have hN0 : N ≠ 0 := by omega
  have hle2 := rough_omega_le_two hN1 hN3 hrough
  have hlen : N.primeFactorsList.length ≤ 2 := by
    rw [← cardFactors_apply]
    exact hle2
  have hprod : N.primeFactorsList.prod = N := Nat.prod_primeFactorsList hN0
  rcases hL : N.primeFactorsList with _ | ⟨p, _ | ⟨q, _ | ⟨r, t⟩⟩⟩
  · rw [hL, List.prod_nil] at hprod
    omega
  · have hp : p.Prime := Nat.prime_of_mem_primeFactorsList
      (hL ▸ List.mem_cons_self ..)
    have hNp : N = p := by
      rw [hL, List.prod_cons, List.prod_nil, mul_one] at hprod
      omega
    rw [hNp]
    exact hp.squarefree
  · have hp : p.Prime := Nat.prime_of_mem_primeFactorsList
      (hL ▸ List.mem_cons_self ..)
    have hq : q.Prime := Nat.prime_of_mem_primeFactorsList
      (hL ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hNpq : p * q = N := by
      rw [hL, List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hprod
      exact hprod
    have hne : p ≠ q := by
      intro hpq
      rw [hpq] at hNpq
      exact minus_wing_no_square hN5 hNpq
    rw [← hNpq]
    exact (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)).mpr
      ⟨hp.squarefree, hq.squarefree⟩
  · rw [hL] at hlen
    simp only [List.length_cons] at hlen
    omega

/-- **μ = λ FOR FREE on the rough minus wing**: on `N ≡ 5 (mod 6)`, rough below `y³`,
    the Möbius and Liouville data coincide pointwise — face B's Liouville wing and
    the μ-signed frame of faces C/E are the SAME object there. -/
theorem rough_minus_moebius_eq_liouville {y N : ℕ} (hN5 : N % 6 = 5) (hN1 : 1 < N)
    (hN3 : N < y ^ 3) (hrough : ∀ p : ℕ, p.Prime → p ∣ N → y < p) :
    ArithmeticFunction.moebius N = ((-1 : ℤ)) ^ (cardFactors N) := by
  have hsq := rough_minus_squarefree hN5 hN1 hN3 hrough
  rw [moebius_apply_of_squarefree hsq]

/-- Roughness is LOAD-BEARING for `μ = λ`: the smallest minus-wing witness is
    `125 = 5³ ≡ 5 (mod 6)` with `μ(125) = 0 ≠ −1 = λ(125)` (pre-pass: the failure
    sequence starts `125, 245, 275, …`). -/
theorem moebius_ne_liouville_125 :
    ArithmeticFunction.moebius 125 ≠ ((-1 : ℤ)) ^ (cardFactors 125) := by
  have hsq : ¬Squarefree (125 : ℕ) := fun h =>
    absurd (Nat.isUnit_iff.mp (h 5 ⟨5, by norm_num⟩)) (by norm_num)
  rw [moebius_eq_zero_of_not_squarefree hsq]
  have h125 : (125 : ℕ) = 5 ^ 3 := by norm_num
  rw [h125, cardFactors_apply_prime_pow (by norm_num)]
  norm_num

/-- The `Ω = 2` rough minus-wing element is a genuine TWO-ROUGH-PRIME semiprime:
    `N = p·q`, `p ≠ q`, both factors `> y` — the input of the B ↔ C/E unification
    (each wing semiprime is one unordered pair of large primes, exactly). -/
theorem rough_minus_semiprime_factor {y N : ℕ} (hN5 : N % 6 = 5) (hN0 : N ≠ 0)
    (hOm2 : cardFactors N = 2) (hrough : ∀ p : ℕ, p.Prime → p ∣ N → y < p) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p * q = N ∧ y < p ∧ y < q := by
  have hlen : N.primeFactorsList.length = 2 := by
    rw [← cardFactors_apply]
    exact hOm2
  obtain ⟨p, q, hL⟩ := List.length_eq_two.mp hlen
  have hprod : N.primeFactorsList.prod = N := Nat.prod_primeFactorsList hN0
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList
    (hL ▸ List.mem_cons_self ..)
  have hq : q.Prime := Nat.prime_of_mem_primeFactorsList
    (hL ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hNpq : p * q = N := by
    rw [hL, List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hprod
    exact hprod
  have hne : p ≠ q := by
    intro hpq
    rw [hpq] at hNpq
    exact minus_wing_no_square hN5 hNpq
  exact ⟨p, q, hp, hq, hne, hNpq,
    hrough p hp ⟨q, hNpq.symm⟩,
    hrough q hq ⟨p, by rw [← hNpq]; ring⟩⟩

/-! ### Layer 5 — the rough affine bridge and the cross-check -/

/-- **THE ROUGH AFFINE BRIDGE** (integer-safe doubled form): on a rough window
    (`Ω(w m) ∈ {1,2}` pointwise), `2·Σ Ω(w m)·λ(w m) = |I| + 3·Σ λ(w m)` — the
    `Ω`-weighted ladder input is an AFFINE function of the plain Liouville bias.
    Pointwise: `(Ω, λ) = (1, −1) ↦ −2 = 1 − 3` and `(2, +1) ↦ 4 = 1 + 3`. -/
theorem rough_window_omega_lambda_sum (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, cardFactors (w m) = 1 ∨ cardFactors (w m) = 2) :
    2 * ∑ m ∈ I, (cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))
      = (I.card : ℤ) + 3 * ∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (w m)) := by
  have hpt : ∀ m ∈ I,
      2 * ((cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m)))
        = 1 + 3 * ((-1 : ℤ)) ^ (cardFactors (w m)) := by
    intro m hm
    rcases hw m hm with h | h <;> rw [h] <;> norm_num
  calc 2 * ∑ m ∈ I, (cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))
      = ∑ m ∈ I, 2 * ((cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))) :=
        Finset.mul_sum _ _ _
    _ = ∑ m ∈ I, (1 + 3 * ((-1 : ℤ)) ^ (cardFactors (w m))) :=
        Finset.sum_congr rfl hpt
    _ = (I.card : ℤ) + 3 * ∑ m ∈ I, ((-1 : ℤ)) ^ (cardFactors (w m)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
          nsmul_eq_mul, mul_one]

/-- **The cross-check** (pre-pass: both sides `= 3B₋ − |I|`): the affine bridge and
    the house `rough_window_liouville_sum` agree — `Σ Ωλ = 3·#composite − |I|`. -/
theorem rough_window_ladder_cross_check (I : Finset ℕ) (w : ℕ → ℕ)
    (hw : ∀ m ∈ I, cardFactors (w m) = 1 ∨ cardFactors (w m) = 2) :
    ∑ m ∈ I, (cardFactors (w m) : ℤ) * (-1) ^ (cardFactors (w m))
      = 3 * ((I.filter fun m => ¬ (w m).Prime).card : ℤ) - I.card := by
  have h1 := rough_window_omega_lambda_sum I w hw
  have h2 := rough_window_liouville_sum I w hw
  linarith

/-! ### Layer 6 — the plus side of the asymmetry -/

/-- The plus wing DOES carry prime squares: `25 = 6·4 + 1 = 5²` (kernel witness). -/
theorem plus_wing_square_exists : 6 * 4 + 1 = 5 * 5 := by norm_num

/-- On rough windows the plus-wing prime squares are confined to the THIN range
    `y < p` with `p² < y³` (the integer-safe form of `p < y^{3/2}`) — the exception
    set of the plus wing is machine-characterized, not hidden. -/
theorem rough_plus_square_thin {y N p : ℕ} (hsq : p * p = N) (hp : p.Prime)
    (hN3 : N < y ^ 3) (hrough : ∀ q : ℕ, q.Prime → q ∣ N → y < q) :
    y < p ∧ p * p < y ^ 3 :=
  ⟨hrough p hp ⟨p, hsq.symm⟩, by omega⟩

/-! ### Kernel demo -/

/-- Strike demo at `N = 35 = 5·7`: exactly two strikes, `(5,7)` and `(7,5)` —
    `ω(35) = 2` rungs, each descending to a prime scale. -/
theorem strikePairs_card_35 : (strikePairs 35).card = 2 := by
  rw [strikePairs_card, show (35 : ℕ) = 5 * 7 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-! ### Axiom audit -/

#print axioms mem_strikePairs
#print axioms strikePairs_lambda_sum
#print axioms wing_dilation_identity
#print axioms wing_dilation_identity_of_squarefree
#print axioms strike_congruence
#print axioms minus_wing_no_square
#print axioms rough_minus_squarefree
#print axioms rough_minus_moebius_eq_liouville
#print axioms moebius_ne_liouville_125
#print axioms rough_minus_semiprime_factor
#print axioms rough_window_omega_lambda_sum
#print axioms rough_window_ladder_cross_check
#print axioms rough_plus_square_thin
#print axioms strikePairs_card_35

end TypeII
end Geometric
end EuclidsPath
