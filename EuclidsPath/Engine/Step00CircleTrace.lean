/-
  Step00CircleTrace — the trigonometric face of the imaginary circle: the Dickson
  trace law, the angle-doubling law, and the Lucas–Lehmer subsumption plaque with
  the full-cascade kernel demo at M₇ = 127.

  READING.  A norm-one point of `Quad d n` is a "circle point" `(cos, sin)` of the
  imaginary circle (companion module `Step00ImaginaryCircle`): multiplication is angle
  addition, powers are Dickson/Chebyshev polynomials of the trace ("cos(kθ) = T_k(cos θ)"
  in the division-free Dickson normalization), and the doubling law
  `trace(x^{2k}) = trace(x^k)² − 2` is EXACTLY the Lucas–Lehmer step `s ↦ s² − 2`.
  The LL walk `s_k = trace(ω^{2^k})` DOUBLES the angle at every step; the
  "half → quarter → …" tower is the same dyadic ladder read from the top — at step
  `p−2` the walk stands on the trace-zero QUARTER-turn, at `p−1` on the HALF-turn `−1`,
  at `p` on the full turn `1` (kernel-verified over 127: `ω^32 = (0,114)` trace 0,
  `ω^64 = (126,0) = −1`, `ω^128 = (1,0) = 1`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `trace_algebraMap` — `x + star x = algebraMap (2·x.re)`: the trace lands in the
      base ring (ALL n, ALL d, no hypotheses);
    * `circle_trace_dickson` — the trace law: for `qnorm x = 1`,
      `x^k + star (x^k) = algebraMap ((dickson 1 1 k).eval (2·x.re))` — Dickson of the
      trace, in ANY `Quad d n`;
    * `circle_trace_doubling` — the doubling law `trace(x^{2k}) = trace(x^k)² − 2`,
      the LL step as the circle's angle doubling (ALL n, ALL d);
    * `xEquiv : LucasLehmer.X m ≃+* Quad 3 m` — mathlib's Lucas–Lehmer ring `X`
      IS `Quad 3 m` componentwise (the mul laws coincide literally at `d = 3, b = 0`);
    * `s_cast_eq_zero_iff_half_turn` — over ANY modulus `m`:
      `(s i : X m) = 0 ↔ ω^(2^(i+1)) = −1` (closed form + one unit cancellation);
    * `ll_test_iff_half_turn_mersenne` — `LucasLehmerTest p ↔ ω^(2^(p−1)) = −1` in
      `X (mersenne p)`: the LL test IS the half-turn condition at the full modulus;
    * `ll_test_iff_half_turn` — the same iff at mathlib's working modulus `X (q p)`
      (`q p = minFac (mersenne p)`); the backward direction must first close the
      modulus gap `q p` vs `mersenne p` by re-running the order/cardinality count —
      the design sketch "multiply by ω^(2^(p−2))" alone only reaches `s ≡ 0 mod q p`
      (deviation disclosed in the docstring);
    * `ll_sufficiency_via_circle` — THE SUBSUMPTION PLAQUE: `LucasLehmerTest p →
      (mersenne p).Prime` for odd `p ≥ 3`, proved THROUGH `circle_lucas` ONLY
      (mathlib's `lucas_lehmer_sufficiency` is never invoked): the LL test is
      `circle_lucas` at the pure-dyadic volume `M + 1 = 2^p`;
    * `mersenne_two_prime` — the honest `p = 2` edge: `d = 3` ramifies (`3 ∣ M₂ = 3`),
      so the circle route is closed there; `norm_num` covers it directly;
    * kernel demo at `M₇ = 127`: `cascade_walk_127` (pure ℕ folds, `decide`),
      the lifted walk `cascade_quarter_turn_127` / `cascade_half_turn_127` /
      `cascade_full_turn_127`, the order-128 norm-one point `full_rotation_127`,
      and `prime_127_via_cascade` — `(127).Prime` END-TO-END through `circle_lucas`.

  MANDATORY DISCLOSURES (read before quoting):
    * MATHLIB OWNS BOTH LUCAS–LEHMER DIRECTIONS: `lucas_lehmer_sufficiency`
      (NumberTheory/LucasLehmer.lean:579) and `lucas_lehmer_necessity` (:593) are
      already in the pin, and even the quarter-turn trace-zero lemma is mathlib's
      `ω_pow_trace` (:449).  This module adds the CIRCLE READING and the
      strict-subsumption derivation (`ll_sufficiency_via_circle` through
      `circle_lucas`), NOT a new result about Mersenne primes.
    * PRIME-BLIND FRAME ARITHMETIC.  The trace law and the doubling law hold for ALL
      moduli `n` and ALL parameters `d` — the circle's trigonometry needs no primality;
      primality enters only through `circle_lucas`'s certificate.
    * POINTWISE ONLY.  Every primality statement here is a pointwise certificate for
      an individual number; nothing feeds the serial-twin wall — no density, no
      infinitude, no progress on twin primes (or on Mersenne infinitude) is claimed.
    * `prime_127_via_cascade` re-proves a fact `norm_num` settles instantly; its value
      is the ROUTE (the entire imaginary-circle volume `128 = 2^7` is one pure dyadic
      cascade and the LL walk descends it), not the fact.
    * Cross-reference by name only (no import): the Mersenne cluster of
      `SophieGermainBranch` (`sophieGermain_divides_mersenne`,
      `mersenne_composite_examples`) treats the COMPOSITE side of the same boundary.

  ANTI-VOCABULARY (mandatory): no statement here "advances" the Lucas–Lehmer test,
  "generalizes" Mersenne primality, or "approaches" any open problem.  "Subsumption"
  means precisely: one existing mathlib theorem is re-derived from this repo's
  `circle_lucas` at the dyadic volume — an alternative derivation of known
  mathematics, machine-checked.  No claim above the certified instances.
-/
import Mathlib
import EuclidsPath.Engine.Step00ImaginaryCircle

set_option autoImplicit false

namespace EuclidsPath
namespace CircleTrace

open EuclidsPath.ImaginaryCircle
open QuadraticAlgebra
open LucasLehmer

/-! ### Layer 1 — the trace and the Dickson law

TRIVIALITY LABEL: everything in this layer is prime-blind frame arithmetic, valid for
ALL moduli `n` (including `0` and `1`) and ALL parameters `d`.  It is the circle's
trigonometry — `cos(kθ) = T_k(cos θ)` in Dickson normalization (no division by 2) —
and carries no arithmetic content about any particular `n`. -/

/-- The trace of `x = (a, b)` is `x + star x = (2a, 0)` — an element of the base ring
    embedded along `algebraMap`.  Holds for ALL `n`, `d`, and `x` (the star of
    `Quad d n = QuadraticAlgebra (ZMod n) d 0` has `b`-parameter `0`, so
    `star ⟨a, b⟩ = ⟨a, −b⟩`). -/
theorem trace_algebraMap {d n : ℕ} (x : Quad d n) :
    x + star x = algebraMap (ZMod n) (Quad d n) (2 * x.re) := by
  ext <;> simp [two_mul]

/-- **The Dickson trace law** (`cos(kθ) = T_k(cos θ)`, division-free form).  On the
    norm-one circle of `Quad d n` the trace of `x^k` is the `k`-th Dickson polynomial
    (first kind, parameter 1) of the trace of `x`:

    `x^k + star (x^k) = algebraMap ((dickson 1 1 k).eval (2·x.re))`.

    Route: `qnorm x = 1` gives `x · star x = 1` (`algebraMap_norm_eq_mul_star`), so
    mathlib's `dickson_one_one_eval_add_inv` applies IN the ring `Quad d n` with
    `y := star x`; the polynomial is then pushed down to the base ring along
    `map_dickson` + `eval₂_at_apply`, using `x + star x = algebraMap (2·x.re)`.

    TRIVIALITY LABEL: valid for ALL `n` and ALL `d` — the circle's trigonometry is
    prime-blind frame arithmetic; no primality is used or available here. -/
theorem circle_trace_dickson {d n : ℕ} (k : ℕ) (x : Quad d n) (hx : qnorm x = 1) :
    x ^ k + star (x ^ k) =
      algebraMap (ZMod n) (Quad d n) ((Polynomial.dickson 1 1 k).eval (2 * x.re)) := by
  have hstar : x * star x = 1 := by
    rw [← algebraMap_norm_eq_mul_star, ← qnorm_eq_norm, hx, map_one]
  calc x ^ k + star (x ^ k)
      = x ^ k + star x ^ k := by rw [star_pow]
    _ = (Polynomial.dickson 1 1 k).eval (x + star x) :=
        (Polynomial.dickson_one_one_eval_add_inv x (star x) hstar k).symm
    _ = ((Polynomial.dickson 1 1 k).map (algebraMap (ZMod n) (Quad d n))).eval
          (algebraMap (ZMod n) (Quad d n) (2 * x.re)) := by
        rw [Polynomial.map_dickson, map_one, trace_algebraMap]
    _ = algebraMap (ZMod n) (Quad d n) ((Polynomial.dickson 1 1 k).eval (2 * x.re)) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- **The angle-doubling law = the Lucas–Lehmer step.**  On the norm-one circle,

    `trace(x^{2k}) = trace(x^k)² − 2`.

    This is the LL iteration `s ↦ s² − 2` read on the circle: the LL walk
    `s_j = trace(ω^{2^j})` DOUBLES the angle at each step.  The "half → quarter → …"
    tower of the companion module is the same dyadic ladder read from the top — at
    step `p−2` the walk stands on the trace-zero QUARTER-turn, at `p−1` on the
    HALF-turn `−1`, at `p` on the full turn `1` (kernel demo `cascade_walk_127`).

    TRIVIALITY LABEL: prime-blind frame arithmetic — ALL `n`, ALL `d`; the only input
    is `x^k · star(x^k) = 1` (norm multiplicativity) plus ring identities. -/
theorem circle_trace_doubling {d n : ℕ} (k : ℕ) (x : Quad d n) (hx : qnorm x = 1) :
    x ^ (2 * k) + star (x ^ (2 * k)) = (x ^ k + star (x ^ k)) ^ 2 - 2 := by
  have hstar : x * star x = 1 := by
    rw [← algebraMap_norm_eq_mul_star, ← qnorm_eq_norm, hx, map_one]
  have hk : x ^ k * star (x ^ k) = 1 := by
    rw [star_pow, ← mul_pow, hstar, one_pow]
  have hpow : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hpow, star_pow]
  linear_combination (-2 : Quad d n) * hk

/-! ### Layer 2 — mathlib's Lucas–Lehmer ring `X q` IS `Quad 3 q`

Mathlib's `LucasLehmer.X q` is `ZMod q × ZMod q` with
`(a,b)·(c,d) = (ac + 3bd, ad + bc)` — literally the multiplication of
`Quad 3 q = QuadraticAlgebra (ZMod q) 3 0`.  The identification is the componentwise
identity map, a ring isomorphism by `rfl`-level computation. -/

/-- Mathlib's Lucas–Lehmer ring is the imaginary-circle ring at `d = 3`:
    `X m ≃+* Quad 3 m`, componentwise identity. -/
def xEquiv (m : ℕ) : LucasLehmer.X m ≃+* Quad 3 m where
  toFun x := ⟨x.1, x.2⟩
  invFun z := (z.re, z.im)
  left_inv x := rfl
  right_inv z := rfl
  map_mul' x y := by
    ext
    · simp only [X.mul_fst, re_mul, Nat.cast_ofNat]
    · simp only [X.mul_snd, im_mul, zero_mul, add_zero]
  map_add' x y := by
    ext <;> simp only [X.add_fst, X.add_snd, re_add, im_add]

@[simp] theorem xEquiv_re (m : ℕ) (x : LucasLehmer.X m) : (xEquiv m x).re = x.1 := rfl

@[simp] theorem xEquiv_im (m : ℕ) (x : LucasLehmer.X m) : (xEquiv m x).im = x.2 := rfl

/-- `xEquiv` sends mathlib's `ω = 2 + √3` to the circle point `⟨2, 1⟩`. -/
theorem xEquiv_omega (m : ℕ) : xEquiv m X.ω = (⟨2, 1⟩ : Quad 3 m) := rfl

/-- The LL point `⟨2, 1⟩ = 2 + √3` lies on the norm-one circle of `Quad 3 m` for
    EVERY modulus `m`: `qnorm = 2² − 3·1² = 1` is frame arithmetic. -/
theorem qnorm_omega_point (m : ℕ) : qnorm (⟨2, 1⟩ : Quad 3 m) = 1 := by
  show (2 : ZMod m) ^ 2 - ((3 : ℕ) : ZMod m) * (1 : ZMod m) ^ 2 = 1
  push_cast
  norm_num

/-! ### Layer 3 — the LL test as the half-turn condition -/

/-- **Closed-form pivot** (ALL moduli `m`): the LL residue `s i` vanishes in `X m`
    iff `ω^(2^(i+1)) = −1`.  Forward: multiply
    `ω^(2^i) + ωb^(2^i) = 0` (mathlib's `closed_form`) by `ω^(2^i)` and use
    `ω·ωb = 1`.  Backward: the same multiplication read the other way plus one
    cancellation of the unit `ω^(2^i)`. -/
theorem s_cast_eq_zero_iff_half_turn (m : ℕ) (i : ℕ) :
    ((s i : ℤ) : LucasLehmer.X m) = 0 ↔ (X.ω : LucasLehmer.X m) ^ 2 ^ (i + 1) = -1 := by
  have ht : (2 : ℕ) ^ i + 2 ^ i = 2 ^ (i + 1) := by ring
  constructor
  · intro h
    have h0 : (X.ω : LucasLehmer.X m) ^ 2 ^ i + X.ωb ^ 2 ^ i = 0 := by
      rw [← X.closed_form]
      exact h
    have key : (X.ω : LucasLehmer.X m) ^ 2 ^ (i + 1) + 1 = 0 := by
      calc (X.ω : LucasLehmer.X m) ^ 2 ^ (i + 1) + 1
          = X.ω ^ (2 ^ i + 2 ^ i) + (X.ω * X.ωb) ^ 2 ^ i := by
            rw [ht, X.ω_mul_ωb, one_pow]
        _ = X.ω ^ 2 ^ i * (X.ω ^ 2 ^ i + X.ωb ^ 2 ^ i) := by
            rw [pow_add, mul_pow, mul_add]
        _ = 0 := by rw [h0, mul_zero]
    exact eq_neg_of_add_eq_zero_left key
  · intro hω
    have key : ((s i : ℤ) : LucasLehmer.X m) * X.ω ^ 2 ^ i = 0 := by
      calc ((s i : ℤ) : LucasLehmer.X m) * X.ω ^ 2 ^ i
          = (X.ω ^ 2 ^ i + X.ωb ^ 2 ^ i) * X.ω ^ 2 ^ i := by rw [X.closed_form]
        _ = X.ω ^ (2 ^ i + 2 ^ i) + (X.ωb * X.ω) ^ 2 ^ i := by
            rw [add_mul, ← pow_add, mul_pow]
        _ = -1 + 1 := by rw [ht, hω, X.ωb_mul_ω, one_pow]
        _ = 0 := by ring
    have hu : IsUnit ((X.ω : LucasLehmer.X m) ^ 2 ^ i) :=
      (IsUnit.of_mul_eq_one X.ωb X.ω_mul_ωb).pow (2 ^ i)
    exact hu.mul_right_cancel (key.trans (zero_mul _).symm)

/-- **The LL test IS the half-turn at the full modulus**: for `p > 1`,
    `LucasLehmerTest p ↔ ω^(2^(p−1)) = −1` in `X (mersenne p)`.

    Both directions are the closed-form pivot: the test says exactly
    `mersenne p ∣ s (p−2)`, i.e. `(s (p−2) : X (mersenne p)) = 0`.  No order or
    cardinality argument is needed at this modulus — contrast `ll_test_iff_half_turn`
    below.  This is the form the subsumption plaque consumes. -/
theorem ll_test_iff_half_turn_mersenne {p : ℕ} (hp : 1 < p) :
    LucasLehmerTest p ↔ (X.ω : LucasLehmer.X (mersenne p)) ^ 2 ^ (p - 1) = -1 := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  rw [show p' + 2 - 1 = p' + 1 from rfl]
  have hres : LucasLehmerTest (p' + 2) ↔
      ((s p' : ℤ) : LucasLehmer.X (mersenne (p' + 2))) = 0 := by
    constructor
    · intro h
      have h0 : ((s p' : ℤ) : ZMod (2 ^ (p' + 2) - 1)) = 0 := by
        rw [← sZMod_eq_s p' p']
        exact h
      apply X.ext
      · rw [X.fst_intCast, X.zero_fst]; exact h0
      · rw [X.snd_intCast, X.zero_snd]
    · intro h
      have h0 := congrArg Prod.fst h
      rw [X.fst_intCast, X.zero_fst] at h0
      show lucasLehmerResidue (p' + 2) = 0
      exact (sZMod_eq_s p' p').trans h0
  exact hres.trans (s_cast_eq_zero_iff_half_turn (mersenne (p' + 2)) p')

/-- **The LL test as the half-turn at mathlib's working modulus** `q p =
    minFac (mersenne p)`: for `p > 1`,
    `LucasLehmerTest p ↔ ω^(2^(p−1)) = −1` in `X (q p)`.

    Forward: mathlib's `ω_pow_eq_neg_one`.  Backward — DEVIATION FROM THE DESIGN
    SKETCH, disclosed: multiplying the closed form by `ω^(2^(p−2))` only yields
    `s (p−2) ≡ 0 (mod q p)`, which is weaker than the test (`mod mersenne p`).  The
    modulus gap is closed the way mathlib's own sufficiency argument runs: the
    half-turn forces `orderOf ω = 2^p` in `X (q p)ˣ`, the cardinality bound
    `2^p < (q p)²` then forces `mersenne p` prime, hence `q p = mersenne p` and the
    mersenne-modulus iff applies.  (The two sides are equivalent even at `p = 2`,
    where both are false.) -/
theorem ll_test_iff_half_turn {p : ℕ} (hp : 1 < p) :
    LucasLehmerTest p ↔ (X.ω : LucasLehmer.X (q p)) ^ 2 ^ (p - 1) = -1 := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  rw [show p' + 2 - 1 = p' + 1 from rfl]
  constructor
  · intro h
    exact ω_pow_eq_neg_one p' h
  · intro hω
    have hω1 : (X.ω : LucasLehmer.X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
      calc (X.ω : LucasLehmer.X (q (p' + 2))) ^ 2 ^ (p' + 2)
          = (X.ω ^ 2 ^ (p' + 1)) ^ 2 := by rw [← pow_mul, ← Nat.pow_succ]
        _ = 1 := by rw [hω]; norm_num
    haveI : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q p'⟩
    have horder : orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
      apply Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two
      · intro o
        have hcoe := congrArg (Units.coeHom (LucasLehmer.X (q (p' + 2))) :
            Units (LucasLehmer.X (q (p' + 2))) → LucasLehmer.X (q (p' + 2)))
          (orderOf_dvd_iff_pow_eq_one.1 o)
        have h1 : (1 : ZMod (q (p' + 2))) = -1 := congrArg Prod.fst (hcoe.symm.trans hω)
        exact ZMod.neg_one_ne_one h1.symm
      · apply orderOf_dvd_iff_pow_eq_one.2
        apply Units.ext
        push_cast
        exact hω1
    have hprime : (mersenne (p' + 2)).Prime := by
      by_contra hM
      have hineq : 2 ^ (p' + 2) < (q (p' + 2) : ℕ) ^ 2 :=
        calc 2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := horder.symm
          _ ≤ Fintype.card (LucasLehmer.X (q (p' + 2)))ˣ := orderOf_le_card_univ
          _ < (q (p' + 2) : ℕ) ^ 2 := X.card_units_lt (Nat.lt_of_succ_lt (two_lt_q p'))
      have hsq := Nat.minFac_sq_le_self (mersenne_pos.2 (by omega)) hM
      have hlt := lt_of_lt_of_le hineq hsq
      exact not_lt_of_ge (Nat.sub_le _ _) hlt
    have hqM : ((q (p' + 2) : ℕ)) = mersenne (p' + 2) := (Nat.prime_def_minFac.mp hprime).2
    rw [hqM] at hω
    exact (ll_test_iff_half_turn_mersenne (by omega)).mpr hω

/-! ### Layer 4 — the subsumption plaque -/

/-- The honest `p = 2` edge of the circle route: `mersenne 2 = 3` and the parameter
    `d = 3` RAMIFIES (`3 ∣ 3`), so `circle_lucas` (which needs `gcd(3, n) = 1`) cannot
    run there.  The fact itself is a `norm_num` one-liner and carries no circle
    content.  For every odd `p` the route is open: `2^p ≡ −1 (mod 3)`, so
    `mersenne p ≡ 1 (mod 3)`. -/
theorem mersenne_two_prime : (mersenne 2).Prime := by norm_num [mersenne]

/-- **THE SUBSUMPTION PLAQUE.**  For odd `p ≥ 3` the Lucas–Lehmer sufficiency
    direction is derived THROUGH this repo's `circle_lucas` ONLY — mathlib's
    `lucas_lehmer_sufficiency` is never invoked:

    the test gives the half-turn `α^(2^(p−1)) = −1` for `α = xEquiv ω = ⟨2,1⟩` on the
    norm-one circle of `Quad 3 M`, `M = mersenne p`; squaring gives the full turn
    `α^(M+1) = 1` at the PURE-DYADIC volume `M + 1 = 2^p`; the only prime divisor of
    `M + 1` is `2`, and `α^((M+1)/2) − 1 = −2` is a unit (its `qnorm` is `4`, a unit
    mod the odd `M`).  `circle_lucas` then certifies `M` prime.

    MANDATORY LABEL: this is an ALTERNATIVE DERIVATION of an existing mathlib theorem
    (`lucas_lehmer_sufficiency`, NumberTheory/LucasLehmer.lean:579).  Its value is the
    demonstrated STRICT SUBSUMPTION: the Lucas–Lehmer test IS `circle_lucas` at the
    pure-dyadic volume `M + 1 = 2^p`, where the entire imaginary circle is the dyadic
    cascade and the LL walk descends it.  No new Mersenne mathematics is claimed.

    HYPOTHESIS DISCLOSURE: `p` odd is required because `d = 3` must not ramify:
    `3 ∤ mersenne p ⟺ p` odd (`2^p ≡ (−1)^p (mod 3)`).  The `p = 2` edge is
    `mersenne_two_prime`; even `p ≥ 4` never passes the test, but that fact is
    mathlib's necessity direction and is not re-derived here. -/
theorem ll_sufficiency_via_circle {p : ℕ} (hp : 2 ≤ p) (hodd : p % 2 = 1) :
    LucasLehmerTest p → (mersenne p).Prime := by
  intro h
  have hp3 : 3 ≤ p := by omega
  -- arithmetic of the modulus: M ≥ 7, M odd, 3 ∤ M
  have hM7 : 7 ≤ mersenne p := by
    have hmono := mersenne_le_mersenne.mpr hp3
    have h7 : mersenne 3 = 7 := rfl
    omega
  have hM2 : 2 ≤ mersenne p := by omega
  have hModd : mersenne p % 2 = 1 := by
    have hdvd : 2 ∣ 2 ^ p := dvd_pow_self 2 (by omega)
    have hM : mersenne p = 2 ^ p - 1 := rfl
    omega
  have h3 : mersenne p % 3 = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
    have h4 : ∀ j : ℕ, 4 ^ j % 3 = 1 := by
      intro j
      induction j with
      | zero => rfl
      | succ i ih => rw [pow_succ]; omega
    have hpow : 2 ^ (2 * m + 1) = 4 ^ m * 2 := by
      rw [pow_succ, pow_mul]
      norm_num
    have h1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hM : mersenne (2 * m + 1) = 2 ^ (2 * m + 1) - 1 := rfl
    have h4m := h4 m
    rw [hM, hpow]
    omega
  have hcop3 : Nat.Coprime 3 (mersenne p) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  -- the half-turn at the full modulus, transported along xEquiv
  have hhalf : (X.ω : LucasLehmer.X (mersenne p)) ^ 2 ^ (p - 1) = -1 :=
    (ll_test_iff_half_turn_mersenne (by omega)).mp h
  have hαhalf : xEquiv (mersenne p) X.ω ^ 2 ^ (p - 1) = -1 := by
    rw [← map_pow, hhalf, map_neg, map_one]
  -- the full turn at the pure-dyadic volume M + 1 = 2^p
  have hexp : (2 : ℕ) ^ p = 2 ^ (p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hα1 : xEquiv (mersenne p) X.ω ^ (mersenne p + 1) = 1 := by
    rw [succ_mersenne, hexp, pow_mul, hαhalf]
    norm_num
  -- −2 is a unit on the circle: qnorm(−2) = 4, a unit mod the odd M
  have hunit2 : IsUnit (-2 : Quad 3 (mersenne p)) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    have hn4 : QuadraticAlgebra.norm (-2 : Quad 3 (mersenne p)) =
        ((4 : ℕ) : ZMod (mersenne p)) := by
      rw [QuadraticAlgebra.norm_neg,
        show (2 : Quad 3 (mersenne p)) = ((2 : ℕ) : Quad 3 (mersenne p)) by norm_cast,
        QuadraticAlgebra.norm_natCast]
      push_cast
      norm_num
    rw [hn4, ZMod.isUnit_iff_coprime,
      show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).pow_left 2
  -- the divisor condition: the ONLY prime dividing M + 1 = 2^p is 2
  have hαdiv : ∀ r : ℕ, r.Prime → r ∣ mersenne p + 1 →
      IsUnit (xEquiv (mersenne p) X.ω ^ ((mersenne p + 1) / r) - 1) := by
    intro r hr hrd
    have hr2 : r = 2 := by
      rw [succ_mersenne] at hrd
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrd)
    subst hr2
    have hhalfdiv : (mersenne p + 1) / 2 = 2 ^ (p - 1) := by
      rw [succ_mersenne, hexp]
      omega
    rw [hhalfdiv, hαhalf, show (-1 - 1 : Quad 3 (mersenne p)) = -2 by ring]
    exact hunit2
  -- Morrison's converse on the imaginary circle certifies M prime
  have hαnorm : qnorm (xEquiv (mersenne p) X.ω) = 1 := by
    rw [xEquiv_omega]
    exact qnorm_omega_point (mersenne p)
  exact circle_lucas hM2 hModd hcop3 hαnorm hα1 hαdiv

/-! ### Layer 5 — the kernel demo at M₇ = 127: the circle IS the dyadic cascade

House kernel discipline: the walk is computed as pure `ℕ` folds (`qpowN`, `sModNat`)
that the kernel unfolds literally; `Quad` enters only through the one-directional spec
lemmas `toQuad_qpowN` / `circleCountN_point_sound` of the companion module — `Quad`
instances stay OUT of every `decide` path (the only `ZMod` decides are single-element
comparisons over `ZMod 127`, the house precedent being `real_rotation_13`). -/

set_option maxRecDepth 8000 in
/-- **The kernel walk at `M₇ = 127`** (pure ℕ, `decide`):
    * `sModNat 127 5 = 0` — the LL residue `s (p−2) = s 5` vanishes mod `127`
      (this IS `LucasLehmerTest 7` in kernel clothing);
    * the cascade of `ω = (2,1)`: `ω^32 = (0, 114)` — the trace-zero QUARTER-turn;
      `ω^64 = (126, 0) = −1` — the HALF-turn; `ω^128 = (1, 0) = 1` — the full turn.
    M₇'s circle volume is `128 = 2^7`: the imaginary circle IS the pure dyadic
    cascade, and the walk visits trace 0 → −1 → 1.
    (`maxRecDepth` is raised for the elaborator's 128-step unfolding of the fold;
    the kernel check itself is cheap.) -/
theorem cascade_walk_127 :
    LucasLehmer.norm_num_ext.sModNat 127 5 = 0 ∧
    qpowN 3 127 (2, 1) 32 = (0, 114) ∧
    qpowN 3 127 (2, 1) 64 = (126, 0) ∧
    qpowN 3 127 (2, 1) 128 = (1, 0) := by decide

/-- The walk's base point lies on the circle: `qnorm (2 + √3) = 1` over `127`
    (kernel congruence + the one-directional spec `circleCountN_point_sound`). -/
theorem cascade_norm_127 : qnorm (toQuad 3 127 (2, 1)) = 1 :=
  circleCountN_point_sound (by decide)

/-- The QUARTER-turn, lifted: `ω^32` has trace zero over `127`.  This is the concrete
    instance of the trace-zero step mathlib proves abstractly as `ω_pow_trace`
    (NumberTheory/LucasLehmer.lean:449) — disclosed, not competed with. -/
theorem cascade_quarter_turn_127 :
    toQuad 3 127 (2, 1) ^ 32 + star (toQuad 3 127 (2, 1) ^ 32) = 0 := by
  rw [← toQuad_qpowN, cascade_walk_127.2.1]
  ext <;> simp [toQuad]

/-- The HALF-turn, lifted: `ω^64 = −1` over `127`. -/
theorem cascade_half_turn_127 : toQuad 3 127 (2, 1) ^ 64 = -1 := by
  rw [← toQuad_qpowN, cascade_walk_127.2.2.1]
  ext
  · simp only [toQuad, re_neg, re_one]
    decide
  · simp only [toQuad, im_neg, im_one, neg_zero, Nat.cast_zero]

/-- The FULL turn, lifted: `ω^128 = 1` over `127`. -/
theorem cascade_full_turn_127 : toQuad 3 127 (2, 1) ^ 128 = 1 := by
  rw [← toQuad_qpowN, cascade_walk_127.2.2.2]
  ext <;> simp [toQuad]

/-- An order-128 norm-one point over `127` exists: the full rotation of the whole
    circle volume `128 = 2^7` is realized by `2 + √3`.  Order dress: order divides
    `128 = 2^7`, the single prime is `2`, and the half-turn `ω^64 = −1 ≠ 1` forbids
    collapse. -/
theorem full_rotation_127 : ∃ α : Quad 3 127, qnorm α = 1 ∧ orderOf α = 128 := by
  refine ⟨toQuad 3 127 (2, 1), cascade_norm_127, ?_⟩
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) cascade_full_turn_127
  intro r hr hrd
  have hr2 : r = 2 := by
    rw [show (128 : ℕ) = 2 ^ 7 by norm_num] at hrd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrd)
  subst hr2
  rw [show (128 : ℕ) / 2 = 64 by norm_num, cascade_half_turn_127]
  intro hcontra
  have hre := congrArg QuadraticAlgebra.re hcontra
  simp only [re_neg, re_one] at hre
  exact absurd hre (by decide)

/-- **`127` is prime, END-TO-END through `circle_lucas`.**  The certificate is the
    cascade walk itself: `α = 2 + √3` with `qnorm α = 1`, the full turn `α^128 = 1`
    at the pure-dyadic volume `127 + 1 = 2^7`, the single prime divisor `2`, and the
    half-turn `α^64 − 1 = −2` a unit (`qnorm(−2) = 4`, with explicit inverse
    `4 · 32 = 128 ≡ 1 (mod 127)` — no primality of `127` consumed anywhere).

    DISCLOSURE: `norm_num` proves `(127).Prime` instantly; the content is the ROUTE —
    M₇'s imaginary circle is one pure dyadic cascade and the LL walk descends it:
    trace 0 (quarter-turn) → `−1` (half-turn) → `1` (full turn). -/
theorem prime_127_via_cascade : Nat.Prime 127 := by
  have hcop : Nat.Coprime 3 127 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by norm_num)
  refine circle_lucas (by norm_num) (by norm_num) hcop cascade_norm_127
    cascade_full_turn_127 ?_
  intro r hr hrd
  have hr2 : r = 2 := by
    rw [show (127 + 1 : ℕ) = 2 ^ 7 by norm_num] at hrd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrd)
  subst hr2
  rw [show (127 + 1) / 2 = 64 by norm_num, cascade_half_turn_127,
    show (-1 - 1 : Quad 3 127) = -2 by ring, QuadraticAlgebra.isUnit_iff_norm_isUnit]
  have hn4 : QuadraticAlgebra.norm (-2 : Quad 3 127) = 4 := by
    rw [QuadraticAlgebra.norm_neg,
      show (2 : Quad 3 127) = ((2 : ℕ) : Quad 3 127) by norm_cast,
      QuadraticAlgebra.norm_natCast]
    push_cast
    norm_num
  rw [hn4]
  exact IsUnit.of_mul_eq_one (32 : ZMod 127) (by decide)

/-! ### Axiom audit -/

#print axioms trace_algebraMap
#print axioms circle_trace_dickson
#print axioms circle_trace_doubling
#print axioms xEquiv
#print axioms xEquiv_omega
#print axioms qnorm_omega_point
#print axioms s_cast_eq_zero_iff_half_turn
#print axioms ll_test_iff_half_turn_mersenne
#print axioms ll_test_iff_half_turn
#print axioms mersenne_two_prime
#print axioms ll_sufficiency_via_circle
#print axioms cascade_walk_127
#print axioms cascade_norm_127
#print axioms cascade_quarter_turn_127
#print axioms cascade_half_turn_127
#print axioms cascade_full_turn_127
#print axioms full_rotation_127
#print axioms prime_127_via_cascade

end CircleTrace
end EuclidsPath
