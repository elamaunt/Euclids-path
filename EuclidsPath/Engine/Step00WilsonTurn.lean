import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The Wilson turn — the number before the prime, the forced 0 → −1 jump, and Clement's congruence

Origin: the author's directive "analyze the number that comes BEFORE the primes; the geometry
of imaginarity forces an orthogonal turn at the transition from the last composite to the
prime".  The honest machine form of that directive: the number before the prime is `(n − 1)!` —
the compressed product of the ENTIRE past of `n` — and the Wilson dichotomy is the forced jump
of its residue at the composite → prime transition: `0 → −1`, annihilator → half-turn.  This is
the repository's first factorial infrastructure.

## The laws (all green, standard axioms only)

* `composite_dvd_pred_factorial` — the composite side, absent from mathlib: for composite
  `n > 4`, `n ∣ (n − 1)!`.  The past of a composite number annihilates it: both factors of
  `n = a·b` already happened below `n`.
* `pred_factorial_zmod_zero` — the same in residue form: `(n−1)! ≡ 0 (mod n)` for composite
  `n > 4`.
* `wilson_dichotomy` — the transition dichotomy: for every `n > 4` the factorial signature
  `((n−1)! : ZMod n)` takes EXACTLY two values, `0` on composites and `−1` on primes.  The
  signature of the entire past is a two-valued observable, and the composite → prime transition
  is the jump `0 → −1`.
* `clement_iff` — **Clement's criterion** (P. A. Clement, *Congruences for sets of primes*,
  Amer. Math. Monthly 56 (1949), 23–25; absent from mathlib): for odd `n ≥ 3`,
  `n` and `n + 2` are BOTH prime iff `n(n+2) ∣ 4((n−1)! + 1) + n` — one congruence, two
  primalities.
* `clement_center` — the center form on the twin panel: for `m ≥ 1`, `TwinCenterZ m` iff
  `36m² − 1 ∣ 4((6m−2)! + 1) + (6m−1)`.  The modulus is `c² − 1` for the center `c = 6m` —
  the product of the two wings.
* `clemFoldB` + `clemFoldB_dvd` + `clemFoldB_twin_center` — a kernel checker in the house
  Bool/Nat-fold discipline: a fused mulmod fold computes `(n−1)! mod n(n+2)` WITHOUT ever
  materialising the factorial, and a passing check IS a twin certificate.  Kernel demos:
  the twin pair `(101, 103)` (center `m = 17`), the stretch pair `(59669, 59671)` (center
  `m = 9945`, 59668 mulmods on ten-digit numbers), and negative controls `n = 7, 9`.

## MANDATORY DISCLOSURES

* **(i) Clement is a costume — it can NEVER feed the wall.**  The criterion is pointwise
  Wilson × 2 + coprimality: one congruence per single candidate `n`.  `TwinJacobsthalBound`
  (the wall) is a window/ensemble statement; NOTHING in this file is summable over windows.
  The one congruence hides exactly the sieve work it replaces — `(n − 1)!` is the whole past
  of `n` in compressed form, and reducing it mod `n(n+2)` costs the same `n − 2` multiplications
  the sieve would have spent.  No window content, no density, no infinitude follows or is
  implied anywhere in this module.
* **(ii) The named value.**  The modulus `c² − 1 = 36m² − 1` is the product of the wings — the
  same panel object that carries the L53 wing–Jacobi collapse (`Step00WingJacobiCollapse`) and
  the circle orders.  The single integer `C(m) = 4((c−2)! + 1) + (c−1)` has the property that
  its vanishing mod `c² − 1` IS twinness of the panel: a one-congruence twin certificate whose
  kernel checker (`clemFoldB`) contains NO primality test anywhere — a new kernel artifact
  type for this repository (`Step00WitnessChainKernel` and `Step00GraveDepthKernel` both
  certify twins through explicit trial-division primality ladders; here primality is never
  tested, only one modular residue is computed).
* **(iii) `−1` is the HALF-turn, not the quarter-turn.**  In `(ZMod p)ˣ` the value `−1` is the
  unique rotation of order 2 — the product of the full rotation group after everything pairs
  off into inverses except `±1`.  The quarter-turn `i` (the order-4 rotation, whose existence
  is governed by `p mod 4`) lives in the circle module `Step00ImaginaryCircle`, built in
  parallel; it is cited here by name only.  The "orthogonal turn" of the directive lands, in
  machine form, on the half-turn: the past of a prime compresses to the half-turn, the past of
  a composite compresses to the annihilator.

## Anti-vocabulary

No claim in this file concerns windows, densities, counts, or the infinitude of anything.
Every theorem is pointwise in `n` (or `m`); every kernel demo is a single verified instance.
-/

open scoped Nat

namespace EuclidsPath
namespace WilsonTurn

open EuclidsPath.Residuals

/-! ### §1 The composite side — the past annihilates a composite

Mathlib has Wilson's lemma (`ZMod.wilsons_lemma`) and its converse
(`Nat.prime_of_fac_equiv_neg_one`) but NOT the composite value of the signature.  We build it:
for composite `n > 4` the two proper factors of `n` both occur below `n`, so the product of
the entire past is divisible by `n` itself.  The bound `4 < n` is sharp — `n = 4` is the
unique composite exception (`3! = 6 ≡ 2 (mod 4)`). -/

/-- **The composite side of the Wilson dichotomy.**  A composite `n > 4` divides `(n − 1)!`.
    Route: `n = a·b` with `2 ≤ a, b < n`.  If `a ≠ b`, the pair `{a, b}` sits inside
    `Ico 1 n` and its product `n` divides `∏ Ico 1 n = (n−1)!`.  If `n = a²` (then `a ≥ 3`
    since `n > 4`), the pair `{a, 2a}` sits inside `Ico 1 n` (as `2a < a²` for `a ≥ 3`) with
    product `2n`, and `n ∣ 2n ∣ (n−1)!`. -/
theorem composite_dvd_pred_factorial {n : ℕ} (h4 : 4 < n) (hn : ¬ n.Prime) :
    n ∣ (n - 1)! := by
  obtain ⟨a, ha_dvd, ha2, ha_lt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hn
  obtain ⟨b, hab⟩ := ha_dvd
  have hprod : (∏ x ∈ Finset.Ico 1 n, x) = (n - 1)! := by
    have h := Finset.prod_Ico_id_eq_factorial (n - 1)
    rwa [show n - 1 + 1 = n from by omega] at h
  have hb2 : 2 ≤ b := by
    rcases b with _ | _ | b
    · rw [Nat.mul_zero] at hab; omega
    · rw [Nat.mul_one] at hab; omega
    · omega
  by_cases hne : a = b
  · -- the square case `n = a²`, `a ≥ 3`: use the pair `{a, 2a}`, whose product is `2n`
    subst hne
    have ha3 : 3 ≤ a := by
      rcases Nat.lt_or_ge a 3 with h | h
      · exfalso
        have ha2' : a = 2 := by omega
        rw [ha2'] at hab
        omega
      · exact h
    have h2a : 2 * a < n :=
      calc 2 * a < 3 * a := by omega
        _ ≤ a * a := Nat.mul_le_mul ha3 (le_refl a)
        _ = n := hab.symm
    have hsub : ({a, 2 * a} : Finset ℕ) ⊆ Finset.Ico 1 n := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_Ico.mpr ⟨by omega, ha_lt⟩
      · rcases Finset.mem_singleton.mp hx with rfl
        exact Finset.mem_Ico.mpr ⟨by omega, h2a⟩
    have hpair : (∏ x ∈ ({a, 2 * a} : Finset ℕ), x) = a * (2 * a) :=
      Finset.prod_pair (by omega)
    have hdvd : a * (2 * a) ∣ (n - 1)! := by
      rw [← hprod, ← hpair]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    exact dvd_trans ⟨2, by rw [hab]; ring⟩ hdvd
  · -- the generic case: two distinct proper factors, the pair `{a, b}` inside `Ico 1 n`
    have hb_lt : b < n :=
      calc b < 2 * b := by omega
        _ ≤ a * b := Nat.mul_le_mul ha2 (le_refl b)
        _ = n := hab.symm
    have hsub : ({a, b} : Finset ℕ) ⊆ Finset.Ico 1 n := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_Ico.mpr ⟨by omega, ha_lt⟩
      · rcases Finset.mem_singleton.mp hx with rfl
        exact Finset.mem_Ico.mpr ⟨by omega, hb_lt⟩
    have hpair : (∏ x ∈ ({a, b} : Finset ℕ), x) = a * b := Finset.prod_pair hne
    have hdvd : a * b ∣ (n - 1)! := by
      rw [← hprod, ← hpair]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    exact dvd_trans (dvd_of_eq hab) hdvd

/-- **The composite signature is the annihilator.**  In residue form: for composite `n > 4`
    the factorial signature of the past vanishes, `((n−1)! : ZMod n) = 0`. -/
theorem pred_factorial_zmod_zero {n : ℕ} (h4 : 4 < n) (hn : ¬ n.Prime) :
    ((n - 1)! : ZMod n) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (composite_dvd_pred_factorial h4 hn)

/-! ### §2 The transition dichotomy — the forced jump 0 → −1 -/

/-- **The Wilson dichotomy** — the machine form of the "orthogonal turn at the transition
    from the last composite to the prime".  For every `n > 4` the factorial signature of the
    ENTIRE past of `n` takes exactly two values: `−1` exactly on primes (Wilson) and `0`
    exactly on composites (§1).  The composite → prime transition is the forced jump
    `0 → −1`: annihilator → half-turn.

    HONESTY (mandatory): `−1` is the HALF-turn — the unique order-2 rotation of `(ZMod p)ˣ`,
    the survivor of the full rotation group after everything pairs off into inverses except
    `±1`.  It is NOT the quarter-turn: the quarter-turn `i` (order 4) lives in the circle
    module `Step00ImaginaryCircle`, built in parallel and cited here by name only. -/
theorem wilson_dichotomy {n : ℕ} (h4 : 4 < n) :
    (((n - 1)! : ZMod n) = -1 ∧ n.Prime) ∨ (((n - 1)! : ZMod n) = 0 ∧ ¬ n.Prime) := by
  by_cases hp : n.Prime
  · haveI := Fact.mk hp
    exact Or.inl ⟨ZMod.wilsons_lemma n, hp⟩
  · exact Or.inr ⟨pred_factorial_zmod_zero h4 hp, hp⟩

/-! ### §3 Clement's criterion — two Wilsons welded by coprimality

The 1949 criterion.  Forward: Wilson at `n` gives `n ∣ 4((n−1)! + 1)`; Wilson at `n + 2`
gives, after writing `(n+1)! = (n+1)·n·(n−1)!` and using `n+1 ≡ −1`, `n ≡ −2 (mod n+2)`,
the congruence `2(n−1)! ≡ −1 (mod n+2)`; the two divisibilities weld along
`gcd(n, n+2) = gcd(n, 2) = 1`.  Backward: each factor of the modulus recovers its own Wilson
residue (the factors `4` and `2` are units mod the odd numbers `n`, `n+2`), and
`Nat.prime_of_fac_equiv_neg_one` converts each residue back into a primality.  The
ℕ-subtraction and cast bookkeeping is the real cost of the proof. -/

/-- **Clement's criterion (1949).**  For odd `n ≥ 3`: `n` and `n + 2` are both prime iff
    `n(n+2) ∣ 4((n−1)! + 1) + n`.  One congruence carries both primalities.  Sanity anchors
    (kernel-checked below): `n = 3`: `15 ∣ 15`; `n = 5`: `35 ∣ 105`; `n = 7`: `63 ∤ 2891`
    (the wing `9 = 3²` is composite). -/
theorem clement_iff {n : ℕ} (h3 : 3 ≤ n) (hodd : n % 2 = 1) :
    (n.Prime ∧ (n + 2).Prime) ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  -- shared bookkeeping: `n ≡ −2 (mod n+2)` and the factorial ladder `(n+1)! = (n+1)·n·(n−1)!`
  have hn2 : (n : ZMod (n + 2)) = -2 := by
    have h0 := ZMod.natCast_self (n + 2)
    push_cast at h0
    linear_combination h0
  have hfac_succ : (n + 1)! = (n + 1) * (n * (n - 1)!) := by
    rw [Nat.factorial_succ, Nat.mul_factorial_pred (show n ≠ 0 by omega)]
  have hcop2n : Nat.Coprime n 2 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega) |>.symm
  have hcop2q : Nat.Coprime (n + 2) 2 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega) |>.symm
  constructor
  · rintro ⟨hp, hq⟩
    -- Wilson at `n`: `n ∣ (n−1)! + 1`, hence `n` divides the object
    have hdvd_n : n ∣ 4 * ((n - 1)! + 1) + n := by
      haveI := Fact.mk hp
      have hW : ((n - 1)! : ZMod n) = -1 := ZMod.wilsons_lemma n
      have h1 : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := by
        push_cast
        linear_combination hW
      exact dvd_add (Dvd.dvd.mul_left ((ZMod.natCast_eq_zero_iff _ _).mp h1) 4) dvd_rfl
    -- Wilson at `n + 2`: `2(n−1)! ≡ −1 (mod n+2)`, hence `n + 2` divides the object
    have hdvd_q : (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
      haveI := Fact.mk hq
      have hW2 : (((n + 2) - 1)! : ZMod (n + 2)) = -1 := ZMod.wilsons_lemma (n + 2)
      rw [show n + 2 - 1 = n + 1 from by omega, hfac_succ] at hW2
      push_cast at hW2
      rw [hn2] at hW2
      have h2 : ((4 * ((n - 1)! + 1) + n : ℕ) : ZMod (n + 2)) = 0 := by
        push_cast
        rw [hn2]
        linear_combination 2 * hW2
      exact (ZMod.natCast_eq_zero_iff _ _).mp h2
    -- weld: `gcd(n, n+2) = gcd(n, 2) = 1` for odd `n`
    have hcop : Nat.Coprime n (n + 2) := by
      have hg2 : Nat.gcd n (n + 2) ∣ 2 := by
        have h := Nat.dvd_sub (Nat.gcd_dvd_right n (n + 2)) (Nat.gcd_dvd_left n (n + 2))
        rwa [show n + 2 - n = 2 from by omega] at h
      rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk⟩ := h ▸ Nat.gcd_dvd_left n (n + 2)
        omega
    exact hcop.mul_dvd_of_dvd_of_dvd hdvd_n hdvd_q
  · intro hd
    -- the `n` factor: strip the unit `4 = 2·2`, recover the Wilson residue at `n`
    have hdn : n ∣ 4 * ((n - 1)! + 1) := by
      have h1 : n ∣ 4 * ((n - 1)! + 1) + n := (dvd_mul_right n (n + 2)).trans hd
      have h2 := Nat.dvd_sub h1 (dvd_refl n)
      rwa [Nat.add_sub_cancel] at h2
    have hdn' : n ∣ (n - 1)! + 1 := by
      rw [show (4 : ℕ) * ((n - 1)! + 1) = 2 * (2 * ((n - 1)! + 1)) from by ring] at hdn
      exact hcop2n.dvd_of_dvd_mul_left (hcop2n.dvd_of_dvd_mul_left hdn)
    have hWn : ((n - 1)! : ZMod n) = -1 := by
      have h0 : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdn'
      push_cast at h0
      linear_combination h0
    have hp : n.Prime := Nat.prime_of_fac_equiv_neg_one hWn (by omega)
    -- the `n + 2` factor: the object is `2(2(n−1)! + 1) + (n + 2)`; strip the unit `2`
    have hdq : (n + 2) ∣ 2 * (2 * (n - 1)! + 1) := by
      have h1 : (n + 2) ∣ 4 * ((n - 1)! + 1) + n := (dvd_mul_left (n + 2) n).trans hd
      rw [show 4 * ((n - 1)! + 1) + n = 2 * (2 * (n - 1)! + 1) + (n + 2) from by ring] at h1
      have h2 := Nat.dvd_sub h1 (dvd_refl (n + 2))
      rwa [Nat.add_sub_cancel] at h2
    have hdq' : (n + 2) ∣ 2 * (n - 1)! + 1 := hcop2q.dvd_of_dvd_mul_left hdq
    have hWq : (((n + 2) - 1)! : ZMod (n + 2)) = -1 := by
      rw [show n + 2 - 1 = n + 1 from by omega, hfac_succ]
      push_cast
      rw [hn2]
      have h0 : ((2 * (n - 1)! + 1 : ℕ) : ZMod (n + 2)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdq'
      push_cast at h0
      linear_combination h0
    have hq : (n + 2).Prime := Nat.prime_of_fac_equiv_neg_one hWq (by omega)
    exact ⟨hp, hq⟩

/-! ### §4 The center form — the modulus is `c² − 1`, center-squared-minus-one -/

/-- **Clement on the twin panel.**  For `m ≥ 1`, with center `c = 6m` and wings `6m ∓ 1`:
    `TwinCenterZ m` iff `36m² − 1 ∣ 4((6m−2)! + 1) + (6m−1)`.  The modulus is `c² − 1`, the
    product of the two wings — the same panel object as the L53 wing–Jacobi collapse.  The
    single integer `C(m) = 4((c−2)! + 1) + (c−1)` vanishes mod `c² − 1` exactly on twin
    centers. -/
theorem clement_center {m : ℕ} (hm : 1 ≤ m) :
    TwinCenterZ m ↔ (36 * m ^ 2 - 1) ∣ 4 * ((6 * m - 2)! + 1) + (6 * m - 1) := by
  have hC := clement_iff (n := 6 * m - 1) (by omega) (by omega)
  have e1 : 6 * m - 1 + 2 = 6 * m + 1 := by omega
  have e2 : 6 * m - 1 - 1 = 6 * m - 2 := by omega
  rw [e1, e2] at hC
  have e3 : (6 * m - 1) * (6 * m + 1) = 36 * m ^ 2 - 1 := by
    have h6 : 1 ≤ 6 * m := by omega
    have h36 : 1 ≤ 36 * m ^ 2 := by nlinarith
    zify [h6, h36]
    ring
  rw [e3] at hC
  exact hC

/-! ### §5 The kernel checker — one congruence, no primality test

House Bool/Nat-fold discipline (`Step00WitnessChainKernel`): the checker is a fused Nat fold
the kernel can unfold literally (structural recursion on fuel, mulmod at every step, `ZMod`
kept OUT of the decide path), plus a one-directional spec lemma `= true → divisibility`.
The checker never tests primality: it computes ONE residue and compares with `0`. -/

/-- Fused mulmod fold: `wilsonFold N acc k fuel` multiplies `acc` by `k, k+1, …, k+fuel−1`,
    reducing mod `N` at every step.  The factorial — the number before the prime — is never
    materialised; only its residue travels.  Structural recursion on `fuel`: the kernel can
    unfold this. -/
def wilsonFold (N : ℕ) : ℕ → ℕ → ℕ → ℕ
  | acc, _, 0 => acc
  | acc, k, fuel + 1 => wilsonFold N (acc * k % N) (k + 1) fuel

/-- Proof-side spec product: `ascProd k fuel = k · (k+1) ⋯ (k+fuel−1)` (empty product `1`).
    Never evaluated by the kernel — it exists to name what `wilsonFold` computes. -/
def ascProd : ℕ → ℕ → ℕ
  | _, 0 => 1
  | k, fuel + 1 => k * ascProd (k + 1) fuel

/-- **Clement checker.**  `clemFoldB n = true` iff the Clement object
    `4((n−1)! + 1) + n` vanishes mod `n(n+2)`, computed by `n − 1` mulmods.  Bool/Nat only;
    no `ZMod`, no `Finset`, no primality test anywhere. -/
def clemFoldB (n : ℕ) : Bool :=
  (4 * (wilsonFold (n * (n + 2)) 1 1 (n - 1) + 1) + n) % (n * (n + 2)) == 0

/-- The fold computes the spec product mod `N`: `wilsonFold N acc k fuel ≡ acc · ascProd k fuel`.
    Induction on fuel; `Nat.mod_mul_mod` absorbs the per-step reduction. -/
theorem wilsonFold_mod (N : ℕ) : ∀ fuel acc k : ℕ,
    wilsonFold N acc k fuel % N = acc * ascProd k fuel % N := by
  intro fuel
  induction fuel with
  | zero => intro acc k; simp [wilsonFold, ascProd]
  | succ fuel ih =>
    intro acc k
    simp only [wilsonFold, ascProd]
    rw [ih, Nat.mod_mul_mod, mul_assoc]

/-- Top-anchored recursion for the spec product: `ascProd k (fuel+1) = ascProd k fuel · (k+fuel)`. -/
theorem ascProd_succ_right : ∀ fuel k : ℕ, ascProd k (fuel + 1) = ascProd k fuel * (k + fuel) := by
  intro fuel
  induction fuel with
  | zero => intro k; simp [ascProd]
  | succ fuel ih =>
    intro k
    calc ascProd k (fuel + 1 + 1) = k * ascProd (k + 1) (fuel + 1) := rfl
      _ = k * (ascProd (k + 1) fuel * (k + 1 + fuel)) := by rw [ih]
      _ = (k * ascProd (k + 1) fuel) * (k + (fuel + 1)) := by ring
      _ = ascProd k (fuel + 1) * (k + (fuel + 1)) := rfl

/-- The spec product from `1` is the factorial: `ascProd 1 n = n !`. -/
theorem ascProd_one_eq_factorial : ∀ n : ℕ, ascProd 1 n = n ! := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ascProd_succ_right, ih, Nat.factorial_succ]
    ring

/-- **Checker spec (one-directional, the direction we consume).**  A passing check IS the
    Clement divisibility.  No hypotheses: the congruence bookkeeping is valid for every `n`,
    including the degenerate small cases. -/
theorem clemFoldB_dvd {n : ℕ} (h : clemFoldB n = true) :
    n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  simp only [clemFoldB, beq_iff_eq] at h
  have hfold : wilsonFold (n * (n + 2)) 1 1 (n - 1) ≡ (n - 1)! [MOD n * (n + 2)] := by
    show wilsonFold (n * (n + 2)) 1 1 (n - 1) % (n * (n + 2)) = (n - 1)! % (n * (n + 2))
    rw [wilsonFold_mod, one_mul, ascProd_one_eq_factorial]
  have hcong : 4 * (wilsonFold (n * (n + 2)) 1 1 (n - 1) + 1) + n
      ≡ 4 * ((n - 1)! + 1) + n [MOD n * (n + 2)] :=
    ((hfold.add_right 1).mul_left 4).add_right n
  exact Nat.modEq_zero_iff_dvd.mp
    (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero h)))

/-- **One-congruence twin certificate, wing form.**  A passing check at odd `n ≥ 3` certifies
    BOTH primalities at once — the checker itself never tested either. -/
theorem clemFoldB_twin_wings {n : ℕ} (h3 : 3 ≤ n) (hodd : n % 2 = 1)
    (h : clemFoldB n = true) : n.Prime ∧ (n + 2).Prime :=
  (clement_iff h3 hodd).mpr (clemFoldB_dvd h)

/-- **One-congruence twin certificate, center form.**  A passing check at the left wing
    `6m − 1` certifies the twin center `m`. -/
theorem clemFoldB_twin_center {m : ℕ} (hm : 1 ≤ m) (h : clemFoldB (6 * m - 1) = true) :
    TwinCenterZ m := by
  obtain ⟨h1, h2⟩ := clemFoldB_twin_wings (n := 6 * m - 1) (by omega) (by omega) h
  refine ⟨h1, ?_⟩
  rwa [show 6 * m - 1 + 2 = 6 * m + 1 from by omega] at h2

/-! #### Kernel demos and sanity anchors

Anchors from the criterion itself: `n = 3` (`15 ∣ 15`), `n = 5` (`35 ∣ 105`) pass;
`n = 7` (`63 ∤ 2891`, right wing `9 = 3²` composite) and `n = 9` (left wing composite) fail. -/

example : clemFoldB 3 = true := by decide
example : clemFoldB 5 = true := by decide
example : clemFoldB 7 = false := by decide
example : clemFoldB 9 = false := by decide

example : (3 * 5) ∣ 4 * ((3 - 1)! + 1) + 3 := by decide      -- 15 ∣ 15
example : (5 * 7) ∣ 4 * ((5 - 1)! + 1) + 5 := by decide      -- 35 ∣ 105
example : ¬ ((7 * 9) ∣ 4 * ((7 - 1)! + 1) + 7) := by decide  -- 63 ∤ 2891

set_option maxRecDepth 100000 in
/-- Kernel demo: the checker passes at `n = 101` — `N = 101·103 = 10403`, one hundred
    mulmods, `decide +kernel` (house discipline for fold checks). -/
theorem clemFoldB_101 : clemFoldB 101 = true := by decide +kernel

/-- The twin pair `(101, 103)` from ONE congruence: no trial division, no primality ladder —
    the kernel computed a single residue mod `10403` and `clement_iff` did the rest. -/
theorem twin_wings_101_103 : Nat.Prime 101 ∧ Nat.Prime 103 := by
  obtain ⟨h1, h2⟩ := clemFoldB_twin_wings (n := 101) (by norm_num) (by norm_num) clemFoldB_101
  exact ⟨h1, h2⟩

/-- The same certificate in panel form: `m = 17` is a twin center. -/
theorem twin_center_17 : TwinCenterZ 17 := by
  refine clemFoldB_twin_center (by norm_num) ?_
  show clemFoldB 101 = true
  exact clemFoldB_101

/-- **Negative control through the criterion.**  `(7, 9)` is refuted by the FORWARD direction
    of Clement: were both prime, `63` would divide `2891`; the kernel computes `2891 % 63 = 56`.
    HONESTY: `¬(9 prime)` is of course provable directly; the value of this demo is the ROUTE —
    the single congruence refutes the pair. -/
theorem not_twin_pair_7_9 : ¬ (Nat.Prime 7 ∧ Nat.Prime 9) := by
  intro h
  have hdvd := (clement_iff (n := 7) (by norm_num) (by norm_num)).mp h
  exact absurd (Nat.mod_eq_zero_of_dvd hdvd) (by decide)

set_option maxRecDepth 100000 in
/-- STRETCH kernel demo: the checker passes at `n = 59669` — modulus
    `N = 59669·59671 = 3560508899 = 59670² − 1`, a fold of 59668 mulmods on ten-digit
    numbers, `decide +kernel`.  Benchmarked standalone before landing: ≈ 2 s over the
    import baseline — far inside the 300 s gate. -/
theorem clemFoldB_59669 : clemFoldB 59669 = true := by decide +kernel

/-- The certified twin center at `m = 9945` (wings `59669 / 59671`) from the single
    congruence — still no primality test anywhere in the kernel path. -/
theorem twin_center_9945 : TwinCenterZ 9945 := by
  refine clemFoldB_twin_center (by norm_num) ?_
  show clemFoldB 59669 = true
  exact clemFoldB_59669

end WilsonTurn
end EuclidsPath

/-
  ### Machine honesty (recorded `#print axioms` output)

  Checked against the elaborated module (`lake env lean` with temporary `#print axioms`
  probes, probes then removed); every declaration of this file sits under the standard
  axioms only — no `sorry`, no `step00FirstCause`, no `native_decide`
  (`Lean.ofReduceBool`):

  * `composite_dvd_pred_factorial`  — [propext, Classical.choice, Quot.sound]
  * `pred_factorial_zmod_zero`      — [propext, Classical.choice, Quot.sound]
  * `wilson_dichotomy`              — [propext, Classical.choice, Quot.sound]
  * `clement_iff`                   — [propext, Classical.choice, Quot.sound]
  * `clement_center`                — [propext, Classical.choice, Quot.sound]
  * `wilsonFold_mod`                — [propext]
  * `ascProd_succ_right`            — [propext]
  * `ascProd_one_eq_factorial`      — [propext]
  * `clemFoldB_dvd`                 — [propext, Quot.sound]
  * `clemFoldB_twin_wings`          — [propext, Classical.choice, Quot.sound]
  * `clemFoldB_twin_center`         — [propext, Classical.choice, Quot.sound]
  * `clemFoldB_101`                 — (does not depend on any axioms)
  * `twin_wings_101_103`            — [propext, Classical.choice, Quot.sound]
  * `twin_center_17`                — [propext, Classical.choice, Quot.sound]
  * `not_twin_pair_7_9`             — [propext, Classical.choice, Quot.sound]
  * `clemFoldB_59669`               — (does not depend on any axioms)
  * `twin_center_9945`              — [propext, Classical.choice, Quot.sound]
-/
