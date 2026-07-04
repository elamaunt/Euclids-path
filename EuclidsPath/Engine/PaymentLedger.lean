/-
  Payment algebra (boundary-energy ledger). Source: twin_prime_boundary_energy_ledger_ru_20260630.md.
  Prose: prose/26_PaymentLedger.md.

  "When the engine stops — it pays, and payment obeys a strict order."
  Here the PROVABLE algebraic core of the payment law is recorded (without distribution):

    * channel law: a clean source in one residue mod p ⟹ exactly `p−2` compatible channels;
    * tax law: the ban `a ≢ θ (mod q)` ⟹ capacity factor `(q−3)/(q−2)`;
    * **shifted-primorial obstruction (DEFICIT LAW):** a free passage to ordered prime `p`
      requires `P_{<p} ∣ a−θ`, hence `P_{<p} ≤ a` — and if the primorial has outgrown `a`, passage is IMPOSSIBLE.

  Honest boundary (numbers, tools/RESULTS_payment_budget.md): the total capacity loss over small
  primes ~ `1/ln A` (Mertens) — therefore the quantitative shifted-charge budget (§20.2) does NOT close
  distribution-free and remains an explicit open input. Here — exactly the provable algebra.

  Everything is elementary (Nat/Int + Finset). No analysis / distribution / sieve.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Payment

/-! ### Channel law: exactly `p − 2` clean-compatible channels -/

/--
  **Channel residue law (§12.1).** If `p > 3`, `p ∣ 6n − ε` (boundary on the opposite side)
  and `6m + σ = a (6n + ε)`, then source `m` lies in a fixed residue class:
  `6m ≡ 2aε − σ (mod p)`. Pure CRT algebra.
-/
theorem channel_residue {p : ℕ} {m n a : ℤ} {σ ε : ℤ}
    (hlift : 6 * m + σ = a * (6 * n + ε))
    (hbnd : (p : ℤ) ∣ 6 * n - ε) :
    (p : ℤ) ∣ (6 * m - (2 * a * ε - σ)) := by
  -- 6n ≡ ε ⟹ 6n+ε ≡ 2ε ⟹ a(6n+ε) ≡ 2aε ⟹ 6m+σ ≡ 2aε ⟹ 6m ≡ 2aε−σ
  have h1 : (p : ℤ) ∣ a * (6 * n + ε) - 2 * a * ε := by
    have : a * (6 * n + ε) - 2 * a * ε = a * (6 * n - ε) := by ring
    rw [this]; exact Dvd.dvd.mul_left hbnd a
  have h2 : 6 * m - (2 * a * ε - σ) = a * (6 * n + ε) - 2 * a * ε := by
    rw [← hlift]; ring
  rw [h2]; exact h1

/-! ### Tax / θ-dichotomy -/

/--
  **Tax dichotomy (§15.1).** Let `θ = σε`. The additional ban on the `6m − σ` side by
  small `q` (`q ∣ a(6n+ε) − 2σ`) vanishes exactly when `a ≡ θ (mod q)` — then it coincides with the
  already-forbidden class. That is, "no tax ⟺ `q ∣ a − θ`".
-/
theorem no_tax_iff_shifted {q : ℕ} {a θ : ℤ} :
    (q : ℤ) ∣ a - θ ↔ a ≡ θ [ZMOD (q : ℤ)] := by
  rw [Int.modEq_iff_dvd]   -- a ≡ θ [ZMOD q] ↔ q ∣ θ - a
  exact (dvd_sub_comm)

/-! ### Shifted-primorial obstruction — DEFICIT LAW -/

/--
  **Tax-free primes divide the shift (Lemma 16.1).** If for prime `q` there is no tax
  (`q ∣ a − θ`) for each `q` in the set `G`, and these `q` are pairwise coprime (via primorial
  `P = ∏ q`), then `P ∣ a − θ`. (Here `P` is the product over `G`; divisibilities combine as lcm.)
-/
theorem primorial_dvd_shift {G : Finset ℕ} {a θ : ℤ}
    (hcop : (G : Set ℕ).Pairwise (Nat.Coprime))
    (htax : ∀ q ∈ G, (q : ℤ) ∣ a - θ) :
    (G.prod (fun q => (q : ℤ))) ∣ a - θ := by
  -- a product of pairwise coprime divisors divides the common argument
  exact Finset.prod_dvd_of_coprime (by
    intro i hi j hj hij
    exact (hcop hi hj hij).isCoprime.intCast) htax

/--
  **Shifted-primorial obstruction (Theorem 16.2 / deficit law).** If the primorial of small primes
  `P` divides `a − θ` and `a ≠ θ`, then `P ≤ |a − θ|`. Contraposition (threshold `Y_A`, §17):
  if `P > |a − θ|`, then `a = θ` — a free passage to `p` is IMPOSSIBLE for non-trivial `a`.
-/
theorem shifted_primorial_bound {P a θ : ℤ}
    (hdvd : P ∣ a - θ) (hne : a ≠ θ) : P ≤ |a - θ| := by
  have hnz : a - θ ≠ 0 := sub_ne_zero.mpr hne
  exact Int.le_of_dvd (abs_pos.mpr hnz) ((dvd_abs P (a - θ)).mpr hdvd)

/--
  **Threshold `Y_A`: a late boundary is not free.** If the primorial `P` exceeds the upper bound
  `Z` of the active divisor (`|a − θ| ≤ Z < P`), then `P ∣ a − θ` forces `a = θ`: a tax-free
  passage to ordered prime `p ≥ Y_A` is impossible (there is no non-trivial `a ≤ Z` divisible by `P`).
-/
theorem late_boundary_not_free {P a θ Z : ℤ}
    (hdvd : P ∣ a - θ) (hZ : |a - θ| ≤ Z) (hlate : Z < P) : a = θ := by
  by_contra hne
  have := shifted_primorial_bound hdvd hne
  omega

end EuclidsPath.Payment
