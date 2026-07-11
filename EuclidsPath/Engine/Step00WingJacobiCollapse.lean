import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The wing–Jacobi collapse — the quadratic layer over the twin panel is mod-8 bookkeeping

A certified kill of the imaginary-objects phase.  The proposed observable class was: "Jacobi
/ Gauss-sum phases over the twin panel `{m, 6m−1, 6m+1}` carry multiplicative content that the
additive window layer cannot see" — the hope being a Friedlander–Iwaniec-style mechanism, where
Gauss-sum factorizations of genuinely independent quadratic phases produce bilinear leverage.
This module PROVES the negative structure theorem: over the panel, every cross-symbol between
the fixed panel members COLLAPSES to a residue character of conductor dividing 8 evaluated on
the panel itself.  The fixed offset `2` between the wings (and the fixed offset `1` between the
center scaled by 6 and each wing) destroys exactly the multiplicative independence the
mechanism needs: `6m−1 ≡ −2 (mod 6m+1)`, `6m+1 ≡ 2 (mod 6m−1)`, `6m±1 ≡ ±1 (mod m)`.
A supplementary law eats each symbol.

## The collapse laws (all green, standard axioms only)

* `wing_cross_jacobi_right` — `J(6m−1 | 6m+1) = χ₈'(6m+1)`: the right-over-left cross symbol
  is the mod-8 character of the right wing (via `−2` + `jacobiSym.at_neg_two`).
* `wing_cross_jacobi_left` — `J(6m+1 | 6m−1) = χ₈(6m−1)`: the left-over-right cross symbol is
  the mod-8 character of the left wing (via `2` + `jacobiSym.at_two`).
* `wing_reciprocity_trivial` — the reciprocity pairing of the two wings is IDENTICALLY `+1`:
  the Jacobi reciprocity sign `(−1)^{(3m−1)·3m}` dies on the product of consecutive integers,
  and the wings are always coprime, so the two cross symbols are mutually inverse signs.
* `wing_phase_product` — corollary: `χ₈'(6m+1) · χ₈(6m−1) = 1` for every `m ≥ 1`; the two
  mod-8 phases of a panel are LOCKED, one determines the other.
* `center_wing_collapse_odd` / `center_wing_collapse_left_odd` — for odd `m`, the center-over-
  wing symbols also collapse: `J(m | 6m+1) = χ₄(m) = J(m | 6m−1)`.  Both proofs run through
  Jacobi reciprocity and `6m±1 ≡ ±1 (mod m)`.  HONEST SCOPE NOTE: for even `m` the same
  collapse holds with the extra factor `χ₈(wing)^{v₂(m)}` from peeling the powers of two out
  of `m` (`jacobiSym.mul_left` + `jacobiSym.at_two` per factor of 2); the `v₂` bookkeeping is
  routine but noisy and is NOT formalized here — the even case is a scope note, not a gap in
  the odd-case theorems.
* `spin_fixed_label_periodic_left` / `_right` — the certified boundary of the kill: for a FIXED
  prime label `p`, the edge spin (Legendre symbol of the cofactor at an exact strike
  `6m∓1 = p·c`) is periodic in the center with period `p²`.  The cofactor moves by exactly
  `6p` per period step, so its class mod `p` is unchanged — fixed-small-label spins are a
  finite, linear-layer object at level `p²`.

## DISCLOSURE — what this closes, and the anti-vocabulary

* The "Gauss-sum energy" `|τ(χ)|² = q` is a unitary basis-change statement, not an arithmetic
  lever: see `gaussSum_mul_gaussSum_eq_card` and `gaussSum_sq` (Mathlib/NumberTheory/GaussSum);
  likewise the balanced-character cancellation `quadraticChar_sum_zero`
  (Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic).  Cited here for the ledger; no
  Lean content of this module depends on them.
* Consequently every fixed-modulus character twist of a window sum over the panel lies in the
  additive span at level `lcm(24, P_A)` — energy-partition "observables" built from such twists
  are exact linear images of the additive layer, which is `Step00StrikeFourier` territory.
  They are costumes, not new observables.
* This module CLOSES the quadratic layer over the panel: all cross symbols between panel
  members at fixed offsets are mod-8 (resp. mod-4) phases of the panel, and fixed-label edge
  spins are `p²`-periodic.  The ONLY surviving quadratic channel is edge spins at GROWING
  labels, which belong to the peel-bilinear harness, not to this file.
* Anti-vocabulary: no claim is made that the collapse refutes the twin conjecture route as a
  whole, nor anything about symbols at growing moduli; a refutation of a proposed lever,
  machine-checked, is a ledger law about the LEVER.
-/

namespace EuclidsPath
namespace WingJacobiCollapse

open NumberTheorySymbols

/-! ### §1 The wing cross symbols are mod-8 phases -/

/-- **Right-over-left collapse.**  The Jacobi symbol of the left wing over the right wing is
    the mod-8 character `χ₈'` of the right wing itself: `6m−1 ≡ −2 (mod 6m+1)`, and the
    supplementary law at `−2` eats the symbol.  No multiplicative content survives the fixed
    offset `2`. -/
theorem wing_cross_jacobi_right (m : ℕ) (hm : 1 ≤ m) :
    J(((6 * m - 1 : ℕ) : ℤ) | 6 * m + 1) = ZMod.χ₈' ((6 * m + 1 : ℕ) : ZMod 8) := by
  have hodd : Odd (6 * m + 1) := ⟨3 * m, by ring⟩
  have hmod : ((6 * m - 1 : ℕ) : ℤ) % ((6 * m + 1 : ℕ) : ℤ)
      = (-2 : ℤ) % ((6 * m + 1 : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have he : ((6 * m - 1 : ℕ) : ℤ) - (-2) = ((6 * m + 1 : ℕ) : ℤ) := by omega
    rw [he, Int.emod_self]
  calc J(((6 * m - 1 : ℕ) : ℤ) | 6 * m + 1)
      = J(-2 | 6 * m + 1) := jacobiSym.mod_left' hmod
    _ = ZMod.χ₈' ((6 * m + 1 : ℕ) : ZMod 8) := jacobiSym.at_neg_two hodd

/-- **Left-over-right collapse.**  The Jacobi symbol of the right wing over the left wing is
    the mod-8 character `χ₈` of the left wing: `6m+1 ≡ 2 (mod 6m−1)`, supplementary law
    at `2`. -/
theorem wing_cross_jacobi_left (m : ℕ) (hm : 1 ≤ m) :
    J(((6 * m + 1 : ℕ) : ℤ) | 6 * m - 1) = ZMod.χ₈ ((6 * m - 1 : ℕ) : ZMod 8) := by
  have hodd : Odd (6 * m - 1) := ⟨3 * m - 1, by omega⟩
  have hmod : ((6 * m + 1 : ℕ) : ℤ) % ((6 * m - 1 : ℕ) : ℤ)
      = (2 : ℤ) % ((6 * m - 1 : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have he : ((6 * m + 1 : ℕ) : ℤ) - 2 = ((6 * m - 1 : ℕ) : ℤ) := by omega
    rw [he, Int.emod_self]
  calc J(((6 * m + 1 : ℕ) : ℤ) | 6 * m - 1)
      = J(2 | 6 * m - 1) := jacobiSym.mod_left' hmod
    _ = ZMod.χ₈ ((6 * m - 1 : ℕ) : ZMod 8) := jacobiSym.at_two hodd

/-! ### §2 Reciprocity between the wings is identically trivial -/

/-- **The wing reciprocity sign is dead.**  For every `m ≥ 1` the product of the two cross
    symbols is `+1`: the Jacobi reciprocity sign is `(−1)^{(3m−1)·3m}`, and `(3m−1)·3m` is a
    product of consecutive integers, hence even; the wings are coprime (they differ by `2` and
    are both odd), so each symbol is a genuine `±1` and they are equal — their product is a
    square.  The reciprocity pairing of the panel carries ZERO information. -/
theorem wing_reciprocity_trivial (m : ℕ) (hm : 1 ≤ m) :
    J(((6 * m - 1 : ℕ) : ℤ) | 6 * m + 1) * J(((6 * m + 1 : ℕ) : ℤ) | 6 * m - 1) = 1 := by
  have hodd₁ : Odd (6 * m - 1) := ⟨3 * m - 1, by omega⟩
  have hodd₂ : Odd (6 * m + 1) := ⟨3 * m, by ring⟩
  have hrec := jacobiSym.quadratic_reciprocity hodd₁ hodd₂
  have hsign : ((-1 : ℤ)) ^ ((6 * m - 1) / 2 * ((6 * m + 1) / 2)) = 1 := by
    have hexp : (6 * m - 1) / 2 * ((6 * m + 1) / 2) = (3 * m - 1) * (3 * m - 1 + 1) := by
      have e1 : (6 * m - 1) / 2 = 3 * m - 1 := by omega
      have e2 : (6 * m + 1) / 2 = 3 * m := by omega
      rw [e1, e2]
      congr 1
      omega
    rw [hexp]
    exact Even.neg_one_pow (Nat.even_mul_succ_self (3 * m - 1))
  have hg : Nat.gcd (6 * m + 1) (6 * m - 1) = 1 := by
    have h1 := Nat.gcd_dvd_left (6 * m + 1) (6 * m - 1)
    have h2 := Nat.gcd_dvd_right (6 * m + 1) (6 * m - 1)
    have h3 : Nat.gcd (6 * m + 1) (6 * m - 1) ∣ 2 := by
      have hs := Nat.dvd_sub h1 h2
      rwa [show 6 * m + 1 - (6 * m - 1) = 2 from by omega] at hs
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := h ▸ h1
      omega
  have hcop : Int.gcd ((6 * m + 1 : ℕ) : ℤ) ((6 * m - 1 : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hg
  rw [hrec, hsign, one_mul, ← pow_two]
  exact jacobiSym.sq_one hcop

/-- **Corollary: the two mod-8 phases of a panel are locked.**  Combining the two collapse
    laws with the trivial reciprocity: `χ₈'(6m+1) · χ₈(6m−1) = 1`.  One wing's mod-8 phase
    determines the other's — the panel carries ONE mod-8 bit, not two. -/
theorem wing_phase_product (m : ℕ) (hm : 1 ≤ m) :
    ZMod.χ₈' ((6 * m + 1 : ℕ) : ZMod 8) * ZMod.χ₈ ((6 * m - 1 : ℕ) : ZMod 8) = 1 := by
  rw [← wing_cross_jacobi_right m hm, ← wing_cross_jacobi_left m hm]
  exact wing_reciprocity_trivial m hm

/-! ### §3 The center–wing symbols collapse to mod-4 phases (odd centers) -/

/-- **Center-over-right-wing collapse (odd center).**  For odd `m`, the symbol of the center
    over the right wing is the mod-4 character of the center: reciprocity flips the symbol at
    the cost of `qrSign (6m+1) m = χ₄(m)` (since `6m+1 ≡ 3 (mod 4)` for odd `m`), and the
    flipped symbol dies on `6m+1 ≡ 1 (mod m)`. -/
theorem center_wing_collapse_odd (m : ℕ) (hm : Odd m) :
    J((m : ℤ) | 6 * m + 1) = ZMod.χ₄ ((m : ℕ) : ZMod 4) := by
  have hm1 : 1 ≤ m := hm.pos
  have hodd' : Odd (6 * m + 1) := ⟨3 * m, by ring⟩
  have h4 : (6 * m + 1) % 4 = 3 := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hJ : J(((6 * m + 1 : ℕ) : ℤ) | m) = 1 := by
    have h1 : ((6 * m + 1 : ℕ) : ℤ) % (m : ℤ) = (1 : ℤ) % (m : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      have he : ((6 * m + 1 : ℕ) : ℤ) - 1 = 6 * (m : ℤ) := by omega
      rw [he, Int.mul_emod_left]
    rw [jacobiSym.mod_left' h1, jacobiSym.one_left]
  rw [jacobiSym.quadratic_reciprocity' hm hodd', hJ, mul_one]
  simp only [qrSign]
  rw [ZMod.χ₄_nat_three_mod_four h4]
  exact jacobiSym.at_neg_one hm

/-- **Center-over-left-wing collapse (odd center).**  Same collapse on the other wing: here
    `6m−1 ≡ 1 (mod 4)` for odd `m`, so the reciprocity sign is invisible, and
    `6m−1 ≡ −1 (mod m)` leaves exactly `χ₄(m)` via the supplementary law at `−1`. -/
theorem center_wing_collapse_left_odd (m : ℕ) (hm : Odd m) :
    J((m : ℤ) | 6 * m - 1) = ZMod.χ₄ ((m : ℕ) : ZMod 4) := by
  have hm1 : 1 ≤ m := hm.pos
  have hodd' : Odd (6 * m - 1) := ⟨3 * m - 1, by omega⟩
  have h4 : (6 * m - 1) % 4 = 1 := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hJ : J(((6 * m - 1 : ℕ) : ℤ) | m) = ZMod.χ₄ ((m : ℕ) : ZMod 4) := by
    have h1 : ((6 * m - 1 : ℕ) : ℤ) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      have he : ((6 * m - 1 : ℕ) : ℤ) - (-1) = 6 * (m : ℤ) := by omega
      rw [he, Int.mul_emod_left]
    rw [jacobiSym.mod_left' h1]
    exact jacobiSym.at_neg_one hm
  rw [jacobiSym.quadratic_reciprocity' hm hodd', hJ]
  simp only [qrSign]
  rw [ZMod.χ₄_nat_one_mod_four h4, jacobiSym.one_left, one_mul]

/-! ### §4 The certified boundary: fixed-label edge spins are `p²`-periodic -/

/-- **Fixed-label spin periodicity, left wing.**  If the prime `p` strikes the left wing at
    center `m` with cofactor `c` (`6m−1 = p·c`) and again at center `m + p²` with cofactor
    `c'`, then the edge spins agree: the cofactor moves by exactly `6p` per `p²`-step, so its
    Legendre class mod `p` is unchanged.  Fixed-small-`p` spins are a linear-layer object at
    level `p²`; only GROWING labels can carry content (peel-bilinear territory). -/
theorem spin_fixed_label_periodic_left (p : ℕ) [Fact p.Prime] {m c c' : ℕ} (hm : 1 ≤ m)
    (h : 6 * m - 1 = p * c) (h' : 6 * (m + p ^ 2) - 1 = p * c') :
    legendreSym p (c' : ℤ) = legendreSym p (c : ℤ) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have e : p * c' = p * (c + 6 * p) := by
    have e1 : 6 * (m + p ^ 2) - 1 = 6 * m - 1 + 6 * p ^ 2 := by omega
    rw [← h', e1, h]
    ring
  have hcc : c' = c + 6 * p := Nat.eq_of_mul_eq_mul_left hp0 e
  subst hcc
  have hcast : ((c + 6 * p : ℕ) : ℤ) = (c : ℤ) + (p : ℤ) * 6 := by
    push_cast
    ring
  rw [hcast, legendreSym.mod, Int.add_mul_emod_self_left, ← legendreSym.mod]

/-- **Fixed-label spin periodicity, right wing.**  The same `p²`-periodicity on the right
    wing: `6m+1 = p·c` and `6(m+p²)+1 = p·c'` force `c' = c + 6p`, hence equal spins. -/
theorem spin_fixed_label_periodic_right (p : ℕ) [Fact p.Prime] {m c c' : ℕ}
    (h : 6 * m + 1 = p * c) (h' : 6 * (m + p ^ 2) + 1 = p * c') :
    legendreSym p (c' : ℤ) = legendreSym p (c : ℤ) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have e : p * c' = p * (c + 6 * p) := by
    have e1 : 6 * (m + p ^ 2) + 1 = 6 * m + 1 + 6 * p ^ 2 := by ring
    rw [← h', e1, h]
    ring
  have hcc : c' = c + 6 * p := Nat.eq_of_mul_eq_mul_left hp0 e
  subst hcc
  have hcast : ((c + 6 * p : ℕ) : ℤ) = (c : ℤ) + (p : ℤ) * 6 := by
    push_cast
    ring
  rw [hcast, legendreSym.mod, Int.add_mul_emod_self_left, ← legendreSym.mod]

end WingJacobiCollapse
end EuclidsPath

/-
  ### Machine honesty (recorded `#print axioms` output)

  Checked against the elaborated module (scratch run with `lake env lean`, scratch deleted);
  every declaration of this file sits under the standard axioms only — no `sorry`,
  no `step00FirstCause`, no `native_decide` (`Lean.ofReduceBool`):

  * `wing_cross_jacobi_right`            — [propext, Classical.choice, Quot.sound]
  * `wing_cross_jacobi_left`             — [propext, Classical.choice, Quot.sound]
  * `wing_reciprocity_trivial`           — [propext, Classical.choice, Quot.sound]
  * `wing_phase_product`                 — [propext, Classical.choice, Quot.sound]
  * `center_wing_collapse_odd`           — [propext, Classical.choice, Quot.sound]
  * `center_wing_collapse_left_odd`      — [propext, Classical.choice, Quot.sound]
  * `spin_fixed_label_periodic_left`     — [propext, Classical.choice, Quot.sound]
  * `spin_fixed_label_periodic_right`    — [propext, Classical.choice, Quot.sound]
-/
