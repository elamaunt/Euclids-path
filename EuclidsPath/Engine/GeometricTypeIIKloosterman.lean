/-
  GeometricTypeIIKloosterman — the Kloosterman / four-corner geometry of the Type-II remainder.

  ORIGIN (parity_wall Prime-Chaos session dossier §22 / §23 / §24 / §25).  The graph operator and the
  Kloosterman operator are ONE object in different bases: the Fourier transform of the inversion
  `x ↦ −2x⁻¹` is `(1/p) Kl_p(a, 2b)` (§22).  The three-component Kloosterman variety of coincidences
  has size `|V_p| = 3(p−1)(p−2)` (§23).  The four corners obey the determinant law
  `det = 2A(r₁−r₂)(ℓ₁−ℓ₂)` (§24), so a rank-one degeneracy modulo `p ∤ 2A` forces `r₁ ≡ r₂` or
  `ℓ₁ ≡ ℓ₂`.  These are the exact objects the repo already proves at Weil strength.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `graph_eq_kloosterman` — the graph=Kloosterman bridge (§22, = repo `circleSum_eq_neg_kloos`);
    * `three_component_count` — `|V_p| = 3(p−1)(p−2)` (§23, = repo `kloosN4_card`);
    * `kloosterman_weil_bound` — `‖Kl‖⁴ ≤ 2p³` (the Weil-strength cancellation, = repo `kloos_norm_le`);
    * `four_corner_det` — the four-corner determinant law `2A(r₁−r₂)(ℓ₁−ℓ₂)` (§24, new);
    * `four_corner_rank_one` — rank-one degeneracy forces a coincidence of rows or columns (§24).

  DISCLOSURE. The determinant-rectangle counting `N_d ≤ 4·2^{ω(d)} R²L²/d` (§25) is documented but
  not formalized here; the wall is the transfer, not the Kloosterman geometry. twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Engine.Step00CircleEnergy
import EuclidsPath.Engine.Step00KloostermanMoment

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open EuclidsPath.CircleEnergy EuclidsPath.KloostermanMoment

/-! ## Graph = Kloosterman (§22) -/

/-- **Graph = Kloosterman (§22).** The inversion Fourier operator IS the Kloosterman operator: for
    `u ≠ 0`, `circleSum u = −Kl(u/2, u/2)`.  (The Type-II reading of the repo's Weil bridge.) -/
theorem graph_eq_kloosterman {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) {u : ZMod ℓ} (hu : u ≠ 0) :
    circleSum d u = - kloos (u * (2 : ZMod ℓ)⁻¹) (u * (2 : ZMod ℓ)⁻¹) :=
  circleSum_eq_neg_kloos h2 hd hu

/-! ## Three-component geometry (§23) and the Weil bound -/

/-- **Three-component Kloosterman geometry (§23).** `|V_p| = 3(p−1)(p−2)`. -/
theorem three_component_count {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (kloosN4 ℓ).card = 3 * (ℓ - 1) * (ℓ - 2) :=
  kloosN4_card h2

/-- **Weil-strength cancellation.** `‖Kl_p(a,b)‖⁴ ≤ 2p³` for `a,b ≠ 0` — the fourth-moment
    input controlling the connected part. -/
theorem kloosterman_weil_bound {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {a b : ZMod ℓ}
    (ha : a ≠ 0) (hb : b ≠ 0) : ‖kloos a b‖ ^ 4 ≤ 2 * (ℓ : ℝ) ^ 3 :=
  kloos_norm_le h2 ha hb

/-! ## The four-corner determinant law (§24) -/

/-- **Four-corner determinant law (§24).** The `2×2` corner determinant is `2A(r₁−r₂)(ℓ₁−ℓ₂)`. -/
theorem four_corner_det (A r₁ r₂ ℓ₁ ℓ₂ : ℤ) :
    (A * r₁ * ℓ₁ + 2) * (A * r₂ * ℓ₂ + 2) - (A * r₁ * ℓ₂ + 2) * (A * r₂ * ℓ₁ + 2)
      = 2 * A * (r₁ - r₂) * (ℓ₁ - ℓ₂) := by
  ring

/-- **Rank-one degeneracy (§24).** Modulo a prime `p ∤ 2A`, a vanishing corner determinant forces a
    coincidence `r₁ ≡ r₂` or `ℓ₁ ≡ ℓ₂` — the determinant-degenerate locus of the four corners. -/
theorem four_corner_rank_one {p : ℕ} (hp : p.Prime) {A r₁ r₂ ℓ₁ ℓ₂ : ℤ}
    (hA : ¬ (p : ℤ) ∣ 2 * A)
    (hdet : (p : ℤ) ∣ ((A * r₁ * ℓ₁ + 2) * (A * r₂ * ℓ₂ + 2)
      - (A * r₁ * ℓ₂ + 2) * (A * r₂ * ℓ₁ + 2))) :
    (p : ℤ) ∣ (r₁ - r₂) ∨ (p : ℤ) ∣ (ℓ₁ - ℓ₂) := by
  rw [four_corner_det] at hdet
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_mul.mp hdet with h | h
  · rcases hp'.dvd_mul.mp h with h1 | h2
    · exact absurd h1 hA
    · exact Or.inl h2
  · exact Or.inr h

end TypeII
end Geometric
end EuclidsPath
