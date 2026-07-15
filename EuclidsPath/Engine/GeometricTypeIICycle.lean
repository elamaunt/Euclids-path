/-
  GeometricTypeIICycle — exact cycle / collision / CRT-root identities.

  ORIGIN (parity_wall dossier §27–28 / §75 / §87 / §90): the KBSZ dilation correlation
  collapses to a fixed determinant shell; the two-row divisor bridge is exact; and the
  high–high boundary phase is governed by a CRT square root `C² ≡ 1 (mod rs)` with
  `C ≡ 1 (mod r)`, `C ≡ −1 (mod s)`.  These are exact algebraic / CRT laws (progress
  criteria A/C: exact annihilation / dimension reduction).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `det_bridge` — `m₂·k₁h₁ − m₁·k₂h₂ = 2(m₂−m₁)` (§75.4);
    * `kbsz_shell` — `r·v − s·u = 2(r−s)` for `u = Arℓ+2`, `v = Asℓ+2` (§27);
    * `same_prime_collision` — a common prime forces `p | A(s−r)ℓ` (§28, same-clock kill);
    * `crt_root_sq` — the CRT root `C` with `C ≡ 1 (r)`, `C ≡ −1 (s)` satisfies `C² = 1`
      in `ZMod (rs)` (§87);
    * `crt_root_phase` — `(Σ + ΔC) ≡ 2m₂ (mod q₁)` and `≡ 2m₁ (mod q₂)` (§87 verification).

  DISCLOSURE. Exact cycle laws of the Type-II geometry. They localize the residual phase;
  the open target is the collective energy of these CRT roots (`CRE`, see `TypeIIMap`).
  Nothing here proves twins. twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

/-! ## The determinant bridge and the KBSZ shell (§27, §75) -/

/-- **Determinant bridge (§75.4).** From `k₁h₁ = m₁n+2` and `k₂h₂ = m₂n+2`,
    `m₂·(k₁h₁) − m₁·(k₂h₂) = 2(m₂−m₁)` — the row-index cancels the long variable `n`. -/
theorem det_bridge {m₁ m₂ n k₁ k₂ h₁ h₂ : ℤ}
    (hk1 : k₁ * h₁ = m₁ * n + 2) (hk2 : k₂ * h₂ = m₂ * n + 2) :
    m₂ * (k₁ * h₁) - m₁ * (k₂ * h₂) = 2 * (m₂ - m₁) := by
  rw [hk1, hk2]; ring

/-- **KBSZ determinant shell (§27).** For the two shifted forms `u = Arℓ+2`, `v = Asℓ+2`,
    `r·v − s·u = 2(r−s)` — the fixed determinant shell independent of `A, ℓ`. -/
theorem kbsz_shell {A r s ℓ u v : ℤ} (hu : u = A * r * ℓ + 2) (hv : v = A * s * ℓ + 2) :
    r * v - s * u = 2 * (r - s) := by
  rw [hu, hv]; ring

/-- **Same-clock collision kill (§28).** If a prime `p` divides both `Arℓ+2` and `Asℓ+2`
    then `p | A(s−r)ℓ` — so with `p ∤ Aℓ` and `p > |r−s|` no common future prime survives. -/
theorem same_prime_collision {p A r s ℓ : ℤ}
    (h1 : p ∣ A * r * ℓ + 2) (h2 : p ∣ A * s * ℓ + 2) :
    p ∣ A * (s - r) * ℓ := by
  have hsub : (A * s * ℓ + 2) - (A * r * ℓ + 2) = A * (s - r) * ℓ := by ring
  have := dvd_sub h2 h1
  rwa [hsub] at this

/-! ## The CRT square root `C² ≡ 1 (mod rs)` (§87) -/

/-- **CRT root of unity (§87).** For coprime `r, s` the CRT element `C` with `C ≡ 1 (mod r)`,
    `C ≡ −1 (mod s)` is a square root of one modulo `rs`: `C² = 1`. -/
theorem crt_root_sq {r s : ℕ} (h : Nat.Coprime r s) :
    ∃ C : ZMod (r * s), C ^ 2 = 1 := by
  refine ⟨(ZMod.chineseRemainder h).symm (1, -1), ?_⟩
  apply (ZMod.chineseRemainder h).injective
  rw [map_pow, RingEquiv.apply_symm_apply, map_one, pow_two]
  ext <;> simp

/-- **CRT-root phase (§87).** With `C ≡ 1 (mod q₁)`, `C ≡ −1 (mod q₂)`, the combined phase
    `Σ + Δ·C` (with `Σ = m₁+m₂`, `Δ = m₂−m₁`) reduces to `2m₂ (mod q₁)` and `2m₁ (mod q₂)`. -/
theorem crt_root_phase {q₁ q₂ C m₁ m₂ : ℤ}
    (hC1 : C ≡ 1 [ZMOD q₁]) (hC2 : C ≡ -1 [ZMOD q₂]) :
    ((m₁ + m₂) + (m₂ - m₁) * C ≡ 2 * m₂ [ZMOD q₁])
      ∧ ((m₁ + m₂) + (m₂ - m₁) * C ≡ 2 * m₁ [ZMOD q₂]) := by
  refine ⟨?_, ?_⟩
  · have h := (Int.ModEq.mul_left (m₂ - m₁) hC1).add_left (m₁ + m₂)
    rwa [show (m₁ + m₂) + (m₂ - m₁) * 1 = 2 * m₂ from by ring] at h
  · have h := (Int.ModEq.mul_left (m₂ - m₁) hC2).add_left (m₁ + m₂)
    rwa [show (m₁ + m₂) + (m₂ - m₁) * (-1) = 2 * m₁ from by ring] at h

end TypeII
end Geometric
end EuclidsPath
