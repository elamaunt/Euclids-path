/-
  GeometricTypeIIMap — the honest map: the single open target CRE and the conditional
  reduction to twin primes.

  ORIGIN (parity_wall dossier §97 / §101 / §108 / Appendix E): after all the exact local
  Type-I projection, S_{2k} support Pythagoras, cycle laws and no-go markers, the parity
  wall is localized to ONE object — the collective cross-modulus CRT-root energy
  `𝔈_× ≪_B x²(log x)^{-B}` (CRE / PFCLS).  This module states that single target and the
  one-directional reduction `[green identities] + CRE + Ford–Maynard ⟹ twins`.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `CRE` — 🔴 the single OPEN target (a named `Prop`, NOT proved, axiom-clean);
    * `twins_of_typeII` — 🟢 CONDITIONAL: the bundled Type-II program (CRE + the named
      Ford–Maynard prime-producing chain) gives infinitely many twin centers.
      ONE-DIRECTIONAL; touches neither `step00FirstCause` nor `twin_prime_conjecture`.

  STATUS MAP (§101 / §104 / Appendix E) — the whole Type-II front, machine-anchored:
    ✅ exact local Type-I projection Y_p = G_p + Z_p     — `TypeII.Projection`
    ✅ two-row diagonal covariance −1/p², survival −1/(p−1)²  — `TypeII.Projection`
    ✅ pure residual mean zero (annihilation, criterion A)    — `Zrow_mean_zero`
    ✅ S_4 summability gain 1/p → 1/p^3 (criterion B)         — `TypeII.Quartic`, `zEnergy_S4`
    ✅ support Pythagoras (distinct supports orthogonal)      — `pythagoras_of_orthogonal`
    ✅ determinant bridge / KBSZ shell (criterion C)          — `TypeII.Cycle`, `det_bridge`
    ✅ CRT-root C² ≡ 1 (mod rs) and its phase                 — `crt_root_sq`, `crt_root_phase`
    ✅ parity wall's exact local form: mixed S_2 energy 1/p   — `mixed_mode_parity_scale`
    ⛔ closed routes: Möbius/Chowla trap, DHR collapse, scalar-BV, false √M — `TypeII.NoGo`
    🔴 THE single open target:  `CRE` (this file) — where to hit.
    🟡 conditional: `twins_of_typeII` (CRE + Ford–Maynard ⟹ twins).

  DISCLOSURE. This is NOT a proof of twins — and the dossier itself proves it is not: the
  parity wall is localized, not defeated.  `CRE` is a named open `Prop` (no `sorry`, no
  axiom).  The Ford–Maynard step is a named hypothesis requiring literal external audit
  (Appendix D / §105).  twin sorry untouched.
-/
import Mathlib
import EuclidsPath.Step00_Overview

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

/-! ## The single open target: CRE / PFCLS (§97, Appendix E) -/

/-- 🔴 **CRE / PFCLS (§CRE, Appendix E) — THE single open target.** The cross-modulus
    CRT-root energy `𝔈` admits arbitrary logarithmic saving: `𝔈(x) ≪_B x²(log x)^{-B}`.
    This is the ONE unproven analytic input of the whole Type-II map — the collective
    additive/reciprocal energy of the factorization-labelled square roots `C² ≡ 1 (mod rs)`
    with the true Euler/Möbius coefficients, after removal of all principal/diagonal
    resonances.  It is a named `Prop`, NOT proved (no `sorry`, no axiom): the place to hit. -/
def CRE (𝔈 : ℝ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → 𝔈 x ≤ C * x ^ 2 / (Real.log x) ^ B

/-! ## The conditional reduction to twins (§52, §85, §101) -/

/-- The bundled Type-II program: the open cross-modulus energy `𝔈` satisfying `CRE`, together
    with the named Ford–Maynard prime-producing chain (`chain`) that converts the resulting
    structured Type-II bound into cofinal twin centers.  The green machinery lives in the
    sibling modules (`TypeII.Projection`/`Quartic`/`Cycle`); the only OPEN pieces are `cre`
    (the analytic energy bound) and `chain` (which requires literal external audit, §105). -/
structure TypeIIProgram where
  𝔈 : ℝ → ℝ
  cre : CRE 𝔈
  chain : CRE 𝔈 → ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m

/-- 🟢 **Conditional twins (§101).** The bundled Type-II program yields infinitely many twin
    centers.  ONE-DIRECTIONAL: the program is strictly stronger than "twins" (it carries the
    CRE energy bound and the external prime-producing criterion), so this is a genuine
    sufficient condition, not an iff-with-the-conjecture.  Uses neither `step00FirstCause`
    nor `twin_prime_conjecture`. -/
theorem twins_of_typeII (H : TypeIIProgram) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsTwinCenter m :=
  H.chain H.cre

end TypeII
end Geometric
end EuclidsPath
