/-
  GeometricTypeIISpectrum — the survivor graph `B_p = J − I` and its operator spectrum.

  ORIGIN (parity_wall Prime-Chaos session dossier §14 / §15 / §16 / §17). After matching the
  forbidden classes, the allowed-cell matrix on the units `U_p` is `B_p = J − I`, i.e. the complete
  graph `K_{q,q} ∖ M` with `q = p − 1`.  The normalized survivor operator `T_p = (J − I)/q` has the
  EXACT spectrum: eigenvalue `(q−1)/q = (p−2)/(p−1)` on the constants (multiplicity 1) and
  `−1/q = −1/(p−1)` on the mean-zero subspace (multiplicity `q − 1 = p − 2`).  The centered survivor
  operator carries the FIXED-POINT parity eigenvalue `−1/(p−2)` on the mean-zero subspace and kills
  constants — this is the eigenvalue that reappears at every even moment (§27).  Finally the
  Schatten `2k`-energy `Tr|Z_p|^{2k} = (p−2)(1/(p−1))^{2k}` is exactly `zEnergy k p`.

  We formalize the spectrum as OPERATOR eigenvalue identities (not matrix diagonalization): the
  operator acts on `κ → ℝ` for a finite `κ` (the units, `card κ = p − 1`).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `survivorKernel_apply`, `survivorOp_eq_kernel` — the operator is `(1/q)(J − I)` (§14);
    * `survivorOp_const` / `survivorOp_meanzero` — eigenvalues `(q−1)/q` and `−1/q` (§15);
    * `centeredSurvivorOp_meanzero` / `_const` — the fixed-point eigenvalue `−1/(q−1)` (§16);
    * `zEnergy_eq_schatten` — `zEnergy k p = (p−2)(1/(p−1))^{2k}` (the Schatten form, §17).

  DISCLOSURE. The eigenvalue `−1/(p−2)` is a wall marker, not a defeat of the wall. twin sorry
  untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIIQuartic

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ## The survivor graph `B = J − I` (§14) -/

/-- The survivor adjacency kernel `B = J − I` on the units (complete graph): `1` off the diagonal,
    `0` on it. -/
def survivorKernel {κ : Type*} [DecidableEq κ] (a b : κ) : ℝ := if a = b then 0 else 1

/-- The `J − I` action: `(B f)(a) = Σ f − f(a)`. -/
theorem survivorKernel_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ℝ) (a : κ) :
    ∑ b, survivorKernel a b * f b = (∑ b, f b) - f a := by
  unfold survivorKernel
  have h : ∀ b, (if a = b then (0 : ℝ) else 1) * f b = f b - (if a = b then f b else 0) := by
    intro b; by_cases hb : a = b <;> simp [hb]
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ a)]

/-! ## The normalized survivor operator and its spectrum (§15) -/

/-- The normalized survivor operator `T_p = (J − I)/q`, `q = card κ`. -/
noncomputable def survivorOp {κ : Type*} [Fintype κ] (f : κ → ℝ) : κ → ℝ :=
  fun n => (1 / (Fintype.card κ : ℝ)) * ((∑ m, f m) - f n)

theorem survivorOp_eq_kernel {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ℝ) (a : κ) :
    survivorOp f a = (1 / (Fintype.card κ : ℝ)) * ∑ b, survivorKernel a b * f b := by
  rw [survivorKernel_apply]; rfl

/-- **Constants eigenvalue (§15).** `T_p 𝟙 = ((q−1)/q) 𝟙` — for `q = p−1` this is `(p−2)/(p−1)`. -/
theorem survivorOp_const {κ : Type*} [Fintype κ] (hq : 0 < Fintype.card κ) (c : ℝ) :
    survivorOp (fun _ : κ => c)
      = fun _ => (((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ)) * c := by
  have hq0 : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  funext n
  unfold survivorOp
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Mean-zero eigenvalue (§15).** `T_p f = (−1/q) f` on `Σf = 0` — for `q = p−1` this is
    `−1/(p−1)` (multiplicity `p − 2`), the parity eigenvalue. -/
theorem survivorOp_meanzero {κ : Type*} [Fintype κ] (f : κ → ℝ) (hf : ∑ m, f m = 0) :
    survivorOp f = fun n => (-1 / (Fintype.card κ : ℝ)) * f n := by
  funext n
  unfold survivorOp
  rw [hf]
  ring

/-! ## The centered survivor operator and the fixed-point eigenvalue (§16) -/

/-- The centered survivor operator with probabilistic normalization: kernel `(J − qI)/(q(q−1))`. -/
noncomputable def centeredSurvivorOp {κ : Type*} [Fintype κ] (f : κ → ℝ) : κ → ℝ :=
  fun n => (1 / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1)))
    * ((∑ m, f m) - (Fintype.card κ : ℝ) * f n)

/-- **Fixed-point parity eigenvalue (§16).** On `Σf = 0` the centered survivor operator acts as
    `−1/(q−1)` — for `q = p−1` this is `−1/(p−2)`, the eigenvalue reproduced by every even moment. -/
theorem centeredSurvivorOp_meanzero {κ : Type*} [Fintype κ] (hq : 1 < Fintype.card κ)
    (f : κ → ℝ) (hf : ∑ m, f m = 0) :
    centeredSurvivorOp f = fun n => (-1 / ((Fintype.card κ : ℝ) - 1)) * f n := by
  have hq0 : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq1 : (Fintype.card κ : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hq
    linarith
  funext n
  unfold centeredSurvivorOp
  rw [hf]
  field_simp
  ring

/-- **Constants are killed (§16).** The centered survivor operator annihilates constants. -/
theorem centeredSurvivorOp_const {κ : Type*} [Fintype κ] (c : ℝ) :
    centeredSurvivorOp (fun _ : κ => c) = fun _ => 0 := by
  funext n
  unfold centeredSurvivorOp
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ## zEnergy as Schatten energy (§17) -/

/-- **Schatten form of zEnergy (§17).** The residual operator `Z_p` has nonzero singular value
    `1/(p−1)` with multiplicity `p − 2`, so `Tr|Z_p|^{2k} = (p−2)(1/(p−1))^{2k} = zEnergy k p`. -/
theorem zEnergy_eq_schatten {p : ℕ} (k : ℕ) :
    zEnergy k p = ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1)) ^ (2 * k) := by
  unfold zEnergy
  rw [div_pow, one_pow, mul_one_div]

end TypeII
end Geometric
end EuclidsPath
