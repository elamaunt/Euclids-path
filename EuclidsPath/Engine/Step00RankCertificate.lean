import Mathlib

/-!
# Step00 rank certificates — det-free integer rank pinning and the homology-dimension bridge

`Matrix.rank` over a field is noncomputable (it is the `finrank` of the range of `mulVecLin`),
so it cannot be checked by `decide`.  This file replaces determinant-minor computations with a
**det-free certificate**: an integer matrix `M` has rank exactly `r` as soon as one exhibits

* a factorization `M = colFac * rowFac` through `r` columns (upper bound), and
* a pseudo-inverse pair `leftInv * M * rightInv = 1` on `r` coordinates (lower bound).

Both certificate equations are decidable data over `ℤ`, so a `decide`-checked certificate pins
`(M.map Int.cast).rank = r` over **every** field `F` simultaneously (`IntRankCert.rank_eq`) —
the ring hom `ℤ → F` transports both matrix equations, and rank inequalities squeeze.

The second half is the meaning layer for gain-complex Betti certificates: for a two-step complex
`D1 * D2 = 0` of matrices over a field, `homologySpace D1 D2 = ker D1 / im D2` has
`finrank = e - rank D1 - rank D2` (`finrank_homologySpace`), and the Euler alternating-sum
consistency `b0 - b1 + b2 = v - e + f` is recorded as pure arithmetic glue (`betti_euler`).

**Disclosed blind spot**: everything here is over fields, so `ℤ`-torsion in integral homology is
invisible to these certificates; they pin Betti numbers (dimensions over `ℚ` and every `F`),
not integral homology groups.

Self-contained over mathlib: no Engine imports, no new axioms, no `native_decide`.
-/

set_option autoImplicit false

namespace EuclidsPath
namespace RankCertificate

/-! ## The certificate -/

/-- Det-free rank certificate for an integer matrix: a factorization bounds the rank above,
    a pseudo-inverse pair bounds it below.  All fields are decidable data over ℤ. -/
structure IntRankCert {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (r : ℕ) where
  /-- Left factor of the width-`r` factorization (upper bound witness). -/
  colFac : Matrix (Fin a) (Fin r) ℤ
  /-- Right factor of the width-`r` factorization (upper bound witness). -/
  rowFac : Matrix (Fin r) (Fin b) ℤ
  /-- The factorization equation `M = colFac * rowFac`. -/
  factor : M = colFac * rowFac
  /-- Left pseudo-inverse (lower bound witness). -/
  leftInv : Matrix (Fin r) (Fin a) ℤ
  /-- Right pseudo-inverse (lower bound witness). -/
  rightInv : Matrix (Fin b) (Fin r) ℤ
  /-- The pseudo-inverse equation: compressing `M` by the pair yields the `r × r` identity. -/
  isOne : leftInv * M * rightInv = 1

/-! ## The bridge: a certificate pins the rank over every field -/

/-- A det-free integer certificate pins the rank of `M` over **every** field `F` at once:
    the factorization caps the rank at `r`, the pseudo-inverse pair forces it up to `r`. -/
theorem IntRankCert.rank_eq {F : Type*} [Field F] {a b r : ℕ}
    {M : Matrix (Fin a) (Fin b) ℤ} (c : IntRankCert M r) :
    (M.map (Int.cast : ℤ → F)).rank = r := by
  -- switch to the bundled ring hom (definitionally equal coercion) so that
  -- `Matrix.map_mul` / `Matrix.map_one` rewrite syntactically
  show (M.map ⇑(Int.castRingHom F)).rank = r
  -- transport the factorization equation along ℤ → F
  have hfac := congrArg (Matrix.map · ⇑(Int.castRingHom F)) c.factor
  rw [Matrix.map_mul] at hfac
  -- transport the pseudo-inverse equation along ℤ → F
  have hone := congrArg (Matrix.map · ⇑(Int.castRingHom F)) c.isOne
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.map_one _ (by simp) (by simp)] at hone
  refine le_antisymm ?_ ?_
  · -- upper bound through the factorization
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · -- lower bound through the pseudo-inverse pair
    calc r = (1 : Matrix (Fin r) (Fin r) F).rank := by simp
      _ = (c.leftInv.map ⇑(Int.castRingHom F) * M.map ⇑(Int.castRingHom F) *
            c.rightInv.map ⇑(Int.castRingHom F)).rank := by rw [hone]
      _ ≤ (c.leftInv.map ⇑(Int.castRingHom F) * M.map ⇑(Int.castRingHom F)).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ (M.map ⇑(Int.castRingHom F)).rank := Matrix.rank_mul_le_right _ _

/-! ## The homology-dimension bridge -/

/-- Middle homology of the two-step complex `(Fin f → F) --D2--> (Fin e → F) --D1--> (Fin v → F)`:
    the kernel of `D1` modulo the image of `D2` (the image is pulled back into the kernel via
    `comap` of the kernel's inclusion; when `D1 * D2 = 0` this pullback is all of the image). -/
noncomputable def homologySpace {F : Type*} [Field F] {v e f : ℕ}
    (D1 : Matrix (Fin v) (Fin e) F) (D2 : Matrix (Fin e) (Fin f) F) : Type _ :=
  LinearMap.ker D1.mulVecLin ⧸
    (LinearMap.range D2.mulVecLin).comap (LinearMap.ker D1.mulVecLin).subtype

noncomputable instance {F : Type*} [Field F] {v e f : ℕ}
    (D1 : Matrix (Fin v) (Fin e) F) (D2 : Matrix (Fin e) (Fin f) F) :
    AddCommGroup (homologySpace D1 D2) :=
  inferInstanceAs (AddCommGroup (LinearMap.ker D1.mulVecLin ⧸
    (LinearMap.range D2.mulVecLin).comap (LinearMap.ker D1.mulVecLin).subtype))

noncomputable instance {F : Type*} [Field F] {v e f : ℕ}
    (D1 : Matrix (Fin v) (Fin e) F) (D2 : Matrix (Fin e) (Fin f) F) :
    Module F (homologySpace D1 D2) :=
  inferInstanceAs (Module F (LinearMap.ker D1.mulVecLin ⧸
    (LinearMap.range D2.mulVecLin).comap (LinearMap.ker D1.mulVecLin).subtype))

/-- Dimension of the middle homology from the two ranks: for a complex `D1 * D2 = 0`,
    `dim H = e - rank D1 - rank D2`.  Combined with `IntRankCert.rank_eq`, two integer
    certificates pin the middle Betti number over every field. -/
theorem finrank_homologySpace {F : Type*} [Field F] {v e f : ℕ}
    (D1 : Matrix (Fin v) (Fin e) F) (D2 : Matrix (Fin e) (Fin f) F)
    (hcx : D1 * D2 = 0) {r1 r2 : ℕ} (h1 : D1.rank = r1) (h2 : D2.rank = r2) :
    Module.finrank F (homologySpace D1 D2) = e - r1 - r2 := by
  classical
  -- the complex condition puts the image of D2 inside the kernel of D1
  have hle : LinearMap.range D2.mulVecLin ≤ LinearMap.ker D1.mulVecLin := by
    rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, hcx, Matrix.mulVecLin_zero]
  -- the pulled-back image has the dimension of the image, i.e. rank D2
  have hsub : Module.finrank F
      ((LinearMap.range D2.mulVecLin).comap (LinearMap.ker D1.mulVecLin).subtype) = r2 := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)]
    exact h2
  -- rank-nullity for D1: rank D1 + dim ker D1 = e
  have hr1 : Module.finrank F (LinearMap.range D1.mulVecLin) = r1 := h1
  have hker := LinearMap.finrank_range_add_finrank_ker D1.mulVecLin
  rw [Module.finrank_pi F, Fintype.card_fin, hr1] at hker
  -- rank-nullity for the quotient: dim H + dim (im D2) = dim ker D1
  have hquot := Submodule.finrank_quotient_add_finrank
    ((LinearMap.range D2.mulVecLin).comap (LinearMap.ker D1.mulVecLin).subtype)
  rw [hsub] at hquot
  have hgoal : Module.finrank F (homologySpace D1 D2) =
      Module.finrank F (LinearMap.ker D1.mulVecLin ⧸
        (LinearMap.range D2.mulVecLin).comap (LinearMap.ker D1.mulVecLin).subtype) := rfl
  rw [hgoal]
  omega

/-! ## Euler consistency -/

set_option linter.unusedVariables false in
/-- Euler alternating-sum consistency for the Betti numbers produced by rank certificates.
    This is pure arithmetic glue: given the standard dimension formulas `b0 = v - r1`
    (here `b0` is read as the cokernel dimension of `D1`, i.e. `dim coker D1 = v - rank D1`),
    `b1 = e - r1 - r2` and `b2 = f - r2`, plus the rank bounds that make the natural
    subtractions honest, the alternating sum of Betti numbers equals the Euler characteristic
    `v - e + f` of the underlying complex.  The complex data `D1`, `D2`, `hcx`, `h1`, `h2`
    is carried in the signature to tie the identity to the complex layer. -/
theorem betti_euler {F : Type*} [Field F] {v e f : ℕ}
    (D1 : Matrix (Fin v) (Fin e) F) (D2 : Matrix (Fin e) (Fin f) F)
    (hcx : D1 * D2 = 0) {r1 r2 : ℕ} (h1 : D1.rank = r1) (h2 : D2.rank = r2)
    (b0 b1 b2 : ℕ) (hb0 : b0 = v - r1) (hb1 : b1 = e - r1 - r2) (hb2 : b2 = f - r2)
    (hle1 : r1 ≤ v) (hle2 : r1 + r2 ≤ e) (hle3 : r2 ≤ f) :
    (b0 : ℤ) - b1 + b2 = (v : ℤ) - e + f := by
  subst hb0 hb1 hb2
  omega

/-! ## Worked instance: the machinery bites -/

namespace DemoRankOne

/-- A concrete 2 × 3 integer matrix of rank 1 (second row is twice the first). -/
def M : Matrix (Fin 2) (Fin 3) ℤ := !![1, 2, 3; 2, 4, 6]

/-- Explicit det-free certificate: `M` factors through one column, and the pseudo-inverse
    pair extracts a 1 × 1 identity.  Both equations are checked by `decide` over ℤ. -/
def cert : IntRankCert M 1 where
  colFac := !![1; 2]
  rowFac := !![1, 2, 3]
  factor := by decide
  leftInv := !![1, 0]
  rightInv := !![1; 0; 0]
  isOne := by decide

/-- The certificate pins the rank of `M` over ℚ (and over any other field alike). -/
example : (M.map (Int.cast : ℤ → ℚ)).rank = 1 := cert.rank_eq

end DemoRankOne

end RankCertificate
end EuclidsPath

/-
Axiom audit (checked via `lake env lean` on a scratch file, then removed):

  #print axioms EuclidsPath.RankCertificate.IntRankCert.rank_eq
    --> [propext, Classical.choice, Quot.sound]
  #print axioms EuclidsPath.RankCertificate.finrank_homologySpace
    --> [propext, Classical.choice, Quot.sound]
  #print axioms EuclidsPath.RankCertificate.betti_euler
    --> [propext, Classical.choice, Quot.sound]
  #print axioms EuclidsPath.RankCertificate.DemoRankOne.cert
    --> [propext, Classical.choice, Quot.sound]
  #print axioms EuclidsPath.RankCertificate.DemoRankOne.M
    --> [propext, Quot.sound]

No `sorryAx`, no `Lean.ofReduceBool` (native_decide), no repo-specific axioms.
-/
