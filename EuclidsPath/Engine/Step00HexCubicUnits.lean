/-
  Step00HexCubicUnits — the hexagonal units of a twin pair, the rigid Eisenstein
  (mod-3) split of the wings, the hand-rolled cubic algebra t³ = −2, and the cubic
  sphere volumes on both mod-3 branches.

  READING.  The twin center `c = 6m` is divisible by 6, so BOTH circles of a twin
  pair carry a hexagonal unit — an order-6 rotation whose cube is the half-turn −1:
  really on the right wing's unit line, imaginarily on the left wing's norm-one
  circle (H1).  The mod-3 residues of the wings are FIXED (right ≡ 1, left ≡ 2 —
  no analogue of the mod-4 parity swing): the right wing always carries rational
  cube roots of unity, the left wing never does (H2 — the rigid Eisenstein split).
  Pushing one degree higher, the cubic algebra `Cub p = ZMod p[t]/(t³ + 2)` (H3)
  carries the norm form `x³ − 2y³ + 4z³ + 6xyz`, and its norm-one CUBIC SPHERE has
  exactly the volumes the mod-3 split dictates: on the 2-mod-3 branch (every left
  wing) the volume is (p−1)(p+1) — THE CUBIC SPHERE WELDS BOTH CIRCLES (H4); on
  the 1-mod-3 branch (every right wing) the volume splits by the root count of
  t³ = −2 into (p−1)² (split) vs p² + p + 1 (inert) — the split face is proved
  here, the inert face is kernel-pinned and harness-measured (H5, scope disclosed).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `hex_unit_real` / `hex_unit_imaginary` — H1: a twin center yields an order-6
      unit with cube −1 on the right wing's REAL circle and an order-6 norm-one
      point with cube −1 on the left wing's IMAGINARY circle (both from the
      order-c rotations of `Step00ImaginaryCircle`, taking m-th powers; the cube
      is the UNIQUE involution −1 via the domain);
    * `right_wing_mod3` / `left_wing_mod3` — the frame: (6m+1) % 3 = 1 and
      (6m−1) % 3 = 2, ALL m ≥ 1 (TRIVIALITY LABEL: 6 ∣ c is definitional;
      pure congruence arithmetic, no primality);
    * `cube_roots_rational_iff` — the dress: a prime q > 3 has a nontrivial cube
      root of unity iff q ≡ 1 (mod 3) (order-3 element of the cyclic unit group);
    * `twin_wings_eisenstein` — the rigid split: in EVERY twin pair the right wing
      has rational cube roots of unity and the left wing does not — the mod-3
      mirror of the mod-4 split, with the side FIXED instead of m-parity-swung;
    * `Cub p`, `cubNorm`, `cubNorm_mul` — H3: the hand-rolled commutative ring
      `ZMod p[t]/(t³ + 2)` on explicit triples (the `Quad` precedent, one degree
      up), with the multiplicative norm form `x³ − 2y³ + 4z³ + 6xyz` (sign
      convention cross-checked numerically before proving: N(1 + t) = −1,
      (1+t)² = 1 + 2t + t², N(1+2t+t²) = 1 − 16 + 4 + 12 = 1 = (−1)²);
    * `cube_bijective_units`, `unique_cube_root_neg_two` — H4 (2-mod-3 branch):
      the cube map is a bijection on units (`powCoprime`, gcd(3, p−1) = 1), so
      t³ = −2 has exactly one rational root;
    * `cubic_sphere_card_two_mod_three` — H4 VOLUME: on the 2-mod-3 branch the
      cubic sphere has volume (p−1)(p+1) — THE CUBIC SPHERE WELDS BOTH CIRCLES.
      Route: the explicit split coordinates (evaluation at the rational root +
      reduction mod the quadratic cofactor) turn the norm form into
      `A · (u² − s·uw + s²w²)` with the quadratic factor ANISOTROPIC
      (−3 is a nonsquare on this branch), so the sphere is a graph over the
      punctured plane: p² − 1 points;
    * `cube_root_count_dichotomy` — H5: on the 1-mod-3 branch the root count of
      t³ = −2 is 0 or 3 (translate the root set by one root onto the cube roots
      of unity; exactly 3 of those, sandwiched by `Polynomial.card_nthRoots`);
    * `cubic_sphere_card_split` — H5 SPLIT FACE: root count 3 ⟹ volume (p−1)²
      (Vieta from three distinct roots, the symmetric-function factorization
      `N = ∏ (x + sᵢy + sᵢ²z)`, a Vandermonde bijection, and the count
      #{A·B·C = 1} = (p−1)²);
    * `twin_right_wing_split_volume` + `twin_cubic_volume_dress` — the twin dress:
      the right wing q = c + 1 carries the conditional volumes {c², c² + 3c + 3};
    * kernel demos (pure-ℕ folds, decide; `Cub`/`ZMod` instances stay OUT of every
      decide path): `cubCountN 5 = 24` (2-mod-3 weld, = 4·6), `rootCountN 7 = 0`
      and `cubCountN 7 = 57` (INERT witness: cubes mod 7 are {1, 6}, −2 ≡ 5 is
      not a cube — the design sketch's guess that 7 might split was WRONG,
      corrected numerically before formalization), `rootCountN 13 = 0` and
      `cubCountN 13 = 183` (second inert witness), `rootCountN 31 = 3` and
      `cubCountN 31 = 900 = 30²` (the SMALLEST split witness — p = 31, found
      numerically; 7, 13, 19 are all inert).

  DISCLOSURES (mandatory reading before quoting):
    * INERT FACE SCOPED OUT.  The general inert count (root count 0 ⟹ volume
      p² + p + 1) is NOT proved in this module: the elementary fiber-count route
      that settles the other two branches does not reach it — it needs the norm's
      surjectivity on the degree-3 extension (finite-field norm theory absent
      from the pin's cheap reach, or ~300 lines of unit-group plumbing).  The
      inert face is kernel-pinned at p = 7 and p = 13 and measured by the harness
      volume-trichotomy observable (tools/sphere_trace_run1.log, stage s6).
    * a² + 3b² FACES SKIPPED.  The classical representation dress of the mod-3
      split (q = a² + 3b² ⟺ q ≡ 1 mod 3) is absent from the pinned mathlib and
      NOT formalized; the deeper a² + 27b² face (2 a cubic residue) is
      HARNESS-ONLY — cubic reciprocity is absent from the pin, disclosed; the
      harness runs a hard Cornacchia selftest on every population prime instead.
    * POINTWISE / FRAME SHAPE.  H1 is a pointwise consequence of twinness; H2 is
      congruence arithmetic dressed by primality.  Nothing here feeds the
      serial-twin wall; no density, no infinitude, no progress on twin primes is
      claimed or implied.
    * KERNEL COUNTER AGREEMENT, NOT EQUALITY.  `cubCountN` and the Finset volume
      are shown to AGREE on demo instances through the abstract theorems; the
      general counting bijection between the ℕ-fold and the `Cub` filter is not
      formalized (`cubCountN_point_sound` is the one-directional bridge, house
      kernel discipline).

  ## Anti-vocabulary

  No claim in this file concerns windows, densities, asymptotics, or the
  infinitude of anything.  "Volume" = cardinality of a finite norm-one set;
  "sphere" = that set; every kernel demo is a single verified instance.
-/
import Mathlib
import EuclidsPath.Engine.Step00ImaginaryCircle

set_option autoImplicit false
set_option maxRecDepth 4000

namespace EuclidsPath
namespace HexCubicUnits

open EuclidsPath.Residuals
open EuclidsPath.ImaginaryCircle
open QuadraticAlgebra

/-! ### Layer 1 — H1: the hexagonal units of a twin pair

The twin center `c = 6m` is divisible by 6 (TRIVIALITY LABEL: definitional), so the
order-c rotations of `Step00ImaginaryCircle` yield order-6 elements by taking m-th
powers; the cube of an order-6 element is the unique involution −1. -/

/-- The norm is multiplicative on powers (`qnorm_eq_norm` + `map_pow`). -/
theorem qnorm_pow {d n : ℕ} (x : Quad d n) (k : ℕ) :
    qnorm (x ^ k) = qnorm x ^ k := by
  rw [qnorm_eq_norm, qnorm_eq_norm, map_pow]

/-- **H1, real face**: a twin center yields an order-6 unit with cube −1 on the
    right wing's REAL circle: the hexagonal unit `a = g^m` for an order-6m
    rotation `g` (from `twin_real_rotation`); its cube is an involution ≠ 1,
    hence −1 (the field has a unique half-turn).
    TRIVIALITY LABEL: `6 ∣ c` is definitional for the twin center `c = 6m`;
    the only arithmetic content is the order bookkeeping. -/
theorem hex_unit_real {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    ∃ a : (ZMod (6 * m + 1))ˣ, orderOf a = 6 ∧ a ^ 3 = -1 := by
  haveI : Fact (6 * m + 1).Prime := ⟨h.2⟩
  obtain ⟨g, hg⟩ := twin_real_rotation hm h
  have hdiv : 6 * m / Nat.gcd (6 * m) m = 6 := by
    rw [Nat.gcd_eq_right ⟨6, by ring⟩, Nat.mul_comm]
    exact Nat.mul_div_cancel_left 6 (by omega)
  have hord : orderOf (g ^ m) = 6 := by
    rw [orderOf_pow' g (by omega : m ≠ 0), hg]
    exact hdiv
  have h6 : (g ^ m) ^ 6 = 1 := by
    have hp := pow_orderOf_eq_one (g ^ m)
    rwa [hord] at hp
  have h3ne : (g ^ m) ^ 3 ≠ 1 := by
    intro hc
    have hdvd := orderOf_dvd_of_pow_eq_one hc
    rw [hord] at hdvd
    omega
  have hsq : ((g ^ m) ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, show 3 * 2 = 6 from rfl]
    exact h6
  have hv : ((((g ^ m) ^ 3 : (ZMod (6 * m + 1))ˣ)) : ZMod (6 * m + 1)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have hfac : (((((g ^ m) ^ 3 : (ZMod (6 * m + 1))ˣ)) : ZMod (6 * m + 1)) - 1)
      * (((((g ^ m) ^ 3 : (ZMod (6 * m + 1))ˣ)) : ZMod (6 * m + 1)) + 1) = 0 := by
    linear_combination hv
  rcases mul_eq_zero.mp hfac with h1 | hneg
  · exfalso
    exact h3ne (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h1))
  · refine ⟨g ^ m, hord, Units.ext ?_⟩
    rw [Units.val_neg, Units.val_one]
    exact eq_neg_of_add_eq_zero_left hneg

/-- **H1, imaginary face**: the same center gives an order-6 norm-one point with
    cube −1 on the left wing's IMAGINARY circle (from `twin_imaginary_rotation`;
    the involution is pinned to −1 by `circle_involution` — the Wilson bottom). -/
theorem hex_unit_imaginary {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    ∃ d : ℕ, ¬ IsSquare ((d : ZMod (6 * m - 1))) ∧
      ∃ α : Quad d (6 * m - 1), qnorm α = 1 ∧ orderOf α = 6 ∧ α ^ 3 = -1 := by
  haveI : Fact (6 * m - 1).Prime := ⟨h.1⟩
  obtain ⟨d, hd, α, hqn, hord0⟩ := twin_imaginary_rotation hm h
  have hdiv : 6 * m / Nat.gcd (6 * m) m = 6 := by
    rw [Nat.gcd_eq_right ⟨6, by ring⟩, Nat.mul_comm]
    exact Nat.mul_div_cancel_left 6 (by omega)
  have hord : orderOf (α ^ m) = 6 := by
    rw [orderOf_pow' α (by omega : m ≠ 0), hord0]
    exact hdiv
  have h6 : (α ^ m) ^ 6 = 1 := by
    have hp := pow_orderOf_eq_one (α ^ m)
    rwa [hord] at hp
  have h3ne : (α ^ m) ^ 3 ≠ 1 := by
    intro hc
    have hdvd := orderOf_dvd_of_pow_eq_one hc
    rw [hord] at hdvd
    omega
  have hsq : ((α ^ m) ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, show 3 * 2 = 6 from rfl]
    exact h6
  refine ⟨d, hd, α ^ m, by rw [qnorm_pow, hqn, one_pow], hord, ?_⟩
  rcases circle_involution hd hsq with h1 | hneg
  · exact absurd h1 h3ne
  · exact hneg

/-! ### Layer 2 — H2: the rigid Eisenstein split of the wings

TRIVIALITY LABEL: the mod-3 residues are congruence arithmetic valid for ALL m ≥ 1
— `6 ∣ c` is definitional.  Primality only enters the dress (rational cube roots
of unity), where the side is FIXED: right always splits, left always inert — the
mod-3 mirror of the mod-4 split WITHOUT the m-parity swing.
DISCLOSURE: the representation faces `q = a² + 3b²` and `q = a² + 27b²` are absent
from the pinned mathlib and not formalized (harness-only, stage s6). -/

/-- Right wing frame: `(6m+1) % 3 = 1` for all `m`. -/
theorem right_wing_mod3 (m : ℕ) : (6 * m + 1) % 3 = 1 := by omega

/-- Left wing frame: `(6m−1) % 3 = 2` for all `m ≥ 1`. -/
theorem left_wing_mod3 {m : ℕ} (hm : 1 ≤ m) : (6 * m - 1) % 3 = 2 := by omega

/-- **The Eisenstein dress**: a prime `q > 3` carries a nontrivial rational cube
    root of unity iff `q ≡ 1 (mod 3)` — an order-3 element exists in the cyclic
    unit group iff `3 ∣ q − 1` (cyclic counting via
    `exists_prime_orderOf_dvd_card`). -/
theorem cube_roots_rational_iff {q : ℕ} [Fact q.Prime] (h3 : 3 < q) :
    (∃ x : ZMod q, x ≠ 1 ∧ x ^ 3 = 1) ↔ q % 3 = 1 := by
  constructor
  · rintro ⟨x, hx1, hx3⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at hx3
      simp at hx3
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx0
    have hu3 : hu.unit ^ 3 = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
      exact hx3
    have hdvd : orderOf hu.unit ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have hne1 : orderOf hu.unit ≠ 1 := by
      intro h1
      have := orderOf_eq_one_iff.mp h1
      rw [Units.ext_iff, IsUnit.unit_spec, Units.val_one] at this
      exact hx1 this
    have hord : orderOf hu.unit = 3 := by
      rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hcard : orderOf hu.unit ∣ q - 1 := by
      have := orderOf_dvd_card (x := hu.unit)
      rwa [ZMod.card_units] at this
    rw [hord] at hcard
    omega
  · intro hq
    have hdvd : 3 ∣ Fintype.card (ZMod q)ˣ := by
      rw [ZMod.card_units]
      omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdvd
    refine ⟨(u : ZMod q), ?_, ?_⟩
    · intro h1
      have : u = 1 := Units.ext (by rw [Units.val_one]; exact h1)
      rw [this, orderOf_one] at hu
      omega
    · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]

/-- **The rigid Eisenstein split**: in EVERY twin pair the RIGHT wing carries
    rational cube roots of unity and the LEFT wing does not.  The mod-3 mirror of
    the mod-4 split (`twin_wings_sqrt_neg_one`), with the side FIXED instead of
    swinging with the parity of `m`. -/
theorem twin_wings_eisenstein {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    (∃ x : ZMod (6 * m + 1), x ≠ 1 ∧ x ^ 3 = 1) ∧
      ¬ (∃ x : ZMod (6 * m - 1), x ≠ 1 ∧ x ^ 3 = 1) := by
  haveI : Fact (6 * m + 1).Prime := ⟨h.2⟩
  haveI : Fact (6 * m - 1).Prime := ⟨h.1⟩
  have hL5 : 3 < 6 * m - 1 := by omega
  constructor
  · exact (cube_roots_rational_iff (by omega)).mpr (right_wing_mod3 m)
  · intro hx
    have := (cube_roots_rational_iff hL5).mp hx
    have := left_wing_mod3 hm
    omega

/-! ### Layer 3 — H3: the cubic algebra `Cub p = ZMod p[t]/(t³ + 2)`

Hand-rolled on explicit triples (the `Quad` precedent one degree up — the pinned
mathlib has no cubic analogue of `QuadraticAlgebra`); instance pattern copied from
mathlib's `Zsqrtd`.  The norm form is `N(x + yt + zt²) = x³ − 2y³ + 4z³ + 6xyz`
(the determinant of multiplication-by-v; sign convention CROSS-CHECKED numerically
before proving: `N(1 + t) = 1 − 2 = −1`, `(1+t)² = 1 + 2t + t²`,
`N(1 + 2t + t²) = 1 − 16 + 4 + 12 = 1 = (−1)²`  ✓). -/

/-- The cubic ring `ZMod p[t]/(t³ + 2)`: triples `(x, y, z) = x + y·t + z·t²`. -/
@[ext]
structure Cub (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p
deriving DecidableEq

namespace Cub

variable {p : ℕ}

instance : Zero (Cub p) := ⟨⟨0, 0, 0⟩⟩
instance : One (Cub p) := ⟨⟨1, 0, 0⟩⟩
instance : Add (Cub p) := ⟨fun v w => ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩⟩
instance : Neg (Cub p) := ⟨fun v => ⟨-v.x, -v.y, -v.z⟩⟩

/-- Multiplication with `t³ = −2` (hence `t⁴ = −2t`): collecting coefficients of
    `1, t, t²` in `(x₁ + y₁t + z₁t²)(x₂ + y₂t + z₂t²)`. -/
instance : Mul (Cub p) :=
  ⟨fun v w => ⟨v.x * w.x - 2 * (v.y * w.z + v.z * w.y),
               v.x * w.y + v.y * w.x - 2 * (v.z * w.z),
               v.x * w.z + v.y * w.y + v.z * w.x⟩⟩

@[simp] theorem x_zero : (0 : Cub p).x = 0 := rfl
@[simp] theorem y_zero : (0 : Cub p).y = 0 := rfl
@[simp] theorem z_zero : (0 : Cub p).z = 0 := rfl
@[simp] theorem x_one : (1 : Cub p).x = 1 := rfl
@[simp] theorem y_one : (1 : Cub p).y = 0 := rfl
@[simp] theorem z_one : (1 : Cub p).z = 0 := rfl
@[simp] theorem x_add (v w : Cub p) : (v + w).x = v.x + w.x := rfl
@[simp] theorem y_add (v w : Cub p) : (v + w).y = v.y + w.y := rfl
@[simp] theorem z_add (v w : Cub p) : (v + w).z = v.z + w.z := rfl
@[simp] theorem x_neg (v : Cub p) : (-v).x = -v.x := rfl
@[simp] theorem y_neg (v : Cub p) : (-v).y = -v.y := rfl
@[simp] theorem z_neg (v : Cub p) : (-v).z = -v.z := rfl
@[simp] theorem x_mul (v w : Cub p) :
    (v * w).x = v.x * w.x - 2 * (v.y * w.z + v.z * w.y) := rfl
@[simp] theorem y_mul (v w : Cub p) :
    (v * w).y = v.x * w.y + v.y * w.x - 2 * (v.z * w.z) := rfl
@[simp] theorem z_mul (v w : Cub p) :
    (v * w).z = v.x * w.z + v.y * w.y + v.z * w.x := rfl

instance addCommGroup : AddCommGroup (Cub p) := by
  refine
  { sub := fun v w => v + -w
    nsmul := @nsmulRec (Cub p) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (Cub p) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (Cub p) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;> ext <;> simp [add_comm, add_left_comm]

instance commRing : CommRing (Cub p) := by
  refine
  { Cub.addCommGroup with
    npow := @npowRec (Cub p) ⟨1⟩ ⟨(· * ·)⟩
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

/-- The coordinate equivalence with the plain triple product (drives `Fintype`). -/
def equivTriple (p : ℕ) : Cub p ≃ ZMod p × ZMod p × ZMod p where
  toFun v := (v.x, v.y, v.z)
  invFun w := ⟨w.1, w.2.1, w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeCub (p : ℕ) [NeZero p] : Fintype (Cub p) :=
  Fintype.ofEquiv _ (equivTriple p).symm

theorem card_cub (p : ℕ) [NeZero p] : Fintype.card (Cub p) = p ^ 3 := by
  rw [Fintype.card_congr (equivTriple p), Fintype.card_prod, Fintype.card_prod,
    ZMod.card]
  ring

end Cub

/-- The generator `t` of the cubic algebra. -/
def tCub (p : ℕ) : Cub p := ⟨0, 1, 0⟩

/-- `t³ = −2` in coordinates — the defining relation, verified from the hand-rolled
    multiplication. -/
theorem tCub_cubed (p : ℕ) : (tCub p) ^ 3 = (⟨-2, 0, 0⟩ : Cub p) := by
  rw [pow_succ, pow_succ, pow_one]
  ext <;> simp [tCub]

/-- **The cubic norm form** `N(x + yt + zt²) = x³ − 2y³ + 4z³ + 6xyz` — the
    determinant of multiplication-by-v in the basis `(1, t, t²)`.  The sign
    convention was derived and cross-checked numerically BEFORE proving
    multiplicativity (see the layer header). -/
def cubNorm {p : ℕ} (v : Cub p) : ZMod p :=
  v.x ^ 3 - 2 * v.y ^ 3 + 4 * v.z ^ 3 + 6 * (v.x * v.y * v.z)

@[simp] theorem cubNorm_zero {p : ℕ} : cubNorm (0 : Cub p) = 0 := by
  simp [cubNorm]

@[simp] theorem cubNorm_one {p : ℕ} : cubNorm (1 : Cub p) = 1 := by
  simp [cubNorm]

/-- The norm of the generator: `N(t) = −2` — the seed of the norm's surjectivity
    on the split branch (kept as a plaque; the inert-branch use is scoped out). -/
theorem cubNorm_tCub (p : ℕ) : cubNorm (tCub p) = -2 := by
  simp [cubNorm, tCub]

/-- **Multiplicativity of the cubic norm** — the degree-6 polynomial identity in
    six variables, discharged by `ring` after unfolding the hand-rolled
    multiplication.  Numerically cross-checked symbolically (sympy) before
    formalization. -/
theorem cubNorm_mul {p : ℕ} (v w : Cub p) :
    cubNorm (v * w) = cubNorm v * cubNorm w := by
  simp only [cubNorm, Cub.x_mul, Cub.y_mul, Cub.z_mul]
  ring

/-! ### Layer 4 — H4: the 2-mod-3 branch (every left wing)

`p ≡ 2 (mod 3)`: the cube map is bijective on units, `t³ = −2` has exactly one
rational root `s`, the algebra splits off a rational line, and the quadratic
cofactor is ANISOTROPIC (−3 is a nonsquare on this branch) — so the norm-one
CUBIC SPHERE is a graph over the punctured plane: volume `(p−1)(p+1)`.
**The cubic sphere welds both circles**: the two factors are exactly the real and
the imaginary circle volumes of `p`. -/

private theorem two_ne_zero' {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)

theorem neg_two_ne_zero {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    (-2 : ZMod p) ≠ 0 :=
  neg_ne_zero.mpr (two_ne_zero' h2)

/-- **H4, cube bijectivity**: on the 2-mod-3 branch the cube map is a bijection on
    units — `gcd(3, p − 1) = 1`, so `powCoprime` applies (in its corollary form
    `Nat.Coprime.pow_left_bijective`). -/
theorem cube_bijective_units {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) :
    Function.Bijective (fun u : (ZMod p)ˣ => u ^ 3) := by
  have h1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hcop : (Nat.card (ZMod p)ˣ).Coprime 3 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    have hnd : ¬ (3 ∣ p - 1) := by omega
    exact Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr hnd)
  exact hcop.pow_left_bijective

/-- **H4, the unique root**: `t³ = −2` has exactly one rational root on the
    2-mod-3 branch. -/
theorem unique_cube_root_neg_two {p : ℕ} [Fact p.Prime] (h2 : 2 < p)
    (hp3 : p % 3 = 2) : ∃! s : ZMod p, s ^ 3 = -2 := by
  have hu2 : IsUnit (-2 : ZMod p) := isUnit_iff_ne_zero.mpr (neg_two_ne_zero h2)
  obtain ⟨u, hu⟩ := (cube_bijective_units hp3).surjective hu2.unit
  refine ⟨(u : ZMod p), ?_, ?_⟩
  · have hval := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at hval
    exact hval
  · intro t ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at ht
      exact neg_two_ne_zero h2 ht.symm
    have htu : IsUnit t := isUnit_iff_ne_zero.mpr ht0
    have hpow : htu.unit ^ 3 = hu2.unit := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, IsUnit.unit_spec]
      exact ht
    have hinj := (cube_bijective_units hp3).injective (hpow.trans hu.symm)
    have hval := congrArg Units.val hinj
    rw [IsUnit.unit_spec] at hval
    exact hval

/-- On the 2-mod-3 branch `−3` is a nonsquare: a square root `c` of `−3` would
    manufacture the nontrivial cube root of unity `ω = (−1 + c)/2`, forcing
    `p ≡ 1 (mod 3)` through the Eisenstein dress. -/
theorem not_isSquare_neg_three {p : ℕ} [Fact p.Prime] (h2 : 2 < p)
    (hp3 : p % 3 = 2) : ¬ IsSquare (-3 : ZMod p) := by
  rintro ⟨c, hc⟩
  have hc2 : c ^ 2 = -3 := by rw [pow_two]; exact hc.symm
  have h20 : (2 : ZMod p) ≠ 0 := two_ne_zero' h2
  have h2i : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h20
  set w3 : ZMod p := (-1 + c) * 2⁻¹ with hw3
  have hquad : w3 ^ 2 + w3 + 1 = 0 := by
    rw [hw3]
    linear_combination ((2 : ZMod p)⁻¹) ^ 2 * hc2 +
      (-(2 : ZMod p)⁻¹ * (1 + c) - 1) * h2i
  have hcube : w3 ^ 3 = 1 := by linear_combination (w3 - 1) * hquad
  have hw3ne : w3 ≠ 1 := by
    intro h1
    have hcval : (-1 : ZMod p) + c = 2 := by
      calc (-1 : ZMod p) + c = (-1 + c) * (2 * 2⁻¹) := by rw [h2i, mul_one]
        _ = 2 * ((-1 + c) * 2⁻¹) := by ring
        _ = 2 * w3 := by rw [hw3]
        _ = 2 := by rw [h1, mul_one]
    have h12 : ((12 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hc2 - (c + 3) * hcval
    have hdvd : p ∣ 12 := (ZMod.natCast_eq_zero_iff 12 p).mp h12
    have hple : p ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p <;> omega
  have h3p : 3 < p := by omega
  have := (cube_roots_rational_iff h3p).mp ⟨w3, hw3ne, hcube⟩
  omega

/-- **H4, THE WELD — the cubic sphere volume on the 2-mod-3 branch**:
    `#{v : Cub p | cubNorm v = 1} = (p−1)·(p+1)` for `p ≡ 2 (mod 3)`, `p > 2` —
    the two factors are the REAL and IMAGINARY circle volumes of `p`: the cubic
    sphere welds both circles of the prime, exactly.

    Route (explicit split coordinates, no ring-isomorphism plumbing — design
    choice disclosed): with `s` the unique cube root of `−2`, the norm form
    factors as `N(v) = A(v) · q(u(v), w(v))` where `A = x + sy + s²z` is the
    evaluation at the rational root, `(u, w) = (x − s²z, y − sz)` are the
    reduction coordinates mod the quadratic cofactor, and
    `q(u,w) = u² − s·uw + s²·w²` is ANISOTROPIC (its discriminant is `−3s²`, a
    nonsquare).  The coordinate change is an explicit bijection (inverse via
    `(3s²)⁻¹`), so the sphere is the graph `{A = q(u,w)⁻¹ : (u,w) ≠ 0}` over the
    punctured plane: `p² − 1` points. -/
theorem cubic_sphere_card_two_mod_three {p : ℕ} [Fact p.Prime] (h2 : 2 < p)
    (hp3 : p % 3 = 2) :
    (Finset.univ.filter fun v : Cub p => cubNorm v = 1).card = (p - 1) * (p + 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  obtain ⟨s, hs, -⟩ := unique_cube_root_neg_two h2 hp3
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hs
    exact neg_two_ne_zero h2 hs.symm
  have h30 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have h3' : ((3 : ℕ) : ZMod p) = 0 := by push_cast; exact h0
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3'
    have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h3s2 : (3 * s ^ 2 : ZMod p) ≠ 0 := mul_ne_zero h30 (pow_ne_zero 2 hs0)
  have hns3 := not_isSquare_neg_three h2 hp3
  -- anisotropy of the quadratic cofactor
  have haniso : ∀ u w : ZMod p,
      u ^ 2 - s * u * w + s ^ 2 * w ^ 2 = 0 → u = 0 ∧ w = 0 := by
    intro u w hq
    by_cases hw : w = 0
    · refine ⟨?_, hw⟩
      rw [hw] at hq
      have hu2 : u ^ 2 = 0 := by linear_combination hq
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hu2
    · exfalso
      apply hns3
      have hsw : s * w ≠ 0 := mul_ne_zero hs0 hw
      have hswinv : (s * w) * (s * w)⁻¹ = 1 := mul_inv_cancel₀ hsw
      have hkey : (2 * u - s * w) ^ 2 = -3 * (s * w) ^ 2 := by
        linear_combination 4 * hq
      refine ⟨(2 * u - s * w) * (s * w)⁻¹, ?_⟩
      calc (-3 : ZMod p)
          = -3 * ((s * w) * (s * w)⁻¹) * ((s * w) * (s * w)⁻¹) := by
            rw [hswinv]; ring
        _ = ((2 * u - s * w) * (s * w)⁻¹) * ((2 * u - s * w) * (s * w)⁻¹) := by
            linear_combination (-(((s * w)⁻¹) ^ 2)) * hkey
  -- the master factorization N = A · q(u, w)
  have hmaster : ∀ v : Cub p, cubNorm v
      = (v.x + s * v.y + s ^ 2 * v.z) *
        ((v.x - s ^ 2 * v.z) ^ 2
          - s * (v.x - s ^ 2 * v.z) * (v.y - s * v.z)
          + s ^ 2 * (v.y - s * v.z) ^ 2) := by
    intro v
    simp only [cubNorm]
    linear_combination
      (3 * v.x * v.y * v.z - v.y ^ 3 + 2 * v.z ^ 3 - s ^ 3 * v.z ^ 3) * hs
  -- the split-coordinates bijection onto the graph set
  have hbij : (Finset.univ.filter fun v : Cub p => cubNorm v = 1).card
      = (Finset.univ.filter fun w : ZMod p × ZMod p × ZMod p =>
          w.1 * (w.2.1 ^ 2 - s * w.2.1 * w.2.2 + s ^ 2 * w.2.2 ^ 2) = 1).card := by
    refine Finset.card_bij
      (fun v _ => (v.x + s * v.y + s ^ 2 * v.z, v.x - s ^ 2 * v.z, v.y - s * v.z))
      ?_ ?_ ?_
    · intro v hv
      have hv1 : cubNorm v = 1 := (Finset.mem_filter.mp hv).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (v.x + s * v.y + s ^ 2 * v.z) *
        ((v.x - s ^ 2 * v.z) ^ 2
          - s * (v.x - s ^ 2 * v.z) * (v.y - s * v.z)
          + s ^ 2 * (v.y - s * v.z) ^ 2) = 1
      rw [← hmaster v]
      exact hv1
    · intro v hv v' hv' heq
      have hA := congrArg Prod.fst heq
      have hu := congrArg (fun w : ZMod p × ZMod p × ZMod p => w.2.1) heq
      have hw := congrArg (fun w : ZMod p × ZMod p × ZMod p => w.2.2) heq
      simp only at hA hu hw
      have hz : v.z = v'.z := by
        have hzz : (3 * s ^ 2) * v.z = (3 * s ^ 2) * v'.z := by
          linear_combination hA - hu - s * hw
        exact mul_left_cancel₀ h3s2 hzz
      have hy : v.y = v'.y := by linear_combination hw + s * hz
      have hx : v.x = v'.x := by linear_combination hu + s ^ 2 * hz
      ext <;> assumption
    · intro w hw
      have hw1 : w.1 * (w.2.1 ^ 2 - s * w.2.1 * w.2.2 + s ^ 2 * w.2.2 ^ 2) = 1 :=
        (Finset.mem_filter.mp hw).2
      have h3i : (3 * s ^ 2 : ZMod p) * (3 * s ^ 2)⁻¹ = 1 := mul_inv_cancel₀ h3s2
      set Z : ZMod p := (w.1 - w.2.1 - s * w.2.2) * (3 * s ^ 2)⁻¹ with hZ
      have hA' : (w.2.1 + s ^ 2 * Z) + s * (w.2.2 + s * Z) + s ^ 2 * Z = w.1 := by
        rw [hZ]
        linear_combination (w.1 - w.2.1 - s * w.2.2) * h3i
      have hu' : (w.2.1 + s ^ 2 * Z) - s ^ 2 * Z = w.2.1 := by ring
      have hw' : (w.2.2 + s * Z) - s * Z = w.2.2 := by ring
      refine ⟨⟨w.2.1 + s ^ 2 * Z, w.2.2 + s * Z, Z⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hmaster]
        show ((w.2.1 + s ^ 2 * Z) + s * (w.2.2 + s * Z) + s ^ 2 * Z) *
          (((w.2.1 + s ^ 2 * Z) - s ^ 2 * Z) ^ 2
            - s * ((w.2.1 + s ^ 2 * Z) - s ^ 2 * Z) * ((w.2.2 + s * Z) - s * Z)
            + s ^ 2 * ((w.2.2 + s * Z) - s * Z) ^ 2) = 1
        rw [hA', hu', hw']
        exact hw1
      · show ((w.2.1 + s ^ 2 * Z) + s * (w.2.2 + s * Z) + s ^ 2 * Z,
          (w.2.1 + s ^ 2 * Z) - s ^ 2 * Z, (w.2.2 + s * Z) - s * Z) = w
        rw [hA', hu', hw']
  -- the graph over the punctured plane
  have hgraph : (Finset.univ.filter fun w : ZMod p × ZMod p × ZMod p =>
      w.1 * (w.2.1 ^ 2 - s * w.2.1 * w.2.2 + s ^ 2 * w.2.2 ^ 2) = 1).card
      = (Finset.univ.filter fun u : ZMod p × ZMod p =>
          ¬ (u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2 = 0)).card := by
    refine Finset.card_bij' (fun w _ => w.2)
      (fun u _ => ((u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2)⁻¹, u)) ?_ ?_ ?_ ?_
    · intro w hw
      have hw1 := (Finset.mem_filter.mp hw).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show ¬ (w.2.1 ^ 2 - s * w.2.1 * w.2.2 + s ^ 2 * w.2.2 ^ 2 = 0)
      intro h0
      rw [h0, mul_zero] at hw1
      exact zero_ne_one hw1
    · intro u hu
      have hu1 := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2)⁻¹ *
        (u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2) = 1
      exact inv_mul_cancel₀ hu1
    · intro w hw
      have hw1 := (Finset.mem_filter.mp hw).2
      have hfst : w.1 = (w.2.1 ^ 2 - s * w.2.1 * w.2.2 + s ^ 2 * w.2.2 ^ 2)⁻¹ :=
        eq_inv_of_mul_eq_one_left hw1
      exact Prod.ext hfst.symm rfl
    · intro u _
      rfl
  have hcompl : (Finset.univ.filter fun u : ZMod p × ZMod p =>
      u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2 = 0).card = 1 := by
    have hset : (Finset.univ.filter fun u : ZMod p × ZMod p =>
        u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2 = 0)
        = {((0 : ZMod p), (0 : ZMod p))} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hq
        obtain ⟨h1', h2'⟩ := haniso u.1 u.2 hq
        exact Prod.ext h1' h2'
      · rintro rfl
        ring
    rw [hset, Finset.card_singleton]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod p × ZMod p)))
    (fun u : ZMod p × ZMod p => u.1 ^ 2 - s * u.1 * u.2 + s ^ 2 * u.2 ^ 2 = 0)
  rw [Finset.card_univ, Fintype.card_prod, ZMod.card, hcompl] at htot
  have h1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hexp : (p - 1) * (p + 1) + 1 = p * p := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hbij, hgraph]
  omega

/-! ### Layer 5 — H5: the 1-mod-3 branch (every right wing)

`p ≡ 1 (mod 3)`: the cube map is 3-to-1 on units, so `t³ = −2` has 0 or 3 roots.
The SPLIT face (3 roots ⟹ volume (p−1)², proved) rides the symmetric-function
factorization `N = ∏ (x + sᵢy + sᵢ²z)`; the INERT face (0 roots, volume p²+p+1)
is SCOPED OUT of this module (kernel-pinned at p = 7, 13; harness-measured —
see the module disclosures) . -/

/-- Exactly 3 cube roots of unity on the 1-mod-3 branch: `{1, ω, ω²}` from the
    Eisenstein dress below, `≤ 3` from `Polynomial.card_nthRoots`. -/
theorem cube_roots_one_card {p : ℕ} [Fact p.Prime] (h3 : 3 < p) (hp3 : p % 3 = 1) :
    (Finset.univ.filter fun x : ZMod p => x ^ 3 = 1).card = 3 := by
  obtain ⟨w, hwne, hw3⟩ := (cube_roots_rational_iff h3).mpr hp3
  have hle : (Finset.univ.filter fun x : ZMod p => x ^ 3 = 1).card ≤ 3 := by
    have hsub : (Finset.univ.filter fun x : ZMod p => x ^ 3 = 1)
        ⊆ (Polynomial.nthRoots 3 (1 : ZMod p)).toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num : 0 < 3)]
      exact (Finset.mem_filter.mp hx).2
    calc (Finset.univ.filter fun x : ZMod p => x ^ 3 = 1).card
        ≤ (Polynomial.nthRoots 3 (1 : ZMod p)).toFinset.card :=
          Finset.card_le_card hsub
      _ ≤ Multiset.card (Polynomial.nthRoots 3 (1 : ZMod p)) :=
          Multiset.toFinset_card_le _
      _ ≤ 3 := Polynomial.card_nthRoots 3 1
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hw3
    exact zero_ne_one hw3
  have hwsq1 : w ^ 2 ≠ 1 := by
    intro h1
    have hw' : w = 1 := by
      have h := hw3
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h1, one_mul] at h
      exact h
    exact hwne hw'
  have hwsqw : w ^ 2 ≠ w := by
    intro heq
    have hmul : w * w = w * 1 := by
      rw [mul_one, ← pow_two]
      exact heq
    exact hwne (mul_left_cancel₀ hw0 hmul)
  have hsub3 : ({1, w, w ^ 2} : Finset (ZMod p))
      ⊆ Finset.univ.filter fun x => x ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_pow 3⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw3⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hw3, one_pow]
  have hcard3 : ({1, w, w ^ 2} : Finset (ZMod p)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hwsqw h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hwne h.symm
      · exact hwsq1 h.symm
  have hge := Finset.card_le_card hsub3
  rw [hcard3] at hge
  omega

/-- **H5, the root-count dichotomy**: on the 1-mod-3 branch `t³ = −2` has 0 or 3
    rational roots (translate the root set onto the cube roots of unity). -/
theorem cube_root_count_dichotomy {p : ℕ} [Fact p.Prime] (h3 : 3 < p)
    (hp3 : p % 3 = 1) :
    (Finset.univ.filter fun x : ZMod p => x ^ 3 = -2).card = 0 ∨
      (Finset.univ.filter fun x : ZMod p => x ^ 3 = -2).card = 3 := by
  by_cases hne : (Finset.univ.filter fun x : ZMod p => x ^ 3 = -2).card = 0
  · exact Or.inl hne
  right
  obtain ⟨s0, hs0mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  have hs0 : s0 ^ 3 = -2 := (Finset.mem_filter.mp hs0mem).2
  have h2 : 2 < p := by omega
  have hs00 : s0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hs0
    exact neg_two_ne_zero h2 hs0.symm
  have hbij : (Finset.univ.filter fun x : ZMod p => x ^ 3 = -2).card
      = (Finset.univ.filter fun x : ZMod p => x ^ 3 = 1).card := by
    refine Finset.card_bij' (fun x _ => x * s0⁻¹) (fun y _ => y * s0) ?_ ?_ ?_ ?_
    · intro x hx
      have hx3 : x ^ 3 = -2 := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [mul_pow, hx3, inv_pow, hs0]
      exact mul_inv_cancel₀ (neg_two_ne_zero h2)
    · intro y hy
      have hy3 : y ^ 3 = 1 := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [mul_pow, hy3, hs0, one_mul]
    · intro x _
      rw [mul_assoc, inv_mul_cancel₀ hs00, mul_one]
    · intro y _
      rw [mul_assoc, mul_inv_cancel₀ hs00, mul_one]
  rw [hbij]
  exact cube_roots_one_card h3 hp3

/-- **H5, THE SPLIT FACE**: 3 rational roots of `t³ = −2` ⟹ the cubic sphere has
    volume `(p−1)²`.  Route: Vieta from the three DISTINCT roots (`e₁ = e₂ = 0`,
    `e₃ = −2` — derived, not assumed), the symmetric-function factorization
    `N(v) = ∏ᵢ (x + sᵢy + sᵢ²z)` (cofactors machine-audited numerically before
    formalization), the Vandermonde evaluation bijection (injective by pairwise
    root differences, hence bijective by cardinality), and the elementary count
    `#{(A,B,C) : A·B·C = 1} = (p−1)²`. -/
theorem cubic_sphere_card_split {p : ℕ} [Fact p.Prime] (_h3 : 3 < p)
    (_hp3 : p % 3 = 1)
    (hroots : (Finset.univ.filter fun x : ZMod p => x ^ 3 = -2).card = 3) :
    (Finset.univ.filter fun v : Cub p => cubNorm v = 1).card
      = (p - 1) * (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  obtain ⟨s1, s2, s3, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hroots
  have hmem : ∀ s ∈ ({s1, s2, s3} : Finset (ZMod p)), s ^ 3 = -2 := by
    intro s hs
    have : s ∈ Finset.univ.filter fun x : ZMod p => x ^ 3 = -2 := by
      rw [hset]; exact hs
    exact (Finset.mem_filter.mp this).2
  have hs1 : s1 ^ 3 = -2 := hmem s1 (by simp)
  have hs2 : s2 ^ 3 = -2 := hmem s2 (by simp)
  have hs3 : s3 ^ 3 = -2 := hmem s3 (by simp)
  -- Vieta from distinctness
  have hd12 : s1 ^ 2 + s1 * s2 + s2 ^ 2 = 0 := by
    have hfac : (s1 - s2) * (s1 ^ 2 + s1 * s2 + s2 ^ 2) = 0 := by
      linear_combination hs1 - hs2
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr h12)
  have hd13 : s1 ^ 2 + s1 * s3 + s3 ^ 2 = 0 := by
    have hfac : (s1 - s3) * (s1 ^ 2 + s1 * s3 + s3 ^ 2) = 0 := by
      linear_combination hs1 - hs3
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr h13)
  have hd23 : s2 ^ 2 + s2 * s3 + s3 ^ 2 = 0 := by
    have hfac : (s2 - s3) * (s2 ^ 2 + s2 * s3 + s3 ^ 2) = 0 := by
      linear_combination hs2 - hs3
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr h23)
  have he1 : s1 + s2 + s3 = 0 := by
    have hfac : (s2 - s3) * (s1 + s2 + s3) = 0 := by
      linear_combination hd12 - hd13
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr h23)
  have he2 : s1 * s2 + s1 * s3 + s2 * s3 = 0 := by
    linear_combination (-1 : ZMod p) * hd23 + (s2 + s3) * he1
  have he3 : s1 * s2 * s3 = -2 := by
    linear_combination (-s1) * hd23 + s1 * (s2 + s3 - s1) * he1 + hs1
  -- the symmetric-function factorization (cofactors machine-audited)
  have hmaster : ∀ v : Cub p, cubNorm v
      = (v.x + s1 * v.y + s1 ^ 2 * v.z) * (v.x + s2 * v.y + s2 ^ 2 * v.z)
        * (v.x + s3 * v.y + s3 ^ 2 * v.z) := by
    intro v
    simp only [cubNorm]
    linear_combination
      (-(v.x ^ 2 * v.y + (s1 + s2 + s3) * v.x ^ 2 * v.z
        + (s1 * s2 * s3) * v.y ^ 2 * v.z
        - 2 * (s1 * s2 * s3) * v.x * v.z ^ 2)) * he1
      + (-(- 2 * v.x ^ 2 * v.z + v.x * v.y ^ 2
        + (s1 + s2 + s3) * v.x * v.y * v.z
        + (s1 * s2 + s1 * s3 + s2 * s3) * v.x * v.z ^ 2
        + (s1 * s2 * s3) * v.y * v.z ^ 2)) * he2
      + (-(- 3 * v.x * v.y * v.z + v.y ^ 3
        + ((s1 * s2 * s3) - 2) * v.z ^ 3)) * he3
  -- the Vandermonde evaluation map, injective hence bijective
  set T : Cub p → ZMod p × ZMod p × ZMod p := fun v =>
    (v.x + s1 * v.y + s1 ^ 2 * v.z, v.x + s2 * v.y + s2 ^ 2 * v.z,
      v.x + s3 * v.y + s3 ^ 2 * v.z) with hT
  have hTinj : Function.Injective T := by
    intro v v' heq
    have hA1 := congrArg Prod.fst heq
    have hA2 := congrArg (fun w : ZMod p × ZMod p × ZMod p => w.2.1) heq
    have hA3 := congrArg (fun w : ZMod p × ZMod p × ZMod p => w.2.2) heq
    simp only [hT] at hA1 hA2 hA3
    have hfac1 : (s1 - s2) * ((v.y - v'.y) + (s1 + s2) * (v.z - v'.z)) = 0 := by
      linear_combination hA1 - hA2
    have ha := (mul_eq_zero.mp hfac1).resolve_left (sub_ne_zero.mpr h12)
    have hfac2 : (s1 - s3) * ((v.y - v'.y) + (s1 + s3) * (v.z - v'.z)) = 0 := by
      linear_combination hA1 - hA3
    have hb := (mul_eq_zero.mp hfac2).resolve_left (sub_ne_zero.mpr h13)
    have hfac3 : (s2 - s3) * (v.z - v'.z) = 0 := by linear_combination ha - hb
    have hz : v.z = v'.z := by
      have := (mul_eq_zero.mp hfac3).resolve_left (sub_ne_zero.mpr h23)
      linear_combination this
    have hy : v.y = v'.y := by linear_combination ha - (s1 + s2) * hz
    have hx : v.x = v'.x := by linear_combination hA1 - s1 * hy - s1 ^ 2 * hz
    ext <;> assumption
  have hTbij : Function.Bijective T := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hTinj, ?_⟩
    rw [Cub.card_cub, Fintype.card_prod, Fintype.card_prod, ZMod.card]
    ring
  -- the sphere maps onto the product-one triples
  have hbij : (Finset.univ.filter fun v : Cub p => cubNorm v = 1).card
      = (Finset.univ.filter fun w : ZMod p × ZMod p × ZMod p =>
          w.1 * w.2.1 * w.2.2 = 1).card := by
    refine Finset.card_bij (fun v _ => T v) ?_ ?_ ?_
    · intro v hv
      have hv1 : cubNorm v = 1 := (Finset.mem_filter.mp hv).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (v.x + s1 * v.y + s1 ^ 2 * v.z) * (v.x + s2 * v.y + s2 ^ 2 * v.z)
        * (v.x + s3 * v.y + s3 ^ 2 * v.z) = 1
      rw [← hmaster v]
      exact hv1
    · intro v _ v' _ heq
      exact hTinj heq
    · intro w hw
      have hw1 : w.1 * w.2.1 * w.2.2 = 1 := (Finset.mem_filter.mp hw).2
      obtain ⟨v, hveq⟩ := hTbij.surjective w
      refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hveq⟩
      rw [hmaster v]
      have h1 := congrArg Prod.fst hveq
      have h2 := congrArg (fun u : ZMod p × ZMod p × ZMod p => u.2.1) hveq
      have h3' := congrArg (fun u : ZMod p × ZMod p × ZMod p => u.2.2) hveq
      simp only [hT] at h1 h2 h3'
      rw [h1, h2, h3']
      exact hw1
  -- count the product-one triples: (p−1)²
  have hcount : (Finset.univ.filter fun w : ZMod p × ZMod p × ZMod p =>
      w.1 * w.2.1 * w.2.2 = 1).card
      = ((Finset.univ.filter fun a : ZMod p => a ≠ 0) ×ˢ
          (Finset.univ.filter fun b : ZMod p => b ≠ 0)).card := by
    refine Finset.card_bij' (fun w _ => (w.1, w.2.1))
      (fun u _ => (u.1, u.2, (u.1 * u.2)⁻¹)) ?_ ?_ ?_ ?_
    · intro w hw
      have hw1 : w.1 * w.2.1 * w.2.2 = 1 := (Finset.mem_filter.mp hw).2
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · show w.1 ≠ 0
        intro h0
        rw [h0, zero_mul, zero_mul] at hw1
        exact zero_ne_one hw1
      · show w.2.1 ≠ 0
        intro h0
        rw [h0, mul_zero, zero_mul] at hw1
        exact zero_ne_one hw1
    · intro u hu
      have ha : u.1 ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hu).1).2
      have hb : u.2 ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hu).2).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show u.1 * u.2 * (u.1 * u.2)⁻¹ = 1
      exact mul_inv_cancel₀ (mul_ne_zero ha hb)
    · intro w hw
      have hw1 : w.1 * w.2.1 * w.2.2 = 1 := (Finset.mem_filter.mp hw).2
      have hinv : (w.1 * w.2.1)⁻¹ = w.2.2 := inv_eq_of_mul_eq_one_right hw1
      exact Prod.ext rfl (Prod.ext rfl hinv)
    · intro u _
      rfl
  rw [hbij, hcount, Finset.card_product, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- The twin dress, split face: a twin right wing `q = 6m + 1` with 3 rational
    roots of `t³ = −2` carries the cubic sphere volume `c² = (6m)²`. -/
theorem twin_right_wing_split_volume {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m)
    (hroots : (Finset.univ.filter fun x : ZMod (6 * m + 1) =>
      x ^ 3 = -2).card = 3) :
    (Finset.univ.filter fun v : Cub (6 * m + 1) => cubNorm v = 1).card
      = (6 * m) ^ 2 := by
  haveI : Fact (6 * m + 1).Prime := ⟨h.2⟩
  rw [cubic_sphere_card_split (by omega) (right_wing_mod3 m) hroots,
    show 6 * m + 1 - 1 = 6 * m by omega]
  ring

/-- The twin dress, arithmetic identities: on the right wing `q = c + 1` the two
    conditional volumes are `{c², c² + 3c + 3}` — `(q−1)² = c²` and
    `q² + q + 1 = c² + 3c + 3` (frame arithmetic, ALL m; the inert value is the
    HARNESS-measured face, disclosed). -/
theorem twin_cubic_volume_dress (m : ℕ) :
    ((6 * m + 1) - 1) * ((6 * m + 1) - 1) = (6 * m) ^ 2 ∧
      (6 * m + 1) ^ 2 + (6 * m + 1) + 1 = (6 * m) ^ 2 + 3 * (6 * m) + 3 := by
  constructor
  · rw [show 6 * m + 1 - 1 = 6 * m by omega]
    ring
  · ring

/-! ### Layer 6 — H6: kernel demos (pure-ℕ folds; `Cub`/`ZMod` instances stay OUT
of every decide path — house kernel discipline)

Branch witnesses were fixed NUMERICALLY BEFORE the decide targets (mandatory,
per design): cubes mod 7 = {1, 6}, so `−2 ≡ 5` is NOT a cube mod 7 — p = 7 is
INERT (the design sketch's tentative guess is corrected); p = 13 is also inert;
the SMALLEST split 1-mod-3 prime is p = 31 (roots {s : s³ ≡ −2} has 3 elements).
Volumes: 24 = 4·6 (weld, p = 5), 57 = 7² + 7 + 1 (inert), 183 = 13² + 13 + 1
(inert), 900 = 30² (split). -/

/-- Pure-ℕ cubic-sphere counter: triples `(a,b,c) ∈ [0,n)³` with
    `a³ + (n−2)·b³ + 4c³ + 6abc ≡ 1 (mod n)` — the norm form with `−2 ≡ n−2`. -/
def cubCountN (n : ℕ) : ℕ :=
  ((List.range n).map fun a =>
    ((List.range n).map fun b =>
      ((List.range n).filter fun c =>
        (a * a * a + (n - 2) * (b * b * b) + 4 * (c * c * c) + 6 * (a * b * c))
          % n == 1 % n).length).sum).sum

/-- Pure-ℕ root counter for `t³ = −2`: `#{s ∈ [0,n) : s³ + 2 ≡ 0 (mod n)}`. -/
def rootCountN (n : ℕ) : ℕ :=
  ((List.range n).filter fun s => (s * s * s + 2) % n == 0).length

/-- Spec (one-directional, house discipline): a triple passing the ℕ-counter's
    congruence test decodes to a norm-one point of `Cub n`. -/
theorem cubCountN_point_sound {n a b c : ℕ} (h2 : 2 ≤ n)
    (h : (a * a * a + (n - 2) * (b * b * b) + 4 * (c * c * c) + 6 * (a * b * c))
      % n = 1 % n) :
    cubNorm (⟨(a : ZMod n), (b : ZMod n), (c : ZMod n)⟩ : Cub n) = 1 := by
  have hc := congrArg (fun k : ℕ => ((k : ZMod n))) h
  simp only [ZMod.natCast_mod] at hc
  push_cast [Nat.cast_sub h2] at hc
  rw [ZMod.natCast_self] at hc
  simp only [cubNorm]
  linear_combination hc

/-- Kernel count, the 2-mod-3 weld at p = 5: volume `24 = 4·6 = (p−1)(p+1)`. -/
theorem cubCountN_5 : cubCountN 5 = 24 := by decide

/-- Kernel witness: p = 7 is INERT (−2 ≡ 5 is not a cube mod 7; cubes = {1, 6}). -/
theorem rootCountN_7 : rootCountN 7 = 0 := by decide

/-- Kernel count, the inert face at p = 7: volume `57 = 7² + 7 + 1`. -/
theorem cubCountN_7 : cubCountN 7 = 57 := by decide

/-- Kernel witness: p = 13 is also INERT. -/
theorem rootCountN_13 : rootCountN 13 = 0 := by decide

/-- Kernel count, the inert face at p = 13: volume `183 = 13² + 13 + 1`. -/
theorem cubCountN_13 : cubCountN 13 = 183 := by decide

/-- Kernel witness: p = 31 is the SMALLEST split 1-mod-3 prime (3 roots). -/
theorem rootCountN_31 : rootCountN 31 = 3 := by decide

/-- Kernel count, the split face at p = 31: volume `900 = 30² = (p−1)²`. -/
theorem cubCountN_31 : cubCountN 31 = 900 := by decide

/-- The abstract weld volume at p = 5 — via `cubic_sphere_card_two_mod_three`,
    NOT via decide on `Cub` (kernel discipline); agrees with `cubCountN_5`. -/
theorem cubic_sphere_card_5 :
    (Finset.univ.filter fun v : Cub 5 => cubNorm v = 1).card = 24 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := cubic_sphere_card_two_mod_three (p := 5) (by norm_num) (by norm_num)
  simpa using h

/-- The abstract split volume at p = 31 — via `cubic_sphere_card_split` (the root
    triple certified by a tiny ZMod-31 decide); agrees with `cubCountN_31`. -/
theorem cubic_sphere_card_31 :
    (Finset.univ.filter fun v : Cub 31 => cubNorm v = 1).card = 900 := by
  have hroots : (Finset.univ.filter fun x : ZMod 31 => x ^ 3 = -2).card = 3 := by
    decide
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have h := cubic_sphere_card_split (p := 31) (by norm_num) (by norm_num) hroots
  simpa using h

/-- Agreement plaque: the ℕ-folds and the abstract volumes give the same constants
    on the demo instances (exhibited, not derived — house discipline). -/
theorem cubCount_agreement :
    cubCountN 5 = (Finset.univ.filter fun v : Cub 5 => cubNorm v = 1).card ∧
      cubCountN 31 = (Finset.univ.filter fun v : Cub 31 => cubNorm v = 1).card := by
  rw [cubCountN_5, cubCountN_31, cubic_sphere_card_5, cubic_sphere_card_31]
  exact ⟨rfl, rfl⟩

/-! ### Axiom audit -/

#print axioms qnorm_pow
#print axioms hex_unit_real
#print axioms hex_unit_imaginary
#print axioms right_wing_mod3
#print axioms left_wing_mod3
#print axioms cube_roots_rational_iff
#print axioms twin_wings_eisenstein
#print axioms Cub.commRing
#print axioms Cub.card_cub
#print axioms tCub_cubed
#print axioms cubNorm_tCub
#print axioms cubNorm_mul
#print axioms cube_bijective_units
#print axioms unique_cube_root_neg_two
#print axioms not_isSquare_neg_three
#print axioms cubic_sphere_card_two_mod_three
#print axioms cube_roots_one_card
#print axioms cube_root_count_dichotomy
#print axioms cubic_sphere_card_split
#print axioms twin_right_wing_split_volume
#print axioms twin_cubic_volume_dress
#print axioms cubCountN_point_sound
#print axioms cubCountN_5
#print axioms rootCountN_7
#print axioms cubCountN_7
#print axioms rootCountN_13
#print axioms cubCountN_13
#print axioms rootCountN_31
#print axioms cubCountN_31
#print axioms cubic_sphere_card_5
#print axioms cubic_sphere_card_31
#print axioms cubCount_agreement

end HexCubicUnits
end EuclidsPath
