/-
  Step00ImaginaryCircle — the imaginary circle of a prime, Morrison's p+1 converse,
  and the twin characterization "the center acts as a full rotation twice —
  once really, once imaginarily".

  ORIGIN (user's brick): "the geometry of imaginarity that forces an orthogonal rotation
  at the composite→prime transition; twins arise when the swept rotation occupies half
  the circle, then a quarter…".

  HONEST MAP of that intuition onto machine-checked content:
    * every odd prime ℓ carries TWO circles — the REAL circle (the cyclic unit group of
      ZMod ℓ, order ℓ − 1) and the IMAGINARY circle (the norm-one torus of the quadratic
      extension ZMod ℓ[√d] for a nonresidue d, order ℓ + 1, `circle_card`);
    * the cascade "half → quarter → …" is the 2-Sylow tower of a circle; the split law
      (`dyadic_split`, `v2_min_split`) says the dyadic depth around an odd n always
      distributes over n−1 / n+1 as {1, ≥2} — the entire depth beyond one step lives on
      exactly ONE of the two circles, and which one is p mod 4 (`twin_wings_mod4`);
    * the cascade bottoms at the Wilson half-turn −1: in the domain case the only
      norm-one points of order ≤ 2 are ±1 (`circle_involution`);
    * for a twin pair (6m−1, 6m+1) the center c = 6m is SIMULTANEOUSLY the real-circle
      order of the right wing and the imaginary-circle order of the left wing; twinness
      is EXACTLY "c is realized as a full rotation twice — once really, once imaginarily"
      (`twin_iff_double_rotation`, the crown iff of this module).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * Quad d n := ZMod n[√d] as mathlib's `QuadraticAlgebra (ZMod n) d 0` (concrete pairs,
      NOT the noncomputable `GaloisField`); `qnorm` = the quadratic norm; `CharP` = n;
    * `quad_pow_card` — the Frobenius on pairs: x^ℓ = (x.re, d^((ℓ−1)/2) · x.im);
    * `quad_pow_card_succ` — nonresidue d: x^(ℓ+1) = (qnorm x, 0);
      `quad_pow_card_of_isSquare` — residue d: x^ℓ = x;
    * `circle_card` — #{x : Quad d ℓ | qnorm x = 1} = ℓ + 1 (the imaginary circle);
    * `circle_exists_full_rotation` — forward leg: an order-(ℓ+1) norm-one point exists;
    * `circle_lucas` — MORRISON'S p+1 CONVERSE (the new theorem of this pass, absent from
      mathlib): a norm-one α of full order n+1 in Quad d n with gcd(d, n) = 1 certifies
      that n is PRIME — the mirror of mathlib's `lucas_primality` on the imaginary circle;
    * `twin_iff_double_rotation` — the crown: TwinCenterZ m ⟺ (order-6m real rotation
      mod 6m+1) ∧ (order-6m imaginary norm-one rotation over 6m−1);
    * micro-blocks: mod-4 split of the wings + the √−1 dress; the dyadic cascade split
      and its padicValNat form; the m-parity depth dichotomy + the m = 1 tombstone
      refuting the naive equal-depth reading; the circle involution (Wilson bottom);
      the DFT quarter-turn plaque; the R3 glue (both rotations from twinness);
    * kernel demos: Nat-pair Bool folds (circle counts at ℓ = 5, 11; the double-rotation
      point at m = 2) with one-directional spec lemmas into Quad — Quad instances stay
      OUT of every decide path.

  DISCLOSURES (mandatory reading before quoting):
    * POINTWISE CERTIFICATE SHAPE. `circle_lucas` and the crown iff are primality
      certificates for INDIVIDUAL numbers: producing the witness requires knowing the
      factorization of the center c = 6m. Nothing here feeds the serial-twin wall; no
      density, no infinitude, no progress on twin primes is claimed or implied.
    * NO CANONICAL PAIRING. Both circles of a twin center are cyclic of order c, hence
      abstractly ≅ Z/c, but ANY pairing of the two circles is a choice — none is claimed,
      none is constructed. The two legs of the crown are logically independent wings.
    * FRAME ARITHMETIC. The mod-4 split, the dyadic split, and the depth dichotomy are
      congruence arithmetic valid for ALL m — primality only dresses them (√−1, Euler).
    * ABSTRACT FACE NOT BRIDGED. Mathlib's `FiniteField.algebraMap_norm_eq_pow`
      (FieldTheory/Finite/GaloisField.lean) says the field norm of F_{ℓ²}/F_ℓ IS
      x^(ℓ+1) — our qnorm-circle is that norm-one torus in concrete coordinates. The
      formal bridge Quad d ℓ ≃ GaloisField ℓ 2 is deliberately NOT built: the isomorphism
      is noncanonical and carries zero content for the results above.
    * NO GAUSS SIGN. The pinned mathlib has no Gauss-sum sign (τ = √p vs i√p); the
      classical "which square root" refinement is skipped and disclosed.
    * COUNTER AGREEMENT, NOT COUNTER EQUALITY. The kernel circle counters
      (`circleCountN`) and the abstract cardinality (`circle_card`) are shown to AGREE
      on the demo instances; the general counting bijection is not formalized (the
      pointwise spec `circleCountN_point_sound` + `toQuad_qpowN` are the one-directional
      bridges, house kernel discipline).
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false

namespace EuclidsPath
namespace ImaginaryCircle

open EuclidsPath.Residuals
open QuadraticAlgebra

/-! ### Layer 1 — the concrete quadratic ring `Quad d n = ZMod n[√d]`

Implemented on mathlib's `QuadraticAlgebra (ZMod n) d 0` (pairs `(re, im)` with
`ω² = d`), which the pin provides with a full `CommRing` instance — concrete and
decide-compatible, unlike the noncomputable `GaloisField`. -/

/-- The quadratic ring `ZMod n[√d]`: pairs `(a, b) = a + b·√d` with
    `(a,b)·(a',b') = (aa' + d·bb', ab' + a'b)`. -/
abbrev Quad (d n : ℕ) : Type := QuadraticAlgebra (ZMod n) (d : ZMod n) 0

/-- The quadratic norm `qnorm (a + b√d) = a² − d·b²` — the "circle equation" of the
    imaginary circle.  Agrees with mathlib's `QuadraticAlgebra.norm` (`qnorm_eq_norm`). -/
def qnorm {d n : ℕ} (x : Quad d n) : ZMod n := x.re ^ 2 - (d : ZMod n) * x.im ^ 2

theorem qnorm_eq_norm {d n : ℕ} (x : Quad d n) : qnorm x = QuadraticAlgebra.norm x := by
  simp only [qnorm, QuadraticAlgebra.norm_def]
  ring

/-- Multiplicativity of the norm (Brahmagupta identity), inherited from the
    `MonoidHom` structure of `QuadraticAlgebra.norm`. -/
theorem qnorm_mul {d n : ℕ} (x y : Quad d n) : qnorm (x * y) = qnorm x * qnorm y := by
  simp only [qnorm_eq_norm]
  exact map_mul QuadraticAlgebra.norm x y

@[simp] theorem qnorm_one {d n : ℕ} : qnorm (1 : Quad d n) = 1 := by
  simp [qnorm]

@[simp] theorem qnorm_zero {d n : ℕ} : qnorm (0 : Quad d n) = 0 := by
  simp [qnorm]

instance instFintypeQuad (d n : ℕ) [NeZero n] : Fintype (Quad d n) :=
  Fintype.ofEquiv (ZMod n × ZMod n) (equivProd ((d : ZMod n)) 0).symm

theorem card_quad (d n : ℕ) [NeZero n] : Fintype.card (Quad d n) = n ^ 2 := by
  rw [Fintype.card_congr (equivProd ((d : ZMod n)) 0), Fintype.card_prod, ZMod.card, sq]

/-- `Quad d n` has characteristic `n`, read off the first component. -/
instance instCharPQuad (d n : ℕ) : CharP (Quad d n) n where
  cast_eq_zero_iff x := by
    rw [show ((x : ℕ) : Quad d n) = ⟨((x : ℕ) : ZMod n), 0⟩ from by ext <;> simp,
      show (0 : Quad d n) = ⟨0, 0⟩ from rfl, QuadraticAlgebra.mk.injEq]
    simp [ZMod.natCast_eq_zero_iff]

/-- A nonresidue `d` is exactly the hypothesis under which mathlib's conditional
    `Field (QuadraticAlgebra K a b)` instance fires for `Quad d ℓ`. -/
theorem nonsquare_fact {d ℓ : ℕ} (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    ∀ r : ZMod ℓ, r ^ 2 ≠ (d : ZMod ℓ) + 0 * r := by
  intro r h
  rw [zero_mul, add_zero, pow_two] at h
  exact hd ⟨r, h.symm⟩

/-- A nonresidue is nonzero (`0 = 0·0` is a square). -/
theorem ne_zero_of_nonsquare {d ℓ : ℕ} (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    (d : ZMod ℓ) ≠ 0 := by
  intro h
  exact hd ⟨0, by rw [h, mul_zero]⟩

/-! ### Layer 2 — the Frobenius workhorse on pairs -/

/-- `ω² = d` in `Quad d n` (mathlib's `omega_mul_omega_eq_mk` with `b = 0`). -/
theorem omega_sq {d n : ℕ} : (omega : Quad d n) ^ 2 = .C ((d : ZMod n)) := by
  rw [pow_two]
  exact omega_mul_omega_eq_mk

theorem omega_pow_even {d n : ℕ} (k : ℕ) :
    (omega : Quad d n) ^ (2 * k) = .C (((d : ZMod n)) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_add, mul_one, pow_add, ih, omega_sq, ← C_mul, ← pow_succ]

theorem omega_pow_odd {d n : ℕ} (k : ℕ) :
    (omega : Quad d n) ^ (2 * k + 1) = .C (((d : ZMod n)) ^ k) * omega := by
  rw [pow_succ, omega_pow_even]

theorem re_add_im_omega {d n : ℕ} (x : Quad d n) :
    .C x.re + .C x.im * (omega : Quad d n) = x := by
  ext <;> simp

/-- **Frobenius on pairs**: over an odd prime `ℓ`,
    `(a + b√d)^ℓ = a + d^((ℓ−1)/2)·b·√d`.  Route: `add_pow_char` in characteristic ℓ,
    `ZMod.pow_card` on components, and the explicit odd power of `ω` — no abstract
    Galois theory. -/
theorem quad_pow_card {d ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ % 2 = 1) (x : Quad d ℓ) :
    x ^ ℓ = ⟨x.re, ((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) * x.im⟩ := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  have homega : (omega : Quad d ℓ) ^ ℓ = .C (((d : ZMod ℓ)) ^ ((ℓ - 1) / 2)) * omega := by
    have h := omega_pow_odd (d := d) (n := ℓ) ((ℓ - 1) / 2)
    rwa [show 2 * ((ℓ - 1) / 2) + 1 = ℓ by omega] at h
  calc x ^ ℓ = (.C x.re + .C x.im * omega) ^ ℓ := by rw [re_add_im_omega]
    _ = (.C x.re) ^ ℓ + (.C x.im * omega) ^ ℓ := add_pow_char _ _ ℓ
    _ = .C (x.re ^ ℓ) + .C (x.im ^ ℓ) * (omega : Quad d ℓ) ^ ℓ := by
        rw [mul_pow, C_pow, C_pow]
    _ = ⟨x.re, ((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) * x.im⟩ := by
        rw [ZMod.pow_card, ZMod.pow_card, homega]
        ext <;> simp only [re_add, im_add, re_C, im_C, re_mul, im_mul, omega_re, omega_im,
          mul_zero, zero_mul, mul_one, add_zero, zero_add]
        ring

/-- Euler's criterion, nonresidue face: `d^((ℓ−1)/2) = −1` in `ZMod ℓ`. -/
theorem nonsquare_pow_half {d ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ % 2 = 1)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    ((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) = -1 := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  have hd0 : (d : ZMod ℓ) ≠ 0 := ne_zero_of_nonsquare hd
  have h1 : (((d : ZMod ℓ)) ^ ((ℓ - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show (ℓ - 1) / 2 * 2 = ℓ - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hd0
  have hne1 : ((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) ≠ 1 := by
    intro h
    exact hd ((ZMod.euler_criterion ℓ hd0).mpr
      (by rwa [show ℓ / 2 = (ℓ - 1) / 2 by omega]))
  have hmul : (((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) - 1) *
      (((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd (sub_eq_zero.mp h) hne1
  · exact eq_neg_of_add_eq_zero_left h

/-- **Nonresidue corollary of the Frobenius**: `x^(ℓ+1) = (qnorm x, 0)` — raising to
    `ℓ+1` is "conjugate times x", i.e. the norm.  This is the concrete face of
    `FiniteField.algebraMap_norm_eq_pow` (norm of F_{ℓ²}/F_ℓ = x^(ℓ+1)); the abstract
    bridge is deliberately not built (disclosed in the header). -/
theorem quad_pow_card_succ {d ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ % 2 = 1)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) (x : Quad d ℓ) :
    x ^ (ℓ + 1) = ⟨qnorm x, 0⟩ := by
  calc x ^ (ℓ + 1) = x ^ ℓ * x := by rw [pow_succ]
    _ = (⟨x.re, ((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) * x.im⟩ : Quad d ℓ) * x := by
        rw [quad_pow_card hodd]
    _ = ⟨qnorm x, 0⟩ := by
        rw [nonsquare_pow_half hodd hd]
        ext <;> simp [qnorm] <;> ring

/-- **Residue corollary of the Frobenius**: for a nonzero residue `d` the Frobenius is
    the identity, `x^ℓ = x` — the extension is split and no imaginary circle appears. -/
theorem quad_pow_card_of_isSquare {d ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ % 2 = 1)
    (hd0 : (d : ZMod ℓ) ≠ 0) (hd : IsSquare ((d : ZMod ℓ))) (x : Quad d ℓ) :
    x ^ ℓ = x := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  have h1 : ((d : ZMod ℓ)) ^ ((ℓ - 1) / 2) = 1 := by
    have h := (ZMod.euler_criterion ℓ hd0).mp hd
    rwa [show ℓ / 2 = (ℓ - 1) / 2 by omega] at h
  rw [quad_pow_card hodd, h1]
  ext <;> simp

/-! ### Layer 3 — domain, field, and the circle cardinality ℓ + 1 -/

/-- For a nonresidue `d`, `Quad d ℓ` is an integral domain (in fact a field via
    mathlib's conditional instance; both are activated in proofs through
    `nonsquare_fact`).  Stated as a theorem producing the `IsDomain` instance. -/
theorem quad_isDomain {d ℓ : ℕ} [Fact ℓ.Prime] (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    IsDomain (Quad d ℓ) := by
  haveI : Fact (∀ r : ZMod ℓ, r ^ 2 ≠ (d : ZMod ℓ) + 0 * r) := ⟨nonsquare_fact hd⟩
  infer_instance

/-- The order-(ℓ+1) generator of the imaginary circle: `ζ = g^(ℓ−1)` for a generator
    `g` of the cyclic unit group of the field `Quad d ℓ` (order ℓ² − 1). -/
theorem circle_exists_unit_order {d ℓ : ℕ} [Fact ℓ.Prime]
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    ∃ ζ : (Quad d ℓ)ˣ, orderOf ζ = ℓ + 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  haveI : Fact (∀ r : ZMod ℓ, r ^ 2 ≠ (d : ZMod ℓ) + 0 * r) := ⟨nonsquare_fact hd⟩
  have h2 := (Fact.out : ℓ.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Quad d ℓ)ˣ)
  have h1 : ℓ ^ 2 = (ℓ - 1) * (ℓ + 1) + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by omega⟩
    have e1 : k + 2 - 1 = k + 1 := by omega
    rw [e1]; ring
  have hcard : orderOf g = (ℓ - 1) * (ℓ + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      Nat.card_eq_fintype_card, card_quad, h1, Nat.add_sub_cancel]
  refine ⟨g ^ (ℓ - 1), ?_⟩
  rw [orderOf_pow' g (show ℓ - 1 ≠ 0 by omega), hcard, Nat.gcd_comm,
    Nat.gcd_eq_left ⟨ℓ + 1, rfl⟩, Nat.mul_div_cancel_left _ (show 0 < ℓ - 1 by omega)]

/-- **The imaginary circle has exactly ℓ + 1 points**:
    `#{x : Quad d ℓ | qnorm x = 1} = ℓ + 1` for an odd prime ℓ and nonresidue d.

    Route: the circle equals the (ℓ+1)-torsion of the cyclic unit group of the field
    `Quad d ℓ` (both inclusions from `quad_pow_card_succ`), and the torsion count is
    sandwiched: `≤` by `IsCyclic.card_pow_eq_one_le`, `≥` by the ℓ+1 distinct powers of
    the order-(ℓ+1) element `ζ`.  This is the machine referent of the phrase "the
    imaginary circle of the prime ℓ". -/
theorem circle_card {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) :
    (Finset.univ.filter fun x : Quad d ℓ => qnorm x = 1).card = ℓ + 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  haveI : Fact (∀ r : ZMod ℓ, r ^ 2 ≠ (d : ZMod ℓ) + 0 * r) := ⟨nonsquare_fact hd⟩
  have hodd : ℓ % 2 = 1 := (Fact.out : ℓ.Prime).eq_two_or_odd.resolve_left (by omega)
  -- the circle is the (ℓ+1)-torsion of the unit group, transported along `Units.val`
  have himage : (Finset.univ.filter fun x : Quad d ℓ => qnorm x = 1) =
      (Finset.univ.filter fun u : (Quad d ℓ)ˣ => u ^ (ℓ + 1) = 1).image Units.val := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      have hpow : x ^ (ℓ + 1) = 1 := by
        rw [quad_pow_card_succ hodd hd x, hx]; rfl
      have hmul : x * x ^ ℓ = 1 := by rw [← pow_succ']; exact hpow
      refine ⟨Units.mkOfMulEqOne x (x ^ ℓ) hmul, ?_, Units.val_mkOfMulEqOne hmul⟩
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, Units.val_one]
      exact hpow
    · rintro ⟨u, hu, rfl⟩
      have h1 : (u : Quad d ℓ) ^ (ℓ + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
      have h2' := quad_pow_card_succ hodd hd (u : Quad d ℓ)
      rw [h1] at h2'
      have := congrArg QuadraticAlgebra.re h2'
      simpa using this.symm
  rw [himage, Finset.card_image_of_injective _ Units.val_injective]
  obtain ⟨ζ, hζ⟩ := circle_exists_unit_order hd
  apply le_antisymm
  · have h := IsCyclic.card_pow_eq_one_le (α := (Quad d ℓ)ˣ) (n := ℓ + 1) (Nat.succ_pos ℓ)
    rwa [Finset.filter_congr_decidable] at h
  · have hsub : (Finset.range (ℓ + 1)).image (fun k => ζ ^ k) ⊆
        Finset.univ.filter fun u : (Quad d ℓ)ˣ => u ^ (ℓ + 1) = 1 := by
      intro u hu
      simp only [Finset.mem_image, Finset.mem_range] at hu
      obtain ⟨k, -, rfl⟩ := hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← pow_mul, mul_comm k (ℓ + 1), pow_mul, ← hζ, pow_orderOf_eq_one, one_pow]
    have hcard : ((Finset.range (ℓ + 1)).image (fun k => ζ ^ k)).card = ℓ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      have h := pow_injOn_Iio_orderOf (x := ζ)
      rw [hζ] at h
      rwa [Finset.coe_range]
    calc ℓ + 1 = ((Finset.range (ℓ + 1)).image (fun k => ζ ^ k)).card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsub

/-! ### Layer 4A — the forward leg: a full imaginary rotation exists at every odd prime -/

/-- **Forward leg**: every odd prime `ℓ` admits a nonresidue `d` and a norm-one point
    `α` of FULL order `ℓ + 1` on the imaginary circle — with the order certified in the
    Lucas shape (`α^(ℓ+1) = 1` and `α^((ℓ+1)/r) − 1` a unit for every prime `r ∣ ℓ+1`),
    chosen to compose with the converse leg `circle_lucas`. -/
theorem circle_exists_full_rotation {ℓ : ℕ} (hp : ℓ.Prime) (h2 : 2 < ℓ) :
    ∃ d : ℕ, ¬ IsSquare ((d : ZMod ℓ)) ∧ ∃ α : Quad d ℓ, qnorm α = 1 ∧
      α ^ (ℓ + 1) = 1 ∧
      ∀ r : ℕ, r.Prime → r ∣ ℓ + 1 → IsUnit (α ^ ((ℓ + 1) / r) - 1) := by
  haveI : Fact ℓ.Prime := ⟨hp⟩
  haveI : NeZero ℓ := ⟨hp.pos.ne'⟩
  have hodd : ℓ % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  obtain ⟨d0, hd0⟩ := FiniteField.exists_nonsquare (F := ZMod ℓ)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  have hcast : ((d0.val : ℕ) : ZMod ℓ) = d0 := ZMod.natCast_rightInverse d0
  have hd : ¬ IsSquare ((d0.val : ZMod ℓ)) := by rw [hcast]; exact hd0
  haveI : Fact (∀ r : ZMod ℓ, r ^ 2 ≠ (d0.val : ZMod ℓ) + 0 * r) := ⟨nonsquare_fact hd⟩
  obtain ⟨ζ, hζ⟩ := circle_exists_unit_order (d := d0.val) hd
  have hval : ((ζ : Quad d0.val ℓ)) ^ (ℓ + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
  have hnorm : qnorm ((ζ : Quad d0.val ℓ)) = 1 := by
    have h := quad_pow_card_succ hodd hd ((ζ : Quad d0.val ℓ))
    rw [hval] at h
    have := congrArg QuadraticAlgebra.re h
    simpa using this.symm
  refine ⟨d0.val, hd, (ζ : Quad d0.val ℓ), hnorm, hval, fun r hr hrd => ?_⟩
  have hne : ((ζ : Quad d0.val ℓ)) ^ ((ℓ + 1) / r) ≠ 1 := by
    intro h
    have hu : ζ ^ ((ℓ + 1) / r) = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
    have hdvd := orderOf_dvd_of_pow_eq_one hu
    rw [hζ] at hdvd
    have hklt : (ℓ + 1) / r < ℓ + 1 := Nat.div_lt_self (by omega) hr.one_lt
    have hkpos : 0 < (ℓ + 1) / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrd) hr.pos
    have := Nat.le_of_dvd hkpos hdvd
    omega
  exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)

/-! ### Layer 4B — Morrison's p+1 converse (`circle_lucas`) -/

/-- Componentwise reduction `Quad d n →+* Quad d ℓ` along `ℓ ∣ n`
    (packaged `ZMod.castHom`). -/
def mapHom {d n ℓ : ℕ} (h : ℓ ∣ n) : Quad d n →+* Quad d ℓ where
  toFun x := ⟨ZMod.castHom h (ZMod ℓ) x.re, ZMod.castHom h (ZMod ℓ) x.im⟩
  map_one' := by ext <;> simp only [re_one, im_one, map_one, map_zero]
  map_mul' x y := by
    ext <;> simp only [re_mul, im_mul, map_add, map_mul, map_natCast,
      zero_mul, add_zero]
  map_zero' := by ext <;> simp only [re_zero, im_zero, map_zero]
  map_add' x y := by ext <;> simp only [re_add, im_add, map_add]

@[simp] theorem mapHom_re {d n ℓ : ℕ} (h : ℓ ∣ n) (x : Quad d n) :
    (mapHom (d := d) h x).re = ZMod.castHom h (ZMod ℓ) x.re := rfl

@[simp] theorem mapHom_im {d n ℓ : ℕ} (h : ℓ ∣ n) (x : Quad d n) :
    (mapHom (d := d) h x).im = ZMod.castHom h (ZMod ℓ) x.im := rfl

/-- The reduction commutes with the norm. -/
theorem qnorm_mapHom {d n ℓ : ℕ} (h : ℓ ∣ n) (x : Quad d n) :
    qnorm (mapHom (d := d) h x) = ZMod.castHom h (ZMod ℓ) (qnorm x) := by
  simp only [qnorm, mapHom_re, mapHom_im, map_sub, map_mul, map_pow, map_natCast]

/-- **MORRISON'S p+1 CONVERSE (the new theorem of this pass — absent from mathlib).**

    If `α` lies on the norm-one circle of `Quad d n` (`qnorm α = 1`, `gcd(d, n) = 1`,
    `n` odd, `n ≥ 2`) and has FULL order `n + 1` — certified Lucas-style by
    `α^(n+1) = 1` together with `α^((n+1)/r) − 1` a UNIT for every prime `r ∣ n+1` —
    then `n` is prime.

    This is the mirror of mathlib's `lucas_primality` (which certifies `n` prime from an
    order-(n−1) element of `ZMod n`): the real rotation is replaced by the imaginary one.

    Route (Morrison 1975, "A note on primality testing using Lucas sequences"): let
    `ℓ = n.minFac` and push everything down `mapHom : Quad d n →+* Quad d ℓ`.  The image
    `β` keeps order `n + 1` (`orderOf_eq_of_pow_and_pow_div_prime` — the unit
    hypotheses forbid any collapse, since a ring hom maps units to units and `0` is not
    a unit in the nontrivial ring `Quad d ℓ`).  Euler split on `d mod ℓ`:
    * `d ≡ 0` is excluded by `gcd(d, n) = 1`;
    * `d` a residue: the Frobenius is split (`quad_pow_card_of_isSquare`), so
      `β^(ℓ−1) = 1`, giving `n + 1 ≤ ℓ − 1 ≤ n − 1` — impossible;
    * `d` a nonresidue: `β^(ℓ+1) = (qnorm β, 0) = 1`, so `n + 1 ∣ ℓ + 1`, forcing
      `ℓ = n`, i.e. `n.minFac = n` — prime.

    DISCLOSURE: a pointwise certificate; the witness search presupposes the
    factorization of `n + 1`.  Nothing here feeds the serial-twin wall. -/
theorem circle_lucas {n d : ℕ} (h2 : 2 ≤ n) (hodd : n % 2 = 1) (hd : Nat.Coprime d n)
    {α : Quad d n} (hnorm : qnorm α = 1) (hpow : α ^ (n + 1) = 1)
    (hdiv : ∀ r : ℕ, r.Prime → r ∣ n + 1 → IsUnit (α ^ ((n + 1) / r) - 1)) :
    n.Prime := by
  have hn1 : n ≠ 1 := by omega
  have hℓp : n.minFac.Prime := Nat.minFac_prime hn1
  haveI : Fact n.minFac.Prime := ⟨hℓp⟩
  have hℓdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hℓodd : n.minFac % 2 = 1 := by
    rcases hℓp.eq_two_or_odd with h | h
    · exfalso
      obtain ⟨k, hk⟩ := hℓdvd
      rw [h] at hk
      omega
    · exact h
  have hℓ2 : 2 < n.minFac := by
    have := hℓp.two_le
    omega
  set β := mapHom (d := d) hℓdvd α with hβ
  have hβnorm : qnorm β = 1 := by
    rw [hβ, qnorm_mapHom, hnorm, map_one]
  have hβpow : β ^ (n + 1) = 1 := by
    rw [hβ, ← map_pow, hpow, map_one]
  have hβord : orderOf β = n + 1 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by omega) hβpow ?_
    intro r hr hrd heq
    have hu := (hdiv r hr hrd).map (mapHom (d := d) hℓdvd)
    rw [map_sub, map_pow, map_one, ← hβ, heq, sub_self] at hu
    exact not_isUnit_zero hu
  by_cases hd0 : (d : ZMod n.minFac) = 0
  · -- ramified case, excluded by coprimality
    exfalso
    have hdd : n.minFac ∣ d := (ZMod.natCast_eq_zero_iff d n.minFac).mp hd0
    have hgcd : n.minFac ∣ Nat.gcd d n := Nat.dvd_gcd hdd hℓdvd
    rw [hd] at hgcd
    have := Nat.le_of_dvd (by norm_num) hgcd
    omega
  by_cases hsq : IsSquare ((d : ZMod n.minFac))
  · -- residue case: the order n+1 would have to divide ℓ − 1 < n + 1 — impossible
    exfalso
    have hfrob : β ^ n.minFac = β := quad_pow_card_of_isSquare hℓodd hd0 hsq β
    have hβunit : IsUnit β := by
      refine IsUnit.of_mul_eq_one (β ^ n) ?_
      rw [← pow_succ']
      exact hβpow
    have hpow1 : β ^ (n.minFac - 1) = 1 := by
      have h1 : β ^ (n.minFac - 1) * β = 1 * β := by
        rw [one_mul, ← pow_succ, show n.minFac - 1 + 1 = n.minFac by omega]
        exact hfrob
      exact hβunit.mul_right_cancel h1
    have hdvd' : n + 1 ∣ n.minFac - 1 := by
      rw [← hβord]
      exact orderOf_dvd_of_pow_eq_one hpow1
    have hle : n + 1 ≤ n.minFac - 1 := Nat.le_of_dvd (by omega) hdvd'
    have hℓn : n.minFac ≤ n := Nat.le_of_dvd (by omega) hℓdvd
    omega
  · -- nonresidue case: β^(ℓ+1) = (qnorm β, 0) = 1 forces ℓ = n
    have hfrob : β ^ (n.minFac + 1) = ⟨qnorm β, 0⟩ := quad_pow_card_succ hℓodd hsq β
    have hβℓ : β ^ (n.minFac + 1) = 1 := by
      rw [hfrob, hβnorm]; rfl
    have hdvd' : n + 1 ∣ n.minFac + 1 := by
      rw [← hβord]
      exact orderOf_dvd_of_pow_eq_one hβℓ
    have hle : n + 1 ≤ n.minFac + 1 := Nat.le_of_dvd (by omega) hdvd'
    have hℓn : n.minFac ≤ n := Nat.le_of_dvd (by omega) hℓdvd
    exact Nat.prime_def_minFac.mpr ⟨h2, by omega⟩

/-! ### Layer 5 — the crown: twinness = the center rotates fully twice -/

/-- **THE CROWN.**  For `m ≥ 1`, the pair `(6m−1, 6m+1)` is a twin pair
    (`TwinCenterZ m`) **iff** the center `c = 6m` is realized as a full rotation twice:

    * ONCE REALLY — an element `a` of order `6m` in `ZMod (6m+1)` (Lucas shape:
      `a^(6m) = 1`, `a^(6m/r) ≠ 1` for every prime `r ∣ 6m`); this is
      `lucas_primality_iff` for the right wing, whose REAL circle has order
      `(6m+1) − 1 = 6m`;
    * ONCE IMAGINARILY — a norm-one point `α` of order `6m` on the imaginary circle of
      `Quad d (6m−1)` for some `d` coprime to `6m−1` (Lucas shape with unit
      differences); this is `circle_exists_full_rotation` + `circle_lucas` for the left
      wing, whose IMAGINARY circle has order `(6m−1) + 1 = 6m`.

    The center is SIMULTANEOUSLY the real-rotation order of the right wing and the
    imaginary-circle order of the left wing.

    DISCLOSURES: pointwise primality-certificate shape — the certificate search
    presupposes the factorization of `c = 6m`; it cannot feed the serial-twin wall.
    The two circles are each cyclic of order `c` but NO canonical pairing between them
    is claimed or constructed (any identification is a choice). -/
theorem twin_iff_double_rotation {m : ℕ} (hm : 1 ≤ m) :
    TwinCenterZ m ↔
      ((∃ a : ZMod (6 * m + 1), a ^ (6 * m) = 1 ∧
          ∀ r : ℕ, r.Prime → r ∣ 6 * m → a ^ (6 * m / r) ≠ 1) ∧
       (∃ d : ℕ, Nat.Coprime d (6 * m - 1) ∧ ∃ α : Quad d (6 * m - 1), qnorm α = 1 ∧
          α ^ (6 * m) = 1 ∧
          ∀ r : ℕ, r.Prime → r ∣ 6 * m → IsUnit (α ^ (6 * m / r) - 1))) := by
  have he : 6 * m - 1 + 1 = 6 * m := by omega
  -- right wing: the REAL rotation (mathlib's Lucas iff, q − 1 = 6m)
  have hR : (6 * m + 1).Prime ↔
      (∃ a : ZMod (6 * m + 1), a ^ (6 * m) = 1 ∧
        ∀ r : ℕ, r.Prime → r ∣ 6 * m → a ^ (6 * m / r) ≠ 1) := by
    simpa using lucas_primality_iff (6 * m + 1)
  -- left wing: the IMAGINARY rotation (layers 4A + 4B, p + 1 = 6m)
  have hL : (6 * m - 1).Prime ↔
      (∃ d : ℕ, Nat.Coprime d (6 * m - 1) ∧ ∃ α : Quad d (6 * m - 1), qnorm α = 1 ∧
        α ^ (6 * m) = 1 ∧
        ∀ r : ℕ, r.Prime → r ∣ 6 * m → IsUnit (α ^ (6 * m / r) - 1)) := by
    constructor
    · intro hp
      obtain ⟨d, hd, α, h1, h2, h3⟩ := circle_exists_full_rotation hp (by omega)
      rw [he] at h2 h3
      have hd0 : ((d : ZMod (6 * m - 1))) ≠ 0 := ne_zero_of_nonsquare hd
      have hnd : ¬ (6 * m - 1) ∣ d := fun hdvd =>
        hd0 ((ZMod.natCast_eq_zero_iff d (6 * m - 1)).mpr hdvd)
      exact ⟨d, Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hnd), α, h1, h2, h3⟩
    · rintro ⟨d, hcop, α, h1, h2, h3⟩
      refine circle_lucas (by omega) (by omega) hcop h1 ?_ ?_
      · rw [he]; exact h2
      · rw [he]; exact h3
  constructor
  · rintro ⟨hp1, hq1⟩
    exact ⟨hR.mp hq1, hL.mp hp1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hL.mpr h2, hR.mpr h1⟩

/-! ### Layer 6a — the mod-4 split of the wings and the √−1 dress

TRIVIALITY LABEL: `twin_wings_mod4` is frame arithmetic valid for ALL `m ≥ 1` — no
primality is used or needed.  Primality only enters the dress
(`twin_wings_sqrt_neg_one`), where mod 4 decides which wing owns a rational √−1. -/

/-- Mod-4 split of the wings (pure congruence arithmetic, ALL m). -/
theorem twin_wings_mod4 {m : ℕ} (hm : 1 ≤ m) :
    (m % 2 = 0 → (6 * m - 1) % 4 = 3 ∧ (6 * m + 1) % 4 = 1) ∧
    (m % 2 = 1 → (6 * m - 1) % 4 = 1 ∧ (6 * m + 1) % 4 = 3) := by
  omega

/-- The prime dress of the mod-4 split: in a twin pair, the wing with a rational √−1
    is decided by the parity of the center (`ZMod.exists_sq_eq_neg_one_iff`). -/
theorem twin_wings_sqrt_neg_one {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    (IsSquare (-1 : ZMod (6 * m - 1)) ↔ m % 2 = 1) ∧
    (IsSquare (-1 : ZMod (6 * m + 1)) ↔ m % 2 = 0) := by
  obtain ⟨hp, hq⟩ := h
  haveI : Fact (6 * m - 1).Prime := ⟨hp⟩
  haveI : Fact (6 * m + 1).Prime := ⟨hq⟩
  rw [ZMod.exists_sq_eq_neg_one_iff, ZMod.exists_sq_eq_neg_one_iff]
  omega

/-- In every twin pair EXACTLY ONE wing has a rational √−1 — the other wing's √−1 is
    forced into the quadratic extension (its imaginary circle). -/
theorem twin_exactly_one_sqrt_neg_one {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    IsSquare (-1 : ZMod (6 * m - 1)) ↔ ¬ IsSquare (-1 : ZMod (6 * m + 1)) := by
  obtain ⟨h1, h2⟩ := twin_wings_sqrt_neg_one hm h
  rw [h1, h2]
  omega

/-! ### Layer 6b — the dyadic cascade: split law, depth dichotomy, tombstone, bottom

TRIVIALITY LABEL: `dyadic_split`, `v2_min_split` and the depth dichotomy are frame
arithmetic for ALL odd n / all m — the cascade geometry needs no primality. -/

/-- The dyadic split law: around an odd `n`, one neighbor is `≡ 2 (mod 4)` (dyadic
    depth exactly 1) and the other is `≡ 0 (mod 4)` (depth ≥ 2). -/
theorem dyadic_split {n : ℕ} (hodd : n % 2 = 1) :
    ((n - 1) % 4 = 2 ∧ (n + 1) % 4 = 0) ∨ ((n - 1) % 4 = 0 ∧ (n + 1) % 4 = 2) := by
  omega

/-- `k ≡ 2 (mod 4)` pins the 2-adic valuation to exactly 1. -/
theorem padicValNat_two_eq_one_of_mod_four {k : ℕ} (hk : k % 4 = 2) :
    padicValNat 2 k = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ j)]

/-- `4 ∣ k` (k ≠ 0) forces 2-adic valuation ≥ 2. -/
theorem two_le_padicValNat_of_mod_four {k : ℕ} (h0 : k ≠ 0) (hk : k % 4 = 0) :
    2 ≤ padicValNat 2 k := by
  have h4 : 2 ^ 2 ∣ k := by
    have : (4 : ℕ) ∣ k := by omega
    rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at this
  exact (padicValNat_dvd_iff_le h0).mp h4

/-- The split law in padicValNat dress: `min(v₂(n−1), v₂(n+1)) = 1` for odd `n > 1` —
    the dyadic cascade beyond one step always lives on exactly ONE side. -/
theorem v2_min_split {n : ℕ} (h1 : 1 < n) (hodd : n % 2 = 1) :
    min (padicValNat 2 (n - 1)) (padicValNat 2 (n + 1)) = 1 := by
  rcases dyadic_split hodd with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have e1 := padicValNat_two_eq_one_of_mod_four ha
    have e2 := two_le_padicValNat_of_mod_four (by omega) hb
    omega
  · have e1 := padicValNat_two_eq_one_of_mod_four hb
    have e2 := two_le_padicValNat_of_mod_four (by omega) ha
    omega

/-- **m-parity depth dichotomy** (frame arithmetic, ALL m ≥ 1).  The three circles
    around a center `c = 6m` are `6m − 2` (left wing's real circle), `6m` (the shared
    circle: imaginary of the left wing AND real of the right wing), `6m + 2` (right
    wing's imaginary circle).
    * `m` even: the shared circle `6m` is the DEEP dyadic side of BOTH wings
      (`v₂ ≥ 2`), the private circles are shallow (`v₂ = 1`);
    * `m` odd: the shared circle is shallow (`v₂ = 1`) and the deep cascades of the two
      wings DIVERGE into their private circles. -/
theorem twin_center_depth_dichotomy {m : ℕ} (hm : 1 ≤ m) :
    (m % 2 = 0 → padicValNat 2 (6 * m - 2) = 1 ∧ padicValNat 2 (6 * m + 2) = 1 ∧
      2 ≤ padicValNat 2 (6 * m)) ∧
    (m % 2 = 1 → padicValNat 2 (6 * m) = 1 ∧ 2 ≤ padicValNat 2 (6 * m - 2) ∧
      2 ≤ padicValNat 2 (6 * m + 2)) := by
  constructor
  · intro he
    exact ⟨padicValNat_two_eq_one_of_mod_four (by omega),
      padicValNat_two_eq_one_of_mod_four (by omega),
      two_le_padicValNat_of_mod_four (by omega) (by omega)⟩
  · intro ho
    exact ⟨padicValNat_two_eq_one_of_mod_four (by omega),
      two_le_padicValNat_of_mod_four (by omega) (by omega),
      two_le_padicValNat_of_mod_four (by omega) (by omega)⟩

/-- **Tombstone at m = 1** refuting the naive equal-depth reading of the cascade: for
    the twin pair (5, 7) the left wing's real circle has `v₂(5 − 1) = v₂(4) = 2` while
    the right wing's imaginary circle has `v₂(7 + 1) = v₂(8) = 3` — the two private
    dyadic depths are NOT equal.  (Kernel-flavored: both sides evaluated to explicit
    powers of two; `padicValNat` itself is not kernel-reducible in the pin, so the
    evaluation goes through `padicValNat.prime_pow` — deviation from the drafted
    `decide` shape, disclosed.) -/
theorem twin_dyadic_depth_tombstone :
    padicValNat 2 (6 * 1 - 1 - 1) ≠ padicValNat 2 (6 * 1 + 1 + 1) := by
  have h4 : padicValNat 2 (6 * 1 - 1 - 1) = 2 := by
    rw [show 6 * 1 - 1 - 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h8 : padicValNat 2 (6 * 1 + 1 + 1) = 3 := by
    rw [show 6 * 1 + 1 + 1 = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  omega

/-- **The cascade bottoms at the Wilson half-turn.**  In the domain case the only
    points of order ≤ 2 (on the circle or anywhere) are `±1`: the descent
    half → quarter → … terminates at the half-turn `−1` — the same `−1` that Wilson's
    theorem reads off the full product of the real circle (companion reconnaissance
    module `Step00WilsonTurn`; named cross-reference only, no import). -/
theorem circle_involution {d ℓ : ℕ} [Fact ℓ.Prime] (hd : ¬ IsSquare ((d : ZMod ℓ)))
    {x : Quad d ℓ} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  haveI : IsDomain (Quad d ℓ) := quad_isDomain hd
  have hmul : (x - 1) * (x + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hmul with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-! ### Layer 6c — the DFT quarter-turn plaque

DISCLOSURE: this holds at ALL moduli `N` — the transform's quarter-turn is
PRIME-BLIND.  It is a naming plaque for where the quarter-turn lives in the additive
stack (the Fourier side), not a tool: nothing downstream consumes it. -/

/-- The discrete Fourier transform on `ZMod N` is a quarter-turn: its fourth power is
    the scalar `N²` (two applications of the inversion formula `ZMod.dft_dft`). -/
theorem dft_fourth_pow {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) :
    ZMod.dft (ZMod.dft (ZMod.dft (ZMod.dft Φ))) = ((N : ℂ) ^ 2) • Φ := by
  rw [ZMod.dft_dft Φ, ZMod.dft_dft]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, neg_neg]
  ring

/-! ### Layer 6d — R3 glue: a twin center rotates fully on both wings -/

/-- Real rotation from twinness: a twin center `m` yields a unit of order exactly `6m`
    in the right wing's real circle (from `reverse_lucas_primality`, order dressed via
    `orderOf_eq_of_pow_and_pow_div_prime` — the SophieGermainBranch template). -/
theorem twin_real_rotation {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    ∃ a : (ZMod (6 * m + 1))ˣ, orderOf a = 6 * m := by
  obtain ⟨-, hq⟩ := h
  obtain ⟨a, ha, hdd⟩ := reverse_lucas_primality (6 * m + 1) hq
  simp only [Nat.add_sub_cancel] at ha hdd
  have hord : orderOf a = 6 * m :=
    orderOf_eq_of_pow_and_pow_div_prime (by omega) ha hdd
  have hunit : IsUnit a := by
    refine IsUnit.of_mul_eq_one (a ^ (6 * m - 1)) ?_
    rw [← pow_succ', show 6 * m - 1 + 1 = 6 * m by omega]
    exact ha
  refine ⟨hunit.unit, ?_⟩
  have hinj := orderOf_injective (Units.coeHom (ZMod (6 * m + 1)))
    Units.val_injective hunit.unit
  simp only [Units.coeHom_apply, IsUnit.unit_spec] at hinj
  rw [← hinj]
  exact hord

/-- Imaginary rotation from twinness: the same center `6m` is realized as the order of
    a norm-one point on the left wing's imaginary circle (layer 4A + the order dress). -/
theorem twin_imaginary_rotation {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    ∃ d : ℕ, ¬ IsSquare ((d : ZMod (6 * m - 1))) ∧
      ∃ α : Quad d (6 * m - 1), qnorm α = 1 ∧ orderOf α = 6 * m := by
  obtain ⟨hp, -⟩ := h
  haveI : Fact (6 * m - 1).Prime := ⟨hp⟩
  obtain ⟨d, hd, α, h1, h2, h3⟩ := circle_exists_full_rotation hp (by omega)
  have he : 6 * m - 1 + 1 = 6 * m := by omega
  rw [he] at h2 h3
  refine ⟨d, hd, α, h1, ?_⟩
  refine orderOf_eq_of_pow_and_pow_div_prime (by omega) h2 fun r hr hrd heq => ?_
  have hu := h3 r hr hrd
  rw [heq, sub_self] at hu
  exact not_isUnit_zero hu

/-! ### Layer 7 — kernel demos (Bool/Nat folds; Quad instances stay OUT of decide)

House kernel discipline: the counters and the power ladder are pure `ℕ` recursion the
kernel can unfold literally; the spec lemmas (`toQuad_qmulN`, `toQuad_qpowN`,
`circleCountN_point_sound`) are the ONE-DIRECTIONAL bridges into `Quad`.  The
agreement between `circleCountN` and `circle_card` on the demo instances is exhibited,
not derived by a general bijection (disclosed in the header). -/

/-- Nat-pair multiplication mirroring `Quad d n` (componentwise mod n). -/
def qmulN (d n : ℕ) (x y : ℕ × ℕ) : ℕ × ℕ :=
  ((x.1 * y.1 + d * (x.2 * y.2)) % n, (x.1 * y.2 + x.2 * y.1) % n)

/-- Nat-pair power ladder (structural recursion — kernel-unfoldable). -/
def qpowN (d n : ℕ) (x : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (1 % n, 0)
  | k + 1 => qmulN d n (qpowN d n x k) x

/-- The circle counter: the number of pairs `(a, b) ∈ [0,n)²` with
    `a² ≡ 1 + d·b² (mod n)`, i.e. `qnorm = 1` in Nat clothing. -/
def circleCountN (n d : ℕ) : ℕ :=
  ((List.range n).map fun a =>
    ((List.range n).filter fun b => (a * a) % n == (1 + d * (b * b)) % n).length).sum

/-- Decoding a Nat pair into `Quad d n`. -/
def toQuad (d n : ℕ) (x : ℕ × ℕ) : Quad d n := ⟨(x.1 : ZMod n), (x.2 : ZMod n)⟩

/-- Spec: the Nat-pair product decodes to the `Quad` product. -/
theorem toQuad_qmulN (d n : ℕ) (x y : ℕ × ℕ) :
    toQuad d n (qmulN d n x y) = toQuad d n x * toQuad d n y := by
  ext <;> simp only [toQuad, qmulN, ZMod.natCast_mod, re_mul, im_mul,
    zero_mul, add_zero] <;> push_cast <;> ring

/-- Spec: the Nat-pair power ladder decodes to the `Quad` power. -/
theorem toQuad_qpowN (d n : ℕ) (x : ℕ × ℕ) (k : ℕ) :
    toQuad d n (qpowN d n x k) = toQuad d n x ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]
    ext <;> simp [toQuad, qpowN, ZMod.natCast_mod]
  | succ k ih =>
    rw [pow_succ, ← ih, qpowN, toQuad_qmulN]

/-- Spec (one-directional): a pair passing the counter's congruence test decodes to a
    norm-one point of `Quad d n`. -/
theorem circleCountN_point_sound {n d a b : ℕ}
    (h : (a * a) % n = (1 + d * (b * b)) % n) :
    qnorm (toQuad d n (a, b)) = 1 := by
  have hc := congrArg (fun k : ℕ => ((k : ZMod n))) h
  simp only [ZMod.natCast_mod] at hc
  push_cast at hc
  simp only [qnorm, toQuad]
  linear_combination hc

/-- Kernel circle count at ℓ = 5, d = 2 (25 pairs): 6 = ℓ + 1 points. -/
theorem circleCountN_5_2 : circleCountN 5 2 = 6 := by decide

/-- Kernel circle count at ℓ = 11, d = 2 (121 pairs): 12 = ℓ + 1 points. -/
theorem circleCountN_11_2 : circleCountN 11 2 = 12 := by decide

/-- The abstract cardinality at ℓ = 5, d = 2 — via `circle_card`, NOT via decide on
    `Quad` (kernel discipline); agrees with `circleCountN_5_2`. -/
theorem circle_card_5_2 :
    (Finset.univ.filter fun x : Quad 2 5 => qnorm x = 1).card = 6 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hns : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by
    rw [show ((2 : ℕ) : ZMod 5) = (2 : ZMod 5) by norm_cast,
      ZMod.exists_sq_eq_two_iff (by norm_num)]
    omega
  simpa using circle_card (by norm_num) hns

/-- The abstract cardinality at ℓ = 11, d = 2 — agrees with `circleCountN_11_2`. -/
theorem circle_card_11_2 :
    (Finset.univ.filter fun x : Quad 2 11 => qnorm x = 1).card = 12 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hns : ¬ IsSquare ((2 : ℕ) : ZMod 11) := by
    rw [show ((2 : ℕ) : ZMod 11) = (2 : ZMod 11) by norm_cast,
      ZMod.exists_sq_eq_two_iff (by norm_num)]
    omega
  simpa using circle_card (by norm_num) hns

/-- Kernel demo, m = 2, REAL wing (13): 2 is a primitive root mod 13 — an order-12
    element of the right wing's real circle.  Order dress via
    `orderOf_eq_of_pow_and_pow_div_prime`; the finite checks are ZMod-13 `decide`s
    (tiny; no `Quad` instances involved). -/
theorem real_rotation_13 : orderOf (2 : ZMod 13) = 12 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · decide
  · intro r hr hrd
    have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) hrd
    interval_cases r <;> revert hr hrd <;> decide

/-- Kernel demo, m = 2, IMAGINARY wing (11): the Nat-pair point `(3, 2)` — i.e.
    `3 + 2√2` over `ZMod 11` — has norm 1 and the full order 12 on the imaginary
    circle: `α⁶ = −1 = (10, 0)`, `α⁴ = (5, 1)`, `α¹² = 1`.  Pure Nat kernel checks. -/
theorem imag_rotation_11_kernel :
    (3 * 3) % 11 = (1 + 2 * (2 * 2)) % 11 ∧
    qpowN 2 11 (3, 2) 12 = (1, 0) ∧
    qpowN 2 11 (3, 2) 6 = (10, 0) ∧
    qpowN 2 11 (3, 2) 4 = (5, 1) := by decide

/-- The kernel point lifted through the spec lemmas: an order-12 norm-one point on the
    imaginary circle of the left wing at m = 2 — `Quad` enters only through theorems,
    never through `decide`. -/
theorem imag_rotation_11 : ∃ α : Quad 2 11, qnorm α = 1 ∧ orderOf α = 12 := by
  obtain ⟨hnorm, h12, h6, h4⟩ := imag_rotation_11_kernel
  refine ⟨toQuad 2 11 (3, 2), circleCountN_point_sound hnorm, ?_⟩
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · rw [← toQuad_qpowN, h12]
    ext <;> simp [toQuad]
  · intro r hr hrd
    have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) hrd
    have h23 : r = 2 ∨ r = 3 := by
      interval_cases r <;> revert hr hrd <;> decide
    rcases h23 with rfl | rfl
    · show toQuad 2 11 (3, 2) ^ 6 ≠ 1
      rw [← toQuad_qpowN, h6]
      intro hcontra
      have := congrArg QuadraticAlgebra.re hcontra
      simp only [toQuad] at this
      exact absurd this (by decide)
    · show toQuad 2 11 (3, 2) ^ 4 ≠ 1
      rw [← toQuad_qpowN, h4]
      intro hcontra
      have := congrArg QuadraticAlgebra.im hcontra
      simp only [toQuad] at this
      exact absurd this (by decide)

/-- The double-rotation plaque at m = 2: the twin pair (11, 13) with the center 12
    realized as a full rotation twice — once really (mod 13), once imaginarily
    (over 11). -/
theorem double_rotation_demo_m2 :
    TwinCenterZ 2 ∧ orderOf (2 : ZMod 13) = 12 ∧
      ∃ α : Quad 2 11, qnorm α = 1 ∧ orderOf α = 12 :=
  ⟨⟨by norm_num, by norm_num⟩, real_rotation_13, imag_rotation_11⟩

/-! ### Axiom audit -/

#print axioms qnorm_mul
#print axioms quad_pow_card
#print axioms quad_pow_card_succ
#print axioms quad_pow_card_of_isSquare
#print axioms quad_isDomain
#print axioms circle_exists_unit_order
#print axioms circle_card
#print axioms circle_exists_full_rotation
#print axioms circle_lucas
#print axioms twin_iff_double_rotation
#print axioms twin_wings_mod4
#print axioms twin_wings_sqrt_neg_one
#print axioms twin_exactly_one_sqrt_neg_one
#print axioms dyadic_split
#print axioms v2_min_split
#print axioms twin_center_depth_dichotomy
#print axioms twin_dyadic_depth_tombstone
#print axioms circle_involution
#print axioms dft_fourth_pow
#print axioms twin_real_rotation
#print axioms twin_imaginary_rotation
#print axioms toQuad_qpowN
#print axioms circleCountN_5_2
#print axioms circleCountN_11_2
#print axioms circle_card_5_2
#print axioms circle_card_11_2
#print axioms real_rotation_13
#print axioms imag_rotation_11
#print axioms double_rotation_demo_m2

end ImaginaryCircle
end EuclidsPath
