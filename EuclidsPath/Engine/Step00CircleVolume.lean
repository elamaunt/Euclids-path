/-
  Step00CircleVolume — the volume of the imaginary circle, its CRT fragmentation
  over a semiprime, and the volume-deficit theorem: the cyclic budget of a composite
  modulus falls short of a full rotation, so the full rotation FORCES primality.

  ORIGIN (user's brick): "the volume direction will let us grasp the essence;
  deficit of volume forces rotations".

  HONEST MAP of that intuition onto machine-checked content:
    * VOLUME = the cardinality of the norm-one torus {x : Quad d n | qnorm x = 1}
      (nothing metric is claimed — "volume" is finite-torus counting);
    * at an odd prime ℓ the volume is exactly ℓ − χ_d(ℓ): ℓ + 1 for a nonresidue d
      (`circle_card`, inherited) and ℓ − 1 for a nonzero residue d
      (`circle_card_split`, new — the split torus is a punctured line);
    * at a semiprime pq the circle FRAGMENTS along the Chinese remainder splitting
      `quadCRT : Quad d (pq) ≃+* Quad d p × Quad d q`, and the volume multiplies:
      (p − χ_d(p)) · (q − χ_d(q))  (`circle_card_semiprime`);
    * but volume alone is not rotation: the fragmented circle is a PRODUCT of two
      cyclic groups, and every norm-one point has order dividing
      lcm(p − χ_d(p), q − χ_d(q))  (`circle_order_bound_semiprime`);
    * THE DEFICIT: both local orders are even, so the cyclic budget obeys
      2·lcm ≤ (p+1)(q+1), and the exact identity
      2(pq + 1) = (p+1)(q+1) + (p−1)(q−1) shows the budget falls short of the full
      rotation n + 1 = pq + 1 by at least (p−1)(q−1)/2
      (`circle_cyclic_budget_semiprime`, `volume_deficit_identity`,
      `circle_volume_deficit_semiprime`) — hence NO norm-one point of a semiprime
      modulus rotates fully (`circle_no_full_rotation_semiprime`);
    * THE HEADLINE IFF: for odd n ≥ 2, n is prime ⟺ the imaginary circle of n
      carries a full rotation of order n + 1 in Lucas shape
      (`circle_full_rotation_iff_prime` = `circle_exists_full_rotation` +
      `circle_lucas` glued) — the volume deficit forces the rotation short at every
      composite, so the rotation's existence forces primality.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `quadCRT` — the CRT ring isomorphism `Quad d (mn) ≃+* Quad d m × Quad d n`
      for coprime m, n, componentwise on mathlib's `ZMod.chineseRemainder`;
      `qnorm` commutes with the components (`qnorm_quadCRT_fst/snd`), so the circle
      of the product is the product of the circles (`qnorm_one_iff_components`);
    * `circle_card_split` — residue face of the volume formula: ℓ − 1 points, via
      the explicit unit-parametrization u ↦ ((u+u⁻¹)/2, (u−u⁻¹)/(2e)) with e² = d;
    * `circle_card_semiprime` — the fragmented volume
      (p − χ_d(p))·(q − χ_d(q)) in ℕ-safe 4-case `if` form;
    * `isUnit_of_qnorm_one` — every norm-one point is a unit (conjugate inverse);
    * `circle_pow_local_order`, `circle_order_bound_semiprime` — the order of any
      norm-one point over pq divides lcm of the local circle orders;
    * `circle_cyclic_budget_semiprime`, `volume_deficit_identity`,
      `circle_volume_deficit_semiprime`, `circle_no_full_rotation_semiprime` — the
      volume-deficit theorem (see the docstrings);
    * `circle_full_rotation_iff_prime` — the headline iff;
    * `twin_shared_parents`, `twin_parent_set` — TRIVIALITY-labeled frame
      arithmetic: the right wing's real parents = the left wing's imaginary
      parents = {2, 3} ∪ primes(m);
    * kernel demos: `circleCountN_35_2` (volume 36 over the semiprime 35),
      `circle_exponent_35_2` (+ its one-directional Prop reading — every circle
      point over 35 has order dividing 6: max rotation 6 vs volume 36, deficit 30),
      `circle_card_35_2` (abstract agreement), `circleCountN_127_3` (the Mersenne
      pure-cascade volume 128).

  DISCLOSURES (mandatory reading before quoting):
    * "VOLUME" IS CARDINALITY. Everywhere below "volume" means the number of
      points of the finite norm-one torus; no measure, no geometry beyond counting.
    * POINTWISE CERTIFICATE SHAPE. The headline iff is a primality certificate for
      INDIVIDUAL numbers: producing the witness requires the factorization of
      n + 1. Nothing here feeds the serial-twin wall; no density, no infinitude,
      no progress on twin primes is claimed or implied.
    * SEMIPRIME SCOPE. The fragmented volume formula and the deficit theorem are
      proved for a product of two distinct odd primes — all that the downstream
      story consumes. The squarefree generalization (list induction over the
      factors) and the prime-power case (where `Quad d ℓᵏ` is not étale and the
      circle is a different animal) are deliberately OUT of scope of this module.
    * FRAME ARITHMETIC. `twin_shared_parents` is the identity
      (6m+1) − 1 = 6m = (6m−1) + 1 dressed in divisor language; primality never
      enters. A twin pair is two primes welded through ONE shared parent set —
      that is a statement about the frame, not about primes.
    * COUNTER AGREEMENT, NOT COUNTER EQUALITY. The kernel counter
      (`circleCountN 35 2 = 36`) and the abstract cardinality
      (`circle_card_35_2`) are shown to AGREE on the demo instance; the general
      counting bijection is not formalized (`circleCountN_point_sound` and
      `toQuad_qpowN` remain the one-directional bridges — house kernel
      discipline, `Quad` instances stay OUT of every decide path).
-/
import Mathlib
import EuclidsPath.Engine.Step00ImaginaryCircle

set_option autoImplicit false

namespace EuclidsPath
namespace CircleVolume

open EuclidsPath.ImaginaryCircle
open QuadraticAlgebra

/-! ### Layer 1 — the CRT fragmentation `Quad d (mn) ≃+* Quad d m × Quad d n`

The forward map is the componentwise reduction pair (`mapHom` on each factor);
the inverse is `ZMod.chineseRemainder.symm` applied to the `re`- and `im`-columns.
The bridge lemmas identify the components of mathlib's `ZMod.chineseRemainder`
with the packaged `ZMod.castHom` reductions, so all `qnorm` compatibility is
inherited from `qnorm_mapHom`. -/

/-- The components of `ZMod.chineseRemainder` are the packaged cast homs.
    (The coercion of `ZMod.chineseRemainder` is definitionally `ZMod.cast` into
    the product ring; this lemma re-expresses the two projections.) -/
theorem chineseRemainder_eq_pair {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod (m * n)) :
    ZMod.chineseRemainder h a =
      (ZMod.castHom (dvd_mul_right m n) (ZMod m) a,
       ZMod.castHom (dvd_mul_left n m) (ZMod n) a) := by
  have hc : ZMod.chineseRemainder h a = (ZMod.cast a : ZMod m × ZMod n) := rfl
  rw [hc]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_zmod_cast, Prod.snd_zmod_cast, ZMod.castHom_apply]

theorem chineseRemainder_fst {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod (m * n)) :
    (ZMod.chineseRemainder h a).1 = ZMod.castHom (dvd_mul_right m n) (ZMod m) a := by
  rw [chineseRemainder_eq_pair h a]

theorem chineseRemainder_snd {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod (m * n)) :
    (ZMod.chineseRemainder h a).2 = ZMod.castHom (dvd_mul_left n m) (ZMod n) a := by
  rw [chineseRemainder_eq_pair h a]

/-- Reconstruction: `chineseRemainder.symm` undoes the cast-hom pair. -/
theorem chineseRemainder_symm_pair {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod (m * n)) :
    (ZMod.chineseRemainder h).symm
      (ZMod.castHom (dvd_mul_right m n) (ZMod m) a,
       ZMod.castHom (dvd_mul_left n m) (ZMod n) a) = a := by
  rw [← chineseRemainder_eq_pair h a, RingEquiv.symm_apply_apply]

theorem castHom_fst_chineseRemainder_symm {m n : ℕ} (h : Nat.Coprime m n)
    (uv : ZMod m × ZMod n) :
    ZMod.castHom (dvd_mul_right m n) (ZMod m) ((ZMod.chineseRemainder h).symm uv) = uv.1 := by
  rw [← chineseRemainder_fst h, RingEquiv.apply_symm_apply]

theorem castHom_snd_chineseRemainder_symm {m n : ℕ} (h : Nat.Coprime m n)
    (uv : ZMod m × ZMod n) :
    ZMod.castHom (dvd_mul_left n m) (ZMod n) ((ZMod.chineseRemainder h).symm uv) = uv.2 := by
  rw [← chineseRemainder_snd h, RingEquiv.apply_symm_apply]

/-- **CRT fragmentation of the quadratic ring**: for coprime `m`, `n` the ring
    `Quad d (mn)` splits as `Quad d m × Quad d n`.  The forward map is the pair of
    componentwise reductions (`mapHom`); the multiplication law of
    `QuadraticAlgebra` is polynomial in the components with the SAME image of `d`
    on both sides, so the reduction pair is a ring hom for free, and
    `ZMod.chineseRemainder.symm` on the `re`/`im` columns inverts it. -/
def quadCRT {d m n : ℕ} (h : Nat.Coprime m n) :
    Quad d (m * n) ≃+* Quad d m × Quad d n where
  toFun := ⇑((mapHom (d := d) (dvd_mul_right m n)).prod (mapHom (d := d) (dvd_mul_left n m)))
  invFun y := ⟨(ZMod.chineseRemainder h).symm (y.1.re, y.2.re),
               (ZMod.chineseRemainder h).symm (y.1.im, y.2.im)⟩
  left_inv x := by
    dsimp only
    ext <;> simp only [RingHom.prod_apply, mapHom_re, mapHom_im] <;>
      exact chineseRemainder_symm_pair h _
  right_inv y := by
    dsimp only
    refine Prod.ext ?_ ?_ <;> ext <;>
      simp only [RingHom.prod_apply, mapHom_re, mapHom_im,
        castHom_fst_chineseRemainder_symm h, castHom_snd_chineseRemainder_symm h]
  map_mul' x y := map_mul _ x y
  map_add' x y := map_add _ x y

@[simp] theorem quadCRT_fst {d m n : ℕ} (h : Nat.Coprime m n) (x : Quad d (m * n)) :
    (quadCRT (d := d) h x).1 = mapHom (d := d) (dvd_mul_right m n) x := rfl

@[simp] theorem quadCRT_snd {d m n : ℕ} (h : Nat.Coprime m n) (x : Quad d (m * n)) :
    (quadCRT (d := d) h x).2 = mapHom (d := d) (dvd_mul_left n m) x := rfl

/-- The norm commutes with the first CRT component (from `qnorm_mapHom`). -/
theorem qnorm_quadCRT_fst {d m n : ℕ} (h : Nat.Coprime m n) (x : Quad d (m * n)) :
    qnorm (quadCRT (d := d) h x).1 =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) (qnorm x) := by
  rw [quadCRT_fst, qnorm_mapHom]

/-- The norm commutes with the second CRT component. -/
theorem qnorm_quadCRT_snd {d m n : ℕ} (h : Nat.Coprime m n) (x : Quad d (m * n)) :
    qnorm (quadCRT (d := d) h x).2 =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) (qnorm x) := by
  rw [quadCRT_snd, qnorm_mapHom]

/-- **The circle of the product is the product of the circles**: a point of
    `Quad d (mn)` has norm one iff both CRT components do (CRT injectivity on the
    norm). -/
theorem qnorm_one_iff_components {d m n : ℕ} (h : Nat.Coprime m n) (x : Quad d (m * n)) :
    qnorm x = 1 ↔
      qnorm (quadCRT (d := d) h x).1 = 1 ∧ qnorm (quadCRT (d := d) h x).2 = 1 := by
  rw [qnorm_quadCRT_fst, qnorm_quadCRT_snd]
  constructor
  · intro h1
    rw [h1]
    exact ⟨map_one _, map_one _⟩
  · rintro ⟨h1, h2⟩
    have hφ : ZMod.chineseRemainder h (qnorm x) = 1 := by
      refine Prod.ext ?_ ?_
      · rw [chineseRemainder_fst h, h1, Prod.fst_one]
      · rw [chineseRemainder_snd h, h2, Prod.snd_one]
    exact (ZMod.chineseRemainder h).injective (by rw [map_one]; exact hφ)

/-! ### Layer 2 — the residue face of the volume formula: ℓ − 1 points

For a NONZERO RESIDUE `d = e²` the extension splits and the "circle"
`a² − d·b² = 1` factors as `(a + eb)(a − eb) = 1`: it is a punctured line,
parametrized by the units `u = a + eb` (with `a − eb = u⁻¹` forced).  Together
with the inherited nonresidue count `circle_card` (= ℓ + 1) this completes the
local volume formula ℓ − χ_d(ℓ). -/

/-- Every norm-one point is a unit: its conjugate `(re, −im)` is an inverse.
    (Valid over ANY modulus `n` — no primality, no residue hypothesis.) -/
theorem isUnit_of_qnorm_one {d n : ℕ} {x : Quad d n} (h : qnorm x = 1) : IsUnit x := by
  have h' : x.re ^ 2 - (d : ZMod n) * x.im ^ 2 = 1 := h
  refine IsUnit.of_mul_eq_one ⟨x.re, -x.im⟩ ?_
  ext
  · show x.re * x.re + (d : ZMod n) * x.im * (-x.im) = 1
    linear_combination h'
  · show x.re * (-x.im) + x.im * x.re + 0 * x.im * (-x.im) = 0
    ring

/-- **Residue face of the volume formula**: for an odd prime ℓ and a NONZERO
    SQUARE `d = e²`, the circle has exactly ℓ − 1 points.

    Route: `qnorm x = 1` factors as `(re + e·im)(re − e·im) = 1`, so
    `u := re + e·im` is a unit with `re − e·im = u⁻¹` forced; conversely every
    unit `u` gives the circle point `((u + u⁻¹)/2, (u − u⁻¹)/(2e))`.  This is a
    bijection with `ZMod ℓ \ {0}` — the split torus is a punctured line, one
    point FEWER than the modulus, mirror image of the nonresidue count ℓ + 1
    (`circle_card`). -/
theorem circle_card_split {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd0 : ((d : ZMod ℓ)) ≠ 0) (hd : IsSquare ((d : ZMod ℓ))) :
    (Finset.univ.filter fun x : Quad d ℓ => qnorm x = 1).card = ℓ - 1 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := fun h0 => hd0 (by rw [he, h0, mul_zero])
  have h2Z : (2 : ZMod ℓ) ≠ 0 := by
    have h22 : ((2 : ℕ) : ZMod ℓ) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    simpa using h22
  have h2e : (2 : ZMod ℓ) * e ≠ 0 := mul_ne_zero h2Z he0
  have hfact : ∀ x : Quad d ℓ, qnorm x = 1 →
      (x.re + e * x.im) * (x.re - e * x.im) = 1 := by
    intro x hx
    have hx' : x.re ^ 2 - (d : ZMod ℓ) * x.im ^ 2 = 1 := hx
    linear_combination hx' + x.im ^ 2 * he
  have hcard : ((Finset.univ : Finset (ZMod ℓ)).erase 0).card = ℓ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  rw [← hcard]
  refine Finset.card_bij' (fun x _ => x.re + e * x.im)
    (fun u _ => (⟨(u + u⁻¹) * (2 : ZMod ℓ)⁻¹, (u - u⁻¹) * ((2 : ZMod ℓ) * e)⁻¹⟩ : Quad d ℓ))
    ?_ ?_ ?_ ?_
  · -- the parameter is a unit, hence nonzero
    intro x hx
    rw [Finset.mem_filter] at hx
    have huv := hfact x hx.2
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h0
    rw [h0, zero_mul] at huv
    exact zero_ne_one huv
  · -- every nonzero parameter lands on the circle
    intro u hu
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show ((u + u⁻¹) * (2 : ZMod ℓ)⁻¹) ^ 2 - (d : ZMod ℓ) *
      ((u - u⁻¹) * ((2 : ZMod ℓ) * e)⁻¹) ^ 2 = 1
    rw [he]
    field_simp
    ring
  · -- left inverse: the parametrization recovers the point
    intro x hx
    rw [Finset.mem_filter] at hx
    have huv := hfact x hx.2
    have hv : x.re - e * x.im = (x.re + e * x.im)⁻¹ := eq_inv_of_mul_eq_one_right huv
    ext
    · show ((x.re + e * x.im) + (x.re + e * x.im)⁻¹) * (2 : ZMod ℓ)⁻¹ = x.re
      rw [← hv]
      have hs : (x.re + e * x.im) + (x.re - e * x.im) = (2 : ZMod ℓ) * x.re := by ring
      rw [hs, mul_comm (2 : ZMod ℓ) x.re, mul_assoc, mul_inv_cancel₀ h2Z, mul_one]
    · show ((x.re + e * x.im) - (x.re + e * x.im)⁻¹) * ((2 : ZMod ℓ) * e)⁻¹ = x.im
      rw [← hv]
      have hs : (x.re + e * x.im) - (x.re - e * x.im) = ((2 : ZMod ℓ) * e) * x.im := by ring
      rw [hs, mul_comm ((2 : ZMod ℓ) * e) x.im, mul_assoc, mul_inv_cancel₀ h2e, mul_one]
  · -- right inverse: the point recovers the parameter
    intro u hu
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    show ((u + u⁻¹) * (2 : ZMod ℓ)⁻¹) + e * ((u - u⁻¹) * ((2 : ZMod ℓ) * e)⁻¹) = u
    field_simp
    ring

/-! ### Layer 3 — the fragmented volume of a semiprime -/

/-- Coprimality to a modulus pushes down to nonvanishing modulo every nontrivial
    divisor (helper, used for both prime factors). -/
theorem natCast_ne_zero_of_coprime_dvd {d k n : ℕ} (hk : 1 < k) (hdvd : k ∣ n)
    (hd : Nat.Coprime d n) : ((d : ZMod k)) ≠ 0 := by
  intro h0
  have hdd : k ∣ d := (ZMod.natCast_eq_zero_iff d k).mp h0
  have hg : k ∣ Nat.gcd d n := Nat.dvd_gcd hdd hdvd
  rw [hd] at hg
  have := Nat.le_of_dvd one_pos hg
  omega

/-- **The fragmented volume**: over a product of two distinct odd primes with
    `gcd(d, pq) = 1`, the circle has exactly
    `(p − χ_d(p)) · (q − χ_d(q))` points, stated ℕ-subtraction-safely as the
    4-case product of `if`s.  Route: `quadCRT` splits the circle into the product
    of the local circles (`qnorm_one_iff_components`), and each factor is counted
    by `circle_card` (nonresidue, ℓ + 1) or `circle_card_split` (residue, ℓ − 1).

    SCOPE DISCLOSURE: semiprime only.  The squarefree case is a list induction
    over the factors that nothing downstream needs; prime powers are a different
    animal (`Quad d ℓᵏ` is not étale) — both are deliberately out. -/
theorem circle_card_semiprime {d p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : 2 < p) (hq2 : 2 < q) (hpq : p ≠ q) (hd : Nat.Coprime d (p * q)) :
    (Finset.univ.filter fun x : Quad d (p * q) => qnorm x = 1).card =
      (if IsSquare ((d : ZMod p)) then p - 1 else p + 1) *
      (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hdp : ((d : ZMod p)) ≠ 0 :=
    natCast_ne_zero_of_coprime_dvd (by omega) (dvd_mul_right p q) hd
  have hdq : ((d : ZMod q)) ≠ 0 :=
    natCast_ne_zero_of_coprime_dvd (by omega) (dvd_mul_left q p) hd
  have hsplit : (Finset.univ.filter fun x : Quad d (p * q) => qnorm x = 1).card =
      ((Finset.univ.filter fun y : Quad d p => qnorm y = 1) ×ˢ
       (Finset.univ.filter fun z : Quad d q => qnorm z = 1)).card := by
    refine Finset.card_bij' (fun x _ => quadCRT (d := d) hcop x)
      (fun y _ => (quadCRT (d := d) hcop).symm y) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      have h1 := (qnorm_one_iff_components hcop x).mp hx.2
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, h1.1⟩, Finset.mem_univ _, h1.2⟩
    · intro y hy
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hy
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [qnorm_one_iff_components hcop]
      simp only [RingEquiv.apply_symm_apply]
      exact ⟨hy.1.2, hy.2.2⟩
    · intro x _
      exact RingEquiv.symm_apply_apply _ x
    · intro y _
      exact RingEquiv.apply_symm_apply _ y
  rw [hsplit, Finset.card_product]
  have hcp : (Finset.univ.filter fun y : Quad d p => qnorm y = 1).card =
      (if IsSquare ((d : ZMod p)) then p - 1 else p + 1) := by
    by_cases hs : IsSquare ((d : ZMod p))
    · rw [if_pos hs]
      exact circle_card_split hp2 hdp hs
    · rw [if_neg hs]
      exact circle_card hp2 hs
  have hcq : (Finset.univ.filter fun z : Quad d q => qnorm z = 1).card =
      (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) := by
    by_cases hs : IsSquare ((d : ZMod q))
    · rw [if_pos hs]
      exact circle_card_split hq2 hdq hs
    · rw [if_neg hs]
      exact circle_card hq2 hs
  rw [hcp, hcq]

/-! ### Layer 4 — the headline iff: a full rotation exists ⟺ the modulus is prime -/

/-- **THE HEADLINE.**  For odd `n ≥ 2`:  `n` is PRIME  ⟺  the imaginary circle
    of `n` carries a FULL ROTATION of order `n + 1` — a `d` coprime to `n` and a
    norm-one `α : Quad d n` with `α^(n+1) = 1` whose order is certified full in
    Lucas shape (`α^((n+1)/r) − 1` a unit for every prime `r ∣ n + 1`).

    Forward: `circle_exists_full_rotation` (the order-(ℓ+1) generator of the
    circle at a prime).  Backward: `circle_lucas` (Morrison's p+1 converse).
    The volume-deficit theorem below (`circle_no_full_rotation_semiprime`)
    exhibits WHY the backward direction must hold at a semiprime: the fragmented
    circle's cyclic budget cannot reach n + 1.

    DISCLOSURE: a pointwise certificate — the witness search presupposes the
    factorization of `n + 1`; nothing here feeds the serial-twin wall. -/
theorem circle_full_rotation_iff_prime {n : ℕ} (h2 : 2 ≤ n) (hodd : n % 2 = 1) :
    n.Prime ↔ ∃ d : ℕ, Nat.Coprime d n ∧ ∃ α : Quad d n, qnorm α = 1 ∧
      α ^ (n + 1) = 1 ∧
      ∀ r : ℕ, r.Prime → r ∣ n + 1 → IsUnit (α ^ ((n + 1) / r) - 1) := by
  constructor
  · intro hp
    obtain ⟨d, hd, α, ha, hb, hc⟩ := circle_exists_full_rotation hp (by omega)
    have hd0 : ((d : ZMod n)) ≠ 0 := ne_zero_of_nonsquare hd
    have hnd : ¬ n ∣ d := fun hdvd => hd0 ((ZMod.natCast_eq_zero_iff d n).mpr hdvd)
    exact ⟨d, Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd), α, ha, hb, hc⟩
  · rintro ⟨d, hcop, α, ha, hb, hc⟩
    exact circle_lucas h2 hodd hcop ha hb hc

/-! ### Layer 5 — THE VOLUME-DEFICIT THEOREM

The heart of the module.  A composite modulus pq fragments the circle
(`quadCRT`); each fragment is cyclic of an EVEN local order p ± 1, q ± 1; the
whole circle is their product, so every rotation on it has order dividing the
lcm of the local orders; and since both are even, the lcm is at most HALF their
product:  2·lcm ≤ (p+1)(q+1) < 2(pq + 1).  The exact identity
2(pq + 1) = (p+1)(q+1) + (p−1)(q−1) names the shortfall: the cyclic budget
misses the full rotation n + 1 = pq + 1 by at least (p−1)(q−1)/2.  THE VOLUME
DEFICIT FORCES THE ROTATION SHORT — so a full rotation, where it exists, forces
primality (which is exactly `circle_lucas` quantified). -/

/-- Local order of the circle at an odd prime: every norm-one `β` over ℓ
    satisfies `β^(ℓ−χ_d(ℓ)) = 1` — nonresidue face via the Frobenius corollary
    `quad_pow_card_succ` (`β^(ℓ+1) = (qnorm β, 0) = 1`), residue face via the
    split Frobenius `quad_pow_card_of_isSquare` (`β^ℓ = β`) after cancelling the
    unit `β` (`isUnit_of_qnorm_one`). -/
theorem circle_pow_local_order {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd0 : ((d : ZMod ℓ)) ≠ 0) {β : Quad d ℓ} (hβ : qnorm β = 1) :
    β ^ (if IsSquare ((d : ZMod ℓ)) then ℓ - 1 else ℓ + 1) = 1 := by
  have hodd : ℓ % 2 = 1 := (Fact.out : ℓ.Prime).eq_two_or_odd.resolve_left (by omega)
  by_cases hsq : IsSquare ((d : ZMod ℓ))
  · rw [if_pos hsq]
    have hfrob : β ^ ℓ = β := quad_pow_card_of_isSquare hodd hd0 hsq β
    have hu : IsUnit β := isUnit_of_qnorm_one hβ
    have h1 : β ^ (ℓ - 1) * β = 1 * β := by
      rw [one_mul, ← pow_succ, show ℓ - 1 + 1 = ℓ by omega]
      exact hfrob
    exact hu.mul_right_cancel h1
  · rw [if_neg hsq]
    have h := quad_pow_card_succ hodd hsq β
    rw [hβ] at h
    rw [h]
    rfl

/-- **The order bound over a semiprime**: every norm-one point of
    `Quad d (pq)` has order dividing `lcm(p − χ_d(p), q − χ_d(q))` — the circle
    fragments along `quadCRT` and each component obeys its local circle order. -/
theorem circle_order_bound_semiprime {d p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : 2 < p) (hq2 : 2 < q) (hpq : p ≠ q) (hd : Nat.Coprime d (p * q))
    {α : Quad d (p * q)} (hnorm : qnorm α = 1) :
    orderOf α ∣ Nat.lcm (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
      (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hdp : ((d : ZMod p)) ≠ 0 :=
    natCast_ne_zero_of_coprime_dvd (by omega) (dvd_mul_right p q) hd
  have hdq : ((d : ZMod q)) ≠ 0 :=
    natCast_ne_zero_of_coprime_dvd (by omega) (dvd_mul_left q p) hd
  have hcomp := (qnorm_one_iff_components hcop α).mp hnorm
  have hβ : (quadCRT (d := d) hcop α).1 ^
      Nat.lcm (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
        (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.dvd_lcm_left
      (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
      (if IsSquare ((d : ZMod q)) then q - 1 else q + 1)
    rw [hk, pow_mul, circle_pow_local_order hp2 hdp hcomp.1, one_pow]
  have hγ : (quadCRT (d := d) hcop α).2 ^
      Nat.lcm (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
        (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.dvd_lcm_right
      (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
      (if IsSquare ((d : ZMod q)) then q - 1 else q + 1)
    rw [hk, pow_mul, circle_pow_local_order hq2 hdq hcomp.2, one_pow]
  apply orderOf_dvd_of_pow_eq_one
  apply (quadCRT (d := d) hcop).injective
  rw [map_pow, map_one]
  exact Prod.ext (by rw [Prod.pow_fst, Prod.fst_one]; exact hβ)
    (by rw [Prod.pow_snd, Prod.snd_one]; exact hγ)

/-- Two even numbers cannot lcm past half their product (helper: the gcd is at
    least 2, and gcd · lcm = product). -/
theorem lcm_even_budget {A B a b : ℕ} (hA2 : 2 ∣ A) (hB2 : 2 ∣ B) (hA0 : 0 < A)
    (hAle : A ≤ a) (hBle : B ≤ b) : 2 * Nat.lcm A B ≤ a * b := by
  have hg : 2 ∣ Nat.gcd A B := Nat.dvd_gcd hA2 hB2
  have hgpos : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left B hA0
  have h2g : 2 ≤ Nat.gcd A B := Nat.le_of_dvd hgpos hg
  calc 2 * Nat.lcm A B ≤ Nat.gcd A B * Nat.lcm A B := Nat.mul_le_mul h2g le_rfl
    _ = A * B := Nat.gcd_mul_lcm A B
    _ ≤ a * b := Nat.mul_le_mul hAle hBle

/-- **The cyclic budget of the fragmented circle**: for odd `p, q > 2` the lcm of
    the local circle orders obeys `2·lcm ≤ (p+1)(q+1)` — both local orders are
    EVEN (p ± 1 and q ± 1 with p, q odd), so their gcd eats a factor 2.
    (Frame arithmetic on the if-shape: primality is not used, only oddness.) -/
theorem circle_cyclic_budget_semiprime (d : ℕ) {p q : ℕ}
    [Decidable (IsSquare ((d : ZMod p)))] [Decidable (IsSquare ((d : ZMod q)))]
    (hp2 : 2 < p) (hq2 : 2 < q) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1) :
    2 * Nat.lcm (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
        (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) ≤ (p + 1) * (q + 1) := by
  refine lcm_even_budget ?_ ?_ ?_ ?_ ?_
  all_goals split_ifs <;> omega

/-- **The exact deficit identity** (pure frame arithmetic, all `p, q ≥ 1`):
    `2(pq + 1) = (p+1)(q+1) + (p−1)(q−1)`.  Twice the full rotation splits as
    the worst-case cyclic budget PLUS the guaranteed deficit `(p−1)(q−1)`. -/
theorem volume_deficit_identity {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2 * (p * q + 1) = (p + 1) * (q + 1) + (p - 1) * (q - 1) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- **THE VOLUME DEFICIT**: the cyclic budget of a semiprime's circle misses the
    full rotation `n + 1 = pq + 1` by at least `(p−1)(q−1)/2`, stated
    ℕ-division-safely in doubled form:
    `2·lcm + (p−1)(q−1) ≤ 2(pq + 1)`.
    (Budget bound `circle_cyclic_budget_semiprime` + identity
    `volume_deficit_identity`.) -/
theorem circle_volume_deficit_semiprime (d : ℕ) {p q : ℕ}
    [Decidable (IsSquare ((d : ZMod p)))] [Decidable (IsSquare ((d : ZMod q)))]
    (hp2 : 2 < p) (hq2 : 2 < q) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1) :
    2 * Nat.lcm (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
        (if IsSquare ((d : ZMod q)) then q - 1 else q + 1)
      + (p - 1) * (q - 1) ≤ 2 * (p * q + 1) := by
  rw [volume_deficit_identity (by omega) (by omega)]
  exact Nat.add_le_add_right
    (circle_cyclic_budget_semiprime d hp2 hq2 hpodd hqodd) _

/-- **THE DEFICIT FORCES THE ROTATION SHORT** (the user's law, machine face):
    over a semiprime modulus `pq` NO norm-one point has the full order
    `pq + 1`.  The circle fragments (`quadCRT`), the local orders are even, the
    cyclic budget `lcm` obeys `2·lcm ≤ (p+1)(q+1) < 2(pq+1)` — the deficit is at
    least `(p−1)(q−1)/2 > 0`, so the full rotation cannot exist.  Contrapositive
    reading: a full rotation of the imaginary circle FORCES primality — which is
    `circle_lucas` quantified, and the composite half of the headline iff
    `circle_full_rotation_iff_prime`. -/
theorem circle_no_full_rotation_semiprime {d p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : 2 < p) (hq2 : 2 < q) (hpq : p ≠ q) (hd : Nat.Coprime d (p * q)) :
    ∀ α : Quad d (p * q), qnorm α = 1 → orderOf α ≠ p * q + 1 := by
  intro α hnorm hord
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hqodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  have hbound := circle_order_bound_semiprime hp2 hq2 hpq hd hnorm
  rw [hord] at hbound
  have hlcm_pos : 0 < Nat.lcm (if IsSquare ((d : ZMod p)) then p - 1 else p + 1)
      (if IsSquare ((d : ZMod q)) then q - 1 else q + 1) :=
    Nat.lcm_pos (by split_ifs <;> omega) (by split_ifs <;> omega)
  have hle := Nat.le_of_dvd hlcm_pos hbound
  have hbudget := circle_cyclic_budget_semiprime d hp2 hq2 hpodd hqodd
  have hexp : (p + 1) * (q + 1) = p * q + p + q + 1 := by ring
  rw [hexp] at hbudget
  have h3p : p * 3 ≤ p * q := Nat.mul_le_mul le_rfl (by omega)
  have h3q : 3 * q ≤ p * q := Nat.mul_le_mul (by omega) le_rfl
  obtain ⟨t, ht⟩ : ∃ t, p * q = t := ⟨p * q, rfl⟩
  rw [ht] at hle hbudget h3p h3q
  omega

/-! ### Layer 6 — the shared parents of a twin pair

TRIVIALITY LABEL (mandatory): everything in this layer is the identity
`(6m+1) − 1 = 6m = (6m−1) + 1` in divisor clothing.  Primality NEVER enters.
The reading: the RIGHT wing's REAL circle order and the LEFT wing's IMAGINARY
circle order are the SAME number `6m`, so the prime divisors steering both Lucas
certificates — the "parents" — form ONE shared set `{2, 3} ∪ primes(m)`.  A twin
pair is two primes welded through one shared parent set; that weld is a property
of the FRAME `6m ± 1`, not of the primes. -/

/-- **Shared parents** (frame arithmetic, ALL `m ≥ 1`): a prime divides the
    right wing's real circle order `(6m+1) − 1` iff it divides the left wing's
    imaginary circle order `(6m−1) + 1` — both are the center `6m`. -/
theorem twin_shared_parents {m : ℕ} (hm : 1 ≤ m) :
    ∀ r : ℕ, r.Prime → (r ∣ (6 * m + 1) - 1 ↔ r ∣ (6 * m - 1) + 1) := by
  intro r _
  have h1 : (6 * m + 1) - 1 = 6 * m := by omega
  have h2 : (6 * m - 1) + 1 = 6 * m := by omega
  rw [h1, h2]

/-- The explicit parent set (frame arithmetic): a prime divides the center `6m`
    iff it is `2`, `3`, or a parent of `m`. -/
theorem twin_parent_set {m r : ℕ} (hr : r.Prime) :
    r ∣ 6 * m ↔ r = 2 ∨ r = 3 ∨ r ∣ m := by
  constructor
  · intro h
    have h6 : (6 : ℕ) * m = 2 * (3 * m) := by ring
    rw [h6] at h
    rcases (Nat.Prime.dvd_mul hr).mp h with h2 | h3m
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    · rcases (Nat.Prime.dvd_mul hr).mp h3m with h3 | hm
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3))
      · exact Or.inr (Or.inr hm)
  · rintro (rfl | rfl | hm)
    · exact ⟨3 * m, by ring⟩
    · exact ⟨2 * m, by ring⟩
    · exact hm.mul_left 6

/-! ### Layer 7 — kernel demos (pure-ℕ folds; `Quad` instances stay OUT of decide)

House kernel discipline as in `Step00ImaginaryCircle`: `circleCountN`, `qpowN`
are reused (imported, not redefined); the spec lemmas `circleCountN_point_sound`
and `toQuad_qpowN` are the one-directional bridges into `Quad`.

Demo constants at the semiprime n = 35 = 5·7, d = 2: χ₂(5) = −1 (2 is a
nonresidue mod 5) and χ₂(7) = +1 (2 = 4² mod 7), so the fragmented volume is
(5+1)·(7−1) = 36 — against the full-rotation demand n + 1 = 36.  The volume is
big enough, but it is FRAGMENTED: the order of every circle point divides
lcm(6, 6) = 6 (the order set is exactly {1, 2, 3, 6}), so the maximal rotation
is 6 against the demanded 36 — deficit 30. -/

/-- Kernel volume count at the semiprime 35 = 5·7, d = 2 (1225 pairs):
    36 = (5+1)·(7−1) points — the fragmented volume formula in kernel clothing.
    Note 36 = 35 + 1: the volume MATCHES the full-rotation demand, yet no full
    rotation exists (`circle_exponent_35_2`) — volume without cyclicity. -/
theorem circleCountN_35_2 : circleCountN 35 2 = 36 := by decide

/-- The abstract cardinality at 35 = 5·7, d = 2 — via `circle_card_semiprime`,
    NOT via decide on `Quad` (kernel discipline); agrees with
    `circleCountN_35_2`. -/
theorem circle_card_35_2 :
    (Finset.univ.filter fun x : Quad 2 35 => qnorm x = 1).card = 36 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := circle_card_semiprime (d := 2) (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hns5 : ¬ IsSquare (((2 : ℕ) : ZMod 5)) := by
    rw [show ((2 : ℕ) : ZMod 5) = (2 : ZMod 5) by norm_cast,
      ZMod.exists_sq_eq_two_iff (by norm_num)]
    omega
  have hs7 : IsSquare (((2 : ℕ) : ZMod 7)) := by
    rw [show ((2 : ℕ) : ZMod 7) = (2 : ZMod 7) by norm_cast,
      ZMod.exists_sq_eq_two_iff (by norm_num)]
    omega
  rw [if_neg hns5, if_pos hs7] at h
  exact h

/-- **The deficit in kernel clothing**: every one of the 36 circle points over
    n = 35, d = 2 already returns to 1 after SIX steps — `qpowN`-fold over all
    1225 pairs, keeping only the circle (the `!… || …` guard).  The maximal
    rotation is 6 = lcm(5+1, 7−1), against the full-rotation demand 36; the
    order set on the circle is exactly {1, 2, 3, 6}.  Pure ℕ kernel fold. -/
theorem circle_exponent_35_2 :
    ((List.range 35).all fun a => (List.range 35).all fun b =>
      (!((a * a) % 35 == (1 + 2 * (b * b)) % 35)) ||
        (decide (qpowN 2 35 (a, b) 6 = (1, 0)))) = true := by decide

/-- The Prop reading of `circle_exponent_35_2` through the one-directional spec
    bridges (`toQuad_qpowN`): every kernel-certified circle point over 35
    satisfies `α⁶ = 1` in `Quad 2 35` — no point can have order 36, exhibiting
    `circle_no_full_rotation_semiprime` at (p, q) = (5, 7). -/
theorem circle_exponent_35_2_prop {a b : ℕ} (ha : a < 35) (hb : b < 35)
    (h : (a * a) % 35 = (1 + 2 * (b * b)) % 35) :
    toQuad 2 35 (a, b) ^ 6 = 1 := by
  have hall := circle_exponent_35_2
  rw [List.all_eq_true] at hall
  have h1 := hall a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.mpr hb)
  rcases Bool.or_eq_true_iff.mp h2 with hne | hq
  · rw [Bool.not_eq_true', beq_eq_false_iff_ne] at hne
    exact absurd h hne
  · have hq' : qpowN 2 35 (a, b) 6 = (1, 0) := of_decide_eq_true hq
    rw [← toQuad_qpowN, hq']
    ext <;> simp [toQuad]

set_option maxRecDepth 8192 in
/-- Kernel volume count at the Mersenne prime 127, d = 3 (16129 pairs):
    128 = 127 + 1 = 2⁷ — the pure dyadic cascade volume of a Mersenne prime's
    imaginary circle (3 is a nonresidue mod 127 by reciprocity).  Cross-cited by
    the Mersenne/Lucas–Lehmer trace story; here it is the volume plaque only.
    (`maxRecDepth` is raised locally for the 16129-pair kernel fold; the decide
    itself stays within the house gates.) -/
theorem circleCountN_127_3 : circleCountN 127 3 = 128 := by decide

/-! ### Axiom audit -/

#print axioms chineseRemainder_eq_pair
#print axioms quadCRT
#print axioms qnorm_quadCRT_fst
#print axioms qnorm_quadCRT_snd
#print axioms qnorm_one_iff_components
#print axioms isUnit_of_qnorm_one
#print axioms circle_card_split
#print axioms natCast_ne_zero_of_coprime_dvd
#print axioms circle_card_semiprime
#print axioms circle_full_rotation_iff_prime
#print axioms circle_pow_local_order
#print axioms circle_order_bound_semiprime
#print axioms lcm_even_budget
#print axioms circle_cyclic_budget_semiprime
#print axioms volume_deficit_identity
#print axioms circle_volume_deficit_semiprime
#print axioms circle_no_full_rotation_semiprime
#print axioms twin_shared_parents
#print axioms twin_parent_set
#print axioms circleCountN_35_2
#print axioms circle_card_35_2
#print axioms circle_exponent_35_2
#print axioms circle_exponent_35_2_prop
#print axioms circleCountN_127_3

end CircleVolume
end EuclidsPath
