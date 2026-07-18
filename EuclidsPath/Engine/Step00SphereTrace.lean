/-
  Step00SphereTrace — the 4D sphere of the dispersion pass: the norm-one sphere of the
  quaternion-style 2×2 model IS SL₂(ZMod p), its volume welds both circles, its trace
  spectrum IS the circle's Kloosterman spectrum amplified by p, and the naive
  sphere-Lucas certificate is refuted by a unipotent tombstone.

  READING.  The imaginary circle of `Step00ImaginaryCircle` is the norm-one torus of a
  2-dimensional quadratic model; the SPHERE is the norm-one locus of the 4-dimensional
  matrix model — `M₂(ZMod p)` with the determinant as its quadratic norm — i.e. the
  special linear group SL₂(ZMod p).  Both circles embed as tori (S2): the imaginary
  circle as the non-split torus, the real circle (units) as the split diagonal torus.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `trace_fiber_card` — THE TRACE-FIBER LAW (the counting workhorse):
      #{g ∈ SL₂ : tr g = 2a} = p² + p·χ(a² − 1) as ℤ — the sphere's trace fibers are
      counted by the SAME quadratic character values `χ(a² − 1)` as the circle fibers
      of `Step00CircleEnergy` (`circle_fiber_card` : 1 − χ, `hyperbola_fiber_card` :
      1 + χ); route: fix the first row-column triple, count the product fiber
      `bc = (a²−1) − (x−a)²` over the free diagonal coordinate — pure conic counting,
      no conjugacy classification is invoked;
    * `sphere_card` — THE SPHERE VOLUME LAW: |SL₂(ZMod p)| = p·(p−1)·(p+1) — the sphere
      volume is exactly p · (real circle) · (imaginary circle): the 4D norm-one sphere
      welds both circles, and the three factors are the unipotent / split / non-split
      budgets.  Derived by SUMMING the trace-fiber law over all half-traces
      (Σ_a χ(a² − 1) = −1, `sum_chi_sq_sub_one`) — the design self-check
      Σ_t N(t) = p³ − p is the machine proof itself, not a side remark;
    * `quadToSL2_*` / `diagTorus` — the two torus embeddings: the imaginary circle
      {qnorm = 1} ⊆ Quad d p embeds injectively and multiplicatively as
      ![![re, d·im], ![im, re]] (non-split torus), the unit line embeds as
      diag(t, t⁻¹) (split torus).  TRIVIALITY LABEL: frame, cheap — the labels
      "circle = torus of the sphere" made machine-precise, nothing more;
    * `sphereSum_eq_p_mul_kloos` — THE NEW THEOREM OF THIS PASS:
      for u ≠ 0, `sphereSum u = Σ_{g ∈ SL₂} ψ(u·tr g) = p · kloos u u`.
      The sphere's trace spectrum IS the circle's Kloosterman spectrum amplified by
      the volume factor p.  Route: trace fibers carry p² + p·χ; the flat p² dies by
      orthogonality; the χ-layer is EXACTLY the hyperbola fiber count minus its flat
      part, and refolding the fibers reassembles kloos(u,u).  Numerically confirmed
      EXACTLY at p = 5, 11, 17 by full SL₂ enumeration BEFORE formalization
      (tools/sphere_trace_run1.log, stage s7 selftest);
    * `sphereSum_norm_le` — ‖sphereSum u‖⁴ ≤ 2·p⁷ for u ≠ 0, transported through the
      bridge from `kloos_norm_le` (‖kloos‖⁴ ≤ 2p³ of `Step00KloostermanMoment`,
      amplified by the volume factor p⁴ per fourth power);
    * `sphere_lucas_naive_refuted` — THE MANDATORY TOMBSTONE: in SL₂(ZMod 15) the
      element g = −![![1,1],![0,1]] has orderOf g = 30 > 16 = 15 + 1.  NO naive
      sphere-Lucas volume-deficit certificate exists: the sphere of a composite
      modulus has room for orders far beyond n + 1 — unipotent shears contribute the
      additive order n itself, and −1 doubles it.  The volume-deficit certificate
      lives at the TORUS level only (`circle_lucas`, the L65 deficit theorem);
      kernel decide over ZMod 15 matrix powers;
    * `borel_card` / `bruhat_card_split` — the exact finite "sphere subdivision":
      |B| = p(p−1) lower-triangular-free budget and |SL₂| = |B| + |BwB| with
      |BwB| = p²(p−1) — the Bruhat cells in cardinality form.

  THE SELF-VERDICT (mandatory reading before quoting):
    * VOLUME, NOT DECAY.  The non-abelian direction added VOLUME, not DECAY:
      `sphereSum = p · kloos` says every sphere trace sum is a circle Kloosterman sum
      times p — the cancellation ‖kloos‖ ≤ 2^{1/4}p^{3/4} is NOT improved by one iota
      on the sphere; it is amplified by the trivial factor p.  The sphere is the
      geometric costume of the L67 bridge (circleSum = −kloos), one dimension up.
    * THE GENUINE NON-ABELIAN CONTENT IS BEYOND THE PIN.  What would be genuinely new
      on the sphere — the irreducible representations of SL₂(F_p), Bessel functions of
      representations, the Kuznetsov/Petersson machinery where Kloosterman sums arise
      as MATRIX COEFFICIENTS rather than trace statistics — is absent from the pinned
      mathlib and is NOT attempted, named here and scoped out.
    * COMPLETE SUMS ONLY.  Every sum is over the COMPLETE group / complete residue
      line; the serial-twin wall lives on INCOMPLETE window sums (the sixth costume,
      complete/incomplete boundary — L69).  Nothing here crosses or claims to cross it.
    * POINTWISE CERTIFICATE SHAPE.  The tombstone refutes a certificate SHAPE; no
      claim about any individual composite beyond the exhibited 15 is made.

  ## Anti-vocabulary

  No claim in this file concerns windows, incomplete sums, densities, bounds beyond
  the stated fourth-power inequality, asymptotics, or the infinitude of anything.
  "Sphere" = the finite set SL₂(ZMod p); "volume" = cardinality; "spectrum" = the
  finite list of complete trace sums.  No twin-prime progress is claimed or implied.
-/
import Mathlib
import EuclidsPath.Engine.Step00CircleEnergy
import EuclidsPath.Engine.Step00KloostermanMoment

set_option autoImplicit false
set_option maxRecDepth 4000

namespace EuclidsPath
namespace SphereTrace

open EuclidsPath.ImaginaryCircle
open EuclidsPath.CircleEnergy
open EuclidsPath.KloostermanMoment
open QuadraticAlgebra

/-! ### Layer 1 — the sphere as a Finset and the product-fiber counting primitives

The sphere is `sl2 p = {m : Matrix (Fin 2) (Fin 2) (ZMod p) | det m = 1}` in Finset
clothing (the `circle d ℓ` idiom of `Step00CircleEnergy`, one dimension up).  The
counting primitives are the two product-fiber counts `#{(b,c) : b·c = m}` — the
hyperbola through the off-diagonal — and the shifted square-root count. -/

/-- The 4D sphere: 2×2 matrices of determinant 1 over `ZMod p`, as a `Finset`.
    `sl2_card` gives the volume `p(p−1)(p+1)`. -/
def sl2 (p : ℕ) [NeZero p] : Finset (Matrix (Fin 2) (Fin 2) (ZMod p)) :=
  Finset.univ.filter fun m => m.det = 1

theorem mem_sl2 {p : ℕ} [NeZero p] {m : Matrix (Fin 2) (Fin 2) (ZMod p)} :
    m ∈ sl2 p ↔ m.det = 1 := by
  unfold sl2
  simp

/-- Product-fiber count, nonzero level: `#{(b,c) : b·c = m} = p − 1` for `m ≠ 0` —
    the punctured hyperbola is parametrized by its first coordinate. -/
theorem pair_mul_count_ne_zero {p : ℕ} [Fact p.Prime] {m : ZMod p} (hm : m ≠ 0) :
    (Finset.univ.filter fun w : ZMod p × ZMod p => w.1 * w.2 = m).card = p - 1 := by
  have hbij : (Finset.univ.filter fun w : ZMod p × ZMod p => w.1 * w.2 = m).card
      = (Finset.univ.filter fun b : ZMod p => b ≠ 0).card := by
    refine Finset.card_bij' (fun w _ => w.1) (fun b _ => (b, b⁻¹ * m)) ?_ ?_ ?_ ?_
    · intro w hw
      have hw2 : w.1 * w.2 = m := (Finset.mem_filter.mp hw).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro h0
      rw [h0, zero_mul] at hw2
      exact hm hw2.symm
    · intro b hb
      have hb0 : b ≠ 0 := (Finset.mem_filter.mp hb).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show b * (b⁻¹ * m) = m
      rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
    · intro w hw
      have hw2 : w.1 * w.2 = m := (Finset.mem_filter.mp hw).2
      have hw1 : w.1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hw2
        exact hm hw2.symm
      have : w.1⁻¹ * m = w.2 := by
        rw [← hw2, ← mul_assoc, inv_mul_cancel₀ hw1, one_mul]
      exact Prod.ext rfl this
    · intro b _
      rfl
  rw [hbij, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]

/-- Product-fiber count, zero level: `#{(b,c) : b·c = 0} = 2p − 1` — the two crossed
    lines of the degenerate hyperbola, counted by complementing the torus `(p−1)²`. -/
theorem pair_mul_count_zero {p : ℕ} [Fact p.Prime] :
    (Finset.univ.filter fun w : ZMod p × ZMod p => w.1 * w.2 = 0).card = 2 * p - 1 := by
  have h1 : 1 ≤ p := (Fact.out : p.Prime).pos
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hcompl : (Finset.univ.filter fun w : ZMod (q + 1) × ZMod (q + 1) =>
      ¬ w.1 * w.2 = 0).card = q * q := by
    have hco : (Finset.univ.filter fun w : ZMod (q + 1) × ZMod (q + 1) =>
        ¬ w.1 * w.2 = 0)
        = (Finset.univ.filter fun b : ZMod (q + 1) => b ≠ 0) ×ˢ
          (Finset.univ.filter fun c : ZMod (q + 1) => c ≠ 0) := by
      rw [← Finset.filter_product, Finset.univ_product_univ]
      exact Finset.filter_congr fun w _ => mul_ne_zero_iff
    rw [hco, Finset.card_product, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.add_sub_cancel]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod (q + 1) × ZMod (q + 1))))
    (fun w : ZMod (q + 1) × ZMod (q + 1) => w.1 * w.2 = 0)
  rw [Finset.card_univ, Fintype.card_prod, ZMod.card] at htot
  have hexp : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by ring
  omega

/-- The combined product-fiber count over `ℤ`: `(p − 1) + p·[m = 0]`. -/
theorem pair_mul_count_int {p : ℕ} [Fact p.Prime] (m : ZMod p) :
    ((Finset.univ.filter fun w : ZMod p × ZMod p => w.1 * w.2 = m).card : ℤ)
      = (p - 1) + if m = 0 then (p : ℤ) else 0 := by
  have h1 : 1 ≤ p := (Fact.out : p.Prime).pos
  by_cases hm : m = 0
  · rw [if_pos hm, hm, pair_mul_count_zero]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
    ring
  · rw [if_neg hm, pair_mul_count_ne_zero hm]
    push_cast [Nat.cast_sub h1]
    ring

/-- Shift invariance of the square-root count: `#{x : (x−a)² = c} = #{z : z² = c}`. -/
theorem shifted_sq_count {p : ℕ} [Fact p.Prime] (a c : ZMod p) :
    (Finset.univ.filter fun x : ZMod p => (x - a) ^ 2 = c).card
      = (Finset.univ.filter fun z : ZMod p => z ^ 2 = c).card := by
  refine Finset.card_bij' (fun x _ => x - a) (fun z _ => z + a) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro z hz
    have h := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [add_sub_cancel_right]
    exact h
  · intro x _
    rw [sub_add_cancel]
  · intro z _
    rw [add_sub_cancel_right]

/-- The square-root count in χ clothes (`quadraticChar_card_sqrts`, filter form). -/
theorem sq_count_int {p : ℕ} [Fact p.Prime] (h2 : 2 < p) (c : ZMod p) :
    ((Finset.univ.filter fun z : ZMod p => z ^ 2 = c).card : ℤ)
      = quadraticChar (ZMod p) c + 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hsq := quadraticChar_card_sqrts hchar c
  simp only [Set.toFinset_setOf] at hsq
  exact hsq

/-! ### Layer 2 — THE TRACE-FIBER LAW (the counting workhorse)

Fixing the trace `2a` (half-trace coordinates: `p` is odd, so doubling is a
bijection), a sphere matrix is `![![x, b], ![c, 2a − x]]` with
`b·c = (a² − 1) − (x − a)²` — a conic fibered over the free diagonal coordinate
`x`.  The product fiber carries `p − 1 + p·[level = 0]` points, and the zero-level
count over `x` is the square-root count of `a² − 1`: the χ-values `χ(a² − 1)` of the
circle pass reappear VERBATIM as the sphere's trace-fiber corrections. -/

/-- **THE TRACE-FIBER LAW**: `#{g ∈ SL₂(ZMod p) : tr g = 2a} = p² + p·χ(a² − 1)`
    (as ℤ), for an odd prime `p`.  The sphere's trace fibers are counted by the SAME
    character values as the circle fibers of `Step00CircleEnergy` — the design
    self-check `Σ_t N(t) = p³ − p` is discharged downstream as `sl2_card`. -/
theorem trace_fiber_card {p : ℕ} [Fact p.Prime] (h2 : 2 < p) (a : ZMod p) :
    (((sl2 p).filter fun m => m.trace = 2 * a).card : ℤ)
      = (p : ℤ) ^ 2 + p * quadraticChar (ZMod p) (a ^ 2 - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  -- step 1: the fiber in triple coordinates (x, b, c) with d = 2a − x forced
  have hbij : ((sl2 p).filter fun m => m.trace = 2 * a).card
      = (Finset.univ.filter fun v : ZMod p × ZMod p × ZMod p =>
          v.2.1 * v.2.2 = (a ^ 2 - 1) - (v.1 - a) ^ 2).card := by
    refine Finset.card_bij' (fun m _ => (m 0 0, m 0 1, m 1 0))
      (fun v _ =>
        (!![v.1, v.2.1; v.2.2, 2 * a - v.1] : Matrix (Fin 2) (Fin 2) (ZMod p)))
      ?_ ?_ ?_ ?_
    · intro m hm
      obtain ⟨hm1, htr⟩ := Finset.mem_filter.mp hm
      have hdet : m.det = 1 := mem_sl2.mp hm1
      rw [Matrix.det_fin_two] at hdet
      rw [Matrix.trace_fin_two] at htr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show m 0 1 * m 1 0 = (a ^ 2 - 1) - (m 0 0 - a) ^ 2
      linear_combination -hdet + m 0 0 * htr
    · intro v hv
      have hv2 : v.2.1 * v.2.2 = (a ^ 2 - 1) - (v.1 - a) ^ 2 :=
        (Finset.mem_filter.mp hv).2
      refine Finset.mem_filter.mpr ⟨mem_sl2.mpr ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        linear_combination -hv2
      · rw [Matrix.trace_fin_two]
        simp
    · intro m hm
      obtain ⟨-, htr⟩ := Finset.mem_filter.mp hm
      rw [Matrix.trace_fin_two] at htr
      have h11 : (2 : ZMod p) * a - m 0 0 = m 1 1 := by linear_combination -htr
      rw [h11]
      exact (Matrix.eta_fin_two m).symm
    · intro v _
      simp
  -- step 2: fiber the triple count over the free diagonal coordinate
  have hcount : ((Finset.univ.filter fun v : ZMod p × ZMod p × ZMod p =>
      v.2.1 * v.2.2 = (a ^ 2 - 1) - (v.1 - a) ^ 2).card : ℤ)
      = ∑ x : ZMod p, ((Finset.univ.filter fun w : ZMod p × ZMod p =>
          w.1 * w.2 = (a ^ 2 - 1) - (x - a) ^ 2).card : ℤ) := by
    rw [Finset.card_filter]
    rw [show (Finset.univ : Finset (ZMod p × ZMod p × ZMod p))
        = Finset.univ ×ˢ Finset.univ from rfl]
    rw [Finset.sum_product]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
    push_cast
    rfl
  -- step 3: each product fiber carries (p − 1) + p·[zero level]
  have hlevel : ∑ x : ZMod p, ((Finset.univ.filter fun w : ZMod p × ZMod p =>
      w.1 * w.2 = (a ^ 2 - 1) - (x - a) ^ 2).card : ℤ)
      = ∑ x : ZMod p,
          ((p : ℤ) - 1 + if (x - a) ^ 2 = a ^ 2 - 1 then (p : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pair_mul_count_int]
    congr 1
    by_cases h : (x - a) ^ 2 = a ^ 2 - 1
    · rw [if_pos h, if_pos (by rw [h, sub_self])]
    · rw [if_neg (fun hc => h (by linear_combination -hc)), if_neg h]
  -- step 4: collect the flat part and the χ-part
  have hflat : ∑ x : ZMod p,
      ((p : ℤ) - 1 + if (x - a) ^ 2 = a ^ 2 - 1 then (p : ℤ) else 0)
      = (p : ℤ) * (p - 1) + p * (quadraticChar (ZMod p) (a ^ 2 - 1) + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      shifted_sq_count]
    have hχ := sq_count_int h2 (a ^ 2 - 1)
    rw [hχ]
    ring
  rw [hbij, hcount, hlevel, hflat]
  ring

/-! ### Layer 3 — THE SPHERE VOLUME LAW

Summing the trace-fiber law over all half-traces: the χ-corrections cancel to `−1`
(`sum_chi_sq_sub_one`, read off the OWNED hyperbola fiber count — every nonzero
residue has exactly one half-trace), leaving `p³ − p = p·(p−1)·(p+1)`.  The design
self-check `Σ_t N(t) = p³ − p` IS the proof. -/

/-- `Σ_a χ(a² − 1) = −1`: summing the hyperbola fiber count `1 + χ(a² − 1)` over all
    half-traces `a` recounts the punctured line (`p − 1` points), once each. -/
theorem sum_chi_sq_sub_one {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    ∑ a : ZMod p, quadraticChar (ZMod p) (a ^ 2 - 1) = (-1 : ℤ) := by
  have h20 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  -- the punctured line, fibered by half-trace
  have hfib : (Finset.univ.filter fun y : ZMod p => y ≠ 0).card
      = ∑ a : ZMod p, (Finset.univ.filter fun y : ZMod p =>
          y ≠ 0 ∧ y + y⁻¹ = 2 * a).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun y : ZMod p => y ≠ 0) (t := Finset.univ)
      (f := fun y => (y + y⁻¹) * (2 : ZMod p)⁻¹) (fun y _ => Finset.mem_univ _)
    rw [h]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun y _ => ?_
    constructor
    · rintro ⟨hy0, hya⟩
      refine ⟨hy0, ?_⟩
      calc y + y⁻¹ = (y + y⁻¹) * (2 : ZMod p)⁻¹ * 2 := by
            rw [mul_assoc, inv_mul_cancel₀ h20, mul_one]
        _ = 2 * a := by rw [hya]; ring
    · rintro ⟨hy0, hya⟩
      exact ⟨hy0, by rw [hya, mul_comm, ← mul_assoc, inv_mul_cancel₀ h20, one_mul]⟩
  have hline : (Finset.univ.filter fun y : ZMod p => y ≠ 0).card = p - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  -- cast to ℤ and use the owned hyperbola fiber count 1 + χ(a² − 1)
  have hz : ((p : ℤ) - 1)
      = ∑ a : ZMod p, (quadraticChar (ZMod p) (a ^ 2 - 1) + 1) := by
    have h1 : 1 ≤ p := (Fact.out : p.Prime).pos
    calc ((p : ℤ) - 1)
        = (((Finset.univ.filter fun y : ZMod p => y ≠ 0).card : ℕ) : ℤ) := by
          rw [hline]; push_cast [Nat.cast_sub h1]; ring
      _ = ∑ a : ZMod p, ((Finset.univ.filter fun y : ZMod p =>
            y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℤ) := by rw [hfib]; push_cast; rfl
      _ = ∑ a : ZMod p, (quadraticChar (ZMod p) (a ^ 2 - 1) + 1) :=
          Finset.sum_congr rfl fun a _ => hyperbola_fiber_card h2 a
  have hsplit : ∑ a : ZMod p, (quadraticChar (ZMod p) (a ^ 2 - 1) + 1)
      = (∑ a : ZMod p, quadraticChar (ZMod p) (a ^ 2 - 1)) + p := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
  rw [hsplit] at hz
  linarith

/-- The sphere volume in Finset clothing: `#(sl2 p) = p·(p−1)·(p+1)`. -/
theorem sl2_card {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    (sl2 p).card = p * (p - 1) * (p + 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have h20 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  -- fiber the sphere by half-trace
  have hfib : (sl2 p).card
      = ∑ a : ZMod p, ((sl2 p).filter fun m => m.trace = 2 * a).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := sl2 p) (t := Finset.univ)
      (f := fun m => m.trace * (2 : ZMod p)⁻¹) (fun m _ => Finset.mem_univ _)
    rw [h]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    refine Finset.filter_congr fun m _ => ?_
    constructor
    · intro ha
      calc m.trace = m.trace * (2 : ZMod p)⁻¹ * 2 := by
            rw [mul_assoc, inv_mul_cancel₀ h20, mul_one]
        _ = 2 * a := by rw [ha]; ring
    · intro ha
      rw [ha, mul_comm, ← mul_assoc, inv_mul_cancel₀ h20, one_mul]
  -- sum the trace-fiber law
  have hz : ((sl2 p).card : ℤ) = (p : ℤ) ^ 3 - p := by
    calc ((sl2 p).card : ℤ)
        = ∑ a : ZMod p, (((sl2 p).filter fun m => m.trace = 2 * a).card : ℤ) := by
          rw [hfib]; push_cast; rfl
      _ = ∑ a : ZMod p,
            ((p : ℤ) ^ 2 + p * quadraticChar (ZMod p) (a ^ 2 - 1)) :=
          Finset.sum_congr rfl fun a _ => trace_fiber_card h2 a
      _ = (p : ℤ) ^ 3 - p := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
            nsmul_eq_mul, ← Finset.mul_sum, sum_chi_sq_sub_one h2]
          ring
  have hcast : ((p * (p - 1) * (p + 1) : ℕ) : ℤ) = (p : ℤ) ^ 3 - p := by
    have h1 : 1 ≤ p := (Fact.out : p.Prime).pos
    push_cast [Nat.cast_sub h1]
    ring
  exact_mod_cast hz.trans hcast.symm

/-- **THE SPHERE VOLUME LAW**: `|SL₂(ZMod p)| = p·(p−1)·(p+1)` for an odd prime `p`
    — the 4D norm-one sphere welds both circles EXACTLY:
    volume = p · (real circle p−1) · (imaginary circle p+1), and the three factors
    are the unipotent / split-torus / non-split-torus budgets.

    DEVIATION (disclosed): the design sketch routed this through `card_GL_field` and
    the determinant surjection; the landed proof instead SUMS the owned trace-fiber
    law over all half-traces (`Σ_a (p² + p·χ(a² − 1)) = p³ − p`) — cheaper, and it
    machine-checks the design's own self-check `Σ_t N(t) = p³ − p` as the proof. -/
theorem sphere_card {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      = p * (p - 1) * (p + 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [show Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      = (sl2 p).card from Fintype.card_subtype _]
  exact sl2_card h2

/-! ### Layer 4 — the two torus embeddings (S2)

TRIVIALITY LABEL: frame, cheap.  The imaginary circle IS the non-split torus of the
sphere, the real circle (the unit line) IS the split torus — these are naming
plaques made machine-precise; no new counting happens here.  The volume law's three
factors `p·(p−1)·(p+1)` are the unipotent / split / non-split budgets, and the two
embeddings exhibit the last two. -/

/-- The non-split torus embedding: a norm-one point `x = re + im·√d` of the imaginary
    circle becomes the sphere point `![![re, d·im], ![im, re]]` (determinant
    `re² − d·im² = qnorm x = 1`). -/
def quadToSL2 {d p : ℕ} [NeZero p] (x : Quad d p) (hx : qnorm x = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![x.re, (d : ZMod p) * x.im; x.im, x.re], by
    rw [Matrix.det_fin_two_of]
    simp only [qnorm] at hx
    linear_combination hx⟩

@[simp] theorem quadToSL2_coe {d p : ℕ} [NeZero p] (x : Quad d p) (hx : qnorm x = 1) :
    (quadToSL2 x hx : Matrix (Fin 2) (Fin 2) (ZMod p))
      = !![x.re, (d : ZMod p) * x.im; x.im, x.re] := rfl

/-- The embedded circle point has trace `2·re` — the sphere's trace coordinate
    restricted to the non-split torus is EXACTLY the doubled real coordinate that
    drives `circleSum` (the L67 bridge's frequency convention). -/
theorem quadToSL2_trace {d p : ℕ} [NeZero p] (x : Quad d p) (hx : qnorm x = 1) :
    (quadToSL2 x hx : Matrix (Fin 2) (Fin 2) (ZMod p)).trace = 2 * x.re := by
  rw [quadToSL2_coe, Matrix.trace_fin_two]
  simp
  ring

/-- The circle embedding is multiplicative: circle multiplication becomes matrix
    multiplication (the 2×2 algebra is concrete on both sides). -/
theorem quadToSL2_mul {d p : ℕ} [NeZero p] (x y : Quad d p)
    (hx : qnorm x = 1) (hy : qnorm y = 1) :
    quadToSL2 (x * y) (by rw [qnorm_mul, hx, hy, mul_one])
      = quadToSL2 x hx * quadToSL2 y hy := by
  have hcoe : (quadToSL2 (x * y) (by rw [qnorm_mul, hx, hy, mul_one])
        : Matrix (Fin 2) (Fin 2) (ZMod p))
      = ((quadToSL2 x hx * quadToSL2 y hy :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
        : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, quadToSL2_coe, quadToSL2_coe, quadToSL2_coe,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [re_mul, im_mul] <;> ring
  exact Subtype.coe_injective hcoe

/-- The circle embedding is injective (read off the entries `(0,0)` and `(1,0)`). -/
theorem quadToSL2_injective {d p : ℕ} [NeZero p] {x y : Quad d p}
    (hx : qnorm x = 1) (hy : qnorm y = 1)
    (h : quadToSL2 x hx = quadToSL2 y hy) : x = y := by
  have h00 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  have h10 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0) h
  simp only [quadToSL2_coe] at h00 h10
  ext
  · exact h00
  · exact h10

/-- The split torus embedding `t ↦ diag(t, t⁻¹)` — the real circle (the unit line of
    `ZMod p`) as the diagonal torus of the sphere, packaged as a `MonoidHom`. -/
def diagTorus {p : ℕ} [NeZero p] :
    (ZMod p)ˣ →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) where
  toFun t := ⟨!![(t : ZMod p), 0; 0, ((t⁻¹ : (ZMod p)ˣ) : ZMod p)], by
    rw [Matrix.det_fin_two_of, zero_mul, sub_zero, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]⟩
  map_one' := Subtype.coe_injective (by
    show !![((1 : (ZMod p)ˣ) : ZMod p), 0; 0, ((1⁻¹ : (ZMod p)ˣ) : ZMod p)]
      = ((1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
        : Matrix (Fin 2) (Fin 2) (ZMod p))
    rw [Matrix.SpecialLinearGroup.coe_one, inv_one, Units.val_one,
      Matrix.one_fin_two])
  map_mul' s t := Subtype.coe_injective (by
    show !![((s * t : (ZMod p)ˣ) : ZMod p), 0; 0, (((s * t)⁻¹ : (ZMod p)ˣ) : ZMod p)]
      = ((⟨!![(s : ZMod p), 0; 0, ((s⁻¹ : (ZMod p)ˣ) : ZMod p)], by
            rw [Matrix.det_fin_two_of, zero_mul, sub_zero, ← Units.val_mul,
              mul_inv_cancel, Units.val_one]⟩
          * ⟨!![(t : ZMod p), 0; 0, ((t⁻¹ : (ZMod p)ˣ) : ZMod p)], by
            rw [Matrix.det_fin_two_of, zero_mul, sub_zero, ← Units.val_mul,
              mul_inv_cancel, Units.val_one]⟩
          : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
        : Matrix (Fin 2) (Fin 2) (ZMod p))
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two, mul_inv,
      Units.val_mul, Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

/-- The split torus embedding is injective (read off the `(0,0)` entry). -/
theorem diagTorus_injective {p : ℕ} [NeZero p] :
    Function.Injective (diagTorus (p := p)) := by
  intro s t h
  have h00 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp only [diagTorus, MonoidHom.coe_mk, OneHom.coe_mk] at h00
  exact Units.ext h00

/-! ### Layer 5 — THE TRACE SPECTRUM: sphereSum = p · kloos (S3)

`ψ := ZMod.stdAddChar p` throughout.  The sphere's trace spectrum is the complete
family `sphereSum u = Σ_{g ∈ SL₂} ψ(u·tr g)`; the crown identity welds it to the
OWNED Kloosterman layer of `Step00CircleEnergy`: the flat p² of every trace fiber
dies by orthogonality, and the χ-corrections refold into `kloos u u` through the
hyperbola fiber count — the same two-line mechanism as the L67 circle bridge, one
dimension up, with the volume factor `p` left standing in front. -/

/-- The sphere's trace spectrum: `sphereSum u = Σ_{g ∈ SL₂(ZMod p)} ψ(u · tr g)`. -/
noncomputable def sphereSum {p : ℕ} [NeZero p] (u : ZMod p) : ℂ :=
  ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
    ZMod.stdAddChar (u * (g : Matrix (Fin 2) (Fin 2) (ZMod p)).trace)

/-- The spectrum in Finset clothing: the subtype sum equals the `sl2` filter sum. -/
theorem sphereSum_eq_sl2 {p : ℕ} [NeZero p] (u : ZMod p) :
    sphereSum u = ∑ m ∈ sl2 p, ZMod.stdAddChar (u * m.trace) := by
  unfold sphereSum
  exact (Finset.sum_subtype _ (fun _ => mem_sl2)
    (fun m => ZMod.stdAddChar (u * m.trace))).symm

/-- **THE NEW THEOREM OF THIS PASS — the sphere's trace spectrum IS the circle's
    Kloosterman spectrum amplified by the volume factor `p`**: for `u ≠ 0`,

    `Σ_{g ∈ SL₂(ZMod p)} ψ(u·tr g) = p · kloos u u`.

    Route: fiber the sphere by half-trace; the fiber count is `p² + p·χ(a² − 1)`
    (`trace_fiber_card`) while the hyperbola fiber count is `1 + χ(a² − 1)`
    (`hyperbola_fiber_card`, owned), so fiber-by-fiber
    `N(a) − p·H(a) = p² − p` — CONSTANT — and the constant layer dies by
    orthogonality (`Σ_a ψ(2u·a) = 0`).  Refolding the hyperbola fibers reassembles
    `kloos u u` exactly.  Confirmed numerically at p = 5, 11, 17 by full SL₂
    enumeration BEFORE formalization (tools/sphere_trace_run1.log, s7 selftest).

    THE SELF-VERDICT: the non-abelian direction added VOLUME, not DECAY — the sphere
    is the geometric costume of the L67 bridge; the genuinely non-abelian layer
    (irreducible representations, Bessel/Kuznetsov) is beyond the pin, named and
    scoped out in the module header. -/
theorem sphereSum_eq_p_mul_kloos {p : ℕ} [Fact p.Prime] (h2 : 2 < p) {u : ZMod p}
    (hu : u ≠ 0) : sphereSum u = p * kloos u u := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have h20 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have h2u : 2 * u ≠ 0 := mul_ne_zero h20 hu
  -- (A) the sphere side, fibered by half-trace
  have hS : sphereSum u = ∑ a : ZMod p,
      ((((sl2 p).filter fun m => m.trace = 2 * a).card : ℕ) : ℂ)
        * ZMod.stdAddChar (u * (2 * a)) := by
    rw [sphereSum_eq_sl2]
    have h1 : ∀ m ∈ sl2 p, ZMod.stdAddChar (u * m.trace)
        = (fun a : ZMod p => ZMod.stdAddChar (u * (2 * a)))
            (m.trace * (2 : ZMod p)⁻¹) := by
      intro m _
      have hval : (2 : ZMod p) * (m.trace * (2 : ZMod p)⁻¹) = m.trace := by
        rw [mul_comm, mul_assoc, inv_mul_cancel₀ h20, mul_one]
      show ZMod.stdAddChar (u * m.trace)
        = ZMod.stdAddChar (u * (2 * (m.trace * (2 : ZMod p)⁻¹)))
      rw [hval]
    rw [Finset.sum_congr rfl h1,
      ← Finset.sum_fiberwise' (sl2 p) (fun m => m.trace * (2 : ZMod p)⁻¹)
        (fun a => ZMod.stdAddChar (u * (2 * a)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hfil : (sl2 p).filter (fun m => m.trace * (2 : ZMod p)⁻¹ = a)
        = (sl2 p).filter (fun m => m.trace = 2 * a) := by
      refine Finset.filter_congr fun m _ => ?_
      constructor
      · intro ha
        calc m.trace = m.trace * (2 : ZMod p)⁻¹ * 2 := by
              rw [mul_assoc, inv_mul_cancel₀ h20, mul_one]
          _ = 2 * a := by rw [ha]; ring
      · intro ha
        rw [ha, mul_comm, ← mul_assoc, inv_mul_cancel₀ h20, one_mul]
    rw [hfil, Finset.sum_const, nsmul_eq_mul]
  -- (B) the Kloosterman side, fibered by half-trace (the L67 idiom)
  have hK : kloos u u = ∑ a : ZMod p,
      ((Finset.univ.filter fun y : ZMod p => y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℂ)
        * ZMod.stdAddChar (u * (2 * a)) := by
    rw [kloos_def]
    have h1 : ∀ y ∈ Finset.univ.filter (fun y : ZMod p => y ≠ 0),
        ZMod.stdAddChar (u * y + u * y⁻¹)
          = (fun a : ZMod p => ZMod.stdAddChar (u * (2 * a)))
              ((y + y⁻¹) * (2 : ZMod p)⁻¹) := by
      intro y _
      have hval : (2 : ZMod p) * ((y + y⁻¹) * (2 : ZMod p)⁻¹) = y + y⁻¹ := by
        rw [mul_comm, mul_assoc, inv_mul_cancel₀ h20, mul_one]
      show ZMod.stdAddChar (u * y + u * y⁻¹)
        = ZMod.stdAddChar (u * (2 * ((y + y⁻¹) * (2 : ZMod p)⁻¹)))
      rw [hval]
      congr 1
      ring
    rw [Finset.sum_congr rfl h1,
      ← Finset.sum_fiberwise' (Finset.univ.filter fun y : ZMod p => y ≠ 0)
        (fun y => (y + y⁻¹) * (2 : ZMod p)⁻¹)
        (fun a => ZMod.stdAddChar (u * (2 * a)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hfeq : (Finset.univ.filter (fun y : ZMod p => y ≠ 0)).filter
        (fun y => (y + y⁻¹) * (2 : ZMod p)⁻¹ = a)
        = Finset.univ.filter fun y : ZMod p => y ≠ 0 ∧ y + y⁻¹ = 2 * a := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun y _ => ?_
      constructor
      · rintro ⟨hy0, hya⟩
        refine ⟨hy0, ?_⟩
        calc y + y⁻¹ = (y + y⁻¹) * (2 : ZMod p)⁻¹ * 2 := by
              rw [mul_assoc, inv_mul_cancel₀ h20, mul_one]
          _ = 2 * a := by rw [hya]; ring
      · rintro ⟨hy0, hya⟩
        exact ⟨hy0, by rw [hya, mul_comm, ← mul_assoc, inv_mul_cancel₀ h20, one_mul]⟩
    rw [hfeq, Finset.sum_const, nsmul_eq_mul]
  -- (C) fiber-by-fiber the difference is the CONSTANT p² − p, killed by orthogonality
  have key : sphereSum u - (p : ℂ) * kloos u u = 0 := by
    rw [hS, hK, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ a ∈ (Finset.univ : Finset (ZMod p)),
        ((((sl2 p).filter fun m => m.trace = 2 * a).card : ℕ) : ℂ)
            * ZMod.stdAddChar (u * (2 * a))
          - (p : ℂ) * (((Finset.univ.filter fun y : ZMod p =>
              y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℂ)
            * ZMod.stdAddChar (u * (2 * a)))
        = ((p : ℂ) ^ 2 - p) * ZMod.stdAddChar (u * (2 * a)) := by
      intro a _
      have hN := trace_fiber_card h2 a
      have hH := hyperbola_fiber_card h2 a
      have hint : (((sl2 p).filter fun m => m.trace = 2 * a).card : ℤ)
          - (p : ℤ) * ((Finset.univ.filter fun y : ZMod p =>
              y ≠ 0 ∧ y + y⁻¹ = 2 * a).card : ℤ)
          = (p : ℤ) ^ 2 - p := by
        rw [hN, hH]
        ring
      have hC := congrArg (fun z : ℤ => (z : ℂ)) hint
      push_cast at hC
      linear_combination ZMod.stdAddChar (u * (2 * a)) * hC
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hall : ∑ a : ZMod p, ZMod.stdAddChar (u * (2 * a)) = 0 := by
      have h := AddChar.sum_mulShift (2 * u) (ZMod.isPrimitive_stdAddChar p)
      rw [if_neg h2u, Nat.cast_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      ring
    rw [hall, mul_zero]
  linear_combination key

/-- The amplified cancellation bound: `‖sphereSum u‖⁴ ≤ 2·p⁷` for `u ≠ 0` — the
    owned `‖kloos‖⁴ ≤ 2p³` (`kloos_norm_le`) times the volume factor `p⁴`.  The
    exponent bookkeeping IS the self-verdict: the sphere amplified the circle's
    cancellation by volume; it did not deepen it. -/
theorem sphereSum_norm_le {p : ℕ} [Fact p.Prime] (h2 : 2 < p) {u : ZMod p}
    (hu : u ≠ 0) : ‖sphereSum u‖ ^ 4 ≤ 2 * (p : ℝ) ^ 7 := by
  rw [sphereSum_eq_p_mul_kloos h2 hu, norm_mul, mul_pow, RCLike.norm_natCast]
  calc (p : ℝ) ^ 4 * ‖kloos u u‖ ^ 4
      ≤ (p : ℝ) ^ 4 * (2 * (p : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left (kloos_norm_le h2 hu hu) (by positivity)
    _ = 2 * (p : ℝ) ^ 7 := by ring

/-! ### Layer 6 — THE TOMBSTONE (S4): no naive sphere-Lucas certificate

`circle_lucas` (L65) certifies primality from a full rotation of order `n + 1` on
the imaginary circle, because a composite circle's cyclic budget falls short of
`n + 1` — THE TORUS HAS A VOLUME DEFICIT.  The sphere does NOT: over the composite
modulus 15 the sphere point `g = −![![1,1],![0,1]]` has order `30 > 16 = 15 + 1`
— the unipotent shear contributes the ADDITIVE order 15 of the modulus itself and
`−1` doubles it.  Any "sphere-Lucas" certificate shaped `order > n + 1 ⟹ prime`
is dead on arrival; the deficit certificate lives at the torus level only.
Kernel decide over `ZMod 15` matrix powers (house discipline: the checks are
matrix-literal computations, `orderOf` enters only through theorems). -/

/-- The tombstone matrix `−![![1,1],![0,1]]` over `ZMod 15`, in literal
    coordinates (`14 = −1 mod 15`). -/
def shearNegMat : Matrix (Fin 2) (Fin 2) (ZMod 15) := !![14, 14; 0, 14]

/-- The literal coordinates are exactly `−![![1,1],![0,1]]`. -/
theorem shearNegMat_eq_neg :
    shearNegMat = -(!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 15)) := by
  decide

/-- Kernel power checks: `M³⁰ = 1` and the three maximal-divisor punctures
    `M¹⁵ ≠ 1` (the sign survives), `M¹⁰ ≠ 1`, `M⁶ ≠ 1` (the shear survives). -/
theorem shearNegMat_pow_30 : shearNegMat ^ 30 = 1 := by decide

theorem shearNegMat_pow_15 : shearNegMat ^ 15 ≠ 1 := by decide

theorem shearNegMat_pow_10 : shearNegMat ^ 10 ≠ 1 := by decide

theorem shearNegMat_pow_6 : shearNegMat ^ 6 ≠ 1 := by decide

/-- The tombstone element as a sphere point of the COMPOSITE modulus 15. -/
def shearNeg : Matrix.SpecialLinearGroup (Fin 2) (ZMod 15) :=
  ⟨shearNegMat, by rw [Matrix.det_fin_two]; decide⟩

/-- The tombstone order: `orderOf (−![![1,1],![0,1]]) = 30` in SL₂(ZMod 15). -/
theorem shearNeg_orderOf : orderOf shearNeg = 30 := by
  have hval : ∀ k : ℕ, shearNeg ^ k = 1 → shearNegMat ^ k = 1 := by
    intro k hk
    have h := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 15) =>
        (g : Matrix (Fin 2) (Fin 2) (ZMod 15))) hk
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · have h : ((shearNeg ^ 30 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 15))
        : Matrix (Fin 2) (Fin 2) (ZMod 15))
        = ((1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 15))
          : Matrix (Fin 2) (Fin 2) (ZMod 15)) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      exact shearNegMat_pow_30
    exact Subtype.coe_injective h
  · intro r hr hrd
    have hle : r ≤ 30 := Nat.le_of_dvd (by norm_num) hrd
    have h235 : r = 2 ∨ r = 3 ∨ r = 5 := by
      interval_cases r <;> revert hr hrd <;> decide
    rcases h235 with rfl | rfl | rfl
    · exact fun hcontra => shearNegMat_pow_15 (hval 15 hcontra)
    · exact fun hcontra => shearNegMat_pow_10 (hval 10 hcontra)
    · exact fun hcontra => shearNegMat_pow_6 (hval 6 hcontra)

/-- **THE TOMBSTONE — no naive sphere-Lucas volume-deficit certificate exists**:
    the sphere of the composite modulus 15 carries a point of order
    `30 > 16 = 15 + 1`.  Unipotents give the sphere too much order-room: the shear
    `![![1,1],![0,1]]` has the ADDITIVE order 15 (the modulus itself, not a divisor
    of any circle volume), and `−1` doubles it to `lcm(2,15) = 30`.  The
    volume-deficit certificate lives at the TORUS level only (`circle_lucas`,
    `circle_no_full_rotation_semiprime` — L65 preserved untouched). -/
theorem sphere_lucas_naive_refuted :
    orderOf shearNeg = 30 ∧ 15 + 1 < orderOf shearNeg :=
  ⟨shearNeg_orderOf, by rw [shearNeg_orderOf]; norm_num⟩

/-! ### Layer 7 — the Bruhat subdivision in cardinality form (S5)

The exact finite "sphere subdivision": the Borel cell (lower-left entry 0) carries
`p(p−1)` points, the big cell the remaining `p²(p−1)`; together they recount the
sphere volume `p(p−1)(p+1)` exactly. -/

/-- The Borel cell count: `#{g ∈ SL₂ : g₁₀ = 0} = p·(p−1)` — the diagonal is a unit
    line (`a·d = 1`), the upper-right entry is free. -/
theorem borel_card {p : ℕ} [Fact p.Prime] :
    ((sl2 p).filter fun m => m 1 0 = 0).card = p * (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hbij : ((sl2 p).filter fun m => m 1 0 = 0).card
      = ((Finset.univ.filter fun a : ZMod p => a ≠ 0) ×ˢ
          (Finset.univ : Finset (ZMod p))).card := by
    refine Finset.card_bij' (fun m _ => (m 0 0, m 0 1))
      (fun w _ => (!![w.1, w.2; 0, w.1⁻¹] : Matrix (Fin 2) (Fin 2) (ZMod p)))
      ?_ ?_ ?_ ?_
    · intro m hm
      obtain ⟨hm1, h10⟩ := Finset.mem_filter.mp hm
      have hdet : m.det = 1 := mem_sl2.mp hm1
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_univ _⟩
      show m 0 0 ≠ 0
      intro h0
      rw [h0, zero_mul] at hdet
      exact zero_ne_one hdet
    · intro w hw
      have hw1 : w.1 ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hw).1).2
      refine Finset.mem_filter.mpr ⟨mem_sl2.mpr ?_, ?_⟩
      · rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_inv_cancel₀ hw1]
      · simp
    · intro m hm
      obtain ⟨hm1, h10⟩ := Finset.mem_filter.mp hm
      have hdet : m.det = 1 := mem_sl2.mp hm1
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
      have h11 : (m 0 0)⁻¹ = m 1 1 := inv_eq_of_mul_eq_one_right hdet
      rw [h11, ← h10]
      exact (Matrix.eta_fin_two m).symm
    · intro w _
      simp
  rw [hbij, Finset.card_product, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  exact Nat.mul_comm _ _

/-- The big Bruhat cell count: `#{g ∈ SL₂ : g₁₀ ≠ 0} = p²·(p−1)` — the complement
    of the Borel cell inside the exact sphere volume. -/
theorem bruhat_cell_card {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    ((sl2 p).filter fun m => ¬ m 1 0 = 0).card = p ^ 2 * (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have htot := Finset.card_filter_add_card_filter_not (s := sl2 p)
    (fun m => m 1 0 = 0)
  rw [borel_card, sl2_card h2] at htot
  have hident : p * (p - 1) * (p + 1) = p ^ 2 * (p - 1) + p * (p - 1) := by ring
  omega

/-- The Bruhat subdivision recounts the sphere exactly:
    `|B| + |BwB| = p(p−1) + p²(p−1) = |SL₂|`. -/
theorem bruhat_decomposition {p : ℕ} [Fact p.Prime] (h2 : 2 < p) :
    p * (p - 1) + p ^ 2 * (p - 1) = (sl2 p).card := by
  rw [sl2_card h2]
  ring

/-! ### Axiom audit -/

#print axioms pair_mul_count_ne_zero
#print axioms pair_mul_count_zero
#print axioms pair_mul_count_int
#print axioms shifted_sq_count
#print axioms sq_count_int
#print axioms trace_fiber_card
#print axioms sum_chi_sq_sub_one
#print axioms sl2_card
#print axioms sphere_card
#print axioms quadToSL2_trace
#print axioms quadToSL2_mul
#print axioms quadToSL2_injective
#print axioms diagTorus
#print axioms diagTorus_injective
#print axioms sphereSum_eq_sl2
#print axioms sphereSum_eq_p_mul_kloos
#print axioms sphereSum_norm_le
#print axioms shearNegMat_eq_neg
#print axioms shearNegMat_pow_30
#print axioms shearNegMat_pow_15
#print axioms shearNeg_orderOf
#print axioms sphere_lucas_naive_refuted
#print axioms borel_card
#print axioms bruhat_cell_card
#print axioms bruhat_decomposition

end SphereTrace
end EuclidsPath
