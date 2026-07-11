/-
  Step00KloostermanMoment — the family fourth moment M4 of Kloosterman sums and the
  program's first machine-checked NONTRIVIAL POINTWISE CANCELLATION BOUND
  `‖kloos a b‖⁴ ≤ 2ℓ³`, i.e. `‖kloos a b‖ ≤ 2^{1/4}·ℓ^{3/4}` (Kloosterman 1926,
  fully elementary — COMPLETE sums only).

  Everything here is an EXACT FINITE IDENTITY or a one-step consequence of one: the
  bound is not an estimate imported from outside but the observation that one
  nonnegative term cannot exceed its family's exactly-computed fourth moment.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `kloos_zero_right` / `kloos_zero_zero` — the degenerate frequencies
      `kloos(a,0) = −1` (`a ≠ 0`) and `kloos(0,0) = ℓ − 1`, completing the boundary
      data of the M2 module's `kloos_zero`;
    * `kloosN4` / `kloos_family_fourth_full` — THE DOUBLE ORTHOGONALITY REDUCTION:
      `Σ_{a,b ∈ ZMod ℓ} kloos(a,b)²·kloos(−a,−b)² = ℓ²·N4`, where `N4` counts pairs
      of unit pairs sharing both symmetric keys `x + z` and `x⁻¹ + z⁻¹` — the M2
      engine one level up, both frequencies summed over the FULL group;
    * `kloosN4_card_int` / `kloosN4_card` — THE N4 COUNT: `N4 = 3(ℓ−1)(ℓ−2)`, by the
      blueprint's completeness spine: for `s = x + z ≠ 0` the keys force `yw = xz`
      (Vieta — `(y−x)(y−z) = 0`, fiber `{(x,z),(z,x)}`), for `s = 0` the inverse key
      is automatic (antipodal fiber `{(y,−y)}`, size `ℓ−1`);
    * `kloos_family_M4` / `kloos_family_M4_norm` — THE FAMILY FOURTH MOMENT:
      `Σ_{c ≠ 0} kloos(1,c)⁴ = Σ_{c ≠ 0} ‖kloos(1,c)‖⁴ = 2ℓ³ − 3ℓ² − 3ℓ − 1`
      (the diagonal family is real; every `kloos(a,b)` with `ab ≠ 0` is a member via
      `kloos_scale`, each member hit `ℓ − 1` times in the full double family);
    * `kloos_norm_le` — **THE CROWN**: `‖kloos a b‖⁴ ≤ 2ℓ³` for `a, b ≠ 0`.  The
      trivial bound is `ℓ − 1 ~ ℓ`; this is `2^{1/4}·ℓ^{3/4}` — the program's first
      machine-checked pointwise cancellation in an exponential sum.  Stated in
      fourth-power form over `ℝ` (no real fourth roots enter the statement);
    * `circleSum_norm_le` — the same bound for the circle's trigonometric sums
      through the bridge `circleSum u = −kloos(u/2, u/2)` of the energy module;
    * kernel demos: `n4CountN` (pure-Nat quadruple fold with Fermat inverses
      `t^(n−2) % n`), `n4CountN 5 = 36`, `n4CountN 7 = 90` by `decide`, with the
      Finset count evaluated to the SAME constants through `kloosN4_card`
      (agreement exhibited at the instances, not derived by a bijection — house
      kernel discipline; `ZMod` instances stay OUT of every decide path).

  NUMERIC GROUNDING (tools/circle_sum_run1.log, T1–T2 of the circle-sum pass):
  `M4 = 2ℓ³ − 3ℓ² − 3ℓ − 1` via `N4 = 3(ℓ−1)(ℓ−2)` was confirmed by exact integer
  assembly at all 302 odd primes ≤ 1999; the stratum decomposition (diagonal
  `(ℓ−1)²`, swap `(ℓ−1)(ℓ−2)`, antipodal `(ℓ−1)(ℓ−3)`), the key-side fiber counts,
  and the completeness spine were verified tuple-by-tuple for ℓ ≤ 31 and key-by-key
  at all 94 odd primes ≤ 500 (log lines 167–216).  The identities landed here are
  the Lean faces of that log; the Lean route follows the log's assembly
  `M4 = (ℓ²·N4 − 2(ℓ−1) − (ℓ−1)⁴)/(ℓ−1)` verbatim, with the χ-key-side table
  replaced by the equivalent Vieta fibers (the counts are identical; the character
  `χ` is not needed).

  DISCLOSURES (mandatory reading before quoting):
    * COMPLETE vs INCOMPLETE — THE WALL'S SIXTH COSTUME.  Every sum in this module is
      COMPLETE: over the full residue line, the full frequency plane, the full
      family.  The serial-twin wall lives on INCOMPLETE sums over windows.  The
      completed stage-D probe (tools/circle_sum_run1.log, T4) measured NO stable
      re-expression of defect-window pair-mode mass in complete Kloosterman data:
      the high-R² rows are interpolation artifacts of clustered census phases, the
      rest are unstable.  The complete/incomplete boundary is the same wall in its
      sixth costume (after the gap bound, the phase covers, the witness chains, the
      perpetual engine, and the parity barrier); nothing here claims to cross it.
    * NOT THE WEIL BOUND.  The pointwise Weil bound is `2√ℓ = 2·ℓ^{1/2}`; this module
      proves the WEAKER elementary `2^{1/4}·ℓ^{3/4}` (Kloosterman's original 1926
      exponent), with no cohomology and no claim beyond it.  The pinned mathlib
      contains no Weil bound and none is imported.
    * FOURTH-POWER FORM.  `kloos_norm_le` is stated as `‖kloos a b‖⁴ ≤ 2ℓ³`; the
      `2^{1/4}·ℓ^{3/4}` reading is the unique nonnegative fourth root, taken in
      prose only — no `Real.rpow` enters the module.
    * COUNTER AGREEMENT, NOT COUNTER EQUALITY.  `n4CountN` and `(kloosN4 ℓ).card`
      are shown to AGREE on the demo instances (both `36` resp. `90`); the general
      counting bijection between the Nat fold and the Finset filter is not
      formalized.

  ## Anti-vocabulary

  No claim in this file concerns windows, incomplete sums, densities, asymptotics,
  or the infinitude of anything.  Every theorem is an exact finite identity over a
  complete range or a single-term-versus-sum inequality derived from one; every
  kernel demo is a single verified instance.
-/
import Mathlib
import EuclidsPath.Engine.Step00CircleEnergy

set_option autoImplicit false

namespace EuclidsPath
namespace KloostermanMoment

open EuclidsPath.CircleEnergy

/-! ### Layer 1 — degenerate frequencies and the squared-sum expansion -/

/-- `2 ≠ 0` in `ZMod ℓ` for an odd prime `ℓ` (characteristic route; local twin of the
    private lemma in `Step00CircleEnergy`). -/
private theorem two_ne_zero_zmod {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (2 : ZMod ℓ) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)

/-- `Σ_{x ≠ 0} ψ(w·x) = −1` for `w ≠ 0`: the full-line sum vanishes by orthogonality
    and the zero term is `1` (the non-inverted twin of the M2 module's `sum_psi_inv`). -/
private theorem sum_psi_lin {ℓ : ℕ} [Fact ℓ.Prime] {w : ZMod ℓ} (hw : w ≠ 0) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar (w * x) = -1 := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun x : ZMod ℓ => ZMod.stdAddChar (w * x)) (Finset.mem_univ (0 : ZMod ℓ))
  have hall : ∑ x : ZMod ℓ, ZMod.stdAddChar (w * x) = 0 := by
    have h := AddChar.sum_mulShift w (ZMod.isPrimitive_stdAddChar ℓ)
    rw [if_neg hw, Nat.cast_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  rw [hall, mul_zero, AddChar.map_zero_eq_one] at hsplit
  rw [Finset.filter_ne']
  linear_combination hsplit

/-- `kloos a 0 = −1` for `a ≠ 0` — the second degenerate frequency (the mirror of the
    M2 module's `kloos_zero`); feeds the `b = 0` boundary stratum of the M4 assembly. -/
theorem kloos_zero_right {ℓ : ℕ} [Fact ℓ.Prime] {a : ZMod ℓ} (ha : a ≠ 0) :
    kloos a (0 : ZMod ℓ) = -1 := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar (a * x + (0 : ZMod ℓ) * x⁻¹) = ZMod.stdAddChar (a * x) :=
    fun x _ => by rw [zero_mul, add_zero]
  rw [kloos_def, Finset.sum_congr rfl h]
  exact sum_psi_lin ha

/-- `kloos 0 0 = ℓ − 1` — the doubly degenerate corner is the size of the punctured
    line; it feeds the `(0,0)` boundary stratum `(ℓ−1)⁴` of the M4 assembly. -/
theorem kloos_zero_zero {ℓ : ℕ} [Fact ℓ.Prime] :
    kloos (0 : ZMod ℓ) (0 : ZMod ℓ) = (ℓ : ℂ) - 1 := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0),
      ZMod.stdAddChar ((0 : ZMod ℓ) * x + (0 : ZMod ℓ) * x⁻¹) = 1 :=
    fun x _ => by rw [zero_mul, zero_mul, add_zero, AddChar.map_zero_eq_one]
  have hcard : (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)).card = ℓ - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  have h1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  rw [kloos_def, Finset.sum_congr rfl h, Finset.sum_const, hcard, nsmul_eq_mul,
    mul_one, Nat.cast_sub h1, Nat.cast_one]

/-- The diagonal family is REAL: `conj (kloos 1 c) = kloos 1 c` — through
    `kloos_conj` and the scaling law `kloos (−1) (−c) = kloos 1 ((−1)·(−c))`. -/
private theorem kloos_one_conj {ℓ : ℕ} [Fact ℓ.Prime] (c : ZMod ℓ) :
    (starRingEnd ℂ) (kloos (1 : ZMod ℓ) c) = kloos (1 : ZMod ℓ) c := by
  rw [kloos_conj, kloos_scale (neg_ne_zero.mpr one_ne_zero)]
  congr 1
  ring

/-- **The squared-sum expansion**: `kloos(a,b)² = Σ_{(x,z) ∈ U²} ψ(a(x+z) + b(x⁻¹+z⁻¹))`
    — the square of the Kloosterman sum as a single sum over ordered unit pairs, keyed
    by the two symmetric functions `e₁ = x + z` and `e₂ = x⁻¹ + z⁻¹` of the blueprint. -/
private theorem kloos_sq_expand {ℓ : ℕ} [Fact ℓ.Prime] (a b : ZMod ℓ) :
    kloos a b ^ 2
      = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
          (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ZMod.stdAddChar (a * (p.1 + p.2) + b * (p.1⁻¹ + p.2⁻¹)) := by
  rw [sq, kloos_def, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-! ### Layer 2 — the counting object N4 and the double orthogonality reduction -/

/-- **The N4 counting object** (blueprint T2, tools/circle_sum_run1.log:170):
    ordered pairs of ordered unit pairs `((x,z),(y,w)) ∈ (U²)²` with equal key pairs
    `x + z = y + w` and `x⁻¹ + z⁻¹ = y⁻¹ + w⁻¹` — the 4-tuple count whose value
    `3(ℓ−1)(ℓ−2)` is `kloosN4_card`.  (The blueprint's 4-tuples `(x,y,z,w)`,
    re-associated as pair-of-pairs; the count is identical.) -/
def kloosN4 (ℓ : ℕ) [NeZero ℓ] : Finset ((ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ)) :=
  (((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
      (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0))) ×ˢ
    ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
      (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)))).filter
    (fun r => r.1.1 + r.1.2 = r.2.1 + r.2.2
      ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹)

/-- **The double orthogonality reduction** (the M2 engine one level up, both
    frequencies summed over the FULL group):
    `Σ_{a,b ∈ ZMod ℓ} kloos(a,b)²·kloos(−a,−b)² = ℓ²·N4`.
    Route: expand each square over unit pairs (`kloos_sq_expand`), multiply, and
    collapse the two full-group character sums `Σ_a ψ(a·Δ₁)`, `Σ_b ψ(b·Δ₂)` by
    primitivity (`AddChar.sum_mulShift`) — each contributes `ℓ·[Δ = 0]`, leaving
    `ℓ²` times the N4 count.  This is line `Σ|kloos|⁴ = ℓ²·N4` of the blueprint
    assembly (tools/circle_sum_run1.log:194). -/
theorem kloos_family_fourth_full {ℓ : ℕ} [Fact ℓ.Prime] :
    ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, kloos a b ^ 2 * kloos (-a) (-b) ^ 2
      = (ℓ : ℂ) ^ 2 * ((kloosN4 ℓ).card : ℂ) := by
  calc ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, kloos a b ^ 2 * kloos (-a) (-b) ^ 2
      = ∑ a : ZMod ℓ, ∑ b : ZMod ℓ,
          ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
            ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
              + b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [kloos_sq_expand, kloos_sq_expand, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = ∑ a : ZMod ℓ,
          ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ b : ZMod ℓ,
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
            ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
              + b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ a : ZMod ℓ, ∑ b : ZMod ℓ,
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
            ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
              + b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))) := Finset.sum_comm
    _ = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ a : ZMod ℓ,
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ b : ZMod ℓ,
            ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
              + b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))) :=
        Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ a : ZMod ℓ, ∑ b : ZMod ℓ,
            ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
              + b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
            if (p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)
              then (ℓ : ℂ) ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        have h1 : ∑ a : ZMod ℓ, ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2)))
            = if p.1 + p.2 - (q.1 + q.2) = 0 then (ℓ : ℂ) else 0 := by
          rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar ℓ), ZMod.card,
            Nat.cast_ite, Nat.cast_zero]
        have h2 : ∑ b : ZMod ℓ,
            ZMod.stdAddChar (b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹)))
            = if p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹) = 0 then (ℓ : ℂ) else 0 := by
          rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar ℓ), ZMod.card,
            Nat.cast_ite, Nat.cast_zero]
        calc ∑ a : ZMod ℓ, ∑ b : ZMod ℓ,
            ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))
              + b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹)))
            = ∑ a : ZMod ℓ, ∑ b : ZMod ℓ,
                ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2)))
                  * ZMod.stdAddChar (b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹))) :=
              Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
                AddChar.map_add_eq_mul _ _ _
          _ = (∑ a : ZMod ℓ, ZMod.stdAddChar (a * (p.1 + p.2 - (q.1 + q.2))))
                * (∑ b : ZMod ℓ,
                    ZMod.stdAddChar (b * (p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹)))) :=
              (Finset.sum_mul_sum _ _ _ _).symm
          _ = (if p.1 + p.2 - (q.1 + q.2) = 0 then (ℓ : ℂ) else 0)
                * (if p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹) = 0 then (ℓ : ℂ) else 0) := by
              rw [h1, h2]
          _ = if (p.1 + p.2 = q.1 + q.2 ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)
                then (ℓ : ℂ) ^ 2 else 0 := by
              by_cases hc1 : p.1 + p.2 - (q.1 + q.2) = 0
              · by_cases hc2 : p.1⁻¹ + p.2⁻¹ - (q.1⁻¹ + q.2⁻¹) = 0
                · rw [if_pos hc1, if_pos hc2,
                    if_pos ⟨sub_eq_zero.mp hc1, sub_eq_zero.mp hc2⟩]
                  ring
                · have hnot : ¬(p.1 + p.2 = q.1 + q.2
                      ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹) :=
                    fun h => hc2 (sub_eq_zero.mpr h.2)
                  rw [if_pos hc1, if_neg hc2, if_neg hnot]
                  ring
              · have hnot : ¬(p.1 + p.2 = q.1 + q.2
                    ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹) :=
                  fun h => hc1 (sub_eq_zero.mpr h.1)
                rw [if_neg hc1, if_neg hnot, zero_mul]
    _ = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
          (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
            if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹)
              then (ℓ : ℂ) ^ 2 else 0) (p, q) := rfl
    _ = ∑ r ∈ ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0))) ×ˢ
          ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0))),
          if (r.1.1 + r.1.2 = r.2.1 + r.2.2
              ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹)
            then (ℓ : ℂ) ^ 2 else 0 :=
        (Finset.sum_product
          ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)))
          ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
            (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)))
          (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
            if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹)
              then (ℓ : ℂ) ^ 2 else 0)).symm
    _ = (ℓ : ℂ) ^ 2 * ((kloosN4 ℓ).card : ℂ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
          nsmul_eq_mul, mul_comm, kloosN4]

/-! ### Layer 3 — the three disjoint strata and N4 = 3(ℓ−1)(ℓ−2)

The blueprint's completeness spine (tools/circle_sum_run1.log:171–176): fix the left
pair `(x, z)` and count the right pairs `(y, w)` with the same keys.  If `s = x + z ≠ 0`
the key equations force `yw = xz` (Vieta), so `(y, w)` is one of the two orderings of
the root pair `{x, z}` — fiber size `2` off the diagonal, `1` on it.  If `s = 0` the
inverse-key equation is automatic and the fiber is the whole antipodal family
`{(y, −y)}` — size `ℓ − 1`.  Summing the fiber sizes over the `(ℓ−1)²` left pairs
gives the three strata I/II/III of the log and the total `3(ℓ−1)(ℓ−2)`. -/

/-- The punctured line has `ℓ − 1` points. -/
private theorem punct_card {ℓ : ℕ} [Fact ℓ.Prime] :
    (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)).card = ℓ - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]

/-- The antipodal stratum: unit pairs with `x + z = 0` are exactly `{(y, −y)}`,
    counted by the punctured line — `ℓ − 1` pairs (stratum III's frame and the
    `s = 0` fiber, in one count). -/
private theorem antipodal_card {ℓ : ℕ} [Fact ℓ.Prime] :
    (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => p.1 + p.2 = 0)).card = ℓ - 1 := by
  have hbij : (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => p.1 + p.2 = 0)).card
      = (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)).card := by
    refine Finset.card_bij' (fun p _ => p.1) (fun y _ => (y, -y)) ?_ ?_ ?_ ?_
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, neg_ne_zero.mpr hy0⟩
      · show y + -y = 0
        ring
    · intro p hp
      have hps : p.1 + p.2 = 0 := (Finset.mem_filter.mp hp).2
      have hp2 : p.2 = -p.1 := by linear_combination hps
      show (p.1, -p.1) = p
      rw [← hp2]
    · intro y _
      rfl
  rw [hbij, punct_card]

/-- The diagonal stratum: unit pairs with `x = z`, counted by the punctured line —
    `ℓ − 1` pairs (stratum I's double-root frame). -/
private theorem diag_card {ℓ : ℕ} [Fact ℓ.Prime] :
    (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => p.1 = p.2)).card = ℓ - 1 := by
  have hbij : (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => p.1 = p.2)).card
      = (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)).card := by
    refine Finset.card_bij' (fun p _ => p.1) (fun y _ => (y, y)) ?_ ?_ ?_ ?_
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩⟩, rfl⟩
    · intro p hp
      have hpd : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      show (p.1, p.1) = p
      nth_rewrite 2 [hpd]
      rfl
    · intro y _
      rfl
  rw [hbij, punct_card]

/-- **The Vieta fiber (the completeness spine, `s ≠ 0` branch)**: for a unit pair
    `(x, z)` with `x + z ≠ 0`, the unit pairs `(y, w)` sharing both keys
    `y + w = x + z` and `y⁻¹ + w⁻¹ = x⁻¹ + z⁻¹` are EXACTLY the two orderings
    `{(x, z), (z, x)}`.  Route: the key equations force `yw = xz` (cancel `x + z`),
    so `y² − (x+z)y + xz = 0`, i.e. `(y − x)(y − z) = 0` — `y` is a root of the same
    monic quadratic, and `w` is then pinned by the sum. -/
private theorem fiber_of_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] {x z : ZMod ℓ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hs : x + z ≠ 0) :
    ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun q => x + z = q.1 + q.2 ∧ x⁻¹ + z⁻¹ = q.1⁻¹ + q.2⁻¹)
      = {(x, z), (z, x)} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hq1, hq2⟩, he1, he2⟩
    have hx1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    have hz1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    have hq11 : q.1 * q.1⁻¹ = 1 := mul_inv_cancel₀ hq1
    have hq21 : q.2 * q.2⁻¹ = 1 := mul_inv_cancel₀ hq2
    have hA : (x⁻¹ + z⁻¹) * (x * z) = z + x := by
      linear_combination z * hx1 + x * hz1
    have hB : (q.1⁻¹ + q.2⁻¹) * (q.1 * q.2) = q.2 + q.1 := by
      linear_combination q.2 * hq11 + q.1 * hq21
    have hs' : x⁻¹ + z⁻¹ ≠ 0 := by
      intro h0
      apply hs
      have hA0 := hA
      rw [h0, zero_mul] at hA0
      linear_combination -hA0
    have hprod : q.1 * q.2 = x * z := by
      apply mul_left_cancel₀ hs'
      calc (x⁻¹ + z⁻¹) * (q.1 * q.2)
          = (q.1⁻¹ + q.2⁻¹) * (q.1 * q.2) := by rw [he2]
        _ = q.2 + q.1 := hB
        _ = x + z := by linear_combination -he1
        _ = (x⁻¹ + z⁻¹) * (x * z) := by linear_combination -hA
    have hviet : (q.1 - x) * (q.1 - z) = 0 := by
      linear_combination (-q.1) * he1 - hprod
    rcases mul_eq_zero.mp hviet with h | h
    · exact Or.inl (Prod.ext_iff.mpr
        ⟨by linear_combination h, by linear_combination -he1 - h⟩)
    · exact Or.inr (Prod.ext_iff.mpr
        ⟨by linear_combination h, by linear_combination -he1 - h⟩)
  · rintro (h | h) <;> subst h
    · exact ⟨⟨hx, hz⟩, rfl, rfl⟩
    · exact ⟨⟨hz, hx⟩, add_comm x z, add_comm x⁻¹ z⁻¹⟩

/-- **The antipodal fiber (the completeness spine, `s = 0` branch)**: for a unit pair
    `(x, z)` with `x + z = 0`, the inverse-key equation is automatic
    (`x⁻¹ + z⁻¹ = 0` and `y⁻¹ + (−y)⁻¹ = 0`), so the fiber is the full antipodal
    stratum `{(y, −y)}`. -/
private theorem fiber_of_zero {ℓ : ℕ} [Fact ℓ.Prime] {x z : ZMod ℓ}
    (hs : x + z = 0) :
    ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun q => x + z = q.1 + q.2 ∧ x⁻¹ + z⁻¹ = q.1⁻¹ + q.2⁻¹)
      = ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun q => q.1 + q.2 = 0) := by
  have hz : z = -x := by linear_combination hs
  have hinv : x⁻¹ + z⁻¹ = 0 := by
    rw [hz, inv_neg]
    ring
  refine Finset.filter_congr fun q _ => ?_
  constructor
  · rintro ⟨h1, _⟩
    rw [← h1]
    exact hs
  · intro h0
    have hq2 : q.2 = -q.1 := by linear_combination h0
    constructor
    · rw [hs, h0]
    · rw [hinv, hq2, inv_neg]
      ring

/-- **THE N4 COUNT** (blueprint T2, verified exactly at all 94 odd primes ≤ 500):
    `N4 = 3(ℓ−1)(ℓ−2)`, over `ℤ`.  Route: fiber the count over the left pair; the
    `s = 0` pairs (`ℓ−1` of them) carry fibers of size `ℓ−1` (stratum count
    `(ℓ−1)²` — the blueprint's stratum I frame re-fibered), the diagonal pairs carry
    fibers of size `1` (`ℓ−1`), the remaining `(ℓ−1)(ℓ−3)` pairs carry fibers of
    size `2`; total `3(ℓ−1)(ℓ−2)` (blueprint line CROSS,
    tools/circle_sum_run1.log:192). -/
theorem kloosN4_card_int {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ((kloosN4 ℓ).card : ℤ) = 3 * ((ℓ : ℤ) - 1) * ((ℓ : ℤ) - 2) := by
  have h1 : 1 ≤ ℓ := by omega
  -- the count, fibered over the left pair
  have hcount : (kloosN4 ℓ).card
      = ∑ p ∈ (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
          (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)),
        (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
            (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
          (fun q => p.1 + p.2 = q.1 + q.2
            ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card := by
    calc (kloosN4 ℓ).card
        = ∑ r ∈ ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
              (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0))) ×ˢ
            ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
              (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0))),
            if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹) then 1 else 0 := by
          rw [kloosN4, Finset.card_filter]
      _ = ∑ p ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
              (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
            ∑ q ∈ (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
              (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)),
            (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
              if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                  ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹) then 1 else 0)
              (p, q) :=
          Finset.sum_product
            ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
              (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)))
            ((Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)) ×ˢ
              (Finset.univ.filter (fun x : ZMod ℓ => x ≠ 0)))
            (fun r : (ZMod ℓ × ZMod ℓ) × (ZMod ℓ × ZMod ℓ) =>
              if (r.1.1 + r.1.2 = r.2.1 + r.2.2
                  ∧ r.1.1⁻¹ + r.1.2⁻¹ = r.2.1⁻¹ + r.2.2⁻¹) then 1 else 0)
      _ = ∑ p ∈ (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
              (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)),
            (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
                (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
              (fun q => p.1 + p.2 = q.1 + q.2
                ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card :=
          Finset.sum_congr rfl fun p _ =>
            (Finset.card_filter
              (fun q : ZMod ℓ × ZMod ℓ => p.1 + p.2 = q.1 + q.2
                ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹) _).symm
  -- split over the antipodal condition on the left pair
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
      (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)))
    (fun p => p.1 + p.2 = 0)
    (fun p => (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun q => p.1 + p.2 = q.1 + q.2
        ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card)
  -- the antipodal part: (ℓ−1) left pairs, each with fiber ℓ−1
  have hpart1 : ∑ p ∈ (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => p.1 + p.2 = 0)),
      (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
          (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun q => p.1 + p.2 = q.1 + q.2
          ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card = (ℓ - 1) * (ℓ - 1) := by
    have hconst : ∀ p ∈ (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
          (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun p => p.1 + p.2 = 0)),
        (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
            (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
          (fun q => p.1 + p.2 = q.1 + q.2
            ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card = ℓ - 1 := by
      intro p hp
      rw [fiber_of_zero (Finset.mem_filter.mp hp).2, antipodal_card]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, antipodal_card,
      smul_eq_mul]
  -- the diagonal-inside-nonantipodal card
  have hB : ((((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => ¬(p.1 + p.2 = 0))).filter (fun p => p.1 = p.2)).card = ℓ - 1 := by
    rw [Finset.filter_filter]
    have heq : ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun p => ¬(p.1 + p.2 = 0) ∧ p.1 = p.2)
        = ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun p => p.1 = p.2) := by
      refine Finset.filter_congr fun p hp => ?_
      have hp1 : p.1 ≠ 0 :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      constructor
      · exact fun h => h.2
      · intro hd
        refine ⟨fun h0 => hp1 ?_, hd⟩
        have h2x : (2 : ZMod ℓ) * p.1 = 0 := by linear_combination h0 + hd
        rcases mul_eq_zero.mp h2x with h | h
        · exact absurd h (two_ne_zero_zmod h2)
        · exact h
    rw [heq, diag_card]
  -- the non-antipodal part: fiber 1 on the diagonal, 2 off it
  have hpart2 : ∑ p ∈ (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
        (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
      (fun p => ¬(p.1 + p.2 = 0))),
      (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
          (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun q => p.1 + p.2 = q.1 + q.2
          ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card
      = (ℓ - 1) * 1
        + ((((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
            (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
          (fun p => ¬(p.1 + p.2 = 0))).filter
            (fun p => ¬(p.1 = p.2))).card * 2 := by
    have hconst : ∀ p ∈ (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
          (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun p => ¬(p.1 + p.2 = 0))),
        (((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
            (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
          (fun q => p.1 + p.2 = q.1 + q.2
            ∧ p.1⁻¹ + p.2⁻¹ = q.1⁻¹ + q.2⁻¹)).card
          = if p.1 = p.2 then 1 else 2 := by
      intro p hp
      have hpm := (Finset.mem_filter.mp hp).1
      have hps : ¬(p.1 + p.2 = 0) := (Finset.mem_filter.mp hp).2
      have hp1 : p.1 ≠ 0 :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hpm).1).2
      have hp2 : p.2 ≠ 0 :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hpm).2).2
      rw [fiber_of_ne_zero hp1 hp2 hps]
      by_cases hd : p.1 = p.2
      · rw [if_pos hd, hd,
          Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
          Finset.card_singleton]
      · rw [if_neg hd]
        refine Finset.card_pair ?_
        intro hEq
        exact hd (congrArg Prod.fst hEq)
    rw [Finset.sum_congr rfl hconst, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, smul_eq_mul, smul_eq_mul, hB]
  -- partition cardinalities
  have hApart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
      (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)))
    (fun p => p.1 + p.2 = 0)
  have hCpart := Finset.card_filter_add_card_filter_not
    (s := ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
      (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
        (fun p => ¬(p.1 + p.2 = 0)))
    (fun p => p.1 = p.2)
  have hUUcard : ((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
      (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).card
      = (ℓ - 1) * (ℓ - 1) := by
    rw [Finset.card_product, punct_card]
  rw [antipodal_card, hUUcard] at hApart
  rw [hB] at hCpart
  -- the master equation over ℕ, then the ℤ assembly
  have hNat : (kloosN4 ℓ).card
      = (ℓ - 1) * (ℓ - 1) + ((ℓ - 1) * 1
        + ((((Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0)) ×ˢ
            (Finset.univ.filter (fun t : ZMod ℓ => t ≠ 0))).filter
          (fun p => ¬(p.1 + p.2 = 0))).filter
            (fun p => ¬(p.1 = p.2))).card * 2) := by
    rw [hcount, ← hsplit, hpart1, hpart2]
  zify [h1] at hNat hApart hCpart
  linear_combination hNat + 2 * hApart + 2 * hCpart

/-- The N4 count over `ℕ` (blueprint totals: `36` at `ℓ = 5`, `90` at `ℓ = 7`,
    `2610` at `ℓ = 31` — tools/circle_sum_run1.log:203–212). -/
theorem kloosN4_card {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    (kloosN4 ℓ).card = 3 * (ℓ - 1) * (ℓ - 2) := by
  have h1 : 1 ≤ ℓ := by omega
  have h2' : 2 ≤ ℓ := by omega
  zify [h1, h2']
  exact kloosN4_card_int h2

/-! ### Layer 4 — the assembly: the family fourth moment M4 -/

/-- **THE FAMILY FOURTH MOMENT M4** (blueprint assembly,
    tools/circle_sum_run1.log:193–198; value confirmed exactly at all 302 odd primes
    ≤ 1999):  `Σ_{c ≠ 0} kloos(1,c)⁴ = 2ℓ³ − 3ℓ² − 3ℓ − 1`.
    Route: the double orthogonality `Σ_{a,b} kloos(a,b)²·kloos(−a,−b)² = ℓ²·N4`
    (`kloos_family_fourth_full`), minus the boundary strata — `(ℓ−1)⁴` at `(0,0)`
    and `1` at each of the `2(ℓ−1)` half-degenerate frequencies — leaves the
    interior `a,b ≠ 0`, which covers each diagonal member `kloos(1, ab)` exactly
    `ℓ − 1` times (`kloos_scale`); cancel `ℓ − 1` and substitute
    `N4 = 3(ℓ−1)(ℓ−2)`. -/
theorem kloos_family_M4 {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ c ∈ Finset.univ.erase (0 : ZMod ℓ), kloos 1 c ^ 4
      = 2 * (ℓ : ℂ) ^ 3 - 3 * (ℓ : ℂ) ^ 2 - 3 * (ℓ : ℂ) - 1 := by
  have h1 : 1 ≤ ℓ := by omega
  have hcard_erase : (Finset.univ.erase (0 : ZMod ℓ)).card = ℓ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hcast : ((ℓ - 1 : ℕ) : ℂ) = (ℓ : ℂ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  -- boundary values
  have h00 : kloos (0 : ZMod ℓ) 0 ^ 2 * kloos (-0 : ZMod ℓ) (-0 : ZMod ℓ) ^ 2
      = ((ℓ : ℂ) - 1) ^ 4 := by
    rw [neg_zero, kloos_zero_zero]
    ring
  have haval : ∀ a ∈ Finset.univ.erase (0 : ZMod ℓ),
      kloos a (0 : ZMod ℓ) ^ 2 * kloos (-a) (-0 : ZMod ℓ) ^ 2 = 1 := by
    intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    rw [neg_zero, kloos_zero_right ha0, kloos_zero_right (neg_ne_zero.mpr ha0)]
    ring
  have h0bval : ∀ b ∈ Finset.univ.erase (0 : ZMod ℓ),
      kloos (0 : ZMod ℓ) b ^ 2 * kloos (-0 : ZMod ℓ) (-b) ^ 2 = 1 := by
    intro b hb
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    rw [neg_zero, kloos_zero hb0, kloos_zero (neg_ne_zero.mpr hb0)]
    ring
  -- the interior: each nonzero row is the SAME diagonal family (kloos_scale)
  have hbval : ∀ a ∈ Finset.univ.erase (0 : ZMod ℓ),
      ∑ b ∈ Finset.univ.erase (0 : ZMod ℓ), kloos a b ^ 2 * kloos (-a) (-b) ^ 2
        = ∑ c ∈ Finset.univ.erase (0 : ZMod ℓ), kloos 1 c ^ 4 := by
    intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hterm : ∀ b ∈ Finset.univ.erase (0 : ZMod ℓ),
        kloos a b ^ 2 * kloos (-a) (-b) ^ 2 = kloos 1 (a * b) ^ 4 := by
      intro b _
      rw [kloos_scale ha0 b, kloos_scale (neg_ne_zero.mpr ha0) (-b), neg_mul_neg]
      ring
    rw [Finset.sum_congr rfl hterm]
    refine Finset.sum_nbij' (fun b => a * b) (fun c => a⁻¹ * c) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      exact Finset.mem_erase.mpr
        ⟨mul_ne_zero ha0 (Finset.mem_erase.mp hb).1, Finset.mem_univ _⟩
    · intro c hc
      exact Finset.mem_erase.mpr
        ⟨mul_ne_zero (inv_ne_zero ha0) (Finset.mem_erase.mp hc).1,
          Finset.mem_univ _⟩
    · intro b _
      rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    · intro c _
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    · intro b _
      rfl
  -- split the full double family into boundary + interior
  have hinner : ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, kloos a b ^ 2 * kloos (-a) (-b) ^ 2
      = (∑ a : ZMod ℓ, kloos a (0 : ZMod ℓ) ^ 2 * kloos (-a) (-0 : ZMod ℓ) ^ 2)
        + ∑ a : ZMod ℓ, ∑ b ∈ Finset.univ.erase (0 : ZMod ℓ),
            kloos a b ^ 2 * kloos (-a) (-b) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.add_sum_erase Finset.univ
      (fun b : ZMod ℓ => kloos a b ^ 2 * kloos (-a) (-b) ^ 2)
      (Finset.mem_univ 0)).symm
  have hsplitA := Finset.add_sum_erase Finset.univ
    (fun a : ZMod ℓ => kloos a (0 : ZMod ℓ) ^ 2 * kloos (-a) (-0 : ZMod ℓ) ^ 2)
    (Finset.mem_univ (0 : ZMod ℓ))
  rw [h00, Finset.sum_congr rfl haval, Finset.sum_const, hcard_erase,
    nsmul_eq_mul, mul_one, hcast] at hsplitA
  have hsplitB := Finset.add_sum_erase Finset.univ
    (fun a : ZMod ℓ => ∑ b ∈ Finset.univ.erase (0 : ZMod ℓ),
      kloos a b ^ 2 * kloos (-a) (-b) ^ 2)
    (Finset.mem_univ (0 : ZMod ℓ))
  rw [Finset.sum_congr rfl h0bval, Finset.sum_const, hcard_erase,
    nsmul_eq_mul, mul_one, hcast, Finset.sum_congr rfl hbval, Finset.sum_const,
    hcard_erase, nsmul_eq_mul, hcast] at hsplitB
  -- assemble and cancel ℓ − 1
  have hN4 : ((kloosN4 ℓ).card : ℂ) = 3 * ((ℓ : ℂ) - 1) * ((ℓ : ℂ) - 2) := by
    exact_mod_cast kloosN4_card_int (ℓ := ℓ) h2
  have hassemble : (ℓ : ℂ) ^ 2 * ((kloosN4 ℓ).card : ℂ)
      = (((ℓ : ℂ) - 1) ^ 4 + ((ℓ : ℂ) - 1)) + (((ℓ : ℂ) - 1)
          + ((ℓ : ℂ) - 1) * ∑ c ∈ Finset.univ.erase (0 : ZMod ℓ),
              kloos 1 c ^ 4) := by
    rw [← kloos_family_fourth_full, hinner, ← hsplitA, ← hsplitB]
  have hne : (ℓ : ℂ) - 1 ≠ 0 := by
    intro h0
    have hl1 : (ℓ : ℂ) = 1 := by linear_combination h0
    have hl1' : ℓ = 1 := by exact_mod_cast hl1
    omega
  apply mul_left_cancel₀ hne
  linear_combination -hassemble + (ℓ : ℂ) ^ 2 * hN4

/-- The `‖·‖⁴`-corollary of M4 over `ℝ`:
    `Σ_{c ≠ 0} ‖kloos(1,c)‖⁴ = 2ℓ³ − 3ℓ² − 3ℓ − 1` — the diagonal family is real
    (`conj (kloos 1 c) = kloos 1 c` through `kloos_conj` + `kloos_scale`), so its
    fourth power IS the fourth power of the norm. -/
theorem kloos_family_M4_norm {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) :
    ∑ c ∈ Finset.univ.erase (0 : ZMod ℓ), ‖kloos 1 c‖ ^ 4
      = 2 * (ℓ : ℝ) ^ 3 - 3 * (ℓ : ℝ) ^ 2 - 3 * (ℓ : ℝ) - 1 := by
  have hsq : ∀ c : ZMod ℓ, ((‖kloos 1 c‖ ^ 4 : ℝ) : ℂ) = kloos 1 c ^ 4 := by
    intro c
    have h2c : kloos 1 c * (starRingEnd ℂ) (kloos 1 c)
        = ((‖kloos 1 c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2c' : kloos 1 c ^ 2 = ((‖kloos 1 c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h2c, kloos_one_conj]
      ring
    calc ((‖kloos 1 c‖ ^ 4 : ℝ) : ℂ)
        = (((‖kloos 1 c‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
          push_cast
          ring
      _ = (kloos 1 c ^ 2) ^ 2 := by rw [h2c']
      _ = kloos 1 c ^ 4 := by ring
  have key : ∑ c ∈ Finset.univ.erase (0 : ZMod ℓ), ((‖kloos 1 c‖ ^ 4 : ℝ) : ℂ)
      = 2 * (ℓ : ℂ) ^ 3 - 3 * (ℓ : ℂ) ^ 2 - 3 * (ℓ : ℂ) - 1 :=
    (Finset.sum_congr rfl fun c _ => hsq c).trans (kloos_family_M4 h2)
  exact_mod_cast key

/-! ### Layer 5 — THE POINTWISE CANCELLATION BOUND -/

/-- **THE POINTWISE CANCELLATION BOUND** (Kloosterman 1926, fully elementary):
    `‖kloos a b‖⁴ ≤ 2ℓ³` for `a, b ≠ 0` — i.e. `‖kloos a b‖ ≤ 2^{1/4}·ℓ^{3/4}`.
    The trivial bound is `ℓ − 1`; this is the program's first machine-checked
    NONTRIVIAL pointwise cancellation: one nonnegative term of the fourth-moment
    family cannot exceed the whole family sum `2ℓ³ − 3ℓ² − 3ℓ − 1 < 2ℓ³`.
    Stated in fourth-power form (no real fourth roots needed).  COMPLETE sums only —
    see the module disclosures. -/
theorem kloos_norm_le {ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ) {a b : ZMod ℓ}
    (ha : a ≠ 0) (hb : b ≠ 0) : ‖kloos a b‖ ^ 4 ≤ 2 * (ℓ : ℝ) ^ 3 := by
  have hmem : a * b ∈ Finset.univ.erase (0 : ZMod ℓ) :=
    Finset.mem_erase.mpr ⟨mul_ne_zero ha hb, Finset.mem_univ _⟩
  have hle : ‖kloos 1 (a * b)‖ ^ 4
      ≤ ∑ c ∈ Finset.univ.erase (0 : ZMod ℓ), ‖kloos 1 c‖ ^ 4 :=
    Finset.single_le_sum (f := fun c => ‖kloos 1 c‖ ^ 4)
      (fun c _ => by positivity) hmem
  rw [kloos_scale ha b]
  refine hle.trans ?_
  rw [kloos_family_M4_norm h2]
  nlinarith [sq_nonneg ((ℓ : ℝ)), Nat.cast_nonneg (α := ℝ) ℓ]

/-- **The circle-sum cancellation bound**: `‖circleSum d u‖⁴ ≤ 2ℓ³` for `u ≠ 0` —
    the pointwise bound transported to the circle's trigonometric sums through the
    Kloosterman bridge `circleSum u = −kloos(u/2, u/2)` of the energy module. -/
theorem circleSum_norm_le {d ℓ : ℕ} [Fact ℓ.Prime] (h2 : 2 < ℓ)
    (hd : ¬ IsSquare ((d : ZMod ℓ))) {u : ZMod ℓ} (hu : u ≠ 0) :
    ‖circleSum d u‖ ^ 4 ≤ 2 * (ℓ : ℝ) ^ 3 := by
  have h20 : (2 : ZMod ℓ) ≠ 0 := two_ne_zero_zmod h2
  have hu2 : u * (2 : ZMod ℓ)⁻¹ ≠ 0 := mul_ne_zero hu (inv_ne_zero h20)
  rw [circleSum_eq_neg_kloos h2 hd hu, norm_neg]
  exact kloos_norm_le h2 hu2 hu2

/-! ### Layer 6 — kernel demo (pure-Nat fold; `ZMod`/`Quad` instances stay OUT of
every decide path — house kernel discipline) -/

/-- Pure-Nat N4 counter: 4-tuples `(x, y, z, w)` of nonzero residues mod `n` with
    `x + z ≡ y + w` and `x⁻¹ + z⁻¹ ≡ y⁻¹ + w⁻¹`, the inverse taken as `t^(n−2) % n`
    (Fermat — valid for prime `n`).  The Nat clothing of `(kloosN4 ℓ).card`. -/
def n4CountN (n : ℕ) : ℕ :=
  ((List.range n).map fun x =>
    ((List.range n).map fun y =>
      ((List.range n).map fun z =>
        ((List.range n).filter fun w =>
          x ≠ 0 && y ≠ 0 && z ≠ 0 && w ≠ 0
            && (x + z) % n == (y + w) % n
            && (x ^ (n - 2) % n + z ^ (n - 2) % n) % n
                == (y ^ (n - 2) % n + w ^ (n - 2) % n) % n).length).sum).sum).sum

/-- Kernel N4 count at `ℓ = 5`: `36 = 3·4·3` (blueprint row `l = 5`,
    tools/circle_sum_run1.log:204). -/
theorem n4CountN_5 : n4CountN 5 = 36 := by decide

/-- Kernel N4 count at `ℓ = 7`: `90 = 3·6·5` (blueprint row `l = 7`,
    tools/circle_sum_run1.log:205). -/
theorem n4CountN_7 : n4CountN 7 = 90 := by decide

/-- Agreement plaque: the Finset count through `kloosN4_card` gives the SAME
    constants at both demo instances (exhibited through the closed form, not by a
    counting bijection — house discipline, disclosed in the header). -/
theorem n4Count_agreement :
    (kloosN4 5).card = n4CountN 5 ∧ (kloosN4 7).card = n4CountN 7 := by
  haveI h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [n4CountN_5, n4CountN_7, kloosN4_card (by norm_num), kloosN4_card (by norm_num)]
  exact ⟨rfl, rfl⟩

/-! ### Axiom audit -/

#print axioms kloos_zero_right
#print axioms kloos_zero_zero
#print axioms kloos_family_fourth_full
#print axioms kloosN4_card_int
#print axioms kloosN4_card
#print axioms kloos_family_M4
#print axioms kloos_family_M4_norm
#print axioms kloos_norm_le
#print axioms circleSum_norm_le
#print axioms n4CountN_5
#print axioms n4CountN_7
#print axioms n4Count_agreement

end KloostermanMoment
end EuclidsPath
