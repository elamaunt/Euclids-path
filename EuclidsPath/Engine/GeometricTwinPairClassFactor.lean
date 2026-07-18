/-
  Engine/GeometricTwinPairClassFactor — wave-5 W5-2 brick (CLOSURE wave) of the
  binary-cancellation program: the PAIR PER-CLASS FACTORIZATION over `ZMod q`,
  the capstone of the rational-frequency layer of the four-cell object.

  ORIGIN (tools/RESEARCH_binary_cancellation.md, wave-4 ledger, refinement
  queue item "four-cell pair-version of ClassFactor").  Wave 4 proved that on
  `Omega <= 2` windows every SINGLE-WING class-weighted Liouville sum factors
  exactly through per-class (rough, prime) counts (`liouville_sum_classFactor`).
  This brick closes the layer at the PAIR level: with BOTH wing dichotomies in
  force, every mod-`q` weighted sum of the PRODUCT `λ(6m−1)·λ(6m+1)` factors
  exactly through per-class (count, prime−, prime+, twin) quadruples.

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `pair_cell_expand` — the pointwise cell algebra
      `(1 − 2·1_P)(1 − 2·1_Q) = 1 − 2·1_P − 2·1_Q + 4·1_{P∧Q}`;
    * `pair_liouville_sum_counts` — the `g = 1` reading: on any finite window
      with BOTH dichotomies pointwise (`Ω(6m−1), Ω(6m+1) ∈ {1,2}`),
        `Σ λ(6m−1)·λ(6m+1) = N − 2·P− − 2·P+ + 4·T`,
      the four-cell/T identity: `T = #{m : both 6m∓1 prime}` IS the twin
      count of the window;
    * `pair_liouville_sum_classFactor_map` / `pair_liouville_sum_classFactor`
      — THE MAIN THEOREM: for any `q ≠ 0` and any weight `g : ZMod q → ℤ`,
        `Σ_{m∈I} (λ(6m−1)·λ(6m+1))·g(m mod q)
           = Σ_{c : ZMod q} g(c)·(N_c − 2·P−_c − 2·P+_c + 4·T_c)`,
      where over the class-`c` fiber `I_c = I.filter (m ≡ c mod q)`:
      `N_c = |I_c|`, `P∓_c = #{m ∈ I_c : 6m∓1 prime}`, and
      `T_c = #{m ∈ I_c : BOTH 6m∓1 prime}` — the PER-CLASS TWIN COUNT.
      Every rational-frequency observation of the pair-Liouville object on a
      dichotomy window is per-class counting and NOTHING MORE;
    * `pairRoughWindow_classFactor` — the window corollary: on the pair-rough
      window (`pairRoughWindow X z = minusRoughWindow ∩ plusRoughWindow`,
      both `6m∓1` z-rough at the SAME `m`), with `z ≥ 1`, `X < z³`, both
      dichotomies are discharged from real arithmetic
      (`minusRoughWindow_omega` / `plusRoughWindow_omega` through the
      intersection), so the factorization holds UNCONDITIONALLY there;
      `pairRoughWindow_cross_counts` is its `g = 1` form — the exact
      four-cell/T identity on the pair-rough window.

  DISCLOSURES (mandatory reading before quoting).
    * COUNTING STRUCTURE ONLY.  Every statement is an exact finite identity;
      NOTHING is estimated, no size or sign of any per-class count is
      claimed.  At `g = 1` the theorem recovers the four-cell/T identity;
      the `T_c` term is the per-class twin count, and the theorem asserts
      only that the rational-frequency layer of the pair object IS this
      per-class bookkeeping — it carries NO information about how large
      `T_c` is.
    * NOTHING MOVES THE PARITY WALL.  The wall remains the single arrow
      `Chowla2LogHypothesis → Chowla2Hypothesis` (un-averaging), and no
      finite identity touches it.  No §110 event is claimed.
    * No new axioms, no sorry.  The twin sorry (`twin_prime_conjecture`) is
      untouched.  This file is NOT registered in `EuclidsPath.lean`.
-/
import EuclidsPath.Engine.GeometricTwinClassFactor
import EuclidsPath.Engine.GeometricTypeIIPlusWing

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators
open ArithmeticFunction

/-! ### (1) The pointwise pair-cell algebra -/

/-- **The pair-cell expansion**: for indicator values of two decidable
propositions, `(1 − 2·1_P)(1 − 2·1_Q) = 1 − 2·1_P − 2·1_Q + 4·1_{P∧Q}`. -/
theorem pair_cell_expand (P Q : Prop) [Decidable P] [Decidable Q] :
    (1 - 2 * (if P then (1 : ℤ) else 0)) * (1 - 2 * (if Q then (1 : ℤ) else 0))
      = 1 - 2 * (if P then (1 : ℤ) else 0) - 2 * (if Q then (1 : ℤ) else 0)
        + 4 * (if P ∧ Q then (1 : ℤ) else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- **The four-term count collapse**: summing the expanded cell over any
finite set turns the four indicator sums into the four counts
(total, `P`-count, `Q`-count, `P∧Q`-count). -/
theorem pair_count_expand (F : Finset ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    ∑ m ∈ F, ((1 : ℤ) - 2 * (if P m then (1 : ℤ) else 0)
        - 2 * (if Q m then (1 : ℤ) else 0)
        + 4 * (if P m ∧ Q m then (1 : ℤ) else 0))
      = (F.card : ℤ) - 2 * ((F.filter P).card : ℤ)
        - 2 * ((F.filter Q).card : ℤ)
        + 4 * ((F.filter fun m => P m ∧ Q m).card : ℤ) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]
  simp

/-! ### (2) The `g = 1` reading: the four-cell/T identity on dichotomy windows -/

/-- **The pair-Liouville count identity** (the `g = 1` four-cell/T reading):
on any finite window where BOTH wings satisfy the prime/semiprime dichotomy
pointwise,

`Σ_{m∈I} λ(6m−1)·λ(6m+1) = N − 2·P− − 2·P+ + 4·T`,

with `N = |I|`, `P∓` the wing prime counts, and `T` the TWIN count
(`both 6m∓1 prime`).  Exact bookkeeping; no estimate. -/
theorem pair_liouville_sum_counts (I : Finset ℕ)
    (hminus : ∀ m ∈ I, cardFactors (6 * m - 1) = 1 ∨ cardFactors (6 * m - 1) = 2)
    (hplus : ∀ m ∈ I, cardFactors (6 * m + 1) = 1 ∨ cardFactors (6 * m + 1) = 2) :
    ∑ m ∈ I, liouville (6 * m - 1) * liouville (6 * m + 1)
      = (I.card : ℤ) - 2 * ((I.filter fun m => (6 * m - 1).Prime).card : ℤ)
        - 2 * ((I.filter fun m => (6 * m + 1).Prime).card : ℤ)
        + 4 * ((I.filter fun m =>
            (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℤ) := by
  calc ∑ m ∈ I, liouville (6 * m - 1) * liouville (6 * m + 1)
      = ∑ m ∈ I, ((1 : ℤ) - 2 * (if (6 * m - 1).Prime then (1 : ℤ) else 0)
          - 2 * (if (6 * m + 1).Prime then (1 : ℤ) else 0)
          + 4 * (if (6 * m - 1).Prime ∧ (6 * m + 1).Prime
              then (1 : ℤ) else 0)) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [liouville_eq_on_dichotomy (hminus m hm),
          liouville_eq_on_dichotomy (hplus m hm), pair_cell_expand]
    _ = _ := pair_count_expand I _ _

/-! ### (3) THE MAIN THEOREM: the pair per-class factorization over `ZMod q` -/

/-- **The pair per-class factorization (mapped form).**  For any finite index
set `I`, any two wing maps `w₁ w₂` with the pointwise dichotomy on `I`, any
modulus `q ≠ 0`, and any class weight `g : ZMod q → ℤ`, the weighted
pair-Liouville sum factors EXACTLY through the per-class
(count, `w₁`-prime, `w₂`-prime, both-prime) quadruples.  The both-prime
fiber count is the per-class TWIN count when `w₁, w₂ = 6m∓1`. -/
theorem pair_liouville_sum_classFactor_map {q : ℕ} [NeZero q] (I : Finset ℕ)
    (w₁ w₂ : ℕ → ℕ)
    (h1 : ∀ m ∈ I, cardFactors (w₁ m) = 1 ∨ cardFactors (w₁ m) = 2)
    (h2 : ∀ m ∈ I, cardFactors (w₂ m) = 1 ∨ cardFactors (w₂ m) = 2)
    (g : ZMod q → ℤ) :
    ∑ m ∈ I, (liouville (w₁ m) * liouville (w₂ m)) * g ((m : ZMod q))
      = ∑ c : ZMod q, g c *
          (((I.filter fun m : ℕ => ((m : ZMod q)) = c).card : ℤ)
            - 2 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (w₁ m).Prime).card : ℤ)
            - 2 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (w₂ m).Prime).card : ℤ)
            + 4 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (w₁ m).Prime ∧ (w₂ m).Prime).card : ℤ)) := by
  refine ((Finset.sum_fiberwise I (fun m => ((m : ZMod q)))
      (fun m => (liouville (w₁ m) * liouville (w₂ m)) * g ((m : ZMod q)))).symm).trans
    (Finset.sum_congr rfl fun c _ => ?_)
  calc ∑ m ∈ I.filter (fun m : ℕ => ((m : ZMod q)) = c),
          (liouville (w₁ m) * liouville (w₂ m)) * g ((m : ZMod q))
      = ∑ m ∈ I.filter (fun m : ℕ => ((m : ZMod q)) = c),
          ((1 : ℤ) - 2 * (if (w₁ m).Prime then (1 : ℤ) else 0)
            - 2 * (if (w₂ m).Prime then (1 : ℤ) else 0)
            + 4 * (if (w₁ m).Prime ∧ (w₂ m).Prime then (1 : ℤ) else 0))
          * g c := by
        refine Finset.sum_congr rfl fun m hm => ?_
        obtain ⟨hmI, hnc⟩ := Finset.mem_filter.mp hm
        rw [hnc, liouville_eq_on_dichotomy (h1 m hmI),
          liouville_eq_on_dichotomy (h2 m hmI), pair_cell_expand]
    _ = (∑ m ∈ I.filter (fun m : ℕ => ((m : ZMod q)) = c),
          ((1 : ℤ) - 2 * (if (w₁ m).Prime then (1 : ℤ) else 0)
            - 2 * (if (w₂ m).Prime then (1 : ℤ) else 0)
            + 4 * (if (w₁ m).Prime ∧ (w₂ m).Prime then (1 : ℤ) else 0)))
          * g c := by
        rw [Finset.sum_mul]
    _ = (((I.filter fun m : ℕ => ((m : ZMod q)) = c).card : ℤ)
          - 2 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
              fun m => (w₁ m).Prime).card : ℤ)
          - 2 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
              fun m => (w₂ m).Prime).card : ℤ)
          + 4 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
              fun m => (w₁ m).Prime ∧ (w₂ m).Prime).card : ℤ)) * g c := by
        rw [pair_count_expand]
    _ = _ := mul_comm _ _

/-- **THE PAIR PER-CLASS FACTORIZATION** (main theorem, twin wings): on a
finite window with BOTH wing dichotomies pointwise, for any `q ≠ 0` and any
`g : ZMod q → ℤ`,

`Σ_{m∈I} (λ(6m−1)·λ(6m+1))·g(m mod q)
   = Σ_{c : ZMod q} g(c)·(N_c − 2·P−_c − 2·P+_c + 4·T_c)`,

where over the class-`c` fiber `I_c = I.filter (m ≡ c)`: `N_c = |I_c|`,
`P∓_c` are the wing prime counts, and `T_c` — the coefficient of `4` — IS
the PER-CLASS TWIN COUNT `#{m ∈ I_c : both 6m∓1 prime}`.  At `g = 1` this
recovers the four-cell/T identity (`pair_liouville_sum_counts`).  The
theorem asserts counting structure ONLY: the entire rational-frequency
layer of the pair object is per-class counting — no estimate on any term
is made or implied. -/
theorem pair_liouville_sum_classFactor {q : ℕ} [NeZero q] (I : Finset ℕ)
    (hminus : ∀ m ∈ I, cardFactors (6 * m - 1) = 1 ∨ cardFactors (6 * m - 1) = 2)
    (hplus : ∀ m ∈ I, cardFactors (6 * m + 1) = 1 ∨ cardFactors (6 * m + 1) = 2)
    (g : ZMod q → ℤ) :
    ∑ m ∈ I, (liouville (6 * m - 1) * liouville (6 * m + 1)) * g ((m : ZMod q))
      = ∑ c : ZMod q, g c *
          (((I.filter fun m : ℕ => ((m : ZMod q)) = c).card : ℤ)
            - 2 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (6 * m - 1).Prime).card : ℤ)
            - 2 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (6 * m + 1).Prime).card : ℤ)
            + 4 * (((I.filter fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℤ)) :=
  pair_liouville_sum_classFactor_map I (fun m => 6 * m - 1) (fun m => 6 * m + 1)
    hminus hplus g

/-! ### (4) The window corollary: the pair-rough window -/

/-- The PAIR-rough window: `m` in BOTH the minus rough window and the plus
rough window — both `6m∓1` lie in `(z, X]` and are `z`-rough at the SAME
`m`.  This is the window where the parity wall lives; here we only COUNT
on it. -/
def pairRoughWindow (X z : ℕ) : Finset ℕ :=
  minusRoughWindow X z ∩ plusRoughWindow X z

/-- The minus dichotomy on the pair-rough window, inherited from
`minusRoughWindow_omega` through the intersection. -/
theorem pairRoughWindow_omega_minus {X z : ℕ} (hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∀ m ∈ pairRoughWindow X z,
      cardFactors (6 * m - 1) = 1 ∨ cardFactors (6 * m - 1) = 2 :=
  fun m hm =>
    minusRoughWindow_omega hz hXz m (Finset.mem_of_mem_inter_left hm)

/-- The plus dichotomy on the pair-rough window, inherited from
`plusRoughWindow_omega` through the intersection. -/
theorem pairRoughWindow_omega_plus {X z : ℕ} (hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∀ m ∈ pairRoughWindow X z,
      cardFactors (6 * m + 1) = 1 ∨ cardFactors (6 * m + 1) = 2 :=
  fun m hm =>
    plusRoughWindow_omega hz hXz m (Finset.mem_of_mem_inter_right hm)

/-- **The pair per-class factorization on the pair-rough window**
(window corollary, unconditional): for `z ≥ 1` and `X < z³` — the regime
where BOTH dichotomies are discharged from real arithmetic — the mod-`q`
weighted pair-Liouville sum on the pair-rough window factors exactly
through per-class (count, prime−, prime+, twin) quadruples.  The `T_c`
coefficient is the per-class twin count of the pair-rough window; nothing
here estimates it. -/
theorem pairRoughWindow_classFactor {X z q : ℕ} [NeZero q]
    (hz : 1 ≤ z) (hXz : X < z ^ 3) (g : ZMod q → ℤ) :
    ∑ m ∈ pairRoughWindow X z,
        (liouville (6 * m - 1) * liouville (6 * m + 1)) * g ((m : ZMod q))
      = ∑ c : ZMod q, g c *
          ((((pairRoughWindow X z).filter
              fun m : ℕ => ((m : ZMod q)) = c).card : ℤ)
            - 2 * ((((pairRoughWindow X z).filter
                fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (6 * m - 1).Prime).card : ℤ)
            - 2 * ((((pairRoughWindow X z).filter
                fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (6 * m + 1).Prime).card : ℤ)
            + 4 * ((((pairRoughWindow X z).filter
                fun m : ℕ => ((m : ZMod q)) = c).filter
                fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℤ)) :=
  pair_liouville_sum_classFactor (pairRoughWindow X z)
    (pairRoughWindow_omega_minus hz hXz) (pairRoughWindow_omega_plus hz hXz) g

/-- **The `g = 1` form on the pair-rough window**: the exact four-cell/T
identity `Σ λλ = N − 2·P− − 2·P+ + 4·T` with `T` the twin count of the
pair-rough window.  Counting only; no estimate. -/
theorem pairRoughWindow_cross_counts {X z : ℕ} (hz : 1 ≤ z) (hXz : X < z ^ 3) :
    ∑ m ∈ pairRoughWindow X z, liouville (6 * m - 1) * liouville (6 * m + 1)
      = ((pairRoughWindow X z).card : ℤ)
        - 2 * (((pairRoughWindow X z).filter
            fun m => (6 * m - 1).Prime).card : ℤ)
        - 2 * (((pairRoughWindow X z).filter
            fun m => (6 * m + 1).Prime).card : ℤ)
        + 4 * (((pairRoughWindow X z).filter
            fun m => (6 * m - 1).Prime ∧ (6 * m + 1).Prime).card : ℤ) :=
  pair_liouville_sum_counts (pairRoughWindow X z)
    (pairRoughWindow_omega_minus hz hXz) (pairRoughWindow_omega_plus hz hXz)

end TypeII
end Geometric
end EuclidsPath
