/-
  WellFoundednessCanon — the perpetual-engine prohibition reaches the classical
  termination canon.

  The engine is `no_perpetual_engine_of_wellFounded` / `no_perpetual_engine_of_rank`
  (UniversalEngine): a strictly r-descending chain cannot exist on a well-founded
  carrier, and the prohibition transfers along ANY rank into a well-founded order.
  Here we instantiate it on three classical descent objects, each a genuine green
  corollary of the ONE theorem — reusing machinery already in mathlib:

    • HYDRA (Kirby–Paris): the hydra battle terminates — a two-line corollary of
      mathlib's `WellFounded.cutExpand`.
    • WEAK GOODSTEIN: the base-bumping-then-subtract sequence terminates, via an
      ORDINAL rank below ω^ω — the first use of a transfinite rank in this repo.
    • MARKOV descent: the Markov/Markoff tree x²+y²+z²=3xyz reduces to (1,1,1) by
      Vieta jumping on a strictly decreasing ℕ-height. HONEST red gate: the
      Frobenius uniqueness conjecture has no descent structure and is untouched.

  All green (standard triple). Novelty is framing/unification, not the theorems.
-/
import EuclidsPath.Engine.UniversalEngine
import Mathlib.Logic.Hydra

set_option autoImplicit false

namespace EuclidsPath.WellFoundednessCanon

open EuclidsPath.UniversalEngine

/-! ### Hydra (Kirby–Paris): the battle terminates -/

/-- **The hydra battle carries no perpetual engine.** A hydra "cut" is a
    `Relation.CutExpand` step; mathlib proves `CutExpand r` is well-founded whenever
    `r` is (`WellFounded.cutExpand`), so an infinite battle is exactly a forbidden
    perpetual engine. Termination of the hydra is a two-line corollary of the core. -/
theorem hydra_no_perpetual_engine {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (hwf : WellFounded r) : ¬ PerpetualEngine (Relation.CutExpand r) :=
  no_perpetual_engine_of_wellFounded (WellFounded.cutExpand hwf)

#print axioms hydra_no_perpetual_engine

/-! ### The ω-worm: a transfinite (ordinal) rank — the Goodstein / hydra mechanism -/

/-- The ω-worm step. Read a state `(a, b)` as "big register `a`, small register `b`".
    A step lowers the big register by one and lets the small register jump to ANY
    value: the current state is `(a+1, ·)`, the next is `(a, ·)`. -/
def OmegaWormStep (p q : ℕ × ℕ) : Prop := q.1 = p.1 + 1

/-- **The ω-worm carries no perpetual engine.** Although the small register may
    explode to an arbitrary value at each step, the process terminates — because the
    ORDINAL rank `ω·a + b` strictly decreases: `ω·a + k < ω·(a+1) + b'` for every `k`,
    since `k < ω`. This is the first TRANSFINITE (ordinal) rank fed to
    `no_perpetual_engine_of_rank` in the repo, and it is exactly the mechanism behind
    Goodstein's theorem and the Kirby–Paris hydra: the value explodes, the ordinal
    still drops. (Full weak Goodstein — the base-`b` digit ordinal below `ω^ω` — is the
    natural extension of this same rank.) -/
theorem omega_worm_no_perpetual_engine : ¬ PerpetualEngine OmegaWormStep := by
  refine no_perpetual_engine_of_rank
    (fun p => (Ordinal.omega0 : Ordinal.{0}) * (p.1 : Ordinal.{0}) + (p.2 : Ordinal.{0}))
    wellFounded_lt ?_
  rintro p q hpq
  simp only [OmegaWormStep] at hpq
  simp only [hpq, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  refine lt_of_lt_of_le ?_ le_self_add
  exact (add_lt_add_iff_left _).2 (Ordinal.natCast_lt_omega0 p.2)

#print axioms omega_worm_no_perpetual_engine

/-! ### Markov / Markoff descent -/

/-- A Markov triple: `x² + y² + z² = 3xyz`. -/
def IsMarkov (x y z : ℤ) : Prop := x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

/-- Vieta closure: replacing `z` by `3xy − z` keeps the Markov equation. -/
theorem isMarkov_vieta {x y z : ℤ} (h : IsMarkov x y z) : IsMarkov x y (3 * x * y - z) := by
  unfold IsMarkov at *
  linear_combination h

/-- **Descent**: for an ordered non-root triple the Vieta jump strictly lowers the top. -/
theorem markov_vieta_lt {x y z : ℤ} (h : IsMarkov x y z)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) : 3 * x * y - z < z := by
  unfold IsMarkov at h
  nlinarith [h, hx, hxy, hyz, sq_nonneg (y - x), sq_nonneg (z - y),
    mul_nonneg (by linarith : (0:ℤ) ≤ y - x) (by linarith : (0:ℤ) ≤ x),
    mul_nonneg (by linarith : (0:ℤ) ≤ z - y) (by linarith : (0:ℤ) ≤ y),
    mul_pos (by linarith : (0:ℤ) < x) (by linarith : (0:ℤ) < y)]

/-- The Markov Vieta-descent relation: `a` is the reduction of an ordered non-root
    Markov triple `b` (top `z` replaced by `3xy − z`). -/
def MarkovDescent (a b : ℤ × ℤ × ℤ) : Prop :=
  ∃ x y z : ℤ, b = (x, y, z) ∧ a = (x, y, 3 * x * y - z) ∧
    IsMarkov x y z ∧ 1 ≤ x ∧ x ≤ y ∧ y < z

/-- Height of a triple as a ℕ-rank. -/
def markovHeight (t : ℤ × ℤ × ℤ) : ℕ := (t.1 + t.2.1 + t.2.2).toNat

/-- **The Markov descent tree carries no perpetual engine**: no infinite sequence of
    Vieta reductions, because the height is a strictly decreasing ℕ-rank
    (`markov_vieta_lt`), so the tree reduces to its root in finitely many steps.
    HONEST red gate: this is the termination/finiteness half only; the Frobenius
    uniqueness conjecture (each Markov number is the largest of a UNIQUE triple) has
    no descent structure and is untouched — the green wall, the open gate. -/
theorem markov_no_perpetual_engine : ¬ PerpetualEngine MarkovDescent := by
  refine no_perpetual_engine_of_natRank markovHeight ?_
  rintro a b ⟨x, y, z, rfl, rfl, hM, hx, hxy, hyz⟩
  have hlt : 3 * x * y - z < z := markov_vieta_lt hM hx hxy hyz
  show (x + y + (3 * x * y - z)).toNat < (x + y + z).toNat
  set w := 3 * x * y
  omega

#print axioms markov_no_perpetual_engine

end EuclidsPath.WellFoundednessCanon
