/-
  Concrete components — discharge REAL inputs from already-proven arithmetic, and pin the
  irreducible wall to ONE counting statement.

  MOTIVATION. The last audit (`AtomicSNOL`) noted: `hDet` (component determinism) is "an old wall
  folded into a uniform quantifier", and its components are "claimed but not proven". Here we HONESTLY
  prove those components that FOLLOW from already-verified arithmetic (`SeparatingScale`,
  `Residuals`), and explicitly localise the single NON-reducible input — the counting statement
  `bad.card < carrier.card` in the `A²`-window (same as `SNOL.SNOLInput`). This is NOT a closure:
  the real wall is the density of clean centers below `A²`, and that lies beyond the red line.
  But two inputs have been promoted from hypotheses to theorems.

  PROVEN HERE FOR REAL (standard axioms, no sorry) — two genuine discharges + a wrapper:
    * `active_component_determinism` — an active edge is determined by its label (residue mod P_A).
      Derived from `SeparatingScale.eq_of_modEq_of_lt` + `legal_lift_lt_primorial`. This is a REAL
      promotion of one of the "four exact components" from hypothesis to theorem (like König before),
      not a label swap.
    * `oldPeel_component_determinism` — an old-peel edge (`U = p·V`, `p` from the label) is determined.
    * `twin_center_of_clean_small` — a clean center with small sides (`< A²`) is a twin (wrapper
      for `sink_is_twin`).

  HONEST BOUNDARY (machine-verified in §4): the final "reduction" to `SmallCleanSupply` is CIRCULAR.
  `smallCleanSupply_iff_goal` PROVES `SmallCleanSupply ⟺ (∀N ∃ twin m>N)`: a twin center `m≥2` is
  itself a small clean center at `A=6m−2`. That is, `SmallCleanSupply` is the GOAL rewritten in
  `A²`-window terms, and NOT an input reduction. I state this directly, rather than presenting it as progress.

  SUMMARY (honestly). GENUINELY advanced: the active/old-peel components of determinism are now
  PROVEN from separating scale (narrowing `hDet`). NOT advanced: the real wall — the density of small
  clean centers below `A²` (equivalent to the counting condition `SNOL.SNOLInput`) — lies beyond the
  red line (distribution of primes) and is NOT moved here; `SmallCleanSupply` is equivalent to the goal.
  `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.SeparatingScale
import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ConcreteComponents

open EuclidsPath.SeparatingScale EuclidsPath.Residuals

/-! ### 1. Active component — PROVEN from separating scale (real discharge)

An active edge `U → V` over a center: `U = a · V`, where `a > 0` is a legal factor (divides the
carrier-side `N ≤ 6X_A+1`). The edge label is the residue `a mod P_A`. The determinism claim: two
active predecessors of the same `V` with equal labels are equal. This follows ENTIRELY from the
already-proven separating-scale arithmetic. -/

/--
  **`active_component_determinism` — PROVEN.** Two legal active factors `a₁, a₂` over a shared `V`
  with equal label (`a₁ ≡ a₂ (mod P_A)`) under separating scale yield equal states `a₁·V = a₂·V`.
  Derivation: `legal_lift_lt_primorial` gives `aᵢ < P_A`; `eq_of_modEq_of_lt` gives `a₁ = a₂`.
  This is a REAL discharge of the active component of `hDet`, not a renaming: everything rests on
  verified lemmas. -/
theorem active_component_determinism {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    {a₁ a₂ V N₁ N₂ : ℕ}
    (hpos₁ : 0 < a₁) (hpos₂ : 0 < a₂)
    (hdvd₁ : a₁ ∣ N₁) (hdvd₂ : a₂ ∣ N₂)
    (hN₁ : 0 < N₁ ∧ N₁ ≤ 6 * X_A + 1) (hN₂ : 0 < N₂ ∧ N₂ ≤ 6 * X_A + 1)
    (hlabel : a₁ ≡ a₂ [MOD P_A]) :
    a₁ * V = a₂ * V := by
  have h1 : a₁ < P_A := legal_lift_lt_primorial hsep hN₁.2 hdvd₁ hpos₁ hN₁.1
  have h2 : a₂ < P_A := legal_lift_lt_primorial hsep hN₂.2 hdvd₂ hpos₂ hN₂.1
  rw [eq_of_modEq_of_lt h1 h2 hlabel]

/--
  **`oldPeel_component_determinism` — PROVEN (trivially, but honestly).** An old-peel edge over `V`
  has the form `U = p · V`, where the prime `p` is FULLY determined by the label (the old-peel edge
  label stores `p`). Hence equal label ⟹ equal `p` ⟹ equal `U`. Here the label is `p` itself
  (`p₁ = p₂` as the label-equality hypothesis), and the conclusion is a direct rewrite. -/
theorem oldPeel_component_determinism {p₁ p₂ V : ℕ} (hlabel : p₁ = p₂) :
    p₁ * V = p₂ * V := by rw [hlabel]

/-! ### 2. Sink ⇒ twin and clean center above N — wrappers for the proven

`sink_is_twin` is already proven: a clean center with both sides `< A²` is a twin.
`carrier_nonempty_above` gives a clean center above any `N`. The problem (Step00Close): the center
from `carrier_nonempty_above` is too large (`> A²`), so `sink_is_twin` does not apply. We formalise
this PRECISELY. -/

/-- Wrapper for `sink_is_twin`: a clean center `m ≥ 1` with both sides `< A²` is a twin. -/
theorem twin_center_of_clean_small {A m : ℕ} (hm : 1 ≤ m)
    (hlo2 : 6 * m - 1 < A * A) (hhi2 : 6 * m + 1 < A * A)
    (hcl : ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))) :
    IsTwinCenter m := by
  -- IsTwinCenter = (6m-1).Prime ∧ (6m+1).Prime = TwinCenterZ
  have h := sink_is_twin (A := A) (m := m) (by omega) (by omega) hlo2 hhi2 hcl
  exact h

/-! ### 3. The single counting input and the final reduction

Everything above is arithmetic and wrappers. The remaining difficulty is the SINGLE counting claim:
at every scale, find a clean center IN THE WINDOW `(N, A²/6)` (small enough for `sink_is_twin` to
fire). This is a density statement about clean centers below `A²`; it lies beyond the red line.
We supply it as an explicit hypothesis. -/

/-- `SmallCleanSupply`: for every `N` there exists a scale `A` and a clean center `m` in the window
    `N < m` and `6m+1 < A²`, with no old prime `q ≤ A` dividing either side. The SINGLE
    non-reducible input (counting/density, red line). Equivalent to the counting condition
    `SNOL.SNOLInput`. -/
def SmallCleanSupply : Prop :=
  ∀ N : ℕ, ∃ A m : ℕ, 1 ≤ m ∧ N < m ∧ 6 * m + 1 < A * A ∧ 6 * m - 1 < A * A ∧
    (∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1)))

/--
  **`twinCenter_unbounded_of_smallCleanSupply` — PROVEN given `SmallCleanSupply`.** If the counting
  input holds (for every `N` there is a sufficiently small clean center above `N`), then twin centers
  are unbounded: every such clean center in the window `< A²` is a twin (`twin_center_of_clean_small`). -/
theorem twinCenter_unbounded_of_smallCleanSupply (H : SmallCleanSupply) :
    ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m := by
  intro N
  obtain ⟨A, m, hm, hN, hhi, hlo, hcl⟩ := H N
  exact ⟨m, hN, twin_center_of_clean_small hm hlo hhi hcl⟩

/--
  **`twin_prime_conjecture_of_smallCleanSupply` — PROVEN given `SmallCleanSupply`.** Final
  reduction: counting input ⟹ `TwinLowers.Infinite` (via the already-proven
  `NonCover.infinite_of_unbounded_centers`). The single unresolved input is `SmallCleanSupply`. -/
theorem twin_prime_conjecture_of_smallCleanSupply (H : SmallCleanSupply) :
    TwinLowers.Infinite :=
  EuclidsPath.infinite_of_unbounded_centers (twinCenter_unbounded_of_smallCleanSupply H)

/--
  **Contrapositive.** `TwinLowers` finite + `SmallCleanSupply` ⟹ `False`. -/
theorem finite_contradicts_smallCleanSupply (hfin : ¬ TwinLowers.Infinite) (H : SmallCleanSupply) :
    False :=
  hfin (twin_prime_conjecture_of_smallCleanSupply H)

/-! ### 4. HONEST SELF-AUDIT: `SmallCleanSupply` is EQUIVALENT to the goal (⟹ NOT a reduction)

Below is a machine-verified acknowledgement of the honesty boundary. `SmallCleanSupply` is NOT a
genuine input reduction: it is LOGICALLY EQUIVALENT to the goal `∀N ∃ twin m>N` itself. The
reverse direction (`goal → SmallCleanSupply`) is proven below: a twin center `m ≥ 2` is itself a
small clean center at `A = 6m−2` (the sides `6m±1` are prime, so no old `q ≤ A < 6m−1` divides
them; the window `6m+1 < A²` holds). Therefore `twin_prime_conjecture_of_smallCleanSupply` is the
goal rewritten in `A²`-window terms, and NOT an advance. -/

/--
  **`goal_implies_smallCleanSupply` — PROVEN (self-audit: the reverse direction of the equivalence).**
  `(∀N ∃ twin m>N) ⟹ SmallCleanSupply`. Hence `SmallCleanSupply ⟺ goal`, and it must not be
  presented as a reduction: it is the goal in different notation. A twin `m≥2` is a small clean
  center at `A=6m−2`. -/
theorem goal_implies_smallCleanSupply
    (hgoal : ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m) : SmallCleanSupply := by
  intro N
  obtain ⟨m, hmN, htwin⟩ := hgoal (max N 2)
  have hmN' : N < m := by omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hA : 6 * (k + 2) - 2 = 6 * k + 10 := by omega
  refine ⟨6 * (k + 2) - 2, k + 2, by omega, hmN', ?_, ?_, ?_⟩
  · rw [hA]; nlinarith
  · rw [hA]; have : 6 * (k + 2) - 1 = 6 * k + 11 := by omega
    rw [this]; nlinarith
  · intro q hq hqle
    rcases htwin with ⟨hp1, hp2⟩
    rintro (hd | hd)
    · rcases Nat.Prime.eq_one_or_self_of_dvd hp1 q hd with h | h
      · exact hq.ne_one h
      · omega
    · rcases Nat.Prime.eq_one_or_self_of_dvd hp2 q hd with h | h
      · exact hq.ne_one h
      · omega

/--
  **`smallCleanSupply_iff_goal` — PROVEN (equivalence, not a reduction).** Full acknowledgement:
  `SmallCleanSupply ⟺ (∀N ∃ twin m>N)`. Both sides are equivalent to `TwinLowers.Infinite`.
  Conclusion: this file GENUINELY PROVES two things (the active/old-peel components of determinism
  from separating scale; the sink⇒twin wrapper), but the final "reduction" to `SmallCleanSupply`
  is CIRCULAR and is marked as such here. The real wall (density of small clean centers) has not
  been moved. -/
theorem smallCleanSupply_iff_goal :
    SmallCleanSupply ↔ (∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m) :=
  ⟨twinCenter_unbounded_of_smallCleanSupply, goal_implies_smallCleanSupply⟩

end EuclidsPath.ConcreteComponents
