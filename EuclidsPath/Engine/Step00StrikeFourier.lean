import Mathlib
import EuclidsPath.Engine.Step00PhaseCoverKernel

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The strike-Fourier layer — the imaginary divisor and the perpetual-engine dichotomy

Origin: the author's directive of this pass.  "The prime `q` is an *imaginary divisor*: it
acts on a window not as a point strike but through all `q`-th roots of unity, and the
*orthogonal transition* annihilates every nonzero mode.  A defect at the `+1` wing must
spawn a twin; without the twin, the defect spawns a *perpetual engine* — or the engine
oscillation breaks."

The honest dictionary, term by term:

* **imaginary divisor** = the additive characters of `ZMod q` (`ZMod.stdAddChar`, the
  `q`-th roots of unity `exp(2πij/q)`): the strike indicator of the clock `q` is exactly
  the averaged character sum (`delta_fourier`, `strike_minus_fourier`, `strike_plus_fourier`);
* **orthogonal transition** = orthogonality of characters (`AddChar.sum_mulShift`): a
  nontrivial mode sums to `0` over a full period, the trivial mode to `q`;
* **the coherence pair** = `defect_forces_coherence` + `oscillation_kills_defect` (Part R):
  the author's dichotomy stated EXACTLY at the finite level.  A window with no clean center
  has fluctuation exactly `-(mainTerm)` — the oscillating engines must hold an exact
  coherent conspiracy of full main-term magnitude.  ANY decay below full coherence, in any
  window below the `A²` ceiling, forces a twin (`oscillation_plants_twin`);
* **the engine decomposition** = `windowFluct_eq_minorSum` (Part E2b): the zero mode of the
  character expansion IS the main term (`modeAmp_zeroMode`, `modeWindowSum_zeroMode`), and
  the nontrivial modes — the engines — carry exactly the fluctuation.  Together with
  `defect_forces_coherence`: without a twin, all engine modes conspire to a coherent spike
  of exact magnitude `mainTerm` (`defect_forces_engine_coherence`).

## DISCLOSURE (read this before anything else)

`perpetualEngine_iff_wall` is the FOURTH COSTUME of the single wall, an exact definitional
repackaging of `CleanGapBound` — the same statement already worn as (1) the combinatorial
gap bound `CleanGapBound` itself (`Step00TwinJacobsthalWall`), (2) the phase-cover UNSAT
certificates (`Step00PhaseCoverKernel`), (3) the Jacobsthal-window / witness-chain form
(`TwinJacobsthalBound`, `Step00WitnessChainKernel`).  The vocabulary is new; the
mathematical content of the iff is zero.  What this module ADDS is exact structure around
the wall: the mathematical body of the rational layer is the engine decomposition of Part
E2b, its empirical body is the spike-anatomy harness; any future PROVEN decay law for the
nontrivial modes plugs into `oscillation_kills_defect` and yields twins.

**The minor-arc BOUND is exactly the parity wall in Fourier clothes.**  This module provides
the exact skeleton — the identities — and NEVER the bound: no asymptotics, no `O(·)`, no
unproven estimate is stated or used anywhere here.  The linear character layer is
parity-blind (Selberg's foil sieve is itself built FROM characters), which is precisely why
the IDENTITY is green while the BOUND is the wall.  Every theorem below is an exact finite
identity, an exact reformulation, or a kernel-checked instance.
-/

namespace EuclidsPath
namespace StrikeFourier

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.TwinJacobsthalWall
open EuclidsPath.PhaseCoverKernel

/-! ### Part R — the rational coherence layer (no complex numbers)

Everything in this part lives over `ℚ` and is independent of the character machinery: the
author's perpetual-motion theorem pair is delivered by exact window counting alone. -/

/-- The active clocks of scale `A`: the primes `5 ≤ q ≤ A`.  The primes `2, 3` never strike
    a wing `6m ± 1` (`m ≥ 1`), so this is the exact clock set of `Clean A`. -/
def clocks (A : ℕ) : Finset ℕ := (Finset.Icc 5 A).filter Nat.Prime

theorem mem_clocks {A q : ℕ} : q ∈ clocks A ↔ q.Prime ∧ 5 ≤ q ∧ q ≤ A := by
  unfold clocks
  rw [Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- `cleanCount A k g` — the number of clean centers in the window `(k, k+g]`. -/
def cleanCount (A k g : ℕ) : ℕ :=
  ((Finset.Ioc k (k + g)).filter fun m => Clean A m).card

theorem cleanCount_pos_iff {A k g : ℕ} :
    1 ≤ cleanCount A k g ↔ ∃ m : ℕ, k < m ∧ m ≤ k + g ∧ Clean A m := by
  unfold cleanCount
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Finset.card_pos.mp h
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    exact ⟨m, hm.1.1, hm.1.2, hm.2⟩
  · rintro ⟨m, h1, h2, h3⟩
    exact Finset.card_pos.mpr
      ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1, h2⟩, h3⟩⟩

theorem cleanCount_eq_zero_iff {A k g : ℕ} :
    cleanCount A k g = 0 ↔ ¬ ∃ m : ℕ, k < m ∧ m ≤ k + g ∧ Clean A m := by
  rw [← cleanCount_pos_iff]
  omega

/-- The main term of a window of length `g` at scale `A`: the window length times the
    product of the exact per-clock survival densities `1 - 2/q` (each clock `q ≥ 5` kills
    exactly the two wing residues).  A DEFINITION, not an estimate: no claim that
    `cleanCount` is near it is made anywhere in this module. -/
def mainTerm (A g : ℕ) : ℚ := (g : ℚ) * ∏ q ∈ clocks A, (1 - 2 / (q : ℚ))

theorem factor_pos {A q : ℕ} (hq : q ∈ clocks A) : (0 : ℚ) < 1 - 2 / (q : ℚ) := by
  obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
  rw [sub_pos, div_lt_one hq0]
  exact_mod_cast (by omega : 2 < q)

theorem prod_factors_pos (A : ℕ) : (0 : ℚ) < ∏ q ∈ clocks A, (1 - 2 / (q : ℚ)) :=
  Finset.prod_pos fun _ hq => factor_pos hq

theorem mainTerm_nonneg (A g : ℕ) : 0 ≤ mainTerm A g :=
  mul_nonneg (Nat.cast_nonneg g) (prod_factors_pos A).le

/-- Every survival factor is positive, so the main term of a nonempty window is positive. -/
theorem mainTerm_pos {A g : ℕ} (hg : 0 < g) : 0 < mainTerm A g :=
  mul_pos (by exact_mod_cast hg) (prod_factors_pos A)

/-- The window fluctuation: the exact count minus the main term.  In Part E2b this is
    proved to be EXACTLY the sum of the nontrivial character modes — the engines. -/
def windowFluct (A k g : ℕ) : ℚ := (cleanCount A k g : ℚ) - mainTerm A g

/-- **A defect without a twin spawns a perpetual engine (coherence form).**  If a window
    holds NO clean center, its fluctuation is exactly `-(mainTerm)`: by
    `windowFluct_eq_minorSum` the oscillating engines (nontrivial modes) must then hold an
    EXACT coherent conspiracy of full main-term magnitude — a perpetual engine.  Trivial
    arithmetic here; the content is the pairing with the engine decomposition below. -/
theorem defect_forces_coherence {A k g : ℕ} (h : cleanCount A k g = 0) :
    windowFluct A k g = -(mainTerm A g) := by
  unfold windowFluct
  rw [h]
  simp

/-- The `|·|`-form of the coherent spike: a defect window has `|fluctuation| = mainTerm`. -/
theorem defect_coherence_abs {A k g : ℕ} (h : cleanCount A k g = 0) :
    |windowFluct A k g| = mainTerm A g := by
  rw [defect_forces_coherence h, abs_neg, abs_of_nonneg (mainTerm_nonneg A g)]

/-- **Oscillation kills the defect.**  ANY decay of the engines below full coherence —
    `|windowFluct| < mainTerm`, however slight — forces a clean center in the window.
    This is the exact finite trigger into which any future proven decay law plugs. -/
theorem oscillation_kills_defect {A k g : ℕ}
    (h : |windowFluct A k g| < mainTerm A g) : 1 ≤ cleanCount A k g := by
  by_contra hc
  have h0 : cleanCount A k g = 0 := by omega
  rw [defect_coherence_abs h0] at h
  exact lt_irrefl _ h

/-- **The loaded form: engine decay below the ceiling plants a TWIN.**  If the engines of a
    window decay below full coherence and the whole window sits under the sieve horizon
    (`6(k+g)+1 < A²`), the clean center it forces has both wings prime (`sink_is_twin`).
    Mirrors `twin_gap_below_wall` (`Step00WitnessChainKernel`); the side conditions of
    `sink_is_twin` are discharged by the horizon bound alone, so no primality of `A` and no
    `1 ≤ k` is needed. -/
theorem oscillation_plants_twin {A k g : ℕ}
    (h : |windowFluct A k g| < mainTerm A g)
    (hwall : 6 * (k + g) + 1 < A * A) :
    ∃ m : ℕ, k < m ∧ m ≤ k + g ∧ TwinCenterZ m := by
  obtain ⟨m, h1, h2, hclean⟩ := cleanCount_pos_iff.mp (oscillation_kills_defect h)
  exact ⟨m, h1, h2, sink_is_twin (by omega) (by omega) (by omega) (by omega) hclean⟩

theorem window_defect_bounded_iff {A k g : ℕ} :
    1 - mainTerm A g ≤ windowFluct A k g ↔ ∃ m : ℕ, k < m ∧ m ≤ k + g ∧ Clean A m := by
  unfold windowFluct
  rw [sub_le_sub_iff_right, Nat.one_le_cast]
  exact cleanCount_pos_iff

/-- **THE FOURTH COSTUME (disclosure).**  The perpetual-engine impossibility statement —
    "in every window the fluctuation stays at least `1 - mainTerm` above the coherent
    spike" — is an EXACT definitional repackaging of the wall `CleanGapBound A g`.  The
    other three costumes of the same wall: the combinatorial gap bound itself
    (`Step00TwinJacobsthalWall`), the phase-cover UNSAT certificates
    (`Step00PhaseCoverKernel`), the Jacobsthal-window / witness-chain form
    (`TwinJacobsthalBound`, `Step00WitnessChainKernel`).  Vocabulary status disclosed, with
    the same honesty as the earlier reformulation disclosures: the iff itself carries zero
    new mathematics.  Its mathematical body is the engine decomposition
    `windowFluct_eq_minorSum` (Part E2b); its empirical body is the spike-anatomy harness;
    any future proven decay law enters through `oscillation_kills_defect` and exits as
    twins. -/
theorem perpetualEngine_iff_wall {A g : ℕ} :
    CleanGapBound A g ↔ ∀ k : ℕ, 1 - mainTerm A g ≤ windowFluct A k g := by
  unfold CleanGapBound
  exact forall_congr' fun k => window_defect_bounded_iff.symm

theorem fluct_eq_neg_mainTerm_iff {A k g : ℕ} :
    windowFluct A k g = -(mainTerm A g) ↔ cleanCount A k g = 0 := by
  unfold windowFluct
  constructor
  · intro h
    have hc : (cleanCount A k g : ℚ) = 0 := by linarith
    exact_mod_cast hc
  · intro h
    rw [h]
    simp

/-- The negative form of the fourth costume: the wall FAILS at `(A, g)` iff some window
    exhibits the exactly coherent spike `windowFluct = -(mainTerm)` — iff a perpetual
    engine runs somewhere. -/
theorem not_cleanGapBound_iff_coherent_spike {A g : ℕ} :
    ¬ CleanGapBound A g ↔ ∃ k : ℕ, windowFluct A k g = -(mainTerm A g) := by
  unfold CleanGapBound
  rw [not_forall]
  refine exists_congr fun k => ?_
  rw [fluct_eq_neg_mainTerm_iff, cleanCount_eq_zero_iff]

/-! #### Perpetual-engine impossibility instances

The ten kernel-certified wall scales, reread in engine vocabulary at zero new kernel cost:
each theorem is one line from `perpetualEngine_iff_wall` and the existing certificate.  The
one-period certificates (`Step00TwinJacobsthalWall`) and the phase-cover UNSAT certificates
(`Step00PhaseCoverKernel`) are finite machine proofs of PERPETUAL-ENGINE IMPOSSIBILITY at
these scales: no window of the stated length can hold the exactly coherent spike. -/

/-- No perpetual engine at scale `5`, window `2` (one-period kernel certificate). -/
theorem engineDecay_at_5 : ∀ k : ℕ, 1 - mainTerm 5 2 ≤ windowFluct 5 k 2 :=
  perpetualEngine_iff_wall.mp cleanGapBound_5

/-- No perpetual engine at scale `7`, window `5` (one-period kernel certificate). -/
theorem engineDecay_at_7 : ∀ k : ℕ, 1 - mainTerm 7 5 ≤ windowFluct 7 k 5 :=
  perpetualEngine_iff_wall.mp cleanGapBound_7

/-- No perpetual engine at scale `11`, window `7` (one-period kernel certificate). -/
theorem engineDecay_at_11 : ∀ k : ℕ, 1 - mainTerm 11 7 ≤ windowFluct 11 k 7 :=
  perpetualEngine_iff_wall.mp cleanGapBound_11

/-- No perpetual engine at scale `13`, window `11` (one-period kernel certificate). -/
theorem engineDecay_at_13 : ∀ k : ℕ, 1 - mainTerm 13 11 ≤ windowFluct 13 k 11 :=
  perpetualEngine_iff_wall.mp cleanGapBound_13

/-- No perpetual engine at scale `17`, window `18` (phase-cover UNSAT certificate). -/
theorem engineDecay_at_17 : ∀ k : ℕ, 1 - mainTerm 17 18 ≤ windowFluct 17 k 18 :=
  perpetualEngine_iff_wall.mp cleanGapBound_17

/-- No perpetual engine at scale `19`, window `25` (phase-cover UNSAT certificate). -/
theorem engineDecay_at_19 : ∀ k : ℕ, 1 - mainTerm 19 25 ≤ windowFluct 19 k 25 :=
  perpetualEngine_iff_wall.mp cleanGapBound_19

/-- No perpetual engine at scale `23`, window `34` (phase-cover UNSAT certificate). -/
theorem engineDecay_at_23 : ∀ k : ℕ, 1 - mainTerm 23 34 ≤ windowFluct 23 k 34 :=
  perpetualEngine_iff_wall.mp cleanGapBound_23

/-- No perpetual engine at scale `29`, window `43` (phase-cover UNSAT certificate). -/
theorem engineDecay_at_29 : ∀ k : ℕ, 1 - mainTerm 29 43 ≤ windowFluct 29 k 43 :=
  perpetualEngine_iff_wall.mp cleanGapBound_29

/-- No perpetual engine at scale `31`, window `58` (phase-cover UNSAT certificate). -/
theorem engineDecay_at_31 : ∀ k : ℕ, 1 - mainTerm 31 58 ≤ windowFluct 31 k 58 :=
  perpetualEngine_iff_wall.mp cleanGapBound_31

/-- No perpetual engine at scale `37`, window `88` (phase-cover UNSAT certificate). -/
theorem engineDecay_at_37 : ∀ k : ℕ, 1 - mainTerm 37 88 ≤ windowFluct 37 k 88 :=
  perpetualEngine_iff_wall.mp cleanGapBound_37

/-! #### The escalation: engine decay on cofinal scales forces infinitely many twins -/

/-- Engine-decay form of the cofinal wall: at cofinally many prime scales `A`, no window of
    length `A²/7` holds the coherent spike.  Definitionally equivalent to
    `TwinJacobsthalBoundCofinal` (see `engineDecayCofinal_iff_twinJacobsthalCofinal`). -/
def EngineDecayCofinal : Prop :=
  ∀ A0 : ℕ, ∃ A : ℕ, A0 ≤ A ∧ A.Prime ∧
    ∀ k : ℕ, 1 - mainTerm A (A ^ 2 / 7) ≤ windowFluct A k (A ^ 2 / 7)

theorem engineDecayCofinal_iff_twinJacobsthalCofinal :
    EngineDecayCofinal ↔ TwinJacobsthalBoundCofinal := by
  unfold EngineDecayCofinal TwinJacobsthalBoundCofinal
  exact forall_congr' fun A0 => exists_congr fun A =>
    and_congr_right fun _ => and_congr_right fun _ => perpetualEngine_iff_wall.symm

/-- **The full chain for the Fourier reader**: perpetual-engine impossibility (engine decay)
    at cofinally many wall scales forces a twin center above every horizon — via the
    existing escalation `twinCenters_unbounded_of_twinJacobsthalCofinal`. -/
theorem twinCenters_unbounded_of_engineDecayCofinal (H : EngineDecayCofinal) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m :=
  twinCenters_unbounded_of_twinJacobsthalCofinal
    (engineDecayCofinal_iff_twinJacobsthalCofinal.mp H)

/-- Engine decay on cofinal scales reaches the goal: `TwinLowers.Infinite`, conditional
    ONLY on the named wall in its engine costume. -/
theorem twinLowersInfinite_of_engineDecayCofinal (H : EngineDecayCofinal) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_twinJacobsthalCofinal
    (engineDecayCofinal_iff_twinJacobsthalCofinal.mp H)

/-! #### Kernel self-tests of the rational layer (tiny) -/

example : clocks 5 = {5} := by decide

/-- Window `(0, 5]` at scale `5`: exactly the clean centers `2, 3, 5` (centers `1, 4` are
    struck by the clock `5`). -/
example : cleanCount 5 0 5 = 3 := by decide

example : mainTerm 5 5 = 3 := by
  rw [mainTerm, show clocks 5 = {5} from by decide, Finset.prod_singleton]
  norm_num

/-! ### Part E1 — the imaginary divisor (additive characters as strike indicators)

THIS is the imaginary divisor: the prime `q` acting through all `q`-th roots of unity.  The
point-strike indicator (a divisibility test) is the orthogonality-averaged character sum;
the "orthogonal transition" of the directive is precisely `AddChar.sum_mulShift`. -/

private theorem prime_neZero {q : ℕ} (hq : q.Prime) : NeZero q := ⟨hq.pos.ne'⟩

/-- **The delta identity (imaginary divisor, raw form).**  Over any modulus `q ≥ 1`, the
    indicator of `x = 0` in `ZMod q` is the average of all `q` character modes at `x` —
    character orthogonality (`AddChar.sum_mulShift`), no primality needed. -/
theorem delta_fourier (q : ℕ) [NeZero q] (x : ZMod q) :
    (if x = 0 then (1 : ℂ) else 0)
      = (q : ℂ)⁻¹ * ∑ j : ZMod q, ZMod.stdAddChar (j * x) := by
  rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q), ZMod.card q]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  split_ifs with h
  · rw [inv_mul_cancel₀ hq0]
  · simp

/-- Converse wing bridge (minus wing): the forced residue really strikes.  Complements the
    one-directional `dvd_wing_minus` of `Step00PhaseCoverKernel`. -/
private theorem wing_minus_of_residue {q i6 m : ℕ} (h2 : 2 ≤ q)
    (hinv : 6 * i6 % q = 1) (hres : m % q = i6 % q) : q ∣ 6 * m - 1 := by
  have hmul : (6 * m) % q = (6 * i6) % q :=
    Nat.ModEq.mul_left 6 (show m ≡ i6 [MOD q] from hres)
  have h1 : (6 * m) % q = 1 := by rw [hmul, hinv]
  have hdm := Nat.div_add_mod (6 * m) q
  exact ⟨6 * m / q, by omega⟩

/-- The plus-wing base strike `q ∣ 6(q - i6) + 1` (the derivation inside `dvd_wing_plus`,
    reproduced as a standalone converse ingredient). -/
private theorem wing_plus_base {q i6 : ℕ} (hi : i6 < q) (hinv : 6 * i6 % q = 1) :
    q ∣ 6 * (q - i6) + 1 := by
  have hdm := Nat.div_add_mod (6 * i6) q
  rw [hinv] at hdm
  have he2 : 6 * (q - i6) + 1 = 6 * q - q * (6 * i6 / q) := by omega
  rw [he2]
  exact Nat.dvd_sub (Dvd.intro 6 (by ring)) (Dvd.intro _ rfl)

/-- Converse wing bridge (plus wing). -/
private theorem wing_plus_of_residue {q i6 m : ℕ} (h2 : 2 ≤ q) (hi : i6 < q)
    (hinv : 6 * i6 % q = 1) (hres : m % q = (q - i6) % q) : q ∣ 6 * m + 1 := by
  have hmul : 6 * m ≡ 6 * (q - i6) [MOD q] :=
    Nat.ModEq.mul_left 6 (show m ≡ q - i6 [MOD q] from hres)
  have hstep : 6 * m + 1 ≡ 6 * (q - i6) + 1 [MOD q] := Nat.ModEq.add_right 1 hmul
  have h0 : 6 * (q - i6) + 1 ≡ 0 [MOD q] :=
    Nat.modEq_zero_iff_dvd.mpr (wing_plus_base hi hinv)
  exact Nat.modEq_zero_iff_dvd.mp (hstep.trans h0)

/-- The minus-wing strike is EXACTLY the residue `i6 = 6⁻¹ mod q` (both directions; the
    forward direction is `dvd_wing_minus` of `Step00PhaseCoverKernel`, reused). -/
theorem strike_minus_iff {q i6 m : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hinv : 6 * i6 % q = 1) (hm : 1 ≤ m) :
    q ∣ 6 * m - 1 ↔ (m : ZMod q) = (i6 : ZMod q) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact ⟨fun hd => dvd_wing_minus hq h5 hinv hm hd,
    fun hres => wing_minus_of_residue (by omega) hinv hres⟩

/-- The plus-wing strike is EXACTLY the residue `-i6` (both directions; forward is
    `dvd_wing_plus`, reused). -/
theorem strike_plus_iff {q i6 m : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hi : i6 < q)
    (hinv : 6 * i6 % q = 1) :
    q ∣ 6 * m + 1 ↔ (m : ZMod q) = -(i6 : ZMod q) := by
  have hcast : ((q - i6 : ℕ) : ZMod q) = -(i6 : ZMod q) := by
    rw [Nat.cast_sub hi.le, ZMod.natCast_self, zero_sub]
  constructor
  · intro hd
    rw [← hcast, ZMod.natCast_eq_natCast_iff]
    exact dvd_wing_plus hq h5 hi hinv hd
  · intro h
    refine wing_plus_of_residue (by omega : 2 ≤ q) hi hinv ?_
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hcast]; exact h)

/-- **The imaginary divisor, minus wing.**  The strike indicator of the clock `q` on the
    wing `6m - 1` — a pure `ℕ`-divisibility — is the averaged sum of ALL `q`-th roots of
    unity at the phase `m - i6`.  The prime does not test a point; it interrogates the
    window through every mode at once, and orthogonality collapses the answer to `0/1`. -/
theorem strike_minus_fourier {q : ℕ} [NeZero q] {i6 : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hinv : 6 * i6 % q = 1) {m : ℕ} (hm : 1 ≤ m) :
    (if q ∣ 6 * m - 1 then (1 : ℂ) else 0)
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (j * ((m : ZMod q) - (i6 : ZMod q))) := by
  rw [← delta_fourier q ((m : ZMod q) - (i6 : ZMod q))]
  exact if_congr (by rw [sub_eq_zero]; exact strike_minus_iff hq h5 hinv hm) rfl rfl

/-- **The imaginary divisor, plus wing** (phase `m + i6`, since the struck residue is
    `-i6`). -/
theorem strike_plus_fourier {q : ℕ} [NeZero q] {i6 : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hi : i6 < q) (hinv : 6 * i6 % q = 1) (m : ℕ) :
    (if q ∣ 6 * m + 1 then (1 : ℂ) else 0)
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (j * ((m : ZMod q) + (i6 : ZMod q))) := by
  rw [← delta_fourier q ((m : ZMod q) + (i6 : ZMod q))]
  refine if_congr ?_ rfl rfl
  rw [show ((m : ZMod q) + (i6 : ZMod q) = 0) ↔ ((m : ZMod q) = -(i6 : ZMod q)) from
    add_eq_zero_iff_eq_neg]
  exact strike_plus_iff hq h5 hi hinv

/-! ### The canonical phase `i6 q = 6⁻¹ mod q` (uniform over clock sets) -/

/-- The canonical phase of the clock `q`: the `ℕ`-representative of `(6 : ZMod q)⁻¹`.
    For a prime clock `q ≥ 5` this satisfies the repo interface `6 * i6 q % q = 1`
    (`i6_spec`), so all `dvd_wing_*` bridges apply with this uniform choice. -/
def i6 (q : ℕ) : ℕ := ((6 : ZMod q)⁻¹).val

theorem i6_lt {q : ℕ} [NeZero q] : i6 q < q := ZMod.val_lt _

theorem i6_spec {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) : 6 * i6 q % q = 1 := by
  haveI := prime_neZero hq
  have hcop : Nat.Coprime 6 q := by
    rcases Nat.coprime_or_dvd_of_prime hq 6 with h | h
    · exact h.symm
    · exfalso
      have h6 := Nat.le_of_dvd (by norm_num) h
      interval_cases q
      · exact absurd h (by norm_num)
      · exact absurd hq (by norm_num)
  have hunit : IsUnit (6 : ZMod q) := by
    have := (ZMod.isUnit_iff_coprime 6 q).mpr hcop
    simpa using this
  have hmul : (6 : ZMod q) * (6 : ZMod q)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  have hval : ((i6 q : ℕ) : ZMod q) = (6 : ZMod q)⁻¹ := by
    simp only [i6]
    exact ZMod.natCast_zmod_val _
  have hcast : ((6 * i6 q : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    push_cast
    rw [hval, hmul]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have h1 : (1 : ℕ) % q = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.ModEq] at hmod
  rw [hmod, h1]

/-! ### Part E2(a) — the exact product-form window identity

Guarded (`q = 0`-safe) forms of the character sums, so that clock-indexed products can be
stated over `Finset ℕ` without carrying instances; the guards never fire on clocks. -/

/-- The minus-wing strike sum of clock `q` at center `m` (guarded total form). -/
noncomputable def strikeSumMinus (q m : ℕ) : ℂ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    (q : ℂ)⁻¹ * ∑ j : ZMod q, ZMod.stdAddChar (j * ((m : ZMod q) - (i6 q : ZMod q)))

/-- The plus-wing strike sum of clock `q` at center `m` (guarded total form). -/
noncomputable def strikeSumPlus (q m : ℕ) : ℂ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    (q : ℂ)⁻¹ * ∑ j : ZMod q, ZMod.stdAddChar (j * ((m : ZMod q) + (i6 q : ZMod q)))

theorem strikeSumMinus_def {q : ℕ} [NeZero q] (m : ℕ) :
    strikeSumMinus q m
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (j * ((m : ZMod q) - (i6 q : ZMod q))) := by
  unfold strikeSumMinus
  rw [dif_neg (NeZero.ne q)]

theorem strikeSumPlus_def {q : ℕ} [NeZero q] (m : ℕ) :
    strikeSumPlus q m
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (j * ((m : ZMod q) + (i6 q : ZMod q))) := by
  unfold strikeSumPlus
  rw [dif_neg (NeZero.ne q)]

theorem strikeSumMinus_eq_indicator {q m : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hm : 1 ≤ m) :
    strikeSumMinus q m = (if q ∣ 6 * m - 1 then (1 : ℂ) else 0) := by
  haveI := prime_neZero hq
  rw [strikeSumMinus_def, ← strike_minus_fourier hq h5 (i6_spec hq h5) hm]

theorem strikeSumPlus_eq_indicator {q m : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    strikeSumPlus q m = (if q ∣ 6 * m + 1 then (1 : ℂ) else 0) := by
  haveI := prime_neZero hq
  rw [strikeSumPlus_def, ← strike_plus_fourier hq h5 i6_lt (i6_spec hq h5) m]

/-- Pointwise indicator algebra: for a clean center every clock factor is `1`; for an
    unclean one some clock strikes exactly one wing (the two wing classes are disjoint for
    `q ≥ 5`), so that factor — and the product — vanishes. -/
theorem clean_indicator_prod {A m : ℕ} (hm : 1 ≤ m) :
    (if Clean A m then (1 : ℂ) else 0)
      = ∏ q ∈ clocks A,
          ((1 : ℂ) - (if q ∣ 6 * m - 1 then 1 else 0)
            - (if q ∣ 6 * m + 1 then 1 else 0)) := by
  by_cases hc : Clean A m
  · rw [if_pos hc]
    symm
    apply Finset.prod_eq_one
    intro q hq
    obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
    have h1 : ¬ q ∣ 6 * m - 1 := fun hd => hc q hp hA (Or.inl hd)
    have h2 : ¬ q ∣ 6 * m + 1 := fun hd => hc q hp hA (Or.inr hd)
    rw [if_neg h1, if_neg h2]
    ring
  · rw [if_neg hc]
    have hex : ∃ q : ℕ, q.Prime ∧ q ≤ A ∧ (q ∣ 6 * m - 1 ∨ q ∣ 6 * m + 1) := by
      by_contra hno
      exact hc fun q hp hA hor => hno ⟨q, hp, hA, hor⟩
    obtain ⟨q, hp, hA, hor⟩ := hex
    have h5 : 5 ≤ q := by
      rcases Nat.lt_or_ge q 5 with hlt | h5
      · exfalso
        have h2 := hp.two_le
        interval_cases q
        · rcases hor with h | h <;> omega
        · rcases hor with h | h <;> omega
        · exact absurd hp (by norm_num)
      · exact h5
    have hqm : q ∈ clocks A := mem_clocks.mpr ⟨hp, h5, hA⟩
    have hdisj : ¬ (q ∣ 6 * m - 1 ∧ q ∣ 6 * m + 1) := by
      rintro ⟨ha, hb⟩
      have hd := Nat.dvd_sub hb ha
      have he : 6 * m + 1 - (6 * m - 1) = 2 := by omega
      rw [he] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    symm
    apply Finset.prod_eq_zero hqm
    rcases hor with h | h
    · rw [if_pos h, if_neg fun h' => hdisj ⟨h, h'⟩]
      ring
    · rw [if_neg fun h' => hdisj ⟨h', h⟩, if_pos h]
      ring

/-- The window count as a sum of clock-indexed indicator products (exact identity). -/
theorem cleanCount_eq_window_prod {A k g : ℕ} :
    (cleanCount A k g : ℂ)
      = ∑ m ∈ Finset.Ioc k (k + g), ∏ q ∈ clocks A,
          ((1 : ℂ) - (if q ∣ 6 * m - 1 then 1 else 0)
            - (if q ∣ 6 * m + 1 then 1 else 0)) := by
  have h1 : (cleanCount A k g : ℂ)
      = ∑ m ∈ Finset.Ioc k (k + g), (if Clean A m then (1 : ℂ) else 0) := by
    unfold cleanCount
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [h1]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  exact clean_indicator_prod hm1

/-- **Part E2(a): the exact product-form window identity, Fourier clothes.**  The window
    count equals the window sum of clock products with every strike indicator replaced by
    its character sum (`strike_minus_fourier` / `strike_plus_fourier`).  Exact identity —
    the two wing classes are disjoint for every clock (`q ∤ 2`), so the clean indicator is
    the product of `1 - strike₋ - strike₊`. -/
theorem cleanCount_eq_window_prod_fourier {A k g : ℕ} :
    (cleanCount A k g : ℂ)
      = ∑ m ∈ Finset.Ioc k (k + g), ∏ q ∈ clocks A,
          ((1 : ℂ) - strikeSumMinus q m - strikeSumPlus q m) := by
  rw [cleanCount_eq_window_prod]
  refine Finset.sum_congr rfl fun m hm => Finset.prod_congr rfl fun q hq => ?_
  obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
  have hm1 : 1 ≤ m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  rw [strikeSumMinus_eq_indicator hp h5 hm1, strikeSumPlus_eq_indicator hp h5]

/-! ### Part E2(b) — the engine decomposition

The product of per-clock character sums expands (`Finset.prod_sum`) into a sum over MODE
TUPLES `j = (j_q)_q`: one mode per clock, ranging over the full dual `range q ≅ ZMod q`.
Each tuple contributes a coefficient (`modeAmp`, collecting the `q⁻¹`-weights, signs and
phase offsets) times a window wave sum (`modeWindowSum`).  The zero tuple IS the main term;
the rest are the engines. -/

/-- The wave of mode `j` of clock `q` at center `m`: `ψ_q(j·m)` (guarded total form). -/
noncomputable def modeWave (q j m : ℕ) : ℂ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    ZMod.stdAddChar ((j : ZMod q) * (m : ZMod q))

/-- The coefficient of mode `j` of clock `q`: the delta at `j = 0` minus the `q⁻¹`-weighted
    pair of wing phase factors `ψ_q(-j·i6) + ψ_q(j·i6)` (guarded total form). -/
noncomputable def modeCoeff (q j : ℕ) : ℂ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    (if j = 0 then (1 : ℂ) else 0)
      - (q : ℂ)⁻¹ * (ZMod.stdAddChar (-(j : ZMod q) * (i6 q : ZMod q))
          + ZMod.stdAddChar ((j : ZMod q) * (i6 q : ZMod q)))

theorem modeWave_def {q : ℕ} [NeZero q] (j m : ℕ) :
    modeWave q j m = ZMod.stdAddChar ((j : ZMod q) * (m : ZMod q)) := by
  unfold modeWave
  rw [dif_neg (NeZero.ne q)]

theorem modeCoeff_def {q : ℕ} [NeZero q] (j : ℕ) :
    modeCoeff q j
      = (if j = 0 then (1 : ℂ) else 0)
        - (q : ℂ)⁻¹ * (ZMod.stdAddChar (-(j : ZMod q) * (i6 q : ZMod q))
            + ZMod.stdAddChar ((j : ZMod q) * (i6 q : ZMod q))) := by
  unfold modeCoeff
  rw [dif_neg (NeZero.ne q)]

/-- Summing over `ZMod q` = summing over the mode labels `0 … q-1`. -/
private theorem sum_range_natCast {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, F ((j : ℕ) : ZMod q) = ∑ j : ZMod q, F j := by
  have hinj : Set.InjOn (fun j : ℕ => ((j : ℕ) : ZMod q)) ↑(Finset.range q) := by
    intro a ha b hb hab
    have ha' : a < q := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < q := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    have hv : ((a : ℕ) : ZMod q).val = ((b : ℕ) : ZMod q).val := by
      simpa using congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt ha', ZMod.val_cast_of_lt hb'] at hv
  have himg : (Finset.range q).image (fun j : ℕ => ((j : ℕ) : ZMod q)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
  rw [← himg,
    Finset.sum_image fun a ha b hb hab =>
      hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab]

/-- **The per-clock mode expansion.**  Each clock factor `1 - strike₋ - strike₊` is the sum
    of its `q` modes, coefficient times wave.  Pure character algebra — holds for every
    center `m`, no divisibility involved. -/
theorem factor_eq_sum_modes {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (m : ℕ) :
    (1 : ℂ) - strikeSumMinus q m - strikeSumPlus q m
      = ∑ j ∈ Finset.range q, modeCoeff q j * modeWave q j m := by
  haveI := prime_neZero hq
  rw [strikeSumMinus_def, strikeSumPlus_def]
  have hterm : ∀ j ∈ Finset.range q, modeCoeff q j * modeWave q j m
      = (if j = 0 then (1 : ℂ) else 0)
          * ZMod.stdAddChar ((j : ZMod q) * (m : ZMod q))
        - (q : ℂ)⁻¹ * ZMod.stdAddChar ((j : ZMod q) * ((m : ZMod q) - (i6 q : ZMod q)))
        - (q : ℂ)⁻¹ * ZMod.stdAddChar ((j : ZMod q) * ((m : ZMod q) + (i6 q : ZMod q))) := by
    intro j _
    rw [modeCoeff_def, modeWave_def]
    have e1 : (j : ZMod q) * ((m : ZMod q) - (i6 q : ZMod q))
        = -(j : ZMod q) * (i6 q : ZMod q) + (j : ZMod q) * (m : ZMod q) := by ring
    have e2 : (j : ZMod q) * ((m : ZMod q) + (i6 q : ZMod q))
        = (j : ZMod q) * (i6 q : ZMod q) + (j : ZMod q) * (m : ZMod q) := by ring
    rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdelta : (∑ j ∈ Finset.range q, (if j = 0 then (1 : ℂ) else 0)
      * ZMod.stdAddChar ((j : ZMod q) * (m : ZMod q))) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) h0
  have hminus : (∑ j ∈ Finset.range q,
      (q : ℂ)⁻¹ * ZMod.stdAddChar ((j : ZMod q) * ((m : ZMod q) - (i6 q : ZMod q))))
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (j * ((m : ZMod q) - (i6 q : ZMod q))) := by
    rw [← Finset.mul_sum,
      sum_range_natCast fun x : ZMod q =>
        ZMod.stdAddChar (x * ((m : ZMod q) - (i6 q : ZMod q)))]
  have hplus : (∑ j ∈ Finset.range q,
      (q : ℂ)⁻¹ * ZMod.stdAddChar ((j : ZMod q) * ((m : ZMod q) + (i6 q : ZMod q))))
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (j * ((m : ZMod q) + (i6 q : ZMod q))) := by
    rw [← Finset.mul_sum,
      sum_range_natCast fun x : ZMod q =>
        ZMod.stdAddChar (x * ((m : ZMod q) + (i6 q : ZMod q)))]
  rw [hdelta, hminus, hplus]

/-- The mode tuples of scale `A`: one mode label `j_q ∈ range q` per clock `q`. -/
def modeTuples (A : ℕ) : Finset (∀ q ∈ clocks A, ℕ) :=
  (clocks A).pi fun q => Finset.range q

/-- The zero mode tuple — the diagonal of trivial modes. -/
def zeroMode (A : ℕ) : ∀ q ∈ clocks A, ℕ := fun _ _ => 0

theorem zeroMode_mem (A : ℕ) : zeroMode A ∈ modeTuples A := by
  simp only [modeTuples, Finset.mem_pi, zeroMode]
  intro q hq
  exact Finset.mem_range.mpr (by have := (mem_clocks.mp hq).2.1; omega)

/-- The amplitude `c(j)` of a mode tuple: the product of per-clock coefficients. -/
noncomputable def modeAmp (A : ℕ) (p : ∀ q ∈ clocks A, ℕ) : ℂ :=
  ∏ x ∈ (clocks A).attach, modeCoeff x.1 (p x.1 x.2)

/-- The window wave sum `S_W(j)` of a mode tuple: the window sum of products of waves. -/
noncomputable def modeWindowSum (A k g : ℕ) (p : ∀ q ∈ clocks A, ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc k (k + g), ∏ x ∈ (clocks A).attach, modeWave x.1 (p x.1 x.2) m

/-- **The engine decomposition (exact).**  The window count is the sum over ALL mode tuples
    of amplitude times window wave sum — `Finset.prod_sum` applied to the per-clock mode
    expansion inside the exact window identity of Part E2(a). -/
theorem cleanCount_eq_modeSum {A k g : ℕ} :
    (cleanCount A k g : ℂ)
      = ∑ p ∈ modeTuples A, modeAmp A p * modeWindowSum A k g p := by
  have h1 : (cleanCount A k g : ℂ)
      = ∑ m ∈ Finset.Ioc k (k + g), ∑ p ∈ (clocks A).pi (fun q => Finset.range q),
          ∏ x ∈ (clocks A).attach,
            (modeCoeff x.1 (p x.1 x.2) * modeWave x.1 (p x.1 x.2) m) := by
    rw [cleanCount_eq_window_prod_fourier]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hfac : ∀ q ∈ clocks A, ((1 : ℂ) - strikeSumMinus q m - strikeSumPlus q m)
        = ∑ j ∈ Finset.range q, modeCoeff q j * modeWave q j m := fun q hq => by
      obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
      exact factor_eq_sum_modes hp h5 m
    rw [Finset.prod_congr rfl hfac]
    exact Finset.prod_sum (clocks A) (fun q => Finset.range q)
      fun q j => modeCoeff q j * modeWave q j m
  rw [h1, Finset.sum_comm]
  simp only [modeTuples, modeAmp, modeWindowSum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  exact Finset.prod_mul_distrib

/-- The zero-mode coefficient of a clock is exactly its survival density `1 - 2/q`. -/
theorem modeCoeff_zero {q : ℕ} [NeZero q] : modeCoeff q 0 = 1 - 2 / (q : ℂ) := by
  rw [modeCoeff_def, if_pos rfl]
  simp only [Nat.cast_zero, neg_zero, zero_mul, AddChar.map_zero_eq_one]
  ring

theorem modeWave_zero {q m : ℕ} [NeZero q] : modeWave q 0 m = 1 := by
  rw [modeWave_def]
  simp

/-- **First anchor: `c(0)` is the density product.** -/
theorem modeAmp_zeroMode (A : ℕ) :
    modeAmp A (zeroMode A) = ∏ q ∈ clocks A, (1 - 2 / (q : ℂ)) := by
  simp only [modeAmp, zeroMode]
  rw [Finset.prod_attach (clocks A) fun q => modeCoeff q 0]
  refine Finset.prod_congr rfl fun q hq => ?_
  haveI : NeZero q := ⟨by have := (mem_clocks.mp hq).2.1; omega⟩
  exact modeCoeff_zero

/-- **Second anchor: `S_W(0) = g`.**  The trivial waves sum to the window length. -/
theorem modeWindowSum_zeroMode (A k g : ℕ) :
    modeWindowSum A k g (zeroMode A) = (g : ℂ) := by
  simp only [modeWindowSum, zeroMode]
  have hone : ∀ m ∈ Finset.Ioc k (k + g),
      (∏ x ∈ (clocks A).attach, modeWave x.1 0 m) = 1 := by
    intro m _
    apply Finset.prod_eq_one
    intro x _
    haveI : NeZero x.1 := ⟨by have := (mem_clocks.mp x.2).2.1; omega⟩
    exact modeWave_zero
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Ioc]
  simp

/-- The `ℂ`-cast of the rational main term is the zero-mode contribution. -/
theorem mainTerm_cast (A g : ℕ) :
    ((mainTerm A g : ℚ) : ℂ) = (g : ℂ) * ∏ q ∈ clocks A, (1 - 2 / (q : ℂ)) := by
  unfold mainTerm
  push_cast [Rat.cast_prod]
  rfl

/-- The zero mode contributes exactly the main term. -/
theorem zeroMode_contribution (A k g : ℕ) :
    modeAmp A (zeroMode A) * modeWindowSum A k g (zeroMode A)
      = ((mainTerm A g : ℚ) : ℂ) := by
  rw [modeAmp_zeroMode, modeWindowSum_zeroMode, mainTerm_cast]
  ring

/-- **THE ENGINES CARRY EXACTLY THE FLUCTUATION (Part E2b, main theorem).**  Splitting the
    engine decomposition at the zero tuple: the window fluctuation of Part R equals the sum
    over all NONTRIVIAL mode tuples of amplitude times window wave sum.  This is the
    mathematical body of the coherence pair: together with `defect_forces_coherence`, a
    window without a clean center forces ALL engine modes to conspire to a coherent spike
    of exact magnitude `mainTerm` — and any decay below full coherence
    (`oscillation_kills_defect`, `oscillation_plants_twin`) forces a clean center / twin.
    Exact finite identity; no bound on either side is claimed. -/
theorem windowFluct_eq_minorSum {A k g : ℕ} :
    ((windowFluct A k g : ℚ) : ℂ)
      = ∑ p ∈ (modeTuples A).erase (zeroMode A),
          modeAmp A p * modeWindowSum A k g p := by
  have hsplit : (∑ p ∈ modeTuples A, modeAmp A p * modeWindowSum A k g p)
      = modeAmp A (zeroMode A) * modeWindowSum A k g (zeroMode A)
        + ∑ p ∈ (modeTuples A).erase (zeroMode A),
            modeAmp A p * modeWindowSum A k g p :=
    (Finset.add_sum_erase _ _ (zeroMode_mem A)).symm
  have hcast : ((windowFluct A k g : ℚ) : ℂ)
      = (cleanCount A k g : ℂ) - ((mainTerm A g : ℚ) : ℂ) := by
    unfold windowFluct
    push_cast
    ring
  rw [hcast, cleanCount_eq_modeSum, hsplit, zeroMode_contribution]
  ring

/-- The coherence pair, engine form: a defect window (no clean center) forces the engine
    modes into the exactly coherent spike `-(mainTerm)`. -/
theorem defect_forces_engine_coherence {A k g : ℕ} (h : cleanCount A k g = 0) :
    (∑ p ∈ (modeTuples A).erase (zeroMode A), modeAmp A p * modeWindowSum A k g p)
      = -((mainTerm A g : ℚ) : ℂ) := by
  rw [← windowFluct_eq_minorSum, defect_forces_coherence h]
  push_cast
  ring

/-! ### Part E3 — a computable mod-`p` image (consistency gate, NOT the meaning layer)

The complex characters above are the meaning layer.  Over a finite field `ZMod p` with
`p ≡ 1 (mod q)` the same clock admits a COMPUTABLE character image (`AddChar.zmodChar`),
usable as a kernel consistency gate for mode tables: identities can be spot-checked by
`decide` in the image.  Mod-`p` images are consistency gates only — they do not carry the
archimedean size information of the `ℂ`-layer, and nothing in Parts R–E2 depends on them. -/

/-- `3` is a `5`-th root of unity in `ZMod 11` (`11 ≡ 1 (mod 5)`). -/
theorem zeta5_pow_eq_one : (3 : ZMod 11) ^ 5 = 1 := by decide

/-- The computable mod-`11` image of the `5`-clock character, `j ↦ 3^j`. -/
def zmodChar_5_11 : AddChar (ZMod 5) (ZMod 11) := AddChar.zmodChar 5 zeta5_pow_eq_one

/-- Consistency self-test: the image character is nontrivial at `1` (so the mode table of
    the clock `5` embeds faithfully into `ZMod 11`). -/
theorem zmodChar_5_11_nontrivial : zmodChar_5_11 1 ≠ 1 := by
  unfold zmodChar_5_11
  rw [AddChar.zmodChar_apply]
  decide

/-- Consistency self-test: a mode-table value, `ψ(2) = 3² = 9`. -/
theorem zmodChar_5_11_apply_two : zmodChar_5_11 2 = 9 := by
  unfold zmodChar_5_11
  rw [AddChar.zmodChar_apply]
  decide

/-!
### Axiom audit (performed with `#print axioms` from a scratch footer, then removed)

    #print axioms defect_forces_coherence        -- [propext, Classical.choice, Quot.sound]
    #print axioms oscillation_kills_defect       -- [propext, Classical.choice, Quot.sound]
    #print axioms oscillation_plants_twin        -- [propext, Classical.choice, Quot.sound]
    #print axioms perpetualEngine_iff_wall       -- [propext, Classical.choice, Quot.sound]
    #print axioms engineDecay_at_5 … at_37       -- [propext, Classical.choice, Quot.sound]
    #print axioms twinLowersInfinite_of_engineDecayCofinal
                                                 -- [propext, Classical.choice, Quot.sound]
    #print axioms delta_fourier                  -- [propext, Classical.choice, Quot.sound]
    #print axioms strike_minus_fourier           -- [propext, Classical.choice, Quot.sound]
    #print axioms cleanCount_eq_window_prod_fourier
                                                 -- [propext, Classical.choice, Quot.sound]
    #print axioms cleanCount_eq_modeSum          -- [propext, Classical.choice, Quot.sound]
    #print axioms windowFluct_eq_minorSum        -- [propext, Classical.choice, Quot.sound]
    #print axioms defect_forces_engine_coherence -- [propext, Classical.choice, Quot.sound]
    #print axioms zeta5_pow_eq_one               -- [propext, Quot.sound]
    #print axioms zmodChar_5_11_nontrivial       -- [propext, Quot.sound]
    #print axioms zmodChar_5_11_apply_two        -- [propext, Quot.sound]

No `sorryAx`, no `native_decide` (`Lean.ofReduceBool`), no `step00FirstCause`: the module is
green.  The standard triple enters through mathlib's analysis layer (`ℂ`, cyclotomic
machinery); the kernel self-tests (`decide`) add no axioms — the mod-`p` gate of Part E3 is
even `Classical.choice`-free.
-/

end StrikeFourier
end EuclidsPath
