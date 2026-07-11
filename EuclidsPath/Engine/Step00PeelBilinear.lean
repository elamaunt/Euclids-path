import EuclidsPath.Engine.GenealogyBasins
import EuclidsPath.Engine.Step00PhaseCoverKernel

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The peel bilinear layer — parity transport, edge counts, small-label confinement, target windows

The genealogical peel `PeelStep m t` (`GenealogyForest`) is a BILINEAR object: one wing of the
center `m` factors as `p · c` with a prime label `p ≥ 5` and a cofactor `c` that is itself a wing
of the target center `t`.  This file states the exact arithmetic identities that the bilinear
harness (`tools/peel_bilinear_harness.py`) normalizes against — the conservation laws of the
edge layer, nothing more:

* `wing_parity_transport` / `peel_parity_transport` — **the exact conservation law**: along EVERY
  peel edge `Ω(wing) = Ω(cofactor) + 1` (`ArithmeticFunction.cardFactors_mul` + the prime label);
* `peel_sign_flip` — its sign form: `(−1)^{Ω(wing)} = −(−1)^{Ω(cofactor)}` — every transition of
  the genealogy carries parity charge `−1`; the engine-oscillation sign flip
  (`Step00TwoEngineOscillation.signPair`) in graph form;
* `window_edge_count` — the canonical out-edge count of a window `(k, k+g]` EQUALS its non-twin
  center count (one canonical edge per non-twin center, `Finset.card_bij` on
  `m ↦ (m, canonicalPeel m)`);
* `struck_wing_minFac_le` + the kernel instance `defect_edges_small_labels_17` (`A = 17` defect
  window at `r = 502`, `decide +kernel` on the `allStruckB` Bool fold) — in a defect window every
  center's struck wing has `minFac ≤ A`: the out-edge label spectrum of a defect window is
  confined to `[5, A]` on one wing per center — the bilinear face of the defect;
* `peel_target_window` / `peel_target_window'` — a peel edge leaving the window `(k, k+g]` with
  label `p` lands in the EXACT ℕ-division interval
  `[(6k+5−p)/(6p), (6(k+g)+1+p)/(6p)]` — a defect window fans into at most `π(A)` renormalized
  windows `W/p`.

## DISCLOSURE (read this before anything else)

* `window_edge_count` is a RESTATEMENT: it grounds the harness normalization exactly (edges per
  window = non-twin centers per window) and claims nothing new — the content is the totality
  `peel_of_not_twin` / `canonicalPeel_isPeelStep`, proved upstream.
* The branch-and-bound tree of the phase-cover solver is a PROOF-SEARCH SHADOW, not an arithmetic
  object: tree-profile observables live only in the deterministic lean-model mode of the harness
  and get NO Lean statements here.
* Anti-vocabulary: nothing above certified scales.  No statement here multiplies twins, bounds a
  bilinear form, or estimates anything: every theorem is an exact finite identity or a kernel
  certificate at one explicit window.  `twin_prime_conjecture` stays untouched.
-/

namespace EuclidsPath
namespace PeelBilinear

open EuclidsPath.Residuals
open EuclidsPath.Genealogy
open EuclidsPath.GenealogyBasins
open EuclidsPath.PhaseCoverKernel
open ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-! ### 1. Parity transport: every peel edge carries parity charge −1 -/

/-- **The ℕ core of parity transport**: if a wing `S` factors as `p · c` with `p` prime and the
    cofactor `c` nonzero, then `Ω S = Ω c + 1` — peeling one prime label off shifts the
    Liouville grade by exactly one. -/
theorem wing_parity_transport {S c p : ℕ} (hp : p.Prime) (hc : c ≠ 0) (hS : S = p * c) :
    Ω S = Ω c + 1 := by
  subst hS
  rw [cardFactors_mul hp.ne_zero hc, cardFactors_apply_prime hp, Nat.add_comm]

/-- **`peel_parity_transport`: the exact conservation law of the peel layer.**  A peel step
    `PeelStep m t` exhibits a wing `S ∈ {6m−1, 6m+1}` of the source, a cofactor wing
    `c ∈ {6t−1, 6t+1}` of the target and a prime label `p ≥ 5` with `S = p · c`, `c ≥ 5`
    (cofactor `> 1` as promised by the witness data), and along the edge

      `Ω S = Ω c + 1`.

    This is `cardFactors_mul` + `cardFactors_apply_prime` transported through the `PeelStep`
    witness shape (the ε/δ sign bookkeeping of `GenealogyForest.PeelStep` done honestly in ℕ). -/
theorem peel_parity_transport {m t : ℕ} (h : PeelStep m t) :
    ∃ S c p : ℕ,
      (S = 6 * m - 1 ∨ S = 6 * m + 1) ∧
      (c = 6 * t - 1 ∨ c = 6 * t + 1) ∧
      p.Prime ∧ 5 ≤ p ∧ 5 ≤ c ∧ S = p * c ∧ Ω S = Ω c + 1 := by
  obtain ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩ := h
  have hpz : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
  have htz : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht1
  have hcz : (5 : ℤ) ≤ 6 * (t : ℤ) + δ := by rcases hδ with rfl | rfl <;> omega
  have hprod : (25 : ℤ) ≤ (p : ℤ) * (6 * (t : ℤ) + δ) := by
    calc (25 : ℤ) = 5 * 5 := by norm_num
      _ ≤ (p : ℤ) * (6 * (t : ℤ) + δ) :=
          mul_le_mul hpz hcz (by norm_num) (by omega)
  have hm4 : 4 ≤ m := by
    have : (4 : ℤ) ≤ (m : ℤ) := by rcases hε with rfl | rfl <;> omega
    exact_mod_cast this
  rcases hδ with rfl | rfl
  · -- cofactor `c = 6t + 1`
    have hccast : ((6 * t + 1 : ℕ) : ℤ) = 6 * (t : ℤ) + 1 := by push_cast; ring
    rcases hε with rfl | rfl
    · -- wing `S = 6m − 1`
      refine ⟨6 * m - 1, 6 * t + 1, p, Or.inl rfl, Or.inr rfl, hp, hp5, by omega, ?_, ?_⟩
      · have hcast : ((6 * m - 1 : ℕ) : ℤ) = ((p * (6 * t + 1) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * m)]
          linarith [heq]
        exact_mod_cast hcast
      · refine wing_parity_transport hp (by omega) ?_
        have hcast : ((6 * m - 1 : ℕ) : ℤ) = ((p * (6 * t + 1) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * m)]
          linarith [heq]
        exact_mod_cast hcast
    · -- wing `S = 6m + 1`
      refine ⟨6 * m + 1, 6 * t + 1, p, Or.inr rfl, Or.inr rfl, hp, hp5, by omega, ?_, ?_⟩
      · have hcast : ((6 * m + 1 : ℕ) : ℤ) = ((p * (6 * t + 1) : ℕ) : ℤ) := by
          push_cast
          linarith [heq]
        exact_mod_cast hcast
      · refine wing_parity_transport hp (by omega) ?_
        have hcast : ((6 * m + 1 : ℕ) : ℤ) = ((p * (6 * t + 1) : ℕ) : ℤ) := by
          push_cast
          linarith [heq]
        exact_mod_cast hcast
  · -- cofactor `c = 6t − 1`
    rcases hε with rfl | rfl
    · -- wing `S = 6m − 1`
      refine ⟨6 * m - 1, 6 * t - 1, p, Or.inl rfl, Or.inl rfl, hp, hp5, by omega, ?_, ?_⟩
      · have hcast : ((6 * m - 1 : ℕ) : ℤ) = ((p * (6 * t - 1) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * m), Nat.cast_sub (by omega : 1 ≤ 6 * t)]
          linarith [heq]
        exact_mod_cast hcast
      · refine wing_parity_transport hp (by omega) ?_
        have hcast : ((6 * m - 1 : ℕ) : ℤ) = ((p * (6 * t - 1) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * m), Nat.cast_sub (by omega : 1 ≤ 6 * t)]
          linarith [heq]
        exact_mod_cast hcast
    · -- wing `S = 6m + 1`
      refine ⟨6 * m + 1, 6 * t - 1, p, Or.inr rfl, Or.inl rfl, hp, hp5, by omega, ?_, ?_⟩
      · have hcast : ((6 * m + 1 : ℕ) : ℤ) = ((p * (6 * t - 1) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * t)]
          linarith [heq]
        exact_mod_cast hcast
      · refine wing_parity_transport hp (by omega) ?_
        have hcast : ((6 * m + 1 : ℕ) : ℤ) = ((p * (6 * t - 1) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 6 * t)]
          linarith [heq]
        exact_mod_cast hcast

/-- **`peel_sign_flip`: every transition between primes carries parity charge −1.**  The sign
    form of the conservation law: along every peel edge the wing sign is MINUS the cofactor sign,
    `(−1)^{Ω S} = −(−1)^{Ω c}` — the engine-oscillation sign flip
    (`TwoEngineOscillation.signPair`) as a statement about the genealogy graph's edges. -/
theorem peel_sign_flip {m t : ℕ} (h : PeelStep m t) :
    ∃ S c p : ℕ,
      (S = 6 * m - 1 ∨ S = 6 * m + 1) ∧
      (c = 6 * t - 1 ∨ c = 6 * t + 1) ∧
      p.Prime ∧ S = p * c ∧
      (-1 : ℤ) ^ Ω S = -((-1 : ℤ) ^ Ω c) := by
  obtain ⟨S, c, p, hS, hc, hp, hp5, hc5, hSc, hΩ⟩ := peel_parity_transport h
  exact ⟨S, c, p, hS, hc, hp, hSc, by rw [hΩ, pow_succ]; ring⟩

/-! ### 2. The window edge count — the harness normalization, disclosed as a restatement -/

/-- The non-twin centers of the window `(k, k+g]` — exactly the centers that peel
    (`peel_of_not_twin` / `not_peel_of_twin`). -/
def windowNonTwins (k g : ℕ) : Finset ℕ :=
  (Finset.Ioc k (k + g)).filter fun m => ¬ TwinCenterZ m

/-- The canonical out-edges of the window: one edge `(m, canonicalPeel m)` per non-twin center
    `m ∈ (k, k+g]` — the deterministic branch of the existential peel. -/
def windowPeelEdges (k g : ℕ) : Finset (ℕ × ℕ) :=
  (windowNonTwins k g).image fun m => (m, canonicalPeel m)

/-- **`window_edge_count` — DISCLOSED as a restatement.**  The number of non-twin centers of the
    window `(k, k+g]` EQUALS the number of canonical out-edges of the window
    (`Finset.card_bij` on `m ↦ (m, canonicalPeel m)`; the first component inverts the map).
    This grounds the harness normalization exactly — edges are counted per non-twin center, one
    canonical edge each — and claims nothing new: the mathematical content (a non-twin center
    peels, deterministically) is `canonicalPeel_isPeelStep`, proved upstream. -/
theorem window_edge_count (k g : ℕ) :
    (windowNonTwins k g).card = (windowPeelEdges k g).card :=
  Finset.card_bij (fun m _ => (m, canonicalPeel m))
    (fun m hm => Finset.mem_image_of_mem _ hm)
    (fun m₁ _ m₂ _ h => congrArg Prod.fst h)
    (fun e he => by
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
      exact ⟨m, hm, rfl⟩)

/-- Every canonical out-edge of the window is a genuine `PeelStep` (the side conditions
    `canonicalPeel` needs — `1 ≤ m`, non-twin — hold on `windowNonTwins`). -/
theorem windowPeelEdges_isPeelStep {k g : ℕ} {e : ℕ × ℕ}
    (he : e ∈ windowPeelEdges k g) : PeelStep e.1 e.2 := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hmem, hnt⟩ := Finset.mem_filter.mp hm
  exact canonicalPeel_isPeelStep (by have := (Finset.mem_Ioc.mp hmem).1; omega) hnt

/-! ### 3. Small-label confinement: the bilinear face of the defect -/

/-- **A struck wing has a small minimal label**: if a prime `q ≤ A` divides the wing `w`, then
    `w.minFac ≤ q ≤ A`.  This is the EXACT mechanical part that the harness subtracts from the
    dyadic label profile O1 before any verdict is read (`Nat.minFac_le_of_dvd`). -/
theorem struck_wing_minFac_le {q A w : ℕ} (hq : q.Prime) (hqA : q ≤ A) (hd : q ∣ w) :
    w.minFac ≤ q ∧ w.minFac ≤ A := by
  have h := Nat.minFac_le_of_dvd hq.two_le hd
  exact ⟨h, le_trans h hqA⟩

set_option maxRecDepth 100000 in
/-- SAT-side kernel gate for the SECOND `A = 17` defect window (`r = 502`; full-period scan,
    `tools/gap_extremal_run1.log` — the first, `r = 117`, is kernel-pinned upstream as
    `PhaseCoverKernel.allStruck_17`): the 17 centers `r+1 … r+17` are all struck by the clocks
    `{5, 7, 11, 13, 17}` (trial-division Bool fold, `allStruckB` style, `decide +kernel`,
    trivial budget). -/
theorem allStruck_17_r502 : allStruckB (smallClocks ++ bigs17) 502 17 = true := by
  decide +kernel

/-- Extract the per-center strike (a listed clock divides a wing) from the `allStruckB` fold. -/
private theorem struck_of_allStruckB {C : List CoverClock} {r len j : ℕ}
    (h : allStruckB C r len = true) (hj : j < len) :
    ∃ p, p ∈ C ∧ (p.1 ∣ (6 * (r + 1 + j) - 1) ∨ p.1 ∣ (6 * (r + 1 + j) + 1)) := by
  have hall := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  have hall' :
      (C.any fun p =>
        ((6 * (r + 1 + j) - 1) % p.1 == 0) || ((6 * (r + 1 + j) + 1) % p.1 == 0)) = true := hall
  obtain ⟨p, hp, hstrike⟩ := List.any_eq_true.mp hall'
  rw [Bool.or_eq_true] at hstrike
  rcases hstrike with hs | hs
  · exact ⟨p, hp, Or.inl (Nat.dvd_of_mod_eq_zero (by simpa using hs))⟩
  · exact ⟨p, hp, Or.inr (Nat.dvd_of_mod_eq_zero (by simpa using hs))⟩

/-- **`defect_edges_small_labels_17`: the bilinear face of the defect, one kernel witness.**
    At the `A = 17` defect window `r = 502` every center `502 + 1 + j` (`j < 17`) has a wing
    whose minimal prime label is `≤ 17`: defect windows are exactly the windows whose out-edge
    label spectrum is confined to `[5, A]` on one wing each.  Combines the kernel SAT gate
    `allStruck_17_r502` with `struck_wing_minFac_le`. -/
theorem defect_edges_small_labels_17 :
    ∀ j : ℕ, j < 17 →
      (6 * (502 + 1 + j) - 1).minFac ≤ 17 ∨ (6 * (502 + 1 + j) + 1).minFac ≤ 17 := by
  intro j hj
  obtain ⟨p, hpmem, hor⟩ := struck_of_allStruckB allStruck_17_r502 hj
  have hsc : ∀ p' ∈ smallClocks ++ bigs17, p'.1.Prime ∧ p'.1 ≤ 17 := by decide
  obtain ⟨hpr, hple⟩ := hsc p hpmem
  rcases hor with hd | hd
  · exact Or.inl (struck_wing_minFac_le hpr hple hd).2
  · exact Or.inr (struck_wing_minFac_le hpr hple hd).2

/-- Every center of the `r = 502` defect window is a NON-twin (its small-label wing is
    composite: a prime wing would be its own `minFac`, but the wings exceed `17`).  So the
    17 centers all carry canonical out-edges (`window_edge_count` applies with full count). -/
theorem defect_window_nonTwin_17 :
    ∀ j : ℕ, j < 17 → ¬ TwinCenterZ (502 + 1 + j) := by
  intro j hj htw
  rcases defect_edges_small_labels_17 j hj with hle | hle
  · have := htw.1.minFac_eq
    omega
  · have := htw.2.minFac_eq
    omega

/-! ### 4. The renormalized target window: a defect fans into ≤ π(A) windows `W/p` -/

/-- **`peel_target_window`: the exact ℕ-division interval of a peel target.**  If a peel edge
    with witness data `(ε, δ, p)` leaves a source `m ∈ (k, k+g]`, its target `t` is confined to

      `(6k + 5 − p) / (6p)  ≤  t  ≤  (6(k+g) + 1 + p) / (6p)`   (ℕ floor division).

    Honest bookkeeping: from `6m − ε = p(6t + δ)` and `k < m ≤ k + g` one gets
    `6k + 5 ≤ 6m − ε ≤ 6(k+g) + 1` and `p(6t − 1) ≤ p(6t + δ) ≤ p(6t + 1)`, hence
    `6k + 5 − p ≤ 6pt ≤ 6(k+g) + 1 + p`, and `t = 6pt/(6p)` is squeezed by
    `Nat.div_le_div_right`.  The lower endpoint `(6k+5−p)/(6p)` is the exactly-provable
    sharpening of the `(6k+1−p)/(6p)` form (the window floor `m ≥ k+1` gives `6m−1 ≥ 6k+5`).
    Primality of `p` is NOT needed — `5 ≤ p` suffices.  Consequence: a defect window fans into
    at most `π(A)` renormalized windows `W/p`, one per label `p ∈ [5, A]` — the exact intervals
    the harness's cascade observable O5 measures. -/
theorem peel_target_window {k g m t p : ℕ} {ε δ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (hp5 : 5 ≤ p) (ht : 1 ≤ t)
    (heq : 6 * (m : ℤ) - ε = (p : ℤ) * (6 * (t : ℤ) + δ))
    (hk : k < m) (hkg : m ≤ k + g) :
    (6 * k + 5 - p) / (6 * p) ≤ t ∧ t ≤ (6 * (k + g) + 1 + p) / (6 * p) := by
  have hp0 : 0 < 6 * p := by omega
  have hpz : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
  have htz : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  have hkz : (k : ℤ) < (m : ℤ) := by exact_mod_cast hk
  have hgz : (m : ℤ) ≤ (k : ℤ) + (g : ℤ) := by exact_mod_cast hkg
  have hεb : -1 ≤ ε ∧ ε ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
  have hpd : -(p : ℤ) ≤ (p : ℤ) * δ ∧ (p : ℤ) * δ ≤ (p : ℤ) := by
    rcases hδ with rfl | rfl
    · rw [mul_one]; omega
    · rw [mul_neg_one]; omega
  -- the two linear bounds on `6pt` (products `p·t`, `p·δ` treated as atoms by `linarith`)
  have hupZ : ((6 * p * t : ℕ) : ℤ) ≤ ((6 * (k + g) + 1 + p : ℕ) : ℤ) := by
    push_cast
    nlinarith [heq, hpd.1, hpd.2, hεb.1, hεb.2, hgz]
  have hloZ : ((6 * k + 5 : ℕ) : ℤ) ≤ ((6 * p * t + p : ℕ) : ℤ) := by
    push_cast
    nlinarith [heq, hpd.1, hpd.2, hεb.1, hεb.2, hkz]
  have hupn : 6 * p * t ≤ 6 * (k + g) + 1 + p := by exact_mod_cast hupZ
  have hlon : 6 * k + 5 ≤ 6 * p * t + p := by exact_mod_cast hloZ
  constructor
  · have h1 : 6 * k + 5 - p ≤ 6 * p * t := tsub_le_iff_right.mpr hlon
    calc (6 * k + 5 - p) / (6 * p) ≤ 6 * p * t / (6 * p) := Nat.div_le_div_right h1
      _ = t := Nat.mul_div_cancel_left t hp0
  · calc t = 6 * p * t / (6 * p) := (Nat.mul_div_cancel_left t hp0).symm
      _ ≤ (6 * (k + g) + 1 + p) / (6 * p) := Nat.div_le_div_right hupn

/-- The `PeelStep`-existential form of `peel_target_window`: every peel edge leaving the window
    `(k, k+g]` lands in the renormalized window of ITS OWN prime label `p`. -/
theorem peel_target_window' {k g m t : ℕ} (hk : k < m) (hkg : m ≤ k + g)
    (h : PeelStep m t) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
      (6 * k + 5 - p) / (6 * p) ≤ t ∧ t ≤ (6 * (k + g) + 1 + p) / (6 * p) := by
  obtain ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩ := h
  exact ⟨p, hp, hp5, peel_target_window hε hδ hp5 ht1 heq hk hkg⟩

end PeelBilinear
end EuclidsPath

/-
  ### Machine honesty (recorded `#print axioms` output)

  Checked with a scratch footer (`lake env lean`, footer then removed); every declaration of
  this file sits under the standard axioms only — no `sorry`, no `step00FirstCause`, no
  `native_decide` (`Lean.ofReduceBool`):

  * `wing_parity_transport`            — `[propext, Classical.choice, Quot.sound]`
  * `peel_parity_transport`            — `[propext, Classical.choice, Quot.sound]`
  * `peel_sign_flip`                   — `[propext, Classical.choice, Quot.sound]`
  * `windowNonTwins` / `windowPeelEdges` — `[propext, Classical.choice, Quot.sound]`
  * `window_edge_count`                — `[propext, Classical.choice, Quot.sound]`
  * `windowPeelEdges_isPeelStep`       — `[propext, Classical.choice, Quot.sound]`
  * `struck_wing_minFac_le`            — `[propext, Classical.choice, Quot.sound]`
  * `allStruck_17_r502`                — `[propext, Classical.choice, Quot.sound]`
  * `defect_edges_small_labels_17`     — `[propext, Classical.choice, Quot.sound]`
  * `defect_window_nonTwin_17`         — `[propext, Classical.choice, Quot.sound]`
  * `peel_target_window`               — `[propext, Classical.choice, Quot.sound]`
  * `peel_target_window'`              — `[propext, Classical.choice, Quot.sound]`
-/
