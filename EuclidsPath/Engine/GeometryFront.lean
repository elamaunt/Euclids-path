/-
  GeometryFront — Euclid's Path geometry: arrow of time, curvature (COMPUTED!),
  intersection of lines.

  The concrete Step00 graph (State: center/defect/absorber, RealStep: clean/boundary/
  peel/absorb) is read GEOMETRICALLY: edges are geodesic segments, lexRank is
  proper time, legal paths are "lines". Machine-proven here:
    • ARROW OF TIME: lexRank strictly drops on every edge and on every non-empty
      path; there is no return (no_return), no eternal run (no_eternal_run), every
      route halts no later than in lexRank of the starting state;
    • CURVATURE: κ(v) = 1 − outdeg(v) is COMPUTED — out-sets are presented as
      Finsets and proven to coincide EXACTLY with RealStep (mem_outTargets);
      everywhere-nonpositive curvature BUILDS a perpetual engine (forbidden), hence
      space is somewhere positively curved; the spectrum of values at (A,M0)=(5,4)
      computed by the kernel (decide): absorbers +1, flat corridors 0, a branching
      defect −1, clean centers −3, −4, −8; discrete Gauss–Bonnet on a
      forward-closed cone: χ(cone3) = −5;
    • LINES: every line is finite and runs into a terminal (every_line_ends);
      there are NO infinite lines (no_infinite_line) — and hence no parallels;
      web: above every horizon there is a clean-center whose path leads to the grave
      of zero absorber 0 (web_above_every_horizon); two clean-lines meet
      in a common terminal (lines_meet_at_origin).

  HONEST BOUNDARIES (disclosed loudly, in order of importance):

  1. "CURVATURE" HERE is COMBINATORIAL curvature of a directed graph:
     κ(v) = 1 − outdeg(v), the deficit/excess of the outgoing geodesic flow.
     This is NOT Riemannian curvature, NOT sectional, NOT Ricci–Ollivier; there is
     no metric, no tensors, no smooth structure. The word "curvature" is legitimate
     exactly in the sense of discrete graph theory (an analogue of Euler's formula/
     combinatorial Gauss–Bonnet), and only in it.

  2. CURVATURE IS COMPUTED FORWARD ONLY — and this is a THEOREM, not a convenience:
     the in-degree at the source is INFINITE (inDegree_infinite_at_origin — into
     absorber 0 enters the infinite family of defects defect 0 q minus over all q).
     A symmetric "total degree" does not exist as a Finset; the oriented
     κ = 1 − outdeg is the only computable version.

  3. THE GRAVE OF ZERO lives on the ℕ-truncation: sideValue Side.minus 0 = 6·0 − 1 = 0
     (in ℕ!), and hence ANY prime q divides the side of the 0-center
     (zeroPoint_absorbs_all_divisors). This is both an ARTIFACT of truncated
     subtraction AND a marker of the event 0 → 1 from the first cause: the point 0 is the only one
     whose sides absorb all divisors at once, all roads down are passable through
     it. We do NOT claim that arithmetic "knows" about 6·0−1 = 0 in ℤ — in ℤ
     it is −1; the geometry of the grave is a property of the ℕ-model of the graph.

  4. NAIVE ELLIPTICITY IS FALSE: the bottom is NOT unique (bottom_not_unique —
     absorber 0 and absorber 1 are both legal and terminal), and TWO
     fully disjoint finite lines are presented (two_disjoint_lines). "All
     lines meet" holds ONLY in the qualified form
     lines_meet_at_origin: for clean-STARTS there exists a COMMON terminal
     (the grave of zero), not for arbitrary paths and not a unique terminal.

  5. THE CARRIER THEOREM of the absence of parallels — no_infinite_line: in this world
     EUCLID'S SECOND POSTULATE FALLS (a line cannot be extended indefinitely),
     not the fifth. "There are no parallels" (no_parallel_lines) is a consequence of
     there being no infinite lines AT ALL; this is a degenerate, not an elliptic
     geometry. Whoever wants to read this as "ellipticity" — must read
     it through point 4.

  6. 🟡-CODA (§6): EXACTLY TWO declarations are tainted by the axiom step00FirstCause —
     twin_vertices_beyond_every_horizon and lines_meet_but_unknowable_from_inside.
     The taint runs through the EXISTING causal boundary
     (twinLowersInfinite_from_step00CausalClosure) — no new axiom,
     no new content of the decree: only the already-accepted twins boundary,
     translated into the language of graph vertices. Everything else in the file is 🟢
     (axiom-free: propext, Classical.choice, Quot.sound).

  Name-collision precedent (as in HodgeFront): EuclidsPath.Engine.* (EPMI,
  Irreversibility) are used ONLY qualified — they have their own State/Step there.
-/
import Mathlib
import EuclidsPath.Engine.Irreversibility
import EuclidsPath.Engine.CausalClosureAxiom

set_option autoImplicit false

namespace EuclidsPath.GeometryFront

open EuclidsPath.CleanGraph
open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.LabelledFanIn
open EuclidsPath.BoundaryLedgerCollision

/-#############################################################################
  §0. Decidability: Clean and Legal are computable
#############################################################################-/

/--
  **Bounded form of Clean.** `Clean A m` quantifies over ALL `q : ℕ`, but
  the condition `q ≤ A` bounds the carrier: `q ∈ range (A+1)` suffices. This
  form yields decidability — and together with it all of the computed curvature of §2.
-/
theorem clean_iff_bounded (A m : ℕ) :
    Clean A m ↔
      ∀ q ∈ Finset.range (A + 1), q.Prime →
        ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1)) := by
  constructor
  · intro h q hq hqp
    exact h q hqp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
  · intro h q hqp hqA
    exact h q (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hqA)) hqp

/-- Kernel-friendly decidability of primality (for `decide` in §2). -/
local instance (priority := 2000) primeDecidableGeom (n : ℕ) : Decidable n.Prime :=
  decidable_of_iff' _ Nat.prime_def_lt

/-- `Clean` is decidable — via the bounded form. -/
instance cleanDecidable (A m : ℕ) : Decidable (Clean A m) :=
  decidable_of_iff' _ (clean_iff_bounded A m)

/-- `Legal` is decidable on each sort of state. -/
instance legalDecidable (A M0 : ℕ) (v : State) : Decidable (Legal A M0 v) :=
  match v with
  | State.center m => inferInstanceAs (Decidable (Clean A m))
  | State.defect n q s =>
      inferInstanceAs (Decidable (q.Prime ∧ q ≤ A ∧ q ∣ sideValue s n))
  | State.absorber a => inferInstanceAs (Decidable (a ≤ M0))

/-#############################################################################
  §1. Arrow of time (🟢): lexRank is proper time, it only drops
#############################################################################-/

/-- **Arrow of time on a single edge**: every real step strictly decreases
    lexRank. Re-export of the carrier theorem of the concrete graph. -/
theorem timeArrow_step {A M0 : ℕ} {U V : State}
    (h : RealStep A M0 U V) : lexRank V < lexRank U :=
  lexRank_strict_decrease_on_RealStep h

/-- **Arrow of time on a path**: along any NON-EMPTY path lexRank strictly
    drops. -/
theorem timeArrow_path {A M0 n : ℕ} {X Y : State}
    (hpos : 0 < n) (hpath : PathN (RealStep A M0) n X Y) :
    lexRank Y < lexRank X :=
  pathN_rank_strict_of_pos_of_step_decrease
    (fun h => lexRank_strict_decrease_on_RealStep h) hpos hpath

/-- **No return**: no state is reachable from itself by a non-empty
    path. Time is not looped. -/
theorem no_return {A M0 : ℕ} (W : State) :
    ¬ NonemptyPath (RealStep A M0) W W :=
  no_concrete_nonemptyPath_by_lexRank W

/-- **Strict anti-monotonicity of time along a run**: if `run` takes
    real steps at least up to moment `k`, then lexRank strictly decreases on the whole
    segment `[0, k]`. -/
theorem time_strictAnti_on_run {A M0 : ℕ} (run : ℕ → State) (k : ℕ)
    (hrun : ∀ t, t < k → RealStep A M0 (run t) (run (t + 1))) :
    ∀ i j, i < j → j ≤ k → lexRank (run j) < lexRank (run i) := by
  intro i j hij hjk
  induction j with
  | zero => omega
  | succ n ih =>
      have hstep : lexRank (run (n + 1)) < lexRank (run n) :=
        lexRank_strict_decrease_on_RealStep (hrun n (by omega))
      by_cases h : i < n
      · have := ih h (by omega)
        omega
      · have hi : i = n := by omega
        subst hi
        exact hstep

/-- **Every route halts**: `k` real steps are possible only when
    `k ≤ lexRank (run 0)`. A qualified "second law" via
    `Engine.turned_engine_halts`. -/
theorem every_journey_halts {A M0 : ℕ} (run : ℕ → State) (k : ℕ)
    (hrun : ∀ t, t < k → RealStep A M0 (run t) (run (t + 1))) :
    k ≤ lexRank (run 0) :=
  EuclidsPath.Engine.turned_engine_halts (fun t => lexRank (run t)) k
    (fun t ht => lexRank_strict_decrease_on_RealStep (hrun t ht))

/-- **No eternal run**: an infinite chain of real steps is impossible.
    Direct application of the root EPMI (`Engine.no_infinite_descent`, A = 1). -/
theorem no_eternal_run {A M0 : ℕ} (H : ℕ → State)
    (hchain : ∀ t, RealStep A M0 (H t) (H (t + 1))) : False :=
  EuclidsPath.Engine.no_infinite_descent (le_refl 1)
    (fun t => lexRank (H t))
    (fun t => by
      show 1 * lexRank (H (t + 1)) < lexRank (H t)
      have := lexRank_strict_decrease_on_RealStep (hchain t)
      omega)

/-#############################################################################
  §2. Curvature (🟢): κ = 1 − outdeg, out-sets are COMPUTED and proven exact
#############################################################################-/

/-- Both sides as a finite set. -/
def sideFinset : Finset Side := {Side.minus, Side.plus}

theorem mem_sideFinset (s : Side) : s ∈ sideFinset := by
  cases s <;> simp [sideFinset]

/-- Targets of a clean-step from center `m`: clean centers strictly below `m`
    (`CleanActiveEdge = Clean ∧ Clean ∧ n < m`). Empty if `m` itself is not clean. -/
def cleanTargets (A m : ℕ) : Finset State :=
  if Clean A m then
    ((Finset.range m).filter (fun n => Clean A n)).image State.center
  else ∅

/-- Targets of a boundary-step from center `m`: defects `defect n q s` with `n < m`,
    prime `q ≤ A` and `q ∣ sideValue s n`. Empty if `m` is not clean. -/
def boundaryTargets (A m : ℕ) : Finset State :=
  if Clean A m then
    (((Finset.range m) ×ˢ ((Finset.range (A + 1)) ×ˢ sideFinset)).filter
      (fun x => x.2.1.Prime ∧ x.2.1 ∣ sideValue x.2.2 x.1)).image
      (fun x => State.defect x.1 x.2.1 x.2.2)
  else ∅

/-- Targets of a peel-step from defect `defect n q s`: centers `t < n` for which
    some side `outSide` gives an exact factorization
    `sideValue s n = q * sideValue outSide t` (fields of `PeelCert`). -/
def peelTargets (n q : ℕ) (s : Side) : Finset State :=
  (((Finset.range n) ×ˢ sideFinset).filter
    (fun x => sideValue s n = q * sideValue x.2 x.1)).image
    (fun x => State.center x.1)

/-- Targets of an absorb-step from a defect with center `n`: the old absorber `absorber n`,
    if `n ≤ M0`. -/
def absorbTargets (M0 n : ℕ) : Finset State :=
  if n ≤ M0 then {State.absorber n} else ∅

/-- **Computed out-set** of a vertex: all targets of all four constructors of
    `RealStep`. An absorber is a terminal: no targets. -/
def outTargets (A M0 : ℕ) : State → Finset State
  | State.center m => cleanTargets A m ∪ boundaryTargets A m
  | State.defect n q s => peelTargets n q s ∪ absorbTargets M0 n
  | State.absorber _ => ∅

/-! Four specification lemmas: each Finset-set coincides with its
    `RealStep` constructor exactly. -/

theorem mem_cleanTargets {A m : ℕ} {w : State} :
    w ∈ cleanTargets A m ↔
      Clean A m ∧ ∃ n, Clean A n ∧ n < m ∧ w = State.center n := by
  unfold cleanTargets
  split_ifs with hm
  · constructor
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨n, hn, rfl⟩
      rcases Finset.mem_filter.mp hn with ⟨hnr, hcn⟩
      exact ⟨hm, n, hcn, Finset.mem_range.mp hnr, rfl⟩
    · rintro ⟨-, n, hcn, hn, rfl⟩
      exact Finset.mem_image.mpr
        ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hcn⟩, rfl⟩
  · constructor
    · intro hw
      exact absurd hw (Finset.notMem_empty w)
    · rintro ⟨hm', -⟩
      exact absurd hm' hm

theorem mem_boundaryTargets {A m : ℕ} {w : State} :
    w ∈ boundaryTargets A m ↔
      Clean A m ∧ ∃ n q s, n < m ∧ q.Prime ∧ q ≤ A ∧ q ∣ sideValue s n ∧
        w = State.defect n q s := by
  unfold boundaryTargets
  split_ifs with hm
  · constructor
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨x, hx, rfl⟩
      rcases Finset.mem_filter.mp hx with ⟨hxmem, hxprop⟩
      rcases Finset.mem_product.mp hxmem with ⟨hx1, hx23⟩
      rcases Finset.mem_product.mp hx23 with ⟨hx2, -⟩
      refine ⟨hm, x.1, x.2.1, x.2.2, Finset.mem_range.mp hx1, hxprop.1, ?_,
        hxprop.2, rfl⟩
      have := Finset.mem_range.mp hx2
      omega
    · rintro ⟨-, n, q, s, hn, hqp, hqA, hdvd, rfl⟩
      refine Finset.mem_image.mpr ⟨(n, q, s), ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, hqp, hdvd⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr hn, ?_⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by dsimp only; omega), mem_sideFinset s⟩
  · constructor
    · intro hw
      exact absurd hw (Finset.notMem_empty w)
    · rintro ⟨hm', -⟩
      exact absurd hm' hm

theorem mem_peelTargets {n q : ℕ} {s : Side} {w : State} :
    w ∈ peelTargets n q s ↔
      ∃ t outSide, t < n ∧ sideValue s n = q * sideValue outSide t ∧
        w = State.center t := by
  unfold peelTargets
  constructor
  · intro hw
    rcases Finset.mem_image.mp hw with ⟨x, hx, rfl⟩
    rcases Finset.mem_filter.mp hx with ⟨hxmem, hxprop⟩
    rcases Finset.mem_product.mp hxmem with ⟨hx1, -⟩
    exact ⟨x.1, x.2, Finset.mem_range.mp hx1, hxprop, rfl⟩
  · rintro ⟨t, os, ht, hfac, rfl⟩
    refine Finset.mem_image.mpr ⟨(t, os), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ht, mem_sideFinset os⟩, hfac⟩

theorem mem_absorbTargets {M0 n : ℕ} {w : State} :
    w ∈ absorbTargets M0 n ↔ n ≤ M0 ∧ w = State.absorber n := by
  unfold absorbTargets
  split_ifs with h
  · constructor
    · intro hw
      exact ⟨h, Finset.mem_singleton.mp hw⟩
    · rintro ⟨-, rfl⟩
      exact Finset.mem_singleton.mpr rfl
  · constructor
    · intro hw
      exact absurd hw (Finset.notMem_empty w)
    · rintro ⟨hle, -⟩
      exact absurd hle h

/--
  **CARRIER LEMMA §2**: the computed out-set coincides EXACTLY with `RealStep`.
  All the ensuing "curvature" is honest: `outDeg` counts the real edges of the graph,
  not an abstraction.
-/
theorem mem_outTargets {A M0 : ℕ} {v w : State} :
    w ∈ outTargets A M0 v ↔ RealStep A M0 v w := by
  cases v with
  | center m =>
      simp only [outTargets]
      constructor
      · intro hw
        rcases Finset.mem_union.mp hw with h | h
        · rcases mem_cleanTargets.mp h with ⟨hm, n, hcn, hn, rfl⟩
          exact RealStep.clean ⟨hm, hcn, trivial, hn⟩
        · rcases mem_boundaryTargets.mp h with ⟨hm, n, q, s, hn, hqp, hqA, hdvd, rfl⟩
          exact RealStep.boundary hm ⟨trivial, hn⟩ hqp hqA hdvd
      · intro hstep
        cases hstep with
        | clean h =>
            exact Finset.mem_union.mpr
              (Or.inl (mem_cleanTargets.mpr ⟨h.1, _, h.2.1, h.2.2.2, rfl⟩))
        | boundary hm hEdge hqp hqA hdvd =>
            exact Finset.mem_union.mpr
              (Or.inr (mem_boundaryTargets.mpr
                ⟨hm, _, _, _, hEdge.2, hqp, hqA, hdvd, rfl⟩))
  | defect n q s =>
      simp only [outTargets]
      constructor
      · intro hw
        rcases Finset.mem_union.mp hw with h | h
        · rcases mem_peelTargets.mp h with ⟨t, os, ht, hfac, rfl⟩
          exact RealStep.peel ⟨hfac, ht⟩
        · rcases mem_absorbTargets.mp h with ⟨hle, rfl⟩
          exact RealStep.absorb hle
      · intro hstep
        cases hstep with
        | peel h =>
            exact Finset.mem_union.mpr
              (Or.inl (mem_peelTargets.mpr ⟨_, _, h.smaller, h.factor, rfl⟩))
        | absorb hle =>
            exact Finset.mem_union.mpr
              (Or.inr (mem_absorbTargets.mpr ⟨hle, rfl⟩))
  | absorber a =>
      simp only [outTargets]
      constructor
      · intro hw
        exact absurd hw (Finset.notMem_empty w)
      · intro hstep
        cases hstep

/-- Out-degree of a vertex — COMPUTED. -/
def outDeg (A M0 : ℕ) (v : State) : ℕ := (outTargets A M0 v).card

/-- **Combinatorial curvature** of a directed graph: κ(v) = 1 − outdeg(v).
    NOT Riemannian (see honest boundary №1 in the header): the deficit of the outgoing
    geodesic flow. κ > 0 — the flow dies out (terminals), κ = 0 — a flat corridor,
    κ < 0 — branching (hyperbolicity). -/
def curvature (A M0 : ℕ) (v : State) : ℤ := 1 - (outDeg A M0 v : ℤ)

/-- Nonpositive curvature ⟹ there is an outgoing edge. -/
theorem hasStep_of_curvature_nonpos {A M0 : ℕ} {v : State}
    (h : curvature A M0 v ≤ 0) : ∃ w, RealStep A M0 v w := by
  have hpos : 0 < (outTargets A M0 v).card := by
    unfold curvature outDeg at h
    omega
  rcases Finset.card_pos.mp hpos with ⟨w, hw⟩
  exact ⟨w, mem_outTargets.mp hw⟩

/--
  **ENGINE-FROM-FLATNESS THEOREM**: if curvature were EVERYWHERE ≤ 0,
  a step would leave every vertex — and iterating the choice would build an eternal run,
  forbidden by EPMI. A nonpositively curved Euclidean world does NOT exist.
-/
theorem nonpositive_curvature_forces_engine {A M0 : ℕ}
    (hflat : ∀ v, curvature A M0 v ≤ 0) : False := by
  classical
  have hnext : ∀ v : State, ∃ w, RealStep A M0 v w :=
    fun v => hasStep_of_curvature_nonpos (hflat v)
  let next : State → State := fun v => Classical.choose (hnext v)
  have hstep : ∀ v, RealStep A M0 v (next v) :=
    fun v => Classical.choose_spec (hnext v)
  have hchain : ∀ t, RealStep A M0
      (next^[t] (State.absorber 0)) (next^[t + 1] (State.absorber 0)) := by
    intro t
    rw [Function.iterate_succ_apply' next t (State.absorber 0)]
    exact hstep _
  exact no_eternal_run (fun t => next^[t] (State.absorber 0)) hchain

/-- A fully flat world (κ ≡ 0) — also an engine. -/
theorem flat_everywhere_forces_engine {A M0 : ℕ}
    (hflat : ∀ v, curvature A M0 v = 0) : False :=
  nonpositive_curvature_forces_engine (fun v => le_of_eq (hflat v))

/-- **Space is somewhere positively curved** — otherwise an engine. -/
theorem space_positively_curved_somewhere (A M0 : ℕ) :
    ∃ v, 0 < curvature A M0 v := by
  by_contra h
  push_neg at h
  exact nonpositive_curvature_forces_engine h

/-- The space of Euclid's Path is NOT flat. -/
theorem space_is_curved (A M0 : ℕ) : ∃ v, curvature A M0 v ≠ 0 := by
  obtain ⟨v, hv⟩ := space_positively_curved_somewhere A M0
  exact ⟨v, by omega⟩

/-- A closed geodesic = a legal non-empty cycle = an engine witness. -/
abbrev ClosedGeodesic (A M0 : ℕ) : Prop :=
  EuclidsPath.BoundaryLedgerCollision.LegalCycle (RealStep A M0) (Legal A M0)

/-- A closed geodesic is exactly a witness of Euclid's perpetual engine. -/
theorem closedGeodesic_is_engineWitness {A M0 : ℕ}
    (h : ClosedGeodesic A M0) : ConcreteEuclideanEngineWitness A M0 :=
  ⟨h⟩

/-- **There are no closed geodesics** (re-export of lexRank-acyclicity). -/
theorem no_closedGeodesic (A M0 : ℕ) : ¬ ClosedGeodesic A M0 :=
  no_concrete_legalCycle_by_lexRank

/-!
  ### HONESTY: why κ is computed FORWARD only

  In-degree does not exist as a Finset: the grave of zero has infinitely many
  predecessors. Symmetric ("undirected") curvature is uncomputable
  in principle — theorem below.
-/

/-- **In-degree at the source is INFINITE**: into `absorber 0` enters the whole family
    of defects `defect 0 q Side.minus` over all `q : ℕ` (the absorb-edge requires
    only `0 ≤ M0`). Hence curvature is oriented forward — not by convenience,
    but by theorem. -/
theorem inDegree_infinite_at_origin (A M0 : ℕ) :
    {u : State | RealStep A M0 u (State.absorber 0)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun q : ℕ => State.defect 0 q Side.minus)
  · intro a b hab
    simpa using hab
  · intro q
    exact RealStep.absorb (Nat.zero_le M0)

/-!
  ### Curvature spectrum at (A, M0) = (5, 4) — computed by the kernel (`decide`)

  Philosophical reading: absorbers are "poles" (κ = +1, the flow dies out), defects
  with a single peel are flat corridors (κ = 0), a defect with peel AND absorb is
  branching (κ = −1), clean centers are ever more hyperbolic funnels
  (κ = −3, −4, −8): the higher the center, the more roads down.
-/

/-- Absorbers are vertices of positive curvature: κ = +1 (terminal). -/
theorem curvature_absorber (A M0 a : ℕ) :
    curvature A M0 (State.absorber a) = 1 := by
  simp [curvature, outDeg, outTargets]

/-- The grave defect `(0, 2, −)`: the only exit is absorb into the grave of zero;
    a flat corridor κ = 0. Legal: `2 ∣ sideValue minus 0 = 0`. -/
theorem curvature_defect_0_2 :
    curvature 5 4 (State.defect 0 2 Side.minus) = 0 ∧
      Legal 5 4 (State.defect 0 2 Side.minus) := by decide

/-- Defect `(6, 5, −)`: `5 ∣ 35 = 6·6−1`, a single peel `35 = 5·7` into
    center 1; absorb closed (`6 > M0 = 4`). A flat corridor κ = 0. -/
theorem curvature_defect_6_5 :
    curvature 5 4 (State.defect 6 5 Side.minus) = 0 ∧
      Legal 5 4 (State.defect 6 5 Side.minus) := by decide

/-- Defect `(4, 5, +)`: `5 ∣ 25 = 6·4+1`; TWO exits — peel `25 = 5·5` into
    center 1 AND absorb into `absorber 4` (`4 ≤ M0`). Branching: κ = −1. -/
theorem curvature_defect_4_5 :
    curvature 5 4 (State.defect 4 5 Side.plus) = -1 ∧
      Legal 5 4 (State.defect 4 5 Side.plus) := by decide

/-- Clean center 2 (pair 11/13): four boundary-exits down, κ = −3. -/
theorem curvature_center_2 :
    curvature 5 4 (State.center 2) = -3 ∧ Legal 5 4 (State.center 2) := by
  decide

/-- Clean center 3 (pair 17/19): a clean-edge into center 2 plus four boundary,
    κ = −4. -/
theorem curvature_center_3 :
    curvature 5 4 (State.center 3) = -4 ∧ Legal 5 4 (State.center 3) := by
  decide

/-- Clean center 7 (pair 41/43): three clean-edges (2, 3, 5) and six boundary,
    κ = −8. The higher the center — the more hyperbolic the funnel. -/
theorem curvature_center_7 :
    curvature 5 4 (State.center 7) = -8 ∧ Legal 5 4 (State.center 7) := by
  decide

/-!
  ### Discrete Gauss–Bonnet
-/

/-- **Gauss–Bonnet formula for a finite window**: the sum of curvature =
    |W| − total out-degree. A purely combinatorial identity. -/
theorem gaussBonnet_sum (A M0 : ℕ) (W : Finset State) :
    W.sum (curvature A M0) =
      (W.card : ℤ) - W.sum (fun v => (outDeg A M0 v : ℤ)) := by
  unfold curvature
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

/-- Window `W` is forward-closed: all out-targets of its vertices lie in `W`. -/
def ForwardClosed (A M0 : ℕ) (W : Finset State) : Prop :=
  ∀ v ∈ W, outTargets A M0 v ⊆ W

instance forwardClosedDecidable (A M0 : ℕ) (W : Finset State) :
    Decidable (ForwardClosed A M0 W) :=
  decidable_of_iff' (∀ v ∈ W, outTargets A M0 v ⊆ W) Iff.rfl

/-- The full light cone of center 3 at (5, 4): center 3 itself, its clean-descendant
    center 2, the grave defects of the zero point, defect `(1,5,−)`, its
    peel-descendant center 0 and both reachable absorbers. -/
def cone3 : Finset State :=
  {State.center 3, State.center 2, State.center 0,
   State.defect 0 2 Side.minus, State.defect 0 3 Side.minus,
   State.defect 0 5 Side.minus, State.defect 1 5 Side.minus,
   State.absorber 0, State.absorber 1}

/-- The cone of center 3 is forward-closed — checked by the kernel. -/
theorem cone3_forwardClosed : ForwardClosed 5 4 cone3 := by decide

/-- **Gauss–Bonnet on the cone of center 3**: χ(cone3) = Σκ = −5. Negative
    total curvature: the cone is a hyperbolic funnel with two poles
    (absorber 0, absorber 1) and center 0 (κ = +1 each), not covering
    the branching of funnels −3 and −4. -/
theorem gaussBonnet_cone3 : cone3.sum (curvature 5 4) = -5 := by decide

/-!
  ### Discrete Gauss–Bonnet, general form: Σκ = χ = |V| − |E|

  `gaussBonnet_cone3` computes the Euler characteristic for one concrete cone.
  Here we lift that: on ANY forward-closed window the total combinatorial
  curvature equals the Euler characteristic |V| − |E| of the induced descent
  subgraph. Because the graph is acyclic (`no_closedGeodesic`) there are no
  antiparallel edges, so the directed edge count equals the undirected one and
  |V| − |E| is a bona-fide Euler characteristic of the 1-complex. This is still
  an analogue at the normalisation κ = 1 − outdeg (honest boundary №1), not a
  theorem of differential geometry — but within that choice it is exact.
-/

/-- Edge count of the subgraph induced by `W`: each `v ∈ W` contributes those of
    its out-targets that land back in `W`. -/
def inducedEdges (A M0 : ℕ) (W : Finset State) : ℕ :=
  W.sum (fun v => (outTargets A M0 v ∩ W).card)

/-- On a forward-closed window every out-edge lands in `W`, so the induced-edge
    count equals the total out-degree. This is where forward-closedness is used. -/
theorem forwardClosed_inducedEdges_eq {A M0 : ℕ} {W : Finset State}
    (hclosed : ForwardClosed A M0 W) :
    inducedEdges A M0 W = W.sum (fun v => outDeg A M0 v) := by
  unfold inducedEdges outDeg
  refine Finset.sum_congr rfl (fun v hv => ?_)
  congr 1
  apply Finset.Subset.antisymm Finset.inter_subset_left
  intro x hx
  exact Finset.mem_inter.mpr ⟨hx, hclosed v hv hx⟩

/-- Euler characteristic of the window `W` read as a 1-complex: |V| − |E|. -/
def eulerChar (A M0 : ℕ) (W : Finset State) : ℤ :=
  (W.card : ℤ) - (inducedEdges A M0 W : ℤ)

/-- **Discrete Gauss–Bonnet = Euler characteristic (general form)**: on ANY
    forward-closed window the total combinatorial curvature equals the Euler
    characteristic |V| − |E| of the induced descent subgraph. Generalises
    `gaussBonnet_cone3` from the single cone to every forward-closed region. -/
theorem gaussBonnet_eq_euler {A M0 : ℕ} {W : Finset State}
    (hclosed : ForwardClosed A M0 W) :
    W.sum (curvature A M0) = eulerChar A M0 W := by
  rw [gaussBonnet_sum, eulerChar, forwardClosed_inducedEdges_eq hclosed, Nat.cast_sum]

/-- Consistency: the general Euler characteristic reproduces `gaussBonnet_cone3`. -/
theorem eulerChar_cone3 : eulerChar 5 4 cone3 = -5 := by
  rw [← gaussBonnet_eq_euler cone3_forwardClosed]
  exact gaussBonnet_cone3

/-#############################################################################
  §3. Lines (🟢): every line is finite, none are infinite, a web above the horizon
#############################################################################-/

/-- **Terminal**: a state without outgoing real steps — the "end of a line",
    the point where a geodesic segment runs into a wall. -/
def Terminal (A M0 : ℕ) (v : State) : Prop := ∀ w, ¬ RealStep A M0 v w

/-- An absorber is always terminal: absorb is a dead end, no `RealStep` leaves it. -/
theorem absorber_terminal {A M0 a : ℕ} : Terminal A M0 (State.absorber a) := by
  intro w hstep
  cases hstep

/-- A non-clean center is terminal: the only outgoing edges of a center —
    clean and boundary — require `Clean A m`. -/
theorem center_terminal_of_notClean {A M0 m : ℕ} (h : ¬ Clean A m) :
    Terminal A M0 (State.center m) := by
  intro w hstep
  cases hstep with
  | clean hEdge => exact h hEdge.1
  | boundary hmClean _ _ _ _ => exact h hmClean

/--
  **EVERY LINE RUNS INTO A TERMINAL**: from any state `v` in a finite
  number of real steps you reach a state with no exit. Strong induction on
  proper time `lexRank v`: if `v` is already terminal — the path is empty;
  otherwise the first step STRICTLY drops `lexRank` (arrow of time, `timeArrow_step`),
  and by IH the tail is finite.
-/
theorem every_line_ends {A M0 : ℕ} (v : State) :
    ∃ k Y, PathN (RealStep A M0) k v Y ∧ Terminal A M0 Y := by
  classical
  induction hwf : lexRank v using Nat.strong_induction_on generalizing v with
  | _ r IH =>
      subst hwf
      by_cases hterm : Terminal A M0 v
      · exact ⟨0, v, rfl, hterm⟩
      · rw [Terminal] at hterm
        push_neg at hterm
        obtain ⟨w, hstep⟩ := hterm
        have hdrop : lexRank w < lexRank v := timeArrow_step hstep
        obtain ⟨k, Y, hpath, hY⟩ := IH (lexRank w) hdrop w rfl
        exact ⟨k + 1, Y, ⟨w, hstep, hpath⟩, hY⟩

/-!
  ### Local flat-space pressure: every forward-closed region has a pole

  `space_positively_curved_somewhere` says the WHOLE graph is positively curved
  somewhere. Here we sharpen it to a LOCAL statement: every nonempty forward-closed
  region contains a pole (κ = +1), so no such region can be flat (κ ≤ 0 everywhere)
  — the local form of `nonpositive_curvature_forces_engine`.
-/

/-- A terminal vertex has curvature +1: no exits, so outdeg 0, so κ = 1 − 0 = 1. -/
theorem curvature_one_of_terminal {A M0 : ℕ} {v : State}
    (h : Terminal A M0 v) : curvature A M0 v = 1 := by
  have h0 : outDeg A M0 v = 0 := by
    by_contra hne
    rw [outDeg] at hne
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    exact h w (mem_outTargets.mp hw)
  simp [curvature, h0]

/-- A path starting inside a forward-closed window stays inside it. -/
theorem pathN_stays_in_forwardClosed {A M0 : ℕ} {W : Finset State}
    (hclosed : ForwardClosed A M0 W) {k : ℕ} {v Y : State}
    (hv : v ∈ W) (hpath : PathN (RealStep A M0) k v Y) : Y ∈ W := by
  induction k generalizing v with
  | zero =>
      have hvy : v = Y := hpath
      subst hvy
      exact hv
  | succ n ih =>
      obtain ⟨Z, hstep, hrest⟩ := hpath
      exact ih (hclosed v hv (mem_outTargets.mpr hstep)) hrest

/-- **Every forward-closed region has a pole**: a nonempty forward-closed window
    contains a terminal vertex, whose curvature is +1. The LOCAL form of
    `space_positively_curved_somewhere` — not "somewhere in the whole graph" but
    "in every bounded region there is a floor". -/
theorem forwardClosed_has_pole {A M0 : ℕ} {W : Finset State}
    (hne : W.Nonempty) (hclosed : ForwardClosed A M0 W) :
    ∃ v ∈ W, Terminal A M0 v ∧ curvature A M0 v = 1 := by
  obtain ⟨start, hstart⟩ := hne
  obtain ⟨k, Y, hpath, hY⟩ := every_line_ends (A := A) (M0 := M0) start
  have hYW : Y ∈ W := pathN_stays_in_forwardClosed hclosed hstart hpath
  exact ⟨Y, hYW, hY, curvature_one_of_terminal hY⟩

/-- **No forward-closed region is flat**: a nonempty forward-closed window cannot
    have κ ≤ 0 everywhere — the LOCAL form of `nonpositive_curvature_forces_engine`. -/
theorem forwardClosed_not_flat {A M0 : ℕ} {W : Finset State}
    (hne : W.Nonempty) (hclosed : ForwardClosed A M0 W) :
    ¬ (∀ v ∈ W, curvature A M0 v ≤ 0) := by
  intro hflat
  obtain ⟨v, hvW, _, hκ⟩ := forwardClosed_has_pole hne hclosed
  have hle := hflat v hvW
  omega

/-- **Infinite line**: a sequence of states connected by real
    steps at EVERY tick — a "line extended indefinitely". -/
def InfiniteLine (A M0 : ℕ) (f : ℕ → State) : Prop :=
  ∀ t, RealStep A M0 (f t) (f (t + 1))

/-- **THERE ARE NO INFINITE LINES**: Euclid's second postulate (unbounded
    extension of a line) FALLS in this world. A direct consequence of `no_eternal_run`. -/
theorem no_infinite_line {A M0 : ℕ} (f : ℕ → State) :
    ¬ InfiniteLine A M0 f :=
  fun h => no_eternal_run f h

/-- **Euclid's second postulate is false**: there is NO line extendable indefinitely
    from any start. It is exactly this degradation, not the fifth postulate, that determines
    the geometry of the path. -/
theorem euclid_postulate_two_fails {A M0 : ℕ} :
    ¬ ∃ f : ℕ → State, InfiniteLine A M0 f := by
  rintro ⟨f, hf⟩
  exact no_infinite_line f hf

/-- **Parallel lines**: two infinite lines that never meet anywhere. -/
def ParallelLines (A M0 : ℕ) (f g : ℕ → State) : Prop :=
  InfiniteLine A M0 f ∧ InfiniteLine A M0 g ∧ ∀ i j, f i ≠ g j

/-- **THERE ARE NO PARALLEL LINES** — but for a degenerate reason: even the first line
    does not exist (`no_infinite_line`). This is NOT ellipticity (see honest
    boundary №5 in the header), but a degradation of the second postulate. -/
theorem no_parallel_lines {A M0 : ℕ} :
    ¬ ∃ f g, ParallelLines A M0 f g := by
  rintro ⟨f, g, hf, -, -⟩
  exact no_infinite_line f hf

/-!
  ### HONESTY §3: the bottom is NOT unique, there exist disjoint lines
-/

/-- **The bottom is not unique**: when `1 ≤ M0` there are TWO distinct legal terminals —
    `absorber 0` and `absorber 1`. Naive ellipticity (a "unique vanishing
    point") is FALSE. -/
theorem bottom_not_unique {A M0 : ℕ} (hM0 : 1 ≤ M0) :
    ∃ Ω₁ Ω₂ : State, Ω₁ ≠ Ω₂ ∧
      Legal A M0 Ω₁ ∧ Legal A M0 Ω₂ ∧
      Terminal A M0 Ω₁ ∧ Terminal A M0 Ω₂ := by
  refine ⟨State.absorber 0, State.absorber 1, ?_, ?_, ?_, absorber_terminal, absorber_terminal⟩
  · intro h; exact absurd (State.absorber.injEq 0 1 ▸ h) (by decide)
  · show (0 : ℕ) ≤ M0; exact Nat.zero_le M0
  · show (1 : ℕ) ≤ M0; exact hM0

/-- **Two FULLY disjoint finite lines** at (5, 4): a route from
    `center 7` via defect `(5,5,+)`? — no; we take the disjoint pair
    `[center 7 → defect 4 5 plus → absorber 4]` and
    `[center 3 → defect 0 2 minus → absorber 0]`. All 9 states are pairwise
    distinct. "All lines meet" is false in the naive form. -/
theorem two_disjoint_lines :
    PathN (RealStep 5 4) 2 (State.center 7) (State.absorber 4) ∧
    PathN (RealStep 5 4) 2 (State.center 3) (State.absorber 0) ∧
    (∀ x ∈ ({State.center 7, State.defect 4 5 Side.plus, State.absorber 4} : Finset State),
      ∀ y ∈ ({State.center 3, State.defect 0 2 Side.minus, State.absorber 0} : Finset State),
        x ≠ y) := by
  refine ⟨?_, ?_, by decide⟩
  · refine ⟨State.defect 4 5 Side.plus, ?_, State.absorber 4, ?_, rfl⟩
    · exact RealStep.boundary (by decide) ⟨trivial, by omega⟩ (by norm_num) (by norm_num)
        (by show (5 : ℕ) ∣ sideValue Side.plus 4; decide)
    · exact RealStep.absorb (by omega)
  · refine ⟨State.defect 0 2 Side.minus, ?_, State.absorber 0, ?_, rfl⟩
    · exact RealStep.boundary (by decide) ⟨trivial, by omega⟩ (by norm_num) (by norm_num)
        (by show (2 : ℕ) ∣ sideValue Side.minus 0; decide)
    · exact RealStep.absorb (by omega)

/-!
  ### WEB: above every horizon — a clean-center whose path leads to the grave of zero
-/

/-- **The point 0 absorbs all divisors**: `sideValue Side.minus 0 = 6·0−1 = 0`
    (in ℕ!), and hence ANY `q` divides the side of zero. This is an ℕ-artifact of truncation AND
    a marker of the grave (see honest boundary №3 in the header). -/
theorem zeroPoint_absorbs_all_divisors (q : ℕ) : q ∣ sideValue Side.minus 0 := by
  show q ∣ 6 * 0 - 1
  simp

/--
  **A LINE TO THE ORIGIN**: from any clean-center `m ≥ 1` (when `2 ≤ A`) there is a path
  of length 2 to the grave of zero `absorber 0`: a boundary-step into defect `(0, 2, −)` (legal,
  since `2 ∣ sideValue minus 0 = 0`), then absorb into `absorber 0` (`0 ≤ M0`).
-/
theorem line_to_origin {A M0 m : ℕ} (hA : 2 ≤ A) (hm : 1 ≤ m) (hc : Clean A m) :
    PathN (RealStep A M0) 2 (State.center m) (State.absorber 0) := by
  refine ⟨State.defect 0 2 Side.minus, ?_, State.absorber 0, ?_, rfl⟩
  · exact RealStep.boundary hc ⟨trivial, by omega⟩ (by norm_num) hA
      (zeroPoint_absorbs_all_divisors 2)
  · exact RealStep.absorb (Nat.zero_le M0)

/-- **Lines meet at the origin** (qualified): any two clean-starts
    (when `2 ≤ A`) have a COMMON terminal — the grave of zero `absorber 0`. This is
    the only legitimate sense of "all lines intersect" (honest boundary №4). -/
theorem lines_meet_at_origin {A M0 m₁ m₂ : ℕ} (hA : 2 ≤ A)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hc₁ : Clean A m₁) (hc₂ : Clean A m₂) :
    Terminal A M0 (State.absorber 0) ∧
      NonemptyPath (RealStep A M0) (State.center m₁) (State.absorber 0) ∧
      NonemptyPath (RealStep A M0) (State.center m₂) (State.absorber 0) :=
  ⟨absorber_terminal,
   ⟨2, by omega, line_to_origin hA hm₁ hc₁⟩,
   ⟨2, by omega, line_to_origin hA hm₂ hc₂⟩⟩

/-- **Bridge ℤ→ℕ for cleanness**: `Residuals.CleanZ A (m : ℤ)` when `1 ≤ m` yields
    `Clean A m` (in ℕ). Mirrors the casting pattern from `CleanGraph.clean_sink_above`. -/
theorem clean_of_cleanZ {A m : ℕ} (hm : 1 ≤ m)
    (h : Residuals.CleanZ A (m : ℤ)) : Clean A m := by
  intro q hq hqA hbad
  refine h q hq hqA ?_
  have h1 : ((6 * m - 1 : ℕ) : ℤ) = 6 * (m : ℤ) - 1 := by
    have : 1 ≤ 6 * m := by omega
    push_cast [Nat.cast_sub this]; ring
  have h2 : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by push_cast; ring
  rcases hbad with hbad | hbad
  · exact Or.inl (by rw [← h1]; exact_mod_cast hbad)
  · exact Or.inr (by rw [← h2]; exact_mod_cast hbad)

/--
  **A WEB ABOVE EVERY HORIZON**: for `2 ≤ A` and any `N` there exists a
  clean-center `m > N` whose path leads to the grave of zero. Density is NOT needed —
  the construction `Residuals.carrier_nonempty_above` (primorial start).
-/
theorem web_above_every_horizon {A M0 : ℕ} (hA : 2 ≤ A) (N : ℕ) :
    ∃ m, N < m ∧ Clean A m ∧
      NonemptyPath (RealStep A M0) (State.center m) (State.absorber 0) := by
  obtain ⟨m, hmN, hcleanZ⟩ := Residuals.carrier_nonempty_above A N
  have hm1 : 1 ≤ m := by omega
  have hclean : Clean A m := clean_of_cleanZ hm1 hcleanZ
  exact ⟨m, hmN, hclean, ⟨2, by omega, line_to_origin hA hm1 hclean⟩⟩

/-#############################################################################
  §4. Epistemics (🟢): the intersection fact is green, but its INTERNAL grounding is
      an engine. To know "lines meet" from inside the system = to build an engine.
#############################################################################-/

/--
  **THE INTERSECTION FACT** as a statement about geometry: when `2 ≤ A` any two
  clean-starts have a COMMON terminal. This is a pure (🟢) geometric truth —
  proven in §3 via `lines_meet_at_origin`.
-/
abbrev IntersectionFact (A M0 : ℕ) : Prop :=
  2 ≤ A → ∀ m₁ m₂, 1 ≤ m₁ → 1 ≤ m₂ → Clean A m₁ → Clean A m₂ →
    ∃ Ω, Terminal A M0 Ω ∧
      NonemptyPath (RealStep A M0) (State.center m₁) Ω ∧
      NonemptyPath (RealStep A M0) (State.center m₂) Ω

/-- **The intersection fact is GREEN**: proven without axioms (the common terminal — the grave
    of zero `absorber 0`). -/
theorem intersectionFact_green {A M0 : ℕ} : IntersectionFact A M0 := by
  intro hA m₁ m₂ hm₁ hm₂ hc₁ hc₂
  obtain ⟨hterm, hp₁, hp₂⟩ := lines_meet_at_origin (M0 := M0) hA hm₁ hm₂ hc₁ hc₂
  exact ⟨State.absorber 0, hterm, hp₁, hp₂⟩

/--
  **INTERNALISED INTERSECTION GROUND**: an attempt to derive the intersection fact
  as an INTERNAL first cause of the Step00-world. By the architecture
  (`InternalUniverseCause = BoundaryCrossingSelfProof`) this is exactly a
  boundary-crossing self-proof — a forbidden engine.
-/
abbrev InternalisedIntersectionGround (A M0 : ℕ) : Prop :=
  InternalUniverseCause (IntersectionFact A M0)

/-- **To know the intersection FROM INSIDE = to build an engine**: any internalised
    ground of the intersection fact builds the forbidden concrete Euclidean engine. -/
theorem knowing_meeting_costs_engine {A M0 : ℕ}
    (h : InternalisedIntersectionGround A M0) : SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine h

/-- **There is NO internalised intersection ground**: re-export of the causal
    boundary `no_boundaryCrossingSelfProof`. -/
theorem no_internalisedIntersectionGround {A M0 : ℕ} :
    ¬ InternalisedIntersectionGround A M0 :=
  no_boundaryCrossingSelfProof

/-- **HONESTY**: the internalised ground ⟺ `P ∧ ¬P` (tautological for
    any P — internalisation into the empty type of attempts is exactly negation).
    There is no carrier content in the ground itself; all the content is in the 🟢-fact
    `intersectionFact_green`. -/
theorem internalisedIntersectionGround_iff {A M0 : ℕ} :
    InternalisedIntersectionGround A M0 ↔
      (IntersectionFact A M0 ∧ ¬ IntersectionFact A M0) :=
  boundaryCrossingSelfProof_iff_and_not

/-- Ex-falso companion: from the internalised ground follows the REFUTATION
    of the intersection (there is none — because there is no ground either). -/
theorem internalisedGround_refutes_meeting {A M0 : ℕ}
    (h : InternalisedIntersectionGround A M0) : ¬ IntersectionFact A M0 :=
  (no_internalisedIntersectionGround h).elim

/-- Ex-falso companion: from the internalised ground follows also the intersection
    fact ITSELF (there is no ground — hence anything). -/
theorem internalisedGround_proves_meeting {A M0 : ℕ}
    (h : InternalisedIntersectionGround A M0) : IntersectionFact A M0 :=
  (no_internalisedIntersectionGround h).elim

/-#############################################################################
  §5. CAPSTONE (🟢): all the geometry of Euclid's Path in one statement, axiom-free
#############################################################################-/

/--
  **THE GEOMETRY OF EUCLID'S PATH — as a single theorem.** For any `(A, M0)`:

  * arrow of time — `lexRank` strictly drops on every edge;
  * space is somewhere positively curved (κ > 0);
  * a fully flat world does not exist (κ ≡ 0 builds an engine);
  * the intersection fact: clean-lines have a common terminal;
  * there are no parallel lines (degenerately — the second postulate falls);
  * there is no internal ground of the intersection fact (it would be an engine).

  All assembled from already-proven 🟢-pieces; there are NO axioms (the expected triple:
  `propext`, `Classical.choice`, `Quot.sound`).
-/
theorem geometry_of_euclids_path (A M0 : ℕ) :
    (∀ U V, RealStep A M0 U V → lexRank V < lexRank U) ∧
    (∃ v, 0 < curvature A M0 v) ∧
    ((∀ v, curvature A M0 v = 0) → False) ∧
    IntersectionFact A M0 ∧
    (¬ ∃ f g, ParallelLines A M0 f g) ∧
    (¬ InternalisedIntersectionGround A M0) :=
  ⟨fun _ _ h => timeArrow_step h,
   space_positively_curved_somewhere A M0,
   fun hflat => flat_everywhere_forces_engine hflat,
   intersectionFact_green,
   no_parallel_lines,
   no_internalisedIntersectionGround⟩

/-#############################################################################
  §6. 🟡-CODA: EXACTLY TWO declarations are tainted by the axiom step00FirstCause.
      Everything above is 🟢. Here the causal twins boundary
      (`twinLowersInfinite_from_step00CausalClosure`) is translated into the language
      of graph vertices. There is NO new axiom and no new content of the decree.
#############################################################################-/

/-- **Bridge twin-pair → twin-center** (🟢, axiom-free). The lower member of a twin
    pair `p > 3` has the form `6m − 1` for some `m ≥ 1`, and this `m` is a
    twin-center (`TwinCenterZ`). Case analysis by the residue `p mod 6`: a prime `p > 3` is not
    divisible by 2 and 3, hence `p mod 6 ∈ {1, 5}`; the case `p mod 6 = 1` gives
    `3 ∣ p+2`, while `(p+2)` is a prime `> 3` — a contradiction; leaving `p = 6m − 1`. -/
theorem twinCenter_of_twinLower {p : ℕ} (hp : IsTwinPair p) (h3 : 3 < p) :
    ∃ m, 1 ≤ m ∧ Residuals.TwinCenterZ m ∧ 6 * m - 1 = p := by
  obtain ⟨hpP, hp2P⟩ := hp
  -- p is not divisible by 2 or 3 (otherwise p = 2 or p = 3, but p > 3)
  have hn2 : ¬ (2 ∣ p) := by
    intro hd
    rcases (hpP.eq_one_or_self_of_dvd 2 hd) with h | h <;> omega
  have hn3 : ¬ (3 ∣ p) := by
    intro hd
    rcases (hpP.eq_one_or_self_of_dvd 3 hd) with h | h <;> omega
  -- so p mod 6 = 1 or 5
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases hmod with h1 | h5
  · -- p mod 6 = 1 ⟹ 3 ∣ p + 2 ⟹ p + 2 = 3 ⟹ p = 1, absurd
    have hdvd : 3 ∣ (p + 2) := by omega
    rcases (hp2P.eq_one_or_self_of_dvd 3 hdvd) with h | h <;> omega
  · -- p mod 6 = 5 ⟹ m = (p + 1) / 6, 6m − 1 = p, 6m + 1 = p + 2
    refine ⟨(p + 1) / 6, by omega, ?_, by omega⟩
    have hlo : 6 * ((p + 1) / 6) - 1 = p := by omega
    have hhi : 6 * ((p + 1) / 6) + 1 = p + 2 := by omega
    exact ⟨by rw [hlo]; exact hpP, by rw [hhi]; exact hp2P⟩

/-- **Infinitude of twin-lowers ⟹ they are unbounded** (🟢, axiom-free).
    If the set `TwinLowers` is infinite, then above any `N` there is an element of it:
    otherwise `TwinLowers ⊆ Set.Iic N` is finite — a contradiction. -/
theorem twinLowers_unbounded_of_infinite (h : TwinLowers.Infinite) :
    ∀ N, ∃ p ∈ TwinLowers, N < p := by
  intro N
  by_contra hcon
  push_neg at hcon
  have hsub : TwinLowers ⊆ Set.Iic N := fun p hp => Set.mem_Iic.mpr (hcon p hp)
  exact h (Set.Finite.subset (Set.finite_Iic N) hsub)

/--
  **⚠️ AXIOM-TAINTED (step00FirstCause).** Twin-vertices of the graph above every
  horizon: for any `N` there exists a twin-center `m > N` (the vertex
  `State.center m`, whose both sides `6m ± 1` are prime). The taint runs EXACTLY through
  the causal twins boundary
  (`twinLowersInfinite_from_step00CausalClosure`) — no new axiom,
  no new content of the decree: the already-accepted boundary, translated into the
  language of vertices. The form `TwinCenterZ` is used via the bridge
  `twinCenter_of_twinLower`.
-/
theorem twin_vertices_beyond_every_horizon :
    ∀ N, ∃ m, N < m ∧ Residuals.TwinCenterZ m := by
  intro N
  -- take a twin-lower p above the horizon 6*N + 5 (⟹ p > 3 and m > N)
  obtain ⟨p, hpMem, hpGt⟩ :=
    twinLowers_unbounded_of_infinite twinLowersInfinite_from_step00CausalClosure (6 * N + 5)
  have hp : IsTwinPair p := hpMem
  have h3 : 3 < p := by omega
  obtain ⟨m, hm1, htwin, hpm⟩ := twinCenter_of_twinLower hp h3
  refine ⟨m, ?_, htwin⟩
  -- 6m − 1 = p > 6N + 5 ⟹ m > N
  omega

/--
  **⚠️ AXIOM-TAINTED (step00FirstCause).** LINES MEET, BUT THIS IS UNKNOWABLE
  FROM INSIDE. The full epistemic summary: (1) the intersection fact is green; (2) twin-
  vertices exist above every horizon (this line carries the twins taint);
  (3) there is no internal ground of the intersection fact; (4) if there were — it
  would be the forbidden concrete Euclidean engine. The taint is only through (2),
  exactly the boundary `twin_vertices_beyond_every_horizon`; no further content
  of the decree is added.
-/
theorem lines_meet_but_unknowable_from_inside (A M0 : ℕ) :
    IntersectionFact A M0 ∧
    (∀ N, ∃ m, N < m ∧ Residuals.TwinCenterZ m) ∧
    (¬ InternalisedIntersectionGround A M0) ∧
    (InternalisedIntersectionGround A M0 → SomeConcreteEuclideanEngine) :=
  ⟨intersectionFact_green,
   twin_vertices_beyond_every_horizon,
   no_internalisedIntersectionGround,
   knowing_meeting_costs_engine⟩

end EuclidsPath.GeometryFront

/-!
  ### Machine honesty of the taint (expectations)

  * Capstone §5 — 🟢: exactly the standard triple `propext`, `Classical.choice`,
    `Quot.sound`, no user axioms.
  * Both declarations of the §6-coda — 🟡: over the standard triple there is exactly
    `step00FirstCause` (via `twinLowersInfinite_from_step00CausalClosure`).
-/

#print axioms EuclidsPath.GeometryFront.geometry_of_euclids_path
#print axioms EuclidsPath.GeometryFront.twin_vertices_beyond_every_horizon
#print axioms EuclidsPath.GeometryFront.lines_meet_but_unknowable_from_inside

-- Generalised Gauss–Bonnet and the local flat-space pressure — all 🟢
-- (expected standard triple `propext`, `Classical.choice`, `Quot.sound`).
#print axioms EuclidsPath.GeometryFront.gaussBonnet_eq_euler
#print axioms EuclidsPath.GeometryFront.forwardClosed_has_pole
#print axioms EuclidsPath.GeometryFront.forwardClosed_not_flat
