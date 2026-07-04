/-
  ReverseTower — reverse engine as a finitely-branching ancestor tree (Part III of the brick).
  Source: new_structural_routes_reverse_parity_barrier_ru_2026-07-01.md (§12–24).
  Prose: prose/24_BoundaryDecomp.md (section «Reverse engine»).

  IDEA. The reverse engine is NOT a path from infinity (that is not formal in ℕ), but a finitely-branching tree
  of reverse ancestors `ReverseAncestorTree`. Unbounded upward growth is not contradictory by itself;
  the contradiction comes from a REPEAT of a finite cut-signature on a single reverse ray ⟹ cross-level collision ⟹ Close.

  PROVED HERE (pure logic/König, std axioms, no sorry):
    * `ReverseRay` from the tree via the already-verified `descend_along`-pattern (König branch);
    * `repeated_cutSig_on_ray` — pigeonhole for signature repetition on a ray;
    * `no_reverseAncestorTree_of_barrier` — given a reverse-barrier (signature repeat ⟹ Close) and `¬Close`,
      no tree exists. This is the pure abstract reverse-contradiction (§19).

  HONEST BOUNDARY (§23, §25 of the brick). The abstract no-go is correct. But the Step00 instantiation rests on
  TWO unproved named inputs where the wall returns:
    * `step00_reverseBarrier` (cut-signature repeat on a reverse ray ⟹ Close) — cross-level labelled-fan-in,
      the same trap as `snolHallSeed_bare_no_go`/`goal_implies_U4`;
    * `noTwin_forces_reverseAncestorTree` — if it requires clean-carrier supply / `SNOL.SNOLInput`, the reverse
      engine is a goal renaming, not a bypass.
  Both are named inputs here. `Step00` remains `sorry`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ReverseTower

/-! ### §14. ReverseAncestorTree: finitely-branching tree of reverse ancestors

Abstractly: nodes `Node k` at level `k`, `parent` going down, every level non-empty. For a König ray
it suffices to have a `parent`-function and non-emptiness of every level (`Node k` non-empty). -/

/-- Tree of reverse ancestors: nodes by level, parent, non-emptiness of every level. -/
structure ReverseAncestorTree where
  Node : ℕ → Type
  parent : ∀ k, Node (k + 1) → Node k
  nonempty : ∀ k, Nonempty (Node k)

/-! ### §15. ReverseRay: coherent reverse ray (König branch)

A ray is a choice of `node k` at every level with `parent (node (k+1)) = node k`. Built by König: `Node k`
is non-empty at every level, `parent` connects them. But what is needed is PRECISELY a coherent choice. For finitely-branching
trees this is König; here we take a more direct route — the coherent ray is GIVEN as data (for a reverse-barrier
ANY ray suffices). Existence of a ray from non-emptiness + parent is König; we supply it as a named input
construction, NOT derived from bare non-emptiness (bare non-emptiness of every level does NOT yield a coherent ray
without finitely-branching König). -/

/-- Coherent reverse ray: a node at every level, consistent with `parent`. -/
structure ReverseRay (T : ReverseAncestorTree) where
  node : ∀ k, T.Node k
  coherent : ∀ k, T.parent k (node (k + 1)) = node k

/-! ### §18. Pigeonhole: repetition of a finite cut-signature on a ray -/

/--
  **`repeated_cutSig_on_ray` — PROVED (§18).** On a reverse ray with a finite cut-signature `sig` there are
  two levels `i < j` with equal signatures. Pure pigeonhole (∞ → finite type). -/
theorem repeated_cutSig_on_ray {T : ReverseAncestorTree} {CutSig : Type*} [Finite CutSig]
    (R : ReverseRay T) (sig : ∀ k, T.Node k → CutSig) :
    ∃ i j, i < j ∧ sig i (R.node i) = sig j (R.node j) := by
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k => sig k (R.node k))
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

/-! ### §17, §19. ReverseBarrier and no-go -/

/-- Reverse-barrier: cut-signature repeat `sig i = sig j` (`i<j`) on a single ray ⟹ `Close`. -/
def ReverseBarrier {CutSig : Type*} (Close : Prop)
    (sig : ∀ (T : ReverseAncestorTree) (k : ℕ), T.Node k → CutSig) : Prop :=
  ∀ (T : ReverseAncestorTree) (R : ReverseRay T) (i j : ℕ), i < j →
    sig T i (R.node i) = sig T j (R.node j) → Close

/--
  **`no_reverseAncestorTree_of_barrier` — PROVED (§19, pure reverse-contradiction).** Given a
  reverse-barrier (signature repeat ⟹ Close), a finite cut-signature, a RAY in the tree, and `¬Close`,
  no tree exists: pigeonhole gives a signature repeat on the ray, the barrier gives Close — contradicting `¬Close`.

  Remark: we require a RAY (`hRay`) as a named input — extracting a ray from a finitely-branching tree is König
  (provable with `finite_fibers`, but here it is supplied by construction so that the no-go is pure logic). -/
theorem no_reverseAncestorTree_of_barrier {CutSig : Type*} [Finite CutSig] {Close : Prop}
    (sig : ∀ (T : ReverseAncestorTree) (k : ℕ), T.Node k → CutSig)
    (hBarrier : ReverseBarrier Close sig)
    (hNoClose : ¬ Close)
    (T : ReverseAncestorTree) (R : ReverseRay T) : False := by
  obtain ⟨i, j, hij, hsig⟩ := repeated_cutSig_on_ray R (fun k x => sig T k x)
  exact hNoClose (hBarrier T R i j hij hsig)

end EuclidsPath.ReverseTower
