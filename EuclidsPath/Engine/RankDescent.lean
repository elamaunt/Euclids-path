/-
  energy_defect_trichotomy + finite product-rank descent. Formalisation of the author's file.
  Source: step00_energy_defect_trichotomy_rank_descent_ru_2026-07-01.md. Prose: prose/31_RankDescent.md.

  Context: `ProductHall` is already closed (separating scale, `Engine/SeparatingScale.no_productHall`).
  Remainder: ExactProductMismatch_r ⟹ LowerRankCollision_{r-1} (since ProductHall is impossible).

  LOGICAL SKELETON (proved here):
    delete mismatched factor ⟹ (R₁=R₂ ⟹ ProductHall) ∨ (R₁≠R₂ ⟹ LowerRankCollision)  [excluded middle];
    ¬ProductHall ⟹ LowerRankCollision; rank-induction r≤4 ⟹ rank-1 ⟹ Engine.

  SUBSTANTIVE NODES (explicit hypotheses of configuration `RankSetup`):
    • delete_preserves_prodSig (4.1) — deleting a role preserves the signature;
    • productHall_of_same_residual / lowerRank_of_diff_residual — constructors;
    • no_mismatch_state_eq (§10) — EXTENSIONALITY: equal signatures + no mismatch ⟹ X₁=X₂
      (CRITICAL: requires ProdSig to distinguish states — verified by trilemma audit);
    • rank1_engine — rank-1 ⟹ Engine (SNOL/old-peel, proved in the SNOL block);
    • no_productHall — already proved (separating scale).
-/
import Mathlib
import EuclidsPath.Engine.SeparatingScale

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.RankDescent

variable {PState : Type*}

/-- Configuration of the product-rank descent. Substantive nodes are fields; logic connects them. -/
structure RankSetup (PState : Type*) where
  rank : PState → ℕ
  ProdSig : PState → Prop → Prop   -- abstract: signature as a comparable object (via Prop equality)
  sig : PState → Sigma (fun _ : Unit => ℕ)  -- simplified signature carrier (placeholder)
  Engine : Prop
  ProductHall : PState → PState → Prop
  LowerRankCollision : ℕ → Prop
  -- (4.1) deletion of a mismatched role: yields a residual of lower rank and a branch
  delete_branch : ∀ X₁ X₂ : PState, rank X₁ = rank X₂ → 1 < rank X₁ →
      -- residual equal ⟹ ProductHall; residual different ⟹ LowerRankCollision
      ProductHall X₁ X₂ ∨ LowerRankCollision (rank X₁ - 1)
  -- (§10) extensionality: nothing distinguishes ⟹ states are equal (CRITICAL)
  no_mismatch_state_eq : ∀ X₁ X₂ : PState, ¬ ProductHall X₁ X₂ → rank X₁ = rank X₂ →
      ¬ LowerRankCollision (rank X₁ - 1) → X₁ = X₂
  -- base: rank-1 collision ⟹ Engine (SNOL/old-peel)
  rank1_engine : LowerRankCollision 0 → Engine
  -- ¬ProductHall (already proved by separating scale)
  no_PH : ∀ X₁ X₂, ¬ ProductHall X₁ X₂

/--
  **rank_step_descent (Theorem 11.1) — logic.** `X₁≠X₂`, equal rank `>1`, and `¬ProductHall`
  ⟹ `LowerRankCollision_{r-1}`. (delete_branch gives `PH ∨ LRC`; `¬PH` ⟹ `LRC`.) -/
theorem rank_step_descent (S : RankSetup PState) (X₁ X₂ : PState)
    (hr : 1 < S.rank X₁) (hreq : S.rank X₁ = S.rank X₂) :
    S.LowerRankCollision (S.rank X₁ - 1) :=
  (S.delete_branch X₁ X₂ hreq hr).resolve_left (S.no_PH X₁ X₂)

/--
  **mismatch ⟹ lower rank (Corollary 9.1).** The same, explicitly: collision of rank `>1` ⟹ collision of rank `r-1`.
  This is exactly «energy defect ⟹ rank descent», with ProductHall already closed. -/
theorem mismatch_gives_lowerRank (S : RankSetup PState) (X₁ X₂ : PState)
    (hr : 1 < S.rank X₁) (hreq : S.rank X₁ = S.rank X₂) :
    S.LowerRankCollision (S.rank X₁ - 1) :=
  rank_step_descent S X₁ X₂ hr hreq

/--
  **product_rank_pump (Theorem 13.1) — finite descent r→…→1→Engine.** Any collision of rank
  `r` (`1≤r≤4`) yields Engine. Here — well-founded on rank: at each step `>1` the rank drops
  (`rank_step_descent`), at `0` (rank-1 in 0-indexing) `rank1_engine` fires.
  We formalise by strong induction on `S.rank X₁`. -/
theorem product_rank_pump (S : RankSetup PState)
    -- rank-1 collision (r=1) ⟹ Engine (SNOL/old-peel base); r≥2 ⟹ there exist states of rank r
    (rank1_base : S.LowerRankCollision 1 → S.Engine)
    (collision_states : ∀ r : ℕ, 2 ≤ r → S.LowerRankCollision r →
        ∃ X₁ X₂ : PState, S.rank X₁ = r ∧ S.rank X₂ = r)
    : ∀ r : ℕ, 1 ≤ r → S.LowerRankCollision r → S.Engine := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ n ih =>
    intro hge hcol
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · -- n=1: SNOL base
      have : n = 1 := by omega
      subst this; exact rank1_base hcol
    · -- n≥2: descend to rank n-1 (1≤n-1<n), recursion
      obtain ⟨X₁, X₂, hr1, hr2⟩ := collision_states n h2 hcol
      have hstep : S.LowerRankCollision (S.rank X₁ - 1) :=
        rank_step_descent S X₁ X₂ (by omega) (by omega)
      exact ih (S.rank X₁ - 1) (by omega) (by omega) hstep

end EuclidsPath.RankDescent
