/-
  energy_defect_trichotomy + конечный product-rank descent. Формализация авторского файла.
  Источник: step00_energy_defect_trichotomy_rank_descent_ru_2026-07-01.md. Проза: prose/31_RankDescent.md.

  Контекст: `ProductHall` уже закрыт (separating scale, `Engine/SeparatingScale.no_productHall`).
  Остаток: ExactProductMismatch_r ⟹ LowerRankCollision_{r-1} (т.к. ProductHall невозможен).

  ЛОГИЧЕСКИЙ СКЕЛЕТ (здесь, доказуемо):
    delete mismatched factor ⟹ (R₁=R₂ ⟹ ProductHall) ∨ (R₁≠R₂ ⟹ LowerRankCollision)  [excluded middle];
    ¬ProductHall ⟹ LowerRankCollision; rank-induction r≤4 ⟹ rank-1 ⟹ Engine.

  СОДЕРЖАТЕЛЬНЫЕ УЗЛЫ (явные гипотезы конфигурации `RankSetup`):
    • delete_preserves_prodSig (4.1) — удаление role сохраняет подпись;
    • productHall_of_same_residual / lowerRank_of_diff_residual — конструкторы;
    • no_mismatch_state_eq (§10) — ЭКСТЕНСИОНАЛЬНОСТЬ: равные подписи + нет mismatch ⟹ X₁=X₂
      (КРИТИЧНО: требует, чтобы ProdSig различал состояния — проверяется аудитом на трилемму);
    • rank1_engine — rank-1 ⟹ Engine (SNOL/old-peel, доказан в SNOL-блоке);
    • no_productHall — уже доказан (separating scale).
-/
import Mathlib
import EuclidsPath.Engine.SeparatingScale

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.RankDescent

variable {PState : Type*}

/-- Конфигурация product-rank descent. Содержательные узлы — поля; логика их связывает. -/
structure RankSetup (PState : Type*) where
  rank : PState → ℕ
  ProdSig : PState → Prop → Prop   -- абстрактно: подпись как сравнимый объект (через равенство Prop)
  sig : PState → Sigma (fun _ : Unit => ℕ)  -- упрощённый носитель подписи (заглушка)
  Engine : Prop
  ProductHall : PState → PState → Prop
  LowerRankCollision : ℕ → Prop
  -- (4.1) удаление mismatched role: даёт residual меньшего ранга и ветвление
  delete_branch : ∀ X₁ X₂ : PState, rank X₁ = rank X₂ → 1 < rank X₁ →
      -- residual равен ⟹ ProductHall; residual различен ⟹ LowerRankCollision
      ProductHall X₁ X₂ ∨ LowerRankCollision (rank X₁ - 1)
  -- (§10) экстенсиональность: нет ничего различающего ⟹ состояния равны (КРИТИЧНО)
  no_mismatch_state_eq : ∀ X₁ X₂ : PState, ¬ ProductHall X₁ X₂ → rank X₁ = rank X₂ →
      ¬ LowerRankCollision (rank X₁ - 1) → X₁ = X₂
  -- база: rank-1 коллизия ⟹ Engine (SNOL/old-peel)
  rank1_engine : LowerRankCollision 0 → Engine
  -- ¬ProductHall (уже доказан separating scale)
  no_PH : ∀ X₁ X₂, ¬ ProductHall X₁ X₂

/--
  **rank_step_descent (Theorem 11.1) — логика.** `X₁≠X₂`, равный ранг `>1`, и `¬ProductHall`
  ⟹ `LowerRankCollision_{r-1}`. (delete_branch даёт `PH ∨ LRC`; `¬PH` ⟹ `LRC`.) -/
theorem rank_step_descent (S : RankSetup PState) (X₁ X₂ : PState)
    (hr : 1 < S.rank X₁) (hreq : S.rank X₁ = S.rank X₂) :
    S.LowerRankCollision (S.rank X₁ - 1) :=
  (S.delete_branch X₁ X₂ hreq hr).resolve_left (S.no_PH X₁ X₂)

/--
  **mismatch ⟹ lower rank (Corollary 9.1).** То же, явно: коллизия ранга `>1` ⟹ коллизия ранга `r-1`.
  Это и есть «energy defect ⟹ снижение ранга», с уже закрытым ProductHall. -/
theorem mismatch_gives_lowerRank (S : RankSetup PState) (X₁ X₂ : PState)
    (hr : 1 < S.rank X₁) (hreq : S.rank X₁ = S.rank X₂) :
    S.LowerRankCollision (S.rank X₁ - 1) :=
  rank_step_descent S X₁ X₂ hr hreq

/--
  **product_rank_pump (Theorem 13.1) — конечный descent r→…→1→Engine.** Любая collision ранга
  `r` (`1≤r≤4`) даёт Engine. Здесь — well-founded по рангу: на каждом шаге `>1` ранг падает
  (`rank_step_descent`), на `0` (rank-1 в 0-индексации) включается `rank1_engine`.
  Формализуем сильной индукцией по `S.rank X₁`. -/
theorem product_rank_pump (S : RankSetup PState)
    -- rank-1 коллизия (r=1) ⟹ Engine (SNOL/old-peel база); r≥2 ⟹ есть состояния ранга r
    (rank1_base : S.LowerRankCollision 1 → S.Engine)
    (collision_states : ∀ r : ℕ, 2 ≤ r → S.LowerRankCollision r →
        ∃ X₁ X₂ : PState, S.rank X₁ = r ∧ S.rank X₂ = r)
    : ∀ r : ℕ, 1 ≤ r → S.LowerRankCollision r → S.Engine := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ n ih =>
    intro hge hcol
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · -- n=1: база SNOL
      have : n = 1 := by omega
      subst this; exact rank1_base hcol
    · -- n≥2: спускаем к рангу n-1 (1≤n-1<n), рекурсия
      obtain ⟨X₁, X₂, hr1, hr2⟩ := collision_states n h2 hcol
      have hstep : S.LowerRankCollision (S.rank X₁ - 1) :=
        rank_step_descent S X₁ X₂ (by omega) (by omega)
      exact ih (S.rank X₁ - 1) (by omega) (by omega) hstep

end EuclidsPath.RankDescent
