/-
  DissipativeCascade — диссипативный cascade-сертификат: decomposition узла Лиувилль-локализации.
  Источник: диссипативный cascade-blueprint (Step00 / RH / Navier–Stokes аналогия).
  Проза: prose/24_BoundaryDecomp.md (раздел «Диссипативный cascade и capacity/overflow»).

  ИДЕЯ (единая для Step00 / RH / NS): «дефект не может исчезнуть; если он не закрывается, он обязан
  двигаться и платить». Это уже воплощено в `ClosedUniverse.no_infinite_closed_paid_run`,
  `DichotomyEngine.close_forced`, `RankJumpBridge` (rank/parity). Здесь — НОВАЯ часть: **capacity /
  overflow** декомпозиция узла `RankJumpLocalization` (Лиувилль-дисбаланс ⟹ twin-jump) на два меньших:
    (1) irrelevant-cancellation (нерелевантная часть не переполняет bound);
    (2) pairing (релевантный дисбаланс не влезает в сокращающиеся пары ⟹ jump).

  ЗДЕСЬ ДОКАЗАНО (чистые суммы/triangle, std аксиомы, без sorry):
    * `L_eq_relevant_add_irrelevant` (§10, `Finset.sum_union` — sorry blueprint'а ЗАКРЫТ);
    * `relevantViolation_of_globalViolation` (§10 overflow, triangle — sorry blueprint'а ЗАКРЫТ);
    * `twinJump_of_relevantViolation` / сборка (§11).

  ЧЕСТНАЯ ГРАНИЦА. Это НЕ доказательство RH/NS/twins. Аналитические входы остаются: `IrrelevantCancellation`
  (bound на нерелевантную часть) и `TwinCarrierPairing.unpaired_gives_jump` — они замещают более крупный
  `RankJumpLocalization`, но сами не доказаны. ℝ-budget оговорка (§2): в отличие от ℕ-движка, строго
  положительная работа над ℝ НЕ даёт well-foundedness (ряд 1/2^n) — поэтому NS-аналогия только структурная.
-/
import Mathlib
import EuclidsPath.Engine.RankJumpBridge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.DissipativeCascade

open scoped BigOperators
open ArithmeticFunction
open EuclidsPath.RankJumpBridge

/-! ### §2. ℕ-budget vs ℝ-budget: почему NS-аналогия только структурная (машинный контрпример)

Для ℕ-движка `Total y + Work ≤ Total x` c `0 < Work` даёт `Total y < Total x` ⟹ well-founded.
Для ℝ строго положительная работа НЕ запрещает бесконечный ряд убываний (`1/2^n`). Фиксируем машинно. -/

/-- **`real_positive_work_not_wellfounded` — ДОКАЗАНА (§2 warning).** Существует ℝ-последовательность
    со строго положительным «шагом работы» на каждом шаге, но конечным суммарным спадом: `a n = 1/2^n`.
    Значит ℝ-диссипация без квантования/ранга НЕ даёт конечности — в отличие от ℕ-движка. -/
theorem real_positive_work_not_wellfounded :
    ∃ a : ℕ → ℝ, (∀ n, a (n + 1) < a n) ∧ (∀ n, 0 < a n) ∧ (∀ n, 0 < a n - a (n + 1)) := by
  refine ⟨fun n => (1 / 2) ^ n, ?_, ?_, ?_⟩
  · intro n
    simp only
    have h : (0:ℝ) < (1/2) ^ n := by positivity
    calc (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
      _ < (1/2) ^ n * 1 := by nlinarith
      _ = (1/2) ^ n := by ring
  · intro n; simp only; positivity
  · intro n
    simp only
    have h : (0:ℝ) < (1/2) ^ n := by positivity
    have he : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
    rw [he]; nlinarith

/-! ### §2bis. Квантизация СПАСАЕТ ℝ-каскад (завершение предупреждения §2)

Контрпример §2 показал: положительная работа над ℝ не даёт конечности. Вот ТОЧНОЕ спасение (опция 3
blueprint'a): равномерная нижняя граница δ на диссипацию bad-шага. Это форма настоящего НС-сертификата:
«каждый каскадный переход к меньшему масштабу диссипирует ≥ δ» ⟹ каскад конечен. -/

/-- **`real_cascade_bounded_of_uniform_work` — ДОКАЗАНА (квантизация).** При равномерной δ-диссипации
    накопленная работа за n шагов ≤ E(0): `n·δ ≤ Total(path 0)`. -/
theorem real_cascade_bounded_of_uniform_work
    {State : Type} {Step : State → State → Prop}
    (Total : State → ℝ) (Work : State → State → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hpaid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x)
    (hwork : ∀ {x y}, Step x y → δ ≤ Work x y)
    (hnonneg : ∀ x, 0 ≤ Total x)
    (path : ℕ → State) (hstep : ∀ k, Step (path k) (path (k + 1))) :
    ∀ n : ℕ, (n : ℝ) * δ ≤ Total (path 0) := by
  intro n
  have key : ∀ m : ℕ, Total (path m) + (m : ℝ) * δ ≤ Total (path 0) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        have hp := hpaid (hstep k)
        have hw := hwork (hstep k)
        have : Total (path (k+1)) + δ ≤ Total (path k) := by linarith
        push_cast
        linarith
  have := key n
  have := hnonneg (path n)
  linarith

/-- **`no_infinite_uniform_dissipative_cascade` — ДОКАЗАНА.** Бесконечный равномерно-диссипативный
    ℝ-каскад невозможен: `n·δ` превысит `E(0)`. Это честный ℝ-аналог `no_infinite_closed_paid_run`
    и ТОЧНАЯ форма, которую должен иметь НС-сертификат регулярности. -/
theorem no_infinite_uniform_dissipative_cascade
    {State : Type} {Step : State → State → Prop}
    (Total : State → ℝ) (Work : State → State → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hpaid : ∀ {x y}, Step x y → Total y + Work x y ≤ Total x)
    (hwork : ∀ {x y}, Step x y → δ ≤ Work x y)
    (hnonneg : ∀ x, 0 ≤ Total x) :
    ¬ ∃ path : ℕ → State, ∀ k, Step (path k) (path (k + 1)) := by
  rintro ⟨path, hstep⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (Total (path 0) / δ)
  have hb := real_cascade_bounded_of_uniform_work Total Work δ hδ hpaid hwork hnonneg path hstep n
  have : Total (path 0) / δ * δ < (n : ℝ) * δ :=
    mul_lt_mul_of_pos_right hn hδ
  rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
  linarith

/-! ### §10. Partition и capacity / overflow -/

/-- Разбиение `[1,X]` на релевантную (twin-carrier) и нерелевантную части. -/
structure LiouvilleTwinPartition where
  relevant : ℕ → Finset ℕ
  irrelevant : ℕ → Finset ℕ
  disjoint : ∀ X, Disjoint (relevant X) (irrelevant X)
  union_eq : ∀ X, relevant X ∪ irrelevant X = Finset.Icc 1 X

/-- Суммирующая функция Лиувилля. -/
noncomputable def L (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, liouville n

/-- Релевантная сумма. -/
noncomputable def LRelevant (P : LiouvilleTwinPartition) (X : ℕ) : ℤ :=
  ∑ n ∈ P.relevant X, liouville n

/-- Нерелевантная сумма. -/
noncomputable def LIrrelevant (P : LiouvilleTwinPartition) (X : ℕ) : ℤ :=
  ∑ n ∈ P.irrelevant X, liouville n

/-- **`L_eq_relevant_add_irrelevant` — ДОКАЗАНА (sorry blueprint'а закрыт).** `L = LRelevant + LIrrelevant`
    по разбиению непересекающегося объединения (`Finset.sum_union`). -/
theorem L_eq_relevant_add_irrelevant (P : LiouvilleTwinPartition) (X : ℕ) :
    L X = LRelevant P X + LIrrelevant P X := by
  unfold L LRelevant LIrrelevant
  rw [← P.union_eq X, Finset.sum_union (P.disjoint X)]

/-- `LiouvilleViolation` (глобальный дисбаланс) — из `RankJumpBridge`. -/
def LiouvilleViolation : Prop := EuclidsPath.RankJumpBridge.LiouvilleViolation

/-- Нерелевантная часть ограничена (аналитический ВХОД, не доказан). -/
def IrrelevantCancellation (P : LiouvilleTwinPartition) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ X : ℕ, |(LIrrelevant P X : ℝ)| ≤ C * (X : ℝ) ^ ((1 / 2 : ℝ) + ε)

/-- Релевантный дисбаланс (то, что переполняет после overflow). -/
def RelevantLiouvilleViolation (P : LiouvilleTwinPartition) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 < C →
    ∃ X : ℕ, C * (X : ℝ) ^ ((1 / 2 : ℝ) + ε) < |(LRelevant P X : ℝ)|

/--
  **`relevantViolation_of_globalViolation` — ДОКАЗАНА (§10 overflow, sorry blueprint'а закрыт).**
  Если глобальный дисбаланс есть, а нерелевантная часть ограничена, то релевантная часть переполняется.
  Triangle: `|L| ≤ |LRelevant| + |LIrrelevant|`; при большом `|L|` и ограниченном `|LIrrelevant|`
  большим обязан быть `|LRelevant|`. Берём `C' = C + Cirr` (bound нерелевантной части) как порог. -/
theorem relevantViolation_of_globalViolation (P : LiouvilleTwinPartition)
    (hCancel : IrrelevantCancellation P)
    (hV : LiouvilleViolation) : RelevantLiouvilleViolation P := by
  obtain ⟨ε, hε, hbig⟩ := hV
  obtain ⟨Cirr, hCirr, hirr⟩ := hCancel ε hε
  refine ⟨ε, hε, ?_⟩
  intro C hC
  -- порог для глобального дисбаланса: C + Cirr
  obtain ⟨X, hX⟩ := hbig (C + Cirr) (by positivity)
  refine ⟨X, ?_⟩
  -- |L X| = |LRelevant + LIrrelevant| ≤ |LRelevant| + |LIrrelevant|
  have hLsplit : (L X : ℝ) = (LRelevant P X : ℝ) + (LIrrelevant P X : ℝ) := by
    have := L_eq_relevant_add_irrelevant P X
    exact_mod_cast this
  have htri : |(L X : ℝ)| ≤ |(LRelevant P X : ℝ)| + |(LIrrelevant P X : ℝ)| := by
    rw [hLsplit]; exact abs_add_le _ _
  have hirrX : |(LIrrelevant P X : ℝ)| ≤ Cirr * (X : ℝ) ^ ((1 / 2 : ℝ) + ε) := hirr X
  -- hX : (C+Cirr)*X^... < |L X|
  -- (C+Cirr)·Xᵖ < |L| ≤ |LRel| + |LIrr| ≤ |LRel| + Cirr·Xᵖ  ⟹  C·Xᵖ < |LRel|
  set p := (X : ℝ) ^ ((1 / 2 : ℝ) + ε) with hp
  have h1 : (C + Cirr) * p < |(LRelevant P X : ℝ)| + |(LIrrelevant P X : ℝ)| :=
    lt_of_lt_of_le hX htri
  have h2 : |(LIrrelevant P X : ℝ)| ≤ Cirr * p := hirrX
  nlinarith [h1, h2]

/-! ### §11. Pairing capacity: релевантный дисбаланс не влезает в сокращающиеся пары ⟹ jump -/

/-- `TwinCarrierEnergyJump` — из `RankJumpBridge`. -/
def TwinCarrierEnergyJump (TwinSystem : RankParitySystem) : Prop :=
  EuclidsPath.RankJumpBridge.TwinCarrierEnergyJump TwinSystem

/-- Pairing-структура: релевантные точки кодируются в twin-систему; сокращающиеся пары флипают знак;
    несокращённый остаток даёт jump (последнее поле — аналитический ВХОД). -/
structure TwinCarrierPairing (P : LiouvilleTwinPartition) (TwinSystem : RankParitySystem) where
  encode : ∀ {X : ℕ}, {n : ℕ // n ∈ P.relevant X} → TwinSystem.State
  paired : TwinSystem.State → TwinSystem.State → Prop
  paired_flips_sign : ∀ a b, paired a b → TwinSystem.sign a = - TwinSystem.sign b
  unpaired_gives_jump : RelevantLiouvilleViolation P → TwinCarrierEnergyJump TwinSystem

/-- **`twinJump_of_relevantViolation` — ДОКАЗАНА (§11).** Релевантный дисбаланс ⟹ twin jump (через
    вход `unpaired_gives_jump`). -/
theorem twinJump_of_relevantViolation (P : LiouvilleTwinPartition)
    (TwinSystem : RankParitySystem) (Pair : TwinCarrierPairing P TwinSystem)
    (hRel : RelevantLiouvilleViolation P) : TwinCarrierEnergyJump TwinSystem :=
  Pair.unpaired_gives_jump hRel

/-- Полный localization-пакет: разбиение + cancellation + pairing. -/
structure LiouvilleToTwinLocalization (TwinSystem : RankParitySystem) where
  P : LiouvilleTwinPartition
  irrelevant_cancellation : IrrelevantCancellation P
  pairing : TwinCarrierPairing P TwinSystem

/--
  **`liouvilleViolation_localizes — ДОКАЗАНА (сборка §10+§11).** Полный пакет декомпозирует узел
  `RankJumpLocalizationTarget`: глобальный Лиувилль-дисбаланс ⟹ (overflow) релевантный дисбаланс ⟹
  (pairing) twin jump. Это разбивает ОДИН крупный вход `RankJumpLocalization` на ДВА меньших
  (`irrelevant_cancellation`, `pairing.unpaired_gives_jump`). Сами они — аналитические входы, не доказаны. -/
theorem liouvilleViolation_localizes (TwinSystem : RankParitySystem)
    (Loc : LiouvilleToTwinLocalization TwinSystem)
    (hV : LiouvilleViolation) : TwinCarrierEnergyJump TwinSystem := by
  have hRel : RelevantLiouvilleViolation Loc.P :=
    relevantViolation_of_globalViolation Loc.P Loc.irrelevant_cancellation hV
  exact twinJump_of_relevantViolation Loc.P TwinSystem Loc.pairing hRel

end EuclidsPath.DissipativeCascade
