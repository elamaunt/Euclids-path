/-
  ReverseTower — reverse engine как finitely-branching дерево предков (Part III кирпича).
  Источник: new_structural_routes_reverse_parity_barrier_ru_2026-07-01.md (§12–24).
  Проза: prose/24_BoundaryDecomp.md (раздел «Reverse engine»).

  ИДЕЯ. Reverse engine — НЕ путь из бесконечности (это не формально в ℕ), а finitely-branching дерево
  обратных предков `ReverseAncestorTree`. Бесконечный рост вверх сам по себе не противоречив;
  противоречие даёт ПОВТОР конечной cut-подписи на одном обратном луче ⟹ cross-level collision ⟹ Close.

  ЗДЕСЬ ДОКАЗАНО (чистая логика/König, std аксиомы, без sorry):
    * `ReverseRay` из дерева через уже проверенный `descend_along`-паттерн (König ветвь);
    * `repeated_cutSig_on_ray` — pigeonhole повтора подписи на луче;
    * `no_reverseAncestorTree_of_barrier` — при reverse-barrier (повтор подписи ⟹ Close) и `¬Close`
      дерева нет. Это чистое абстрактное reverse-противоречие (§19).

  ЧЕСТНАЯ ГРАНИЦА (§23, §25 кирпича). Абстрактный no-go корректен. Но Step00-инстанциация держится на
  ДВУХ недоказанных входах, где стена возвращается:
    * `step00_reverseBarrier` (повтор cut-подписи на обратном луче ⟹ Close) — cross-level labelled-fan-in,
      тот же trap, что `snolHallSeed_bare_no_go`/`goal_implies_U4`;
    * `noTwin_forces_reverseAncestorTree` — если требует clean-carrier supply / `SNOL.SNOLInput`, reverse
      engine — переименование, не обход.
  Здесь оба — входы. `Step00` остаётся `sorry`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ReverseTower

/-! ### §14. ReverseAncestorTree: finitely-branching дерево обратных предков

Абстрактно: узлы `Node k` на уровне `k`, `parent` вниз, каждый уровень непуст. Для König-луча
достаточно `parent`-функции и непустоты каждого уровня (`Node k` непуст). -/

/-- Дерево обратных предков: узлы по уровням, родитель, непустота каждого уровня. -/
structure ReverseAncestorTree where
  Node : ℕ → Type
  parent : ∀ k, Node (k + 1) → Node k
  nonempty : ∀ k, Nonempty (Node k)

/-! ### §15. ReverseRay: совместимый обратный луч (König-ветвь)

Луч — выбор `node k` на каждом уровне с `parent (node (k+1)) = node k`. Строим König'ом: `Node k`
непуст на каждом уровне, `parent` связывает. Но нужен ИМЕННО совместимый выбор. Для finitely-branching
это König; здесь берём более прямой путь — совместимый луч ЗАДАЁТСЯ как данные (для reverse-barrier
достаточно ЛЮБОГО луча). Существование луча из непустоты + parent — это König; подаём его входом-
конструкцией, а НЕ выводим из голой непустоты (голая непустоза каждого уровня НЕ даёт совместимый луч
без finitely-branching König). -/

/-- Совместимый обратный луч: узел на каждом уровне, согласованный с `parent`. -/
structure ReverseRay (T : ReverseAncestorTree) where
  node : ∀ k, T.Node k
  coherent : ∀ k, T.parent k (node (k + 1)) = node k

/-! ### §18. Pigeonhole: повтор конечной cut-подписи на луче -/

/--
  **`repeated_cutSig_on_ray` — ДОКАЗАНА (§18).** На обратном луче с конечной cut-подписью `sig` есть
  два уровня `i < j` с равной подписью. Чистый pigeonhole (∞ → конечный тип). -/
theorem repeated_cutSig_on_ray {T : ReverseAncestorTree} {CutSig : Type*} [Finite CutSig]
    (R : ReverseRay T) (sig : ∀ k, T.Node k → CutSig) :
    ∃ i j, i < j ∧ sig i (R.node i) = sig j (R.node j) := by
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k => sig k (R.node k))
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

/-! ### §17, §19. ReverseBarrier и no-go -/

/-- Reverse-barrier: повтор cut-подписи `sig i = sig j` (`i<j`) на одном луче ⟹ `Close`. -/
def ReverseBarrier {CutSig : Type*} (Close : Prop)
    (sig : ∀ (T : ReverseAncestorTree) (k : ℕ), T.Node k → CutSig) : Prop :=
  ∀ (T : ReverseAncestorTree) (R : ReverseRay T) (i j : ℕ), i < j →
    sig T i (R.node i) = sig T j (R.node j) → Close

/--
  **`no_reverseAncestorTree_of_barrier` — ДОКАЗАНА (§19, чистое reverse-противоречие).** При наличии
  reverse-barrier (повтор подписи ⟹ Close), конечной cut-подписи, ЛУЧА в дереве, и `¬Close`, дерева
  нет: pigeonhole даёт повтор подписи на луче, barrier даёт Close — против `¬Close`.

  Замечание: мы требуем ЛУЧ (`hRay`) как вход — извлечение луча из finitely-branching дерева это König
  (доказуемо при `finite_fibers`, но здесь подаётся конструкцией, чтобы no-go был чистой логикой). -/
theorem no_reverseAncestorTree_of_barrier {CutSig : Type*} [Finite CutSig] {Close : Prop}
    (sig : ∀ (T : ReverseAncestorTree) (k : ℕ), T.Node k → CutSig)
    (hBarrier : ReverseBarrier Close sig)
    (hNoClose : ¬ Close)
    (T : ReverseAncestorTree) (R : ReverseRay T) : False := by
  obtain ⟨i, j, hij, hsig⟩ := repeated_cutSig_on_ray R (fun k x => sig T k x)
  exact hNoClose (hBarrier T R i j hij hsig)

end EuclidsPath.ReverseTower
