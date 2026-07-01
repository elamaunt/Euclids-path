/-
  ObstructionClosure — абстрактный well-founded «двигатель» на положительных obstruction-сертификатах.
  Источник: step00_obstruction_closure_badcert_engine_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Obstruction-двигатель»).

  ИДЕЯ (и её граница). Прежние обходы (BadCoverDescent, SmallCleanSupply) оказались циркулярны, потому
  что `Bad := ¬Good` не несёт положительной структуры. Этот кирпич предлагает искать двигатель в
  ПОЛОЖИТЕЛЬНОМ obstruction-сертификате: `Bad m ⟹ ∃ obs, ObsAt obs m`, и `ObsAt obs m ⟹ Close ∨
  меньший obs`. Тогда well-founded индукция по `rank obs` даёт `Bad m ⟹ Close`.

  ЗДЕСЬ ДОКАЗАНО (чистая механика, стандартные аксиомы, без sorry, БЕЗ арифметики простых):
    * `obs_closes` — well-founded reduction ⟹ Close (ядро §5.1);
    * `mem_bad_closes_of_obstruction_reduction` — bad→obs + reduction ⟹ bad→Close (§5.2);
    * `exists_close_of_nonempty_carrier_and_bad_engine` — полная абстрактная сборка (§6);
    * `goal_of_exists_close`, `goal_all_of_exists_close_all` — снятие engine-ветки под `¬Engine` (§7).

  ГЛАВНЫЙ АУДИТНЫЙ ТЕСТ КИРПИЧА (§13) — ПРОВЕРЕН ЭМПИРИЧЕСКИ, РЕЗУЛЬТАТ ОТРИЦАТЕЛЬНЫЙ:
  в кодовой базе НЕТ `def bad`/`def good`/`def carrier`/`Obs`/`LocalObstruction`. Реальный узел
  `SNOL.SNOLInput` (`Engine/SNOL.lean:69`) использует `bad, carrier : Finset ℕ` как ЭКЗИСТЕНЦИАЛЬНО-
  квантифицированные абстрактные множества с ЕДИНСТВЕННЫМ содержательным условием `bad.card <
  carrier.card` (counting), а `twin_center_of_block` тянет survivor из `survivor_of_not_covered` —
  чистый counting. То есть `SNOL.bad` — НЕ положительный obstruction-объект, а counting-объект.

  ВЫВОД (по no-go критерию §16 самого кирпича): положительной obstruction-семантики для `SNOL.bad`
  НЕТ, поэтому U1 (`mem_bad_to_obstruction`) и U2 (`obstruction_reduce`) НЕинстанциируемы без цели/
  counting, и этот двигатель на реальном узле НЕ ЗАПУСКАЕТСЯ. Абстрактный модуль корректен и
  переиспользуем, но его входы к `SNOL.SNOLInput` не привязываются. Итог аудита стоит:
  `SNOL.SNOLInput` — настоящая density/counting/parity стена. `Step00` остаётся `sorry`.

  ВАЖНО (чтобы никто не принял «положительный obstruction» за лазейку): даже ЕСЛИ построить
  obstruction для `6m±1` (уже частично построен: `ObsAt` = old-peel/active ребро с большим простым
  делителем, `rank` = высота-центр). Шаги редукции U2 доказуемы НЕциркулярно (`cofactor_is_center`,
  `old_peel_height_drop`, `active_descent_height` — реальная алгебра спуска, catch — это ступенька, а
  не стена). НО в РАНГ-0 терминале (clean-центр с ПРОСТЫМИ сторонами) ветви `regeneration_dichotomy`
  (составная сторона / old-peel) ОБЕ исчезают, остаётся ровно «это twin» — то есть U2-терминал
  «Close ∨ меньший obs» сводится к «Close ∨ ничего» = ЦЕЛЬ. Та же circularity-подпись, что машинно
  зафиксирована в `BadCoverDescent.descent_reduction_is_circular` и
  `ConcreteComponents.smallCleanSupply_iff_goal` (обе: вход ⟺ цель). Двигатель добавляет реальную
  лемму спуска и более точную локализацию стены, но НИЧЕГО не закрывает.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ObstructionClosure

/-! ### §5.1. Ядро: well-founded reduction obstruction'а ⟹ Close -/

/--
  **`obs_closes` — ДОКАЗАНА.** Если каждый obstruction либо сразу закрывает `Close`, либо редуцируется
  к obstruction строго меньшего ранга, то любой obstruction закрывает `Close`. Well-founded induction
  по `rank : Obs → ℕ` (через `InvImage.wf Nat.lt_wfRel.wf`). -/
theorem obs_closes {Obs Point : Type*}
    (rank : Obs → ℕ) (ObsAt : Obs → Point → Prop) (Close : Prop)
    (hReduce : ∀ {x : Point} {obs : Obs}, ObsAt obs x →
      Close ∨ ∃ x' obs', ObsAt obs' x' ∧ rank obs' < rank obs) :
    ∀ {x : Point} {obs : Obs}, ObsAt obs x → Close := by
  intro x obs hobs
  have hWF : WellFounded (fun a b : Obs => rank a < rank b) :=
    InvImage.wf rank Nat.lt_wfRel.wf
  exact hWF.induction obs
    (C := fun obs => ∀ x, ObsAt obs x → Close)
    (fun obs IH x hobs => by
      rcases hReduce hobs with hClose | ⟨x', obs', hobs', hlt⟩
      · exact hClose
      · exact IH obs' hlt x' hobs')
    x hobs

/-! ### §5.2. Membership-in-bad даёт obstruction ⟹ bad закрывает -/

/--
  **`mem_bad_closes_of_obstruction_reduction` — ДОКАЗАНА.** Если `Bad x` даёт положительный
  obstruction-свидетель (`hBadToObs`), а reduction well-founded (`hReduce`), то любой bad закрывает
  `Close`. Это `obs_closes`, применённый к извлечённому свидетелю.

  КЛЮЧЕВОЙ ВХОД `hBadToObs` — вот где живёт вся содержательность: он требует ПОЛОЖИТЕЛЬНОЙ
  obstruction-структуры у `Bad`. Для `SNOL.bad` (counting-объект) такой структуры НЕТ. -/
theorem mem_bad_closes_of_obstruction_reduction {Obs Point : Type*}
    (Bad : Point → Prop) (rank : Obs → ℕ) (ObsAt : Obs → Point → Prop) (Close : Prop)
    (hBadToObs : ∀ {x : Point}, Bad x → ∃ obs : Obs, ObsAt obs x)
    (hReduce : ∀ {x : Point} {obs : Obs}, ObsAt obs x →
      Close ∨ ∃ x' obs', ObsAt obs' x' ∧ rank obs' < rank obs) :
    ∀ {x : Point}, Bad x → Close := by
  intro x hx
  obtain ⟨obs, hobs⟩ := hBadToObs hx
  exact obs_closes rank ObsAt Close hReduce hobs

/-! ### §6. Абстрактная сборка carrier / good / bad -/

/--
  **`exists_close_of_nonempty_carrier_and_bad_engine` — ДОКАЗАНА (абстрактная сборка §6).** Если
  carrier непуст, каждый carrier-point good или bad, good закрывает, а bad закрывается через
  obstruction-engine, то для каждого `N` существует `A` с `CloseAt A N`. Чистая логика + `obs_closes`. -/
theorem exists_close_of_nonempty_carrier_and_bad_engine
    {Obs : ℕ → ℕ → Type*}
    (Carrier : ℕ → ℕ → ℕ → Prop) (Good : ℕ → ℕ → ℕ → Prop) (Bad : ℕ → ℕ → ℕ → Prop)
    (CloseAt : ℕ → ℕ → Prop)
    (rank : ∀ {A N : ℕ}, Obs A N → ℕ) (ObsAt : ∀ {A N : ℕ}, Obs A N → ℕ → Prop)
    (hCarrierNonempty : ∀ N, ∃ A m, Carrier A N m)
    (hGoodOrBad : ∀ {A N m}, Carrier A N m → Good A N m ∨ Bad A N m)
    (hGoodCloses : ∀ {A N m}, Carrier A N m → Good A N m → CloseAt A N)
    (hBadToObs : ∀ {A N m}, Bad A N m → ∃ obs : Obs A N, ObsAt obs m)
    (hReduce : ∀ {A N m} {obs : Obs A N}, ObsAt obs m →
      CloseAt A N ∨ ∃ (m' : ℕ) (obs' : Obs A N), ObsAt obs' m' ∧ rank obs' < rank obs) :
    ∀ N, ∃ A, CloseAt A N := by
  intro N
  obtain ⟨A, m, hm⟩ := hCarrierNonempty N
  refine ⟨A, ?_⟩
  rcases hGoodOrBad hm with hGood | hBad
  · exact hGoodCloses hm hGood
  · exact mem_bad_closes_of_obstruction_reduction
      (Bad := fun x => Bad A N x) (rank := @rank A N) (ObsAt := @ObsAt A N)
      (Close := CloseAt A N)
      (fun {x} hx => hBadToObs hx) (fun {x obs} hobs => hReduce hobs) hBad

/-! ### §7. Снятие engine-ветки под `¬Engine` -/

/--
  **`goal_of_exists_close` — ДОКАЗАНА.** При `CloseAt := Engine ∨ (∃ t>N, Twin t)` и `¬Engine`,
  `∃ A, CloseAt A N` даёт `∃ t>N, Twin t`. Чистая логика (разбор дизъюнкции). -/
theorem goal_of_exists_close {Engine : ℕ → Prop} {Twin : ℕ → Prop} {N : ℕ}
    (hNoEngine : ∀ A, ¬ Engine A)
    (hClose : ∃ A, Engine A ∨ ∃ t, N < t ∧ Twin t) :
    ∃ t, N < t ∧ Twin t := by
  obtain ⟨A, hE | hT⟩ := hClose
  · exact absurd hE (hNoEngine A)
  · exact hT

/-- **`goal_all_of_exists_close_all` — ДОКАЗАНА.** Версия для всех `N`. -/
theorem goal_all_of_exists_close_all {Engine : ℕ → Prop} {Twin : ℕ → Prop}
    (hNoEngine : ∀ A, ¬ Engine A)
    (hCloseAll : ∀ N, ∃ A, Engine A ∨ ∃ t, N < t ∧ Twin t) :
    ∀ N, ∃ t, N < t ∧ Twin t :=
  fun N => goal_of_exists_close hNoEngine (hCloseAll N)

end EuclidsPath.ObstructionClosure
