/-
  ManyUnresolved — маршрут «бесконечно много unresolved terminals ⟹ collision подписей ⟹ Engine».
  Источник: step00_manyunresolved_signature_collision_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Many-unresolved collision»).

  ИДЕЯ (отличие от прежних). Прежние маршруты закрывали ОДИН terminal локально — и он в rank-0 всегда
  схлопывался в «предъяви twin» = цель (ObstructionClosure, аудит). Здесь другое: НЕ закрывать один
  terminal, а закрыть МАССОВОЕ семейство через pigeonhole + local determinism. Схема:
    NoNewTwinAbove N ⟹ ∞ high starts ⟹ (many old-absorbed ∨ many unresolved) ⟹ Engine ∨ TwinAbove.

  ЗДЕСЬ ДОКАЗАН абстрактный КОМБИНАТОРНЫЙ костяк (стандартные аксиомы, без sorry, без арифметики
  простых):
    * `infinite_split` — ∞ множество, покрытое двумя классами ⟹ один класс ∞ (§5);
    * `infinite_two_same_sig` — ∞ множество + карта в Fintype ⟹ два РАЗНЫХ элемента с равной подписью (§9);
    * `many_unresolved_force_close` — при U4 (same-sig ⟹ Close) ∞ unresolved ⟹ Close (§11);
    * `close_of_highStarts` — полная сборка (§12): split исходов + old-branch + unresolved-branch ⟹ Close;
    * `forall_goal_of_engine` — снятие engine-ветки под ¬Engine ⟹ ∀N ∃twin>N ⟹ `TwinLowers.Infinite` (§13).

  ЧЕТЫРЕ ВХОДА (U1–U4), от которых зависит ЖИЗНЬ маршрута — здесь ЯВНЫЕ гипотезы:
    U1 `hFixedStarts`  : ∀N ∃A, ∞ high starts (CRT при фикс. A, НЕ density-below-A²);
    U2 `hOutcome`      : high start ⟹ old-absorbed ∨ unresolved ∨ Close (БЕЗ `SNOL.SNOLInput`);
    U3 `[Finite Sig]`  : конечная подпись unresolved terminal (НЕ хранит m/path/genealogy);
    U4 `hSameSig`      : два РАЗНЫХ старта с равной подписью ⟹ Close (через local determinism, НЕ twin).

  ЧЕСТНАЯ ГРАНИЦА (исправлена после аудита — маршрут ЦИРКУЛЯРЕН, как шесть предыдущих). Костяк — чистая
  комбинаторика, доказан. Но маршрут НЕ жив:
    * U4 (`hSameSig`) циркулярен НЕ только в терминале, а В КАЖДОЙ genuine-collision ветке. Первичное
      предположение «нетерминальные случаи закрываются через `active_component_determinism`/
      `oldPeel_component_determinism`» — ОШИБОЧНО (аудит): эти леммы доказывают ДРУГОЕ — one-step
      детерминизм над ОБЩИМ base `V` (два предшественника ОДНОГО `V` совпадают при равной метке через
      separating scale). Они (а) здесь даже не импортированы/не применены, и (б) НЕ берут два РАЗНЫХ
      старта `m₁≠m₂` и НЕ дают `Close`. А pigeonhole-collision в конечный кодомен как раз НЕ даёт общего
      base. Направление противоположное. Значит U4 — недоказанный вход во всех ветках.
    * Машинно: `goal_implies_U4` — цель разряжает U4 ⟹ U4 at-least-as-hard-as goal; обратное — сама
      гипотеза. Наиболее наглядно в rank-0 clean prime-sided терминале: единственный `Close` =
      «предъяви twin» = цель (как `ObstructionClosure`, `smallCleanSupply_iff_goal`).
    * U2 (outcome-split old-absorbed/unresolved) ТРЕБУЕТ counting: знать, что unresolved-класс
      бесконечен на фикс. масштабе — это ровно `bad.card < carrier.card` = `SNOL.SNOLInput`. U2
      переносит стену, не пробивает.
    * U1: `carrier_nonempty_above` даёт ОДИН clean-центр выше N (честный CRT, без плотности), но
      `hFixedStarts` требует БЕСКОНЕЧНОЕ семейство на фикс. масштабе — этого single-center факт НЕ даёт.
  Маршрут даёт более точную локализацию (стена = U2-split + U4-collision), но НЕ закрывает. `Step00`
  остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ManyUnresolved

open Set EuclidsPath

/-! ### §5. Бесконечное разделение исходов -/

/--
  **`infinite_split` — ДОКАЗАНА.** Бесконечное `S`, каждый элемент которого попадает в класс `P` или
  `Q`, разбивается так, что один из классов бесконечен. Чистая комбинаторика (объединение двух
  конечных было бы конечно). -/
theorem infinite_split {α : Type*} (S : Set α) (hS : S.Infinite)
    (P Q : α → Prop) (hcov : ∀ x ∈ S, P x ∨ Q x) :
    {x ∈ S | P x}.Infinite ∨ {x ∈ S | Q x}.Infinite := by
  by_contra h
  push_neg at h
  obtain ⟨hP, hQ⟩ := h
  have hsub : S ⊆ {x ∈ S | P x} ∪ {x ∈ S | Q x} := by
    intro x hx; rcases hcov x hx with hp | hq
    · exact Or.inl ⟨hx, hp⟩
    · exact Or.inr ⟨hx, hq⟩
  exact hS ((hP.union hQ).subset hsub)

/-! ### §9. Бесконечное множество + конечная подпись ⟹ collision -/

/--
  **`infinite_two_same_sig` — ДОКАЗАНА (pigeonhole §9).** Бесконечное `S` и карта `sig : α → Sig` в
  конечный тип дают два РАЗНЫХ элемента с равной подписью. (Иначе `sig` инъективна на `S` ⟹ `S`
  конечно.) -/
theorem infinite_two_same_sig {α : Type*} {Sig : Type*} [Finite Sig]
    (S : Set α) (hS : S.Infinite) (sig : α → Sig) :
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, x₁ ≠ x₂ ∧ sig x₁ = sig x₂ := by
  by_contra h
  push_neg at h
  have hinj : Set.InjOn sig S := fun a ha b hb hab => by
    by_contra hne; exact h a ha b hb hne hab
  exact hS (Set.Finite.of_finite_image (Set.toFinite _) hinj)

/-! ### §11. Many unresolved ⟹ Close (через U4)

Абстрактно: `HighStart`, `Unresolved`, `Sig` — параметры; `sig : subtype → Sig`. `ManyUnresolved` —
бесконечность множества high-start-unresolved точек. При U4 (равная подпись у разных ⟹ Close) collision
даёт Close. -/

/--
  **`many_unresolved_force_close` — ДОКАЗАНА (при U4).** Если множество unresolved high-starts
  бесконечно, подпись конечна, и равная подпись у РАЗНЫХ стартов даёт `Close`, то `Close`. Собирается
  из `infinite_two_same_sig`. Вся нетривиальность — в `hSameSig` (U4). -/
theorem many_unresolved_force_close {Sig : Type*} [Finite Sig] {Close : Prop}
    (U : ℕ → Prop) (sig : ℕ → Sig)
    (hMany : {m : ℕ | U m}.Infinite)
    (hSameSig : ∀ m₁ m₂, U m₁ → U m₂ → m₁ ≠ m₂ → sig m₁ = sig m₂ → Close) :
    Close := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hne, hsig⟩ := infinite_two_same_sig {m : ℕ | U m} hMany sig
  exact hSameSig m₁ m₂ hm₁ hm₂ hne hsig

/-! ### §12. Полная диагностическая редукция -/

/--
  **`close_of_highStarts` — ДОКАЗАНА (сборка §12).** При:
    * бесконечности high starts,
    * покрытии исходов (`hOutcome`: каждый high start old-absorbed ∨ unresolved ∨ Close),
    * old-branch закрытии (`hOldCloses`: many old-absorbed ⟹ Close),
    * unresolved-branch закрытии (`hUnrCloses`: many unresolved ⟹ Close),
  получаем `Close`. Разбор по `infinite_split` исходов (Close-случай ловится, если хоть один старт
  даёт Close). -/
theorem close_of_highStarts {Close : Prop}
    (HighStart OldAbsorbed Unresolved : ℕ → Prop)
    (hInf : {m : ℕ | HighStart m}.Infinite)
    (hOutcome : ∀ m, HighStart m → OldAbsorbed m ∨ Unresolved m ∨ Close)
    (hOldCloses : {m : ℕ | HighStart m ∧ OldAbsorbed m}.Infinite → Close)
    (hUnrCloses : {m : ℕ | HighStart m ∧ Unresolved m}.Infinite → Close) :
    Close := by
  -- если Close достигается на каком-то старте — сразу done
  by_cases hc : ∃ m, HighStart m ∧ Close
  · obtain ⟨m, _, hcl⟩ := hc; exact hcl
  · push_neg at hc
    -- иначе каждый high start — old-absorbed ∨ unresolved
    have hcov : ∀ m ∈ {m : ℕ | HighStart m}, OldAbsorbed m ∨ Unresolved m := by
      intro m hm
      rcases hOutcome m hm with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hc m hm)
    rcases infinite_split {m : ℕ | HighStart m} hInf OldAbsorbed Unresolved hcov with hO | hU
    · exact hOldCloses hO
    · exact hUnrCloses hU

/-! ### §13. Финальная сборка по N и снятие engine -/

/--
  **`forall_goal_of_engine` — ДОКАЗАНА (условная сборка §13).** При U1 (∞ high starts на фикс. масштабе)
  и закрытии всех веток в `CloseAt := Engine ∨ ∃ t>N, twin`, под `¬Engine` получаем `∀N ∃twin>N`.
  Engine-ветка снимается `hNoEngine`. -/
theorem forall_goal_of_engine {Engine : ℕ → Prop}
    (HighStart OldAbsorbed Unresolved : ℕ → ℕ → ℕ → Prop)
    (hFixedStarts : ∀ N, ∃ A, {m : ℕ | HighStart A N m}.Infinite)
    (hOutcome : ∀ A N, ∀ m, HighStart A N m →
      OldAbsorbed A N m ∨ Unresolved A N m ∨ (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hOldCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ OldAbsorbed A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hUnrCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ Unresolved A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hNoEngine : ∀ A, ¬ Engine A) :
    ∀ N, ∃ t, N < t ∧ IsTwinCenter t := by
  intro N
  obtain ⟨A, hInf⟩ := hFixedStarts N
  have hclose : Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t :=
    close_of_highStarts (Close := Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t)
      (HighStart A N) (OldAbsorbed A N) (Unresolved A N)
      hInf (hOutcome A N) (hOldCloses A N) (hUnrCloses A N)
  rcases hclose with he | ht
  · exact absurd he (hNoEngine A)
  · exact ht

/--
  **`twin_prime_conjecture_of_engine` — ДОКАЗАНА (условная).** Та же сборка + доказанный мост
  `infinite_of_unbounded_centers` ⟹ `TwinLowers.Infinite`. -/
theorem twin_prime_conjecture_of_engine {Engine : ℕ → Prop}
    (HighStart OldAbsorbed Unresolved : ℕ → ℕ → ℕ → Prop)
    (hFixedStarts : ∀ N, ∃ A, {m : ℕ | HighStart A N m}.Infinite)
    (hOutcome : ∀ A N, ∀ m, HighStart A N m →
      OldAbsorbed A N m ∨ Unresolved A N m ∨ (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hOldCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ OldAbsorbed A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hUnrCloses : ∀ A N, {m : ℕ | HighStart A N m ∧ Unresolved A N m}.Infinite →
      (Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t))
    (hNoEngine : ∀ A, ¬ Engine A) :
    TwinLowers.Infinite :=
  infinite_of_unbounded_centers
    (forall_goal_of_engine HighStart OldAbsorbed Unresolved
      hFixedStarts hOutcome hOldCloses hUnrCloses hNoEngine)

/-! ### §U4. Само-аудит (исправлен после аудита): U4 циркулярен во всех genuine-collision ветках

Честная оценка входа U4 (`hSameSig`), исправленная адверсариальным аудитом. Первоначально я заявил,
что НЕТЕРМИНАЛЬНЫЕ случаи U4 закрываются через `active_component_determinism`/`oldPeel_component_determinism`.
Это ОШИБКА, и я её принимаю. Эти леммы доказывают ДРУГОЕ: one-step детерминизм над ОБЩИМ base `V` (два
предшественника ОДНОГО `V` при равной метке совпадают — separating scale). Они НЕ берут два РАЗНЫХ
старта `m₁≠m₂`, НЕ дают `Close`, и здесь даже не импортированы. Pigeonhole-collision в конечный кодомен
общего base НЕ даёт — направление противоположное. Значит U4 — недоказанный вход ВЕЗДЕ, не только в
терминале.

Машинно (`goal_implies_U4`): цель разряжает U4 ⟹ U4 at-least-as-hard-as goal. Наиболее наглядно в
rank-0 clean prime-sided терминале: единственный `Close` = «предъяви twin» = цель (fine-vs-coarse
трилемма: fine-подпись определяет `m` ⟹ не конечна ⟹ ⊥U3; конечная coarse-подпись не различает старты
⟹ ⊥U4). Тот же статус, что `smallCleanSupply_iff_goal` / `descent_reduction_is_circular`. -/

/--
  **`goal_implies_U4` — ДОКАЗАНА (само-аудит: U4 at-least-as-hard-as goal).** Цель `∃t>N, twin`
  тривиально разряжает вход U4 (`Close` = цель). Значит U4 не легче цели во ВСЕХ genuine-collision
  ветках (не только терминал); маршрут циркулярен, как шесть предыдущих. -/
theorem goal_implies_U4 {N : ℕ} (hgoal : ∃ t, N < t ∧ IsTwinCenter t)
    {Sig : Type} (U : ℕ → Prop) (sig : ℕ → Sig) :
    ∀ m₁ m₂, U m₁ → U m₂ → m₁ ≠ m₂ → sig m₁ = sig m₂ → (∃ t, N < t ∧ IsTwinCenter t) :=
  fun _ _ _ _ _ _ => hgoal

/-! ### §Э. Теорема высшей энергетической несовместимости (4 канала — обобщение)

Кирпич `higher_energy_incompatibility` обобщает `close_of_highStarts` до ЧЕТЫРЁХ каналов, добавляя
явный `DescentSeed` (запрещённый бесконечный legal descent, убиваемый EPMI). Теорема — чистая
комбинаторная несовместимость: бесконечное семейство high-starts не может избежать всех четырёх
каналов. Это ДОКАЗУЕМО и НЕ циркулярно КАК КОМБИНАТОРНОЕ УТВЕРЖДЕНИЕ.

ЧЕСТНО (что это НЕ меняет): новый `DescentSeed`-канал закрывается тривиально (`hNoDescent`, EPMI) и
НЕ добавляет escape. Содержательные входы — те же `hOutcome` (U2) и `hUnresolvedManyCloses` (U4/E3),
которые адверсариальный аудит (`w16s8jc2v`) уже признал: U2 требует counting (= `SNOL.SNOLInput`), U4
циркулярен во всех genuine-collision ветках (`goal_implies_U4`). Обобщение до 4 каналов соундно, но
стену не двигает. -/

/-- §5. Вспомогательная: `S ⊆ A ∪ B`, `S` бесконечно ⟹ `A` или `B` бесконечно. -/
theorem infinite_or_infinite_of_subset_union {α : Type*} {S A B : Set α}
    (hInf : S.Infinite) (hSub : S ⊆ A ∪ B) : A.Infinite ∨ B.Infinite := by
  by_contra h
  push_neg at h
  obtain ⟨hA, hB⟩ := h
  exact hInf ((hA.union hB).subset hSub)

/--
  **`higher_energy_incompatibility_on_euclidean_path` — ДОКАЗАНА (4-канальная несовместимость; это
  КОМБИНАТОРНАЯ ОБОЛОЧКА, стену НЕ двигает — нагрузка в недоказанных U2/U4).**
  Бесконечное семейство high-starts + покрытие исходов четырьмя каналами (Close / DescentSeed /
  OldAbsorbed / Unresolved) + запрет Descent (EPMI) + закрытие обеих массовых веток ⟹ `¬Close`
  невозможно (`False`). Чистая комбинаторика: под `¬Close` и `¬DescentSeed` каждый high-start —
  old-absorbed ∨ unresolved, бесконечность даёт бесконечную массовую ветку, та закрывает — против
  `hNoClose`. Соундно и НЕ циркулярно как утверждение; нагрузка — в U2 (`hOutcome`) и U4
  (`hUnresolvedManyCloses`), см. §Э. -/
theorem higher_energy_incompatibility_on_euclidean_path
    (HighStart OldAbsorbed Unresolved DescentSeed : ℕ → Prop) (Close : Prop)
    (hInfStarts : Set.Infinite {m : ℕ | HighStart m})
    (hOutcome : ∀ m, HighStart m → Close ∨ DescentSeed m ∨ OldAbsorbed m ∨ Unresolved m)
    (hNoDescent : ∀ m, DescentSeed m → False)
    (hOldManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ OldAbsorbed m} → Close)
    (hUnresolvedManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ Unresolved m} → Close)
    (hNoClose : ¬ Close) : False := by
  have hCover : {m : ℕ | HighStart m} ⊆
      {m : ℕ | HighStart m ∧ OldAbsorbed m} ∪ {m : ℕ | HighStart m ∧ Unresolved m} := by
    intro m hm
    rcases hOutcome m hm with hC | hD | hO | hU
    · exact absurd hC hNoClose
    · exact absurd (hNoDescent m hD) not_false
    · exact Or.inl ⟨hm, hO⟩
    · exact Or.inr ⟨hm, hU⟩
  rcases infinite_or_infinite_of_subset_union hInfStarts hCover with hOld | hUnr
  · exact hNoClose (hOldManyCloses hOld)
  · exact hNoClose (hUnresolvedManyCloses hUnr)

/-! ### §7. Step00-специализация: `CloseAt` и снятие двух предпосылок -/

/-- `CloseAt A M0 N := Engine A ∨ ∃ t>N, twin`. -/
def CloseAt (Engine : ℕ → Prop) (A N : ℕ) : Prop :=
  Engine A ∨ ∃ t, N < t ∧ IsTwinCenter t

/-- **`noClose_of_noEngine_noNew` — ДОКАЗАНА.** `¬Engine` + «нет twin выше N» ⟹ `¬CloseAt`. -/
theorem noClose_of_noEngine_noNew {Engine : ℕ → Prop} {A N : ℕ}
    (hNoEngine : ¬ Engine A) (hNoNew : ¬ ∃ t, N < t ∧ IsTwinCenter t) :
    ¬ CloseAt Engine A N := by
  rintro (hE | hT)
  · exact hNoEngine hE
  · exact hNoNew hT

/--
  **`higher_energy_incompatibility_step00` — ДОКАЗАНА (специализация §7; оболочка, стену НЕ двигает).**
  Под `¬Engine A` и «нет twin выше N» четыре канала несовместимы ⟹ `False`. Это КОНТРАПОЗИТИВНАЯ
  упаковка: входы U2/U4 остаются недоказанными (U2 = counting = `SNOL.SNOLInput`, U4 циркулярен). Из
  теоремы `twin_prime_conjecture` НЕ следует — вся нагрузка в неинстанциированных входах. -/
theorem higher_energy_incompatibility_step00 {Engine : ℕ → Prop} {A N : ℕ}
    (HighStart OldAbsorbed Unresolved DescentSeed : ℕ → Prop)
    (hInfStarts : Set.Infinite {m : ℕ | HighStart m})
    (hOutcome : ∀ m, HighStart m →
      CloseAt Engine A N ∨ DescentSeed m ∨ OldAbsorbed m ∨ Unresolved m)
    (hNoDescent : ∀ m, DescentSeed m → False)
    (hOldManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ OldAbsorbed m} → CloseAt Engine A N)
    (hUnresolvedManyCloses : Set.Infinite {m : ℕ | HighStart m ∧ Unresolved m} → CloseAt Engine A N)
    (hNoEngine : ¬ Engine A)
    (hNoNew : ¬ ∃ t, N < t ∧ IsTwinCenter t) : False :=
  higher_energy_incompatibility_on_euclidean_path
    HighStart OldAbsorbed Unresolved DescentSeed (CloseAt Engine A N)
    hInfStarts hOutcome hNoDescent hOldManyCloses hUnresolvedManyCloses
    (noClose_of_noEngine_noNew hNoEngine hNoNew)

end EuclidsPath.ManyUnresolved
