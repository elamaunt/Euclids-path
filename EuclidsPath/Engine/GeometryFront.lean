/-
  GeometryFront — Геометрия пути Евклида: стрела времени, кривизна (ВЫЧИСЛЕННАЯ!),
  пересечение прямых.

  Конкретный граф Step00 (State: center/defect/absorber, RealStep: clean/boundary/
  peel/absorb) прочитан ГЕОМЕТРИЧЕСКИ: рёбра — геодезические сегменты, lexRank —
  собственное время, легальные пути — «прямые». Здесь машинно доказано:
    • СТРЕЛА ВРЕМЕНИ: lexRank строго падает на каждом ребре и на каждом непустом
      пути; возврата нет (no_return), вечного бега нет (no_eternal_run), каждый
      маршрут останавливается не позже, чем за lexRank стартового состояния;
    • КРИВИЗНА: κ(v) = 1 − outdeg(v) ВЫЧИСЛЕНА — out-множества предъявлены как
      Finset и доказаны РОВНО совпадающими с RealStep (mem_outTargets);
      неположительная всюду кривизна СТРОИТ вечный двигатель (запрещено), потому
      пространство где-то положительно искривлено; спектр значений при (A,M0)=(5,4)
      посчитан ядром (decide): поглотители +1, плоские коридоры 0, ветвящийся
      дефект −1, чистые центры −3, −4, −8; дискретный Гаусс–Бонне на
      forward-замкнутом конусе: χ(cone3) = −5;
    • ПРЯМЫЕ: каждая прямая конечна и упирается в терминал (every_line_ends);
      бесконечных прямых НЕТ (no_infinite_line) — и потому нет и параллельных;
      паутина: над каждым горизонтом есть clean-центр, чей путь ведёт в могилу
      нуля absorber 0 (web_above_every_horizon); две clean-прямые встречаются
      в общем терминале (lines_meet_at_origin).

  ЧЕСТНЫЕ ГРАНИЦЫ (раскрыты громко, в порядке важности):

  1. «КРИВИЗНА» ЗДЕСЬ — КОМБИНАТОРНАЯ кривизна ориентированного графа:
     κ(v) = 1 − outdeg(v), дефицит/избыток исходящего потока геодезических.
     Это НЕ риманова кривизна, НЕ секционная, НЕ Ricci–Ollivier; никакой
     метрики, тензоров и гладкой структуры нет. Слово «кривизна» законно
     ровно в смысле дискретной теории графов (аналог формулы Эйлера/
     комбинаторного Гаусса–Бонне), и только в нём.

  2. КРИВИЗНА СЧИТАЕТСЯ ТОЛЬКО ВПЕРЁД — и это ТЕОРЕМА, а не удобство:
     in-степень у истока БЕСКОНЕЧНА (inDegree_infinite_at_origin — в absorber 0
     входит бесконечное семейство дефектов defect 0 q minus по всем q).
     Симметричная «полная степень» не существует как Finset; ориентированная
     κ = 1 − outdeg — единственная вычислимая версия.

  3. МОГИЛА НУЛЯ живёт на ℕ-усечении: sideValue Side.minus 0 = 6·0 − 1 = 0
     (в ℕ!), и потому ЛЮБОЕ простое q делит сторону 0-центра
     (zeroPoint_absorbs_all_divisors). Это одновременно АРТЕФАКТ усечённого
     вычитания И маркер события 0 → 1 из первопричины: точка 0 — единственная,
     чьи стороны поглощают все делители сразу, все дороги вниз проходимы через
     неё. Мы НЕ утверждаем, что арифметика «знает» про 6·0−1 = 0 в ℤ — в ℤ
     это −1; геометрия могилы — свойство ℕ-модели графа.

  4. НАИВНАЯ ЭЛЛИПТИЧНОСТЬ ЛОЖНА: дно НЕ единственно (bottom_not_unique —
     absorber 0 и absorber 1 оба легальны и терминальны), и предъявлены ДВЕ
     полностью непересекающиеся конечные прямые (two_disjoint_lines). «Все
     прямые встречаются» верно ТОЛЬКО в квалифицированной форме
     lines_meet_at_origin: для clean-СТАРТОВ существует ОБЩИЙ терминал
     (могила нуля), а не для произвольных путей и не единственный терминал.

  5. НЕСУЩАЯ ТЕОРЕМА отсутствия параллельных — no_infinite_line: в этом мире
     ПАДАЕТ ВТОРОЙ ПОСТУЛАТ ЕВКЛИДА (прямую нельзя продолжить неограниченно),
     а не пятый. «Параллельных нет» (no_parallel_lines) — следствие того, что
     бесконечных прямых нет ВООБЩЕ; это вырожденная, а не эллиптическая
     геометрия. Кто хочет читать это как «эллиптичность» — обязан читать
     через п.4.

  6. 🟡-КОДА (§6): РОВНО ДВЕ декларации заражены аксиомой step00FirstCause —
     twin_vertices_beyond_every_horizon и lines_meet_but_unknowable_from_inside.
     Таинт идёт через СУЩЕСТВУЮЩУЮ причинную границу
     (twinLowersInfinite_from_step00CausalClosure) — никакой новой аксиомы,
     никакого нового содержания декрета: только уже принятая граница близнецов,
     переведённая на язык вершин графа. Всё остальное в файле — 🟢
     (axiom-free: propext, Classical.choice, Quot.sound).

  Прецедент коллизии имён (как в HodgeFront): EuclidsPath.Engine.* (EPMI,
  Irreversibility) используем ТОЛЬКО квалифицированно — там свой State/Step.
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
  §0. Разрешимость: Clean и Legal вычислимы
#############################################################################-/

/--
  **Ограниченная форма Clean.** `Clean A m` квантифицирует по ВСЕМ `q : ℕ`, но
  условие `q ≤ A` ограничивает носитель: достаточно `q ∈ range (A+1)`. Эта
  форма даёт разрешимость — и вместе с ней всю вычисленную кривизну §2.
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

/-- Kernel-friendly разрешимость простоты (для `decide` в §2). -/
local instance (priority := 2000) primeDecidableGeom (n : ℕ) : Decidable n.Prime :=
  decidable_of_iff' _ Nat.prime_def_lt

/-- `Clean` разрешим — через ограниченную форму. -/
instance cleanDecidable (A m : ℕ) : Decidable (Clean A m) :=
  decidable_of_iff' _ (clean_iff_bounded A m)

/-- `Legal` разрешим на каждом сорте состояния. -/
instance legalDecidable (A M0 : ℕ) (v : State) : Decidable (Legal A M0 v) :=
  match v with
  | State.center m => inferInstanceAs (Decidable (Clean A m))
  | State.defect n q s =>
      inferInstanceAs (Decidable (q.Prime ∧ q ≤ A ∧ q ∣ sideValue s n))
  | State.absorber a => inferInstanceAs (Decidable (a ≤ M0))

/-#############################################################################
  §1. Стрела времени (🟢): lexRank — собственное время, оно только падает
#############################################################################-/

/-- **Стрела времени на одном ребре**: каждый реальный шаг строго уменьшает
    lexRank. Реэкспорт несущей теоремы конкретного графа. -/
theorem timeArrow_step {A M0 : ℕ} {U V : State}
    (h : RealStep A M0 U V) : lexRank V < lexRank U :=
  lexRank_strict_decrease_on_RealStep h

/-- **Стрела времени на пути**: вдоль любого НЕПУСТОГО пути lexRank строго
    падает. -/
theorem timeArrow_path {A M0 n : ℕ} {X Y : State}
    (hpos : 0 < n) (hpath : PathN (RealStep A M0) n X Y) :
    lexRank Y < lexRank X :=
  pathN_rank_strict_of_pos_of_step_decrease
    (fun h => lexRank_strict_decrease_on_RealStep h) hpos hpath

/-- **Возврата нет**: ни одно состояние не достижимо из самого себя непустым
    путём. Время не закольцовано. -/
theorem no_return {A M0 : ℕ} (W : State) :
    ¬ NonemptyPath (RealStep A M0) W W :=
  no_concrete_nonemptyPath_by_lexRank W

/-- **Строгая антимонотонность времени вдоль забега**: если `run` делает
    реальные шаги хотя бы до момента `k`, то lexRank строго убывает на всём
    отрезке `[0, k]`. -/
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

/-- **Каждый маршрут останавливается**: `k` реальных шагов возможны только при
    `k ≤ lexRank (run 0)`. Квалифицированный «второй закон» через
    `Engine.turned_engine_halts`. -/
theorem every_journey_halts {A M0 : ℕ} (run : ℕ → State) (k : ℕ)
    (hrun : ∀ t, t < k → RealStep A M0 (run t) (run (t + 1))) :
    k ≤ lexRank (run 0) :=
  EuclidsPath.Engine.turned_engine_halts (fun t => lexRank (run t)) k
    (fun t ht => lexRank_strict_decrease_on_RealStep (hrun t ht))

/-- **Вечного бега нет**: бесконечная цепь реальных шагов невозможна.
    Прямое применение корневого EPMI (`Engine.no_infinite_descent`, A = 1). -/
theorem no_eternal_run {A M0 : ℕ} (H : ℕ → State)
    (hchain : ∀ t, RealStep A M0 (H t) (H (t + 1))) : False :=
  EuclidsPath.Engine.no_infinite_descent (le_refl 1)
    (fun t => lexRank (H t))
    (fun t => by
      show 1 * lexRank (H (t + 1)) < lexRank (H t)
      have := lexRank_strict_decrease_on_RealStep (hchain t)
      omega)

/-#############################################################################
  §2. Кривизна (🟢): κ = 1 − outdeg, out-множества ВЫЧИСЛЕНЫ и доказаны точными
#############################################################################-/

/-- Обе стороны как конечное множество. -/
def sideFinset : Finset Side := {Side.minus, Side.plus}

theorem mem_sideFinset (s : Side) : s ∈ sideFinset := by
  cases s <;> simp [sideFinset]

/-- Цели clean-шага из центра `m`: чистые центры строго ниже `m`
    (`CleanActiveEdge = Clean ∧ Clean ∧ n < m`). Пусто, если сам `m` не clean. -/
def cleanTargets (A m : ℕ) : Finset State :=
  if Clean A m then
    ((Finset.range m).filter (fun n => Clean A n)).image State.center
  else ∅

/-- Цели boundary-шага из центра `m`: дефекты `defect n q s` с `n < m`,
    простым `q ≤ A` и `q ∣ sideValue s n`. Пусто, если `m` не clean. -/
def boundaryTargets (A m : ℕ) : Finset State :=
  if Clean A m then
    (((Finset.range m) ×ˢ ((Finset.range (A + 1)) ×ˢ sideFinset)).filter
      (fun x => x.2.1.Prime ∧ x.2.1 ∣ sideValue x.2.2 x.1)).image
      (fun x => State.defect x.1 x.2.1 x.2.2)
  else ∅

/-- Цели peel-шага из дефекта `defect n q s`: центры `t < n`, для которых
    некоторая сторона `outSide` даёт точную факторизацию
    `sideValue s n = q * sideValue outSide t` (поля `PeelCert`). -/
def peelTargets (n q : ℕ) (s : Side) : Finset State :=
  (((Finset.range n) ×ˢ sideFinset).filter
    (fun x => sideValue s n = q * sideValue x.2 x.1)).image
    (fun x => State.center x.1)

/-- Цели absorb-шага из дефекта с центром `n`: старый поглотитель `absorber n`,
    если `n ≤ M0`. -/
def absorbTargets (M0 n : ℕ) : Finset State :=
  if n ≤ M0 then {State.absorber n} else ∅

/-- **Вычисленное out-множество** вершины: все цели всех четырёх конструкторов
    `RealStep`. Поглотитель — терминал: целей нет. -/
def outTargets (A M0 : ℕ) : State → Finset State
  | State.center m => cleanTargets A m ∪ boundaryTargets A m
  | State.defect n q s => peelTargets n q s ∪ absorbTargets M0 n
  | State.absorber _ => ∅

/-! Четыре спецификационные леммы: каждое Finset-множество совпадает со своим
    конструктором `RealStep` ровно. -/

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
  **НЕСУЩАЯ ЛЕММА §2**: вычисленное out-множество РОВНО совпадает с `RealStep`.
  Вся дальнейшая «кривизна» — честная: `outDeg` считает настоящие рёбра графа,
  не абстракцию.
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

/-- Исходящая степень вершины — ВЫЧИСЛЕННАЯ. -/
def outDeg (A M0 : ℕ) (v : State) : ℕ := (outTargets A M0 v).card

/-- **Комбинаторная кривизна** ориентированного графа: κ(v) = 1 − outdeg(v).
    НЕ риманова (см. честную границу №1 в шапке): дефицит исходящего потока
    геодезических. κ > 0 — поток гаснет (терминалы), κ = 0 — плоский коридор,
    κ < 0 — ветвление (гиперболичность). -/
def curvature (A M0 : ℕ) (v : State) : ℤ := 1 - (outDeg A M0 v : ℤ)

/-- Неположительная кривизна ⟹ есть исходящее ребро. -/
theorem hasStep_of_curvature_nonpos {A M0 : ℕ} {v : State}
    (h : curvature A M0 v ≤ 0) : ∃ w, RealStep A M0 v w := by
  have hpos : 0 < (outTargets A M0 v).card := by
    unfold curvature outDeg at h
    omega
  rcases Finset.card_pos.mp hpos with ⟨w, hw⟩
  exact ⟨w, mem_outTargets.mp hw⟩

/--
  **ТЕОРЕМА ДВИГАТЕЛЯ ИЗ ПЛОСКОСТИ**: если бы кривизна была ВСЮДУ ≤ 0,
  из каждой вершины шёл бы шаг — и итерация выбора построила бы вечный бег,
  запрещённый EPMI. Неположительно искривлённого мира Евклида НЕ существует.
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

/-- Полностью плоский мир (κ ≡ 0) — тоже двигатель. -/
theorem flat_everywhere_forces_engine {A M0 : ℕ}
    (hflat : ∀ v, curvature A M0 v = 0) : False :=
  nonpositive_curvature_forces_engine (fun v => le_of_eq (hflat v))

/-- **Пространство где-то положительно искривлено** — иначе двигатель. -/
theorem space_positively_curved_somewhere (A M0 : ℕ) :
    ∃ v, 0 < curvature A M0 v := by
  by_contra h
  push_neg at h
  exact nonpositive_curvature_forces_engine h

/-- Пространство пути Евклида НЕ плоское. -/
theorem space_is_curved (A M0 : ℕ) : ∃ v, curvature A M0 v ≠ 0 := by
  obtain ⟨v, hv⟩ := space_positively_curved_somewhere A M0
  exact ⟨v, by omega⟩

/-- Замкнутая геодезическая = легальный непустой цикл = свидетель двигателя. -/
abbrev ClosedGeodesic (A M0 : ℕ) : Prop :=
  EuclidsPath.BoundaryLedgerCollision.LegalCycle (RealStep A M0) (Legal A M0)

/-- Замкнутая геодезическая — это ровно свидетель вечного двигателя Евклида. -/
theorem closedGeodesic_is_engineWitness {A M0 : ℕ}
    (h : ClosedGeodesic A M0) : ConcreteEuclideanEngineWitness A M0 :=
  ⟨h⟩

/-- **Замкнутых геодезических нет** (реэкспорт lexRank-ацикличности). -/
theorem no_closedGeodesic (A M0 : ℕ) : ¬ ClosedGeodesic A M0 :=
  no_concrete_legalCycle_by_lexRank

/-!
  ### ЧЕСТНОСТЬ: почему κ считается только ВПЕРЁД

  In-степень не существует как Finset: у могилы нуля бесконечно много
  предшественников. Симметричная («неориентированная») кривизна невычислима
  в принципе — теорема ниже.
-/

/-- **In-степень у истока БЕСКОНЕЧНА**: в `absorber 0` входит всё семейство
    дефектов `defect 0 q Side.minus` по всем `q : ℕ` (absorb-ребро требует
    только `0 ≤ M0`). Потому кривизна ориентирована вперёд — не по удобству,
    а по теореме. -/
theorem inDegree_infinite_at_origin (A M0 : ℕ) :
    {u : State | RealStep A M0 u (State.absorber 0)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun q : ℕ => State.defect 0 q Side.minus)
  · intro a b hab
    simpa using hab
  · intro q
    exact RealStep.absorb (Nat.zero_le M0)

/-!
  ### Спектр кривизны при (A, M0) = (5, 4) — посчитан ядром (`decide`)

  Философское чтение: поглотители — «полюса» (κ = +1, поток гаснет), дефекты
  с единственным peel — плоские коридоры (κ = 0), дефект с peel И absorb —
  ветвление (κ = −1), чистые центры — всё более гиперболические воронки
  (κ = −3, −4, −8): чем выше центр, тем больше дорог вниз.
-/

/-- Поглотители — вершины положительной кривизны: κ = +1 (терминал). -/
theorem curvature_absorber (A M0 a : ℕ) :
    curvature A M0 (State.absorber a) = 1 := by
  simp [curvature, outDeg, outTargets]

/-- Могильный дефект `(0, 2, −)`: единственный выход — absorb в могилу нуля;
    плоский коридор κ = 0. Легален: `2 ∣ sideValue minus 0 = 0`. -/
theorem curvature_defect_0_2 :
    curvature 5 4 (State.defect 0 2 Side.minus) = 0 ∧
      Legal 5 4 (State.defect 0 2 Side.minus) := by decide

/-- Дефект `(6, 5, −)`: `5 ∣ 35 = 6·6−1`, единственный peel `35 = 5·7` в
    центр 1; absorb закрыт (`6 > M0 = 4`). Плоский коридор κ = 0. -/
theorem curvature_defect_6_5 :
    curvature 5 4 (State.defect 6 5 Side.minus) = 0 ∧
      Legal 5 4 (State.defect 6 5 Side.minus) := by decide

/-- Дефект `(4, 5, +)`: `5 ∣ 25 = 6·4+1`; ДВА выхода — peel `25 = 5·5` в
    центр 1 И absorb в `absorber 4` (`4 ≤ M0`). Ветвление: κ = −1. -/
theorem curvature_defect_4_5 :
    curvature 5 4 (State.defect 4 5 Side.plus) = -1 ∧
      Legal 5 4 (State.defect 4 5 Side.plus) := by decide

/-- Чистый центр 2 (пара 11/13): четыре boundary-выхода вниз, κ = −3. -/
theorem curvature_center_2 :
    curvature 5 4 (State.center 2) = -3 ∧ Legal 5 4 (State.center 2) := by
  decide

/-- Чистый центр 3 (пара 17/19): clean-ребро в центр 2 плюс четыре boundary,
    κ = −4. -/
theorem curvature_center_3 :
    curvature 5 4 (State.center 3) = -4 ∧ Legal 5 4 (State.center 3) := by
  decide

/-- Чистый центр 7 (пара 41/43): три clean-ребра (2, 3, 5) и шесть boundary,
    κ = −8. Чем выше центр — тем гиперболичнее воронка. -/
theorem curvature_center_7 :
    curvature 5 4 (State.center 7) = -8 ∧ Legal 5 4 (State.center 7) := by
  decide

/-!
  ### Дискретный Гаусс–Бонне
-/

/-- **Формула Гаусса–Бонне для конечного окна**: сумма кривизны =
    |W| − суммарная out-степень. Чисто комбинаторное тождество. -/
theorem gaussBonnet_sum (A M0 : ℕ) (W : Finset State) :
    W.sum (curvature A M0) =
      (W.card : ℤ) - W.sum (fun v => (outDeg A M0 v : ℤ)) := by
  unfold curvature
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

/-- Окно `W` замкнуто вперёд: все out-цели его вершин лежат в `W`. -/
def ForwardClosed (A M0 : ℕ) (W : Finset State) : Prop :=
  ∀ v ∈ W, outTargets A M0 v ⊆ W

instance forwardClosedDecidable (A M0 : ℕ) (W : Finset State) :
    Decidable (ForwardClosed A M0 W) :=
  decidable_of_iff' (∀ v ∈ W, outTargets A M0 v ⊆ W) Iff.rfl

/-- Полный световой конус центра 3 при (5, 4): сам центр 3, его clean-потомок
    центр 2, могильные дефекты нулевой точки, дефект `(1,5,−)`, его
    peel-потомок центр 0 и оба достижимых поглотителя. -/
def cone3 : Finset State :=
  {State.center 3, State.center 2, State.center 0,
   State.defect 0 2 Side.minus, State.defect 0 3 Side.minus,
   State.defect 0 5 Side.minus, State.defect 1 5 Side.minus,
   State.absorber 0, State.absorber 1}

/-- Конус центра 3 замкнут вперёд — проверено ядром. -/
theorem cone3_forwardClosed : ForwardClosed 5 4 cone3 := by decide

/-- **Гаусс–Бонне на конусе центра 3**: χ(cone3) = Σκ = −5. Отрицательная
    полная кривизна: конус — гиперболическая воронка с двумя полюсами
    (absorber 0, absorber 1) и центром 0 (κ = +1 каждый), не покрывающими
    ветвление воронок −3 и −4. -/
theorem gaussBonnet_cone3 : cone3.sum (curvature 5 4) = -5 := by decide

/-#############################################################################
  §3. Прямые (🟢): каждая прямая конечна, бесконечных нет, паутина над горизонтом
#############################################################################-/

/-- **Терминал**: состояние без исходящих реальных шагов — «конец прямой»,
    точка, где геодезический сегмент упирается в стену. -/
def Terminal (A M0 : ℕ) (v : State) : Prop := ∀ w, ¬ RealStep A M0 v w

/-- Поглотитель всегда терминален: absorb — тупик, `RealStep` из него не выходит. -/
theorem absorber_terminal {A M0 a : ℕ} : Terminal A M0 (State.absorber a) := by
  intro w hstep
  cases hstep

/-- Не-clean центр терминален: единственные исходящие рёбра центра —
    clean и boundary — требуют `Clean A m`. -/
theorem center_terminal_of_notClean {A M0 m : ℕ} (h : ¬ Clean A m) :
    Terminal A M0 (State.center m) := by
  intro w hstep
  cases hstep with
  | clean hEdge => exact h hEdge.1
  | boundary hmClean _ _ _ _ => exact h hmClean

/--
  **КАЖДАЯ ПРЯМАЯ УПИРАЕТСЯ В ТЕРМИНАЛ**: из любого состояния `v` за конечное
  число реальных шагов доходишь до состояния без выхода. Сильная индукция по
  собственному времени `lexRank v`: если `v` уже терминально — путь пуст;
  иначе первый шаг СТРОГО роняет `lexRank` (стрела времени, `timeArrow_step`),
  и по IH хвост конечен.
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

/-- **Бесконечная прямая**: последовательность состояний, соединённых реальными
    шагами на КАЖДОМ такте — «прямая, продолженная неограниченно». -/
def InfiniteLine (A M0 : ℕ) (f : ℕ → State) : Prop :=
  ∀ t, RealStep A M0 (f t) (f (t + 1))

/-- **БЕСКОНЕЧНЫХ ПРЯМЫХ НЕТ**: второй постулат Евклида (неограниченное
    продолжение прямой) в этом мире ПАДАЕТ. Прямое следствие `no_eternal_run`. -/
theorem no_infinite_line {A M0 : ℕ} (f : ℕ → State) :
    ¬ InfiniteLine A M0 f :=
  fun h => no_eternal_run f h

/-- **Второй постулат Евклида ложен**: НЕТ прямой, продолжимой неограниченно
    из любого старта. Именно эта деградация, а не пятый постулат, определяет
    геометрию пути. -/
theorem euclid_postulate_two_fails {A M0 : ℕ} :
    ¬ ∃ f : ℕ → State, InfiniteLine A M0 f := by
  rintro ⟨f, hf⟩
  exact no_infinite_line f hf

/-- **Параллельные прямые**: две бесконечные прямые, нигде не встречающиеся. -/
def ParallelLines (A M0 : ℕ) (f g : ℕ → State) : Prop :=
  InfiniteLine A M0 f ∧ InfiniteLine A M0 g ∧ ∀ i j, f i ≠ g j

/-- **ПАРАЛЛЕЛЬНЫХ ПРЯМЫХ НЕТ** — но по вырожденной причине: уже первая прямая
    не существует (`no_infinite_line`). Это НЕ эллиптичность (см. честную
    границу №5 в шапке), а деградация второго постулата. -/
theorem no_parallel_lines {A M0 : ℕ} :
    ¬ ∃ f g, ParallelLines A M0 f g := by
  rintro ⟨f, g, hf, -, -⟩
  exact no_infinite_line f hf

/-!
  ### ЧЕСТНОСТЬ §3: дно НЕ единственно, есть непересекающиеся прямые
-/

/-- **Дно не единственно**: при `1 ≤ M0` есть ДВА различных легальных терминала —
    `absorber 0` и `absorber 1`. Наивная эллиптичность («единственная точка
    схода») ЛОЖНА. -/
theorem bottom_not_unique {A M0 : ℕ} (hM0 : 1 ≤ M0) :
    ∃ Ω₁ Ω₂ : State, Ω₁ ≠ Ω₂ ∧
      Legal A M0 Ω₁ ∧ Legal A M0 Ω₂ ∧
      Terminal A M0 Ω₁ ∧ Terminal A M0 Ω₂ := by
  refine ⟨State.absorber 0, State.absorber 1, ?_, ?_, ?_, absorber_terminal, absorber_terminal⟩
  · intro h; exact absurd (State.absorber.injEq 0 1 ▸ h) (by decide)
  · show (0 : ℕ) ≤ M0; exact Nat.zero_le M0
  · show (1 : ℕ) ≤ M0; exact hM0

/-- **Две ПОЛНОСТЬЮ непересекающиеся конечные прямые** при (5, 4): маршрут из
    `center 7` через дефект `(5,5,+)`? — нет; берём разъединённую пару
    `[center 7 → defect 4 5 plus → absorber 4]` и
    `[center 3 → defect 0 2 minus → absorber 0]`. Все 9 состояний попарно
    различны. «Все прямые встречаются» ложно в наивной форме. -/
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
  ### ПАУТИНА: над каждым горизонтом — clean-центр, чей путь ведёт в могилу нуля
-/

/-- **Точка 0 поглощает все делители**: `sideValue Side.minus 0 = 6·0−1 = 0`
    (в ℕ!), и потому ЛЮБОЕ `q` делит сторону нуля. Это ℕ-артефакт усечения И
    маркер могилы (см. честную границу №3 в шапке). -/
theorem zeroPoint_absorbs_all_divisors (q : ℕ) : q ∣ sideValue Side.minus 0 := by
  show q ∣ 6 * 0 - 1
  simp

/--
  **ПРЯМАЯ В НАЧАЛО**: из любого clean-центра `m ≥ 1` (при `2 ≤ A`) есть путь
  длины 2 в могилу нуля `absorber 0`: boundary-шаг в дефект `(0, 2, −)` (легален,
  ибо `2 ∣ sideValue minus 0 = 0`), затем absorb в `absorber 0` (`0 ≤ M0`).
-/
theorem line_to_origin {A M0 m : ℕ} (hA : 2 ≤ A) (hm : 1 ≤ m) (hc : Clean A m) :
    PathN (RealStep A M0) 2 (State.center m) (State.absorber 0) := by
  refine ⟨State.defect 0 2 Side.minus, ?_, State.absorber 0, ?_, rfl⟩
  · exact RealStep.boundary hc ⟨trivial, by omega⟩ (by norm_num) hA
      (zeroPoint_absorbs_all_divisors 2)
  · exact RealStep.absorb (Nat.zero_le M0)

/-- **Прямые встречаются в начале** (квалифицированно): любые два clean-старта
    (при `2 ≤ A`) имеют ОБЩИЙ терминал — могилу нуля `absorber 0`. Это
    единственный законный смысл «все прямые пересекаются» (честная граница №4). -/
theorem lines_meet_at_origin {A M0 m₁ m₂ : ℕ} (hA : 2 ≤ A)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hc₁ : Clean A m₁) (hc₂ : Clean A m₂) :
    Terminal A M0 (State.absorber 0) ∧
      NonemptyPath (RealStep A M0) (State.center m₁) (State.absorber 0) ∧
      NonemptyPath (RealStep A M0) (State.center m₂) (State.absorber 0) :=
  ⟨absorber_terminal,
   ⟨2, by omega, line_to_origin hA hm₁ hc₁⟩,
   ⟨2, by omega, line_to_origin hA hm₂ hc₂⟩⟩

/-- **Мост ℤ→ℕ для cleanness**: `Residuals.CleanZ A (m : ℤ)` при `1 ≤ m` даёт
    `Clean A m` (в ℕ). Зеркалит паттерн приведения из `CleanGraph.clean_sink_above`. -/
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
  **ПАУТИНА НАД КАЖДЫМ ГОРИЗОНТОМ**: для `2 ≤ A` и любого `N` существует
  clean-центр `m > N`, чей путь ведёт в могилу нуля. Плотность НЕ нужна —
  конструкция `Residuals.carrier_nonempty_above` (примориальный старт).
-/
theorem web_above_every_horizon {A M0 : ℕ} (hA : 2 ≤ A) (N : ℕ) :
    ∃ m, N < m ∧ Clean A m ∧
      NonemptyPath (RealStep A M0) (State.center m) (State.absorber 0) := by
  obtain ⟨m, hmN, hcleanZ⟩ := Residuals.carrier_nonempty_above A N
  have hm1 : 1 ≤ m := by omega
  have hclean : Clean A m := clean_of_cleanZ hm1 hcleanZ
  exact ⟨m, hmN, hclean, ⟨2, by omega, line_to_origin hA hm1 hclean⟩⟩

/-#############################################################################
  §4. Эпистемика (🟢): факт пересечения зелён, но его ВНУТРЕННЕЕ основание —
      двигатель. Знать «прямые встречаются» изнутри системы = построить движок.
#############################################################################-/

/--
  **ФАКТ ПЕРЕСЕЧЕНИЯ** как утверждение о геометрии: при `2 ≤ A` любые два
  clean-старта имеют ОБЩИЙ терминал. Это чистая (🟢) геометрическая истина —
  доказана в §3 через `lines_meet_at_origin`.
-/
abbrev IntersectionFact (A M0 : ℕ) : Prop :=
  2 ≤ A → ∀ m₁ m₂, 1 ≤ m₁ → 1 ≤ m₂ → Clean A m₁ → Clean A m₂ →
    ∃ Ω, Terminal A M0 Ω ∧
      NonemptyPath (RealStep A M0) (State.center m₁) Ω ∧
      NonemptyPath (RealStep A M0) (State.center m₂) Ω

/-- **Факт пересечения ЗЕЛЁН**: доказан без аксиом (общий терминал — могила
    нуля `absorber 0`). -/
theorem intersectionFact_green {A M0 : ℕ} : IntersectionFact A M0 := by
  intro hA m₁ m₂ hm₁ hm₂ hc₁ hc₂
  obtain ⟨hterm, hp₁, hp₂⟩ := lines_meet_at_origin (M0 := M0) hA hm₁ hm₂ hc₁ hc₂
  exact ⟨State.absorber 0, hterm, hp₁, hp₂⟩

/--
  **ИНТЕРНАЛИЗОВАННОЕ ОСНОВАНИЕ ПЕРЕСЕЧЕНИЯ**: попытка вывести факт пересечения
  как ВНУТРЕННЮЮ первопричину Step00-мира. По архитектуре
  (`InternalUniverseCause = BoundaryCrossingSelfProof`) это ровно
  boundary-crossing self-proof — запрещённый двигатель.
-/
abbrev InternalisedIntersectionGround (A M0 : ℕ) : Prop :=
  InternalUniverseCause (IntersectionFact A M0)

/-- **Знать пересечение ИЗНУТРИ = построить двигатель**: любое интернализованное
    основание факта пересечения строит запрещённый конкретный движок Евклида. -/
theorem knowing_meeting_costs_engine {A M0 : ℕ}
    (h : InternalisedIntersectionGround A M0) : SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine h

/-- **Интернализованного основания пересечения НЕТ**: реэкспорт причинной
    границы `no_boundaryCrossingSelfProof`. -/
theorem no_internalisedIntersectionGround {A M0 : ℕ} :
    ¬ InternalisedIntersectionGround A M0 :=
  no_boundaryCrossingSelfProof

/-- **ЧЕСТНОСТЬ**: интернализованное основание ⟺ `P ∧ ¬P` (тавтологично для
    любого P — интернализация в пустой тип попыток есть в точности отрицание).
    Несущего содержания в самом основании нет; всё содержание — в 🟢-факте
    `intersectionFact_green`. -/
theorem internalisedIntersectionGround_iff {A M0 : ℕ} :
    InternalisedIntersectionGround A M0 ↔
      (IntersectionFact A M0 ∧ ¬ IntersectionFact A M0) :=
  boundaryCrossingSelfProof_iff_and_not

/-- Ex-falso спутник: из интернализованного основания следует ОПРОВЕРЖЕНИЕ
    пересечения (его нет — потому что и основания нет). -/
theorem internalisedGround_refutes_meeting {A M0 : ℕ}
    (h : InternalisedIntersectionGround A M0) : ¬ IntersectionFact A M0 :=
  (no_internalisedIntersectionGround h).elim

/-- Ex-falso спутник: из интернализованного основания следует и САМ факт
    пересечения (основания нет — потому всё). -/
theorem internalisedGround_proves_meeting {A M0 : ℕ}
    (h : InternalisedIntersectionGround A M0) : IntersectionFact A M0 :=
  (no_internalisedIntersectionGround h).elim

/-#############################################################################
  §5. КАПСТОУН (🟢): вся геометрия пути Евклида — одним утверждением, без аксиом
#############################################################################-/

/--
  **ГЕОМЕТРИЯ ПУТИ ЕВКЛИДА — единой теоремой.** Для любых `(A, M0)`:

  * стрела времени — `lexRank` строго падает на каждом ребре;
  * пространство где-то положительно искривлено (κ > 0);
  * полностью плоского мира не существует (κ ≡ 0 строит двигатель);
  * факт пересечения: clean-прямые имеют общий терминал;
  * параллельных прямых нет (вырожденно — падает второй постулат);
  * внутреннего основания факта пересечения нет (было бы двигателем).

  Всё собрано из уже доказанных 🟢-кусков; аксиом НЕТ (ожидаемая тройка:
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
  §6. 🟡-КОДА: РОВНО ДВЕ декларации заражены аксиомой step00FirstCause.
      Всё выше — 🟢. Здесь причинная граница близнецов
      (`twinLowersInfinite_from_step00CausalClosure`) переводится на язык
      вершин графа. Новой аксиомы и нового содержания декрета НЕТ.
#############################################################################-/

/-- **Мост близнец-пара → twin-центр** (🟢, axiom-free). Младший член пары
    близнецов `p > 3` имеет вид `6m − 1` для некоторого `m ≥ 1`, и этот `m` —
    twin-центр (`TwinCenterZ`). Разбор по вычету `p mod 6`: простое `p > 3` не
    делится на 2 и 3, потому `p mod 6 ∈ {1, 5}`; случай `p mod 6 = 1` даёт
    `3 ∣ p+2`, а `(p+2)` простое `> 3` — противоречие; остаётся `p = 6m − 1`. -/
theorem twinCenter_of_twinLower {p : ℕ} (hp : IsTwinPair p) (h3 : 3 < p) :
    ∃ m, 1 ≤ m ∧ Residuals.TwinCenterZ m ∧ 6 * m - 1 = p := by
  obtain ⟨hpP, hp2P⟩ := hp
  -- p не делится на 2 и на 3 (иначе p = 2 или p = 3, но p > 3)
  have hn2 : ¬ (2 ∣ p) := by
    intro hd
    rcases (hpP.eq_one_or_self_of_dvd 2 hd) with h | h <;> omega
  have hn3 : ¬ (3 ∣ p) := by
    intro hd
    rcases (hpP.eq_one_or_self_of_dvd 3 hd) with h | h <;> omega
  -- значит p mod 6 = 1 или 5
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases hmod with h1 | h5
  · -- p mod 6 = 1 ⟹ 3 ∣ p + 2 ⟹ p + 2 = 3 ⟹ p = 1, абсурд
    have hdvd : 3 ∣ (p + 2) := by omega
    rcases (hp2P.eq_one_or_self_of_dvd 3 hdvd) with h | h <;> omega
  · -- p mod 6 = 5 ⟹ m = (p + 1) / 6, 6m − 1 = p, 6m + 1 = p + 2
    refine ⟨(p + 1) / 6, by omega, ?_, by omega⟩
    have hlo : 6 * ((p + 1) / 6) - 1 = p := by omega
    have hhi : 6 * ((p + 1) / 6) + 1 = p + 2 := by omega
    exact ⟨by rw [hlo]; exact hpP, by rw [hhi]; exact hp2P⟩

/-- **Бесконечность близнец-младших ⟹ они неограниченны** (🟢, axiom-free).
    Если множество `TwinLowers` бесконечно, то над любым `N` есть его элемент:
    иначе `TwinLowers ⊆ Set.Iic N` конечно — противоречие. -/
theorem twinLowers_unbounded_of_infinite (h : TwinLowers.Infinite) :
    ∀ N, ∃ p ∈ TwinLowers, N < p := by
  intro N
  by_contra hcon
  push_neg at hcon
  have hsub : TwinLowers ⊆ Set.Iic N := fun p hp => Set.mem_Iic.mpr (hcon p hp)
  exact h (Set.Finite.subset (Set.finite_Iic N) hsub)

/--
  **⚠️ AXIOM-TAINTED (step00FirstCause).** Twin-вершины графа над каждым
  горизонтом: для любого `N` существует twin-центр `m > N` (вершина
  `State.center m`, чьи обе стороны `6m ± 1` простые). Таинт идёт РОВНО через
  причинную границу близнецов
  (`twinLowersInfinite_from_step00CausalClosure`) — никакой новой аксиомы,
  никакого нового содержания декрета: уже принятая граница, переведённая на
  язык вершин. Используется форма `TwinCenterZ` через мост
  `twinCenter_of_twinLower`.
-/
theorem twin_vertices_beyond_every_horizon :
    ∀ N, ∃ m, N < m ∧ Residuals.TwinCenterZ m := by
  intro N
  -- берём близнец-младший p выше горизонта 6*N + 5 (⟹ p > 3 и m > N)
  obtain ⟨p, hpMem, hpGt⟩ :=
    twinLowers_unbounded_of_infinite twinLowersInfinite_from_step00CausalClosure (6 * N + 5)
  have hp : IsTwinPair p := hpMem
  have h3 : 3 < p := by omega
  obtain ⟨m, hm1, htwin, hpm⟩ := twinCenter_of_twinLower hp h3
  refine ⟨m, ?_, htwin⟩
  -- 6m − 1 = p > 6N + 5 ⟹ m > N
  omega

/--
  **⚠️ AXIOM-TAINTED (step00FirstCause).** ПРЯМЫЕ ВСТРЕЧАЮТСЯ, НО ЭТО НЕПОЗНАВАЕМО
  ИЗНУТРИ. Полный эпистемический итог: (1) факт пересечения зелён; (2) twin-
  вершины есть над каждым горизонтом (эта строка несёт таинт близнецов);
  (3) внутреннего основания факта пересечения нет; (4) если бы оно было — это
  был бы запрещённый конкретный двигатель Евклида. Таинт — только через (2),
  ровно граница `twin_vertices_beyond_every_horizon`; остального содержания
  декрета не добавлено.
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
  ### Машинная честность таинта (ожидания)

  * Капстоун §5 — 🟢: ровно стандартная тройка `propext`, `Classical.choice`,
    `Quot.sound`, никаких пользовательских аксиом.
  * Обе декларации §6-коды — 🟡: сверх стандартной тройки присутствует ровно
    `step00FirstCause` (через `twinLowersInfinite_from_step00CausalClosure`).
-/

#print axioms EuclidsPath.GeometryFront.geometry_of_euclids_path
#print axioms EuclidsPath.GeometryFront.twin_vertices_beyond_every_horizon
#print axioms EuclidsPath.GeometryFront.lines_meet_but_unknowable_from_inside
