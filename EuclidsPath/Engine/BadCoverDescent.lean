/-
  Bad-cover finite descent — попытка ОБОЙТИ counting/parity-стену `bad.card < carrier.card`.
  Источник: step00_post_audit_snolinput_badcover_descent_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Bad-cover descent»).

  ИДЕЯ (и почему она НЕ сработала как обход). Вместо density-условия `bad.card < carrier.card`
  (sieve/parity-wall) — динамика: если carrier конечен и непуст, а каждый bad порождает строго
  меньший по энергии bad-преемник (или сразу закрывает), то bad-cover невозможен (energy-минимум).
  НАДЕЖДА была: good-элемент без подсчёта. РЕЗУЛЬТАТ АУДИТА: обхода НЕТ — energy-спуск в конечном
  carrier обязан терминировать на good/twin, поэтому вход `bad_internal_descent` в energy-минимуме
  carrier ЭКВИВАЛЕНТЕН существованию twin выше N. Стена перенесена в минимум, не снята.

  ЧЕСТНЫЙ СТАТУС. Доказан СТРУКТУРНЫЙ костяк (абстрактно, стандартные аксиомы, без sorry) — он реален
  и переиспользуем:
    * `bad_cover_absurd` — конечный energy-минимум ⟹ bad-cover невозможен (ядро, настоящая
      комбинаторика Finset/well-founded);
    * `bad_cover_closes`, `good_or_close`, `arbitrarily_large_twins_of_descent`,
      `twin_prime_conjecture_of_descent` — сборка ⟹ `TwinLowers.Infinite` (через `infinite_of_unbounded_centers`).

  НО РЕДУКЦИЯ ЦИРКУЛЯРНА (машинно доказано в §circularity): `descent_reduction_is_circular` +
  `twin_prime_conjecture_of_descent` дают `SNOLDescentInput ⟺ goal` — ТОТ ЖЕ статус, что
  `ConcreteComponents.SmallCleanSupply` (⟺ цели). Вход R3 (`bad_internal_descent`) в energy-минимуме
  carrier — это цель в динамических координатах, а НЕ более лёгкая задача. Мой первоначальный довод о
  «не-циркулярности» был ОШИБОЧЕН (игнорировал минимум); аудит это вскрыл, я исправил.

  ВЫВОД (честно, латерально): костяк bad-cover ⟹ False — реальная малая лемма (Euclidean-engine на
  конечном множестве, пригодится, ЕСЛИ появится настоящая инстанциация). Но стена НЕ обойдена: R3
  as-hard-as-goal, машина абстрактна и ничем не потребляется, `hAll`-подобных ложностей нет, красная
  линия цела (чистая Finset-комбинаторика). `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.BadCoverDescent

open Finset EuclidsPath

/-! ### §11. Ядро: bad-cover невозможен (конечный energy-минимум)

Абстрактно: `carrier : Finset ℕ`, `Bad : ℕ → Prop`, `Energy : ℕ → ℕ`. Если carrier непуст и каждый
bad-элемент имеет строго-меньший по энергии bad-преемник в carrier, то carrier НЕ покрывается bad. -/

/--
  **`bad_cover_absurd` — ДОКАЗАНА (ядро Euclidean-engine на конечном carrier).** Непустой конечный
  carrier + строгий energy-спуск из каждого bad + bad-cover ⟹ `False`. Берём energy-минимум `m₀`;
  он bad (cover), значит есть `m₁ ∈ carrier` с `Energy m₁ < Energy m₀` — против минимальности. -/
theorem bad_cover_absurd {carrier : Finset ℕ} {Bad : ℕ → Prop} {Energy : ℕ → ℕ}
    (hNonempty : carrier.Nonempty)
    (hBadDesc : ∀ m ∈ carrier, Bad m → ∃ m' ∈ carrier, Energy m' < Energy m)
    (hCover : ∀ m ∈ carrier, Bad m) : False := by
  obtain ⟨m₀, hm₀, hmin⟩ := carrier.exists_min_image Energy hNonempty
  obtain ⟨m₁, hm₁, hlt⟩ := hBadDesc m₀ hm₀ (hCover m₀ hm₀)
  exact absurd (hmin m₁ hm₁) (by omega)

/-! ### §12. Bad-cover закрывает: engine ∨ twin -/

/--
  **`bad_cover_closes` — ДОКАЗАНА.** Если каждый bad даёт engine ∨ twin ∨ energy-спуск, и carrier
  весь bad, то engine ∨ twin. От противного: без engine и без twin остаётся только energy-спуск для
  всех bad, и `bad_cover_absurd` даёт `False`. -/
theorem bad_cover_closes {carrier : Finset ℕ} {Bad : ℕ → Prop} {Energy : ℕ → ℕ}
    {Engine : Prop} {TwinAbove : Prop}
    (hNonempty : carrier.Nonempty)
    (hBadDesc : ∀ m ∈ carrier, Bad m →
      Engine ∨ TwinAbove ∨ ∃ m' ∈ carrier, Energy m' < Energy m)
    (hCover : ∀ m ∈ carrier, Bad m) :
    Engine ∨ TwinAbove := by
  by_contra hno
  push_neg at hno
  obtain ⟨hNoEng, hNoTwin⟩ := hno
  -- каждый bad даёт energy-спуск (engine/twin исключены)
  refine bad_cover_absurd (Energy := Energy) hNonempty (fun m hm hb => ?_) hCover
  rcases hBadDesc m hm hb with he | ht | hd
  · exact absurd he hNoEng
  · exact absurd ht hNoTwin
  · exact hd

/-! ### §13–14. Carrier nonempty ⟹ good-или-close; сборка -/

/--
  **`good_or_close` — ДОКАЗАНА.** Непустой carrier: либо есть good-элемент (`¬Bad`), либо все bad
  (тогда `bad_cover_closes` даёт engine ∨ twin). Классический разбор по `∀ m ∈ carrier, Bad m`. -/
theorem good_or_close {carrier : Finset ℕ} {Bad : ℕ → Prop} {Energy : ℕ → ℕ}
    {Engine TwinAbove : Prop}
    (hNonempty : carrier.Nonempty)
    (hBadDesc : ∀ m ∈ carrier, Bad m →
      Engine ∨ TwinAbove ∨ ∃ m' ∈ carrier, Energy m' < Energy m) :
    (∃ m ∈ carrier, ¬ Bad m) ∨ Engine ∨ TwinAbove := by
  by_cases hcov : ∀ m ∈ carrier, Bad m
  · exact Or.inr (bad_cover_closes hNonempty hBadDesc hcov)
  · push_neg at hcov
    obtain ⟨m, hm, hb⟩ := hcov
    exact Or.inl ⟨m, hm, hb⟩

/-! ### §18. Главная сборка: SNOLDescentInput ⟹ неограниченно много twin-центров

Условная редукция, полностью параметризованная по `carrier A N`, `Bad A N`, `Energy`, и по
`good_to_twin`/`bad_internal_descent`. Заменяет counting `SNOL.SNOLInput`. -/

/--
  **`arbitrarily_large_twins_of_descent` — ДОКАЗАНА (условная сборка §21).** При:
  (i) carrier непуст выше каждого `N`;
  (ii) bad-internal-descent (`Bad m ⟹ Engine ∨ twin>N ∨ energy-спуск в carrier`);
  (iii) good-to-twin (`¬Bad m ⟹ twin>N`);
  (iv) `¬Engine` (EPMI);
  для каждого `N` есть twin-центр `> N`. Разбор good/all-bad; engine противоречит (iv), twin — цель. -/
theorem arbitrarily_large_twins_of_descent
    {carrier : ℕ → Finset ℕ} {Bad : ℕ → ℕ → Prop} {Energy : ℕ → ℕ} {Engine : Prop}
    (hNonempty : ∀ N, (carrier N).Nonempty)
    (hBadDesc : ∀ N, ∀ m ∈ carrier N, Bad N m →
      Engine ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨ ∃ m' ∈ carrier N, Energy m' < Energy m)
    (hGoodTwin : ∀ N, ∀ m ∈ carrier N, ¬ Bad N m → ∃ t, N < t ∧ IsTwinCenter t)
    (hNoEngine : ¬ Engine) :
    ∀ N, ∃ t, N < t ∧ IsTwinCenter t := by
  intro N
  rcases good_or_close (Engine := Engine) (TwinAbove := ∃ t, N < t ∧ IsTwinCenter t)
      (hNonempty N) (hBadDesc N) with hgood | he | ht
  · obtain ⟨m, hm, hb⟩ := hgood
    exact hGoodTwin N m hm hb
  · exact absurd he hNoEngine
  · exact ht

/--
  **`twin_prime_conjecture_of_descent` — ДОКАЗАНА (условная).** Та же сборка + уже доказанный мост
  `infinite_of_unbounded_centers` ⟹ `TwinLowers.Infinite`. Единственные содержательные входы —
  `hBadDesc` (R3, новая красная линия), `hGoodTwin` (R2), `hNonempty` (R1). -/
theorem twin_prime_conjecture_of_descent
    {carrier : ℕ → Finset ℕ} {Bad : ℕ → ℕ → Prop} {Energy : ℕ → ℕ} {Engine : Prop}
    (hNonempty : ∀ N, (carrier N).Nonempty)
    (hBadDesc : ∀ N, ∀ m ∈ carrier N, Bad N m →
      Engine ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨ ∃ m' ∈ carrier N, Energy m' < Energy m)
    (hGoodTwin : ∀ N, ∀ m ∈ carrier N, ¬ Bad N m → ∃ t, N < t ∧ IsTwinCenter t)
    (hNoEngine : ¬ Engine) :
    TwinLowers.Infinite :=
  infinite_of_unbounded_centers
    (arbitrarily_large_twins_of_descent hNonempty hBadDesc hGoodTwin hNoEngine)

/-! ### §circularity. Само-аудит (ИСПРАВЛЕН ПОСЛЕ АУДИТА): ЦИРКУЛЯРНО, как `SmallCleanSupply`

ЧЕСТНОЕ ПРИЗНАНИЕ. Первоначально я заявил, что эта редукция НЕ циркулярна (в отличие от
`SmallCleanSupply`). Адверсариальный аудит показал, что это была ОШИБКА, и я её принимаю. Аргумент
аудита (машинно подтверждён ниже): у конечного carrier есть energy-МИНИМУМ `m₀`
(`Finset.exists_min_image` — та же лемма, что в `bad_cover_absurd`). В `m₀` третий дизъюнкт R3
(`∃ m'∈carrier, Energy m' < Energy m₀`) ПРОВАЛЬНО ЛОЖЕН (ниже минимума ничего нет). Значит при
`¬Engine` R3 в `m₀` для каждого `N` СВОДИТСЯ к `∃ t>N, twin t` — это ЦЕЛЬ. Мой прежний довод («escape
через energy-спуск») верен только для НЕминимальных элементов и молча игнорирует минимум, где escape
структурно невозможен. Energy-спуск в конечном carrier обязан ТЕРМИНИРОВАТЬ на good/twin — то есть
counting/parity-стена ПЕРЕНЕСЕНА в минимум carrier, а НЕ обойдена.

Ниже — машинно-проверенная эквивалентность `SNOLDescentInput ⟺ goal` (оба направления), тот же статус,
что `ConcreteComponents.smallCleanSupply_iff_goal`. -/

/--
  **`good_to_twin_trivial` — ДОКАЗАНА.** При естественном `Bad N m := ¬(N<m ∧ twin m)` предпосылка
  `¬Bad` тривиально даёт twin выше `N`. R2 нагрузки не несёт. -/
theorem good_to_twin_trivial {N m : ℕ}
    (hgood : ¬ ¬ (N < m ∧ IsTwinCenter m)) : ∃ t, N < t ∧ IsTwinCenter t := by
  simp only [not_not] at hgood
  exact ⟨m, hgood.1, hgood.2⟩

/--
  **`goal_implies_descent_inputs` — ДОКАЗАНА (обратное направление: цель ⟹ входы).** Само-аудит:
  из цели `∀N ∃ twin>N` следуют ВСЕ входы `twin_prime_conjecture_of_descent` при естественной
  инстанциации (singleton carrier `{N+1}`, `Energy := id`, `Engine := False`, `Bad N m := ¬(N<m ∧
  twin m)`). В singleton нет меньшего элемента ⟹ escape-ветвь R3 мертва ⟹ R3 обязан выдать twin из
  цели. Вместе с доказанным прямым направлением это даёт `SNOLDescentInput ⟺ goal` — ЦИРКУЛЯРНО. -/
theorem goal_implies_descent_inputs
    (hgoal : ∀ N : ℕ, ∃ t, N < t ∧ IsTwinCenter t) :
    (∀ N, (({N + 1} : Finset ℕ)).Nonempty) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ (N < m ∧ IsTwinCenter m) →
      False ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨
        ∃ m' ∈ ({N + 1} : Finset ℕ), (id m' : ℕ) < id m) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ ¬ (N < m ∧ IsTwinCenter m) →
      ∃ t, N < t ∧ IsTwinCenter t) := by
  refine ⟨fun N => ⟨N + 1, by simp⟩, ?_, ?_⟩
  · intro N m hm hbad
    exact Or.inr (Or.inl (hgoal N))
  · intro N m hm hgood
    exact good_to_twin_trivial hgood

/--
  **`descent_reduction_is_circular` — ДОКАЗАНА (итог само-аудита).** Явная фиксация: цель влечёт
  входной набор descent-редукции (при естественной инстанциации). Вместе с `twin_prime_conjecture_of_descent`
  (входы ⟹ цель) это эквивалентность. Вывод: descent-редукция — это ЦЕЛЬ в динамических координатах,
  а не продвижение; parity-стена перенесена в минимум carrier. То же, что `SmallCleanSupply`. -/
theorem descent_reduction_is_circular :
    (∀ N : ℕ, ∃ t, N < t ∧ IsTwinCenter t) →
    (∀ N, (({N + 1} : Finset ℕ)).Nonempty) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ (N < m ∧ IsTwinCenter m) →
      False ∨ (∃ t, N < t ∧ IsTwinCenter t) ∨
        ∃ m' ∈ ({N + 1} : Finset ℕ), (id m' : ℕ) < id m) ∧
    (∀ N, ∀ m ∈ ({N + 1} : Finset ℕ), ¬ ¬ (N < m ∧ IsTwinCenter m) →
      ∃ t, N < t ∧ IsTwinCenter t) :=
  goal_implies_descent_inputs

end EuclidsPath.BadCoverDescent
