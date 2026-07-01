/-
  HigherEnergy — теорема высшей энергетической несовместимости на пути Евклида.
  Источник: higher_energy_incompatibility_full_formal_ru_2026-07-01.md.
  Проза: prose/24_BoundaryDecomp.md (раздел «Weighted debt energy»).

  ИДЕЯ. Лексикографическая энергия узла пути Евклида: `Energy(x) = (DebtEnergy(x), LocalFuel(x))`, где
  `DebtEnergy(D) = ∑_{a∈D} (B+1)^rank(a)` — взвешенный вес долга. Internal-ход держит долг и роняет
  LocalFuel; promotion роняет DebtEnergy (замена одного focus-долга младшими kids меньшего суммарного
  веса). Оба хода строго уменьшают лексикографическую энергию ⟹ вечный путь невозможен (well-founded).

  ЗДЕСЬ ДОКАЗАНО (реальная математика, стандартные аксиомы, без sorry):
    * `lexNat_wf` — well-foundedness лекс-порядка на ℕ×ℕ;
    * `no_live_state_if_closes_or_moves_down` — well-founded запрет вечного двигателя;
    * `debtEnergy_decreases_of_weightedReplacement` — замена долга РЕАЛЬНО роняет `DebtEnergy` (арифметика
      весов, не абстрактно);
    * `kids_weight_lt_focus_of_rank_bound` — branch-bound (`kids.card ≤ B` + меньший ранг) ⟹ весовое
      неравенство;
    * `euclideanPathMove_decreases_energy` — каждый ход роняет лекс-энергию;
    * `higher_energy_incompatibility_on_euclidean_path` — главная теорема (под NoEngine/NoNewTwin — ⊥);
    * `twin_above_of_higher_energy_engine` — позитивная форма.

  ЧЕСТНАЯ ГРАНИЦА (подтверждена аудитом — вход НЕ инстанциируем; §22bis machine-checked). Абстрактный
  модуль sound и reusable — это самый содержательный descent-каркас в дереве (теоремы §8–9 — реальная
  арифметика весов). Но Step00 НЕ закрыт: единственный вход `step00_promotion_is_weightedDebtReplacement`
  на графе `6m±1` **МИЗОРИЕНТИРОВАН и не инстанциируем**:
    • ВСЯ реально-арифметическая динамика идёт ВНИЗ по высоте/центру (`active_descent_height` `n<m`,
      `old_peel_height_drop` `t<n`, `cofactor_is_center`, `RankDescent` `r→r−1`), а `PromotePass` требует
      `x.A < y.A` — ВВЕРХ. Forward-хода ВВЕРХ у реального движка нет;
    • повышение `A→A'` РАСТИТ множество старых простых (примориал монотонен) ⟹ promotion ДОБАВЛЯЕТ
      атомы-долги (refuel), а не гасит focus — а weight-увеличивающий ход НЕ является replacement
      (машинно: `refuel_is_not_weightedReplacement`, §22bis; тип структурно запрещает подделку);
    • любой `rank`, при котором ход ВВЕРХ роняет вес, уже утверждает, что спуск оканчивается близнецами
      = цель (та же подпись, что `smallCleanSupply_iff_goal` / `descent_reduction_is_circular`).
  Плюс `repeated_level_signature_closes` (повтор подписи ⟹ Close) — это labelled-fan-in ветка, чей
  терминал прежние аудиты нашли циркулярным; а LocalFuel-граница прячет counting = `SNOL.SNOLInput`.
  Итог аудита: net = SAME WALL в энергетической одежде. `Step00` остаётся `sorry`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.HigherEnergy

/-! ### §3–4. Лексикографический порядок на ℕ×ℕ и его well-foundedness -/

/-- Лекс-порядок: `(a',b') < (a,b)` если `a'<a` или (`a'=a` и `b'<b`). -/
def LexNat (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- **`lexNat_wf` — ДОКАЗАНА.** Лекс-порядок на ℕ×ℕ well-founded (двойная сильная индукция). -/
theorem lexNat_wf : WellFounded LexNat := by
  refine ⟨?_⟩
  intro p
  rcases p with ⟨a, b⟩
  revert b
  refine Nat.strong_induction_on a ?_
  intro a IHa b
  refine Nat.strong_induction_on b ?_
  intro b IHb
  apply Acc.intro
  intro q hq
  rcases q with ⟨a', b'⟩
  rcases hq with hLeft | ⟨ha, hb⟩
  · exact IHa a' hLeft b'
  · simp only at ha hb
    subst ha
    exact IHb b' hb

/-! ### §5. Общий well-founded-комбинатор: нет живого узла -/

/--
  **`no_live_state_if_closes_or_moves_down` — ДОКАЗАНА.** Если каждый live-узел либо закрывается
  (`Close`), либо делает ход к live-узлу строго меньшей лекс-энергии, а закрытие запрещено, то
  live-узла не существует. Well-founded индукция по `LexNat ∘ EnergyPair`. Чистый запрет вечного
  двигателя. -/
theorem no_live_state_if_closes_or_moves_down {Node : Type*}
    (Live : Node → Prop) (Close : Node → Prop) (Move : Node → Node → Prop)
    (EnergyPair : Node → ℕ × ℕ)
    (hStep : ∀ x, Live x → Close x ∨ ∃ y, Live y ∧ Move x y)
    (hNoClose : ∀ x, Live x → ¬ Close x)
    (hDrop : ∀ {x y}, Move x y → LexNat (EnergyPair y) (EnergyPair x)) :
    ¬ ∃ x, Live x := by
  have hWF : WellFounded (fun y x => LexNat (EnergyPair y) (EnergyPair x)) :=
    InvImage.wf EnergyPair lexNat_wf
  have hNoLive : ∀ x, ¬ Live x := by
    intro x
    refine hWF.induction (C := fun x => ¬ Live x) x ?_
    intro x IH hxLive
    rcases hStep x hxLive with hClose | ⟨y, hyLive, hxy⟩
    · exact (hNoClose x hxLive) hClose
    · exact IH y (hDrop hxy) hyLive
  rintro ⟨x, hx⟩
  exact hNoLive x hx

/-! ### §6. Взвешенная энергия долга -/

variable {Atom : Type*} [DecidableEq Atom]

/-- Вес атома долга: `(B+1)^rank`. Старший ранг весит экспоненциально больше суммы младших. -/
def AtomWeight (rank : Atom → ℕ) (B : ℕ) (a : Atom) : ℕ := (B + 1) ^ rank a

/-- Энергия долга: сумма весов атомов. -/
def DebtEnergy (rank : Atom → ℕ) (B : ℕ) (D : Finset Atom) : ℕ :=
  ∑ a ∈ D, AtomWeight rank B a

/-! ### §7. Weighted debt replacement -/

/-- Замена одного focus-долга набором kids: младший ранг, меньший суммарный вес, обновление
    `D' = (D.erase focus) ∪ kids`. Несёт данные (`focus`, `kids`), поэтому `Type`, не `Prop`. -/
structure WeightedDebtReplacement (rank : Atom → ℕ) (B : ℕ) (D D' : Finset Atom) where
  focus : Atom
  hfocus : focus ∈ D
  kids : Finset Atom
  kids_lower : ∀ k ∈ kids, rank k < rank focus
  kids_weight_lt_focus : (∑ k ∈ kids, AtomWeight rank B k) < AtomWeight rank B focus
  disjoint : Disjoint (D.erase focus) kids
  update : D' = (D.erase focus) ∪ kids

/-! ### §8. Замена долга РЕАЛЬНО уменьшает `DebtEnergy` -/

/--
  **`debtEnergy_decreases_of_weightedReplacement` — ДОКАЗАНА (реальная арифметика весов).**
  `DebtEnergy(D') < DebtEnergy(D)`. Разбиваем `D = {focus} ⊔ (D.erase focus)`, `D' = (D.erase focus)
  ⊔ kids`; общий член `E(D.erase focus)` сокращается, остаётся `E(kids) < E(focus)`. -/
theorem debtEnergy_decreases_of_weightedReplacement (rank : Atom → ℕ) (B : ℕ)
    {D D' : Finset Atom} (hRep : WeightedDebtReplacement rank B D D') :
    DebtEnergy rank B D' < DebtEnergy rank B D := by
  -- разбираем структуру в плоские гипотезы, чтобы D' не сидел в зависимом типе
  obtain ⟨focus, hfocus, kids, _, hkw, hdisj, hupd⟩ := hRep
  unfold DebtEnergy
  have hnm : focus ∉ D.erase focus := Finset.notMem_erase focus D
  have hsumD : (∑ a ∈ D, AtomWeight rank B a)
      = AtomWeight rank B focus + ∑ a ∈ D.erase focus, AtomWeight rank B a := by
    conv_lhs => rw [← Finset.insert_erase hfocus]
    rw [Finset.sum_insert hnm]
  have hsumD' : (∑ a ∈ D', AtomWeight rank B a)
      = (∑ a ∈ D.erase focus, AtomWeight rank B a) + ∑ a ∈ kids, AtomWeight rank B a := by
    rw [hupd, Finset.sum_union hdisj]
  rw [hsumD, hsumD']
  omega

/-! ### §9. Branch-bound ⟹ weight-bound (техническая, для инстанциации) -/

/--
  **`kids_weight_lt_focus_of_rank_bound` — ДОКАЗАНА.** Если `kids.card ≤ B` и все kid-ранги меньше
  `rank focus`, то `∑ weight(kids) < weight(focus)`. При `rank focus = 0` kids пусты; при `r+1` каждый
  kid весит `≤ (B+1)^r`, а `B·(B+1)^r < (B+1)^{r+1}`. -/
theorem kids_weight_lt_focus_of_rank_bound (rank : Atom → ℕ) (B : ℕ)
    (focus : Atom) (kids : Finset Atom)
    (hBpos : 0 < B) (hcard : kids.card ≤ B) (hlower : ∀ k ∈ kids, rank k < rank focus) :
    (∑ k ∈ kids, AtomWeight rank B k) < AtomWeight rank B focus := by
  rcases Nat.eq_zero_or_pos (rank focus) with h0 | hpos
  · have hempty : kids = ∅ := by
      by_contra hne
      obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty hne
      have := hlower k hk; omega
    simp [hempty, AtomWeight]
  · set r := rank focus - 1 with hr
    have hrf : rank focus = r + 1 := by omega
    have hbound : ∀ k ∈ kids, AtomWeight rank B k ≤ (B + 1) ^ r := by
      intro k hk
      have h2 : rank k ≤ r := by have := hlower k hk; omega
      exact Nat.pow_le_pow_right (by omega) h2
    have hpp : 0 < (B + 1) ^ r := pow_pos (by omega) r
    calc (∑ k ∈ kids, AtomWeight rank B k)
        ≤ ∑ _k ∈ kids, (B + 1) ^ r := Finset.sum_le_sum hbound
      _ = kids.card * (B + 1) ^ r := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ B * (B + 1) ^ r := Nat.mul_le_mul_right _ hcard
      _ < (B + 1) * (B + 1) ^ r := by nlinarith [hpp]
      _ = AtomWeight rank B focus := by rw [AtomWeight, hrf]; ring

/-! ### §10–15. Узел пути Евклида, ходы, убывание энергии -/

/-- Узел пути Евклида: уровень `A`, долг `debt`, локальное топливо `localFuel`. -/
structure EuclideanPathNode (M0 N : ℕ) (Atom : Type*) [DecidableEq Atom] where
  A : ℕ
  debt : Finset Atom
  localFuel : ℕ

/-- Энергия узла: `(DebtEnergy, localFuel)`. -/
def EuclideanPathNode.energy {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    (x : EuclideanPathNode M0 N Atom) : ℕ × ℕ :=
  (DebtEnergy rank B x.debt, x.localFuel)

/-- Internal-ход: тот же уровень, тот же долг, строго меньше топлива. -/
structure InternalPass {M0 N : ℕ} (x y : EuclideanPathNode M0 N Atom) : Prop where
  same_level : y.A = x.A
  debt_same : y.debt = x.debt
  fuel_drop : y.localFuel < x.localFuel

/-- Promote-ход: уровень вверх + weighted debt replacement (несёт данные replacement, поэтому `Type`). -/
structure PromotePass {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    (x y : EuclideanPathNode M0 N Atom) where
  level_lt : x.A < y.A
  replacement : WeightedDebtReplacement rank B x.debt y.debt

/-- **`promotePass_decreases_debtEnergy` — ДОКАЗАНА.** Promotion роняет `DebtEnergy`. -/
theorem promotePass_decreases_debtEnergy {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    {x y : EuclideanPathNode M0 N Atom} (h : PromotePass rank B x y) :
    DebtEnergy rank B y.debt < DebtEnergy rank B x.debt :=
  debtEnergy_decreases_of_weightedReplacement rank B h.replacement

/-- Ход пути Евклида: internal или promote. -/
inductive EuclideanPathMove {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ) :
    EuclideanPathNode M0 N Atom → EuclideanPathNode M0 N Atom → Prop
  | internal {x y} : InternalPass x y → EuclideanPathMove rank B x y
  | promote {x y} : PromotePass rank B x y → EuclideanPathMove rank B x y

/--
  **`euclideanPathMove_decreases_energy` — ДОКАЗАНА.** Каждый ход строго уменьшает лекс-энергию:
  internal — вторая координата (топливо), promote — первая (долг). -/
theorem euclideanPathMove_decreases_energy {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    {x y : EuclideanPathNode M0 N Atom} (hMove : EuclideanPathMove rank B x y) :
    LexNat (EuclideanPathNode.energy rank B y) (EuclideanPathNode.energy rank B x) := by
  cases hMove with
  | internal h =>
    refine Or.inr ⟨?_, h.fuel_drop⟩
    show DebtEnergy rank B y.debt = DebtEnergy rank B x.debt
    rw [h.debt_same]
  | promote h =>
    exact Or.inl (promotePass_decreases_debtEnergy rank B h)

/-! ### §16–18. CloseAt, NoClose и главная теорема -/

/-- `CloseAt A M0 N := Engine A M0 ∨ ∃ t>N, twin`. Абстрактный `Engine`. -/
def CloseAt (Engine : ℕ → ℕ → Prop) (Twin : ℕ → Prop) (A M0 N : ℕ) : Prop :=
  Engine A M0 ∨ ∃ t, N < t ∧ Twin t

/--
  **`higher_energy_incompatibility_on_euclidean_path` — ДОКАЗАНА (главная теорема).** Если есть живой
  старт, каждый живой узел закрывается ∨ делает энергетически убывающий ход к живому узлу, а под
  `¬Engine` и «нет twin выше N» закрытие запрещено, то `False`. Это well-founded запрет вечного пути
  Евклида, применённый к лекс-энергии `(DebtEnergy, LocalFuel)`. -/
theorem higher_energy_incompatibility_on_euclidean_path
    {Engine : ℕ → ℕ → Prop} {Twin : ℕ → Prop}
    (rank : Atom → ℕ) (B : ℕ) (M0 N : ℕ)
    (Live : EuclideanPathNode M0 N Atom → Prop)
    (hStart : ∃ x, Live x)
    (hStep : ∀ x, Live x →
      CloseAt Engine Twin x.A M0 N ∨ ∃ y, Live y ∧ EuclideanPathMove rank B x y)
    (hNoEngine : ∀ A, ¬ Engine A M0)
    (hNoNew : ¬ ∃ t, N < t ∧ Twin t) :
    False := by
  refine no_live_state_if_closes_or_moves_down Live
    (fun x => CloseAt Engine Twin x.A M0 N)
    (fun x y => EuclideanPathMove rank B x y)
    (fun x => EuclideanPathNode.energy rank B x)
    hStep ?_ (fun {x y} h => euclideanPathMove_decreases_energy rank B h) hStart
  · intro x hx hClose
    rcases hClose with hE | hT
    · exact hNoEngine x.A hE
    · exact hNoNew hT

/--
  **`twin_above_of_higher_energy_engine` — ДОКАЗАНА (позитивная форма).** Тот же движок в
  контрапозиции: под `¬Engine` наличие живого пути с закрытием-или-убыванием даёт twin выше N. -/
theorem twin_above_of_higher_energy_engine
    {Engine : ℕ → ℕ → Prop} {Twin : ℕ → Prop}
    (rank : Atom → ℕ) (B : ℕ) (M0 N : ℕ)
    (Live : EuclideanPathNode M0 N Atom → Prop)
    (hStart : ∃ x, Live x)
    (hStep : ∀ x, Live x →
      CloseAt Engine Twin x.A M0 N ∨ ∃ y, Live y ∧ EuclideanPathMove rank B x y)
    (hNoEngine : ∀ A, ¬ Engine A M0) :
    ∃ t, N < t ∧ Twin t := by
  by_contra hNoTwin
  exact higher_energy_incompatibility_on_euclidean_path rank B M0 N Live hStart hStep hNoEngine hNoTwin

/-! ### §22bis. Машинно-проверенный NO-GO: refuel-promotion НЕ является replacement

Честность (по аудиту): единственный несведённый вход — `step00_promotion_is_weightedDebtReplacement`,
и он на графе `6m±1` НЕ инстанциируем. Причина арифметическая и резкая: ВСЯ реально-арифметическая
динамика графа идёт ВНИЗ по высоте/центру (`active_descent_height` `n<m`, `old_peel_height_drop` `t<n`,
`cofactor_is_center`, `RankDescent` `r→r−1`), а `PromotePass` требует `x.A < y.A` — ВВЕРХ. Повышение
порога `A→A'` РАСТИТ множество старых простых (`oldPrimorial ∏_{5≤p≤A} p` монотонен), то есть promotion
ДОБАВЛЯЕТ атомы-долги (union со свежими, без стёртого focus) — это refuel, а не
`(D.erase focus) ∪ kids` со строго меньшим весом. Любой `rank`, при котором ход ВВЕРХ роняет
`(B+1)^rank`, уже утверждает, что спуск оканчивается близнецами = цель (та же подпись, что
`smallCleanSupply_iff_goal`).

Ниже — конкретная машинно-проверенная фиксация: promotion, УВЕЛИЧИВАЮЩИЙ вес (добавил атом, ничего не
стёр), НЕ может быть `WeightedDebtReplacement` — тип структурно запрещает подделать убывание. -/

/--
  **`refuel_is_not_weightedReplacement` — ДОКАЗАНА (no-go, честность встроена в тип).** Конкретно:
  `Atom := ℕ`, `rank := id`, `B := 1`. Refuel `{0} → {0,1}` (добавлен атом `1`, ничего не стёрто)
  РАСТИТ вес (`E({0})=1 < E({0,1})=3`), поэтому НЕ существует `WeightedDebtReplacement id 1 {0} {0,1}`:
  replacement обязан СТРОГО уменьшать `DebtEnergy` (`debtEnergy_decreases_of_weightedReplacement`), а
  здесь энергия растёт. Значит weight-увеличивающий promotion (= refuel) невыразим как replacement —
  движок его отвергает по построению. Это машинная версия §22-признания «линия умирает честно». -/
theorem refuel_is_not_weightedReplacement :
    ¬ Nonempty (WeightedDebtReplacement (Atom := ℕ) id 1 {0} {0, 1}) := by
  rintro ⟨rep⟩
  have hdec := debtEnergy_decreases_of_weightedReplacement (Atom := ℕ) id 1 rep
  have h1 : DebtEnergy (Atom := ℕ) id 1 {0} = 1 := by decide
  have h2 : DebtEnergy (Atom := ℕ) id 1 {0, 1} = 3 := by decide
  rw [h1, h2] at hdec
  omega

end EuclidsPath.HigherEnergy
