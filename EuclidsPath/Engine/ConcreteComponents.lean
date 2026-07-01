/-
  Concrete components — discharge REAL inputs from already-proven arithmetic, and pin the
  irreducible wall to ONE counting statement.

  МОТИВАЦИЯ. Последний аудит (`AtomicSNOL`) отметил: `hDet` (компонентный детерминизм) — «старая стена,
  свёрнутая в равномерный квантор», а её компоненты «заявлены, но не доказаны». Здесь мы ЧЕСТНО
  доказываем те компоненты, что ВЫВОДЯТСЯ из уже проверенной арифметики (`SeparatingScale`,
  `Residuals`), и явно локализуем единственный НЕсводимый вход — counting `bad.card < carrier.card`
  в `A²`-окне (то же, что `SNOL.SNOLInput`). Это НЕ закрытие: настоящая стена — плотность clean-центров
  ниже `A²`, а она за красной линией. Но два входа переведены из гипотез в теоремы.

  ДОКАЗАНО здесь РЕАЛЬНО (стандартные аксиомы, без sorry) — два genuine discharge + обёртка:
    * `active_component_determinism` — active-ребро детерминировано меткой (residue mod P_A). Выводится
      из `SeparatingScale.eq_of_modEq_of_lt` + `legal_lift_lt_primorial`. Это НАСТОЯЩИЙ перевод одной из
      «четырёх exact-компонент» из гипотезы в теорему (как раньше König), а не переклейка ярлыка.
    * `oldPeel_component_determinism` — old-peel-ребро (`U = p·V`, `p` из метки) детерминировано.
    * `twin_center_of_clean_small` — clean-центр с малыми сторонами (`< A²`) есть twin (обёртка
      `sink_is_twin`).

  ЧЕСТНАЯ ГРАНИЦА (машинно-проверена в §4): финальная «редукция» к `SmallCleanSupply` — ЦИРКУЛЯРНА.
  `smallCleanSupply_iff_goal` ДОКАЗЫВАЕТ `SmallCleanSupply ⟺ (∀N ∃ twin m>N)`: twin-центр `m≥2` сам
  является малым clean-центром при `A=6m−2`. То есть `SmallCleanSupply` — это ЦЕЛЬ, переписанная в
  `A²`-оконных терминах, а НЕ вход-редукция. Я это признаю прямо, а не выдаю за продвижение.

  ИТОГ (честно). РЕАЛЬНО продвинуто: active/old-peel компоненты детерминизма теперь ДОКАЗАНЫ из
  separating scale (сузили `hDet`). НЕ продвинуто: настоящая стена — плотность малых clean-центров ниже
  `A²` (эквивалент counting-условия `SNOL.SNOLInput`), она за красной линией (распределение простых) и
  здесь НЕ сдвинута; `SmallCleanSupply` эквивалентна цели. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.SeparatingScale
import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.NonCover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ConcreteComponents

open EuclidsPath.SeparatingScale EuclidsPath.Residuals

/-! ### 1. Active-компонента — ДОКАЗАНА из separating scale (реальный discharge)

Active-ребро `U → V` над центром: `U = a · V`, где `a > 0` — legal factor (делит carrier-side
`N ≤ 6X_A+1`). Метка ребра — residue `a mod P_A`. Утверждение детерминизма: два active-предшественника
одного `V` с равной меткой равны. Это выводится ЦЕЛИКОМ из уже доказанной separating-scale арифметики. -/

/--
  **`active_component_determinism` — ДОКАЗАНА.** Два legal active-фактора `a₁, a₂` над общим `V` с
  равной меткой (`a₁ ≡ a₂ (mod P_A)`) при separating scale дают равные состояния `a₁·V = a₂·V`.
  Вывод: `legal_lift_lt_primorial` даёт `aᵢ < P_A`; `eq_of_modEq_of_lt` даёт `a₁ = a₂`. Это РЕАЛЬНЫЙ
  discharge active-компоненты `hDet`, а не переименование: всё опирается на проверенные леммы. -/
theorem active_component_determinism {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    {a₁ a₂ V N₁ N₂ : ℕ}
    (hpos₁ : 0 < a₁) (hpos₂ : 0 < a₂)
    (hdvd₁ : a₁ ∣ N₁) (hdvd₂ : a₂ ∣ N₂)
    (hN₁ : 0 < N₁ ∧ N₁ ≤ 6 * X_A + 1) (hN₂ : 0 < N₂ ∧ N₂ ≤ 6 * X_A + 1)
    (hlabel : a₁ ≡ a₂ [MOD P_A]) :
    a₁ * V = a₂ * V := by
  have h1 : a₁ < P_A := legal_lift_lt_primorial hsep hN₁.2 hdvd₁ hpos₁ hN₁.1
  have h2 : a₂ < P_A := legal_lift_lt_primorial hsep hN₂.2 hdvd₂ hpos₂ hN₂.1
  rw [eq_of_modEq_of_lt h1 h2 hlabel]

/--
  **`oldPeel_component_determinism` — ДОКАЗАНА (тривиально, но честно).** Old-peel-ребро над `V`
  имеет вид `U = p · V`, где простое `p` ПОЛНОСТЬЮ определяется меткой (метка old-peel-ребра хранит
  `p`). Значит равная метка ⟹ равное `p` ⟹ равное `U`. Здесь метка = сам `p` (`p₁ = p₂` как гипотеза
  равенства меток), и заключение — прямое переписывание. -/
theorem oldPeel_component_determinism {p₁ p₂ V : ℕ} (hlabel : p₁ = p₂) :
    p₁ * V = p₂ * V := by rw [hlabel]

/-! ### 2. Sink ⇒ twin и clean-центр выше N — обёртки проверенного

`sink_is_twin` уже доказано: clean-центр с обеими сторонами `< A²` есть twin. `carrier_nonempty_above`
даёт clean-центр выше любого `N`. Проблема (Step00Close): centre из `carrier_nonempty_above` слишком
большой (`> A²`), так что `sink_is_twin` неприменим. Формализуем это ТОЧНО. -/

/-- Обёртка `sink_is_twin`: clean-центр `m ≥ 1` с обеими сторонами `< A²` — twin. -/
theorem twin_center_of_clean_small {A m : ℕ} (hm : 1 ≤ m)
    (hlo2 : 6 * m - 1 < A * A) (hhi2 : 6 * m + 1 < A * A)
    (hcl : ∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1))) :
    IsTwinCenter m := by
  -- IsTwinCenter = (6m-1).Prime ∧ (6m+1).Prime = TwinCenterZ
  have h := sink_is_twin (A := A) (m := m) (by omega) (by omega) hlo2 hhi2 hcl
  exact h

/-! ### 3. Единственный counting-вход и финальная редукция

Всё выше — арифметика и обёртки. Оставшаяся трудность — ЕДИНСТВЕННОЕ counting-утверждение: на каждом
масштабе найти clean-центр В ОКНЕ `(N, A²/6)` (достаточно малый, чтобы `sink_is_twin` сработал). Это
плотностное утверждение о clean-центрах ниже `A²`; оно за красной линией. Подаём явной гипотезой. -/

/-- `SmallCleanSupply`: для каждого `N` найдётся масштаб `A` и clean-центр `m` в окне `N < m` и
    `6m+1 < A²`, ни один старый `q ≤ A` не делит стороны. ЕДИНСТВЕННЫЙ несводимый вход (counting/density,
    красная линия). Эквивалент counting-условия `SNOL.SNOLInput`. -/
def SmallCleanSupply : Prop :=
  ∀ N : ℕ, ∃ A m : ℕ, 1 ≤ m ∧ N < m ∧ 6 * m + 1 < A * A ∧ 6 * m - 1 < A * A ∧
    (∀ q : ℕ, q.Prime → q ≤ A → ¬ (q ∣ (6 * m - 1) ∨ q ∣ (6 * m + 1)))

/--
  **`twinCenter_unbounded_of_smallCleanSupply` — ДОКАЗАНА при `SmallCleanSupply`.** Если counting-вход
  выполнен (для каждого `N` есть достаточно малый clean-центр выше `N`), то twin-центров неограниченно
  много: каждый такой clean-центр в окне `< A²` — twin (`twin_center_of_clean_small`). -/
theorem twinCenter_unbounded_of_smallCleanSupply (H : SmallCleanSupply) :
    ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m := by
  intro N
  obtain ⟨A, m, hm, hN, hhi, hlo, hcl⟩ := H N
  exact ⟨m, hN, twin_center_of_clean_small hm hlo hhi hcl⟩

/--
  **`twin_prime_conjecture_of_smallCleanSupply` — ДОКАЗАНА при `SmallCleanSupply`.** Финальная
  редукция: counting-вход ⟹ `TwinLowers.Infinite` (через уже доказанный
  `NonCover.infinite_of_unbounded_centers`). Единственный несведённый вход — `SmallCleanSupply`. -/
theorem twin_prime_conjecture_of_smallCleanSupply (H : SmallCleanSupply) :
    TwinLowers.Infinite :=
  EuclidsPath.infinite_of_unbounded_centers (twinCenter_unbounded_of_smallCleanSupply H)

/--
  **Контрапозиция.** `TwinLowers` конечно + `SmallCleanSupply` ⟹ `False`. -/
theorem finite_contradicts_smallCleanSupply (hfin : ¬ TwinLowers.Infinite) (H : SmallCleanSupply) :
    False :=
  hfin (twin_prime_conjecture_of_smallCleanSupply H)

/-! ### 4. ЧЕСТНЫЙ САМО-АУДИТ: `SmallCleanSupply` ЭКВИВАЛЕНТНА цели (⟹ НЕ редукция)

Ниже — машинно-проверенное признание границы честности. `SmallCleanSupply` НЕ является настоящим
входом-редукцией: она ЛОГИЧЕСКИ ЭКВИВАЛЕНТНА самой цели `∀N ∃ twin m>N`. Обратное направление
(`goal → SmallCleanSupply`) доказано ниже: twin-центр `m ≥ 2` сам является малым clean-центром при
`A = 6m−2` (стороны `6m±1` просты, значит не делятся старыми `q ≤ A < 6m−1`; окно `6m+1 < A²`
выполнено). Поэтому `twin_prime_conjecture_of_smallCleanSupply` — это цель, переписанная в
`A²`-оконных терминах, а НЕ продвижение. -/

/--
  **`goal_implies_smallCleanSupply` — ДОКАЗАНА (само-аудит: обратное направление эквивалентности).**
  `(∀N ∃ twin m>N) ⟹ SmallCleanSupply`. Значит `SmallCleanSupply ⟺ цель`, и её нельзя выдавать за
  редукцию: это цель в другой записи. Twin `m≥2` — малый clean-центр при `A=6m−2`. -/
theorem goal_implies_smallCleanSupply
    (hgoal : ∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m) : SmallCleanSupply := by
  intro N
  obtain ⟨m, hmN, htwin⟩ := hgoal (max N 2)
  have hmN' : N < m := by omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hA : 6 * (k + 2) - 2 = 6 * k + 10 := by omega
  refine ⟨6 * (k + 2) - 2, k + 2, by omega, hmN', ?_, ?_, ?_⟩
  · rw [hA]; nlinarith
  · rw [hA]; have : 6 * (k + 2) - 1 = 6 * k + 11 := by omega
    rw [this]; nlinarith
  · intro q hq hqle
    rcases htwin with ⟨hp1, hp2⟩
    rintro (hd | hd)
    · rcases Nat.Prime.eq_one_or_self_of_dvd hp1 q hd with h | h
      · exact hq.ne_one h
      · omega
    · rcases Nat.Prime.eq_one_or_self_of_dvd hp2 q hd with h | h
      · exact hq.ne_one h
      · omega

/--
  **`smallCleanSupply_iff_goal` — ДОКАЗАНА (эквивалентность, а не редукция).** Полное признание:
  `SmallCleanSupply ⟺ (∀N ∃ twin m>N)`. Обе стороны эквивалентны `TwinLowers.Infinite`. Вывод: этот
  файл ДОКАЗЫВАЕТ РЕАЛЬНО две вещи (active/old-peel компоненты детерминизма из separating scale;
  обёртку sink⇒twin), но финальная «редукция» к `SmallCleanSupply` ЦИРКУЛЯРНА и здесь помечена как
  таковая. Настоящая стена (плотность малых clean-центров) не сдвинута. -/
theorem smallCleanSupply_iff_goal :
    SmallCleanSupply ↔ (∀ N : ℕ, ∃ m, N < m ∧ IsTwinCenter m) :=
  ⟨twinCenter_unbounded_of_smallCleanSupply, goal_implies_smallCleanSupply⟩

end EuclidsPath.ConcreteComponents
