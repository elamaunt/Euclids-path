/-
  DyadicFrontWindow — T-ОТНОСИТЕЛЬНОЕ ОКНО ИНВАРИАНТА ФРОНТА КАЦА–ПАВЛОВИЧА (🟢, БЕЗ ТАИНТА).

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  ГРОМКИЙ ЧЕСТНЫЙ ЗАГОЛОВОК — ЧТО ЗДЕСЬ ЕСТЬ, ЧЕГО НЕТ.                                    │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  КОНТЕКСТ. В `DyadicBlowup.lean` (§2ter) красный вход дядической ветви назван открыто:
  `FrontPreservedForever` — сохранение инварианта доминирования фронта `FrontDomination`
  на ВСЁМ `[0,∞)` для бесконечного каскада. Это исследовательский фронтир (движущийся фронт;
  Barbato–Morandin–Romito 2011, Cheskidov 2008, Kiselev–Zlatoš 2005), и мы его НЕ доказываем.
  Здесь красный вход ЧЕСТНО СУЖАЕТСЯ с трёх сторон, НЕ закрываясь:

  ЧТО ЗДЕСЬ ЕСТЬ (всё 🟢: стандартная тройка аксиом, без sorry/native_decide, БЕЗ карантина):
    • §1 `FrontPreservedUntil T` — T-ОТНОСИТЕЛЬНЫЙ БЛИЗНЕЦ красного входа: сохранение
      `FrontDomination` на конечном окне `[0,T)`. Мост `frontPreservedForever_iff_forall_until`:
      «навсегда» ⟺ «до любого T». ЧЕСТНОСТЬ: мост — ФОРМАЛЬНАЯ СВЯЗКА, оплаченная чистой
      логикой кванторов (инстанцирование `T := t+1`), а НЕ новой аналитикой.
    • §2 ОБИТАЕМОСТЬ (анти-вакуумные свидетели): `ssMode_frontPreservedUntil` — самоподобный
      профиль §2bis удовлетворяет T-относительной форме на ВСЁМ интервале жизни `[0,T)` с
      ФИКСИРОВАННОЙ нижней границей `m₀ := β_{J+1}/T`. Оплата: `ssMode_frontDomination` даёт
      лишь t-ЗАВИСИМОЕ `m = a_{J+1}(t)`; фиксация `m₀` оплачена монотонностью
      `g(t) = (T−t)⁻¹` (`inv_anti₀`) при `0 < T` — это CORR-исправление отчёта
      («НЕ прямая композиция», единственная настоящая работа юнита). КОНТРАСТ
      `ssMode_not_frontPreservedForever`: тот же профиль с тем же `m₀` НЕ удовлетворяет
      `FrontPreservedForever` (в `t = T` амплитуда обнуляется в Lean-конвенции `0⁻¹ = 0`) —
      разрыв между «до T» и «навсегда» ОБИТАЕМ, формы НЕ совпадают.
    • §3 КОНЕЧНО-ОКОННЫЙ MVT-ШАГ `frontDomination_persists_on_window`: если инвариант в `t₀`
      выполнен со СТРОГИМ ЗАПАСОМ `δ` и скорости трёх зазоров фронта ограничены `C` на окне,
      то `FrontDomination` держится на всём `[t₀, t₀+ε]` при `C·ε ≤ δ`. Оплата — MVT-оценка
      mathlib `norm_image_sub_le_of_norm_deriv_le_segment'` + `HasDerivAt`-кирпичи динамики КП
      (`DyadicBlowup`). Скоростные границы `C` — ИМЕНОВАННЫЙ ЛОКАЛЬНЫЙ ВХОД (оконная форма
      «гипотезы непересечения», анонсированной в §2ter как сознательно опущенный шаг).
      Стационарный свидетель `frontWindow_realizable` подтверждает СОВМЕСТНОСТЬ гипотез окна.

  ЧЕГО ЗДЕСЬ НЕТ (КРАСНЫЕ ЛИНИИ — ГРОМКО):
    • `FrontPreservedForever` НЕ доказан и НЕ закрыт: T-относительная форма СТРОГО СЛАБЕЕ,
      и разрыв обитаем машинно (`ssMode_not_frontPreservedForever`). Красный вход ОСТАЁТСЯ.
    • MVT-шаг НЕ итерируется здесь до `[0,∞)`: запас `δ` и граница `C` ЛОКАЛЬНЫ; их
      равномерное удержание при движущемся фронте бесконечного каскада — СУЩЕСТВО открытой
      трудности. Итерация окон — не формальность, а сам фронтир; мы её НЕ выдаём за сделанную.
    • Это НЕ решение Навье–Стокса, НЕ конечно-энергетическая теорема КП, НЕ Гёдель.
      Стационарный свидетель §3 несёт ТРИВИАЛЬНУЮ динамику (все скорости нулевые): он
      свидетельствует лишь совместность гипотез окна, а НЕ содержательный движущийся фронт.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/DyadicFrontWindow.lean
-/
import Mathlib
import EuclidsPath.Engine.DyadicBlowup

set_option autoImplicit false

noncomputable section

namespace EuclidsPath.DyadicFrontWindow

open EuclidsPath.DyadicBlowup

/-! ### §1. T-относительная форма красного входа и мост к «навсегда»

`FrontPreservedForever` (DyadicBlowup §2ter) требует инварианта на всём `[0,∞)`. Здесь тот же
инвариант ставится на конечное окно `[0,T)` — это НАЗВАННОЕ ЧЕСТНОЕ СУЖЕНИЕ, а не подмена:
мост §1 показывает, что «навсегда» в точности равносильно «до любого T». -/

/-- **T-относительный близнец красного входа.** Сохранение инварианта доминирования фронта
    `FrontDomination` на конечном окне `[0,T)` (вместо всего `[0,∞)` у `FrontPreservedForever`).
    В отличие от бесконечной моды, эта форма ОБИТАЕМА содержательно: самоподобный профиль
    `ssMode` удовлетворяет ей на всём своём интервале жизни (`ssMode_frontPreservedUntil`),
    и разрыв с «навсегда» обитаем (`ssMode_not_frontPreservedForever`). -/
def FrontPreservedUntil (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) (T : ℝ) : Prop :=
  ∀ t, 0 ≤ t → t < T → FrontDomination lam d a J ρ κ m t

/-- **Нулевое окно — граница шкалы (ЧЕСТНО: вакуумная истинность).** При `T = 0` окно `[0,0)`
    пусто, и `FrontPreservedUntil` выполнено для ЛЮБЫХ параметров. Это НЕ анти-вакуумный
    свидетель (он в §2, `ssMode_frontPreservedUntil`), а честная отметка нижнего конца шкалы:
    T-относительная форма стартует с тривиального окна и растёт содержанием вместе с T. -/
theorem frontPreservedUntil_zero (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) :
    FrontPreservedUntil lam d a J ρ κ m 0 :=
  fun _ ht ht0 => absurd ht0 (not_lt.mpr ht)

/-- **Антитонность по окну.** Сохранение до большего времени влечёт сохранение до меньшего:
    окна вложены. Формальная связка (сужение квантора), оплачена `lt_of_lt_of_le`. -/
theorem frontPreservedUntil_mono {lam : ℝ} {d : ℕ → ℝ} {a : ℕ → ℝ → ℝ}
    {J : ℕ} {ρ κ m : ℝ} {T T' : ℝ} (hTT' : T ≤ T')
    (h : FrontPreservedUntil lam d a J ρ κ m T') :
    FrontPreservedUntil lam d a J ρ κ m T :=
  fun t ht htT => h t ht (lt_of_lt_of_le htT hTT')

/-- **МОСТ: «навсегда» ⟺ «до любого T».** Красный вход `FrontPreservedForever` равносилен
    семейству всех своих T-относительных близнецов.
    ЧЕСТНОСТЬ: это ФОРМАЛЬНАЯ СВЯЗКА, оплаченная чистой логикой кванторов (в обратную сторону —
    инстанцирование `T := t+1`), а НЕ аналитикой. Она НЕ закрывает красный вход, но точно
    локализует его: открытым остаётся именно РАВНОМЕРНОЕ ПО T удержание инварианта, тогда как
    каждое конечное окно — предмет §2 (обитаемость) и §3 (MVT-шаг). -/
theorem frontPreservedForever_iff_forall_until (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ)
    (J : ℕ) (ρ κ m : ℝ) :
    FrontPreservedForever lam d a J ρ κ m ↔
      ∀ T : ℝ, FrontPreservedUntil lam d a J ρ κ m T := by
  constructor
  · intro h T t ht _
    exact h t ht
  · intro h t ht
    exact h (t + 1) t ht (by linarith)

#print axioms FrontPreservedUntil
#print axioms frontPreservedUntil_zero
#print axioms frontPreservedUntil_mono
#print axioms frontPreservedForever_iff_forall_until

/-! ### §2. Обитаемость: самоподобный профиль живёт в T-относительной форме и НЕ живёт в вечной

CORR-исправление отчёта выполнено дословно: `ssMode_frontDomination` даёт t-ЗАВИСИМОЕ
`m = a_{J+1}(t)`, а верный близнец `FrontPreservedForever` требует ФИКСИРОВАННОГО `m`.
Фиксация `m₀ := β_{J+1}/T` оплачивается монотонностью `g(t) = (T−t)⁻¹` на `[0,T)` при `0 < T`. -/

/-- **АНТИ-ВАКУУМНЫЙ СВИДЕТЕЛЬ (🟢): самоподобный профиль обитает в T-относительной форме.**

Профиль §2bis `ssMode` (тот самый, который РЕАЛЬНО взрывается в момент `T`) удовлетворяет
`FrontPreservedUntil T` на всём интервале жизни `[0,T)` с `ρ = 1`, `κ = 1` и ФИКСИРОВАННОЙ
нижней границей `m₀ := β_{J+1}/T`. Оплата фиксации: `a_{J+1}(t) = β_{J+1}·(T−t)⁻¹`, а
`(T−t)⁻¹ ≥ T⁻¹` на `[0,T)` (`inv_anti₀`), поэтому `m₀ = β_{J+1}·T⁻¹` — честная нижняя грань.
Это усиление не-вакуумности §2ter с ТОЧЕЧНОЙ (`ssMode_frontDomination` при фиксированном `t`)
до ИНТЕРВАЛЬНОЙ. НЕ утверждается сохранение за пределами жизни профиля — см. контраст ниже. -/
theorem ssMode_frontPreservedUntil {lam T : ℝ} (hlam : 1 < lam) (hT : 0 < T) (J : ℕ) :
    FrontPreservedUntil lam (fun _ => 0) (ssMode lam T) J 1 1 (ssBeta lam (J+1) / T) T := by
  intro t ht htT
  have hb : 0 < ssBeta lam (J+1) := ssBeta_pos hlam (J+1)
  have hm0 : 0 < ssBeta lam (J+1) / T := div_pos hb hT
  -- t-зависимые компоненты порядка трёх мод — из точечной не-вакуумности §2ter.
  obtain ⟨_, _, hρle, hκle, hκ⟩ := ssMode_frontDomination hlam J htT
  -- Фиксация нижней границы: `β_{J+1}/T ≤ β_{J+1}·(T−t)⁻¹`, т.к. `(T−t)⁻¹ ≥ T⁻¹` на `[0,T)`.
  have hTt : 0 < T - t := by linarith
  have hinv : T⁻¹ ≤ (T - t)⁻¹ := inv_anti₀ hTt (by linarith)
  have hmle : ssBeta lam (J+1) / T ≤ ssMode lam T (J+1) t := by
    simp only [ssMode, ssG, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hb.le
  exact ⟨hm0, hmle, hρle, hκle, hκ⟩

/-- **КОНТРАСТ (🟢): тот же свидетель НЕ живёт в «навсегда» — разрыв форм обитаем.**

Самоподобный профиль с той же фиксированной границей `m₀ = β_{J+1}/T` НЕ удовлетворяет
`FrontPreservedForever`: в момент `t = T` амплитуда `a_{J+1}(T) = β_{J+1}·(T−T)⁻¹` обнуляется
(Lean-конвенция `0⁻¹ = 0`), и требование `m₀ ≤ a_{J+1}(T)` рушится о `m₀ > 0`. Вместе с
`ssMode_frontPreservedUntil` это МАШИННО фиксирует: T-относительная форма СТРОГО слабее
красного входа — их разность обитаема, и никакая словесная склейка «до T» с «навсегда»
не пройдёт мимо этой пары теорем. -/
theorem ssMode_not_frontPreservedForever {lam T : ℝ} (hlam : 1 < lam) (hT : 0 < T) (J : ℕ) :
    ¬ FrontPreservedForever lam (fun _ => 0) (ssMode lam T) J 1 1 (ssBeta lam (J+1) / T) := by
  intro h
  obtain ⟨_, hmle, _, _, _⟩ := h T hT.le
  have hzero : ssMode lam T (J+1) T = 0 := by
    simp [ssMode, ssG, sub_self]
  rw [hzero] at hmle
  have hm0 : 0 < ssBeta lam (J+1) / T := div_pos (ssBeta_pos hlam (J+1)) hT
  linarith

#print axioms ssMode_frontPreservedUntil
#print axioms ssMode_not_frontPreservedForever

/-! ### §3. Конечно-оконный MVT-шаг сохранения инварианта

В §2ter этот шаг был анонсирован и СОЗНАТЕЛЬНО ОПУЩЕН («конечно-оконное сохранение через
MVT-оценки границ возможно при названной локальной гипотезе непересечения»). Здесь он ЗАКРЫТ:
из строгого запаса `δ` в начальный момент и скоростных границ `C` трёх зазоров фронта на окне
инвариант удерживается на `[t₀, t₀+ε]` при `C·ε ≤ δ`. Скоростные границы — ИМЕНОВАННЫЙ
ЛОКАЛЬНЫЙ ВХОД (оконная форма «гипотезы непересечения»); MVT-оценку поставляет mathlib
(`norm_image_sub_le_of_norm_deriv_le_segment'`), производные — динамика КП. Шаг ЛОКАЛЕН:
итерация до `[0,∞)` потребовала бы равномерных `δ`, `C` при движущемся фронте — это и есть
открытый фронтир, который здесь НЕ закрывается. -/

/-- **MVT-ядро шага (🟢): нижняя граница с запасом переживает окно при ограниченной скорости.**

Если `f` дифференцируема на `[t₀, t₀+ε]` со скоростью, ограниченной `C` по норме, стартует
с запасом `c + δ ≤ f(t₀)` и `C·ε ≤ δ`, то `c ≤ f(t)` на всём окне. Оплата — односторонняя
MVT-оценка mathlib `norm_image_sub_le_of_norm_deriv_le_segment'`:
`|f(t) − f(t₀)| ≤ C·(t−t₀) ≤ C·ε ≤ δ`, и запас поглощает дрейф. Неотрицательность `C`
выводится из самой границы скорости в `t₀` (норма неотрицательна). -/
theorem lowerBound_persists_of_deriv_bound
    {f f' : ℝ → ℝ} {t0 ε C δ c : ℝ}
    (hε : 0 < ε) (hCε : C * ε ≤ δ)
    (hf : ∀ x ∈ Set.Icc t0 (t0 + ε), HasDerivWithinAt f (f' x) (Set.Icc t0 (t0 + ε)) x)
    (hbound : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖f' x‖ ≤ C)
    (hinit : c + δ ≤ f t0) :
    ∀ t ∈ Set.Icc t0 (t0 + ε), c ≤ f t := by
  intro t ht
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hbound t0 ⟨le_refl t0, by linarith⟩)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound t ht
  have habs : |f t - f t0| ≤ C * (t - t0) := by
    simpa [Real.norm_eq_abs] using hmvt
  have hup : C * (t - t0) ≤ C * ε :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1, ht.2]) hC0
  have hlow := (abs_le.mp habs).1
  linarith

/-- **КОНЕЧНО-ОКОННОЕ СОХРАНЕНИЕ `FrontDomination` (🟢, MVT-шаг §2ter — закрыт).**

Если в момент `t₀` инвариант доминирования фронта выполнен со СТРОГИМ ЗАПАСОМ `δ` по всем трём
зазорам (`m + δ ≤ a_{J+1}`, `ρ·a_{J+1} + δ ≤ a_J`, `a_{J+2} + δ ≤ κ·a_{J+1}`), динамика — НАСТОЯЩИЕ
ОДУ КП (`HasDerivAt`-кирпичи `DyadicBlowup`), и скорости трёх зазоров ограничены `C` на окне
(ИМЕНОВАННЫЙ ЛОКАЛЬНЫЙ ВХОД — оконная «гипотеза непересечения» §2ter: `‖kpRHS(J+1)‖ ≤ C`,
`‖kpRHS(J) − ρ·kpRHS(J+1)‖ ≤ C`, `‖κ·kpRHS(J+1) − kpRHS(J+2)‖ ≤ C`), то при `C·ε ≤ δ`
инвариант держится на ВСЁМ `[t₀, t₀+ε]`.

ЧЕСТНОСТЬ: шаг ЛОКАЛЕН и НЕ закрывает `FrontPreservedForever` — при движущемся фронте
бесконечного каскада равномерное по времени удержание запаса `δ` и границы `C` есть существо
открытой трудности (Barbato–Morandin–Romito, Cheskidov, Kiselev–Zlatoš); диссипация `d` в этом
шаге не обязана быть неотрицательной — знак нужен лишь выводу драйва (`frontDrive_of_invariant`),
а не удержанию окна. -/
theorem frontDomination_persists_on_window
    (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (J : ℕ) (ρ κ m : ℝ)
    (t0 ε δ C : ℝ)
    (ht0 : 0 ≤ t0) (hε : 0 < ε) (hCε : C * ε ≤ δ)
    (hm : 0 < m) (hκ0 : 0 ≤ κ)
    (dynamics : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s => a n s) (kpRHS lam d a n t) t)
    (hgap1 : m + δ ≤ a (J+1) t0)
    (hgap2 : ρ * a (J+1) t0 + δ ≤ a J t0)
    (hgap3 : a (J+2) t0 + δ ≤ κ * a (J+1) t0)
    (hb1 : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖kpRHS lam d a (J+1) x‖ ≤ C)
    (hb2 : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖kpRHS lam d a J x - ρ * kpRHS lam d a (J+1) x‖ ≤ C)
    (hb3 : ∀ x ∈ Set.Ico t0 (t0 + ε), ‖κ * kpRHS lam d a (J+1) x - kpRHS lam d a (J+2) x‖ ≤ C) :
    ∀ t ∈ Set.Icc t0 (t0 + ε), FrontDomination lam d a J ρ κ m t := by
  -- Все точки окна лежат в области динамики `[0,∞)`.
  have hx0 : ∀ x ∈ Set.Icc t0 (t0 + ε), (0:ℝ) ≤ x := fun x hx => le_trans ht0 hx.1
  -- Зазор 1: ведущая мода держится над фиксированным `m`.
  have hpers1 : ∀ t ∈ Set.Icc t0 (t0 + ε), m ≤ a (J+1) t := by
    refine lowerBound_persists_of_deriv_bound
      (f := fun s => a (J+1) s)
      (f' := fun x => kpRHS lam d a (J+1) x)
      (c := m) hε hCε ?_ hb1 hgap1
    intro x hx
    exact (dynamics (J+1) x (hx0 x hx)).hasDerivWithinAt
  -- Зазор 2: подпитка притока снизу (`ρ·a_{J+1} ≤ a_J`).
  have hpers2 : ∀ t ∈ Set.Icc t0 (t0 + ε), (0:ℝ) ≤ a J t - ρ * a (J+1) t := by
    refine lowerBound_persists_of_deriv_bound
      (f := fun s => a J s - ρ * a (J+1) s)
      (f' := fun x => kpRHS lam d a J x - ρ * kpRHS lam d a (J+1) x)
      (c := 0) hε hCε ?_ hb2
      (by show (0:ℝ) + δ ≤ a J t0 - ρ * a (J+1) t0; linarith)
    intro x hx
    exact ((dynamics J x (hx0 x hx)).sub
      ((dynamics (J+1) x (hx0 x hx)).const_mul ρ)).hasDerivWithinAt
  -- Зазор 3: контроль оттока вверх (`a_{J+2} ≤ κ·a_{J+1}`).
  have hpers3 : ∀ t ∈ Set.Icc t0 (t0 + ε), (0:ℝ) ≤ κ * a (J+1) t - a (J+2) t := by
    refine lowerBound_persists_of_deriv_bound
      (f := fun s => κ * a (J+1) s - a (J+2) s)
      (f' := fun x => κ * kpRHS lam d a (J+1) x - kpRHS lam d a (J+2) x)
      (c := 0) hε hCε ?_ hb3
      (by show (0:ℝ) + δ ≤ κ * a (J+1) t0 - a (J+2) t0; linarith)
    intro x hx
    exact (((dynamics (J+1) x (hx0 x hx)).const_mul κ).sub
      (dynamics (J+2) x (hx0 x hx))).hasDerivWithinAt
  -- Сборка инварианта из трёх удержанных зазоров.
  intro t ht
  refine ⟨hm, hpers1 t ht, ?_, ?_, hκ0⟩
  · have := hpers2 t ht
    linarith
  · have := hpers3 t ht
    linarith

/-- **Королларий: MVT-шаг из нуля производит обитателя T-относительной формы.**
Те же гипотезы при `t₀ = 0` дают `FrontPreservedUntil` на окне `ε` — конечно-оконное
сохранение и T-относительный близнец §1 стыкуются буквально. Формальная связка
(переупаковка `Icc`-заключения в `[0,ε)`-форму), оплачена `zero_add`. -/
theorem frontPreservedUntil_of_deriv_bound
    (lam : ℝ) (d : ℕ → ℝ) (a : ℕ → ℝ → ℝ) (J : ℕ) (ρ κ m : ℝ)
    (ε δ C : ℝ)
    (hε : 0 < ε) (hCε : C * ε ≤ δ)
    (hm : 0 < m) (hκ0 : 0 ≤ κ)
    (dynamics : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s => a n s) (kpRHS lam d a n t) t)
    (hgap1 : m + δ ≤ a (J+1) 0)
    (hgap2 : ρ * a (J+1) 0 + δ ≤ a J 0)
    (hgap3 : a (J+2) 0 + δ ≤ κ * a (J+1) 0)
    (hb1 : ∀ x ∈ Set.Ico (0:ℝ) ε, ‖kpRHS lam d a (J+1) x‖ ≤ C)
    (hb2 : ∀ x ∈ Set.Ico (0:ℝ) ε, ‖kpRHS lam d a J x - ρ * kpRHS lam d a (J+1) x‖ ≤ C)
    (hb3 : ∀ x ∈ Set.Ico (0:ℝ) ε, ‖κ * kpRHS lam d a (J+1) x - kpRHS lam d a (J+2) x‖ ≤ C) :
    FrontPreservedUntil lam d a J ρ κ m ε := by
  intro t ht htε
  have hwin := frontDomination_persists_on_window lam d a J ρ κ m 0 ε δ C
    le_rfl hε hCε hm hκ0 dynamics hgap1 hgap2 hgap3
    (fun x hx => hb1 x (by rwa [zero_add] at hx))
    (fun x hx => hb2 x (by rwa [zero_add] at hx))
    (fun x hx => hb3 x (by rwa [zero_add] at hx))
  exact hwin t ⟨ht, by rw [zero_add]; exact le_of_lt htε⟩

/-! #### Не-вакуумность MVT-шага: стационарный свидетель

Гипотезы окна СОВМЕСТНЫ: стационарный каскад (все амплитуды `≡ 1`, диссипация подобрана так,
что `kpRHS ≡ 0`) удовлетворяет им с `C = 0`. ЧЕСТНОСТЬ: динамика свидетеля тривиальна (нулевые
скорости) — он подтверждает лишь, что MVT-шаг не пусто-истинен, а НЕ моделирует движущийся фронт. -/

/-- Диссипация стационарного свидетеля: подобрана так, что `kpRHS 2 steadyD (≡1) n t = 0`
    (у оболочки `n` приток `[n=0 ? 0 : 2ⁿ]` и отток `2ⁿ⁺¹` при единичных амплитудах).
    ЧЕСТНОСТЬ: `steadyD n < 0` при всех `n` — это НЕ физическая диссипация, а ПОДКАЧКА энергии,
    компенсирующая чистый отток; окно §3 знака `d` не требует (см. докстроку теоремы),
    но свидетель с `d ≥ 0` был бы дороже. -/
def steadyD (n : ℕ) : ℝ := (if n = 0 then 0 else (2:ℝ) ^ n) - 2 ^ (n + 1)

/-- Правая часть КП на стационарном свидетеле тождественно нулевая. -/
theorem steady_kpRHS_zero (n : ℕ) (t : ℝ) :
    kpRHS 2 steadyD (fun _ _ => (1:ℝ)) n t = 0 := by
  cases n with
  | zero => simp [kpRHS, kpInflow, kpOutflow, steadyD]
  | succ k =>
    simp only [kpRHS, kpInflow, kpOutflow, steadyD, Nat.succ_ne_zero, if_false]
    ring

/-- **Не-вакуумность MVT-шага (🟢):** гипотезы `frontDomination_persists_on_window` совместны —
    стационарный свидетель проходит их с `J = 1`, `ρ = 1/2`, `κ = 2`, `m = 1/2`, `δ = 1/4`,
    `C = 0`, `ε = 1`, и инвариант держится на всём `[0,1]`. ЧЕСТНОСТЬ: скорости нулевые —
    свидетель совместности, а не движущийся фронт. -/
theorem frontWindow_realizable :
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      FrontDomination 2 steadyD (fun _ _ => (1:ℝ)) 1 (1/2) 2 (1/2) t := by
  have h := frontDomination_persists_on_window 2 steadyD (fun _ _ => (1:ℝ)) 1
    (1/2) 2 (1/2) 0 1 (1/4) 0
    le_rfl one_pos (by norm_num) (by norm_num) (by norm_num)
    (fun n t _ => by
      have hz := steady_kpRHS_zero n t
      rw [hz]
      exact hasDerivAt_const t 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun x _ => by simp [steady_kpRHS_zero])
    (fun x _ => by simp [steady_kpRHS_zero])
    (fun x _ => by simp [steady_kpRHS_zero])
  intro t ht
  exact h t (by simpa using ht)

#print axioms lowerBound_persists_of_deriv_bound
#print axioms steadyD
#print axioms frontDomination_persists_on_window
#print axioms frontPreservedUntil_of_deriv_bound
#print axioms steady_kpRHS_zero
#print axioms frontWindow_realizable

/-! ### §4. Итог и аудит аксиом

Красный вход `FrontPreservedForever` ЧЕСТНО СУЖЕН, но НЕ закрыт: (1) T-относительный близнец
`FrontPreservedUntil` назван и мостом связан с «навсегда» (чистая логика кванторов);
(2) близнец обитаем взрывающимся профилем на всём интервале жизни с фиксированной нижней
границей (монотонность `g`), и разрыв с «навсегда» обитаем машинно; (3) сознательно опущенный
в §2ter конечно-оконный MVT-шаг закрыт mathlib-оценкой при именованном локальном входе
(скоростные границы зазоров) и не-вакуумен. Открытым остаётся ровно то, что и было существом
трудности: РАВНОМЕРНОЕ по времени удержание запаса при движущемся фронте бесконечного каскада.
Ни sorry, ни новых аксиом, ни native_decide; карантин не импортирован. -/

end EuclidsPath.DyadicFrontWindow
