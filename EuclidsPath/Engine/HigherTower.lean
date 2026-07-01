/-
  HigherTower — Euclidean Tower / BadTower: движок как инверсный предел совместимых конечных теней.
  Источник: higher_energy_incompatibility_full_formal_ru_2026-07-01.md (Euclidean Tower / BadTower).
  Проза: prose/24_BoundaryDecomp.md (раздел «Euclidean Tower»).

  ИДЕЯ. Не конечный двигатель едет через ∞ уровней, а САМ двигатель — бесконечная совместимая башня
  конечных теней: уровень `A` даёт тень `State A`, restriction `B→A` (A≤B) забывает информацию, а
  башня — совместимый выбор `(state A)` с `restrict (state B) = state A`.

  ГЛАВНЫЙ АРИФМЕТИЧЕСКИЙ ФАКТ (реальный, НЕ counting, доказан). Центр `m`, чистый на ВСЕХ уровнях
  (`∀ A, CleanZ A m`), не может иметь стороны `≥ 2`: чистота-навсегда запрещает ЛЮБОЙ простой делитель
  сторон (`allClean_forces_no_prime_divisor` — взять `A = q`), а число `≥ 2` имеет простой делитель
  (`minFac`). Это конечность множества простых делителей, а не плотность.

  ЧЕСТНАЯ ГРАНИЦА (ключевая, вскрыта при формализации). Из этого следует, что fixed-center BadTower
  ВАКУУМЕН: поля `clean` (⟹ `∀A CleanZ`) и `side_gt` (стороны `≥ 2`) ВЗАИМНО ПРОТИВОРЕЧИВЫ, поэтому
  `no_badTower` доказан, но по ВЫРОЖДЕННОЙ причине — башни не существует не потому что «clean-forever ⟹
  twin», а потому что «clean-forever ⟹ side ≤ 1» против `side ≥ 2`. Кирпич сам подозревал (§16), что
  fixed-center «too strong»; здесь причина РЕЗЧЕ. (Задуманная кирпичом лемма «clean-for-all-A ⟹ twin»
  НЕ определена в коде — она формально верна, но её гипотеза НЕВЫПОЛНИМА для сторон `≥ 2`, так что «twin»
  выводился бы вакуумно; мы её не вводим, а доказываем прямую причину `allClean_forces_side_le_one`.)

  ЧТО ОСТАЁТСЯ (§17–19 кирпича — НЕ доказано, вероятно та же стена): реальная надежда — moving-center
  relational tower (`RelTower`), где `center` МЕНЯЕТСЯ с `A` (`m_A → ∞`), и теорема
  `relTower_stabilizes_or_forces_twin`. Но без стабилизации/cross-level collision башня из движущихся
  центров — это снова orientation/carrier стена (спуск даёт всё новые clean non-twin центры). Здесь
  moving-часть — ВХОД. `Step00` остаётся `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.HigherTower

open EuclidsPath.Residuals

/-! ### §2–3. Главный арифметический факт: чистота-навсегда ⟹ нет простого делителя ⟹ side ≤ 1 -/

/--
  **`allClean_forces_no_prime_divisor` — ДОКАЗАНА.** Если `m` чист на всех уровнях (`∀ A, CleanZ A m`),
  то НИ ОДИН простой `q` не делит сторону `6m+1`. Механизм: взять уровень `A = q`; `CleanZ q m`
  запрещает `q ∣ (6m±1)`. Это конечность простых делителей, не плотность. -/
theorem allClean_forces_no_prime_divisor {m : ℕ} (hAll : ∀ A, CleanZ A (m : ℤ)) :
    ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ (6 * (m : ℤ) + 1) :=
  fun q hq hdvd => (hAll q) q hq (le_refl q) (Or.inr hdvd)

/-- То же для стороны `6m−1`. -/
theorem allClean_forces_no_prime_divisor_minus {m : ℕ} (hAll : ∀ A, CleanZ A (m : ℤ)) :
    ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ (6 * (m : ℤ) - 1) :=
  fun q hq hdvd => (hAll q) q hq (le_refl q) (Or.inl hdvd)

/--
  **`allClean_forces_side_le_one` — ДОКАЗАНА (вскрывает вакуумность башни).** Если `∀ A, CleanZ A m`,
  то сторона `6m+1 ≤ 1` (т.е. `6m+1` НЕ может быть `≥ 2`). Иначе `minFac` — простой делитель, что
  запрещено. Следствие: гипотеза «чист на всех уровнях» НЕСОВМЕСТИМА со стороной `≥ 2`. -/
theorem allClean_forces_side_le_one {m : ℕ} (hAll : ∀ A, CleanZ A (m : ℤ)) :
    ¬ (2 ≤ 6 * m + 1) := by
  intro hge
  have hp : (6 * m + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hd : (6 * m + 1).minFac ∣ (6 * m + 1) := Nat.minFac_dvd _
  have hdZ : ((6 * m + 1).minFac : ℤ) ∣ (6 * (m : ℤ) + 1) := by
    have hcast : ((6 * m + 1 : ℕ) : ℤ) = 6 * (m : ℤ) + 1 := by push_cast; ring
    rw [← hcast]; exact_mod_cast hd
  exact allClean_forces_no_prime_divisor hAll _ hp hdZ

/-! ### §5–6. Абстрактная система уровней и башня (инверсный предел) -/

/-- Система уровней: тень `State A` на каждом уровне + restriction `B→A` с законами инверсной системы. -/
structure LevelSystem where
  State : ℕ → Type
  restrict : ∀ {A B : ℕ}, A ≤ B → State B → State A
  restrict_id : ∀ A (x : State A), restrict (le_refl A) x = x
  restrict_comp : ∀ {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (x : State C),
    restrict hAB (restrict hBC x) = restrict (le_trans hAB hBC) x

/-- Башня: совместимый выбор состояния на каждом уровне (элемент инверсного предела). -/
structure Tower (S : LevelSystem) where
  state : ∀ A, S.State A
  compat : ∀ {A B : ℕ} (hAB : A ≤ B), S.restrict hAB (state B) = state A

/-! ### §7–11. Fixed-center BadState и BadTower

`BadState A` — центр, чистый на уровне `A`, со сторонами `≥ 2` и НЕ twin. Restriction сохраняет center
(и роняет уровень чистоты через `CleanZ`-монотонность). -/

/-- Fixed-center bad-state: чистый на уровне `A`, стороны `≥ 2`, не twin. -/
structure BadState (A : ℕ) where
  center : ℕ
  clean : CleanZ A (center : ℤ)
  side_lo : 2 ≤ 6 * center - 1
  side_hi : 2 ≤ 6 * center + 1
  bad : ¬ TwinCenterZ center

/-- `CleanZ` монотонна вниз: `A ≤ B`, `CleanZ B m` ⟹ `CleanZ A m` (меньше запретов). -/
theorem cleanZ_mono_down {A B : ℕ} {m : ℤ} (hAB : A ≤ B) (hB : CleanZ B m) : CleanZ A m :=
  fun q hq hqA => hB q hq (le_trans hqA hAB)

/-- Restriction для BadState: тот же center, чистота на меньшем уровне. -/
def badRestrict {A B : ℕ} (hAB : A ≤ B) (x : BadState B) : BadState A where
  center := x.center
  clean := cleanZ_mono_down hAB x.clean
  side_lo := x.side_lo
  side_hi := x.side_hi
  bad := x.bad

/-- Система уровней bad-state (fixed-center). -/
def BadLevelSystem : LevelSystem where
  State := fun A => BadState A
  restrict := fun {A B} hAB x => badRestrict hAB x
  restrict_id := by intro A x; rfl
  restrict_comp := by intro A B C hAB hBC x; rfl

/-- Fixed-center BadTower. -/
def BadTower : Type := Tower BadLevelSystem

/-! ### §12–14. Извлечение fixed center и невозможность башни (ВАКУУМНАЯ) -/

/-- **`badTower_center_const` — ДОКАЗАНА.** В fixed-center башне center постоянен на всех уровнях
    (`badRestrict` сохраняет center; совместимость даёт равенство). -/
theorem badTower_center_const (T : BadTower) : ∀ A, (T.state A).center = (T.state 0).center := by
  intro A
  have hc := T.compat (Nat.zero_le A)
  -- badRestrict сохраняет center, значит (state 0).center = (state A).center
  have hcc : (badRestrict (Nat.zero_le A) (T.state A)).center = (T.state 0).center :=
    congrArg BadState.center hc
  -- badRestrict сохраняет center: LHS = (state A).center
  simpa [badRestrict] using hcc

/--
  **`badState_inhabited_single_level` — ДОКАЗАНА (вакуумность именно у ∞-башни, не у теней).** На
  ОТДЕЛЬНОМ уровне bad-state существует: центр `4` (сторона `23` простая, `25 = 5²` — нет ⟹ не twin),
  clean на уровне `1` тривиально (нет простых `≤ 1`), стороны `≥ 2`. Значит пустота — свойство именно
  ИНВЕРСНОГО ПРЕДЕЛА (совместимость по ВСЕМ уровням фиксирует один центр «чистым навсегда»), а не
  каждой конечной тени. Это делает вырожденность `no_badTower` точной. -/
theorem badState_inhabited_single_level : Nonempty (BadState 1) := by
  refine ⟨{ center := 4, clean := ?_, side_lo := by norm_num, side_hi := by norm_num, bad := ?_ }⟩
  · intro q hq hq1
    interval_cases q <;> simp_all [Nat.Prime]
  · intro htwin
    have := htwin.2
    norm_num [Nat.Prime] at this

/--
  **`no_badTower` — ДОКАЗАНА, но ВАКУУМНО (честная пометка).** Fixed-center BadTower не существует.
  ПРИЧИНА (вырожденная, вскрыта при формализации): у любого состояния башни `clean : CleanZ A center`
  на ВСЕХ уровнях даёт `∀A CleanZ`, а это запрещает стороне быть `≥ 2` (`allClean_forces_side_le_one`)
  — против поля `side_hi`. То есть противоречие НЕ «clean-forever ⟹ twin», а «clean-forever ⟹ side ≤ 1».
  `bad`-поле (не-twin) даже НЕ используется. Значит башня пуста по вырожденной причине, и этот no-go
  НЕ несёт twin-содержания. -/
theorem no_badTower : ¬ Nonempty (@BadTower) := by
  rintro ⟨T⟩
  -- state 0 clean на уровне 0; но нам нужен ∀A CleanZ на общем центре
  have hconst := badTower_center_const T
  set m := (T.state 0).center with hm
  have hAll : ∀ A, CleanZ A (m : ℤ) := by
    intro A
    have hcl : CleanZ A ((T.state A).center : ℤ) := (T.state A).clean
    rw [hconst A] at hcl
    exact hcl
  -- side_hi: 2 ≤ 6m+1, но allClean запрещает
  exact allClean_forces_side_le_one hAll (T.state 0).side_hi

/-! ### §15–16. Условная теорема + ЧЕСТНОЕ предупреждение о вакуумности

Кирпич (§15) даёт: если `NoTwinAbove N ⟹ Nonempty BadTower`, то `TwinAbove N`. Но т.к. `BadTower`
пуст ВАКУУМНО (не из-за twin), force-лемма `NoTwinAbove ⟹ Nonempty BadTower` требует построить
состояние с `∀A CleanZ ∧ side ≥ 2` — что НЕВОЗМОЖНО. Значит force-лемма ЛОЖНА (не «too strong», а
неверна), и условная теорема, хоть и валидна, опирается на ложную посылку. -/

/--
  **`twinAbove_of_badTower_forcing` — ДОКАЗАНА, но МЁРТВАЯ УСЛОВНАЯ (посылка недостижима).** Если `¬TwinAbove N`
  влечёт непустоту fixed-center BadTower, то `TwinAbove N`. Валидно логически (`no_badTower`), НО
  посылка `hForce` НЕДОСТИЖИМА: `Nonempty BadTower` ложно всегда (вакуумно), а вывести ложь из
  `¬TwinAbove` — значит доказать `TwinAbove` напрямую. Это НЕ путь. -/
theorem twinAbove_of_badTower_forcing {N : ℕ}
    (hForce : (¬ ∃ t, N < t ∧ TwinCenterZ t) → Nonempty (@BadTower)) :
    ∃ t, N < t ∧ TwinCenterZ t := by
  by_contra hNo
  exact no_badTower (hForce hNo)

/-! ### §17–19. Moving-center relational tower — реальный (недоказанный) target

Чтобы не встраивать цель, ослабляем башню: center МЕНЯЕТСЯ с уровнем (`m_A`), совместимость —
отношение, а не функция. Тогда невозможность НЕ автоматична: `m_A → ∞` даёт всё новые clean non-twin
центры, и без стабилизации/cross-level collision это снова orientation/carrier стена. -/

/-- Moving bad-state: те же поля, но center может меняться между уровнями. -/
structure MovingBadState (A : ℕ) where
  center : ℕ
  clean : CleanZ A (center : ℤ)
  side_hi : 2 ≤ 6 * center + 1
  bad : ¬ TwinCenterZ center

/-- Relational tower: состояния на каждом уровне + отношение совместимости (center не фиксирован). -/
structure RelTower (Compatible : ∀ {A B : ℕ}, A ≤ B → MovingBadState B → MovingBadState A → Prop) where
  state : ∀ A, MovingBadState A
  compat : ∀ {A B : ℕ} (hAB : A ≤ B), Compatible hAB (state B) (state A)

/--
  **`relTower_contradiction_yields_twin` — ДОКАЗАНА (условная упаковка §21).** Если `¬TwinAbove N`
  влечёт moving-tower, а moving-tower невозможна, то `TwinAbove N`. НО `hNoRelTower` (невозможность
  moving-башни) — это `relTower_stabilizes_or_forces_twin`, НЕ доказанная и, по §19, вероятно = та же
  orientation/carrier стена (движущиеся центры `m_A → ∞` не дают противоречия без стабилизации). -/
theorem relTower_contradiction_yields_twin {N : ℕ}
    {Compatible : ∀ {A B : ℕ}, A ≤ B → MovingBadState B → MovingBadState A → Prop}
    (hForce : (¬ ∃ t, N < t ∧ TwinCenterZ t) → Nonempty (RelTower @Compatible))
    (hNoRelTower : ¬ Nonempty (RelTower @Compatible)) :
    ∃ t, N < t ∧ TwinCenterZ t := by
  by_contra hNo
  exact hNoRelTower (hForce hNo)

end EuclidsPath.HigherTower
