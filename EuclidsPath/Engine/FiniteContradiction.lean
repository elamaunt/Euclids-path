/-
  Доказательство ОТ ПРОТИВНОГО: «близнецов конечно» + четырёхугольник `H` ⟹ `False`.
  Проза: prose/25_FiniteContradiction.md.

  Это контрапозиция всей программы. Многоагентная разведка (3 независимых маршрута —
  counting / EPMI / four-corner) дала ОДИН честный вывод: предположение конечности близнецов
  замыкается в противоречие с двигателем РОВНО через тот же открытый вход, что и прямая линия —
  строгий РЕАЛЬНЫЙ four-corner на масштабах + carrier. Ни один маршрут не обходит стену:
    * counting-маршрут дохнет на Мертенсе (`Σ 1/p → ∞`, union bound не бьёт carrier;
      починка = Brun + Bombieri–Vinogradov = распределение = красная линия);
    * EPMI-маршрут инвертирует бремя (чтобы применить `no_infinite_descent`, надо ИЗГОТОВИТЬ
      бесконечную цепь спуска — а её нет; «покрытие тотально» — это то, что надо опровергнуть);
    * four-corner-маршрут — чистейший: вся редукция `finite ⟹ False` уже машинно проверена,
      открытое изолировано в ОДНУ типизированную гипотезу `H`.

  Здесь фиксируется ИМЕННО это: честная УСЛОВНАЯ теорема `finite ∧ H ⟹ False`, без `sorry`
  (`H` — явная гипотеза, а не `sorry`). Содержательное открытое — конъюнкт «строгий реальный
  four-corner» в `H` (= проблема чётности / перенос модель→реальность). Модельная сторона
  (`four_corner_binom_strict`, `model_four_corner`) уже доказана безусловно.
-/
import EuclidsPath.Engine.ToTwins

set_option autoImplicit false

namespace EuclidsPath

/-- Единственный открытый вход — ДОСЛОВНО гипотеза `twin_primes_of_four_corner` (ToTwins.lean).
    Содержательно открыт конъюнкт 2 (строгий РЕАЛЬНЫЙ four-corner на настоящих ранговых счётах). -/
abbrev FourCornerInput : Prop :=
  ∀ N : ℕ, ∃ (R00 R03 R30 R33 carrier bad : Finset ℕ),
      0 < R00.card ∧
      R00.card * R33.card < R03.card * R30.card ∧
      R03.card * R30.card ≤ R00.card * R00.card ∧
      carrier.card = R00.card ∧ bad.card = R33.card ∧
      (∀ m ∈ carrier, N < m) ∧
      (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)

/--
  **«Близнецов конечно» противоречиво (по модулю `H`).** Если множество twin-пар КОНЕЧНО
  (`¬ TwinLowers.Infinite`) и выполнен четырёхугольный вход `H`, то `False`. Чисто: каждый шаг —
  машинно проверенная лемма; единственное открытое — `H`. (Контрапозиция: `H ⟹` бесконечность.)
-/
theorem twin_finite_contradiction
    (hfin : ¬ TwinLowers.Infinite) (H : FourCornerInput) : False :=
  hfin (twin_primes_of_four_corner H)

/-- То же явно через `TwinLowers.Finite` (= `¬ Infinite` для множеств). -/
theorem twin_finite_contradiction_of_finite
    (hfin : TwinLowers.Finite) (H : FourCornerInput) : False :=
  (Set.not_infinite.mpr hfin) (twin_primes_of_four_corner H)

/-- Контрапозиция-вывод: четырёхугольник опровергает конечность ⟹ близнецов бесконечно. -/
theorem twin_infinite_of_fourCorner (H : FourCornerInput) : TwinLowers.Infinite :=
  twin_primes_of_four_corner H

end EuclidsPath
