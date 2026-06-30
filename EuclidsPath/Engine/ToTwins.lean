/-
  Капстоун: цепь до близнецов из реального four-corner. Проза: prose/21_ToTwins.md.

  Собирает в ОДНУ машинно-проверенную цепь все верифицированные звенья:
    real four-corner + side-corner  --(N33_lt_N00_of_four_corner)-->  N₃₃ < N₀₀
      --(survivor_of_not_covered)-->  выживший carrier-центр
      --(survivor ⟹ twin)-->  twin-центр выше N
      --(infinite_of_unbounded_centers)-->  TwinLowers.Infinite (гипотеза близнецов).

  Открытым входом `H` остаётся РОВНО ОДНО: что РЕАЛЬНЫЕ ранговые счёты удовлетворяют four-corner
  `R₀₀·R₃₃ < R₀₃·R₃₀` (+ лёгкий side-corner) на сколь угодно больших масштабах, и что выживший —
  twin. Модельный four-corner уже доказан (`ModelFourCorner`); остаётся перенос модель→реальность.
  Здесь НЕТ `sorry`: это честная условная теорема (гипотеза ⟸ явный вход `H`).
-/
import EuclidsPath.Engine.FourCorner
import EuclidsPath.Engine.TwoTransport

set_option autoImplicit false

namespace EuclidsPath

/--
  **Гипотеза близнецов из реального four-corner.** Если на каждом масштабе `N` найдётся блок, где
  реальные ранговые счёты дают строгий four-corner и side-corner (значит `N₃₃ < N₀₀`), carrier лежит
  выше `N`, а каждый выживший — twin-центр, то простых-близнецов бесконечно много.
-/
theorem twin_primes_of_four_corner
    (H : ∀ N : ℕ, ∃ (R00 R03 R30 R33 carrier bad : Finset ℕ),
        0 < R00.card ∧
        R00.card * R33.card < R03.card * R30.card ∧        -- four-corner (реальный)
        R03.card * R30.card ≤ R00.card * R00.card ∧        -- side-corner (реальный, лёгкий)
        carrier.card = R00.card ∧ bad.card = R33.card ∧    -- carrier = ранг-(0,0), bad = ранг-(3,3)
        (∀ m ∈ carrier, N < m) ∧
        (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)) :
    TwinLowers.Infinite := by
  apply twin_prime_conjecture_of_blocks
  intro N
  obtain ⟨R00, R03, R30, R33, carrier, bad, hpos, hfc, hsc, hcc, hbc, habove, htwin⟩ := H N
  have h33 : R33.card < R00.card := N33_lt_N00_of_four_corner hpos hfc hsc
  refine ⟨carrier, bad, habove, ?_, htwin⟩
  rw [hbc, hcc]; exact h33

end EuclidsPath
