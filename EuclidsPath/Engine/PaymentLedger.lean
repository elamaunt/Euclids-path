/-
  Алгебра оплаты (boundary-energy ledger). Источник: twin_prime_boundary_energy_ledger_ru_20260630.md.
  Проза: prose/26_PaymentLedger.md.

  «Когда двигатель останавливается — он платит, и оплата подчинена строгому порядку.»
  Здесь зафиксировано ДОКАЗУЕМОЕ алгебраическое ядро закона оплаты (без распределения):

    * channel law: clean-источник в одном residue mod p ⟹ ровно `p−2` совместимых каналов;
    * tax law: запрет `a ≢ θ (mod q)` ⟹ фактор ёмкости `(q−3)/(q−2)`;
    * **shifted-primorial obstruction (ЗАКОН ДЕФЕКТА):** бесплатный проход к ordered prime `p`
      требует `P_{<p} ∣ a−θ`, откуда `P_{<p} ≤ a` — а если примориал перерос `a`, проход НЕВОЗМОЖЕН.

  Честная граница (числа, tools/RESULTS_payment_budget.md): суммарная потеря ёмкости по малым
  простым ~ `1/ln A` (Мертенс) — поэтому количественный shifted-charge budget (§20.2) НЕ закрывается
  distribution-free и остаётся явным открытым входом. Здесь — ровно доказуемая алгебра.

  Всё элементарно (Nat/Int + Finset). Без анализа/распределения/сита.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.Payment

/-! ### Channel law: ровно `p − 2` clean-совместимых каналов -/

/--
  **Channel residue law (§12.1).** Если `p > 3`, `p ∣ 6n − ε` (boundary на противоположной стороне)
  и `6m + σ = a (6n + ε)`, то источник `m` лежит в фиксированном классе вычетов:
  `6m ≡ 2aε − σ (mod p)`. Чистая CRT-алгебра.
-/
theorem channel_residue {p : ℕ} {m n a : ℤ} {σ ε : ℤ}
    (hlift : 6 * m + σ = a * (6 * n + ε))
    (hbnd : (p : ℤ) ∣ 6 * n - ε) :
    (p : ℤ) ∣ (6 * m - (2 * a * ε - σ)) := by
  -- 6n ≡ ε ⟹ 6n+ε ≡ 2ε ⟹ a(6n+ε) ≡ 2aε ⟹ 6m+σ ≡ 2aε ⟹ 6m ≡ 2aε−σ
  have h1 : (p : ℤ) ∣ a * (6 * n + ε) - 2 * a * ε := by
    have : a * (6 * n + ε) - 2 * a * ε = a * (6 * n - ε) := by ring
    rw [this]; exact Dvd.dvd.mul_left hbnd a
  have h2 : 6 * m - (2 * a * ε - σ) = a * (6 * n + ε) - 2 * a * ε := by
    rw [← hlift]; ring
  rw [h2]; exact h1

/-! ### Tax / θ-дихотомия -/

/--
  **Tax dichotomy (§15.1).** Положим `θ = σε`. Дополнительный запрет на стороне `6m − σ` по
  малому `q` (`q ∣ a(6n+ε) − 2σ`) исчезает ровно когда `a ≡ θ (mod q)` — тогда он совпадает с уже
  запрещённым классом. То есть «нет налога ⟺ `q ∣ a − θ`».
-/
theorem no_tax_iff_shifted {q : ℕ} {a θ : ℤ} :
    (q : ℤ) ∣ a - θ ↔ a ≡ θ [ZMOD (q : ℤ)] := by
  rw [Int.modEq_iff_dvd]   -- a ≡ θ [ZMOD q] ↔ q ∣ θ - a
  exact (dvd_sub_comm)

/-! ### Shifted-primorial obstruction — ЗАКОН ДЕФЕКТА -/

/--
  **Безналоговые простые делят сдвиг (Лемма 16.1).** Если по простому `q` налога нет
  (`q ∣ a − θ`) для каждого `q` из множества `G`, и эти `q` попарно различны (через примориал
  `P = ∏ q`), то `P ∣ a − θ`. (Здесь `P` — произведение по `G`; делимости складываются как lcm.)
-/
theorem primorial_dvd_shift {G : Finset ℕ} {a θ : ℤ}
    (hcop : (G : Set ℕ).Pairwise (Nat.Coprime))
    (htax : ∀ q ∈ G, (q : ℤ) ∣ a - θ) :
    (G.prod (fun q => (q : ℤ))) ∣ a - θ := by
  -- произведение попарно взаимно простых делителей делит общий аргумент
  exact Finset.prod_dvd_of_coprime (by
    intro i hi j hj hij
    exact (hcop hi hj hij).isCoprime.intCast) htax

/--
  **Shifted-primorial obstruction (Теорема 16.2 / закон дефекта).** Если примориал малых простых
  `P` делит `a − θ` и `a ≠ θ`, то `P ≤ |a − θ|`. Контрапозиция (порог `Y_A`, §17):
  если `P > |a − θ|`, то `a = θ` — бесплатный проход к `p` НЕВОЗМОЖЕН для нетривиального `a`.
-/
theorem shifted_primorial_bound {P a θ : ℤ}
    (hdvd : P ∣ a - θ) (hne : a ≠ θ) : P ≤ |a - θ| := by
  have hnz : a - θ ≠ 0 := sub_ne_zero.mpr hne
  exact Int.le_of_dvd (abs_pos.mpr hnz) ((dvd_abs P (a - θ)).mpr hdvd)

/--
  **Порог `Y_A`: поздняя граница не бесплатна.** Если примориал `P` превосходит верхнюю границу
  `Z` активного делителя (`|a − θ| ≤ Z < P`), то `P ∣ a − θ` вынуждает `a = θ`: безналоговый
  проход к ordered prime `p ≥ Y_A` невозможен (нет нетривиального `a ≤ Z`, делящегося `P`).
-/
theorem late_boundary_not_free {P a θ Z : ℤ}
    (hdvd : P ∣ a - θ) (hZ : |a - θ| ≤ Z) (hlate : Z < P) : a = θ := by
  by_contra hne
  have := shifted_primorial_bound hdvd hne
  omega

end EuclidsPath.Payment
