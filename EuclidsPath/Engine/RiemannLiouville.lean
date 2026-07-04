/-
  RH через Liouville-эквивалентность (арифметический мост на ℤ). Проза: prose/31_RiemannLiouville.md.

  Идея (быстрее «двигатель→нули»): взять ГОТОВОЕ арифметическое утверждение, эквивалентное RH, и
  разложить ЕГО в нашей теории — тогда его истинность = RH автоматически.

  Выбрано: **эквивалентность Лиувилля.** `λ(n) = (−1)^Ω(n)` (`ArithmeticFunction.liouville`, mathlib),
  и RH ⟺ `L(x) = Σ_{n≤x} λ(n) = O(x^{1/2+ε})`.

  ПОЧЕМУ ложится на наш аппарат (числа RESULTS): `λ(n) = (−1)^cardFactors n` — а `cardFactors` = число
  простых факторов = НАШ `rank` у RankNode! И наш `deleteFactor` (rank r→r−1) ФЛИПАЕТ `λ`. То есть
  product-rank descent — это динамика знака Лиувилля, а RH ⟺ баланс этих знаков (`L` мал).

  Здесь: связь `λ = (−1)^rank` (из mathlib), формулировка `LiouvilleRH` (эквивалент RH на ℤ), и
  ветка `RH ⟸ LiouvilleBound` через явный мост. `LiouvilleBound` — арифметический вход, который наш
  rank-аппарат должен разложить (баланс знаков ⟺ rank-баланс).
-/
import Mathlib
import EuclidsPath.Engine.ProductCore

set_option autoImplicit false

namespace EuclidsPath.RiemannLiouville

open ArithmeticFunction Finset

/-- Суммирующая функция Лиувилля `L(x) = Σ_{n=1}^{x} λ(n)`. -/
def L (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, liouville n

/--
  **Связь λ = (−1)^rank (из mathlib).** `liouville n = (−1)^Ω(n)`, а `Ω(n) = cardFactors n` — это
  число простых факторов = НАШ rank. Значит знак Лиувилля = `(−1)^rank`. -/
theorem liouville_eq_neg_one_pow_rank {n : ℕ} (hn : n ≠ 0) :
    liouville n = (-1) ^ (cardFactors n) :=
  liouville_apply hn

/-- **Простой имеет λ = −1 (из mathlib).** Bridge для deleteFactor. -/
theorem liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp]; norm_num

/--
  **Флип знака при удалении фактора (наш deleteFactor ↔ λ).** Если `n = p·m` (`p` простое),
  то `λ(n) = −λ(m)`: удаление одного фактора (наш rank r→r−1) флипает знак Лиувилля. Это ровно
  `RankNode.deleteFactor` в терминах `λ`. Доказано через mathlib-мультипликативность `liouville_apply_mul`
  (безусловна — верно и при `m = 0`), поэтому гипотеза `m ≠ 0` НЕ нужна. -/
theorem liouville_flip_of_mul_prime {p m : ℕ} (hp : p.Prime) :
    liouville (p * m) = - liouville m := by
  rw [liouville_apply_mul, liouville_prime hp]; ring

/-- **Версия для deleteFactor-шага.** Если engine говорит `n = p·m`, удаление `p` флипает λ. -/
theorem liouville_flip_of_deleteFactor_eq {n p m : ℕ} (hp : p.Prime) (hdel : n = p * m) :
    liouville n = - liouville m := by
  subst n; exact liouville_flip_of_mul_prime hp

/-! ### RH-эквивалентность Лиувилля и ветка -/

/-- `LiouvilleBound`: `L(x) = O(x^{1/2+ε})` для всех `ε>0` — АРИФМЕТИЧЕСКИЙ эквивалент RH на ℤ.
    (Классическая теорема: RH ⟺ этот bound. Здесь — как целевое утверждение.) -/
def LiouvilleBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, |(L x : ℝ)| ≤ C * (x : ℝ) ^ (1/2 + ε)

/--
  **Мост Лиувилля (H_L) — классическая эквивалентность.** `LiouvilleBound ⟺ RH`. Это ИЗВЕСТНАЯ
  теорема аналитической теории чисел (в mathlib пока нет). Здесь — как явный вход-мост, чтобы ветка
  RH была условной на нём (не постулируем RH, постулируем классическую эквивалентность).
  `RiemannHypothesis` — из **mathlib** (официальная формулировка через нули `riemannZeta`), а НЕ
  самодельный def. -/
def LiouvilleRHBridge : Prop := LiouvilleBound ↔ RiemannHypothesis

/--
  **RH из Liouville-bound (условная ветка).** Если классический мост `LiouvilleRHBridge` дан и
  `LiouvilleBound` доказан (в нашей теории — через rank-баланс), то RH. Вся аналитика — в мосту;
  арифметика (`LiouvilleBound`) — то, что наш rank-аппарат должен разложить. -/
theorem riemann_of_liouville_bound (bridge : LiouvilleRHBridge) (hbound : LiouvilleBound) :
    RiemannHypothesis :=
  bridge.mp hbound

end EuclidsPath.RiemannLiouville
