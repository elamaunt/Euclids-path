# 04. Descent: строгий спуск и boundary-law

> Lean: `Engine/Descent.lean` (`two_carry_opposite`, `no_small_divisor`, `obstruction_on_opposite`).

Если у `m∈Ω_A` одна сторона составна, `6m+σ = a(6n+ε)` с активным `a>A`, то высота строго падает
(`n < m/A`) — это шаг двигателя. Перенос двойки: противоположная сторона `6n−ε = (6n+ε) − 2ε`, и
обструкция схлопывается в одну делимость `p ∣ 6n−ε` (boundary-law). Это связывает спуск с двойкой и
готовит rank-1 шаг [18 SNOL].
