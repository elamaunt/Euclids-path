# 11. DASC (diagonal anchor side-corner bound)

> Lean-аналог: `EuclidsPath/Step11_DASC.lean` (заготовка)
> Источник: BE_UPDATED §23–24; ledger §17–18.

## Цель шага

Дать верхнюю нормировку product-corner `N₀₃N₃₀/N₀₀` через `N₀₀` с контролируемым избытком.

## Формулировки

**Теорема 24.1 (DASC).**
$$N_{03}N_{30}\ \le\ N_{00}^2+\eta_D\frac MA N_{00}+o\!\left(\frac MA N_{00}\right),$$
эквивалентно
$$\frac{N_{03}N_{30}}{N_{00}}\ \le\ N_{00}+\eta_D\frac MA+o(M/A).$$
В hard-clean режиме `η_D=0`.

**Через anchor-excess.** `E₊=(N₀₃−N₀₀)₊`, `E₋=(N₃₀−N₀₀)₊`; `N₀₃N₃₀ ≤ N₀₀²+N₀₀(E₊+E₋)+E₊E₋`. Если
`E₊+E₋ ≫ M/A`, то один из terminal-слоёв имеет слишком большой избыток над `N₀₀`; через anchor-map
`π_±: 𝒩₀₃,₃₀ → 𝒩₀₀` это даёт many-to-one fibers, image deficiency или projection concentration —
все входят в charged-ledger либо `O(P^ε)`. Значит в hard-clean complement `E₊+E₋=o(M/A)`.

## Статус

🔴 **ОТКРЫТО.** Нужно строго доказать anchor-excess theorem: что `N₀₃>N₀₀` обязательно создаёт
projection obstruction (контроль fibers или оплаченный избыток) — ledger §27.3.

## Ссылки

- BE_UPDATED §23–24; ledger §17–18, §27.3.
