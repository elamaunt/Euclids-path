# 07. Charged-ledger (заряженный слой)

> Lean-аналог: `EuclidsPath/Step07_ChargedLedger.lean` (заготовка)
> Источник: BE_UPDATED §14–15; ledger §6–8.

## Цель шага

Классифицировать все структурные исключения «плохого» слоя в **конечный** список заряженных классов,
вне которого остаток степенно мал.

## Формулировки

**Теорема 14.1 (charged exhaustion).**
$$\mathrm{Bad}\ \subset\ \mathrm{Charged}_{\le K}\cup O(P^\varepsilon),$$
$$\mathrm{Charged}=\mathrm{Fixed}\cup\mathrm{HighGCD}\cup\mathrm{SharedCRT}\cup\mathrm{AffineProjection}\cup\mathrm{RepeatedChord}\cup\mathrm{BoundedCycle}_{\le K}.$$

Дополнительные типы редуцируются: `PrimitiveLine ⊂ Fixed∪HighGCD∪AffineProjection`,
`RepeatedFullDifference ⊂ RepeatedChord∪AffineProjection∪BoundedCycle_{≤K}` — третьего автономного
типа остатка нет.

## Идея

Если плохой слой не входит в уже заряженные классы, он обязан породить bounded additive structure в
координатах `r`; при отсутствии bounded cycles до порядка `K` множество `r`-значений становится
`B_K`-множеством и потому мало [[08]].

## Статус

🟡 **локально.** Классификация считается структурно закрытой *при условии* чистого ядра
(clean-core reduction). Полнота списка и отсутствие «скрытого» автономного остатка опираются на
аналитический слой, чья финальная опора переписывалась (PMKLS → row-mixing → descent, см. [[15]], [[B]]).

## Ссылки

- BE_UPDATED §14–15; ledger §6–8.
