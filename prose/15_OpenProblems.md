# 15. Честный реестр открытого

> Lean-аналог: `EuclidsPath/Step15_OpenProblems.lean` (заготовка — каждый пункт = `sorry`/axiom-кандидат)
> Источник: BE_UPDATED §80–82; ledger §27, §29; AUDIT_REPLACED §67.

## Цель шага

Собрать в одном месте **всё**, что не закрыто, без приукрашивания. Это граница известного: пока эти
пункты открыты, главная теорема [[00]] остаётся недоказанной.

## Несущий центральный фронт (самое свежее)

**BDNC⁺ — Boundary-depth non-cover / compression theorem** (BE_UPDATED §80–81).
Локальная инвариантность ([[06]]) не даёт глобальный non-cover: конечное bounded-depth дерево, где
каждая ветвь оканчивается absorbing boundary-leaf, комбинаторно возможно. Нужно доказать, что
absorbing boundary leaves **недостаточно**, чтобы покрыть всю clean-root mass без повторения/сжатия, а
повторение boundary-signatures даёт charged pattern или SmallModulusLock. Сопутствующие остатки:

- `C₁` Boundary Leaf Compression / BDNC⁺.
- `C₂` SmallModulusLock budget: для класса `p≤A`, `uv≡±2 (mod p)` определить lock-условие и доказать
  first-charge бюджет.
- `C₃` Carrier lower bound / cutoff: закрепить old-cutoff (строго `z=A` либо deterministic
  Buchstab-bridge от `z<A` к `A`), чисто ситово-комбинаторно.
- `C₄` Degenerate charged budget: оплатить active squareful, residual cofactor, shared CRT,
  affine/repeated/bounded-cycle degeneracies.
- `C₅` Final support implication: строго проверить `B₅>0 ⇒` реально простые `6m±1`.

## Глобальный «бухгалтерский» слой (ledger §27, §29)

Не закрыто полностью:
$$\boxed{O4C\text{-}res,\quad RowLight\Rightarrow ProjectionObstruction,\quad DASC,\quad G2,\quad c_G>\eta_D+\eta_B.}$$

Технические подпункты (ledger §27.1–27.12): O4C-res normalization; RowLight no-escape; DASC
anchor-excess theorem; G2 product normalization; active product lower bound `F₄≫M/A`; scale separation
`P^ε=o(M/A)`; first-charge disjointness; certificate-cover fiber bound; bounded-cycle constants `C_K`;
uniformity по `h,R,C₀`; downstream scale match; infinite block iteration.

## Промежуточная замена-аудит (AUDIT_REPLACED §67) — остатки `V₁–V₄`

После замены произвольного PMKLS коротким CRT row-mixing (`P⁴=o(M/A)`, т.е. `P≤A^{3/4−ε}`):
`V₁` глобальный scale audit при `P≤A^{3/4−ε}`; `V₂` old-carrier equidistribution modulo `P⁴`;
`V₃` бюджет non-coprime/incompatible CRT row-pairs; `V₄` DASC и G2 под коротким активным масштабом.

## Что строго закрыто (для контраста)

Центровая форма [[01]], CRT-запреты [[02]], просеивание [[03]], достаточность `B₅>0` [[04]],
детерминантный закон и zero-one slot [[05]], локальная невозможность двигателя [[06]], малые
charged-классы и `B_K` [[08]] (при фиксированных порогах), certificate cover [[09]].

## Важное предупреждение о миграции статусов

Ключевое движение поздних файлов (30 июня) — **не дозакрытие, а снятие** прежней опоры:
PMKLS/QSPMKLS, считавшийся в base/UPDATED опорой, в AUDIT_REPLACED/BE_UPDATED снят как недоказанный в
нужной силе и заменён (см. [[B]]). Поэтому итоговый честный статус задают **последние** файлы:
локальная анатомия закрыта, глобальный слой — нет. Открытые мосты по сложности сопоставимы с самой
гипотезой простых-близнецов.

## Ссылки

- BE_UPDATED §80–82; ledger §27, §29; AUDIT_REPLACED §62, §67.
