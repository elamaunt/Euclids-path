# 15. Честный реестр открытого

> Lean-аналог: `EuclidsPath/Step15_OpenProblems.lean` (заготовка — каждый пункт = `sorry`/axiom-кандидат)
> Источник: BE_UPDATED §80–82; ledger §27, §29; AUDIT_REPLACED §67.

## Цель шага

Собрать в одном месте **всё**, что не закрыто, без приукрашивания. Это граница известного: пока эти
пункты открыты, главная теорема [[00]] остаётся недоказанной.

## Новейшее обновление (multi-rank / fan-cycle, см. [[16]])

Файл `twin_prime_new_layers_after_BE_update_…` переоформляет фронт:

- **Сняты как отдельные остатки:** PBF/DBF/FBF (поглощены Universal Fan-Cycle леммой) и изолированная
  `(3,3)`-проблема (стала одним слоем multi-rank индукции).
- **Исправлен** логически недостаточный финал `N₃₃<N₀₀` → правильный full-support non-cover
  `Ω_A ⊄ ⋃_{(i,j)≠(1,1)} R_{ij}^{clean}`.
- **Новый центральный фронт** — не BDNC⁺ по отдельности, а три proof-local convention, на которых
  условна Multi-Rank Non-Cover теорема (§10.4.1):
  1. **внешняя β-sieve** нижняя оценка carrier `|Ω_A| ≫ X/(log A)²` (должна быть указана как сито-вход);
  2. **path-selection / first-boundary** бухгалтерия (правило выбора одной composite-стороны и одной
     descent-ветви на каждый non-twin certificate);
  3. **local bounded-cycle clean-convention** (цикл = локальный forbidden-сертификат, не глобальное
     удаление).
- **Стало строго (и часть — машинно):** EPMI (проверено компилятором, [[06]]), exact rank ≤4,
  `=0`-удаления и `|Ω_del|≪X/A`, лемма B_K, эквивалент `(1,1)⟺twin`.

Старые пункты ниже (BDNC⁺/C-, V-, бухгалтерский слой) сохранены как исторический контекст; они
относятся к версии до этого обновления.

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
