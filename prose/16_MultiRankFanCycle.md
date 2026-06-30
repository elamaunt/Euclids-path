# 16. Новые слои: multi-rank descent и Universal Fan-Cycle

> Lean-аналоги: `EuclidsPath/Engine/EPMI.lean` (невозможность двигателя, скомпилировано),
> `EuclidsPath/Step16_MultiRankFanCycle.lean` (B_K и fan-cycle — частично).
> Источник: `twin_prime_new_layers_after_BE_update_ru_2026-06-30.md` (целиком).

## Цель шага

Это переработка финала после `BE_UPDATED`. Она заменяет «бухгалтерский» слой (DASC/G2/O4C-res/
`c_G>η_D+η_B`, шаги [[10]]–[[13]]) на комбинаторную конструкцию **multi-rank descent + Fan-Cycle**,
и исправляет логически недостаточный старый мост `N₃₃<N₀₀`.

## Новый масштаб carrier

Вместо жёсткого `X=A⁴`:
$$X=A^\kappa,\qquad \beta_2<\kappa<5,$$
где `β₂` — нижний порог двумерного комбинаторного beta-sieve. Old-free carrier:
$$\Omega_A=\{m\le X:\gcd((6m-1)(6m+1),P_A)=1\},\qquad P_A=\prod_{p\le A}p.$$

**Теорема 1.3.1 (нижняя оценка carrier).** При `κ>β₂`:
$$|\Omega_A|\gg X\prod_{3<p\le A}\Big(1-\tfrac2p\Big)\gg \frac{X}{(\log A)^2}.$$
🟡 опирается на **внешнюю** finite dimension-2 beta-sieve нижнюю оценку (детерминированную, но это
сито-теорема; carrier — это числа без малых делителей, НЕ простые, поэтому parity problem здесь не
мешает нижней оценке smooth-free массы).

## Exact rank ≤ 4 и необходимые удаления

Так как `6m±1 ≤ A^κ`, `κ<5`, и все простые делители `>A`:
$$\rho_\pm(m)=\Omega(6m\pm1)\le 4.$$
🟢 **проверено компилятором:** `EuclidsPath/Step16` теорема `fullRank_le_four`
(`(A+1)^{Ω(n)} ≤ ∏ простых = n < A^5 < (A+1)^5 ⇒ Ω(n) ≤ 4`).
**Лемма 2.2.1 (exact factorization):** rank-3 сторона `= abv` без residual cofactor (иначе `h>A²` ⟹
`abvh>A⁵`, противоречие `κ<5`). 🟢 элементарно.

**Теорема 3.5.1 (бюджет удалений):** `|Ω_del| ≪ X/A = o(|Ω_A|)`, где удаляются только неизбежные классы:
squareful active (`≪X/A`), shared gcd (`=0`, т.к. `p∣2`), residual cofactor (`=0`), boundary recycling
(`=0`). 🟢 элементарно (суммирование `∑ 1/p²` и логические `=0`).

## Вечный двигатель: три лица (§XI)

1. **Downward EPMI** — нет бесконечного lossless спуска `m_{t+1}<m_t/A` ([[06]], `EPMI.lean`). 🟢
2. **Boundary EPMI** — `⊥↛S`: продолжение через границу даёт `n∈Ω_A ∧ n∉Ω_A`. 🟢
3. **Upward finite-cycle EPMI** — слишком большой fan над одним `U` ⇒ bounded additive cycle
   `∑α_i=∑β_i` ⇒ `∑m_{α_i}=∑m_{β_i}` (local charged certificate). 🟡 (см. ниже)

## Универсальная Fan-Cycle лемма

**Boundary compression (§5.2):** carrier-масса `≫X/(log A)²`, поглощённая leaves с product `U>A^s`,
даёт (число leaves `≪X/A^s`, Дирихле) fixed `U` с fan height `H≫A^s/(log A)²`.

**Лемма 6.1.1 (B_K):** если `𝒜⊂[1,T]` не содержит нетривиального равенства `K`-сумм, то
`|𝒜|≪_K T^{1/K}`. 🟢 **элементарно и доказуемо** (число неубывающих `K`-наборов `≫|𝒜|^K`, все суммы
различны и лежат в `[K,KT]` ⇒ `|𝒜|^K≪T`). — формализуется в Lean.

**Теорема 7.1.1 (Universal Fan-Cycle):** при `T≪A^{κ-s}` и `|𝒜|≫A^s/(log A)²`, выбрав `K>(κ-s)/s`
(достаточно `K=5` для всех `1≤s≤4, κ<5`), множество `𝒜` содержит bounded additive cycle. 🟡
строго следует из 6.1.1 + 5.2, но 5.2 зависит от того, что compression действительно набирает
carrier-массу (path bookkeeping).

**Следствие:** `PBF`(r=1), `DBF`(r=2), `FBF`(r=3) — частные случаи одной леммы, а не отдельные остатки.

## Исправление финальной цели (§IX)

Старый мост `N₃₃<N₀₀ ⇒ twin` **логически недостаточен**: точка вне `R₃₃` может лежать в
`R₂₁,R₂₂,R₁₄,…`. Правильная цель — **full support non-cover**:
$$\boxed{\Omega_A\setminus\Omega_{del}\ \not\subseteq\ \bigcup_{(i,j)\ne(1,1)}\mathcal R_{ij}^{clean}.}$$
Twin center `⟺ (ρ₋,ρ₊)=(1,1)`. Выживший вне всех non-twin рангов ⇒ оба `6m±1` простые. 🟢 (сам
эквивалент); 🔴 (само non-cover — см. ниже).

## Multi-Rank Non-Cover Theorem (§10.4)

**Теорема 10.4.1.** При гипотезах 1–8 (масштаб; carrier lower bound; exact rank; `|Ω_del|≪X/A`;
boundary absorbing; EPMI; unpaid clean certificates исключают fan-cycles порядка `≤K=5`;
path-selection bookkeeping) — union non-twin clean rank supports не покрывает carrier ⇒ существует
twin center.

**Идея (от противного):** если carrier покрыт non-twin сертификатами, для каждого `m` берём composite
side и спускаемся. Каждая ветвь: (1) строго убывает (EPMI запрещает бесконечность) ⇒ доходит до `(1,1)`
= twin (противоречие «нет twins»); или (2) boundary absorption ⇒ при carrier-масштабе даёт large fan
⇒ fan-cycle (запрещён convention); или (3) local charged ⇒ сертификат не был unpaid clean. Все исходы
противоречат полному unpaid non-twin покрытию.

## Статус (честно, §XV/§12.3)

🟢 **строго:** EPMI (все три лица в части арифметики спуска/границы), exact rank ≤4, `=0`-удаления,
B_K лемма, эквивалент `(1,1)⟺twin`, исправление финальной цели на full-support non-cover.

🟡 **условно (proof-local conventions):** Fan-Cycle (нужен carrier-mass capture), Multi-Rank Non-Cover —
зависят от:
- **внешней β-sieve** нижней оценки carrier (теорема сита, должна быть указана как вход);
- **path-selection / first-boundary** бухгалтерии (формальное правило выбора одной ветви);
- **local bounded-cycle clean-convention** (циклы как локальные forbidden-сертификаты, а не глобальные
  удаления) — именно здесь прячется главная тонкость.

🔴 **остаётся открытым до интеграции:** строгая увязка трёх условностей в единый аргумент без скрытых
допущений; именно это (а не PBF/DBF/FBF по отдельности) — настоящий фронт. См. [[15]].

## Что это меняет в карте

- `PBF/DBF/FBF` и изолированная `(3,3)`-проблема **сняты как отдельные остатки** (поглощены Fan-Cycle и
  multi-rank индукцией).
- Старые шаги [[10]]–[[13]] (DASC/G2/O4C-res) становятся **необязательными**: финал теперь идёт через
  multi-rank non-cover, а не через `c_G>η_D+η_B`.
- Новый центральный фронт — три proof-local convention выше, а не аналитический large sieve.

## Ссылки

- Весь файл `twin_prime_new_layers_after_BE_update_ru_2026-06-30.md` (§I–§XV).
