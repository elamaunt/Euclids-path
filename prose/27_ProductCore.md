# 27. Product-core: снятие трилеммы и вся машина

<!--navtop-->
[← 26. Separating scale](26_SeparatingScale.md) · [Оглавление](00_Overview.md) · [28. MkNode →](28_MkNode.md)
<!--/navtop-->

> Источник: `step00_product_core_rank_descent_corrected_ru_2026-07-01.md`. Lean:
> `Engine/ProductCore.lean` (`no_mismatch_core_eq`, `core_step_proved`,
> `coreCollision_of_infinite`, `product_core_engine_of_carrier` — без `sorry`; открытым
> остаётся ровно один структурный вход от carrier).

В предыдущей главе (§26) мы закрыли `ProductHall` чистой арифметикой — separating scale
$P_A > 6X_A+1$ сделал редукцию $a \mapsto a \bmod P_A$ инъективной на legal-слое. Но при
переносе этого рычага в индукцию по родословным (rank descent) три дефекта аудита возродили
трилемму: экстенсиональность паспорта, несохранение границы $a < P_A$ на residual-рангах и
неконечность пространства подписей. В этой главе мы устраняем все три **одним структурным
ходом** — заменой объекта индукции. Мы перестаём индуцировать по genealogies с их
хвостом-абсорбером и переходим к чистому **product-core**, где экстенсиональность становится
настоящей теоремой, а не гипотезой.

## Почему трилемма возникала: fan-in внутри объекта

Напомним диагноз §26 (три возражения аудита к `no_mismatch_state_eq`):

1. **Экстенсиональность.** Чтобы «нет mismatch $\Rightarrow X_1 = X_2$», паспорт обязан
   определять состояние экстенсионально. Но состояние-genealogy несёт tail/absorber, и
   декомпозиция границы (BoundaryDecomp) давала $570 \to 1$ many-to-one: разные состояния
   с одинаковым хвостом сливались. Паспорт нужен fine (для леммы) и coarse (для pigeonhole)
   одновременно — та же трилемма `UniqueLegalLift`, поднятая на ранг выше.
2. **Граница на residual.** $a < P_A$ доказывалась только на top-level; при спуске к residual
   состояниям она не передоказывалась.
3. **Конечность подписи.** Пространство остатков $(\mathbb{Z}/P_A)^r$ имеет размер $P_A^r$, и
   при $A \to \infty$ (чего требует separating scale) оно неограниченно, что убивает
   pigeonhole (который требует фиксированного $A$).

Из интуиции наблюдение: все три дефекта — это **один и тот же** дефект, и он структурный.
Fan-in $570 \to 1$ живёт в хвосте состояния. Пока хвост входит в объект индукции, он ломает
экстенсиональность (дефект 1), тащит за собой факторы, не покрытые top-level bound (дефект 2),
и раздувает пространство подписей (дефект 3). Естественно предположить: если удалить хвост из
объекта, все три дефекта исчезнут одновременно. Именно это мы и делаем.

## Объект: RankNode без хвоста

Вводим product-core node ранга $r$ — знак стороны плюс role-indexed факторы, **без** genealogy
и absorber.

$$
\texttt{RankNode}\;r \;:=\; \bigl\{\, \mathrm{sign} : \texttt{Sign},\;\; \mathrm{factors} : \mathrm{Fin}\,r \to \mathbb{N} \,\bigr\}.
$$

В Lean это `structure RankNode (r : ℕ)` с полями `sign : Sign` и `factors : Fin r → ℕ`,
где `Sign` — двухэлементный `inductive Sign | plus | minus`. Ключевое слово здесь —
`factors : Fin r → ℕ`: состояние **экстенсионально** по паре $(\mathrm{sign}, \mathrm{factors})$
по построению типа. Никакого хвоста в записи нет — потому что $570 \to 1$ fan-in жил в tail,
а tail мы в `RankNode` не положили.

> **Примечание.** Это не косметика записи. Экстенсиональность структуры — это то, что
> `funext` и инъективность конструктора дают бесплатно для `RankNode` и чего принципиально
> нельзя было получить для состояния-genealogy, где хвост склеивал различные объекты в один
> паспорт. Мы не «объявили» экстенсиональность — мы выбрали объект, для которого она есть.

## Fix 1: экстенсиональность ядра — настоящая теорема

Первый дефект снимается напрямую. Если у двух product-core узлов совпали знак и **все**
факторы, они равны.

**Теорема** (`no_mismatch_core_eq`). Для $X_1, X_2 : \texttt{RankNode}\,r$, если
$X_1.\mathrm{sign} = X_2.\mathrm{sign}$ и $\forall k,\; X_1.\mathrm{factors}\,k = X_2.\mathrm{factors}\,k$,
то $X_1 = X_2$.

Доказательство — разбор конструктора и `funext`: `cases X₁; cases X₂`, затем
`RankNode.mk.injEq` сводит равенство к паре, а `⟨hsign, funext hfac⟩` её закрывает. Что это
**значит**: «нет mismatched role $\Rightarrow$ узлы равны» — теперь лемма, а не вход. Причина,
почему это работает здесь и не работало в §31, буквально одна: в `RankNode` нет tail, поэтому
поточечное равенство факторов — это и есть всё содержание состояния.

## Fix 2: AmbientLegal и граница $a < P_A$ на всех рангах

Второй дефект (несохранение границы) снимается сертификатом, который переживает удаление
роли. Вводим предикат.

**Определение** (`AmbientLegal`). Семейство факторов $\mathrm{factors} : \mathrm{Fin}\,r \to \mathbb{N}$
*ambient-legal при масштабе* $X_A$, если существует общий top legal side $N_0$, который все
факторы делят и который не превосходит carrier-границы:

$$
\texttt{AmbientLegal}\;X_A\;\mathrm{factors} \;:=\; \exists\, N_0 : \mathbb{N},\;\; 0 < N_0 \;\wedge\; N_0 \le 6X_A + 1 \;\wedge\; \forall i,\; \mathrm{factors}\,i \mid N_0.
$$

Из этого сертификата граница следует немедленно.

**Теорема** (`ambient_factor_lt_primorial`). При separating scale $6X_A + 1 < P_A$ и
`AmbientLegal X_A factors` имеем $\forall i,\; \mathrm{factors}\,i < P_A$.

Доказательство: $\mathrm{factors}\,i \mid N_0 \Rightarrow \mathrm{factors}\,i \le N_0$
(`Nat.le_of_dvd`), а $N_0 \le 6X_A+1 < P_A$; `omega` замыкает. Это тот же аргумент, что в §26
(`legal_lift_lt_primorial`), но теперь он привязан к **семейству ролей**, а не к одному фактору.

Критично, что сертификат сохраняется при удалении роли. Residual — это подсемейство факторов,
значит **тот же** $N_0$ годится.

**Теорема** (`ambientLegal_delete`). Для $\mathrm{factors} : \mathrm{Fin}(r+1) \to \mathbb{N}$ и
роли $k$, из `AmbientLegal X_A factors` следует
`AmbientLegal X_A (fun i => factors (k.succAbove i))`.

Здесь `Fin.succAbove` — каноническое вложение $\mathrm{Fin}\,r \hookrightarrow \mathrm{Fin}(r+1)$,
пропускающее позицию $k$; доказательство переносит тот же $N_0$ на подсемейство. Что это
**значит**: граница $a < P_A$ теперь **инвариант спуска**, а не top-level-факт. Дефект 2 закрыт
структурно — удаление роли не выводит нас из legal-слоя.

## Fix 3: конечность подписи при фиксированном $A$

Третий дефект (неконечность $(\mathbb{Z}/P_A)^r$) снимается тем, что мы фиксируем $A$ **на
время pigeonhole** и берём подпись только по фиксированному $P_A$ и фиксированному $r$.

**Определение** (`CoreSig`). При фиксированных $P_A, r$ core-подпись — знак плюс остатки
факторов mod $P_A$, **без** genealogy:

$$
\texttt{CoreSig}\;P_A\;r \;:=\; \bigl\{\, \mathrm{sign} : \texttt{Sign},\;\; \mathrm{residues} : \mathrm{Fin}\,r \to \mathbb{Z}/P_A \,\bigr\}.
$$

**Теорема** (`coreSig_fintype`). При $[\texttt{NeZero}\,P_A]$ (т.е. $P_A > 0$) и фиксированном
$r$ тип `CoreSig P_A r` конечен.

Инстанс строится через `Fintype.ofInjective` вложением
$s \mapsto (s.\mathrm{sign}, s.\mathrm{residues})$ в конечный тип
$\texttt{Sign} \times (\mathrm{Fin}\,r \to \mathbb{Z}/P_A)$; инъективность — разбор конструктора.
Что это **значит**: пространство подписей конечно, и pigeonhole применим.

> **Примечание (о напряжении $A$ фиксирован vs $A \to \infty$).** Дефект 3 в §31 указывал на
> прямое противоречие: separating scale хочет $A \to \infty$, а pigeonhole — фиксированный $A$.
> Разрешение честное, а не иллюзорное: separating scale используется **внутри одного слоя $A$**
> (чтобы редукция была инъективна и граница держалась), а pigeonhole применяется **при этом же
> фиксированном $A$** к бесконечному семейству стартов внутри слоя. Мы не устремляем $A$ к
> бесконечности внутри pigeonhole — мы работаем на конкретном $A$, для которого separating scale
> уже достигнут (по §26 это происходит уже при $A \approx 50$ с огромным запасом). Финальная
> бесконечность близнецов придёт от бесконечности слоёв извне, не от раздувания $r$ или $P_A$.

## Мост подпись↔узел: ¬ProductHall на RankNode

Свяжем узел с подписью. `coreSigOf X := ⟨X.sign, fun i => (X.factors i : ZMod P_A)⟩` —
паспорт узла. Теперь перенесём аргумент §26 на product-core: равенство остатков плюс граница
дают равенство факторов.

**Теорема** (`no_productHall`). Если на роли $k$ оба фактора $< P_A$ и сравнимы mod $P_A$, но
$X_1.\mathrm{factors}\,k \ne X_2.\mathrm{factors}\,k$ — противоречие ($\texttt{False}$).

Доказательство: при $a < P_A$ имеем $\texttt{ZMod.val}(a \bmod P_A) = a$
(`ZMod.val_natCast` + `Nat.mod_eq_of_lt`); равенство остатков тогда переносится на сами $a$,
и $\mathrm{hne}$ падает. Отсюда — финальная сборка «равные подписи + граница $\Rightarrow$
равные узлы».

**Теорема** (`factors_eq_of_coreSig`). Если $\mathrm{coreSigOf}\,X_1 = \mathrm{coreSigOf}\,X_2$
и все факторы обоих $< P_A$, то факторы совпадают поточечно (по `no_productHall` от противного).

**Теорема** (`rankNode_eq_of_coreSig`). При тех же гипотезах $X_1 = X_2$: знак берётся из
подписи (`congrArg CoreSig.sign`), факторы — из границы, и `no_mismatch_core_eq` собирает узел.

Три fix встретились в одной точке: экстенсиональность (`no_mismatch_core_eq`) даёт знак-и-факторы
$\Rightarrow$ узел; граница (`ambient_factor_lt_primorial`) даёт из подписи $\Rightarrow$
факторы; конечность обеспечит существование коллизии. Осталось запустить это как индукцию.

## База индукции: rank-1 арифметикой, без внешнего SNOL

Определим объект спуска.

**Определение** (`CoreCollision`). $\texttt{CoreCollision}\;X_A\;P_A\;r$ — существование двух
**разных** ambient-legal RankNode ранга $r$ с равной подписью:

$$
\exists\, X_1\, X_2 : \texttt{RankNode}\,r,\;\; X_1 \ne X_2 \;\wedge\; \texttt{AmbientLegal}\,X_A\,X_1.\mathrm{factors} \;\wedge\; \texttt{AmbientLegal}\,X_A\,X_2.\mathrm{factors} \;\wedge\; \mathrm{coreSigOf}\,X_1 = \mathrm{coreSigOf}\,X_2.
$$

**Теорема** (`rank_one_coreCollision_absurd`). При separating scale $6X_A+1 < P_A$
коллизия ранга $1$ невозможна: $\texttt{CoreCollision}\,X_A\,P_A\,1 \Rightarrow \texttt{False}$.

Доказательство целиком арифметическое: `ambient_factor_lt_primorial` даёт границу для обоих,
`rankNode_eq_of_coreSig` даёт $X_1 = X_2$, противоречащее $X_1 \ne X_2$. Подчеркнём: **база не
опирается на внешний SNOL** — она замыкается той же separating-scale арифметикой, что и
индукционный шаг. Это устраняет зависимость §31 от отдельного rank-1 SNOL-модуля.

## Шаг спуска $r \to r-1$: удаление mismatched role

Дефект §31 состоял в том, что шаг `core_step` оставался *входом* (гипотезой). Здесь мы его
**доказываем**. Инструмент — удаление роли.

**Определение** (`deleteFactor`). Удаление роли $k$ из $\texttt{RankNode}(r+1)$ даёт
$\texttt{RankNode}\,r$: тот же знак, факторы переиндексованы через `Fin.succAbove`.

**Теорема** (`delete_preserves_coreSig`). Если подписи полных узлов равны, то и подписи после
удаления одной и той же роли $k$ равны (знаки те же; остатки на выживших ролях те же).

**Теорема** (`core_step_succ`). При separating scale коллизия ранга $r'+1$ даёт коллизию
ранга $r'$.

Логика шага — суть всей главы, разберём подробно. Из равенства подписей и $X_1 \ne X_2$
существует mismatched role $k$ (иначе `no_mismatch_core_eq` дал бы $X_1 = X_2$). Удаляем $k$,
получая $Y_1, Y_2$. Их подписи равны (`delete_preserves_coreSig`), сертификаты `AmbientLegal`
сохранены (`ambientLegal_delete`). Дальше — **дихотомия residual**:

- если $Y_1 \ne Y_2$, то $(Y_1, Y_2)$ — коллизия ранга $r'$ (спуск состоялся);
- если $Y_1 = Y_2$, то residual-факторы совпали, и весь mismatch сосредоточен на роли $k$:
  $X_1.\mathrm{factors}\,k \ne X_2.\mathrm{factors}\,k$, но эти факторы сравнимы mod $P_A$ и оба
  $< P_A$ — это в точности **ProductHall**, невозможный по `no_productHall`. Ветвь ложна.

В обеих ветвях мы либо спустились на ранг, либо получили противоречие. Отсюда упаковка:

**Теорема** (`core_step_proved`). При separating scale
$\forall r,\; 2 \le r \Rightarrow \texttt{CoreCollision}\,X_A\,P_A\,r \Rightarrow \texttt{CoreCollision}\,X_A\,P_A\,(r-1)$
(из `core_step_succ` подстановкой $r = (r-1)+1$).

> **Примечание.** Почему трилемма здесь не возрождается? В §31 шаг ломался на
> экстенсиональности residual: удаление хвоста могло склеить разные состояния. В `RankNode`
> хвоста нет, поэтому `no_mismatch_core_eq` (для полного узла) и `delete_preserves_coreSig`
> (для residual) держатся оба, а `no_productHall` закрывает вырожденную ветвь без всякого
> обращения к паспорту как «нормальной форме». Индукция по product-core **без tail убирает
> fan-in из объекта** — и вместе с ним источник трилеммы.

## Собираем индукцию: коллизия $\Rightarrow$ Engine

**Теорема** (`coreCollision_engine`). При separating scale и шаге `core_step`
(теперь предъявленном как `core_step_proved`):
$\forall r,\; 1 \le r \Rightarrow \texttt{CoreCollision}\,X_A\,P_A\,r \Rightarrow \texttt{Engine}$.

Доказательство — сильная индукция (`Nat.strong_induction_on`): при $n < 2$ имеем $n = 1$ и
работает база `rank_one_coreCollision_engine`; при $n \ge 2$ спускаемся `core_step` на $n-1$ и
применяем гипотезу индукции. Off-by-one между collision-rank и state-rank, пойманный при
формализации §31, здесь учтён: индукция ведётся по рангу коллизии, спуск строго уменьшает его.

## База pigeonhole: бесконечность стартов $\Rightarrow$ коллизия

Теперь предъявим саму коллизию. Конечность подписи (`coreSig_fintype`) плюс бесконечное
инъективное семейство стартов дают два разных старта с равной подписью.

**Теорема** (`coreCollision_of_infinite`). Пусть $S \subseteq \iota$ бесконечно,
$\mathrm{node} : \iota \to \texttt{RankNode}\,r$ инъективно на $S$ (разные старты $\Rightarrow$
разные cores), и каждый $\mathrm{node}\,i$ ($i \in S$) ambient-legal. Тогда
$\texttt{CoreCollision}\,X_A\,P_A\,r$.

Доказательство — pigeonhole от противного. Если коллизии нет, то $\mathrm{coreSigOf} \circ \mathrm{node}$
инъективна на $S$ (равные подписи двух разных cores дали бы коллизию). Но образ лежит в
конечном `CoreSig` (`Set.toFinite`), а инъективное отображение бесконечного $S$ в конечный тип
невозможно (`Set.Finite.of_finite_image`) — противоречие с $S.\texttt{Infinite}$. **Это ядро
доказано полностью**, без входов.

Отсюда — упаковка карьерных данных:

**Теорема** (`freshStarts_to_coreCollision`). Структура carrier (бесконечно много стартов
одного знака и ранга $1 \le r \le 4$, каждый — ambient-legal RankNode, разные старты $\Rightarrow$
разные cores) даёт $\exists r',\; 1 \le r' \le 4 \wedge \texttt{CoreCollision}\,X_A\,P_A\,r'$.

## Вся машина: Engine из carrier-данных

**Теорема** (`product_core_engine_of_carrier`). При separating scale $6X_A+1 < P_A$,
$1 \le r \le 4$, бесконечном $S$ со стартами $\mathrm{node}$, инъективными на $S$ и всюду
ambient-legal — получаем $\texttt{Engine}$.

Сборка: `product_core_pump_closed` (финал **без** гипотезы `core_step`, т.к. шаг доказан как
`core_step_proved`, база доказана арифметикой) применяется к
`freshStarts_to_coreCollision`. Всё внутреннее содержание — экстенсиональность, граница,
конечность, спуск, база и pigeonhole — **доказано в этом файле без `sorry`**.

Что это **значит** для программы. Мы прошли путь от «трилемма возрождается на ранг выше» (§31) к
машине, где три дефекта сняты структурно одним выбором объекта. Открытым остаётся ровно **один**
вход — `CarrierData`: бесконечность nodeable-центров одного слоя, каждый дающий ambient-legal
RankNode ранга $1 \le r \le 4$ с попарно различными cores.

> **Примечание (честная граница закрытого и открытого).** Мы не выдаём редукцию за
> доказательство. `product_core_engine_of_carrier` — это **условная** теорема: она превращает
> одну явную структурную гипотезу (carrier даёт бесконечное инъективное семейство ambient-legal
> стартов фиксированного ранга) в Engine, и всё между гипотезой и Engine машинно проверено. Дыра
> не исчезла — она сжата до `CarrierData` и точно локализована.

**Гипотеза (`CarrierData`) и план закрытия.** Требуется: из глобального absorption на слое $A$
извлечь тип центров $\iota$, бесконечное подмножество $S$ nodeable-центров, и отображение
$\mathrm{node} : \iota \to \texttt{RankNode}\,r$ такое, что (i) каждый центр $m \in S$ даёт clean
composite side $6m + \sigma = \prod_i a_i$ с факторами $a_i > A$; (ii) все $a_i$ делят общий
top legal side $N_0 \le 6X_A+1$ (ambient-legal); (iii) $r \le 4$; (iv) разные центры дают
различные cores. План: пункты (i)–(iii) — арифметика факторизации clean-стороны и
carrier-границы, разбираемая в следующей главе; пункт (iv) (инъективность) и, главное,
**бесконечность** $S$ приходят из GlobalOldAbsorption и остаются последним содержательным
входом всей программы.

Именно эту факторизацию clean composite side в конкретный `RankNode` — с доказанной
арифметикой $a_i > A$, `AmbientLegal` и $r \le 4$ — мы строим в следующей главе (§28, mkNode),
сводя открытый `CarrierData` к единственному внешнему факту: бесконечности nodeable-центров.

<!--navbot-->

---

[← 26. Separating scale](26_SeparatingScale.md) · [Оглавление](00_Overview.md) · [28. MkNode →](28_MkNode.md)
<!--/navbot-->
