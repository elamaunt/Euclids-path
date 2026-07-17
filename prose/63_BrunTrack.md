# 63. Тропа Бруна: плотность ноль и безусловные темпы — formalization-first

<!--navtop-->
[← 62. Дилатационная лестница](62_DilationLadder.md) · [Оглавление](00_Overview.md)
<!--/navtop-->

> Lean: `Engine/GeometricTypeIIBrun.lean` (`alternating_partial_binomial`,
> `moebius_truncated_divisor_sum`, `bonferroni_isUpperMoebius`),
> `Engine/GeometricTypeIIBrunTwin.lean` (`twinValue`, `sievePrimes`, `twinNu`,
> `twinSieve`, `root_res_card`, `twinSieve_rem_bound`, `brun_twin_upper`,
> `esymmOn_le_pow_div_factorial`), `Engine/GeometricTypeIIBrunTwinDensity.lean`
> (`twin_mainSum_eq`, `twin_errSum_le_const`, `twin_count_le_eps`,
> `twin_density_zero`), `Engine/GeometricTypeIIBrunTwinRate.lean`
> (`twin_count_of_prod_le`, `twin_count_log_rate`),
> `Engine/GeometricTypeIIBrunTwinMertens.lean`
> (`sievePrimes_prod_le_nine_div_log_sq`, `twin_count_log_rate_unconditional`),
> `Engine/GeometricTypeIIBrunTwinMertensUpper.lean` (`sum_primesLE_inv_le`,
> `sievePrimes_sum_two_div_le`), `Engine/GeometricTypeIIBrunTwinTruncated.lean`
> (`twin_mainSum_truncated_le`, `esymm_tail_le`, `twin_errSum_truncated_le`,
> `twin_count_brun_truncated`).

Метод Бруна — верхнеоценочный: он структурно слеп к стене чётности, и **именно поэтому**
его можно довести до конца безусловно. Эта глава — formalization-first трек: от моста в
спящую решётную раму mathlib до машинных теорем «близнецы имеют плотность ноль» и
«twins$(N) \le 9N/\log^2 z + 3^z + z/6 + 1$», и дальше — до обрезанного решета с истинной
Брун-формой. Ни одно из этих утверждений не говорит ничего о *бесконечности* близнецов;
верхняя оценка не касается стены — и это записано в каждом дисклоужере.

## 1. Этап 1: мост Бонферрони в спящую раму

В пине mathlib есть решётная рама (`BoundingSieve`) с теоремой
`siftedSum_le_mainSum_errSum_of_upperMoebius` — но без единого пригодного веса.

> **Теорема 63.1** (`moebius_truncated_divisor_sum`). Замкнутая форма усечённой суммы
> Мёбиуса: для $n \ge 2$
>
> $$
> \sum_{d \mid n,\ \omega(d) \le t} \mu(d) \;=\; (-1)^t \binom{\omega(n)-1}{t} \tag{63.1}
> $$
>
> — каждое усечение закрывается одним членом Паскаля (`alternating_partial_binomial`).
> При чётном $t$ правая часть $\ge 0$: вес Бонферрони — верхне-мёбиусов
> (`bonferroni_isUpperMoebius`), и рама mathlib становится применимой. 🟢

## 2. Этап 2: близнецовое решето

> **Определение 63.2** (близнецовое решето). Носитель — значения
> `twinValue` $m = (6m-1)(6m+1)$, решётные простые — `sievePrimes` $z$ = простые из
> $[5, z]$, плотность — `twinNu` $d = 2^{\omega(d)}/d$. Число корней $36r^2 \equiv 1
> \pmod d$ равно точно $2^{\omega(d)}$ (`root_res_card`), остаток $|r(d)| \le 2^{\omega(d)}$
> (`twinSieve_rem_bound`).

> **Теорема 63.3** (`brun_twin_upper`). Для всех $N, z$ и чётного $t$
>
> $$
> \#\{m \le N: \text{оба } 6m\pm1 \text{ просты}\}
> \;\le\; N \cdot \mathrm{mainSum}(\mu^+_t) + \mathrm{errSum}(\mu^+_t) + \tfrac{z}{6} + 1. \tag{63.2}
> $$
>
> Точное, безусловное неравенство; решётные члены пока символические. 🟢

## 3. Этап 3: плотность ноль

Выбор $t = 2k$ ($k$ — число решётных простых) делает усечение пустым:
$\mathrm{mainSum} = \prod_{5 \le p \le z}(1 - 2/p)$ **точно** (`twin_mainSum_eq`), а
бюджет ошибки $N$-свободен: $\mathrm{errSum} \le 3^k$ (`twin_errSum_le_const`).
Расходимость $\sum 1/p$ убивает произведение Лежандра, и:

> **Теорема 63.4** (`twin_density_zero`). Близнецовые центры имеют плотность ноль:
>
> $$
> \frac{\#\{m \le N : \text{оба } 6m\pm1 \text{ просты}\}}{N} \;\xrightarrow[N\to\infty]{}\; 0. \tag{63.3}
> $$
>
> Первая самостоятельная классическая теорема formalization-first трека — машинно, в
> стандартных аксиомах, без `sorry` (рабочая форма — `twin_count_le_eps`). 🟢

## 4. Этап 4a: безусловный логарифмический темп

Параметрическая форма `twin_count_of_prod_le` принимает любую оценку произведения.
Мертенсов вход разрядился **трюком возведения в квадрат**: $1 - 2/p \le (1 - 1/p)^2$
(разность ровно $1/p^2$), конечное эйлерово тождество пина мажорирует гармонику, и
$\prod_{5 \le p \le z}(1 - 2/p) \le 9/\log^2 z$ для всех $z \ge 2$
(`sievePrimes_prod_le_nine_div_log_sq`; пре-пасс: $\sup_z \mathrm{LHS}\cdot\log^2 z =
2.497$ — запас $3.6\times$; истинная константа $4e^{-2\gamma} \approx 1.26$ не заявлена).

> **Теорема 63.5** (`twin_count_log_rate_unconditional`). Для всех $N$ и всех $z \ge 2$
>
> $$
> \#\{m \le N: \text{оба } 6m\pm1 \text{ просты}\}
> \;\le\; \frac{9N}{\log^2 z} + 3^z + \frac{z}{6} + 1. \tag{63.4}
> $$
>
> Прозаическое чтение: $z \approx \tfrac12\log N$ даёт грубый Брун
> $O\bigl(N/(\log\log N)^2\bigr)$. 🟢

## 5. Этап 4b: Мертенс-верхняя и обрезанное решето

Истинный Брун-темп требует большого $z$, а значит — обрезания $t \ll k$ и контроля
хвоста. Нужная верхняя оценка Мертенса получена маршрутом «Чебышёв прямо в Абеля»:
$\theta(x) \le x\log 4$ пина подан в спящую раму суммирования Абеля
(`sum_mul_eq_sub_integral_mul₁`), граничный член сокращает антипроизводную точно:

> **Теорема 63.6** (`sum_primesLE_inv_le`). Для $x \ge 2$
>
> $$
> \sum_{p \le x} \frac1p \;\le\; \log 4 \cdot \log\log x
> + \log 4\Bigl(\frac{1}{\log 2} - \log\log 2\Bigr), \tag{63.5}
> $$
>
> и в решётной форме $\sum_{p \in \text{sievePrimes } z} 2/p \le 3\log\log z + 6$ при
> $z \ge 3$ (`sievePrimes_sum_two_div_le`). Константа $\log 4$ — чебышёвская, не
> оптимальная; PNT нигде не используется. 🟢

Дефект обрезания оценивается элементарно-симметрическим хвостом: делители $P(z)$
биективны подмножествам решётных простых, $e_j \le X^j/j!$
(`esymmOn_le_pow_div_factorial` — спящий инструмент этапа 2, теперь съеденный), и
$\sum_{j>t} e_j \le e^{3X}/2^{t+1}$ (`esymm_tail_le`); ошибка обрезания полиномиальна:
$\mathrm{errSum}(\mu^+_t) \le (t+1)(2z)^t$ (`twin_errSum_truncated_le`).

> **Теорема 63.7** (`twin_count_brun_truncated`). Для всех $N$, $z \ge 3$ и чётного $t$
>
> $$
> \#\{m \le N\}
> \;\le\; N\Bigl(\frac{9}{\log^2 z} + \frac{e^{9\log\log z + 18}}{2^{t+1}}\Bigr)
> + (t+1)(2z)^t + \frac{z}{6} + 1. \tag{63.6}
> $$
>
> Прозаическое чтение (не Lean): $2^t \approx \log^{11} z$, $z \approx N^{1/4t}$ дают
> истинную Брун-форму $O\bigl(N(\log\log N)^2/\log^2 N\bigr)$. Константы честные и
> грубые; численные пороги применимости астрономичны — как у всякой честной цепочки
> констант Бруна; ценность — машинно проверенное параметрическое семейство. 🟢

**Итог главы.** Мост Бонферрони открыл спящую раму (63.1); близнецовое решето
инстанцировано с точным числом корней (Определение 63.2, 63.2); плотность ноль — машинно
(63.3); темп $9N/\log^2 z$ безусловен (63.4); Мертенс-верхняя взята Чебышёвым через
Абеля без PNT (63.5); обрезанное решето дало параметрическую истинную Брун-форму (63.6).
Всё это — верхние оценки: метод слеп к стене чётности, бесконечность близнецов не
затронута ни в одной строке, и ни одно событие §110 не заявлено.
