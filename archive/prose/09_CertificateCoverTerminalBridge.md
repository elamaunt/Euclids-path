# 09. Certificate cover и terminal bridge

> Lean-аналог: `EuclidsPath/Step09_CertificateCoverTerminalBridge.lean` (заготовка)
> Источник: BE_UPDATED §16–17; ledger §9–10.

## Цель шага

Корректно нормировать заряженные вершины: не считать все additive-сертификаты (их слишком много), а
покрыть по одному минимальному на вершину и оплатить terminal-рядами.

## Формулировки

**Отказ от подсчёта всех сертификатов.** Для `𝓡={1,…,L}` число chord-сертификатов `a−b=c−d` имеет
порядок `E₂(𝓡)≍L³` при числе supports `≍L`; значит оценка «#all certificates ≪ O» ложна.

**Certificate cover.** Отображение `χ: 𝒬_{≤K} → 𝔠_{≤K}` назначает каждой charged-вершине один
минимальный сертификат; тогда `|𝒬_{≤K}| ≤ 2K·|𝔠_cov|`.

**Теорема 17.1 (terminal bridge).** Каждая charged-вершина возникает из occupied rank-(3,3) support;
$$|\mathcal O|\ \ll\ \mathcal M_{03}+\mathcal M_{30},\qquad |\mathcal Q_{\le K}|\ \ll\ P^{o(1)}(\mathcal M_{03}+\mathcal M_{30}).$$

## Статус

🟡 **локально.** Cover-нормировка корректна; «мост» к terminal-резервуарам опирается на divisor-bound
для факторизаций fixed-support — требует строгой проверки fiber-bound (ledger §27.8: fixed occupied
support фиксирует `r,m,C,D` с кратностью `≤ P^{o(1)}`).

## Ссылки

- BE_UPDATED §16–17; ledger §9–10, §27.7–27.8 (first-charge disjointness, fiber-bound).
