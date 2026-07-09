# 10. O4C-res: нормировка terminal-рядов

> Lean-аналог: `EuclidsPath/Step10_O4CRes.lean` (заготовка)
> Источник: BE_UPDATED §18–22; ledger §11–16.

## Цель шага

Нормировать terminal-резервуары `ℳ₀₃+ℳ₃₀` через four-corner-произведение — ключевой вход в финальное
неравенство.

## Формулировки

**Целевая нормировка (Теорема 22.2).**
$$\mathcal M_{03}+\mathcal M_{30}\ \ll\ \frac{N_{03}N_{30}}{N_{00}}+P^\varepsilon.$$

**Incidence-модель.** `Ω` — множество `00`-центров (`|Ω|=N₀₀`); incidence-функции `A(u,x),B(v,x)∈{0,1}`;
локальные степени `a(x)=∑_u A(u,x)`, `b(x)=∑_v B(v,x)`; `N₀₃=∑_x a(x)`, `N₃₀=∑_x b(x)`;
four-corner `F₄=∑_x a(x)b(x)`. Нужна оценка
$$F_4\ \ll\ \frac{N_{03}N_{30}}{N_{00}}+\mathrm{Err}_{proj}.$$

**Exposed/light decomposition + RowLight ⇒ Projection obstruction.** Exposed-ряды оплачиваются
four-corner incidence; row-light-ряды должны создавать systematic projection discrepancy, списываемый
в charged-ledger [[07]] либо в `O(P^ε)`; first-charge ledger устраняет двойное списание.

## Статус

🔴 **ОТКРЫТО.** Это первый из несущих глобальных пробелов. Нужно строго доказать:
- совместная концентрация `a,b` ⇒ projection obstruction (ledger §27.1);
- `RowLight ⇒ Projection obstruction` без слов «должно быть» (ledger §27.2);
- first-charge disjointness (никакая масса не списывается дважды).

## Ссылки

- BE_UPDATED §18–22; ledger §11–16, §27.1–27.2, §27.7.
