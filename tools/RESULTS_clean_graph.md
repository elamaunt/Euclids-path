# RESULTS: clean/boundary split — куда переходит трудность

Харнесс: clean-continuation trace (A=200), 300 clean non-twin стартов выше 10⁶/6.

## Числа

| исход clean non-twin центра | доля |
|---|---|
| есть CLEAN active-ребро (clean continuation) | 122/300 = **40.7%** |
| ВСЕ active-рёбра → boundary (unclean цель) | 178/300 = **59.3%** |
| нет active-ребра (twin) | 0 |

## Что это значит

Исправление автора **корректно**: unclean малый twin (18) теперь классифицируется как **BoundaryExit**,
а не CleanSink — он больше не «решает» теорему. `clean_sink_is_twin` + `clean_sink_above` доказаны
(`Engine/CleanGraph.lean`): **CleanSink ⟹ twin выше M₀**. ✅

**Но** clean-граф **не самодостаточен**: у 59% clean центров ВСЕ рёбра уходят в boundary. То есть
спуск в clean-графе почти сразу упирается в BoundaryExit, и достижение CleanSink **не гарантировано**.
Значит вся нагрузка переходит на обработку BoundaryExit — `boundary_exit_regenerates`
(boundary-state регенерирует / даёт engine), который в исходном скелете — **axiom**.

## Вывод (честно)

Исправление **закрыло локальный разрыв** (unclean sink больше не годится как twin) и **точно
локализовало** оставшуюся трудность: она вся теперь в **boundary-ledger** — доказать, что каждый
BoundaryExit регенерирует (не тупик) без счёта/распределения. Это тот же old-peel/NOPSL узел
(`regenerate` / fan-in), теперь — единственный и явный. `Step00` НЕ закрыт; gap перемещён, не снят.
