# RESULTS: глобальный absorber-узел — где финальная стена

Харнесс: полная траектория (clean→active→boundary→old-peel) для 2000 clean стартов (A=200).

## Числа

| исход полной траектории | доля |
|---|---|
| доходит до clean TWIN sink | 1430/2000 = **71.5%** |
| Q1 (peel не продолжается, absorber endpoint) | 570/2000 = **28.5%** |

Fan-in реален: один absorber-центр собирает **570 родословных**; малые центры (≤50) поглощают
**30%** массы. То есть «глобальное поглощение» свежих стартов конечным `O_{M₀}` — НАБЛЮДАЕТСЯ.

## Что доказано (BoundaryDecomp.lean, std axioms)

- `boundary_exit_decomposes` — BoundaryExit ⟹ меньший центр (old-peel) через `cofactor_is_center`. ✅
- `no_global_absorption_under_epmi` — сборка: `GlobalAbsorberNode` + `¬engine` ⟹ нет глобального
  поглощения ⟹ twin выше M₀. ✅ (но `GlobalAbsorberNode` — гипотеза)

## Финальная стена (честно)

`GlobalAbsorberNode` = «массовый fan-in в absorber ⟹ engine». Числа показывают fan-in реальным
(570→1 узел), НО превращение fan-in в engine — это **pigeonhole по волокну** (Hall-capacity), то есть
**счётный аргумент про размер волокна** = красная линия = ровно стена NOPSL §11, которую аудит уже
пометил. Distribution-free она не следует.

## Вывод

Вся программа честно сведена к ОДНОМУ глобальному узлу `GlobalAbsorberNode` (= no_global_old_twin_
absorption). Он НЕ локальная арифметика (та доказана), а глобальное pigeonhole-утверждение про fan-in,
эквивалентное счётной/Hall стене. `Step00` НЕ закрыт; это последний и единственный явный вход.
