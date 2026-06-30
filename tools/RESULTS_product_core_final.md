# RESULTS: product-core pump — финальная сборка (что доказано / что осталось)

## Доказано в Lean (ProductCore.lean, стандартные аксиомы, без sorry)

Вся внутренняя машина pump:
- no_mismatch_core_eq (Fix1 extensionality, трилемма устранена);
- ambient_factor_lt_primorial + ambientLegal_delete (Fix2, a<P_A на всех рангах);
- coreSig_fintype (Fix3, конечность при фикс. A);
- no_productHall (residue инъективна);
- rank_one_coreCollision_absurd (БАЗА чистой арифметикой, не внешний SNOL);
- deleteFactor + delete_preserves_coreSig + core_step_succ + core_step_proved (DESCENT доказан);
- coreCollision_of_infinite (PIGEONHOLE доказан: inf домен -> конечная CoreSig -> коллизия);
- product_core_engine_of_carrier (ФИНАЛ: carrier-данные => Engine).

То есть: descent, база, pigeonhole — ВСЁ доказано. Прежние стены (counting/fan-in, трилемма,
UniqueLegalLift, steering, 3 дефекта) — УСТРАНЕНЫ.

## Единственный оставшийся вход — CarrierData (структура от GlobalOldAbsorption)

product_core_engine_of_carrier берёт: бесконечное S стартов, node:ι->RankNode r, InjOn, AmbientLegal.
Это надо ПОСТРОИТЬ из carrier:
1. факторизация N=6m+σ = ∏ aᵢ (aᵢ>A) — существование разложения;
2. rank≤4 — ЧИСЛЕННО ПРОВЕРЕНО: держится для fixed κ<5 при A > 6^(1/(5-κ)).
   (κ=4.5: A>36; κ=4.8: A>7776; κ=4.9: A>6e7; κ→5: порог взрывается.) Согласуется с separating
   scale (тоже large A). Доказуемо при согласованных κ,A.
3. distinct cores: 6m₁+σ ≠ 6m₂+σ — тривиально;
4. бесконечность стартов — приходит из GlobalOldAbsorption (отдельная часть Step00).

## Статус

Step00 = sorry: CarrierData не построена внутри (она — мост к GlobalOldAbsorption + факторизация).
НО: вся pump-машина доказана; остался ОДИН структурный вход (carrier), не counting-стена.
rank≤4 — арифметика степеней (доказуемо при large A). Факторизация — существование (от carrier).
