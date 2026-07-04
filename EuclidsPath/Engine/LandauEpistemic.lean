/-
  LandauEpistemic — ЭПИСТЕМИЧЕСКИЙ КОМПЛЕМЕНТ 4-й проблемы Ландау (простые `n² + 1`).
  Зелёный фронт: Engine/LandauFront.lean (мост, вычетный факт); хребет честности:
  Engine/SideInfinitude.lean (Дирихле). Образцы эпистемики: PNPFirstCause,
  TwinNodeEpistemic, LehmerEpistemic; двигательный шаблон: PolignacManifestationFront.

  ЧТО ЭТО. Четыре слоя поверх LandauFront, ни один не решает открытую задачу:
    (а) КАНОНИЗАЦИЯ ГЕЙТА: `landau4thUnbounded_iff_infinite` — неограниченность
        простых `k² + 1` ⟺ бесконечность множества `LandauPrimes`; красный вход
        остаётся ровно ОДНИМ, обе формы взаимозаменяемы;
    (б) ЧЁТНЫЙ КАНАЛ: `landauPrime_even_of_two_lt` (всякое простое `k² + 1 > 2`
        требует чётного `k`) и `landau4thUnbounded_iff_even_k` — гейт локализован
        на чётный канал (прямая стрелка через `max N 1`: свидетель `k = 1` при
        `N = 0` нечётен и честно обходится краевым сдвигом);
    (в) МОСТ К ДИРИХЛЕ: `landau_lives_in_dirichlet_class` — простые Ландау лежат
        в `{2} ∪ {p ≡ 1 mod 4}`, а объемлющий класс `1 mod 4` РЕАЛЬНО бесконечен
        (тот же mathlib-Дирихле `Nat.forall_exists_prime_gt_and_modEq`, что в
        SideInfinitude); плюс стена делителей `landauFactor_mod_four` — всякий
        нечётный простой делитель `k² + 1` сравним с `1 mod 4` (квадратичная
        взаимность mathlib). Дирихле даёт бесконечную объемлющую шеренгу,
        открыта именно СЕЛЕКЦИЯ внутри неё (маркер `NoSelectionClaimed` — тот же
        жанр честности, что `NoPairingClaimed` у сторон близнецов);
    (г) ЭПИСТЕМИКА: `InternalisedLandauGround` (ground = гейт, beyondOwnHorizon =
        свидетель отсутствия), `no_internalisedLandauGround`,
        `landauCause_unknowable`; закон манифестации `LandauManifestationLaw`
        (НЕ декретирован) и двигательный факт `landauRefutation_carries_engine`
        полиньяк-класса.

  ЧЕСТНОСТЬ (обязательные раскрытия, CORR учтён).
  (1) НЕ решение 4-й проблемы Ландау и НЕ Гёдель: про открытую бесконечность
      простых `n² + 1` НЕ утверждается НИЧЕГО (лучшее известное — Иванец 1978:
      бесконечно много `n² + 1` с ≤ 2 простыми множителями, здесь отсутствует);
      никакая независимость не заявляется — только самоуничтожение внутреннего
      самообоснования.
  (2) ПАРА ground/beyondOwnHorizon ТАВТОЛОГИЧНА: это `P ∧ ¬P` в свидетельской
      упаковке (коллатц-класс упаковки, НЕ pnp-класс: у `InternalisedPNPGround`
      противоречие поставляет ВНЕШНИЙ зелёный пижонхол
      `no_fullPayment_of_unboundedSupply`, здесь — сами поля друг о друга).
      Раскрыто машинно: `internalisedLandauGround_semantically_selfNegating`.
  (3) ОПЛАТА СОДЕРЖАТЕЛЬНОСТИ ДВУХСЛОЙНАЯ, И ОБА СЛОЯ СЛАБЕЕ ЭТАЛОНОВ:
      * `landauRefutation_carries_engine` — подлинная двигательная конструкция
        (двигатель-свидетель как объект через
        `infiniteFlows_in_stableNoEnergy_build_engine`), но ГЕЙЧЕНА
        недекретированным `LandauManifestationLaw` — полиньяк-класс, слабее
        безусловного `nonHalting_carries_perpetual_engine` Коллатца и
        безусловного пижонхола `no_fullPayment_of_unboundedSupply` P/NP;
      * `landau_supply_parityWalled` — БЕЗУСЛОВНАЯ зелёная стена, но закрывает
        только НЕЧЁТНЫЙ канал; на чётном канале, где живёт вся открытая суть,
        ни стены, ни поставки зелёно нет.
      Без слоя двигателя связка выродилась бы в чистую тавтологию — поэтому
      манифестационный слой (§4) встроен сюда как пререквизит эпистемики (§5).
  (4) ЗАКОН НЕ ДЕКРЕТИРОВАН — при ПОЛОЖИТЕЛЬНОМ знаке эвристики (Харди–Литтлвуд
      предсказывает бесконечность): прецедент Полиньяка — серийное расширение
      декрета обесценило бы карантин; Ландау НЕ входит в четыре границы
      step00FirstCause, и границы здесь НЕ добавляются.
  (5) КОВАТЬ НЕЧЕГО: `k² + 1` — значения квадратичной формы на ВСЕЙ сетке `k`,
      а не подпоследовательность-цепь (как 4c+1 у Мерсенна) — кованого свидетеля
      в этой ветви не существует за отсутствием субстрата ковки (как у кузенов).

  Никакого sorry, никакой новой аксиомы, никакого native_decide; карантин
  (Engine/CausalClosureAxiom) НЕ импортируется. Таинт репозитория (47) НЕ меняется.

  Компиляция: cd /f/Primes/Euclids-path &&
    "$USERPROFILE/.elan/bin/lake.exe" env lean EuclidsPath/Engine/LandauEpistemic.lean
-/
import Mathlib
import EuclidsPath.Engine.LandauFront
import EuclidsPath.Engine.SideInfinitude
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath.LandauFront.Epistemic

open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation

/-! ## §1. Канонизация гейта: неограниченность ⟺ бесконечность (🟢) -/

/-- 🟢 **КАНОНИЗАЦИЯ ГЕЙТА (доказано):** `Landau4thUnbounded` ⟺
    `LandauPrimes.Infinite`. Прямая стрелка — существующий мост
    `landauPrimes_infinite_of_unbounded`; обратная — конечность `Set.Iic` на ℕ:
    если выше `N` нет простых `k² + 1`, всё множество влезает под крышку
    `N² + 1`. Красный вход остаётся ровно ОДНИМ — обе формы взаимозаменяемы,
    гейт не двоится на «родственные» открытые входы. -/
theorem landau4thUnbounded_iff_infinite :
    Landau4thUnbounded ↔ LandauPrimes.Infinite := by
  constructor
  · exact landauPrimes_infinite_of_unbounded
  · intro hInf N
    by_contra h
    push Not at h
    refine hInf ((Set.finite_Iic (N ^ 2 + 1)).subset ?_)
    rintro p ⟨k, rfl, hp⟩
    have hk : k ≤ N := by
      by_contra hgt
      push Not at hgt
      exact h k hgt hp
    have hle : k ^ 2 + 1 ≤ N ^ 2 + 1 := by nlinarith
    exact Set.mem_Iic.mpr hle

/-! ## §2. Чётный канал: гейт локализован на чётные `k` (🟢) -/

/-- 🟢 **ЧЁТНЫЙ КАНАЛ (доказано):** всякое простое `k² + 1 > 2` требует
    ЧЁТНОГО `k` — при нечётном `k` число `k² + 1` чётно и потому равно `2`
    (реюз `oddLandauPrime_even_k`). -/
theorem landauPrime_even_of_two_lt {k : ℕ} (hp : (k ^ 2 + 1).Prime)
    (h2 : 2 < k ^ 2 + 1) : Even k := by
  rcases Nat.even_or_odd k with he | ho
  · exact he
  · exact absurd (oddLandauPrime_even_k ho hp) (ne_of_gt h2)

/-- 🟢 **ГЕЙТ ⟺ ЧЁТНЫЙ ГЕЙТ (доказано):** неограниченность простых `k² + 1`
    равносильна неограниченности по ЧЁТНЫМ `k`. Существующий вычетный факт
    перестаёт быть украшением: область поиска гейта честно сужена вдвое, все
    свидетели выше `1` вынуждены быть чётными. ТЕХНИКА (CORR): прямая стрелка
    применяет гейт к `max N 1` — при `N = 0` свидетель `k = 1` (простое `2`)
    нечётен, краевой сдвиг обходит его без потери неограниченности. -/
theorem landau4thUnbounded_iff_even_k :
    Landau4thUnbounded ↔
      ∀ N : ℕ, ∃ k : ℕ, N < k ∧ Even k ∧ (k ^ 2 + 1).Prime := by
  constructor
  · intro H N
    obtain ⟨k, hk, hp⟩ := H (max N 1)
    have hN : N < k := lt_of_le_of_lt (le_max_left N 1) hk
    have h1 : 1 < k := lt_of_le_of_lt (le_max_right N 1) hk
    have h2 : 2 < k ^ 2 + 1 := by nlinarith
    exact ⟨k, hN, landauPrime_even_of_two_lt hp h2, hp⟩
  · intro H N
    obtain ⟨k, hk, _, hp⟩ := H N
    exact ⟨k, hk, hp⟩

/-- 🟢 **КЛАСС `1 mod 4` (доказано):** всякое простое `k² + 1 > 2` сравнимо с
    `1` по модулю `4` — чётное `k = j + j` даёт `k² + 1 = 4j² + 1`. -/
theorem landauPrime_mod_four {k : ℕ} (hp : (k ^ 2 + 1).Prime)
    (h2 : 2 < k ^ 2 + 1) : (k ^ 2 + 1) % 4 = 1 := by
  obtain ⟨j, hj⟩ := landauPrime_even_of_two_lt hp h2
  have h : k ^ 2 + 1 = 4 * j ^ 2 + 1 := by subst hj; ring
  rw [h, Nat.mul_add_mod]

/-! ## §3. Мост к SideInfinitude: объемлющий класс Дирихле `1 mod 4` (🟢) -/

/-- 🟢 **ОБЪЕМЛЮЩИЙ КЛАСС НЕОГРАНИЧЕН (доказано, РЕАЛЬНЫЙ Дирихле):** над любым
    `n` есть простое `p ≡ 1 (mod 4)` — тот же mathlib-двигатель
    `Nat.forall_exists_prime_gt_and_modEq` (аналитика L-рядов), что у
    `minusSide_primes_unbounded` в SideInfinitude, при `q := 4`, `a := 1`. -/
theorem onemodfour_primes_unbounded (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ p % 4 = 1 := by
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 1) (by norm_num) (by decide)
  exact ⟨p, hgt, hp, by simpa [Nat.ModEq] using hmod⟩

/-- 🟢 Та же неограниченность в форме `Set.Infinite`. -/
theorem onemodfour_primes_infinite :
    {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hgt, hp, hmod⟩ := onemodfour_primes_unbounded B
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p % 4 = 1} := ⟨hp, hmod⟩
  exact absurd (hB hmem) (not_le.mpr hgt)

/-- 🟢 **ВЛОЖЕНИЕ (доказано):** простые Ландау лежат в `{2} ∪ {p ≡ 1 mod 4}` —
    класс объемлющего Дирихле; единственное исключение — `2 = 1² + 1`. -/
theorem landauPrimes_subset_onemodfour :
    LandauPrimes ⊆ {2} ∪ {p : ℕ | p.Prime ∧ p % 4 = 1} := by
  rintro p ⟨k, rfl, hp⟩
  rcases Nat.lt_or_ge 2 (k ^ 2 + 1) with h2 | h2
  · exact Set.mem_union_right _ ⟨hp, landauPrime_mod_four hp h2⟩
  · have h : k ^ 2 + 1 = 2 := le_antisymm h2 hp.two_le
    exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr h)

/-- 🟢 **СТЕНА ДЕЛИТЕЛЕЙ `mod 4` (доказано, настоящая теория формы):** всякий
    НЕЧЁТНЫЙ простой делитель `q ∣ k² + 1` сравним с `1` по модулю `4` — из
    `q ∣ k² + 1` следует, что `−1` — квадрат в `ZMod q`, а mathlib-критерий
    квадратичной взаимности (`ZMod.exists_sq_eq_neg_one_iff`) запрещает это при
    `q ≡ 3 (mod 4)`. Весь спектр делителей формы (не только сами простые
    Ландау) прижат к классу `1 mod 4` — арифметический скелет, на котором стоят
    почти-простые результаты типа Иванца. -/
theorem landauFactor_mod_four {q k : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hdvd : q ∣ k ^ 2 + 1) : q % 4 = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h0 : ((k : ZMod q) ^ 2 + 1) = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    have hcast : ((k ^ 2 + 1 : ℕ) : ZMod q) = ((q * t : ℕ) : ZMod q) := by
      rw [ht]
    push_cast at hcast
    rw [ZMod.natCast_self, zero_mul] at hcast
    exact hcast
  have hsq : IsSquare (-1 : ZMod q) := ⟨(k : ZMod q), by linear_combination -h0⟩
  have h3 : q % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  have h2 : q % 2 = 1 := Nat.odd_iff.mp hodd
  omega

/-- 🟢 **«ДИРИХЛЕ ДАЁТ ШЕРЕНГУ, НО НЕ СЕЛЕКЦИЮ» — ТОЧНАЯ ФОРМА:** простые
    Ландау живут в классе `1 mod 4` объемлющего Дирихле (`⊆`), и этот класс
    РЕАЛЬНО бесконечен (mathlib-Дирихле). Открыта именно СЕЛЕКЦИЯ значений
    `k² + 1` внутри бесконечной шеренги — квадратичную форму Дирихле не
    достаёт (см. `NoSelectionClaimed` ниже). -/
theorem landau_lives_in_dirichlet_class :
    LandauPrimes ⊆ {2} ∪ {p : ℕ | p.Prime ∧ p % 4 = 1} ∧
      {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite :=
  ⟨landauPrimes_subset_onemodfour, onemodfour_primes_infinite⟩

/-- **ЧЕСТНОСТЬ (охват):** бесконечность ОБЪЕМЛЮЩЕГО класса `1 mod 4` зелёная
    (Дирихле), но она НЕ даёт бесконечности СЕЛЕКЦИИ — простых, попадающих на
    квадратичную форму `k² + 1`. Селекция — вся открытая суть 4-й проблемы
    Ландау, и здесь она НЕ утверждается, НЕ доказана и ниоткуда не выводится.
    Тот же жанр честности, что `NoPairingClaimed` у сторон близнецов
    (SideInfinitude) — маркер намеренно оплачен тем же трюизмом. -/
abbrev NoSelectionClaimed : Prop := True

theorem noSelectionClaimed : NoSelectionClaimed :=
  EuclidsPath.SideInfinitude.noPairingClaimed

/-! ## §4. Свидетель отсутствия, закон манифестации, двигатель (🟢-плумбинг,
    закон — гейт; зеркало кузен-семьи PolignacManifestationFront)

    ⚠️ Секции цепи (аналога ковки Мерсенна) здесь НЕТ намеренно: `k² + 1` —
    значения формы на всей сетке, а не подпоследовательность-цепь; кованого
    свидетеля не существует за отсутствием субстрата ковки (как у кузенов). -/

/-- **Отсутствие простых Ландау выше `P`** (Π-свидетель, зеркало
    `CousinAbsenceAbove`): каждый `k` с простым `k² + 1` сидит не выше `P`. -/
def LandauAbsenceAbove (P : ℕ) : Prop :=
  ∀ k : ℕ, (k ^ 2 + 1).Prime → k ≤ P

/-- 🟢 Плумбинг: из ограниченности извлекается свидетель отсутствия. -/
theorem exists_landauAbsence_of_not_unbounded (h : ¬ Landau4thUnbounded) :
    ∃ P : ℕ, LandauAbsenceAbove P := by
  unfold Landau4thUnbounded at h
  push Not at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun k hk => by
    by_contra hgt
    exact hP k (by omega) hk⟩

/-- 🟢 Плумбинг: гейт ⟺ свидетелей отсутствия нет (свидетельская форма
    отрицания — ею оплачено поле `beyondOwnHorizon` ниже). -/
theorem landau4thUnbounded_iff_no_absence :
    Landau4thUnbounded ↔ ∀ P : ℕ, ¬ LandauAbsenceAbove P := by
  constructor
  · intro hU P hAbs
    obtain ⟨k, hlt, hp⟩ := hU P
    exact absurd (hAbs k hp) (by omega)
  · intro hNo
    by_contra h
    obtain ⟨P, hAbs⟩ := exists_landauAbsence_of_not_unbounded h
    exact hNo P hAbs

/-- 🟢 **M8 (локализация домена свидетеля):** всякая граница отсутствия ≥ 26 —
    `26² + 1 = 677` просто (norm_num). Свидетель отсутствия зелёно непредъявим
    в начальном сегменте. -/
theorem landauAbsenceBound_ge_26 {P : ℕ}
    (hAbs : LandauAbsenceAbove P) : 26 ≤ P :=
  hAbs 26 (by norm_num)

/-- Отсутствие выше `P` манифестирует арифметически: на каждом леджер-масштабе
    не ниже `P`, всюду где проекция сводит книги, отсутствие проявляется
    неоплатимой бесконечной поставкой потоков (объект заимствован у римановского
    фронта — `DeviationFlowSupply`; свидетель содержательности L1 живёт ТАМ ЖЕ,
    `deviationFlowSupply_of_twinBound`, и здесь НЕ передоказывается). -/
def LandauAbsenceManifests (P : ℕ) : Prop :=
  ∀ (A M0 : ℕ), P ≤ M0 →
    ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
      SemanticExtendedFlowLedgerCollisionResolves proj →
        DeviationFlowSupply A M0

/-- **ЗАКОН МАНИФЕСТАЦИИ ЛАНДАУ** — гейчен свидетелем отсутствия (зеркало
    `CousinManifestationLaw`). Негейченная форма `∀ P, LandauAbsenceManifests P`
    при `P := 0` вместе с принятой границей дала бы поставку на разрешённом
    масштабе — противоречие с зелёной `no_deviationFlowSupply_at_resolved_scale`
    (точный механизм провала манифестационных кандидатов ЯМ/НС). ⚠️ ПОЛЕ НЕ
    ДЕКРЕТИРОВАНО — при ПОЛОЖИТЕЛЬНОМ знаке Харди–Литтлвуда: прецедент
    Полиньяка — серийное расширение декрета обесценило бы карантин;
    единственность принятой границы и есть его содержание. -/
def LandauManifestationLaw : Prop :=
  ∀ P : ℕ, LandauAbsenceAbove P → LandauAbsenceManifests P

/-- 🟢 **«ОПРОВЕРЖЕНИЕ ПРЕДЪЯВЛЯЕТ ДВИГАТЕЛЬ» (M3⁺, полиньяк-класс):**
    свидетель отсутствия + закон + сведённые книги на масштабе не ниже `P`
    манифестируют вечный двигатель — как ОБЪЕКТ
    (`ConcreteEuclideanEngineWitness`), до убийства lexRank'ом.
    ЧЕСТНОСТЬ: конструкция подлинная (через
    `infiniteFlows_in_stableNoEnergy_build_engine`), но ГЕЙЧЕНА
    недекретированным `LandauManifestationLaw` — двигательный факт
    ПОЛИНЬЯК-КЛАССА, слабее безусловного `nonHalting_carries_perpetual_engine`
    Коллатца и безусловного пижонхола `no_fullPayment_of_unboundedSupply` P/NP. -/
theorem landauRefutation_carries_engine
    (hLaw : LandauManifestationLaw)
    {P : ℕ} (hAbs : LandauAbsenceAbove P)
    {A M0 : ℕ} (hM : P ≤ M0)
    (proj : SemanticExtendedFlowLedgerProjection A M0)
    (hres : SemanticExtendedFlowLedgerCollisionResolves proj) :
    ConcreteEuclideanEngineWitness A M0 := by
  have hStable : NoEnergyStableUniverse proj :=
    (noEnergyStableUniverse_iff_resolves proj).mpr hres
  obtain ⟨𝓕, h𝓕⟩ := hLaw P hAbs A M0 hM proj hres
  obtain ⟨_, _, _, hEngine⟩ :=
    infiniteFlows_in_stableNoEnergy_build_engine hStable h𝓕
  exact hEngine

/-- 🟢 **M3 — ESSENCE (зеркало кузенов):** двигателей нет + принятая граница +
    закон манифестации ⟹ гейт Ландау. Все три гипотезы потребляются
    ПО-НАСТОЯЩЕМУ: из ограниченности извлекается свидетель `P`; граница даёт
    разрешение ровно на масштабе `M0 := P`; закон поставляет семью (не ex
    falso); из коллизии строится двигатель-СВИДЕТЕЛЬ; убивает его `hNoEngine`. -/
theorem landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LandauManifestationLaw) :
    Landau4thUnbounded := by
  by_contra hBounded
  obtain ⟨P, hAbs⟩ := exists_landauAbsence_of_not_unbounded hBounded
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf P) :=
    strictSemanticExtended_resolves_old (hres P)
  exact hNoEngine ⟨A, P,
    landauRefutation_carries_engine hLaw hAbs (le_refl P) (projOf P) hResolves⟩

/-- 🟢 Зелёное доведение до цели программы: та же тройка ⟹ множество простых
    Ландау бесконечно (композиция с мостом `landauPrimes_infinite_of_unbounded`). -/
theorem landauPrimesInfinite_of_noEngine_boundary_and_manifestation
    (hNoEngine : ¬ SomeConcreteEuclideanEngine)
    (hBoundary : TheStrictLastStep00Obligation)
    (hLaw : LandauManifestationLaw) :
    LandauPrimes.Infinite :=
  landauPrimes_infinite_of_unbounded
    (landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
      hNoEngine hBoundary hLaw)

/-! ## §5. Эпистемика: внутреннее решение = самообоснование за горизонтом -/

/-- **Внутреннее самообоснование решения Ландау.** Поле `ground` — сам гейт
    (`Landau4thUnbounded` — красный закон формы; у Ландау НЕТ границы в
    step00FirstCause, и ground — не декрет-проекция, как у Коллатца);
    поле `beyondOwnHorizon` — свидетель отсутствия (свидетельская форма
    отрицания через `landau4thUnbounded_iff_no_absence`; оба поля потребляются
    в `no_internalisedLandauGround`, запрет вакуумности №3 соблюдён).

    ⚠️ ЧЕСТНАЯ ОГОВОРКА (обязательная): пара ТАВТОЛОГИЧНА — это `P ∧ ¬P` в
    свидетельской упаковке (коллатц-класс, НЕ pnp-класс: там противоречие
    поставлял внешний зелёный пижонхол). Раскрыто машинно ниже
    (`internalisedLandauGround_semantically_selfNegating`). Содержательность
    оплачивается НЕ формой структуры, а двумя внешними слоями — двигательной
    конструкцией `landauRefutation_carries_engine` (гейченной законом,
    полиньяк-класс) и безусловной стеной нечётного канала
    `landau_supply_parityWalled`; оба слоя слабее эталонов (см. шапку файла). -/
structure InternalisedLandauGround : Prop where
  ground : Landau4thUnbounded
  beyondOwnHorizon : ∃ P : ℕ, LandauAbsenceAbove P

/-- «Внутреннее знание причины Ландау» = внутреннее самообоснование решения. -/
abbrev InternalKnowledgeOfLandauCause : Prop := InternalisedLandauGround

/-- 🟢 Самообоснование самоуничтожается — одна строка через плумбинг
    `landau4thUnbounded_iff_no_absence` (зеркало `no_internalisedPNPGround`;
    честно: противоречие здесь поставляют САМИ поля, см. оговорку структуры). -/
theorem no_internalisedLandauGround : InternalisedLandauGround → False :=
  fun H => by
    obtain ⟨P, hAbs⟩ := H.beyondOwnHorizon
    exact landau4thUnbounded_iff_no_absence.mp H.ground P hAbs

/-- 🟢 **«УЗНАТЬ НЕЛЬЗЯ ИЗНУТРИ» — ТЕОРЕМА** (зеркало `collatzCause_unknowable`,
    `pnpCause_unknowable`, `lehmerCause_unknowable`): внутреннее самообоснование
    решения Ландау невозможно. НЕ утверждение о самой 4-й проблеме: гейт
    остаётся открытым красным входом. -/
theorem landauCause_unknowable : ¬ InternalKnowledgeOfLandauCause :=
  no_internalisedLandauGround

/-- 🟢 **МАШИННАЯ ЧЕСТНОСТЬ (тавтологичность раскрыта):** структура
    `InternalisedLandauGround` доказуемо эквивалентна контрадикторной паре
    «гейт ∧ ¬гейт» (обратная стрелка — ex falso, честно). Это СЛАБЕЕ
    pnp-аналога `internalisedPNPGround_semantically_selfNegating`: там
    эквивалентность оплачена внешним точным законом оплаты, здесь — прямой
    перепаковкой отрицания. Содержательность модуля живёт в §3–§4, не здесь. -/
theorem internalisedLandauGround_semantically_selfNegating :
    InternalisedLandauGround ↔ (Landau4thUnbounded ∧ ¬ Landau4thUnbounded) := by
  constructor
  · intro H
    refine ⟨H.ground, fun hU => ?_⟩
    obtain ⟨P, hAbs⟩ := H.beyondOwnHorizon
    exact landau4thUnbounded_iff_no_absence.mp hU P hAbs
  · rintro ⟨hU, hnU⟩
    exact (hnU hU).elim

/-- 🟢 **СТЕНА НЕЧЁТНОГО КАНАЛА (безусловная):** внутренний вывод, слепой к
    рельсу чётности — «нечётные `k` неограниченно поставляют простые
    `k² + 1`» — опровергается БЕСПЛАТНО (реюз `oddLandauPrime_even_k`).
    ЧЕСТНОСТЬ: это аналог пижонхола P/NP лишь по ЖАНРУ — стена закрывает
    ТОЛЬКО нечётный канал; на чётном канале, где живёт вся открытая суть,
    зелёной стены нет и быть не может без решения самой задачи. -/
theorem landau_supply_parityWalled :
    (∀ N : ℕ, ∃ k : ℕ, N < k ∧ Odd k ∧ (k ^ 2 + 1).Prime) → False := by
  intro h
  obtain ⟨k, hgt, hodd, hp⟩ := h 1
  have h2 : k ^ 2 + 1 = 2 := oddLandauPrime_even_k hodd hp
  have h3 : 2 < k ^ 2 + 1 := by nlinarith
  exact absurd h2 (ne_of_gt h3)

/-- 🟢 **«РЕШЕНИЕ ЗАПЕРТО ЗА ДВИГАТЕЛЕМ» — 3-РАЗВИЛКА (зеркало
    `twin_no_internal_decision_without_engine`,
    `pnp_no_internal_decision_without_engine`):**
    (1) ОПРОВЕРГНУТЬ при законе = предъявить двигатель-свидетель
        (`landauRefutation_carries_engine`; цена честно видна: закон
        `LandauManifestationLaw` НЕ декретирован — полиньяк-класс);
    (2) САМООБОСНОВАТЬ решение изнутри — самоуничтожается
        (`no_internalisedLandauGround`);
    (3) единственный без-двигательный путь — ВНЕШНЕЕ ПРИНЯТИЕ гейта: оно влечёт
        бесконечность простых Ландау (`landauPrimes_infinite_of_unbounded`;
        сам гейт здесь НЕ утверждается).
    НЕ утверждается гёделевская независимость и НЕ решение 4-й проблемы —
    только: оба внутренних решения стоят вечного двигателя. -/
theorem landau_no_internal_decision_without_engine :
    (∀ P : ℕ, LandauAbsenceAbove P → LandauManifestationLaw →
      ∀ (A M0 : ℕ), P ≤ M0 →
      ∀ proj : SemanticExtendedFlowLedgerProjection A M0,
        SemanticExtendedFlowLedgerCollisionResolves proj →
          ConcreteEuclideanEngineWitness A M0) ∧
    (InternalisedLandauGround → False) ∧
    (Landau4thUnbounded → LandauPrimes.Infinite) :=
  ⟨fun _P hAbs hLaw _A _M0 hM proj hres =>
      landauRefutation_carries_engine hLaw hAbs hM proj hres,
   no_internalisedLandauGround,
   landauPrimes_infinite_of_unbounded⟩

/-- 🟢 Итоговый эпистемический статус Ландау (зеркало
    `pnp_locked_behind_engine_status` — БЕЗ декрет-конъюнкта: гейт НЕ принят,
    границы у Ландау нет и она не добавляется):
    (1) решить изнутри нельзя (теорема);
    (2) нечётный канал стенирован безусловно (теорема);
    (3) двигатель запрещён (`no_someConcreteEuclideanEngine`, lexRank);
    (4) закон + граница ⟹ гейт (закон НЕ декретирован — вся цена видна);
    (5) гейт канонизирован: неограниченность ⟺ бесконечность (теорема).
    ЦЕЛИКОМ ЗЕЛЁНАЯ: конъюнкты 1–3, 5 безусловны; 4 — условная стрелка. -/
theorem landau_locked_behind_engine_status :
    (¬ InternalKnowledgeOfLandauCause) ∧
    ((∀ N : ℕ, ∃ k : ℕ, N < k ∧ Odd k ∧ (k ^ 2 + 1).Prime) → False) ∧
    (¬ SomeConcreteEuclideanEngine) ∧
    (LandauManifestationLaw → TheStrictLastStep00Obligation → Landau4thUnbounded) ∧
    (Landau4thUnbounded ↔ LandauPrimes.Infinite) :=
  ⟨landauCause_unknowable,
   landau_supply_parityWalled,
   no_someConcreteEuclideanEngine,
   fun hLaw hBoundary =>
     landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
       no_someConcreteEuclideanEngine hBoundary hLaw,
   landau4thUnbounded_iff_infinite⟩

/-! ## Аудит аксиом: весь модуль зелёный (максимум стандартная тройка),
    карантин не импортирован, таинт репо (47) НЕ меняется -/
#print axioms landau4thUnbounded_iff_infinite
#print axioms landauPrime_even_of_two_lt
#print axioms landau4thUnbounded_iff_even_k
#print axioms landauPrime_mod_four
#print axioms onemodfour_primes_unbounded
#print axioms onemodfour_primes_infinite
#print axioms landauPrimes_subset_onemodfour
#print axioms landauFactor_mod_four
#print axioms landau_lives_in_dirichlet_class
#print axioms noSelectionClaimed
#print axioms exists_landauAbsence_of_not_unbounded
#print axioms landau4thUnbounded_iff_no_absence
#print axioms landauAbsenceBound_ge_26
#print axioms landauRefutation_carries_engine
#print axioms landau4thUnbounded_of_noEngine_and_boundary_and_manifestation
#print axioms landauPrimesInfinite_of_noEngine_boundary_and_manifestation
#print axioms no_internalisedLandauGround
#print axioms landauCause_unknowable
#print axioms internalisedLandauGround_semantically_selfNegating
#print axioms landau_supply_parityWalled
#print axioms landau_no_internal_decision_without_engine
#print axioms landau_locked_behind_engine_status

end EuclidsPath.LandauFront.Epistemic
