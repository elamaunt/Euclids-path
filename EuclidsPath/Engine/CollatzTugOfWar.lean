/-
  Collatz как ПЕРЕТЯГИВАНИЕ КАНАТА (tug-of-war): двигатель против каната.
  Разбор: prose/55_Collatz.md. Числа: tools/collatz_engine_harness.py, tools/collatz_fuel_harness.py.

  Чтение автора: «соревнование двигателя и каната: двигатель продвигается НЕ БОЛЕЕ чем на
  1 ранг вперёд за шаг, канат тянет на 1 или 2 ранга назад; топливо кончается — двигатель
  стягивается к старту». Формализация МУЛЬТИПЛИКАТИВНАЯ (чистая ℕ-арифметика, без логарифмов):
  ранг = двоичный порядок; «+1 ранг» = не более удвоения, «−1 ранг» = ровно половина.

  ЗЕЛЁНОЕ ЯДРО (доказано здесь):
  - engine_at_most_one_rank : T n ≤ 2n               — двигатель: ≤ +1 ранг за ЛЮБОЙ шаг;
  - rope_pulls_one          : 2·T n = n  (n чёт.)    — канат: ровно −1 ранг;
  - rope_pulls_two          : 4·T²(n) = n (n≡0 mod4) — канат: −2 ранга за два шага;
  - window_budget           : 2^e·T^k(n) ≤ 2^t·n     — БЮДЖЕТ ОКНА: границы перемножаются
                              НЕЗАВИСИМО от порядка шагов (t нечётных, e чётных, t+e=k);
  - window_descends         : e > t в окне ⟹ T^k(n) < n — канат перетянул ⟹ строгий спуск;
  - reaches_one_of_countingLaw (ГЕРОЙ): закон каната ⟹ достижение 1.

  🔴 ИМЕНОВАННЫЙ ВХОД (открытое сердце, НЕ доказывается): RopeCountingLaw n — «в каждой
  позиции траектории ВЫШЕ цикла остановки (значение > 2) найдётся окно, где чётных шагов
  строго больше нечётных». Универсальная форма (∀ n ≥ 1) ОТКРЫТА: она ВЛЕЧЁТ гипотезу
  Коллатца (герой); обратное НЕ известно; она может быть строго сильнее гипотезы. При
  слиянии с репо этот вход становится полем `collatzBoundary` первопричины `step00FirstCause`
  (см. `Engine/CausalClosureAxiom` §18 и потребитель `Engine/CollatzFirstCause`).

  ЧЕСТНОСТЬ (три раскрытия):
  1) «Мост приговорённого»: ценностная форма закона (ValueDescentLaw) ЭКВИВАЛЕНТНА сходимости
     (valueLaw_iff_reaches_one) — сама по себе содержания НЕ добавляет. Содержательна только
     счётная форма; её обратная сторона (сходимость ⟹ счётный закон) НЕ утверждается:
     бюджет окна односторонен.
  2) Исходная форма «2·odd < even» ОТВЕРГНУТА: эмпирически e ≈ 1.016·t на ускоренной карте
     (halvings/triplings = 2.016 в сырой карте, минус 1 съеденное ускорением), т.е. e > 2t
     ЛОЖНО в среднем. Порог e > t — ТОЧНЫЙ порог, который грубая граница ×2 конвертирует
     в спуск, и он впритык (средний запас ~1.6%). Это цена отказа от log₂3.
  3) Окна длины 1 ПРОВАЛИВАЮТСЯ на каждой нечётной позиции (no_single_step_law) — согласовано
     со стеной CollatzFuel.no_monotone_height: монотонной высоты нет, закон ОБЯЗАН жить на
     окнах ≥ 2. На состоянии остановки закон вакуумен (countingLaw_1) — потому квантор
     ограничен «выше цикла»: от значения 1 шаги чередуются 1→2→1 и t ≥ e во ВСЕХ окнах,
     закон без ограничения был бы ложен для всякой сходящейся траектории.

  Дублирование T из CollatzEngine.lean НАМЕРЕННОЕ: три Collatz-ядра самодостаточны
  (core Lean, без Mathlib и без import); при слиянии дубли ушли только из потребителя.
-/

namespace EuclidsPath.Collatz.TugOfWar

/-- Ускоренная карта Коллатца (дубль CollatzEngine.T — файлы самодостаточны). -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Траектория: k шагов карты T от n (снятие ПЕРВОГО шага — удобно для бюджета окна). -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter k (T n)

/-- Число НЕЧЁТНЫХ шагов (ходов двигателя) в окне из k шагов от n. -/
def oddCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => oddCount k (T n) + (if n % 2 = 0 then 0 else 1)

/-- Число ЧЁТНЫХ шагов (рывков каната) в окне из k шагов от n. -/
def evenCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => evenCount k (T n) + (if n % 2 = 0 then 1 else 0)

/-! ## Двигатель и канат: пошаговые границы (зелёные) -/

/-- **ДВИГАТЕЛЬ: не более +1 ранга за шаг.** `T n ≤ 2n` для ВСЕХ n: нечётный шаг
    (3n+1)/2 ≤ 2n при n ≥ 1 (нечётное n ≥ 1 автоматически), чётный — тем более. -/
theorem engine_at_most_one_rank (n : Nat) : T n ≤ 2 * n := by
  unfold T
  by_cases h : n % 2 = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **Точный расход топлива нечётного шага:** `2·T n = 3n+1` — двигатель платит ×1.5+ε,
    а НЕ ×2; граница ×2 — грубая (см. честность-2 в шапке). -/
theorem engine_exact_fuel (n : Nat) (ho : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  unfold T; rw [if_neg (by omega : ¬ n % 2 = 0)]; omega

/-- **КАНАТ: ровно −1 ранг на чётном шаге:** `2·T n = n` («тянет на 1»). -/
theorem rope_pulls_one (n : Nat) (he : n % 2 = 0) : 2 * T n = n := by
  unfold T; rw [if_pos he]; omega

/-- **КАНАТ: −2 ранга за два чётных шага** (n ≡ 0 mod 4): `4·T²(n) = n` («тянет на 2»). -/
theorem rope_pulls_two (n : Nat) (h4 : n % 4 = 0) : 4 * iter 2 n = n := by
  have e1 : T n = n / 2 := by unfold T; rw [if_pos (by omega : n % 2 = 0)]
  have e2 : T (n / 2) = n / 2 / 2 := by
    unfold T; rw [if_pos (by omega : n / 2 % 2 = 0)]
  have e3 : iter 2 n = T (T n) := rfl
  rw [e3, e1, e2]
  omega

/-- Двигатель не глохнет в нуле: при n ≥ 1 шаг сохраняет n ≥ 1. -/
theorem T_pos (n : Nat) (h : 1 ≤ n) : 1 ≤ T n := by
  unfold T
  by_cases hp : n % 2 = 0
  · rw [if_pos hp]; omega
  · rw [if_neg hp]; omega

theorem iter_pos (j n : Nat) (h : 1 ≤ n) : 1 ≤ iter j n := by
  induction j generalizing n with
  | zero => exact h
  | succ j ih => simp only [iter]; exact ih (T n) (T_pos n h)

/-- Склейка траектории: `T^(j+k) = T^k ∘ T^j`. -/
theorem iter_add (j k n : Nat) : iter (j + k) n = iter k (iter j n) := by
  induction j generalizing n with
  | zero => simp [iter]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [iter]
    exact ih (T n)

/-- Учёт шагов: окно из k шагов = t нечётных + e чётных, t + e = k. -/
theorem counts_total (k n : Nat) : oddCount k n + evenCount k n = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [oddCount, evenCount]
    have h := ih (T n)
    by_cases hp : n % 2 = 0
    · simp only [if_pos hp]; omega
    · simp only [if_neg hp]; omega

/-! ## Бюджет окна — зелёное ядро перетягивания -/

/-- **БЮДЖЕТ ОКНА.** За k шагов от n с t = oddCount нечётными и e = evenCount чётными:
    `2^e · T^k(n) ≤ 2^t · n`. Каждый рывок каната множит РОВНО на ½ (rope_pulls_one),
    каждый ход двигателя — НЕ БОЛЕЕ чем на 2 (engine_at_most_one_rank); границы
    перемножаются при ЛЮБОМ порядке шагов. Чистая ℕ-арифметика: floor-деления съедены
    точностью границ, логарифмы не нужны. -/
theorem window_budget (k n : Nat) :
    2 ^ evenCount k n * iter k n ≤ 2 ^ oddCount k n * n := by
  induction k generalizing n with
  | zero =>
    simp only [iter, oddCount, evenCount]
    exact Nat.le_refl _
  | succ k ih =>
    simp only [iter, oddCount, evenCount]
    by_cases h : n % 2 = 0
    · simp only [if_pos h, Nat.add_zero]
      have hT : 2 * T n = n := rope_pulls_one n h
      calc 2 ^ (evenCount k (T n) + 1) * iter k (T n)
          = 2 * (2 ^ evenCount k (T n) * iter k (T n)) := by
            rw [Nat.pow_add_one, Nat.mul_comm (2 ^ evenCount k (T n)) 2, Nat.mul_assoc]
        _ ≤ 2 * (2 ^ oddCount k (T n) * T n) :=
            Nat.mul_le_mul (Nat.le_refl 2) (ih (T n))
        _ = 2 ^ oddCount k (T n) * (2 * T n) :=
            Nat.mul_left_comm 2 (2 ^ oddCount k (T n)) (T n)
        _ = 2 ^ oddCount k (T n) * n := by rw [hT]
    · simp only [if_neg h, Nat.add_zero]
      have hT : T n ≤ 2 * n := engine_at_most_one_rank n
      calc 2 ^ evenCount k (T n) * iter k (T n)
          ≤ 2 ^ oddCount k (T n) * T n := ih (T n)
        _ ≤ 2 ^ oddCount k (T n) * (2 * n) :=
            Nat.mul_le_mul (Nat.le_refl (2 ^ oddCount k (T n))) hT
        _ = 2 ^ (oddCount k (T n) + 1) * n := by rw [Nat.pow_add_one, Nat.mul_assoc]

/-- **Канат перетянул окно ⟹ строгий спуск.** Если чётных шагов СТРОГО больше (t < e),
    то `2^(t+1) ≤ 2^e`, бюджет даёт `2^t·(2·T^k(n)) ≤ 2^t·n`, сокращаем 2^t > 0:
    `2·T^k(n) ≤ n`, откуда `T^k(n) < n` при n ≥ 1. -/
theorem window_descends (k n : Nat) (h1 : 1 ≤ n)
    (hc : oddCount k n < evenCount k n) : iter k n < n := by
  have hb := window_budget k n
  have hmono : 2 ^ (oddCount k n + 1) ≤ 2 ^ evenCount k n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hchain : 2 ^ oddCount k n * (2 * iter k n) ≤ 2 ^ oddCount k n * n := by
    calc 2 ^ oddCount k n * (2 * iter k n)
        = 2 ^ (oddCount k n + 1) * iter k n := by rw [Nat.pow_add_one, Nat.mul_assoc]
      _ ≤ 2 ^ evenCount k n * iter k n := Nat.mul_le_mul hmono (Nat.le_refl (iter k n))
      _ ≤ 2 ^ oddCount k n * n := hb
  have hhalf : 2 * iter k n ≤ n :=
    Nat.le_of_mul_le_mul_left hchain (Nat.two_pow_pos (oddCount k n))
  omega

/-! ## Законы перетягивания: две формы, честная лестница -/

/-- **🔴 ЗАКОН ДОМИНИРОВАНИЯ КАНАТА (счётная форма) — именованный вход.** В каждой позиции
    траектории ВЫШЕ цикла остановки (значение > 2) найдётся окно, где чётных шагов строго
    больше нечётных. k > 0 автоматически (при k = 0 оба счёта равны 0). Здесь ТОЛЬКО
    определение: универсально по n это ОТКРЫТО (см. шапку). -/
def RopeCountingLaw (n : Nat) : Prop :=
  ∀ j : Nat, 2 < iter j n →
    ∃ k : Nat, oddCount k (iter j n) < evenCount k (iter j n)

/-- **Закон спуска значения (ценностная форма).** В каждой позиции выше цикла найдётся
    будущая позиция строго ниже. ВНИМАНИЕ: эта форма ЭКВИВАЛЕНТНА сходимости
    (valueLaw_iff_reaches_one) — «мост приговорённого», содержание не добавляется. -/
def ValueDescentLaw (n : Nat) : Prop :=
  ∀ j : Nat, 2 < iter j n → ∃ k : Nat, iter (j + k) n < iter j n

/-- Ступень лестницы: счётный закон ⟹ ценностный (через бюджет окна). -/
theorem valueLaw_of_countingLaw (n : Nat) (law : RopeCountingLaw n) :
    ValueDescentLaw n := by
  intro j hj
  cases law j hj with
  | intro k hk =>
    refine ⟨k, ?_⟩
    rw [iter_add j k n]
    exact window_descends k (iter j n) (by omega) hk

/-- Цикл остановки поглощает: после достижения 1 значения навсегда в {1, 2} (1→2→1). -/
theorem cycle_absorbs (n K : Nat) (hK : iter K n = 1) :
    ∀ d : Nat, iter (K + d) n = 1 ∨ iter (K + d) n = 2 := by
  intro d
  induction d with
  | zero => exact Or.inl hK
  | succ d ih =>
    have hstep : iter (K + (d + 1)) n = iter 1 (iter (K + d) n) := iter_add (K + d) 1 n
    rw [hstep]
    cases ih with
    | inl h => rw [h]; exact Or.inr (by decide)
    | inr h => rw [h]; exact Or.inl (by decide)

/-- **ГЕРОЙ-ДВИЖОК: ценностный закон ⟹ достижение 1.** Индукция по ПОТОЛКУ значения
    (обычная индукция по v — без сильной рекурсии и без Classical.choice): позиция со
    значением ≤ v+1 либо уже 1, либо 2 (один шаг), либо > 2 — закон даёт будущую позицию
    со значением ≤ v, применяем гипотезу индукции. -/
theorem reaches_one_of_valueLaw (n : Nat) (h1 : 1 ≤ n) (law : ValueDescentLaw n) :
    ∃ K, iter K n = 1 := by
  suffices h : ∀ v j, iter j n ≤ v → ∃ K, iter K n = 1 by
    exact h n 0 (Nat.le_refl n)
  intro v
  induction v with
  | zero =>
    intro j hj
    exfalso
    have hp := iter_pos j n h1
    omega
  | succ v ih =>
    intro j hj
    by_cases hle : iter j n ≤ v
    · exact ih j hle
    · by_cases hone : iter j n = 1
      · exact ⟨j, hone⟩
      · by_cases htwo : iter j n = 2
        · exact ⟨j + 1,
            ((iter_add j 1 n).trans (congrArg (iter 1) htwo)).trans (by decide)⟩
        · have hp := iter_pos j n h1
          cases law j (by omega) with
          | intro k hk => exact ih (j + k) (by omega)

/-- **ГЕРОЙ (главная теорема): закон доминирования каната ⟹ двигатель стянут к старту.**
    Лестница: RopeCountingLaw → (бюджет окна) → ValueDescentLaw → (индукция по потолку) → 1. -/
theorem reaches_one_of_countingLaw (n : Nat) (h1 : 1 ≤ n) (law : RopeCountingLaw n) :
    ∃ K, iter K n = 1 :=
  reaches_one_of_valueLaw n h1 (valueLaw_of_countingLaw n law)

/-! ## Аудит коллапса: чем ценностная форма хуже счётной -/

/-- **КОЛЛАПС ценностной формы (раскрытие «моста приговорённого»):** сходимость ⟹
    ценностный закон. До достижения 1 спуск даёт сама точка достижения; после — позиций
    выше цикла нет (cycle_absorbs). Вместе с героем: ValueDescentLaw ⟺ сходимость. -/
theorem valueLaw_of_reaches_one (n : Nat) (hr : ∃ K, iter K n = 1) :
    ValueDescentLaw n := by
  cases hr with
  | intro K hK =>
    intro j hj
    by_cases hjK : j < K
    · refine ⟨K - j, ?_⟩
      rw [show j + (K - j) = K by omega, hK]
      omega
    · exfalso
      have habs := cycle_absorbs n K hK (j - K)
      rw [show K + (j - K) = j by omega] at habs
      cases habs with
      | inl h => omega
      | inr h => omega

/-- Ценностная форма ⟺ гипотеза для n: «мост приговорённого» раскрыт формально. -/
theorem valueLaw_iff_reaches_one (n : Nat) (h1 : 1 ≤ n) :
    ValueDescentLaw n ↔ ∃ K, iter K n = 1 :=
  ⟨reaches_one_of_valueLaw n h1, valueLaw_of_reaches_one n⟩

/-! ## Аудиты честности -/

/-- **Окно k=1 ПРОВАЛИВАЕТСЯ на каждой нечётной позиции:** значение растёт (двигатель
    тянет вперёд), а счёт даёт t=1 > e=0. Согласовано с CollatzFuel.no_monotone_height:
    пошагового закона нет — закон каната ОБЯЗАН жить на окнах ≥ 2. -/
theorem single_window_fails (n : Nat) (ho : n % 2 = 1) :
    n < T n ∧ ¬ (oddCount 1 n < evenCount 1 n) := by
  constructor
  · unfold T; rw [if_neg (by omega : ¬ n % 2 = 0)]; omega
  · simp only [oddCount, evenCount, if_neg (show ¬ n % 2 = 0 by omega)]
    omega

/-- Сколь угодно большие свидетели провала k=1 (семейство 2N+1; ср. 4N+5 в CollatzFuel). -/
theorem no_single_step_law (N : Nat) :
    ∃ n, N < n ∧ n % 2 = 1 ∧ n < T n ∧ ¬ (oddCount 1 n < evenCount 1 n) := by
  have h := single_window_fails (2 * N + 1) (by omega)
  exact ⟨2 * N + 1, by omega, by omega, h.1, h.2⟩

/-- Невакуумный зелёный пример счётного условия: у n=4 окно k=2 (4→2→1): t=0 < e=2. -/
theorem window_at_4 : oddCount 2 4 < evenCount 2 4 := by decide

/-- Счётный закон ВЕРЕН для n=4: единственная позиция выше цикла — старт (окно k=2);
    существование выполняющих n — зелёное. Универсальность — открытый вход. -/
theorem countingLaw_4 : RopeCountingLaw 4 := by
  intro j hj
  by_cases h0 : j = 0
  · subst h0
    exact ⟨2, by decide⟩
  · by_cases h1 : j = 1
    · subst h1
      exact absurd hj (by decide)
    · exfalso
      have habs := cycle_absorbs 4 2 (by decide) (j - 2)
      rw [show 2 + (j - 2) = j by omega] at habs
      cases habs with
      | inl h => omega
      | inr h => omega

/-- **Ловушка хвоста цикла (раскрытие):** для n=1 закон истинен ВАКУУМНО — позиций выше
    цикла нет. Ограничение «значение > 2» в кванторе обязательно: от значения 1 шаги
    чередуются 1→2→1 и t ≥ e во всех окнах — закон без ограничения был бы ложен для
    ВСЯКОЙ сходящейся траектории. -/
theorem countingLaw_1 : RopeCountingLaw 1 := by
  intro j hj
  exfalso
  have habs := cycle_absorbs 1 0 (by decide) j
  rw [show 0 + j = j by omega] at habs
  cases habs with
  | inl h => omega
  | inr h => omega

/-! ## Неубывающая орбита = вечный двигатель -/

/-- **Неубывающая орбита**: траектория никогда не опускается ниже старта. -/
def NonDescendingOrbit (n : Nat) : Prop :=
  ∀ k : Nat, n ≤ iter k n

/-- **ТЕОРЕМА (неубывание = вечный двигатель, счётная форма):** чтобы орбита
    не убывала, двигатель обязан выигрывать или сводить вничью КАЖДОЕ окно —
    навсегда: `evenCount ≤ oddCount` для всех k. Прямо из бюджета окна:
    2^e·iter ≤ 2^t·n и n ≤ iter дают 2^e ≤ 2^t. Бесконечная подпитка
    топливом без единого проигранного окна — это и есть вечный двигатель. -/
theorem nonDescending_engine_never_loses (n : Nat) (h1 : 1 ≤ n)
    (hnd : NonDescendingOrbit n) :
    ∀ k : Nat, evenCount k n ≤ oddCount k n := by
  intro k
  cases Nat.lt_or_ge (oddCount k n) (evenCount k n) with
  | inr hge => omega
  | inl hlt =>
    exfalso
    have hb := window_budget k n
    have hup := hnd k
    have hchain : 2 ^ evenCount k n * n ≤ 2 ^ oddCount k n * n :=
      Nat.le_trans (Nat.mul_le_mul (Nat.le_refl _) hup) hb
    have hpow : 2 ^ evenCount k n ≤ 2 ^ oddCount k n :=
      Nat.le_of_mul_le_mul_right hchain (by omega)
    have hmono : 2 ^ (oddCount k n + 1) ≤ 2 ^ evenCount k n :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 0 < 2 ^ oddCount k n := Nat.two_pow_pos _
    have hdouble : (2 : Nat) ^ (oddCount k n + 1) = 2 * 2 ^ oddCount k n := by
      rw [Nat.pow_add_one, Nat.mul_comm]
    omega

/-- Неубывающая орбита (со старта выше цикла) никогда не достигает 1 —
    вечное движение без остановки. -/
theorem nonDescending_never_halts (n : Nat) (h3 : 3 ≤ n)
    (hnd : NonDescendingOrbit n) :
    ∀ K : Nat, iter K n ≠ 1 := by
  intro K hK
  have := hnd K
  omega

/-- **Сводка «неубывающая орбита = вечный двигатель»:** двигатель не
    проигрывает ни одного окна И никогда не останавливается. -/
theorem nonDescendingOrbit_is_perpetual_engine (n : Nat) (h3 : 3 ≤ n)
    (hnd : NonDescendingOrbit n) :
    (∀ k, evenCount k n ≤ oddCount k n) ∧ (∀ K, iter K n ≠ 1) :=
  ⟨nonDescending_engine_never_loses n (by omega) hnd,
   nonDescending_never_halts n h3 hnd⟩

/-- **Закон каната запрещает вечный двигатель:** при законе доминирования
    неубывающих орбит (выше цикла) НЕ существует — первая же позиция даёт
    окно с перевесом каната и строгий спуск ниже старта. -/
theorem no_nonDescendingOrbit_under_countingLaw (n : Nat) (h3 : 3 ≤ n)
    (law : RopeCountingLaw n) : ¬ NonDescendingOrbit n := by
  intro hnd
  cases law 0 (by simp only [iter]; omega) with
  | intro k hk =>
    have hdrop : iter k n < n := by
      have := window_descends k n (by omega)
      simp only [iter] at hk
      exact this hk
    have := hnd k
    omega

/-! ## Нижний ранг: почему +1 запутывает двигатель на цифрах 2 и 3 -/

/-- **«+1 весит полный ранг ТОЛЬКО при n = 1»:** 3n+1 достигает верхней
    границы двигателя 4n (ровно +2 сырых ранга) в одной-единственной точке —
    на дне. Выше дна добавка +1 суб-ранговая: 3n+1 < 4n. -/
theorem plus_one_full_rank_only_at_one (n : Nat) (h1 : 1 ≤ n) :
    3 * n + 1 = 4 * n ↔ n = 1 := by
  constructor
  · intro h; omega
  · intro h; omega

/-- Выше дна +1 строго суб-ранговая. -/
theorem plus_one_subrank_above_one (n : Nat) (h3 : 3 ≤ n) :
    3 * n + 1 < 4 * n := by omega

/-- **«Двигатель запутан на дне»:** ровно при n = 1 выстрел двигателя
    попадает в ЧИСТУЮ степень каната (3·1+1 = 4 = 2²) — канат стягивает его
    два шага подряд назад, образуя поглощающий цикл 1→2→1. Цифры 2 и 3 на
    нижнем ранге неразличимы для +1: она составляет там целый ранг. -/
theorem engine_confused_at_bottom :
    3 * 1 + 1 = 2 ^ 2 ∧ T 1 = 2 ∧ T 2 = 1 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Опровержение = двигатель: любой контрпример несёт вечный двигатель

ЧЕСТНОЕ РАСКРЫТИЕ ОБ АКСИОМАХ: теоремы этой секции — единственное место файла,
где используется классическая логика (`Classical.em` — выбор позиции минимума
орбиты неконструктивен); их список аксиом — стандартная тройка
[propext, Classical.choice, Quot.sound]. Весь остальной файл остаётся
choice-free ([propext, Quot.sound]). -/

/-- **Минимум орбиты существует** (вполне-упорядоченность ℕ): у всякой орбиты
    есть позиция глобального минимума значения. -/
theorem exists_min_position (n : Nat) :
    ∃ j : Nat, ∀ k : Nat, iter j n ≤ iter k n := by
  suffices h : ∀ v j0 : Nat, iter j0 n ≤ v →
      ∃ j, ∀ k, iter j n ≤ iter k n from
    h (iter 0 n) 0 (Nat.le_refl _)
  intro v
  induction v with
  | zero =>
    intro j0 h0
    refine ⟨j0, fun k => ?_⟩
    omega
  | succ v ih =>
    intro j0 h0
    cases Classical.em (∃ k, iter k n < iter j0 n) with
    | inl hex =>
      cases hex with
      | intro k hk => exact ih k (by omega)
    | inr hno =>
      refine ⟨j0, fun k => ?_⟩
      cases Nat.lt_or_ge (iter k n) (iter j0 n) with
      | inl hlt => exact absurd ⟨k, hlt⟩ hno
      | inr hge => exact hge

/-- **ЦЕНТРАЛЬНАЯ ТЕОРЕМА: контрпример Коллатца несёт вечный двигатель.**
    Если орбита никогда не достигает 1, то её хвост от позиции минимума —
    неубывающая не-останавливающаяся орбита, то есть ровно наш вечный
    двигатель (`nonDescendingOrbit_is_perpetual_engine`: не проигрывает ни
    одного окна и никогда не останавливается). Конструкция ПОДЛИННАЯ, не
    ex falso: хвост предъявляется явно. Опровергнуть Коллатца = построить
    вечный двигатель — дословно. -/
theorem nonHalting_carries_perpetual_engine (n : Nat)
    (hnh : ∀ K : Nat, iter K n ≠ 1) :
    ∃ j : Nat, NonDescendingOrbit (iter j n) ∧
      ∀ K : Nat, iter K (iter j n) ≠ 1 := by
  cases exists_min_position n with
  | intro j hj =>
    refine ⟨j, ?_, ?_⟩
    · intro k
      rw [← iter_add]
      exact hj (j + k)
    · intro K hK
      rw [← iter_add] at hK
      exact hnh (j + K) hK

/-- **Коллатц ⟺ «вечного двигателя нет».** Остановка орбиты эквивалентна
    отсутствию вечного хвоста: гипотеза Коллатца — это в точности утверждение
    о невозможности вечного двигателя для карты T. -/
theorem collatz_iff_no_perpetual_tail (n : Nat) :
    (∃ K : Nat, iter K n = 1) ↔
      ¬ ∃ j : Nat, NonDescendingOrbit (iter j n) ∧
        ∀ K : Nat, iter K (iter j n) ≠ 1 := by
  constructor
  · intro hhalt htail
    cases hhalt with
    | intro K hK =>
      cases htail with
      | intro j htl =>
        cases Nat.lt_or_ge K j with
        | inr hjK =>
          -- j ≤ K: хвост ловит 1 на шаге K − j
          have hidx : j + (K - j) = K := by omega
          have h1 : iter (K - j) (iter j n) = 1 := by
            rw [← iter_add, hidx]
            exact hK
          exact htl.2 (K - j) h1
        | inl hKj =>
          -- K < j: после K всё в вакууме {1,2}, хвост гаснет за ≤ 1 шаг
          have habs := cycle_absorbs n K hK (j - K)
          have hidx : K + (j - K) = j := by omega
          rw [hidx] at habs
          cases habs with
          | inl h1 =>
            exact htl.2 0 h1
          | inr h2 =>
            have h1 : iter 1 (iter j n) = 1 := by
              show iter 0 (T (iter j n)) = 1
              rw [h2]
              decide
            exact htl.2 1 h1
  · intro hno
    cases Classical.em (∃ K : Nat, iter K n = 1) with
    | inl h => exact h
    | inr hne =>
      exfalso
      exact hno (nonHalting_carries_perpetual_engine n
        (fun K hK => hne ⟨K, hK⟩))

/-- **Вакуум не имеет щели:** из цикла {1, 2} не выйти никогда. -/
theorem vacuum_has_no_gap (d : Nat) : iter d 1 = 1 ∨ iter d 1 = 2 := by
  have h := cycle_absorbs 1 0 rfl d
  rwa [Nat.zero_add] at h

/-- **«Щель в вакууме» = вечный двигатель:** орбита, вечно избегающая вакуума
    {1, 2} (второе дно, «другой ранг с самого низа»), несёт вечный двигатель —
    прямое следствие центральной теоремы. Найти щель в вакууме стоит ровно
    вечного двигателя. -/
theorem second_bottom_carries_engine (n : Nat)
    (havoid : ∀ K : Nat, 3 ≤ iter K n) :
    ∃ j : Nat, NonDescendingOrbit (iter j n) ∧
      ∀ K : Nat, iter K (iter j n) ≠ 1 :=
  nonHalting_carries_perpetual_engine n
    (fun K hK => by have := havoid K; omega)

/-! ## Аудит аксиом (choice-free ядро: [propext, Quot.sound];
    секция «Опровержение = двигатель» — стандартная тройка, em раскрыт выше) -/
#print axioms window_budget
#print axioms window_descends
#print axioms reaches_one_of_valueLaw
#print axioms reaches_one_of_countingLaw
#print axioms valueLaw_iff_reaches_one
#print axioms no_single_step_law
#print axioms countingLaw_4
#print axioms nonDescending_engine_never_loses
#print axioms nonDescendingOrbit_is_perpetual_engine
#print axioms no_nonDescendingOrbit_under_countingLaw
#print axioms plus_one_full_rank_only_at_one
#print axioms engine_confused_at_bottom
#print axioms exists_min_position
#print axioms nonHalting_carries_perpetual_engine
#print axioms collatz_iff_no_perpetual_tail
#print axioms vacuum_has_no_gap
#print axioms second_bottom_carries_engine

end EuclidsPath.Collatz.TugOfWar
