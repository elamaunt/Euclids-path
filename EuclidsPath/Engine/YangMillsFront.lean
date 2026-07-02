/-
  YangMillsFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль ветви Янга–Миллса в
  программе вечного двигателя: БЕЗМАССОВЫЙ (gapless) спектр = ВЕЧНЫЙ ДВИГАТЕЛЬ
  (возбуждения сколь угодно малой энергии над вакуумом = бесконечный
  мультипликативный спуск в ℝ); его опровержение = МАСС-ГЭП.

  ЧЕСТНАЯ ГРАНИЦА (громко, как в NavierStokes): в mathlib НЕТ калибровочной
  теории. `SpectralModel` — абстрактная спектральная модель (Set ℝ + вакуум +
  неотрицательность); НИКАКОГО содержания Янга–Миллса сверх намеренной будущей
  инстанциации здесь нет. Проблема тысячелетия НЕ решается и НЕ заявляется.

  Архитектура:
    * двигатель: `GaplessLadder` — halving-лестница энергий (2·E' ≤ E), ровно
      ℝ-контрпример `real_positive_work_not_wellfounded` (DissipativeCascade §2);
    * закон квантования `QuantizationLaw` (per-model 🔴 ВХОД, NS-паттерн, как
      EnergyBalanceLaw): каждый положительный уровень несёт ℕ-ранг,
      мультипликативный спуск энергии отражается в строгий спуск ранга;
    * ЗЕЛЁНЫЙ убийца: ℕ-спуск невозможен — КОРЕНЬ репозитория
      (`EuclidsPath.Engine.no_infinite_descent`, EPMI); отсюда
      `massGap_of_quantizationLaw` — зелёная условная цепь.

  ИНВЕРТИРОВАННАЯ АСИММЕТРИЯ (раскрыта, не подделана, зеркало P/NP): убийца
  лестницы — чистая well-foundedness ℕ, гипотеза hNoEngine НЕ добавлена;
  конкретная ранговая машина потребляется по-настоящему только в V3/§8.

  ТРИЛЕММА четвёртой границы декрета — все вердикты машинны (§7):
    V1 универсальная форма ОПРОВЕРЖИМА (cookedGapless + cookedLadder + EPMI);
    V2 экзистенциальная форма УЖЕ ДОКАЗАНА (cookedGapped — декрет вакуумен);
    V3 манифестационная (риманово зеркало) форма НЕСОВМЕСТИМА с принятой
       границей: лестница, в отличие от off-critical нуля, зелёно ПРЕДЪЯВИМА.
  КОЛЛАПС стоимости (§4): `quantizationLaw_iff_massGap` — per-model закон ⟺
  гэп ЗЕЛЁНО и БЕЗ границы (форма осуждённого моста `offCriticalBridge_iff_RH`;
  контраст: `manifestationLaw_iff_RH_of_boundary` требует границу). Потому
  ЧЕТВЁРТОГО ПОЛЯ НЕТ: недостающее — data anchor (реальный YM-спектр),
  урок SpectralAnchorAudit/P-NP. Модуль карантин НЕ импортирует; axiom/sorry
  нет — верификатор обязан показать все декларации незаражёнными.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.DissipativeCascade
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace YangMills

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
-- EPMI и OriginAnchorAudit используем КВАЛИФИЦИРОВАННО (коллизии State/Step/Bridge).

/-#############################################################################
  §1. Спектральная модель, гэп, безмассовость
#############################################################################-/

/-- **D1. Абстрактная спектральная модель**: множество уровней энергии с
    вакуумом 0 и неотрицательностью. `vacuum_mem` — семантический якорь
    (0 = вакуум; делает гард `E ≠ 0` в `MassGap` осмысленным); в выводах
    несёт только обитаемость cooked-моделей — инертность раскрыта.
    НИКАКОГО YM-содержания (раскрыто в шапке). -/
structure SpectralModel where
  Energy : Set ℝ
  vacuum_mem : (0 : ℝ) ∈ Energy
  nonneg : ∀ E ∈ Energy, 0 ≤ E

/-- Положительное (не-вакуумное) состояние спектра. -/
abbrev PositiveState (S : SpectralModel) : Type :=
  {E : ℝ // E ∈ S.Energy ∧ 0 < E}

/-- **D2. МАСС-ГЭП** (направление Клэя; здесь — только абстрактная форма):
    существует Δ > 0 ниже всех ненулевых уровней. -/
def MassGap (S : SpectralModel) : Prop :=
  ∃ Δ > 0, ∀ E ∈ S.Energy, E ≠ 0 → Δ ≤ E

/-- **D3. БЕЗМАССОВОСТЬ = вечный двигатель**: возбуждения сколь угодно малой
    положительной энергии над вакуумом. -/
def Gapless (S : SpectralModel) : Prop :=
  ∀ ε > 0, ∃ E ∈ S.Energy, 0 < E ∧ E < ε

/-- **L1: ¬гэп ⟺ безмассовость** — классическая эквивалентность
    (`nonneg` потребляется в переходе E ≠ 0 ⟺ 0 < E). Выбор НЕ нужен. -/
theorem not_massGap_iff_gapless (S : SpectralModel) :
    ¬ MassGap S ↔ Gapless S := by
  constructor
  · intro hNo ε hε
    by_contra hnone
    push_neg at hnone
    exact hNo ⟨ε, hε, fun E hE hne =>
      hnone E hE (lt_of_le_of_ne (S.nonneg E hE) (Ne.symm hne))⟩
  · rintro hG ⟨Δ, hΔ, hgap⟩
    obtain ⟨E, hE, hpos, hlt⟩ := hG Δ hΔ
    exact absurd (hgap E hE (ne_of_gt hpos)) (not_le.mpr hlt)

theorem massGap_iff_not_gapless (S : SpectralModel) :
    MassGap S ↔ ¬ Gapless S := by
  rw [← not_massGap_iff_gapless, not_not]

/-#############################################################################
  §2. ОБЪЕКТ-ДВИГАТЕЛЬ: halving-лестница
#############################################################################-/

/-- **D4. ЛЕСТНИЦА БЕЗМАССОВОСТИ — вечный двигатель в ℝ**: бесконечная
    последовательность положительных уровней с мультипликативным спуском
    `2·E(n+1) ≤ E(n)` (аналог `DescentStep` EPMI с A = 2, но над ℝ, где
    well-foundedness сама по себе НЕ работает — ровно ℝ-предупреждение
    `real_positive_work_not_wellfounded`). -/
structure GaplessLadder (S : SpectralModel) where
  seq : ℕ → ℝ
  mem : ∀ n, seq n ∈ S.Energy
  pos : ∀ n, 0 < seq n
  halving : ∀ n, 2 * seq (n + 1) ≤ seq n

/-- Один шаг выбора: уровень ниже половины текущего. -/
noncomputable def ladderNext {S : SpectralModel} (hG : Gapless S)
    (p : PositiveState S) : PositiveState S :=
  ⟨(hG (p.1 / 2) (half_pos p.2.2)).choose,
   (hG (p.1 / 2) (half_pos p.2.2)).choose_spec.1,
   (hG (p.1 / 2) (half_pos p.2.2)).choose_spec.2.1⟩

theorem ladderNext_lt_half {S : SpectralModel} (hG : Gapless S)
    (p : PositiveState S) : (ladderNext hG p).1 < p.1 / 2 :=
  (hG (p.1 / 2) (half_pos p.2.2)).choose_spec.2.2

/-- Рекурсивная последовательность выбора (`Classical.choice` честно виден). -/
noncomputable def ladderSeq {S : SpectralModel} (hG : Gapless S) :
    ℕ → PositiveState S
  | 0 => ⟨(hG 1 one_pos).choose, (hG 1 one_pos).choose_spec.1,
          (hG 1 one_pos).choose_spec.2.1⟩
  | n + 1 => ladderNext hG (ladderSeq hG n)

@[simp] theorem ladderSeq_succ {S : SpectralModel} (hG : Gapless S) (n : ℕ) :
    ladderSeq hG (n + 1) = ladderNext hG (ladderSeq hG n) := rfl

/-- **L2 (свидетель содержательности, зеркало `offCriticalZero_of_not_RH`):**
    из безмассовости лестница СТРОИТСЯ (выбором). -/
noncomputable def gaplessLadder_of_gapless {S : SpectralModel}
    (hG : Gapless S) : GaplessLadder S where
  seq := fun n => (ladderSeq hG n).1
  mem := fun n => (ladderSeq hG n).2.1
  pos := fun n => (ladderSeq hG n).2.2
  halving := fun n => by
    have h := ladderNext_lt_half hG (ladderSeq hG n)
    show 2 * (ladderSeq hG (n + 1)).1 ≤ (ladderSeq hG n).1
    rw [ladderSeq_succ]
    linarith

/-- Именованная форма из ¬гэпа. -/
noncomputable def gaplessLadder_of_not_massGap {S : SpectralModel}
    (h : ¬ MassGap S) : GaplessLadder S :=
  gaplessLadder_of_gapless ((not_massGap_iff_gapless S).mp h)

/-- Лестница мажорируется геометрической прогрессией. -/
theorem ladder_le_geometric {S : SpectralModel} (D : GaplessLadder S) :
    ∀ n : ℕ, D.seq n ≤ D.seq 0 * (1 / 2) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h := D.halving n
      have hpow : (0 : ℝ) < (1 / 2) ^ n := by positivity
      calc D.seq (n + 1) ≤ D.seq n / 2 := by linarith
        _ ≤ D.seq 0 * (1 / 2) ^ n / 2 := by linarith
        _ = D.seq 0 * (1 / 2) ^ (n + 1) := by ring

/-- **L3: лестница ⟹ безмассовость** (архимедов спуск,
    `exists_pow_lt_of_lt_one`): лестница опровергает ВСЯКИЙ кандидат-Δ. -/
theorem gapless_of_ladder {S : SpectralModel} (D : GaplessLadder S) :
    Gapless S := by
  intro ε hε
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one (div_pos hε (D.pos 0)) (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨D.seq n, D.mem n, D.pos n, ?_⟩
  have h1 : D.seq 0 * (1 / 2) ^ n < ε := (lt_div_iff₀' (D.pos 0)).mp hn
  have h2 := ladder_le_geometric D n
  linarith

theorem not_massGap_of_ladder {S : SpectralModel} (D : GaplessLadder S) :
    ¬ MassGap S :=
  fun hM => (massGap_iff_not_gapless S).mp hM (gapless_of_ladder D)

/-- **L4 — точная зелёная характеризация двигателя:** безмассовость ⟺
    непустота типа лестниц. -/
theorem gapless_iff_nonempty_ladder (S : SpectralModel) :
    Gapless S ↔ Nonempty (GaplessLadder S) :=
  ⟨fun h => ⟨gaplessLadder_of_gapless h⟩, fun ⟨D⟩ => gapless_of_ladder D⟩

/-#############################################################################
  §3. Закон квантования и EPMI-убийца (геройская цепь, NS-паттерн)
#############################################################################-/

/-- **D5. ЗАКОН КВАНТОВАНИЯ — per-model 🔴 ВХОД (NS-паттерн, как
    `EnergyBalanceLaw`):** каждое положительное состояние манифестирует на
    натуральном ранге, и мультипликативный спуск энергии (2y ≤ x) отражается
    в СТРОГИЙ спуск ранга. Для НАМЕРЕННОЙ (не построенной!) инстанциации
    S = реальный YM-спектр это и есть остаточный физический вход ветви. -/
def QuantizationLaw (S : SpectralModel) : Prop :=
  ∃ rank : PositiveState S → ℕ,
    ∀ x y : PositiveState S, 2 * (y : ℝ) ≤ (x : ℝ) → rank y < rank x

/-- **L5 — ЗЕЛЁНЫЙ УБИЙЦА (КОРЕНЬ РЕПОЗИТОРИЯ):** квантованная лестница =
    бесконечный ℕ-спуск = вечный двигатель Евклида; убит
    `no_infinite_descent` (EPMI, A = 1). ЧЕСТНОСТЬ (инвертированная
    асимметрия, зеркало P/NP): убийца — чистая well-foundedness,
    hNoEngine НЕ добавлен (был бы фальшивой гипотезой). -/
theorem no_quantizedLadder {S : SpectralModel}
    (hQ : QuantizationLaw S) (D : GaplessLadder S) : False := by
  obtain ⟨rank, hrank⟩ := hQ
  exact EuclidsPath.Engine.no_infinite_descent (le_refl 1)
    (fun t => rank ⟨D.seq t, D.mem t, D.pos t⟩)
    (fun t => by
      show 1 * rank ⟨D.seq (t + 1), D.mem (t + 1), D.pos (t + 1)⟩ <
        rank ⟨D.seq t, D.mem t, D.pos t⟩
      rw [Nat.one_mul]
      exact hrank _ _ (D.halving t))

/-- **L6 — ГЕРОЙ (зелёная условная цепь, NS-паттерн):** закон квантования ⟹
    масс-гэп. ¬гэп → лестница (выбор) → ℕ-спуск → EPMI-False. -/
theorem massGap_of_quantizationLaw (S : SpectralModel)
    (hQ : QuantizationLaw S) : MassGap S := by
  by_contra hNo
  exact no_quantizedLadder hQ (gaplessLadder_of_not_massGap hNo)

/-- **L7 (аналог римановской L2):** безмассовой квантованной модели НЕ
    существует. -/
theorem no_gapless_quantized_model :
    ¬ ∃ S : SpectralModel, Gapless S ∧ QuantizationLaw S := by
  rintro ⟨S, hG, hQ⟩
  exact no_quantizedLadder hQ (gaplessLadder_of_gapless hG)

/-#############################################################################
  §4. Зеркало стоимости и его КОЛЛАПС (решающий аудит честности)
#############################################################################-/

/-- **L8 (обратная сторона — НЕ вакуумна, в отличие от римановской L5):**
    гэп ⟹ закон квантования. Ранг: `Nat.log 2 ⌊E/Δ⌋₊` — двоичный этаж
    уровня над порогом Δ. -/
theorem quantizationLaw_of_massGap (S : SpectralModel)
    (hM : MassGap S) : QuantizationLaw S := by
  obtain ⟨Δ, hΔ, hgap⟩ := hM
  refine ⟨fun x => Nat.log 2 ⌊(x : ℝ) / Δ⌋₊, ?_⟩
  intro x y hxy
  have hyΔ : Δ ≤ (y : ℝ) := hgap y.1 y.2.1 (ne_of_gt y.2.2)
  set m : ℕ := ⌊(y : ℝ) / Δ⌋₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.le_floor (by push_cast; exact (one_le_div hΔ).mpr hyΔ)
  have hmle : (m : ℝ) ≤ (y : ℝ) / Δ := by
    rw [hm]; exact Nat.floor_le (div_pos y.2.2 hΔ).le
  have hmΔ : (m : ℝ) * Δ ≤ (y : ℝ) := (le_div_iff₀ hΔ).mp hmle
  have hcast : ((m * 2 : ℕ) : ℝ) ≤ (x : ℝ) / Δ := by
    rw [le_div_iff₀ hΔ]
    push_cast
    nlinarith [hxy, hmΔ]
  have hfloor : m * 2 ≤ ⌊(x : ℝ) / Δ⌋₊ := Nat.le_floor hcast
  calc Nat.log 2 m < Nat.log 2 m + 1 := Nat.lt_succ_self _
    _ = Nat.log 2 (m * 2) :=
        (Nat.log_mul_base (by norm_num) (by omega)).symm
    _ ≤ Nat.log 2 ⌊(x : ℝ) / Δ⌋₊ := Nat.log_mono_right hfloor

/-- **L9 — ГЛАВНЫЙ АУДИТ (коллапс зеркала стоимости):** per-model закон ⟺
    масс-гэп — ЗЕЛЁНО и БЕЗ ВСЯКОЙ ГРАНИЦЫ. Это форма ОСУЖДЁННОГО моста
    (`offCriticalBridge_iff_RH`), а НЕ римановского зеркала
    (`manifestationLaw_iff_RH_of_boundary` требует границу): декретировать
    закон для модели = декретировать её гэп дословно. Потому per-model
    декретное поле невозможно ЧЕСТНО; недостающее — data anchor (реальный
    YM-спектр), Prop-невакуумность — неверный критерий (SpectralAnchorAudit). -/
theorem quantizationLaw_iff_massGap (S : SpectralModel) :
    QuantizationLaw S ↔ MassGap S :=
  ⟨massGap_of_quantizationLaw S, quantizationLaw_of_massGap S⟩

/-#############################################################################
  §5. Кованые модели (свидетели трилеммы)
#############################################################################-/

/-- Кованая БЕЗМАССОВАЯ модель: `{0} ∪ {(1/2)^n}` — спектральная реализация
    ℝ-предупреждения `real_positive_work_not_wellfounded`. -/
noncomputable def cookedGapless : SpectralModel where
  Energy := insert (0 : ℝ) (Set.range fun n : ℕ => (1 / 2 : ℝ) ^ n)
  vacuum_mem := Set.mem_insert 0 _
  nonneg := by
    rintro E hE
    rcases Set.mem_insert_iff.mp hE with rfl | ⟨n, rfl⟩
    · exact le_refl 0
    · positivity

/-- Её ЯВНАЯ лестница (никакого выбора — двигатель предъявлен конструкцией;
    noncomputable — только из-за ℝ-деления в данных). -/
noncomputable def cookedLadder : GaplessLadder cookedGapless where
  seq := fun n => (1 / 2 : ℝ) ^ n
  mem := fun n => Set.mem_insert_of_mem _ ⟨n, rfl⟩
  pos := fun n => by positivity
  halving := fun n => le_of_eq (by ring)

theorem cookedGapless_gapless : Gapless cookedGapless :=
  gapless_of_ladder cookedLadder

theorem cookedGapless_not_massGap : ¬ MassGap cookedGapless :=
  not_massGap_of_ladder cookedLadder

theorem cookedGapless_no_quantizationLaw : ¬ QuantizationLaw cookedGapless :=
  fun hQ => no_quantizedLadder hQ cookedLadder

/-- Кованая ГЭПНУТАЯ модель `{0, 1}`. -/
def cookedGapped : SpectralModel where
  Energy := {0, 1}
  vacuum_mem := Set.mem_insert 0 _
  nonneg := by
    rintro E hE
    rcases Set.mem_insert_iff.mp hE with rfl | hE1
    · exact le_refl 0
    · rw [Set.mem_singleton_iff] at hE1; rw [hE1]; norm_num

theorem cookedGapped_massGap : MassGap cookedGapped := by
  refine ⟨1, one_pos, ?_⟩
  rintro E hE hne
  rcases Set.mem_insert_iff.mp hE with rfl | hE1
  · exact absurd rfl hne
  · rw [Set.mem_singleton_iff] at hE1; rw [hE1]

/-- Закон на гэпнутой модели — ВАКУУМНО (нет ни одной halving-пары): rank ≡ 0
    проходит. Раскрыто: вот почему V2-декрет ничего не добавил бы. -/
theorem cookedGapped_quantizationLaw : QuantizationLaw cookedGapped := by
  refine ⟨fun _ => 0, ?_⟩
  rintro ⟨x, hx, hxpos⟩ ⟨y, hy, hypos⟩ hxy
  exfalso
  have hxy' : 2 * y ≤ x := hxy
  rcases Set.mem_insert_iff.mp hx with rfl | hx1
  · exact lt_irrefl _ hxpos
  rcases Set.mem_insert_iff.mp hy with rfl | hy1
  · exact lt_irrefl _ hypos
  rw [Set.mem_singleton_iff] at hx1 hy1
  rw [hx1, hy1] at hxy'
  norm_num at hxy'

/-- Чисто-вакуумная модель `{0}`: гэп ВАКУУМНО (гард пуст) — Prop-невакуумность
    как критерий снова неверна (урок SpectralAnchorAudit). -/
def vacuumOnlyModel : SpectralModel where
  Energy := {0}
  vacuum_mem := Set.mem_singleton 0
  nonneg := by
    rintro E hE
    rw [Set.eq_of_mem_singleton hE]

theorem vacuumOnly_massGap : MassGap vacuumOnlyModel :=
  ⟨1, one_pos, fun _E hE hne => absurd (Set.eq_of_mem_singleton hE) hne⟩

/-#############################################################################
  §6. Мост к Навье–Стоксу: почему спасает ранг, а не δ-диссипация
#############################################################################-/

/-- Переиспользование generic-машины каскада: равномерно-δ-диссипирующая
    лестница невозможна (`no_infinite_uniform_dissipative_cascade`). -/
theorem no_uniformlyDissipative_ladder {S : SpectralModel}
    (D : GaplessLadder S) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ n : ℕ, δ ≤ D.seq n - D.seq (n + 1)) : False :=
  EuclidsPath.DissipativeCascade.no_infinite_uniform_dissipative_cascade
    (State := ℕ) (Step := fun m n => n = m + 1)
    D.seq (fun m n => D.seq m - D.seq n) δ hδ
    (fun {m n} h => by subst h; exact le_of_eq (by ring))
    (fun {m n} h => by subst h; exact hstep m)
    (fun n => (D.pos n).le)
    ⟨fun k => k, fun _ => rfl⟩

/-- **НО: cooked-лестница НЕ равномерно диссипативна** — её шаги (1/2)^(n+1)
    убывают под всякий δ. Машинная фиксация: δ-квантование диссипации
    (НС-сертификат) лестницу НЕ убивает; убивает только РАНГОВОЕ квантование
    (§3). Мост NS↔YM честен и структурен: общий корень — EPMI, спасения
    разные. -/
theorem cookedLadder_not_uniformlyDissipative (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ n : ℕ, δ ≤ cookedLadder.seq n - cookedLadder.seq (n + 1) := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
  have hstep := h n
  have heq : cookedLadder.seq n - cookedLadder.seq (n + 1)
      = (1 / 2 : ℝ) ^ (n + 1) := by
    show (1/2 : ℝ) ^ n - (1/2) ^ (n + 1) = (1/2) ^ (n + 1)
    ring
  have hlt : ((1 : ℝ) / 2) ^ (n + 1) < (1 / 2) ^ n := by
    have hp : (0:ℝ) < (1/2)^n := by positivity
    calc ((1:ℝ)/2)^(n+1) = (1/2)^n * (1/2) := by ring
      _ < (1/2)^n := by nlinarith
  rw [heq] at hstep
  linarith

/-#############################################################################
  §7. ТРИЛЕММА четвёртой границы декрета — все вердикты машинны
#############################################################################-/

/-- **D6a. КАНДИДАТ 1 (универсальная форма четвёртого поля).** -/
def YmQuantizationLawUniversal : Prop :=
  ∀ S : SpectralModel, QuantizationLaw S

/-- **D6b. КАНДИДАТ 2 (экзистенциальная форма).** -/
def YmQuantizationLawExistential : Prop :=
  ∃ S : SpectralModel, QuantizationLaw S ∧ MassGap S

/-- **D6c. КАНДИДАТ 3 (манифестационная форма, риманово зеркало):** лестница
    манифестирует неоплатимой поставкой потоков на всех разрешённых
    леджер-масштабах (тот же объект `DeviationFlowSupply`, что у
    riemannBoundary). Абстрактная лестница НЕ несёт арифметической высоты —
    закон привязан ко ВСЕМ масштабам; эта D-свобода вскрыта аудитами A3/A4. -/
def LadderManifests {S : SpectralModel} (_D : GaplessLadder S) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def YmManifestationLaw : Prop :=
  ∀ (S : SpectralModel) (D : GaplessLadder S), LadderManifests D

/-- **V1: КАНДИДАТ 1 ЗЕЛЁНО-ОПРОВЕРЖИМ** — его декрет сделал бы карантин
    противоречивым. Свидетель: cookedGapless + cookedLadder + EPMI. Точная
    асимметрия с Риманом: off-critical нуль зелёно НЕ предъявим (это была бы
    ¬RH), cooked-лестница — предъявлена выше конструкцией. -/
theorem ymLawUniversal_refuted : ¬ YmQuantizationLawUniversal :=
  fun h => no_quantizedLadder (h cookedGapless) cookedLadder

/-- **V2: КАНДИДАТ 2 ЗЕЛЁНО-ДОКАЗУЕМ** — декрет был бы вакуумен.
    Свидетель: cookedGapped (закон вакуумен, гэп дословно Δ = 1). -/
theorem ymLawExistential_green : YmQuantizationLawExistential :=
  ⟨cookedGapped, cookedGapped_quantizationLaw, cookedGapped_massGap⟩

/-- **V3: КАНДИДАТ 3 НЕСОВМЕСТИМ С ПРИНЯТОЙ ГРАНИЦЕЙ** (зелёная условная
    форма, taint-free): закон + существующий декретный узел ⟹ False.
    Цепь: граница даёт разрешающую проекцию (M0 = 1) → закон с
    cooked-лестницей поставляет `DeviationFlowSupply` → L2
    (`no_deviationFlowSupply_at_resolved_scale`) сжигает её. Потому четвёртое
    поле этой формы ВЗОРВАЛО бы карантин — ОТКЛОНЕНО. -/
theorem ymManifestationLaw_refutes_boundary
    (hLaw : YmManifestationLaw) : ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hres⟩
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf 1) :=
    strictSemanticExtended_resolves_old (hres 1)
  exact no_deviationFlowSupply_at_resolved_scale (projOf 1) hResolves
    (hLaw cookedGapless cookedLadder A 1 (projOf 1) hResolves)

/-- Контрапозиция для читаемости: при принятой границе закона НЕТ. -/
theorem not_ymManifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) : ¬ YmManifestationLaw :=
  fun hLaw => ymManifestationLaw_refutes_boundary hLaw hBoundary

/-- **V3-характеризация (зеркало римановской L6, ЗАОСТРЁННОЕ):** закон ⟺
    «никакой леджер нигде не сводит книги» — глобальная заморозка. У Римана
    прямое направление требовало нуль (квантор мог быть пуст); здесь квантор
    ЗЕЛЁНО обитаем (cookedLadder), потому характеризация безусловна. -/
theorem ymManifestationLaw_iff_no_resolution :
    YmManifestationLaw ↔
      ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw A M0 proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw cookedGapless cookedLadder A M0 proj hres)
  · intro hFreeze S D A M0 proj hres
    exact ((hFreeze A M0 proj) hres).elim

/-#############################################################################
  §8. Раскол по масштабам (граница как ГИПОТЕЗА — карантин не импортируется)
#############################################################################-/

/-- **L10 (нижний масштаб, зелёный свидетель поставки):** при A ≤ 4 поставка
    отклонений РЕАЛЬНА — 5-адическая цепь даёт бесконечную admissible-семью
    без единой twin-гипотезы (зеркало римановской L1: объект манифестации —
    не пустая форма). -/
theorem smallScale_deviationSupply {A : ℕ} (hA : A ≤ 4) :
    DeviationFlowSupply A 1 :=
  ⟨Set.range (fiveAdicChainFlow hA),
   Set.infinite_range_of_injective (fiveAdicChainFlow_injective hA),
   fun F hF => by
     rcases hF with ⟨k, rfl⟩
     exact extendedFlow_admissible _⟩

/-- **L11 (декретный масштаб):** принятая граница (как ГИПОТЕЗА) на своём
    A ≥ 5 ОТКАЗЫВАЕТ поставке на каждом M0 — в мире декрета нет бесконечной
    башни возбуждений: его вселенная «гэпнута» в языке поставок.
    (A ≥ 5 — через опровергнутую малую ветвь, зеркало P/NP-раскола.) -/
theorem boundary_refuses_deviationSupply_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ, ¬ DeviationFlowSupply A M0 := by
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hA : 5 ≤ A := by
    by_contra hlt
    exact no_projection_resolves_at_smallScale (by omega) (projOf 1)
      (strictSemanticExtended_resolves_old (hres 1))
  exact ⟨A, hA, fun M0 =>
    no_deviationFlowSupply_at_resolved_scale (projOf M0)
      (strictSemanticExtended_resolves_old (hres M0))⟩

/-#############################################################################
  §9. Origin-anchor аудиты (инстанциация осуждающей машины)
#############################################################################-/

/-- **A1 (bundling-аудит, инстанциация `front_pair_iff_no_zero`):**
    Bridge∧Impossible для семейства манифестаций ⟺ лестниц нет. -/
theorem ym_bundling_audit (S : SpectralModel) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun D : GaplessLadder S => LadderManifests D) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun D : GaplessLadder S => LadderManifests D)) ↔
      ¬ Nonempty (GaplessLadder S) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-- **A2 (асимметрия с Риманом, машинно):** на кованой модели связка
    ОПРОВЕРГНУТА — лестница предъявлена. У Римана связку спасала
    непредъявимость нуля; здесь Bridge-сторону декретировать НЕЛЬЗЯ. -/
theorem ym_bundle_refuted_at_cooked :
    ¬ (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
         (fun D : GaplessLadder cookedGapless => LadderManifests D) ∧
       EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
         (fun D : GaplessLadder cookedGapless => LadderManifests D)) :=
  fun h => (ym_bundling_audit cookedGapless).mp h ⟨cookedLadder⟩

/-- **A3 (Z-free collapse, дословно урок SpectralAnchorAudit):** семейство
    манифестаций СВОБОДНО от лестницы — коллапсирует к одному D-независимому
    вопросу-«атому». -/
theorem ymLaw_freeCollapse (S : SpectralModel) :
    EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.FreeLawCollapse
      (fun D : GaplessLadder S => LadderManifests D)
      (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
          DeviationFlowSupply A M0) :=
  fun _D => Iff.rfl

/-- **A4:** потому семейство не разделяет лестниц — свободный закон не несёт
    информации об отклонении (та же причина, по которой он не годится
    в декретное поле). -/
theorem ymLaw_cannot_separate (S : SpectralModel) :
    ¬ EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.ZeroSeparating
        (fun D : GaplessLadder S => LadderManifests D) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.no_zero_separation_under_freeCollapse
    (ymLaw_freeCollapse S)

end YangMills
end EuclidsPath

-- Машинная видимость чистоты в build-логе
-- (ожидаемо [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.YangMills.massGap_of_quantizationLaw
#print axioms EuclidsPath.YangMills.quantizationLaw_iff_massGap
#print axioms EuclidsPath.YangMills.ymLawUniversal_refuted
#print axioms EuclidsPath.YangMills.ymLawExistential_green
#print axioms EuclidsPath.YangMills.ymManifestationLaw_refutes_boundary
#print axioms EuclidsPath.YangMills.boundary_refuses_deviationSupply_at_decreed_scale
