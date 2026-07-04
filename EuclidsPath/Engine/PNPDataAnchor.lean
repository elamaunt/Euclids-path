/-
  PNPDataAnchor — ЯКОРЬ-ФРОНТ машинной модели P/NP: именованные data-anchors
  над РЕАЛЬНЫМИ mathlib-структурами TM2 (Turing.TM2ComputableInPolyTime,
  Mathlib/Computability/TuringMachine/Computable.lean:179), пристыкованные к
  абстрактному фрейму репозитория (ClassicalComplexityFrame / FaithfulPFrame).

  Урок PNPRankPaymentFront: «подлинно недостающее — data-anchored реальная
  машинная модель». Этот модуль ставит два ИМЕНОВАННЫХ красных def-входа:
    * TM2CompositionLaw — закон композиции polytime-вычислимости; в пине это
      ДОСЛОВНО proof_wanted TM2ComputableInPolyTime.comp (Computable.lean:284) —
      деклараций в окружении НЕ создаёт, ссылаться не на что: вход честно красный;
    * TM2FrameBridge — что обязан предъявить строитель, чтобы получить
      настоящий faithful ClassicalComplexityFrame из TM2-модели (InP на
      ℕ-языках ⟺ TM2-разрешимость над КАНОНИЧЕСКОЙ кодировкой encodeNat).

  Зелёные свидетели невакуумности: tm2_id_computable (реэкспорт
  idComputableInPolyTime, Computable.lean:221 — модель ОБИТАЕМА),
  tm2_model_inhabited, tm2CompositionLaw_shape_inhabited_id.

  ⚠️ МАШИННАЯ ЧЕСТНОСТЬ (аудиты на переименование цели — все теоремы):
    * tm2DecidesWithSomeEncoding_free — ∃-квантор по кодировке ПРОТАСКИВАЕТ
      ОТВЕТ (enc x := encodeBool (run x), машина — транспорт тождества):
      «разрешимость с какой-нибудь кодировкой» — True для ЛЮБОГО языка;
      потому якорь фрейма обязан жить над ФИКСИРОВАННОЙ канонической
      кодировкой (урок SpectralAnchorAudit: Prop-невакуумность — неверный
      критерий; здесь он вскрыт на уровне кодировок);
    * faithful_frame_alone_is_free — Nonempty (FaithfulPFrame C) сам по себе
      БЕСПЛАТЕН (freeFrame); вся тяжесть TM2FrameBridge — в iff-клаузе;
    * frame_p_overclosure / tm2FrameBridge_overclosure — свободное Prop-поле
      polynomial_time в PolyManyOneReduction ОТРАВЛЯЕТ замыкание: один
      неконстантный TM2-разрешимый ℕ-язык в InP затопил бы InP ВСЕМИ
      ℕ-языками. Настоящий строитель обязан сначала заменить редукции
      машинными — это зафиксировано машинно, не прозой.

  НЕ решение P/NP, НЕ Гёдель-приём: anchors_do_not_decide_pnp — якоря сами
  по себе ничего не решают (маркер охвата по образцу notAProofOfBeal).
  Модуль НЕ импортирует карантин (CausalClosureAxiom); axiom/sorry/
  native_decide нет; таинт 47 не меняется.
-/
import Mathlib
import EuclidsPath.Engine.ClassicalPNPBridge
import EuclidsPath.Engine.CanonicalSelfReduction

set_option autoImplicit false

namespace EuclidsPath
namespace PNPDataAnchor

open EuclidsPath.ClassicalPNPBridge
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction.CanonicalSelfReduction

/-#############################################################################
  §1. Зелёные свидетели: TM2-модель mathlib обитаема
#############################################################################-/

/-- **🟢 Зелёный свидетель невакуумности: модель обитаема.** Реэкспорт
    `Turing.idComputableInPolyTime`
    (Mathlib/Computability/TuringMachine/Computable.lean:221): тождественная
    функция вычислима за полиномиальное время НАСТОЯЩЕЙ машиной TM2
    (`Turing.FinTM2`), а не Prop-заглушкой. Всё, что говорят якоря ниже,
    говорится о непустом типе машин. -/
noncomputable def tm2_id_computable {α αΓ : Type} [Fintype αΓ]
    (ea : α → List αΓ) :
    Turing.TM2ComputableInPolyTime ea ea id :=
  Turing.idComputableInPolyTime ea

/-- **🟢 Обитаемость в конкретной точке:** тип polytime-машин для `id : Bool → Bool`
    над кодировкой `Computability.encodeBool` непуст. -/
theorem tm2_model_inhabited :
    Nonempty (Turing.TM2ComputableInPolyTime
      Computability.encodeBool Computability.encodeBool (id : Bool → Bool)) :=
  ⟨tm2_id_computable Computability.encodeBool⟩

/-#############################################################################
  §2. Красный вход №1: закон композиции (proof_wanted в пине)
#############################################################################-/

/-- **🔴 КРАСНЫЙ ВХОД №1 (data-anchor): закон композиции TM2-polytime.**

    Композиция polytime-вычислимых функций polytime-вычислима — сформулировано
    над реальными структурами `Turing.TM2ComputableInPolyTime` пина. В mathlib
    v4.31 этого НЕТ: в Mathlib/Computability/TuringMachine/Computable.lean:284
    стоит дословно

    ```
    proof_wanted TM2ComputableInPolyTime.comp
        {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
        {eγ : γ → List γΓ} {f : α → β} {g : β → γ} (h1 : TM2ComputableInPolyTime eα eβ f)
        (h2 : TM2ComputableInPolyTime eβ eγ g) :
      Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))
    ```

    `proof_wanted` НЕ создаёт декларации в окружении — сослаться не на что.
    Математика ДОЛЖНА предъявить: конструкцию машины-композита (ленты обеих
    машин + перенос выходного стека первой на входной стек второй) и
    полиномиальную оценку её времени. Это НЕ переименование цели P/NP:
    закон композиции — лемма о МОДЕЛИ, обе стороны P vs NP совместимы с ним. -/
def TM2CompositionLaw : Prop :=
  ∀ (α β γ αΓ βΓ γΓ : Type)
    (eα : α → List αΓ) (eβ : β → List βΓ) (eγ : γ → List γΓ)
    (f : α → β) (g : β → γ),
    Turing.TM2ComputableInPolyTime eα eβ f →
    Turing.TM2ComputableInPolyTime eβ eγ g →
    Nonempty (Turing.TM2ComputableInPolyTime eα eγ (g ∘ f))

/-- **🟢 Форма заключения якоря обитаема** (невакуумность утверждения, не его
    доказательство): для `f = g = id` заключение композиционного закона —
    теорема уже сейчас. Тип `Nonempty (… (id ∘ id))` непуст благодаря
    `tm2_id_computable`. -/
theorem tm2CompositionLaw_shape_inhabited_id
    {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    Nonempty (Turing.TM2ComputableInPolyTime ea ea (id ∘ id : α → α)) := by
  have h : (id ∘ id : α → α) = id := Function.comp_id id
  rw [h]
  exact ⟨tm2_id_computable ea⟩

/-#############################################################################
  §3. Аудит кодировок: ∃-кодировка протаскивает ответ (машинно)
#############################################################################-/

/-- **🟡 Машина-транспорт ответа (инструмент аудита §3).** Для ЛЮБОЙ функции
    `run : α → Bool` и жульнической кодировки `enc x := encodeBool (run x)`
    тождественная машина `Turing.idComputer` «вычисляет» `run`: ответ уже
    записан во входе. Конструкция честно переиспользует
    `idComputableInPolyTime.outputsFun` — вход и выход совпадают дословно. -/
noncomputable def tm2AnswerTransport {α : Type} (run : α → Bool) :
    Turing.TM2ComputableInPolyTime
      (fun x : α => Computability.encodeBool (run x))
      Computability.encodeBool run where
  toTM2ComputableAux :=
    (Turing.idComputableInPolyTime Computability.encodeBool).toTM2ComputableAux
  time := (Turing.idComputableInPolyTime Computability.encodeBool).time
  outputsFun a :=
    (Turing.idComputableInPolyTime Computability.encodeBool).outputsFun (run a)

/-- «Язык TM2-разрешим с КАКОЙ-НИБУДЬ кодировкой» — соблазнительная, но
    НЕВЕРНАЯ форма якоря (см. `tm2DecidesWithSomeEncoding_free`). -/
def TM2DecidesWithSomeEncoding (L : ClassicalProblem) : Prop :=
  ∃ (enc : L.Instance → List Bool) (run : L.Instance → Bool),
    (∀ x : L.Instance, run x = true ↔ L.Accepts x) ∧
    Nonempty (Turing.TM2ComputableInPolyTime enc Computability.encodeBool run)

/-- **🟢 АУДИТ (переименование цели вскрыто машинно): ∃-кодировка БЕСПЛАТНА.**
    Для КАЖДОГО языка `TM2DecidesWithSomeEncoding` — теорема: классический
    решатель + жульническая кодировка + машина-транспорт (§3). Значит,
    формулировать якорь фрейма через ∃-кодировку = переименовать True.
    Именно поэтому `TM2DecidesNatLanguage` ниже прибита к ФИКСИРОВАННОЙ
    канонической `Computability.encodeNat`. Урок SpectralAnchorAudit
    (Prop-невакуумность — неверный критерий) — здесь на уровне кодировок. -/
theorem tm2DecidesWithSomeEncoding_free (L : ClassicalProblem) :
    TM2DecidesWithSomeEncoding L := by
  classical
  exact ⟨fun x => Computability.encodeBool (decide (L.Accepts x)),
    fun x => decide (L.Accepts x),
    fun x => ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩,
    ⟨tm2AnswerTransport _⟩⟩

/-#############################################################################
  §4. Красный вход №2: мост от TM2-модели к faithful-фрейму
#############################################################################-/

/-- ℕ-язык как классическая задача фрейма (инстанции — натуральные числа). -/
def natProblem (Accepts : ℕ → Prop) : ClassicalProblem where
  Instance := ℕ
  Accepts := Accepts

/-- TM2-разрешимость ℕ-языка за полиномиальное время над КАНОНИЧЕСКОЙ
    бинарной кодировкой `Computability.encodeNat` (никакого ∃ по кодировке —
    см. аудит §3). Ответ машины читается через `Computability.encodeBool`. -/
def TM2DecidesNatLanguage (Accepts : ℕ → Prop) : Prop :=
  ∃ run : ℕ → Bool,
    (∀ n : ℕ, run n = true ↔ Accepts n) ∧
    Nonempty (Turing.TM2ComputableInPolyTime
      Computability.encodeNat Computability.encodeBool run)

/-- **🔴 КРАСНЫЙ ВХОД №2 (data-anchor): мост TM2-модель → faithful-фрейм.**

    Раскрытие: строитель обязан предъявить фрейм `C` такой, что
      1. `Nonempty (FaithfulPFrame C)` — конкретные решатели за `InP`
         и оба константных языка в P (отсечка дегенеративных фреймов);
      2. `C.InP` на ℕ-языках — В ТОЧНОСТИ TM2-polytime-разрешимость над
         канонической кодировкой (обе стороны iff, иначе `¬ InP` ничего
         не говорит о настоящих машинах).

    Чего в mathlib v4.31 НЕТ (и что математика должна предъявить):
      * замыкание под композицией — proof_wanted
        `TM2ComputableInPolyTime.comp` (Computable.lean:284, §2);
      * ни одной машины вида `run : ℕ → Bool` над `encodeNat` — даже
        константной (единственный житель модели — `idComputableInPolyTime`,
        Computable.lean:221, тип-в-себя);
      * перекодировщики между кодировками (recoding-машины).

    ⚠️ Аудиты честности: `faithful_frame_alone_is_free` — пункт 1 сам по себе
    бесплатен; `tm2FrameBridge_overclosure` — при ТЕКУЩЕЙ структуре
    `ClassicalComplexityFrame` (замыкание под СВОБОДНЫМИ PolyManyOneReduction)
    пункт 2 почти наверняка невыполним нетривиально: один неконстантный
    разрешимый язык затапливает InP всеми ℕ-языками. То есть якорь фиксирует
    и обязательство, и машинно вскрытую ловушку: сперва машинные редукции,
    потом мост. -/
def TM2FrameBridge : Prop :=
  ∃ C : ClassicalComplexityFrame,
    Nonempty (FaithfulPFrame C) ∧
    ∀ Accepts : ℕ → Prop,
      C.InP (natProblem Accepts) ↔ TM2DecidesNatLanguage Accepts

/-- **🟢 При якоре фронт закрывается:** `TM2FrameBridge` даёт faithful-фрейм,
    в котором `InP` на ℕ-языках несёт НАСТОЯЩУЮ машинную семантику, и вся
    мостовая машинерия репозитория (`Step00ToClassicalBridge` +
    несжимаемость ⟹ `ClassesSeparate`) работает над ним.
    ⚠️ ЧЕСТНОСТЬ: последний конъюнкт — `bridgeSlogan`, верный для ЛЮБОГО
    фрейма; добавленная стоимость якоря — исключительно iff-клауза
    (машинная семантика InP), не «разделение стало ближе». -/
theorem tm2FrameBridge_closes_machine_front (h : TM2FrameBridge) :
    ∃ C : ClassicalComplexityFrame,
      Nonempty (FaithfulPFrame C) ∧
      (∀ Accepts : ℕ → Prop,
        C.InP (natProblem Accepts) ↔ TM2DecidesNatLanguage Accepts) ∧
      ∀ N : Step00LocalNode, Step00ToClassicalBridge C N →
        N.LocalSearchIncompressible → C.ClassesSeparate := by
  obtain ⟨C, hFaithful, hIff⟩ := h
  exact ⟨C, hFaithful, hIff,
    fun _N B hInc => B.classicalSeparation_of_localIncompressible hInc⟩

/-#############################################################################
  §5. Аудиты на переименование цели для входа №2
#############################################################################-/

/-- Фрейм «всё в P»: локальный двойник `allPFrame` из PNPRankPaymentFront
    (тот модуль сюда не импортируется — аудит самодостаточен). -/
def freeFrame : ClassicalComplexityFrame where
  InP := fun _ => True
  InNP := fun _ => True
  P_closed_under_poly_preimage := fun _ _ => trivial

/-- Классический решатель любого языка (двойник `classicalPDecider`):
    `PDecider` не несёт complexity-содержания. -/
noncomputable def freeDecider (L : ClassicalProblem) : PDecider L := by
  classical
  exact
    { run := fun x => decide (L.Accepts x)
      sound := fun x hx => of_decide_eq_true hx
      complete := fun x hx => decide_eq_true hx }

/-- `freeFrame` проходит faithfulness-гейт репозитория. -/
theorem freeFrame_faithful : Nonempty (FaithfulPFrame freeFrame) :=
  ⟨{ concreteP := ⟨fun L _ => ⟨freeDecider L⟩⟩
     true_inP := trivial
     false_inP := trivial }⟩

/-- **🟢 АУДИТ (первая половина входа №2 бесплатна):** существование
    faithful-фрейма — НЕ содержание якоря: `freeFrame` даёт его даром.
    Вся тяжесть `TM2FrameBridge` — в iff-клаузе с `TM2DecidesNatLanguage`. -/
theorem faithful_frame_alone_is_free :
    ∃ C : ClassicalComplexityFrame, Nonempty (FaithfulPFrame C) :=
  ⟨freeFrame, freeFrame_faithful⟩

/-- **🟢 АУДИТ (замыкание отравлено свободным poly-полем):** в ЛЮБОМ фрейме
    репозитория один неконстантный ℕ-язык в InP затапливает InP всеми
    ℕ-языками: классическая редукция `n ↦ if A n then n₁ else n₀` легальна,
    ибо поле `polynomial_time` в `PolyManyOneReduction` — свободный Prop
    (`polynomial_time := True`). Никакой машины за `map` не требуется —
    в этом и дыра. -/
theorem frame_p_overclosure
    (C : ClassicalComplexityFrame)
    (A : ℕ → Prop) {A' : ℕ → Prop} {n₁ n₀ : ℕ}
    (h₁ : A' n₁) (h₀ : ¬ A' n₀)
    (hInP : C.InP (natProblem A')) :
    C.InP (natProblem A) := by
  classical
  refine C.P_closed_under_poly_preimage
    { map := fun n : ℕ => if A n then n₁ else n₀
      preserves := ?_
      polynomial_time := True
      polynomial_time_proof := trivial } hInP
  intro n
  by_cases hn : A n
  · rw [if_pos hn]
    exact iff_of_true hn h₁
  · rw [if_neg hn]
    exact iff_of_false hn h₀

/-- **🟢 АУДИТ (ловушка входа №2 машинно):** якорь `TM2FrameBridge` + ХОТЬ ОДИН
    неконстантный TM2-разрешимый ℕ-язык ⟹ TM2-разрешимы ВСЕ ℕ-языки (что
    математически абсурдно, хоть в пине и неопровержимо — диагонализации по
    `FinTM2` в mathlib нет). Вывод зафиксирован теоремой: нетривиальное
    выполнение якоря при текущем `ClassicalComplexityFrame` требует сперва
    ЗАМЕНИТЬ свободные редукции машинными. Якорь не подкрашен под выполнимый —
    ловушка выставлена наружу. -/
theorem tm2FrameBridge_overclosure
    (hBridge : TM2FrameBridge)
    (hWitness : ∃ (A' : ℕ → Prop) (n₁ n₀ : ℕ),
      TM2DecidesNatLanguage A' ∧ A' n₁ ∧ ¬ A' n₀) :
    ∀ A : ℕ → Prop, TM2DecidesNatLanguage A := by
  obtain ⟨C, _hFaithful, hIff⟩ := hBridge
  obtain ⟨A', n₁, n₀, hDec, h₁, h₀⟩ := hWitness
  intro A
  exact (hIff A).1 (frame_p_overclosure C A h₁ h₀ ((hIff A').2 hDec))

/-#############################################################################
  §6. Маркер охвата: якоря НЕ решают P/NP
#############################################################################-/

/-- **🟢 ЧЕСТНОСТЬ ОХВАТА (по образцу `notAProofOfBeal`):** этот модуль НЕ
    доказывает и НЕ опровергает P = NP и НЕ приближает вердикт. Здесь только:
    два ИМЕНОВАННЫХ красных def-входа (`TM2CompositionLaw` — proof_wanted
    mathlib; `TM2FrameBridge` — мост модель→фрейм), зелёные свидетели
    обитаемости TM2-модели и машинные аудиты честности (∃-кодировка
    протаскивает ответ; faithful-часть бесплатна; замыкание отравлено
    свободным poly-полем). Якоря — это точки стыковки для БУДУЩЕЙ математики,
    не её замена. -/
abbrev AnchorsDoNotDecidePNP : Prop := True

theorem anchors_do_not_decide_pnp : AnchorsDoNotDecidePNP := trivial

-- Машинная видимость чистоты прямо в build-логе: все новые экспорты
-- аксиомо-свободны (не более стандартной тройки
-- [propext, Classical.choice, Quot.sound]); таинт 47 не меняется.
#print axioms tm2_id_computable
#print axioms tm2_model_inhabited
#print axioms TM2CompositionLaw
#print axioms tm2CompositionLaw_shape_inhabited_id
#print axioms tm2AnswerTransport
#print axioms TM2DecidesWithSomeEncoding
#print axioms tm2DecidesWithSomeEncoding_free
#print axioms natProblem
#print axioms TM2DecidesNatLanguage
#print axioms TM2FrameBridge
#print axioms tm2FrameBridge_closes_machine_front
#print axioms freeFrame
#print axioms freeDecider
#print axioms freeFrame_faithful
#print axioms faithful_frame_alone_is_free
#print axioms frame_p_overclosure
#print axioms tm2FrameBridge_overclosure
#print axioms anchors_do_not_decide_pnp

end PNPDataAnchor
end EuclidsPath
