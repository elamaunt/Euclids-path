/-
  ParityBarrier — формализация СТЕНЫ ЧЁТНОСТИ как негативного результата, а НЕ доказательство близнецов.
  Источник: new_structural_routes_reverse_parity_barrier_ru_2026-07-01.md (Part IV + Part III reverse).
  Проза: prose/24_BoundaryDecomp.md (раздел «Стена чётности как теорема»).

  ГЛАВНЫЙ СДВИГ. Прежние 11 кирпичей ПЫТАЛИСЬ закрыть близнецов и упирались в counting/parity стену.
  Этот кирпич делает иное: формализует САМУ СТЕНУ как теорему — доказывает, что finite-sieve движок
  (сертификат, зависящий лишь от конечного вида уровня `A`) НЕ МОЖЕТ сертифицировать twin через
  ambiguity, и что пересечение стены ТРЕБУЕТ cofinal-информации. Это негативный/диагностический
  результат, честно НЕ утверждающий twin primes.

  ЗДЕСЬ ДОКАЗАНО (чистая логика + один арифметический факт, std аксиомы, без sorry):
    * `parityBlind_cannot_certify_twin` — parity-blind + sound + ambiguity ⟹ False (сердце стены);
    * `sound_cert_ambiguous_at_level_not_blind`, `sound_cert_requires_cofinal_information` — sound-cert
      при ambiguity на каждом уровне ⟹ требует cofinal-информации;
    * `finite_sieve_engine_cannot_cross_barrier` — finite-sieve движок не пересекает стену;
    * `parity_barrier_model_no_finite_view_decides_twin` — модельная форма (никакой конечный вид не
      решает twin при ambiguity);
    * `finite_twins_contradiction_requires_cofinal_cert` — любое опровержение конечности близнецов
      новым сертификатом обязано использовать cofinal-информацию;
    * `exists_clean_nonTwin_block` — стена НЕ вакуумна: clean-non-twin блок существует;
    * `repeated_value_of_infinite_finite` — pigeonhole (для reverse-tree);
    * `contradiction_of_finiteTwinEuclid` — правильная форма конечно-списочного противоречия (§2).

  ЧЕСТНАЯ ГРАНИЦА. Это НЕ доказательство близнецов и НЕ его редукция. Это доказательство ОГРАНИЧЕНИЯ:
  чтобы закрыть Step00, нужно предъявить `RequiresCofinalInformation`-сертификат (cofinal, а не
  finite-sieve). Конкретная Step00-инстанциация (`Step00Cert`, `AmbiguousAtEveryFiniteLevel` для нашего
  движка, reverse-barrier §22–23) — ВХОДЫ, где стена возвращается: `AmbiguousAtEveryFiniteLevel` для
  реального движка ≈ то, что движок finite-sieve = не пересекает стену. Здесь эти инстанциации не
  предъявлены. `Step00` остаётся `sorry`. Ценность: стена стала машинно-проверенной теоремой, а
  требование к её пересечению — точным и аудируемым.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ParityBarrier

open EuclidsPath.Residuals

/-! ### §26. TwinBlock: пара сторон как один объект. Здесь центр = ℕ, twin = `TwinCenterZ`. -/

/-- Блок-близнец задаётся центром; `IsTwin` = обе стороны просты (`TwinCenterZ`). -/
abbrev IsTwin (B : ℕ) : Prop := TwinCenterZ B

/-! ### §27–28. Sieve-view система и parity-blind предикат -/

/-- Система конечных «видов» уровня `A` (сито-вид блока на уровне `A`). Интерфейс, без residues. -/
structure SieveViewSystem where
  View : ℕ → Type
  view : ∀ A, ℕ → View A

/-- Два блока `A`-эквивалентны, если совпадают их виды на уровне `A`. -/
def SieveEquivalent (S : SieveViewSystem) (A : ℕ) (B₁ B₂ : ℕ) : Prop := S.view A B₁ = S.view A B₂

/-- Сертификат `parity-blind` на уровне `A`: зависит лишь от `A`-вида (не различает `A`-эквивалентные). -/
def ParityBlindPredicate (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) : Prop :=
  ∀ B₁ B₂, SieveEquivalent S A B₁ B₂ → (Cert B₁ ↔ Cert B₂)

/-- Требует cofinal-информации: НЕ parity-blind ни на одном уровне. -/
def RequiresCofinalInformation (S : SieveViewSystem) (Cert : ℕ → Prop) : Prop :=
  ∀ A, ¬ ParityBlindPredicate S A Cert

/-! ### §29–30. Sound-сертификат и ambiguity на уровне -/

/-- `Cert` корректен: сертифицирует только реальные twin-блоки. -/
def SoundTwinCert (Cert : ℕ → Prop) : Prop := ∀ B, Cert B → IsTwin B

/-- Ambiguity на уровне `A`: `A`-эквивалентные `good` (сертифицирован) и `bad` (не twin). -/
def CertAmbiguousAt (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) : Prop :=
  ∃ good bad, SieveEquivalent S A good bad ∧ Cert good ∧ ¬ IsTwin bad

/-! ### §31–33. СЕРДЦЕ СТЕНЫ: parity-blind + sound + ambiguity ⟹ False -/

/--
  **`parityBlind_cannot_certify_twin` — ДОКАЗАНА (сердце стены чётности).** Parity-blind сертификат
  (зависит лишь от `A`-вида) + корректность + ambiguity (`A`-эквивалентные `good`/`bad`, `bad` не
  twin) ⟹ `False`. Механизм: blind переносит сертификат с `good` на `bad`, корректность делает `bad`
  twin — против `¬IsTwin bad`. Чистая логика: конечный вид не может отличить twin от не-twin. -/
theorem parityBlind_cannot_certify_twin (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop)
    (hBlind : ParityBlindPredicate S A Cert) (hSound : SoundTwinCert Cert)
    (hAmb : CertAmbiguousAt S A Cert) : False := by
  obtain ⟨good, bad, hSame, hCertGood, hBadNotTwin⟩ := hAmb
  exact hBadNotTwin (hSound bad ((hBlind good bad hSame).mp hCertGood))

/-- **`sound_cert_ambiguous_at_level_not_blind` — ДОКАЗАНА.** Sound + ambiguity на `A` ⟹ НЕ blind на `A`. -/
theorem sound_cert_ambiguous_at_level_not_blind (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert) (hAmb : CertAmbiguousAt S A Cert) :
    ¬ ParityBlindPredicate S A Cert :=
  fun hBlind => parityBlind_cannot_certify_twin S A Cert hBlind hSound hAmb

/-- Ambiguity на каждом конечном уровне. -/
def AmbiguousAtEveryFiniteLevel (S : SieveViewSystem) (Cert : ℕ → Prop) : Prop :=
  ∀ A, CertAmbiguousAt S A Cert

/--
  **`sound_cert_requires_cofinal_information` — ДОКАЗАНА (главная диагностика).** Sound-сертификат +
  ambiguity на КАЖДОМ уровне ⟹ он требует cofinal-информации (не blind ни на одном `A`). То есть
  корректный сертификат близнецов при неснимаемой ambiguity не может факторизоваться через конечный
  вид — он обязан «видеть бесконечно далеко». Это точная форма стены чётности. -/
theorem sound_cert_requires_cofinal_information (S : SieveViewSystem) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert) (hAmbAll : AmbiguousAtEveryFiniteLevel S Cert) :
    RequiresCofinalInformation S Cert :=
  fun A => sound_cert_ambiguous_at_level_not_blind S A Cert hSound (hAmbAll A)

/-! ### §34. Finite-sieve движок не пересекает стену -/

/-- Finite-sieve движок: сертификат, blind на некотором конечном уровне `cutoff`. Несёт данные
    (`cutoff`), поэтому `Type`, не `Prop`. -/
structure FiniteSieveEngine (S : SieveViewSystem) (Cert : ℕ → Prop) where
  cutoff : ℕ
  blind : ParityBlindPredicate S cutoff Cert

/--
  **`finite_sieve_engine_cannot_cross_barrier` — ДОКАЗАНА (чистый no-go).** Finite-sieve движок
  (blind на `cutoff`) + корректность + ambiguity на `cutoff` ⟹ `False`. Финитно-сеточный сертификат
  не может пересечь стену чётности. -/
theorem finite_sieve_engine_cannot_cross_barrier (S : SieveViewSystem) (Cert : ℕ → Prop)
    (E : FiniteSieveEngine S Cert) (hSound : SoundTwinCert Cert)
    (hAmb : CertAmbiguousAt S E.cutoff Cert) : False :=
  parityBlind_cannot_certify_twin S E.cutoff Cert E.blind hSound hAmb

/-! ### §40. Модельная форма стены (независима от реального существования близнецов) -/

/--
  **`parity_barrier_model_no_finite_view_decides_twin` — ДОКАЗАНА (модельная стена).** Если в модели
  есть ambiguity (виды `X`, `Y` совпадают на `A`, но `X` twin, `Y` — нет), то никакой предикат
  `DecideTwin` на `A`-виде не может корректно решать `modelTwin`. Чистая логика, не зависит от
  арифметики близнецов — формальная модель parity barrier. -/
theorem parity_barrier_model_no_finite_view_decides_twin {View ModelBlock : Type*}
    (modelView : ModelBlock → View) (modelTwin : ModelBlock → Prop)
    (X Y : ModelBlock) (hView : modelView X = modelView Y)
    (hTwinX : modelTwin X) (hNotTwinY : ¬ modelTwin Y)
    (DecideTwin : View → Prop) (hCorrect : ∀ Z, DecideTwin (modelView Z) ↔ modelTwin Z) : False :=
  hNotTwinY ((hCorrect Y).mp (hView ▸ (hCorrect X).mpr hTwinX))

/-! ### §2. Правильная форма конечно-списочного противоречия -/

/-- §2: конечно-списочное противоречие. Полный список `T` twin-центров + новый twin вне `T` ⟹ False. -/
structure FiniteTwinEuclidContradiction where
  T : Finset ℕ
  complete : ∀ m, IsTwin m → m ∈ T
  newCenter : ℕ
  newTwin : IsTwin newCenter
  newNotIn : newCenter ∉ T

/-- **`contradiction_of_finiteTwinEuclid` — ДОКАЗАНА (§2, чистая логика).** -/
theorem contradiction_of_finiteTwinEuclid (E : FiniteTwinEuclidContradiction) : False :=
  E.newNotIn (E.complete E.newCenter E.newTwin)

/--
  **`finite_twins_contradiction_requires_cofinal_cert` — ДОКАЗАНА (§41, диагностика).** Любое
  опровержение конечности близнецов через НОВЫЙ корректный сертификат при ambiguity на каждом уровне
  ОБЯЗАНО использовать cofinal-информацию. То есть finite-sieve движок этого сделать не может. -/
theorem finite_twins_contradiction_requires_cofinal_cert (S : SieveViewSystem) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert) (hAmbAll : AmbiguousAtEveryFiniteLevel S Cert) :
    RequiresCofinalInformation S Cert :=
  sound_cert_requires_cofinal_information S Cert hSound hAmbAll

/-! ### §39. Стена НЕ вакуумна: clean-non-twin блок существует (не контрабанда близнецов) -/

/--
  **`exists_clean_nonTwin_block` — ДОКАЗАНА.** Существует чистый (на уровне 1) не-twin центр: `m = 4`
  (сторона `25 = 5²` не проста ⟹ не twin). Это гарантирует, что ambiguity/barrier — НЕ вакуумная
  абстракция: реальные clean-non-twin блоки есть. (Мы НЕ утверждаем существование clean-TWIN блока —
  это была бы контрабанда близнецов, §39.) -/
theorem exists_clean_nonTwin_block : ∃ m : ℕ, CleanZ 1 (m : ℤ) ∧ ¬ IsTwin m := by
  refine ⟨4, ?_, ?_⟩
  · intro q hq hq1; interval_cases q <;> simp_all [Nat.Prime]
  · intro h; have := h.2; norm_num [Nat.Prime] at this

/-! ### Reverse-engine ядро (Part III): pigeonhole ⟹ повтор подписи на луче -/

/-- **`repeated_value_of_infinite_finite` — ДОКАЗАНА (§18 pigeonhole).** Бесконечная
    последовательность в конечный тип имеет повтор `f i = f j`, `i < j`. Основа reverse-barrier. -/
theorem repeated_value_of_infinite_finite {Sig : Type*} [Finite Sig] (f : ℕ → Sig) :
    ∃ i j, i < j ∧ f i = f j := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

end EuclidsPath.ParityBarrier
