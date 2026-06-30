/-
  Pump Lemma v2 — concrete two-token standing engine. Формализация авторского файла.
  Источник: step00_pump_standing_engine_strict_proof_ru_2026-06-30.md. Проза: prose/27_PumpStanding.md.

  Исправление прошлой версии: вместо quotient self-loop `K→K` (мог быть бесконечным shift'ом, не
  циклом — реальная дыра) — concrete 2-cycle `D₁→D₂→D₁` между РАЗНЫМИ debt-tokens. Логически чище.

  pump v2: `γ₁≠γ₂ ∧ key γ₁ = key γ₂ ⟹ EuclideanEngine` через:
    same_key_payment + debtToken_ne + standing_engine_of_two_cycle.

  ЧЕСТНАЯ ГРАНИЦА (файл признаёт §14–15): три входа НЕ доказаны:
    (1) same_key_payment — key-коллизия ⟹ PaymentStep (сердце = бывший Hall-узел);
    (2) debtToken_ne — разные родословные ⟹ разные токены (различимость);
    (3) standing_engine_of_two_cycle — 2-cycle токенов ⟹ engine (= новый EPMI на standing-циклах).

  Здесь pump формализован как УСЛОВНАЯ теорема; #print axioms покажет, что нагрузка в трёх входах.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.PumpStanding

variable {Genealogy DebtToken : Type*}

/-- `pump` v2 (Theorem 10.1) — ЧИСТАЯ ЛОГИКА при трёх явных входах. -/
theorem pump
    {Key : Type*} (key : Genealogy → Key)
    (debt : Genealogy → DebtToken)
    (PaymentStep : DebtToken → DebtToken → Prop)
    (EuclideanEngine : Prop)
    -- (1) payment-completeness (НЕ доказан — сердце):
    (same_key_payment : ∀ a b : Genealogy, a ≠ b → key a = key b →
        PaymentStep (debt a) (debt b))
    -- (2) различимость токенов (НЕ доказан):
    (debtToken_ne : ∀ a b : Genealogy, a ≠ b → debt a ≠ debt b)
    -- (3) standing 2-cycle ⟹ engine (НЕ доказан — новый EPMI на standing-циклах):
    (standing_engine_of_two_cycle : ∀ D₁ D₂ : DebtToken, D₁ ≠ D₂ →
        PaymentStep D₁ D₂ → PaymentStep D₂ D₁ → EuclideanEngine)
    {γ₁ γ₂ : Genealogy} (hne : γ₁ ≠ γ₂) (hkey : key γ₁ = key γ₂) :
    EuclideanEngine :=
  standing_engine_of_two_cycle (debt γ₁) (debt γ₂)
    (debtToken_ne γ₁ γ₂ hne)
    (same_key_payment γ₁ γ₂ hne hkey)
    (same_key_payment γ₂ γ₁ (Ne.symm hne) hkey.symm)

/--
  **Two-cycle ДЕЙСТВИТЕЛЬНО чинит self-loop дыру (в одном смысле).** Concrete 2-cycle `D₁→D₂→D₁`
  с `D₁ ≠ D₂` — это настоящий directed cycle длины 2 в графе `PaymentStep`, не quotient-артефакт.
  В отличие от self-loop, он содержит ДВЕ разные вершины ⟹ это реальный цикл. (Логика цикла.) -/
theorem two_cycle_is_real_cycle {DebtToken : Type*}
    (PaymentStep : DebtToken → DebtToken → Prop) (D₁ D₂ : DebtToken)
    (hne : D₁ ≠ D₂) (h12 : PaymentStep D₁ D₂) (h21 : PaymentStep D₂ D₁) :
    D₁ ≠ D₂ ∧ PaymentStep D₁ D₂ ∧ PaymentStep D₂ D₁ :=
  ⟨hne, h12, h21⟩

/--
  **НО EPMI-разрыв ОСТАЁТСЯ (высота не падает в цикле).** Standing 2-cycle `D₁→D₂→D₁` ВОЗВРАЩАЕТСЯ
  в `D₁` — значит любая «высота» `h` на нём НЕ строго убывает (`h D₁ = h D₁` после обхода). Наш
  доказанный EPMI (`no_infinite_engine_descent`) запрещает строго УБЫВАЮЩИЙ спуск — а standing-цикл
  высоту СОХРАНЯЕТ. Значит `standing_engine_of_two_cycle ⟹ ⊥` из нашего высотного EPMI НЕ следует:
  нужен НОВЫЙ EPMI на lossless standing-циклах (§14.3), который НЕ доказан. -/
theorem standing_cycle_preserves_height {DebtToken : Type*}
    (h : DebtToken → ℕ) (D₁ D₂ : DebtToken) :
    h D₁ = h D₁ ∧ ¬ (h D₁ < h D₁) :=
  ⟨rfl, lt_irrefl _⟩

end EuclidsPath.PumpStanding
