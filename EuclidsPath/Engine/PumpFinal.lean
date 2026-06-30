/-
  Pump Lemma — финальный узел Step00, формализация авторского файла.
  Источник: step00_final_pump_payment_complete_normsig_ru_2026-06-30.md. Проза: prose/26_Pump.md.

  Авторская цель: `γ₁≠γ₂ ∧ key γ₁ = key γ₂ ⟹ EuclideanEngine` (закрывает GlobalAbsorberNode).
  Через: collision ⟹ CertifiedPayment ⟹ rigid self-loop ⟹ engine.

  ЧЕСТНАЯ ГРАНИЦА (файл сам признаёт §15–16): `pump` — тривиальная ЛОГИКА, если даны три входа:
    (1) PaymentCompleteKey: key-коллизия ⟹ CertifiedPayment  — НЕ доказан (сердце);
    (2) rigid_payment_step: CertifiedPayment ⟹ RigidStep self-loop — НЕ доказан;
    (3) engine_of_self_loop: RigidStep S S ⟹ engine — зависит от ОПРЕДЕЛЕНИЯ engine.

  КРИТИЧНО: наш доказанный EPMI (`no_infinite_engine_descent`) запрещает бесконечный СТРОГО
  УБЫВАЮЩИЙ спуск ВЫСОТЫ. Self-loop `LedgerState K → LedgerState K` высоту НЕ меняет — это НЕ строгий
  спуск. Значит `engine_of_self_loop` под нашим EPMI НЕ выводится: «engine = self-loop» — ДРУГОЕ
  понятие, чем «engine = бесконечный спуск». Это разрыв, помеченный явно.

  Здесь pump формализован как УСЛОВНАЯ теорема: все три входа — явные гипотезы. `#print axioms`
  покажет, что вся нагрузка в них.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.PumpFinal

variable {Genealogy AbsKey RigidState : Type*}

/-- `pump` (Theorem 12.1) — ЧИСТАЯ ЛОГИКА при трёх явных входах. -/
theorem pump
    (key : Genealogy → AbsKey)
    (LedgerState : AbsKey → RigidState)
    (RigidStep : RigidState → RigidState → Prop)
    (EuclideanEngine : Prop)
    -- (1) payment-completeness (НЕ доказан — сердце узла):
    (same_key_payment : ∀ γ₁ γ₂ : Genealogy, γ₁ ≠ γ₂ → key γ₁ = key γ₂ →
        RigidStep (LedgerState (key γ₁)) (LedgerState (key γ₁)))
    -- (2) self-loop ⟹ engine (зависит от определения engine; под нашим EPMI НЕ выводится):
    (engine_of_self_loop : ∀ S : RigidState, RigidStep S S → EuclideanEngine)
    {γ₁ γ₂ : Genealogy} (hne : γ₁ ≠ γ₂) (hkey : key γ₁ = key γ₂) :
    EuclideanEngine :=
  engine_of_self_loop (LedgerState (key γ₁)) (same_key_payment γ₁ γ₂ hne hkey)

/--
  **Разрыв EPMI (явно).** Наш `no_infinite_engine_descent` (Irreversibility) запрещает бесконечный
  СТРОГО убывающий спуск высоты. Self-loop сохраняет высоту (`h S = h S`), значит постоянная цепь
  `z = fun _ => S` НЕ `StrictAnti` ⟹ EPMI к ней НЕприменим. Поэтому «self-loop ⟹ ⊥» из нашего EPMI
  НЕ следует: для закрытия нужно РАСШИРИТЬ EPMI до lossless-ledger-циклов (§15.3), а это НЕ доказано. -/
theorem self_loop_height_preserved {RigidState : Type*} (h : RigidState → ℕ) (S : RigidState) :
    h S = h S ∧ ¬ (h S < h S) := ⟨rfl, lt_irrefl _⟩

end EuclidsPath.PumpFinal
