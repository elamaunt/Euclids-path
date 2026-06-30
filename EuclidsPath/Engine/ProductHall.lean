/-
  ProductHall / SteeringEngine — строгий локальный pump БЕЗ циркулярного payment.
  Источник: step00_producthall_steering_pump_strict_ru_2026-07-01.md. Проза: prose/29_ProductHall.md.

  Существенное улучшение прошлых pump: НЕ использует «same key ⟹ payment по определению» (§9 явно
  это отвергает — устранение циркулярности, которую нашёл аудит). Вместо этого — 4-случайная
  дихотомия зон Legal/Forbidden с настоящим логическим содержанием.

  ДОКАЗУЕМОЕ ЯДРО (здесь): zone-дихотомия + steering-конструкторы + `productHall_engine` (логика по
  случаям). Открытые узлы (явные гипотезы): `UniqueLegalLift` (нормальность паспорта) и
  `SteeringEngine ⟹ EuclideanEngine` (новый EPMI на steering). Они НЕ доказаны — но это
  СТРУКТУРНЫЕ узлы, не циркулярные определения.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.ProductHall

variable {EngineState : Type*}

/-- Конфигурация локального движка: зоны, шаг, паспорт. Все поля — абстрактные предикаты/функции;
    их конкретная реализация (product-state `6m+σ`, residue-паспорт) — вход. -/
structure HallConfig (EngineState : Type*) (Passport : Type*) where
  Legal : EngineState → Prop
  Forbidden : EngineState → Prop
  RigidStep : EngineState → EngineState → Prop
  pass : EngineState → Passport
  EuclideanEngine : Prop
  /-- zone dichotomy (§1): каждое состояние legal или forbidden -/
  zone_cases : ∀ X, Legal X ∨ Forbidden X
  /-- **UniqueLegalLift (UL, §4) — ОТКРЫТЫЙ узел.** Два legal-lift одного паспорта над одним base
      совпадают. (Должно следовать из паспорта как нормальной формы legal-state; §13.) -/
  uniqueLegalLift : ∀ X₁ X₂ Y, RigidStep X₁ Y → RigidStep X₂ Y →
      pass X₁ = pass X₂ → Legal X₁ → Legal X₂ → X₁ = X₂
  /-- **SteeringEngine ⟹ EuclideanEngine (§6) — ОТКРЫТЫЙ узел (новый EPMI).** Любая steering-
      конфигурация (пересечение legal/forbidden boundary) даёт запрещённый двигатель. -/
  steering_is_euclidean : ∀ X₁ X₂ Y, X₁ ≠ X₂ → pass X₁ = pass X₂ →
      RigidStep X₁ Y → RigidStep X₂ Y →
      ((Legal X₁ ∧ Forbidden X₂) ∨ (Forbidden X₁ ∧ Legal X₂) ∨
       (Forbidden X₁ ∧ Legal Y) ∨ (Forbidden X₂ ∧ Legal Y)) →
      EuclideanEngine

variable {Passport : Type*}

/--
  **ProductHall ⟹ EuclideanEngine (Lemma 8.1) — ДОКАЗАНО по 4 случаям.** Локальный fan-in
  `X₁→Y`, `X₂→Y` с `X₁≠X₂`, одинаковым паспортом, и `Legal Y`. Разбор зон `X₁,X₂`:
  - оба legal ⟹ `uniqueLegalLift` даёт `X₁=X₂`, противоречие;
  - смешанные ⟹ steering;
  - оба forbidden ⟹ forbidden-inflow в legal Y ⟹ steering.
  Во всех случаях — `EuclideanEngine`. Это ЧИСТАЯ ЛОГИКА (не циркулярна), на двух открытых узлах. -/
theorem productHall_engine (C : HallConfig EngineState Passport)
    (X₁ X₂ Y : EngineState) (hne : X₁ ≠ X₂) (hp : C.pass X₁ = C.pass X₂)
    (h1 : C.RigidStep X₁ Y) (h2 : C.RigidStep X₂ Y) (hYlegal : C.Legal Y) :
    C.EuclideanEngine := by
  rcases C.zone_cases X₁ with hX1L | hX1F
  · rcases C.zone_cases X₂ with hX2L | hX2F
    · -- оба legal ⟹ X₁=X₂, противоречие
      exact absurd (C.uniqueLegalLift X₁ X₂ Y h1 h2 hp hX1L hX2L) hne
    · -- legal/forbidden ⟹ steering
      exact C.steering_is_euclidean X₁ X₂ Y hne hp h1 h2 (Or.inl ⟨hX1L, hX2F⟩)
  · rcases C.zone_cases X₂ with hX2L | hX2F
    · -- forbidden/legal ⟹ steering
      exact C.steering_is_euclidean X₁ X₂ Y hne hp h1 h2 (Or.inr (Or.inl ⟨hX1F, hX2L⟩))
    · -- оба forbidden, Y legal ⟹ forbidden-inflow ⟹ steering
      exact C.steering_is_euclidean X₁ X₂ Y hne hp h1 h2 (Or.inr (Or.inr (Or.inl ⟨hX1F, hYlegal⟩)))

/--
  **Почему это НЕ переименование payment (§9).** Здесь нет «same key ⟹ payment». Содержание —
  в `uniqueLegalLift` (нормальность) и zone-дихотомии: коллизия паспортов разрешается ЛИБО
  совпадением (UL), ЛИБО steering'ом. Это разные логические ветки, а не вшитый вывод. -/
theorem productHall_noncircular (C : HallConfig EngineState Passport)
    (X₁ X₂ Y : EngineState) (h1 : C.RigidStep X₁ Y) (h2 : C.RigidStep X₂ Y)
    (hp : C.pass X₁ = C.pass X₂) (hX1L : C.Legal X₁) (hX2L : C.Legal X₂) :
    X₁ = X₂ :=
  C.uniqueLegalLift X₁ X₂ Y h1 h2 hp hX1L hX2L

end EuclidsPath.ProductHall
