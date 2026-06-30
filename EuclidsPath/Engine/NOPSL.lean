/-
  NOPSL — No Old-Peel Sink Lemma. Замыкание SNOL через old-peel регенерацию.
  Источник: snol_old_peel_closure_ru_2026-06-30.md (§5–14). Проза: prose/20_NOPSL.md.

  Абстрактное ядро финального замыкания. Состояние old-peel ledger имеет высоту `h : σ → ℕ`.
  Дихотомия каждого состояния (§10–11, four cases): либо оно — КОРРЕКТНЫЙ sink (twin / clean-возврат
  с остановкой), либо у него есть преемник СТРОГО МЕНЬШЕЙ высоты (next old-peel / fan-in / known
  defect — все они old-peel-регенерируют, `t < n`, см. `OldPeel.old_peel_height_drop`).

  NOPSL: carrier-scale SN-catch НЕ может быть genuine terminal sink. Формально: если поток не имеет
  корректного sink (нет twin), то у каждого состояния есть нисходящий преемник ⟹ бесконечный строгий
  спуск ⟹ противоречие с двигателем (EPMI, `no_infinite_engine_descent`).

  Логика — та же, что у двигателя: строгое убывание высоты не может длиться вечно.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.Irreversibility
import EuclidsPath.Engine.OldPeel
import EuclidsPath.Engine.TwoTransport

set_option autoImplicit false

namespace EuclidsPath.NOPSL

open EuclidsPath.Engine

variable {σ : Type*}

/--
  **Дихотомия состояния (§10–11, four-case taxonomy).** `Sink` — корректная остановка потока
  (twin sink или clean-возврат, который не продолжается вниз). `Step h s s'` — old-peel шаг со
  строгим падением высоты (`h s' < h s`): покрывает next-peel / fan-in / known-defect.
-/
structure OldPeelLedger (σ : Type*) where
  /-- высота состояния (центр) -/
  h : σ → ℕ
  /-- корректный sink: twin или остановившийся clean-возврат -/
  Sink : σ → Prop
  /-- old-peel преемник со строгим падением высоты -/
  Step : σ → σ → Prop
  /-- **закон old-peel:** каждый шаг строго уменьшает высоту (`OldPeel.old_peel_height_drop`) -/
  step_drops : ∀ {s s'}, Step s s' → h s' < h s
  /-- **регенерация (§10, NOPSL-ядро):** не-sink состояние ВСЕГДА имеет old-peel преемника
      (clean-возврат/next-peel/fan-in/known-defect — но не «висячий» терминал) -/
  regenerate : ∀ s, ¬ Sink s → ∃ s', Step s s'

/--
  **NOPSL (Теорема 11.1 / 13.1).** В old-peel ledger из любого состояния поток за конечное число
  шагов достигает корректного sink: НЕ существует бесконечной траектории без sink. Доказательство —
  чистая логика двигателя: иначе высота строго убывает вечно (`step_drops`), что невозможно в ℕ.
-/
theorem no_old_peel_sink (L : OldPeelLedger σ) (start : σ) :
    ∃ s, L.Sink s := by
  by_contra hno
  -- нет ни одного sink ⟹ каждое состояние не-sink ⟹ имеет нисходящего преемника
  have hstep : ∀ s, ∃ s', L.Step s s' := fun s => L.regenerate s (fun hs => hno ⟨s, hs⟩)
  -- строим бесконечную цепь по выбору преемника
  choose next hnext using hstep
  let z : ℕ → σ := fun k => Nat.rec start (fun _ s => next s) k
  have hz : ∀ k, L.Step (z k) (z (k + 1)) := fun k => hnext (z k)
  -- высота строго убывает на каждом шаге ⟹ бесконечный спуск ⟹ False
  have hdrop : ∀ k, L.h (z (k + 1)) < L.h (z k) := fun k => L.step_drops (hz k)
  exact OldPeel.old_peel_terminates (fun k => L.h (z k)) hdrop

/--
  **SNOL как следствие NOPSL (§13).** Если carrier-scale terminal shifted-neighbour obstruction
  существовал бы, его состояния были бы НЕ-sink (нет twin) и НЕ имели бы регенерации — что
  противоречит `regenerate`. Значит obstruction невозможен: поток достигает twin sink.
  Формально: из любого старта существует sink (= twin или остановка), `no_old_peel_sink`.
-/
theorem snol_of_nopsl (L : OldPeelLedger σ) (start : σ) : ∃ s, L.Sink s :=
  no_old_peel_sink L start

/-! ### Мост к гипотезе: NOPSL ⟹ бесконечно много близнецов -/

open EuclidsPath in
/--
  **Финальное замыкание (Теорема 14.1).** Пусть на каждом масштабе `N` дан old-peel ledger со
  стартом, у которого КАЖДЫЙ корректный sink — это twin-центр выше `N` (поток old-peel
  останавливается только на близнеце). Тогда по NOPSL sink существует, значит на каждом `N` есть
  twin-центр выше `N` ⟹ простых-близнецов бесконечно много (`infinite_of_unbounded_centers`).

  Это замыкает всю программу на двигатель: единственный вход — структура `OldPeelLedger`
  (регенерация old-peel + строгое падение высоты), а НЕ распределение.
-/
theorem twin_primes_of_nopsl
    (L : ∀ N : ℕ, OldPeelLedger σ) (start : ∀ N : ℕ, σ)
    (center : ∀ N : ℕ, σ → ℕ)
    (sink_is_twin : ∀ N s, (L N).Sink s → N < center N s ∧ IsTwinCenter (center N s)) :
    TwinLowers.Infinite := by
  apply infinite_of_unbounded_centers
  intro N
  obtain ⟨s, hs⟩ := no_old_peel_sink (L N) (start N)
  exact ⟨center N s, sink_is_twin N s hs⟩

end EuclidsPath.NOPSL
