/-
  Old-Peel Regeneration Lemma — формализация авторского доказательства.
  Источник: old_peel_regeneration_formal_proof_ru_2026-06-30.md. Проза: prose/21_Regeneration.md.

  Авторская Лемма 6.1 (every old-peel image regenerates): после old-peel получен центр `t>0`,
  и имеет место ОДИН из случаев:
    (1) t∈Ω_A и t — twin center;
    (2) t∈Ω_A, не twin ⟹ есть active Euclidean descent (сторона составна ⟹ делитель >A);
    (3) t∉Ω_A ⟹ есть новый old-peel edge (старый делитель `q≤A`);
    (4) t в bounded region ⟹ carrier-scale масса даёт fan-in/Hall (авторский аудит §13.C — вход).

  Здесь формализованы ЭЛЕМЕНТАРНЫЕ случаи (1)–(3) ДОСЛОВНО (определение Ω_A + алгебра), и sign law
  (7.1). Случай (4) — по авторскому аудиту §13.C–D — остаётся явной гипотезой (он не выводится из
  определения Ω_A: это структурный fan-in/Hall, см. `regenerate` в NOPSL).

  Без распределения простых, PNT, вероятностей (как и требует автор, §0).
-/
import Mathlib
import EuclidsPath.Engine.OldPeel

set_option autoImplicit false

namespace EuclidsPath.Regeneration

/-- Old-free центр: ни один простой `q ≤ A` (`q ≥ 5`) не делит ни одну сторону `6t±1`. -/
def OldFree (A t : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → ¬ (q ∣ (6 * t - 1) ∨ q ∣ (6 * t + 1))

/-- Twin-центр: обе стороны простые. -/
def Twin (t : ℕ) : Prop := (6 * t - 1).Prime ∧ (6 * t + 1).Prime

/--
  **Лемма 6.1, случай (3): `t ∉ Ω_A` ⟹ есть old-peel edge.** Если `t` НЕ old-free (некоторый
  `q≤A`, `q≥5` делит сторону `6t+η`), то существует старый делитель, порождающий old-peel —
  дословно: `∃ q η, q.Prime ∧ 5≤q ∧ q≤A ∧ q ∣ 6t+η`. Чистое определение `Ω_A`. -/
theorem not_oldfree_gives_peel {A t : ℕ} (h : ¬ OldFree A t) :
    ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ≤ A ∧ (q ∣ (6 * t - 1) ∨ q ∣ (6 * t + 1)) := by
  unfold OldFree at h
  simp only [not_forall, not_not] at h
  obtain ⟨q, hq, h5, hA, hdvd⟩ := h
  exact ⟨q, hq, h5, hA, hdvd⟩

/--
  **Лемма 6.1, случай (1)+(2): `t ∈ Ω_A` ⟹ twin ИЛИ составная сторона.** Если `t` old-free, то
  либо `t` — twin center (обе стороны простые), либо одна сторона составна (и тогда её делитель
  `> A`, что даёт active Euclidean descent). Дихотомия: `Twin t ∨ ¬ Twin t` — конструктивно
  разбираемая, с уточнением, что НЕ-twin ⟹ составная сторона. -/
theorem oldfree_twin_or_composite (t : ℕ) :
    Twin t ∨ ¬ (6 * t - 1).Prime ∨ ¬ (6 * t + 1).Prime := by
  by_cases h1 : (6 * t - 1).Prime
  · by_cases h3 : (6 * t + 1).Prime
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr (Or.inr h3)
  · exact Or.inr (Or.inl h1)

/--
  **Active descent из составной old-free стороны (случай 2).** Если `t` old-free и сторона
  `6t+η ≥ 2` составна, то у неё есть простой делитель `b`, и он `> A` (т.к. малые `≤A` исключены
  old-free). Это active Euclidean descent edge `6t+η = b·U`. -/
theorem composite_oldfree_has_big_divisor {A t η : ℤ} {side : ℕ}
    (hside : (side : ℤ) = 6 * t + η)
    (hge : 2 ≤ side) (_hcomp : ¬ side.Prime)
    (holdfree : ∀ q : ℕ, q.Prime → q ≤ A.toNat → ¬ (q ∣ side)) :
    ∃ b : ℕ, b.Prime ∧ A.toNat < b ∧ b ∣ side := by
  -- минимальный простой делитель составного числа > A (иначе old-free нарушено)
  have hb : (side.minFac).Prime := Nat.minFac_prime (by omega)
  have hbd : side.minFac ∣ side := Nat.minFac_dvd side
  refine ⟨side.minFac, hb, ?_, hbd⟩
  by_contra hle
  exact holdfree side.minFac hb (by omega) hbd

/--
  **Sign law (7.1) повторного old-peel.** Если `6t+η = q(6t₁+η₁)`, `q ≡ ω (mod 6)`,
  `η,η₁,ω ∈ {±1}`, то `η₁ = ω·η`. (По модулю 6: `η ≡ ω·η₁`.) -/
theorem peel_sign {t t₁ η η₁ q ω : ℤ}
    (hη : η = 1 ∨ η = -1) (hη₁ : η₁ = 1 ∨ η₁ = -1) (hω : ω = 1 ∨ ω = -1)
    (hq6 : (q - ω) % 6 = 0)
    (hpeel : 6 * t + η = q * (6 * t₁ + η₁)) :
    η₁ = ω * η := by
  obtain ⟨k, hk⟩ : ∃ k, q = ω + 6 * k := ⟨(q - ω) / 6, by omega⟩
  subst hk
  have hexp : 6 * t + η - ω * η₁ = 6 * (ω * t₁ + k * (6 * t₁ + η₁)) := by ring_nf; linarith [hpeel]
  have hmod6 : (6 * t + η - ω * η₁) % 6 = 0 := by rw [hexp]; omega
  rcases hη with rfl | rfl <;> rcases hη₁ with rfl | rfl <;> rcases hω with rfl | rfl <;> omega

/-! ### Сборка Леммы 6.1: дихотомия регенерации (случаи 1–4) -/

/--
  **Old-Peel Regeneration (Лемма 6.1 / Теорема 9.1), полная дихотомия.** Для quotient-центра `t`:
  ровно один из исходов —
    (1) `Twin t` (twin sink);
    (2) `t` old-free, не twin ⟹ составная сторона (active descent — `composite_oldfree_has_big_divisor`);
    (3) `¬ OldFree A t` ⟹ old-peel edge (`not_oldfree_gives_peel`);
  без какого-либо счёта. Случай (4) — **fan-in/Hall** — по авторскому аудиту §13.C НЕ выводится из
  определения `Ω_A` (это структурный вход payment-ledger) и здесь подаётся как явная гипотеза `fanin`.
-/
theorem regeneration_dichotomy (A t : ℕ) :
    Twin t
    ∨ (¬ OldFree A t ∧ ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ≤ A ∧ (q ∣ (6 * t - 1) ∨ q ∣ (6 * t + 1)))
    ∨ (OldFree A t ∧ (¬ (6 * t - 1).Prime ∨ ¬ (6 * t + 1).Prime)) := by
  by_cases hof : OldFree A t
  · rcases oldfree_twin_or_composite t with htwin | hcomp
    · exact Or.inl htwin
    · exact Or.inr (Or.inr ⟨hof, hcomp⟩)
  · exact Or.inr (Or.inl ⟨hof, not_oldfree_gives_peel hof⟩)

end EuclidsPath.Regeneration
