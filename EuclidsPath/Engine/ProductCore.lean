/-
  Исправленный product-core rank descent. Формализация авторского файла.
  Источник: step00_product_core_rank_descent_corrected_ru_2026-07-01.md. Проза: prose/32_ProductCore.md.

  Отвечает на 3 дефекта прошлого аудита ПО ИМЕНИ:
    Дефект 1 (extensionality): индукция по PRODUCT-CORE (RankNode), а не по genealogies. Tail/absorber
      (570→1 fan-in) В RANKNODE НЕ ВХОДИТ ⟹ no_mismatch_core_eq реален (экстенсиональность ядра).
    Дефект 2 (residual bound): AmbientLegal-сертификат (факторы делят один top side ≤6X_A+1) ⟹
      a_i < P_A на ВСЕХ рангах; сохраняется удалением.
    Дефект 3 (finiteness): CoreSig над ZMod P_A при ФИКСИРОВАННОМ A — Fintype.

  Здесь — КОНКРЕТНЫЙ RankNode (factors : Fin r → ℕ), чтобы экстенсиональность была настоящей
  теоремой. Проверяем, какие из 3 fix реально доказываются и что остаётся.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.ProductCore

/-- Знак стороны. -/
inductive Sign | plus | minus
deriving DecidableEq, Fintype

/-- **Product-core node ранга `r`** (Def 2.1): знак + role-indexed факторы, БЕЗ genealogy/tail.
    `factors : Fin r → ℕ` — вот ключ: состояние ЭКСТЕНСИОНАЛЬНО по (sign, factors). -/
structure RankNode (r : ℕ) where
  sign : Sign
  factors : Fin r → ℕ
deriving DecidableEq

/-- **Fix1 — экстенсиональность ядра (Lemma 9.1) ДОКАЗАНА.** Если у двух RankNode совпали знак и
    ВСЕ факторы (нет mismatch), то они равны. Это настоящая теорема (не гипотеза), потому что
    RankNode НЕ содержит tail/absorber — 570→1 fan-in сюда не входит. -/
theorem no_mismatch_core_eq {r : ℕ} (X₁ X₂ : RankNode r)
    (hsign : X₁.sign = X₂.sign) (hfac : ∀ k, X₁.factors k = X₂.factors k) :
    X₁ = X₂ := by
  cases X₁; cases X₂
  simp only [RankNode.mk.injEq]
  exact ⟨hsign, funext hfac⟩

/-! ### Fix2 — AmbientLegal: граница a < P_A на всех рангах -/

/-- `AmbientLegal` (Def 3.1): все факторы делят один top legal side `N₀ ≤ 6X_A+1`. -/
def AmbientLegal (X_A : ℕ) {r : ℕ} (factors : Fin r → ℕ) : Prop :=
  ∃ N₀ : ℕ, 0 < N₀ ∧ N₀ ≤ 6 * X_A + 1 ∧ ∀ i, factors i ∣ N₀

/-- **Fix2a — factor bound (Lemma 4.1) ДОКАЗАНА.** Separating scale + AmbientLegal ⟹ каждый
    фактор `< P_A`. (`a_i ∣ N₀ ≤ 6X_A+1 < P_A`.) -/
theorem ambient_factor_lt_primorial {X_A P_A : ℕ} {r : ℕ} {factors : Fin r → ℕ}
    (hsep : 6 * X_A + 1 < P_A) (hamb : AmbientLegal X_A factors) :
    ∀ i, factors i < P_A := by
  obtain ⟨N₀, hpos, hle, hdvd⟩ := hamb
  intro i
  have : factors i ≤ N₀ := Nat.le_of_dvd hpos (hdvd i)
  omega

/-- **Fix2b — AmbientLegal сохраняется удалением (Lemma 5.2) ДОКАЗАНА.** Факторы residual —
    подмножество факторов `X`, значит тот же `N₀` подходит. (Удаление role `k` через `Fin.succAbove`.) -/
theorem ambientLegal_delete {X_A : ℕ} {r : ℕ} {factors : Fin (r + 1) → ℕ} (k : Fin (r + 1))
    (hamb : AmbientLegal X_A factors) :
    AmbientLegal X_A (fun i : Fin r => factors (k.succAbove i)) := by
  obtain ⟨N₀, hpos, hle, hdvd⟩ := hamb
  exact ⟨N₀, hpos, hle, fun i => hdvd (k.succAbove i)⟩

/-! ### Fix3 — CoreSig конечна при фиксированном A -/

/-- `CoreSig` (Def 6.1) при фиксированном `P_A`: знак + residues факторов mod P_A. БЕЗ genealogy. -/
structure CoreSig (P_A r : ℕ) where
  sign : Sign
  residues : Fin r → ZMod P_A
deriving DecidableEq

/-- **Fix3 — CoreSig конечна (Lemma 7.1) ДОКАЗАНА** при фиксированном `P_A > 0` и `r`. -/
noncomputable instance coreSig_fintype {P_A r : ℕ} [NeZero P_A] : Fintype (CoreSig P_A r) :=
  Fintype.ofInjective
    (fun s => (s.sign, s.residues))
    (by intro a b h; cases a; cases b; simp only [Prod.mk.injEq] at h; cases h.1; cases h.2; rfl)

/-! ### No ProductHall на RankNode (через separating scale) -/

/-- `coreSigOf`: подпись из RankNode. -/
def coreSigOf {P_A r : ℕ} (X : RankNode r) : CoreSig P_A r :=
  ⟨X.sign, fun i => (X.factors i : ZMod P_A)⟩

/--
  **No ProductHall (Lemma 12.1) ДОКАЗАНА на RankNode.** Если факторы обоих `< P_A` (AmbientLegal +
  separating scale, `ambient_factor_lt_primorial`) и сравнимы mod P_A на role `k`, то они равны —
  противоречие с `a_k(X₁) ≠ a_k(X₂)`. Значит ProductHall невозможен на каждом ранге. -/
theorem no_productHall {P_A r : ℕ} {X₁ X₂ : RankNode r} (k : Fin r)
    (h1 : X₁.factors k < P_A) (h2 : X₂.factors k < P_A)
    (hcong : (X₁.factors k : ZMod P_A) = (X₂.factors k : ZMod P_A))
    (hne : X₁.factors k ≠ X₂.factors k) : False := by
  -- residue равенство + оба < P_A ⟹ равны
  have : X₁.factors k = X₂.factors k := by
    have hP : 0 < P_A := by
      rcases Nat.eq_zero_or_pos P_A with h0 | hp
      · subst h0; omega
      · exact hp
    have e1 : (X₁.factors k : ZMod P_A).val = X₁.factors k := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt h1
    have e2 : (X₂.factors k : ZMod P_A).val = X₂.factors k := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt h2
    rw [← e1, ← e2, hcong]
  exact hne this

end EuclidsPath.ProductCore
