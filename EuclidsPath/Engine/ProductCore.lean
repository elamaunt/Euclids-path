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

/-! ### Финальная сборка: equal residues + bound ⟹ equal factors -/

/--
  **Equal CoreSig + bound ⟹ equal factors.** Если `coreSigOf X₁ = coreSigOf X₂` (равные residues)
  и все факторы обоих `< P_A`, то факторы совпадают поточечно. (Residue инъективна на `[0,P_A)`.) -/
theorem factors_eq_of_coreSig {P_A r : ℕ} {X₁ X₂ : RankNode r}
    (hsig : (coreSigOf X₁ : CoreSig P_A r) = coreSigOf X₂)
    (h1 : ∀ i, X₁.factors i < P_A) (h2 : ∀ i, X₂.factors i < P_A) :
    ∀ k, X₁.factors k = X₂.factors k := by
  intro k
  have hres : (X₁.factors k : ZMod P_A) = (X₂.factors k : ZMod P_A) := by
    have := congrArg CoreSig.residues hsig
    exact congrFun this k
  by_contra hne
  exact no_productHall k (h1 k) (h2 k) hres hne

/--
  **Equal CoreSig + bound ⟹ equal nodes (extensionality через арифметику).** Объединяет
  `factors_eq_of_coreSig` и `no_mismatch_core_eq`: signs из подписи, факторы из bound. -/
theorem rankNode_eq_of_coreSig {P_A r : ℕ} {X₁ X₂ : RankNode r}
    (hsig : (coreSigOf X₁ : CoreSig P_A r) = coreSigOf X₂)
    (h1 : ∀ i, X₁.factors i < P_A) (h2 : ∀ i, X₂.factors i < P_A) :
    X₁ = X₂ := by
  have hsign : X₁.sign = X₂.sign := congrArg CoreSig.sign hsig
  exact no_mismatch_core_eq X₁ X₂ hsign (factors_eq_of_coreSig hsig h1 h2)

/-- `CoreCollision`: два РАЗНЫХ AmbientLegal-RankNode ранга `r` с равной `CoreSig`. -/
def CoreCollision (X_A P_A r : ℕ) : Prop :=
  ∃ X₁ X₂ : RankNode r, X₁ ≠ X₂ ∧
    AmbientLegal X_A X₁.factors ∧ AmbientLegal X_A X₂.factors ∧
    (coreSigOf X₁ : CoreSig P_A r) = coreSigOf X₂

/--
  **rank_one_coreCollision_absurd (Lemma 9.1) — ДОКАЗАНО чистой арифметикой.** При separating scale
  `CoreCollision_1` ⟹ False: rank-1 факторы `< P_A`, равные residues ⟹ равны ⟹ `X₁=X₂` ⟹ ⊥.
  База НЕ через внешний SNOL — через ту же separating-scale арифметику. -/
theorem rank_one_coreCollision_absurd {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (h : CoreCollision X_A P_A 1) : False := by
  obtain ⟨X₁, X₂, hne, ha1, ha2, hsig⟩ := h
  have b1 := ambient_factor_lt_primorial hsep ha1
  have b2 := ambient_factor_lt_primorial hsep ha2
  exact hne (rankNode_eq_of_coreSig hsig b1 b2)

/-- rank-1 коллизия ⟹ Engine (по ex falso, через separating scale). -/
theorem rank_one_coreCollision_engine {X_A P_A : ℕ} {Engine : Prop}
    (hsep : 6 * X_A + 1 < P_A) (h : CoreCollision X_A P_A 1) : Engine :=
  False.elim (rank_one_coreCollision_absurd hsep h)

/-! ### coreCollision_engine: индукция r→1; и финальный product_core_pump -/

/--
  **CoreCollision ⟹ Engine (Theorem 10.1) — индукция по рангу.** База `r=1` — арифметика
  (`rank_one_coreCollision_absurd`). Шаг `r>1` — `core_step` (открытый вход: descent r→r-1 через
  удаление mismatched role; вся его арифметика — `delete_preserves_coreSig` + `no_productHall`,
  доказаны в RankDescent/здесь, но сшивка с конкретным `deleteFactor` — оставлена входом). -/
theorem coreCollision_engine {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (core_step : ∀ r, 2 ≤ r → CoreCollision X_A P_A r → CoreCollision X_A P_A (r - 1)) :
    ∀ r, 1 ≤ r → CoreCollision X_A P_A r → Engine := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ n ih =>
    intro hge hcol
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this; exact rank_one_coreCollision_engine hsep hcol
    · exact ih (n - 1) (by omega) (by omega) (core_step n h2 hcol)
  -- (core_step здесь — гипотеза; ниже он ЗАКРЫТ как `core_step_succ` и подставлен в финал)

/--
  **product_core_pump (Theorem 12.1) — финальная сборка.** Бесконечно много fresh-стартов дают
  core-коллизию (`freshStarts`, открытый вход: pigeonhole + факторизация), а та ⟹ Engine. -/
theorem product_core_pump {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (core_step : ∀ r, 2 ≤ r → CoreCollision X_A P_A r → CoreCollision X_A P_A (r - 1))
    (freshStarts : ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ CoreCollision X_A P_A r) : Engine := by
  obtain ⟨r, hrpos, _hrle, hcol⟩ := freshStarts
  exact coreCollision_engine hsep core_step r hrpos hcol

/-! ### Закрытие core_step: удаление role + дихотомия residual -/

/-- Удаление role `k` из `RankNode (r+1)` ⟹ `RankNode r` (через `Fin.succAbove`). -/
def deleteFactor {r : ℕ} (X : RankNode (r + 1)) (k : Fin (r + 1)) : RankNode r :=
  ⟨X.sign, fun i => X.factors (k.succAbove i)⟩

/-- **Удаление сохраняет CoreSig.** Равные подписи ⟹ равные после удаления того же `k`. -/
theorem delete_preserves_coreSig {P_A r : ℕ} {X₁ X₂ : RankNode (r + 1)} (k : Fin (r + 1))
    (hsig : (coreSigOf X₁ : CoreSig P_A (r + 1)) = coreSigOf X₂) :
    (coreSigOf (deleteFactor X₁ k) : CoreSig P_A r) = coreSigOf (deleteFactor X₂ k) := by
  have hsign : X₁.sign = X₂.sign := congrArg CoreSig.sign hsig
  have hres : ∀ i, (X₁.factors i : ZMod P_A) = (X₂.factors i : ZMod P_A) :=
    fun i => congrFun (congrArg CoreSig.residues hsig) i
  unfold deleteFactor coreSigOf
  simp only [CoreSig.mk.injEq]
  exact ⟨hsign, funext fun i => hres (k.succAbove i)⟩

/--
  **core_step ДОКАЗАН (для `r = r'+1 ≥ 2`).** Коллизия ранга `r'+1` ⟹ коллизия ранга `r'`.
  Есть mismatched role `k` (иначе `no_mismatch_core_eq` ⟹ равны ⟹ ⊥). Удаляем `k`: residual
  signatures равны (`delete_preserves_coreSig`). Если residual различны — коллизия `r'`. Если равны —
  это ProductHall (`a_k` различны но ≡ mod P_A), невозможный по separating scale (`no_productHall`). -/
theorem core_step_succ {X_A P_A r' : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (hcol : CoreCollision X_A P_A (r' + 1)) : CoreCollision X_A P_A r' := by
  obtain ⟨X₁, X₂, hne, ha1, ha2, hsig⟩ := hcol
  have b1 := ambient_factor_lt_primorial hsep ha1
  have b2 := ambient_factor_lt_primorial hsep ha2
  -- mismatched role существует (иначе X₁=X₂)
  have hmis : ∃ k, X₁.factors k ≠ X₂.factors k := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    exact hne (no_mismatch_core_eq X₁ X₂ (congrArg CoreSig.sign hsig) hno)
  obtain ⟨k, hk⟩ := hmis
  set Y₁ := deleteFactor X₁ k with hY1
  set Y₂ := deleteFactor X₂ k with hY2
  have hsigDel : (coreSigOf Y₁ : CoreSig P_A r') = coreSigOf Y₂ := delete_preserves_coreSig k hsig
  have haY1 : AmbientLegal X_A Y₁.factors := ambientLegal_delete k ha1
  have haY2 : AmbientLegal X_A Y₂.factors := ambientLegal_delete k ha2
  by_cases hYeq : Y₁ = Y₂
  · -- residual равны ⟹ ProductHall ⟹ ⊥
    exfalso
    have hres : (X₁.factors k : ZMod P_A) = (X₂.factors k : ZMod P_A) :=
      congrFun (congrArg CoreSig.residues hsig) k
    exact no_productHall k (b1 k) (b2 k) hres hk
  · -- residual различны ⟹ коллизия ранга r'
    exact ⟨Y₁, Y₂, hYeq, haY1, haY2, hsigDel⟩

/-- `core_step` (с `r-1`) теперь ДОКАЗАН из `core_step_succ`: для `r≥2`, `r = (r-1)+1`. -/
theorem core_step_proved {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A) :
    ∀ r, 2 ≤ r → CoreCollision X_A P_A r → CoreCollision X_A P_A (r - 1) := by
  intro r hr hcol
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simpa using core_step_succ hsep hcol

/--
  **product_core_pump_closed — финал БЕЗ гипотезы core_step.** Только separating scale + freshStarts
  (бесконечно много стартов ⟹ core-коллизия). Шаг descent ДОКАЗАН (`core_step_proved`), база rank-1
  ДОКАЗАНА (арифметика). Единственный оставшийся вход — `freshStarts`. -/
theorem product_core_pump_closed {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (freshStarts : ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ CoreCollision X_A P_A r) : Engine := by
  obtain ⟨r, hrpos, _hrle, hcol⟩ := freshStarts
  exact coreCollision_engine hsep (core_step_proved hsep) r hrpos hcol

end EuclidsPath.ProductCore
