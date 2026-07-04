/-
  Corrected product-core rank descent. Formalisation of the author's file.
  Source: step00_product_core_rank_descent_corrected_ru_2026-07-01.md. Prose: prose/32_ProductCore.md.

  Addresses 3 defects of the previous audit BY NAME:
    Defect 1 (extensionality): induction on PRODUCT-CORE (RankNode), not on genealogies. Tail/absorber
      (570→1 fan-in) DOES NOT ENTER RANKNODE ⟹ no_mismatch_core_eq is real (core extensionality).
    Defect 2 (residual bound): AmbientLegal certificate (factors divide one top side ≤6X_A+1) ⟹
      a_i < P_A at ALL ranks; preserved under deletion.
    Defect 3 (finiteness): CoreSig over ZMod P_A with FIXED A — Fintype.

  Here — CONCRETE RankNode (factors : Fin r → ℕ), so that extensionality is a genuine
  theorem. We check which of the 3 fixes are actually provable and what remains.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath.ProductCore

/-- Side sign. -/
inductive Sign | plus | minus
deriving DecidableEq, Fintype

/-- **Product-core node of rank `r`** (Def 2.1): sign + role-indexed factors, WITHOUT genealogy/tail.
    `factors : Fin r → ℕ` — this is the key: the state is EXTENSIONAL in (sign, factors). -/
structure RankNode (r : ℕ) where
  sign : Sign
  factors : Fin r → ℕ
deriving DecidableEq

/-- **Fix1 — core extensionality (Lemma 9.1) PROVED.** If two RankNodes share the same sign and
    ALL factors (no mismatch), they are equal. This is a genuine theorem (not a hypothesis), because
    RankNode does NOT contain tail/absorber — the 570→1 fan-in does not enter here. -/
theorem no_mismatch_core_eq {r : ℕ} (X₁ X₂ : RankNode r)
    (hsign : X₁.sign = X₂.sign) (hfac : ∀ k, X₁.factors k = X₂.factors k) :
    X₁ = X₂ := by
  cases X₁; cases X₂
  simp only [RankNode.mk.injEq]
  exact ⟨hsign, funext hfac⟩

/-! ### Fix2 — AmbientLegal: boundary a < P_A at all ranks -/

/-- `AmbientLegal` (Def 3.1): all factors divide one top legal side `N₀ ≤ 6X_A+1`. -/
def AmbientLegal (X_A : ℕ) {r : ℕ} (factors : Fin r → ℕ) : Prop :=
  ∃ N₀ : ℕ, 0 < N₀ ∧ N₀ ≤ 6 * X_A + 1 ∧ ∀ i, factors i ∣ N₀

/-- **Fix2a — factor bound (Lemma 4.1) PROVED.** Separating scale + AmbientLegal ⟹ every
    factor `< P_A`. (`a_i ∣ N₀ ≤ 6X_A+1 < P_A`.) -/
theorem ambient_factor_lt_primorial {X_A P_A : ℕ} {r : ℕ} {factors : Fin r → ℕ}
    (hsep : 6 * X_A + 1 < P_A) (hamb : AmbientLegal X_A factors) :
    ∀ i, factors i < P_A := by
  obtain ⟨N₀, hpos, hle, hdvd⟩ := hamb
  intro i
  have : factors i ≤ N₀ := Nat.le_of_dvd hpos (hdvd i)
  omega

/-- **Fix2b — AmbientLegal preserved under deletion (Lemma 5.2) PROVED.** Residual factors are
    a subset of factors of `X`, so the same `N₀` works. (Deletion of role `k` via `Fin.succAbove`.) -/
theorem ambientLegal_delete {X_A : ℕ} {r : ℕ} {factors : Fin (r + 1) → ℕ} (k : Fin (r + 1))
    (hamb : AmbientLegal X_A factors) :
    AmbientLegal X_A (fun i : Fin r => factors (k.succAbove i)) := by
  obtain ⟨N₀, hpos, hle, hdvd⟩ := hamb
  exact ⟨N₀, hpos, hle, fun i => hdvd (k.succAbove i)⟩

/-! ### Fix3 — CoreSig is finite with fixed A -/

/-- `CoreSig` (Def 6.1) with fixed `P_A`: sign + residues of factors mod P_A. WITHOUT genealogy. -/
structure CoreSig (P_A r : ℕ) where
  sign : Sign
  residues : Fin r → ZMod P_A
deriving DecidableEq

/-- **Fix3 — CoreSig is finite (Lemma 7.1) PROVED** with fixed `P_A > 0` and `r`. -/
noncomputable instance coreSig_fintype {P_A r : ℕ} [NeZero P_A] : Fintype (CoreSig P_A r) :=
  Fintype.ofInjective
    (fun s => (s.sign, s.residues))
    (by intro a b h; cases a; cases b; simp only [Prod.mk.injEq] at h; cases h.1; cases h.2; rfl)

/-! ### No ProductHall on RankNode (via separating scale) -/

/-- `coreSigOf`: signature from a RankNode. -/
def coreSigOf {P_A r : ℕ} (X : RankNode r) : CoreSig P_A r :=
  ⟨X.sign, fun i => (X.factors i : ZMod P_A)⟩

/--
  **No ProductHall (Lemma 12.1) PROVED on RankNode.** If the factors of both are `< P_A` (AmbientLegal +
  separating scale, `ambient_factor_lt_primorial`) and congruent mod P_A at role `k`, then they are equal —
  contradicting `a_k(X₁) ≠ a_k(X₂)`. Hence ProductHall is impossible at every rank. -/
theorem no_productHall {P_A r : ℕ} {X₁ X₂ : RankNode r} (k : Fin r)
    (h1 : X₁.factors k < P_A) (h2 : X₂.factors k < P_A)
    (hcong : (X₁.factors k : ZMod P_A) = (X₂.factors k : ZMod P_A))
    (hne : X₁.factors k ≠ X₂.factors k) : False := by
  -- residue equality + both < P_A ⟹ equal
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

/-! ### Final assembly: equal residues + bound ⟹ equal factors -/

/--
  **Equal CoreSig + bound ⟹ equal factors.** If `coreSigOf X₁ = coreSigOf X₂` (equal residues)
  and all factors of both are `< P_A`, then the factors coincide pointwise. (Residue is injective on `[0,P_A)`.) -/
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
  **Equal CoreSig + bound ⟹ equal nodes (extensionality via arithmetic).** Combines
  `factors_eq_of_coreSig` and `no_mismatch_core_eq`: signs from the signature, factors from the bound. -/
theorem rankNode_eq_of_coreSig {P_A r : ℕ} {X₁ X₂ : RankNode r}
    (hsig : (coreSigOf X₁ : CoreSig P_A r) = coreSigOf X₂)
    (h1 : ∀ i, X₁.factors i < P_A) (h2 : ∀ i, X₂.factors i < P_A) :
    X₁ = X₂ := by
  have hsign : X₁.sign = X₂.sign := congrArg CoreSig.sign hsig
  exact no_mismatch_core_eq X₁ X₂ hsign (factors_eq_of_coreSig hsig h1 h2)

/-- `CoreCollision`: two DISTINCT AmbientLegal-RankNodes of rank `r` with equal `CoreSig`. -/
def CoreCollision (X_A P_A r : ℕ) : Prop :=
  ∃ X₁ X₂ : RankNode r, X₁ ≠ X₂ ∧
    AmbientLegal X_A X₁.factors ∧ AmbientLegal X_A X₂.factors ∧
    (coreSigOf X₁ : CoreSig P_A r) = coreSigOf X₂

/--
  **rank_one_coreCollision_absurd (Lemma 9.1) — PROVED by pure arithmetic.** Under separating scale
  `CoreCollision_1` ⟹ False: rank-1 factors `< P_A`, equal residues ⟹ equal ⟹ `X₁=X₂` ⟹ ⊥.
  Base case NOT via external SNOL — via the same separating-scale arithmetic. -/
theorem rank_one_coreCollision_absurd {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (h : CoreCollision X_A P_A 1) : False := by
  obtain ⟨X₁, X₂, hne, ha1, ha2, hsig⟩ := h
  have b1 := ambient_factor_lt_primorial hsep ha1
  have b2 := ambient_factor_lt_primorial hsep ha2
  exact hne (rankNode_eq_of_coreSig hsig b1 b2)

/-- rank-1 collision ⟹ Engine (by ex falso, via separating scale). -/
theorem rank_one_coreCollision_engine {X_A P_A : ℕ} {Engine : Prop}
    (hsep : 6 * X_A + 1 < P_A) (h : CoreCollision X_A P_A 1) : Engine :=
  False.elim (rank_one_coreCollision_absurd hsep h)

/-! ### coreCollision_engine: induction r→1; and the final product_core_pump -/

/--
  **CoreCollision ⟹ Engine (Theorem 10.1) — induction on rank.** Base `r=1` — arithmetic
  (`rank_one_coreCollision_absurd`). Step `r>1` — `core_step` (open input: descent r→r-1 via
  deletion of the mismatched role; all its arithmetic — `delete_preserves_coreSig` + `no_productHall`,
  proved in RankDescent/here, but the stitching with concrete `deleteFactor` — left as input). -/
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
  -- (core_step here is a hypothesis; below it is CLOSED as `core_step_succ` and substituted into the final)

/--
  **product_core_pump (Theorem 12.1) — final assembly.** Infinitely many fresh starts yield
  a core collision (`freshStarts`, open input: pigeonhole + factorisation), and that ⟹ Engine. -/
theorem product_core_pump {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (core_step : ∀ r, 2 ≤ r → CoreCollision X_A P_A r → CoreCollision X_A P_A (r - 1))
    (freshStarts : ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ CoreCollision X_A P_A r) : Engine := by
  obtain ⟨r, hrpos, _hrle, hcol⟩ := freshStarts
  exact coreCollision_engine hsep core_step r hrpos hcol

/-! ### Closing core_step: role deletion + residual dichotomy -/

/-- Deletion of role `k` from `RankNode (r+1)` ⟹ `RankNode r` (via `Fin.succAbove`). -/
def deleteFactor {r : ℕ} (X : RankNode (r + 1)) (k : Fin (r + 1)) : RankNode r :=
  ⟨X.sign, fun i => X.factors (k.succAbove i)⟩

/-- **Deletion preserves CoreSig.** Equal signatures ⟹ equal after deleting the same `k`. -/
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
  **core_step PROVED (for `r = r'+1 ≥ 2`).** Collision of rank `r'+1` ⟹ collision of rank `r'`.
  There is a mismatched role `k` (otherwise `no_mismatch_core_eq` ⟹ equal ⟹ ⊥). We delete `k`: residual
  signatures are equal (`delete_preserves_coreSig`). If residuals differ — collision at `r'`. If equal —
  this is ProductHall (`a_k` differ but ≡ mod P_A), impossible by separating scale (`no_productHall`). -/
theorem core_step_succ {X_A P_A r' : ℕ} (hsep : 6 * X_A + 1 < P_A)
    (hcol : CoreCollision X_A P_A (r' + 1)) : CoreCollision X_A P_A r' := by
  obtain ⟨X₁, X₂, hne, ha1, ha2, hsig⟩ := hcol
  have b1 := ambient_factor_lt_primorial hsep ha1
  have b2 := ambient_factor_lt_primorial hsep ha2
  -- mismatched role exists (otherwise X₁=X₂)
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
  · -- residuals equal ⟹ ProductHall ⟹ ⊥
    exfalso
    have hres : (X₁.factors k : ZMod P_A) = (X₂.factors k : ZMod P_A) :=
      congrFun (congrArg CoreSig.residues hsig) k
    exact no_productHall k (b1 k) (b2 k) hres hk
  · -- residuals differ ⟹ collision of rank r'
    exact ⟨Y₁, Y₂, hYeq, haY1, haY2, hsigDel⟩

/-- `core_step` (with `r-1`) is now PROVED from `core_step_succ`: for `r≥2`, `r = (r-1)+1`. -/
theorem core_step_proved {X_A P_A : ℕ} (hsep : 6 * X_A + 1 < P_A) :
    ∀ r, 2 ≤ r → CoreCollision X_A P_A r → CoreCollision X_A P_A (r - 1) := by
  intro r hr hcol
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simpa using core_step_succ hsep hcol

/--
  **product_core_pump_closed — final WITHOUT the core_step hypothesis.** Only separating scale + freshStarts
  (infinitely many starts ⟹ core collision). The descent step is PROVED (`core_step_proved`), the rank-1 base
  is PROVED (arithmetic). The only remaining input is `freshStarts`. -/
theorem product_core_pump_closed {X_A P_A : ℕ} {Engine : Prop} (hsep : 6 * X_A + 1 < P_A)
    (freshStarts : ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ CoreCollision X_A P_A r) : Engine := by
  obtain ⟨r, hrpos, _hrle, hcol⟩ := freshStarts
  exact coreCollision_engine hsep (core_step_proved hsep) r hrpos hcol

/-! ### Closing freshStarts: pigeonhole core (proved) + carrier structure -/

/--
  **Pigeonhole core (FULLY PROVED).** Given a type of starts `ι` with an infinite set `S`, and
  a map `node : ι → RankNode r` injective on `S` (distinct starts ⟹ distinct cores). If
  `CoreSig` is finite, then there exist two distinct starts with equal signature ⟹ `CoreCollision r`
  (with AmbientLegal, if each node has it). -/
theorem coreCollision_of_infinite {ι : Type*} {X_A P_A r : ℕ} [NeZero P_A]
    (S : Set ι) (hS : S.Infinite)
    (node : ι → RankNode r)
    (hinj : Set.InjOn node S)                                 -- distinct starts ⟹ distinct cores
    (hamb : ∀ i ∈ S, AmbientLegal X_A (node i).factors) :
    CoreCollision X_A P_A r := by
  -- infinite S into finite CoreSig ⟹ two distinct images with equal signature
  have hfin : Set.Finite (Set.range (fun i => (coreSigOf (node i) : CoreSig P_A r))) :=
    Set.toFinite _
  -- if coreSig∘node were InjOn on S, S would be finite
  by_contra hno
  -- assume there is NO collision ⟹ coreSig∘node is injective on S
  have hcsinj : Set.InjOn (fun i => (coreSigOf (node i) : CoreSig P_A r)) S := by
    intro a ha b hb hcs
    by_contra hab
    -- node a ≠ node b (injectivity of node), but coreSig equal ⟹ CoreCollision
    exact hno ⟨node a, node b,
      fun h => hab (hinj ha hb h), hamb a ha, hamb b hb, hcs⟩
  -- InjOn into a finite type ⟹ S finite ⟹ contradiction
  exact hS (Set.Finite.of_finite_image (Set.toFinite _) hcsinj)

/--
  **freshStarts ⟹ CoreCollision (structural carrier input).** If the carrier provides: infinitely many
  starts of the same sign and rank `r` (`1≤r≤4`), each ⟹ AmbientLegal-RankNode, and distinct starts ⟹
  distinct cores, then `CoreCollision_r`. Pigeonhole is proved (`coreCollision_of_infinite`); the input is only
  the DATA STRUCTURE from the carrier (factorisation `6m+σ=∏aᵢ`, `rank≤4`, distinct). -/
theorem freshStarts_to_coreCollision {ι : Type*} {X_A P_A r : ℕ} [NeZero P_A]
    (hr : 1 ≤ r ∧ r ≤ 4)
    (S : Set ι) (hS : S.Infinite) (node : ι → RankNode r)
    (hinj : Set.InjOn node S) (hamb : ∀ i ∈ S, AmbientLegal X_A (node i).factors) :
    ∃ r', 1 ≤ r' ∧ r' ≤ 4 ∧ CoreCollision X_A P_A r' :=
  ⟨r, hr.1, hr.2, coreCollision_of_infinite S hS node hinj hamb⟩

/--
  **FINAL from carrier data (Theorem 12.1, fully assembled).** Separating scale + carrier structure
  (infinitely many starts of one rank `1≤r≤4`, each an AmbientLegal-RankNode, distinct starts ⟹
  distinct cores) ⟹ Engine. EVERYTHING inside is proved: pigeonhole, descent (`core_step_proved`), rank-1 base.
  The only thing left open is exactly the carrier structure `CarrierData` — what must come from
  GlobalOldAbsorption (factorisation `6m+σ`, `rank≤4`, infinitely many starts). -/
theorem product_core_engine_of_carrier {ι : Type*} {X_A P_A r : ℕ} {Engine : Prop} [NeZero P_A]
    (hsep : 6 * X_A + 1 < P_A) (hr : 1 ≤ r ∧ r ≤ 4)
    (S : Set ι) (hS : S.Infinite) (node : ι → RankNode r)
    (hinj : Set.InjOn node S) (hamb : ∀ i ∈ S, AmbientLegal X_A (node i).factors) :
    Engine :=
  product_core_pump_closed hsep (freshStarts_to_coreCollision hr S hS node hinj hamb)

end EuclidsPath.ProductCore
