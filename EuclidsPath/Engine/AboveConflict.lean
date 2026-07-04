/-
  AboveConflict — the contradiction lies in the word "Above" (an order conflict), not in "Twin" (the tail).
  Source: above_structure_order_conflict_formal_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "Above-order conflict").

  IDEA. Look for the contradiction not in the tail `NoTwinAbove(max T)`, but in an ORDER CONFLICT: the
  engine order is `T₁ <_eng T₂ <_eng T₃`, yet the natural order of centers is
  `center T₁ < center T₃ < center T₂` ("Twin #3 ended up between Twin #1 and Twin #2").
  If these are genuine interior twins and the engine order is independent — this is a non-tail contradiction.

  PROVED HERE (pure order logic, std axioms, no sorry):
    * `no_above_conflict` — a sound above-order cannot yield a conflict (§7);
    * `no_order_crossing` (§8), `contradiction_of_twin_order_conflict` (§9);
    * `twinGap_not_pierced`, `contradiction_of_gap_piercing` (§3);
    * `no_twin_between_consecutive` (§2), `no_third_between_first_second` (§5 order);
    * `contradiction_of_finiteTwinOrderAttack` (§10).

  HONEST BOUNDARY (§14, §17, §19 of the brick — exposed and MACHINE-VERIFIED). All theorems above are
  TRIVIAL order logic (consequences of `above_sound`). The only substantive input is
  `step00_forces_above_conflict` (finite twins ⟹ conflict), and it is TRAPPED:
    * if `Step00Above := center X < center Y` (definitional), the conflict CANNOT BE CONSTRUCTED
      (`definitional_above_conflict_impossible` — machine-verified), the route is dead;
    * if `above` is an independent sound order, `no_above_conflict` still forbids the conflict;
    hence `step00_forces_above_conflict` demands constructing a conflict that does not exist under any
    sound order — meaning it is either false, or its "conflict" actually exhibits a new twin between two
    existing ones (= `TwinAbove` of the interior gap = the goal). The brick acknowledges this itself (§17).
    This input is NOT supplied here. `Step00` remains `sorry`.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.AboveConflict

open EuclidsPath.Residuals

/-! ### §6–8. AboveStructure and order conflict (pure logic) -/

/-- Abstract above-structure: objects with a center, an `above` order that is monotone on centers and transitive. -/
structure AboveStructure where
  Obj : Type
  center : Obj → ℕ
  above : Obj → Obj → Prop
  above_sound : ∀ X Y, above X Y → center X < center Y
  trans : ∀ X Y Z, above X Y → above Y Z → above X Z

/--
  **`no_above_conflict` — PROVED (core of the order contradiction §7).** There cannot exist `above X Y`,
  `above Y Z` with `center X < center Z < center Y`: from `above Y Z` it follows that `center Y < center Z`,
  contradicting `center Z < center Y`. Pure order logic — but all the force lies in `above_sound`. -/
theorem no_above_conflict (S : AboveStructure) (X Y Z : S.Obj)
    (hXY : S.above X Y) (hYZ : S.above Y Z)
    (hbetween : S.center X < S.center Z ∧ S.center Z < S.center Y) : False := by
  have := S.above_sound Y Z hYZ
  omega

/-- **`no_order_crossing` — PROVED (§8).** Same result for an explicit two-order crossing. -/
theorem no_order_crossing (S : AboveStructure) (X Y Z : S.Obj)
    (hXY : S.above X Y) (hYZ : S.above Y Z)
    (hnatXZ : S.center X < S.center Z) (hnatZY : S.center Z < S.center Y) : False := by
  have := S.above_sound Y Z hYZ
  omega

/-! ### §2–3. TwinGap: the interval between consecutive twins -/

/-- Gap between two twin centers with no twin inside. -/
structure TwinGap where
  left : ℕ
  right : ℕ
  hLeftTwin : TwinCenterZ left
  hRightTwin : TwinCenterZ right
  hlt : left < right
  noTwinBetween : ∀ m, left < m → m < right → ¬ TwinCenterZ m

/-- **`twinGap_not_pierced` — PROVED (§3).** The gap cannot be pierced by a twin inside it. -/
theorem twinGap_not_pierced (G : TwinGap) :
    ¬ ∃ m, G.left < m ∧ m < G.right ∧ TwinCenterZ m := by
  rintro ⟨m, hlm, hmr, hT⟩
  exact G.noTwinBetween m hlm hmr hT

/-- **`contradiction_of_gap_piercing` — PROVED (§3).** Piercing the gap ⟹ False. -/
theorem contradiction_of_gap_piercing (G : TwinGap)
    (hPierce : ∃ m, G.left < m ∧ m < G.right ∧ TwinCenterZ m) : False :=
  twinGap_not_pierced G hPierce

/-- **`no_twin_between_consecutive` — PROVED (§2).** Consecutive twins have no twin between them. -/
theorem no_twin_between_consecutive {a b : ℕ}
    (haTwin : TwinCenterZ a) (hbTwin : TwinCenterZ b) (hab : a < b)
    (hNoBetween : ∀ c, a < c → c < b → ¬ TwinCenterZ c) :
    ¬ ∃ c, a < c ∧ c < b ∧ TwinCenterZ c := by
  rintro ⟨c, hac, hcb, hT⟩
  exact hNoBetween c hac hcb hT

/-! ### §9. TwinOrderConflict — specialisation to twin blocks -/

/-- Twin block (center). -/
structure TwinBlock where
  center : ℕ

/-- `IsTwin` of a block = twin center. -/
def TwinBlock.IsTwin (B : TwinBlock) : Prop := TwinCenterZ B.center

/-- Order conflict of three twins: engine order `T₁→T₂→T₃`, but `center T₁ < center T₃ < center T₂`. -/
structure TwinOrderConflict where
  T1 : TwinBlock
  T2 : TwinBlock
  T3 : TwinBlock
  hTwin1 : T1.IsTwin
  hTwin2 : T2.IsTwin
  hTwin3 : T3.IsTwin
  EngineBefore : TwinBlock → TwinBlock → Prop
  engine_before_12 : EngineBefore T1 T2
  engine_before_23 : EngineBefore T2 T3
  engine_before_sound : ∀ X Y, EngineBefore X Y → X.center < Y.center
  natural_between : T1.center < T3.center ∧ T3.center < T2.center

/--
  **`contradiction_of_twin_order_conflict` — PROVED (§9).** "Twin #3 between Twin #1 and Twin #2"
  is impossible: from `EngineBefore T2 T3` it follows that `center T2 < center T3`, contradicting
  `center T3 < center T2`. -/
theorem contradiction_of_twin_order_conflict (C : TwinOrderConflict) : False := by
  have := C.engine_before_sound C.T2 C.T3 C.engine_before_23
  have := C.natural_between.2
  omega

/-! ### §5. Nth-twin order (example; monotonicity of the rank itself is a separate fact) -/

/-- **`no_third_between_of_order` — PROVED (§5, pure order).** If the nth-twin is monotone
    (`b < c` from ranks), then `c < b` is impossible. Rank monotonicity itself is an input; it is not needed here. -/
theorem no_third_between_of_order {b c : ℕ} (hbc : b < c) (hcb : c < b) : False := by omega

/-! ### §10. FiniteTwinOrderAttack -/

/-- Attack: complete list of twins + interior gap + its piercing. -/
structure FiniteTwinOrderAttack where
  T : Finset ℕ
  complete : ∀ m, TwinCenterZ m → m ∈ T
  gap : TwinGap
  pierce : ∃ m, gap.left < m ∧ m < gap.right ∧ TwinCenterZ m

/-- **`contradiction_of_finiteTwinOrderAttack` — PROVED (§10).** -/
theorem contradiction_of_finiteTwinOrderAttack (A : FiniteTwinOrderAttack) : False :=
  twinGap_not_pierced A.gap A.pierce

/-! ### §14, §17. MACHINE DIAGNOSIS OF THE TRAP: why this is not a new route on its own

All theorems above are trivial (consequences of `above_sound`). The only substantive input is
`step00_forces_above_conflict`. We show machine-formally that it is trapped. -/

/--
  **`definitional_above_conflict_impossible` — PROVED (trap diagnosis §14).** If the above-order is
  DEFINED as `center X < center Y` (definitional), then `AboveConflict` CANNOT BE CONSTRUCTED: `above X Y`,
  `above Y Z` yield `center X < center Y < center Z`, and `center Z < center Y` is a contradiction. Hence,
  under definitional above the route is dead (the conflict does not exist). -/
theorem definitional_above_conflict_impossible (center : ℕ → ℕ) (X Y Z : ℕ)
    (hXY : center X < center Y) (hYZ : center Y < center Z)
    (hbetween : center X < center Z ∧ center Z < center Y) : False := by omega

/--
  **`above_conflict_route_is_trapped` — PROVED (conclusion of the diagnosis).** For ANY sound above-structure,
  `AboveConflict` is impossible (`no_above_conflict`). Hence `step00_forces_above_conflict` (finite twins
  ⟹ conflict) demands constructing a non-existent object — it is EITHER false, OR its "conflict" in fact
  exhibits a new twin inside the interval (= `TwinAbove` of the interior gap = the goal). In both cases
  this is NOT a bypass, but a reformulation. Formally: conflict ⟹ False, so the forcing input is
  equivalent to `¬finite` only through the already-established impossibility, not through a new resource. -/
theorem above_conflict_route_is_trapped (S : AboveStructure)
    (hConflict : ∃ X Y Z : S.Obj, S.above X Y ∧ S.above Y Z ∧
      S.center X < S.center Z ∧ S.center Z < S.center Y) : False := by
  obtain ⟨X, Y, Z, hXY, hYZ, h1, h2⟩ := hConflict
  exact no_above_conflict S X Y Z hXY hYZ ⟨h1, h2⟩

end EuclidsPath.AboveConflict
