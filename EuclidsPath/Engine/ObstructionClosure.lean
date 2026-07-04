/-
  ObstructionClosure — an abstract well-founded perpetual engine on positive obstruction certificates.
  Source: step00_obstruction_closure_badcert_engine_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section «Obstruction engine»).

  IDEA (and its boundary). Earlier workarounds (BadCoverDescent, SmallCleanSupply) turned out to be
  circular, because `Bad := ¬Good` carries no positive structure. This brick proposes to seek the
  engine in a POSITIVE obstruction certificate: `Bad m ⟹ ∃ obs, ObsAt obs m`, and
  `ObsAt obs m ⟹ Close ∨ smaller obs`. Then well-founded induction on `rank obs` gives
  `Bad m ⟹ Close`.

  PROVED HERE (pure mechanics, standard axioms, no sorry, NO prime-number arithmetic):
    * `obs_closes` — well-founded reduction ⟹ Close (core §5.1);
    * `mem_bad_closes_of_obstruction_reduction` — bad→obs + reduction ⟹ bad→Close (§5.2);
    * `exists_close_of_nonempty_carrier_and_bad_engine` — full abstract assembly (§6);
    * `goal_of_exists_close`, `goal_all_of_exists_close_all` — discharging the engine branch under `¬Engine` (§7).

  MAIN AUDIT TEST OF THE BRICK (§13) — VERIFIED EMPIRICALLY, RESULT NEGATIVE:
  the codebase has NO `def bad`/`def good`/`def carrier`/`Obs`/`LocalObstruction`. The real node
  `SNOL.SNOLInput` (`Engine/SNOL.lean:69`) uses `bad, carrier : Finset ℕ` as EXISTENTIALLY-
  quantified abstract sets with the SINGLE substantive condition `bad.card <
  carrier.card` (counting), and `twin_center_of_block` pulls a survivor from `survivor_of_not_covered` —
  pure counting. That is, `SNOL.bad` is NOT a positive obstruction object, but a counting object.

  CONCLUSION (by the no-go criterion §16 of the brick itself): there is NO positive
  obstruction semantics for `SNOL.bad`, so U1 (`mem_bad_to_obstruction`) and U2
  (`obstruction_reduce`) are non-instantiable without the goal/counting, and this engine
  DOES NOT START on the real node. The abstract module is correct and reusable, but its
  inputs do not bind to `SNOL.SNOLInput`. Audit verdict:
  `SNOL.SNOLInput` is a genuine density/counting/parity wall. `Step00` remains `sorry`.

  IMPORTANT (so that no one takes «positive obstruction» as a loophole): even IF one
  constructs an obstruction for `6m±1` (already partially built: `ObsAt` = old-peel/active
  edge with a large prime divisor, `rank` = height-centre). The U2 reduction steps are
  provable NON-circularly (`cofactor_is_center`, `old_peel_height_drop`,
  `active_descent_height` — real descent algebra; a catch is a step, not a wall). BUT at
  the RANK-0 terminal (clean centre with PRIME sides) BOTH branches of `regeneration_dichotomy`
  (composite side / old-peel) vanish, leaving exactly «this is a twin» — i.e. the U2 terminal
  «Close ∨ smaller obs» reduces to «Close ∨ nothing» = THE GOAL. The same circularity
  signature, machine-recorded in `BadCoverDescent.descent_reduction_is_circular` and
  `ConcreteComponents.smallCleanSupply_iff_goal` (both: input ⟺ goal). The engine adds a
  real descent lemma and a more precise wall localisation, but CLOSES NOTHING.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ObstructionClosure

/-! ### §5.1. Core: well-founded reduction of an obstruction ⟹ Close -/

/--
  **`obs_closes` — PROVED.** If every obstruction either immediately closes `Close`, or reduces to
  an obstruction of strictly smaller rank, then every obstruction closes `Close`. Well-founded induction
  on `rank : Obs → ℕ` (via `InvImage.wf Nat.lt_wfRel.wf`). -/
theorem obs_closes {Obs Point : Type*}
    (rank : Obs → ℕ) (ObsAt : Obs → Point → Prop) (Close : Prop)
    (hReduce : ∀ {x : Point} {obs : Obs}, ObsAt obs x →
      Close ∨ ∃ x' obs', ObsAt obs' x' ∧ rank obs' < rank obs) :
    ∀ {x : Point} {obs : Obs}, ObsAt obs x → Close := by
  intro x obs hobs
  have hWF : WellFounded (fun a b : Obs => rank a < rank b) :=
    InvImage.wf rank Nat.lt_wfRel.wf
  exact hWF.induction obs
    (C := fun obs => ∀ x, ObsAt obs x → Close)
    (fun obs IH x hobs => by
      rcases hReduce hobs with hClose | ⟨x', obs', hobs', hlt⟩
      · exact hClose
      · exact IH obs' hlt x' hobs')
    x hobs

/-! ### §5.2. Membership-in-bad yields an obstruction ⟹ bad closes -/

/--
  **`mem_bad_closes_of_obstruction_reduction` — PROVED.** If `Bad x` yields a positive obstruction
  witness (`hBadToObs`), and the reduction is well-founded (`hReduce`), then every bad point closes
  `Close`. This is `obs_closes` applied to the extracted witness.

  KEY INPUT `hBadToObs` — this is where all the substance lives: it requires a POSITIVE
  obstruction structure for `Bad`. For `SNOL.bad` (a counting object) such structure does NOT exist. -/
theorem mem_bad_closes_of_obstruction_reduction {Obs Point : Type*}
    (Bad : Point → Prop) (rank : Obs → ℕ) (ObsAt : Obs → Point → Prop) (Close : Prop)
    (hBadToObs : ∀ {x : Point}, Bad x → ∃ obs : Obs, ObsAt obs x)
    (hReduce : ∀ {x : Point} {obs : Obs}, ObsAt obs x →
      Close ∨ ∃ x' obs', ObsAt obs' x' ∧ rank obs' < rank obs) :
    ∀ {x : Point}, Bad x → Close := by
  intro x hx
  obtain ⟨obs, hobs⟩ := hBadToObs hx
  exact obs_closes rank ObsAt Close hReduce hobs

/-! ### §6. Abstract assembly: carrier / good / bad -/

/--
  **`exists_close_of_nonempty_carrier_and_bad_engine` — PROVED (abstract assembly §6).** If the
  carrier is nonempty, every carrier-point is good or bad, good closes, and bad closes via the
  obstruction engine, then for every `N` there exists `A` with `CloseAt A N`. Pure logic + `obs_closes`. -/
theorem exists_close_of_nonempty_carrier_and_bad_engine
    {Obs : ℕ → ℕ → Type*}
    (Carrier : ℕ → ℕ → ℕ → Prop) (Good : ℕ → ℕ → ℕ → Prop) (Bad : ℕ → ℕ → ℕ → Prop)
    (CloseAt : ℕ → ℕ → Prop)
    (rank : ∀ {A N : ℕ}, Obs A N → ℕ) (ObsAt : ∀ {A N : ℕ}, Obs A N → ℕ → Prop)
    (hCarrierNonempty : ∀ N, ∃ A m, Carrier A N m)
    (hGoodOrBad : ∀ {A N m}, Carrier A N m → Good A N m ∨ Bad A N m)
    (hGoodCloses : ∀ {A N m}, Carrier A N m → Good A N m → CloseAt A N)
    (hBadToObs : ∀ {A N m}, Bad A N m → ∃ obs : Obs A N, ObsAt obs m)
    (hReduce : ∀ {A N m} {obs : Obs A N}, ObsAt obs m →
      CloseAt A N ∨ ∃ (m' : ℕ) (obs' : Obs A N), ObsAt obs' m' ∧ rank obs' < rank obs) :
    ∀ N, ∃ A, CloseAt A N := by
  intro N
  obtain ⟨A, m, hm⟩ := hCarrierNonempty N
  refine ⟨A, ?_⟩
  rcases hGoodOrBad hm with hGood | hBad
  · exact hGoodCloses hm hGood
  · exact mem_bad_closes_of_obstruction_reduction
      (Bad := fun x => Bad A N x) (rank := @rank A N) (ObsAt := @ObsAt A N)
      (Close := CloseAt A N)
      (fun {x} hx => hBadToObs hx) (fun {x obs} hobs => hReduce hobs) hBad

/-! ### §7. Discharging the engine branch under `¬Engine` -/

/--
  **`goal_of_exists_close` — PROVED.** With `CloseAt := Engine ∨ (∃ t>N, Twin t)` and `¬Engine`,
  `∃ A, CloseAt A N` gives `∃ t>N, Twin t`. Pure logic (disjunction case analysis). -/
theorem goal_of_exists_close {Engine : ℕ → Prop} {Twin : ℕ → Prop} {N : ℕ}
    (hNoEngine : ∀ A, ¬ Engine A)
    (hClose : ∃ A, Engine A ∨ ∃ t, N < t ∧ Twin t) :
    ∃ t, N < t ∧ Twin t := by
  obtain ⟨A, hE | hT⟩ := hClose
  · exact absurd hE (hNoEngine A)
  · exact hT

/-- **`goal_all_of_exists_close_all` — PROVED.** Version for all `N`. -/
theorem goal_all_of_exists_close_all {Engine : ℕ → Prop} {Twin : ℕ → Prop}
    (hNoEngine : ∀ A, ¬ Engine A)
    (hCloseAll : ∀ N, ∃ A, Engine A ∨ ∃ t, N < t ∧ Twin t) :
    ∀ N, ∃ t, N < t ∧ Twin t :=
  fun N => goal_of_exists_close hNoEngine (hCloseAll N)

end EuclidsPath.ObstructionClosure
