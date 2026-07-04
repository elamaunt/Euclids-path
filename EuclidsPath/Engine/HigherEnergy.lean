/-
  HigherEnergy — the higher energy incompatibility theorem on the Euclidean path.
  Source: higher_energy_incompatibility_full_formal_ru_2026-07-01.md.
  Prose: prose/24_BoundaryDecomp.md (section "Weighted debt energy").

  IDEA. Lexicographic energy of a node on the Euclidean path: `Energy(x) = (DebtEnergy(x), LocalFuel(x))`, where
  `DebtEnergy(D) = ∑_{a∈D} (B+1)^rank(a)` — the weighted debt. An internal move keeps the debt and drops
  LocalFuel; a promotion move drops DebtEnergy (replacing one focus-debt with lower-rank kids of smaller total
  weight). Both moves strictly decrease the lexicographic energy ⟹ an infinite path is impossible (well-founded).

  PROVED HERE (real mathematics, standard axioms, no sorry):
    * `lexNat_wf` — well-foundedness of the lex order on ℕ×ℕ;
    * `no_live_state_if_closes_or_moves_down` — well-founded prohibition of a perpetual engine;
    * `debtEnergy_decreases_of_weightedReplacement` — debt replacement ACTUALLY drops `DebtEnergy` (weight
      arithmetic, not abstract);
    * `kids_weight_lt_focus_of_rank_bound` — branch-bound (`kids.card ≤ B` + lower rank) ⟹ weight
      inequality;
    * `euclideanPathMove_decreases_energy` — every move drops the lex-energy;
    * `higher_energy_incompatibility_on_euclidean_path` — the main theorem (under NoEngine/NoNewTwin — ⊥);
    * `twin_above_of_higher_energy_engine` — positive form.

  HONEST BOUNDARY (confirmed by audit — the input is NOT instantiable; §22bis machine-checked). The abstract
  module is sound and reusable — it is the most substantive descent framework in the tree (theorems §8–9 — real
  weight arithmetic). But Step00 is NOT closed: the sole input `step00_promotion_is_weightedDebtReplacement`
  on the `6m±1` graph is **MIS-ORIENTED and not instantiable**:
    • ALL real-arithmetic dynamics goes DOWNWARD in height/centre (`active_descent_height` `n<m`,
      `old_peel_height_drop` `t<n`, `cofactor_is_center`, `RankDescent` `r→r−1`), whereas `PromotePass` requires
      `x.A < y.A` — UPWARD. The real engine has no forward move UPWARD;
    • raising the threshold `A→A'` GROWS the set of old primes (the primorial is monotone) ⟹ promotion ADDS
      debt atoms (refuel), rather than clearing the focus — and a weight-increasing move is NOT a replacement
      (machine-verified: `refuel_is_not_weightedReplacement`, §22bis; the type structurally forbids forging);
    • any `rank` under which an UPWARD move drops the weight already asserts that the descent ends in twins
      = the goal (the same signature as `smallCleanSupply_iff_goal` / `descent_reduction_is_circular`).
  Also `repeated_level_signature_closes` (repeated signature ⟹ Close) — this is a labelled-fan-in branch whose
  terminal previous audits found circular; and the LocalFuel boundary hides counting = `SNOL.SNOLInput`.
  Audit verdict: net = SAME WALL in energetic clothing. `Step00` remains `sorry`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.HigherEnergy

/-! ### §3–4. Lexicographic order on ℕ×ℕ and its well-foundedness -/

/-- Lex order: `(a',b') < (a,b)` if `a'<a` or (`a'=a` and `b'<b`). -/
def LexNat (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- **`lexNat_wf` — PROVED.** The lex order on ℕ×ℕ is well-founded (double strong induction). -/
theorem lexNat_wf : WellFounded LexNat := by
  refine ⟨?_⟩
  intro p
  rcases p with ⟨a, b⟩
  revert b
  refine Nat.strong_induction_on a ?_
  intro a IHa b
  refine Nat.strong_induction_on b ?_
  intro b IHb
  apply Acc.intro
  intro q hq
  rcases q with ⟨a', b'⟩
  rcases hq with hLeft | ⟨ha, hb⟩
  · exact IHa a' hLeft b'
  · simp only at ha hb
    subst ha
    exact IHb b' hb

/-! ### §5. General well-founded combinator: no live node -/

/--
  **`no_live_state_if_closes_or_moves_down` — PROVED.** If every live node either closes
  (`Close`) or makes a move to a live node of strictly smaller lex-energy, and closing is
  forbidden, then no live node exists. Well-founded induction on `LexNat ∘ EnergyPair`. Pure
  prohibition of a perpetual engine. -/
theorem no_live_state_if_closes_or_moves_down {Node : Type*}
    (Live : Node → Prop) (Close : Node → Prop) (Move : Node → Node → Prop)
    (EnergyPair : Node → ℕ × ℕ)
    (hStep : ∀ x, Live x → Close x ∨ ∃ y, Live y ∧ Move x y)
    (hNoClose : ∀ x, Live x → ¬ Close x)
    (hDrop : ∀ {x y}, Move x y → LexNat (EnergyPair y) (EnergyPair x)) :
    ¬ ∃ x, Live x := by
  have hWF : WellFounded (fun y x => LexNat (EnergyPair y) (EnergyPair x)) :=
    InvImage.wf EnergyPair lexNat_wf
  have hNoLive : ∀ x, ¬ Live x := by
    intro x
    refine hWF.induction (C := fun x => ¬ Live x) x ?_
    intro x IH hxLive
    rcases hStep x hxLive with hClose | ⟨y, hyLive, hxy⟩
    · exact (hNoClose x hxLive) hClose
    · exact IH y (hDrop hxy) hyLive
  rintro ⟨x, hx⟩
  exact hNoLive x hx

/-! ### §6. Weighted debt energy -/

variable {Atom : Type*} [DecidableEq Atom]

/-- Weight of a debt atom: `(B+1)^rank`. A higher rank weighs exponentially more than the sum of lower ones. -/
def AtomWeight (rank : Atom → ℕ) (B : ℕ) (a : Atom) : ℕ := (B + 1) ^ rank a

/-- Debt energy: the sum of atom weights. -/
def DebtEnergy (rank : Atom → ℕ) (B : ℕ) (D : Finset Atom) : ℕ :=
  ∑ a ∈ D, AtomWeight rank B a

/-! ### §7. Weighted debt replacement -/

/-- Replacement of one focus-debt by a set of kids: lower rank, smaller total weight, update
    `D' = (D.erase focus) ∪ kids`. Carries data (`focus`, `kids`), hence `Type`, not `Prop`. -/
structure WeightedDebtReplacement (rank : Atom → ℕ) (B : ℕ) (D D' : Finset Atom) where
  focus : Atom
  hfocus : focus ∈ D
  kids : Finset Atom
  kids_lower : ∀ k ∈ kids, rank k < rank focus
  kids_weight_lt_focus : (∑ k ∈ kids, AtomWeight rank B k) < AtomWeight rank B focus
  disjoint : Disjoint (D.erase focus) kids
  update : D' = (D.erase focus) ∪ kids

/-! ### §8. Debt replacement ACTUALLY decreases `DebtEnergy` -/

/--
  **`debtEnergy_decreases_of_weightedReplacement` — PROVED (real weight arithmetic).**
  `DebtEnergy(D') < DebtEnergy(D)`. We split `D = {focus} ⊔ (D.erase focus)`, `D' = (D.erase focus)
  ⊔ kids`; the common term `E(D.erase focus)` cancels, leaving `E(kids) < E(focus)`. -/
theorem debtEnergy_decreases_of_weightedReplacement (rank : Atom → ℕ) (B : ℕ)
    {D D' : Finset Atom} (hRep : WeightedDebtReplacement rank B D D') :
    DebtEnergy rank B D' < DebtEnergy rank B D := by
  -- decompose the structure into flat hypotheses so that D' does not sit in a dependent type
  obtain ⟨focus, hfocus, kids, _, hkw, hdisj, hupd⟩ := hRep
  unfold DebtEnergy
  have hnm : focus ∉ D.erase focus := Finset.notMem_erase focus D
  have hsumD : (∑ a ∈ D, AtomWeight rank B a)
      = AtomWeight rank B focus + ∑ a ∈ D.erase focus, AtomWeight rank B a := by
    conv_lhs => rw [← Finset.insert_erase hfocus]
    rw [Finset.sum_insert hnm]
  have hsumD' : (∑ a ∈ D', AtomWeight rank B a)
      = (∑ a ∈ D.erase focus, AtomWeight rank B a) + ∑ a ∈ kids, AtomWeight rank B a := by
    rw [hupd, Finset.sum_union hdisj]
  rw [hsumD, hsumD']
  omega

/-! ### §9. Branch-bound ⟹ weight-bound (technical, for instantiation) -/

/--
  **`kids_weight_lt_focus_of_rank_bound` — PROVED.** If `kids.card ≤ B` and all kid ranks are less than
  `rank focus`, then `∑ weight(kids) < weight(focus)`. When `rank focus = 0` the kids set is empty; at `r+1`
  each kid weighs `≤ (B+1)^r`, and `B·(B+1)^r < (B+1)^{r+1}`. -/
theorem kids_weight_lt_focus_of_rank_bound (rank : Atom → ℕ) (B : ℕ)
    (focus : Atom) (kids : Finset Atom)
    (hBpos : 0 < B) (hcard : kids.card ≤ B) (hlower : ∀ k ∈ kids, rank k < rank focus) :
    (∑ k ∈ kids, AtomWeight rank B k) < AtomWeight rank B focus := by
  rcases Nat.eq_zero_or_pos (rank focus) with h0 | hpos
  · have hempty : kids = ∅ := by
      by_contra hne
      obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty hne
      have := hlower k hk; omega
    simp [hempty, AtomWeight]
  · set r := rank focus - 1 with hr
    have hrf : rank focus = r + 1 := by omega
    have hbound : ∀ k ∈ kids, AtomWeight rank B k ≤ (B + 1) ^ r := by
      intro k hk
      have h2 : rank k ≤ r := by have := hlower k hk; omega
      exact Nat.pow_le_pow_right (by omega) h2
    have hpp : 0 < (B + 1) ^ r := pow_pos (by omega) r
    calc (∑ k ∈ kids, AtomWeight rank B k)
        ≤ ∑ _k ∈ kids, (B + 1) ^ r := Finset.sum_le_sum hbound
      _ = kids.card * (B + 1) ^ r := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ B * (B + 1) ^ r := Nat.mul_le_mul_right _ hcard
      _ < (B + 1) * (B + 1) ^ r := by nlinarith [hpp]
      _ = AtomWeight rank B focus := by rw [AtomWeight, hrf]; ring

/-! ### §10–15. Euclidean path node, moves, energy decrease -/

/-- Euclidean path node: level `A`, debt `debt`, local fuel `localFuel`. -/
structure EuclideanPathNode (M0 N : ℕ) (Atom : Type*) [DecidableEq Atom] where
  A : ℕ
  debt : Finset Atom
  localFuel : ℕ

/-- Node energy: `(DebtEnergy, localFuel)`. -/
def EuclideanPathNode.energy {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    (x : EuclideanPathNode M0 N Atom) : ℕ × ℕ :=
  (DebtEnergy rank B x.debt, x.localFuel)

/-- Internal move: same level, same debt, strictly less fuel. -/
structure InternalPass {M0 N : ℕ} (x y : EuclideanPathNode M0 N Atom) : Prop where
  same_level : y.A = x.A
  debt_same : y.debt = x.debt
  fuel_drop : y.localFuel < x.localFuel

/-- Promote move: level up + weighted debt replacement (carries replacement data, hence `Type`). -/
structure PromotePass {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    (x y : EuclideanPathNode M0 N Atom) where
  level_lt : x.A < y.A
  replacement : WeightedDebtReplacement rank B x.debt y.debt

/-- **`promotePass_decreases_debtEnergy` — PROVED.** Promotion drops `DebtEnergy`. -/
theorem promotePass_decreases_debtEnergy {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    {x y : EuclideanPathNode M0 N Atom} (h : PromotePass rank B x y) :
    DebtEnergy rank B y.debt < DebtEnergy rank B x.debt :=
  debtEnergy_decreases_of_weightedReplacement rank B h.replacement

/-- Euclidean path move: internal or promote. -/
inductive EuclideanPathMove {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ) :
    EuclideanPathNode M0 N Atom → EuclideanPathNode M0 N Atom → Prop
  | internal {x y} : InternalPass x y → EuclideanPathMove rank B x y
  | promote {x y} : PromotePass rank B x y → EuclideanPathMove rank B x y

/--
  **`euclideanPathMove_decreases_energy` — PROVED.** Every move strictly decreases the lex-energy:
  internal — the second coordinate (fuel), promote — the first (debt). -/
theorem euclideanPathMove_decreases_energy {M0 N : ℕ} (rank : Atom → ℕ) (B : ℕ)
    {x y : EuclideanPathNode M0 N Atom} (hMove : EuclideanPathMove rank B x y) :
    LexNat (EuclideanPathNode.energy rank B y) (EuclideanPathNode.energy rank B x) := by
  cases hMove with
  | internal h =>
    refine Or.inr ⟨?_, h.fuel_drop⟩
    show DebtEnergy rank B y.debt = DebtEnergy rank B x.debt
    rw [h.debt_same]
  | promote h =>
    exact Or.inl (promotePass_decreases_debtEnergy rank B h)

/-! ### §16–18. CloseAt, NoClose and the main theorem -/

/-- `CloseAt A M0 N := Engine A M0 ∨ ∃ t>N, twin`. Abstract `Engine`. -/
def CloseAt (Engine : ℕ → ℕ → Prop) (Twin : ℕ → Prop) (A M0 N : ℕ) : Prop :=
  Engine A M0 ∨ ∃ t, N < t ∧ Twin t

/--
  **`higher_energy_incompatibility_on_euclidean_path` — PROVED (main theorem).** If there is a live
  start, every live node either closes or makes an energy-decreasing move to a live node, and under
  `¬Engine` and "no twin above N" closing is forbidden, then `False`. This is the well-founded prohibition
  of an infinite Euclidean path, applied to the lex-energy `(DebtEnergy, LocalFuel)`. -/
theorem higher_energy_incompatibility_on_euclidean_path
    {Engine : ℕ → ℕ → Prop} {Twin : ℕ → Prop}
    (rank : Atom → ℕ) (B : ℕ) (M0 N : ℕ)
    (Live : EuclideanPathNode M0 N Atom → Prop)
    (hStart : ∃ x, Live x)
    (hStep : ∀ x, Live x →
      CloseAt Engine Twin x.A M0 N ∨ ∃ y, Live y ∧ EuclideanPathMove rank B x y)
    (hNoEngine : ∀ A, ¬ Engine A M0)
    (hNoNew : ¬ ∃ t, N < t ∧ Twin t) :
    False := by
  refine no_live_state_if_closes_or_moves_down Live
    (fun x => CloseAt Engine Twin x.A M0 N)
    (fun x y => EuclideanPathMove rank B x y)
    (fun x => EuclideanPathNode.energy rank B x)
    hStep ?_ (fun {x y} h => euclideanPathMove_decreases_energy rank B h) hStart
  · intro x hx hClose
    rcases hClose with hE | hT
    · exact hNoEngine x.A hE
    · exact hNoNew hT

/--
  **`twin_above_of_higher_energy_engine` — PROVED (positive form).** The same engine in
  contrapositive: under `¬Engine`, the existence of a live path with close-or-decrease gives a twin above N. -/
theorem twin_above_of_higher_energy_engine
    {Engine : ℕ → ℕ → Prop} {Twin : ℕ → Prop}
    (rank : Atom → ℕ) (B : ℕ) (M0 N : ℕ)
    (Live : EuclideanPathNode M0 N Atom → Prop)
    (hStart : ∃ x, Live x)
    (hStep : ∀ x, Live x →
      CloseAt Engine Twin x.A M0 N ∨ ∃ y, Live y ∧ EuclideanPathMove rank B x y)
    (hNoEngine : ∀ A, ¬ Engine A M0) :
    ∃ t, N < t ∧ Twin t := by
  by_contra hNoTwin
  exact higher_energy_incompatibility_on_euclidean_path rank B M0 N Live hStart hStep hNoEngine hNoTwin

/-! ### §22bis. Machine-verified NO-GO: refuel-promotion is NOT a replacement

Honesty (per audit): the sole unresolved input is `step00_promotion_is_weightedDebtReplacement`,
and on the `6m±1` graph it is NOT instantiable. The reason is arithmetic and sharp: ALL real-arithmetic
dynamics of the graph goes DOWNWARD in height/centre (`active_descent_height` `n<m`, `old_peel_height_drop` `t<n`,
`cofactor_is_center`, `RankDescent` `r→r−1`), whereas `PromotePass` requires `x.A < y.A` — UPWARD. Raising
the threshold `A→A'` GROWS the set of old primes (`oldPrimorial ∏_{5≤p≤A} p` is monotone), meaning promotion
ADDS debt atoms (union with fresh ones, without erasing the focus) — this is refuel, not
`(D.erase focus) ∪ kids` with strictly smaller weight. Any `rank` under which an UPWARD move drops
`(B+1)^rank` already asserts that the descent ends in twins = the goal (the same signature as
`smallCleanSupply_iff_goal`).

Below is the concrete machine-verified witness: a promotion that INCREASES weight (added an atom, erased nothing)
CANNOT be a `WeightedDebtReplacement` — the type structurally forbids forging a decrease. -/

/--
  **`refuel_is_not_weightedReplacement` — PROVED (no-go, honesty built into the type).** Concretely:
  `Atom := ℕ`, `rank := id`, `B := 1`. Refuel `{0} → {0,1}` (atom `1` added, nothing erased)
  GROWS the weight (`E({0})=1 < E({0,1})=3`), so there is NO `WeightedDebtReplacement id 1 {0} {0,1}`:
  a replacement must STRICTLY decrease `DebtEnergy` (`debtEnergy_decreases_of_weightedReplacement`), but
  here the energy grows. Therefore a weight-increasing promotion (= refuel) cannot be expressed as a replacement —
  the engine rejects it by construction. This is the machine version of the §22 admission "the line dies honestly". -/
theorem refuel_is_not_weightedReplacement :
    ¬ Nonempty (WeightedDebtReplacement (Atom := ℕ) id 1 {0} {0, 1}) := by
  rintro ⟨rep⟩
  have hdec := debtEnergy_decreases_of_weightedReplacement (Atom := ℕ) id 1 rep
  have h1 : DebtEnergy (Atom := ℕ) id 1 {0} = 1 := by decide
  have h2 : DebtEnergy (Atom := ℕ) id 1 {0, 1} = 3 := by decide
  rw [h1, h2] at hdec
  omega

end EuclidsPath.HigherEnergy
