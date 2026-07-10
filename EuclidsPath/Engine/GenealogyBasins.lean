import Mathlib
import EuclidsPath.Engine.GenealogyForest
import EuclidsPath.Engine.BoundaryDecomp
import EuclidsPath.Engine.Step00GraveStructure

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Genealogy basins — deterministic graves, infinite fan-in, and the price of every escape route

The genealogical forest (`GenealogyForest`) proves that every center `m ≥ 1` descends to a
twin at or below `m`, through the EXISTENTIAL peel `peel_of_not_twin`.  This file makes one
branch of that descent DETERMINISTIC — a computable `canonicalPeel` mirroring the
left-wing-first construction inside `peel_of_not_twin`, and its well-founded iterate
`grave` — and then measures, honestly, what each proposed escape route actually buys:

* `TwinFreeInterval` / `twinFree_descent_exit` — every genealogy entering a twin-free
  interval passes strictly below its floor: intervals do not trap genealogies, they
  deflect them downward (the honest replacement of the literal dichotomy);
* `canonicalPeel` / `canonicalPeel_isPeelStep` / `grave` / `grave_isTwin` / `grave_le` —
  the deterministic descent and its twin endpoint;
* `dichotomy_literal_refuted` — the DETERMINISTIC-genealogy reading of the dichotomy is
  FALSE at `(a, b) = (8, 9)`: the interval is twin-free, yet `grave 8 = 1 ≠ 2 = grave 9`;
* `grave_le_of_noNewTwinAbove` / `grave_infinite_fanin_of_noNewTwinAbove` — under the
  finite-twins hypothesis `BoundaryDecomp.NoNewTwinAbove M0` every grave sits `≤ M0` and
  some single grave has INFINITE fan-in (the pigeonhole half of
  `BoundaryDecomp.global_absorber_forces_engine`, proved directly — see the docstring);
* `reverse_fanin_infinite` — the reverse tree is infinitely branching at EVERY node
  (one predecessor per prime `p ≥ 5`): the König tombstone;
* `adjacent_wings_pairwise_coprime` / `adjacent_peel_alphabets_disjoint` — adjacent
  centers have pairwise coprime wings, so their first-step peel alphabets are disjoint
  (genuine green content: infinitely close points differ);
* `escape_iff_unbounded_twins` — "the graves escape every finite set" is EQUIVALENT to
  twin infinitude: the formal name of the escape strategy, and the exact wall it pays.

## Honest reading

Nothing here multiplies twins.  The deterministic layer picks one branch of the existing
existential descent; the fan-in statements convert the finite-twins hypothesis into
counting facts but never discharge it; the equivalence names the wall, it does not scale
it.  `twin_prime_conjecture` stays untouched.
-/

namespace EuclidsPath.GenealogyBasins

open EuclidsPath.Residuals
open EuclidsPath.Genealogy
open EuclidsPath.BoundaryDecomp

/-! ### Section 1 — twin-free intervals deflect genealogies downward -/

/-- `TwinFreeInterval a b`: no twin center strictly above `a` and at most `b`. -/
def TwinFreeInterval (a b : ℕ) : Prop :=
  ∀ m, a < m → m ≤ b → ¬ TwinCenterZ m

/-- **Every genealogy entering a twin-free interval exits below its floor.**  From
    `descent_reaches_twin` the descent from `m` hits a twin `t ≤ m`; a twin cannot sit in
    the twin-free window `(a, b]`, so `t ≤ a`.  This is the honest replacement of the
    literal interval dichotomy: a twin-free interval does not trap or split genealogies,
    it deflects every one of them strictly below its floor. -/
theorem twinFree_descent_exit {a b m : ℕ} (h : TwinFreeInterval a b)
    (ha : a < m) (hb : m ≤ b) (hm : 1 ≤ m) :
    ∃ t : ℕ, t ≤ a ∧ 1 ≤ t ∧ TwinCenterZ t := by
  obtain ⟨t, htm, ht1, htw⟩ := descent_reaches_twin m hm
  refine ⟨t, ?_, ht1, htw⟩
  by_contra hgt
  exact h t (by omega) (by omega) htw

/-! ### Section 2 — the deterministic peel and the grave map -/

/-- `m = 1` is a twin center: the pair `(5, 7)`. -/
theorem twinCenterZ_one : TwinCenterZ 1 := by norm_num [TwinCenterZ]

/-- `m = 2` is a twin center: the pair `(11, 13)`. -/
theorem twinCenterZ_two : TwinCenterZ 2 := by norm_num [TwinCenterZ]

instance : DecidablePred TwinCenterZ := fun m =>
  decidable_of_iff ((6 * m - 1).Prime ∧ (6 * m + 1).Prime) Iff.rfl

/-- The canonical peel target read off a composite wing `S`: take `p := S.minFac`, cofactor
    `s := S / p` (coprime to 6, hence `s ≡ ±1 (mod 6)`), and return the center of `s`:
    `(s - 1)/6` when `s ≡ 1`, `(s + 1)/6` when `s ≡ 5`.  Mirrors the arithmetic inside
    `Genealogy.peel_of_not_twin` (`peel_of_composite_side` / `factor_coprime6`). -/
def wingPeel (S : ℕ) : ℕ :=
  if S / S.minFac % 6 = 1 then (S / S.minFac - 1) / 6 else (S / S.minFac + 1) / 6

/-- **The canonical (deterministic) peel** — left-wing-first: if the left wing `6m − 1` is
    composite, peel it; else if the right wing `6m + 1` is composite, peel that; a twin
    (both wings prime) gets the junk value `0`.  This is one computable branch of the
    existential `peel_of_not_twin`, nothing more. -/
def canonicalPeel (m : ℕ) : ℕ :=
  if (6 * m - 1).Prime then
    if (6 * m + 1).Prime then 0 else wingPeel (6 * m + 1)
  else wingPeel (6 * m - 1)

/-- The canonical peel of a composite wing is a genuine `PeelStep` target.  Deterministic
    mirror of `Genealogy.peel_of_composite_side`. -/
private theorem wingPeel_peelStep {m : ℕ} (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    {S : ℕ} (hSeq : (S : ℤ) = 6 * (m : ℤ) - ε) (hS5 : 5 ≤ S) (hSc : ¬ S.Prime) :
    PeelStep m (wingPeel S) := by
  have h2 : ¬ 2 ∣ S := by rcases hε with rfl | rfl <;> omega
  have h3 : ¬ 3 ∣ S := by rcases hε with rfl | rfl <;> omega
  have hp : S.minFac.Prime := Nat.minFac_prime (by omega)
  have hpd : S.minFac ∣ S := Nat.minFac_dvd S
  have hp2 : S.minFac ≠ 2 := fun h => h2 (h ▸ hpd)
  have hp3 : S.minFac ≠ 3 := fun h => h3 (h ▸ hpd)
  have hp4 : S.minFac ≠ 4 := fun h => (show ¬ Nat.Prime 4 by decide) (h ▸ hp)
  have hp5 : 5 ≤ S.minFac := by have := hp.two_le; omega
  obtain ⟨s, hs⟩ := hpd
  have hsdiv : S / S.minFac = s := Nat.div_eq_of_eq_mul_right hp.pos hs
  have h2s : ¬ 2 ∣ s := fun h => h2 (hs ▸ Dvd.dvd.mul_left h S.minFac)
  have h3s : ¬ 3 ∣ s := fun h => h3 (hs ▸ Dvd.dvd.mul_left h S.minFac)
  have hs0 : s ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hs; omega
  have hs1 : s ≠ 1 := by
    rintro rfl; rw [Nat.mul_one] at hs; exact hSc (by rw [hs]; exact hp)
  have hs5 : 5 ≤ s := by omega
  unfold wingPeel
  rw [hsdiv]
  rcases (by omega : s % 6 = 1 ∨ s % 6 = 5) with h1 | h5
  · rw [if_pos h1]
    refine ⟨ε, 1, hε, Or.inl rfl, S.minFac, hp, hp5, by omega, ?_⟩
    have hst : ((s : ℕ) : ℤ) = 6 * (((s - 1) / 6 : ℕ) : ℤ) + 1 := by omega
    calc 6 * (m : ℤ) - ε = (S : ℤ) := hSeq.symm
      _ = (S.minFac : ℤ) * ((s : ℕ) : ℤ) := by exact_mod_cast hs
      _ = (S.minFac : ℤ) * (6 * (((s - 1) / 6 : ℕ) : ℤ) + 1) := by rw [hst]
  · rw [if_neg (by omega : ¬ s % 6 = 1)]
    refine ⟨ε, -1, hε, Or.inr rfl, S.minFac, hp, hp5, by omega, ?_⟩
    have hst : ((s : ℕ) : ℤ) = 6 * (((s + 1) / 6 : ℕ) : ℤ) - 1 := by omega
    calc 6 * (m : ℤ) - ε = (S : ℤ) := hSeq.symm
      _ = (S.minFac : ℤ) * ((s : ℕ) : ℤ) := by exact_mod_cast hs
      _ = (S.minFac : ℤ) * (6 * (((s + 1) / 6 : ℕ) : ℤ) - 1) := by rw [hst]

/-- **The canonical peel of a non-twin is a genuine peel step.**  Deterministic totality:
    `canonicalPeel` realises one branch of `Genealogy.peel_of_not_twin`. -/
theorem canonicalPeel_isPeelStep {m : ℕ} (hm : 1 ≤ m) (hnt : ¬ TwinCenterZ m) :
    PeelStep m (canonicalPeel m) := by
  by_cases hL : (6 * m - 1).Prime
  · have hR : ¬ (6 * m + 1).Prime := fun h => hnt ⟨hL, h⟩
    have hval : canonicalPeel m = wingPeel (6 * m + 1) := by
      unfold canonicalPeel
      rw [if_pos hL, if_neg hR]
    rw [hval]
    exact wingPeel_peelStep (-1) (Or.inr rfl) (S := 6 * m + 1)
      (by push_cast; ring) (by omega) hR
  · have hval : canonicalPeel m = wingPeel (6 * m - 1) := by
      unfold canonicalPeel
      rw [if_neg hL]
    rw [hval]
    exact wingPeel_peelStep 1 (Or.inl rfl) (S := 6 * m - 1)
      (by omega) (by omega) hL

/-- **The grave map**: iterate the canonical peel until a twin (or the degenerate `m ≤ 1`;
    note `m = 1` IS a twin, the pair `(5, 7)`, so the `m ≤ 1` guard only truncates `m = 0`).
    Well-founded: each canonical peel is strictly downhill (`peelStep_lt`). -/
def grave (m : ℕ) : ℕ :=
  if h : TwinCenterZ m ∨ m ≤ 1 then m
  else grave (canonicalPeel m)
termination_by m
decreasing_by
  have hnt : ¬ TwinCenterZ m := fun ht => h (Or.inl ht)
  have hm2 : 2 ≤ m := by
    by_contra hc
    exact h (Or.inr (by omega))
  exact peelStep_lt hm2 (canonicalPeel_isPeelStep (by omega) hnt)

/-- A twin is its own grave (the recursion stops immediately). -/
theorem grave_twin_self {m : ℕ} (h : TwinCenterZ m) : grave m = m := by
  rw [grave.eq_def, dif_pos (Or.inl h)]

/-- Unfolding equation for the recursive branch of `grave`. -/
theorem grave_step {m : ℕ} (hm2 : 2 ≤ m) (hnt : ¬ TwinCenterZ m) :
    grave m = grave (canonicalPeel m) := by
  have hcond : ¬ (TwinCenterZ m ∨ m ≤ 1) := fun hc =>
    hc.elim hnt (fun hle => absurd hle (by omega))
  rw [grave.eq_def, dif_neg hcond]

/-- **The grave of every center `m ≥ 1` is a twin.** -/
theorem grave_isTwin {m : ℕ} (hm : 1 ≤ m) : TwinCenterZ (grave m) := by
  revert hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases htw : TwinCenterZ m
    · rwa [grave_twin_self htw]
    · have hm2 : 2 ≤ m := by
        by_contra hlt
        exact htw (by
          have h1 : m = 1 := by omega
          rw [h1]; exact twinCenterZ_one)
      have hpeel := canonicalPeel_isPeelStep (by omega) htw
      have hlt := peelStep_lt hm2 hpeel
      have ht1 : 1 ≤ canonicalPeel m := by
        obtain ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩ := hpeel
        exact ht1
      rw [grave_step hm2 htw]
      exact ih _ hlt ht1

/-- **The grave never climbs**: `grave m ≤ m` (the descent is downhill). -/
theorem grave_le {m : ℕ} : grave m ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hcond : TwinCenterZ m ∨ m ≤ 1
    · have h : grave m = m := by rw [grave.eq_def, dif_pos hcond]
      exact h.le
    · have hnt : ¬ TwinCenterZ m := fun ht => hcond (Or.inl ht)
      have hm2 : 2 ≤ m := by
        by_contra hc
        exact hcond (Or.inr (by omega))
      have hlt : canonicalPeel m < m :=
        peelStep_lt hm2 (canonicalPeel_isPeelStep (by omega) hnt)
      calc grave m = grave (canonicalPeel m) := by
            rw [grave.eq_def, dif_neg hcond]
        _ ≤ canonicalPeel m := ih _ hlt
        _ ≤ m := Nat.le_of_lt hlt

/-! ### Section 3 — the literal dichotomy is refuted -/

/--
  **The literal (deterministic-genealogy) reading of the interval dichotomy is FALSE.**
  The interval `(8, 9]` is twin-free (`6·9 + 1 = 55 = 5·11` is composite), yet the two
  deterministic genealogies entering it from its endpoints land in DIFFERENT graves:
  `grave 8 = 1` (via `6·8 + 1 = 49 = 7·7`, cofactor `7 = 6·1 + 1`, then the twin `(5,7)`;
  the left wing `47` is prime, so the canonical left-wing-first order peels the RIGHT wing)
  and `grave 9 = 2` (via `6·9 + 1 = 55 = 5·11`, cofactor `11 = 6·2 − 1`, then the twin
  `(11,13)`).  So "all genealogies crossing a twin-free interval merge" is false as stated.

  DISCLOSURE: this refutes only the DETERMINISTIC-genealogy reading of the user dichotomy
  (the reading in which each center has ONE genealogy, the canonical one).  The relational
  reading — "the reach-sets of the two endpoints MAY share a twin below" — is separately
  VACUOUS rather than false: reach-sets along the existential `PeelStep` may always share
  a low grave (every descent can be routed into the basin of `(5,7)`), so that reading
  carries no obstruction at all.  Neither reading produces a twin above anything.

  Proof note: `grave` is defined by well-founded recursion, which the kernel does not
  reduce, so `decide` is not available here; the values are obtained by unfolding the
  equation lemmas (`grave_step` / `grave_twin_self`) with `norm_num` closing the
  wing-primality side conditions.
-/
theorem dichotomy_literal_refuted :
    TwinFreeInterval 8 9 ∧ grave 8 = 1 ∧ grave 9 = 2 ∧ (1 : ℕ) ≠ 2 := by
  have h8nt : ¬ TwinCenterZ 8 := by norm_num [TwinCenterZ]
  have h9nt : ¬ TwinCenterZ 9 := by norm_num [TwinCenterZ]
  have hc8 : canonicalPeel 8 = 1 := by norm_num [canonicalPeel, wingPeel]
  have hc9 : canonicalPeel 9 = 2 := by norm_num [canonicalPeel, wingPeel]
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro k h8 h9 htw
    have hk : k = 9 := by omega
    subst hk
    exact h9nt htw
  · rw [grave_step (by norm_num) h8nt, hc8, grave_twin_self twinCenterZ_one]
  · rw [grave_step (by norm_num) h9nt, hc9, grave_twin_self twinCenterZ_two]

/-! ### Section 4 — graves under the finite-twins hypothesis: pigeonhole fan-in -/

/-- **Under `BoundaryDecomp.NoNewTwinAbove M0` every grave sits at or below `M0`.**
    The grave is a twin (`grave_isTwin`); no twins above `M0` means it cannot exceed `M0`.
    (Adaptation note: `NoNewTwinAbove M0 = ∀ m, M0 < m → ¬ TwinCenterZ m` is exactly the
    predicate of `EuclidsPath.Engine.BoundaryDecomp` — no reshaping was needed.) -/
theorem grave_le_of_noNewTwinAbove {M0 : ℕ} (h : NoNewTwinAbove M0)
    {m : ℕ} (hm : 1 ≤ m) : grave m ≤ M0 := by
  by_contra hgt
  exact h (grave m) (by omega) (grave_isTwin hm)

/--
  **Pigeonhole: if no new twin exists above `M0`, some single grave has INFINITE fan-in.**
  The infinite set `{m | 1 ≤ m}` is mapped by `grave` into the finite window `[0, M0]`
  (`grave_le_of_noNewTwinAbove`), so some fiber `{m | 1 ≤ m ∧ grave m = t}` is infinite —
  and its base point `t` is a twin.

  DISCLOSURE (relation to `BoundaryDecomp.global_absorber_forces_engine`): that skeleton
  is the same pigeonhole, but it CONSUMES a `pump` hypothesis (collision ⟹ engine) and
  PRODUCES an engine; it cannot be instantiated to produce the infinite fiber itself
  (it only ever extracts ONE collision pair).  So this statement is proved directly via
  `Set.Finite.biUnion` — if every fiber over `[0, M0]` were finite, their union would be
  finite, contradicting the infinitude of `{m | 1 ≤ m}`.  All the millennium weight still
  lives exactly where BoundaryDecomp flags it: turning this fan-in into an engine (the
  `pump` / Hall node) is NOT proved here or there.
-/
theorem grave_infinite_fanin_of_noNewTwinAbove {M0 : ℕ} (h : NoNewTwinAbove M0) :
    ∃ t : ℕ, t ≤ M0 ∧ TwinCenterZ t ∧ {m : ℕ | 1 ≤ m ∧ grave m = t}.Infinite := by
  by_contra hno
  have hfib : ∀ t ∈ Set.Iic M0, ({m : ℕ | 1 ≤ m ∧ grave m = t}).Finite := by
    intro t htmem
    by_cases htw : TwinCenterZ t
    · exact Set.not_infinite.mp (fun hinf => hno ⟨t, htmem, htw, hinf⟩)
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro k ⟨hk1, rfl⟩
      exact (htw (grave_isTwin hk1)).elim
  have hfin : (⋃ t ∈ Set.Iic M0, {m : ℕ | 1 ≤ m ∧ grave m = t}).Finite :=
    Set.Finite.biUnion (Set.finite_Iic M0) hfib
  have hcover : (Set.Ici 1 : Set ℕ) ⊆ ⋃ t ∈ Set.Iic M0, {m : ℕ | 1 ≤ m ∧ grave m = t} := by
    intro k hk
    have hk1 : 1 ≤ k := hk
    exact Set.mem_iUnion₂.mpr
      ⟨grave k, grave_le_of_noNewTwinAbove h hk1, hk1, rfl⟩
  exact Set.not_infinite.mpr (hfin.subset hcover) (Set.Ici_infinite 1)

/-! ### Section 5 — the reverse tree is infinitely branching: the König tombstone -/

/--
  **Reverse fan-in is infinite at EVERY node**: for each center `t ≥ 1` there are
  infinitely many `m` with `PeelStep m t`.  Construction: for every prime `p ≥ 5` take the
  right-form side `p · (6t + 1)`; since `p ≡ ±1 (mod 6)`, the product is `6m ∓ 1` for a
  center `m ≈ p(6t+1)/6 > p/6`, so ever-larger primes give ever-larger predecessors
  (`Nat.exists_infinite_primes` supplies them above every bound; the same
  unboundedness pattern as `GeometryFront.inDegree_infinite_at_origin`).

  DISCLOSURE (the König tombstone): the reverse genealogical tree is infinitely branching
  at every node, with branch labels = the primes `p ≥ 5`.  König's lemma (infinite
  finitely-branching tree has an infinite path) therefore NEVER applies to the reverse
  tree as-is; any argument routed through it must first compress the label alphabet to a
  finite one — which is exactly why `[Finite Lbl]` in `LabelledFanIn` is counting content
  in typeclass disguise, and why the reverse route pays the same wall as the forward one.
-/
theorem reverse_fanin_infinite {t : ℕ} (ht : 1 ≤ t) :
    {m : ℕ | PeelStep m t}.Infinite := by
  have key : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ PeelStep m t := by
    intro N
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 7)
    have h2 : ¬ 2 ∣ p := by
      intro hd
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega
    have h3 : ¬ 3 ∣ p := by
      intro hd
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
    rcases (by omega : p % 6 = 1 ∨ p % 6 = 5) with h1 | h5
    · -- p ≡ 1 (mod 6): p(6t+1) ≡ 1, so p(6t+1) = 6m + 1 = 6m − (−1)
      obtain ⟨a, rfl⟩ : ∃ a, p = 6 * a + 1 := ⟨p / 6, by omega⟩
      refine ⟨a * (6 * t + 1) + t, ?_,
        -1, 1, Or.inr rfl, Or.inl rfl, 6 * a + 1, hp, by omega, ht, ?_⟩
      · have h7 : a * 7 ≤ a * (6 * t + 1) := Nat.mul_le_mul_left a (by omega)
        omega
      · push_cast
        ring
    · -- p ≡ 5 (mod 6): p(6t+1) ≡ 5 ≡ −1, so p(6t+1) = 6m − 1
      obtain ⟨a, rfl⟩ : ∃ a, p = 6 * a + 5 := ⟨p / 6, by omega⟩
      refine ⟨a * (6 * t + 1) + 5 * t + 1, ?_,
        1, 1, Or.inl rfl, Or.inl rfl, 6 * a + 5, hp, by omega, ht, ?_⟩
      · have h7 : a * 7 ≤ a * (6 * t + 1) := Nat.mul_le_mul_left a (by omega)
        omega
      · push_cast
        ring
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨b, hb⟩
  obtain ⟨m, hbm, hpeel⟩ := key b
  exact absurd (hb hpeel) (by omega)

/-! ### Section 6 — adjacent centers have disjoint peel alphabets (green) -/

/-- No shared prime divisor forces coprimality (via the minimal factor of the gcd). -/
private theorem coprime_of_no_shared_prime {x y : ℕ}
    (h : ∀ q : ℕ, q.Prime → q ∣ x → q ∣ y → False) : Nat.Coprime x y := by
  by_contra hnc
  exact h (Nat.gcd x y).minFac (Nat.minFac_prime hnc)
    ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_left x y))
    ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_right x y))

/-- A prime cannot divide both members of a coprime pair. -/
private theorem prime_not_dvd_both {x y p : ℕ} (hco : Nat.Coprime x y) (hp : p.Prime)
    (hx : p ∣ x) (hy : p ∣ y) : False := by
  have hg : Nat.gcd x y = 1 := hco
  have h1 : p ∣ Nat.gcd x y := Nat.dvd_gcd hx hy
  rw [hg] at h1
  have := Nat.le_of_dvd Nat.one_pos h1
  have := hp.two_le
  omega

/--
  **Adjacent wings are pairwise coprime** ("infinitely close points differ"): each wing of
  the center `m` is coprime to each wing of the center `m + 1` (whose wings are
  `6(m+1) − 1 = 6m + 5` and `6(m+1) + 1 = 6m + 7`).  Any common divisor divides the
  difference (`6`, `8`, `4`, `6` respectively), is odd (all wings are odd), and is coprime
  to 3 (all wings are `≡ ±1 (mod 6)`) — so it is 1.  Together with the in-center
  coprimality (`Engine.twin_sides_shared_dvd_two`), all four wings of two adjacent centers
  are pairwise coprime. -/
theorem adjacent_wings_pairwise_coprime {m : ℕ} (hm : 1 ≤ m) :
    Nat.Coprime (6 * m - 1) (6 * m + 5) ∧ Nat.Coprime (6 * m - 1) (6 * m + 7) ∧
      Nat.Coprime (6 * m + 1) (6 * m + 5) ∧ Nat.Coprime (6 * m + 1) (6 * m + 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply coprime_of_no_shared_prime
    intro q hq hqa hqb
    have hq2 := hq.two_le
    have hd := Nat.dvd_sub hqb hqa
    rw [show 6 * m + 5 - (6 * m - 1) = 6 from by omega] at hd
    have hqle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases q <;> omega
  · apply coprime_of_no_shared_prime
    intro q hq hqa hqb
    have hq2 := hq.two_le
    have hd := Nat.dvd_sub hqb hqa
    rw [show 6 * m + 7 - (6 * m - 1) = 8 from by omega] at hd
    have hqle : q ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    interval_cases q <;> omega
  · apply coprime_of_no_shared_prime
    intro q hq hqa hqb
    have hq2 := hq.two_le
    have hd := Nat.dvd_sub hqb hqa
    rw [show 6 * m + 5 - (6 * m + 1) = 4 from by omega] at hd
    have hqle : q ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases q <;> omega
  · apply coprime_of_no_shared_prime
    intro q hq hqa hqb
    have hq2 := hq.two_le
    have hd := Nat.dvd_sub hqb hqa
    rw [show 6 * m + 7 - (6 * m + 1) = 6 from by omega] at hd
    have hqle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases q <;> omega

/-- **Adjacent peel alphabets are disjoint**: a prime `p ≥ 5` cannot divide a wing of `m`
    AND a wing of `m + 1`.  Consequence of the four coprimalities above: the first-step
    peel alphabets (available prime labels) of two adjacent centers share nothing. -/
theorem adjacent_peel_alphabets_disjoint {m p : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (h1 : p ∣ (6 * m - 1) ∨ p ∣ (6 * m + 1))
    (h2 : p ∣ (6 * (m + 1) - 1) ∨ p ∣ (6 * (m + 1) + 1)) : False := by
  obtain ⟨c15, c17, c55, c57⟩ := adjacent_wings_pairwise_coprime hm
  have h2' : p ∣ (6 * m + 5) ∨ p ∣ (6 * m + 7) := by
    rcases h2 with h | h
    · exact Or.inl (by rwa [show 6 * (m + 1) - 1 = 6 * m + 5 from by omega] at h)
    · exact Or.inr (by rwa [show 6 * (m + 1) + 1 = 6 * m + 7 from by omega] at h)
  rcases h1 with ha | ha <;> rcases h2' with hb | hb
  · exact prime_not_dvd_both c15 hp ha hb
  · exact prime_not_dvd_both c17 hp ha hb
  · exact prime_not_dvd_both c55 hp ha hb
  · exact prime_not_dvd_both c57 hp ha hb

/-! ### Section 7 — the escape strategy is exactly the goal -/

/--
  **The escape strategy, named and priced**: "the graves escape every finite set" is
  EQUIVALENT to "twins are unbounded".  Forward: to escape `Finset.Iic M0` the grave must
  exceed `M0`, and the grave is a twin.  Backward: an unbounded twin `t` above `T.sup id`
  is its own grave (`grave_twin_self`) and lies outside `T`.

  DISCLOSURE: this is the formal name of the user's escape strategy.  It shows the
  strategy is not a shortcut: producing escaping graves IS producing unbounded twins —
  the equivalence relocates the wall without lowering it by a single brick.
-/
theorem escape_iff_unbounded_twins :
    (∀ T : Finset ℕ, ∃ m, 1 ≤ m ∧ grave m ∉ T) ↔
      (∀ M0 : ℕ, ∃ t, M0 < t ∧ TwinCenterZ t) := by
  constructor
  · intro hesc M0
    obtain ⟨m, hm1, hnot⟩ := hesc (Finset.Iic M0)
    have hgt : M0 < grave m := by
      by_contra hle
      exact hnot (Finset.mem_Iic.mpr (by omega))
    exact ⟨grave m, hgt, grave_isTwin hm1⟩
  · intro hub T
    obtain ⟨t, hgt, htw⟩ := hub (T.sup id)
    refine ⟨t, GraveStructure.TwinCenterZ.one_le htw, ?_⟩
    rw [grave_twin_self htw]
    intro hmem
    have hle : t ≤ T.sup id := Finset.le_sup (f := id) hmem
    omega

end EuclidsPath.GenealogyBasins

/-
  ### Machine honesty (recorded `#print axioms` output)

  Checked against the built module (scratch run with `lake env lean`, file deleted);
  every declaration of this file sits under the standard axioms only — no `sorry`,
  no `step00FirstCause`, no `native_decide` (`Lean.ofReduceBool`):

  * `twinFree_descent_exit`                     — `[propext, Classical.choice, Quot.sound]`
  * `twinCenterZ_one` / `twinCenterZ_two`       — `[propext, Classical.choice, Quot.sound]`
  * `wingPeel` / `canonicalPeel`                — `[propext, Classical.choice, Quot.sound]`
  * `canonicalPeel_isPeelStep`                  — `[propext, Classical.choice, Quot.sound]`
  * `grave` / `grave_twin_self` / `grave_step`  — `[propext, Classical.choice, Quot.sound]`
  * `grave_isTwin` / `grave_le`                 — `[propext, Classical.choice, Quot.sound]`
  * `dichotomy_literal_refuted`                 — `[propext, Classical.choice, Quot.sound]`
  * `grave_le_of_noNewTwinAbove`                — `[propext, Classical.choice, Quot.sound]`
  * `grave_infinite_fanin_of_noNewTwinAbove`    — `[propext, Classical.choice, Quot.sound]`
  * `reverse_fanin_infinite`                    — `[propext, Classical.choice, Quot.sound]`
  * `adjacent_wings_pairwise_coprime`           — `[propext, Classical.choice, Quot.sound]`
  * `adjacent_peel_alphabets_disjoint`          — `[propext, Classical.choice, Quot.sound]`
  * `escape_iff_unbounded_twins`                — `[propext, Classical.choice, Quot.sound]`
-/
