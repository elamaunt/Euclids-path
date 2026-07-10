import EuclidsPath.Engine.Step00TwinJacobsthalWall

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Phase-cover kernel certificates — TRUE gaps `G(A)` for `A = 17 … 37`

`Step00TwinJacobsthalWall` proves wall instances by ONE-PERIOD certificates (`decide` over
`P_A` starts) and `Step00WitnessChainKernel` by witness CHAINS (cost still linear in the
period `P_A`, memory-bound at `A = 19`).  Both walls scale with the PERIOD — the P-scaling
wall.  This file breaks it: the gap bound `CleanGapBound A g` is decided by an UNSAT
**phase-cover certificate** whose cost tracks the branch-and-bound tree of the exact solver
(`tools/gap_extremal_harness.py::decision`), NOT the period.

The reduction (offsets vs phases): a window start `k` induces on each clock `q` the phase
`t_q = (-k) mod q`, and clock `q` strikes window offset `o` iff
`o ≡ t_q ± 6⁻¹ (mod q)`.  By CRT every phase tuple is realised by some `k`, so

  `G(A) ≤ g`  ⟺  no phase tuple covers all offsets `1 … g` (UNSAT).

The Bool layer below replays the solver's UNSAT run: full enumeration of the small-clock
phases (`5, 7, 11, 13` — `5005` tuples, NO mirror reduction: the Lean-canonical mode
`--pc nomirror,leanmodel` of the harness, node counts asserted equal per scale in
`tools/phase_cover_run1.log`), then a DFS over the big clocks anchored at the minimal
uncovered offset, branching over remaining clocks × the two phases covering that offset,
pruned by the EXACT residual capacity bound `Σ_q max_t |U ∩ cov_q(t)| < |U|`.

The Prop layer is one-directional (`Bool = true → …`): the fold is a certificate CHECKER.
`Uncoverable rem U` says NO phase assignment covers all of `U`; `dfsB_sound`,
`enumSmall_sound` recover it from the fold, and the bridge `cleanGapBound_of_unsatCover`
turns it into `CleanGapBound A g` by instantiating the assignment induced by an arbitrary
window start `k` (the direction `q ∣ 6(k+o) ∓ 1 → o` covered is `dvd_wing_*` +
`offset_phase`).  The SAT side (`allStruckB` + a trial-division-verified run of `G-1`
consecutive struck centers) refutes `CleanGapBound A (G-1)` — together: `G(A)` EXACT,
kernel-checked, at cost ~ the B&B tree (hundreds to tens of thousands of nodes), not the
period (`P_37 ≈ 1.3·10¹²`).
-/

namespace EuclidsPath
namespace PhaseCoverKernel

open EuclidsPath.CleanGraph
open EuclidsPath.TwinJacobsthalWall

/-! ### The Bool checker (kernel-reducible replica of the exact phase-cover solver) -/

/-- A sieve clock: the modulus `q` paired with `i6 = 6⁻¹ mod q`. -/
abbrev CoverClock := ℕ × ℕ

/-- `coveredB q i6 t o`: clock `q` at phase `t` strikes window offset `o`
    (`o ≡ t ± i6 (mod q)`; the phase `t` represents `(-k) mod q` for window start `k`). -/
def coveredB (q i6 t o : ℕ) : Bool :=
  (o % q == (t + i6) % q) || (o % q == (t + (q - i6)) % q)

/-- The offsets of `U` surviving clock `q` at phase `t` (order-preserving, so the head of
    the result is the minimal survivor — the DFS anchor policy). -/
def strikeFilter (q i6 t : ℕ) (U : List ℕ) : List ℕ :=
  U.filter fun o => !coveredB q i6 t o

/-- Base of the residue-count words (a window never holds `2¹⁶` offsets — `g ≤ 88` here). -/
def cntB : ℕ := 65536

theorem cntB_pos : 0 < cntB := by norm_num [cntB]

/-- The residue-count word `Σ_{o ∈ U} cntB ^ (o % q)`: one base-`cntB` digit per residue
    class of `q`, carry-free because `|U| < cntB`.  This is the GMP-friendly form of the
    per-residue histogram — the kernel folds `U` ONCE per clock instead of re-scanning it
    for each of the `q` phases (the naive `q·|U|` scan measured ≈ 15 KB of kernel-cache
    growth per phase×element visit; the word cuts both time and peak memory ≈ 5×). -/
def resWord (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | o :: U => cntB ^ (o % q) + resWord q U

/-- Digit `r` of a residue-count word. -/
def digit (N r : ℕ) : ℕ := N / cntB ^ r % cntB

/-- Exact per-clock capacity on `U`: the best phase's coverage count
    `max_{t < q} |U ∩ cov_q(t)|`, read off the residue-count word as the digit sum of the
    two wings `(t ± i6) mod q`. -/
def capQ (q i6 : ℕ) (U : List ℕ) : ℕ :=
  let N := resWord q U
  (List.range q).foldl
    (fun b t => max b (digit N ((t + i6) % q) + digit N ((t + (q - i6)) % q))) 0

/-- The exact residual-capacity prune as an early-exit fold:
    `capLtB rem n U = true ↔ Σ_{p ∈ rem} capQ p U < n` (the fold stops as soon as the
    accumulated capacity reaches the demand `n`). -/
def capLtB : List CoverClock → ℕ → List ℕ → Bool
  | [], n, _ => Nat.blt 0 n
  | p :: rem, n, U =>
      Nat.blt (capQ p.1 p.2 U) n && capLtB rem (n - capQ p.1 p.2 U) U

/-- The UNSAT DFS over the big clocks.  `dfsB fuel rem U = true` certifies that no phase
    assignment of `rem` covers all of `U`: either the exact residual capacity already
    falls short, or for EVERY remaining clock and EACH of the two phases striking the
    minimal uncovered offset `o` (head of `U`), the residual problem is again
    uncoverable.  `fuel = |rem| + 1` makes the recursion structural; running out of fuel
    or out of offsets answers `false` (the checker only ever errs on the safe side). -/
def dfsB : ℕ → List CoverClock → List ℕ → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => false
  | fuel + 1, rem, o :: U' =>
      capLtB rem (o :: U').length (o :: U') ||
        (List.range rem.length).all fun i =>
          let p := rem[i]!
          let rem' := rem.eraseIdx i
          dfsB fuel rem' (strikeFilter p.1 p.2 ((o + p.1 - p.2) % p.1) (o :: U')) &&
            dfsB fuel rem' (strikeFilter p.1 p.2 ((o + p.2) % p.1) (o :: U'))

/-- Full enumeration of the small-clock phases (NO mirror reduction — the Lean-canonical
    mode of the harness), then the DFS over the big clocks. -/
def enumSmallB : List CoverClock → List CoverClock → List ℕ → Bool
  | [], bigs, U => dfsB (bigs.length + 1) bigs U
  | (q, i6) :: ss, bigs, U =>
      (List.range q).all fun t => enumSmallB ss bigs (strikeFilter q i6 t U)

/-- The SAT side: all `len` centers `r+1 … r+len` are struck by some listed clock
    (checked by trial division — phases play no role here). -/
def allStruckB (clocks : List CoverClock) (r len : ℕ) : Bool :=
  (List.range len).all fun j =>
    clocks.any fun p =>
      ((6 * (r + 1 + j) - 1) % p.1 == 0) || ((6 * (r + 1 + j) + 1) % p.1 == 0)

/-! #### Convention sanity checks (scale `A = 5`, window `g = 2`; `G(5) = 2`)

`coveredB q i6 t o` must hold iff clock `q` strikes offset `o` at window start `k` with
`t = (-k) mod q`: for `k = 3`, `o = 1` the center is `m = 4`, `6m + 1 = 25` is struck by
`5`, and indeed `coveredB 5 1 ((5 - 3 % 5) % 5) 1 = true`; offset `o = 2` gives `m = 5`,
`29 · 31` clean at scale 5, and `coveredB … 2 = false`. -/

example : coveredB 5 1 ((5 - 3 % 5) % 5) 1 = true := by decide
example : coveredB 5 1 ((5 - 3 % 5) % 5) 2 = false := by decide
/-- UNSAT at `g = G(5) = 2`: no phase of the single clock 5 covers both offsets. -/
example : enumSmallB [(5, 1)] [] (List.range' 1 2) = true := by decide
/-- SAT at `g = G(5) - 1 = 1`: phase `t = 0` covers offset 1 — the checker answers `false`. -/
example : enumSmallB [(5, 1)] [] (List.range' 1 1) = false := by decide

/-! ### Soundness: from the Bool fold to `Uncoverable` (one direction only) -/

/-- NO phase assignment `f` (clock modulus ↦ phase) covers all of `U`. -/
def Uncoverable (rem : List CoverClock) (U : List ℕ) : Prop :=
  ∀ f : ℕ → ℕ, ∃ o ∈ U, ∀ p ∈ rem, coveredB p.1 p.2 (f p.1) o = false

/-- Phases matter only mod `q`. -/
theorem coveredB_mod_phase (q i6 t o : ℕ) :
    coveredB q i6 (t % q) o = coveredB q i6 t o := by
  simp [coveredB, Nat.mod_add_mod]

private theorem countP_coveredB_mod (q i6 t : ℕ) (U : List ℕ) :
    U.countP (coveredB q i6 t) = U.countP (coveredB q i6 (t % q)) :=
  List.countP_congr fun o _ => by rw [coveredB_mod_phase]

/-- Subadditivity of `countP` over a disjunction. -/
private theorem countP_or_le (p q : ℕ → Bool) (l : List ℕ) :
    (l.countP fun a => p a || q a) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hp : p x <;> by_cases hq : q x <;>
        simp [hp, hq] <;> omega

/-- Subadditivity over the clock list: the number of offsets covered by SOME clock is at
    most the sum of the per-clock coverage counts. -/
private theorem countP_any_le (f : ℕ → ℕ) (U : List ℕ) :
    ∀ rem : List CoverClock,
      (U.countP fun o => rem.any fun p => coveredB p.1 p.2 (f p.1) o) ≤
        (rem.map fun p => U.countP (coveredB p.1 p.2 (f p.1))).sum
  | [] => by simp
  | p :: rem => by
      have h1 : (U.countP fun o => (p :: rem).any fun p' => coveredB p'.1 p'.2 (f p'.1) o) ≤
          U.countP (coveredB p.1 p.2 (f p.1)) +
            (U.countP fun o => rem.any fun p' => coveredB p'.1 p'.2 (f p'.1) o) := by
        simpa [List.any_cons] using
          countP_or_le (coveredB p.1 p.2 (f p.1))
            (fun o => rem.any fun p' => coveredB p'.1 p'.2 (f p'.1) o) U
      have h2 := countP_any_le f U rem
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem le_foldl_max_acc (fn : ℕ → ℕ) :
    ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl (fun acc t => max acc (fn t)) b := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons x xs ih => intro b; exact le_trans (le_max_left b (fn x)) (ih _)

private theorem fn_le_foldl_max (fn : ℕ → ℕ) :
    ∀ (l : List ℕ) (b x : ℕ), x ∈ l → fn x ≤ l.foldl (fun acc t => max acc (fn t)) b := by
  intro l
  induction l with
  | nil => intro b x hx; simp at hx
  | cons a as ih =>
      intro b x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_trans (le_trans (le_max_right b (fn x)) (le_foldl_max_acc fn as _)) le_rfl
      · exact ih _ x hx'

/-! #### The residue-count word is a carry-free histogram (digit = class count) -/

/-- Little-endian coefficient evaluation (spec-side only — never kernel-evaluated). -/
private def wordOf : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + cntB * wordOf cs

/-- Residue-class count. -/
private def cnt (q c : ℕ) (U : List ℕ) : ℕ := U.countP fun o => o % q == c

/-- The counts table over `range q`. -/
private def countsList (q : ℕ) (U : List ℕ) : List ℕ :=
  (List.range q).map fun c => cnt q c U

/-- Digit extraction from a carry-free coefficient word. -/
private theorem wordOf_digit :
    ∀ (cs : List ℕ), (∀ c ∈ cs, c < cntB) →
      ∀ j, wordOf cs / cntB ^ j % cntB = cs.getD j 0 := by
  intro cs
  induction cs with
  | nil => intro _ j; simp [wordOf]
  | cons c cs ih =>
      intro hb j
      have hc : c < cntB := hb c List.mem_cons_self
      have hb' : ∀ x ∈ cs, x < cntB := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      cases j with
      | zero =>
          simp only [wordOf, pow_zero, Nat.div_one, List.getD_cons_zero]
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hc
      | succ j =>
          simp only [wordOf, List.getD_cons_succ]
          rw [pow_succ, Nat.mul_comm (cntB ^ j) cntB, ← Nat.div_div_eq_div_mul]
          have hdiv : (c + cntB * wordOf cs) / cntB = wordOf cs := by
            rw [Nat.add_mul_div_left _ _ cntB_pos]
            simp [Nat.div_eq_of_lt hc]
          rw [hdiv]
          exact ih hb' j

/-- Bumping one coefficient bumps the word by the corresponding power. -/
private theorem wordOf_set :
    ∀ (cs : List ℕ) (s : ℕ), s < cs.length →
      wordOf (cs.set s (cs.getD s 0 + 1)) = wordOf cs + cntB ^ s := by
  intro cs
  induction cs with
  | nil => intro s hs; simp at hs
  | cons c cs ih =>
      intro s hs
      cases s with
      | zero => simp [wordOf]; ring
      | succ s =>
          simp only [List.set_cons_succ, List.getD_cons_succ, wordOf]
          rw [ih s (by simpa using hs)]
          rw [pow_succ]
          ring

/-- The counts table of `o :: U` is the table of `U` bumped at `o % q`. -/
private theorem countsList_cons (q o : ℕ) (U : List ℕ) :
    countsList q (o :: U) = (countsList q U).set (o % q) (cnt q (o % q) U + 1) := by
  apply List.ext_getElem
  · simp [countsList]
  · intro i h1 h2
    have hiq : i < q := by simpa [countsList] using h1
    simp only [countsList, List.getElem_map, List.getElem_range, List.getElem_set]
    by_cases hio : i = o % q
    · subst hio
      simp [cnt]
    · rw [if_neg (by omega)]
      simp only [cnt, List.countP_cons]
      have hne : (o % q == i) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      rw [hne]
      simp

private theorem wordOf_replicate_zero : ∀ n : ℕ, wordOf (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, wordOf, wordOf_replicate_zero n]

/-- `resWord` is the carry-free evaluation of the counts table. -/
private theorem resWord_eq_wordOf (q : ℕ) (hq : 0 < q) :
    ∀ U : List ℕ, resWord q U = wordOf (countsList q U) := by
  intro U
  induction U with
  | nil =>
      have hrep : countsList q [] = List.replicate q 0 := by
        apply List.ext_getElem <;> simp [countsList, cnt]
      rw [resWord, hrep, wordOf_replicate_zero]
  | cons o U ih =>
      rw [resWord, ih, countsList_cons q o U]
      have hlen : o % q < (countsList q U).length := by
        simp [countsList, Nat.mod_lt o hq]
      have hgetd : (countsList q U).getD (o % q) 0 = cnt q (o % q) U := by
        rw [List.getD_eq_getElem _ _ hlen]
        simp [countsList]
      rw [← hgetd, wordOf_set _ _ hlen]
      ring

/-- **The digit really is the residue count** (windows shorter than the base). -/
private theorem digit_resWord {q : ℕ} (hq : 0 < q) (U : List ℕ) (hlen : U.length < cntB)
    {c : ℕ} (hc : c < q) : digit (resWord q U) c = cnt q c U := by
  rw [digit, resWord_eq_wordOf q hq U]
  have hb : ∀ x ∈ countsList q U, x < cntB := by
    intro x hx
    simp only [countsList, List.mem_map] at hx
    obtain ⟨r, _, rfl⟩ := hx
    exact lt_of_le_of_lt List.countP_le_length hlen
  rw [wordOf_digit _ hb c]
  rw [List.getD_eq_getElem _ _ (by simpa [countsList] using hc)]
  simp [countsList]

/-- Any phase's coverage count is bounded by the clock capacity. -/
theorem countP_le_capQ {q : ℕ} (i6 : ℕ) (hq : 0 < q) (t : ℕ) (U : List ℕ)
    (hlen : U.length < cntB) :
    U.countP (coveredB q i6 t) ≤ capQ q i6 U := by
  rw [countP_coveredB_mod]
  have ht'q : t % q < q := Nat.mod_lt t hq
  have hsplit : U.countP (coveredB q i6 (t % q)) ≤
      cnt q ((t % q + i6) % q) U + cnt q ((t % q + (q - i6)) % q) U :=
    countP_or_le (fun o => o % q == (t % q + i6) % q)
      (fun o => o % q == (t % q + (q - i6)) % q) U
  have hd1 := digit_resWord hq U hlen (Nat.mod_lt (t % q + i6) hq)
  have hd2 := digit_resWord hq U hlen (Nat.mod_lt (t % q + (q - i6)) hq)
  have hfold : digit (resWord q U) ((t % q + i6) % q) +
      digit (resWord q U) ((t % q + (q - i6)) % q) ≤ capQ q i6 U := by
    simp only [capQ]
    exact fn_le_foldl_max
      (fun t' => digit (resWord q U) ((t' + i6) % q) + digit (resWord q U) ((t' + (q - i6)) % q))
      (List.range q) 0 (t % q) (List.mem_range.mpr ht'q)
  omega

/-- The early-exit fold really is the strict sum bound. -/
private theorem capLtB_sum {U : List ℕ} :
    ∀ {rem : List CoverClock} {n : ℕ}, capLtB rem n U = true →
      (rem.map fun p => capQ p.1 p.2 U).sum < n
  | [], n, h => by simpa [capLtB, Nat.blt_eq] using h
  | p :: rem, n, h => by
      simp only [capLtB, Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2⟩ := h
      have h3 := capLtB_sum h2
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem exists_false_of_countP_lt {p : ℕ → Bool} :
    ∀ {l : List ℕ}, l.countP p < l.length → ∃ o ∈ l, p o = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x xs ih =>
      intro h
      cases hx : p x with
      | false => exact ⟨x, List.mem_cons_self, hx⟩
      | true =>
          have hcount : (x :: xs).countP p = xs.countP p + 1 := by simp [hx]
          rw [hcount, List.length_cons] at h
          obtain ⟨o, ho, hpo⟩ := ih (by omega)
          exact ⟨o, List.mem_cons_of_mem _ ho, hpo⟩

/-- **Soundness of the capacity prune** (pigeonhole): if the summed exact capacities fall
    short of `|U|`, then under EVERY phase assignment some offset of `U` escapes. -/
theorem prune_sound {rem : List CoverClock} {U : List ℕ}
    (hside : ∀ p ∈ rem, 0 < p.1) (hlen : U.length < cntB)
    (h : capLtB rem U.length U = true) : Uncoverable rem U := by
  intro f
  have hsum := capLtB_sum h
  have hcap : (rem.map fun p => U.countP (coveredB p.1 p.2 (f p.1))).sum ≤
      (rem.map fun p => capQ p.1 p.2 U).sum := by
    apply List.sum_le_sum
    intro p hp
    exact countP_le_capQ p.2 (hside p hp) (f p.1) U hlen
  have hcnt : (U.countP fun o => rem.any fun p => coveredB p.1 p.2 (f p.1) o) < U.length :=
    lt_of_le_of_lt (countP_any_le f U rem) (lt_of_le_of_lt hcap hsum)
  obtain ⟨o, ho, hfalse⟩ := exists_false_of_countP_lt hcnt
  refine ⟨o, ho, fun p hp => ?_⟩
  cases hcb : coveredB p.1 p.2 (f p.1) o with
  | false => rfl
  | true =>
      have hany : (rem.any fun p => coveredB p.1 p.2 (f p.1) o) = true :=
        List.any_eq_true.mpr ⟨p, hp, hcb⟩
      have hfalse' : (rem.any fun p => coveredB p.1 p.2 (f p.1) o) = false := hfalse
      rw [hany] at hfalse'
      exact Bool.noConfusion hfalse'

/-- **Branch completeness**: a phase striking `o` is (mod `q`) one of the two phases the
    DFS tries — `t ≡ o + (q - i6)` (the `+i6` wing) or `t ≡ o + i6` (the `-i6` wing). -/
theorem branch_complete {q i6 t o : ℕ} (hi : i6 ≤ q)
    (h : coveredB q i6 t o = true) :
    t % q = (o + (q - i6)) % q ∨ t % q = (o + i6) % q := by
  simp only [coveredB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · left
    have h2 : (t + i6 + (q - i6)) % q = (o + (q - i6)) % q :=
      Nat.ModEq.add_right (q - i6) h.symm
    have h3 : t + i6 + (q - i6) = t + q := by omega
    rw [h3, Nat.add_mod_right] at h2
    exact h2
  · right
    have h2 : (t + (q - i6) + i6) % q = (o + i6) % q :=
      Nat.ModEq.add_right i6 h.symm
    have h3 : t + (q - i6) + i6 = t + q := by omega
    rw [h3, Nat.add_mod_right] at h2
    exact h2

private theorem eq_getElem_or_mem_eraseIdx {α : Type} :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length) {x : α},
      x ∈ l → x = l[i] ∨ x ∈ l.eraseIdx i
  | [], i, hi, x, hx => absurd hi (by simp)
  | a :: as, 0, _, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Or.inl rfl
      · exact Or.inr (by simpa [List.eraseIdx_cons_zero] using hx')
  | a :: as, i + 1, hi, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Or.inr (by simp [List.eraseIdx_cons_succ])
      · rcases eq_getElem_or_mem_eraseIdx as i (by simpa using hi) hx' with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simp [List.eraseIdx_cons_succ, h])

/-- **Soundness of the DFS**: a `true` answer certifies uncoverability.  Induction on the
    fuel; given an assignment `f`, either some listed clock covers the anchor `o` — then by
    `branch_complete` its phase agrees (mod `q`) with one of the two children, whose
    recursive witness survives that clock's filter and hence escapes it under `f` as well —
    or no clock covers `o`, and `o` itself witnesses. -/
theorem dfsB_sound (fuel : ℕ) : ∀ (rem : List CoverClock) (U : List ℕ),
    (∀ p ∈ rem, 0 < p.1 ∧ p.2 ≤ p.1) → U.length < cntB →
    dfsB fuel rem U = true → Uncoverable rem U := by
  induction fuel with
  | zero =>
      intro rem U hside hlen h
      simp [dfsB] at h
  | succ fuel ih =>
      intro rem U hside hlen h
      cases U with
      | nil => simp [dfsB] at h
      | cons o U' =>
          simp only [dfsB] at h
          cases hcap : capLtB rem (o :: U').length (o :: U') with
          | true => exact prune_sound (fun p hp => (hside p hp).1) hlen hcap
          | false =>
              rw [hcap, Bool.false_or] at h
              intro f
              by_cases hcov : ∃ p ∈ rem, coveredB p.1 p.2 (f p.1) o = true
              · obtain ⟨p, hp, hpc⟩ := hcov
                obtain ⟨i, hilt, hpi⟩ := List.getElem_of_mem hp
                have hall := List.all_eq_true.mp h i (List.mem_range.mpr hilt)
                have hbang : rem[i]! = p := by
                  rw [getElem!_pos rem i hilt, hpi]
                have hall' :
                    (dfsB fuel (rem.eraseIdx i)
                        (strikeFilter (rem[i]!).1 (rem[i]!).2
                          ((o + (rem[i]!).1 - (rem[i]!).2) % (rem[i]!).1) (o :: U')) &&
                      dfsB fuel (rem.eraseIdx i)
                        (strikeFilter (rem[i]!).1 (rem[i]!).2
                          ((o + (rem[i]!).2) % (rem[i]!).1) (o :: U'))) = true := hall
                rw [hbang, Bool.and_eq_true] at hall'
                obtain ⟨hA, hB⟩ := hall'
                have hside' : ∀ p' ∈ rem.eraseIdx i, 0 < p'.1 ∧ p'.2 ≤ p'.1 :=
                  fun p' hp' => hside p' ((List.eraseIdx_sublist rem i).subset hp')
                have hq0 : 0 < p.1 := (hside p hp).1
                have hiq : p.2 ≤ p.1 := (hside p hp).2
                -- the two children, keyed by the phase class of `f p.1`
                have hlen' : ∀ t : ℕ,
                    (strikeFilter p.1 p.2 t (o :: U')).length < cntB :=
                  fun t => lt_of_le_of_lt (List.length_filter_le _ _) hlen
                rcases branch_complete hiq hpc with hph | hph
                · -- `f p.1 ≡ o + (q - i6)`: child A (phase `(o + q - i6) % q`)
                  obtain ⟨o', ho'mem, ho'unc⟩ :=
                    ih (rem.eraseIdx i) _ hside' (hlen' _) hA f
                  obtain ⟨ho'U, ho'surv⟩ := List.mem_filter.mp ho'mem
                  refine ⟨o', ho'U, fun p'' hp'' => ?_⟩
                  rcases eq_getElem_or_mem_eraseIdx rem i hilt hp'' with rfl | hmem'
                  · -- p'' is the branching clock itself
                    rw [hpi]
                    have hsurv : coveredB p.1 p.2 ((o + p.1 - p.2) % p.1) o' = false := by
                      have := ho'surv
                      simpa [Bool.not_eq_true'] using this
                    have heq : (o + p.1 - p.2) % p.1 = f p.1 % p.1 := by
                      rw [hph]
                      congr 1
                      omega
                    rw [← coveredB_mod_phase p.1 p.2 (f p.1) o', ← heq]
                    exact hsurv
                  · exact ho'unc p'' hmem'
                · -- `f p.1 ≡ o + i6`: child B (phase `(o + i6) % q`)
                  obtain ⟨o', ho'mem, ho'unc⟩ :=
                    ih (rem.eraseIdx i) _ hside' (hlen' _) hB f
                  obtain ⟨ho'U, ho'surv⟩ := List.mem_filter.mp ho'mem
                  refine ⟨o', ho'U, fun p'' hp'' => ?_⟩
                  rcases eq_getElem_or_mem_eraseIdx rem i hilt hp'' with rfl | hmem'
                  · rw [hpi]
                    have hsurv : coveredB p.1 p.2 ((o + p.2) % p.1) o' = false := by
                      have := ho'surv
                      simpa [Bool.not_eq_true'] using this
                    have heq : (o + p.2) % p.1 = f p.1 % p.1 := by rw [hph]
                    rw [← coveredB_mod_phase p.1 p.2 (f p.1) o', ← heq]
                    exact hsurv
                  · exact ho'unc p'' hmem'
              · -- no listed clock covers the anchor: `o` witnesses
                refine ⟨o, List.mem_cons_self, fun p hp => ?_⟩
                cases hcb : coveredB p.1 p.2 (f p.1) o with
                | false => rfl
                | true => exact absurd ⟨p, hp, hcb⟩ hcov

/-- **Soundness of the small-clock enumeration**: instantiate each small clock at the
    phase `f q % q ∈ range q`; the recursive witness survives that clock's filter, hence
    escapes it under `f` as well (`coveredB_mod_phase`). -/
theorem enumSmall_sound :
    ∀ (smalls : List CoverClock) {bigs : List CoverClock} {U : List ℕ},
      (∀ p ∈ smalls ++ bigs, 0 < p.1 ∧ p.2 ≤ p.1) → U.length < cntB →
      enumSmallB smalls bigs U = true → Uncoverable (smalls ++ bigs) U
  | [], bigs, U, hside, hlen, h => by
      simpa using dfsB_sound (bigs.length + 1) bigs U (by simpa using hside) hlen h
  | (q, i6) :: ss, bigs, U, hside, hlen, h => by
      simp only [enumSmallB, List.all_eq_true] at h
      intro f
      have hq : 0 < q := (hside (q, i6) (by simp)).1
      have hmem : f q % q ∈ List.range q := List.mem_range.mpr (Nat.mod_lt _ hq)
      have hside' : ∀ p ∈ ss ++ bigs, 0 < p.1 ∧ p.2 ≤ p.1 := by
        intro p hp
        exact hside p (by simpa using Or.inr hp)
      have hlen' : (strikeFilter q i6 (f q % q) U).length < cntB :=
        lt_of_le_of_lt (List.length_filter_le _ _) hlen
      obtain ⟨o', ho'mem, ho'unc⟩ :=
        enumSmall_sound ss hside' hlen' (h (f q % q) hmem) f
      obtain ⟨ho'U, ho'surv⟩ := List.mem_filter.mp ho'mem
      refine ⟨o', ho'U, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · have hsurv : coveredB q i6 (f q % q) o' = false := by
          simpa [Bool.not_eq_true'] using ho'surv
        show coveredB q i6 (f q) o' = false
        rw [← coveredB_mod_phase q i6 (f q) o']
        exact hsurv
      · exact ho'unc p hp'

/-! ### Wing arithmetic: divisibility of a wing ⟺ a phase covers the offset -/

/-- `(-k) mod q` really cancels `k` mod `q`. -/
private theorem phase_cancel {q : ℕ} (k : ℕ) (hq : 0 < q) :
    ((q - k % q) % q + k) ≡ 0 [MOD q] := by
  have hmlt : k % q < q := Nat.mod_lt _ hq
  calc (q - k % q) % q + k
      ≡ (q - k % q) + k [MOD q] := Nat.ModEq.add_right k (Nat.mod_modEq _ _)
    _ ≡ (q - k % q) + k % q [MOD q] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
    _ = q := Nat.sub_add_cancel hmlt.le
    _ ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl

/-- Transport a congruence on the CENTER `k + o` to the phase form on the OFFSET `o`:
    if `k + o ≡ a (mod q)` then `o ≡ t_k + a (mod q)` for `t_k = (-k) mod q`. -/
private theorem offset_phase {q k o a : ℕ} (hq : 0 < q)
    (h : (k + o) % q = a % q) : o % q = ((q - k % q) % q + a) % q := by
  have hc : ((q - k % q) % q + k) ≡ 0 [MOD q] := phase_cancel k hq
  have h2 : (q - k % q) % q + a + k ≡ a [MOD q] := by
    calc (q - k % q) % q + a + k
        = a + ((q - k % q) % q + k) := by ring
      _ ≡ a + 0 [MOD q] := Nat.ModEq.add_left a hc
      _ = a := by ring
  have h3 : o + k ≡ (q - k % q) % q + a + k [MOD q] := by
    have ho : o + k ≡ a [MOD q] := by
      show (o + k) % q = a % q
      rw [Nat.add_comm o k]
      exact h
    exact ho.trans h2.symm
  exact Nat.ModEq.add_right_cancel' k h3

private theorem coprime_six {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) : Nat.gcd q 6 = 1 := by
  have hnd : ¬ q ∣ 6 := by
    intro hdvd
    have h6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases q
    · exact absurd hdvd (by norm_num)
    · exact absurd hq (by norm_num)
  exact hq.coprime_iff_not_dvd.mpr hnd

/-- Wing `6m - 1`: a strike forces the residue `i6`. -/
theorem dvd_wing_minus {q i6 m : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hinv : 6 * i6 % q = 1) (hm : 1 ≤ m) (hd : q ∣ 6 * m - 1) : m % q = i6 % q := by
  obtain ⟨c, hc⟩ := hd
  have h6m : 6 * m = q * c + 1 := by omega
  have e1 : 6 * m ≡ 1 [MOD q] := by
    show (6 * m) % q = 1 % q
    rw [h6m, Nat.mul_add_mod]
  have e2 : 6 * i6 ≡ 1 [MOD q] := by
    show (6 * i6) % q = 1 % q
    rw [hinv, Nat.mod_eq_of_lt (by omega)]
  exact Nat.ModEq.cancel_left_of_coprime (coprime_six hq h5) (e1.trans e2.symm)

/-- Wing `6m + 1`: a strike forces the residue `q - i6`. -/
theorem dvd_wing_plus {q i6 m : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hi : i6 < q)
    (hinv : 6 * i6 % q = 1) (hd : q ∣ 6 * m + 1) : m % q = (q - i6) % q := by
  -- `q ∣ 6 (q - i6) + 1` from `6 i6 = q d + 1`
  have hdm := Nat.div_add_mod (6 * i6) q
  rw [hinv] at hdm
  have hd2 : q ∣ 6 * (q - i6) + 1 := by
    have hX : (q - i6) + i6 = q := by omega
    have he : 6 * (q - i6) + 1 + (q * (6 * i6 / q) + 1) = 6 * q + 1 := by
      have h6 : 6 * (q - i6) + 6 * i6 = 6 * q := by omega
      omega
    have he2 : 6 * (q - i6) + 1 = 6 * q - q * (6 * i6 / q) := by omega
    rw [he2]
    exact Nat.dvd_sub (Dvd.intro 6 (by ring)) (Dvd.intro _ rfl)
  have e1 : 6 * m + 1 ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hd
  have e2 : 6 * (q - i6) + 1 ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hd2
  have e3 : 6 * m ≡ 6 * (q - i6) [MOD q] :=
    Nat.ModEq.add_right_cancel' 1 (e1.trans e2.symm)
  exact Nat.ModEq.cancel_left_of_coprime (coprime_six hq h5) e3

/-! ### The bridge: UNSAT phase cover ⟹ the gap bound -/

/-- **THE BRIDGE.**  An uncoverability certificate for the offsets `1 … g` over a clock
    list carrying every prime of `[5, A]` yields the gap bound `CleanGapBound A g`: an
    arbitrary window start `k` induces the assignment `f q = (-k) mod q`; the uncovered
    offset `o` has both wings of `k + o` free of every listed clock (`dvd_wing_*` +
    `offset_phase` would otherwise cover `o`), and the clocks `2, 3` never strike wings
    (`omega`). -/
theorem cleanGapBound_of_unsatCover {A g : ℕ} {C : List CoverClock}
    (hsc : ∀ p ∈ C, p.1.Prime ∧ 5 ≤ p.1 ∧ p.1 ≤ A ∧ p.2 < p.1 ∧ 6 * p.2 % p.1 = 1)
    (hcov : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∈ C.map Prod.fst)
    (hU : Uncoverable C (List.range' 1 g)) : CleanGapBound A g := by
  intro k
  obtain ⟨o, homem, hounc⟩ := hU fun q => (q - k % q) % q
  obtain ⟨ho1, ho2⟩ := List.mem_range'_1.mp homem
  refine ⟨k + o, by omega, by omega, ?_⟩
  intro q hq hqA hor
  rcases Nat.lt_or_ge q 5 with h5 | h5
  · have h2 := hq.two_le
    interval_cases q
    · rcases hor with hd | hd <;> omega
    · rcases hor with hd | hd <;> omega
    · exact absurd hq (by norm_num)
  · obtain ⟨p, hpmem, hpq⟩ := List.mem_map.mp (hcov q hq h5 hqA)
    obtain ⟨hqp, h5p, hAp, hip, hinvp⟩ := hsc p hpmem
    have hcb := hounc p hpmem
    rw [hpq] at hqp h5p hAp hip hinvp hcb
    simp only [coveredB, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hcb
    obtain ⟨hcb1, hcb2⟩ := hcb
    have hq0 : 0 < q := by omega
    rcases hor with hd | hd
    · exact hcb1 (offset_phase hq0 (dvd_wing_minus hqp h5p hinvp (by omega) hd))
    · exact hcb2 (offset_phase hq0 (dvd_wing_plus hqp h5p hip hinvp hd))

/-! ### The SAT side: a struck run refutes the shorter window -/

/-- A verified run of `len` consecutive struck centers `r+1 … r+len` refutes
    `CleanGapBound A len` (the window `(r, r+len]` has no clean center). -/
theorem not_cleanGapBound_of_struck {A r len : ℕ} {C : List CoverClock}
    (hsc : ∀ p ∈ C, p.1.Prime ∧ p.1 ≤ A)
    (h : allStruckB C r len = true) : ¬ CleanGapBound A len := by
  intro hb
  obtain ⟨m, h1, h2, hclean⟩ := hb r
  have hj : m - (r + 1) < len := by omega
  have hall := List.all_eq_true.mp h (m - (r + 1)) (List.mem_range.mpr hj)
  have hall' :
      (C.any fun p =>
        ((6 * (r + 1 + (m - (r + 1))) - 1) % p.1 == 0) ||
          ((6 * (r + 1 + (m - (r + 1))) + 1) % p.1 == 0)) = true := hall
  have hm : r + 1 + (m - (r + 1)) = m := by omega
  rw [hm] at hall'
  obtain ⟨p, hp, hstrike⟩ := List.any_eq_true.mp hall'
  obtain ⟨hpr, hpA⟩ := hsc p hp
  rw [Bool.or_eq_true] at hstrike
  rcases hstrike with hs | hs
  · exact hclean p.1 hpr hpA (Or.inl (Nat.dvd_of_mod_eq_zero (by simpa using hs)))
  · exact hclean p.1 hpr hpA (Or.inr (Nat.dvd_of_mod_eq_zero (by simpa using hs)))

/-! ### The clock tables (`i6 = 6⁻¹ mod q`) -/

/-- The small clocks, fully enumerated (`5 · 7 · 11 · 13 = 5005` phase tuples). -/
def smallClocks : List CoverClock := [(5, 1), (7, 6), (11, 2), (13, 11)]

def bigs17 : List CoverClock := [(17, 3)]
def bigs19 : List CoverClock := [(19, 16), (17, 3)]
def bigs23 : List CoverClock := [(23, 4), (19, 16), (17, 3)]
def bigs29 : List CoverClock := [(29, 5), (23, 4), (19, 16), (17, 3)]
def bigs31 : List CoverClock := [(31, 26), (29, 5), (23, 4), (19, 16), (17, 3)]
def bigs37 : List CoverClock := [(37, 31), (31, 26), (29, 5), (23, 4), (19, 16), (17, 3)]

/-- Assemble the gap bound at a scale from the kernel UNSAT gate (`decide +kernel` on
    `enumSmallB`) and the two `decide`-level side conditions. -/
theorem cleanGapBound_of_gate {A g : ℕ} (smalls bigs : List CoverClock)
    (hsc : ∀ p ∈ smalls ++ bigs,
      p.1.Prime ∧ 5 ≤ p.1 ∧ p.1 ≤ A ∧ p.2 < p.1 ∧ 6 * p.2 % p.1 = 1)
    (hcov : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∈ (smalls ++ bigs).map Prod.fst)
    (hg : g < cntB)
    (hgate : enumSmallB smalls bigs (List.range' 1 g) = true) : CleanGapBound A g :=
  cleanGapBound_of_unsatCover hsc hcov
    (enumSmall_sound smalls
      (fun p hp =>
        ⟨by have := (hsc p hp).2.1; omega, by have := (hsc p hp).2.2.2.1; omega⟩)
      (by simpa using hg)
      hgate)

/-- Peel one small clock: per-phase chunk certificates glue to the full enumeration.
    This is the chunk split that keeps every kernel gate inside the 300 s / 8 GB
    per-theorem budget at the big scales (measured: a `w ≈ 6·10⁵` chunk peaks ≈ 7.6 GB). -/
theorem enumSmall_cons_of_parts {q i6 : ℕ} {ss bigs : List CoverClock} {U : List ℕ}
    (h : ∀ t, t < q → enumSmallB ss bigs (strikeFilter q i6 t U) = true) :
    enumSmallB ((q, i6) :: ss) bigs U = true := by
  simp only [enumSmallB, List.all_eq_true]
  intro t ht
  exact h t (List.mem_range.mp ht)

/-! ### The gate ladder

STRICT order `17 → 19 → 23 → 29 → 31 → 37`; every `decide +kernel` obligation sits inside
the 300 s / 8 GB per-theorem budget (scales `23+` are split into per-phase chunks of the
small-clock enumeration and glued back by `enumSmall_cons_of_parts` — the documented
fallback, applied after the single-theorem `A = 19` gate measured 8.1 GB peak RSS).
Representative kernel measurements (32 GB reference machine, Lean v4.31):
`unsatCover_17` ≈ 13 s whole-gate; `A = 19` t₅-chunks ≈ 6 s each; the heaviest chunks of
the ladder — `unsat31_t0_0` ≈ 21 s / 6.9 GB, `unsat37_t2_1` ≈ 24 s / 7.6 GB. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- UNSAT phase cover at `A = 17`, `g = G(17) = 18`. -/
theorem unsatCover_17 : enumSmallB smallClocks bigs17 (List.range' 1 18) = true := by
  decide +kernel

/-- **The TRUE gap at 17**: `G(17) = 18 ≤ 18` on all of ℕ. -/
theorem cleanGapBound_17 : CleanGapBound 17 18 := by
  refine cleanGapBound_of_gate smallClocks bigs17 (by decide) ?_
    (by norm_num [cntB]) unsatCover_17
  intro q hq h5 hA
  interval_cases q <;> first
    | decide
    | exact absurd hq (by norm_num)

/-! ### Scale 17 — exactness and the sharp instance -/

set_option maxRecDepth 100000 in
/-- SAT witness at 17 (`r = 117`, period scan, re-verified by trial division —
    `tools/phase_cover_run1.log`): the 17 centers `r+1 … r+17` are all struck. -/
theorem allStruck_17 : allStruckB (smallClocks ++ bigs17) 117 17 = true := by
  decide +kernel

/-- **Exactness at 17**: `G(17) = 18` — the bound holds at 18 (kernel UNSAT
    cover) and fails at 17 (kernel SAT run). -/
theorem gapExact_17 : CleanGapBound 17 18 ∧ ¬ CleanGapBound 17 17 :=
  ⟨cleanGapBound_17, not_cleanGapBound_of_struck (by decide) allStruck_17⟩

/-- Sharp-wall instance at 17: `G(17) = 18 ≤ ⌊17²/14⌋ = 20`. -/
theorem twinJacobsthalSharp_at_17 : CleanGapBound 17 (17 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_17 (by norm_num)

/-! ### Scale 19 — the gate, the true gap, exactness, the wall instances -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat19_t0 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs19 (strikeFilter 5 1 0 (List.range' 1 25)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat19_t1 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs19 (strikeFilter 5 1 1 (List.range' 1 25)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat19_t2 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs19 (strikeFilter 5 1 2 (List.range' 1 25)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat19_t3 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs19 (strikeFilter 5 1 3 (List.range' 1 25)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat19_t4 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs19 (strikeFilter 5 1 4 (List.range' 1 25)) = true := by
  decide +kernel

/-- UNSAT phase cover at `A = 19`, `g = G(19) = 25`, glued from the 5 per-phase kernel chunks. -/
theorem unsatCover_19 : enumSmallB smallClocks bigs19 (List.range' 1 25) = true := by
  show enumSmallB ((5, 1) :: [(7, 6), (11, 2), (13, 11)]) bigs19 (List.range' 1 25) = true
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat19_t0
  · exact unsat19_t1
  · exact unsat19_t2
  · exact unsat19_t3
  · exact unsat19_t4

/-- **The TRUE gap at 19**: `CleanGapBound 19 25` on all of ℕ. -/
theorem cleanGapBound_19 : CleanGapBound 19 25 := by
  refine cleanGapBound_of_gate smallClocks bigs19 (by decide) ?_
    (by norm_num [cntB]) unsatCover_19
  intro q hq h5 hA
  interval_cases q <;> first
    | decide
    | exact absurd hq (by norm_num)

set_option maxRecDepth 100000 in
/-- SAT witness at 19 (`r = 110`, period scan, re-verified by trial division —
    `tools/phase_cover_run1.log`): the 24 centers `r+1 … r+24` are all struck. -/
theorem allStruck_19 : allStruckB (smallClocks ++ bigs19) 110 24 = true := by
  decide +kernel

/-- **Exactness at 19**: `G(19) = 25` — the bound holds at 25 (kernel UNSAT
    cover) and fails at 24 (kernel SAT run). -/
theorem gapExact_19 : CleanGapBound 19 25 ∧ ¬ CleanGapBound 19 24 :=
  ⟨cleanGapBound_19, not_cleanGapBound_of_struck (by decide) allStruck_19⟩

/-- Sharp-wall instance at 19: `G(19) = 25 ≤ ⌊19²/14⌋ = 25` (TIGHT — the sharp constant is exact here). -/
theorem twinJacobsthalSharp_at_19 : CleanGapBound 19 (19 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_19 (by norm_num)

/-! ### Scale 23 — the gate, the true gap, exactness, the wall instances -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat23_t0 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs23 (strikeFilter 5 1 0 (List.range' 1 34)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat23_t1 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs23 (strikeFilter 5 1 1 (List.range' 1 34)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat23_t2 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs23 (strikeFilter 5 1 2 (List.range' 1 34)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat23_t3 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs23 (strikeFilter 5 1 3 (List.range' 1 34)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat23_t4 :
    enumSmallB [(7, 6), (11, 2), (13, 11)] bigs23 (strikeFilter 5 1 4 (List.range' 1 34)) = true := by
  decide +kernel

/-- UNSAT phase cover at `A = 23`, `g = G(23) = 34`, glued from the 5 per-phase kernel chunks. -/
theorem unsatCover_23 : enumSmallB smallClocks bigs23 (List.range' 1 34) = true := by
  show enumSmallB ((5, 1) :: [(7, 6), (11, 2), (13, 11)]) bigs23 (List.range' 1 34) = true
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat23_t0
  · exact unsat23_t1
  · exact unsat23_t2
  · exact unsat23_t3
  · exact unsat23_t4

/-- **The TRUE gap at 23**: `CleanGapBound 23 34` on all of ℕ. -/
theorem cleanGapBound_23 : CleanGapBound 23 34 := by
  refine cleanGapBound_of_gate smallClocks bigs23 (by decide) ?_
    (by norm_num [cntB]) unsatCover_23
  intro q hq h5 hA
  interval_cases q <;> first
    | decide
    | exact absurd hq (by norm_num)

set_option maxRecDepth 100000 in
/-- SAT witness at 23 (`r = 12694428`, solver certificate, re-verified by trial division —
    `tools/phase_cover_run1.log`): the 33 centers `r+1 … r+33` are all struck. -/
theorem allStruck_23 : allStruckB (smallClocks ++ bigs23) 12694428 33 = true := by
  decide +kernel

/-- **Exactness at 23**: `G(23) = 34` — the bound holds at 34 (kernel UNSAT
    cover) and fails at 33 (kernel SAT run). -/
theorem gapExact_23 : CleanGapBound 23 34 ∧ ¬ CleanGapBound 23 33 :=
  ⟨cleanGapBound_23, not_cleanGapBound_of_struck (by decide) allStruck_23⟩

/-- The wall instance at 23 (first proof beyond any period certificate reach):
    `G(23) = 34 ≤ ⌊23²/7⌋ = 75`. -/
theorem twinJacobsthal_at_23 : CleanGapBound 23 (23 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_23 (by norm_num)

/-- Sharp-wall instance at 23: `G(23) = 34 ≤ ⌊23²/14⌋ = 37`. -/
theorem twinJacobsthalSharp_at_23 : CleanGapBound 23 (23 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_23 (by norm_num)

/-! ### Scale 29 — the gate, the true gap, exactness, the wall instances -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_0 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 0 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_1 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 1 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_2 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_3 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 3 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_4 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 4 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_5 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 5 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t0_6 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 6 (strikeFilter 5 1 0 (List.range' 1 43))) = true := by
  decide +kernel

private theorem unsat29_t0 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs29 (strikeFilter 5 1 0 (List.range' 1 43)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat29_t0_0
  · exact unsat29_t0_1
  · exact unsat29_t0_2
  · exact unsat29_t0_3
  · exact unsat29_t0_4
  · exact unsat29_t0_5
  · exact unsat29_t0_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_0 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 0 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_1 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 1 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_2 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 2 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_3 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 3 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_4 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 4 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_5 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 5 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t1_6 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 6 (strikeFilter 5 1 1 (List.range' 1 43))) = true := by
  decide +kernel

private theorem unsat29_t1 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs29 (strikeFilter 5 1 1 (List.range' 1 43)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat29_t1_0
  · exact unsat29_t1_1
  · exact unsat29_t1_2
  · exact unsat29_t1_3
  · exact unsat29_t1_4
  · exact unsat29_t1_5
  · exact unsat29_t1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_0 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 0 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_1 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 1 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_2 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 2 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_3 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 3 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_4 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 4 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_5 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 5 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t2_6 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 6 (strikeFilter 5 1 2 (List.range' 1 43))) = true := by
  decide +kernel

private theorem unsat29_t2 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs29 (strikeFilter 5 1 2 (List.range' 1 43)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat29_t2_0
  · exact unsat29_t2_1
  · exact unsat29_t2_2
  · exact unsat29_t2_3
  · exact unsat29_t2_4
  · exact unsat29_t2_5
  · exact unsat29_t2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_0 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 0 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_1 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 1 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_2 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 2 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_3 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 3 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_4 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 4 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_5 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 5 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t3_6 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 6 (strikeFilter 5 1 3 (List.range' 1 43))) = true := by
  decide +kernel

private theorem unsat29_t3 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs29 (strikeFilter 5 1 3 (List.range' 1 43)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat29_t3_0
  · exact unsat29_t3_1
  · exact unsat29_t3_2
  · exact unsat29_t3_3
  · exact unsat29_t3_4
  · exact unsat29_t3_5
  · exact unsat29_t3_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_0 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 0 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_1 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_2 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 2 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_3 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 3 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_4 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 4 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_5 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 5 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat29_t4_6 :
    enumSmallB [(11, 2), (13, 11)] bigs29
      (strikeFilter 7 6 6 (strikeFilter 5 1 4 (List.range' 1 43))) = true := by
  decide +kernel

private theorem unsat29_t4 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs29 (strikeFilter 5 1 4 (List.range' 1 43)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat29_t4_0
  · exact unsat29_t4_1
  · exact unsat29_t4_2
  · exact unsat29_t4_3
  · exact unsat29_t4_4
  · exact unsat29_t4_5
  · exact unsat29_t4_6

/-- UNSAT phase cover at `A = 29`, `g = G(29) = 43`, glued from the 35 per-phase kernel chunks. -/
theorem unsatCover_29 : enumSmallB smallClocks bigs29 (List.range' 1 43) = true := by
  show enumSmallB ((5, 1) :: [(7, 6), (11, 2), (13, 11)]) bigs29 (List.range' 1 43) = true
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat29_t0
  · exact unsat29_t1
  · exact unsat29_t2
  · exact unsat29_t3
  · exact unsat29_t4

/-- **The TRUE gap at 29**: `CleanGapBound 29 43` on all of ℕ. -/
theorem cleanGapBound_29 : CleanGapBound 29 43 := by
  refine cleanGapBound_of_gate smallClocks bigs29 (by decide) ?_
    (by norm_num [cntB]) unsatCover_29
  intro q hq h5 hA
  interval_cases q <;> first
    | decide
    | exact absurd hq (by norm_num)

set_option maxRecDepth 100000 in
/-- SAT witness at 29 (`r = 200906185`, solver certificate, re-verified by trial division —
    `tools/phase_cover_run1.log`): the 42 centers `r+1 … r+42` are all struck. -/
theorem allStruck_29 : allStruckB (smallClocks ++ bigs29) 200906185 42 = true := by
  decide +kernel

/-- **Exactness at 29**: `G(29) = 43` — the bound holds at 43 (kernel UNSAT
    cover) and fails at 42 (kernel SAT run). -/
theorem gapExact_29 : CleanGapBound 29 43 ∧ ¬ CleanGapBound 29 42 :=
  ⟨cleanGapBound_29, not_cleanGapBound_of_struck (by decide) allStruck_29⟩

/-- The wall instance at 29 (first proof beyond any period certificate reach):
    `G(29) = 43 ≤ ⌊29²/7⌋ = 120`. -/
theorem twinJacobsthal_at_29 : CleanGapBound 29 (29 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_29 (by norm_num)

/-- Sharp-wall instance at 29: `G(29) = 43 ≤ ⌊29²/14⌋ = 60`. -/
theorem twinJacobsthalSharp_at_29 : CleanGapBound 29 (29 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_29 (by norm_num)

/-! ### Scale 31 — the gate, the true gap, exactness, the wall instances -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_0 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 0 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_1 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 1 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s0 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 0 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s1 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 1 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s2 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 2 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s3 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 3 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s4 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 4 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s5 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 5 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s6 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 6 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s7 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 7 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s8 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 8 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s9 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 9 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_2_s10 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 10 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58)))) = true := by
  decide +kernel

private theorem unsat31_t0_2 :
    enumSmallB ((11, 2) :: [(13, 11)]) bigs31 (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t0_2_s0
  · exact unsat31_t0_2_s1
  · exact unsat31_t0_2_s2
  · exact unsat31_t0_2_s3
  · exact unsat31_t0_2_s4
  · exact unsat31_t0_2_s5
  · exact unsat31_t0_2_s6
  · exact unsat31_t0_2_s7
  · exact unsat31_t0_2_s8
  · exact unsat31_t0_2_s9
  · exact unsat31_t0_2_s10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_3 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 3 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_4 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 4 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_5 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 5 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t0_6 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 6 (strikeFilter 5 1 0 (List.range' 1 58))) = true := by
  decide +kernel

private theorem unsat31_t0 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs31 (strikeFilter 5 1 0 (List.range' 1 58)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t0_0
  · exact unsat31_t0_1
  · exact unsat31_t0_2
  · exact unsat31_t0_3
  · exact unsat31_t0_4
  · exact unsat31_t0_5
  · exact unsat31_t0_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_0 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 0 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_1 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 1 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_2 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 2 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_3 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 3 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_4 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 4 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_5 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 5 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t1_6 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 6 (strikeFilter 5 1 1 (List.range' 1 58))) = true := by
  decide +kernel

private theorem unsat31_t1 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs31 (strikeFilter 5 1 1 (List.range' 1 58)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t1_0
  · exact unsat31_t1_1
  · exact unsat31_t1_2
  · exact unsat31_t1_3
  · exact unsat31_t1_4
  · exact unsat31_t1_5
  · exact unsat31_t1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_0 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 0 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_1 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 1 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_2 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 2 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_3 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 3 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_4 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 4 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_5 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 5 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t2_6 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 6 (strikeFilter 5 1 2 (List.range' 1 58))) = true := by
  decide +kernel

private theorem unsat31_t2 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs31 (strikeFilter 5 1 2 (List.range' 1 58)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t2_0
  · exact unsat31_t2_1
  · exact unsat31_t2_2
  · exact unsat31_t2_3
  · exact unsat31_t2_4
  · exact unsat31_t2_5
  · exact unsat31_t2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_0 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 0 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_1 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 1 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_2 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 2 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_3 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 3 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_4 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 4 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_5 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 5 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t3_6 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 6 (strikeFilter 5 1 3 (List.range' 1 58))) = true := by
  decide +kernel

private theorem unsat31_t3 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs31 (strikeFilter 5 1 3 (List.range' 1 58)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t3_0
  · exact unsat31_t3_1
  · exact unsat31_t3_2
  · exact unsat31_t3_3
  · exact unsat31_t3_4
  · exact unsat31_t3_5
  · exact unsat31_t3_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_0 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 0 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s0 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 0 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s1 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 1 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s2 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 2 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s3 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 3 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s4 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 4 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s5 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 5 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s6 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 6 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s7 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 7 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s8 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 8 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s9 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 9 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_1_s10 :
    enumSmallB [(13, 11)] bigs31
      (strikeFilter 11 2 10 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58)))) = true := by
  decide +kernel

private theorem unsat31_t4_1 :
    enumSmallB ((11, 2) :: [(13, 11)]) bigs31 (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t4_1_s0
  · exact unsat31_t4_1_s1
  · exact unsat31_t4_1_s2
  · exact unsat31_t4_1_s3
  · exact unsat31_t4_1_s4
  · exact unsat31_t4_1_s5
  · exact unsat31_t4_1_s6
  · exact unsat31_t4_1_s7
  · exact unsat31_t4_1_s8
  · exact unsat31_t4_1_s9
  · exact unsat31_t4_1_s10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_2 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 2 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_3 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 3 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_4 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 4 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_5 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 5 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat31_t4_6 :
    enumSmallB [(11, 2), (13, 11)] bigs31
      (strikeFilter 7 6 6 (strikeFilter 5 1 4 (List.range' 1 58))) = true := by
  decide +kernel

private theorem unsat31_t4 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs31 (strikeFilter 5 1 4 (List.range' 1 58)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t4_0
  · exact unsat31_t4_1
  · exact unsat31_t4_2
  · exact unsat31_t4_3
  · exact unsat31_t4_4
  · exact unsat31_t4_5
  · exact unsat31_t4_6

/-- UNSAT phase cover at `A = 31`, `g = G(31) = 58`, glued from the 55 per-phase kernel chunks. -/
theorem unsatCover_31 : enumSmallB smallClocks bigs31 (List.range' 1 58) = true := by
  show enumSmallB ((5, 1) :: [(7, 6), (11, 2), (13, 11)]) bigs31 (List.range' 1 58) = true
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat31_t0
  · exact unsat31_t1
  · exact unsat31_t2
  · exact unsat31_t3
  · exact unsat31_t4

/-- **The TRUE gap at 31**: `CleanGapBound 31 58` on all of ℕ. -/
theorem cleanGapBound_31 : CleanGapBound 31 58 := by
  refine cleanGapBound_of_gate smallClocks bigs31 (by decide) ?_
    (by norm_num [cntB]) unsatCover_31
  intro q hq h5 hA
  interval_cases q <;> first
    | decide
    | exact absurd hq (by norm_num)

set_option maxRecDepth 100000 in
/-- SAT witness at 31 (`r = 21844264615`, solver certificate, re-verified by trial division —
    `tools/phase_cover_run1.log`): the 57 centers `r+1 … r+57` are all struck. -/
theorem allStruck_31 : allStruckB (smallClocks ++ bigs31) 21844264615 57 = true := by
  decide +kernel

/-- **Exactness at 31**: `G(31) = 58` — the bound holds at 58 (kernel UNSAT
    cover) and fails at 57 (kernel SAT run). -/
theorem gapExact_31 : CleanGapBound 31 58 ∧ ¬ CleanGapBound 31 57 :=
  ⟨cleanGapBound_31, not_cleanGapBound_of_struck (by decide) allStruck_31⟩

/-- The wall instance at 31 (first proof beyond any period certificate reach):
    `G(31) = 58 ≤ ⌊31²/7⌋ = 137`. -/
theorem twinJacobsthal_at_31 : CleanGapBound 31 (31 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_31 (by norm_num)

/-- Sharp-wall instance at 31: `G(31) = 58 ≤ ⌊31²/14⌋ = 68`. -/
theorem twinJacobsthalSharp_at_31 : CleanGapBound 31 (31 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_31 (by norm_num)

/-! ### Scale 37 — the gate, the true gap, exactness, the wall instances -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_0 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 0 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_1 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 1 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_2 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 2 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_3 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 3 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_4 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 4 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_5 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 5 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t0_6 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 6 (strikeFilter 5 1 0 (List.range' 1 88))) = true := by
  decide +kernel

private theorem unsat37_t0 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs37 (strikeFilter 5 1 0 (List.range' 1 88)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat37_t0_0
  · exact unsat37_t0_1
  · exact unsat37_t0_2
  · exact unsat37_t0_3
  · exact unsat37_t0_4
  · exact unsat37_t0_5
  · exact unsat37_t0_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_0 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 0 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_1 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 1 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_2 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 2 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_3 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 3 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_4 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 4 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_5 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 5 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t1_6 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 6 (strikeFilter 5 1 1 (List.range' 1 88))) = true := by
  decide +kernel

private theorem unsat37_t1 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs37 (strikeFilter 5 1 1 (List.range' 1 88)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat37_t1_0
  · exact unsat37_t1_1
  · exact unsat37_t1_2
  · exact unsat37_t1_3
  · exact unsat37_t1_4
  · exact unsat37_t1_5
  · exact unsat37_t1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_0 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 0 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_1 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 1 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_2 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 2 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_3 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 3 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_4 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 4 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_5 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 5 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t2_6 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 6 (strikeFilter 5 1 2 (List.range' 1 88))) = true := by
  decide +kernel

private theorem unsat37_t2 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs37 (strikeFilter 5 1 2 (List.range' 1 88)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat37_t2_0
  · exact unsat37_t2_1
  · exact unsat37_t2_2
  · exact unsat37_t2_3
  · exact unsat37_t2_4
  · exact unsat37_t2_5
  · exact unsat37_t2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_0 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 0 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_1 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 1 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_2 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 2 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_3 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 3 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_4 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 4 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_5 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 5 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t3_6 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 6 (strikeFilter 5 1 3 (List.range' 1 88))) = true := by
  decide +kernel

private theorem unsat37_t3 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs37 (strikeFilter 5 1 3 (List.range' 1 88)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat37_t3_0
  · exact unsat37_t3_1
  · exact unsat37_t3_2
  · exact unsat37_t3_3
  · exact unsat37_t3_4
  · exact unsat37_t3_5
  · exact unsat37_t3_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_0 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 0 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_1 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 1 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_2 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 2 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_3 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 3 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_4 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 4 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_5 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 5 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem unsat37_t4_6 :
    enumSmallB [(11, 2), (13, 11)] bigs37
      (strikeFilter 7 6 6 (strikeFilter 5 1 4 (List.range' 1 88))) = true := by
  decide +kernel

private theorem unsat37_t4 :
    enumSmallB ((7, 6) :: [(11, 2), (13, 11)]) bigs37 (strikeFilter 5 1 4 (List.range' 1 88)) = true := by
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat37_t4_0
  · exact unsat37_t4_1
  · exact unsat37_t4_2
  · exact unsat37_t4_3
  · exact unsat37_t4_4
  · exact unsat37_t4_5
  · exact unsat37_t4_6

/-- UNSAT phase cover at `A = 37`, `g = G(37) = 88`, glued from the 35 per-phase kernel chunks. -/
theorem unsatCover_37 : enumSmallB smallClocks bigs37 (List.range' 1 88) = true := by
  show enumSmallB ((5, 1) :: [(7, 6), (11, 2), (13, 11)]) bigs37 (List.range' 1 88) = true
  refine enumSmall_cons_of_parts ?_
  intro t ht
  interval_cases t
  · exact unsat37_t0
  · exact unsat37_t1
  · exact unsat37_t2
  · exact unsat37_t3
  · exact unsat37_t4

/-- **The TRUE gap at 37**: `CleanGapBound 37 88` on all of ℕ. -/
theorem cleanGapBound_37 : CleanGapBound 37 88 := by
  refine cleanGapBound_of_gate smallClocks bigs37 (by decide) ?_
    (by norm_num [cntB]) unsatCover_37
  intro q hq h5 hA
  interval_cases q <;> first
    | decide
    | exact absurd hq (by norm_num)

set_option maxRecDepth 100000 in
/-- SAT witness at 37 (`r = 1145973108145`, solver certificate, re-verified by trial division —
    `tools/phase_cover_run1.log`): the 87 centers `r+1 … r+87` are all struck. -/
theorem allStruck_37 : allStruckB (smallClocks ++ bigs37) 1145973108145 87 = true := by
  decide +kernel

/-- **Exactness at 37**: `G(37) = 88` — the bound holds at 88 (kernel UNSAT
    cover) and fails at 87 (kernel SAT run). -/
theorem gapExact_37 : CleanGapBound 37 88 ∧ ¬ CleanGapBound 37 87 :=
  ⟨cleanGapBound_37, not_cleanGapBound_of_struck (by decide) allStruck_37⟩

/-- The wall instance at 37 (first proof beyond any period certificate reach):
    `G(37) = 88 ≤ ⌊37²/7⌋ = 195`. -/
theorem twinJacobsthal_at_37 : CleanGapBound 37 (37 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_37 (by norm_num)

/-- Sharp-wall instance at 37: `G(37) = 88 ≤ ⌊37²/14⌋ = 97`. -/
theorem twinJacobsthalSharp_at_37 : CleanGapBound 37 (37 ^ 2 / 14) :=
  cleanGapBound_mono cleanGapBound_37 (by norm_num)

/-!
### Axiom audit (performed against the built module from a scratch file outside the repo)

    #print axioms unsatCover_17            -- [propext]
    #print axioms unsatCover_19 … 37       -- [propext, Quot.sound]
    #print axioms allStruck_17 … 37        -- do not depend on any axioms
    #print axioms enumSmall_sound          -- [propext, Classical.choice, Quot.sound]
    #print axioms cleanGapBound_of_unsatCover
                                           -- [propext, Classical.choice, Quot.sound]
    #print axioms not_cleanGapBound_of_struck  -- [propext, Quot.sound]
    #print axioms cleanGapBound_17 … 37    -- [propext, Classical.choice, Quot.sound]
    #print axioms gapExact_17 … 37         -- [propext, Classical.choice, Quot.sound]
    #print axioms twinJacobsthal_at_23 … 37, twinJacobsthalSharp_at_17 … 37
                                           -- [propext, Classical.choice, Quot.sound]

`decide +kernel` adds NO axioms: the six SAT gates are axiom-FREE, the UNSAT gates carry
at most `propext`/`Quot.sound` (from the chunk-glue `simp` lemmas), and every Prop-level
result stays inside the standard triple.  No `sorryAx`, no `Lean.ofReduceBool` /
`Lean.trustCompiler` (`native_decide` is not used anywhere in this file), no
`step00FirstCause`.

### Measured budget ledger (32 GB reference machine, Lean v4.31)

Full module build: **1024 s wall, peak lean RSS 14.4 GB** (lake checks chunk gates
concurrently; each individual obligation stays inside the 300 s / 8 GB per-theorem
budget — heaviest standalone chunks: `unsat37_t2_1` 24 s net / 7.6 GB peak,
`unsat31_t0_0` 21 s net / 6.9 GB peak).  For comparison, the period-bound witness chain
at `A = 19` (`Step00WitnessChainKernel`) costs 2–4 min / 23 GB for ONE scale; the whole
six-scale ladder here costs 17 min / 14 GB — and `P_37 ≈ 1.29 · 10¹²` is six orders of
magnitude beyond any period certificate.
-/

end PhaseCoverKernel
end EuclidsPath
