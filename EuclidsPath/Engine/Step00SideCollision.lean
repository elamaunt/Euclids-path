import EuclidsPath.Engine.Step00WitnessChainKernel

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Side-collision kernel census — the L62 wing-side collision law as an exact machine law

Kernel escalation of the ledger-L62 WING-SIDE COLLISION LAW (escalation candidate C-A of the
pratt-wing campaign; harness twin: `tools/pratt_wing_harness.py` stage `sidepgf`, log
`tools/pratt_wing_run1.log`).  The campaign measured the ω-excess of the shifted wing values
`p ∓ 1` of twin wings over isolated primes: `+0.1535` at `10⁷` (z ≈ +64 per cell) and
`+0.1504` at the `10⁹` window — matching the PRE-derived E4/L34 reference
`Σ_{q≥5} (1/(q−2) − 1/(q−1)) ≈ +0.1539` (all `q ≤ 10⁵`; the `B = 31` truncation
`+0.147425` is what the campaign registration printed).  This file freezes the truncated
`B ∈ {7, 13}` layer of that law into `decide`-gated kernel censuses over the SAME full
periods `35` and `5005` as the L34 competition law and the `periodCert_13` wall certificate
(`Step00TwinJacobsthalWall`).

## The five residue classes per clock

For a prime clock `q ≥ 5` with `i6 = 6⁻¹ mod q`, the frame values at center `m` are struck
as follows: the center `6m` at `m ≡ 0`; the wings `6m − 1` / `6m + 1` at `m ≡ i6` / `−i6`;
the OUTER SIDES `6m − 2` / `6m + 2` at `m ≡ 2·i6` / `−2·i6` (side-L: `q ∣ 6m − 2 ⟺
6m ≡ 2 ⟺ m ≡ 2·i6`; side-R mirrored).  The five classes `{0, ±i6, ±2·i6}` are pairwise
distinct for every prime `q ≥ 5` (`2·i6 = i6` would force `i6 ≡ 0`, `2·i6 = −i6` would
force `3·i6 ≡ 0`, i.e. `q = 3`); at `q = 5` they EXACTLY fill `ℤ/5` (`i6 = 1`, classes
`{0, 1, 4, 2, 3}`).  Kernel instances: `sideClass_distinct_5/7/11/13`.

## The two conditionings and the exact census law

* TWIN-CLASS: `m` avoids `{±i6}` mod every clock (both wings clean at `B` — `q − 2`
  admissible classes per clock); the side-L class `2·i6` is one of them (the `Nodup` of
  the frame lemma) ⟹ conditional side-hit probability `1/(q−2)` per clock.
* CLEAN-at-B (single wing): `m` avoids `{i6}` only (left wing `6m − 1` clean — `q − 1`
  classes); side-hit probability `1/(q−1)` per clock.

Over a full period the classes at distinct clocks are CRT-independent, so the histogram of
the side-L hit count `j = #{q : q ∣ 6m − 2}` is EXACTLY the coefficient list of the pgf
numerator `∏_q ((q−3) + x)` (twin-class) resp. `∏_q ((q−2) + x)` (clean-at-B):

* `twin_side_pgf_B7`   — `B = 7`, period 35: `(2+x)(4+x)` → `[8, 6, 1]`, total `15 = 3·5`;
* `twin_side_pgf_B13`  — `B = 13`, period 5005: `(2+x)(4+x)(8+x)(10+x)` →
  `[640, 624, 196, 24, 1]`, total `1485 = 3·5·9·11` — THE L34 kernel constant
  (`twin_total_eq_L34` welds this module to the L34 competition law);
* `clean_side_pgf_B13` — `(3+x)(5+x)(9+x)(11+x)` → `[1485, 1092, 274, 28, 1]`, total
  `2880 = 4·6·10·12` (`clean_total_2880`);
* `pgfNum` / `mulLin` + `…_census_eq_pgf_…` — the pgf-product identities as machine
  equalities on the coefficient lists (the L34-lineage face);
* `countAux_card_Icc` + `twinSideCountB_card` — the one-directional spec bridge: the fused
  Nat folds equal `Finset.card` of the filtered ranges `{m ∈ [1, P] : …}` (house Bool/Nat
  fold discipline); pinned instances `twin_side_card_B13_j0 … j4`, `twin_class_card_B13`;
* `twinClass_clean_13` — wall-vocabulary weld: a twin-class survivor of the B13 census IS
  a `Clean 13` center (through `clean_of_cleanListB`; `twinClassB` is literally the house
  `cleanListB`, `twinClassB_eq_cleanListB : … = … := rfl`);
* `side_collision_mean_excess_B13` — THE FRACTION COROLLARY: mean side-L hits, twin-class
  minus clean-at-B, `= 1092/1485 − 1728/2880 = 364/495 − 3/5 = 67/495`, machine-tied to
  the two census gates; `side_reference_B13` pins
  `67/495 = Σ_{q ∈ {5,7,11,13}} (1/(q−2) − 1/(q−1))` — the pre-derived L62 reference
  truncated to `B = 13`.

## MANDATORY disclosures (read before quoting this file)

* **The conditioning is CLASS-exact, NOT primality.**  "Twin-class" means mod-`q`
  admissibility of BOTH wings for the clocks `q ≤ B` (the survivor classes of the sieve);
  "clean-at-B" means one-wing admissibility.  NOTHING here conditions on actual primality
  or isolation of the wings.  The measured L62 law lives on prime-conditioned populations;
  what is proved here is its truncated CLASS layer — the disclosed caveat of ledger
  L62(a), machine-frozen.
* **Truncation remainder.**  The `B = 13` truncation gives `67/495 ≈ 0.13535` against the
  measured `+0.1535` (10⁷) / `+0.1504` (10⁹) and the full reference `≈ 0.1539`; the tail
  `Σ_{q > 13} (1/(q−2) − 1/(q−1)) ≈ 0.0185` is the disclosed remainder — the kernel layer
  freezes the `B ≤ 13` truncation ONLY.
* **This law does NOT feed the wall.**  It is a collision/competition statement in the
  L34/L35 family (per-clock class splitting and its exact pgf); it carries NO
  window-ensemble structure — no gap bound, no survivor forcing, no parity leverage.
  The wall (`TwinJacobsthalBound` and its costumes) is untouched.

## Kernel notes

Everything in the decide path is ℕ/Bool (house discipline — no `Finset`, no `ZMod`, no
`Decidable` beyond literal equality on fold outputs): `twinClassB` / `cleanLeftB` are
single `List.all` passes (two / one `%` per clock), `sideHits` a single `foldr`, and the
histogram census `censusAux` one fuel-driven pass over `m ∈ [1, P]` bumping one histogram
entry per survivor (`cond`, not `if`, in the fold — Bool-native reduction).  The `B = 13`
gates are 5005 iterations × ~20 Nat-ops; the `periodCert_13` precedent (same period,
heavier per-center work) sits comfortably inside the 300 s / 8 GB gates.  Measured
timings and the axiom audit are in the block at the end of this file.
-/

namespace EuclidsPath
namespace SideCollision

open EuclidsPath.CleanGraph
open EuclidsPath.WitnessChainKernel

/-! ### The five side classes per clock (frame lemma) -/

/-- `SideClassesDistinct q i`: `i` inverts `6` mod `q`, and the five frame classes
    `{0, i, −i, 2i, −2i}` (center, wing-L, wing-R, side-L, side-R; represented in `[0, q)`)
    are pairwise distinct.  The `Nodup` in particular places the side-L class `2·i6`
    OUTSIDE the twin-killed pair `{±i6}`: side-L is one of the `q − 2` twin-admissible
    classes, which is what makes the twin-class side-hit probability `1/(q−2)`. -/
def SideClassesDistinct (q i : ℕ) : Prop :=
  6 * i % q = 1 ∧ ([0, i, q - i, 2 * i % q, q - 2 * i % q] : List ℕ).Nodup

instance sideClassesDistinctDecidable (q i : ℕ) : Decidable (SideClassesDistinct q i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `q = 5`, `i6 = 1`: classes `{0, 1, 4, 2, 3}` — the five classes EXACTLY fill `ℤ/5`
    (honest check at the smallest clock: `q − 2 = 3` twin-admissible classes remain, and
    side-L `= 2` is among them). -/
theorem sideClass_distinct_5 : SideClassesDistinct 5 1 := by decide

/-- `q = 7`, `i6 = 6`: classes `{0, 6, 1, 5, 2}`. -/
theorem sideClass_distinct_7 : SideClassesDistinct 7 6 := by decide

/-- `q = 11`, `i6 = 2`: classes `{0, 2, 9, 4, 7}`. -/
theorem sideClass_distinct_11 : SideClassesDistinct 11 2 := by decide

/-- `q = 13`, `i6 = 11`: classes `{0, 11, 2, 9, 4}`. -/
theorem sideClass_distinct_13 : SideClassesDistinct 13 11 := by decide

/-! ### The fused census folds (ℕ/Bool decide path) -/

/-- Twin-CLASS survival at center `m` over the clock list `qs`: BOTH wings `6m ∓ 1` clear
    every clock (mod-`q` admissibility — NOT primality; see the module disclosures).
    Literally the house `cleanListB` fold (`twinClassB_eq_cleanListB`). -/
def twinClassB (qs : List ℕ) (m : ℕ) : Bool :=
  qs.all fun q => (!((6 * m - 1) % q == 0)) && (!((6 * m + 1) % q == 0))

/-- The named weld to the house checker: `twinClassB` IS `cleanListB`. -/
theorem twinClassB_eq_cleanListB (qs : List ℕ) (m : ℕ) :
    twinClassB qs m = cleanListB qs m := rfl

/-- CLEAN-at-B single-wing survival: the LEFT wing `6m − 1` clears every clock
    (`q − 1` admissible classes per clock — the isolated-side conditioning of L62(a)). -/
def cleanLeftB (qs : List ℕ) (m : ℕ) : Bool :=
  qs.all fun q => !((6 * m - 1) % q == 0)

/-- Side-L hit count: `#{q ∈ qs : q ∣ 6m − 2}` (one `foldr` pass). -/
def sideHits (qs : List ℕ) (m : ℕ) : ℕ :=
  qs.foldr (fun q n => cond ((6 * m - 2) % q == 0) (n + 1) n) 0

/-- The hit count never exceeds the clock count (so the `qs.length + 1`-entry histogram
    below never drops a bump). -/
theorem sideHits_le (qs : List ℕ) (m : ℕ) : sideHits qs m ≤ qs.length := by
  induction qs with
  | nil => simp [sideHits]
  | cons q t ih =>
    have hstep : sideHits (q :: t) m =
        cond ((6 * m - 2) % q == 0) (sideHits t m + 1) (sideHits t m) := rfl
    rw [hstep]
    cases (6 * m - 2) % q == 0 <;> simp <;> omega

/-- Bump entry `j` of a histogram (out-of-range bumps are dropped; the census instances
    never reach that case — `sideHits_le`). -/
def bump : List ℕ → ℕ → List ℕ
  | [], _ => []
  | c :: t, 0 => (c + 1) :: t
  | c :: t, j + 1 => c :: bump t j

/-- The fused census fold: scan `fuel` centers upward from `m`, bumping the `hit` entry of
    the histogram for every `surv`-survivor — ONE pass, everything ℕ/Bool. -/
def censusAux (surv : ℕ → Bool) (hit : ℕ → ℕ) : List ℕ → ℕ → ℕ → List ℕ
  | h, _, 0 => h
  | h, m, fuel + 1 => censusAux surv hit (cond (surv m) (bump h (hit m)) h) (m + 1) fuel

/-- Twin-class side-L histogram over the centers `m ∈ [1, P]`. -/
def sideCensusB (qs : List ℕ) (P : ℕ) : List ℕ :=
  censusAux (twinClassB qs) (sideHits qs) (List.replicate (qs.length + 1) 0) 1 P

/-- Clean-at-B (left wing) side-L histogram over the centers `m ∈ [1, P]`. -/
def cleanSideCensusB (qs : List ℕ) (P : ℕ) : List ℕ :=
  censusAux (cleanLeftB qs) (sideHits qs) (List.replicate (qs.length + 1) 0) 1 P

/-! ### The kernel census gates -/

/-- **`B = 7` twin-class census (period 35)**: side-L hits over `q ∈ {5, 7}` distribute as
    the coefficients of `(2+x)(4+x)` — counts `(8, 6, 1)`, total `15 = 3·5` (L34). -/
theorem twin_side_pgf_B7 : sideCensusB [5, 7] 35 = [8, 6, 1] := by decide

set_option maxRecDepth 100000 in
/-- **`B = 13` twin-class census (period 5005 — the `periodCert_13` period)**: side-L hits
    over `q ∈ {5, 7, 11, 13}` distribute as the coefficients of `(2+x)(4+x)(8+x)(10+x)` —
    counts `(640, 624, 196, 24, 1)`, total `1485 = 3·5·9·11`, THE L34 kernel constant. -/
theorem twin_side_pgf_B13 :
    sideCensusB [5, 7, 11, 13] 5005 = [640, 624, 196, 24, 1] := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`B = 13` clean-at-B census (left wing clean)**: coefficients of
    `(3+x)(5+x)(9+x)(11+x)` — counts `(1485, 1092, 274, 28, 1)`, total `2880 = 4·6·10·12`. -/
theorem clean_side_pgf_B13 :
    cleanSideCensusB [5, 7, 11, 13] 5005 = [1485, 1092, 274, 28, 1] := by decide +kernel

/-! ### The pgf-product identities (the L34-lineage face) -/

/-- Coefficients of `(a + x) · h(x)` from the coefficient list `h` (low degree first):
    entry `k` of the product is `a·h_k + h_{k−1}`. -/
def mulLin (a : ℕ) (h : List ℕ) : List ℕ :=
  List.zipWith (· + ·) (h.map (a * ·) ++ [0]) (0 :: h)

/-- Coefficient list of `∏_{a ∈ as} (a + x)` (elementary-symmetric convolution). -/
def pgfNum (as : List ℕ) : List ℕ := as.foldr mulLin [1]

theorem twin_pgf_product_B7 : pgfNum [2, 4] = [8, 6, 1] := by decide

theorem twin_pgf_product_B13 : pgfNum [2, 4, 8, 10] = [640, 624, 196, 24, 1] := by decide

theorem clean_pgf_product_B13 : pgfNum [3, 5, 9, 11] = [1485, 1092, 274, 28, 1] := by decide

/-- The census IS the pgf numerator `∏ ((q−3) + x)`, `B = 7`. -/
theorem twin_census_eq_pgf_B7 : sideCensusB [5, 7] 35 = pgfNum [2, 4] := by
  rw [twin_side_pgf_B7, twin_pgf_product_B7]

/-- The census IS the pgf numerator `∏ ((q−3) + x)`, `B = 13`. -/
theorem twin_census_eq_pgf_B13 :
    sideCensusB [5, 7, 11, 13] 5005 = pgfNum [2, 4, 8, 10] := by
  rw [twin_side_pgf_B13, twin_pgf_product_B13]

/-- The clean-at-B census IS the pgf numerator `∏ ((q−2) + x)`, `B = 13`. -/
theorem clean_census_eq_pgf_B13 :
    cleanSideCensusB [5, 7, 11, 13] 5005 = pgfNum [3, 5, 9, 11] := by
  rw [clean_side_pgf_B13, clean_pgf_product_B13]

/-- **The L34 weld**: the twin-class survivor total at `B = 13` is `1485 = 3·5·9·11` —
    the exact kernel constant of the L34 competition law (`#{m ∈ [1, 5005] : both wings
    d₁₃ = 0} = 1485`), reproduced here as the histogram mass. -/
theorem twin_total_eq_L34 : (sideCensusB [5, 7, 11, 13] 5005).sum = 3 * 5 * 9 * 11 := by
  rw [twin_side_pgf_B13]; rfl

/-- The clean-at-B total: `2880 = 4·6·10·12 = ∏ (q−1)`. -/
theorem clean_total_2880 : (cleanSideCensusB [5, 7, 11, 13] 5005).sum = 4 * 6 * 10 * 12 := by
  rw [clean_side_pgf_B13]; rfl

/-! ### The one-directional spec bridge (fold → `Finset.card`) -/

/-- Fused per-predicate counter over `[m, m + fuel)`, peeling from the top (the top peel
    aligns the induction with `Finset.range_succ` / the `Icc` insert step). -/
def countAux (p : ℕ → Bool) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => countAux p m fuel + (if p (m + fuel) = true then 1 else 0)

/-- **Spec bridge, `[1, n]` form**: the Nat fold counts exactly the filtered-interval
    cardinality `#{m ∈ [1, n] : p m}`. -/
theorem countAux_card_Icc (p : ℕ → Bool) :
    ∀ n : ℕ, countAux p 1 n = ((Finset.Icc 1 n).filter (fun m => p m = true)).card := by
  intro n
  induction n with
  | zero => simp [countAux]
  | succ n ih =>
    have hins : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (n + 1) ∉ (Finset.Icc 1 n).filter (fun m => p m = true) := by
      simp [Finset.mem_filter, Finset.mem_Icc]
    have harg : 1 + n = n + 1 := by omega
    rw [countAux, ih, hins, Finset.filter_insert, harg]
    by_cases h : p (n + 1) = true
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem hnot]
    · rw [if_neg h, if_neg h]; omega

/-- Per-`j` fused counter for the twin-class census over `m ∈ [1, n]`. -/
def twinSideCountB (qs : List ℕ) (n j : ℕ) : ℕ :=
  countAux (fun m => twinClassB qs m && (sideHits qs m == j)) 1 n

/-- Fused counter for the twin-class survivor total over `m ∈ [1, n]`. -/
def twinClassCountB (qs : List ℕ) (n : ℕ) : ℕ :=
  countAux (fun m => twinClassB qs m) 1 n

/-- **The spec bridge for the twin census**: the fused per-`j` count IS the cardinality of
    `{m ∈ [1, n] : m twin-class survivor with exactly j side-L hits}`. -/
theorem twinSideCountB_card (qs : List ℕ) (n j : ℕ) :
    twinSideCountB qs n j = ((Finset.Icc 1 n).filter
      (fun m => twinClassB qs m = true ∧ sideHits qs m = j)).card := by
  rw [twinSideCountB, countAux_card_Icc]
  exact congrArg Finset.card (Finset.filter_congr fun m _ => by
    simp [Bool.and_eq_true, beq_iff_eq])

/-- The survivor-total bridge. -/
theorem twinClassCountB_card (qs : List ℕ) (n : ℕ) :
    twinClassCountB qs n =
      ((Finset.Icc 1 n).filter (fun m => twinClassB qs m = true)).card :=
  countAux_card_Icc _ n

set_option maxRecDepth 100000 in
/-- `#{m ∈ [1, 5005] : twin-class, 0 side-L hits} = 640` (Prop-level, via the bridge). -/
theorem twin_side_card_B13_j0 :
    ((Finset.Icc 1 5005).filter (fun m => twinClassB [5, 7, 11, 13] m = true ∧
      sideHits [5, 7, 11, 13] m = 0)).card = 640 := by
  rw [← twinSideCountB_card]; decide +kernel

set_option maxRecDepth 100000 in
/-- `#{m ∈ [1, 5005] : twin-class, 1 side-L hit} = 624`. -/
theorem twin_side_card_B13_j1 :
    ((Finset.Icc 1 5005).filter (fun m => twinClassB [5, 7, 11, 13] m = true ∧
      sideHits [5, 7, 11, 13] m = 1)).card = 624 := by
  rw [← twinSideCountB_card]; decide +kernel

set_option maxRecDepth 100000 in
/-- `#{m ∈ [1, 5005] : twin-class, 2 side-L hits} = 196`. -/
theorem twin_side_card_B13_j2 :
    ((Finset.Icc 1 5005).filter (fun m => twinClassB [5, 7, 11, 13] m = true ∧
      sideHits [5, 7, 11, 13] m = 2)).card = 196 := by
  rw [← twinSideCountB_card]; decide +kernel

set_option maxRecDepth 100000 in
/-- `#{m ∈ [1, 5005] : twin-class, 3 side-L hits} = 24`. -/
theorem twin_side_card_B13_j3 :
    ((Finset.Icc 1 5005).filter (fun m => twinClassB [5, 7, 11, 13] m = true ∧
      sideHits [5, 7, 11, 13] m = 3)).card = 24 := by
  rw [← twinSideCountB_card]; decide +kernel

set_option maxRecDepth 100000 in
/-- `#{m ∈ [1, 5005] : twin-class, 4 side-L hits} = 1` — the unique full-collision class
    (`m ≡ 2·i6` mod all four clocks simultaneously, CRT). -/
theorem twin_side_card_B13_j4 :
    ((Finset.Icc 1 5005).filter (fun m => twinClassB [5, 7, 11, 13] m = true ∧
      sideHits [5, 7, 11, 13] m = 4)).card = 1 := by
  rw [← twinSideCountB_card]; decide +kernel

set_option maxRecDepth 100000 in
/-- `#{m ∈ [1, 5005] : twin-class survivor} = 1485` — the L34 kernel constant as a
    `Finset.card` statement (the Prop face of `twin_total_eq_L34`). -/
theorem twin_class_card_B13 :
    ((Finset.Icc 1 5005).filter
      (fun m => twinClassB [5, 7, 11, 13] m = true)).card = 1485 := by
  rw [← twinClassCountB_card]; decide +kernel

/-- **Wall-vocabulary weld** (one direction — the checker discipline): a twin-class
    survivor of the B13 census is a `Clean 13` center, the survivor notion of the
    `periodCert_13` wall certificate over the same period 5005. -/
theorem twinClass_clean_13 {m : ℕ} (hm : 1 ≤ m)
    (h : twinClassB [5, 7, 11, 13] m = true) : Clean 13 m := by
  refine clean_of_cleanListB hm ?_ h
  intro q hq h5 hqA
  interval_cases q
  · exact List.mem_cons_self ..
  · exact absurd hq (by norm_num)
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact absurd hq (by norm_num)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))

/-! ### The Fraction corollary (the exact L62-a excess, truncated `B = 13`) -/

/-- First-moment numerator `Σ_j j · h_j` of a histogram. -/
def moment1 (h : List ℕ) : ℕ := (List.zipWith (· * ·) (List.range h.length) h).sum

/-- **THE FRACTION COROLLARY — the exact machine law of ledger L62(a), truncated
    `B = 13`.**  Mean side-L hits under twin-CLASS conditioning minus under clean-at-B
    conditioning, both read off the kernel censuses:
    `1092/1485 − 1728/2880 = 364/495 − 3/5 = 67/495 ≈ 0.13535` — against the measured
    `+0.1535` (10⁷) / `+0.1504` (10⁹); the tail `Σ_{q>13} ≈ 0.0185` is the disclosed
    truncation remainder. -/
theorem side_collision_mean_excess_B13 :
    (moment1 (sideCensusB [5, 7, 11, 13] 5005) : ℚ) /
        ((sideCensusB [5, 7, 11, 13] 5005).sum : ℚ) -
      (moment1 (cleanSideCensusB [5, 7, 11, 13] 5005) : ℚ) /
        ((cleanSideCensusB [5, 7, 11, 13] 5005).sum : ℚ) = 67 / 495 := by
  have h1 : moment1 [640, 624, 196, 24, 1] = 1092 := by rfl
  have h2 : moment1 [1485, 1092, 274, 28, 1] = 1728 := by rfl
  have h3 : ([640, 624, 196, 24, 1] : List ℕ).sum = 1485 := by rfl
  have h4 : ([1485, 1092, 274, 28, 1] : List ℕ).sum = 2880 := by rfl
  rw [twin_side_pgf_B13, clean_side_pgf_B13, h1, h2, h3, h4]
  norm_num

/-- **The pre-derived L62 reference at `B = 13`**: the per-clock excesses sum to the same
    fraction, `Σ_{q ∈ {5,7,11,13}} (1/(q−2) − 1/(q−1)) = 67/495` — the collision law and
    its reference agree EXACTLY at the truncation (the `q > 13` tail is the disclosed
    remainder). -/
theorem side_reference_B13 :
    (1 / 3 - 1 / 4) + (1 / 5 - 1 / 6) + (1 / 9 - 1 / 10) + (1 / 11 - 1 / 12)
      = (67 / 495 : ℚ) := by norm_num

/-!
### Axiom audit (performed against the built module from a scratch file outside the repo)

    #print axioms sideClass_distinct_5/7/11/13     -- does not depend on any axioms
    #print axioms twinClassB_eq_cleanListB         -- does not depend on any axioms
    #print axioms twin_side_pgf_B7                 -- does not depend on any axioms
    #print axioms twin_side_pgf_B13                -- does not depend on any axioms
    #print axioms clean_side_pgf_B13               -- does not depend on any axioms
    #print axioms twin_pgf_product_B7/B13, clean_pgf_product_B13
                                                   -- does not depend on any axioms
    #print axioms twin_census_eq_pgf_B7/B13, clean_census_eq_pgf_B13
                                                   -- does not depend on any axioms
    #print axioms twin_total_eq_L34                -- [propext]
    #print axioms clean_total_2880                 -- [propext]
    #print axioms sideHits_le                      -- [propext, Classical.choice, Quot.sound]
    #print axioms countAux_card_Icc                -- [propext, Classical.choice, Quot.sound]
    #print axioms twinSideCountB_card              -- [propext, Classical.choice, Quot.sound]
    #print axioms twinClassCountB_card             -- [propext, Classical.choice, Quot.sound]
    #print axioms twin_side_card_B13_j0 … j4       -- [propext, Classical.choice, Quot.sound]
    #print axioms twin_class_card_B13              -- [propext, Classical.choice, Quot.sound]
    #print axioms twinClass_clean_13               -- [propext, Classical.choice, Quot.sound]
    #print axioms side_collision_mean_excess_B13   -- [propext, Classical.choice, Quot.sound]
    #print axioms side_reference_B13               -- [propext, Classical.choice, Quot.sound]

The three census gates and every pgf identity are axiom-FREE pure kernel computation
(`decide` / `decide +kernel` — no `native_decide`, no `Lean.ofReduceBool`, no new axioms
anywhere).  The Prop-level bridge and the ℚ corollary carry only the standard mathlib
triple.  No `sorryAx`; the module does not touch `step00FirstCause`.

Measured decide budgets (`-Dprofiler=true`, this machine): the eight 5005-iteration
kernel gates (`twin_side_pgf_B13`, `clean_side_pgf_B13`, `twin_side_card_B13_j0…j4`,
`twin_class_card_B13`) type-check at 1.3–2.0 s EACH; `twin_side_pgf_B7` and every other
declaration are below the 0.2 s profiler threshold; whole file 27 s including 5 s of
imports — two orders of magnitude inside the 300 s / 8 GB gates.
-/

end SideCollision
end EuclidsPath
