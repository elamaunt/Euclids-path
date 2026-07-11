import EuclidsPath.Engine.Step00GraveDepthKernel

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Twin-chain completeness census — ALL twin centers on `[1, 10⁴]`, both directions

The repo's FIRST two-directional kernel certificate.  Every kernel census so far
(`Step00WitnessChainKernel`, `Step00GraveDepthKernel`, `Step00PhaseCoverKernel`) consumed
only the SOUNDNESS direction of its Bool checker: a passing fold certified that the listed
objects are what they claim to be, and said nothing about objects NOT on the list.  This
file closes both directions on one finite range: the 810-entry list `twinList10k` contains
every twin center `m ∈ [1, 10⁴]` AND nothing else —

    twinList_complete_10000 : ∀ m, 1 ≤ m → m ≤ 10000 → (TwinCenterZ m ↔ m ∈ twinList10k).

* `witB` / `killB` — the compositeness certificates: one explicit factor witness per
  clock-surviving non-twin (2158 of them), one small-clock kill for the rest (7032);
* `twinSegB` — the fused two-list walk over `n` consecutive centers: twin head ⟹ `twinB`,
  else witness head ⟹ `witB`, else `killB`; terminal case demands FULL consumption;
* `twinSegB_spec` — the two-directional soundness (one induction on the fuel): every
  listed center is in range and IS a twin, every center in range is a twin IFF listed;
* `twinSeg_chunk_1 … _10` — the kernel data gates (`decide +kernel`, 1000 centers each,
  clock list `[5, 7, 11, 13]`, wings up to `60001`, witness factors up to `239`);
* `twinList_complete_10000` / `twinList_range` — the assembled census;
* `maxGap_twinList10k` / `twin_in_every_83_window` / `twin_gap_83_attained` — the gap
  geometry pinned by the census: max consecutive twin-center gap on `[1, 10⁴]` is
  EXACTLY 83 (after `m = 4070`, next twin `4153`), and every window `(k, k + 83]`
  with `k + 83 ≤ 10000` contains a twin center.

## Kernel note — why the completeness direction is cheap

The forward direction (listed ⟹ twin) pays the usual `primeB` ladder price (two
fuel-driven odd trial divisions per twin, wings ≤ 60001, `⌊√60001⌋ = 244`).  The NEW
direction (unlisted ⟹ not a twin) needs NO primality test at all: a single nontrivial
divisor `1 < d <` wing kills that wing's primality (`not_prime_of_dvd`, five lines off
`Nat.Prime.eq_one_or_self_of_dvd`).  The clock kill needs no primality of the clock
either — only `2 ≤ q`, a side condition on the LIST, checked once by `decide`.  This is
why 9190 non-twins cost less kernel work than 810 twins (measured: the whole ten-chunk
census ≈ 7 s of kernel time; calibration chunk 5 = 0.66 s net).

## MANDATORY anti-vocabulary (read before quoting this file)

* **Finite-range facts ONLY.**  Every statement here dies at `N = 10⁴`.  Nothing in this
  file says or hints that ANY twin center exists above `10⁴` — `twinList_complete_10000`
  is silent there, `twin_in_every_83_window` is silent there, and the census cannot be
  extrapolated.
* **This does NOT say twins are infinite.**  A complete finite census is compatible with
  the twin set being finite; completeness on `[1, 10⁴]` adds ZERO evidence either way.
* **No density claim.**  810/10⁴ is a count, not a density statement, and no statement
  here bounds counts on any other interval.
* **The gap pin is range-local.**  `maxGap = 83` holds for consecutive twin centers
  inside `[1, 10⁴]` only; gaps grow past any bound at scale (RANGE-LOCAL maximum, not a
  law).  The window theorem needs `k + 83 ≤ 10000` — dropping that hypothesis is exactly
  the twin prime conjecture and is NOT proved here.
* **The census is a certificate, not evidence.**  It re-verifies known finite data at
  kernel trust; it is an instrument (the first two-directional one), not an argument.
* **What IS new here, honestly:** the two-directional shape itself — every twin found AND
  everything found is a twin — with the completeness direction resting on the
  kill/witness side (a divisor kills a wing), NOT on completeness of any primality test
  (`primeB` completeness is never used, only `primeB_prime` soundness through `twinB`).
-/

namespace EuclidsPath
namespace TwinChainCensus

open EuclidsPath.Residuals
open EuclidsPath.GraveDepthKernel

/-! ### The fused Bool checkers -/

/-- The clock list at `B = 13`: the small primes whose divisibility kills most non-twin
    centers (measured kill-scan average 1.70 clocks with early exit). -/
def clock13 : List ℕ := [5, 7, 11, 13]

/-- Factor witness check at center `m`: `(p, side)` certifies compositeness of one wing,
    `side = true` for the `6m - 1` wing, `side = false` for `6m + 1`.  A nontrivial
    divisor `1 < p <` wing kills that wing's primality — no primality of `p` needed. -/
def witB (m : ℕ) : ℕ × Bool → Bool
  | (p, true) => Nat.blt 1 p && Nat.blt p (6 * m - 1) && ((6 * m - 1) % p == 0)
  | (p, false) => Nat.blt 1 p && Nat.blt p (6 * m + 1) && ((6 * m + 1) % p == 0)

/-- Small-clock kill: some `q` in the clock list divides a wing with `q <` wing.
    The guard `Nat.blt q` wing keeps the divisor nontrivial from above; nontriviality
    from below (`2 ≤ q`) is a side condition on the clock list, not re-checked here. -/
def killB (qs : List ℕ) (m : ℕ) : Bool :=
  qs.any fun q =>
    ((6 * m - 1) % q == 0 && Nat.blt q (6 * m - 1)) ||
      ((6 * m + 1) % q == 0 && Nat.blt q (6 * m + 1))

/-- The fused two-list census walk: `twinSegB qs m n twins wits` visits the `n` centers
    `m, m + 1, …, m + n - 1` in order, consuming the sorted twin list and the sorted
    witness list.  Twin head match ⟹ `twinB`; otherwise witness head match ⟹ `witB`;
    otherwise the clock kill must fire.  Terminal case: BOTH lists fully consumed.
    Structural recursion on the fuel `n` with inner list matches (the `chainB` shape —
    the kernel unfolds it literally). -/
def twinSegB (qs : List ℕ) : ℕ → ℕ → List ℕ → List (ℕ × ℕ × Bool) → Bool
  | _, 0, twins, wits => twins.isEmpty && wits.isEmpty
  | m, n + 1, twins, wits =>
    match twins with
    | t :: ts =>
      cond (t == m)
        (twinB m && twinSegB qs (m + 1) n ts wits)
        (match wits with
          | (mw, p, s) :: ws =>
            cond (mw == m)
              (witB m (p, s) && twinSegB qs (m + 1) n (t :: ts) ws)
              (killB qs m && twinSegB qs (m + 1) n (t :: ts) ((mw, p, s) :: ws))
          | [] => killB qs m && twinSegB qs (m + 1) n (t :: ts) [])
    | [] =>
      match wits with
      | (mw, p, s) :: ws =>
        cond (mw == m)
          (witB m (p, s) && twinSegB qs (m + 1) n [] ws)
          (killB qs m && twinSegB qs (m + 1) n [] ((mw, p, s) :: ws))
      | [] => killB qs m && twinSegB qs (m + 1) n [] []

/-! ### Soundness of the compositeness certificates -/

/-- A nontrivial divisor `1 < d < w` kills primality of `w`. -/
private theorem not_prime_of_dvd {d w : ℕ} (h1 : 1 < d) (h2 : d < w) (hd : d ∣ w) :
    ¬ w.Prime := fun hp => by
  rcases hp.eq_one_or_self_of_dvd d hd with h | h <;> omega

/-- A passing factor witness refutes `TwinCenterZ m` (the certified wing is composite). -/
private theorem witB_not_twin {m p : ℕ} {s : Bool} (h : witB m (p, s) = true) :
    ¬ TwinCenterZ m := by
  intro htw
  cases s with
  | true =>
    simp only [witB, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
    exact not_prime_of_dvd h.1.1 h.1.2 (Nat.dvd_of_mod_eq_zero h.2) htw.1
  | false =>
    simp only [witB, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
    exact not_prime_of_dvd h.1.1 h.1.2 (Nat.dvd_of_mod_eq_zero h.2) htw.2

/-- A passing clock kill refutes `TwinCenterZ m`.  NOTE: no primality of the clock is
    needed — ANY nontrivial divisor kills a wing; the only side condition is `2 ≤ q`. -/
private theorem killB_not_twin {qs : List ℕ} (hqs : ∀ q ∈ qs, 2 ≤ q) {m : ℕ}
    (h : killB qs m = true) : ¬ TwinCenterZ m := by
  intro htw
  simp only [killB, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    Nat.blt_eq, beq_iff_eq] at h
  obtain ⟨q, hqmem, hq⟩ := h
  have h2 : 2 ≤ q := hqs q hqmem
  rcases hq with ⟨hmod, hlt⟩ | ⟨hmod, hlt⟩
  · exact not_prime_of_dvd (by omega) hlt (Nat.dvd_of_mod_eq_zero hmod) htw.1
  · exact not_prime_of_dvd (by omega) hlt (Nat.dvd_of_mod_eq_zero hmod) htw.2

/-- `cond` eliminators (definitional; keep the spec proof free of simp-name roulette). -/
private theorem cond_true_elim {c a b : Bool} (h : cond c a b = true) (hc : c = true) :
    a = true := by subst hc; exact h

private theorem cond_false_elim {c a b : Bool} (h : cond c a b = true) (hc : c = false) :
    b = true := by subst hc; exact h

/-! ### The two-directional spec — one induction on the fuel -/

/-- Step lemma, twin case: the head `m` is consumed, the tail census shifts by one. -/
private theorem spec_step_twin {n m : ℕ} {ts : List ℕ} (htw : TwinCenterZ m)
    (ih1 : ∀ x ∈ ts, ∃ j, j < n ∧ x = (m + 1) + j)
    (ih2 : ∀ j, j < n → (TwinCenterZ ((m + 1) + j) ↔ ((m + 1) + j) ∈ ts)) :
    (∀ x ∈ m :: ts, ∃ j, j < n + 1 ∧ x = m + j) ∧
    (∀ j, j < n + 1 → (TwinCenterZ (m + j) ↔ (m + j) ∈ m :: ts)) := by
  constructor
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨j, hj, rfl⟩ := ih1 x hx'
      exact ⟨j + 1, by omega, by omega⟩
  · intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨fun _ => List.mem_cons_self, fun _ => htw⟩
    | succ j =>
      have harith : m + (j + 1) = (m + 1) + j := by omega
      rw [harith, List.mem_cons, ih2 j (by omega)]
      constructor
      · exact Or.inr
      · rintro (heq | hmem)
        · exact absurd heq (by omega)
        · exact hmem

/-- Step lemma, non-twin case: the twin list passes through unchanged; part 1 of the
    IH localizes it above `m`, so `m` itself cannot be a member. -/
private theorem spec_step_nonTwin {n m : ℕ} {twins : List ℕ} (hnt : ¬ TwinCenterZ m)
    (ih1 : ∀ x ∈ twins, ∃ j, j < n ∧ x = (m + 1) + j)
    (ih2 : ∀ j, j < n → (TwinCenterZ ((m + 1) + j) ↔ ((m + 1) + j) ∈ twins)) :
    (∀ x ∈ twins, ∃ j, j < n + 1 ∧ x = m + j) ∧
    (∀ j, j < n + 1 → (TwinCenterZ (m + j) ↔ (m + j) ∈ twins)) := by
  constructor
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := ih1 x hx
    exact ⟨j + 1, by omega, by omega⟩
  · intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      constructor
      · exact fun htw => absurd htw hnt
      · intro hmem
        obtain ⟨j, hj', heq⟩ := ih1 m hmem
        exact absurd heq (by omega)
    | succ j =>
      have harith : m + (j + 1) = (m + 1) + j := by omega
      rw [harith]
      exact ih2 j (by omega)

/-- **Two-directional soundness of `twinSegB`** — the module's heart.  A passing walk over
    `n` centers starting at `m` certifies BOTH directions at once:

    1. every listed twin center lies in the visited window `[m, m + n)`;
    2. for EVERY center in the window: it is a twin center IFF it is listed.

    Induction on the fuel; the twin branch uses `twinB_twin` (forward soundness at
    `j = 0`), the kill/witness branches use `witB_not_twin` / `killB_not_twin` (a
    nontrivial divisor kills a wing), and part 1 localizes the remaining twin list above
    `m` so that membership splits cleanly.  Only `2 ≤ q` is required of the clock list. -/
theorem twinSegB_spec {qs : List ℕ} (hqs : ∀ q ∈ qs, 2 ≤ q) :
    ∀ {n m : ℕ} {twins : List ℕ} {wits : List (ℕ × ℕ × Bool)},
      twinSegB qs m n twins wits = true →
      (∀ x ∈ twins, ∃ j, j < n ∧ x = m + j) ∧
      (∀ j, j < n → (TwinCenterZ (m + j) ↔ (m + j) ∈ twins)) := by
  intro n
  induction n with
  | zero =>
    intro m twins wits h
    cases twins with
    | nil => exact ⟨by simp, fun j hj => absurd hj (by omega)⟩
    | cons t ts => simp [twinSegB] at h
  | succ n ih =>
    intro m twins wits h
    cases twins with
    | cons t ts =>
      rcases wits with _ | ⟨⟨mw, p, s⟩, ws⟩
      · -- no witnesses left: twin head or clock kill
        simp only [twinSegB] at h
        cases htm : (t == m) with
        | true =>
          replace h := cond_true_elim h htm
          simp only [Bool.and_eq_true] at h
          obtain ⟨ih1, ih2⟩ := ih h.2
          have ht : t = m := by simpa using htm
          subst ht
          exact spec_step_twin (twinB_twin h.1) ih1 ih2
        | false =>
          replace h := cond_false_elim h htm
          simp only [Bool.and_eq_true] at h
          obtain ⟨ih1, ih2⟩ := ih h.2
          exact spec_step_nonTwin (killB_not_twin hqs h.1) ih1 ih2
      · -- twin head, else witness head, else clock kill
        simp only [twinSegB] at h
        cases htm : (t == m) with
        | true =>
          replace h := cond_true_elim h htm
          simp only [Bool.and_eq_true] at h
          obtain ⟨ih1, ih2⟩ := ih h.2
          have ht : t = m := by simpa using htm
          subst ht
          exact spec_step_twin (twinB_twin h.1) ih1 ih2
        | false =>
          replace h := cond_false_elim h htm
          cases hmw : (mw == m) with
          | true =>
            replace h := cond_true_elim h hmw
            simp only [Bool.and_eq_true] at h
            obtain ⟨ih1, ih2⟩ := ih h.2
            exact spec_step_nonTwin (witB_not_twin h.1) ih1 ih2
          | false =>
            replace h := cond_false_elim h hmw
            simp only [Bool.and_eq_true] at h
            obtain ⟨ih1, ih2⟩ := ih h.2
            exact spec_step_nonTwin (killB_not_twin hqs h.1) ih1 ih2
    | nil =>
      rcases wits with _ | ⟨⟨mw, p, s⟩, ws⟩
      · simp only [twinSegB, Bool.and_eq_true] at h
        obtain ⟨ih1, ih2⟩ := ih h.2
        exact spec_step_nonTwin (killB_not_twin hqs h.1) ih1 ih2
      · simp only [twinSegB] at h
        cases hmw : (mw == m) with
        | true =>
          replace h := cond_true_elim h hmw
          simp only [Bool.and_eq_true] at h
          obtain ⟨ih1, ih2⟩ := ih h.2
          exact spec_step_nonTwin (witB_not_twin h.1) ih1 ih2
        | false =>
          replace h := cond_false_elim h hmw
          simp only [Bool.and_eq_true] at h
          obtain ⟨ih1, ih2⟩ := ih h.2
          exact spec_step_nonTwin (killB_not_twin hqs h.1) ih1 ih2

/-! ### The verified data — twins and factor witnesses per 1000-center chunk

Emitted and independently re-verified by `tools/gen_twinchain_lean.py` (sieve, then a
SEPARATE pure-trial-division re-check of every literal, then an exact Python simulation
of `twinSegB` on every chunk — branch order included).  Census on `[1, 10⁴]`:
810 twins, 2158 factor witnesses, 7032 clock-killed; wings ≤ 60001; witness factors
≤ 239.  Chunk plan frozen after calibration (chunk 5 standalone: 0.66 s net kernel). -/

-- GENERATED DATA START (tools/gen_twinchain_lean.py, chunk 1000)
private def tc_1 : List ℕ := [1, 2, 3, 5, 7, 10, 12, 17, 18, 23, 25, 30, 32, 33, 38, 40, 45, 47,
  52, 58, 70, 72, 77, 87, 95, 100, 103, 107, 110, 135, 137, 138, 143, 147, 170, 172, 175, 177,
  182, 192, 205, 213, 215, 217, 220, 238, 242, 247, 248, 268, 270, 278, 283, 287, 298, 312, 313,
  322, 325, 333, 338, 347, 348, 352, 355, 357, 373, 378, 385, 390, 397, 425, 432, 443, 448, 452,
  455, 465, 467, 495, 500, 520, 528, 542, 543, 550, 555, 560, 562, 565, 577, 578, 588, 590, 593,
  597, 612, 628, 637, 642, 653, 655, 667, 670, 675, 682, 688, 693, 703, 705, 707, 710, 712, 723,
  737, 747, 753, 758, 773, 775, 787, 798, 800, 822, 828, 835, 837, 850, 872, 880, 903, 907, 913,
  917, 920, 940, 942, 943, 957, 975, 978, 980]
private def wc_1 : List (ℕ × ℕ × Bool) := [(60, 19, false), (65, 17, false), (73, 19, true),
  (82, 17, false), (88, 17, true), (98, 19, false), (105, 17, true), (117, 19, false),
  (122, 17, true), (133, 17, false), (140, 29, false), (142, 23, true), (150, 17, false),
  (157, 23, false), (165, 23, true), (168, 19, true), (173, 17, true), (187, 19, true),
  (198, 29, false), (203, 23, false), (208, 29, true), (212, 19, false), (227, 29, false),
  (228, 37, false), (235, 17, false), (243, 31, true), (250, 19, false), (252, 17, false),
  (257, 23, true), (263, 19, true), (280, 23, true), (282, 19, true), (285, 29, false),
  (290, 37, true), (292, 17, true), (303, 17, false), (305, 31, true), (308, 43, false),
  (315, 31, false), (318, 23, false), (320, 17, false), (345, 19, false), (360, 17, true),
  (367, 31, true), (368, 47, false), (380, 43, true), (382, 29, true), (395, 23, true),
  (402, 19, false), (403, 41, false), (408, 31, false), (410, 23, false), (413, 37, false),
  (415, 19, true), (417, 41, true), (422, 17, false), (423, 43, true), (430, 29, false),
  (437, 43, false), (445, 17, true), (450, 37, false), (458, 41, true), (462, 17, true),
  (472, 19, true), (473, 17, false), (478, 19, false), (480, 43, false), (485, 41, false),
  (487, 23, true), (488, 29, false), (490, 17, false), (502, 23, false), (507, 17, false),
  (513, 17, true), (523, 43, false), (525, 23, false), (527, 29, true), (532, 31, false),
  (553, 31, true), (558, 17, false), (567, 19, true), (572, 47, true), (595, 43, true),
  (598, 17, true), (602, 23, true), (605, 19, true), (620, 61, false), (623, 37, true),
  (627, 53, false), (630, 19, false), (632, 17, true), (633, 29, false), (660, 17, false),
  (663, 23, false), (668, 19, false), (672, 29, true), (677, 17, false), (683, 17, true),
  (690, 41, false), (697, 37, true), (698, 53, true), (718, 31, false), (725, 19, false),
  (732, 23, false), (733, 53, false), (738, 19, true), (740, 23, true), (742, 61, false),
  (745, 17, false), (760, 47, true), (763, 19, false), (767, 43, true), (770, 31, true),
  (777, 59, true), (780, 31, false), (788, 29, true), (793, 67, true), (802, 17, true),
  (803, 61, false), (807, 29, false), (810, 43, true), (815, 67, false), (833, 19, true),
  (840, 71, false), (842, 31, false), (852, 19, true), (857, 37, false), (858, 19, false),
  (863, 31, true), (865, 29, false), (868, 41, true), (870, 17, true), (875, 29, true),
  (877, 19, false), (885, 47, false), (887, 17, true), (892, 53, false), (898, 17, false),
  (905, 61, true), (910, 43, false), (927, 67, true), (928, 19, true), (935, 31, false),
  (945, 53, false), (950, 41, true), (952, 29, false), (962, 23, false), (963, 53, true),
  (968, 37, false), (982, 43, true), (983, 17, false), (985, 19, true), (987, 31, true),
  (997, 31, false), (998, 53, false)]
private def tc_2 : List ℕ := [1015, 1022, 1033, 1045, 1050, 1060, 1075, 1092, 1095, 1110, 1115,
  1117, 1127, 1130, 1132, 1138, 1145, 1158, 1160, 1188, 1202, 1218, 1222, 1225, 1243, 1248, 1258,
  1260, 1265, 1293, 1313, 1325, 1335, 1348, 1370, 1372, 1382, 1398, 1405, 1423, 1433, 1438, 1470,
  1473, 1477, 1495, 1500, 1502, 1507, 1540, 1547, 1557, 1570, 1572, 1573, 1577, 1605, 1613, 1620,
  1628, 1643, 1655, 1668, 1673, 1678, 1682, 1690, 1712, 1717, 1722, 1738, 1743, 1750, 1755, 1785,
  1810, 1815, 1823, 1843, 1845, 1853, 1860, 1862, 1892, 1915, 1925, 1950, 1953, 1963, 1972, 1990,
  1995]
private def wc_2 : List (ℕ × ℕ × Bool) := [(1005, 37, false), (1008, 23, false),
  (1013, 59, true), (1017, 17, false), (1018, 31, true), (1020, 29, true), (1027, 61, true),
  (1040, 17, true), (1048, 19, false), (1052, 59, false), (1053, 71, false), (1057, 17, true),
  (1062, 23, true), (1067, 19, false), (1073, 41, true), (1078, 29, true), (1082, 43, false),
  (1083, 67, false), (1085, 17, false), (1088, 61, true), (1097, 29, false), (1108, 17, true),
  (1118, 19, true), (1122, 53, true), (1123, 23, false), (1125, 17, true), (1137, 19, true),
  (1143, 19, false), (1148, 71, true), (1150, 67, false), (1152, 31, false), (1162, 19, false),
  (1165, 29, true), (1167, 47, false), (1173, 31, true), (1178, 37, true), (1180, 73, false),
  (1183, 31, false), (1187, 17, false), (1192, 23, false), (1193, 17, true), (1195, 67, true),
  (1200, 19, false), (1213, 19, true), (1215, 23, false), (1227, 17, true), (1228, 53, true),
  (1232, 19, true), (1235, 31, true), (1242, 29, false), (1253, 73, false), (1255, 17, false),
  (1257, 19, false), (1262, 67, true), (1270, 19, true), (1277, 47, true), (1283, 43, true),
  (1288, 59, false), (1290, 71, true), (1292, 23, true), (1295, 17, true), (1297, 31, true),
  (1305, 41, false), (1312, 17, true), (1320, 89, false), (1323, 17, false), (1327, 19, true),
  (1330, 23, false), (1332, 61, true), (1342, 83, true), (1347, 59, false), (1353, 23, false),
  (1358, 29, false), (1360, 41, true), (1365, 19, true), (1368, 29, true), (1375, 37, false),
  (1383, 43, false), (1390, 19, false), (1397, 17, true), (1400, 31, false), (1403, 19, true),
  (1407, 23, true), (1412, 37, false), (1418, 47, true), (1425, 17, false), (1430, 23, true),
  (1435, 79, false), (1437, 37, true), (1440, 53, true), (1442, 17, false), (1447, 19, false),
  (1452, 31, true), (1453, 23, true), (1460, 19, true), (1463, 67, true), (1468, 23, false),
  (1475, 53, false), (1482, 17, true), (1488, 79, true), (1503, 29, false), (1508, 83, true),
  (1512, 43, false), (1515, 61, true), (1517, 19, true), (1522, 23, true), (1528, 53, false),
  (1530, 67, true), (1533, 17, true), (1535, 61, false), (1537, 23, false), (1543, 47, false),
  (1550, 17, true), (1552, 67, false), (1563, 83, false), (1565, 41, true), (1568, 23, true),
  (1578, 17, false), (1580, 19, false), (1585, 37, true), (1587, 89, false), (1592, 41, false),
  (1598, 43, false), (1600, 29, true), (1603, 59, true), (1607, 31, true), (1612, 17, false),
  (1617, 31, false), (1622, 37, true), (1633, 41, false), (1635, 17, true), (1638, 31, true),
  (1642, 59, false), (1645, 71, true), (1647, 41, true), (1650, 19, true), (1657, 61, false),
  (1677, 29, false), (1680, 17, false), (1683, 23, true), (1687, 29, true), (1697, 17, false),
  (1698, 23, false), (1708, 37, false), (1710, 31, false), (1713, 19, false), (1715, 41, false),
  (1720, 17, true), (1732, 19, false), (1733, 37, true), (1745, 19, true), (1748, 17, false),
  (1752, 23, true), (1760, 59, false), (1767, 23, false), (1768, 103, false), (1775, 23, true),
  (1778, 47, false), (1782, 17, false), (1787, 71, true), (1788, 17, true), (1790, 23, false),
  (1797, 41, false), (1803, 29, true), (1808, 19, false), (1820, 61, true), (1825, 47, false),
  (1827, 19, false), (1830, 79, false), (1832, 29, true), (1837, 73, false), (1838, 41, false),
  (1852, 41, true), (1855, 31, true), (1858, 71, true), (1865, 19, false), (1867, 17, false),
  (1873, 17, true), (1878, 19, true), (1880, 29, false), (1885, 43, true), (1888, 47, true),
  (1893, 37, false), (1895, 83, false), (1897, 19, true), (1902, 101, false), (1907, 17, true),
  (1908, 107, false), (1918, 17, false), (1920, 41, false), (1928, 23, false), (1930, 37, false),
  (1932, 67, true), (1937, 59, false), (1942, 43, false), (1943, 89, false), (1955, 37, true),
  (1957, 59, true), (1958, 17, true), (1962, 61, false), (1970, 53, true), (1977, 29, true),
  (1983, 73, false), (1985, 43, false), (1988, 79, false), (1992, 17, true), (1997, 23, false),
  (1998, 19, false)]
private def tc_3 : List ℕ := [2007, 2012, 2018, 2027, 2040, 2042, 2063, 2090, 2102, 2137, 2153,
  2167, 2168, 2203, 2223, 2233, 2280, 2282, 2285, 2287, 2293, 2305, 2313, 2317, 2322, 2333, 2335,
  2347, 2375, 2387, 2398, 2408, 2425, 2427, 2432, 2438, 2478, 2523, 2545, 2548, 2555, 2560, 2597,
  2607, 2608, 2622, 2623, 2648, 2662, 2677, 2678, 2690, 2698, 2705, 2727, 2742, 2772, 2775, 2782,
  2805, 2817, 2830, 2838, 2865, 2868, 2882, 2898, 2903, 2915, 2930, 2933, 2943, 2947, 2958, 2965,
  2973, 2985, 2987, 2993, 2998]
private def wc_3 : List (ℕ × ℕ × Bool) := [(2002, 41, false), (2005, 23, true),
  (2020, 17, false), (2023, 53, true), (2025, 29, false), (2028, 23, true), (2032, 73, true),
  (2035, 29, true), (2047, 71, false), (2053, 97, false), (2058, 53, false), (2060, 17, true),
  (2062, 89, true), (2067, 79, false), (2068, 19, true), (2072, 31, true), (2075, 59, true),
  (2083, 29, false), (2093, 19, false), (2097, 23, true), (2098, 41, true), (2100, 43, true),
  (2105, 17, false), (2107, 47, false), (2112, 19, false), (2118, 71, false), (2123, 47, true),
  (2128, 17, true), (2133, 67, true), (2135, 23, false), (2138, 101, true), (2140, 37, true),
  (2142, 71, true), (2145, 17, true), (2152, 37, false), (2163, 19, true), (2170, 29, false),
  (2172, 83, true), (2175, 31, false), (2177, 37, true), (2188, 19, false), (2193, 59, true),
  (2200, 43, false), (2205, 101, false), (2207, 17, false), (2210, 89, false), (2215, 97, true),
  (2217, 47, true), (2222, 67, false), (2228, 29, false), (2230, 17, true), (2237, 31, false),
  (2240, 89, true), (2243, 43, false), (2245, 19, false), (2250, 23, false), (2252, 59, true),
  (2258, 17, false), (2263, 37, false), (2265, 107, true), (2270, 53, false), (2272, 43, true),
  (2278, 79, true), (2292, 17, false), (2298, 17, true), (2300, 37, false), (2307, 109, false),
  (2310, 83, false), (2315, 17, true), (2320, 31, true), (2327, 23, true), (2328, 61, false),
  (2340, 19, false), (2343, 17, false), (2348, 73, false), (2350, 23, true), (2357, 79, true),
  (2362, 37, true), (2370, 59, true), (2373, 23, true), (2380, 109, true), (2382, 31, true),
  (2383, 17, true), (2392, 31, false), (2397, 19, false), (2405, 47, true), (2410, 19, true),
  (2412, 29, true), (2413, 31, true), (2415, 43, false), (2417, 17, true), (2443, 107, false),
  (2445, 17, false), (2447, 53, true), (2448, 19, true), (2450, 61, false), (2452, 47, true),
  (2453, 41, false), (2457, 23, false), (2460, 29, false), (2467, 19, true), (2475, 31, true),
  (2480, 23, false), (2482, 53, false), (2483, 47, false), (2487, 43, true), (2490, 67, false),
  (2492, 19, false), (2497, 71, true), (2502, 17, true), (2503, 23, false), (2508, 41, true),
  (2513, 17, false), (2515, 79, true), (2518, 29, false), (2522, 37, false), (2525, 109, false),
  (2527, 59, false), (2530, 17, false), (2538, 97, false), (2552, 61, true), (2553, 17, true),
  (2557, 23, true), (2558, 103, true), (2562, 19, true), (2567, 73, false), (2573, 43, true),
  (2578, 31, false), (2580, 23, true), (2588, 53, false), (2590, 41, true), (2592, 103, false),
  (2593, 47, true), (2595, 23, false), (2600, 19, true), (2613, 61, true), (2618, 23, false),
  (2625, 19, false), (2630, 31, true), (2632, 17, false), (2635, 97, false), (2643, 101, true),
  (2655, 17, true), (2657, 19, true), (2658, 37, true), (2665, 59, true), (2670, 37, false),
  (2672, 17, true), (2683, 17, false), (2685, 89, true), (2688, 127, false), (2692, 29, false),
  (2695, 19, true), (2700, 17, false), (2707, 37, false), (2712, 53, true), (2713, 41, true),
  (2718, 23, true), (2720, 19, false), (2723, 17, true), (2725, 83, false), (2733, 19, true),
  (2735, 61, true), (2740, 17, true), (2747, 53, false), (2753, 83, true), (2755, 61, false),
  (2760, 29, true), (2762, 73, true), (2765, 47, false), (2768, 17, false), (2777, 19, false),
  (2783, 59, true), (2788, 43, true), (2790, 19, true), (2795, 31, false), (2798, 103, false),
  (2800, 53, false), (2802, 17, false), (2812, 47, false), (2828, 19, true), (2833, 23, true),
  (2835, 73, true), (2837, 29, false), (2842, 17, true), (2852, 71, true), (2853, 17, false),
  (2860, 131, false), (2863, 41, false), (2867, 103, true), (2870, 17, false), (2872, 19, false),
  (2877, 41, true), (2887, 17, false), (2893, 17, true), (2900, 127, true), (2905, 29, true),
  (2907, 107, true), (2908, 73, true), (2912, 101, false), (2922, 47, true), (2937, 67, true),
  (2938, 17, false), (2942, 19, true), (2945, 41, false), (2952, 89, true), (2963, 23, false),
  (2970, 71, false), (2977, 53, true), (2978, 17, true), (2980, 19, true), (2982, 29, false),
  (3000, 41, true)]
private def tc_4 : List ℕ := [3007, 3008, 3010, 3020, 3022, 3042, 3048, 3052, 3087, 3090, 3152,
  3153, 3180, 3190, 3197, 3202, 3230, 3237, 3238, 3245, 3257, 3283, 3292, 3307, 3315, 3327, 3332,
  3337, 3358, 3372, 3393, 3407, 3413, 3418, 3425, 3440, 3453, 3458, 3462, 3468, 3483, 3497, 3502,
  3503, 3510, 3532, 3553, 3563, 3582, 3587, 3593, 3598, 3600, 3602, 3608, 3623, 3640, 3673, 3682,
  3685, 3693, 3712, 3713, 3728, 3747, 3757, 3762, 3770, 3773, 3783, 3790, 3810, 3827, 3838, 3840,
  3843, 3867, 3882, 3895, 3923, 3927, 3938, 3945, 3948, 3957, 3972, 3985]
private def wc_4 : List (ℕ × ℕ × Bool) := [(3003, 37, false), (3013, 101, false),
  (3015, 79, false), (3017, 23, true), (3028, 37, true), (3033, 31, true), (3035, 131, true),
  (3043, 19, false), (3047, 47, false), (3050, 29, true), (3055, 23, false), (3062, 19, false),
  (3063, 17, true), (3068, 41, false), (3073, 103, true), (3075, 19, true), (3077, 37, false),
  (3080, 17, true), (3085, 83, true), (3097, 17, true), (3098, 29, false), (3103, 43, false),
  (3108, 17, false), (3110, 47, true), (3112, 71, false), (3113, 19, true), (3117, 59, false),
  (3120, 97, false), (3125, 17, false), (3127, 29, false), (3132, 19, true), (3138, 19, false),
  (3140, 83, false), (3143, 109, true), (3145, 113, false), (3147, 23, false), (3150, 41, false),
  (3160, 67, false), (3162, 61, true), (3167, 31, false), (3168, 83, true), (3173, 79, false),
  (3175, 43, true), (3178, 23, true), (3182, 17, true), (3185, 29, false), (3195, 19, false),
  (3208, 19, true), (3215, 101, false), (3217, 97, false), (3218, 43, true), (3220, 139, false),
  (3223, 61, true), (3227, 17, false), (3250, 17, true), (3253, 29, true), (3255, 59, true),
  (3260, 31, false), (3262, 23, false), (3267, 17, true), (3272, 29, false), (3273, 41, false),
  (3285, 23, false), (3288, 109, false), (3290, 19, false), (3293, 23, true), (3295, 17, false),
  (3297, 73, false), (3308, 23, false), (3318, 17, true), (3322, 19, true), (3323, 127, false),
  (3325, 71, false), (3328, 19, false), (3348, 53, true), (3350, 101, true), (3355, 41, false),
  (3360, 19, true), (3362, 23, true), (3363, 17, false), (3367, 89, false), (3370, 73, false),
  (3377, 23, false), (3383, 53, false), (3385, 19, false), (3388, 29, false), (3392, 47, true),
  (3398, 19, true), (3400, 23, false), (3402, 137, false), (3405, 31, true), (3420, 17, true),
  (3427, 29, true), (3428, 67, false), (3432, 59, true), (3433, 43, true), (3435, 37, true),
  (3437, 17, true), (3442, 19, false), (3448, 17, false), (3455, 19, true), (3465, 17, false),
  (3470, 47, false), (3472, 37, true), (3475, 29, false), (3477, 23, true), (3488, 17, true),
  (3490, 43, false), (3493, 19, true), (3498, 31, true), (3505, 17, true), (3517, 47, false),
  (3523, 23, true), (3528, 61, true), (3530, 59, false), (3535, 127, true), (3537, 19, false),
  (3542, 53, false), (3545, 89, false), (3552, 101, true), (3558, 37, false), (3565, 73, true),
  (3567, 17, false), (3568, 79, false), (3570, 31, false), (3572, 29, true), (3575, 19, false),
  (3580, 47, true), (3605, 43, true), (3607, 17, true), (3615, 23, true), (3622, 31, true),
  (3630, 23, false), (3633, 71, true), (3635, 17, false), (3637, 139, false), (3645, 19, true),
  (3647, 79, false), (3652, 17, false), (3657, 37, true), (3658, 17, true), (3663, 31, false),
  (3670, 19, false), (3675, 17, true), (3678, 29, false), (3680, 71, false), (3692, 17, true),
  (3700, 79, true), (3708, 19, false), (3710, 113, false), (3715, 31, true), (3717, 29, true),
  (3722, 23, false), (3735, 73, false), (3740, 19, true), (3743, 17, true), (3745, 23, false),
  (3748, 43, false), (3750, 149, true), (3752, 47, false), (3763, 67, false), (3777, 17, true),
  (3778, 19, true), (3780, 37, false), (3787, 31, false), (3792, 61, false), (3803, 19, false),
  (3805, 17, false), (3812, 89, false), (3813, 137, false), (3817, 37, false), (3818, 31, false),
  (3822, 17, false), (3825, 53, true), (3832, 83, true), (3845, 17, true), (3847, 41, false),
  (3853, 61, false), (3855, 101, true), (3857, 73, true), (3860, 19, false), (3862, 17, true),
  (3868, 23, true), (3873, 17, false), (3875, 67, true), (3878, 53, true), (3880, 31, false),
  (3883, 23, false), (3887, 83, false), (3888, 41, false), (3890, 17, false), (3897, 67, false),
  (3908, 131, false), (3910, 29, false), (3913, 17, true), (3917, 19, false), (3920, 29, true),
  (3922, 101, false), (3930, 17, true), (3932, 31, true), (3943, 41, true), (3952, 23, false),
  (3953, 37, true), (3955, 19, false), (3960, 23, true), (3965, 37, false), (3978, 29, true),
  (3983, 23, true), (3987, 19, true), (3988, 71, true), (3990, 37, true), (3992, 17, false),
  (3997, 29, false), (4000, 103, true)]
private def tc_5 : List ℕ := [4018, 4030, 4062, 4070, 4153, 4163, 4172, 4195, 4217, 4218, 4235,
  4245, 4263, 4267, 4300, 4308, 4322, 4333, 4352, 4375, 4377, 4447, 4450, 4452, 4455, 4477, 4480,
  4482, 4492, 4510, 4518, 4540, 4547, 4568, 4580, 4588, 4590, 4597, 4615, 4623, 4625, 4632, 4653,
  4657, 4683, 4685, 4697, 4713, 4718, 4725, 4735, 4758, 4762, 4770, 4777, 4792, 4837, 4855, 4868,
  4898, 4900, 4928, 4945, 4960, 4980]
private def wc_5 : List (ℕ × ℕ × Bool) := [(4007, 29, true), (4008, 139, true), (4020, 89, true),
  (4022, 59, true), (4023, 101, false), (4025, 19, true), (4027, 37, true), (4037, 53, true),
  (4042, 79, false), (4043, 17, false), (4048, 107, false), (4053, 83, false), (4055, 29, false),
  (4060, 17, false), (4063, 19, true), (4065, 29, true), (4077, 17, false), (4078, 43, true),
  (4085, 127, false), (4088, 19, false), (4092, 43, false), (4095, 79, true), (4098, 23, true),
  (4100, 17, true), (4102, 151, false), (4107, 19, false), (4113, 23, false), (4118, 31, true),
  (4120, 19, true), (4125, 53, false), (4128, 17, false), (4130, 71, true), (4133, 137, true),
  (4135, 43, false), (4137, 103, false), (4140, 59, true), (4142, 29, false), (4147, 139, true),
  (4148, 41, true), (4155, 97, true), (4165, 67, false), (4168, 17, true), (4170, 127, true),
  (4177, 19, true), (4183, 19, false), (4190, 23, true), (4198, 89, true), (4202, 17, true),
  (4203, 151, true), (4205, 23, false), (4207, 43, true), (4212, 37, true), (4225, 101, false),
  (4228, 23, false), (4230, 17, false), (4232, 67, false), (4238, 47, true), (4242, 31, true),
  (4247, 17, false), (4252, 31, false), (4258, 29, false), (4260, 61, true), (4265, 157, false),
  (4268, 29, true), (4272, 19, true), (4273, 31, true), (4280, 61, false), (4282, 23, true),
  (4287, 17, true), (4293, 43, true), (4295, 73, true), (4298, 17, false), (4302, 53, true),
  (4307, 43, false), (4312, 41, true), (4315, 17, false), (4317, 59, true), (4323, 37, true),
  (4328, 23, true), (4330, 83, true), (4335, 19, false), (4337, 53, false), (4338, 17, true),
  (4342, 109, true), (4345, 29, false), (4350, 43, false), (4363, 47, false), (4368, 73, true),
  (4372, 17, true), (4373, 19, false), (4378, 109, false), (4382, 61, true), (4385, 83, false),
  (4393, 43, false), (4400, 17, false), (4403, 29, false), (4407, 31, false), (4408, 53, true),
  (4410, 47, false), (4412, 23, false), (4415, 59, false), (4417, 17, false), (4427, 101, false),
  (4428, 31, true), (4433, 67, false), (4438, 31, false), (4440, 17, true), (4443, 19, true),
  (4445, 149, false), (4462, 19, true), (4463, 61, false), (4473, 47, true), (4478, 67, true),
  (4485, 17, false), (4498, 137, false), (4503, 41, false), (4505, 151, true), (4515, 103, true),
  (4517, 41, true), (4520, 37, false), (4525, 17, true), (4527, 23, false), (4532, 71, false),
  (4533, 59, false), (4538, 19, true), (4543, 97, true), (4550, 23, false), (4553, 17, false),
  (4555, 151, false), (4557, 19, true), (4560, 109, true), (4562, 31, false), (4573, 23, false),
  (4575, 97, false), (4582, 19, false), (4583, 31, true), (4592, 59, false), (4595, 19, true),
  (4602, 53, false), (4603, 71, false), (4608, 43, false), (4610, 17, true), (4620, 19, false),
  (4627, 17, true), (4637, 43, true), (4638, 17, false), (4645, 29, true), (4648, 79, true),
  (4650, 23, true), (4658, 19, false), (4660, 73, true), (4667, 41, false), (4672, 17, false),
  (4680, 43, true), (4687, 61, true), (4690, 19, true), (4692, 47, false), (4693, 29, false),
  (4700, 163, true), (4702, 89, false), (4707, 31, true), (4715, 19, false), (4720, 127, false),
  (4722, 29, false), (4723, 17, false), (4727, 79, true), (4737, 43, false), (4742, 23, true),
  (4748, 31, false), (4753, 19, false), (4755, 47, true), (4757, 17, false), (4763, 17, true),
  (4767, 37, true), (4778, 109, true), (4785, 19, true), (4788, 23, true), (4790, 29, true),
  (4793, 149, true), (4797, 17, true), (4800, 31, true), (4802, 47, true), (4807, 151, true),
  (4813, 67, true), (4818, 137, true), (4823, 19, true), (4828, 59, false), (4830, 73, false),
  (4832, 53, true), (4833, 47, false), (4835, 67, false), (4840, 71, true), (4848, 17, true),
  (4858, 103, false), (4862, 31, true), (4863, 163, true), (4865, 17, true), (4867, 19, false),
  (4870, 61, true), (4872, 23, false), (4883, 83, false), (4888, 139, false), (4895, 23, false),
  (4902, 67, false), (4905, 19, false), (4907, 59, true), (4910, 17, false), (4917, 163, false),
  (4918, 19, true), (4923, 109, false), (4932, 101, false), (4933, 17, true), (4935, 29, true),
  (4940, 107, true), (4947, 67, true), (4953, 113, false), (4958, 71, false), (4965, 31, false),
  (4967, 17, true), (4972, 23, true), (4973, 53, false), (4975, 19, true), (4982, 71, true),
  (4987, 23, false), (4988, 173, false), (4993, 29, true), (4995, 17, false), (4998, 157, true),
  (5000, 19, false)]
private def tc_6 : List ℕ := [5002, 5015, 5023, 5045, 5065, 5078, 5082, 5093, 5140, 5142, 5145,
  5180, 5187, 5192, 5197, 5208, 5220, 5232, 5252, 5257, 5287, 5288, 5295, 5308, 5338, 5343, 5353,
  5357, 5365, 5383, 5387, 5395, 5402, 5407, 5422, 5427, 5435, 5453, 5467, 5472, 5485, 5490, 5495,
  5512, 5525, 5530, 5548, 5555, 5558, 5598, 5600, 5603, 5625, 5628, 5635, 5638, 5672, 5688, 5693,
  5702, 5710, 5717, 5728, 5745, 5750, 5752, 5765, 5775, 5793, 5807, 5808, 5827, 5842, 5847, 5880,
  5908, 5918, 5922, 5932, 5955, 5967, 5973, 5983]
private def wc_6 : List (ℕ × ℕ × Bool) := [(5005, 59, false), (5008, 151, false),
  (5010, 23, false), (5012, 17, false), (5017, 31, true), (5022, 29, true), (5028, 97, true),
  (5030, 103, true), (5035, 17, true), (5037, 47, true), (5038, 19, false), (5043, 79, true),
  (5050, 41, true), (5052, 17, true), (5057, 19, false), (5063, 17, false), (5070, 19, true),
  (5075, 37, false), (5077, 41, false), (5087, 23, true), (5092, 137, true), (5100, 37, true),
  (5103, 17, true), (5105, 109, true), (5108, 19, true), (5110, 23, true), (5112, 37, false),
  (5115, 47, false), (5122, 73, false), (5127, 19, true), (5138, 29, true), (5143, 59, true),
  (5147, 89, false), (5148, 17, false), (5152, 19, false), (5155, 157, true), (5162, 47, false),
  (5170, 67, false), (5173, 41, true), (5175, 61, true), (5177, 89, true), (5178, 47, true),
  (5182, 17, false), (5203, 19, true), (5210, 43, false), (5213, 31, false), (5217, 23, false),
  (5218, 131, false), (5222, 17, true), (5225, 23, true), (5233, 17, false), (5240, 23, false),
  (5243, 83, true), (5247, 19, false), (5248, 23, true), (5253, 43, false), (5255, 41, true),
  (5262, 131, true), (5268, 73, false), (5273, 17, true), (5275, 31, false), (5283, 29, true),
  (5285, 19, false), (5290, 17, true), (5292, 113, false), (5297, 37, false), (5303, 47, false),
  (5310, 151, false), (5313, 71, false), (5317, 19, true), (5318, 17, false), (5320, 59, true),
  (5323, 19, false), (5325, 43, true), (5327, 31, true), (5330, 113, true), (5350, 47, false),
  (5352, 17, false), (5360, 29, false), (5362, 53, true), (5372, 167, true), (5373, 103, false),
  (5378, 23, false), (5385, 79, false), (5390, 73, true), (5400, 179, true), (5408, 37, false),
  (5413, 47, true), (5415, 53, true), (5418, 19, false), (5420, 17, false), (5428, 29, true),
  (5430, 31, false), (5437, 17, false), (5442, 103, true), (5448, 97, false), (5450, 19, true),
  (5455, 23, true), (5457, 29, true), (5460, 17, true), (5463, 73, true), (5470, 23, false),
  (5477, 17, true), (5478, 23, true), (5483, 67, true), (5492, 31, false), (5493, 23, false),
  (5500, 61, false), (5505, 17, false), (5507, 19, true), (5518, 113, false), (5528, 17, true),
  (5532, 19, false), (5533, 89, true), (5537, 139, true), (5547, 23, true), (5560, 73, false),
  (5563, 29, false), (5565, 173, true), (5567, 127, true), (5570, 19, false), (5572, 67, false),
  (5577, 109, false), (5582, 107, true), (5583, 19, true), (5593, 23, true), (5595, 59, false),
  (5602, 19, true), (5607, 17, false), (5610, 41, false), (5617, 67, true), (5632, 47, false),
  (5633, 73, false), (5637, 31, true), (5642, 97, false), (5647, 17, true), (5658, 17, false),
  (5660, 29, true), (5665, 19, false), (5668, 31, true), (5673, 101, true), (5675, 17, false),
  (5677, 23, false), (5680, 53, true), (5682, 73, true), (5687, 149, true), (5695, 47, true),
  (5698, 17, true), (5703, 19, false), (5708, 23, true), (5712, 43, true), (5715, 17, true),
  (5723, 23, false), (5730, 31, true), (5737, 29, false), (5738, 173, true), (5742, 47, true),
  (5743, 17, false), (5747, 29, true), (5758, 179, true), (5763, 71, true), (5768, 53, false),
  (5772, 59, false), (5778, 37, false), (5780, 79, false), (5782, 113, true), (5785, 61, true),
  (5792, 19, true), (5798, 19, false), (5803, 37, true), (5805, 29, true), (5812, 43, false),
  (5815, 23, false), (5820, 47, false), (5833, 31, false), (5838, 23, false), (5840, 37, true),
  (5845, 17, false), (5855, 19, false), (5857, 113, false), (5862, 17, false), (5863, 29, true),
  (5868, 17, true), (5870, 41, true), (5873, 131, false), (5875, 101, true), (5877, 37, true),
  (5882, 29, false), (5885, 17, true), (5890, 59, false), (5892, 23, true), (5897, 41, false),
  (5903, 107, true), (5910, 59, true), (5912, 19, false), (5915, 23, true), (5925, 19, true),
  (5933, 97, false), (5940, 29, false), (5945, 53, true), (5947, 17, false), (5948, 89, false),
  (5950, 19, false), (5957, 31, false), (5962, 83, false), (5968, 61, true), (5980, 53, false),
  (5985, 149, true), (5987, 17, true), (5988, 19, false), (5990, 83, true), (5992, 157, false)]
private def tc_7 : List ℕ := [6002, 6018, 6057, 6078, 6088, 6130, 6132, 6150, 6155, 6170, 6200,
  6218, 6223, 6227, 6258, 6262, 6265, 6282, 6297, 6302, 6332, 6373, 6388, 6408, 6410, 6428, 6435,
  6442, 6445, 6452, 6458, 6487, 6507, 6527, 6538, 6540, 6557, 6562, 6585, 6638, 6640, 6673, 6688,
  6692, 6738, 6755, 6773, 6783, 6808, 6857, 6863, 6867, 6872, 6898, 6902, 6920, 6935, 6960, 6975,
  6993, 6997]
private def wc_7 : List (ℕ × ℕ × Bool) := [(6003, 181, false), (6010, 107, true),
  (6013, 43, true), (6020, 19, true), (6022, 23, false), (6023, 71, false), (6025, 37, true),
  (6027, 29, false), (6032, 17, false), (6038, 17, true), (6045, 19, false), (6050, 31, false),
  (6053, 23, true), (6055, 17, true), (6058, 19, true), (6062, 37, true), (6065, 151, false),
  (6067, 59, false), (6072, 17, true), (6080, 191, false), (6083, 17, false), (6087, 59, true),
  (6090, 61, true), (6093, 139, true), (6097, 157, true), (6100, 17, false), (6102, 19, false),
  (6113, 43, false), (6115, 19, true), (6120, 73, true), (6122, 23, true), (6123, 17, true),
  (6127, 97, false), (6128, 83, false), (6135, 131, false), (6137, 23, false), (6142, 43, true),
  (6143, 29, false), (6148, 37, false), (6153, 19, true), (6157, 17, true), (6163, 103, true),
  (6165, 47, true), (6167, 163, true), (6172, 19, true), (6178, 19, false), (6183, 23, false),
  (6185, 17, false), (6188, 107, false), (6192, 53, false), (6193, 73, true), (6197, 19, false),
  (6198, 41, true), (6205, 31, false), (6207, 167, true), (6220, 67, true), (6230, 29, false),
  (6232, 61, false), (6233, 149, false), (6237, 23, true), (6240, 29, true), (6247, 37, true),
  (6248, 19, true), (6253, 17, false), (6260, 23, true), (6263, 53, true), (6267, 19, true),
  (6270, 17, false), (6275, 23, false), (6288, 29, false), (6293, 17, true), (6295, 107, false),
  (6298, 23, false), (6300, 103, false), (6310, 17, true), (6317, 29, false), (6318, 167, false),
  (6325, 137, true), (6328, 43, false), (6330, 19, false), (6335, 191, true), (6337, 47, false),
  (6340, 109, false), (6347, 113, true), (6352, 23, true), (6353, 47, true), (6358, 37, true),
  (6363, 73, false), (6365, 181, false), (6370, 37, false), (6375, 23, true), (6377, 83, false),
  (6380, 101, true), (6387, 19, false), (6395, 17, true), (6402, 71, true), (6403, 41, true),
  (6405, 83, true), (6412, 17, true), (6417, 139, false), (6423, 17, false), (6430, 41, false),
  (6438, 19, true), (6440, 17, false), (6443, 29, true), (6447, 47, true), (6457, 17, false),
  (6465, 79, true), (6468, 151, true), (6473, 71, true), (6475, 53, true), (6478, 47, false),
  (6480, 17, true), (6482, 19, false), (6493, 163, true), (6500, 43, false), (6505, 23, false),
  (6508, 17, false), (6512, 41, false), (6513, 23, true), (6517, 61, true), (6520, 19, false),
  (6522, 109, true), (6533, 19, true), (6535, 113, false), (6542, 17, false), (6545, 107, true),
  (6548, 17, true), (6552, 19, true), (6555, 37, false), (6568, 157, true), (6570, 79, false),
  (6573, 113, true), (6575, 103, true), (6577, 19, false), (6578, 29, false), (6582, 17, true),
  (6583, 127, true), (6590, 19, true), (6592, 37, false), (6597, 23, false), (6603, 173, true),
  (6605, 23, true), (6608, 31, false), (6610, 17, false), (6612, 97, false), (6617, 29, true),
  (6618, 59, true), (6622, 67, true), (6625, 127, false), (6627, 17, false), (6633, 17, true),
  (6643, 23, false), (6647, 19, true), (6648, 113, false), (6650, 17, true), (6652, 107, true),
  (6655, 73, false), (6660, 31, true), (6662, 71, false), (6678, 17, false), (6682, 47, true),
  (6683, 101, true), (6685, 19, true), (6687, 53, true), (6695, 17, false), (6702, 79, true),
  (6703, 37, false), (6713, 47, false), (6715, 43, false), (6717, 41, false), (6718, 17, true),
  (6720, 23, true), (6722, 31, true), (6725, 157, true), (6727, 181, false), (6737, 83, true),
  (6743, 23, true), (6748, 19, false), (6750, 101, false), (6753, 31, true), (6757, 71, true),
  (6760, 47, false), (6765, 37, true), (6772, 41, true), (6780, 17, false), (6787, 43, true),
  (6790, 131, false), (6792, 83, false), (6793, 53, true), (6795, 59, true), (6802, 37, true),
  (6813, 41, true), (6815, 31, true), (6820, 17, true), (6825, 31, false), (6828, 53, false),
  (6830, 43, true), (6832, 179, true), (6835, 23, true), (6837, 17, true), (6842, 61, false),
  (6843, 19, false), (6848, 17, false), (6850, 23, false), (6858, 23, true), (6860, 79, true),
  (6865, 17, false), (6870, 47, true), (6878, 29, true), (6883, 61, true), (6885, 101, true),
  (6890, 67, true), (6893, 59, false), (6897, 29, false), (6900, 19, false), (6907, 29, true),
  (6912, 67, false), (6913, 19, true), (6923, 73, true), (6925, 37, false), (6930, 43, false),
  (6933, 17, false), (6937, 107, false), (6942, 23, false), (6947, 73, false), (6948, 47, false),
  (6955, 29, false), (6958, 83, false), (6962, 37, false), (6963, 41, false), (6967, 17, false),
  (6968, 97, true), (6977, 41, true), (6982, 163, true), (6988, 23, false), (6990, 17, true),
  (6995, 19, false), (7000, 97, false)]
private def tc_8 : List ℕ := [7003, 7012, 7030, 7037, 7047, 7068, 7077, 7095, 7107, 7117, 7140,
  7150, 7175, 7220, 7233, 7257, 7263, 7268, 7275, 7297, 7298, 7315, 7327, 7338, 7348, 7355, 7367,
  7378, 7380, 7397, 7422, 7437, 7450, 7462, 7520, 7523, 7530, 7553, 7557, 7598, 7637, 7675, 7682,
  7697, 7712, 7718, 7725, 7740, 7765, 7780, 7795, 7803, 7805, 7843, 7858, 7892, 7898, 7903, 7943,
  7950, 7952, 7957, 7963, 7968]
private def wc_8 : List (ℕ × ℕ × Bool) := [(7002, 43, true), (7007, 17, true), (7010, 137, true),
  (7017, 71, false), (7023, 29, true), (7025, 61, false), (7028, 149, true), (7032, 31, true),
  (7033, 19, false), (7040, 53, false), (7045, 41, false), (7052, 17, false), (7058, 17, true),
  (7063, 31, true), (7065, 19, true), (7067, 109, true), (7072, 151, true), (7073, 31, false),
  (7080, 23, false), (7088, 23, true), (7098, 37, true), (7102, 43, false), (7103, 17, false),
  (7105, 47, true), (7110, 29, true), (7112, 71, true), (7123, 79, false), (7128, 19, false),
  (7133, 127, false), (7138, 113, true), (7142, 73, true), (7143, 17, true), (7145, 43, false),
  (7147, 19, false), (7157, 23, true), (7158, 29, false), (7168, 29, true), (7172, 23, false),
  (7173, 193, false), (7177, 17, true), (7180, 23, true), (7182, 41, true), (7193, 103, true),
  (7198, 19, true), (7205, 17, false), (7208, 59, true), (7210, 181, true), (7212, 109, false),
  (7215, 73, true), (7222, 17, false), (7227, 103, false), (7228, 17, true), (7235, 83, true),
  (7238, 137, false), (7242, 19, false), (7245, 17, true), (7248, 157, false), (7250, 41, false),
  (7255, 19, true), (7270, 53, true), (7277, 47, false), (7283, 37, true), (7285, 109, true),
  (7287, 23, false), (7290, 17, false), (7292, 67, true), (7303, 29, false), (7305, 41, true),
  (7310, 23, false), (7312, 19, true), (7318, 19, false), (7320, 37, true), (7322, 197, true),
  (7325, 71, true), (7332, 29, false), (7333, 23, false), (7340, 47, true), (7345, 127, true),
  (7352, 31, false), (7353, 157, true), (7362, 163, false), (7375, 17, false), (7385, 59, true),
  (7387, 23, true), (7388, 19, true), (7392, 17, false), (7402, 23, false), (7403, 43, false),
  (7410, 23, true), (7413, 19, false), (7415, 17, true), (7417, 191, false), (7418, 47, false),
  (7420, 211, false), (7430, 109, false), (7432, 17, true), (7443, 17, false), (7448, 23, false),
  (7452, 61, false), (7453, 97, true), (7455, 41, false), (7457, 101, false), (7458, 29, true),
  (7465, 47, false), (7472, 107, false), (7480, 37, false), (7483, 17, true), (7485, 97, false),
  (7487, 29, true), (7488, 179, false), (7492, 79, true), (7495, 193, true), (7497, 31, true),
  (7502, 19, true), (7507, 31, false), (7508, 19, false), (7513, 61, false), (7518, 43, true),
  (7527, 19, false), (7528, 17, false), (7532, 43, false), (7535, 29, false), (7543, 167, true),
  (7550, 89, false), (7558, 101, false), (7560, 67, true), (7562, 17, false), (7563, 23, false),
  (7565, 19, false), (7567, 83, true), (7572, 181, true), (7578, 19, true), (7583, 173, false),
  (7585, 17, true), (7593, 29, false), (7595, 199, false), (7597, 19, true), (7600, 31, false),
  (7602, 17, true), (7605, 103, true), (7612, 109, true), (7613, 17, false), (7618, 43, false),
  (7623, 53, false), (7627, 67, true), (7628, 37, false), (7630, 17, false), (7635, 19, true),
  (7640, 23, true), (7648, 109, false), (7653, 17, true), (7660, 19, false), (7662, 31, false),
  (7663, 23, true), (7667, 157, true), (7670, 17, true), (7677, 73, false), (7683, 31, true),
  (7688, 163, false), (7690, 29, true), (7693, 31, false), (7695, 137, true), (7700, 47, false),
  (7703, 113, true), (7705, 83, false), (7710, 167, true), (7717, 19, false), (7723, 149, false),
  (7728, 89, false), (7730, 19, true), (7732, 17, false), (7738, 17, true), (7745, 31, true),
  (7747, 23, false), (7752, 193, false), (7758, 89, true), (7760, 101, false), (7767, 29, false),
  (7770, 23, false), (7773, 149, true), (7777, 29, true), (7782, 53, false), (7787, 19, true),
  (7788, 83, false), (7793, 19, false), (7800, 17, false), (7807, 31, true), (7810, 47, true),
  (7817, 17, false), (7822, 71, true), (7833, 43, false), (7835, 29, true), (7838, 31, true),
  (7840, 17, true), (7842, 211, false), (7847, 23, true), (7857, 17, true), (7865, 41, false),
  (7868, 17, false), (7870, 23, true), (7872, 73, true), (7873, 97, false), (7875, 37, true),
  (7877, 151, false), (7882, 19, true), (7887, 37, false), (7905, 43, true), (7908, 17, true),
  (7910, 31, false), (7912, 29, false), (7913, 79, false), (7917, 67, false), (7920, 19, true),
  (7927, 199, true), (7935, 47, false), (7938, 97, true), (7942, 17, true), (7947, 41, false),
  (7948, 43, true), (7970, 17, false), (7975, 59, true), (7978, 151, true), (7982, 47, false),
  (7983, 19, false), (7985, 23, true), (7987, 17, false), (7990, 191, false), (7992, 79, false),
  (7998, 37, false)]
private def tc_9 : List ℕ := [8020, 8052, 8068, 8080, 8090, 8108, 8113, 8122, 8130, 8137, 8143,
  8145, 8165, 8172, 8187, 8195, 8200, 8213, 8222, 8228, 8232, 8235, 8255, 8258, 8278, 8290, 8298,
  8320, 8323, 8332, 8337, 8342, 8355, 8377, 8410, 8425, 8432, 8482, 8495, 8510, 8522, 8533, 8540,
  8557, 8558, 8570, 8573, 8580, 8620, 8628, 8638, 8645, 8662, 8678, 8697, 8715, 8727, 8757, 8785,
  8810, 8817, 8848, 8858, 8862, 8872, 8878, 8880, 8925, 8932, 8935, 8953, 8983]
private def wc_9 : List (ℕ × ℕ × Bool) := [(8003, 31, false), (8005, 43, false),
  (8008, 23, true), (8012, 53, true), (8013, 131, true), (8015, 19, true), (8018, 73, true),
  (8022, 127, false), (8025, 89, true), (8027, 17, true), (8033, 157, false), (8038, 17, false),
  (8040, 19, false), (8047, 53, false), (8048, 43, false), (8053, 19, true), (8055, 17, false),
  (8057, 29, false), (8060, 37, true), (8067, 29, true), (8073, 59, false), (8078, 17, true),
  (8082, 71, false), (8085, 139, false), (8092, 23, false), (8095, 17, true), (8102, 173, false),
  (8103, 61, true), (8115, 23, false), (8117, 31, true), (8118, 53, true), (8125, 29, true),
  (8132, 59, false), (8148, 19, true), (8150, 79, false), (8152, 41, false), (8155, 113, true),
  (8157, 17, false), (8158, 31, false), (8167, 19, true), (8173, 19, false), (8178, 139, true),
  (8180, 17, true), (8183, 29, true), (8185, 67, false), (8190, 157, false), (8202, 29, false),
  (8207, 23, false), (8220, 31, false), (8223, 103, true), (8225, 17, false), (8242, 17, false),
  (8243, 19, true), (8250, 59, false), (8260, 29, false), (8262, 19, true), (8265, 17, true),
  (8267, 193, true), (8272, 31, true), (8277, 53, true), (8288, 223, false), (8293, 17, false),
  (8295, 71, false), (8297, 67, true), (8300, 19, true), (8302, 109, false), (8312, 53, false),
  (8313, 31, false), (8327, 17, false), (8328, 29, true), (8330, 23, true), (8333, 17, true),
  (8353, 23, true), (8360, 103, false), (8363, 19, false), (8365, 31, true), (8367, 17, true),
  (8368, 23, false), (8372, 191, false), (8375, 31, false), (8382, 19, false), (8388, 59, true),
  (8390, 71, true), (8393, 37, true), (8397, 83, true), (8398, 41, false), (8403, 127, false),
  (8405, 29, false), (8407, 73, false), (8412, 17, false), (8418, 17, true), (8423, 97, true),
  (8430, 37, true), (8433, 19, true), (8437, 23, false), (8438, 197, false), (8440, 79, true),
  (8442, 37, false), (8445, 23, true), (8447, 59, true), (8453, 41, true), (8458, 19, false),
  (8460, 23, false), (8463, 17, false), (8467, 37, true), (8470, 89, true), (8473, 29, true),
  (8475, 211, false), (8477, 19, false), (8480, 17, false), (8488, 127, true),
  (8493, 131, false), (8498, 67, true), (8502, 29, true), (8503, 17, true), (8507, 43, true),
  (8508, 71, false), (8515, 19, false), (8528, 19, true), (8535, 41, true), (8537, 17, true),
  (8542, 53, true), (8547, 19, true), (8550, 29, false), (8563, 83, true), (8568, 101, false),
  (8572, 19, false), (8575, 23, false), (8577, 53, false), (8585, 19, true), (8587, 67, false),
  (8592, 31, false), (8598, 23, false), (8603, 41, false), (8605, 17, true), (8607, 43, false),
  (8610, 19, false), (8612, 163, true), (8613, 31, true), (8627, 37, false), (8635, 103, true),
  (8640, 47, false), (8642, 19, true), (8650, 17, false), (8652, 23, true), (8657, 127, false),
  (8663, 59, false), (8668, 131, true), (8675, 23, true), (8680, 19, true), (8683, 53, false),
  (8685, 31, false), (8687, 47, false), (8690, 17, true), (8698, 23, true), (8705, 19, false),
  (8713, 23, false), (8717, 193, false), (8718, 17, false), (8720, 113, true), (8722, 43, true),
  (8733, 61, false), (8740, 41, true), (8745, 71, true), (8748, 73, true), (8750, 47, true),
  (8752, 17, false), (8753, 29, false), (8755, 131, false), (8762, 19, false), (8767, 23, true),
  (8768, 31, true), (8775, 17, true), (8778, 31, false), (8782, 23, false), (8783, 151, false),
  (8788, 67, false), (8792, 17, true), (8795, 113, false), (8797, 47, true), (8808, 41, false),
  (8815, 227, false), (8818, 157, false), (8822, 41, true), (8823, 167, false),
  (8827, 211, true), (8830, 31, true), (8832, 19, true), (8837, 17, false), (8843, 17, true),
  (8845, 73, false), (8850, 29, true), (8852, 173, true), (8860, 17, true), (8865, 43, false),
  (8867, 83, false), (8873, 139, true), (8883, 223, true), (8885, 89, false), (8887, 71, true),
  (8888, 17, false), (8892, 31, true), (8893, 229, true), (8895, 19, false), (8900, 67, true),
  (8902, 31, false), (8913, 53, true), (8915, 89, true), (8918, 73, false), (8922, 17, false),
  (8927, 19, true), (8928, 17, true), (8937, 29, true), (8943, 23, false), (8948, 37, true),
  (8950, 83, false), (8957, 61, true), (8958, 59, false), (8960, 37, false), (8962, 17, true),
  (8965, 19, true), (8970, 107, false), (8977, 61, false), (8988, 199, false), (8990, 17, false),
  (8992, 163, false), (8993, 79, true), (8995, 29, true), (8997, 23, true)]
private def tc_10 : List ℕ := [9002, 9067, 9070, 9083, 9090, 9097, 9105, 9153, 9175, 9203, 9222,
  9223, 9240, 9270, 9272, 9277, 9303, 9317, 9322, 9340, 9350, 9368, 9373, 9378, 9413, 9417, 9422,
  9433, 9452, 9468, 9482, 9485, 9487, 9532, 9537, 9545, 9555, 9558, 9588, 9593, 9632, 9650, 9685,
  9692, 9695, 9705, 9728, 9732, 9740, 9742, 9767, 9798, 9818, 9835, 9837, 9842, 9868, 9870, 9893,
  9903, 9907, 9912, 9938, 9945]
private def wc_10 : List (ℕ × ℕ × Bool) := [(9005, 71, false), (9012, 23, false),
  (9013, 17, true), (9023, 43, true), (9025, 173, true), (9027, 41, true), (9028, 19, false),
  (9030, 17, true), (9032, 47, true), (9035, 23, false), (9042, 227, false), (9047, 17, true),
  (9048, 233, false), (9053, 29, true), (9058, 17, false), (9060, 19, true), (9065, 109, false),
  (9068, 41, true), (9075, 17, false), (9082, 29, true), (9093, 89, true), (9100, 71, true),
  (9103, 193, false), (9107, 53, false), (9112, 23, true), (9118, 227, true), (9123, 19, false),
  (9125, 53, true), (9130, 29, false), (9133, 37, true), (9135, 23, true), (9138, 109, true),
  (9140, 29, true), (9142, 19, false), (9145, 37, false), (9147, 71, false), (9152, 43, true),
  (9158, 23, true), (9160, 17, false), (9168, 67, true), (9170, 37, true), (9173, 23, false),
  (9177, 17, false), (9182, 37, false), (9188, 29, false), (9195, 43, true), (9200, 17, true),
  (9207, 37, true), (9208, 101, true), (9210, 73, false), (9212, 19, true), (9217, 17, true),
  (9230, 79, true), (9233, 31, true), (9235, 67, true), (9237, 19, false), (9243, 31, false),
  (9247, 109, true), (9250, 19, true), (9252, 43, false), (9257, 67, false), (9263, 149, true),
  (9265, 23, false), (9268, 17, true), (9273, 23, true), (9278, 179, false), (9285, 17, true),
  (9287, 103, false), (9292, 127, false), (9298, 47, false), (9300, 41, false),
  (9305, 31, false), (9307, 19, true), (9312, 59, false), (9313, 17, false), (9320, 199, true),
  (9327, 107, true), (9328, 97, false), (9333, 29, false), (9335, 79, false), (9338, 43, false),
  (9342, 23, true), (9343, 29, true), (9347, 17, false), (9355, 37, true), (9357, 23, false),
  (9377, 127, true), (9380, 23, false), (9382, 41, false), (9383, 19, true), (9387, 17, true),
  (9390, 53, true), (9398, 17, false), (9405, 73, true), (9408, 19, false), (9412, 149, true),
  (9415, 17, false), (9420, 29, false), (9432, 17, false), (9438, 17, true), (9443, 53, true),
  (9445, 61, true), (9448, 83, false), (9450, 31, true), (9455, 17, true), (9457, 23, true),
  (9460, 31, false), (9467, 43, false), (9478, 19, true), (9483, 17, false), (9490, 97, true),
  (9497, 19, true), (9503, 19, false), (9508, 89, false), (9510, 43, false), (9515, 37, false),
  (9520, 239, false), (9522, 19, false), (9523, 17, true), (9525, 67, false), (9530, 211, false),
  (9538, 89, true), (9543, 31, true), (9548, 59, false), (9552, 37, false), (9560, 19, false),
  (9562, 103, true), (9565, 29, false), (9567, 61, true), (9573, 19, true), (9578, 101, false),
  (9580, 47, false), (9585, 17, false), (9587, 23, false), (9595, 23, true), (9597, 71, true),
  (9600, 239, true), (9602, 17, false), (9607, 59, false), (9608, 17, true), (9613, 137, true),
  (9615, 31, false), (9620, 197, false), (9625, 17, true), (9628, 41, false), (9630, 19, true),
  (9637, 53, false), (9642, 17, true), (9643, 47, true), (9653, 17, false), (9655, 19, false),
  (9658, 167, false), (9662, 29, true), (9663, 37, false), (9665, 103, true), (9672, 131, false),
  (9677, 31, false), (9688, 37, true), (9690, 47, true), (9697, 73, true), (9698, 31, true),
  (9702, 23, false), (9707, 139, true), (9712, 19, false), (9718, 199, true), (9720, 29, true),
  (9723, 227, false), (9725, 19, true), (9727, 17, true), (9730, 79, false), (9747, 233, false),
  (9753, 139, false), (9758, 127, true), (9760, 31, true), (9762, 37, true), (9763, 19, true),
  (9768, 29, false), (9772, 17, false), (9775, 89, false), (9782, 19, true), (9783, 79, true),
  (9790, 151, true), (9793, 67, false), (9795, 17, true), (9797, 29, false), (9802, 23, true),
  (9805, 89, true), (9807, 19, false), (9812, 17, true), (9823, 17, false), (9828, 109, false),
  (9833, 41, false), (9838, 67, true), (9840, 17, false), (9845, 19, false), (9853, 31, true),
  (9860, 67, false), (9863, 17, true), (9867, 53, true), (9872, 61, true), (9873, 37, true),
  (9875, 179, true), (9877, 19, true), (9888, 41, true), (9900, 191, false), (9905, 67, true),
  (9910, 37, true), (9915, 19, true), (9922, 37, false), (9923, 29, true), (9928, 71, false),
  (9933, 61, true), (9937, 109, false), (9940, 19, false), (9950, 227, false), (9952, 29, true),
  (9958, 149, false), (9963, 23, true), (9965, 17, true), (9970, 41, true), (9972, 19, true),
  (9977, 31, true), (9978, 19, false), (9980, 233, false), (9985, 139, true), (9987, 31, false),
  (9992, 167, false), (9993, 17, false), (9998, 223, true), (10000, 29, false)]

set_option maxRecDepth 100000 in
/-- Census chunk 1: centers `[1, 1000]` — 142 twins, 155 factor witnesses,
    clock kill for the remaining 703 centers (`decide +kernel`). -/
theorem twinSeg_chunk_1 : twinSegB clock13 1 1000 tc_1 wc_1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 2: centers `[1001, 2000]` — 92 twins, 208 factor witnesses,
    clock kill for the remaining 700 centers (`decide +kernel`). -/
theorem twinSeg_chunk_2 : twinSegB clock13 1001 1000 tc_2 wc_2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 3: centers `[2001, 3000]` — 80 twins, 213 factor witnesses,
    clock kill for the remaining 707 centers (`decide +kernel`). -/
theorem twinSeg_chunk_3 : twinSegB clock13 2001 1000 tc_3 wc_3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 4: centers `[3001, 4000]` — 87 twins, 214 factor witnesses,
    clock kill for the remaining 699 centers (`decide +kernel`). -/
theorem twinSeg_chunk_4 : twinSegB clock13 3001 1000 tc_4 wc_4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 5: centers `[4001, 5000]` — 65 twins, 229 factor witnesses,
    clock kill for the remaining 706 centers (`decide +kernel`). -/
theorem twinSeg_chunk_5 : twinSegB clock13 4001 1000 tc_5 wc_5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 6: centers `[5001, 6000]` — 83 twins, 212 factor witnesses,
    clock kill for the remaining 705 centers (`decide +kernel`). -/
theorem twinSeg_chunk_6 : twinSegB clock13 5001 1000 tc_6 wc_6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 7: centers `[6001, 7000]` — 61 twins, 239 factor witnesses,
    clock kill for the remaining 700 centers (`decide +kernel`). -/
theorem twinSeg_chunk_7 : twinSegB clock13 6001 1000 tc_7 wc_7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 8: centers `[7001, 8000]` — 64 twins, 229 factor witnesses,
    clock kill for the remaining 707 centers (`decide +kernel`). -/
theorem twinSeg_chunk_8 : twinSegB clock13 7001 1000 tc_8 wc_8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 9: centers `[8001, 9000]` — 72 twins, 229 factor witnesses,
    clock kill for the remaining 699 centers (`decide +kernel`). -/
theorem twinSeg_chunk_9 : twinSegB clock13 8001 1000 tc_9 wc_9 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Census chunk 10: centers `[9001, 10000]` — 64 twins, 230 factor witnesses,
    clock kill for the remaining 706 centers (`decide +kernel`). -/
theorem twinSeg_chunk_10 : twinSegB clock13 9001 1000 tc_10 wc_10 = true := by
  decide +kernel

/-- All 810 twin centers on `[1, 10000]` in increasing order — the chunk lists
    concatenated (parenthesised to match the right-to-left glue fold). -/
def twinList10k : List ℕ :=
  tc_1 ++ (tc_2 ++ (tc_3 ++ (tc_4 ++ (tc_5 ++ (tc_6 ++ (tc_7 ++ (tc_8 ++ (tc_9 ++ (tc_10)))))))))
-- GENERATED DATA END

/-! ### Glue: assembling the ten chunks into the full census -/

/-- `2 ≤ q` for every clock — the ONLY side condition the kill direction needs. -/
private theorem clock13_ge2 : ∀ q ∈ clock13, 2 ≤ q := by decide

/-- Localized census on `[lo, hi]`: the list is exactly the twin centers of the range. -/
private def IntervalCensus (lo hi : ℕ) (l : List ℕ) : Prop :=
  (∀ x ∈ l, lo ≤ x ∧ x ≤ hi) ∧
  (∀ m : ℕ, lo ≤ m → m ≤ hi → (TwinCenterZ m ↔ m ∈ l))

/-- One chunk gate + the spec = one interval census. -/
private theorem intervalCensus_of_seg {qs : List ℕ} (hqs : ∀ q ∈ qs, 2 ≤ q)
    {m0 n hi : ℕ} {tw : List ℕ} {wits : List (ℕ × ℕ × Bool)}
    (h : twinSegB qs m0 n tw wits = true) (hhi : m0 + n = hi + 1) :
    IntervalCensus m0 hi tw := by
  obtain ⟨h1, h2⟩ := twinSegB_spec hqs h
  constructor
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := h1 x hx
    omega
  · intro m hlo hhi'
    have hiff := h2 (m - m0) (by omega)
    have harith : m0 + (m - m0) = m := by omega
    rwa [harith] at hiff

/-- Adjacent interval censuses concatenate (membership splits by the range parts). -/
private theorem intervalCensus_append {lo mid lo2 hi : ℕ} {l1 l2 : List ℕ}
    (h1 : IntervalCensus lo mid l1) (h2 : IntervalCensus lo2 hi l2)
    (hmid : lo2 = mid + 1) (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    IntervalCensus lo hi (l1 ++ l2) := by
  obtain ⟨r1, c1⟩ := h1
  obtain ⟨r2, c2⟩ := h2
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := r1 x hx; omega
    · have := r2 x hx; omega
  · intro m hlo hhi
    by_cases hm : m ≤ mid
    · rw [c1 m hlo hm, List.mem_append]
      constructor
      · exact Or.inl
      · rintro (hmem | hmem)
        · exact hmem
        · exact absurd (r2 m hmem) (by omega)
    · rw [c2 m (by omega) hhi, List.mem_append]
      constructor
      · exact Or.inr
      · rintro (hmem | hmem)
        · exact absurd (r1 m hmem) (by omega)
        · exact hmem

private theorem census_1 : IntervalCensus 1 1000 tc_1 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_1 (by norm_num)
private theorem census_2 : IntervalCensus 1001 2000 tc_2 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_2 (by norm_num)
private theorem census_3 : IntervalCensus 2001 3000 tc_3 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_3 (by norm_num)
private theorem census_4 : IntervalCensus 3001 4000 tc_4 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_4 (by norm_num)
private theorem census_5 : IntervalCensus 4001 5000 tc_5 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_5 (by norm_num)
private theorem census_6 : IntervalCensus 5001 6000 tc_6 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_6 (by norm_num)
private theorem census_7 : IntervalCensus 6001 7000 tc_7 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_7 (by norm_num)
private theorem census_8 : IntervalCensus 7001 8000 tc_8 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_8 (by norm_num)
private theorem census_9 : IntervalCensus 8001 9000 tc_9 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_9 (by norm_num)
private theorem census_10 : IntervalCensus 9001 10000 tc_10 :=
  intervalCensus_of_seg clock13_ge2 twinSeg_chunk_10 (by norm_num)

private theorem census_9_10 : IntervalCensus 8001 10000 (tc_9 ++ tc_10) :=
  intervalCensus_append census_9 census_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_8_10 : IntervalCensus 7001 10000 (tc_8 ++ (tc_9 ++ tc_10)) :=
  intervalCensus_append census_8 census_9_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_7_10 : IntervalCensus 6001 10000 (tc_7 ++ (tc_8 ++ (tc_9 ++ tc_10))) :=
  intervalCensus_append census_7 census_8_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_6_10 :
    IntervalCensus 5001 10000 (tc_6 ++ (tc_7 ++ (tc_8 ++ (tc_9 ++ tc_10)))) :=
  intervalCensus_append census_6 census_7_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_5_10 :
    IntervalCensus 4001 10000 (tc_5 ++ (tc_6 ++ (tc_7 ++ (tc_8 ++ (tc_9 ++ tc_10))))) :=
  intervalCensus_append census_5 census_6_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_4_10 :
    IntervalCensus 3001 10000
      (tc_4 ++ (tc_5 ++ (tc_6 ++ (tc_7 ++ (tc_8 ++ (tc_9 ++ tc_10)))))) :=
  intervalCensus_append census_4 census_5_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_3_10 :
    IntervalCensus 2001 10000
      (tc_3 ++ (tc_4 ++ (tc_5 ++ (tc_6 ++ (tc_7 ++ (tc_8 ++ (tc_9 ++ tc_10))))))) :=
  intervalCensus_append census_3 census_4_10 (by norm_num) (by norm_num) (by norm_num)
private theorem census_2_10 :
    IntervalCensus 1001 10000
      (tc_2 ++ (tc_3 ++ (tc_4 ++ (tc_5 ++ (tc_6 ++ (tc_7 ++ (tc_8 ++ (tc_9 ++ tc_10)))))))) :=
  intervalCensus_append census_2 census_3_10 (by norm_num) (by norm_num) (by norm_num)

private theorem censusAll : IntervalCensus 1 10000 twinList10k :=
  intervalCensus_append census_1 census_2_10 (by norm_num) (by norm_num) (by norm_num)

/-- **THE COMPLETE CENSUS** (two directions): on `[1, 10⁴]`, `m` is a twin center IFF it
    is one of the 810 entries of `twinList10k`.  Forward: `twinB` soundness on the listed
    entries.  Backward (the NEW direction): every unlisted center in range carries a
    kernel-checked compositeness certificate for one wing.  Finite-range fact ONLY — see
    the module anti-vocabulary. -/
theorem twinList_complete_10000 :
    ∀ m : ℕ, 1 ≤ m → m ≤ 10000 → (TwinCenterZ m ↔ m ∈ twinList10k) :=
  fun m h1 h2 => censusAll.2 m h1 h2

/-- Every census entry lies in `[1, 10⁴]` (part 1 of the assembled spec). -/
theorem twinList_range : ∀ x ∈ twinList10k, 1 ≤ x ∧ x ≤ 10000 :=
  censusAll.1

/-! ### Kernel demos on the assembled list -/

set_option maxRecDepth 100000 in
/-- 810 twin centers on `[1, 10⁴]` (matches the classical twin-pair count below `60000`
    up to the `6m ± 1` reindexing of this repo). -/
theorem twinList10k_length : twinList10k.length = 810 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The first twin center: `m = 1` (wings `5, 7`). -/
theorem one_mem_twinList10k : (1 : ℕ) ∈ twinList10k := by decide +kernel

set_option maxRecDepth 100000 in
/-- The last twin center at or below `10⁴`: `m = 9945` (wings `59669, 59671`). -/
theorem last_mem_twinList10k : (9945 : ℕ) ∈ twinList10k := by decide +kernel

/-! ### Corollary: the max twin-center gap on `[1, 10⁴]` is exactly 83 -/

/-- Bool-native max (`Nat.ble` + `cond` — no `Decidable` detour for the kernel). -/
def maxN (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

/-- Fold: largest consecutive difference along a list, threaded from the head. -/
def maxGapB : ℕ → ℕ → List ℕ → ℕ
  | _, acc, [] => acc
  | prev, acc, x :: xs => maxGapB x (maxN acc (x - prev)) xs

/-- Largest consecutive gap of a list (`0` for `[]` and singletons). -/
def maxGap : List ℕ → ℕ
  | [] => 0
  | x :: xs => maxGapB x 0 xs

set_option maxRecDepth 100000 in
/-- The pinned census fold: the max consecutive twin-center gap on `[1, 10⁴]` is 83.
    RANGE-LOCAL maximum — see the anti-vocabulary. -/
theorem maxGap_twinList10k : maxGap twinList10k = 83 := by decide +kernel

/-- Chain fold for the window corollary: strictly increasing, consecutive steps `≤ G`,
    and the last element reaches at least `last0`. -/
def gapChainB (G last0 : ℕ) : ℕ → List ℕ → Bool
  | prev, [] => Nat.ble last0 prev
  | prev, x :: xs => Nat.blt prev x && Nat.ble x (prev + G) && gapChainB G last0 x xs

set_option maxRecDepth 100000 in
/-- Kernel gate for the window corollary: from the virtual start `0`, `twinList10k`
    climbs in steps `≤ 83` and its last entry is `≥ 9918` (it is `9945`). -/
theorem gapChain_twinList10k : gapChainB 83 9918 0 twinList10k = true := by decide +kernel

/-- The chain fold serves every window `(k, k + G]` with `k` below the chain's floor. -/
private theorem gapChainB_window {G last0 : ℕ} : ∀ {l : List ℕ} {prev : ℕ},
    gapChainB G last0 prev l = true →
    ∀ k : ℕ, prev ≤ k → k < last0 → ∃ x ∈ l, k < x ∧ x ≤ k + G := by
  intro l
  induction l with
  | nil =>
    intro prev h k hpk hk
    simp only [gapChainB, Nat.ble_eq] at h
    exact absurd hk (by omega)
  | cons x xs ih =>
    intro prev h k hpk hk
    simp only [gapChainB, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases Nat.lt_or_ge k x with hkx | hxk
    · exact ⟨x, List.mem_cons_self, hkx, by omega⟩
    · obtain ⟨y, hy, hky, hyk⟩ := ih h3 k hxk hk
      exact ⟨y, List.mem_cons_of_mem x hy, hky, hyk⟩

/-- **Window corollary**: every window `(k, k + 83]` that fits below `10⁴` contains a
    twin center.  The hypothesis `k + 83 ≤ 10000` is NOT decorative: dropping it is the
    twin prime conjecture (see the anti-vocabulary). -/
theorem twin_in_every_83_window :
    ∀ k : ℕ, k + 83 ≤ 10000 → ∃ m : ℕ, k < m ∧ m ≤ k + 83 ∧ TwinCenterZ m := by
  intro k hk
  obtain ⟨x, hmem, hkx, hxk⟩ :=
    gapChainB_window gapChain_twinList10k k (Nat.zero_le k) (by omega)
  obtain ⟨hx1, hx2⟩ := twinList_range x hmem
  exact ⟨x, hkx, hxk, (twinList_complete_10000 x hx1 hx2).mpr hmem⟩

set_option maxRecDepth 100000 in
/-- No census entry lies strictly between `4070` and `4153` (kernel fold). -/
private theorem no_twin_between_4070_4153 :
    twinList10k.all (fun x => Nat.ble x 4070 || Nat.ble 4153 x) = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem mem_4070 : (4070 : ℕ) ∈ twinList10k := by decide +kernel

set_option maxRecDepth 100000 in
private theorem mem_4153 : (4153 : ℕ) ∈ twinList10k := by decide +kernel

/-- **The gap 83 is attained**: `4070` and `4153` are twin centers (wings
    `24419/24421` and `24917/24919`) with NO twin center strictly between — the max-gap
    pin `maxGap_twinList10k` is sharp, via completeness (both directions used). -/
theorem twin_gap_83_attained :
    TwinCenterZ 4070 ∧ TwinCenterZ 4153 ∧
      ∀ m : ℕ, 4070 < m → m < 4153 → ¬ TwinCenterZ m := by
  refine ⟨(twinList_complete_10000 4070 (by norm_num) (by norm_num)).mpr mem_4070,
    (twinList_complete_10000 4153 (by norm_num) (by norm_num)).mpr mem_4153, ?_⟩
  intro m h1 h2 htw
  have hmem := (twinList_complete_10000 m (by omega) (by omega)).mp htw
  have hx := List.all_eq_true.mp no_twin_between_4070_4153 m hmem
  simp only [Bool.or_eq_true, Nat.ble_eq] at hx
  omega

/-!
### Axiom audit (performed against the built module from a scratch file outside the repo)

    #print axioms twinSeg_chunk_1 … _10    -- do not depend on any axioms
    #print axioms twinList10k_length       -- does not depend on any axioms
    #print axioms maxGap_twinList10k       -- does not depend on any axioms
    #print axioms gapChain_twinList10k     -- does not depend on any axioms
    #print axioms one_mem_twinList10k / last_mem_twinList10k
                                           -- [propext, Quot.sound]
    #print axioms twinSegB_spec            -- [propext, Classical.choice, Quot.sound]
    #print axioms twinList_complete_10000 / twinList_range
                                           -- [propext, Classical.choice, Quot.sound]
    #print axioms twin_in_every_83_window / twin_gap_83_attained
                                           -- [propext, Classical.choice, Quot.sound]

All ten `decide +kernel` data gates and the three pure census folds are axiom-FREE (Bool
kernel reduction end to end).  The membership demos add `propext`/`Quot.sound` (decidable
membership through `simp` glue in core), and every Prop-level result stays inside the
standard mathlib triple.  No `sorryAx`, no `Lean.ofReduceBool`/`Lean.trustCompiler`
(`native_decide` unused), no `step00FirstCause`.

### Measured budget ledger (32 GB reference machine, Lean v4.31, LEAN_NUM_THREADS=1)

Full module: **21.5 s wall, peak lean RSS 4.1 GB** (≈ 11 s of that is the one-time
mathlib import + initializers; the import baseline alone peaks at 3.3 GB).  Per-chunk
kernel type-checking, chunks 1 → 10 (ms): 480, 527, 621, 681, 642, 820, 687, 770, 870,
831 — Σ ≈ 6.9 s for all 172k+ kernel ops; every corollary decide is < 100 ms.
Calibration protocol: chunk 5 was generated standalone FIRST (predicted the heaviest at
~20.2k weighted ops; measured 0.66 s net kernel, 13.4 s wall with import), the
10 × 1000-center chunk plan was frozen only after that gate — each chunk two orders of
magnitude inside the 300 s / 8 GB per-theorem budget.  (Post-freeze note: by the finer
op count chunk 9 is the true heaviest — 870 ms, still ~350× under the gate.)
-/

end TwinChainCensus
end EuclidsPath
