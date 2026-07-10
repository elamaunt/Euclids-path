import EuclidsPath.Engine.GenealogyForest

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Grave-depth kernel census — machine-checked `≤ 3`-step descent to a twin on `[1, 2000]`

Lean companion of `tools/grave_depth_harness.py` (ledger L43).  The harness measured the
UNCONDITIONED grave depth — the minimal number of `Genealogy.PeelStep`s from a center `m`
down to a twin center — exhaustively on `[1, 10⁶]` and on windows at `10⁹` and `10¹²`.
This file kernel-verifies the smallest exact slice of that census: explicit min-depth path
witnesses for every `m ∈ [1, 2000]`, each of length `≤ 3`, checked by `decide +kernel`
through a fused Bool fold (the `Step00WitnessChainKernel` discipline: one tail-position
`&&` pass, no `Finset`, no `Decidable` instances on the Prop layer).

* `noOddFacB` / `primeB` — kernel-reducible primality (fuel-driven odd trial division);
* `stepB` / `stepB_peelStep` — one Bool peel-step check, sound for `Genealogy.PeelStep`;
* `twinB` / `twinB_twin` — Bool twin check, sound for `TwinCenterZ`;
* `ReachTwin d m` — "some peel path of length `≤ d` from `m` ends at a twin center";
* `pathB` / `pathB_reach` — fused path checker + soundness (induction on the witness);
* `censusB` / `censusB_sound` — positional fold over the data (entry `i` = center `m₀ + i`);
* `depthCensus_1_2000` — the kernel census (`decide +kernel`, 2000 verified paths);
* `reachTwin_all_1_2000 : ∀ m, 1 ≤ m → m ≤ 2000 → ReachTwin 3 m`.

## Kernel note — deviation from the drafted `Nat.minFac` shape

The drafted `primeB p := Nat.ble 2 p && (Nat.minFac p == p)` CANNOT survive `decide +kernel`:
mathlib's `Nat.minFac` runs through `Nat.minFacAux`, which is well-founded recursion, and its
own docstring warns that `rfl`/`decide` cannot unfold it (the kernel gets stuck on `Acc.rec`
over an opaque accessibility proof).  `primeB` here is therefore a FUEL-driven odd
trial-division ladder (`noOddFacB`, structural recursion — the kernel unfolds it literally),
and the soundness proof goes through `Nat.prime_def_le_sqrt` instead of
`Nat.prime_def_minFac`.  Only soundness is proved — the checker direction we consume.

## MANDATORY anti-vocabulary (read before quoting this file)

* **Bounded depth does NOT imply twin infinitude.**  The peel descent is strictly DOWNHILL
  (`peelStep_lt`), and one step can be a GIANT DROP: the min-path per-step ratio `t/m`
  reaches `5×10⁻⁵` (e.g. `19994 → 1` peeling `p = 23993`).  A FINITE twin set can absorb
  every center; `ReachTwin 3 m` on `[1, 2000]` certifies twins at or below `m`, never above.
* **Min-path drop-control is REFUTED** (harness, drops stages): min-depth paths take ratio
  `~5×10⁻⁵` drops.  Only the MAX-TARGET peel rule remains a drop-control candidate, and its
  verdict is a MEASUREMENT in the harness log, not a theorem here.
* **The survivor-conditioned L41 data (depth `≤ 3` on all 59 338 clean survivors at
  `10⁶`/`10⁹`) must NOT be read as a `∀ m` statement.**  This census is the unconditioned
  complement, and it is finite: `[1, 2000]` only.
* **Max depth is NOT claimed bounded.**  Depth 4 exists at `m = 4229`
  (`4229 → 846 → 169 → 34 → 5`), outside this file's range; whether the unconditioned max
  grows with scale is the harness's growth verdict (a measurement, open).
-/

namespace EuclidsPath
namespace GraveDepthKernel

open EuclidsPath.Residuals

/-! ### Kernel-reducible primality -/

/-- Fuel-driven odd trial-division ladder: `noOddFacB n k fuel = true` certifies that no
    odd `d` with `k ≤ d` and `d * d ≤ n` divides `n` (for odd `k`).  Fuel
    `≥ (sqrt n − k)/2 + 1` always suffices; callers pass `n` itself.  Structural recursion
    on `fuel` — the kernel CAN unfold this, unlike `Nat.minFacAux`. -/
def noOddFacB (n : ℕ) : ℕ → ℕ → Bool
  | k, 0 => Nat.blt n (k * k)
  | k, fuel + 1 => Nat.blt n (k * k) || (Nat.blt 0 (n % k) && noOddFacB n (k + 2) fuel)

/-- Kernel-checkable primality certificate: `2 ≤ p`, `p` odd, and the odd ladder clears
    every odd `3 ≤ d` with `d² ≤ p`.  Sound for all `p` (`primeB_prime`); complete for odd
    `p` — the only inputs here are wings `6k ± 1` and peel primes `≥ 5`, never `2`. -/
def primeB (p : ℕ) : Bool := Nat.ble 2 p && Nat.blt 0 (p % 2) && noOddFacB p 3 p

theorem noOddFacB_sound {n : ℕ} : ∀ fuel k, noOddFacB n k fuel = true → k % 2 = 1 →
    ∀ d, d % 2 = 1 → k ≤ d → d * d ≤ n → ¬ d ∣ n := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h hk d hd hkd hdd hdvd
    simp only [noOddFacB, Nat.blt_eq] at h
    exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h (Nat.mul_le_mul hkd hkd)) hdd)
  | succ fuel ih =>
    intro k h hk d hd hkd hdd hdvd
    simp only [noOddFacB, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    rcases h with h | ⟨hmod, hrec⟩
    · exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h (Nat.mul_le_mul hkd hkd)) hdd)
    · rcases Nat.eq_or_lt_of_le hkd with rfl | hlt
      · have := Nat.mod_eq_zero_of_dvd hdvd
        omega
      · exact ih (k + 2) hrec (by omega) d hd (by omega) hdd hdvd

/-- **Soundness of `primeB`** (via `Nat.prime_def_le_sqrt`; the drafted
    `Nat.prime_def_minFac` route is unavailable to the kernel — see the module note). -/
theorem primeB_prime {p : ℕ} (h : primeB p = true) : p.Prime := by
  simp only [primeB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨h2, hodd⟩, hlad⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm2 hms hmd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨r, hr⟩ := he
    have h2p : 2 ∣ p := Dvd.dvd.trans ⟨r, by omega⟩ hmd
    have := Nat.mod_eq_zero_of_dvd h2p
    omega
  · obtain ⟨r, hr⟩ := ho
    exact noOddFacB_sound p 3 hlad rfl m (by omega) (by omega) hmm hmd

/-! ### The step, twin and path checkers (fused Bool discipline) -/

/-- One peel-step check.  `w = (t, p, e, d)` encodes `6m − ε = p · (6t + δ)` with
    `e = true ↔ ε = 1` (left wing `6m − 1`) and `d = true ↔ δ = 1` (cofactor `6t + 1`) —
    the EXACT `Genealogy.PeelStep` conventions.  `cond` is the Bool-native `if`. -/
def stepB (m : ℕ) : ℕ × ℕ × Bool × Bool → Bool
  | (t, p, e, d) =>
    Nat.ble 1 t && Nat.ble 5 p && primeB p && Nat.blt t m &&
      (cond e (6 * m - 1) (6 * m + 1) == p * cond d (6 * t + 1) (6 * t - 1))

/-- **Soundness of `stepB`**: a passing check IS a `Genealogy.PeelStep m t` (the Bools are
    mapped back to the `∃ ε δ` witnesses; ℕ-truncation is discharged by `omega` from
    `1 ≤ t < m`). -/
theorem stepB_peelStep {m : ℕ} {w : ℕ × ℕ × Bool × Bool} (h : stepB m w = true) :
    Genealogy.PeelStep m w.1 := by
  obtain ⟨t, p, e, d⟩ := w
  show Genealogy.PeelStep m t
  simp only [stepB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨ht1, hp5⟩, hpB⟩, htm⟩, heq⟩ := h
  have hp : p.Prime := primeB_prime hpB
  cases e <;> cases d
  · replace heq : 6 * m + 1 = p * (6 * t - 1) := heq
    refine ⟨-1, -1, Or.inr rfl, Or.inr rfl, p, hp, hp5, ht1, ?_⟩
    calc 6 * (m : ℤ) - (-1) = ((6 * m + 1 : ℕ) : ℤ) := by omega
      _ = ((p * (6 * t - 1) : ℕ) : ℤ) := by rw [heq]
      _ = (p : ℤ) * ((6 * t - 1 : ℕ) : ℤ) := by rw [Nat.cast_mul]
      _ = (p : ℤ) * (6 * (t : ℤ) + (-1)) := by
          have h6t : ((6 * t - 1 : ℕ) : ℤ) = 6 * (t : ℤ) + (-1) := by omega
          rw [h6t]
  · replace heq : 6 * m + 1 = p * (6 * t + 1) := heq
    refine ⟨-1, 1, Or.inr rfl, Or.inl rfl, p, hp, hp5, ht1, ?_⟩
    calc 6 * (m : ℤ) - (-1) = ((6 * m + 1 : ℕ) : ℤ) := by omega
      _ = ((p * (6 * t + 1) : ℕ) : ℤ) := by rw [heq]
      _ = (p : ℤ) * (6 * (t : ℤ) + 1) := by push_cast; ring
  · replace heq : 6 * m - 1 = p * (6 * t - 1) := heq
    refine ⟨1, -1, Or.inl rfl, Or.inr rfl, p, hp, hp5, ht1, ?_⟩
    calc 6 * (m : ℤ) - 1 = ((6 * m - 1 : ℕ) : ℤ) := by omega
      _ = ((p * (6 * t - 1) : ℕ) : ℤ) := by rw [heq]
      _ = (p : ℤ) * ((6 * t - 1 : ℕ) : ℤ) := by rw [Nat.cast_mul]
      _ = (p : ℤ) * (6 * (t : ℤ) + (-1)) := by
          have h6t : ((6 * t - 1 : ℕ) : ℤ) = 6 * (t : ℤ) + (-1) := by omega
          rw [h6t]
  · replace heq : 6 * m - 1 = p * (6 * t + 1) := heq
    refine ⟨1, 1, Or.inl rfl, Or.inl rfl, p, hp, hp5, ht1, ?_⟩
    calc 6 * (m : ℤ) - 1 = ((6 * m - 1 : ℕ) : ℤ) := by omega
      _ = ((p * (6 * t + 1) : ℕ) : ℤ) := by rw [heq]
      _ = (p : ℤ) * (6 * (t : ℤ) + 1) := by push_cast; ring

/-- Twin-center check: `1 ≤ m` and both wings prime. -/
def twinB (m : ℕ) : Bool := Nat.ble 1 m && primeB (6 * m - 1) && primeB (6 * m + 1)

theorem twinB_twin {m : ℕ} (h : twinB m = true) : TwinCenterZ m := by
  simp only [twinB, Bool.and_eq_true] at h
  exact ⟨primeB_prime h.1.2, primeB_prime h.2⟩

/-- `ReachTwin d m`: some peel path of length `≤ d` from `m` ends at a twin center. -/
def ReachTwin : ℕ → ℕ → Prop
  | 0, m => TwinCenterZ m
  | d + 1, m => TwinCenterZ m ∨ ∃ t, Genealogy.PeelStep m t ∧ ReachTwin d t

/-- Fused path checker: consume the steps left to right, then certify the terminal twin. -/
def pathB : ℕ → List (ℕ × ℕ × Bool × Bool) → Bool
  | m, [] => twinB m
  | m, w :: ws => stepB m w && pathB w.1 ws

/-- **Soundness of `pathB`**: a passing path witnesses `ReachTwin (length) m`. -/
theorem pathB_reach {ws : List (ℕ × ℕ × Bool × Bool)} {m : ℕ} (h : pathB m ws = true) :
    ReachTwin ws.length m := by
  induction ws generalizing m with
  | nil => exact twinB_twin h
  | cons w ws ih =>
    simp only [pathB, Bool.and_eq_true] at h
    exact Or.inr ⟨w.1, stepB_peelStep h.1, ih h.2⟩

theorem reachTwin_succ {d m : ℕ} (h : ReachTwin d m) : ReachTwin (d + 1) m := by
  induction d generalizing m with
  | zero => exact Or.inl h
  | succ d ih =>
    have h' : TwinCenterZ m ∨ ∃ t, Genealogy.PeelStep m t ∧ ReachTwin d t := h
    rcases h' with h' | ⟨t, hstep, hr⟩
    · exact Or.inl h'
    · exact Or.inr ⟨t, hstep, ih hr⟩

/-- Reaching within `d` steps reaches within any `d' ≥ d` steps. -/
theorem reachTwin_mono {d d' m : ℕ} (h : ReachTwin d m) (hle : d ≤ d') : ReachTwin d' m := by
  induction d' with
  | zero =>
    have hd0 : d = 0 := Nat.le_zero.mp hle
    exact hd0 ▸ h
  | succ d' ih =>
    rcases Nat.lt_or_ge d (d' + 1) with hlt | hge
    · exact reachTwin_succ (ih (by omega))
    · have hde : d = d' + 1 := by omega
      exact hde ▸ h

/-! ### The positional census fold -/

/-- Positional census: entry `i` of the data is checked as a `≤ 3`-step path witness for
    the center `m₀ + i` (single tail-position `&&` pass — kernel-friendly). -/
def censusB : ℕ → List (List (ℕ × ℕ × Bool × Bool)) → Bool
  | _, [] => true
  | m, e :: es => Nat.ble e.length 3 && pathB m e && censusB (m + 1) es

/-- **Positional-fold soundness**: a passing census certifies `ReachTwin 3 (m₀ + i)` for
    every index `i` below the data length. -/
theorem censusB_sound : ∀ {es : List (List (ℕ × ℕ × Bool × Bool))} {m0 : ℕ},
    censusB m0 es = true → ∀ i, i < es.length → ReachTwin 3 (m0 + i) := by
  intro es
  induction es with
  | nil => intro m0 _ i hi; exact absurd hi (by simp)
  | cons e es ih =>
    intro m0 h i hi
    simp only [censusB, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨hlen, hpath⟩, hrest⟩ := h
    cases i with
    | zero => simpa using reachTwin_mono (pathB_reach hpath) hlen
    | succ i =>
      have hi' : i < es.length := by simpa using hi
      have hstep := ih hrest i hi'
      have harith : m0 + (i + 1) = (m0 + 1) + i := by omega
      rw [harith]
      exact hstep

/-! ### The verified data — min-depth path witnesses for `m ∈ [1, 2000]`

Emitted by `tools/grave_depth_harness.py emit` (min-depth paths, smallest-`t` tie-break),
independently re-verified and chunked (200 entries each) by `tools/gen_paths_lean.py`.
Measured depth histogram on `[1, 2000]`: `{0: 234, 1: 1323, 2: 434, 3: 9}` — max 3. -/

-- GENERATED DATA START (tools/gen_paths_lean.py, chunk 200)
private def gd_0 : List (List (ℕ × ℕ × Bool × Bool)) := [[], [], [], [(1, 5, false, false)], [],
  [(1, 5, true, true)], [], [(1, 7, false, true)], [(1, 11, false, false)], [],
  [(1, 13, true, false)], [], [(1, 11, true, true)], [(1, 17, false, false)],
  [(1, 13, false, true)], [(1, 19, true, false)], [], [], [(1, 23, false, false)],
  [(1, 17, true, true)], [(4, 5, true, true), (1, 5, false, false)], [(1, 19, false, true)], [],
  [(1, 29, false, false)], [], [(1, 31, true, false)], [(1, 23, true, true)],
  [(2, 13, false, true)], [(4, 7, false, true), (1, 5, false, false)], [],
  [(1, 37, true, false)], [], [], [(1, 29, true, true)], [(2, 19, true, false)],
  [(1, 43, true, false)], [(2, 17, true, true)], [], [(1, 47, false, false)], [],
  [(2, 19, false, true)], [(2, 23, false, false)], [(1, 37, false, true)],
  [(1, 53, false, false)], [], [(4, 11, true, true), (1, 5, false, false)], [],
  [(1, 41, true, true)], [(1, 59, false, false)], [(1, 43, false, true)], [(1, 61, true, false)],
  [], [(2, 29, false, false)], [(3, 17, true, true)], [(1, 47, true, true)],
  [(1, 67, true, false)], [(2, 31, true, false)], [], [(1, 71, false, false)],
  [(3, 19, false, true)], [(1, 73, true, false)], [(1, 53, true, true)], [(2, 29, true, true)],
  [(6, 11, false, false), (1, 5, true, true)], [(3, 23, false, false)], [(1, 79, true, false)],
  [(2, 31, false, true)], [(2, 37, true, false)], [(1, 59, true, true)], [],
  [(1, 61, false, true)], [], [(3, 23, true, true)], [(1, 89, false, false)],
  [(2, 41, false, false)], [(6, 13, true, false), (1, 5, true, true)], [],
  [(1, 67, false, true)], [(2, 43, true, false)], [(2, 37, false, true)], [(1, 97, true, false)],
  [(3, 29, false, false)], [(1, 71, true, true)], [(1, 101, false, false)],
  [(1, 73, false, true)], [(1, 103, true, false)], [], [(3, 31, true, false)],
  [(1, 107, false, false)], [(8, 11, true, true), (1, 7, false, true)], [(1, 109, true, false)],
  [(1, 79, false, true)], [(2, 43, false, true)], [(1, 113, false, false)], [],
  [(4, 23, true, true), (1, 5, false, false)], [(1, 83, true, true)], [(3, 31, false, true)],
  [(6, 17, false, false), (1, 5, true, true)], [], [(9, 11, true, true), (1, 11, false, false)],
  [(2, 47, true, true)], [], [(1, 89, true, true)], [(3, 37, true, false)],
  [(1, 127, true, false)], [], [(2, 59, false, false)], [(1, 131, false, false)], [],
  [(5, 23, false, false)], [(2, 61, true, false)], [(1, 97, false, true)],
  [(1, 137, false, false)], [(2, 53, true, true)], [(1, 139, true, false)],
  [(3, 37, false, true)], [(1, 101, true, true)], [(5, 23, true, true)], [(1, 103, false, true)],
  [(4, 29, true, true), (1, 5, false, false)], [(3, 43, true, false)], [(2, 67, true, false)],
  [(1, 149, false, false)], [(1, 107, true, true)], [(1, 151, true, false)],
  [(1, 109, false, true)], [(2, 59, true, true)], [(4, 31, false, true), (1, 5, false, false)],
  [(2, 71, false, false)], [(1, 157, true, false)], [(1, 113, true, true)],
  [(3, 47, false, false)], [(2, 73, true, false)], [], [(1, 163, true, false)], [], [],
  [(1, 167, false, false)], [(5, 29, false, false)],
  [(11, 13, true, false), (1, 13, true, false)], [(4, 37, true, false), (1, 5, false, false)],
  [], [(1, 173, false, false)], [(2, 79, true, false)],
  [(21, 7, true, false), (4, 5, true, true), (1, 5, false, false)], [], [(1, 127, false, true)],
  [(1, 179, false, false)], [(3, 53, false, false)], [(1, 181, true, false)],
  [(2, 83, false, false)], [(1, 131, true, true)], [(2, 71, true, true)],
  [(8, 19, false, true), (1, 7, false, true)], [(9, 17, true, true), (1, 11, false, false)],
  [(7, 23, false, false)], [(2, 73, false, true)], [(1, 191, false, false)],
  [(1, 137, true, true)], [(1, 193, true, false)], [(1, 139, false, true)],
  [(2, 89, false, false)], [(1, 197, false, false)], [(7, 23, true, true)],
  [(1, 199, true, false)], [(3, 59, false, false)], [(3, 53, true, true)],
  [(6, 29, false, false), (1, 5, true, true)], [], [(2, 79, false, true)], [],
  [(3, 61, true, false)], [(1, 149, true, true)], [], [(1, 211, true, false)], [],
  [(2, 97, true, false)], [(5, 37, true, false)], [(2, 83, true, true)],
  [(6, 31, true, false), (1, 5, true, true)], [], [(1, 157, false, true)],
  [(11, 17, false, false), (1, 13, true, false)], [(2, 101, false, false)],
  [(1, 223, true, false)], [(3, 59, true, true)], [(8, 23, true, true), (1, 7, false, true)],
  [(1, 227, false, false)], [(1, 163, false, true)], [(1, 229, true, false)], [],
  [(2, 89, true, true)], [(1, 233, false, false)], [(1, 167, true, true)],
  [(2, 107, false, false)], [(15, 13, false, true), (1, 13, false, true)],
  [(5, 41, false, false)], [(1, 239, false, false)], [(2, 109, true, false)]]
private def gd_1 : List (List (ℕ × ℕ × Bool × Bool)) := [[(1, 241, true, false)],
  [(1, 173, true, true)], [(4, 53, false, false), (1, 5, false, false)],
  [(41, 5, false, false), (2, 19, false, true)], [],
  [(11, 19, true, false), (1, 13, true, false)], [(2, 113, false, false)],
  [(5, 43, true, false)], [(1, 179, true, true)], [(2, 97, false, true)],
  [(1, 181, false, true)], [(3, 67, false, true)], [], [(1, 257, false, false)], [],
  [(6, 37, true, false), (1, 5, true, true)], [], [(13, 17, false, false), (1, 11, true, true)],
  [(1, 263, false, false)], [], [(4, 53, true, true), (1, 5, false, false)],
  [(5, 43, false, true)], [(1, 191, true, true)], [(1, 269, false, false)],
  [(1, 193, false, true)], [(1, 271, true, false)], [(5, 47, false, false)],
  [(6, 37, false, true), (1, 5, true, true)],
  [(21, 11, false, false), (4, 5, true, true), (1, 5, false, false)], [(1, 197, true, true)],
  [(1, 277, true, false)], [(1, 199, false, true)], [(2, 127, true, false)],
  [(1, 281, false, false)], [(3, 83, false, false)], [(1, 283, true, false)],
  [(8, 29, true, true), (1, 7, false, true)], [], [(6, 41, false, false), (1, 5, true, true)],
  [(2, 131, false, false)], [(14, 17, true, true), (1, 17, false, false)], [],
  [(5, 47, true, true)], [(1, 293, false, false)], [(2, 113, true, true)],
  [(1, 211, false, true)], [], [], [(11, 23, false, false), (1, 13, true, false)],
  [(3, 79, false, true)], [(2, 137, false, false)], [(3, 89, false, false)],
  [(7, 37, true, false)], [(4, 61, false, true), (1, 5, false, false)], [(2, 139, true, false)],
  [(1, 307, true, false)], [(4, 67, true, false), (1, 5, false, false)],
  [(15, 17, true, true), (1, 13, false, true)], [(1, 311, false, false)],
  [(1, 223, false, true)], [(1, 313, true, false)], [(20, 13, false, true), (1, 17, true, true)],
  [(3, 83, true, true)], [(1, 317, false, false)], [(1, 227, true, true)],
  [(9, 29, true, true), (1, 11, false, false)], [(1, 229, false, true)], [],
  [(14, 19, false, true), (1, 17, false, false)], [], [(54, 5, true, true), (3, 17, true, true)],
  [(1, 233, true, true)], [(2, 149, false, false)], [(5, 53, true, true)],
  [(2, 127, false, true)], [(1, 331, true, false)], [(2, 151, true, false)], [],
  [(1, 239, true, true)], [(7, 41, false, false)], [(1, 337, true, false)],
  [(3, 89, true, true)], [], [(2, 131, true, true)], [(5, 59, false, false)],
  [(3, 101, false, false)], [], [(2, 157, true, false)], [(1, 347, false, false)],
  [(6, 47, true, true), (1, 5, true, true)], [(1, 349, true, false)], [(3, 103, true, false)],
  [(1, 251, true, true)], [(1, 353, false, false)], [(5, 61, true, false)],
  [(4, 71, true, true), (1, 5, false, false)], [(2, 137, true, true)], [],
  [(1, 359, false, false)], [(1, 257, true, true)], [(2, 139, false, true)],
  [(8, 37, false, true), (1, 7, false, true)], [(3, 107, false, false)],
  [(4, 73, false, true), (1, 5, false, false)], [(5, 59, true, true)], [(1, 367, true, false)],
  [(1, 263, true, true)], [(7, 43, false, true)], [(3, 109, true, false)],
  [(24, 13, true, false), (1, 29, false, false)], [(1, 373, true, false)], [], [],
  [(1, 269, true, true)], [(5, 61, false, true)], [(1, 379, true, false)],
  [(2, 173, false, false)], [(4, 83, false, false), (1, 5, false, false)],
  [(1, 383, false, false)], [(3, 101, true, true)], [(7, 47, false, false)], [],
  [(1, 277, false, true)], [(1, 389, false, false)], [], [(3, 103, false, true)],
  [(2, 151, false, true)], [(1, 281, true, true)], [(4, 79, false, true), (1, 5, false, false)],
  [(1, 283, false, true)], [(1, 397, true, false)], [(2, 181, true, false)], [],
  [(1, 401, false, false)], [(8, 41, true, true), (1, 7, false, true)],
  [(11, 31, true, false), (1, 13, true, false)], [(7, 47, true, true)], [],
  [(3, 107, true, true)], [(2, 157, false, true)], [(1, 409, true, false)],
  [(1, 293, true, true)], [(5, 71, false, false)], [(6, 59, false, false), (1, 5, true, true)],
  [(3, 109, false, true)], [(5, 67, false, true)], [], [], [(1, 419, false, false)],
  [(2, 191, false, false)], [(1, 421, true, false)], [], [(2, 163, false, true)],
  [(2, 193, true, false)], [], [(6, 61, true, false), (1, 5, true, true)], [],
  [(1, 307, false, true)], [(1, 431, false, false)], [(3, 127, true, false)],
  [(1, 433, true, false)], [(2, 167, true, true)], [(1, 311, true, true)],
  [(10, 37, true, false)], [(1, 313, false, true)], [(1, 439, true, false)],
  [(5, 71, true, true)], [(8, 47, false, false), (1, 7, false, true)], [(1, 443, false, false)],
  [(1, 317, true, true)], [(3, 131, false, false)], [(4, 97, true, false), (1, 5, false, false)],
  [], [(1, 449, false, false)], [(2, 173, true, true)], [(10, 37, false, true)],
  [(5, 73, false, true)], [], [(54, 7, false, true), (3, 17, true, true)], [(7, 53, true, true)],
  [(1, 457, true, false)], [(5, 79, true, false)], [(20, 19, false, true), (1, 17, true, true)],
  [(1, 461, false, false)], [], [(1, 463, true, false)], [(2, 211, true, false)],
  [(2, 179, true, true)], [(1, 467, false, false)], [],
  [(6, 67, true, false), (1, 5, true, true)], [(2, 181, false, true)], [(1, 337, false, true)],
  [(3, 139, true, false)], [(17, 23, true, true)], [(79, 5, true, true), (2, 43, true, false)],
  [], [(13, 31, true, false), (1, 11, true, true)], [(1, 479, false, false)],
  [(57, 7, false, true), (2, 31, true, false)]]
private def gd_2 : List (List (ℕ × ℕ × Bool × Bool)) := [[(5, 83, false, false)],
  [(3, 127, false, true)], [(7, 59, false, false)], [(4, 97, false, true), (1, 5, false, false)],
  [(1, 347, true, true)], [(1, 487, true, false)], [(1, 349, false, true)],
  [(5, 79, false, true)], [(1, 491, false, false)], [(18, 23, false, false)],
  [(14, 29, true, true), (1, 17, false, false)], [(1, 353, true, true)],
  [(6, 67, false, true), (1, 5, true, true)], [(2, 191, true, true)], [(3, 131, true, true)],
  [(1, 499, true, false)], [(7, 61, true, false)], [(2, 193, false, true)],
  [(1, 359, true, true)], [(2, 229, true, false)], [(4, 101, true, true), (1, 5, false, false)],
  [(3, 149, false, false)], [(7, 59, true, true)], [(1, 509, false, false)], [],
  [(6, 73, true, false), (1, 5, true, true)], [(2, 197, true, true)], [(1, 367, false, true)],
  [(5, 83, true, true)], [(5, 89, false, false)], [(2, 199, false, true)], [],
  [(4, 113, false, false), (1, 5, false, false)], [(1, 521, false, false)],
  [(1, 373, false, true)], [(1, 523, true, false)], [(7, 61, false, true)],
  [(2, 239, false, false)], [(14, 31, false, true), (1, 17, false, false)],
  [(3, 139, false, true)], [(19, 23, true, true), (1, 23, false, false)],
  [(1, 379, false, true)], [], [(11, 41, false, false), (1, 13, true, false)],
  [(3, 157, true, false)], [(4, 107, true, true), (1, 5, false, false)], [(1, 383, true, true)],
  [], [(41, 11, false, false), (2, 19, false, true)], [(12, 37, false, true)],
  [(1, 541, true, false)], [], [(24, 19, true, false), (1, 29, false, false)],
  [(1, 389, true, true)], [], [(1, 547, true, false)], [(2, 211, false, true)],
  [(7, 67, true, false)], [(16, 29, false, false), (1, 19, true, false)],
  [(2, 251, false, false)], [(6, 79, true, false), (1, 5, true, true)], [(3, 163, true, false)],
  [(1, 397, false, true)], [(1, 557, false, false)], [],
  [(11, 43, true, false), (1, 13, true, false)], [], [(1, 401, true, true)],
  [(1, 563, false, false)], [(15, 31, false, true), (1, 13, false, true)],
  [(2, 257, false, false)], [(3, 149, true, true)], [(3, 167, false, false)],
  [(1, 569, false, false)], [(13, 37, true, false), (1, 11, true, true)],
  [(1, 571, true, false)], [(1, 409, false, true)], [(3, 151, false, true)],
  [(28, 17, true, true), (2, 13, false, true)], [(7, 67, false, true)], [(1, 577, true, false)],
  [(2, 263, false, false)], [(2, 223, false, true)], [(6, 83, false, false), (1, 5, true, true)],
  [(7, 71, false, false)], [(9, 53, true, true), (1, 11, false, false)],
  [(4, 127, true, false), (1, 5, false, false)], [(5, 101, false, false)],
  [(1, 419, true, true)], [(3, 173, false, false)], [(1, 421, false, true)],
  [(2, 227, true, true)], [(2, 269, false, false)], [(1, 593, false, false)], [],
  [(2, 229, false, true)], [(2, 271, true, false)], [(5, 103, true, false)],
  [(1, 599, false, false)], [], [(1, 601, true, false)],
  [(4, 131, false, false), (1, 5, false, false)], [(1, 431, true, true)],
  [(46, 11, false, false), (4, 11, true, true), (1, 5, false, false)], [(1, 433, false, true)],
  [(1, 607, true, false)], [(3, 179, false, false)], [(2, 277, true, false)],
  [(7, 71, true, true)], [(22, 23, true, true), (1, 19, false, true)], [(1, 613, true, false)],
  [(1, 439, false, true)], [(3, 181, true, false)], [(1, 617, false, false)],
  [(2, 281, false, false)], [(1, 619, true, false)], [(1, 443, true, true)],
  [(2, 239, true, true)], [(2, 283, true, false)], [], [(10, 53, false, false)],
  [(2, 241, false, true)], [(7, 73, false, true)], [(1, 449, true, true)],
  [(23, 23, false, false)], [(1, 631, true, false)], [(5, 109, true, false)], [],
  [(3, 167, true, true)], [(31, 17, true, true), (1, 37, true, false)],
  [(41, 13, true, false), (2, 19, false, true)], [(5, 103, false, true)],
  [(1, 457, false, true)], [(1, 641, false, false)],
  [(28, 19, false, true), (2, 13, false, true)], [(1, 643, true, false)],
  [(2, 293, false, false)], [(1, 461, true, true)], [(1, 647, false, false)],
  [(1, 463, false, true)], [(3, 191, false, false)], [], [], [(1, 653, false, false)],
  [(1, 467, true, true)], [(5, 113, false, false)], [(3, 193, true, false)],
  [(3, 173, true, true)], [(1, 659, false, false)], [], [(1, 661, true, false)],
  [(13, 43, true, false), (1, 11, true, true)], [(5, 107, true, true)],
  [(79, 7, false, true), (2, 43, true, false)], [], [(12, 47, false, false)],
  [(2, 257, true, true)], [(3, 197, false, false)], [(1, 479, true, true)], [],
  [(1, 673, true, false)], [], [(2, 307, true, false)], [(1, 677, false, false)], [],
  [(7, 79, false, true)], [(3, 179, true, true)], [(1, 487, false, true)],
  [(1, 683, false, false)], [(2, 263, true, true)], [(25, 23, false, false)],
  [(12, 47, true, true)], [(1, 491, true, true)], [(2, 313, true, false)],
  [(20, 29, false, false), (1, 17, true, true)], [(1, 691, true, false)], [], [],
  [(25, 23, true, true)], [(10, 59, false, false)], [(2, 317, false, false)],
  [(1, 499, false, true)], [(2, 269, true, true)], [(1, 701, false, false)],
  [(20, 29, true, true), (1, 17, true, true)], [(16, 37, true, false), (1, 19, true, false)],
  [(1, 503, true, true)], [], [(6, 101, false, false), (1, 5, true, true)], [],
  [(1, 709, true, false)], [(9, 67, true, false), (1, 11, false, false)], [],
  [(1, 509, true, true)], [(7, 83, true, true)], [(8, 73, false, true), (1, 7, false, true)], [],
  [(3, 211, true, false)], [(1, 719, false, false)], [(2, 277, false, true)]]
private def gd_3 : List (List (ℕ × ℕ × Bool × Bool)) := [
  [(6, 103, true, false), (1, 5, true, true)], [(4, 157, true, false), (1, 5, false, false)],
  [(13, 47, false, false), (1, 11, true, true)],
  [(21, 29, false, false), (4, 5, true, true), (1, 5, false, false)], [(3, 191, true, true)],
  [(1, 727, true, false)], [(2, 331, true, false)], [(1, 521, true, true)],
  [(2, 281, true, true)], [(1, 523, false, true)], [(1, 733, true, false)], [],
  [(2, 283, false, true)], [(5, 127, true, false)], [(20, 31, true, false), (1, 17, true, true)],
  [(1, 739, true, false)], [(27, 23, false, false), (1, 23, true, true)],
  [(2, 337, true, false)], [(1, 743, false, false)], [(10, 61, false, true)],
  [(4, 149, true, true), (1, 5, false, false)], [(15, 41, true, true), (1, 13, false, true)],
  [(17, 37, true, false)], [(3, 197, true, true)], [(4, 163, true, false), (1, 5, false, false)],
  [(1, 751, true, false)], [(12, 53, false, false)], [],
  [(4, 151, false, true), (1, 5, false, false)], [(3, 199, false, true)],
  [(1, 757, true, false)], [(3, 223, true, false)], [(5, 131, false, false)],
  [(1, 761, false, false)], [(2, 293, true, true)], [(2, 347, false, false)], [],
  [(1, 547, false, true)], [(11, 59, false, false), (1, 13, true, false)],
  [(2, 349, true, false)], [(1, 769, true, false)], [], [(3, 227, false, false)],
  [(1, 773, false, false)], [(12, 53, true, true)],
  [(21, 31, true, false), (4, 5, true, true), (1, 5, false, false)], [(2, 353, false, false)],
  [(28, 23, true, true), (2, 13, false, true)], [(3, 229, true, false)], [(1, 557, true, true)],
  [(9, 71, true, true), (1, 11, false, false)], [(15, 43, false, true), (1, 13, false, true)],
  [], [(4, 157, false, true), (1, 5, false, false)], [], [(1, 787, true, false)],
  [(1, 563, true, true)], [(2, 359, false, false)], [(10, 67, true, false)],
  [(3, 233, false, false)], [(11, 61, true, false), (1, 13, true, false)],
  [(5, 137, false, false)], [(7, 97, true, false)], [(1, 569, true, true)],
  [(2, 307, false, true)], [(1, 571, false, true)], [], [(3, 211, false, true)],
  [(9, 73, false, true), (1, 11, false, false)], [],
  [(134, 5, true, true), (2, 73, true, false)], [(5, 139, true, false)], [(1, 577, false, true)],
  [(1, 809, false, false)], [], [(1, 811, true, false)], [(3, 239, false, false)],
  [(2, 313, false, true)], [(4, 163, false, true), (1, 5, false, false)],
  [(13, 53, false, false), (1, 11, true, true)], [(10, 67, false, true)], [],
  [(3, 241, true, false)], [(1, 821, false, false)], [(1, 587, true, true)],
  [(1, 823, true, false)], [(2, 317, true, true)], [], [(1, 827, false, false)],
  [(7, 101, false, false)], [(1, 829, true, false)], [(1, 593, true, true)], [],
  [(30, 23, true, true)], [(2, 379, true, false)], [(4, 167, true, true), (1, 5, false, false)],
  [(6, 113, true, true), (1, 5, true, true)], [(10, 71, false, false)], [(1, 599, true, true)],
  [(37, 19, true, false), (2, 17, true, true)], [(1, 601, false, true)],
  [(2, 383, false, false)], [], [(7, 103, true, false)], [], [(3, 223, false, true)], [],
  [(1, 607, false, true)], [(19, 37, false, true), (1, 23, false, false)], [],
  [(1, 853, true, false)], [], [(2, 389, false, false)], [(1, 857, false, false)],
  [(1, 613, false, true)], [(1, 859, true, false)], [(2, 331, false, true)],
  [(5, 139, false, true)], [(1, 863, false, false)], [(1, 617, true, true)],
  [(4, 173, true, true), (1, 5, false, false)], [(1, 619, false, true)], [],
  [(7, 101, true, true)], [(3, 229, false, true)], [(11, 67, true, false), (1, 13, true, false)],
  [(8, 89, true, true), (1, 7, false, true)], [(2, 397, true, false)],
  [(104, 7, false, true), (1, 89, true, true)], [(2, 337, false, true)], [(1, 877, true, false)],
  [(32, 23, false, false)], [(9, 83, false, false), (1, 11, false, false)],
  [(1, 881, false, false)], [(2, 401, false, false)], [(1, 883, true, false)], [],
  [(3, 233, true, true)], [(1, 887, false, false)], [(32, 23, true, true)],
  [(6, 127, true, false), (1, 5, true, true)], [(10, 73, false, true)],
  [(57, 13, false, true), (2, 31, true, false)], [(16, 47, false, false), (1, 19, true, false)],
  [(3, 263, false, false)], [(4, 179, true, true), (1, 5, false, false)], [],
  [(1, 641, true, true)], [(24, 31, false, true), (1, 29, false, false)],
  [(1, 643, false, true)], [(14, 53, true, true), (1, 17, false, false)], [(2, 347, true, true)],
  [], [(4, 181, false, true), (1, 5, false, false)], [(1, 647, true, true)],
  [(1, 907, true, false)], [(3, 239, true, true)], [], [(1, 911, false, false)],
  [(8, 97, true, false), (1, 7, false, true)], [(9, 83, true, true), (1, 11, false, false)],
  [(1, 653, true, true)], [(3, 241, false, true)], [(6, 131, false, false), (1, 5, true, true)],
  [(2, 353, true, true)], [(1, 919, true, false)], [(7, 107, true, true)],
  [(2, 419, false, false)], [(1, 659, true, true)], [(5, 149, true, true)],
  [(1, 661, false, true)], [(2, 421, true, false)], [], [(1, 929, false, false)], [],
  [(41, 19, true, false), (2, 19, false, true)], [(10, 79, true, false)], [(2, 359, true, true)],
  [(71, 11, false, false), (1, 61, false, true)], [(5, 151, false, true)],
  [(1, 937, true, false)], [(41, 19, false, true), (2, 19, false, true)],
  [(6, 127, false, true), (1, 5, true, true)], [(1, 941, false, false)], [(1, 673, false, true)],
  [(9, 89, false, false), (1, 11, false, false)], [], [(5, 163, true, false)],
  [(1, 947, false, false)], [(1, 677, true, true)], [(17, 47, false, false)],
  [(8, 97, false, true), (1, 7, false, true)], [(12, 67, true, false)], [(1, 953, false, false)],
  [(2, 367, false, true)], [(3, 281, false, false)], [(1, 683, true, true)], [],
  [(6, 137, false, false), (1, 5, true, true)], []]
private def gd_4 : List (List (ℕ × ℕ × Bool × Bool)) := [
  [(26, 31, true, false), (1, 31, true, false)], [(3, 283, true, false)],
  [(10, 79, false, true)], [(4, 193, false, true), (1, 5, false, false)],
  [(2, 439, true, false)], [(1, 967, true, false)], [(5, 167, false, false)],
  [(2, 373, false, true)], [(1, 971, false, false)], [(7, 113, true, true)],
  [(5, 157, false, true)], [(2, 443, false, false)],
  [(20, 41, false, false), (1, 17, true, true)], [(1, 977, false, false)],
  [(12, 67, false, true)], [(10, 83, false, false)],
  [(28, 29, true, true), (2, 13, false, true)], [(1, 701, true, true)], [(1, 983, false, false)],
  [(22, 37, false, true), (1, 19, false, true)], [(2, 379, false, true)], [],
  [(2, 449, false, false)], [(19, 43, false, true), (1, 23, false, false)],
  [(8, 101, true, true), (1, 7, false, true)], [(1, 991, true, false)], [(1, 709, false, true)],
  [], [(4, 199, false, true), (1, 5, false, false)], [(2, 383, true, true)],
  [(1, 997, true, false)], [(27, 31, true, false), (1, 23, true, true)], [(3, 263, true, true)],
  [(119, 7, false, true), (5, 23, true, true)], [], [(5, 173, false, false)], [],
  [(2, 457, true, false)], [(1, 719, true, true)], [(12, 71, false, false)],
  [(1, 1009, true, false)], [(5, 163, false, true)], [(2, 389, true, true)],
  [(1, 1013, false, false)], [(2, 461, false, false)],
  [(29, 29, true, true), (4, 7, false, true), (1, 5, false, false)],
  [(37, 23, false, false), (2, 17, true, true)], [(1, 727, false, true)],
  [(1, 1019, false, false)], [], [(1, 1021, true, false)], [(3, 269, true, true)],
  [(20, 43, true, false), (1, 17, true, true)], [(18, 47, true, true)], [(1, 733, false, true)],
  [(2, 467, false, false)], [(23, 37, false, true)], [(3, 271, false, true)],
  [(1, 1031, false, false)], [(2, 397, false, true)], [(1, 1033, true, false)],
  [(1, 739, false, true)], [(5, 167, true, true)], [(12, 71, true, true)],
  [(5, 179, false, false)], [(1, 1039, true, false)], [(1, 743, true, true)],
  [(7, 127, true, false)], [(2, 401, true, true)], [(3, 307, true, false)],
  [(79, 11, true, true), (2, 43, true, false)], [],
  [(28, 31, false, true), (2, 13, false, true)], [(1, 1049, false, false)],
  [(5, 181, true, false)], [(1, 1051, true, false)], [(3, 277, false, true)],
  [(2, 479, false, false)], [(4, 211, false, true), (1, 5, false, false)], [],
  [(3, 311, false, false)], [(11, 79, false, true), (1, 13, true, false)],
  [(1, 757, false, true)], [(1, 1061, false, false)],
  [(8, 113, false, false), (1, 7, false, true)], [(1, 1063, true, false)],
  [(3, 313, true, false)], [(1, 761, true, true)], [(9, 97, false, true), (1, 11, false, false)],
  [(3, 281, true, true)], [(1, 1069, true, false)], [(17, 53, false, false)],
  [(2, 487, true, false)], [(5, 173, true, true)], [(7, 131, false, false)],
  [(3, 283, false, true)], [(1, 769, false, true)], [(3, 317, false, false)],
  [(11, 83, false, false), (1, 13, true, false)], [(2, 491, false, false)],
  [(19, 47, true, true), (1, 23, false, false)], [(1, 773, true, true)], [],
  [(31, 29, true, true), (1, 37, true, false)], [(10, 89, true, true)], [(1, 1087, true, false)],
  [], [(2, 419, true, true)], [(1, 1091, false, false)], [(7, 127, false, true)],
  [(1, 1093, true, false)], [(2, 421, false, true)], [], [(1, 1097, false, false)],
  [(2, 499, true, false)], [(40, 23, false, false)], [], [(1, 787, false, true)],
  [(1, 1103, false, false)], [], [(54, 17, true, true), (3, 17, true, true)],
  [(2, 503, false, false)], [(5, 191, false, false)], [(1, 1109, false, false)],
  [(5, 179, true, true)], [(9, 101, true, true), (1, 11, false, false)],
  [(11, 83, true, true), (1, 13, true, false)], [(3, 293, true, true)],
  [(4, 223, false, true), (1, 5, false, false)], [(1, 797, true, true)],
  [(1, 1117, true, false)], [(20, 47, false, false), (1, 17, true, true)],
  [(2, 509, false, false)], [(2, 431, true, true)], [(5, 181, false, true)],
  [(1, 1123, true, false)], [(13, 73, true, false), (1, 11, true, true)],
  [(2, 433, false, true)], [(7, 131, true, true)], [], [(1, 1129, true, false)], [], [],
  [(1, 809, true, true)], [(18, 53, false, false)], [(1, 811, false, true)],
  [(41, 23, true, true), (2, 19, false, true)], [(20, 47, true, true), (1, 17, true, true)],
  [(14, 67, false, true), (1, 17, false, false)], [(7, 139, true, false)],
  [(2, 439, false, true)], [(5, 197, false, false)],
  [(22, 43, false, true), (1, 19, false, true)], [(10, 97, true, false)],
  [(2, 521, false, false)], [(26, 37, true, false), (1, 31, true, false)], [],
  [(1, 821, true, true)], [(1, 1151, false, false)], [(1, 823, false, true)],
  [(1, 1153, true, false)], [(5, 199, true, false)], [(18, 53, true, true)],
  [(11, 89, false, false), (1, 13, true, false)], [(1, 827, true, true)],
  [(16, 61, true, false), (1, 19, true, false)], [(1, 829, false, true)],
  [(6, 157, false, true), (1, 5, true, true)], [(1, 1163, false, false)],
  [(42, 23, true, true), (2, 23, false, false)], [(4, 233, true, true), (1, 5, false, false)],
  [(3, 307, false, true)], [(2, 449, true, true)], [(6, 167, false, false), (1, 5, true, true)],
  [], [(1, 1171, true, false)], [(24, 41, false, false), (1, 29, false, false)], [],
  [(1, 839, true, true)], [], [(9, 107, true, true), (1, 11, false, false)],
  [(7, 137, true, true)], [(3, 347, false, false)], [(1, 1181, false, false)],
  [(3, 311, true, true)], [(10, 97, false, true)], [(5, 191, true, true)],
  [(90, 11, false, false), (8, 11, true, true), (1, 7, false, true)], [(1, 1187, false, false)],
  [(2, 457, false, true)], [(3, 313, false, true)], [(2, 541, true, false)],
  [(10, 101, false, false)], [(1, 1193, false, false)], [(1, 853, false, true)],
  [(7, 139, false, true)], [(5, 193, false, true)],
  [(9, 113, false, false), (1, 11, false, false)], [(2, 461, true, true)], [(1, 857, true, true)]]
private def gd_5 : List (List (ℕ × ℕ × Bool × Bool)) := [[(1, 1201, true, false)],
  [(1, 859, false, true)], [(2, 547, true, false)], [(3, 317, true, true)],
  [(6, 163, false, true), (1, 5, true, true)], [(14, 71, true, true), (1, 17, false, false)],
  [(1, 863, true, true)], [(4, 263, false, false), (1, 5, false, false)],
  [(6, 173, false, false), (1, 5, true, true)], [(12, 83, true, true)], [(1, 1213, true, false)],
  [(2, 467, true, true)], [(10, 103, true, false)], [(1, 1217, false, false)], [],
  [(15, 67, false, true), (1, 13, false, true)], [(3, 359, false, false)],
  [(5, 197, true, true)], [(1, 1223, false, false)], [(5, 211, true, false)],
  [(2, 557, false, false)], [], [(1, 877, false, true)], [(1, 1229, false, false)],
  [(24, 43, true, false), (1, 29, false, false)], [(1, 1231, true, false)],
  [(10, 101, true, true)], [(1, 881, true, true)], [(54, 19, false, true), (3, 17, true, true)],
  [(1, 883, false, true)], [(1, 1237, true, false)], [(2, 563, false, false)], [],
  [(14, 73, false, true), (1, 17, false, false)], [(1, 887, true, true)],
  [(9, 113, true, true), (1, 11, false, false)], [(8, 127, false, true), (1, 7, false, true)],
  [(2, 479, true, true)], [(45, 23, true, true)], [(3, 367, true, false)],
  [(1, 1249, true, false)], [(22, 47, true, true), (1, 19, false, true)],
  [(2, 569, false, false)], [(6, 179, false, false), (1, 5, true, true)], [],
  [(4, 251, true, true), (1, 5, false, false)], [(2, 571, true, false)], [(3, 331, false, true)],
  [(1, 1259, false, false)], [], [(11, 97, true, false), (1, 13, true, false)],
  [(10, 107, false, false)], [(12, 89, false, false)],
  [(211, 5, false, false), (1, 181, false, true)], [(2, 487, false, true)],
  [(6, 181, true, false), (1, 5, true, true)], [(3, 373, true, false)], [(1, 907, false, true)],
  [(26, 41, false, false), (1, 31, true, false)], [],
  [(16, 67, true, false), (1, 19, true, false)], [(4, 277, true, false), (1, 5, false, false)],
  [(1, 911, true, true)], [(1, 1277, false, false)],
  [(13, 83, false, false), (1, 11, true, true)], [(1, 1279, true, false)],
  [(3, 337, false, true)], [(7, 149, true, true)], [(1, 1283, false, false)],
  [(8, 131, true, true), (1, 7, false, true)], [(4, 257, true, true), (1, 5, false, false)],
  [(1, 919, false, true)], [(7, 157, true, false)], [(1, 1289, false, false)], [],
  [(1, 1291, true, false)], [(47, 23, false, false)], [(5, 223, true, false)],
  [(154, 7, false, true), (2, 71, true, true)], [(35, 31, true, false), (2, 19, true, false)],
  [(1, 1297, true, false)], [(7, 151, false, true)], [(12, 89, true, true)],
  [(1, 929, true, true)], [(3, 383, false, false)], [(1, 1303, true, false)],
  [(2, 593, false, false)], [(10, 107, true, true)], [(1, 1307, false, false)],
  [(2, 503, true, true)], [(64, 17, true, true), (6, 11, false, false), (1, 5, true, true)], [],
  [(1, 937, false, true)], [(11, 101, false, false), (1, 13, true, false)], [],
  [(4, 263, true, true), (1, 5, false, false)], [(5, 227, false, false)], [(1, 941, true, true)],
  [(1, 1319, false, false)], [(27, 41, false, false), (1, 23, true, true)],
  [(1, 1321, true, false)], [(2, 601, true, false)], [(2, 509, true, true)],
  [(30, 37, true, false)], [(1, 947, true, true)], [(1, 1327, true, false)],
  [(5, 229, true, false)], [(10, 109, false, true)],
  [(222, 5, false, false), (5, 43, false, true)], [], [(10, 113, false, false)],
  [(1, 953, true, true)], [(2, 607, true, false)], [(7, 163, true, false)], [],
  [(30, 37, false, true)], [], [(3, 353, true, true)],
  [(8, 137, true, true), (1, 7, false, true)], [(24, 47, false, false), (1, 29, false, false)],
  [(4, 269, true, true), (1, 5, false, false)], [(9, 127, true, false), (1, 11, false, false)],
  [(4, 293, false, false), (1, 5, false, false)], [(2, 613, true, false)],
  [(3, 397, true, false)], [(5, 233, false, false)], [], [(1, 967, false, true)],
  [(2, 521, true, true)], [], [(2, 617, false, false)], [], [(1, 971, true, true)],
  [(1, 1361, false, false)], [(2, 619, true, false)], [(3, 401, false, false)],
  [(3, 359, true, true)], [], [(1, 1367, false, false)], [(1, 977, true, true)],
  [(7, 167, false, false)], [(13, 89, false, false), (1, 11, true, true)],
  [(60, 19, false, true), (3, 19, false, true)], [(1, 1373, false, false)], [],
  [(50, 23, false, false), (1, 43, false, true)], [(1, 983, true, true)],
  [(12, 97, true, false)], [(10, 113, true, true)], [(17, 67, false, true)],
  [(1, 1381, true, false)], [(5, 223, false, true)],
  [(31, 37, false, true), (1, 37, true, false)], [(4, 277, false, true), (1, 5, false, false)],
  [(5, 239, false, false)], [(1, 991, false, true)], [(2, 631, true, false)], [],
  [(3, 409, true, false)], [], [(6, 199, true, false), (1, 5, true, true)],
  [(3, 367, false, true)], [(1, 997, false, true)],
  [(9, 127, false, true), (1, 11, false, false)], [(5, 241, true, false)],
  [(1, 1399, true, false)], [(25, 47, false, false)], [(7, 163, false, true)],
  [(19, 61, false, true), (1, 23, false, false)], [(20, 59, false, false), (1, 17, true, true)],
  [(4, 281, true, true), (1, 5, false, false)], [(2, 541, false, true)], [(5, 227, true, true)],
  [(1, 1409, false, false)], [(2, 641, false, false)],
  [(14, 83, true, true), (1, 17, false, false)], [(1, 1009, false, true)],
  [(32, 37, true, false)], [(2, 643, true, false)], [(12, 97, false, true)],
  [(3, 373, false, true)], [(1, 1013, true, true)], [(5, 229, false, true)],
  [(41, 29, false, false), (2, 19, false, true)], [(2, 547, false, true)],
  [(1, 1423, true, false)], [(3, 419, false, false)], [], [(1, 1019, true, true)],
  [(32, 37, false, true)], [(1, 1429, true, false)], [(52, 23, false, false)],
  [(3, 421, true, false)], [(1, 1433, false, false)], [(12, 101, false, false)],
  [(171, 7, true, false), (2, 79, false, true)], [(2, 653, false, false)],
  [(15, 79, false, true), (1, 13, false, true)], [(1, 1439, false, false)],
  [(3, 379, false, true)]]
private def gd_6 : List (List (ℕ × ℕ × Bool × Bool)) := [
  [(9, 131, true, true), (1, 11, false, false)], [], [(1, 1031, true, true)],
  [(5, 233, true, true)], [(1, 1033, false, true)], [(1, 1447, true, false)],
  [(2, 557, true, true)], [(2, 659, false, false)], [(1, 1451, false, false)],
  [(23, 53, false, false)], [(1, 1453, true, false)], [(1, 1039, false, true)],
  [(3, 383, true, true)], [(26, 47, false, false), (1, 31, true, false)],
  [(33, 37, true, false)], [(1, 1459, true, false)], [(18, 67, false, true)], [],
  [(12, 103, true, false)], [(2, 563, true, true)], [(3, 431, false, false)], [],
  [(7, 179, false, false)], [(1, 1049, true, true)], [], [(1, 1471, true, false)],
  [(3, 433, true, false)], [(23, 53, true, true)], [(12, 101, true, true)],
  [(8, 157, true, false), (1, 7, false, true)], [(6, 211, true, false), (1, 5, true, true)],
  [(3, 389, true, true)], [(2, 569, true, true)], [(1, 1481, false, false)],
  [(5, 239, true, true)], [(1, 1483, true, false)], [(2, 571, false, true)],
  [(1, 1061, true, true)], [(1, 1487, false, false)], [(1, 1063, false, true)],
  [(1, 1489, true, false)], [(5, 257, false, false)], [], [(1, 1493, false, false)],
  [(5, 241, false, true)], [(54, 23, true, true), (3, 17, true, true)], [(1, 1069, false, true)],
  [], [(1, 1499, false, false)], [(2, 577, false, true)],
  [(16, 79, true, false), (1, 19, true, false)], [(2, 683, false, false)],
  [(12, 103, false, true)], [(179, 7, false, true), (5, 37, true, false)],
  [(3, 443, false, false)], [(9, 137, true, true), (1, 11, false, false)],
  [(3, 397, false, true)], [], [(1, 1511, false, false)], [],
  [(14, 89, true, true), (1, 17, false, false)], [(11, 113, true, true), (1, 13, true, false)],
  [(24, 53, false, false), (1, 29, false, false)],
  [(31, 41, false, false), (1, 37, true, false)], [], [(12, 107, false, false)],
  [(2, 691, true, false)], [(1, 1087, false, true)], [(1, 1523, false, false)],
  [(3, 401, true, true)], [(5, 263, false, false)], [(2, 587, true, true)],
  [(1, 1091, true, true)], [(9, 139, false, true), (1, 11, false, false)],
  [(1, 1093, false, true)], [(1, 1531, true, false)],
  [(8, 163, true, false), (1, 7, false, true)], [(31, 41, true, true), (1, 37, true, false)],
  [(4, 307, false, true), (1, 5, false, false)], [(1, 1097, true, true)],
  [(24, 53, true, true), (1, 29, false, false)], [(8, 157, false, true), (1, 7, false, true)],
  [(7, 179, true, true)], [(19, 67, false, true), (1, 23, false, false)], [(2, 593, true, true)],
  [(1, 1543, true, false)], [(1, 1103, true, true)], [(10, 131, false, false)],
  [(35, 37, true, false), (2, 19, true, false)], [(12, 109, true, false)],
  [(1, 1549, true, false)], [(4, 337, true, false), (1, 5, false, false)], [],
  [(1, 1109, true, true)], [(3, 457, true, false)], [(4, 311, true, true), (1, 5, false, false)],
  [(5, 251, true, true)], [(2, 599, true, true)], [(1, 1559, false, false)],
  [(2, 709, true, false)], [(6, 223, true, false), (1, 5, true, true)], [(2, 601, false, true)],
  [(1, 1117, false, true)], [(4, 313, false, true), (1, 5, false, false)],
  [(7, 191, false, false)], [(1, 1567, true, false)],
  [(42, 31, false, true), (2, 23, false, false)], [(8, 167, false, false), (1, 7, false, true)],
  [(1, 1571, false, false)], [(1, 1123, false, true)],
  [(119, 11, true, true), (5, 23, true, true)], [(3, 463, true, false)], [],
  [(16, 83, false, false), (1, 19, true, false)], [(2, 607, false, true)],
  [(1, 1579, true, false)], [(1, 1129, false, true)], [(2, 719, false, false)],
  [(1, 1583, false, false)], [(15, 89, false, false), (1, 13, false, true)],
  [(4, 317, true, true), (1, 5, false, false)], [(13, 103, true, false), (1, 11, true, true)],
  [(3, 467, false, false)], [(6, 227, false, false), (1, 5, true, true)], [],
  [(12, 109, false, true)], [(3, 419, true, true)], [(2, 613, false, true)],
  [(20, 67, true, false), (1, 17, true, true)], [(17, 79, true, false)],
  [(1, 1597, true, false)], [(10, 131, true, true)], [(2, 727, true, false)],
  [(1, 1601, false, false)], [], [(6, 229, true, false), (1, 5, true, true)],
  [(2, 617, true, true)], [(58, 23, true, true)], [(1, 1607, false, false)],
  [(31, 43, false, true), (1, 37, true, false)], [(1, 1609, true, false)],
  [(14, 97, true, false), (1, 17, false, false)], [(1, 1151, true, true)],
  [(1, 1613, false, false)], [(1, 1153, false, true)], [(7, 197, false, false)],
  [(10, 137, false, false)], [], [(1, 1619, false, false)],
  [(15, 89, true, true), (1, 13, false, true)], [(1, 1621, true, false)],
  [(22, 61, false, true), (1, 19, false, true)], [(4, 353, false, false), (1, 5, false, false)],
  [(104, 13, false, true), (1, 89, true, true)], [(2, 739, true, false)],
  [(1, 1627, true, false)], [(1, 1163, true, true)], [(5, 281, false, false)],
  [(5, 263, true, true)], [(7, 199, true, false)], [(19, 71, true, true), (1, 23, false, false)],
  [(2, 743, false, false)], [(37, 37, true, false), (2, 17, true, true)],
  [(1, 1637, false, false)], [(3, 431, true, true)], [(1, 1171, false, true)],
  [(2, 631, false, true)], [(5, 283, true, false)], [(7, 191, true, true)], [],
  [(3, 433, false, true)], [], [(13, 107, false, false), (1, 11, true, true)],
  [(14, 97, false, true), (1, 17, false, false)], [(12, 113, true, true)],
  [(4, 359, false, false), (1, 5, false, false)], [(2, 751, true, false)],
  [(1, 1181, true, true)], [(4, 331, false, true), (1, 5, false, false)],
  [(3, 487, true, false)], [(1, 1657, true, false)], [], [(7, 193, false, true)],
  [(9, 151, false, true), (1, 11, false, false)], [(1, 1187, true, true)],
  [(1, 1663, true, false)], [(9, 157, true, false), (1, 11, false, false)],
  [(2, 757, true, false)], [(1, 1667, false, false)], [(3, 439, false, true)],
  [(1, 1669, true, false)], [(1, 1193, true, true)], [(2, 643, false, true)],
  [(6, 239, false, false), (1, 5, true, true)], [(2, 761, false, false)],
  [(279, 5, true, true), (1, 239, true, true)], [(17, 83, false, false)], [],
  [(13, 109, true, false), (1, 11, true, true)], [(5, 271, false, true)]]
private def gd_7 : List (List (ℕ × ℕ × Bool × Bool)) := [[(1, 1201, false, true)],
  [(2, 647, true, true)], [(3, 443, true, true)], [(4, 337, false, true), (1, 5, false, false)],
  [], [(6, 241, true, false), (1, 5, true, true)], [(4, 367, true, false), (1, 5, false, false)],
  [(20, 71, false, false), (1, 17, true, true)], [(18, 79, true, false)],
  [(2, 769, true, false)], [(1, 1693, true, false)], [(7, 197, true, true)],
  [(10, 139, false, true)], [(1, 1697, false, false)], [(1, 1213, false, true)],
  [(1, 1699, true, false)], [(2, 773, false, false)], [(30, 47, true, true)],
  [(11, 131, false, false), (1, 13, true, false)], [(1, 1217, true, true)],
  [(284, 5, true, true), (2, 131, true, true)], [(3, 449, true, true)], [],
  [(1, 1709, false, false)], [(3, 503, false, false)], [(7, 199, false, true)],
  [(1, 1223, true, true)], [(2, 659, true, true)],
  [(286, 5, false, false), (3, 101, false, false)],
  [(4, 373, true, false), (1, 5, false, false)], [(5, 277, false, true)],
  [(2, 661, false, true)], [], [(1, 1229, true, true)], [(18, 79, false, true)],
  [(1, 1723, true, false)], [(6, 233, true, true), (1, 5, true, true)], [],
  [(9, 157, false, true), (1, 11, false, false)], [(9, 163, true, false), (1, 11, false, false)],
  [(111, 13, true, false), (5, 23, false, false)], [(3, 509, false, false)],
  [(1, 1237, false, true)], [(1, 1733, false, false)],
  [(50, 29, false, false), (1, 43, false, true)], [(4, 347, true, true), (1, 5, false, false)],
  [(3, 457, false, true)], [(20, 73, true, false), (1, 17, true, true)],
  [(31, 47, false, false), (1, 37, true, false)], [(13, 113, false, false), (1, 11, true, true)],
  [(1, 1741, true, false)], [(5, 281, true, true)],
  [(4, 379, true, false), (1, 5, false, false)], [(4, 349, false, true), (1, 5, false, false)],
  [(34, 43, true, false), (1, 29, true, true)], [(1, 1747, true, false)],
  [(1, 1249, false, true)], [(2, 673, false, true)],
  [(14, 103, false, true), (1, 17, false, false)], [(3, 461, true, true)],
  [(1, 1753, true, false)], [(5, 283, false, true)],
  [(11, 131, true, true), (1, 13, true, false)], [(6, 251, false, false), (1, 5, true, true)],
  [(10, 149, false, false)], [(1, 1759, true, false)], [(2, 677, true, true)],
  [(4, 383, false, false), (1, 5, false, false)], [(1, 1259, true, true)], [],
  [(4, 353, true, true), (1, 5, false, false)], [(20, 73, false, true), (1, 17, true, true)], [],
  [(40, 37, true, false)], [(9, 167, false, false), (1, 11, false, false)],
  [(3, 521, false, false)], [], [(8, 181, false, true), (1, 7, false, true)],
  [(3, 467, true, true)], [(2, 683, true, true)], [(1, 1777, true, false)],
  [(3, 523, true, false)], [(2, 809, false, false)], [(5, 307, true, false)],
  [(10, 151, true, false)], [(1, 1783, true, false)], [(2, 811, true, false)],
  [(13, 113, true, true), (1, 11, true, true)], [(1, 1787, false, false)],
  [(1, 1277, true, true)], [(1, 1789, true, false)], [(1, 1279, false, true)],
  [(28, 53, true, true), (2, 13, false, true)], [(9, 163, false, true), (1, 11, false, false)],
  [], [(32, 47, false, false)], [(1, 1283, true, true)], [(17, 89, false, false)],
  [(6, 257, false, false), (1, 5, true, true)], [], [(1, 1801, true, false)], [],
  [(5, 311, false, false)], [(1, 1289, true, true)], [(2, 821, false, false)],
  [(1, 1291, false, true)], [], [(18, 83, true, true)], [(1, 1811, false, false)],
  [(37, 41, false, false), (2, 17, true, true)], [(41, 37, true, false), (2, 19, false, true)],
  [(7, 211, false, true)], [(1, 1297, false, true)], [(5, 293, true, true)],
  [(10, 149, true, true)], [(2, 827, false, false)], [(3, 479, true, true)],
  [(1, 1301, true, true)], [(1, 1823, false, false)], [(1, 1303, false, true)],
  [(21, 73, true, false), (4, 5, true, true), (1, 5, false, false)],
  [(4, 397, true, false), (1, 5, false, false)], [(41, 37, false, true), (2, 19, false, true)],
  [(7, 223, true, false)], [(1, 1307, true, true)], [(1, 1831, true, false)],
  [(139, 11, false, false), (1, 167, false, false)], [(17, 89, true, true)],
  [(4, 367, false, true), (1, 5, false, false)], [(23, 67, true, false)],
  [(9, 167, true, true), (1, 11, false, false)], [(5, 317, false, false)],
  [(3, 541, true, false)], [(6, 263, false, false), (1, 5, true, true)],
  [(10, 151, false, true)], [(2, 709, false, true)],
  [(4, 401, false, false), (1, 5, false, false)], [(2, 839, false, false)],
  [(1, 1319, true, true)], [], [(1, 1321, false, true)], [(3, 487, false, true)],
  [(33, 47, false, false)], [(10, 157, true, false)], [(12, 127, false, true)],
  [(309, 5, true, true), (3, 109, true, false)], [], [(1, 1327, false, true)],
  [(119, 13, false, true), (5, 23, true, true)], [(3, 547, true, false)],
  [(1, 1861, true, false)], [(23, 67, false, true)],
  [(222, 7, true, false), (5, 43, false, true)], [(4, 373, false, true), (1, 5, false, false)],
  [(3, 491, true, true)], [(1, 1867, true, false)], [], [(2, 719, true, true)],
  [(1, 1871, false, false)], [(8, 191, true, true), (1, 7, false, true)],
  [(1, 1873, true, false)], [(15, 103, false, true), (1, 13, false, true)],
  [(14, 113, false, false), (1, 17, false, false)], [(1, 1877, false, false)],
  [(7, 229, true, false)], [(1, 1879, true, false)],
  [(20, 79, true, false), (1, 17, true, true)], [(4, 409, true, false), (1, 5, false, false)],
  [(6, 269, false, false), (1, 5, true, true)], [], [(2, 857, false, false)], [], [],
  [(1, 1889, false, false)], [(2, 859, true, false)],
  [(8, 193, false, true), (1, 7, false, true)], [], [(3, 557, false, false)],
  [(4, 379, false, true), (1, 5, false, false)], [(3, 499, false, true)],
  [(30, 53, false, false)], [(2, 863, false, false)],
  [(27, 59, false, false), (1, 23, true, true)], [(1, 1901, false, false)],
  [(6, 257, true, true), (1, 5, true, true)], [(5, 307, false, true)], [(18, 89, false, false)],
  [(1, 1361, true, true)], [(1, 1907, false, false)],
  [(34, 47, false, false), (1, 29, true, true)], [(19, 83, true, true), (1, 23, false, false)],
  [(7, 233, false, false)], [(3, 503, true, true)], [(1, 1913, false, false)],
  [(1, 1367, true, true)], [(10, 157, false, true)],
  [(24, 67, true, false), (1, 29, false, false)], [(7, 223, false, true)],
  [(30, 53, true, true)], [(5, 331, true, false)]]
private def gd_8 : List (List (ℕ × ℕ × Bool × Bool)) := [[(2, 739, false, true)],
  [(1, 1373, true, true)], [(10, 163, true, false)],
  [(321, 5, false, false), (7, 47, false, false)], [], [(70, 23, false, false)],
  [(5, 311, true, true)], [(2, 877, true, false)], [(1, 1931, false, false)],
  [(2, 743, true, true)], [(1, 1933, true, false)], [(3, 509, true, true)], [],
  [(70, 23, true, true)], [(2, 881, false, false)], [(6, 277, true, false), (1, 5, true, true)],
  [(5, 313, false, true)], [(3, 571, true, false)], [(2, 883, true, false)], [],
  [(12, 137, false, false)], [(6, 263, true, true), (1, 5, true, true)],
  [(15, 107, true, true), (1, 13, false, true)], [(1, 1949, false, false)],
  [(8, 199, false, true), (1, 7, false, true)], [(1, 1951, true, false)],
  [(2, 751, false, true)], [], [(5, 337, true, false)],
  [(13, 127, true, false), (1, 11, true, true)], [(16, 103, true, false), (1, 19, true, false)],
  [(1, 1399, false, true)], [(7, 239, false, false)],
  [(31, 53, false, false), (1, 37, true, false)], [(3, 577, true, false)],
  [(11, 151, true, false), (1, 13, true, false)], [(27, 61, true, false), (1, 23, true, true)],
  [(5, 317, true, true)], [(6, 281, false, false), (1, 5, true, true)], [(2, 757, false, true)],
  [(7, 229, false, true)], [(10, 167, false, false)], [], [(1, 1409, true, true)],
  [(12, 139, true, false)], [(20, 83, false, false), (1, 17, true, true)],
  [(7, 241, true, false)], [(53, 31, false, true), (2, 29, false, false)],
  [(1, 1979, false, false)], [(3, 521, true, true)], [(6, 283, true, false), (1, 5, true, true)],
  [(72, 23, false, false)], [(8, 211, true, false), (1, 7, false, true)],
  [(4, 397, false, true), (1, 5, false, false)], [], [(1, 1987, true, false)],
  [(10, 163, false, true)], [(57, 29, true, true), (2, 31, true, false)],
  [(45, 37, true, false)], [(1, 1423, false, true)], [(1, 1993, true, false)],
  [(28, 59, true, true), (2, 13, false, true)], [(2, 907, true, false)],
  [(1, 1997, false, false)], [(1, 1427, true, true)], [(1, 1999, true, false)],
  [(1, 1429, false, true)], [], [(1, 2003, false, false)], [(2, 911, false, false)],
  [(45, 37, false, true)], [(1, 1433, true, true)], [],
  [(20, 83, true, true), (1, 17, true, true)], [(2, 773, true, true)], [(1, 2011, true, false)],
  [(5, 347, false, false)], [], [(1, 1439, true, true)], [(3, 593, false, false)],
  [(1, 2017, true, false)], [], [(4, 439, true, false), (1, 5, false, false)],
  [(36, 47, false, false), (1, 43, true, false)], [(2, 919, true, false)],
  [(25, 67, false, true)], [(5, 349, true, false)], [(1, 1447, false, true)],
  [(1, 2027, false, false)], [], [(1, 2029, true, false)],
  [(24, 71, false, false), (1, 29, false, false)], [(1, 1451, true, true)],
  [(16, 107, false, false), (1, 19, true, false)], [(1, 1453, false, true)],
  [(154, 11, true, true), (2, 71, true, true)], [(3, 599, false, false)],
  [(10, 167, true, true)], [(1, 2039, false, false)], [(17, 101, false, false)],
  [(10, 173, false, false)], [(1, 1459, false, true)], [(2, 929, false, false)],
  [(4, 409, false, true), (1, 5, false, false)], [(2, 787, false, true)],
  [(5, 353, false, false)], [(244, 7, true, false), (1, 293, false, false)],
  [(6, 277, false, true), (1, 5, true, true)], [(6, 293, false, false), (1, 5, true, true)],
  [(5, 331, false, true)], [(1, 2053, true, false)], [], [(3, 541, false, true)],
  [(15, 113, true, true), (1, 13, false, true)], [(7, 251, false, false)],
  [(1, 1471, false, true)], [], [(2, 937, true, false)], [(1, 2063, false, false)],
  [(3, 607, true, false)], [(4, 449, false, false), (1, 5, false, false)], [],
  [(8, 211, false, true), (1, 7, false, true)], [(1, 2069, false, false)],
  [(2, 941, false, false)], [(16, 109, true, false), (1, 19, true, false)],
  [(2, 797, true, true)], [(1, 1481, true, true)], [(42, 41, true, true), (2, 23, false, false)],
  [(1, 1483, false, true)], [(26, 67, true, false), (1, 31, true, false)],
  [(3, 547, false, true)], [(47, 37, true, false)], [(1, 2081, false, false)],
  [(1, 1487, true, true)], [(1, 2083, true, false)], [(1, 1489, false, true)], [],
  [(1, 2087, false, false)], [(33, 53, false, false)], [(1, 2089, true, false)],
  [(1, 1493, true, true)], [], [(134, 13, false, true), (2, 73, true, false)],
  [(47, 37, false, true)], [(4, 419, true, true), (1, 5, false, false)],
  [(2, 953, false, false)], [(3, 617, false, false)], [(1, 1499, true, true)], [],
  [(9, 191, true, true), (1, 11, false, false)], [(4, 457, true, false), (1, 5, false, false)],
  [(2, 809, true, true)], [(3, 619, true, false)], [], [(7, 257, false, false)],
  [(2, 811, false, true)], [(33, 53, true, true)], [(1, 2111, false, false)],
  [(10, 179, false, false)], [(1, 2113, true, false)], [(18, 97, false, true)],
  [(1, 1511, true, true)], [(3, 557, true, true)], [(20, 89, false, false), (1, 17, true, true)],
  [(11, 163, true, false), (1, 13, true, false)], [(77, 23, false, false)],
  [(17, 103, false, true)], [(9, 193, false, true), (1, 11, false, false)],
  [(41, 43, false, true), (2, 19, false, true)], [(104, 17, true, true), (1, 89, true, true)],
  [(57, 31, false, true), (2, 31, true, false)], [(2, 967, true, false)],
  [(1, 2129, false, false)], [(77, 23, true, true)], [(1, 2131, true, false)],
  [(1, 1523, true, true)], [(38, 47, false, false)], [(2, 821, true, true)],
  [(2, 971, false, false)], [(1, 2137, true, false)],
  [(48, 37, false, true), (1, 41, true, true)], [(2, 823, false, true)],
  [(1, 2141, false, false)], [], [(1, 2143, true, false)], [(12, 151, true, false)],
  [(3, 631, true, false)], [(16, 113, false, false), (1, 19, true, false)],
  [(4, 467, false, false), (1, 5, false, false)], [(2, 977, false, false)],
  [(2, 827, true, true)], [(5, 347, true, true)], [(1, 2153, false, false)],
  [(20, 89, true, true), (1, 17, true, true)], [(2, 829, false, true)], [(7, 263, false, false)],
  [(27, 67, true, false), (1, 23, true, true)], [(7, 251, true, true)], [(1, 1543, false, true)]]
private def gd_9 : List (List (ℕ × ℕ × Bool × Bool)) := [[(1, 2161, true, false)],
  [(2, 983, false, false)], [(5, 373, true, false)], [(23, 79, true, false)],
  [(106, 17, true, true), (1, 127, true, false)], [(9, 197, true, true), (1, 11, false, false)],
  [(1, 1549, false, true)], [(3, 571, false, true)],
  [(11, 167, false, false), (1, 13, true, false)], [],
  [(34, 53, true, true), (1, 29, true, true)], [(1, 1553, true, true)], [(12, 149, true, true)],
  [(6, 311, false, false), (1, 5, true, true)], [], [(1, 2179, true, false)],
  [(2, 991, true, false)], [(2, 839, true, true)], [(1, 1559, true, true)],
  [(10, 179, true, true)], [(8, 223, false, true), (1, 7, false, true)], [(3, 643, true, false)],
  [], [(5, 353, true, true)], [(8, 233, false, false), (1, 7, false, true)],
  [(6, 313, true, false), (1, 5, true, true)], [(3, 577, false, true)], [(1, 1567, false, true)],
  [(4, 439, false, true), (1, 5, false, false)], [(23, 79, false, true)],
  [(366, 5, true, true), (1, 439, true, false)], [(5, 379, true, false)],
  [(1, 1571, true, true)], [(26, 71, false, false), (1, 31, true, false)],
  [(17, 109, true, false)], [(1, 2203, true, false)], [(12, 151, false, true)],
  [(7, 269, false, false)], [(1, 2207, false, false)], [(10, 181, false, true)],
  [(39, 47, true, true), (1, 47, false, false)], [(1, 1579, false, true)], [],
  [(1, 2213, false, false)], [], [(4, 443, true, true), (1, 5, false, false)],
  [(1, 1583, true, true)], [(2, 853, false, true)], [(6, 317, false, false), (1, 5, true, true)],
  [(2, 1009, true, false)], [(1, 2221, true, false)], [(7, 271, true, false)], [],
  [(8, 227, true, true), (1, 7, false, true)], [(5, 359, true, true)],
  [(14, 131, true, true), (1, 17, false, false)], [(2, 857, true, true)],
  [(12, 157, true, false)], [(3, 587, true, true)], [], [(2, 859, false, true)], [],
  [(1, 1597, false, true)], [(1, 2237, false, false)],
  [(11, 167, true, true), (1, 13, true, false)], [(1, 2239, true, false)],
  [(3, 659, false, false)], [(1, 1601, true, true)], [(1, 2243, false, false)],
  [(2, 863, true, true)], [(17, 109, false, true)], [(2, 1021, true, false)],
  [(3, 661, true, false)], [(11, 173, false, false), (1, 13, true, false)],
  [(1, 1607, true, true)], [(1, 2251, true, false)], [(1, 1609, false, true)],
  [(3, 593, true, true)], [(171, 11, false, false), (2, 79, false, true)],
  [(5, 389, false, false)], [(31, 61, true, false), (1, 37, true, false)],
  [(1, 1613, true, true)], [(24, 79, true, false), (1, 29, false, false)],
  [(15, 127, true, false), (1, 13, false, true)], [(7, 263, true, true)],
  [(26, 73, true, false), (1, 31, true, false)], [(28, 67, false, true), (2, 13, false, true)],
  [(40, 47, true, true)], [(1, 1619, true, true)], [(2, 1031, false, false)],
  [(1, 2269, true, false)], [], [(7, 277, true, false)], [(1, 2273, false, false)],
  [(23, 83, false, false)], [(5, 367, false, true)], [(3, 599, true, true)],
  [(1, 1627, false, true)], [(36, 53, false, false), (1, 43, true, false)],
  [(2, 877, false, true)], [(1, 2281, true, false)], [(17, 113, false, false)],
  [(3, 601, false, true)], [(4, 457, false, true), (1, 5, false, false)],
  [(2, 1039, true, false)], [(1, 2287, true, false)], [(3, 673, true, false)],
  [(18, 107, false, false)], [(2, 881, true, true)], [(1, 1637, true, true)],
  [(1, 2293, true, false)], [(13, 149, false, false), (1, 11, true, true)],
  [(2, 883, false, true)], [(1, 2297, false, false)], [],
  [(174, 11, true, true), (1, 149, true, true)], [(36, 53, true, true), (1, 43, true, false)],
  [(3, 677, false, false)], [(5, 397, true, false)], [(7, 281, false, false)],
  [(4, 461, true, true), (1, 5, false, false)], [(2, 887, true, true)],
  [(2, 1049, false, false)], [(1, 2309, false, false)], [], [(1, 2311, true, false)],
  [(2, 1051, true, false)], [(7, 269, true, true)], [(12, 163, true, false)],
  [(52, 37, false, true)], [(6, 331, true, false), (1, 5, true, true)],
  [(11, 173, true, true), (1, 13, true, false)], [(1, 1657, false, true)],
  [(7, 283, true, false)], [(3, 683, false, false)],
  [(19, 101, true, true), (1, 23, false, false)], [(10, 197, false, false)],
  [(5, 401, false, false)], [(11, 179, false, false), (1, 13, true, false)],
  [(1, 1663, false, true)], [(3, 613, false, true)], [(7, 271, false, true)],
  [(15, 131, false, false), (1, 13, false, true)], [(1, 2333, false, false)],
  [(1, 1667, true, true)], [(4, 467, true, true), (1, 5, false, false)],
  [(1, 1669, false, true)], [(63, 31, true, false), (2, 29, true, true)],
  [(1, 2339, false, false)], [], [(1, 2341, true, false)],
  [(8, 239, true, true), (1, 7, false, true)], [], [(3, 617, true, true)],
  [(6, 317, true, true), (1, 5, true, true)], [(1, 2347, true, false)], [(10, 199, true, false)],
  [(3, 691, true, false)], [(1, 2351, false, false)], [(2, 1069, true, false)],
  [(11, 181, true, false), (1, 13, true, false)], [(10, 193, false, true)], [],
  [(1, 2357, false, false)], [(2, 907, false, true)],
  [(6, 337, true, false), (1, 5, true, true)], [(53, 37, false, true), (2, 29, false, false)],
  [(8, 241, false, true), (1, 7, false, true)], [(14, 139, false, true), (1, 17, false, false)],
  [(9, 223, true, false), (1, 11, false, false)], [(179, 11, true, true), (5, 37, true, false)],
  [], [(22, 89, true, true), (1, 19, false, true)], [(2, 911, true, true)],
  [(1, 1693, false, true)], [(1, 2371, true, false)], [(5, 409, true, false)],
  [(24, 83, false, false), (1, 29, false, false)], [(5, 383, true, true)],
  [(1, 1697, true, true)], [(1, 2377, true, false)], [(1, 1699, false, true)],
  [(12, 163, false, true)], [(1, 2381, false, false)], [(7, 277, false, true)],
  [(1, 2383, true, false)], [(15, 131, true, true), (1, 13, false, true)],
  [(25, 79, false, true)], [(284, 7, false, true), (2, 131, true, true)], [],
  [(1, 2389, true, false)], [(54, 37, true, false), (3, 17, true, true)],
  [(2, 1087, true, false)], [(1, 1709, true, true)], [],
  [(4, 479, true, true), (1, 5, false, false)], [(87, 23, false, false)],
  [(3, 631, false, true)], [(1, 2399, false, false)], [(2, 1091, false, false)]]

/-- Positional min-depth path data: entry `i` is the verified peel path for the center
    `m = i + 1` (empty list = `m` is itself a twin center); 2000 entries, every step
    re-verified arithmetically at emission (`tools/gen_paths_lean.py`). -/
def depthData : List (List (ℕ × ℕ × Bool × Bool)) :=
  gd_0 ++ gd_1 ++ gd_2 ++ gd_3 ++ gd_4 ++
    gd_5 ++ gd_6 ++ gd_7 ++ gd_8 ++ gd_9
-- GENERATED DATA END

theorem depthData_length : depthData.length = 2000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- **KERNEL CENSUS** (`decide +kernel`): all 2000 positional path witnesses pass — every
    step a genuine `PeelStep` (prime `p ≥ 5`, exact wing arithmetic), every terminal a
    genuine twin, every length `≤ 3`.  Budget: ~5×10⁵ kernel Nat-ops (ladder primality on
    wings `≤ 12001`), well inside the 300 s / 8 GB gate. -/
theorem depthCensus_1_2000 : censusB 1 depthData = true := by decide +kernel

/-- **Every center `1 ≤ m ≤ 2000` reaches a twin within `≤ 3` peel steps** — the
    unconditioned grave-depth census, kernel-checked.  Read the module anti-vocabulary:
    this bounds a DOWNHILL descent on a finite range and says NOTHING about twins above
    `m`, nothing about drop control, and nothing about depths beyond 2000 (depth 4 lives
    at `m = 4229`). -/
theorem reachTwin_all_1_2000 : ∀ m : ℕ, 1 ≤ m → m ≤ 2000 → ReachTwin 3 m := by
  intro m h1 h2
  have h := censusB_sound depthCensus_1_2000 (m - 1) (by rw [depthData_length]; omega)
  have harith : 1 + (m - 1) = m := by omega
  rwa [harith] at h

end GraveDepthKernel
end EuclidsPath
