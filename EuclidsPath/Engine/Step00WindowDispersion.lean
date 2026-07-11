import Mathlib
import EuclidsPath.Engine.Step00StrikeFourier

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Window dispersion — the CRT pair law, the exact window variance, and the rarity of defect windows

Origin: the dispersion pass of the geometry line.  The user's goal throughout is TWINS:
a defect window under the ceiling `A²` is the only obstruction between the clean
skeleton and a twin center (`oscillation_plants_twin`), so this module attacks the
window system itself with the classical dispersion (second-moment) method — kept, as
everywhere in this program, at the level of EXACT finite identities, exact counts, and
kernel-checked instances.  No asymptotics, no `O(·)`, no unproven estimate appears.

## THE HEADLINE (S3): defect windows are RARE per period

`defect_windows_rare`: `defectCount · mainTerm² ≤ ∑_{k<P} Fluct²` — the program's first
QUANTITATIVE law about the wall's own objects.  A defect window is exactly a window
carrying a perpetual engine (`defect_forces_coherence`), and Markov against the exact
variance of S2 bounds how many can live in one period — unconditionally, with a closed
rational right-hand side.  The remaining distance — "rare per period" → "absent under
the ceiling" — is exactly the parity wall, now with a MEASURABLE gap (the harness s1
table, `tools/dispersion_run1.log`).  At `(A, g) = (5, 2)` the gap is `5/9 < 1` and the
averaging route genuinely crosses: `cleanGapBound_5_via_dispersion` — the only scale
where it does (measured `B(G) ≥ 1` for all `A ≥ 7`, growing to `≈ 2·10⁷` by `A = 29`).

## The exact skeleton

* **S1 — the CRT pair law (the L9 closure).**  `pairCorr_eq_prod`:
  `pairCorr A d = ∏_{q ∈ clocks A} (q − c_q(d))`.  `pairCorr` IS the CRT pair
  generalization of `admissible_card` (`Step00TwoEngineOscillation`), with the exact
  local trichotomy `c_q(d) ∈ {2,3,4}`: `2` iff `d ≡ 0 (mod q)`, `3` iff `3d ≡ ±1
  (mod q)` (i.e. `d ≡ ±2·i6`, the half-alignments of the shifted wing phases), `4`
  otherwise.
* **S2 — the exact moments.**  `first_moment_eq_mainTerm`: the period average of
  `cleanCount` IS the main term; `second_moment` / `window_variance_exact`:
  `∑ Fluct² = ∑_{j,j'} pairCorr(|j−j'|) − P·mainTerm²`, exact in ℚ, closed via S1.
* **S4 — engine energies.**  `engine_energy_clock` (`2(q−2)/q²` per clock) and
  `total_engine_energy` (`M₁ − M₁²`, the exact Bernoulli variance of the clean density
  `M₁ = ∏(q−2)/q`) — the ℓ²-anchor of any mode-count analysis of the wall.
* **S5 — the dispersion identity.**  `modeWindowSum_shift` (`S_{k+t} = ω^t S_k`) and
  `dispersion_identity`: the `K`-shift `Fluct²`-sum reorganized exactly into mode
  pairs against the geometric kernel `D_K` (`geomKernel_closed` via `geom_sum_eq`).
* **S6 — the death certificate of naive shift-dispersion.**
  `near_diagonal_no_decay` (`Re D_K ≥ K/2` within `1/(6K)` of the diagonal), the CRT
  frequency bijection (`modeTuples_freq_complete`/`_unique`, `card_modeTuples`), and
  `freq_density_near_diagonal` (`≥ P/(3K) − 1` no-decay partners per row).

## DISCLOSURES (read before use)

* **The dispersion identity is a reorganization of an already parity-blind quadratic
  class.**  Every ingredient is linear character algebra, squared; Selberg's foil
  sieve is built FROM the same material.  The identity states no bound — its value is
  that S6 can certify exactly where the naive route dies.
* **Markov is the AVERAGE form.**  S3 bounds the NUMBER of defect windows per period;
  the pointwise statement (no defect window under the ceiling) remains the wall.  No
  costume is worn: `defect_windows_rare` is not an iff with `CleanGapBound`.
* **No Kloosterman sums arise from clean-indicator dispersions.**  The clean indicator
  is a product of LINEAR character conditions in the center `m`, so after opening
  `Fluct²` the inner sums stay linear in the shifted variable: the bilinear twist that
  completes to Kloosterman sums in classical dispersion (divisor-type weights) is
  structurally absent.  The route cannot be rescued by Weil-strength cancellation
  because nothing of Weil type ever appears — this is the anatomy of the blindness,
  not a missing lemma.
* **S6 is a law about a ROUTE (L53 genus)**: the death of naive shift-dispersion is
  NOT an iff with the wall and is deliberately not numbered as a costume — killing a
  proof strategy does not repackage `CleanGapBound`.

## Axiom audit

Every declaration below depends on standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`) — see the audit block at the end of the
file; no `sorry`, no `native_decide`, no repo axiom is used anywhere here.
-/

namespace EuclidsPath
namespace WindowDispersion

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.TwinJacobsthalWall
open EuclidsPath.StrikeFourier

/-! ### Part P — the period of the clock system -/

/-- The exact period `P_A` of the clock system at scale `A`: the product of the active
    clocks.  `Clean A` is `P_A`-periodic on centers `m ≥ 1` (`clean_add_mul_period` with
    `periodP_dvd`), so every per-period count below is a complete invariant. -/
def periodP (A : ℕ) : ℕ := ∏ q ∈ clocks A, q

theorem periodP_pos (A : ℕ) : 0 < periodP A :=
  Finset.prod_pos fun q hq => by have := (mem_clocks.mp hq).2.1; omega

/-- Every prime `q ≤ A` divides `6 · P_A` — the hypothesis shape of `clean_shift`. -/
theorem periodP_dvd {A : ℕ} : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * periodP A := by
  intro q hq hqA
  rcases Nat.lt_or_ge q 5 with h5 | h5
  · have h2 := hq.two_le
    interval_cases q
    · exact Dvd.dvd.mul_right (by norm_num) _
    · exact Dvd.dvd.mul_right (by norm_num) _
    · exact absurd hq (by norm_num)
  · exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem _ (mem_clocks.mpr ⟨hq, h5, hqA⟩)) 6

/-- CRT divisor extraction: if every clock divides `x`, the whole period divides `x`
    (the clocks are distinct primes, so their product is squarefree). -/
theorem periodP_dvd_of_forall_dvd {A x : ℕ} (h : ∀ q ∈ clocks A, q ∣ x) :
    periodP A ∣ x :=
  Finset.prod_primes_dvd x (fun q hq => (mem_clocks.mp hq).1.prime) h

/-- `Clean` is exactly the clock conditions: the primes `2, 3` never strike a wing
    `6m ± 1` (`m ≥ 1`), so the unbounded quantifier of `Clean` collapses to `clocks A`. -/
theorem clean_iff_clocks {A m : ℕ} (hm : 1 ≤ m) :
    Clean A m ↔ ∀ q ∈ clocks A, ¬ (q ∣ 6 * m - 1 ∨ q ∣ 6 * m + 1) := by
  constructor
  · intro h q hq
    obtain ⟨hp, _, hA⟩ := mem_clocks.mp hq
    exact h q hp hA
  · intro h q hp hqA hor
    rcases Nat.lt_or_ge q 5 with h5 | h5
    · have h2 := hp.two_le
      interval_cases q
      · rcases hor with hd | hd <;> omega
      · rcases hor with hd | hd <;> omega
      · exact absurd hp (by norm_num)
    · exact h q (mem_clocks.mpr ⟨hp, h5, hqA⟩) hor

/-! ### S1(a) — the local pair obstruction `badSet` and its exact size trichotomy

For a single center the clock `q` forbids the two wing phases `±i6` (`i6 = 6⁻¹ mod q`,
`strike_minus_iff` / `strike_plus_iff`).  For the PAIR `(m, m+d)` the second center pulls
the same two phases back by `d`, so `m mod q` must avoid `{±i6} ∪ {±i6 − d}`.  The size
of this union is the whole local story: `2` when `d ≡ 0 (mod q)` (the shifts align),
`3` when `3d ≡ ±1 (mod q)` (exactly one shifted phase lands on a wing phase, since
`i6 − d = −i6 ⟺ d = 2·i6 ⟺ 3d = 1`, and `−i6 − d = i6 ⟺ d = −2·i6 ⟺ 3d = −1`),
and `4` otherwise. -/

/-- The forbidden residues of the pair `(m, m+d)` at clock `q`: the wing phases `±i6`
    and their `d`-shifted preimages `±i6 − d`. -/
def badSet (q d : ℕ) : Finset (ZMod q) :=
  {(i6 q : ZMod q), -(i6 q : ZMod q),
    (i6 q : ZMod q) - (d : ZMod q), -(i6 q : ZMod q) - (d : ZMod q)}

/-- `c_q(d)` — the local pair-obstruction count of the clock `q` at shift `d`. -/
def cq (q d : ℕ) : ℕ := (badSet q d).card

theorem mem_badSet {q d : ℕ} {r : ZMod q} :
    r ∈ badSet q d ↔ r = (i6 q : ZMod q) ∨ r = -(i6 q : ZMod q)
      ∨ r = (i6 q : ZMod q) - (d : ZMod q) ∨ r = -(i6 q : ZMod q) - (d : ZMod q) := by
  simp [badSet]

section Trichotomy

variable {q d : ℕ}

/-- The defining equation of the phase: `6 · i6 = 1` in `ZMod q`. -/
theorem six_mul_i6 (hq : q.Prime) (h5 : 5 ≤ q) :
    (6 : ZMod q) * (i6 q : ZMod q) = 1 := by
  have h := i6_spec hq h5
  calc (6 : ZMod q) * (i6 q : ZMod q) = ((6 * i6 q : ℕ) : ZMod q) := by push_cast; ring
    _ = (((6 * i6 q) % q : ℕ) : ZMod q) := (ZMod.natCast_mod _ _).symm
    _ = ((1 : ℕ) : ZMod q) := by rw [h]
    _ = 1 := Nat.cast_one

private theorem natCast_ne_zero_of_lt (hq : q.Prime) {n : ℕ} (hn : 0 < n) (hnq : n < q) :
    (n : ZMod q) ≠ 0 := fun h0 => by
  have hdvd : q ∣ n := (ZMod.natCast_eq_zero_iff n q).mp h0
  have := Nat.le_of_dvd hn hdvd
  omega

/-- Small multiples of the phase never vanish: `n · i6 ≠ 0` for `0 < n < q`. -/
private theorem mul_i6_ne_zero (hq : q.Prime) (h5 : 5 ≤ q) {n : ℕ} (hn : 0 < n)
    (hnq : n < q) : (n : ZMod q) * (i6 q : ZMod q) ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have ha0 : (i6 q : ZMod q) ≠ 0 := fun h => by
    have h6 := six_mul_i6 hq h5
    rw [h, mul_zero] at h6
    exact zero_ne_one h6
  exact mul_ne_zero (natCast_ne_zero_of_lt hq hn hnq) ha0

private theorem i6_ne_neg_i6 (hq : q.Prime) (h5 : 5 ≤ q) :
    (i6 q : ZMod q) ≠ -(i6 q : ZMod q) := fun h => by
  have h2 : ((2 : ℕ) : ZMod q) * (i6 q : ZMod q) = 0 := by push_cast; linear_combination h
  exact mul_i6_ne_zero hq h5 (by norm_num) (by omega) h2

private theorem four_i6_ne_zero (hq : q.Prime) (h5 : 5 ≤ q) :
    ((4 : ℕ) : ZMod q) * (i6 q : ZMod q) ≠ 0 :=
  mul_i6_ne_zero hq h5 (by norm_num) (by omega)

/-- **Aligned shift** (`d ≡ 0 mod q`): the pulled-back phases coincide with the wing
    phases — `c_q = 2`. -/
theorem cq_eq_two (hq : q.Prime) (h5 : 5 ≤ q) (hd : (d : ZMod q) = 0) : cq q d = 2 := by
  have hset : badSet q d = {(i6 q : ZMod q), -(i6 q : ZMod q)} := by
    ext r
    simp only [mem_badSet, hd, sub_zero, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [cq, hset, Finset.card_pair (i6_ne_neg_i6 hq h5)]

/-- **Half-aligned shift, plus side** (`3d ≡ 1 mod q`, i.e. `d ≡ 2·i6`): exactly one
    pulled-back phase lands on a wing phase — `c_q = 3`. -/
theorem cq_eq_three_pos (hq : q.Prime) (h5 : 5 ≤ q) (hd : 3 * (d : ZMod q) = 1) :
    cq q d = 3 := by
  have h6 := six_mul_i6 hq h5
  have hd2 : (d : ZMod q) = 2 * (i6 q : ZMod q) := by
    haveI : Fact q.Prime := ⟨hq⟩
    have h3 : ((3 : ℕ) : ZMod q) ≠ 0 := natCast_ne_zero_of_lt hq (by norm_num) (by omega)
    have h3' : (3 : ZMod q) ≠ 0 := by exact_mod_cast h3
    apply mul_left_cancel₀ h3'
    rw [hd]
    linear_combination -h6
  have e1 : (i6 q : ZMod q) - (d : ZMod q) = -(i6 q : ZMod q) := by
    rw [hd2]; ring
  have e2 : -(i6 q : ZMod q) - (d : ZMod q) = -(3 * (i6 q : ZMod q)) := by
    rw [hd2]; ring
  have hset : badSet q d
      = {(i6 q : ZMod q), -(i6 q : ZMod q), -(3 * (i6 q : ZMod q))} := by
    ext r
    simp only [mem_badSet, e1, e2, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hne12 := i6_ne_neg_i6 hq h5
  have hne13 : (i6 q : ZMod q) ≠ -(3 * (i6 q : ZMod q)) := fun h => by
    apply four_i6_ne_zero hq h5
    push_cast
    linear_combination h
  have hne23 : -(i6 q : ZMod q) ≠ -(3 * (i6 q : ZMod q)) := fun h => by
    apply mul_i6_ne_zero hq h5 (show 0 < 2 by norm_num) (by omega)
    push_cast
    linear_combination h
  rw [cq, hset, Finset.card_insert_of_notMem (by simp [hne12, hne13]),
    Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]

/-- **Half-aligned shift, minus side** (`3d ≡ −1 mod q`, i.e. `d ≡ −2·i6`): `c_q = 3`. -/
theorem cq_eq_three_neg (hq : q.Prime) (h5 : 5 ≤ q) (hd : 3 * (d : ZMod q) = -1) :
    cq q d = 3 := by
  have h6 := six_mul_i6 hq h5
  have hd2 : (d : ZMod q) = -(2 * (i6 q : ZMod q)) := by
    haveI : Fact q.Prime := ⟨hq⟩
    have h3 : ((3 : ℕ) : ZMod q) ≠ 0 := natCast_ne_zero_of_lt hq (by norm_num) (by omega)
    have h3' : (3 : ZMod q) ≠ 0 := by exact_mod_cast h3
    apply mul_left_cancel₀ h3'
    rw [hd]
    linear_combination h6
  have e1 : (i6 q : ZMod q) - (d : ZMod q) = 3 * (i6 q : ZMod q) := by
    rw [hd2]; ring
  have e2 : -(i6 q : ZMod q) - (d : ZMod q) = (i6 q : ZMod q) := by
    rw [hd2]; ring
  have hset : badSet q d
      = {(i6 q : ZMod q), -(i6 q : ZMod q), 3 * (i6 q : ZMod q)} := by
    ext r
    simp only [mem_badSet, e1, e2, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hne12 := i6_ne_neg_i6 hq h5
  have hne13 : (i6 q : ZMod q) ≠ 3 * (i6 q : ZMod q) := fun h => by
    apply mul_i6_ne_zero hq h5 (show 0 < 2 by norm_num) (by omega)
    push_cast
    linear_combination -h
  have hne23 : -(i6 q : ZMod q) ≠ 3 * (i6 q : ZMod q) := fun h => by
    apply four_i6_ne_zero hq h5
    push_cast
    linear_combination -h
  rw [cq, hset, Finset.card_insert_of_notMem (by simp [hne12, hne13]),
    Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]

/-- **Generic shift** (`d ≢ 0` and `3d ≢ ±1 mod q`): the four forbidden residues are
    pairwise distinct — `c_q = 4`. -/
theorem cq_eq_four (hq : q.Prime) (h5 : 5 ≤ q) (h0 : (d : ZMod q) ≠ 0)
    (h1 : 3 * (d : ZMod q) ≠ 1) (h2 : 3 * (d : ZMod q) ≠ -1) : cq q d = 4 := by
  have h6 := six_mul_i6 hq h5
  have hne12 := i6_ne_neg_i6 hq h5
  have hne13 : (i6 q : ZMod q) ≠ (i6 q : ZMod q) - (d : ZMod q) := fun h => by
    apply h0
    linear_combination h
  have hne14 : (i6 q : ZMod q) ≠ -(i6 q : ZMod q) - (d : ZMod q) := fun h => by
    apply h2
    linear_combination 3 * h - h6
  have hne23 : -(i6 q : ZMod q) ≠ (i6 q : ZMod q) - (d : ZMod q) := fun h => by
    apply h1
    linear_combination 3 * h + h6
  have hne24 : -(i6 q : ZMod q) ≠ -(i6 q : ZMod q) - (d : ZMod q) := fun h => by
    apply h0
    linear_combination h
  have hne34 : (i6 q : ZMod q) - (d : ZMod q) ≠ -(i6 q : ZMod q) - (d : ZMod q) :=
    fun h => hne12 (by linear_combination h)
  rw [cq, badSet, Finset.card_insert_of_notMem (by simp [hne12, hne13, hne14]),
    Finset.card_insert_of_notMem (by simp [hne23, hne24]),
    Finset.card_insert_of_notMem (by simp [hne34]), Finset.card_singleton]

end Trichotomy

/-! ### S1(b) — the pair-correlation count and THE CRT PAIR LAW

`pairCorr` is the CRT pair generalization of `admissible_card`
(`Step00TwoEngineOscillation`): at `d = 0` it degenerates to the per-period clean count
`∏ (q − 2)` — the Hardy–Littlewood local densities — and for general `d` it is the exact
finite pair-correlation function of the clean set, factored over the clocks. -/

/-- `pairCorr A d` — the exact number of doubly-clean pairs `(m, m + d)` per period:
    centers `m` of the full-period window `(0, P_A]` with both `m` and `m + d` clean.
    The window starts at `1` (the `Ioc` convention of `cleanCount`): `m = 0` is not a
    center — the `ℕ`-wing `6·0 − 1 = 0` is an artifact, not a residue class. -/
def pairCorr (A d : ℕ) : ℕ :=
  ((Finset.Ioc 0 (periodP A)).filter fun m => Clean A m ∧ Clean A (m + d)).card

/-- The guarded residue universe of a clock (`= Finset.univ` on every actual clock). -/
private def resUniv (q : ℕ) : Finset (ZMod q) :=
  if h : q = 0 then ∅ else
    haveI : NeZero q := ⟨h⟩
    Finset.univ

private theorem resUniv_eq {q : ℕ} [NeZero q] : resUniv q = Finset.univ := by
  unfold resUniv
  rw [dif_neg (NeZero.ne q)]

private theorem card_resUniv {q : ℕ} [NeZero q] : (resUniv q).card = q := by
  rw [resUniv_eq, Finset.card_univ, ZMod.card]

/-- The pair `(m, m+d)` is doubly clean iff `m mod q` avoids `badSet q d` at every
    clock — the local-global dictionary of the pair count. -/
theorem cleanPair_iff_badSet {A d m : ℕ} (hm : 1 ≤ m) :
    (Clean A m ∧ Clean A (m + d)) ↔ ∀ q ∈ clocks A, (m : ZMod q) ∉ badSet q d := by
  rw [clean_iff_clocks hm, clean_iff_clocks (show 1 ≤ m + d by omega)]
  constructor
  · rintro ⟨h1, h2⟩ q hq hbad
    obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
    haveI : NeZero q := ⟨by omega⟩
    rcases mem_badSet.mp hbad with h | h | h | h
    · exact h1 q hq (Or.inl ((strike_minus_iff hp h5 (i6_spec hp h5) hm).mpr h))
    · exact h1 q hq (Or.inr ((strike_plus_iff hp h5 i6_lt (i6_spec hp h5)).mpr h))
    · refine h2 q hq (Or.inl
        ((strike_minus_iff hp h5 (i6_spec hp h5) (show 1 ≤ m + d by omega)).mpr ?_))
      push_cast
      linear_combination h
    · refine h2 q hq (Or.inr ((strike_plus_iff hp h5 i6_lt (i6_spec hp h5)).mpr ?_))
      push_cast
      linear_combination h
  · intro h
    refine ⟨fun q hq hor => ?_, fun q hq hor => ?_⟩
    · obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
      haveI : NeZero q := ⟨by omega⟩
      apply h q hq
      rcases hor with hd | hd
      · exact mem_badSet.mpr
          (Or.inl ((strike_minus_iff hp h5 (i6_spec hp h5) hm).mp hd))
      · exact mem_badSet.mpr
          (Or.inr (Or.inl ((strike_plus_iff hp h5 i6_lt (i6_spec hp h5)).mp hd)))
    · obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
      haveI : NeZero q := ⟨by omega⟩
      apply h q hq
      rcases hor with hd | hd
      · refine mem_badSet.mpr (Or.inr (Or.inr (Or.inl ?_)))
        have hres := (strike_minus_iff hp h5 (i6_spec hp h5)
          (show 1 ≤ m + d by omega)).mp hd
        push_cast at hres
        linear_combination hres
      · refine mem_badSet.mpr (Or.inr (Or.inr (Or.inr ?_)))
        have hres := (strike_plus_iff hp h5 i6_lt (i6_spec hp h5)).mp hd
        push_cast at hres
        linear_combination hres

/-- CRT uniqueness on one period: two centers of `(0, P_A]` with equal residues at
    every clock coincide (the clocks are distinct primes; their product is the period). -/
private theorem center_eq_of_res_eq {A m m' : ℕ}
    (hm : m ∈ Finset.Ioc 0 (periodP A)) (hm' : m' ∈ Finset.Ioc 0 (periodP A))
    (h : ∀ q ∈ clocks A, (m : ZMod q) = (m' : ZMod q)) : m = m' := by
  rw [Finset.mem_Ioc] at hm hm'
  rcases le_total m m' with hle | hle
  · have hdvd : periodP A ∣ m' - m := periodP_dvd_of_forall_dvd fun q hq =>
      (Nat.modEq_iff_dvd' hle).mp ((ZMod.natCast_eq_natCast_iff m m' q).mp (h q hq))
    rcases Nat.eq_zero_or_pos (m' - m) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega
  · have hdvd : periodP A ∣ m - m' := periodP_dvd_of_forall_dvd fun q hq =>
      (Nat.modEq_iff_dvd' hle).mp
        ((ZMod.natCast_eq_natCast_iff m m' q).mp (h q hq)).symm
    rcases Nat.eq_zero_or_pos (m - m') with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega

/-- CRT existence: every residue tuple is realized by a center of `(0, P_A]` —
    injectivity plus the exact cardinality match, no explicit CRT lift needed. -/
private theorem res_surjective {A : ℕ} :
    ∀ f ∈ (clocks A).pi (fun q => resUniv q), ∃ m, ∃ _ : m ∈ Finset.Ioc 0 (periodP A),
      f = fun q (_ : q ∈ clocks A) => (m : ZMod q) := by
  apply Finset.surj_on_of_inj_on_of_card_le
    (f := fun m (_ : m ∈ Finset.Ioc 0 (periodP A)) =>
      fun q (_ : q ∈ clocks A) => (m : ZMod q))
  · intro m hm
    rw [Finset.mem_pi]
    intro q hq
    haveI : NeZero q := ⟨by have := (mem_clocks.mp hq).2.1; omega⟩
    rw [resUniv_eq]
    exact Finset.mem_univ _
  · intro m m' hm hm' heq
    exact center_eq_of_res_eq hm hm' fun q hq => congrFun (congrFun heq q) hq
  · have hcard : ((clocks A).pi fun q => resUniv q).card = periodP A := by
      rw [Finset.card_pi]
      exact Finset.prod_congr rfl fun q hq => by
        haveI : NeZero q := ⟨by have := (mem_clocks.mp hq).2.1; omega⟩
        exact card_resUniv
    rw [hcard, Nat.card_Ioc]
    omega

/-- **THE CRT PAIR LAW.**  The pair correlation factors EXACTLY over the clocks:
    `pairCorr A d = ∏_{q ∈ clocks A} (q − c_q(d))`, with the local obstruction count
    `c_q(d) ∈ {2, 3, 4}` classified by the trichotomy `cq_eq_two` (`d ≡ 0 mod q`),
    `cq_eq_three_pos`/`cq_eq_three_neg` (`3d ≡ ±1 mod q`), `cq_eq_four` (generic).
    This is `admissible_card` lifted from single centers to pairs: exact, per period,
    no error term. -/
theorem pairCorr_eq_prod (A d : ℕ) :
    pairCorr A d = ∏ q ∈ clocks A, (q - cq q d) := by
  unfold pairCorr
  have hcard : ((clocks A).pi fun q => resUniv q \ badSet q d).card
      = ∏ q ∈ clocks A, (q - cq q d) := by
    rw [Finset.card_pi]
    refine Finset.prod_congr rfl fun q hq => ?_
    haveI : NeZero q := ⟨by have := (mem_clocks.mp hq).2.1; omega⟩
    rw [Finset.card_sdiff, card_resUniv, resUniv_eq, Finset.inter_univ]
    rfl
  rw [← hcard]
  refine Finset.card_bij
    (fun m _ => fun q (_ : q ∈ clocks A) => (m : ZMod q)) ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmem, hclean⟩ := hm
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp hmem).1
      omega
    rw [Finset.mem_pi]
    intro q hq
    haveI : NeZero q := ⟨by have := (mem_clocks.mp hq).2.1; omega⟩
    rw [Finset.mem_sdiff, resUniv_eq]
    exact ⟨Finset.mem_univ _, (cleanPair_iff_badSet hm1).mp hclean q hq⟩
  · intro m hm m' hm' heq
    rw [Finset.mem_filter] at hm hm'
    exact center_eq_of_res_eq hm.1 hm'.1 fun q hq => congrFun (congrFun heq q) hq
  · intro f hf
    have hf' : f ∈ (clocks A).pi fun q => resUniv q := by
      rw [Finset.mem_pi] at hf ⊢
      intro q hq
      exact (Finset.mem_sdiff.mp (hf q hq)).1
    obtain ⟨m, hm, hfm⟩ := res_surjective f hf'
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    refine ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩, hfm.symm⟩
    refine (cleanPair_iff_badSet hm1).mpr fun q hq => ?_
    have hnb := (Finset.mem_sdiff.mp (Finset.mem_pi.mp hf q hq)).2
    rw [hfm] at hnb
    exact hnb

/-- At `d = 0` the pair law is the per-period clean-residue count `∏ (q − 2)` — the
    exact CRT form of the Hardy–Littlewood local densities (the `mainTerm` numerators). -/
theorem pairCorr_zero (A : ℕ) : pairCorr A 0 = ∏ q ∈ clocks A, (q - 2) := by
  rw [pairCorr_eq_prod]
  refine Finset.prod_congr rfl fun q hq => ?_
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  rw [cq_eq_two hp h5 Nat.cast_zero]

/-- `pairCorr A 0` is literally the clean count of one full-period window. -/
theorem pairCorr_zero_eq_cleanCount (A : ℕ) :
    pairCorr A 0 = cleanCount A 0 (periodP A) := by
  unfold pairCorr cleanCount
  rw [zero_add]
  exact congrArg Finset.card (Finset.filter_congr fun m _ => by simp)

/-! #### Kernel instances of the CRT pair law (both sides literal)

Scale `5` (period `5`, clean residues `{2,3,5} mod 5`): the trichotomy in full —
`d ≡ 0`: `5−2 = 3`; `3d ≡ ±1` (`d ≡ 2,3`): `5−3 = 2`; generic (`d ≡ 1,4`): `5−4 = 1`.
Scale `7` (period `35`): products over two clocks. -/

example : pairCorr 5 0 = 3 := by decide
example : pairCorr 5 1 = 1 := by decide
example : pairCorr 5 2 = 2 := by decide
example : pairCorr 5 3 = 2 := by decide
example : pairCorr 5 4 = 1 := by decide
example : pairCorr 5 5 = 3 := by decide
example : pairCorr 7 0 = 15 := by decide
example : pairCorr 7 1 = 3 := by decide
example : pairCorr 7 2 = 8 := by decide
example : pairCorr 7 3 = 6 := by decide

/-- The trichotomy checked against the kernel at clock `5`: `3·2 ≡ 1` gives `c = 3`. -/
example : cq 5 2 = 3 := cq_eq_three_pos (by norm_num) (by norm_num) (by decide)
example : cq 5 3 = 3 := cq_eq_three_neg (by norm_num) (by norm_num) (by decide)
example : cq 5 5 = 2 := cq_eq_two (by norm_num) (by norm_num) (by decide)
example : cq 5 1 = 4 :=
  cq_eq_four (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- The pair law at the wall scale `13` (period `5005`), twin shift `d = 2`:
    `(5−3)(7−3)(11−4)(13−4) = 2·4·7·9 = 504` doubly-clean pairs per period —
    kernel-checked against the raw filter count, the same budget class as
    `periodCert_13`.  (The harness `tools/dispersion_run1.log` confirms `504`.) -/
theorem pairCorr_at_13 : pairCorr 13 2 = 504 := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- The aligned pair count at scale `13`: `pairCorr 13 0 = 3·5·9·11 = 1485` — the
    per-period clean-residue count (harness-confirmed byte-exactly). -/
theorem pairCorr_at_13_zero : pairCorr 13 0 = 1485 := by decide

/-! ### S2(a) — periodic window invariance and the exact first moment -/

private theorem sum_Ioc_split (f : ℕ → ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ m ∈ Finset.Ioc a c, f m
      = ∑ m ∈ Finset.Ioc a b, f m + ∑ m ∈ Finset.Ioc b c, f m := by
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]

/-- One-period counts of a `P`-periodic (on `m ≥ 1`) predicate do not depend on the
    window start: sliding the window `(s, s+P]` by one exchanges the entering and the
    leaving center, and periodicity makes the exchange even. -/
private theorem periodic_count_shift {P : ℕ} (hP : 0 < P) (F : ℕ → Prop)
    [DecidablePred F] (hper : ∀ m, 1 ≤ m → (F (m + P) ↔ F m)) :
    ∀ s, ((Finset.Ioc s (s + P)).filter F).card = ((Finset.Ioc 0 P).filter F).card := by
  intro s
  induction s with
  | zero => rw [Nat.zero_add]
  | succ n ih =>
    rw [← ih]
    have hkey : ∀ a b : ℕ, ((Finset.Ioc a b).filter F).card
        = ∑ m ∈ Finset.Ioc a b, if F m then 1 else 0 := fun a b => by
      rw [Finset.card_filter]
    have h1 : ∑ m ∈ Finset.Ioc n (n + 1 + P), (if F m then (1:ℕ) else 0)
        = ∑ m ∈ Finset.Ioc n (n + P), (if F m then 1 else 0)
          + ∑ m ∈ Finset.Ioc (n + P) (n + 1 + P), (if F m then 1 else 0) :=
      sum_Ioc_split _ (by omega) (by omega)
    have h2 : ∑ m ∈ Finset.Ioc n (n + 1 + P), (if F m then (1:ℕ) else 0)
        = ∑ m ∈ Finset.Ioc n (n + 1), (if F m then 1 else 0)
          + ∑ m ∈ Finset.Ioc (n + 1) (n + 1 + P), (if F m then 1 else 0) :=
      sum_Ioc_split _ (by omega) (by omega)
    have e1 : Finset.Ioc (n + P) (n + 1 + P) = {n + P + 1} := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    have e2 : Finset.Ioc n (n + 1) = {n + 1} := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    have hFP : (if F (n + P + 1) then (1:ℕ) else 0) = if F (n + 1) then 1 else 0 := by
      have hp := hper (n + 1) (by omega)
      rw [show n + P + 1 = n + 1 + P by omega]
      by_cases h : F (n + 1)
      · rw [if_pos h, if_pos (hp.mpr h)]
      · rw [if_neg h, if_neg fun hc => h (hp.mp hc)]
    have hbal := h1.symm.trans h2
    rw [e1, e2, Finset.sum_singleton, Finset.sum_singleton, hFP] at hbal
    rw [hkey, hkey]
    omega

/-- The doubly-clean predicate is `P_A`-periodic, so EVERY window `(s, s + P_A]` sees
    exactly `pairCorr A d` doubly-clean pairs. -/
theorem pairCount_shift (A d s : ℕ) :
    ((Finset.Ioc s (s + periodP A)).filter
      fun m => Clean A m ∧ Clean A (m + d)).card = pairCorr A d := by
  refine periodic_count_shift (periodP_pos A) _ (fun m hm => ?_) s
  refine and_congr (clean_shift periodP_dvd hm) ?_
  rw [show m + periodP A + d = m + d + periodP A by omega]
  exact clean_shift periodP_dvd (by omega)

/-- Every full-period window carries the same clean count `pairCorr A 0`. -/
theorem cleanCount_period_shift (A s : ℕ) :
    cleanCount A s (periodP A) = pairCorr A 0 := by
  rw [← pairCount_shift A 0 s]
  exact congrArg Finset.card (Finset.filter_congr fun m _ => by simp)

/-- `cleanCount` as an indicator sum over window offsets `j ∈ [1, g]`. -/
private theorem cleanCount_eq_sum_offsets (A k g : ℕ) :
    cleanCount A k g = ∑ j ∈ Finset.Icc 1 g, if Clean A (k + j) then 1 else 0 := by
  unfold cleanCount
  rw [Finset.card_filter]
  have himg : Finset.Ioc k (k + g) = (Finset.Icc 1 g).image (fun j => k + j) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hx
      exact ⟨x - k, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [himg, Finset.sum_image fun a _ b _ h => by omega]

/-- One offset column summed over a period of starts is one full-period clean count. -/
private theorem column_sum (A : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    (∑ k ∈ Finset.range (periodP A), if Clean A (k + j) then (1:ℕ) else 0)
      = pairCorr A 0 := by
  have himg : Finset.Ioc (j - 1) (j - 1 + periodP A)
      = (Finset.range (periodP A)).image (fun k => k + j) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨x - j, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  calc (∑ k ∈ Finset.range (periodP A), if Clean A (k + j) then (1:ℕ) else 0)
      = ∑ m ∈ Finset.Ioc (j - 1) (j - 1 + periodP A),
          (if Clean A m then (1:ℕ) else 0) := by
        rw [himg, Finset.sum_image fun a _ b _ h => by omega]
    _ = cleanCount A (j - 1) (periodP A) := by
        rw [cleanCount, Finset.card_filter]
    _ = pairCorr A 0 := cleanCount_period_shift A (j - 1)

/-- **The exact first moment.**  Over one full period of window starts, the total clean
    count is `g · pairCorr A 0`: each of the `g` offset columns contributes one full
    period.  Exact — no boundary error, because the period is a genuine period. -/
theorem first_moment (A g : ℕ) :
    ∑ k ∈ Finset.range (periodP A), cleanCount A k g = g * pairCorr A 0 := by
  have hsw : ∑ k ∈ Finset.range (periodP A), cleanCount A k g
      = ∑ j ∈ Finset.Icc 1 g, ∑ k ∈ Finset.range (periodP A),
          if Clean A (k + j) then 1 else 0 := by
    rw [Finset.sum_congr rfl fun k _ => cleanCount_eq_sum_offsets A k g,
      Finset.sum_comm]
  rw [hsw, Finset.sum_congr rfl fun j hj => column_sum A (Finset.mem_Icc.mp hj).1,
    Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]

/-- The ℕ-product cast: `∏(q−2)` over the clocks, in ℚ. -/
private theorem cast_prod_sub_two (A : ℕ) :
    ((∏ q ∈ clocks A, (q - 2) : ℕ) : ℚ) = ∏ q ∈ clocks A, ((q : ℚ) - 2) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun q hq => ?_
  have h5 := (mem_clocks.mp hq).2.1
  exact_mod_cast Nat.cast_sub (R := ℚ) (by omega : 2 ≤ q)

/-- **The first moment in ℚ: the period average of `cleanCount` IS the main term.**
    `∑_{k<P} cleanCount = P · mainTerm` exactly — the zero-mode anchor of the variance
    computation, and the reason `windowFluct` sums to `0` over a period. -/
theorem first_moment_eq_mainTerm (A g : ℕ) :
    ∑ k ∈ Finset.range (periodP A), (cleanCount A k g : ℚ)
      = (periodP A : ℚ) * mainTerm A g := by
  have hcast : ∑ k ∈ Finset.range (periodP A), (cleanCount A k g : ℚ)
      = ((g * pairCorr A 0 : ℕ) : ℚ) := by
    rw [← first_moment A g]
    push_cast
    rfl
  have hfac : ∏ q ∈ clocks A, ((q : ℚ) - 2)
      = (∏ q ∈ clocks A, (q : ℚ)) * ∏ q ∈ clocks A, (1 - 2 / (q : ℚ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have h5 := (mem_clocks.mp hq).2.1
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  rw [hcast, pairCorr_zero, mainTerm, periodP, Nat.cast_mul, cast_prod_sub_two,
    Nat.cast_prod, hfac]
  ring

/-- The fluctuation sums to zero over a period (the exact mean-zero law). -/
theorem fluct_sum_zero (A g : ℕ) :
    ∑ k ∈ Finset.range (periodP A), windowFluct A k g = 0 := by
  unfold windowFluct
  rw [Finset.sum_sub_distrib, first_moment_eq_mainTerm, Finset.sum_const,
    nsmul_eq_mul, Finset.card_range]
  ring

/-! ### S2(b) — the exact second moment and THE EXACT WINDOW VARIANCE -/

private theorem ite_mul_ite (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1:ℕ) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- One offset pair column `(j, j')`, `j ≤ j'`, summed over a period of starts, is one
    pair correlation at distance `j' − j`. -/
private theorem column_pair_sum_le (A : ℕ) {j j' : ℕ} (hj : 1 ≤ j) (hjj : j ≤ j') :
    (∑ k ∈ Finset.range (periodP A),
      if Clean A (k + j) ∧ Clean A (k + j') then (1:ℕ) else 0)
      = pairCorr A (j' - j) := by
  have himg : Finset.Ioc (j - 1) (j - 1 + periodP A)
      = (Finset.range (periodP A)).image (fun k => k + j) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨x - j, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have hpred : ∀ k : ℕ, (Clean A (k + j) ∧ Clean A (k + j'))
      ↔ (Clean A (k + j) ∧ Clean A ((k + j) + (j' - j))) := by
    intro k
    rw [show (k + j) + (j' - j) = k + j' by omega]
  rw [← pairCount_shift A (j' - j) (j - 1), Finset.card_filter, himg,
    Finset.sum_image fun a _ b _ h => by omega]
  exact Finset.sum_congr rfl fun k _ => if_congr (hpred k) rfl rfl

/-- The symmetric form: any offset pair column is a pair correlation at `Nat.dist`. -/
private theorem column_pair_sum (A : ℕ) {j j' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') :
    (∑ k ∈ Finset.range (periodP A),
      if Clean A (k + j) ∧ Clean A (k + j') then (1:ℕ) else 0)
      = pairCorr A (Nat.dist j' j) := by
  rcases le_total j j' with h | h
  · rw [Nat.dist_eq_sub_of_le_right h]
    exact column_pair_sum_le A hj h
  · rw [Nat.dist_eq_sub_of_le h]
    rw [Finset.sum_congr rfl fun k _ => if_congr and_comm rfl rfl]
    exact column_pair_sum_le A hj' h

/-- **The exact second moment.**  The period sum of `cleanCount²` is the double sum of
    pair correlations over the `g²` offset pairs — pure double counting: each ordered
    pair of clean centers at distance `d` is seen by exactly the offset pairs at that
    distance, and periodicity makes every column a full period.  Exact, in ℕ. -/
theorem second_moment (A g : ℕ) :
    ∑ k ∈ Finset.range (periodP A), (cleanCount A k g) ^ 2
      = ∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g, pairCorr A (Nat.dist j' j) := by
  have hexp : ∀ k, (cleanCount A k g) ^ 2
      = ∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g,
          if Clean A (k + j) ∧ Clean A (k + j') then 1 else 0 := by
    intro k
    rw [pow_two, cleanCount_eq_sum_offsets, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ =>
      ite_mul_ite _ _
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j' hj' =>
    column_pair_sum A (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj').1

/-- **THE EXACT WINDOW VARIANCE.**  Over one full period of window starts,

    `∑_{k<P} Fluct(k)² = (∑_{j,j' ∈ [1,g]} pairCorr(|j − j'|)) − P · mainTerm²`

    — an exact identity in ℚ, obtained by expanding `Fluct = cleanCount − mainTerm`
    and closing the cross term with the exact first moment
    (`first_moment_eq_mainTerm`).  With the CRT pair law (`pairCorr_eq_prod`) the right
    side is a closed rational form in the clocks alone.  The collected weights satisfy
    `∑_{|d|<g} (g − |d|) = g²` (the sanity instance below): the double sum is the
    `(g − |d|)`-weighted sum of pair correlations. -/
theorem window_variance_exact (A g : ℕ) :
    ∑ k ∈ Finset.range (periodP A), (windowFluct A k g) ^ 2
      = (∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g,
          (pairCorr A (Nat.dist j' j) : ℚ))
        - (periodP A : ℚ) * (mainTerm A g) ^ 2 := by
  have hexp : ∀ k, (windowFluct A k g) ^ 2
      = (cleanCount A k g : ℚ)^2 - 2 * mainTerm A g * (cleanCount A k g : ℚ)
        + (mainTerm A g)^2 := by
    intro k
    unfold windowFluct
    ring
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have h1 : ∑ k ∈ Finset.range (periodP A), (cleanCount A k g : ℚ)^2
      = ∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g,
          (pairCorr A (Nat.dist j' j) : ℚ) := by
    calc ∑ k ∈ Finset.range (periodP A), (cleanCount A k g : ℚ)^2
        = ((∑ k ∈ Finset.range (periodP A), (cleanCount A k g)^2 : ℕ) : ℚ) := by
          push_cast
          rfl
      _ = _ := by
          rw [second_moment]
          push_cast
          rfl
  have h2 : ∑ k ∈ Finset.range (periodP A),
      2 * mainTerm A g * (cleanCount A k g : ℚ)
      = 2 * mainTerm A g * ((periodP A : ℚ) * mainTerm A g) := by
    rw [← Finset.mul_sum, first_moment_eq_mainTerm]
  have h3 : ∑ k ∈ Finset.range (periodP A), (mainTerm A g)^2
      = (periodP A : ℚ) * (mainTerm A g)^2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  rw [h1, h2, h3]
  ring

/-- Sanity: the double sum ranges over exactly `g²` offset pairs — the collected form
    of `∑_{|d|<g} (g − |d|) = g²`. -/
example (g : ℕ) : ∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g, (1:ℕ) = g ^ 2 := by
  simp [Nat.card_Icc, pow_two]

/-! #### Kernel instances of the variance (both sides literal)

Scale `5`, `g = 2`: counts per period `[1,2,1,1,1]`, `M = 6/5`; variance `4/5`; double
sum `3+1+1+3 = 8`; `8 − 5·(6/5)² = 4/5`.  Scale `7`, `g = 3`: second moment `73` both
as the raw window scan and as the pair-correlation double sum. -/

example : ∑ j ∈ Finset.Icc 1 2, ∑ j' ∈ Finset.Icc 1 2, pairCorr 5 (Nat.dist j' j) = 8 := by
  decide

example : (8 : ℚ) - (5 : ℚ) * (6 / 5) ^ 2 = 4 / 5 := by norm_num

private theorem mainTerm_5_2 : mainTerm 5 2 = 6 / 5 := by
  rw [mainTerm, show clocks 5 = {5} from by decide, Finset.prod_singleton]
  norm_num

/-- The variance at scale `5`, window `2`, computed window by window: `4/5`. -/
private theorem window_variance_5_2 :
    ∑ k ∈ Finset.range (periodP 5), (windowFluct 5 k 2) ^ 2 = 4 / 5 := by
  rw [show periodP 5 = 5 from by decide, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  unfold windowFluct
  rw [show cleanCount 5 0 2 = 1 from by decide, show cleanCount 5 1 2 = 2 from by decide,
    show cleanCount 5 2 2 = 1 from by decide, show cleanCount 5 3 2 = 1 from by decide,
    show cleanCount 5 4 2 = 1 from by decide, mainTerm_5_2]
  norm_num

example : ∑ k ∈ Finset.range (periodP 7), (cleanCount 7 k 3) ^ 2 = 73 := by decide

example : ∑ j ∈ Finset.Icc 1 3, ∑ j' ∈ Finset.Icc 1 3, pairCorr 7 (Nat.dist j' j) = 73 := by
  decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- The raw second moment at the wall scale `13`, `g = G(13) = 11`: one kernel scan of
    all `5005` windows (the `periodCert_13` budget class). -/
private theorem second_moment_at_13 :
    ∑ k ∈ Finset.range (periodP 13), (cleanCount 13 k 11) ^ 2 = 59839 := by decide

private theorem mainTerm_13_11 : mainTerm 13 11 = 297 / 91 := by
  rw [mainTerm, show clocks 13 = {5, 7, 11, 13} from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num

/-- **The exact window variance at the wall scale `13`** (`g = G(13) = 11`, period
    `5005`): `∑ Fluct² = 59839 − 5005·(297/91)² = 593854/91` — the harness constant
    (`tools/dispersion_run1.log`, s1 table) reproduced by kernel scan plus the exact
    variance identity. -/
theorem window_variance_at_13 :
    ∑ k ∈ Finset.range (periodP 13), (windowFluct 13 k 11) ^ 2 = 593854 / 91 := by
  rw [window_variance_exact]
  have hdbl : ∑ j ∈ Finset.Icc 1 11, ∑ j' ∈ Finset.Icc 1 11,
      (pairCorr 13 (Nat.dist j' j) : ℚ) = 59839 := by
    have h2 : ∑ j ∈ Finset.Icc 1 11, ∑ j' ∈ Finset.Icc 1 11,
        pairCorr 13 (Nat.dist j' j) = 59839 := by
      rw [← second_moment 13 11]
      exact second_moment_at_13
    calc ∑ j ∈ Finset.Icc 1 11, ∑ j' ∈ Finset.Icc 1 11,
          (pairCorr 13 (Nat.dist j' j) : ℚ)
        = ((∑ j ∈ Finset.Icc 1 11, ∑ j' ∈ Finset.Icc 1 11,
            pairCorr 13 (Nat.dist j' j) : ℕ) : ℚ) := by
          push_cast
          rfl
      _ = 59839 := by rw [h2]; norm_num
  rw [hdbl, show periodP 13 = 5005 from by decide, mainTerm_13_11]
  norm_num

/-! ### S3 — DEFECT WINDOWS ARE RARE (the headline law)

The first quantitative law about the wall's own objects.  A defect window — a window
with no clean center — is exactly a window on which a perpetual engine runs
(`defect_forces_coherence`: its fluctuation is the full coherent spike `−mainTerm`).
Markov's inequality against the EXACT variance of S2 bounds how many such windows one
period can carry — unconditionally, with a closed rational right-hand side.  Perpetual
engines are RARE per period.  The remaining distance — from "rare per period" to
"absent under the ceiling `A²`" — is exactly the parity wall, now with a measurable
gap (the harness s1 table, `tools/dispersion_run1.log`, measures it scale by scale). -/

/-- The defect windows of one period: starts `k < P_A` whose window `(k, k+g]` holds
    no clean center — the windows carrying a coherent engine spike. -/
def defectCount (A g : ℕ) : ℕ :=
  ((Finset.range (periodP A)).filter fun k => cleanCount A k g = 0).card

/-- **DEFECT WINDOWS ARE RARE (Markov form — the headline).**  Each defect window
    contributes exactly `mainTerm²` to the period variance (`defect_forces_coherence`),
    and squares are nonnegative, so

    `defectCount · mainTerm² ≤ ∑_{k<P} Fluct(k)²`

    — the program's first QUANTITATIVE law about defect windows: unconditional, exact
    on the left, exact and closed (S2) on the right. -/
theorem defect_windows_rare (A g : ℕ) :
    (defectCount A g : ℚ) * (mainTerm A g) ^ 2
      ≤ ∑ k ∈ Finset.range (periodP A), (windowFluct A k g) ^ 2 := by
  have hconst : ∀ k ∈ (Finset.range (periodP A)).filter
      (fun k => cleanCount A k g = 0),
      (windowFluct A k g) ^ 2 = (mainTerm A g) ^ 2 := fun k hk => by
    rw [defect_forces_coherence (Finset.mem_filter.mp hk).2, neg_sq]
  have heq : ∑ k ∈ (Finset.range (periodP A)).filter
      (fun k => cleanCount A k g = 0), (windowFluct A k g) ^ 2
      = (defectCount A g : ℚ) * (mainTerm A g) ^ 2 := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, defectCount]
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun k _ _ => sq_nonneg _

/-- The headline with the S2 closed form on the right: the defect count is bounded by
    a closed rational expression in the pair correlations — which the CRT law
    (`pairCorr_eq_prod`) reduces to the clocks alone. -/
theorem defect_windows_rare_closed (A g : ℕ) :
    (defectCount A g : ℚ) * (mainTerm A g) ^ 2
      ≤ (∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g,
          (pairCorr A (Nat.dist j' j) : ℚ))
        - (periodP A : ℚ) * (mainTerm A g) ^ 2 := by
  rw [← window_variance_exact]
  exact defect_windows_rare A g

/-- The division form (`g ≥ 1` makes `mainTerm² > 0`): the defect count itself is at
    most variance over `mainTerm²` — the Markov gap `B` measured by the harness. -/
theorem defectCount_le_of_pos {A g : ℕ} (hg : 0 < g) :
    (defectCount A g : ℚ)
      ≤ ((∑ j ∈ Finset.Icc 1 g, ∑ j' ∈ Finset.Icc 1 g,
          (pairCorr A (Nat.dist j' j) : ℚ))
        - (periodP A : ℚ) * (mainTerm A g) ^ 2) / (mainTerm A g) ^ 2 := by
  rw [le_div_iff₀ (pow_pos (mainTerm_pos hg) 2)]
  exact defect_windows_rare_closed A g

/-- Zero defect windows in one period lift to the wall bound on all of ℕ:
    per-period defect-freeness IS the one-period certificate `PeriodCert`. -/
theorem cleanGapBound_of_defectCount_zero {A g : ℕ} (h : defectCount A g = 0) :
    CleanGapBound A g := by
  refine cleanGapBound_of_periodCert (periodP_pos A) periodP_dvd ?_
  intro r hr
  have hpos : 1 ≤ cleanCount A r g := by
    rcases Nat.eq_zero_or_pos (cleanCount A r g) with h0 | h1
    · exfalso
      have hmem : r ∈ (Finset.range (periodP A)).filter
          fun k => cleanCount A k g = 0 := Finset.mem_filter.mpr ⟨hr, h0⟩
      rw [defectCount, Finset.card_eq_zero] at h
      rw [h] at hmem
      exact absurd hmem (by simp)
    · exact h1
  obtain ⟨m, h1, h2, h3⟩ := cleanCount_pos_iff.mp hpos
  refine ⟨m - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show r + (m - r) = m by omega]
  exact h3

/-- The Markov numerics at `(5, 2)`: `defectCount · (6/5)² ≤ 4/5` forces
    `defectCount ≤ 5/9 < 1` — the variance bound alone kills every defect window. -/
theorem defectCount_5_2_eq_zero : defectCount 5 2 = 0 := by
  have h := defect_windows_rare 5 2
  rw [window_variance_5_2, mainTerm_5_2] at h
  by_contra hne
  have h1q : (1 : ℚ) ≤ (defectCount 5 2 : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have h2 : (1 : ℚ) * (6 / 5) ^ 2 ≤ (defectCount 5 2 : ℚ) * (6 / 5) ^ 2 := by
    apply mul_le_mul_of_nonneg_right h1q
    norm_num
  have h3 : (36 : ℚ) / 25 ≤ 4 / 5 :=
    calc (36 : ℚ) / 25 = 1 * (6 / 5) ^ 2 := by norm_num
      _ ≤ (defectCount 5 2 : ℚ) * (6 / 5) ^ 2 := h2
      _ ≤ 4 / 5 := h
  norm_num at h3

/-- **`CleanGapBound 5 2` crossed by the dispersion route alone.**  At `(A, g) =
    (5, 2)` the Markov bound is `(4/5)/(6/5)² = 5/9 < 1`: the exact variance forces
    the defect count to zero, and defect-freeness lifts to the full wall bound.
    HONESTY (the measured boundary, `tools/dispersion_run1.log`, s1 table): this is
    the ONLY scale where the averaging argument crosses the wall — the measured
    Markov gap satisfies `B(G) ≥ 1` for every `A ≥ 7` and grows to `≈ 2·10⁷` by
    `A = 29`.  A showcase of the route's exact reach, NOT a new wall instance:
    `CleanGapBound 5 2` has carried a kernel certificate since the first pass
    (`cleanGapBound_5`). -/
theorem cleanGapBound_5_via_dispersion : CleanGapBound 5 2 :=
  cleanGapBound_of_defectCount_zero defectCount_5_2_eq_zero

/-! #### Kernel instances of defect rarity (both sides literal)

Scale `5`, `g = 1`: two defect windows per period (`k ≡ 0, 3 (mod 5)`), `M = 3/5`,
variance `6/5`: the bound reads `2·(3/5)² = 18/25 ≤ 30/25`.  Scale `7`: `8` defect
windows at `g = 2`, `4` at `g = 3`.  At the wall pair `(13, G(13) = 11)` the defect
count is `0` — `periodCert_13` in S3 vocabulary, at zero new kernel cost. -/

example : defectCount 5 1 = 2 := by decide
example : (2 : ℚ) * (3 / 5) ^ 2 ≤ 6 / 5 := by norm_num
example : defectCount 7 2 = 8 := by decide
example : defectCount 7 3 = 4 := by decide

/-- Defect-freeness at the wall pair `(13, 11)`, derived from the existing kernel
    certificate `periodCert_13` — no new kernel scan. -/
theorem defectCount_13_11 : defectCount 13 11 = 0 := by
  rw [defectCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  rw [show periodP 13 = 5005 from by decide] at hk
  obtain ⟨j, hj, hclean⟩ := periodCert_13 k hk
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  intro h0
  rw [cleanCount_eq_zero_iff] at h0
  exact h0 ⟨k + j, by omega, by omega, hclean⟩

/-! ### S4 — engine energies: the exact Bernoulli-variance anchor

The squared amplitudes of the engine modes (`modeCoeff`, `modeAmp` of
`Step00StrikeFourier`) admit exact closed forms: per clock the nontrivial modes carry
`2(q−2)/q²`, all modes together `(q−2)/q`, and over the whole tuple spectrum the
engines carry exactly `M₁ − M₁²` where `M₁ = ∏ (q−2)/q` is the clean density — the
Bernoulli variance of the clean indicator, mode by mode.  The product structure also
yields the per-support profile `∏_{q∈S} 2(q−2)/q² · ∏_{q∉S} ((q−2)/q)²` for tuples
supported on a clock set `S` (same `prod_sum` computation restricted); this is the
exact anchor against which the measured `Wall_L` mode-mass profile (ledger L52) is
compared. -/

section Energy

open ComplexConjugate

/-- Summing over `ZMod q` = summing over the mode labels `0 … q−1` (local copy of the
    `Step00StrikeFourier` private reindexing lemma). -/
private theorem sum_range_natCast {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, F ((j : ℕ) : ZMod q) = ∑ j : ZMod q, F j := by
  have hinj : Set.InjOn (fun j : ℕ => ((j : ℕ) : ZMod q)) ↑(Finset.range q) := by
    intro a ha b hb hab
    have ha' : a < q := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < q := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    have hv : ((a : ℕ) : ZMod q).val = ((b : ℕ) : ZMod q).val := by
      simpa using congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt ha', ZMod.val_cast_of_lt hb'] at hv
  have himg : (Finset.range q).image (fun j : ℕ => ((j : ℕ) : ZMod q))
      = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
  rw [← himg,
    Finset.sum_image fun a ha b hb hab =>
      hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab]

private theorem stdAddChar_pow_card {q : ℕ} [NeZero q] (x : ZMod q) :
    (ZMod.stdAddChar x : ℂ) ^ q = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  have h0 : q • x = 0 := by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [h0, AddChar.map_zero_eq_one]

private theorem norm_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    ‖(ZMod.stdAddChar x : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (stdAddChar_pow_card x) (NeZero.ne q)

/-- Conjugation inverts the character: `conj ψ(x) = ψ(−x)` (unit modulus). -/
private theorem conj_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  have hmul : (ZMod.stdAddChar x : ℂ) * ZMod.stdAddChar (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [← Complex.inv_eq_conj (norm_stdAddChar x),
    (eq_inv_of_mul_eq_one_right hmul).symm]

/-- The ℂ-level per-clock energy sum: `∑_{j≠0} c_j · conj c_j = (2q − 4)/q²` —
    character orthogonality applied to the squared wing pair. -/
private theorem energy_sum_complex {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    ∑ j ∈ Finset.Ioo 0 q, (modeCoeff q j * conj (modeCoeff q j))
      = (2 * (q : ℂ) - 4) / (q : ℂ) ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  set a : ZMod q := (i6 q : ZMod q) with ha
  set cp : ZMod q := (2 : ZMod q) * a with hcp
  have hcp0 : cp ≠ 0 := by
    have h2 := mul_i6_ne_zero hq h5 (show 0 < 2 by norm_num) (by omega)
    rw [show ((2:ℕ) : ZMod q) = (2 : ZMod q) from by push_cast; rfl] at h2
    exact h2
  have hterm : ∀ j ∈ Finset.Ioo 0 q,
      modeCoeff q j * conj (modeCoeff q j)
        = (q:ℂ)⁻¹ * (q:ℂ)⁻¹
          * ((ZMod.stdAddChar ((j : ZMod q) * cp) : ℂ)
             + ZMod.stdAddChar ((j : ZMod q) * (-cp)) + 2) := by
    intro j hj
    obtain ⟨hj0, hjq⟩ := Finset.mem_Ioo.mp hj
    have hplain : modeCoeff q j
        = -((q:ℂ)⁻¹ * ((ZMod.stdAddChar (-((j : ZMod q) * a)) : ℂ)
            + ZMod.stdAddChar ((j : ZMod q) * a))) := by
      rw [modeCoeff_def, if_neg (by omega : j ≠ 0), ← ha, neg_mul]
      ring
    have hconj : conj (modeCoeff q j)
        = -((q:ℂ)⁻¹ * ((ZMod.stdAddChar ((j : ZMod q) * a) : ℂ)
            + ZMod.stdAddChar (-((j : ZMod q) * a)))) := by
      rw [hplain, map_neg, map_mul, map_add, map_inv₀, map_natCast,
        conj_stdAddChar, conj_stdAddChar, neg_neg]
    have hz : (ZMod.stdAddChar (-((j : ZMod q) * a)) : ℂ)
        * ZMod.stdAddChar (-((j : ZMod q) * a))
        = ZMod.stdAddChar ((j : ZMod q) * (-cp)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      rw [hcp]
      ring
    have hw : (ZMod.stdAddChar ((j : ZMod q) * a) : ℂ)
        * ZMod.stdAddChar ((j : ZMod q) * a)
        = ZMod.stdAddChar ((j : ZMod q) * cp) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      rw [hcp]
      ring
    have hzw : (ZMod.stdAddChar (-((j : ZMod q) * a)) : ℂ)
        * ZMod.stdAddChar ((j : ZMod q) * a) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rw [hconj, hplain]
    linear_combination ((q:ℂ)⁻¹ * (q:ℂ)⁻¹) * hz + ((q:ℂ)⁻¹ * (q:ℂ)⁻¹) * hw
      + (2 * (q:ℂ)⁻¹ * (q:ℂ)⁻¹) * hzw
  have hchar : ∀ c : ZMod q, c ≠ 0 →
      (∑ j ∈ Finset.range q, (ZMod.stdAddChar ((j : ZMod q) * c) : ℂ)) = 0 := by
    intro c hc
    rw [sum_range_natCast fun x : ZMod q => (ZMod.stdAddChar (x * c) : ℂ),
      AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar q)]
    simp [hc]
  have hIoo : Finset.Ioo 0 q = (Finset.range q).erase 0 := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_erase, Finset.mem_range]
    omega
  have hall : ∑ j ∈ Finset.range q,
      ((ZMod.stdAddChar ((j : ZMod q) * cp) : ℂ)
        + ZMod.stdAddChar ((j : ZMod q) * (-cp)) + 2) = 2 * (q : ℂ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hchar cp hcp0,
      hchar (-cp) (neg_ne_zero.mpr hcp0), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have hF0 : ((ZMod.stdAddChar (((0:ℕ) : ZMod q) * cp) : ℂ)
      + ZMod.stdAddChar (((0:ℕ) : ZMod q) * (-cp)) + 2) = 4 := by
    rw [Nat.cast_zero, zero_mul, zero_mul, AddChar.map_zero_eq_one]
    norm_num
  have hadd : ((ZMod.stdAddChar (((0:ℕ) : ZMod q) * cp) : ℂ)
        + ZMod.stdAddChar (((0:ℕ) : ZMod q) * (-cp)) + 2)
      + ∑ j ∈ (Finset.range q).erase 0,
          ((ZMod.stdAddChar ((j : ZMod q) * cp) : ℂ)
            + ZMod.stdAddChar ((j : ZMod q) * (-cp)) + 2)
      = ∑ j ∈ Finset.range q,
          ((ZMod.stdAddChar ((j : ZMod q) * cp) : ℂ)
            + ZMod.stdAddChar ((j : ZMod q) * (-cp)) + 2) :=
    Finset.add_sum_erase _
      (fun j : ℕ => (ZMod.stdAddChar ((j : ZMod q) * cp) : ℂ)
        + ZMod.stdAddChar ((j : ZMod q) * (-cp)) + 2)
      (Finset.mem_range.mpr (show (0:ℕ) < q by omega))
  have hsum : (∑ j ∈ Finset.Ioo 0 q,
      ((ZMod.stdAddChar ((j : ZMod q) * cp) : ℂ)
        + ZMod.stdAddChar ((j : ZMod q) * (-cp)) + 2)) = 2 * (q : ℂ) - 4 := by
    rw [hIoo]
    linear_combination hadd + hall - hF0
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, div_eq_mul_inv, pow_two,
    mul_inv]
  ring

/-- **The per-clock engine energy** (`engine_energy_clock`): the nontrivial modes of
    the clock `q` carry total squared amplitude EXACTLY `2(q−2)/q²`.  From character
    orthogonality alone — the archimedean size of one clock's engine bank. -/
theorem engine_energy_clock {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    ∑ j ∈ Finset.Ioo 0 q, ‖modeCoeff q j‖ ^ 2
      = 2 * ((q : ℝ) - 2) / (q : ℝ) ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  have hcast : ((∑ j ∈ Finset.Ioo 0 q, ‖modeCoeff q j‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ Finset.Ioo 0 q, (modeCoeff q j * conj (modeCoeff q j)) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Complex.ofReal_pow]
      exact (Complex.mul_conj' _).symm
  have hval : ((∑ j ∈ Finset.Ioo 0 q, ‖modeCoeff q j‖ ^ 2 : ℝ) : ℂ)
      = ((2 * ((q : ℝ) - 2) / (q : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [hcast, energy_sum_complex hq h5]
    push_cast
    ring
  exact_mod_cast hval

/-- The FULL per-clock mode energy (trivial mode included) is the survival density:
    `((q−2)/q)² + 2(q−2)/q² = (q−2)/q` — the Bernoulli mean-square of one clock. -/
private theorem clock_energy_total {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    ∑ j ∈ Finset.range q, ‖modeCoeff q j‖ ^ 2 = ((q : ℝ) - 2) / (q : ℝ) := by
  haveI : NeZero q := ⟨by omega⟩
  have hq0 : (0:ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsplit : (Finset.range q).erase 0 = Finset.Ioo 0 q := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]
    omega
  have h0 : ‖modeCoeff q 0‖ ^ 2 = (((q:ℝ) - 2) / (q:ℝ)) ^ 2 := by
    rw [modeCoeff_zero,
      show (1 : ℂ) - 2 / (q : ℂ) = (((1 : ℝ) - 2 / (q : ℝ) : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hne : (q:ℝ) ≠ 0 := ne_of_gt hq0
    congr 1
    rw [sub_div, div_self hne]
  have hadd : ‖modeCoeff q 0‖ ^ 2
      + ∑ j ∈ (Finset.range q).erase 0, ‖modeCoeff q j‖ ^ 2
      = ∑ j ∈ Finset.range q, ‖modeCoeff q j‖ ^ 2 :=
    Finset.add_sum_erase _ (fun j : ℕ => ‖modeCoeff q j‖ ^ 2)
      (Finset.mem_range.mpr (show (0:ℕ) < q by omega))
  rw [← hadd, hsplit, engine_energy_clock hq h5, h0]
  have hne : (q:ℝ) ≠ 0 := ne_of_gt hq0
  field_simp
  ring

/-- The full tuple-spectrum energy: `∑_{all p} ‖modeAmp p‖² = ∏ (q−2)/q = M₁`. -/
private theorem total_mode_energy (A : ℕ) :
    ∑ p ∈ modeTuples A, ‖modeAmp A p‖ ^ 2
      = ∏ q ∈ clocks A, ((q : ℝ) - 2) / (q : ℝ) := by
  have hamp : ∀ p ∈ modeTuples A, ‖modeAmp A p‖ ^ 2
      = ∏ x ∈ (clocks A).attach, ‖modeCoeff x.1 (p x.1 x.2)‖ ^ 2 := by
    intro p _
    rw [modeAmp, norm_prod]
    exact (Finset.prod_pow _ _ _).symm
  calc ∑ p ∈ modeTuples A, ‖modeAmp A p‖ ^ 2
      = ∑ p ∈ (clocks A).pi (fun q => Finset.range q),
          ∏ x ∈ (clocks A).attach, ‖modeCoeff x.1 (p x.1 x.2)‖ ^ 2 :=
        Finset.sum_congr rfl hamp
    _ = ∏ q ∈ clocks A, ∑ j ∈ Finset.range q, ‖modeCoeff q j‖ ^ 2 :=
        (Finset.prod_sum (clocks A) (fun q => Finset.range q)
          (fun q j => ‖modeCoeff q j‖ ^ 2)).symm
    _ = ∏ q ∈ clocks A, ((q : ℝ) - 2) / (q : ℝ) :=
        Finset.prod_congr rfl fun q hq => by
          obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
          exact clock_energy_total hp h5

/-- The zero-mode energy is the squared clean density `M₁²`. -/
private theorem zeroMode_energy (A : ℕ) :
    ‖modeAmp A (zeroMode A)‖ ^ 2
      = (∏ q ∈ clocks A, ((q : ℝ) - 2) / (q : ℝ)) ^ 2 := by
  rw [modeAmp_zeroMode,
    show ∏ q ∈ clocks A, (1 - 2 / (q : ℂ))
        = ((∏ q ∈ clocks A, ((q : ℝ) - 2) / (q : ℝ) : ℝ) : ℂ) from by
      push_cast
      refine Finset.prod_congr rfl fun q hq => ?_
      have h5 := (mem_clocks.mp hq).2.1
      have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The total engine energy: the exact Bernoulli variance `M₁ − M₁²`.**  Summed over
    ALL nontrivial mode tuples, the squared amplitudes total exactly `M₁(1 − M₁)`
    where `M₁ = ∏_{q ∈ clocks A} (q−2)/q` is the clean density: full spectrum `M₁`
    (product of per-clock Bernoulli mean-squares) minus zero mode `M₁²`.  The exact
    variance anchor for any mode-count analysis of the wall: no amplitude bound is
    asserted anywhere — this is the ℓ²-mass identity the measured `Wall_L` profile
    (L52) must and does respect. -/
theorem total_engine_energy (A : ℕ) :
    ∑ p ∈ (modeTuples A).erase (zeroMode A), ‖modeAmp A p‖ ^ 2
      = (∏ q ∈ clocks A, ((q : ℝ) - 2) / (q : ℝ))
        - (∏ q ∈ clocks A, ((q : ℝ) - 2) / (q : ℝ)) ^ 2 := by
  have h1 := total_mode_energy A
  have h2 := zeroMode_energy A
  have hsplit : ‖modeAmp A (zeroMode A)‖ ^ 2
      + ∑ p ∈ (modeTuples A).erase (zeroMode A), ‖modeAmp A p‖ ^ 2
      = ∑ p ∈ modeTuples A, ‖modeAmp A p‖ ^ 2 :=
    Finset.add_sum_erase _ (fun p => ‖modeAmp A p‖ ^ 2) (zeroMode_mem A)
  linarith

end Energy

/-! ### S5 — shift covariance and THE DISPERSION IDENTITY (exact, over ℂ)

Sliding a window by one step multiplies every mode's window sum by a fixed unit — the
tuple's frequency wave.  Summing `Fluct²` over `K` consecutive window starts therefore
reorganizes EXACTLY into a mode-pair double sum against the geometric kernel
`D_K(ω(p)·conj ω(p'))`.  No estimate is made — the identity is the exact bookkeeping
of the naive shift-dispersion route, stated so that S6 can certify its death. -/

section Dispersion

open ComplexConjugate

/-- The frequency wave of a mode tuple: the product of its per-clock waves at step
    `1`.  Shifting the window start by one multiplies the tuple's window sum by this
    unit (`modeWindowSum_succ`). -/
noncomputable def tupleWave (A : ℕ) (p : ∀ q ∈ clocks A, ℕ) : ℂ :=
  ∏ x ∈ (clocks A).attach, modeWave x.1 (p x.1 x.2) 1

private theorem modeWave_succ {q : ℕ} [NeZero q] (j m : ℕ) :
    modeWave q j (m + 1) = modeWave q j m * modeWave q j 1 := by
  rw [modeWave_def, modeWave_def, modeWave_def, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  ring

/-- One-step shift covariance: `S_{k+1}(p) = ω(p) · S_k(p)` — reindex `Ioc` by `+1`
    and factor the common wave. -/
theorem modeWindowSum_succ (A k g : ℕ) (p : ∀ q ∈ clocks A, ℕ) :
    modeWindowSum A (k + 1) g p = tupleWave A p * modeWindowSum A k g p := by
  unfold modeWindowSum tupleWave
  rw [show k + 1 + g = k + g + 1 by omega,
    show Finset.Ioc (k + 1) (k + g + 1) = (Finset.Ioc k (k + g)).image (· + 1) from
      (Finset.image_add_right_Ioc k (k + g) 1).symm,
    Finset.sum_image fun a _ b _ h => by omega, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  haveI : NeZero x.1 := ⟨by have := (mem_clocks.mp x.2).2.1; omega⟩
  rw [modeWave_succ]
  exact mul_comm _ _

/-- **Shift covariance**: `S_{k+t}(p) = ω(p)^t · S_k(p)` — exact, for every tuple. -/
theorem modeWindowSum_shift (A k g t : ℕ) (p : ∀ q ∈ clocks A, ℕ) :
    modeWindowSum A (k + t) g p = tupleWave A p ^ t * modeWindowSum A k g p := by
  induction t with
  | zero => simp
  | succ n ih =>
      rw [show k + (n + 1) = k + n + 1 by omega, modeWindowSum_succ, ih, pow_succ]
      ring

/-- `D_K` — the dispersion kernel: the geometric sum `∑_{t<K} z^t`. -/
noncomputable def geomKernel (K : ℕ) (z : ℂ) : ℂ := ∑ t ∈ Finset.range K, z ^ t

/-- The exact closed form of the kernel (`geom_sum_eq`): `K` at the diagonal ratio
    `z = 1`, `(z^K − 1)/(z − 1)` off it.  Exact — no estimate. -/
theorem geomKernel_closed (K : ℕ) (z : ℂ) :
    geomKernel K z = if z = 1 then (K : ℂ) else (z ^ K - 1) / (z - 1) := by
  unfold geomKernel
  split_ifs with h
  · subst h
    simp
  · exact geom_sum_eq h K

/-- **THE DISPERSION IDENTITY (exact).**  The `Fluct²`-sum over `K` consecutive window
    starts equals the double sum over nontrivial mode pairs of
    `c(p)·conj c(p') · S_{k₀}(p)·conj S_{k₀}(p') · D_K(ω(p)·conj ω(p'))`.
    Conjugation-correct form: `Fluct` is real (a ℚ-cast), so `Fluct² = Fluct·conj Fluct`
    and the engine decomposition (`windowFluct_eq_minorSum`) conjugates onto the second
    factor.  Pure reorganization — see the S6/S7 disclosure: this identity does not
    move the wall, it EXPOSES where the route dies. -/
theorem dispersion_identity (A k₀ g K : ℕ) :
    ∑ t ∈ Finset.range K, ((windowFluct A (k₀ + t) g : ℚ) : ℂ) ^ 2
      = ∑ p ∈ (modeTuples A).erase (zeroMode A),
          ∑ p' ∈ (modeTuples A).erase (zeroMode A),
            (modeAmp A p * conj (modeAmp A p'))
              * (modeWindowSum A k₀ g p * conj (modeWindowSum A k₀ g p'))
              * geomKernel K (tupleWave A p * conj (tupleWave A p')) := by
  have hterm : ∀ t ∈ Finset.range K,
      ((windowFluct A (k₀ + t) g : ℚ) : ℂ) ^ 2
        = ∑ p ∈ (modeTuples A).erase (zeroMode A),
            ∑ p' ∈ (modeTuples A).erase (zeroMode A),
              (modeAmp A p * (tupleWave A p ^ t * modeWindowSum A k₀ g p))
                * conj (modeAmp A p'
                    * (tupleWave A p' ^ t * modeWindowSum A k₀ g p')) := by
    intro t _
    have hself : conj ((windowFluct A (k₀ + t) g : ℚ) : ℂ)
        = ((windowFluct A (k₀ + t) g : ℚ) : ℂ) := map_ratCast (starRingEnd ℂ) _
    rw [pow_two]
    nth_rewrite 2 [← hself]
    rw [windowFluct_eq_minorSum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
    rw [modeWindowSum_shift A k₀ g t p, modeWindowSum_shift A k₀ g t p']
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' hp' => ?_
  unfold geomKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_mul, map_pow, mul_pow]
  ring

end Dispersion

/-! ### S6 — the death certificate of naive shift-dispersion

THE DISPERSION-BLINDNESS DISCLOSURE.  The naive shift-dispersion over the ceiling
segment is dead, provably, for three exact reasons assembled here:

1. the segment is exponentially shorter than the period — the ceiling gives
   `K ≈ A²/6` shift positions while the spectrum lives on `P_A = ∏ q ~ e^A`
   frequencies, so the diagonal window `|θ| ≤ 1/(6K)` of the kernel is enormously
   populated;
2. the near-diagonal carries NO kernel decay — `near_diagonal_no_decay`: every kernel
   value within `1/(6K)` of the diagonal has real part `≥ K/2`, exactly as on the
   diagonal itself;
3. the spectrum is exactly equidistributed — `modeTuples_freq_complete` /
   `modeTuples_freq_unique` / `card_modeTuples`: the CRT bijection `p ↦ r/P_A` puts
   the `P_A` mode frequencies at exact spacing `1/P_A`, so EVERY row of the dispersion
   double sum has at least `P_A/(3K) − 1` no-decay partners
   (`freq_density_near_diagonal`) — at the wall scale `13`, `g = G(13) = 11`,
   `K = 17`: at least `2·49 + 1 = 99` partners per row against `5005` frequencies.

Per-mode amplitude bounds then lose to the measured `Wall_L` mode-count combinatorics
(ledger L52): the no-decay block alone carries more weight than any uniform amplitude
saving.  This is a law about a ROUTE (an L53-genus statement: the death of a proof
strategy), NOT an iff with the wall — deliberately NOT numbered as a costume: killing
the naive route does not repackage `CleanGapBound`, it certifies that this particular
quadratic reorganization cannot cross it. -/

section DeathCertificate

open Real

/-- **No kernel decay near the diagonal.**  For a frequency offset `|θ| ≤ 1/(6K)`,
    every term of the dispersion kernel at ratio `e(θ)` has real part `≥ 1/2`
    (`cos 2πtθ ≥ cos π/3`), so the kernel's real part is at least `K/2` — exactly the
    diagonal size, no cancellation.  Elementary cosine bound; exact. -/
theorem near_diagonal_no_decay {θ : ℝ} {K : ℕ} (hK : 0 < K)
    (hθ : |θ| ≤ 1 / (6 * K)) :
    (K : ℝ) / 2 ≤ (∑ t ∈ Finset.range K,
      Complex.exp ((2 * π * θ * t : ℝ) * Complex.I)).re := by
  rw [Complex.re_sum]
  have hpi := Real.pi_pos
  have hbound : ∀ t ∈ Finset.range K,
      (1 : ℝ) / 2 ≤ (Complex.exp ((2 * π * θ * t : ℝ) * Complex.I)).re := by
    intro t ht
    rw [Complex.exp_ofReal_mul_I_re]
    have hKpos : (0:ℝ) < K := by exact_mod_cast hK
    have ht1 : (t : ℝ) ≤ (K : ℝ) - 1 := by
      have h1 : t + 1 ≤ K := Finset.mem_range.mp ht
      have h2 : ((t + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have hθt : |θ| * t ≤ 1 / 6 := by
      calc |θ| * t ≤ 1 / (6 * K) * t :=
            mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg t)
        _ ≤ 1 / (6 * K) * ((K : ℝ) - 1) := by
            apply mul_le_mul_of_nonneg_left ht1
            positivity
        _ ≤ 1 / 6 := by
            rw [one_div_mul_eq_div,
              div_le_div_iff₀ (by linarith : (0:ℝ) < 6 * K) (by norm_num : (0:ℝ) < 6)]
            nlinarith
    have habs : |2 * π * θ * t| ≤ π / 3 := by
      have h1 : |2 * π * θ * ↑t| = 2 * π * |θ| * t := by
        rw [show (2:ℝ) * π * θ * ↑t = θ * (2 * π * ↑t) by ring, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * ↑t)]
        ring
      rw [h1]
      calc 2 * π * |θ| * ↑t = 2 * π * (|θ| * ↑t) := by ring
        _ ≤ 2 * π * (1 / 6) :=
            mul_le_mul_of_nonneg_left hθt (by positivity)
        _ = π / 3 := by ring
    calc (1:ℝ)/2 = Real.cos (π / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |2 * π * θ * ↑t| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
      _ = Real.cos (2 * π * θ * ↑t) := Real.cos_abs _
  calc (K : ℝ) / 2 = ∑ _t ∈ Finset.range K, (1:ℝ)/2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum hbound

/-- The kernel form: `Re D_K(e(θ)) ≥ K/2` on the whole near-diagonal `|θ| ≤ 1/(6K)`. -/
theorem geomKernel_no_decay {θ : ℝ} {K : ℕ} (hK : 0 < K)
    (hθ : |θ| ≤ 1 / (6 * K)) :
    (K : ℝ) / 2 ≤ (geomKernel K (Complex.exp ((2 * π * θ : ℝ) * Complex.I))).re := by
  have h := near_diagonal_no_decay hK hθ
  unfold geomKernel
  have hexp : ∀ t ∈ Finset.range K,
      Complex.exp ((2 * π * θ : ℝ) * Complex.I) ^ t
        = Complex.exp ((2 * π * θ * t : ℝ) * Complex.I) := by
    intro t _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hexp]
  exact h

/-- CRT frequency uniqueness core: two labels below `P_A` with equal residues at
    every clock coincide. -/
private theorem freq_eq_of_forall_mod_eq {A r r' : ℕ} (hr : r < periodP A)
    (hr' : r' < periodP A) (h : ∀ q ∈ clocks A, r % q = r' % q) : r = r' := by
  rcases le_total r r' with hle | hle
  · have hdvd : periodP A ∣ r' - r :=
      periodP_dvd_of_forall_dvd fun q hq => (Nat.modEq_iff_dvd' hle).mp (h q hq)
    rcases Nat.eq_zero_or_pos (r' - r) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega
  · have hdvd : periodP A ∣ r - r' :=
      periodP_dvd_of_forall_dvd fun q hq =>
        (Nat.modEq_iff_dvd' hle).mp (Nat.ModEq.symm (h q hq))
    rcases Nat.eq_zero_or_pos (r - r') with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega

/-- The tuple spectrum has exactly `P_A` modes — one per available frequency. -/
theorem card_modeTuples (A : ℕ) : (modeTuples A).card = periodP A := by
  rw [show modeTuples A = (clocks A).pi (fun q => Finset.range q) from rfl,
    Finset.card_pi]
  exact Finset.prod_congr rfl fun q _ => Finset.card_range q

/-- **The CRT frequency bijection (existence).**  Every mode tuple is realized by a
    frequency label `r < P_A` via `j_q = r mod q`: the spectrum of the engine
    decomposition is EXACTLY the `P_A` equally spaced frequencies `r/P_A`. -/
theorem modeTuples_freq_complete (A : ℕ) :
    ∀ p ∈ modeTuples A, ∃ r, ∃ _ : r ∈ Finset.range (periodP A),
      p = fun q (_ : q ∈ clocks A) => r % q := by
  apply Finset.surj_on_of_inj_on_of_card_le
    (f := fun r (_ : r ∈ Finset.range (periodP A)) =>
      fun q (_ : q ∈ clocks A) => r % q)
  · intro r hr
    rw [show modeTuples A = (clocks A).pi (fun q => Finset.range q) from rfl,
      Finset.mem_pi]
    intro q hq
    exact Finset.mem_range.mpr
      (Nat.mod_lt r (by have := (mem_clocks.mp hq).2.1; omega))
  · intro r r' hr hr' heq
    exact freq_eq_of_forall_mod_eq (Finset.mem_range.mp hr) (Finset.mem_range.mp hr')
      fun q hq => congrFun (congrFun heq q) hq
  · rw [card_modeTuples, Finset.card_range]

/-- **The CRT frequency bijection (uniqueness).**  Distinct labels below `P_A` give
    distinct tuples. -/
theorem modeTuples_freq_unique {A r r' : ℕ} (hr : r ∈ Finset.range (periodP A))
    (hr' : r' ∈ Finset.range (periodP A))
    (h : (fun q (_ : q ∈ clocks A) => r % q)
      = fun q (_ : q ∈ clocks A) => r' % q) : r = r' :=
  freq_eq_of_forall_mod_eq (Finset.mem_range.mp hr) (Finset.mem_range.mp hr')
    fun q hq => congrFun (congrFun h q) hq

/-- Circular nearness of frequency labels mod `P`: the difference `(a' − a) mod P`
    lies within `D` of `0` on the circle. -/
def NearFreq (P D a a' : ℕ) : Prop :=
  (a' + P - a) % P ≤ D ∨ P - D ≤ (a' + P - a) % P

instance (P D a a' : ℕ) : Decidable (NearFreq P D a a') := by
  unfold NearFreq
  infer_instance

/-- **Near-diagonal frequency density.**  With `D = ⌊P/(6K)⌋`, every frequency label
    has at least `2D + 1 ≥ P/(3K) − 1` labels within circular distance `D` — i.e.
    within kernel offset `1/(6K)`: the no-decay block of every dispersion row grows
    linearly in `P/K`.  With `K` pinned to the ceiling segment (`K ≈ A²/6`) and
    `P_A ~ e^A`, the no-decay mass per row explodes — the death certificate's
    quantitative clause. -/
theorem freq_density_near_diagonal {P K : ℕ} (hP : 0 < P) (hK : 0 < K)
    {a : ℕ} (ha : a < P) :
    (P : ℚ) / (3 * K) - 1
      ≤ (((Finset.range P).filter (NearFreq P (P / (6 * K)) a)).card : ℚ) := by
  set D := P / (6 * K) with hD
  have h1 : D * (6 * K) ≤ P := Nat.div_mul_le_self P (6 * K)
  have h2 : 6 * D ≤ D * (6 * K) := by
    calc 6 * D = D * 6 := by ring
      _ ≤ D * (6 * K) := Nat.mul_le_mul_left D (by omega)
  have h6D : 6 * D ≤ P := le_trans h2 h1
  have h2D : 2 * D < P := by omega
  have hinj : ∀ e₁ ∈ Finset.Icc 0 (2 * D), ∀ e₂ ∈ Finset.Icc 0 (2 * D),
      (a + (P - D + e₁)) % P = (a + (P - D + e₂)) % P → e₁ = e₂ := by
    intro e₁ h₁ e₂ h₂ he
    rw [Finset.mem_Icc] at h₁ h₂
    have hc1 : P - D + e₁ ≡ P - D + e₂ [MOD P] :=
      Nat.ModEq.add_left_cancel' a he
    have hc2 : e₁ ≡ e₂ [MOD P] := Nat.ModEq.add_left_cancel' (P - D) hc1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc2
  have hInjOn : Set.InjOn (fun e => (a + (P - D + e)) % P) ↑(Finset.Icc 0 (2 * D)) :=
    fun e₁ h₁ e₂ h₂ he =>
      hinj e₁ (Finset.mem_coe.mp h₁) e₂ (Finset.mem_coe.mp h₂) he
  have hSsub : (Finset.Icc 0 (2 * D)).image (fun e => (a + (P - D + e)) % P)
      ⊆ (Finset.range P).filter (NearFreq P D a) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [Finset.mem_Icc] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hP), ?_⟩
    have hdiff : ((a + (P - D + e)) % P + P - a) % P = (P - D + e) % P := by
      have t1 : (a + (P - D + e)) % P + P ≡ (a + (P - D + e)) % P [MOD P] :=
        Nat.add_modEq_left_iff.mpr dvd_rfl
      have t2 : (a + (P - D + e)) % P ≡ a + (P - D + e) [MOD P] :=
        Nat.mod_modEq _ _
      have t3 : (a + (P - D + e)) % P + P ≡ a + (P - D + e) [MOD P] := t1.trans t2
      have t4 : ((a + (P - D + e)) % P + P - a) + a
          ≡ (P - D + e) + a [MOD P] := by
        rw [show ((a + (P - D + e)) % P + P - a) + a
            = (a + (P - D + e)) % P + P from by
          have := Nat.mod_lt (a + (P - D + e)) hP
          omega,
          show (P - D + e) + a = a + (P - D + e) by omega]
        exact t3
      exact Nat.ModEq.add_right_cancel' a t4
    unfold NearFreq
    rw [hdiff]
    rcases Nat.lt_or_ge e D with hlt | hge
    · right
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · left
      rw [show P - D + e = P + (e - D) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hcardS : ((Finset.Icc 0 (2 * D)).image
      (fun e => (a + (P - D + e)) % P)).card = 2 * D + 1 := by
    rw [Finset.card_image_of_injOn hInjOn, Nat.card_Icc]
    omega
  have hcard_le : 2 * D + 1 ≤ ((Finset.range P).filter (NearFreq P D a)).card := by
    rw [← hcardS]
    exact Finset.card_le_card hSsub
  have hdm := Nat.div_add_mod P (6 * K)
  have hrlt : P % (6 * K) < 6 * K := Nat.mod_lt P (by omega)
  have hPq : (P : ℚ) = 6 * (K : ℚ) * (D : ℚ) + ((P % (6 * K) : ℕ) : ℚ) := by
    exact_mod_cast hdm.symm
  have hrq : ((P % (6 * K) : ℕ) : ℚ) < 6 * K := by exact_mod_cast hrlt
  calc (P : ℚ) / (3 * K) - 1 ≤ ((2 * D + 1 : ℕ) : ℚ) := by
        rw [sub_le_iff_le_add,
          div_le_iff₀ (show (0:ℚ) < 3 * K from by
            exact_mod_cast (show (0:ℕ) < 3 * K by omega))]
        push_cast
        nlinarith [hPq, hrq]
    _ ≤ _ := by exact_mod_cast hcard_le

/-! #### Kernel instances of the death certificate at the wall scale

`A = 13`, `g = G(13) = 11`, ceiling segment `K = 17` (`6(k+g)+1 < 169` caps the usable
starts), period `P₁₃ = 5005`: `D = ⌊5005/102⌋ = 49`, so every dispersion row carries at
least `2·49 + 1 = 99` no-decay partners — while the whole segment offers only `17`
shifts to average over. -/

example : (5005 : ℕ) / (6 * 17) = 49 := by norm_num

example : (5005 : ℚ) / (3 * 17) - 1 ≤ ((2 * 49 + 1 : ℕ) : ℚ) := by norm_num

/-- The density bound instantiated at the wall scale: at least `99` no-decay partners
    per row (of `≥ 5005/51 − 1 ≈ 97.1` guaranteed). -/
example (a : ℕ) (ha : a < 5005) :
    (5005 : ℚ) / (3 * 17) - 1
      ≤ (((Finset.range 5005).filter
          (NearFreq 5005 (5005 / (6 * 17)) a)).card : ℚ) :=
  freq_density_near_diagonal (by norm_num) (by norm_num) ha

end DeathCertificate

/-!
### Axiom audit (performed with `#print axioms` from a scratch footer, then removed)

    #print axioms pairCorr_eq_prod               -- [propext, Classical.choice, Quot.sound]
    #print axioms cq_eq_two                      -- [propext, Classical.choice, Quot.sound]
    #print axioms cq_eq_three_pos                -- [propext, Classical.choice, Quot.sound]
    #print axioms cq_eq_three_neg                -- [propext, Classical.choice, Quot.sound]
    #print axioms cq_eq_four                     -- [propext, Classical.choice, Quot.sound]
    #print axioms pairCorr_at_13                 -- [propext, Classical.choice, Quot.sound]
    #print axioms first_moment_eq_mainTerm       -- [propext, Classical.choice, Quot.sound]
    #print axioms second_moment                  -- [propext, Classical.choice, Quot.sound]
    #print axioms window_variance_exact          -- [propext, Classical.choice, Quot.sound]
    #print axioms window_variance_at_13          -- [propext, Classical.choice, Quot.sound]
    #print axioms defect_windows_rare            -- [propext, Classical.choice, Quot.sound]
    #print axioms defect_windows_rare_closed     -- [propext, Classical.choice, Quot.sound]
    #print axioms defectCount_le_of_pos          -- [propext, Classical.choice, Quot.sound]
    #print axioms cleanGapBound_of_defectCount_zero
                                                 -- [propext, Classical.choice, Quot.sound]
    #print axioms cleanGapBound_5_via_dispersion -- [propext, Classical.choice, Quot.sound]
    #print axioms defectCount_13_11              -- [propext, Classical.choice, Quot.sound]
    #print axioms engine_energy_clock            -- [propext, Classical.choice, Quot.sound]
    #print axioms total_engine_energy            -- [propext, Classical.choice, Quot.sound]
    #print axioms modeWindowSum_shift            -- [propext, Classical.choice, Quot.sound]
    #print axioms dispersion_identity            -- [propext, Classical.choice, Quot.sound]
    #print axioms geomKernel_closed              -- [propext, Classical.choice, Quot.sound]
    #print axioms near_diagonal_no_decay         -- [propext, Classical.choice, Quot.sound]
    #print axioms geomKernel_no_decay            -- [propext, Classical.choice, Quot.sound]
    #print axioms card_modeTuples                -- [propext, Classical.choice, Quot.sound]
    #print axioms modeTuples_freq_complete       -- [propext, Classical.choice, Quot.sound]
    #print axioms modeTuples_freq_unique         -- [propext, Classical.choice, Quot.sound]
    #print axioms freq_density_near_diagonal     -- [propext, Classical.choice, Quot.sound]

No `sorry`, no `native_decide`, no repo axiom (`step00FirstCause` is NOT used): every
declaration of this module is machine-proved under the three standard axioms.
-/

end WindowDispersion
end EuclidsPath
