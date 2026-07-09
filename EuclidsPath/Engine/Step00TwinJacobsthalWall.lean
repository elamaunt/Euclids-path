import EuclidsPath.Engine.Step00GradedWindowComplex

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The twin-Jacobsthal wall — Line C discharged to a single quantitative named input

Assault postmortem of this pass (numeric ledger tools/LAWS_ordered_exponent.md):

* **Line A (phase-mirror matching): REFUTED** (L17).  Every phase-mirror involution on the
  killed sector flips `wingSign` at the fair-coin rate 0.4993–0.4999 (|z| ≤ 1.1), identically
  under the Selberg foils — the parity sign carries no phase-mirror structure.  No Lean content;
  the matching route through `GradedKilledBoundaryMatching` needs a NON-sign pairing invariant.
* **Line B (index telescope): RESOLVED in corrected form.**  Constancy of the relative index in
  the apex is refuted (L13), but its `M0`-invariance is now the green theorem
  `relIndexStruct_m0_invariant` (`Step00GradedWindowComplex`), and the survivor tournament
  `eSS_eq_choose_two` pins the exact apex law.
* **Line C (short-window reduction): THE WINNER — this file.**  The full-period census (L18)
  found that the largest gap `G(A)` between consecutive `Clean A` centers satisfies
  `G(A) ≤ A²/6` at EVERY tested scale, with stable margin (`G/(A²/6)` ≈ 0.35–0.61, exact scans
  through `A = 23`).  Here that law becomes a single named wall and a green escalation:

  * `CleanGapBound A L` — every window `(k, k+L]` contains a clean center;
  * `PeriodCert A L P` — the DECIDABLE one-period certificate; `cleanGapBound_of_periodCert`
    lifts it to all of ℕ (clean periodicity in steps of `P`, kernel-checkable per scale);
  * kernel certificates at the measured exact gaps: `A = 5 (G=2, P=5)`, `7 (5, 35)`,
    `11 (7, 385)`, `13 (11, 5005)` — machine-proved instances of the wall, margins vs `A²/7`:
    `2 ≤ 3`, `5 ≤ 7`, `7 ≤ 17`, `11 ≤ 24`;
  * **`TwinJacobsthalBound`** — the named wall: `CleanGapBound A (A²/7)` for every prime
    `A ≥ 5` (the `1/7 < 1/6` slack is what the measured margins afford, and what the
    escalation needs);
  * **`twinCenters_unbounded_of_twinJacobsthal` (green)** — the wall forces twins above every
    horizon: choose a prime `A ≥ 7(M0+7)` (infinitude of primes only — no Bertrand), the gap
    bound plants a clean center in `(M0, M0 + A²/7]`, and both wings sit below `A²`, so
    `sink_is_twin` fires; the route then reaches `TwinLowers.Infinite` through the graded
    killed-boundary bridge (`twinLowersInfinite_of_twinJacobsthal`).

## Honest status of the wall

`TwinJacobsthalBound` is a HYPOTHESIS, never an axiom.  It is (a) numerically exact-verified
through `A = 23` by full-period scans with margins far from tight and no drift, (b) kernel-PROVED
here for `A ∈ {5, 7, 11, 13}`, (c) SUFFICIENT for twin infinitude (green), (d) per-scale
falsifiable: each `A` is a finite computation, and a failing `A` would be a machine-checkable
refutation.  It is plausibly STRICTLY STRONGER than the twin conjecture (a uniform
Jacobsthal-type gap law for the twin sieve — asymptotically a Cramér-strength statement, since
`ln² P_A ≈ A²`); the converse is NOT claimed.  Compared to `OrnamentEngineBridge` and
`RelativeCurvatureRealizationProblem`, the wall is strictly sharper in FORM: one quantitative,
scale-indexed, kernel-instantiable inequality about the computable gap function of the sieve —
the parity barrier compressed into the single constant `1/7`.
-/

namespace EuclidsPath
namespace TwinJacobsthalWall

open EuclidsPath.Residuals
open EuclidsPath.CleanGraph
open EuclidsPath.GeometryFront

/-! ### The gap predicate and its one-period certificate -/

/-- Every window `(k, k+L]` contains a clean center at scale `A`. -/
def CleanGapBound (A L : ℕ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, k < m ∧ m ≤ k + L ∧ Clean A m

/-- A longer window is easier. -/
theorem cleanGapBound_mono {A L L' : ℕ} (h : CleanGapBound A L) (hLL : L ≤ L') :
    CleanGapBound A L' := fun k => by
  obtain ⟨m, h1, h2, h3⟩ := h k
  exact ⟨m, h1, by omega, h3⟩

/-- The decidable one-period certificate: every residue start `r < P` finds a clean center
    within `L` steps. -/
def PeriodCert (A L P : ℕ) : Prop :=
  ∀ r ∈ Finset.range P, ∃ j ∈ Finset.Icc 1 L, Clean A (r + j)

instance periodCertDecidable (A L P : ℕ) : Decidable (PeriodCert A L P) :=
  inferInstanceAs (Decidable (∀ r ∈ Finset.range P, ∃ j ∈ Finset.Icc 1 L, Clean A (r + j)))

/-- Cleanliness is `P`-periodic once every active clock divides `6P`. -/
theorem clean_shift {A P : ℕ} (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P)
    {m : ℕ} (hm : 1 ≤ m) : Clean A (m + P) ↔ Clean A m := by
  constructor
  · intro h q hq hqA hor
    apply h q hq hqA
    rcases hor with hd | hd
    · left
      have he : 6 * (m + P) - 1 = 6 * P + (6 * m - 1) := by omega
      rw [he]
      exact dvd_add (hdvd q hq hqA) hd
    · right
      have he : 6 * (m + P) + 1 = 6 * P + (6 * m + 1) := by omega
      rw [he]
      exact dvd_add (hdvd q hq hqA) hd
  · intro h q hq hqA hor
    apply h q hq hqA
    rcases hor with hd | hd
    · left
      have he : 6 * (m + P) - 1 = 6 * P + (6 * m - 1) := by omega
      rw [he] at hd
      exact (Nat.dvd_add_right (hdvd q hq hqA)).mp hd
    · right
      have he : 6 * (m + P) + 1 = 6 * P + (6 * m + 1) := by omega
      rw [he] at hd
      exact (Nat.dvd_add_right (hdvd q hq hqA)).mp hd

theorem clean_add_mul_period {A P : ℕ} (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P)
    {x : ℕ} (hx : 1 ≤ x) : ∀ t : ℕ, (Clean A (x + P * t) ↔ Clean A x)
  | 0 => by simp
  | t + 1 => by
      have he : x + P * (t + 1) = (x + P * t) + P := by ring
      rw [he, clean_shift hdvd (by omega : 1 ≤ x + P * t)]
      exact clean_add_mul_period hdvd hx t

/-- **Lift**: a kernel-checkable one-period certificate yields the gap bound on all of ℕ. -/
theorem cleanGapBound_of_periodCert {A L P : ℕ} (hP0 : 0 < P)
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P)
    (hcert : PeriodCert A L P) : CleanGapBound A L := by
  intro k
  obtain ⟨j, hjmem, hclean⟩ :=
    hcert (k % P) (Finset.mem_range.mpr (Nat.mod_lt _ hP0))
  obtain ⟨hj1, hjL⟩ := Finset.mem_Icc.mp hjmem
  refine ⟨k + j, by omega, by omega, ?_⟩
  have hmod := Nat.mod_add_div k P
  have hdecomp : k + j = (k % P + j) + P * (k / P) := by omega
  rw [hdecomp]
  exact (clean_add_mul_period hdvd (by omega) (k / P)).mpr hclean

/-! ### Kernel certificates at the measured exact gaps -/

/-- `G(5) = 2`: among any two consecutive centers one is clean at scale 5. -/
theorem periodCert_5 : PeriodCert 5 2 5 := by decide

/-- `G(7) = 5` over the period 35. -/
theorem periodCert_7 : PeriodCert 7 5 35 := by decide

set_option maxRecDepth 8000 in
/-- `G(11) = 7` over the period 385. -/
theorem periodCert_11 : PeriodCert 11 7 385 := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- `G(13) = 11` over the period 5005. -/
theorem periodCert_13 : PeriodCert 13 11 5005 := by decide

private theorem dvd_helper {A P : ℕ} (h : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∣ P) :
    ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P := by
  intro q hq hqA
  rcases Nat.lt_or_ge q 5 with h5 | h5
  · interval_cases q
    · exact absurd hq (by norm_num)
    · exact absurd hq (by norm_num)
    · exact Dvd.dvd.mul_right (by norm_num) P
    · exact Dvd.dvd.mul_right (by norm_num) P
    · exact absurd hq (by norm_num)
  · exact Dvd.dvd.mul_left (h q hq h5 hqA) 6

/-- The gap bound at scale 5, on all of ℕ (kernel + periodicity). -/
theorem cleanGapBound_5 : CleanGapBound 5 2 := by
  refine cleanGapBound_of_periodCert (by norm_num) (dvd_helper ?_) periodCert_5
  intro q hq h5 hA
  have : q = 5 := by omega
  subst this
  rfl

/-- The gap bound at scale 7. -/
theorem cleanGapBound_7 : CleanGapBound 7 5 := by
  refine cleanGapBound_of_periodCert (by norm_num) (dvd_helper ?_) periodCert_7
  intro q hq h5 hA
  interval_cases q
  · exact Dvd.intro 7 rfl
  · exact absurd hq (by norm_num)
  · exact Dvd.intro 5 rfl

/-- The gap bound at scale 11. -/
theorem cleanGapBound_11 : CleanGapBound 11 7 := by
  refine cleanGapBound_of_periodCert (by norm_num) (dvd_helper ?_) periodCert_11
  intro q hq h5 hA
  interval_cases q
  · exact ⟨77, rfl⟩
  · exact absurd hq (by norm_num)
  · exact ⟨55, rfl⟩
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact ⟨35, rfl⟩

/-- The gap bound at scale 13. -/
theorem cleanGapBound_13 : CleanGapBound 13 11 := by
  refine cleanGapBound_of_periodCert (by norm_num) (dvd_helper ?_) periodCert_13
  intro q hq h5 hA
  interval_cases q
  · exact ⟨1001, rfl⟩
  · exact absurd hq (by norm_num)
  · exact ⟨715, rfl⟩
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact ⟨455, rfl⟩
  · exact absurd hq (by norm_num)
  · exact ⟨385, rfl⟩

/-! ### The named wall and the green escalation -/

/-- **THE NAMED WALL (Line C): the twin-Jacobsthal bound.**  Every prime scale `A ≥ 5` admits
    the gap bound at window length `A²/7`.  A HYPOTHESIS, never an axiom: exact-verified through
    `A = 23` (margins 0.35–0.61 of the `A²/6` ceiling, no drift), kernel-proved below for
    `A ∈ {5,7,11,13}`, per-scale falsifiable, plausibly strictly stronger than the twin
    conjecture (a Cramér-strength uniform gap law: `ln² P_A ≈ A²`). -/
def TwinJacobsthalBound : Prop :=
  ∀ A : ℕ, A.Prime → 5 ≤ A → CleanGapBound A (A ^ 2 / 7)

/-- **The weakest sufficient form of the wall**: the gap bound at COFINALLY many prime scales
    (a strictly weaker hypothesis than `TwinJacobsthalBound`; the escalation below only ever
    consumes one sufficiently large scale per horizon). -/
def TwinJacobsthalBoundCofinal : Prop :=
  ∀ A0 : ℕ, ∃ A : ℕ, A0 ≤ A ∧ A.Prime ∧ CleanGapBound A (A ^ 2 / 7)

theorem twinJacobsthalCofinal_of_full (H : TwinJacobsthalBound) :
    TwinJacobsthalBoundCofinal := by
  intro A0
  obtain ⟨A, hge, hp⟩ := Nat.exists_infinite_primes (max A0 5)
  exact ⟨A, le_trans (le_max_left _ _) hge, hp,
    H A hp (le_trans (le_max_right _ _) hge)⟩

/-- The kernel-proved instances of the wall at the small scales (margin `G(A) ≤ A²/7`). -/
theorem twinJacobsthal_at_5 : CleanGapBound 5 (5 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_5 (by norm_num)

theorem twinJacobsthal_at_7 : CleanGapBound 7 (7 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_7 (by norm_num)

theorem twinJacobsthal_at_11 : CleanGapBound 11 (11 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_11 (by norm_num)

theorem twinJacobsthal_at_13 : CleanGapBound 13 (13 ^ 2 / 7) :=
  cleanGapBound_mono cleanGapBound_13 (by norm_num)

/-- **THE ESCALATION (green): even the cofinal wall forces a twin above every horizon.**
    Take any wall scale `A ≥ 7(M0+7)` (no Bertrand needed) — the gap bound plants a clean
    center in `(M0, M0 + A²/7]`, both its wings sit below `A²`, and `sink_is_twin` fires. -/
theorem twinCenters_unbounded_of_twinJacobsthalCofinal (H : TwinJacobsthalBoundCofinal) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m := by
  intro M0
  obtain ⟨A, hAge, hAp, hbound⟩ := H (7 * (M0 + 7))
  have h5 : 5 ≤ A := by omega
  obtain ⟨m, hkm, hmle, hclean⟩ := hbound M0
  have hS : A ^ 2 = A * A := sq A
  have hA2 : 49 * (M0 + 7) ^ 2 ≤ A ^ 2 := by nlinarith
  have hbig : 6 * M0 + 8 ≤ A ^ 2 / 7 := by
    have hmono : 49 * (M0 + 7) ^ 2 / 7 ≤ A ^ 2 / 7 := Nat.div_le_div_right hA2
    have h49 : 49 * (M0 + 7) ^ 2 / 7 = 7 * (M0 + 7) ^ 2 := by omega
    nlinarith [sq_nonneg (M0 + 7), hmono, h49.symm.le]
  have hwing : 6 * m + 1 < A * A := by
    have hdm := Nat.div_add_mod (A ^ 2) 7
    omega
  exact ⟨m, hkm, sink_is_twin (by omega) (by omega) (by omega) (by omega) hclean⟩

/-- The full wall forces twins (corollary of the cofinal escalation). -/
theorem twinCenters_unbounded_of_twinJacobsthal (H : TwinJacobsthalBound) :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ TwinCenterZ m :=
  twinCenters_unbounded_of_twinJacobsthalCofinal (twinJacobsthalCofinal_of_full H)

/-- The wall inhabits the graded killed-boundary route (via the disclosure iff). -/
theorem orderedExponentRoute_of_twinJacobsthalCofinal (H : TwinJacobsthalBoundCofinal) :
    Nonempty GradedKilledBoundary.OrderedExponentRoute :=
  GradedKilledBoundary.nonempty_orderedExponentRoute_iff_unboundedTwinCenters.mpr
    (twinCenters_unbounded_of_twinJacobsthalCofinal H)

/-- **The wall reaches the goal**: `TwinJacobsthalBoundCofinal → TwinLowers.Infinite`, through
    the graded route and the existing ornament adapter.  Conditional ONLY on the named wall. -/
theorem twinLowersInfinite_of_twinJacobsthalCofinal (H : TwinJacobsthalBoundCofinal) :
    TwinLowers.Infinite := by
  obtain ⟨R⟩ := orderedExponentRoute_of_twinJacobsthalCofinal H
  exact GradedKilledBoundary.twinLowersInfinite_of_orderedExponentRoute R

/-- The full-wall corollary. -/
theorem twinLowersInfinite_of_twinJacobsthal (H : TwinJacobsthalBound) :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_twinJacobsthalCofinal (twinJacobsthalCofinal_of_full H)

end TwinJacobsthalWall
end EuclidsPath
