import EuclidsPath.Engine.Step00TwinJacobsthalWall

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The transfer-operator costume — two spectral objects unmasked, one exact law gained

A certified kill of the imaginary-objects phase.  The proposed observable class was: "the twin
sieve as a transfer operator — killed-shift truncations, induced return maps, and their
spectra/pseudospectra carry content the window layer cannot see."  This module makes the
picture EXACT in List/Bool discipline and proves that two of its three objects are costumes of
existing layers, then extracts the one genuinely new exact asset the picture affords.

## The three objects

1. **The killed shift** `killedStep A : r ↦ r+1, absorbed at clean centers` (the sieve's
   transfer operator with the survivor sector deleted: `K = D·R`, kill at `Clean`).
   **`cleanGapBound_iff_killed_nilpotent`** — `K^g = 0` (every `g`-fold orbit is absorbed) is
   EQUIVALENT to the wall's gap law `CleanGapBound A g`.  This is a disclosure-iff in the style
   of `escape_iff_unbounded_twins` (`GenealogyBasins`): the spectral/dynamical costume of the
   gap law.  There is no eigenvalue-1 vector, no Perron picture, no perpetual engine — the
   abelian killed dynamics is nilpotency-broken at exactly the gap.  Kernel instances at the
   measured exact gaps: `A = 5 (g=2, P=5)`, `7 (5, 35)`, `11 (7, 385)`, `13 (11, 5005)`,
   with `killed_nilpotent_of_period` lifting one period to all of ℕ
   (via `clean_add_mul_period`), and the closed loop `cleanGapBound_via_killed_5` rederiving
   the wall's law from pure nilpotency.
2. **The energy of the killed shift** — `killed_energy_forward` / `killed_energy_backward`:
   composing the shift with its reverse gives partial identities cut by the clean indicator
   (`K∘Kᵀ` and `Kᵀ∘K` are 0/1 diagonals).  ALL singular values of every window truncation are
   `0` or `1`: the "gap statistics of window-restricted transfer matrices" observable is DEAD —
   its spectra and pseudospectra are trivial, determined by the clean indicator, i.e. by the
   additive layer.  (The full cyclic — unkilled — shift is a circulant, hence
   character-diagonal: `Matrix.circulant_apply` territory; its spectrum is the character layer
   verbatim.  No Lean content needed for a diagonal fact about a costume.)
3. **The induced return map on clean residues** — the one genuinely NEW exact law:
   **`kac_return_identity`** (Kac).  The first-return times `τ` of the induced map tile the
   period exactly: `∑_{r ∈ cleanResidues} τ(r) = P`.  Proved in FULL GENERALITY (not just
   kernel instances) by the telescoping master identity `kac_master`
   (`∑_{clean r ∈ (x, x+n]} τ(r) + τ(x)-anchor = n + τ(x+n)-anchor`), plus periodicity to
   close the cycle.  Corollaries: `max_return_le_of_cleanGapBound` pins the max side to the
   wall (`τ ≤ g` under `CleanGapBound A g`), and `mean_gap_exact`
   (`P ≤ #cleanResidues · g`) is the max-vs-mean form: the mean return time is
   `P / ∏(q−2) = ∏ q/(q−2)` (the Hardy–Littlewood local factor, cf. `admissible_card` in
   `Step00TwoEngineOscillation`), while the wall bounds the MAX.  Kernel census of the counts:
   `#cleanResidues = 3, 15, 135, 1485 = ∏_{5 ≤ q ≤ A} (q−2)` at `A = 5, 7, 11, 13`.

## DISCLOSURE — costume verdicts and anti-vocabulary

* Object (i) is COSTUME #5 of the wall: killed-shift nilpotency at index `g` IS
  `CleanGapBound A g` — the iff relocates the wall without lowering it by a brick.
* Object (ii) is a costume of the character layer: the unkilled shift is circulant
  (character-diagonal), and the killed truncations have 0/1 singular values — nothing lives
  between the additive layer and the clean indicator.
* The ONLY spectral object with possible content is the peel-band operator (growing labels),
  which belongs to the bilinear module, NOT here.
* Kac's identity is the genuinely new exact asset: the mean-gap dual of the window identity
  (`mainTerm = g · density` ↔ `∑ τ = P`).
* Anti-vocabulary: no claims above the certified scales; the nilpotency-index facts at
  `A ∈ {5,…,13}` are finite-range kernel certificates; the general theorems are exact
  identities about the sieve's period, not asymptotic statements.
-/

namespace EuclidsPath
namespace TransferCostume

open EuclidsPath.CleanGraph
open EuclidsPath.TwinJacobsthalWall

/-! ### §1 The killed shift and its nilpotency -/

/-- **The killed shift** `K`: advance the center by one, absorb (kill) on arrival at a clean
    center.  This is the sieve transfer operator with the survivor sector deleted — the
    partial map whose matrix is the 0/1 subdiagonal shift cut at clean columns. -/
def killedStep (A r : ℕ) : Option ℕ :=
  if Clean A (r + 1) then none else some (r + 1)

/-- `g`-fold iteration of the killed shift (`K^g` applied to the point mass at `r`). -/
def iterateKilled (A : ℕ) : ℕ → ℕ → Option ℕ
  | 0, r => some r
  | g + 1, r => if Clean A (r + 1) then none else iterateKilled A g (r + 1)

/-- The iteration is literally the `Option.bind`-power of the one-step kernel. -/
theorem iterateKilled_succ_bind (A g r : ℕ) :
    iterateKilled A (g + 1) r = (killedStep A r).bind (iterateKilled A g) := by
  by_cases hc : Clean A (r + 1) <;> simp [iterateKilled, killedStep, hc]

/-- **Absorption law**: the `g`-fold killed orbit from `r` dies iff some center in the window
    `(r, r+g]` is clean. -/
theorem iterateKilled_eq_none_iff (A : ℕ) :
    ∀ g r : ℕ, (iterateKilled A g r = none ↔ ∃ j, 1 ≤ j ∧ j ≤ g ∧ Clean A (r + j)) := by
  intro g
  induction g with
  | zero =>
    intro r
    constructor
    · intro h
      exact absurd h (by simp [iterateKilled])
    · rintro ⟨j, h1, h0, -⟩
      exfalso
      omega
  | succ g ih =>
    intro r
    by_cases hc : Clean A (r + 1)
    · constructor
      · intro _
        exact ⟨1, le_refl 1, by omega, hc⟩
      · intro _
        simp only [iterateKilled]
        rw [if_pos hc]
    · simp only [iterateKilled]
      rw [if_neg hc, ih (r + 1)]
      constructor
      · rintro ⟨j, h1, hg, hcl⟩
        exact ⟨j + 1, by omega, by omega,
          by rwa [show r + (j + 1) = r + 1 + j from by omega]⟩
      · rintro ⟨j, h1, hg, hcl⟩
        have hj2 : 2 ≤ j := by
          by_contra hlt
          have hj1 : j = 1 := by omega
          subst hj1
          exact hc hcl
        exact ⟨j - 1, by omega, by omega,
          by rwa [show r + 1 + (j - 1) = r + j from by omega]⟩

/-- **THE DISCLOSURE-IFF (costume #5 of the wall).**  The gap law `CleanGapBound A g` is
    EQUIVALENT to nilpotency of the killed shift at index `g`: `K^g = 0` on every state.
    The "spectral picture of the sieve" — no invariant vector, spectral radius zero, orbit
    extinction — is the twin-Jacobsthal wall wearing a dynamics costume.  Both directions are
    total over ℕ; no period hypothesis is needed at this altitude. -/
theorem cleanGapBound_iff_killed_nilpotent (A g : ℕ) :
    CleanGapBound A g ↔ ∀ r : ℕ, iterateKilled A g r = none := by
  constructor
  · intro h r
    rw [iterateKilled_eq_none_iff]
    obtain ⟨m, h1, h2, h3⟩ := h r
    exact ⟨m - r, by omega, by omega, by rwa [show r + (m - r) = m from by omega]⟩
  · intro h k
    obtain ⟨j, h1, h2, h3⟩ := (iterateKilled_eq_none_iff A g k).mp (h k)
    exact ⟨k + j, by omega, by omega, h3⟩

/-- **One period suffices**: killed-shift nilpotency checked on `r < P` extends to all of ℕ
    through clean periodicity (`clean_add_mul_period`) — the mod-`P` reduction lemma that
    turns a kernel certificate into the global law. -/
theorem killed_nilpotent_of_period {A g P : ℕ} (hP0 : 0 < P)
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P)
    (h : ∀ r < P, iterateKilled A g r = none) :
    ∀ r : ℕ, iterateKilled A g r = none := by
  intro r
  rw [iterateKilled_eq_none_iff]
  obtain ⟨j, h1, h2, h3⟩ :=
    (iterateKilled_eq_none_iff A g (r % P)).mp (h (r % P) (Nat.mod_lt r hP0))
  refine ⟨j, h1, h2, ?_⟩
  have hmod := Nat.mod_add_div r P
  have hdecomp : r + j = (r % P + j) + P * (r / P) := by omega
  rw [hdecomp]
  exact (clean_add_mul_period hdvd (by omega) (r / P)).mpr h3

/-! ### §2 Kernel certificates of nilpotency at the measured exact gaps -/

/-- Nilpotency index 2 at scale 5 over its period 5 (`K² = 0`). -/
theorem killed_nilpotent_5 : ∀ r < 5, iterateKilled 5 2 r = none := by decide

/-- Nilpotency index 5 at scale 7 over its period 35. -/
theorem killed_nilpotent_7 : ∀ r < 35, iterateKilled 7 5 r = none := by decide

set_option maxRecDepth 8000 in
/-- Nilpotency index 7 at scale 11 over its period 385. -/
theorem killed_nilpotent_11 : ∀ r < 385, iterateKilled 11 7 r = none := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- Nilpotency index 11 at scale 13 over its period 5005. -/
theorem killed_nilpotent_13 : ∀ r < 5005, iterateKilled 13 11 r = none := by decide

/-- Clock-divisibility helper (same shape as the wall's private helper): all active clocks
    divide `6P` once the clocks `≥ 5` divide `P`. -/
private theorem dvd_clocks {A P : ℕ} (h : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → q ∣ P) :
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

private theorem clocks_dvd_5 : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ 5 → q ∣ 5 := by
  intro q hq h5 hA
  have hq5 : q = 5 := by omega
  subst hq5
  rfl

private theorem clocks_dvd_7 : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ 7 → q ∣ 35 := by
  intro q hq h5 hA
  interval_cases q
  · exact ⟨7, rfl⟩
  · exact absurd hq (by norm_num)
  · exact ⟨5, rfl⟩

private theorem clocks_dvd_11 : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ 11 → q ∣ 385 := by
  intro q hq h5 hA
  interval_cases q
  · exact ⟨77, rfl⟩
  · exact absurd hq (by norm_num)
  · exact ⟨55, rfl⟩
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact ⟨35, rfl⟩

private theorem clocks_dvd_13 : ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ 13 → q ∣ 5005 := by
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

/-- **The closed loop at scale 5**: pure killed-shift nilpotency (one kernel period) plus the
    mod-`P` reduction rederives the wall's gap law through the disclosure-iff — the costume
    translates back without loss. -/
theorem cleanGapBound_via_killed_5 : CleanGapBound 5 2 :=
  (cleanGapBound_iff_killed_nilpotent 5 2).mpr
    (killed_nilpotent_of_period (by norm_num) (dvd_clocks clocks_dvd_5)
      (fun r hr => killed_nilpotent_5 r hr))

/-- The wall's laws, worn as global nilpotency (scale 5). -/
theorem killed_nilpotent_global_5 : ∀ r : ℕ, iterateKilled 5 2 r = none :=
  (cleanGapBound_iff_killed_nilpotent 5 2).mp cleanGapBound_5

/-- The wall's laws, worn as global nilpotency (scale 7). -/
theorem killed_nilpotent_global_7 : ∀ r : ℕ, iterateKilled 7 5 r = none :=
  (cleanGapBound_iff_killed_nilpotent 7 5).mp cleanGapBound_7

/-- The wall's laws, worn as global nilpotency (scale 11). -/
theorem killed_nilpotent_global_11 : ∀ r : ℕ, iterateKilled 11 7 r = none :=
  (cleanGapBound_iff_killed_nilpotent 11 7).mp cleanGapBound_11

/-- The wall's laws, worn as global nilpotency (scale 13). -/
theorem killed_nilpotent_global_13 : ∀ r : ℕ, iterateKilled 13 11 r = none :=
  (cleanGapBound_iff_killed_nilpotent 13 11).mp cleanGapBound_13

/-! ### §3 The energy of the killed shift: all singular values are 0 or 1 -/

/-- The reverse (adjoint) step `Kᵀ`: step back by one, absorb at clean centers — the exact
    transpose of the killed shift's 0/1 matrix. -/
def backStep (A s : ℕ) : Option ℕ :=
  if Clean A s then none else some (s - 1)

/-- **Energy law, forward**: `Kᵀ∘K` is the partial identity cut by the clean indicator of the
    TARGET — a 0/1 diagonal.  In matrix language `KᵀK = D_{1−s}`: every singular value of the
    killed shift (and of each of its window truncations) is 0 or 1. -/
theorem killed_energy_forward (A r : ℕ) :
    (killedStep A r).bind (backStep A) = if Clean A (r + 1) then none else some r := by
  by_cases hc : Clean A (r + 1) <;> simp [killedStep, backStep, hc]

/-- **Energy law, backward**: `K∘Kᵀ` is the partial identity cut by the clean indicator of the
    SOURCE (`s ≥ 1`; on ℕ the state 0 is an artifact — residue class 0 is represented by `P`).
    Together with `killed_energy_forward`: the spectra and pseudospectra of window-restricted
    transfer matrices are trivial — that observable class is a costume of the clean
    indicator. -/
theorem killed_energy_backward (A s : ℕ) (hs : 1 ≤ s) :
    (backStep A s).bind (killedStep A) = if Clean A s then none else some s := by
  have he : s - 1 + 1 = s := by omega
  by_cases hc : Clean A s
  · simp [backStep, hc]
  · simp [backStep, killedStep, hc, he]

/-! ### §4 The induced return map and Kac's identity -/

/-- The clean residues of one period, on the representative window `(0, P]` (residue class 0
    is represented by `P` itself: `Clean` is truncation-poisoned at 0, an ℕ artifact). -/
def cleanResidues (A P : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 P).filter (fun r => Clean A r)

/-- The first-return scan with fuel: `tauFuel A f r` walks `r+1, r+2, …` until it meets a
    clean center, for at most `f` steps (0 on fuel exhaustion — the spec lemmas below only
    ever run it with adequate fuel). -/
def tauFuel (A : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, r => if Clean A (r + 1) then 1 else tauFuel A f (r + 1) + 1

/-- A gap bound yields the window fact the scan needs, at every start. -/
theorem gapBound_window {A L : ℕ} (hgap : CleanGapBound A L) (r : ℕ) :
    ∃ j, 1 ≤ j ∧ j ≤ L ∧ Clean A (r + j) := by
  obtain ⟨m, h1, h2, h3⟩ := hgap r
  exact ⟨m - r, by omega, by omega, by rwa [show r + (m - r) = m from by omega]⟩

/-- **Correctness of the scan**: with a clean center inside the fuel window, `tauFuel` is a
    genuine first-return time — positive, fuel-bounded, landing clean, minimal. -/
theorem tauFuel_spec (A : ℕ) :
    ∀ f r : ℕ, (∃ j, 1 ≤ j ∧ j ≤ f ∧ Clean A (r + j)) →
      1 ≤ tauFuel A f r ∧ tauFuel A f r ≤ f ∧ Clean A (r + tauFuel A f r) ∧
        ∀ i, 1 ≤ i → i < tauFuel A f r → ¬ Clean A (r + i) := by
  intro f
  induction f with
  | zero =>
    rintro r ⟨j, h1, h0, -⟩
    exfalso
    omega
  | succ f ih =>
    rintro r ⟨j, hj1, hjf, hcl⟩
    by_cases hc : Clean A (r + 1)
    · have heq : tauFuel A (f + 1) r = 1 := by
        simp only [tauFuel]
        rw [if_pos hc]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [heq]
        exact hc
      · intro i hi1 hilt
        exfalso
        omega
    · have hj2 : 2 ≤ j := by
        by_contra hlt
        have hj1' : j = 1 := by omega
        subst hj1'
        exact hc hcl
      obtain ⟨ht1, htf, htcl, htmin⟩ := ih (r + 1)
        ⟨j - 1, by omega, by omega, by rwa [show r + 1 + (j - 1) = r + j from by omega]⟩
      have heq : tauFuel A (f + 1) r = tauFuel A f (r + 1) + 1 := by
        simp only [tauFuel]
        rw [if_neg hc]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [heq, show r + (tauFuel A f (r + 1) + 1) = r + 1 + tauFuel A f (r + 1) from by omega]
        exact htcl
      · intro i hi1 hilt
        rw [heq] at hilt
        rcases Nat.eq_or_lt_of_le hi1 with h | h
        · rw [← h]
          exact hc
        · have := htmin (i - 1) (by omega) (by omega)
          rwa [show r + 1 + (i - 1) = r + i from by omega] at this

/-- The first-return time is the UNIQUE positive minimal clean landing — the uniqueness
    handle used to move the scan across steps and periods. -/
theorem tauFuel_unique (A f r j : ℕ)
    (hex : ∃ i, 1 ≤ i ∧ i ≤ f ∧ Clean A (r + i))
    (hj1 : 1 ≤ j) (hcl : Clean A (r + j))
    (hmin : ∀ i, 1 ≤ i → i < j → ¬ Clean A (r + i)) :
    tauFuel A f r = j := by
  obtain ⟨ht1, htf, htcl, htmin⟩ := tauFuel_spec A f r hex
  rcases Nat.lt_trichotomy (tauFuel A f r) j with h | h | h
  · exact absurd htcl (hmin _ ht1 h)
  · exact h
  · exact absurd hcl (htmin _ hj1 h)

/-- Under the gap bound, a clean successor forces return time 1. -/
theorem tauFuel_eq_one_of_clean {A F r : ℕ} (hF : 0 < F) (hc : Clean A (r + 1)) :
    tauFuel A F r = 1 := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
  simp only [tauFuel]
  rw [if_pos hc]

/-- Under the gap bound, an unclean successor shifts the return time by exactly one — the
    cocycle step of the telescoping identity. -/
theorem tauFuel_succ_of_not_clean {A F r : ℕ} (hgap : CleanGapBound A F)
    (hc : ¬ Clean A (r + 1)) :
    tauFuel A F r = tauFuel A F (r + 1) + 1 := by
  obtain ⟨ht1, htf, htcl, htmin⟩ := tauFuel_spec A F (r + 1) (gapBound_window hgap (r + 1))
  apply tauFuel_unique A F r (tauFuel A F (r + 1) + 1) (gapBound_window hgap r) (by omega)
  · rwa [show r + (tauFuel A F (r + 1) + 1) = r + 1 + tauFuel A F (r + 1) from by omega]
  · intro i hi1 hilt
    rcases Nat.eq_or_lt_of_le hi1 with h | h
    · rw [← h]
      exact hc
    · have := htmin (i - 1) (by omega) (by omega)
      rwa [show r + 1 + (i - 1) = r + i from by omega] at this

/-- **The telescoping master identity**: over any window `(x, x+n]` the return times of the
    clean centers sum to the window length, corrected by the two boundary anchors
    `N(y) = y + τ(y)` (next-clean-after).  Induction on the window length; the two step laws
    above are exactly the two cases. -/
theorem kac_master {A F : ℕ} (hgap : CleanGapBound A F) :
    ∀ n x : ℕ,
      ((Finset.Ioc x (x + n)).filter (fun r => Clean A r)).sum (tauFuel A F)
          + tauFuel A F x = n + tauFuel A F (x + n) := by
  have hF : 0 < F := by
    obtain ⟨m, h1, h2, -⟩ := hgap 0
    omega
  intro n
  induction n with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    have hins : Finset.Ioc x (x + (n + 1)) = insert (x + n + 1) (Finset.Ioc x (x + n)) := by
      ext y
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hins, Finset.filter_insert, show x + (n + 1) = x + n + 1 from by omega]
    by_cases hc : Clean A (x + n + 1)
    · have hnm : x + n + 1 ∉ (Finset.Ioc x (x + n)).filter (fun r => Clean A r) := by
        intro hmem
        rw [Finset.mem_filter, Finset.mem_Ioc] at hmem
        obtain ⟨⟨-, h2⟩, -⟩ := hmem
        omega
      rw [if_pos hc, Finset.sum_insert hnm]
      have h1 : tauFuel A F (x + n) = 1 := tauFuel_eq_one_of_clean hF hc
      -- eta-expanded binder form so the sum atom matches the goal after `sum_insert`
      have hIH : (∑ r ∈ (Finset.Ioc x (x + n)).filter (fun r => Clean A r), tauFuel A F r)
          + tauFuel A F x = n + tauFuel A F (x + n) := ih x
      omega
    · rw [if_neg hc]
      have hstep : tauFuel A F (x + n) = tauFuel A F (x + n + 1) + 1 :=
        tauFuel_succ_of_not_clean hgap hc
      have hIH := ih x
      omega

/-- The scan is `P`-periodic at the period anchor: the return time from `P` (the
    representative of residue 0) equals the return time from 0. -/
theorem tauFuel_period_zero {A F P : ℕ} (hgap : CleanGapBound A F)
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P) :
    tauFuel A F P = tauFuel A F 0 := by
  obtain ⟨ht1, htF, htcl, htmin⟩ := tauFuel_spec A F 0 (gapBound_window hgap 0)
  have htcl' : Clean A (tauFuel A F 0) := by
    rwa [Nat.zero_add] at htcl
  apply tauFuel_unique A F P (tauFuel A F 0) (gapBound_window hgap P) ht1
  · have h := (clean_add_mul_period hdvd ht1 1).mpr htcl'
    rwa [show tauFuel A F 0 + P * 1 = P + tauFuel A F 0 from by omega] at h
  · intro i hi1 hilt
    have hni : ¬ Clean A i := by
      have := htmin i hi1 hilt
      rwa [Nat.zero_add] at this
    intro hcl
    exact hni ((clean_add_mul_period hdvd hi1 1).mp
      (by rwa [show i + P * 1 = P + i from by omega]))

/-- **KAC'S RETURN IDENTITY (general, green).**  The first-return times of the induced map on
    clean residues tile the period EXACTLY: `∑_{r ∈ cleanResidues A P} τ(r) = P`.  This is the
    genuinely new exact asset of the transfer picture — the mean-gap dual of the window
    identity: the mean return time is `P / #cleanResidues = ∏_{5 ≤ q ≤ A} q/(q−2)`, the
    Hardy–Littlewood local product, while the wall (`CleanGapBound`) bounds the max.
    Hypotheses: any fuel `F` with the gap bound, any period `P` divisible by all clocks. -/
theorem kac_return_identity {A F P : ℕ} (hgap : CleanGapBound A F)
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P) :
    (cleanResidues A P).sum (tauFuel A F) = P := by
  have hm := kac_master hgap P 0
  simp only [Nat.zero_add] at hm
  have hper : tauFuel A F P = tauFuel A F 0 := tauFuel_period_zero hgap hdvd
  -- re-ascribe through `cleanResidues` (defeq) so the sum atom matches the goal
  have hm' : (cleanResidues A P).sum (tauFuel A F) + tauFuel A F 0
      = P + tauFuel A F P := hm
  omega

/-- **The max side pinned to the wall**: under `CleanGapBound A g` every return time is at
    most `g` (any start, not only clean ones) — max τ ≤ G(A) exactly, no off-by-one. -/
theorem max_return_le_of_cleanGapBound {A F g : ℕ} (hgap : CleanGapBound A g)
    (hgF : g ≤ F) (r : ℕ) : tauFuel A F r ≤ g := by
  obtain ⟨j, hj1, hjg, hcl⟩ := gapBound_window hgap r
  obtain ⟨ht1, htF, htcl, htmin⟩ := tauFuel_spec A F r ⟨j, hj1, by omega, hcl⟩
  by_contra hgt
  exact htmin j hj1 (by omega) hcl

/-- **Max-vs-mean, exact form**: Kac + the max bound give `P ≤ #cleanResidues · g` — the
    period is covered by `#cleanResidues` return blocks of length ≤ `g`.  Equivalently the
    MEAN return time `P / #cleanResidues = ∏ q/(q−2)` is at most the wall's max `g`: the gap
    law is a max-vs-mean statement, and the mean side is exactly the Hardy–Littlewood local
    factor (kernel census below: `#cleanResidues = ∏ (q−2)`). -/
theorem mean_gap_exact {A g P : ℕ} (hgap : CleanGapBound A g)
    (hdvd : ∀ q : ℕ, q.Prime → q ≤ A → q ∣ 6 * P) :
    P ≤ (cleanResidues A P).card * g := by
  have hkac := kac_return_identity hgap hdvd
  have hbound : (cleanResidues A P).sum (tauFuel A g) ≤ (cleanResidues A P).card • g :=
    Finset.sum_le_card_nsmul _ _ _ (fun x _ => max_return_le_of_cleanGapBound hgap le_rfl x)
  rw [smul_eq_mul] at hbound
  omega

/-! ### §5 Kac instances at the certified scales (derived, not decided) -/

/-- Kac at scale 5: the 3 clean residues' return times tile the period 5. -/
theorem kac_return_5 : (cleanResidues 5 5).sum (tauFuel 5 2) = 5 :=
  kac_return_identity cleanGapBound_5 (dvd_clocks clocks_dvd_5)

/-- Kac at scale 7: the 15 clean residues tile the period 35. -/
theorem kac_return_7 : (cleanResidues 7 35).sum (tauFuel 7 5) = 35 :=
  kac_return_identity cleanGapBound_7 (dvd_clocks clocks_dvd_7)

/-- Kac at scale 11: the 135 clean residues tile the period 385. -/
theorem kac_return_11 : (cleanResidues 11 385).sum (tauFuel 11 7) = 385 :=
  kac_return_identity cleanGapBound_11 (dvd_clocks clocks_dvd_11)

/-- Kac at scale 13: the 1485 clean residues tile the period 5005. -/
theorem kac_return_13 : (cleanResidues 13 5005).sum (tauFuel 13 11) = 5005 :=
  kac_return_identity cleanGapBound_13 (dvd_clocks clocks_dvd_13)

/-- Kernel cross-check of Kac at scale 5 (independent of the general proof). -/
theorem kac_return_kernel_5 : (cleanResidues 5 5).sum (tauFuel 5 2) = 5 := by decide

/-- Kernel cross-check of Kac at scale 7. -/
theorem kac_return_kernel_7 : (cleanResidues 7 35).sum (tauFuel 7 5) = 35 := by decide

/-! ### §6 Kernel census: the clean-residue counts are the local product `∏ (q−2)` -/

/-- `#cleanResidues(5) = 3 = 5−2` — the local factor of `admissible_card` at the single
    clock 5. -/
theorem card_cleanResidues_5 : (cleanResidues 5 5).card = 3 := by decide

/-- `#cleanResidues(7) = 15 = 3·5`. -/
theorem card_cleanResidues_7 : (cleanResidues 7 35).card = 15 := by decide

set_option maxRecDepth 8000 in
/-- `#cleanResidues(11) = 135 = 3·5·9`. -/
theorem card_cleanResidues_11 : (cleanResidues 11 385).card = 135 := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 8000000 in
/-- `#cleanResidues(13) = 1485 = 3·5·9·11` — mean return time `5005/1485 = ∏ q/(q−2)`. -/
theorem card_cleanResidues_13 : (cleanResidues 13 5005).card = 1485 := by decide

end TransferCostume
end EuclidsPath

/-
  ### Machine honesty (recorded `#print axioms` output)

  Checked against the elaborated module (scratch run with `lake env lean`, scratch deleted);
  every declaration of this file sits under the standard axioms only — no `sorry`,
  no `step00FirstCause`, no `native_decide` (`Lean.ofReduceBool`):

  * `iterateKilled_succ_bind` / `iterateKilled_eq_none_iff` — [propext, Classical.choice, Quot.sound]
  * `cleanGapBound_iff_killed_nilpotent`                    — [propext, Classical.choice, Quot.sound]
  * `killed_nilpotent_of_period`                            — [propext, Classical.choice, Quot.sound]
  * `killed_nilpotent_5` / `_7` / `_11` / `_13`             — [propext] (kernel decide)
  * `cleanGapBound_via_killed_5` / `killed_nilpotent_global_{5,7,11,13}`
                                                            — [propext, Classical.choice, Quot.sound]
  * `killed_energy_forward` / `killed_energy_backward`      — [propext, Classical.choice, Quot.sound]
  * `tauFuel_spec` / `tauFuel_unique` / `kac_master`        — [propext, Classical.choice, Quot.sound]
  * `kac_return_identity` / `mean_gap_exact`                — [propext, Classical.choice, Quot.sound]
  * `kac_return_{5,7,11,13}` / `kac_return_kernel_{5,7}`    — [propext, Classical.choice, Quot.sound]
  * `card_cleanResidues_{5,7,11,13}`                        — [propext] (kernel decide)
-/
