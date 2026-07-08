import Mathlib
import EuclidsPath.Engine.Residuals
import EuclidsPath.Engine.OldPeel

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Genealogical forest — the descent sinks are EXACTLY the twins (green scaffold)

The genealogical tree, made precise.  The old-peel descent sends a center `m` whose side `6m ∓ 1` is
composite to the center `t` of the cofactor side, and does so strictly downhill (`t < m`, reusing
`OldPeel.old_peel_height_drop`).  A center with NOTHING to peel — a descent *root* / sink — is exactly
a center both of whose sides are prime, i.e. a twin.  Hence every center descends in finitely many
steps to a twin BELOW it, and the centers partition into twin basins.

## Green here (no `sorry`, no new axiom)

  * `PeelStep m t` — one old-peel step `6m − ε = p · (6t + δ)`, `p` prime `≥ 5`, `δ = ±1`, `t ≥ 1`;
  * `peelStep_lt` — a peel is strictly downhill (reuses `OldPeel.old_peel_height_drop`);
  * `not_peel_of_twin` — a twin is a root: both sides prime ⟹ no composite side ⟹ no peel;
  * `peel_of_not_twin` — a non-twin peels: a composite side factors as `p · (6t ± 1)` (totality);
  * `root_iff_twin` — **the descent sinks are EXACTLY the twins**;
  * `descent_reaches_root` / `descent_reaches_twin` — every center `m ≥ 1` descends (well-founded) to a
    root, i.e. to a twin `≤ m`.

## Honest reading (why this does NOT prove infinitude)

The descent flows DOWNHILL: a peel's target is strictly smaller.  So `descent_reaches_twin` only ever
certifies a twin **at or below** `m` — never above.  Twin infinitude is a statement about twins above
every bound; a finite set of twins can root an infinite forest (bottomless basins — a low twin absorbs
arbitrarily high centers).  So this brick maps the genealogical tree faithfully but does not multiply
its roots.  `twin_prime_conjecture` stays `sorry`.
-/

namespace EuclidsPath.Genealogy

open EuclidsPath.Residuals

/-- One old-peel descent step from center `m` to center `t`: a side `6m − ε` (`ε = ±1`) is composite,
    factoring as `p · (6t + δ)` with a prime `p ≥ 5`, `δ = ±1`, and `t ≥ 1`. -/
def PeelStep (m t : ℕ) : Prop :=
  ∃ ε δ : ℤ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ 1 ≤ t ∧
      6 * (m : ℤ) - ε = (p : ℤ) * (6 * (t : ℤ) + δ)

/-- A center is a **root** (descent sink) when no peel step leaves it. -/
def IsRoot (m : ℕ) : Prop := ¬ ∃ t : ℕ, PeelStep m t

/-- **Green — a peel goes strictly downhill.**  Reuses `OldPeel.old_peel_height_drop`. -/
theorem peelStep_lt {m t : ℕ} (hm : 2 ≤ m) (h : PeelStep m t) : t < m := by
  obtain ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩ := h
  have : (t : ℤ) < (m : ℤ) :=
    EuclidsPath.OldPeel.old_peel_height_drop hε hδ (by exact_mod_cast hp5)
      (by exact_mod_cast ht1) (by exact_mod_cast hm) heq
  exact_mod_cast this

/-! ### Totality: a composite side always peels -/

/-- A number coprime to 6, `≥ 5` and composite, factors as `p · s` with a prime `p ≥ 5`, cofactor
    `s ≥ 5`, and `s ≡ ±1 (mod 6)` (so `s` is again a side of some center). -/
private theorem factor_coprime6 {S : ℕ} (hS5 : 5 ≤ S) (hSc : ¬ S.Prime)
    (h2 : ¬ 2 ∣ S) (h3 : ¬ 3 ∣ S) :
    ∃ p s : ℕ, p.Prime ∧ 5 ≤ p ∧ 5 ≤ s ∧ p * s = S ∧ (s % 6 = 1 ∨ s % 6 = 5) := by
  have hp : S.minFac.Prime := Nat.minFac_prime (by omega)
  have hpd : S.minFac ∣ S := Nat.minFac_dvd S
  set p := S.minFac with hpe
  have hp2 : p ≠ 2 := fun h => h2 (h ▸ hpd)
  have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpd)
  have hp4 : p ≠ 4 := fun h => (show ¬ Nat.Prime 4 by decide) (h ▸ hp)
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  obtain ⟨s, hs⟩ := hpd
  have h2s : ¬ 2 ∣ s := fun h => h2 (hs ▸ Dvd.dvd.mul_left h p)
  have h3s : ¬ 3 ∣ s := fun h => h3 (hs ▸ Dvd.dvd.mul_left h p)
  have hs0 : s ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hs; omega
  have hs1 : s ≠ 1 := by
    rintro rfl; rw [Nat.mul_one] at hs; exact hSc (by rw [hs]; exact hp)
  refine ⟨p, s, hp, hp5, by omega, hs.symm, by omega⟩

/-- **Totality (the real work): a non-twin center peels.**  If a side `6m − ε` is composite it
    factors as `p · (6t + δ)`, giving a peel step `m → t`. -/
private theorem peel_of_composite_side {m : ℕ} (hm : 1 ≤ m) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    {S : ℕ} (hSeq : (S : ℤ) = 6 * (m : ℤ) - ε) (hS5 : 5 ≤ S) (hSc : ¬ S.Prime) :
    ∃ t : ℕ, PeelStep m t := by
  have h2 : ¬ 2 ∣ S := by rcases hε with rfl | rfl <;> omega
  have h3 : ¬ 3 ∣ S := by rcases hε with rfl | rfl <;> omega
  obtain ⟨p, s, hp, hp5, hs5, hps, hs6⟩ := factor_coprime6 hS5 hSc h2 h3
  rcases hs6 with h1 | h5
  · refine ⟨(s - 1) / 6, ε, 1, hε, Or.inl rfl, p, hp, hp5, by omega, ?_⟩
    have hst : (s : ℤ) = 6 * (((s - 1) / 6 : ℕ) : ℤ) + 1 := by
      have h6 : 6 * ((s - 1) / 6) + 1 = s := by omega
      omega
    calc 6 * (m : ℤ) - ε = (S : ℤ) := hSeq.symm
      _ = (p : ℤ) * (s : ℤ) := by exact_mod_cast hps.symm
      _ = (p : ℤ) * (6 * (((s - 1) / 6 : ℕ) : ℤ) + 1) := by rw [hst]
  · refine ⟨(s + 1) / 6, ε, -1, hε, Or.inr rfl, p, hp, hp5, by omega, ?_⟩
    have hst : (s : ℤ) = 6 * (((s + 1) / 6 : ℕ) : ℤ) - 1 := by
      have h6 : 6 * ((s + 1) / 6) = s + 1 := by omega
      omega
    calc 6 * (m : ℤ) - ε = (S : ℤ) := hSeq.symm
      _ = (p : ℤ) * (s : ℤ) := by exact_mod_cast hps.symm
      _ = (p : ℤ) * (6 * (((s + 1) / 6 : ℕ) : ℤ) - 1) := by rw [hst]

/-- **A non-twin center peels.** -/
theorem peel_of_not_twin {m : ℕ} (hm : 1 ≤ m) (hnt : ¬ TwinCenterZ m) :
    ∃ t : ℕ, PeelStep m t := by
  simp only [TwinCenterZ, not_and_or] at hnt
  rcases hnt with h | h
  · exact peel_of_composite_side hm 1 (Or.inl rfl) (S := 6 * m - 1) (by omega) (by omega) h
  · exact peel_of_composite_side hm (-1) (Or.inr rfl) (S := 6 * m + 1) (by omega) (by omega) h

/-- **A twin center is a root: it has no peel.**  Both sides prime ⟹ no composite side. -/
theorem not_peel_of_twin {m : ℕ} (hm : 1 ≤ m) (ht : TwinCenterZ m) : IsRoot m := by
  rintro ⟨t, ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩
  have htz : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht1
  have hu : (5 : ℤ) ≤ 6 * (t : ℤ) + δ := by rcases hδ with rfl | rfl <;> omega
  have hpdvdZ : (p : ℤ) ∣ (6 * (m : ℤ) - ε) := ⟨6 * (t : ℤ) + δ, heq⟩
  rcases hε with rfl | rfl
  · have hcast : (6 * (m : ℤ) - 1) = ((6 * m - 1 : ℕ) : ℤ) := by omega
    rw [hcast] at hpdvdZ
    have hpd : p ∣ (6 * m - 1) := by exact_mod_cast hpdvdZ
    rcases ht.1.eq_one_or_self_of_dvd p hpd with h1 | hself
    · omega
    · have hpz : (p : ℤ) = 6 * (m : ℤ) - 1 := by rw [hself]; omega
      rw [hpz] at heq
      have hne : (6 * (m : ℤ) - 1) ≠ 0 := by omega
      have e : (6 * (m : ℤ) - 1) * 1 = (6 * (m : ℤ) - 1) * (6 * (t : ℤ) + δ) := by
        rw [mul_one]; exact heq
      have := mul_left_cancel₀ hne e
      omega
  · have hcast : (6 * (m : ℤ) - -1) = ((6 * m + 1 : ℕ) : ℤ) := by omega
    rw [hcast] at hpdvdZ
    have hpd : p ∣ (6 * m + 1) := by exact_mod_cast hpdvdZ
    rcases ht.2.eq_one_or_self_of_dvd p hpd with h1 | hself
    · omega
    · have hpz : (p : ℤ) = 6 * (m : ℤ) + 1 := by rw [hself]; omega
      rw [show (6 * (m : ℤ) - -1) = 6 * (m : ℤ) + 1 from by ring] at heq
      rw [hpz] at heq
      have hne : (6 * (m : ℤ) + 1) ≠ 0 := by omega
      have e : (6 * (m : ℤ) + 1) * 1 = (6 * (m : ℤ) + 1) * (6 * (t : ℤ) + δ) := by
        rw [mul_one]; exact heq
      have := mul_left_cancel₀ hne e
      omega

/-- **`root_iff_twin`: the descent sinks are EXACTLY the twins.** -/
theorem root_iff_twin {m : ℕ} (hm : 1 ≤ m) : IsRoot m ↔ TwinCenterZ m := by
  constructor
  · intro hroot
    by_contra hnt
    exact hroot (peel_of_not_twin hm hnt)
  · intro htwin
    exact not_peel_of_twin hm htwin

/-- **`descent_reaches_root`: every center `m ≥ 1` descends (well-founded) to a root `≤ m`.** -/
theorem descent_reaches_root : ∀ m : ℕ, 1 ≤ m → ∃ t : ℕ, t ≤ m ∧ 1 ≤ t ∧ IsRoot t := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases htw : TwinCenterZ m
    · exact ⟨m, le_refl m, hm, not_peel_of_twin hm htw⟩
    · obtain ⟨t, hpeel⟩ := peel_of_not_twin hm htw
      obtain ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩ := hpeel
      have hm2 : 2 ≤ m := by
        by_contra hlt
        have hm1 : m = 1 := by omega
        rw [hm1] at htw
        exact htw (by norm_num [TwinCenterZ])
      have hlt : t < m := peelStep_lt hm2 ⟨ε, δ, hε, hδ, p, hp, hp5, ht1, heq⟩
      obtain ⟨t', hle', h1', hroot'⟩ := ih t hlt ht1
      exact ⟨t', by omega, h1', hroot'⟩

/-- **`descent_reaches_twin`: every center `m ≥ 1` descends to a twin `≤ m`.**  The forest is rooted at
    twins.  Honest: the twin is at or below `m` (the descent goes down); this does NOT reach a twin
    above any bound, so it does not prove infinitude. -/
theorem descent_reaches_twin (m : ℕ) (hm : 1 ≤ m) :
    ∃ t : ℕ, t ≤ m ∧ 1 ≤ t ∧ TwinCenterZ t := by
  obtain ⟨t, hle, h1, hroot⟩ := descent_reaches_root m hm
  exact ⟨t, hle, h1, (root_iff_twin h1).mp hroot⟩

end EuclidsPath.Genealogy
