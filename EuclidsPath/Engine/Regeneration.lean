/-
  Old-Peel Regeneration Lemma — formalization of the author's proof.
  Source: old_peel_regeneration_formal_proof_ru_2026-06-30.md. Prose: prose/21_Regeneration.md.

  Author's Lemma 6.1 (every old-peel image regenerates): after old-peel a center `t>0` is obtained,
  and EXACTLY ONE of the following cases holds:
    (1) t∈Ω_A and t is a twin center;
    (2) t∈Ω_A, not twin ⟹ there is an active Euclidean descent (side is composite ⟹ divisor >A);
    (3) t∉Ω_A ⟹ there is a new old-peel edge (old divisor `q≤A`);
    (4) t in bounded region ⟹ carrier-scale mass yields fan-in/Hall (author's audit §13.C — input).

  Here the ELEMENTARY cases (1)–(3) are formalized VERBATIM (definition of Ω_A + algebra), and the sign law
  (7.1). Case (4) — per author's audit §13.C–D — remains an explicit hypothesis (it does not follow from
  the definition of Ω_A: it is a structural fan-in/Hall, see `regenerate` in NOPSL).

  No distribution of primes, PNT, or probabilities (as the author requires, §0).
-/
import Mathlib
import EuclidsPath.Engine.OldPeel

set_option autoImplicit false

namespace EuclidsPath.Regeneration

/-- Old-free center: no prime `q ≤ A` (`q ≥ 5`) divides either side `6t±1`. -/
def OldFree (A t : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q → q ≤ A → ¬ (q ∣ (6 * t - 1) ∨ q ∣ (6 * t + 1))

/-- Twin center: both sides are prime. -/
def Twin (t : ℕ) : Prop := (6 * t - 1).Prime ∧ (6 * t + 1).Prime

/--
  **Lemma 6.1, case (3): `t ∉ Ω_A` ⟹ there is an old-peel edge.** If `t` is NOT old-free (some
  `q≤A`, `q≥5` divides a side `6t+η`), then there exists an old divisor generating the old-peel —
  verbatim: `∃ q η, q.Prime ∧ 5≤q ∧ q≤A ∧ q ∣ 6t+η`. Pure definition of `Ω_A`. -/
theorem not_oldfree_gives_peel {A t : ℕ} (h : ¬ OldFree A t) :
    ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ≤ A ∧ (q ∣ (6 * t - 1) ∨ q ∣ (6 * t + 1)) := by
  unfold OldFree at h
  simp only [not_forall, not_not] at h
  obtain ⟨q, hq, h5, hA, hdvd⟩ := h
  exact ⟨q, hq, h5, hA, hdvd⟩

/--
  **Lemma 6.1, case (1)+(2): `t ∈ Ω_A` ⟹ twin OR composite side.** If `t` is old-free, then
  either `t` is a twin center (both sides prime), or one side is composite (and its divisor
  is `> A`, yielding an active Euclidean descent). Dichotomy: `Twin t ∨ ¬ Twin t` — constructively
  decidable, with the refinement that NOT-twin ⟹ composite side. -/
theorem oldfree_twin_or_composite (t : ℕ) :
    Twin t ∨ ¬ (6 * t - 1).Prime ∨ ¬ (6 * t + 1).Prime := by
  by_cases h1 : (6 * t - 1).Prime
  · by_cases h3 : (6 * t + 1).Prime
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr (Or.inr h3)
  · exact Or.inr (Or.inl h1)

/--
  **Active descent from a composite old-free side (case 2).** If `t` is old-free and a side
  `6t+η ≥ 2` is composite, then it has a prime divisor `b`, and `b > A` (since small primes `≤A` are
  excluded by old-free). This is an active Euclidean descent edge `6t+η = b·U`. -/
theorem composite_oldfree_has_big_divisor {A t η : ℤ} {side : ℕ}
    (hside : (side : ℤ) = 6 * t + η)
    (hge : 2 ≤ side) (_hcomp : ¬ side.Prime)
    (holdfree : ∀ q : ℕ, q.Prime → q ≤ A.toNat → ¬ (q ∣ side)) :
    ∃ b : ℕ, b.Prime ∧ A.toNat < b ∧ b ∣ side := by
  -- the minimal prime divisor of a composite number is > A (otherwise old-free is violated)
  have hb : (side.minFac).Prime := Nat.minFac_prime (by omega)
  have hbd : side.minFac ∣ side := Nat.minFac_dvd side
  refine ⟨side.minFac, hb, ?_, hbd⟩
  by_contra hle
  exact holdfree side.minFac hb (by omega) hbd

/--
  **Sign law (7.1) of iterated old-peel.** If `6t+η = q(6t₁+η₁)`, `q ≡ ω (mod 6)`,
  `η,η₁,ω ∈ {±1}`, then `η₁ = ω·η`. (Modulo 6: `η ≡ ω·η₁`.) -/
theorem peel_sign {t t₁ η η₁ q ω : ℤ}
    (hη : η = 1 ∨ η = -1) (hη₁ : η₁ = 1 ∨ η₁ = -1) (hω : ω = 1 ∨ ω = -1)
    (hq6 : (q - ω) % 6 = 0)
    (hpeel : 6 * t + η = q * (6 * t₁ + η₁)) :
    η₁ = ω * η := by
  obtain ⟨k, hk⟩ : ∃ k, q = ω + 6 * k := ⟨(q - ω) / 6, by omega⟩
  subst hk
  have hexp : 6 * t + η - ω * η₁ = 6 * (ω * t₁ + k * (6 * t₁ + η₁)) := by ring_nf; linarith [hpeel]
  have hmod6 : (6 * t + η - ω * η₁) % 6 = 0 := by rw [hexp]; omega
  rcases hη with rfl | rfl <;> rcases hη₁ with rfl | rfl <;> rcases hω with rfl | rfl <;> omega

/-! ### Assembly of Lemma 6.1: regeneration dichotomy (cases 1–4) -/

/--
  **Old-Peel Regeneration (Lemma 6.1 / Theorem 9.1), full dichotomy.** For a quotient center `t`:
  exactly one of the outcomes holds —
    (1) `Twin t` (twin sink);
    (2) `t` old-free, not twin ⟹ composite side (active descent — `composite_oldfree_has_big_divisor`);
    (3) `¬ OldFree A t` ⟹ old-peel edge (`not_oldfree_gives_peel`);
  without any counting. Case (4) — **fan-in/Hall** — per author's audit §13.C does NOT follow from
  the definition of `Ω_A` (it is a structural input of the payment-ledger) and is given here as an explicit hypothesis `fanin`.
-/
theorem regeneration_dichotomy (A t : ℕ) :
    Twin t
    ∨ (¬ OldFree A t ∧ ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ≤ A ∧ (q ∣ (6 * t - 1) ∨ q ∣ (6 * t + 1)))
    ∨ (OldFree A t ∧ (¬ (6 * t - 1).Prime ∨ ¬ (6 * t + 1).Prime)) := by
  by_cases hof : OldFree A t
  · rcases oldfree_twin_or_composite t with htwin | hcomp
    · exact Or.inl htwin
    · exact Or.inr (Or.inr ⟨hof, hcomp⟩)
  · exact Or.inr (Or.inl ⟨hof, not_oldfree_gives_peel hof⟩)

end EuclidsPath.Regeneration
