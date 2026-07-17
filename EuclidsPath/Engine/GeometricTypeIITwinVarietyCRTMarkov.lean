/-
  GeometricTypeIITwinVarietyCRTMarkov — THE EXCEPTIONAL FREQUENCY SET LEAVES
  THE PRIME LINE: the a-averaged fourth moment of the unit twin family
  FACTORS through CRT, and the Markov count of bad wing-frequency pairs holds
  at EVERY modulus — instantiated at semiprimes with explicit constants.

  ORIGIN.  Autonomous continuation (wave 5b of the Two-Axes program): the
  named follow-up of wave 5a — "twinVU-Markov at semiprime moduli".  Design
  adversarially verified (numerical pre-pass, this session): the moment
  factorization checked at (5,7) over ALL 1225 frequency pairs (worst
  relative error 2.0e−15); M4U(35) = 28 940 625 matches the closed form
  exactly; the constant-4 envelope has 7.3× slack at (5,7).

  THE THREE MOVES:
    * `twinVU_moment_crt_factor` — **THE MOMENT FACTORIZATION**: for coprime
      q₁, q₂ and ANY frequency pair (b₁,b₂) mod q₁q₂,
        Σ_a ‖V_{q₁q₂}(a,b₁,b₂)‖⁴
          = Σ_{a₁}‖V_{q₁}(a₁, u₁b₁, u₁b₂)‖⁴ · Σ_{a₂}‖V_{q₂}(a₂, u₂b₁, u₂b₂)‖⁴
      (cocycle-twisted component frequencies; the a-slot twist is absorbed by
      a unit bijection).  The a-averaged moment at a composite modulus is
      EXACTLY the product of component moments — so a frequency pair is
      exceptional mod q₁q₂ iff its twisted components are jointly exceptional.
    * `twinVU_markov_general` — Markov at EVERY modulus: for K > 0 the pairs
      (b₁,b₂) with Σ_a ‖V‖⁴ ≥ K·q³ number at most N4U(q)/K.
    * `twinVU_markov_semiprime` — the semiprime instantiation with the wave-5a
      closed form: at q = ℓ₁ℓ₂ the count is ≤ 4q²/K (the prime-line constant
      2 doubles once, once per prime factor envelope (ℓ−2)(2ℓ−5) ≤ 2ℓ²).

  WHAT IS PROVED (std axioms, no sorry, no new axioms): the three theorems
  above plus `twinVU_family_M4_semiprime_le` (M4U(ℓ₁ℓ₂) ≤ 4(ℓ₁ℓ₂)⁵).

  DISCLOSURES.
    * Complete sums over full boxes, unsigned — infrastructure on the
      composite-modulus core.  The SHORT-WINDOW transfer at composite modulus
      is NOT ported here: the completion engine
      (`GeometricTypeIICompletion`) is stated on the prime line, and its
      composite port is separate (named, unclaimed) work.  Faces C/E (short
      windows, incommensurable moduli, μ-signed aggregation) are UNTOUCHED.
    * As on the prime line, NO pointwise extraction exists for this family —
      the averaged Markov count is the entire cash value.
    * NOT a §110 event: no registered target moved.
    * The twin sorry (`twin_prime_conjecture`) is untouched.
-/
import Mathlib
import EuclidsPath.Engine.GeometricTypeIITwinVarietyCRT

set_option maxHeartbeats 1600000

namespace EuclidsPath
namespace Geometric
namespace TypeII

open scoped BigOperators

/-! ### Layer 1: the unit rescaling of the `a`-slot -/

/-- Rescaling the averaged variable by a unit leaves the moment invariant. -/
private theorem sum_moment_unit_rescale {q : ℕ} [NeZero q] {u : ZMod q}
    (hu : IsUnit u) (B₁ B₂ : ZMod q) :
    ∑ a : ZMod q, ‖twinVU q (u * a) B₁ B₂‖ ^ 4
      = ∑ a : ZMod q, ‖twinVU q a B₁ B₂‖ ^ 4 := by
  refine Fintype.sum_bijective (fun a : ZMod q => u * a) ?_ _ _ (fun a => rfl)
  constructor
  · intro a b hab
    exact hu.mul_left_cancel hab
  · intro b
    refine ⟨u⁻¹ * b, ?_⟩
    show u * (u⁻¹ * b) = b
    rw [← mul_assoc, ZMod.mul_inv_of_unit u hu, one_mul]

/-! ### Layer 2: THE MOMENT FACTORIZATION -/

/-- **The a-averaged fourth moment factors through CRT**: for coprime moduli
and ANY frequency pair, the composite moment is the product of the component
moments at the cocycle-twisted component frequencies.  (Numerically verified
at (5,7) over all 1225 pairs, worst relative error 2.0e−15.) -/
theorem twinVU_moment_crt_factor {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hco : Nat.Coprime q₁ q₂) (b₁ b₂ : ZMod (q₁ * q₂)) :
    ∑ a : ZMod (q₁ * q₂), ‖twinVU (q₁ * q₂) a b₁ b₂‖ ^ 4
      = (∑ a₁ : ZMod q₁, ‖twinVU q₁ a₁
            ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₁)
            ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₂)‖ ^ 4)
        * (∑ a₂ : ZMod q₂, ‖twinVU q₂ a₂
            ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₁)
            ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₂)‖ ^ 4) := by
  classical
  -- the cocycle units ARE units
  have hq₂u : IsUnit ((q₂ : ℕ) : ZMod q₁) :=
    (ZMod.isUnit_iff_coprime q₂ q₁).mpr hco.symm
  have hq₁u : IsUnit ((q₁ : ℕ) : ZMod q₂) :=
    (ZMod.isUnit_iff_coprime q₁ q₂).mpr hco
  have hu₁u : IsUnit ((q₂ : ZMod q₁)⁻¹) :=
    IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ hq₂u)
  have hu₂u : IsUnit ((q₁ : ZMod q₂)⁻¹) :=
    IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ hq₁u)
  -- pointwise factorization, then CRT Fubini, then unit rescale of the a-slot
  calc ∑ a : ZMod (q₁ * q₂), ‖twinVU (q₁ * q₂) a b₁ b₂‖ ^ 4
      = ∑ a : ZMod (q₁ * q₂),
          (fun t : ZMod q₁ => ‖twinVU q₁ ((q₂ : ZMod q₁)⁻¹ * t)
              ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₁)
              ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₂)‖ ^ 4)
            (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) a)
          * (fun t : ZMod q₂ => ‖twinVU q₂ ((q₁ : ZMod q₂)⁻¹ * t)
              ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₁)
              ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₂)‖ ^ 4)
            (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [twinVU_crt_factor hco a b₁ b₂, norm_mul, mul_pow]
    _ = (∑ t : ZMod q₁, ‖twinVU q₁ ((q₂ : ZMod q₁)⁻¹ * t)
            ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₁)
            ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₂)‖ ^ 4)
        * (∑ t : ZMod q₂, ‖twinVU q₂ ((q₁ : ZMod q₂)⁻¹ * t)
            ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₁)
            ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₂)‖ ^ 4) :=
        SegreFarey.crt_sum_factor hco
          (fun t : ZMod q₁ => ‖twinVU q₁ ((q₂ : ZMod q₁)⁻¹ * t)
            ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₁)
            ((q₂ : ZMod q₁)⁻¹ * ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) b₂)‖ ^ 4)
          (fun t : ZMod q₂ => ‖twinVU q₂ ((q₁ : ZMod q₂)⁻¹ * t)
            ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₁)
            ((q₁ : ZMod q₂)⁻¹ * ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) b₂)‖ ^ 4)
    _ = _ := by
        rw [sum_moment_unit_rescale hu₁u, sum_moment_unit_rescale hu₂u]

/-! ### Layer 3: Markov at every modulus -/

/-- **The Markov count of bad frequency pairs, at EVERY modulus**: for `K > 0`
the pairs `(b₁,b₂)` whose a-averaged fourth moment reaches `K·q³` number at
most `N4U(q)/K` — the general norm form converted into an exceptional-set
count off the prime line. -/
theorem twinVU_markov_general {q : ℕ} [NeZero q] {K : ℝ} (hK : 0 < K) :
    ((Finset.univ.filter (fun bb : ZMod q × ZMod q =>
        K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4)).card : ℝ)
      ≤ ((twinN4U q).card : ℝ) / K := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hl3 : (0 : ℝ) < (q : ℝ) ^ 3 := pow_pos hq0 3
  have htotal : ∑ bb : ZMod q × ZMod q, ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4
      = (q : ℝ) ^ 3 * ((twinN4U q).card : ℝ) := by
    calc ∑ bb : ZMod q × ZMod q, ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4
        = ∑ a : ZMod q, ∑ bb : ZMod q × ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4 :=
          Finset.sum_comm
      _ = ∑ a : ZMod q, ∑ b₁ : ZMod q, ∑ b₂ : ZMod q, ‖twinVU q a b₁ b₂‖ ^ 4 :=
          Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _
      _ = (q : ℝ) ^ 3 * ((twinN4U q).card : ℝ) := twinVU_family_M4_norm_general
  have hcard : ((Finset.univ.filter (fun bb : ZMod q × ZMod q =>
        K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4)).card : ℝ)
        * (K * (q : ℝ) ^ 3)
      ≤ ∑ bb ∈ Finset.univ.filter (fun bb : ZMod q × ZMod q =>
          K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4),
          ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4 := by
    have h := Finset.card_nsmul_le_sum
      (Finset.univ.filter (fun bb : ZMod q × ZMod q =>
        K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4))
      (fun bb => ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4) (K * (q : ℝ) ^ 3)
      (fun bb hbb => (Finset.mem_filter.mp hbb).2)
    rwa [nsmul_eq_mul] at h
  have hsub : ∑ bb ∈ Finset.univ.filter (fun bb : ZMod q × ZMod q =>
        K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4),
        ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4
      ≤ ∑ bb : ZMod q × ZMod q, ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun bb _ _ => Finset.sum_nonneg fun a _ => by positivity)
  rw [le_div_iff₀ hK]
  refine le_of_mul_le_mul_right ?_ hl3
  calc ((Finset.univ.filter (fun bb : ZMod q × ZMod q =>
        K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4)).card : ℝ)
        * K * (q : ℝ) ^ 3
      = ((Finset.univ.filter (fun bb : ZMod q × ZMod q =>
          K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4)).card : ℝ)
          * (K * (q : ℝ) ^ 3) := by ring
    _ ≤ ∑ bb ∈ Finset.univ.filter (fun bb : ZMod q × ZMod q =>
          K * (q : ℝ) ^ 3 ≤ ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4),
          ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4 := hcard
    _ ≤ ∑ bb : ZMod q × ZMod q, ∑ a : ZMod q, ‖twinVU q a bb.1 bb.2‖ ^ 4 := hsub
    _ = (q : ℝ) ^ 3 * ((twinN4U q).card : ℝ) := htotal
    _ = ((twinN4U q).card : ℝ) * (q : ℝ) ^ 3 := by ring

/-! ### Layer 4: the semiprime instantiation -/

/-- The semiprime family moment obeys the constant-4 envelope:
`M4U(ℓ₁ℓ₂) ≤ 4(ℓ₁ℓ₂)⁵` (7.3× slack at (5,7), from the pre-pass). -/
theorem twinVU_family_M4_semiprime_le {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    ∑ a : ZMod (ℓ₁ * ℓ₂), ∑ b₁ : ZMod (ℓ₁ * ℓ₂), ∑ b₂ : ZMod (ℓ₁ * ℓ₂),
      ‖twinVU (ℓ₁ * ℓ₂) a b₁ b₂‖ ^ 4
      ≤ 4 * ((ℓ₁ : ℝ) * ℓ₂) ^ 5 := by
  rw [twinVU_family_M4_semiprime h₁ h₂ hne]
  have hl₁ : (3 : ℝ) ≤ (ℓ₁ : ℝ) := by exact_mod_cast (by omega : 3 ≤ ℓ₁)
  have hl₂ : (3 : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast (by omega : 3 ≤ ℓ₂)
  have e₁ : ((ℓ₁ : ℝ) - 2) * (2 * ℓ₁ - 5) ≤ 2 * (ℓ₁ : ℝ) ^ 2 := by nlinarith
  have e₂ : ((ℓ₂ : ℝ) - 2) * (2 * ℓ₂ - 5) ≤ 2 * (ℓ₂ : ℝ) ^ 2 := by nlinarith
  have p₂ : (0 : ℝ) ≤ ((ℓ₂ : ℝ) - 2) * (2 * ℓ₂ - 5) := by nlinarith
  have hq3 : (0 : ℝ) ≤ ((ℓ₁ : ℝ) * ℓ₂) ^ 3 := by positivity
  calc ((ℓ₁ : ℝ) * ℓ₂) ^ 3 * (((ℓ₁ : ℝ) - 2) * (2 * ℓ₁ - 5))
        * (((ℓ₂ : ℝ) - 2) * (2 * ℓ₂ - 5))
      ≤ ((ℓ₁ : ℝ) * ℓ₂) ^ 3 * (2 * (ℓ₁ : ℝ) ^ 2) * (2 * (ℓ₂ : ℝ) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left e₁ hq3) e₂ p₂ (by positivity)
    _ = 4 * ((ℓ₁ : ℝ) * ℓ₂) ^ 5 := by ring

/-- **THE SEMIPRIME MARKOV COUNT**: at `q = ℓ₁ℓ₂` the pairs `(b₁,b₂)` whose
a-averaged fourth moment reaches `K·q³` number at most `4q²/K` — the wave-1
prime-line exceptional-set count, now living at a composite modulus. -/
theorem twinVU_markov_semiprime {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h₁ : 2 < ℓ₁) (h₂ : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) {K : ℝ} (hK : 0 < K) :
    ((Finset.univ.filter (fun bb : ZMod (ℓ₁ * ℓ₂) × ZMod (ℓ₁ * ℓ₂) =>
        K * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 3 ≤ ∑ a : ZMod (ℓ₁ * ℓ₂),
          ‖twinVU (ℓ₁ * ℓ₂) a bb.1 bb.2‖ ^ 4)).card : ℝ)
      ≤ 4 * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 2 / K := by
  refine (twinVU_markov_general hK).trans ?_
  have hco : Nat.Coprime ℓ₁ ℓ₂ :=
    (Nat.coprime_primes Fact.out Fact.out).mpr hne
  have hn₁ : (ℓ₁ - 2) * (2 * ℓ₁ - 5) ≤ 2 * ℓ₁ ^ 2 :=
    calc (ℓ₁ - 2) * (2 * ℓ₁ - 5)
        ≤ ℓ₁ * (2 * ℓ₁) := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = 2 * ℓ₁ ^ 2 := by ring
  have hn₂ : (ℓ₂ - 2) * (2 * ℓ₂ - 5) ≤ 2 * ℓ₂ ^ 2 :=
    calc (ℓ₂ - 2) * (2 * ℓ₂ - 5)
        ≤ ℓ₂ * (2 * ℓ₂) := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = 2 * ℓ₂ ^ 2 := by ring
  have hmul : (ℓ₁ - 2) * (2 * ℓ₁ - 5) * ((ℓ₂ - 2) * (2 * ℓ₂ - 5))
      ≤ 4 * (ℓ₁ * ℓ₂) ^ 2 :=
    le_trans (Nat.mul_le_mul hn₁ hn₂) (le_of_eq (by ring))
  have hcard : ((twinN4U (ℓ₁ * ℓ₂)).card : ℝ) ≤ 4 * ((ℓ₁ * ℓ₂ : ℕ) : ℝ) ^ 2 := by
    rw [twinN4U_card_crt hco, twinN4U_eq_twinN4, twinN4U_eq_twinN4,
      twinN4_card h₁, twinN4_card h₂]
    exact_mod_cast hmul
  gcongr

end TypeII
end Geometric
end EuclidsPath
