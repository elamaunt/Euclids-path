/-
  GeometricTwinShellFourier — the twin-center defect law, the Hodge shape-line, and the
  log-divisor Fourier product.

  ORIGIN (user's geometric program, §XXIX / §XXXI / §XXXIII of
  `geometric_twin_prime_program_full.md`): between adjacent twin centers the empty-defect
  obeys an exact combinatorial law E_j = g_j + 1 − N_j; all divisor factorizations of one
  center lie on a single Hodge shape-line u+v = ½log((c+1)/(c−1)), on which the Hodge
  complement is the reflection x ↦ −x; and the centered log-divisor measure of a squarefree
  number has Fourier transform ∏ cos(ξ log p / 2).

  WHAT IS PROVED (std axioms, no sorry, no new axioms):
    * `twin_defect_law` — E_j = g_j + 1 − N_j (the combinatorial defect law, §55);
    * `gap_from_volume` — g_j = (c_j c_{j+1}/6)·ΔV_j (§56);
    * `shape_line` — u + v = η_c := ½log((c+1)/(c−1)) (all divisor reps on one line, §59);
    * `hodge_reflection` — in centered coordinates the Hodge complement is x ↦ −x (§60);
    * `logDivisor_fourier` — the centered log-divisor Fourier sum equals ∏ cos(ξ log p/2)
      (§XXXIII): the exact Fourier image of the factorization hypercube.

  DISCLOSURE.  These are exact identities of the twin-center geometry.  §58's global
  telescoping equivalence (infinitely many twin-centers ⟺ the shell decomposition reaches
  r = 0) is a tautological reformulation of `TwinLowers.Infinite`, disclosed as packaging,
  not progress; it is deliberately NOT reproduced here as a "result".  The spectral-
  denominator law P_spec(p|D) = 2/p (§61) is the repo's existing "two forbidden classes
  ±6⁻¹" (`Residuals`) / the x²≡1 count (`Step00HexCubicUnits`); not duplicated.
  Nothing here feeds the wall.  twin sorry untouched.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath
namespace Geometric
namespace TwinShell

open scoped BigOperators

/-! ## The twin-center defect law (§55–56) -/

/-- **Combinatorial defect law (§55).** Between adjacent twin centers, with `N = 2 + S`
    prime-occupied centers and `E = (g−1) − S` empty centers, the empty defect obeys
    `E = g + 1 − N`. -/
theorem twin_defect_law {g N S E : ℕ} (hN : N = 2 + S) (hE : E = (g - 1) - S)
    (hg : 1 ≤ g) (hSg : S ≤ g - 1) : (E : ℤ) = (g : ℤ) + 1 - N := by
  omega

/-- **Gap from volume (§56).** `g_j = (c_j c_{j+1}/6)·(1/c_j − 1/c_{j+1})`. -/
theorem gap_from_volume {cj cj1 : ℝ} (hcj : cj ≠ 0) (hcj1 : cj1 ≠ 0) :
    (cj1 - cj) / 6 = cj * cj1 / 6 * (1 / cj - 1 / cj1) := by
  field_simp

/-! ## The Hodge shape-line and reflection (§59–60) -/

/-- The shape half-log `η_c = ½ log((c+1)/(c−1))`. -/
noncomputable def eta (c : ℝ) : ℝ := (1 / 2) * Real.log ((c + 1) / (c - 1))

/-- **Shape-line theorem (§59).** For a twin center `c` with `c−1 = d·m`, `c+1 = e·n`, the
    shape coordinates `u = ½log(e/d)`, `v = ½log(n/m)` satisfy `u + v = η_c`: all divisor
    representations of one center lie on a single line. -/
theorem shape_line {c d e m n : ℝ} (hd : 0 < d) (he : 0 < e) (hm : 0 < m) (hn : 0 < n)
    (h1 : c - 1 = d * m) (h2 : c + 1 = e * n) :
    (1 / 2) * Real.log (e / d) + (1 / 2) * Real.log (n / m) = eta c := by
  unfold eta
  rw [h1, h2]
  have hratio : (e * n) / (d * m) = (e / d) * (n / m) := by field_simp
  rw [hratio, Real.log_mul (div_ne_zero he.ne' hd.ne') (div_ne_zero hn.ne' hm.ne')]
  ring

/-- **Hodge reflection (§60).** In the centered coordinate `x = u − η_c/2`, the Hodge
    complement `u ↦ η_c − u` is the mirror reflection `x ↦ −x`. -/
theorem hodge_reflection (c u : ℝ) : (eta c - u) - eta c / 2 = -(u - eta c / 2) := by
  ring

/-! ## The log-divisor Fourier product (§XXXIII) -/

/-- Product-to-sum for two cosines. -/
private theorem cos_sub_add (A B : ℝ) :
    Real.cos (A - B) + Real.cos (A + B) = 2 * Real.cos A * Real.cos B := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- **Log-divisor Fourier product (§XXXIII).** The centered log-divisor Fourier sum of a
    squarefree number (prime "logs" `θ i`, `i ∈ P`) factors as a product of per-prime
    cosines: `2^{-|P|} Σ_{T⊆P} cos(ξ/2·(2Σ_T θ − Σ_P θ)) = ∏_{i∈P} cos(ξ θ_i/2)`. The exact
    Fourier image of the Rubik hypercube of factorization choices. -/
theorem logDivisor_fourier {ι : Type*} [DecidableEq ι] (P : Finset ι) (θ : ι → ℝ) (ξ : ℝ) :
    ∏ i ∈ P, Real.cos (ξ * θ i / 2)
      = (2 : ℝ)⁻¹ ^ P.card * ∑ T ∈ P.powerset,
          Real.cos (ξ / 2 * (2 * (∑ i ∈ T, θ i) - ∑ i ∈ P, θ i)) := by
  induction P using Finset.induction with
  | empty => simp
  | @insert a P ha ih =>
      have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        rw [Finset.mem_image] at hT'
        obtain ⟨S, _, hS⟩ := hT'
        exact ha (Finset.mem_powerset.mp hT (hS ▸ Finset.mem_insert_self a S))
      have hinj : ∀ S ∈ P.powerset, ∀ S' ∈ P.powerset,
          insert a S = insert a S' → S = S' := by
        intro S hS S' hS' hSS'
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        have haS' : a ∉ S' := fun h => ha (Finset.mem_powerset.mp hS' h)
        have hc := congrArg (fun s => Finset.erase s a) hSS'
        simpa [Finset.erase_insert haS, Finset.erase_insert haS'] using hc
      rw [Finset.prod_insert ha, ih, Finset.card_insert_of_notMem ha, Finset.powerset_insert,
        Finset.sum_union hdisj, Finset.sum_image hinj, Finset.sum_insert ha]
      have hIS : ∀ S ∈ P.powerset,
          Real.cos (ξ / 2 * (2 * (∑ i ∈ insert a S, θ i) - (θ a + ∑ i ∈ P, θ i)))
            = Real.cos (ξ / 2 * (2 * (∑ i ∈ S, θ i) - ∑ i ∈ P, θ i) + ξ / 2 * θ a) := by
        intro S hS
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        rw [Finset.sum_insert haS]
        congr 1
        ring
      have hTa : ∀ T ∈ P.powerset,
          Real.cos (ξ / 2 * (2 * (∑ i ∈ T, θ i) - (θ a + ∑ i ∈ P, θ i)))
            = Real.cos (ξ / 2 * (2 * (∑ i ∈ T, θ i) - ∑ i ∈ P, θ i) - ξ / 2 * θ a) := by
        intro T hT
        congr 1
        ring
      rw [Finset.sum_congr rfl hTa, Finset.sum_congr rfl hIS, ← Finset.sum_add_distrib]
      have hpair : ∀ S ∈ P.powerset,
          Real.cos (ξ / 2 * (2 * (∑ i ∈ S, θ i) - ∑ i ∈ P, θ i) - ξ / 2 * θ a)
            + Real.cos (ξ / 2 * (2 * (∑ i ∈ S, θ i) - ∑ i ∈ P, θ i) + ξ / 2 * θ a)
            = 2 * Real.cos (ξ / 2 * (2 * (∑ i ∈ S, θ i) - ∑ i ∈ P, θ i))
                * Real.cos (ξ / 2 * θ a) := by
        intro S hS
        exact cos_sub_add _ _
      rw [Finset.sum_congr rfl hpair]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [show ξ * θ a / 2 = ξ / 2 * θ a by ring]
      ring

end TwinShell
end Geometric
end EuclidsPath
