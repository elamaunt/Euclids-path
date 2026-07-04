/-
  Proof BY CONTRADICTION: "twins are finite" + four-corner `H` ⟹ `False`.
  Prose: prose/25_FiniteContradiction.md.

  This is the contraposition of the entire programme. Multi-agent reconnaissance (3 independent
  routes — counting / EPMI / four-corner) produced ONE honest conclusion: the assumption of twin
  finiteness closes into a contradiction with the engine via EXACTLY the same open input as the
  direct line — the strict REAL four-corner on scales + carrier. Not one route bypasses the wall:
    * the counting route dies on Mertens (`Σ 1/p → ∞`, union bound does not beat carrier;
      the fix = Brun + Bombieri–Vinogradov = distribution = red line);
    * the EPMI route inverts the burden (to apply `no_infinite_descent` one must FORGE
      an infinite descent chain — which does not exist; "coverage is total" is what needs refuting);
    * the four-corner route is the cleanest: the entire reduction `finite ⟹ False` is already
      machine-verified, the open part is isolated into ONE typed hypothesis `H`.

  What is recorded HERE is exactly this: an honest CONDITIONAL theorem `finite ∧ H ⟹ False`,
  without `sorry` (`H` is an explicit hypothesis, not `sorry`). The substantive open part is
  conjunct "strict real four-corner" in `H` (= parity problem / transfer model→reality). The
  model side (`four_corner_binom_strict`, `model_four_corner`) is already proven unconditionally.
-/
import EuclidsPath.Engine.ToTwins

set_option autoImplicit false

namespace EuclidsPath

/-- The sole open input is VERBATIM the hypothesis `twin_primes_of_four_corner` (ToTwins.lean).
    Substantively open is conjunct 2 (the strict REAL four-corner on actual rank counts). -/
abbrev FourCornerInput : Prop :=
  ∀ N : ℕ, ∃ (R00 R03 R30 R33 carrier bad : Finset ℕ),
      0 < R00.card ∧
      R00.card * R33.card < R03.card * R30.card ∧
      R03.card * R30.card ≤ R00.card * R00.card ∧
      carrier.card = R00.card ∧ bad.card = R33.card ∧
      (∀ m ∈ carrier, N < m) ∧
      (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)

/--
  **"Twins are finite" is contradictory (modulo `H`).** If the set of twin pairs is FINITE
  (`¬ TwinLowers.Infinite`) and the four-corner input `H` holds, then `False`. Clean: every step
  is a machine-verified lemma; the sole open part is `H`. (Contraposition: `H ⟹` infinitude.)
-/
theorem twin_finite_contradiction
    (hfin : ¬ TwinLowers.Infinite) (H : FourCornerInput) : False :=
  hfin (twin_primes_of_four_corner H)

/-- Same, explicitly via `TwinLowers.Finite` (= `¬ Infinite` for sets). -/
theorem twin_finite_contradiction_of_finite
    (hfin : TwinLowers.Finite) (H : FourCornerInput) : False :=
  (Set.not_infinite.mpr hfin) (twin_primes_of_four_corner H)

/-- Contraposition corollary: the four-corner refutes finiteness ⟹ twins are infinite. -/
theorem twin_infinite_of_fourCorner (H : FourCornerInput) : TwinLowers.Infinite :=
  twin_primes_of_four_corner H

end EuclidsPath
