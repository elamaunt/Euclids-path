/-
  Step 00 — Overview: main theorem and basic definitions.
  Prose: prose/00_Overview.md

  Here the formal goal of the entire chain is fixed — the statement of the twin-prime conjecture —
  and the basic definitions on which all subsequent steps rely are introduced.

  Status: the statement of the main theorem is left as `sorry` (this is the ultimate goal of the program);
  its proof is assembled in steps 13/14 and runs into the open gaps of step 15.

  NB: the project has not yet been compiled (Lean is not installed). See lakefile.toml.
-/
import Mathlib

namespace EuclidsPath

/-- A twin-prime pair with lesser member `p`: primes `p` and `p+2`. -/
def IsTwinPair (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- The set of lesser members of twin-prime pairs. -/
def TwinLowers : Set ℕ := { p | IsTwinPair p }

/--
  **Main theorem (twin-prime conjecture).**
  There are infinitely many primes `p` for which `p + 2` is also prime.

  This is the ultimate goal of the entire `Euclids-path` chain. The proof is assembled from steps 00–14 and
  runs into the open lemmas of step 15 (BDNC⁺, DASC, G2, `c_G > η_D + η_B`, O4C-res).
-/
theorem twin_prime_conjecture : TwinLowers.Infinite := by
  -- OPEN: ultimate goal of the program. Assembly — Step13/Step14; open gaps — Step15.
  sorry

/--
  Index (center) form: center `m` defines a twin-prime pair when both `6m-1` and `6m+1` are prime.
  The connection with `IsTwinPair` is established in step 01 (`Step01_CenterReduction`).
-/
def IsTwinCenter (m : ℕ) : Prop := (6 * m - 1).Prime ∧ (6 * m + 1).Prime

/-- The set of centers of twin-prime pairs. -/
def TwinCenters : Set ℕ := { m | IsTwinCenter m }

end EuclidsPath
