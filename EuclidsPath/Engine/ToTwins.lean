/-
  Capstone: chain to twin primes from the real four-corner. Prose: prose/21_ToTwins.md.

  Assembles into ONE machine-verified chain all verified links:
    real four-corner + side-corner  --(N33_lt_N00_of_four_corner)-->  N₃₃ < N₀₀
      --(survivor_of_not_covered)-->  surviving carrier center
      --(survivor ⟹ twin)-->  twin center above N
      --(infinite_of_unbounded_centers)-->  TwinLowers.Infinite (twin prime conjecture).

  The ONLY open input `H` is: that the REAL rank counts satisfy the four-corner
  `R₀₀·R₃₃ < R₀₃·R₃₀` (+ easy side-corner) at arbitrarily large scales, and that every survivor is a
  twin. The model four-corner is already proved (`ModelFourCorner`); what remains is the transfer model→reality.
  There is NO `sorry` here: this is an honest conditional theorem (conjecture ⟸ explicit input `H`).
-/
import EuclidsPath.Engine.FourCorner
import EuclidsPath.Engine.TwoTransport

set_option autoImplicit false

namespace EuclidsPath

/--
  **Twin prime conjecture from the real four-corner.** If at every scale `N` there exists a block where
  the real rank counts give a strict four-corner and side-corner (hence `N₃₃ < N₀₀`), the carrier lies
  above `N`, and every survivor is a twin center, then there are infinitely many twin primes.
-/
theorem twin_primes_of_four_corner
    (H : ∀ N : ℕ, ∃ (R00 R03 R30 R33 carrier bad : Finset ℕ),
        0 < R00.card ∧
        R00.card * R33.card < R03.card * R30.card ∧        -- four-corner (real)
        R03.card * R30.card ≤ R00.card * R00.card ∧        -- side-corner (real, easy)
        carrier.card = R00.card ∧ bad.card = R33.card ∧    -- carrier = rank-(0,0), bad = rank-(3,3)
        (∀ m ∈ carrier, N < m) ∧
        (∀ m ∈ carrier, m ∉ bad → IsTwinCenter m)) :
    TwinLowers.Infinite := by
  apply twin_prime_conjecture_of_blocks
  intro N
  obtain ⟨R00, R03, R30, R33, carrier, bad, hpos, hfc, hsc, hcc, hbc, habove, htwin⟩ := H N
  have h33 : R33.card < R00.card := N33_lt_N00_of_four_corner hpos hfc hsc
  refine ⟨carrier, bad, habove, ?_, htwin⟩
  rw [hbc, hcc]; exact h33

end EuclidsPath
