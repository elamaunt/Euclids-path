/-
  Model→reality separation for four-corner. Prose: prose/22_RealFourCorner.md.

  Context: the model four-corner `N₀₀^CRT·N₃₃^CRT ≤ N₀₃^CRT·N₃₀^CRT` is proved by construction
  (`ModelFourCorner`, construction G_q=∏(1+w_q(x+z)) + Maclaurin). The real counts differ by
  the sieve remainder `e_ij = N_ij^real − N_ij^CRT`. Here the EXACT difference formula is recorded
  together with the condition under which the real four-corner follows from the model one.

  This is the honest boundary in the code: real four-corner ⟺ model + remainder control (one formula).
  Everything is ring algebra over ℤ (the remainder may be signed). No analysis/distribution/sieve.
-/
import Mathlib

set_option autoImplicit false

namespace EuclidsPath

/--
  **Exact four-corner decomposition (real = model + remainder).**
  The difference of the real four-corner equals the model difference plus an explicit remainder term `R`
  (cross-terms of the remainder). A pure ring identity.
-/
theorem real_four_corner_decomp (m00 m03 m30 m33 e00 e03 e30 e33 : ℤ) :
    (m00 + e00) * (m33 + e33) - (m03 + e03) * (m30 + e30)
      = (m00 * m33 - m03 * m30)
        + (m00 * e33 + e00 * m33 + e00 * e33 - m03 * e30 - e03 * m30 - e03 * e30) := by
  ring

/--
  **Real four-corner from model + remainder control.**
  If the model four-corner `m₀₀·m₃₃ ≤ m₀₃·m₃₀` holds (proved by construction), and the remainder
  term `R` fits within the model supply (`R ≤ m₀₃m₃₀ − m₀₀m₃₃`), then the REAL four-corner
  `(m₀₀+e₀₀)(m₃₃+e₃₃) ≤ (m₀₃+e₀₃)(m₃₀+e₃₀)` holds as well.

  This is the sole open input of the capstone `ToTwins`: control of the sieve remainder `e_ij`.
-/
theorem real_four_corner_of_remainder
    (m00 m03 m30 m33 e00 e03 e30 e33 : ℤ)
    (_hmodel : m00 * m33 ≤ m03 * m30)
    (hrem : m00 * e33 + e00 * m33 + e00 * e33 - m03 * e30 - e03 * m30 - e03 * e30
              ≤ m03 * m30 - m00 * m33) :
    (m00 + e00) * (m33 + e33) ≤ (m03 + e03) * (m30 + e30) := by
  have h := real_four_corner_decomp m00 m03 m30 m33 e00 e03 e30 e33
  have hle : (m00 + e00) * (m33 + e33) - (m03 + e03) * (m30 + e30) ≤ 0 := by
    rw [h]; linarith
  linarith

end EuclidsPath
