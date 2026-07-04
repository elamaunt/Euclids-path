/-
  "Wherever the engine goes — it will not turn back and will always halt."
  Prose: prose/24_Irreversibility.md.

  This is the 2nd law of thermodynamics for Euclid's engine, and it is machine-proven here and in the neighbouring modules:
    * "will not turn back" (one step):   `descent_strict` — the rank strictly decreases;
    * "will never return" (globally):     `engine_never_returns` — the rank is strictly anti-monotone,
      the engine never returns to any earlier (higher) state;
    * "will not turn back at two points": `NoBackward.exclusive_no_backward` — the self-member disappears;
    * "will always halt":                 `no_infinite_descent` / `no_perpetual_engine` — an infinite
      chain does not exist (`H(S_t) < H(S_0)/Aᵗ < 1`).

  This is the unifying capstone. No analysis / distribution / sieve.
-/
import Mathlib
import EuclidsPath.Engine.EPMI

set_option autoImplicit false

namespace EuclidsPath.Engine

/--
  **"Will not turn back" (globally).** If every step is a successful `A`-descent (`A ≥ 1`), then the rank is
  STRICTLY ANTI-MONOTONE: `s < t ⟹ H t < H s`. The engine never returns to any earlier
  (higher) state — irreversibility.
-/
theorem engine_never_returns {A : ℕ} (hA : 1 ≤ A) (H : ℕ → ℕ)
    (hchain : ∀ t, DescentStep A (H t) (H (t + 1))) : StrictAnti H :=
  strictAnti_nat_of_succ_lt (fun n => descent_strict hA (hchain n))

/-
  "Will always halt" — that is `no_infinite_descent` (Engine/EPMI): an infinite `A`-descent chain
  does not exist. Together with `engine_never_returns` ("will not turn back") this is the entire 2nd law:
  wherever the engine goes, it will not turn back and will always halt.
-/

/-! ### Directional asymmetry: "+1 is fuel", the engine runs forever only upward -/

/--
  **Downward — finite.** In `ℕ` there is no infinitely descending chain: any strictly decreasing `f : ℕ → ℕ`
  yields a contradiction (ordinal completeness of ℕ = EPMI at `A=1`). The engine cannot run downward forever.
-/
theorem no_infinite_engine_descent (f : ℕ → ℕ) (hf : StrictAnti f) : False :=
  no_infinite_descent (le_refl 1) f
    (fun t => by simp only [DescentStep, one_mul]; exact hf (Nat.lt_succ_self t))

/--
  **Upward — infinite ("+1 = fuel").** Successor yields a strictly increasing chain: fuel
  (larger centers) is always available, the engine runs upward without stopping.
  Together with `no_infinite_engine_descent`: the engine runs forever ONLY in one direction (upward).
-/
theorem fuel_ascent_strictMono : StrictMono (fun n : ℕ => n + 1) :=
  fun _ _ h => Nat.add_lt_add_right h 1

/--
  **"Turns and halts" (exact bound).** If the engine turned into descent and made `k` strict
  steps downward (`H(t+1) < H(t)` for `t < k`), then `k ≤ H 0`: it will definitely halt, in at most
  `H 0` steps. Any turn downward is a finite path (ordinal completeness of ℕ).
-/
theorem turned_engine_halts (H : ℕ → ℕ) (k : ℕ)
    (hdesc : ∀ t, t < k → H (t + 1) < H t) : k ≤ H 0 := by
  have hbound : ∀ t, t ≤ k → H t + t ≤ H 0 := by
    intro t ht
    induction t with
    | zero => simp
    | succ n ih =>
      have hn : H (n + 1) < H n := hdesc n (by omega)
      have := ih (by omega)
      omega
  have := hbound k (le_refl k)
  omega

end EuclidsPath.Engine
