/-
  Collatz as a TUG OF WAR: the engine against the rope.
  Discussion: prose/55_Collatz.md. Numbers: tools/collatz_engine_harness.py, tools/collatz_fuel_harness.py.

  The author's reading: "a contest between engine and rope: the engine advances by AT MOST
  1 rank forward per step, the rope pulls back by 1 or 2 ranks; the fuel runs out — the engine
  is dragged back to the start". The formalization is MULTIPLICATIVE (pure ℕ-arithmetic, no logarithms):
  rank = binary order; "+1 rank" = at most a doubling, "−1 rank" = exactly a halving.

  GREEN CORE (proved here):
  - engine_at_most_one_rank : T n ≤ 2n               — engine: ≤ +1 rank on ANY step;
  - rope_pulls_one          : 2·T n = n  (n even)    — rope: exactly −1 rank;
  - rope_pulls_two          : 4·T²(n) = n (n≡0 mod4) — rope: −2 ranks over two steps;
  - window_budget           : 2^e·T^k(n) ≤ 2^t·n     — WINDOW BUDGET: the bounds multiply
                              INDEPENDENTLY of the step order (t odd, e even, t+e=k);
  - window_descends         : e > t in a window ⟹ T^k(n) < n — rope out-pulled ⟹ strict descent;
  - reaches_one_of_countingLaw (HERO): the rope law ⟹ reaching 1.

  🔴 NAMED INPUT (the open heart, NOT proved): RopeCountingLaw n — "at every
  position of the trajectory ABOVE the halting cycle (value > 2) there is a window in which the even
  steps strictly outnumber the odd ones". The universal form (∀ n ≥ 1) is OPEN: it ENTAILS the Collatz
  conjecture (hero); the converse is NOT known; it may be strictly stronger than the conjecture. On
  merging with the repo this input becomes the field `collatzBoundary` of the first cause `step00FirstCause`
  (see `Engine/CausalClosureAxiom` §18 and the consumer `Engine/CollatzFirstCause`).

  HONESTY (three disclosures):
  1) "The condemned man's bridge": the value form of the law (ValueDescentLaw) is EQUIVALENT to convergence
     (valueLaw_iff_reaches_one) — on its own it adds NO content. Only the counting
     form is substantive; its reverse side (convergence ⟹ counting law) is NOT asserted:
     the window budget is one-sided.
  2) The original form "2·odd < even" is REJECTED: empirically e ≈ 1.016·t on the accelerated map
     (halvings/triplings = 2.016 in the raw map, minus 1 eaten by the acceleration), i.e. e > 2t
     is FALSE on average. The threshold e > t is the EXACT threshold that the crude ×2 bound converts
     into descent, and it is razor-thin (average margin ~1.6%). This is the price of giving up log₂3.
  3) Windows of length 1 FAIL at every odd position (no_single_step_law) — consistent
     with the wall CollatzFuel.no_monotone_height: there is no monotone height, the law MUST live on
     windows ≥ 2. On the halting state the law is vacuous (countingLaw_1) — that is why the quantifier
     is restricted to "above the cycle": from value 1 the steps alternate 1→2→1 and t ≥ e in ALL windows,
     the law without the restriction would be false for every convergent trajectory.

  Duplicating T from CollatzEngine.lean is INTENTIONAL: the three Collatz cores are self-contained
  (core Lean, no Mathlib and no import); on merging the duplicates were removed only from the consumer.
-/

namespace EuclidsPath.Collatz.TugOfWar

/-- The accelerated Collatz map (a duplicate of CollatzEngine.T — the files are self-contained). -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Trajectory: k steps of the map T from n (peeling off the FIRST step — convenient for the window budget). -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter k (T n)

/-- Number of ODD steps (engine moves) in a window of k steps from n. -/
def oddCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => oddCount k (T n) + (if n % 2 = 0 then 0 else 1)

/-- Number of EVEN steps (rope pulls) in a window of k steps from n. -/
def evenCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => evenCount k (T n) + (if n % 2 = 0 then 1 else 0)

/-! ## Engine and rope: per-step bounds (green) -/

/-- **ENGINE: at most +1 rank per step.** `T n ≤ 2n` for ALL n: the odd step
    (3n+1)/2 ≤ 2n for n ≥ 1 (odd n ≥ 1 automatically), the even one all the more so. -/
theorem engine_at_most_one_rank (n : Nat) : T n ≤ 2 * n := by
  unfold T
  by_cases h : n % 2 = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **Exact fuel cost of an odd step:** `2·T n = 3n+1` — the engine pays ×1.5+ε,
    and NOT ×2; the ×2 bound is crude (see honesty-2 in the header). -/
theorem engine_exact_fuel (n : Nat) (ho : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  unfold T; rw [if_neg (by omega : ¬ n % 2 = 0)]; omega

/-- **ROPE: exactly −1 rank on an even step:** `2·T n = n` ("pulls by 1"). -/
theorem rope_pulls_one (n : Nat) (he : n % 2 = 0) : 2 * T n = n := by
  unfold T; rw [if_pos he]; omega

/-- **ROPE: −2 ranks over two even steps** (n ≡ 0 mod 4): `4·T²(n) = n` ("pulls by 2"). -/
theorem rope_pulls_two (n : Nat) (h4 : n % 4 = 0) : 4 * iter 2 n = n := by
  have e1 : T n = n / 2 := by unfold T; rw [if_pos (by omega : n % 2 = 0)]
  have e2 : T (n / 2) = n / 2 / 2 := by
    unfold T; rw [if_pos (by omega : n / 2 % 2 = 0)]
  have e3 : iter 2 n = T (T n) := rfl
  rw [e3, e1, e2]
  omega

/-- The engine does not stall at zero: for n ≥ 1 a step preserves n ≥ 1. -/
theorem T_pos (n : Nat) (h : 1 ≤ n) : 1 ≤ T n := by
  unfold T
  by_cases hp : n % 2 = 0
  · rw [if_pos hp]; omega
  · rw [if_neg hp]; omega

theorem iter_pos (j n : Nat) (h : 1 ≤ n) : 1 ≤ iter j n := by
  induction j generalizing n with
  | zero => exact h
  | succ j ih => simp only [iter]; exact ih (T n) (T_pos n h)

/-- Gluing trajectories: `T^(j+k) = T^k ∘ T^j`. -/
theorem iter_add (j k n : Nat) : iter (j + k) n = iter k (iter j n) := by
  induction j generalizing n with
  | zero => simp [iter]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [iter]
    exact ih (T n)

/-- Step accounting: a window of k steps = t odd + e even, t + e = k. -/
theorem counts_total (k n : Nat) : oddCount k n + evenCount k n = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [oddCount, evenCount]
    have h := ih (T n)
    by_cases hp : n % 2 = 0
    · simp only [if_pos hp]; omega
    · simp only [if_neg hp]; omega

/-! ## Window budget — the green core of the tug of war -/

/-- **WINDOW BUDGET.** Over k steps from n with t = oddCount odd and e = evenCount even:
    `2^e · T^k(n) ≤ 2^t · n`. Each rope pull multiplies by EXACTLY ½ (rope_pulls_one),
    each engine move — by AT MOST 2 (engine_at_most_one_rank); the bounds
    multiply under ANY step order. Pure ℕ-arithmetic: floor-divisions are eaten
    by the precision of the bounds, no logarithms needed. -/
theorem window_budget (k n : Nat) :
    2 ^ evenCount k n * iter k n ≤ 2 ^ oddCount k n * n := by
  induction k generalizing n with
  | zero =>
    simp only [iter, oddCount, evenCount]
    exact Nat.le_refl _
  | succ k ih =>
    simp only [iter, oddCount, evenCount]
    by_cases h : n % 2 = 0
    · simp only [if_pos h, Nat.add_zero]
      have hT : 2 * T n = n := rope_pulls_one n h
      calc 2 ^ (evenCount k (T n) + 1) * iter k (T n)
          = 2 * (2 ^ evenCount k (T n) * iter k (T n)) := by
            rw [Nat.pow_add_one, Nat.mul_comm (2 ^ evenCount k (T n)) 2, Nat.mul_assoc]
        _ ≤ 2 * (2 ^ oddCount k (T n) * T n) :=
            Nat.mul_le_mul (Nat.le_refl 2) (ih (T n))
        _ = 2 ^ oddCount k (T n) * (2 * T n) :=
            Nat.mul_left_comm 2 (2 ^ oddCount k (T n)) (T n)
        _ = 2 ^ oddCount k (T n) * n := by rw [hT]
    · simp only [if_neg h, Nat.add_zero]
      have hT : T n ≤ 2 * n := engine_at_most_one_rank n
      calc 2 ^ evenCount k (T n) * iter k (T n)
          ≤ 2 ^ oddCount k (T n) * T n := ih (T n)
        _ ≤ 2 ^ oddCount k (T n) * (2 * n) :=
            Nat.mul_le_mul (Nat.le_refl (2 ^ oddCount k (T n))) hT
        _ = 2 ^ (oddCount k (T n) + 1) * n := by rw [Nat.pow_add_one, Nat.mul_assoc]

/-- **Rope out-pulled the window ⟹ strict descent.** If the even steps STRICTLY outnumber (t < e),
    then `2^(t+1) ≤ 2^e`, the budget gives `2^t·(2·T^k(n)) ≤ 2^t·n`, we cancel 2^t > 0:
    `2·T^k(n) ≤ n`, whence `T^k(n) < n` for n ≥ 1. -/
theorem window_descends (k n : Nat) (h1 : 1 ≤ n)
    (hc : oddCount k n < evenCount k n) : iter k n < n := by
  have hb := window_budget k n
  have hmono : 2 ^ (oddCount k n + 1) ≤ 2 ^ evenCount k n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hchain : 2 ^ oddCount k n * (2 * iter k n) ≤ 2 ^ oddCount k n * n := by
    calc 2 ^ oddCount k n * (2 * iter k n)
        = 2 ^ (oddCount k n + 1) * iter k n := by rw [Nat.pow_add_one, Nat.mul_assoc]
      _ ≤ 2 ^ evenCount k n * iter k n := Nat.mul_le_mul hmono (Nat.le_refl (iter k n))
      _ ≤ 2 ^ oddCount k n * n := hb
  have hhalf : 2 * iter k n ≤ n :=
    Nat.le_of_mul_le_mul_left hchain (Nat.two_pow_pos (oddCount k n))
  omega

/-! ## Tug-of-war laws: two forms, an honest ladder -/

/-- **🔴 ROPE DOMINATION LAW (counting form) — a named input.** At every position
    of the trajectory ABOVE the halting cycle (value > 2) there is a window in which the even steps strictly
    outnumber the odd ones. k > 0 automatically (for k = 0 both counts equal 0). Here ONLY the
    definition: universally in n this is OPEN (see the header). -/
def RopeCountingLaw (n : Nat) : Prop :=
  ∀ j : Nat, 2 < iter j n →
    ∃ k : Nat, oddCount k (iter j n) < evenCount k (iter j n)

/-- **Value descent law (value form).** At every position above the cycle there is
    a future position strictly lower. ATTENTION: this form is EQUIVALENT to convergence
    (valueLaw_iff_reaches_one) — "the condemned man's bridge", no content is added. -/
def ValueDescentLaw (n : Nat) : Prop :=
  ∀ j : Nat, 2 < iter j n → ∃ k : Nat, iter (j + k) n < iter j n

/-- A rung of the ladder: the counting law ⟹ the value law (via the window budget). -/
theorem valueLaw_of_countingLaw (n : Nat) (law : RopeCountingLaw n) :
    ValueDescentLaw n := by
  intro j hj
  cases law j hj with
  | intro k hk =>
    refine ⟨k, ?_⟩
    rw [iter_add j k n]
    exact window_descends k (iter j n) (by omega) hk

/-- The halting cycle absorbs: after reaching 1 the values stay forever in {1, 2} (1→2→1). -/
theorem cycle_absorbs (n K : Nat) (hK : iter K n = 1) :
    ∀ d : Nat, iter (K + d) n = 1 ∨ iter (K + d) n = 2 := by
  intro d
  induction d with
  | zero => exact Or.inl hK
  | succ d ih =>
    have hstep : iter (K + (d + 1)) n = iter 1 (iter (K + d) n) := iter_add (K + d) 1 n
    rw [hstep]
    cases ih with
    | inl h => rw [h]; exact Or.inr (by decide)
    | inr h => rw [h]; exact Or.inl (by decide)

/-- **HERO ENGINE: the value law ⟹ reaching 1.** Induction on the CEILING of the value
    (ordinary induction on v — without strong recursion and without Classical.choice): a position with
    value ≤ v+1 is either already 1, or 2 (one step), or > 2 — the law gives a future position
    with value ≤ v, we apply the induction hypothesis. -/
theorem reaches_one_of_valueLaw (n : Nat) (h1 : 1 ≤ n) (law : ValueDescentLaw n) :
    ∃ K, iter K n = 1 := by
  suffices h : ∀ v j, iter j n ≤ v → ∃ K, iter K n = 1 by
    exact h n 0 (Nat.le_refl n)
  intro v
  induction v with
  | zero =>
    intro j hj
    exfalso
    have hp := iter_pos j n h1
    omega
  | succ v ih =>
    intro j hj
    by_cases hle : iter j n ≤ v
    · exact ih j hle
    · by_cases hone : iter j n = 1
      · exact ⟨j, hone⟩
      · by_cases htwo : iter j n = 2
        · exact ⟨j + 1,
            ((iter_add j 1 n).trans (congrArg (iter 1) htwo)).trans (by decide)⟩
        · have hp := iter_pos j n h1
          cases law j (by omega) with
          | intro k hk => exact ih (j + k) (by omega)

/-- **HERO (main theorem): the rope domination law ⟹ the engine is dragged back to the start.**
    Ladder: RopeCountingLaw → (window budget) → ValueDescentLaw → (induction on the ceiling) → 1. -/
theorem reaches_one_of_countingLaw (n : Nat) (h1 : 1 ≤ n) (law : RopeCountingLaw n) :
    ∃ K, iter K n = 1 :=
  reaches_one_of_valueLaw n h1 (valueLaw_of_countingLaw n law)

/-! ## Collapse audit: why the value form is worse than the counting form -/

/-- **COLLAPSE of the value form (disclosure of "the condemned man's bridge"):** convergence ⟹
    the value law. Before reaching 1 the descent is given by the point of reaching itself; after — there are no
    positions above the cycle (cycle_absorbs). Together with the hero: ValueDescentLaw ⟺ convergence. -/
theorem valueLaw_of_reaches_one (n : Nat) (hr : ∃ K, iter K n = 1) :
    ValueDescentLaw n := by
  cases hr with
  | intro K hK =>
    intro j hj
    by_cases hjK : j < K
    · refine ⟨K - j, ?_⟩
      rw [show j + (K - j) = K by omega, hK]
      omega
    · exfalso
      have habs := cycle_absorbs n K hK (j - K)
      rw [show K + (j - K) = j by omega] at habs
      cases habs with
      | inl h => omega
      | inr h => omega

/-- The value form ⟺ the conjecture for n: "the condemned man's bridge" disclosed formally. -/
theorem valueLaw_iff_reaches_one (n : Nat) (h1 : 1 ≤ n) :
    ValueDescentLaw n ↔ ∃ K, iter K n = 1 :=
  ⟨reaches_one_of_valueLaw n h1, valueLaw_of_reaches_one n⟩

/-! ## Honesty audits -/

/-- **The k=1 window FAILS at every odd position:** the value grows (the engine
    pulls forward), and the count gives t=1 > e=0. Consistent with CollatzFuel.no_monotone_height:
    there is no per-step law — the rope law MUST live on windows ≥ 2. -/
theorem single_window_fails (n : Nat) (ho : n % 2 = 1) :
    n < T n ∧ ¬ (oddCount 1 n < evenCount 1 n) := by
  constructor
  · unfold T; rw [if_neg (by omega : ¬ n % 2 = 0)]; omega
  · simp only [oddCount, evenCount, if_neg (show ¬ n % 2 = 0 by omega)]
    omega

/-- Arbitrarily large witnesses of the k=1 failure (the family 2N+1; cf. 4N+5 in CollatzFuel). -/
theorem no_single_step_law (N : Nat) :
    ∃ n, N < n ∧ n % 2 = 1 ∧ n < T n ∧ ¬ (oddCount 1 n < evenCount 1 n) := by
  have h := single_window_fails (2 * N + 1) (by omega)
  exact ⟨2 * N + 1, by omega, by omega, h.1, h.2⟩

/-- A non-vacuous green example of the counting condition: n=4 has a window k=2 (4→2→1): t=0 < e=2. -/
theorem window_at_4 : oddCount 2 4 < evenCount 2 4 := by decide

/-- The counting law is TRUE for n=4: the only position above the cycle is the start (window k=2);
    the existence of satisfying n is green. Universality is the open input. -/
theorem countingLaw_4 : RopeCountingLaw 4 := by
  intro j hj
  by_cases h0 : j = 0
  · subst h0
    exact ⟨2, by decide⟩
  · by_cases h1 : j = 1
    · subst h1
      exact absurd hj (by decide)
    · exfalso
      have habs := cycle_absorbs 4 2 (by decide) (j - 2)
      rw [show 2 + (j - 2) = j by omega] at habs
      cases habs with
      | inl h => omega
      | inr h => omega

/-- **The cycle-tail trap (disclosure):** for n=1 the law is true VACUOUSLY — there are no positions above
    the cycle. The restriction "value > 2" in the quantifier is mandatory: from value 1 the steps
    alternate 1→2→1 and t ≥ e in all windows — the law without the restriction would be false for
    EVERY convergent trajectory. -/
theorem countingLaw_1 : RopeCountingLaw 1 := by
  intro j hj
  exfalso
  have habs := cycle_absorbs 1 0 (by decide) j
  rw [show 0 + j = j by omega] at habs
  cases habs with
  | inl h => omega
  | inr h => omega

/-! ## Non-descending orbit = perpetual engine -/

/-- **Non-descending orbit**: the trajectory never drops below the start. -/
def NonDescendingOrbit (n : Nat) : Prop :=
  ∀ k : Nat, n ≤ iter k n

/-- **THEOREM (non-descent = perpetual engine, counting form):** for the orbit
    not to descend, the engine must win or draw EVERY window —
    forever: `evenCount ≤ oddCount` for all k. Directly from the window budget:
    2^e·iter ≤ 2^t·n and n ≤ iter give 2^e ≤ 2^t. Infinite refuelling
    without a single lost window — that is exactly a perpetual engine. -/
theorem nonDescending_engine_never_loses (n : Nat) (h1 : 1 ≤ n)
    (hnd : NonDescendingOrbit n) :
    ∀ k : Nat, evenCount k n ≤ oddCount k n := by
  intro k
  cases Nat.lt_or_ge (oddCount k n) (evenCount k n) with
  | inr hge => omega
  | inl hlt =>
    exfalso
    have hb := window_budget k n
    have hup := hnd k
    have hchain : 2 ^ evenCount k n * n ≤ 2 ^ oddCount k n * n :=
      Nat.le_trans (Nat.mul_le_mul (Nat.le_refl _) hup) hb
    have hpow : 2 ^ evenCount k n ≤ 2 ^ oddCount k n :=
      Nat.le_of_mul_le_mul_right hchain (by omega)
    have hmono : 2 ^ (oddCount k n + 1) ≤ 2 ^ evenCount k n :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 0 < 2 ^ oddCount k n := Nat.two_pow_pos _
    have hdouble : (2 : Nat) ^ (oddCount k n + 1) = 2 * 2 ^ oddCount k n := by
      rw [Nat.pow_add_one, Nat.mul_comm]
    omega

/-- A non-descending orbit (from a start above the cycle) never reaches 1 —
    perpetual motion without halting. -/
theorem nonDescending_never_halts (n : Nat) (h3 : 3 ≤ n)
    (hnd : NonDescendingOrbit n) :
    ∀ K : Nat, iter K n ≠ 1 := by
  intro K hK
  have := hnd K
  omega

/-- **Summary "non-descending orbit = perpetual engine":** the engine does not
    lose a single window AND never halts. -/
theorem nonDescendingOrbit_is_perpetual_engine (n : Nat) (h3 : 3 ≤ n)
    (hnd : NonDescendingOrbit n) :
    (∀ k, evenCount k n ≤ oddCount k n) ∧ (∀ K, iter K n ≠ 1) :=
  ⟨nonDescending_engine_never_loses n (by omega) hnd,
   nonDescending_never_halts n h3 hnd⟩

/-- **The rope law forbids a perpetual engine:** under the domination law
    non-descending orbits (above the cycle) do NOT exist — the very first position gives
    a window with a rope surplus and a strict descent below the start. -/
theorem no_nonDescendingOrbit_under_countingLaw (n : Nat) (h3 : 3 ≤ n)
    (law : RopeCountingLaw n) : ¬ NonDescendingOrbit n := by
  intro hnd
  cases law 0 (by simp only [iter]; omega) with
  | intro k hk =>
    have hdrop : iter k n < n := by
      have := window_descends k n (by omega)
      simp only [iter] at hk
      exact this hk
    have := hnd k
    omega

/-! ## The bottom rank: why +1 confuses the engine at the digits 2 and 3 -/

/-- **"+1 weighs a full rank ONLY at n = 1":** 3n+1 reaches the engine's upper
    bound 4n (exactly +2 raw ranks) at one single point —
    at the bottom. Above the bottom the +1 addition is sub-rank: 3n+1 < 4n. -/
theorem plus_one_full_rank_only_at_one (n : Nat) (h1 : 1 ≤ n) :
    3 * n + 1 = 4 * n ↔ n = 1 := by
  constructor
  · intro h; omega
  · intro h; omega

/-- Above the bottom +1 is strictly sub-rank. -/
theorem plus_one_subrank_above_one (n : Nat) (h3 : 3 ≤ n) :
    3 * n + 1 < 4 * n := by omega

/-- **"The engine is confused at the bottom":** exactly at n = 1 the engine's shot
    lands on a PURE power of the rope (3·1+1 = 4 = 2²) — the rope drags it
    two steps in a row back, forming the absorbing cycle 1→2→1. The digits 2 and 3 at
    the bottom rank are indistinguishable for +1: it makes up a whole rank there. -/
theorem engine_confused_at_bottom :
    3 * 1 + 1 = 2 ^ 2 ∧ T 1 = 2 ∧ T 2 = 1 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Refutation = engine: any counterexample carries a perpetual engine

HONEST DISCLOSURE ABOUT THE AXIOMS: the theorems of this section are the only place in the file
where classical logic is used (`Classical.em` — the choice of the orbit's minimum
position is non-constructive); their axiom list is the standard triple
[propext, Classical.choice, Quot.sound]. The rest of the file stays
choice-free ([propext, Quot.sound]). -/

/-- **The orbit's minimum exists** (well-ordering of ℕ): every orbit
    has a position of global minimum value. -/
theorem exists_min_position (n : Nat) :
    ∃ j : Nat, ∀ k : Nat, iter j n ≤ iter k n := by
  suffices h : ∀ v j0 : Nat, iter j0 n ≤ v →
      ∃ j, ∀ k, iter j n ≤ iter k n from
    h (iter 0 n) 0 (Nat.le_refl _)
  intro v
  induction v with
  | zero =>
    intro j0 h0
    refine ⟨j0, fun k => ?_⟩
    omega
  | succ v ih =>
    intro j0 h0
    cases Classical.em (∃ k, iter k n < iter j0 n) with
    | inl hex =>
      cases hex with
      | intro k hk => exact ih k (by omega)
    | inr hno =>
      refine ⟨j0, fun k => ?_⟩
      cases Nat.lt_or_ge (iter k n) (iter j0 n) with
      | inl hlt => exact absurd ⟨k, hlt⟩ hno
      | inr hge => exact hge

/-- **CENTRAL THEOREM: a Collatz counterexample carries a perpetual engine.**
    If an orbit never reaches 1, then its tail from the minimum position is a
    non-descending non-halting orbit, that is, exactly our perpetual
    engine (`nonDescendingOrbit_is_perpetual_engine`: loses not a
    single window and never halts). The construction is GENUINE, not
    ex falso: the tail is exhibited explicitly. To refute Collatz = to build
    a perpetual engine — literally. -/
theorem nonHalting_carries_perpetual_engine (n : Nat)
    (hnh : ∀ K : Nat, iter K n ≠ 1) :
    ∃ j : Nat, NonDescendingOrbit (iter j n) ∧
      ∀ K : Nat, iter K (iter j n) ≠ 1 := by
  cases exists_min_position n with
  | intro j hj =>
    refine ⟨j, ?_, ?_⟩
    · intro k
      rw [← iter_add]
      exact hj (j + k)
    · intro K hK
      rw [← iter_add] at hK
      exact hnh (j + K) hK

/-- **Collatz ⟺ "there is no perpetual engine".** Halting of an orbit is equivalent to
    the absence of a perpetual tail: the Collatz conjecture is exactly the statement
    of the impossibility of a perpetual engine for the map T. -/
theorem collatz_iff_no_perpetual_tail (n : Nat) :
    (∃ K : Nat, iter K n = 1) ↔
      ¬ ∃ j : Nat, NonDescendingOrbit (iter j n) ∧
        ∀ K : Nat, iter K (iter j n) ≠ 1 := by
  constructor
  · intro hhalt htail
    cases hhalt with
    | intro K hK =>
      cases htail with
      | intro j htl =>
        cases Nat.lt_or_ge K j with
        | inr hjK =>
          -- j ≤ K: the tail catches 1 at step K − j
          have hidx : j + (K - j) = K := by omega
          have h1 : iter (K - j) (iter j n) = 1 := by
            rw [← iter_add, hidx]
            exact hK
          exact htl.2 (K - j) h1
        | inl hKj =>
          -- K < j: after K everything is in the vacuum {1,2}, the tail dies out in ≤ 1 step
          have habs := cycle_absorbs n K hK (j - K)
          have hidx : K + (j - K) = j := by omega
          rw [hidx] at habs
          cases habs with
          | inl h1 =>
            exact htl.2 0 h1
          | inr h2 =>
            have h1 : iter 1 (iter j n) = 1 := by
              show iter 0 (T (iter j n)) = 1
              rw [h2]
              decide
            exact htl.2 1 h1
  · intro hno
    cases Classical.em (∃ K : Nat, iter K n = 1) with
    | inl h => exact h
    | inr hne =>
      exfalso
      exact hno (nonHalting_carries_perpetual_engine n
        (fun K hK => hne ⟨K, hK⟩))

/-- **The vacuum has no gap:** one can never escape the cycle {1, 2}. -/
theorem vacuum_has_no_gap (d : Nat) : iter d 1 = 1 ∨ iter d 1 = 2 := by
  have h := cycle_absorbs 1 0 rfl d
  rwa [Nat.zero_add] at h

/-- **"A gap in the vacuum" = perpetual engine:** an orbit forever avoiding the vacuum
    {1, 2} (the second bottom, "another rank from the very bottom") carries a perpetual engine —
    a direct consequence of the central theorem. Finding a gap in the vacuum costs exactly
    a perpetual engine. -/
theorem second_bottom_carries_engine (n : Nat)
    (havoid : ∀ K : Nat, 3 ≤ iter K n) :
    ∃ j : Nat, NonDescendingOrbit (iter j n) ∧
      ∀ K : Nat, iter K (iter j n) ≠ 1 :=
  nonHalting_carries_perpetual_engine n
    (fun K hK => by have := havoid K; omega)

/-! ## REFUTATION OF THE UNIVERSAL LAW: n = 27 (the rope does NOT out-pull from the start)

The counting law in prefix form is FALSE. For the famously climbing trajectory n = 27
(peak 4616) 41 odd steps against 29 even ones lead to unity, and the difference
`evenCount − oddCount` in windows from position j = 0 never becomes
positive; the tail in the absorbing cycle 1→2→1 adds steps in pairs
(odd + even) and does not raise the difference. The core checks the prefix k ≤ 70
by computation (decide), the tail is closed by the cycle lemma. Consequence: the universal
form `∀ n ≥ 1, RopeCountingLaw n` is false. The decree that "may have
overpaid" (see Engine/CollatzFirstCause) overpaid into falsehood — the tripwire
fired, the fourth boundary is lifted. The conditional machinery (`window_budget`,
`reaches_one_of_countingLaw`) stays green and correct: the per-n law for
individual n (for example, `countingLaw_4`) is alive and entails halting. -/

/-- Additivity of the odd-step counter under window concatenation. -/
theorem oddCount_add (a b n : Nat) :
    oddCount (a + b) n = oddCount a n + oddCount b (iter a n) := by
  induction a generalizing n with
  | zero =>
      rw [Nat.zero_add]
      show oddCount b n = 0 + oddCount b n
      omega
  | succ a ih =>
      rw [Nat.succ_add]
      show oddCount (a + b) (T n) + (if n % 2 = 0 then 0 else 1) =
        (oddCount a (T n) + (if n % 2 = 0 then 0 else 1)) + oddCount b (iter a (T n))
      rw [ih (T n)]
      omega

/-- Additivity of the even-step counter under window concatenation. -/
theorem evenCount_add (a b n : Nat) :
    evenCount (a + b) n = evenCount a n + evenCount b (iter a n) := by
  induction a generalizing n with
  | zero =>
      rw [Nat.zero_add]
      show evenCount b n = 0 + evenCount b n
      omega
  | succ a ih =>
      rw [Nat.succ_add]
      show evenCount (a + b) (T n) + (if n % 2 = 0 then 1 else 0) =
        (evenCount a (T n) + (if n % 2 = 0 then 1 else 0)) + evenCount b (iter a (T n))
      rw [ih (T n)]
      omega

/-- **Cycle lemma:** in the vacuum 1→2→1 the rope never out-pulls — windows from 1
    give `even ≤ odd`, windows from 2 — `even ≤ odd + 1` (steps come in pairs). -/
theorem cycle_counts (m : Nat) :
    evenCount m 1 ≤ oddCount m 1 ∧ evenCount m 2 ≤ oddCount m 2 + 1 := by
  induction m with
  | zero => exact ⟨Nat.le_refl 0, Nat.zero_le _⟩
  | succ m ih =>
      refine ⟨?_, ?_⟩
      · show evenCount m 2 + 0 ≤ oddCount m 2 + 1
        have := ih.2
        omega
      · show (evenCount m 1 + 1) ≤ (oddCount m 1 + 0) + 1
        have := ih.1
        omega

set_option maxRecDepth 8000 in
/-- Prefix of the trajectory 27: up to k = 70 inclusive the rope never out-pulled
    (machine check by the core). -/
theorem counts_le_70_at_27 : ∀ k < 71, evenCount k 27 ≤ oddCount k 27 := by decide

set_option maxRecDepth 8000 in
/-- Result of the length-70 window from 27: 41 engine moves, 29 rope pulls, finishing at 1. -/
theorem counts_at_70_at_27 :
    oddCount 70 27 = 41 ∧ evenCount 70 27 = 29 ∧ iter 70 27 = 1 := by decide

/-- Tail: after entering the vacuum (k ≥ 70) the rope's deficit of −12 is not recovered. -/
theorem counts_ge_70_at_27 (k : Nat) (hk : 70 ≤ k) :
    evenCount k 27 ≤ oddCount k 27 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 70 + m := ⟨k - 70, by omega⟩
  have ho := oddCount_add 70 m 27
  have he := evenCount_add 70 m 27
  have h70 := counts_at_70_at_27
  rw [h70.2.2] at ho he
  have hc := (cycle_counts m).1
  omega

/-- **REFUTATION: `RopeCountingLaw 27` is false.** From position j = 0 (value 27 > 2)
    no window gives a rope surplus: the prefix by computation, the tail by the cycle
    lemma. -/
theorem not_ropeCountingLaw_27 : ¬ RopeCountingLaw 27 := by
  intro h
  obtain ⟨k, hk⟩ := h 0 (by decide)
  have hk' : oddCount k 27 < evenCount k 27 := hk
  by_cases hlt : k < 71
  · have := counts_le_70_at_27 k hlt
    omega
  · have := counts_ge_70_at_27 k (by omega)
    omega

/-- **THE UNIVERSAL FORM OF THE LAW IS REFUTED** — a forged refutation for
    the trilemma: `∀ n ≥ 1, RopeCountingLaw n` is false (witness n = 27). A decree
    boundary on this law is impossible. -/
theorem ropeLaw_universal_refuted :
    ¬ ∀ n : Nat, 1 ≤ n → RopeCountingLaw n :=
  fun h => not_ropeCountingLaw_27 (h 27 (by omega))

/-! ## Axiom audit (choice-free core: [propext, Quot.sound];
    the section "Refutation = engine" — the standard triple, em disclosed above) -/
#print axioms not_ropeCountingLaw_27
#print axioms ropeLaw_universal_refuted
#print axioms window_budget
#print axioms window_descends
#print axioms reaches_one_of_valueLaw
#print axioms reaches_one_of_countingLaw
#print axioms valueLaw_iff_reaches_one
#print axioms no_single_step_law
#print axioms countingLaw_4
#print axioms nonDescending_engine_never_loses
#print axioms nonDescendingOrbit_is_perpetual_engine
#print axioms no_nonDescendingOrbit_under_countingLaw
#print axioms plus_one_full_rank_only_at_one
#print axioms engine_confused_at_bottom
#print axioms exists_min_position
#print axioms nonHalting_carries_perpetual_engine
#print axioms collatz_iff_no_perpetual_tail
#print axioms vacuum_has_no_gap
#print axioms second_bottom_carries_engine

end EuclidsPath.Collatz.TugOfWar
