import Mathlib
import EuclidsPath.Engine.Step00GenealogicalOrnament

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Ordered exponent geometry — the graded layer over `Nat.factorization` (all green)

The parity barrier sees only `Ω(n) mod 2`.  This layer keeps the full graded state of a number —
the ordered exponent vector over `p_0 = 2, p_1 = 3, p_2 = 5, ...` and its derived grades — so that
downstream killed-boundary bookkeeping does not have to collapse primes and almost-primes into one
parity shadow.  Empirical compass (tools/LAWS_ordered_exponent.md): the graded correlation of the
two wings `MI(Ω(6m−1); Ω(6m+1)) > 0` survives every tested scale up to `10^12`, while the sign
projection of the same pair is flat — measured, not postulated (law L1).

## Contents (no `sorry`, no new axiom, nothing conditional)

* ordered index view: `primeIdx`, `expVec`, `idxSupport`;
* grades: `Ω` (mathlib `ArithmeticFunction.cardFactors`), `ω` (`cardDistinctFactors`),
  `powerDefect = Ω − ω` with `powerDefect_eq_zero_iff_squarefree`, `hullCard`/`gapDefect`;
* ordered prime blocks `orderedPrimeBlock i k = p_i ⋯ p_{i+k−1}`: squarefree, `Ω = ω = k`,
  both defects `0`, index support the interval `Ico i (i+k)`, sliding-window identity;
* the exchange operator `exchange p q n = n / p * q`: preserves `Ω`
  (`cardFactors_exchange`), hence is blind to the parity sign
  (`neg_one_pow_cardFactors_exchange`) while it does move the grades — the machine-visible
  mechanism of the parity barrier (witness `12 → 8`: `Ω` stays `3`, `powerDefect` jumps `1 → 2`);
* wing grade state of a center `c = 6m`: `wingSign`, `TwinGradeState`,
  `centerGradeDefect_eq_zero_iff` (the grade vector is REDUNDANT at its zero locus — recorded
  honestly, the extra coordinates only stratify non-twin centers);
* **the corrected draft bridge, green both ways**: `twinCenterZ_activeSieveSafe` and
  `activeSieveSafe_iff_twinCenterZ` — the safe hole of the ornament route is POINTWISE the twin
  predicate.  All content of the route is cofinal existence; this equivalence is the honest
  disclosure that no pointwise reformulation weakens the goal.

Bosonic/fermionic reading (occupation numbers vs squarefree exterior states) is the standard
primon-gas dictionary (Julia; Spector; Bost–Connes) — vocabulary, not new mathematics.
-/

namespace EuclidsPath
namespace OrderedExponent

open EuclidsPath.Residuals
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation.GenealogicalOrnament
open ArithmeticFunction
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

/-! ### The ordered index view -/

/-- Index of a prime in the ordered enumeration `p_0 = 2, p_1 = 3, p_2 = 5, ...`
    (the count of primes strictly below it). -/
def primeIdx (p : ℕ) : ℕ := Nat.count Nat.Prime p

/-- Ordered exponent vector `ν(n)`: the exponent of the `i`-th prime in `n`. -/
noncomputable def expVec (n i : ℕ) : ℕ := n.factorization (Nat.nth Nat.Prime i)

/-- Index support of `n`: the set of prime INDICES occurring in `n`. -/
def idxSupport (n : ℕ) : Finset ℕ := n.primeFactors.image primeIdx

private theorem nth_prime_injective : Function.Injective (Nat.nth Nat.Prime) :=
  (Nat.nth_strictMono Nat.infinite_setOf_prime).injective

/-- `nth ∘ primeIdx` is the identity on primes. -/
theorem nth_primeIdx {p : ℕ} (hp : p.Prime) : Nat.nth Nat.Prime (primeIdx p) = p :=
  Nat.nth_count hp

theorem primeIdx_injOn_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : primeIdx p = primeIdx q) : p = q := by
  have hp' : Nat.nth Nat.Prime (primeIdx p) = p := nth_primeIdx hp
  have hq' : Nat.nth Nat.Prime (primeIdx q) = q := nth_primeIdx hq
  rw [← hp', ← hq', h]

theorem primeIdx_nth (i : ℕ) : primeIdx (Nat.nth Nat.Prime i) = i :=
  Nat.count_nth_of_infinite Nat.infinite_setOf_prime i

/-- Membership in the index support is exactly a nonzero ordered exponent. -/
theorem mem_idxSupport_iff {n i : ℕ} : i ∈ idxSupport n ↔ expVec n i ≠ 0 := by
  constructor
  · intro hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [expVec, nth_primeIdx hpp]
    rw [← Nat.support_factorization] at hp
    exact Finsupp.mem_support_iff.mp hp
  · intro h
    have hmem : Nat.nth Nat.Prime i ∈ n.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr h
    exact Finset.mem_image.mpr ⟨_, hmem, primeIdx_nth i⟩

/-! ### The grades: `Ω`, `ω`, power defect -/

theorem omega_eq_card_primeFactors (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply]
  exact (List.card_toFinset _).symm

theorem omega_le_cardFactors (n : ℕ) : ω n ≤ Ω n := by
  rw [cardDistinctFactors_apply, cardFactors_apply]
  exact (List.dedup_sublist _).length_le

theorem primeIdx_injOn (n : ℕ) : Set.InjOn primeIdx n.primeFactors := fun p hp q hq h =>
  primeIdx_injOn_primes (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp))
    (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq)) h

/-- The index support has exactly `ω n` elements. -/
theorem card_idxSupport (n : ℕ) : (idxSupport n).card = ω n := by
  rw [idxSupport, Finset.card_image_of_injOn (primeIdx_injOn n), omega_eq_card_primeFactors]

/-- `Ω` as the total mass of the ordered exponent vector. -/
theorem cardFactors_eq_sum_expVec (n : ℕ) : Ω n = ∑ i ∈ idxSupport n, expVec n i := by
  have h0 : Ω n = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [cardFactors_eq_sum_factorization]; rfl
  rw [h0, idxSupport,
    Finset.sum_image fun p hp q hq h =>
      primeIdx_injOn_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq) h]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [expVec, nth_primeIdx (Nat.prime_of_mem_primeFactors hp)]

/-- Power defect `PowDef(n) = Ω(n) − ω(n)`: the exponent mass sitting in repeated powers
    (the "bosonic" vertical stacking of the primon-gas dictionary). -/
def powerDefect (n : ℕ) : ℕ := Ω n - ω n

/-- **Zero power defect is exactly squarefreeness** (`n ≠ 0`). -/
theorem powerDefect_eq_zero_iff_squarefree {n : ℕ} (hn : n ≠ 0) :
    powerDefect n = 0 ↔ Squarefree n := by
  rw [powerDefect]
  constructor
  · intro h
    have hle : Ω n ≤ ω n := Nat.sub_eq_zero_iff_le.mp h
    have heq : ω n = Ω n := le_antisymm (omega_le_cardFactors n) hle
    exact (cardDistinctFactors_eq_cardFactors_iff_squarefree hn).mp heq
  · intro h
    have heq : ω n = Ω n := (cardDistinctFactors_eq_cardFactors_iff_squarefree hn).mpr h
    rw [heq, Nat.sub_self]

/-! ### Gap defect: holes in the index hull -/

/-- Cardinality of the index hull `[min, max]` of the support (`0` when the support is empty). -/
def hullCard (n : ℕ) : ℕ :=
  if h : (idxSupport n).Nonempty
  then (idxSupport n).max' h + 1 - (idxSupport n).min' h
  else 0

/-- Gap defect `GapDef(n)`: how many index slots of the hull are NOT occupied.
    Numerically (law L4 of the ledger) this grade is dominated by the top prime index and its
    survival signal is confounded by the least factor, so it stays a LABEL of the grading and
    enters no named hypothesis. -/
def gapDefect (n : ℕ) : ℕ := hullCard n - ω n

theorem card_idxSupport_le_hullCard (n : ℕ) : (idxSupport n).card ≤ hullCard n := by
  by_cases h : (idxSupport n).Nonempty
  · rw [hullCard, dif_pos h]
    have hsub : idxSupport n ⊆
        Finset.Icc ((idxSupport n).min' h) ((idxSupport n).max' h) := fun i hi =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hi, Finset.le_max' _ _ hi⟩
    calc (idxSupport n).card ≤ _ := Finset.card_le_card hsub
    _ = _ := by rw [Nat.card_Icc]
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [hullCard, h]

theorem idxSupport_one : idxSupport 1 = ∅ := by simp [idxSupport]

theorem hullCard_one : hullCard 1 = 0 := by
  rw [hullCard, dif_neg]
  rw [idxSupport_one]
  exact Finset.not_nonempty_empty

theorem gapDefect_one : gapDefect 1 = 0 := by
  rw [gapDefect, hullCard_one]
  exact Nat.zero_sub _

theorem idxSupport_prime {p : ℕ} (hp : p.Prime) : idxSupport p = {primeIdx p} := by
  rw [idxSupport, hp.primeFactors, Finset.image_singleton]

/-- A prime atom has no holes. -/
theorem gapDefect_of_prime {p : ℕ} (hp : p.Prime) : gapDefect p = 0 := by
  have hs := idxSupport_prime hp
  rw [gapDefect, hullCard]
  simp only [hs, Finset.singleton_nonempty, dif_pos, Finset.max'_singleton,
    Finset.min'_singleton, cardDistinctFactors_apply_prime hp]
  omega

/-! ### Ordered prime blocks `B(i,k) = p_i ⋯ p_{i+k−1}` -/

/-- The `k` consecutive primes with indices `i, i+1, ..., i+k−1`. -/
noncomputable def blockPrimes (i k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun j => Nat.nth Nat.Prime (i + j)

/-- Ordered prime block `B(i,k) = p_i · p_{i+1} ⋯ p_{i+k−1}` — the canonical contiguous
    squarefree cell of the modulus space. -/
noncomputable def orderedPrimeBlock (i k : ℕ) : ℕ := ∏ p ∈ blockPrimes i k, p

theorem prime_of_mem_blockPrimes {i k p : ℕ} (hp : p ∈ blockPrimes i k) : p.Prime := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
  exact Nat.prime_nth_prime _

theorem blockPrimes_card (i k : ℕ) : (blockPrimes i k).card = k := by
  have hinj : Function.Injective fun j => Nat.nth Nat.Prime (i + j) := by
    intro a b h
    have := nth_prime_injective h
    omega
  rw [blockPrimes, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem orderedPrimeBlock_pos (i k : ℕ) : 0 < orderedPrimeBlock i k :=
  Finset.prod_pos fun p hp => (prime_of_mem_blockPrimes hp).pos

theorem orderedPrimeBlock_ne_zero (i k : ℕ) : orderedPrimeBlock i k ≠ 0 :=
  (orderedPrimeBlock_pos i k).ne'

theorem orderedPrimeBlock_squarefree (i k : ℕ) : Squarefree (orderedPrimeBlock i k) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hne
    have hpp := prime_of_mem_blockPrimes (Finset.mem_coe.mp hp)
    have hqq := prime_of_mem_blockPrimes (Finset.mem_coe.mp hq)
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hpp hqq).mpr hne)
  · intro p hp
    exact (prime_of_mem_blockPrimes hp).prime.squarefree

theorem primeFactors_orderedPrimeBlock (i k : ℕ) :
    (orderedPrimeBlock i k).primeFactors = blockPrimes i k := by
  rw [orderedPrimeBlock]
  exact Nat.primeFactors_prod fun p hp => prime_of_mem_blockPrimes hp

/-- Blocks sit in the fermionic stratum: `ω(B(i,k)) = k`. -/
theorem omega_orderedPrimeBlock (i k : ℕ) : ω (orderedPrimeBlock i k) = k := by
  rw [omega_eq_card_primeFactors, primeFactors_orderedPrimeBlock, blockPrimes_card]

/-- `Ω(B(i,k)) = k`. -/
theorem cardFactors_orderedPrimeBlock (i k : ℕ) : Ω (orderedPrimeBlock i k) = k := by
  have h := (cardDistinctFactors_eq_cardFactors_iff_squarefree
    (orderedPrimeBlock_ne_zero i k)).mpr (orderedPrimeBlock_squarefree i k)
  rw [← h, omega_orderedPrimeBlock]

/-- Blocks carry no power defect. -/
theorem powerDefect_orderedPrimeBlock (i k : ℕ) : powerDefect (orderedPrimeBlock i k) = 0 := by
  rw [powerDefect, cardFactors_orderedPrimeBlock, omega_orderedPrimeBlock, Nat.sub_self]

/-- The index support of a block is a contiguous interval. -/
theorem idxSupport_orderedPrimeBlock (i k : ℕ) :
    idxSupport (orderedPrimeBlock i k) = Finset.Ico i (i + k) := by
  rw [idxSupport, primeFactors_orderedPrimeBlock, blockPrimes, Finset.image_image]
  ext j
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico, Function.comp_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [primeIdx_nth]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨j - i, by omega, by rw [primeIdx_nth]; omega⟩

/-- Blocks have no holes: `GapDef(B(i,k)) = 0`. -/
theorem gapDefect_orderedPrimeBlock (i k : ℕ) : gapDefect (orderedPrimeBlock i k) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : orderedPrimeBlock i 0 = 1 := by
      rw [orderedPrimeBlock, blockPrimes]
      simp
    rw [h1, gapDefect_one]
  · rw [gapDefect, hullCard]
    have hs := idxSupport_orderedPrimeBlock i k
    have hne : (idxSupport (orderedPrimeBlock i k)).Nonempty := by
      rw [hs, Finset.nonempty_Ico]
      omega
    rw [dif_pos hne]
    have hmin : (idxSupport (orderedPrimeBlock i k)).min' hne = i := by
      apply le_antisymm
      · exact Finset.min'_le _ _ (by rw [hs]; exact Finset.mem_Ico.mpr ⟨le_refl i, by omega⟩)
      · refine Finset.le_min' _ _ _ fun j hj => ?_
        rw [hs] at hj
        exact (Finset.mem_Ico.mp hj).1
    have hmax : (idxSupport (orderedPrimeBlock i k)).max' hne = i + k - 1 := by
      apply le_antisymm
      · refine Finset.max'_le _ _ _ fun j hj => ?_
        rw [hs] at hj
        have := (Finset.mem_Ico.mp hj).2
        omega
      · exact Finset.le_max' _ _ (by rw [hs]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    rw [hmin, hmax, omega_orderedPrimeBlock]
    omega

/-- Range form of the block (for sliding). -/
theorem orderedPrimeBlock_eq_prod_range (i k : ℕ) :
    orderedPrimeBlock i k = ∏ j ∈ Finset.range k, Nat.nth Nat.Prime (i + j) := by
  rw [orderedPrimeBlock, blockPrimes]
  exact Finset.prod_image fun a _ b _ h => by
    have := nth_prime_injective h
    omega

/-- **Sliding window**: `B(i,k) · p_{i+k} = p_i · B(i+1,k)` — the multiplicative form of the
    exchange `X_{p_i → p_{i+k}}` acting on the modulus space. -/
theorem orderedPrimeBlock_slide (i k : ℕ) :
    orderedPrimeBlock i k * Nat.nth Nat.Prime (i + k)
      = Nat.nth Nat.Prime i * orderedPrimeBlock (i + 1) k := by
  rw [orderedPrimeBlock_eq_prod_range, orderedPrimeBlock_eq_prod_range,
    ← Finset.prod_range_succ (fun j => Nat.nth Nat.Prime (i + j)) k]
  rw [Finset.prod_range_succ' (fun j => Nat.nth Nat.Prime (i + j)) k]
  rw [Nat.add_zero, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  omega

/-! ### The exchange operator and the machine-visible parity mechanism -/

/-- Exchange `X_{p → q}`: move one exponent unit from direction `p` to direction `q`. -/
def exchange (p q n : ℕ) : ℕ := n / p * q

/-- **Exchange preserves the total degree `Ω`.** -/
theorem cardFactors_exchange {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : p ∣ n) (hn : n ≠ 0) : Ω (exchange p q n) = Ω n := by
  obtain ⟨d, rfl⟩ := hpn
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hn
  rw [exchange, Nat.mul_div_cancel_left d hp.pos,
    cardFactors_mul hd hq.ne_zero, cardFactors_mul hp.ne_zero hd,
    cardFactors_apply_prime hp, cardFactors_apply_prime hq]
  omega

/-- **The parity barrier, machine-visible**: exchanges cannot change the Liouville sign
    `(−1)^Ω`.  Only the finer grades (`ω`, `powerDefect`, `gapDefect`) distinguish a prime from
    an odd-`Ω` almost-prime — which is why this layer keeps them. -/
theorem neg_one_pow_cardFactors_exchange {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : p ∣ n) (hn : n ≠ 0) :
    ((-1 : ℤ)) ^ Ω (exchange p q n) = (-1 : ℤ) ^ Ω n := by
  rw [cardFactors_exchange hp hq hpn hn]

/-! #### Concrete witness: `X_{3→2}(12) = 8` keeps `Ω = 3` but moves the grades -/

theorem exchange_three_two_twelve : exchange 3 2 12 = 8 := by norm_num [exchange]

theorem cardFactors_twelve : Ω (12 : ℕ) = 3 := by
  have h : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h, cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_apply_prime_pow Nat.prime_two, cardFactors_apply_prime Nat.prime_three]

theorem cardFactors_eight : Ω (8 : ℕ) = 3 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, cardFactors_apply_prime_pow Nat.prime_two]

theorem omega_twelve : ω (12 : ℕ) = 2 := by
  have h : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h, cardDistinctFactors_mul (by norm_num),
    cardDistinctFactors_apply_prime_pow Nat.prime_two (by norm_num),
    cardDistinctFactors_apply_prime Nat.prime_three]

theorem omega_eight : ω (8 : ℕ) = 1 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, cardDistinctFactors_apply_prime_pow Nat.prime_two (by norm_num)]

/-- The witness assembled: the exchange `12 → 8` is `Ω`-invisible and grade-visible. -/
theorem exchange_moves_grades :
    Ω (exchange 3 2 12) = Ω (12 : ℕ) ∧ powerDefect (exchange 3 2 12) ≠ powerDefect 12 := by
  rw [exchange_three_two_twelve]
  refine ⟨by rw [cardFactors_eight, cardFactors_twelve], ?_⟩
  rw [powerDefect, powerDefect, cardFactors_eight, omega_eight, cardFactors_twelve, omega_twelve]
  norm_num

/-! ### Wing grade state of a center `c = 6m` -/

/-- Liouville sign of the wing pair — the parity shadow the barrier sees. -/
def wingSign (m : ℕ) : ℤ := (-1) ^ (Ω (6 * m - 1) + Ω (6 * m + 1))

/-- The two oscillating engines never land on zero. -/
theorem wingSign_ne_zero (m : ℕ) : wingSign m ≠ 0 := by
  rw [wingSign]
  exact pow_ne_zero _ (by norm_num)

theorem wingSign_of_twin {m : ℕ} (h : TwinCenterZ m) : wingSign m = 1 := by
  rw [wingSign, cardFactors_eq_one_iff_prime.mpr h.1, cardFactors_eq_one_iff_prime.mpr h.2]
  norm_num

/-- The draft's fermionic twin state: both wings in the `Λ¹` sector. -/
structure TwinGradeState (m : ℕ) : Prop where
  left_line : Ω (6 * m - 1) = 1
  right_line : Ω (6 * m + 1) = 1

theorem twinGradeState_iff_twinCenterZ (m : ℕ) : TwinGradeState m ↔ TwinCenterZ m :=
  ⟨fun h => ⟨cardFactors_eq_one_iff_prime.mp h.left_line,
    cardFactors_eq_one_iff_prime.mp h.right_line⟩,
   fun h => ⟨cardFactors_eq_one_iff_prime.mpr h.1, cardFactors_eq_one_iff_prime.mpr h.2⟩⟩

/-- Scalar grade defect of one wing: distance from the prime atom `Λ¹`. -/
def wingGradeDefect (n : ℕ) : ℕ := (Ω n - 1) + powerDefect n + gapDefect n

/-- Scalar grade defect of a center: both wings summed. -/
def centerGradeDefect (m : ℕ) : ℕ := wingGradeDefect (6 * m - 1) + wingGradeDefect (6 * m + 1)

theorem wingGradeDefect_eq_zero_of_prime {p : ℕ} (hp : p.Prime) : wingGradeDefect p = 0 := by
  have h1 : Ω p = 1 := cardFactors_apply_prime hp
  have h2 : ω p = 1 := cardDistinctFactors_apply_prime hp
  rw [wingGradeDefect, powerDefect, h1, h2, gapDefect_of_prime hp]

/-- **Redundancy at the zero locus** (honesty lemma): the six-component defect vector vanishes
    exactly on twins — `Ω = 1` already forces both `powerDefect = 0` and `gapDefect = 0`, so the
    extra grades carry content ONLY on non-twin centers (they stratify the failure set). -/
theorem centerGradeDefect_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) :
    centerGradeDefect m = 0 ↔ TwinCenterZ m := by
  constructor
  · intro h
    have hzero : Ω (6 * m - 1) - 1 = 0 ∧ Ω (6 * m + 1) - 1 = 0 := by
      rw [centerGradeDefect, wingGradeDefect, wingGradeDefect] at h
      omega
    have hposL : 0 < Ω (6 * m - 1) := cardFactors_pos_iff_one_lt.mpr (by omega)
    have hposR : 0 < Ω (6 * m + 1) := cardFactors_pos_iff_one_lt.mpr (by omega)
    exact ⟨cardFactors_eq_one_iff_prime.mp (by omega),
      cardFactors_eq_one_iff_prime.mp (by omega)⟩
  · intro h
    rw [centerGradeDefect, wingGradeDefect_eq_zero_of_prime h.1,
      wingGradeDefect_eq_zero_of_prime h.2]

/-! ### The corrected bridge: safe hole ⟺ twin, GREEN BOTH WAYS -/

/-- **The converse of `safeHole_implies_twin` (new, green).**  If both wings are prime then no
    clock `k ∈ [2, √(6m+1)]` divides either wing: a divisor of a prime wing equals the wing
    itself, but both wings exceed `√(6m+1)`. -/
theorem twinCenterZ_activeSieveSafe {m : ℕ} (hm : 1 ≤ m) (h : TwinCenterZ m) :
    ActiveSieveSafe m := by
  intro k hk2 hkle
  constructor
  · intro hdvd
    rcases h.1.eq_one_or_self_of_dvd k hdvd with rfl | rfl
    · omega
    · have hlt : Nat.sqrt (6 * m + 1) < 6 * m - 1 := by
        rw [Nat.sqrt_lt]
        obtain ⟨a, ha⟩ : ∃ a, 6 * m - 1 = a + 5 := ⟨6 * m - 6, by omega⟩
        rw [ha, show 6 * m + 1 = a + 7 by omega]
        nlinarith
      omega
  · intro hdvd
    rcases h.2.eq_one_or_self_of_dvd k hdvd with rfl | rfl
    · omega
    · have hlt : Nat.sqrt (6 * m + 1) < 6 * m + 1 := Nat.sqrt_lt_self (by omega)
      omega

/-- **AUDIT (green, both directions): the safe hole is POINTWISE the twin predicate.**
    All content of the ornament route lives in cofinal existence, not in any pointwise
    reformulation — machine-checked disclosure. -/
theorem activeSieveSafe_iff_twinCenterZ {m : ℕ} (hm : 1 ≤ m) :
    ActiveSieveSafe m ↔ TwinCenterZ m :=
  ⟨safeHole_implies_twin hm, twinCenterZ_activeSieveSafe hm⟩

/-- The graded twin state is likewise pointwise-equivalent to the safe hole. -/
theorem twinGradeState_iff_activeSieveSafe {m : ℕ} (hm : 1 ≤ m) :
    TwinGradeState m ↔ ActiveSieveSafe m :=
  (twinGradeState_iff_twinCenterZ m).trans (activeSieveSafe_iff_twinCenterZ hm).symm

end OrderedExponent
end EuclidsPath
