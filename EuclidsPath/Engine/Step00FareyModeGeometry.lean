import Mathlib
import EuclidsPath.Engine.Step00StrikeFourier

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The Farey geometry of the mode frequencies — the strict exact relation at every scale

Origin: the author's directive of this pass.  "Infinitely subdividing a sphere with a
relation strict, exact, at scale."  The honest home of that image inside the program: the
level-1 mode frequencies of the strike-Fourier layer (`Step00StrikeFourier`) are the Farey
fractions `j/q` over the clocks `q ∈ clocks A`, `1 ≤ j ≤ q - 1`, living on the frequency
circle (the "sphere" is `ℚ/ℤ`); and the strict exact relation holding at every scale is
UNIMODULARITY — `j·q' - j'·q = ±1`, Bezout's identity, which is Ford-circle tangency in
classical dress — together with CRT injectivity of the cross-term classes.

The honest dictionary, term by term:

* **the sphere** = the frequency circle `ℚ/ℤ`: every level-1 mode of the engine
  decomposition (`modeWave q j m`, frequency `j/q`) sits at the rational point `j/q`;
  everything below stays in exact `ℚ`/`ℤ` arithmetic — no analysis, no `AddCircle`, the
  circle metric is hand-rolled on `ℚ` where needed (`level1_circle_spacing`);
* **subdivision at scale** = the clock Farey fractions at scale `A`:
  `level1_freq_injective` (all level-1 frequencies are DISTINCT points),
  `level1_spacing` (any two are at least `1/(q·q')` apart), `level1_spacing_scale`
  (hence never closer than `1/A²`), `level1_spacing_wraparound` (the same bound against
  EVERY integer translate — the true distance-to-nearest-integer form);
* **the strict exact relation** = unimodularity: `farey_adjacent_exists_unique` — for
  every ordered pair of distinct clocks there is EXACTLY ONE mode pair `(j, j')` with
  `j·q' - j'·q = 1` (Bezout existence, range-window uniqueness), the machine form of
  Ford-circle tangency / Farey adjacency, and `farey_adjacent_exists_unique_neg` for the
  mirror relation `= -1`;
* **the load-bearing consequence** = `crossterm_class_bijection`: the cross-term map
  `(j, j') ↦ (j·q' - j'·q) mod (q·q')` is a BIJECTION from the mode box
  `[1,q-1] × [1,q'-1]` onto the `(q-1)(q'-1)` admissible classes (those vanishing at
  neither clock) — CRT injectivity plus explicit surjectivity.  Every admissible Farey
  class occurs EXACTLY ONCE per ordered clock pair: this replaces sorting arguments in
  the large-sieve v0 route and organizes the dispersion cross-terms into `m`-classes.

## DISCLOSURE (read this before anything else)

The Ford/sphere language is TRANSLATION, not new mathematics: the exact content of every
theorem below is Bezout/CRT arithmetic over `ℤ` and `ℚ`; the classical names (Ford
circles, Farey adjacency, mediants) are dictionary entries only.  One entry of the
directive is positively KILLED rather than translated: the mediant/Apollonian subdivision
(the Descartes circle-packing picture) does NOT act on the clock set — the mediant of
`j/q` and `j'/q'` has denominator `q + q'`, which is EVEN (a sum of two odd primes) and
hence NEVER a clock at any scale (`mediant_denom_not_clock`).  The Apollonian/Descartes
angle is closed as vocabulary, at zero cost, before anyone mistakes it for a program
front.

Frame status: INFRASTRUCTURE.  This module proves exact finite statements feeding the
dispersion pass — the spacing input of the large-sieve route (`level1_spacing`,
`level1_spacing_scale`) and the `m`-class organization of the dispersion identity's
cross-terms (`crossterm_class_bijection`).  No wall contact is claimed anywhere here: no
estimate, no `O(·)`, no unproven bound; the parity wall is neither touched nor
repackaged.
-/

namespace EuclidsPath
namespace FareyModeGeometry

open EuclidsPath.StrikeFourier

/-! ### Part A — the cross-term numerator

The single integer that controls everything below: for an ordered clock pair `(q, q')`
and mode labels `(j, j')`, the cross-term numerator `j·q' - j'·q`.  The difference of the
two mode frequencies is exactly this numerator over `q·q'` (`freq_sub_eq`); the Farey
class of the pair is its residue mod `q·q'` (`crossClass`); unimodularity is the equation
`= ±1`. -/

/-- The cross-term numerator of the ordered clock pair `(q, q')` at mode labels
    `(j, j')`: the integer `j·q' - j'·q`.  Numerator of `j/q - j'/q'` over the common
    denominator `q·q'`; the object whose residue class organizes the dispersion
    cross-terms and whose value `±1` is Farey adjacency. -/
def crossNum (q q' j j' : ℕ) : ℤ := (j : ℤ) * q' - (j' : ℤ) * q

/-- An integer multiple of `a > 0` lying strictly between `-a` and `a` is zero.  The
    range-window step used by every uniqueness argument in this module. -/
private theorem eq_zero_of_dvd_of_abs_lt {a d : ℤ} (ha : 0 < a) (hdvd : a ∣ d)
    (h1 : -a < d) (h2 : d < a) : d = 0 := by
  obtain ⟨c, rfl⟩ := hdvd
  rcases lt_trichotomy c 0 with hc | hc | hc
  · exfalso
    have h3 : a * c ≤ a * (-1) := mul_le_mul_of_nonneg_left (by omega) ha.le
    linarith
  · rw [hc, mul_zero]
  · exfalso
    have h3 : a * 1 ≤ a * c := mul_le_mul_of_nonneg_left (by omega) ha.le
    linarith

/-- A clock never divides a cross-term numerator against a DIFFERENT clock: from
    `q ∣ j·q' - j'·q` follows `q ∣ j·q'`, and `q` (prime) divides neither `j`
    (a nonzero mode label below `q`) nor `q'` (a different prime). -/
theorem crossNum_not_dvd_left {q q' j j' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hne : q ≠ q') (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) :
    ¬ (q : ℤ) ∣ crossNum q q' j j' := by
  intro hdvd
  have h2q := hq.two_le
  have hjq' : (q : ℤ) ∣ (j : ℤ) * q' := by
    have h2 : (q : ℤ) ∣ (j' : ℤ) * q := dvd_mul_left (q : ℤ) (j' : ℤ)
    have h3 := dvd_add hdvd h2
    have he : crossNum q q' j j' + (j' : ℤ) * q = (j : ℤ) * q' := by
      unfold crossNum; ring
    rwa [he] at h3
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hjq' with h | h
  · have hd : q ∣ j := Int.natCast_dvd_natCast.mp h
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : q ∣ q' := Int.natCast_dvd_natCast.mp h
    exact hne ((Nat.prime_dvd_prime_iff_eq hq hq').mp hd)

/-- Mirror of `crossNum_not_dvd_left` for the second clock. -/
theorem crossNum_not_dvd_right {q q' j j' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hne : q ≠ q') (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1) :
    ¬ (q' : ℤ) ∣ crossNum q q' j j' := by
  intro hdvd
  have h2q' := hq'.two_le
  have hj'q : (q' : ℤ) ∣ (j' : ℤ) * q := by
    have h2 : (q' : ℤ) ∣ (j : ℤ) * q' := dvd_mul_left (q' : ℤ) (j : ℤ)
    have h3 := dvd_sub h2 hdvd
    have he : (j : ℤ) * q' - crossNum q q' j j' = (j' : ℤ) * q := by
      unfold crossNum; ring
    rwa [he] at h3
  rcases (Nat.prime_iff_prime_int.mp hq').dvd_mul.mp hj'q with h | h
  · have hd : q' ∣ j' := Int.natCast_dvd_natCast.mp h
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : q' ∣ q := Int.natCast_dvd_natCast.mp h
    exact hne (((Nat.prime_dvd_prime_iff_eq hq' hq).mp hd).symm)

/-- **The nonvanishing kernel of the spacing law**: for a genuine pair of level-1 modes
    (`(q, j) ≠ (q', j')`), the cross-term numerator misses EVERY multiple of `q·q'`.
    Same clock: the numerator is `(j - j')·q` with `0 < |j - j'| < q`.  Distinct clocks:
    `q` does not divide the numerator at all (`crossNum_not_dvd_left`), while it divides
    every multiple of `q·q'`. -/
theorem crossNum_shift_ne_zero {q q' j j' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) (n : ℤ) :
    crossNum q q' j j' - n * ((q : ℤ) * q') ≠ 0 := by
  have h2q := hq.two_le
  have h2q' := hq'.two_le
  rcases eq_or_ne q q' with rfl | hne
  · have hjj : j ≠ j' := fun h => hpair (by rw [h])
    intro h0
    have hfact : crossNum q q j j' - n * ((q : ℤ) * q) = ((j : ℤ) - j' - n * q) * q := by
      unfold crossNum; ring
    rw [hfact, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · have hd : (q : ℤ) ∣ (j : ℤ) - j' := ⟨n, by linarith⟩
      have hz : (j : ℤ) - j' = 0 :=
        eq_zero_of_dvd_of_abs_lt (by exact_mod_cast hq.pos) hd (by omega) (by omega)
      omega
    · have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.pos.ne'
      exact hq0 h0
  · intro h0
    have hdvd : (q : ℤ) ∣ crossNum q q' j j' := by
      refine ⟨n * q', ?_⟩
      linarith
    exact crossNum_not_dvd_left hq hq' hne hj1 hjq hdvd

/-! ### Part B — the level-1 frequency geometry (spacing on the circle)

The frequencies `j/q` as points of `ℚ`: distinctness, the `1/(q·q')` spacing, the `1/A²`
floor, and the wraparound (distance-to-nearest-integer) form.  These are the exact
spacing inputs of the large-sieve route: `δ = 1/A²` well-spacedness of the level-1 mode
system. -/

/-- The difference of two mode frequencies is the cross-term numerator over `q·q'`. -/
theorem freq_sub_eq {q q' : ℕ} (j j' : ℕ) (hq0 : 0 < q) (hq'0 : 0 < q') :
    (j : ℚ) / q - (j' : ℚ) / q' = (crossNum q q' j j' : ℚ) / ((q : ℚ) * q') := by
  have h1 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq0.ne'
  have h2 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq'0.ne'
  rw [div_sub_div _ _ h1 h2]
  unfold crossNum
  push_cast
  ring

/-- A level-1 frequency is strictly positive. -/
theorem freq_pos {A q j : ℕ} (hq : q ∈ clocks A) (hj1 : 1 ≤ j) : 0 < (j : ℚ) / q := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  exact div_pos (by exact_mod_cast hj1) (by exact_mod_cast hp.pos)

/-- A level-1 frequency is strictly below `1`. -/
theorem freq_lt_one {A q j : ℕ} (hq : q ∈ clocks A) (hjq : j ≤ q - 1) :
    (j : ℚ) / q < 1 := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hp.pos
  rw [div_lt_one hq0]
  exact_mod_cast (by omega : j < q)

/-- **The wraparound spacing law (distance to EVERY integer translate).**  For a genuine
    pair of level-1 modes, `|j/q - j'/q' - n| ≥ 1/(q·q')` for every `n : ℤ` — the
    distance-to-nearest-integer (circle metric) form of the spacing, proved entirely in
    `ℚ`: the shifted difference is a nonzero integer (`crossNum_shift_ne_zero`) over the
    denominator `q·q'`. -/
theorem level1_spacing_wraparound {A q q' j j' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) (n : ℤ) :
    1 / ((q : ℚ) * q') ≤ |(j : ℚ) / q - (j' : ℚ) / q' - n| := by
  obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', hA'⟩ := mem_clocks.mp hq'
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hp.pos
  have hq'0 : (0 : ℚ) < q' := by exact_mod_cast hp'.pos
  have hden : (0 : ℚ) < (q : ℚ) * q' := mul_pos hq0 hq'0
  have hnum := crossNum_shift_ne_zero hp hp' hj1 hjq hj'1 hj'q' hpair n
  have hdelta : (j : ℚ) / q - (j' : ℚ) / q' - (n : ℚ)
      = ((crossNum q q' j j' - n * ((q : ℤ) * q') : ℤ) : ℚ) / ((q : ℚ) * q') := by
    rw [freq_sub_eq j j' hp.pos hp'.pos]
    push_cast
    rw [sub_div, mul_div_cancel_right₀ _ hden.ne']
  rw [hdelta, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
  exact_mod_cast Int.one_le_abs hnum

/-- **The pairwise spacing law.**  Two distinct level-1 mode frequencies differ by at
    least `1/(q·q')`: the `n = 0` slice of `level1_spacing_wraparound`. -/
theorem level1_spacing {A q q' j j' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) :
    1 / ((q : ℚ) * q') ≤ |(j : ℚ) / q - (j' : ℚ) / q'| := by
  have h := level1_spacing_wraparound hq hq' hj1 hjq hj'1 hj'q' hpair 0
  simpa using h

/-- **The `1/A²` floor** — the spacing constant of the whole level-1 system at scale `A`
    (the direct input `δ = 1/A²` of the large-sieve route): both clocks are at most `A`,
    so `1/(q·q') ≥ 1/A²`. -/
theorem level1_spacing_scale {A q q' j j' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) :
    1 / ((A : ℚ) * A) ≤ |(j : ℚ) / q - (j' : ℚ) / q'| := by
  obtain ⟨hp, h5, hA⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', hA'⟩ := mem_clocks.mp hq'
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hp.pos
  have hq'0 : (0 : ℚ) < q' := by exact_mod_cast hp'.pos
  have hle : (q : ℚ) * q' ≤ (A : ℚ) * A := by
    have h1 : (q : ℚ) ≤ A := by exact_mod_cast hA
    have h2 : (q' : ℚ) ≤ A := by exact_mod_cast hA'
    exact mul_le_mul h1 h2 hq'0.le (le_trans hq0.le h1)
  calc 1 / ((A : ℚ) * A) ≤ 1 / ((q : ℚ) * q') :=
        one_div_le_one_div_of_le (mul_pos hq0 hq'0) hle
    _ ≤ _ := level1_spacing hq hq' hj1 hjq hj'1 hj'q' hpair

/-- **Distinctness of the level-1 frequencies.**  The map `(q, j) ↦ j/q` is injective on
    the level-1 mode system: distinct labels give distinct rational points.  Same clock:
    distinct numerators.  Distinct clocks: `q ∣ j·q'` would force `q ∣ j` (prime `q`,
    `q ∤ q'`), impossible for `1 ≤ j < q`.  Derived here from the spacing law: equal
    frequencies would violate the strictly positive gap. -/
theorem level1_freq_injective {A q q' j j' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) :
    (j : ℚ) / q ≠ (j' : ℚ) / q' := by
  intro heq
  have h := level1_spacing hq hq' hj1 hjq hj'1 hj'q' hpair
  rw [heq, sub_self, abs_zero] at h
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hp.pos
  have hq'0 : (0 : ℚ) < q' := by exact_mod_cast hp'.pos
  have hpos : (0 : ℚ) < 1 / ((q : ℚ) * q') := one_div_pos.mpr (mul_pos hq0 hq'0)
  linarith

/-- **The circle-metric spacing.**  Both frequencies lie in `(0, 1)`, so their circle
    distance is `min |Δ| (1 - |Δ|)`; both branches carry the same `1/(q·q')` bound — the
    `|Δ|` branch is `level1_spacing`, the complement branch is the wraparound bound at
    the translate `n = ±1`.  The "sphere" reading of the spacing law, delivered without
    leaving `ℚ`. -/
theorem level1_circle_spacing {A q q' j j' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A)
    (hj1 : 1 ≤ j) (hjq : j ≤ q - 1) (hj'1 : 1 ≤ j') (hj'q' : j' ≤ q' - 1)
    (hpair : (q, j) ≠ (q', j')) :
    1 / ((q : ℚ) * q') ≤ min |(j : ℚ) / q - (j' : ℚ) / q'|
      (1 - |(j : ℚ) / q - (j' : ℚ) / q'|) := by
  have hf1 := freq_pos hq hj1
  have hf2 := freq_lt_one hq hjq
  have hf'1 := freq_pos hq' hj'1
  have hf'2 := freq_lt_one hq' hj'q'
  refine le_min (level1_spacing hq hq' hj1 hjq hj'1 hj'q' hpair) ?_
  rcases le_or_gt 0 ((j : ℚ) / q - (j' : ℚ) / q') with hsign | hsign
  · have h1 := level1_spacing_wraparound hq hq' hj1 hjq hj'1 hj'q' hpair 1
    push_cast at h1
    rw [abs_of_nonpos (by linarith : (j : ℚ) / q - (j' : ℚ) / q' - 1 ≤ 0)] at h1
    rw [abs_of_nonneg hsign]
    linarith
  · have h1 := level1_spacing_wraparound hq hq' hj1 hjq hj'1 hj'q' hpair (-1)
    push_cast at h1
    rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ (j : ℚ) / q - (j' : ℚ) / q' - (-1))] at h1
    rw [abs_of_neg hsign]
    linarith

/-! ### Part C — Farey adjacency: the unimodular pair exists and is unique

Bezout delivered in the mode window.  The congruence-solving core (`exists_mode_solving`)
inverts one clock modulo the other inside the field `ZMod q`; the range window
`[1, q-1] × [1, q'-1]` then pins the solution exactly. -/

/-- Congruence-solving core: for prime `q` and `t, s` both nonzero mod `q`, there is a
    mode label `j ∈ [1, q-1]` with `j·t ≡ s (mod q)` — division in the field `ZMod q`,
    with the representative pulled back to the fundamental range. -/
private theorem exists_mode_solving {q : ℕ} (hp : q.Prime) {t s : ℤ}
    (ht : ((t : ℤ) : ZMod q) ≠ 0) (hs : ((s : ℤ) : ZMod q) ≠ 0) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ q - 1 ∧ (q : ℤ) ∣ (j : ℤ) * t - s := by
  haveI : Fact q.Prime := ⟨hp⟩
  haveI : NeZero q := ⟨hp.pos.ne'⟩
  obtain ⟨a, hane, hadef⟩ :
      ∃ a : ZMod q, a ≠ 0 ∧ a * ((t : ℤ) : ZMod q) = ((s : ℤ) : ZMod q) := by
    refine ⟨((s : ℤ) : ZMod q) * (((t : ℤ) : ZMod q))⁻¹,
      mul_ne_zero hs (inv_ne_zero ht), ?_⟩
    rw [mul_assoc, inv_mul_cancel₀ ht, mul_one]
  refine ⟨a.val, ?_, ?_, ?_⟩
  · have h0 : a.val ≠ 0 := fun h => hane ((ZMod.val_eq_zero a).mp h)
    omega
  · have := ZMod.val_lt a
    omega
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact sub_eq_zero.mpr hadef

/-- A different prime is nonzero as an element of `ZMod q`. -/
private theorem natCast_prime_ne_zero {q q' : ℕ} (hp : q.Prime) (hp' : q'.Prime)
    (hne : q ≠ q') : ((q' : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp hp').mp hd)

/-- **Farey adjacency / Ford tangency, machine form (`ε = 1`).**  For distinct clocks
    `q ≠ q'` there is EXACTLY ONE mode pair `(j, j')` in the level-1 box
    `[1, q-1] × [1, q'-1]` with `j·q' - j'·q = 1`.  Existence: invert `q'` mod `q`
    (Bezout through `ZMod q`), solve the mirror congruence mod `q'`, and observe that a
    number `≡ 1 (mod q·q')` trapped in `(-q·q', q·q')` IS `1`.  Uniqueness: two solutions
    differ by a `(q, q')`-multiple, expelled by the range window.  This is the "strict,
    exact relation at scale" of the directive: the unimodular relation between adjacent
    Farey fractions, alias tangency of the Ford circles at `j/q` and `j'/q'`. -/
theorem farey_adjacent_exists_unique {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    ∃! p : ℕ × ℕ, (1 ≤ p.1 ∧ p.1 ≤ q - 1) ∧ (1 ≤ p.2 ∧ p.2 ≤ q' - 1) ∧
      (p.1 : ℤ) * q' - (p.2 : ℤ) * q = 1 := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  haveI : Fact (1 < q) := ⟨by omega⟩
  haveI : Fact (1 < q') := ⟨by omega⟩
  have h5Z : (5 : ℤ) ≤ (q : ℤ) := by exact_mod_cast h5
  have h5'Z : (5 : ℤ) ≤ (q' : ℤ) := by exact_mod_cast h5'
  -- Existence: solve `j·q' ≡ 1 (mod q)` and `j'·q ≡ -1 (mod q')`, then trap the value.
  obtain ⟨j, hj1, hjq, hdq⟩ := exists_mode_solving hp (t := ((q' : ℕ) : ℤ)) (s := 1)
    (by push_cast; exact natCast_prime_ne_zero hp hp' hne)
    (by rw [Int.cast_one]; exact one_ne_zero)
  obtain ⟨j', hj'1, hj'q', hdq'⟩ := exists_mode_solving hp' (t := ((q : ℕ) : ℤ)) (s := -1)
    (by push_cast; exact natCast_prime_ne_zero hp' hp hne.symm)
    (by rw [Int.cast_neg, Int.cast_one]; exact neg_ne_zero.mpr one_ne_zero)
  have hdq'' : (q' : ℤ) ∣ (j' : ℤ) * q + 1 := by
    have he : (j' : ℤ) * q + 1 = (j' : ℤ) * q - (-1) := by ring
    rw [he]; exact hdq'
  have hcop : IsCoprime (q : ℤ) (q' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hp').mpr hne)
  have hd1 : (q : ℤ) ∣ ((j : ℤ) * q' - (j' : ℤ) * q) - 1 := by
    have he : ((j : ℤ) * q' - (j' : ℤ) * q) - 1 = ((j : ℤ) * q' - 1) - (j' : ℤ) * q := by
      ring
    rw [he]
    exact dvd_sub hdq (dvd_mul_left _ _)
  have hd2 : (q' : ℤ) ∣ ((j : ℤ) * q' - (j' : ℤ) * q) - 1 := by
    have he : ((j : ℤ) * q' - (j' : ℤ) * q) - 1 = (j : ℤ) * q' - ((j' : ℤ) * q + 1) := by
      ring
    rw [he]
    exact dvd_sub (dvd_mul_left _ _) hdq''
  have hdvd : (q : ℤ) * q' ∣ ((j : ℤ) * q' - (j' : ℤ) * q) - 1 := hcop.mul_dvd hd1 hd2
  have hb1 : (j : ℤ) * q' ≤ ((q : ℤ) - 1) * q' :=
    mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hb2 : (1 : ℤ) * q ≤ (j' : ℤ) * q :=
    mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hb3 : (1 : ℤ) * q' ≤ (j : ℤ) * q' :=
    mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hb4 : (j' : ℤ) * q ≤ ((q' : ℤ) - 1) * q :=
    mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hzero : ((j : ℤ) * q' - (j' : ℤ) * q) - 1 = 0 := by
    refine eq_zero_of_dvd_of_abs_lt (mul_pos (by omega) (by omega)) hdvd ?_ ?_
    · linarith
    · linarith
  have heq : (j : ℤ) * q' - (j' : ℤ) * q = 1 := by linarith
  refine ⟨(j, j'), ⟨⟨hj1, hjq⟩, ⟨hj'1, hj'q'⟩, heq⟩, ?_⟩
  -- Uniqueness: the range window expels every other solution.
  rintro ⟨y1, y2⟩ ⟨hy1, hy2, hyeqP⟩
  have hyeq : (y1 : ℤ) * q' - (y2 : ℤ) * q = 1 := hyeqP
  obtain ⟨hy11, hy12⟩ : 1 ≤ y1 ∧ y1 ≤ q - 1 := hy1
  obtain ⟨hy21, hy22⟩ : 1 ≤ y2 ∧ y2 ≤ q' - 1 := hy2
  have hq_dvd : (q : ℤ) ∣ ((y1 : ℤ) - j) * q' := ⟨(y2 : ℤ) - j', by linarith⟩
  have hy1j : y1 = j := by
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hq_dvd with h | h
    · have h0 : (y1 : ℤ) - j = 0 :=
        eq_zero_of_dvd_of_abs_lt (by exact_mod_cast hp.pos) h (by omega) (by omega)
      omega
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hp').mp
        (Int.natCast_dvd_natCast.mp h)) hne
  have hy2j : y2 = j' := by
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hy1Z : (y1 : ℤ) = j := by exact_mod_cast hy1j
    have hyeq2 : (j : ℤ) * q' - (y2 : ℤ) * q = 1 := by rw [← hy1Z]; exact hyeq
    have he : (y2 : ℤ) * q = (j' : ℤ) * q := by linarith
    have := mul_right_cancel₀ hq0 he
    exact_mod_cast this
  simp only [Prod.mk.injEq]
  exact ⟨hy1j, hy2j⟩

/-- **Farey adjacency, mirror wing (`ε = -1`)** — by the `(q', q)`-symmetry of
    `farey_adjacent_exists_unique`: exactly one pair with `j·q' - j'·q = -1`. -/
theorem farey_adjacent_exists_unique_neg {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    ∃! p : ℕ × ℕ, (1 ≤ p.1 ∧ p.1 ≤ q - 1) ∧ (1 ≤ p.2 ∧ p.2 ≤ q' - 1) ∧
      (p.1 : ℤ) * q' - (p.2 : ℤ) * q = -1 := by
  obtain ⟨⟨a, b⟩, ⟨hr1, hr2, habP⟩, huniq⟩ :=
    farey_adjacent_exists_unique hq' hq hne.symm
  have hab : (a : ℤ) * q - (b : ℤ) * q' = 1 := habP
  obtain ⟨ha1, ha2⟩ : 1 ≤ a ∧ a ≤ q' - 1 := hr1
  obtain ⟨hb1, hb2⟩ : 1 ≤ b ∧ b ≤ q - 1 := hr2
  have hswap : (b : ℤ) * q' - (a : ℤ) * q = -1 := by linarith
  refine ⟨(b, a), ⟨⟨hb1, hb2⟩, ⟨ha1, ha2⟩, hswap⟩, ?_⟩
  rintro ⟨y1, y2⟩ ⟨hy1, hy2, hyeqP⟩
  have hyeq : (y1 : ℤ) * q' - (y2 : ℤ) * q = -1 := hyeqP
  obtain ⟨hy11, hy12⟩ : 1 ≤ y1 ∧ y1 ≤ q - 1 := hy1
  obtain ⟨hy21, hy22⟩ : 1 ≤ y2 ∧ y2 ≤ q' - 1 := hy2
  have hswap2 : (y2 : ℤ) * q - (y1 : ℤ) * q' = 1 := by linarith
  have h := huniq (y2, y1) ⟨⟨hy21, hy22⟩, ⟨hy11, hy12⟩, hswap2⟩
  rw [Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  exact ⟨h.2, h.1⟩

/-! ### Part D — the cross-term class bijection (the load-bearing theorem)

The map `(j, j') ↦ (j·q' - j'·q) mod (q·q')` from the level-1 mode box of an ordered
clock pair.  CRT reads the class mod `q` as `j·q'` (so `j` is determined — `q'` is
invertible) and mod `q'` as `-j'·q` (so `j'` is determined): the map is INJECTIVE.  Its
image is exactly the classes vanishing at NEITHER clock — `(q-1)(q'-1)` of them — and
each is hit EXACTLY ONCE.  Every admissible Farey class `m` occurs once per ordered clock
pair: this replaces sorting arguments in the large-sieve v0 route and organizes the
dispersion identity's cross-terms into `m`-classes. -/

/-- The Farey class of the mode pair `(j, j')` of the ordered clock pair `(q, q')`: the
    cross-term numerator reduced mod `q·q'`. -/
def crossClass (q q' j j' : ℕ) : ZMod (q * q') :=
  ((crossNum q q' j j' : ℤ) : ZMod (q * q'))

/-- The level-1 mode box of the ordered clock pair: `[1, q-1] × [1, q'-1]`. -/
def fareyBox (q q' : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 (q - 1) ×ˢ Finset.Icc 1 (q' - 1)

theorem mem_fareyBox {q q' : ℕ} {p : ℕ × ℕ} :
    p ∈ fareyBox q q' ↔ (1 ≤ p.1 ∧ p.1 ≤ q - 1) ∧ (1 ≤ p.2 ∧ p.2 ≤ q' - 1) := by
  unfold fareyBox
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]

theorem fareyBox_card (q q' : ℕ) : (fareyBox q q').card = (q - 1) * (q' - 1) := by
  unfold fareyBox
  rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
  simp

/-- The admissible Farey classes of the ordered clock pair: the residues mod `q·q'`
    vanishing at NEITHER clock (both CRT coordinates nonzero). -/
def admissibleClasses (q q' : ℕ) : Set (ZMod (q * q')) :=
  {m | ZMod.castHom (dvd_mul_right q q') (ZMod q) m ≠ 0 ∧
       ZMod.castHom (dvd_mul_left q' q) (ZMod q') m ≠ 0}

/-- The two CRT coordinates of a Farey class, computed on the integer numerator. -/
theorem crossClass_castHom_left (q q' j j' : ℕ) :
    ZMod.castHom (dvd_mul_right q q') (ZMod q) (crossClass q q' j j')
      = ((crossNum q q' j j' : ℤ) : ZMod q) := by
  unfold crossClass
  exact map_intCast _ _

theorem crossClass_castHom_right (q q' j j' : ℕ) :
    ZMod.castHom (dvd_mul_left q' q) (ZMod q') (crossClass q q' j j')
      = ((crossNum q q' j j' : ℤ) : ZMod q') := by
  unfold crossClass
  exact map_intCast _ _

/-- **CRT injectivity of the class map.**  Two mode pairs of the box with the same Farey
    class coincide: the class mod `q` determines `j` (`q'` is invertible mod `q`), the
    class mod `q'` determines `j'`, and the range window does the rest. -/
theorem crossterm_class_injective {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    Set.InjOn (fun p : ℕ × ℕ => crossClass q q' p.1 p.2) ↑(fareyBox q q') := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  intro p₁ hm₁ p₂ hm₂ heq
  obtain ⟨j₁, k₁⟩ := p₁
  obtain ⟨j₂, k₂⟩ := p₂
  rw [Finset.mem_coe, mem_fareyBox] at hm₁ hm₂
  obtain ⟨⟨hj₁1, hj₁q⟩, ⟨hk₁1, hk₁q⟩⟩ := hm₁
  obtain ⟨⟨hj₂1, hj₂q⟩, ⟨hk₂1, hk₂q⟩⟩ := hm₂
  simp only [crossClass] at heq
  have hdvd : ((q * q' : ℕ) : ℤ) ∣ crossNum q q' j₂ k₂ - crossNum q q' j₁ k₁ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp heq
  push_cast at hdvd
  have hq_dvd : (q : ℤ) ∣ ((j₂ : ℤ) - j₁) * q' := by
    have h1 : (q : ℤ) ∣ crossNum q q' j₂ k₂ - crossNum q q' j₁ k₁ :=
      dvd_trans (dvd_mul_right _ _) hdvd
    have h2 : (q : ℤ) ∣ ((k₂ : ℤ) - k₁) * q := dvd_mul_left _ _
    have h3 := dvd_add h1 h2
    have he : (crossNum q q' j₂ k₂ - crossNum q q' j₁ k₁) + ((k₂ : ℤ) - k₁) * q
        = ((j₂ : ℤ) - j₁) * q' := by
      unfold crossNum; ring
    rwa [he] at h3
  have h2q := hp.two_le
  have h2q' := hp'.two_le
  have hj : j₁ = j₂ := by
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hq_dvd with h | h
    · have h0 : (j₂ : ℤ) - j₁ = 0 :=
        eq_zero_of_dvd_of_abs_lt (by exact_mod_cast hp.pos) h (by omega) (by omega)
      omega
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hp').mp
        (Int.natCast_dvd_natCast.mp h)) hne
  subst hj
  have hk : k₁ = k₂ := by
    obtain ⟨c, hc⟩ := hdvd
    unfold crossNum at hc
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have he : ((k₁ : ℤ) - k₂) * q = ((q' : ℤ) * c) * q := by linarith
    have hcancel : (k₁ : ℤ) - k₂ = (q' : ℤ) * c := mul_right_cancel₀ hq0 he
    have h0 : (k₁ : ℤ) - k₂ = 0 :=
      eq_zero_of_dvd_of_abs_lt (by exact_mod_cast hp'.pos) ⟨c, hcancel⟩
        (by omega) (by omega)
    omega
  rw [hk]

/-- The class map lands in the admissible classes: a box pair hits neither clock
    (`crossNum_not_dvd_left` / `crossNum_not_dvd_right`). -/
theorem crossterm_class_mapsTo {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    Set.MapsTo (fun p : ℕ × ℕ => crossClass q q' p.1 p.2) ↑(fareyBox q q')
      (admissibleClasses q q') := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  intro p hm
  obtain ⟨j, k⟩ := p
  rw [Finset.mem_coe, mem_fareyBox] at hm
  obtain ⟨⟨hj1, hjq⟩, ⟨hk1, hkq⟩⟩ := hm
  simp only [admissibleClasses, Set.mem_setOf_eq]
  constructor
  · rw [crossClass_castHom_left, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact crossNum_not_dvd_left hp hp' hne hj1 hjq
  · rw [crossClass_castHom_right, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact crossNum_not_dvd_right hp hp' hne hk1 hkq

/-- **CRT surjectivity of the class map.**  Every admissible class is hit: read the two
    CRT coordinates of `m`, solve `j·q' ≡ m (mod q)` and `j'·q ≡ -m (mod q')` in the
    respective fields (`exists_mode_solving`), and glue with coprimality. -/
theorem crossterm_class_surjOn {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    Set.SurjOn (fun p : ℕ × ℕ => crossClass q q' p.1 p.2) ↑(fareyBox q q')
      (admissibleClasses q q') := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  haveI : NeZero (q * q') := ⟨Nat.mul_ne_zero hp.pos.ne' hp'.pos.ne'⟩
  intro m hm
  obtain ⟨hm1, hm2⟩ := hm
  have hxm : (((m.val : ℕ) : ℤ) : ZMod (q * q')) = m := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val m
  have hb1 : ZMod.castHom (dvd_mul_right q q') (ZMod q) m
      = (((m.val : ℕ) : ℤ) : ZMod q) := by
    conv_lhs => rw [← hxm]
    exact map_intCast (ZMod.castHom (dvd_mul_right q q') (ZMod q)) _
  have hb2 : ZMod.castHom (dvd_mul_left q' q) (ZMod q') m
      = (((m.val : ℕ) : ℤ) : ZMod q') := by
    conv_lhs => rw [← hxm]
    exact map_intCast (ZMod.castHom (dvd_mul_left q' q) (ZMod q')) _
  have hqx : (((m.val : ℕ) : ℤ) : ZMod q) ≠ 0 := by rw [← hb1]; exact hm1
  have hq'x : (((m.val : ℕ) : ℤ) : ZMod q') ≠ 0 := by rw [← hb2]; exact hm2
  generalize hgen : ((m.val : ℕ) : ℤ) = x at hxm hqx hq'x
  obtain ⟨j, hj1, hjq, hdq⟩ := exists_mode_solving hp (t := ((q' : ℕ) : ℤ)) (s := x)
    (by push_cast; exact natCast_prime_ne_zero hp hp' hne) hqx
  obtain ⟨j', hj'1, hj'q', hdq'⟩ := exists_mode_solving hp' (t := ((q : ℕ) : ℤ)) (s := -x)
    (by push_cast; exact natCast_prime_ne_zero hp' hp hne.symm)
    (by rw [Int.cast_neg]; exact neg_ne_zero.mpr hq'x)
  have hdq'' : (q' : ℤ) ∣ (j' : ℤ) * q + x := by
    have he : (j' : ℤ) * q + x = (j' : ℤ) * q - (-x) := by ring
    rw [he]; exact hdq'
  have hNq : (q : ℤ) ∣ crossNum q q' j j' - x := by
    have he : crossNum q q' j j' - x = ((j : ℤ) * q' - x) - (j' : ℤ) * q := by
      unfold crossNum; ring
    rw [he]
    exact dvd_sub hdq (dvd_mul_left _ _)
  have hNq' : (q' : ℤ) ∣ crossNum q q' j j' - x := by
    have he : crossNum q q' j j' - x = (j : ℤ) * q' - ((j' : ℤ) * q + x) := by
      unfold crossNum; ring
    rw [he]
    exact dvd_sub (dvd_mul_left _ _) hdq''
  have hcop : IsCoprime (q : ℤ) (q' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hp').mpr hne)
  have hN : (q : ℤ) * q' ∣ crossNum q q' j j' - x := hcop.mul_dvd hNq hNq'
  refine ⟨(j, j'), ?_, ?_⟩
  · rw [Finset.mem_coe, mem_fareyBox]
    exact ⟨⟨hj1, hjq⟩, ⟨hj'1, hj'q'⟩⟩
  · show crossClass q q' j j' = m
    unfold crossClass
    rw [← hxm, ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    have he : x - crossNum q q' j j' = -(crossNum q q' j j' - x) := by ring
    rw [he]
    exact dvd_neg.mpr hN

/-- **THE CROSS-TERM CLASS BIJECTION (load-bearing).**  For distinct clocks `q ≠ q'`,
    `(j, j') ↦ (j·q' - j'·q) mod (q·q')` is a BIJECTION from the level-1 mode box
    `[1, q-1] × [1, q'-1]` onto the admissible Farey classes (nonzero at both clocks).
    Every admissible class `m` occurs EXACTLY ONCE per ordered clock pair — the
    dispersion identity's cross-terms reorganize into `m`-classes with multiplicity one,
    replacing the sorting arguments of the large-sieve v0 route.  Exact CRT content:
    injectivity is `crossterm_class_injective`, surjectivity `crossterm_class_surjOn`. -/
theorem crossterm_class_bijection {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    Set.BijOn (fun p : ℕ × ℕ => crossClass q q' p.1 p.2) ↑(fareyBox q q')
      (admissibleClasses q q') :=
  ⟨crossterm_class_mapsTo hq hq' hne, crossterm_class_injective hq hq' hne,
    crossterm_class_surjOn hq hq' hne⟩

/-- The image characterization, extracted: the class map's image over the box IS the
    admissible-class set. -/
theorem crossterm_class_image {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    (fun p : ℕ × ℕ => crossClass q q' p.1 p.2) '' ↑(fareyBox q q')
      = admissibleClasses q q' :=
  (crossterm_class_bijection hq hq' hne).image_eq

/-- The box injects: the Farey classes of an ordered clock pair number exactly
    `(q-1)(q'-1)` — one per mode pair. -/
theorem crossterm_class_card {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    ((fareyBox q q').image fun p : ℕ × ℕ => crossClass q q' p.1 p.2).card
      = (q - 1) * (q' - 1) := by
  rw [Finset.card_image_of_injOn (crossterm_class_injective hq hq' hne), fareyBox_card]

/-- The honest count on the class side: there are exactly `(q-1)(q'-1)` admissible
    classes — the bijection transported to cardinalities. -/
theorem admissibleClasses_ncard {A q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) (hne : q ≠ q') :
    (admissibleClasses q q').ncard = (q - 1) * (q' - 1) := by
  rw [← crossterm_class_image hq hq' hne,
    (crossterm_class_injective hq hq' hne).ncard_image,
    Set.ncard_coe_finset, fareyBox_card]

/-! ### Part E — the Apollonian vocabulary kill

The mediant of `j/q` and `j'/q'` is `(j + j')/(q + q')`: the Stern–Brocot / Ford-circle
subdivision step, the generator of the Apollonian (Descartes) packing picture.  Its
denominator is the SUM of two odd primes — even, hence never prime, hence never a clock
at any scale.  The mediant/Apollonian subdivision does not act on the clock set: the
Descartes-circle angle of the directive is killed as vocabulary, exactly here. -/

/-- Mediant denominators are even: clocks are odd primes, so `q + q'` is even. -/
theorem mediant_denom_even {A q q' : ℕ} (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) :
    Even (q + q') := by
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  exact (hp.odd_of_ne_two (by omega)).add_odd (hp'.odd_of_ne_two (by omega))

/-- **The Apollonian kill.**  The mediant denominator `q + q'` of two clock frequencies
    is NEVER a clock, at ANY scale `B`: it is even (`mediant_denom_even`) and at least
    `10`, while the only even prime is `2`.  The mediant/Stern–Brocot subdivision —
    and with it the Descartes/Apollonian packing route — does not act on the clock
    set.  Vocabulary status: this closes a dictionary entry, not a mathematical front. -/
theorem mediant_denom_not_clock {A B q q' : ℕ}
    (hq : q ∈ clocks A) (hq' : q' ∈ clocks A) :
    q + q' ∉ clocks B := by
  intro hmem
  obtain ⟨hpm, h5m, _⟩ := mem_clocks.mp hmem
  obtain ⟨hp, h5, _⟩ := mem_clocks.mp hq
  obtain ⟨hp', h5', _⟩ := mem_clocks.mp hq'
  have heven := mediant_denom_even hq hq'
  have h2 : q + q' = 2 := (Nat.Prime.even_iff hpm).mp heven
  omega

/-! ### Part F — kernel demos at the clock pair `(5, 7)`

The smallest ordered clock pair, checked by the kernel: the unimodular pair is `(3, 4)`
(`3·7 - 4·5 = 1`), it is the ONLY one among the `4·6 = 24` box pairs, and the class map
is injective there — `24` distinct Farey classes mod `35`. -/

/-- `5` and `7` are exactly the clocks of scale `7`. -/
example : clocks 7 = {5, 7} := by decide

/-- The unimodular pair of `(5, 7)` is `(3, 4)`: `3·7 - 4·5 = 21 - 20 = 1`. -/
theorem unimodular_5_7 : crossNum 5 7 3 4 = 1 := by decide

/-- Kernel uniqueness sweep over all `24` box pairs of `(5, 7)`: `(3, 4)` is the ONLY
    unimodular pair — the concrete instance of `farey_adjacent_exists_unique`. -/
theorem unimodular_5_7_unique :
    ∀ j ∈ Finset.Icc 1 4, ∀ j' ∈ Finset.Icc 1 6,
      crossNum 5 7 j j' = 1 → j = 3 ∧ j' = 4 := by decide

/-- The Farey class of the unimodular pair is `1 (mod 35)`. -/
theorem crossClass_5_7_unimodular : crossClass 5 7 3 4 = 1 := by decide

/-- Kernel injectivity at `(5, 7)`: the `24` box pairs land on `24` DISTINCT classes
    mod `35` — the concrete instance of `crossterm_class_bijection` (and, with
    `4·6 = (5-1)·(7-1)`, of `admissibleClasses_ncard`). -/
theorem crossterm_classes_distinct_5_7 :
    ((fareyBox 5 7).image fun p : ℕ × ℕ => crossClass 5 7 p.1 p.2).card = 24 := by
  decide

/-! ### Axiom audit

Recorded output of the block below (this pass):

    level1_freq_injective … admissibleClasses_ncard, mediant_denom_not_clock,
    unimodular_5_7_unique, crossterm_classes_distinct_5_7
                                    -- [propext, Classical.choice, Quot.sound]
    unimodular_5_7                  -- does not depend on any axioms
    crossClass_5_7_unimodular       -- [propext, Quot.sound]

No `sorryAx`, no `native_decide` (`Lean.ofReduceBool`), no `step00FirstCause`: the module
is green under the standard triple; the raw `crossNum` demo is even axiom-free. -/

#print axioms level1_freq_injective
#print axioms level1_spacing
#print axioms level1_spacing_scale
#print axioms level1_spacing_wraparound
#print axioms level1_circle_spacing
#print axioms farey_adjacent_exists_unique
#print axioms farey_adjacent_exists_unique_neg
#print axioms crossterm_class_injective
#print axioms crossterm_class_bijection
#print axioms crossterm_class_image
#print axioms crossterm_class_card
#print axioms admissibleClasses_ncard
#print axioms mediant_denom_not_clock
#print axioms unimodular_5_7
#print axioms unimodular_5_7_unique
#print axioms crossClass_5_7_unimodular
#print axioms crossterm_classes_distinct_5_7

end FareyModeGeometry
end EuclidsPath
