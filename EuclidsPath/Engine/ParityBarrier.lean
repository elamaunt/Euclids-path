/-
  ParityBarrier — formalisation of the PARITY WALL as a negative result, NOT a proof of twin primes.
  Source: new_structural_routes_reverse_parity_barrier_ru_2026-07-01.md (Part IV + Part III reverse).
  Prose: prose/24_BoundaryDecomp.md (section "The parity wall as a theorem").

  THE KEY SHIFT. The previous 11 bricks TRIED to close twin primes and ran into the counting/parity wall.
  This brick does something different: it formalises THE WALL ITSELF as a theorem — it proves that a
  finite-sieve engine (a certificate depending only on the finite view at level `A`) CANNOT certify twin
  through ambiguity, and that crossing the wall REQUIRES cofinal information. This is a negative /
  diagnostic result, which honestly does NOT assert twin primes.

  PROVED HERE (pure logic + one arithmetic fact, std axioms, no sorry):
    * `parityBlind_cannot_certify_twin` — parity-blind + sound + ambiguity ⟹ False (heart of the wall);
    * `sound_cert_ambiguous_at_level_not_blind`, `sound_cert_requires_cofinal_information` — sound-cert
      with ambiguity at every level ⟹ requires cofinal information;
    * `finite_sieve_engine_cannot_cross_barrier` — finite-sieve engine does not cross the wall;
    * `parity_barrier_model_no_finite_view_decides_twin` — model form (no finite view decides twin
      under ambiguity);
    * `finite_twins_contradiction_requires_cofinal_cert` — any refutation of the finiteness of twin primes
      by a new certificate must use cofinal information;
    * `exists_clean_nonTwin_block` — the wall is NOT vacuous: a clean-non-twin block exists;
    * `repeated_value_of_infinite_finite` — pigeonhole (for the reverse-tree);
    * `contradiction_of_finiteTwinEuclid` — the correct form of the finite-list contradiction (§2).

  HONEST BOUNDARY. This is NOT a proof of twin primes and NOT a reduction of one. It is a proof of a
  LIMITATION: to close Step00 one must supply a `RequiresCofinalInformation` certificate (cofinal, not
  finite-sieve). The concrete Step00 instantiation (`Step00Cert`, `AmbiguousAtEveryFiniteLevel` for our
  engine, reverse-barrier §22–23) — NAMED INPUTS where the wall returns: `AmbiguousAtEveryFiniteLevel`
  for the real engine ≈ the fact that the engine is finite-sieve = does not cross the wall. These
  instantiations are not supplied here. `Step00` remains `sorry`. Value: the wall has become a
  machine-verified theorem, and the requirement for crossing it — precise and auditable.
-/
import Mathlib
import EuclidsPath.Engine.Residuals

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath.ParityBarrier

open EuclidsPath.Residuals

/-! ### §26. TwinBlock: a pair of sides as one object. Here center = ℕ, twin = `TwinCenterZ`. -/

/-- A twin block is given by its center; `IsTwin` = both sides are prime (`TwinCenterZ`). -/
abbrev IsTwin (B : ℕ) : Prop := TwinCenterZ B

/-! ### §27–28. Sieve-view system and parity-blind predicate -/

/-- System of finite "views" at level `A` (sieve-view of a block at level `A`). Interface, no residues. -/
structure SieveViewSystem where
  View : ℕ → Type
  view : ∀ A, ℕ → View A

/-- Two blocks are `A`-equivalent if their views at level `A` coincide. -/
def SieveEquivalent (S : SieveViewSystem) (A : ℕ) (B₁ B₂ : ℕ) : Prop := S.view A B₁ = S.view A B₂

/-- A `parity-blind` certificate at level `A`: depends only on the `A`-view (does not distinguish `A`-equivalent blocks). -/
def ParityBlindPredicate (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) : Prop :=
  ∀ B₁ B₂, SieveEquivalent S A B₁ B₂ → (Cert B₁ ↔ Cert B₂)

/-- Requires cofinal information: NOT parity-blind at any level. -/
def RequiresCofinalInformation (S : SieveViewSystem) (Cert : ℕ → Prop) : Prop :=
  ∀ A, ¬ ParityBlindPredicate S A Cert

/-! ### §29–30. Sound certificate and ambiguity at a level -/

/-- `Cert` is sound: it certifies only genuine twin blocks. -/
def SoundTwinCert (Cert : ℕ → Prop) : Prop := ∀ B, Cert B → IsTwin B

/-- Ambiguity at level `A`: `A`-equivalent `good` (certified) and `bad` (not twin). -/
def CertAmbiguousAt (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop) : Prop :=
  ∃ good bad, SieveEquivalent S A good bad ∧ Cert good ∧ ¬ IsTwin bad

/-! ### §31–33. HEART OF THE WALL: parity-blind + sound + ambiguity ⟹ False -/

/--
  **`parityBlind_cannot_certify_twin` — PROVED (heart of the parity wall).** A parity-blind certificate
  (depends only on the `A`-view) + soundness + ambiguity (`A`-equivalent `good`/`bad`, `bad` not
  twin) ⟹ `False`. Mechanism: blind transfers the certificate from `good` to `bad`, soundness makes `bad`
  a twin — contradicting `¬IsTwin bad`. Pure logic: a finite view cannot distinguish twin from non-twin. -/
theorem parityBlind_cannot_certify_twin (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop)
    (hBlind : ParityBlindPredicate S A Cert) (hSound : SoundTwinCert Cert)
    (hAmb : CertAmbiguousAt S A Cert) : False := by
  obtain ⟨good, bad, hSame, hCertGood, hBadNotTwin⟩ := hAmb
  exact hBadNotTwin (hSound bad ((hBlind good bad hSame).mp hCertGood))

/-- **`sound_cert_ambiguous_at_level_not_blind` — PROVED.** Sound + ambiguity at `A` ⟹ NOT blind at `A`. -/
theorem sound_cert_ambiguous_at_level_not_blind (S : SieveViewSystem) (A : ℕ) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert) (hAmb : CertAmbiguousAt S A Cert) :
    ¬ ParityBlindPredicate S A Cert :=
  fun hBlind => parityBlind_cannot_certify_twin S A Cert hBlind hSound hAmb

/-- Ambiguity at every finite level. -/
def AmbiguousAtEveryFiniteLevel (S : SieveViewSystem) (Cert : ℕ → Prop) : Prop :=
  ∀ A, CertAmbiguousAt S A Cert

/--
  **`sound_cert_requires_cofinal_information` — PROVED (main diagnostic).** Sound certificate +
  ambiguity at EVERY level ⟹ it requires cofinal information (not blind at any `A`). That is, a sound
  twin certificate under irremovable ambiguity cannot factor through a finite view — it must "see
  infinitely far". This is the precise form of the parity wall. -/
theorem sound_cert_requires_cofinal_information (S : SieveViewSystem) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert) (hAmbAll : AmbiguousAtEveryFiniteLevel S Cert) :
    RequiresCofinalInformation S Cert :=
  fun A => sound_cert_ambiguous_at_level_not_blind S A Cert hSound (hAmbAll A)

/-! ### §34. Finite-sieve engine does not cross the wall -/

/-- Finite-sieve engine: a certificate blind at some finite level `cutoff`. Carries data
    (`cutoff`), hence `Type`, not `Prop`. -/
structure FiniteSieveEngine (S : SieveViewSystem) (Cert : ℕ → Prop) where
  cutoff : ℕ
  blind : ParityBlindPredicate S cutoff Cert

/--
  **`finite_sieve_engine_cannot_cross_barrier` — PROVED (pure no-go).** Finite-sieve engine
  (blind at `cutoff`) + soundness + ambiguity at `cutoff` ⟹ `False`. A finite-sieve certificate
  cannot cross the parity wall. -/
theorem finite_sieve_engine_cannot_cross_barrier (S : SieveViewSystem) (Cert : ℕ → Prop)
    (E : FiniteSieveEngine S Cert) (hSound : SoundTwinCert Cert)
    (hAmb : CertAmbiguousAt S E.cutoff Cert) : False :=
  parityBlind_cannot_certify_twin S E.cutoff Cert E.blind hSound hAmb

/-! ### §40. Model form of the wall (independent of the actual existence of twin primes) -/

/--
  **`parity_barrier_model_no_finite_view_decides_twin` — PROVED (model wall).** If the model
  has ambiguity (views of `X`, `Y` coincide at `A`, but `X` is twin and `Y` is not), then no
  predicate `DecideTwin` on the `A`-view can correctly decide `modelTwin`. Pure logic, independent
  of the arithmetic of twin primes — a formal model of the parity barrier. -/
theorem parity_barrier_model_no_finite_view_decides_twin {View ModelBlock : Type*}
    (modelView : ModelBlock → View) (modelTwin : ModelBlock → Prop)
    (X Y : ModelBlock) (hView : modelView X = modelView Y)
    (hTwinX : modelTwin X) (hNotTwinY : ¬ modelTwin Y)
    (DecideTwin : View → Prop) (hCorrect : ∀ Z, DecideTwin (modelView Z) ↔ modelTwin Z) : False :=
  hNotTwinY ((hCorrect Y).mp (hView ▸ (hCorrect X).mpr hTwinX))

/-! ### §2. The correct form of the finite-list contradiction -/

/-- §2: finite-list contradiction. Complete list `T` of twin centers + new twin outside `T` ⟹ False. -/
structure FiniteTwinEuclidContradiction where
  T : Finset ℕ
  complete : ∀ m, IsTwin m → m ∈ T
  newCenter : ℕ
  newTwin : IsTwin newCenter
  newNotIn : newCenter ∉ T

/-- **`contradiction_of_finiteTwinEuclid` — PROVED (§2, pure logic).** -/
theorem contradiction_of_finiteTwinEuclid (E : FiniteTwinEuclidContradiction) : False :=
  E.newNotIn (E.complete E.newCenter E.newTwin)

/--
  **`finite_twins_contradiction_requires_cofinal_cert` — PROVED (§41, diagnostic).** Any refutation
  of the finiteness of twin primes via a NEW sound certificate under ambiguity at every level MUST use
  cofinal information. That is, a finite-sieve engine cannot do this. -/
theorem finite_twins_contradiction_requires_cofinal_cert (S : SieveViewSystem) (Cert : ℕ → Prop)
    (hSound : SoundTwinCert Cert) (hAmbAll : AmbiguousAtEveryFiniteLevel S Cert) :
    RequiresCofinalInformation S Cert :=
  sound_cert_requires_cofinal_information S Cert hSound hAmbAll

/-! ### §39. The wall is NOT vacuous: a clean-non-twin block exists (no twin-prime smuggling) -/

/--
  **`exists_clean_nonTwin_block` — PROVED.** There exists a clean (at level 1) non-twin center: `m = 4`
  (side `25 = 5²` is not prime ⟹ not twin). This guarantees that ambiguity/barrier is NOT a vacuous
  abstraction: genuine clean-non-twin blocks exist. (We do NOT assert the existence of a clean-TWIN block —
  that would be twin-prime smuggling, §39.) -/
theorem exists_clean_nonTwin_block : ∃ m : ℕ, CleanZ 1 (m : ℤ) ∧ ¬ IsTwin m := by
  refine ⟨4, ?_, ?_⟩
  · intro q hq hq1; interval_cases q <;> simp_all [Nat.Prime]
  · intro h; have := h.2; norm_num [Nat.Prime] at this

/-! ### Reverse-engine core (Part III): pigeonhole ⟹ repeated signature on a ray -/

/-- **`repeated_value_of_infinite_finite` — PROVED (§18 pigeonhole).** An infinite
    sequence into a finite type has a repeat `f i = f j`, `i < j`. Foundation of the reverse-barrier. -/
theorem repeated_value_of_infinite_finite {Sig : Type*} [Finite Sig] (f : ℕ → Sig) :
    ∃ i j, i < j ∧ f i = f j := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

end EuclidsPath.ParityBarrier
