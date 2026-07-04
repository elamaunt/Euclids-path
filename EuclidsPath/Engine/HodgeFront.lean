/-
  HodgeFront — the GREEN (axiom-free) module of the Hodge branch in the
  perpetual-engine programme: a Hodge class = a QUANTIZED (rational) charge
  of cohomology of aligned type (p,p); an algebraic cycle = PAYMENT;
  the conjecture = every quantized aligned charge is paid. An UNPAID
  charge would open an infinite strict descent along the ℕ-height (denominator /
  complexity) — a forbidden perpetual engine (EPMI).

  HONEST BOUNDARY (loud, as in YM/NS): mathlib has NO Hodge theory for
  projective varieties — no Hodge classes, no algebraic cycles,
  no cohomology of varieties. Checked against the pin: the word "Hodge" occurs
  exactly three times — a citation of W. Hodges's book on MODEL theory
  (ModelTheory/Fraisse) and mentions of p-adic Hodge theory in comments
  of period rings (RingTheory/Perfectoid/BDeRham, FontaineTheta); there is no
  hodge-star operator either. `HodgeLedger` is an ABSTRACT LEDGER; NO
  content of algebraic geometry beyond an intended future instantiation
  is present here. The millennium problem is NOT solved and NOT claimed.

  Architecture:
    * model: `HodgeLedger` — classes, payment, ℕ-height, quantization anchor
      "paid ⟺ height 0" (`height_zero_iff`; genuinely consumed:
      `unpaid_height_pos` + V1 refutation);
    * engine: `UnpaidDescentChain` — an infinite strictly decreasing ℕ-chain
      of unpaid charges; KILLED UNCONDITIONALLY (`isEmpty_unpaidDescentChain`,
      the repository's ROOT — EPMI, A = 1). INVERSION of the YM asymmetry (disclosed,
      not forged): in YM the ℝ-ladder WAS ALIVE before the quantization law arrived
      (gapless ⟺ Nonempty ladder), here quantization is BUILT INTO the model
      (height : ℕ) — the engine is dead in any model; the whole substance of
      the branch lies in the existence of descent STEPS, i.e. in the law;
    * descent law `DescentLaw` (per-model 🔴 INPUT, NS/YM pattern): every
      unpaid Hodge charge admits a payment step — a strictly smaller
      unpaid Hodge charge; for the INTENDED (not constructed!)
      instantiation this is precisely the residual input of the branch;
    * HERO: `hodgeProperty_of_descentLaw` — strong induction on height
      (choice NOT needed); the chain route via choice (mirror of ladderSeq) is given
      separately (`hodgeProperty_of_descentLaw'`).

  COLLAPSE of cost (§4): `descentLaw_iff_hodgeProperty` — the per-model law
  ⟺ the conjecture, GREEN and WITHOUT ANY boundary (the form of a condemned bridge, like
  `quantizationLaw_iff_massGap`); the reverse side is VACUOUS (like the Riemann
  L5 `manifestationLaw_of_RH`, in CONTRAST to YM L8 with a genuine rank) —
  disclosed. That is why THERE IS NO SIXTH FIELD: to decree the law = to decree
  the goal verbatim.

  TRILEMMA of the sixth boundary of the decree — all verdicts are machine-made (§6):
    V1 the universal form is REFUTABLE (cookedUnpaid: a charge of height 1 —
       a descent step would run into the paidness of height zero);
    V2 the existential form is ALREADY PROVEN (cookedPaid — the law is vacuous);
    V2′ the chain-manifestation form is DEGENERATED INTO A GREEN THEOREM
       (`hodgeChainManifestationLaw_green`: there are no chains IN ANY model) —
       a V2-type verdict, the decree would be vacuous; the unique structural
       point of the branch, disclosed;
    V3 the manifestation form over a PRESENTABLE witness (a single
       unpaid class, `cookedUnpaidClass`) is INCOMPATIBLE with the accepted
       boundary — a mirror of YM/NS V3.
  The split by scales is NOT duplicated: it is already fixed in §12 of the quarantine
  (`decreedScale_no_deviationSupply`) and in `YangMills.smallScale_deviationSupply`.
  The module does NOT import the quarantine; there is no axiom/sorry — the verifier must
  show all declarations untainted.
-/
import Mathlib
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.RiemannManifestationFront

set_option autoImplicit false

namespace EuclidsPath
namespace Hodge

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
-- We use EPMI and OriginAnchorAudit QUALIFIED (collisions State/Step/Bridge).

/-#############################################################################
  §1. Abstract cohomology ledger, the conjecture, unpaid classes
#############################################################################-/

/-- **D1. Abstract cohomology ledger**: classes, distinguished quantized
    (rational) charges of aligned type (p,p) (`IsHodge`), paid by
    cycles (`IsAlgebraic`), and an ℕ-height (denominator/complexity) with the
    quantization anchor `height_zero_iff` ("paid ⟺ height 0"). `zero` is
    the invariant habitability anchor (the zero charge is paid by the zero cycle);
    no group structure is imposed — the killer chain does not subtract
    (the algebra of payments belongs to a future instantiation, disclosed).
    `IsAlgebraic` is definable from the height via the anchor — kept as a named
    field for the sake of the ledger reading. NO content of algebraic
    geometry (disclosed in the header). -/
structure HodgeLedger where
  Cls : Type
  zero : Cls
  IsHodge : Cls → Prop
  IsAlgebraic : Cls → Prop
  height : Cls → ℕ
  zero_hodge : IsHodge zero
  zero_algebraic : IsAlgebraic zero
  height_zero_iff : ∀ c, height c = 0 ↔ IsAlgebraic c

/-- **D2. HODGE CONJECTURE for a model** (the Clay direction; here — only
    the abstract form): every quantized aligned charge is paid. -/
def HodgeProperty (S : HodgeLedger) : Prop :=
  ∀ c : S.Cls, S.IsHodge c → S.IsAlgebraic c

/-- **D3. Unpaid Hodge class** — the deviation object (analogue of an
    off-critical zero / a positive state): exactly this type is forged and
    PRESENTABLE (fuel for V3 and origin-anchor audits). -/
abbrev UnpaidClass (S : HodgeLedger) : Type :=
  {c : S.Cls // S.IsHodge c ∧ ¬ S.IsAlgebraic c}

/-- The zero charge is paid — habitability of the payment world in every model. -/
theorem zero_paid (S : HodgeLedger) : S.IsHodge S.zero ∧ S.IsAlgebraic S.zero :=
  ⟨S.zero_hodge, S.zero_algebraic⟩

/-- The height of the zero charge is 0 (the anchor is consumed). -/
theorem height_zero (S : HodgeLedger) : S.height S.zero = 0 :=
  (S.height_zero_iff S.zero).mpr S.zero_algebraic

/-- **L1 (quantum of unpaidness):** an unpaid charge carries STRICTLY
    positive height — "quantization" is honest: between "paid" and
    "not paid" lies a whole quantum. -/
theorem unpaid_height_pos {S : HodgeLedger} {c : S.Cls}
    (hna : ¬ S.IsAlgebraic c) : 0 < S.height c :=
  Nat.pos_of_ne_zero (fun h0 => hna ((S.height_zero_iff c).mp h0))

/-- **L2 — the exact classical characterization of the conjecture:** the conjecture ⟺
    there are no unpaid classes (mirror of YM `not_massGap_iff_gapless`). -/
theorem hodgeProperty_iff_no_unpaidClass (S : HodgeLedger) :
    HodgeProperty S ↔ ¬ Nonempty (UnpaidClass S) := by
  constructor
  · rintro hP ⟨⟨c, hc, hna⟩⟩
    exact hna (hP c hc)
  · intro hNo c hc
    by_contra hna
    exact hNo ⟨⟨c, hc, hna⟩⟩

theorem not_hodgeProperty_iff_unpaidClass (S : HodgeLedger) :
    ¬ HodgeProperty S ↔ Nonempty (UnpaidClass S) := by
  rw [hodgeProperty_iff_no_unpaidClass, not_not]

/-#############################################################################
  §2. ENGINE OBJECT: the unpaid descent chain — dead UNCONDITIONALLY
#############################################################################-/

/-- **D4. UNPAID DESCENT CHAIN — a perpetual engine in ℕ**: an infinite
    sequence of unpaid Hodge charges with strictly decreasing
    height (analogue of YM's `GaplessLadder`, but over ℕ, where well-foundedness
    WORKS — hence the type is empty unconditionally, see L3). -/
structure UnpaidDescentChain (S : HodgeLedger) where
  seq : ℕ → S.Cls
  hodge : ∀ n, S.IsHodge (seq n)
  unpaid : ∀ n, ¬ S.IsAlgebraic (seq n)
  descent : ∀ n, S.height (seq (n + 1)) < S.height (seq n)

/-- **L3 — the GREEN KILLER (the repository's ROOT), UNCONDITIONAL:** the unpaid
    descent chain = an infinite ℕ-descent = Euclid's perpetual engine;
    killed by `no_infinite_descent` (EPMI, A = 1). DISCLOSED ASYMMETRY WITH YM:
    there the ladders lived exactly under masslessness (`gapless_iff_nonempty_ladder`),
    here quantization is built into the model (height : ℕ) — the engine is dead IN
    ANY model, no conjecture is consumed. -/
theorem no_unpaidDescentChain {S : HodgeLedger}
    (C : UnpaidDescentChain S) : False :=
  EuclidsPath.Engine.no_infinite_descent (le_refl 1)
    (fun t => S.height (C.seq t))
    (fun t => by
      show 1 * S.height (C.seq (t + 1)) < S.height (C.seq t)
      rw [Nat.one_mul]
      exact C.descent t)

/-- **L3′ — EPMI resonance by form:** the type of chains is EMPTY in every model.
    (In YM emptiness of ladders was ⟺ the gap; here — a theorem without hypotheses.) -/
theorem isEmpty_unpaidDescentChain (S : HodgeLedger) :
    IsEmpty (UnpaidDescentChain S) :=
  ⟨no_unpaidDescentChain⟩

/-#############################################################################
  §3. Descent law (per-model 🔴 INPUT) and the HERO
#############################################################################-/

/-- **D5. DESCENT/APPROXIMATION LAW — per-model 🔴 INPUT (NS/YM pattern, like
    `EnergyBalanceLaw`/`QuantizationLaw`):** every unpaid Hodge
    charge admits a payment step — an unpaid Hodge charge of STRICTLY
    smaller height (paying the best approximation strictly decreases the
    denominator of the remainder). For the INTENDED (not constructed!) instantiation
    S = rational (p,p)-classes of a smooth projective variety
    this is precisely the residual mathematical input of the branch. -/
def DescentLaw (S : HodgeLedger) : Prop :=
  ∀ c : S.Cls, S.IsHodge c → ¬ S.IsAlgebraic c →
    ∃ c' : S.Cls, S.IsHodge c' ∧ ¬ S.IsAlgebraic c' ∧
      S.height c' < S.height c

/-- One choice step: the next unpaid charge of strictly smaller height. -/
noncomputable def descentNext {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) : UnpaidClass S :=
  ⟨(hLaw p.1 p.2.1 p.2.2).choose,
   (hLaw p.1 p.2.1 p.2.2).choose_spec.1,
   (hLaw p.1 p.2.1 p.2.2).choose_spec.2.1⟩

theorem descentNext_height_lt {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) :
    S.height (descentNext hLaw p).1 < S.height p.1 :=
  (hLaw p.1 p.2.1 p.2.2).choose_spec.2.2

/-- The recursive choice sequence (`Classical.choice` honestly visible;
    mirror of `ladderSeq`). -/
noncomputable def descentSeq {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) : ℕ → UnpaidClass S
  | 0 => p
  | n + 1 => descentNext hLaw (descentSeq hLaw p n)

@[simp] theorem descentSeq_succ {S : HodgeLedger} (hLaw : DescentLaw S)
    (p : UnpaidClass S) (n : ℕ) :
    descentSeq hLaw p (n + 1) = descentNext hLaw (descentSeq hLaw p n) := rfl

/-- **L4 (substance witness, mirror of `gaplessLadder_of_gapless`):**
    from the law + an unpaid class a chain is BUILT (by choice). Since
    chains do not exist (L3′), this is already a verdict on the pair "law + unpaidness". -/
noncomputable def unpaidDescentChain_of_descentLaw {S : HodgeLedger}
    (hLaw : DescentLaw S) (p : UnpaidClass S) : UnpaidDescentChain S where
  seq := fun n => (descentSeq hLaw p n).1
  hodge := fun n => (descentSeq hLaw p n).2.1
  unpaid := fun n => (descentSeq hLaw p n).2.2
  descent := fun n => by
    show S.height (descentSeq hLaw p (n + 1)).1
        < S.height (descentSeq hLaw p n).1
    rw [descentSeq_succ]
    exact descentNext_height_lt hLaw (descentSeq hLaw p n)

/-- **L5:** the descent law and an unpaid class are INCOMPATIBLE (chain route). -/
theorem no_descentLaw_with_unpaid {S : HodgeLedger}
    (hLaw : DescentLaw S) (p : UnpaidClass S) : False :=
  no_unpaidDescentChain (unpaidDescentChain_of_descentLaw hLaw p)

/-- Payment on every floor of the height: strong induction on the ℕ-height (choice NOT
    needed — a second, direct form of the same EPMI root). -/
theorem algebraic_at_height_of_descentLaw {S : HodgeLedger}
    (hLaw : DescentLaw S) :
    ∀ n : ℕ, ∀ c : S.Cls, S.height c = n → S.IsHodge c → S.IsAlgebraic c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hcn hc
    by_contra hna
    obtain ⟨c', hc', hna', hlt⟩ := hLaw c hc hna
    exact hna' (ih (S.height c') (by omega) c' rfl hc')

/-- **L6 — HERO (green conditional chain, NS/YM pattern):** the descent law ⟹
    the model's Hodge conjecture. Route: strong induction on height. -/
theorem hodgeProperty_of_descentLaw {S : HodgeLedger}
    (hLaw : DescentLaw S) : HodgeProperty S :=
  fun c hc => algebraic_at_height_of_descentLaw hLaw (S.height c) c rfl hc

/-- **L6′ — the same hero via the chain route** (choice + unconditional emptiness
    of chains; both forms, as in YM — the direct killer and the ladder). -/
theorem hodgeProperty_of_descentLaw' {S : HodgeLedger}
    (hLaw : DescentLaw S) : HodgeProperty S := by
  intro c hc
  by_contra hna
  exact no_descentLaw_with_unpaid hLaw ⟨c, hc, hna⟩

/-- **L7 (analogue of YM L7):** a model with the law and an unpaid charge does NOT
    exist. -/
theorem no_unpaid_lawful_model :
    ¬ ∃ S : HodgeLedger, DescentLaw S ∧ Nonempty (UnpaidClass S) := by
  rintro ⟨S, hLaw, ⟨p⟩⟩
  exact no_descentLaw_with_unpaid hLaw p

/-#############################################################################
  §4. The cost mirror and its COLLAPSE (the decisive honesty audit)
#############################################################################-/

/-- **L8 (the reverse side — VACUOUS, disclosed):** the conjecture ⟹ the law:
    the quantifier over unpaid charges is empty. Like the Riemann L5
    (`manifestationLaw_of_RH`), in CONTRAST to YM L8, where the rank was built
    genuinely (`Nat.log 2 ⌊E/Δ⌋₊`). -/
theorem descentLaw_of_hodgeProperty {S : HodgeLedger}
    (hP : HodgeProperty S) : DescentLaw S :=
  fun c hc hna => (hna (hP c hc)).elim

/-- **L9 — THE MAIN AUDIT (collapse of the cost mirror):** the per-model law ⟺
    the model's Hodge conjecture — GREEN and WITHOUT ANY BOUNDARY. The form of a CONDEMNED
    bridge (`offCriticalBridge_iff_RH`, `quantizationLaw_iff_massGap`):
    to decree the law for a model = to decree its conjecture verbatim.
    That is why a per-model decree field is impossible HONESTLY; what is missing is a
    data anchor (genuine rational (p,p)-classes; mathlib has NONE — the
    header), Prop-nonvacuity is the wrong criterion (SpectralAnchorAudit). -/
theorem descentLaw_iff_hodgeProperty (S : HodgeLedger) :
    DescentLaw S ↔ HodgeProperty S :=
  ⟨hodgeProperty_of_descentLaw, descentLaw_of_hodgeProperty⟩

/-#############################################################################
  §5. Forged models (witnesses of the trilemma)
#############################################################################-/

/-- Forged UNPAID model: classes ℕ, the Hodge ones are `{0, 1}`, only
    `0` is paid, height is the identity. The charge `1` is quantized, aligned,
    UNPAID; it has NO descent step. -/
def cookedUnpaid : HodgeLedger where
  Cls := ℕ
  zero := 0
  IsHodge := fun c => c ≤ 1
  IsAlgebraic := fun c => c = 0
  height := fun c => c
  zero_hodge := Nat.zero_le 1
  zero_algebraic := rfl
  height_zero_iff := fun _ => Iff.rfl

theorem cookedUnpaid_one_hodge : cookedUnpaid.IsHodge (1 : ℕ) := le_refl 1

theorem cookedUnpaid_one_unpaid : ¬ cookedUnpaid.IsAlgebraic (1 : ℕ) :=
  Nat.one_ne_zero

/-- Explicit unpaid witness (mirror of `cookedLadder`: presented
    by CONSTRUCTION, without choice) — fuel for V3 and the audits of §7. -/
def cookedUnpaidClass : UnpaidClass cookedUnpaid :=
  ⟨(1 : ℕ), cookedUnpaid_one_hodge, cookedUnpaid_one_unpaid⟩

theorem cookedUnpaid_not_hodgeProperty : ¬ HodgeProperty cookedUnpaid :=
  fun hP => cookedUnpaid_one_unpaid (hP (1 : ℕ) cookedUnpaid_one_hodge)

/-- The forged charge `1` has NO descent step: a step from height 1 would give
    an unpaid class of height 0 — paid by the quantization anchor
    (`height_zero_iff` consumed FOR REAL). -/
theorem cookedUnpaid_no_descent_step :
    ¬ ∃ c' : cookedUnpaid.Cls, cookedUnpaid.IsHodge c' ∧
        ¬ cookedUnpaid.IsAlgebraic c' ∧
        cookedUnpaid.height c' < cookedUnpaid.height (1 : ℕ) := by
  rintro ⟨c', _, hna', hlt⟩
  apply hna'
  apply (cookedUnpaid.height_zero_iff c').mp
  have h1 : cookedUnpaid.height (1 : ℕ) = 1 := rfl
  omega

theorem cookedUnpaid_not_descentLaw : ¬ DescentLaw cookedUnpaid :=
  fun hLaw => cookedUnpaid_no_descent_step
    (hLaw (1 : ℕ) cookedUnpaid_one_hodge cookedUnpaid_one_unpaid)

/-- Forged FULLY PAID model: everything is Hodge, everything is paid,
    height ≡ 0. -/
def cookedPaid : HodgeLedger where
  Cls := ℕ
  zero := 0
  IsHodge := fun _ => True
  IsAlgebraic := fun _ => True
  height := fun _ => 0
  zero_hodge := trivial
  zero_algebraic := trivial
  height_zero_iff := fun _ => ⟨fun _ => trivial, fun _ => rfl⟩

theorem cookedPaid_hodgeProperty : HodgeProperty cookedPaid :=
  fun _ _ => trivial

/-- The law on the paid model — VACUOUSLY (there are no unpaid charges).
    Disclosed: this is why a V2 decree would add nothing. -/
theorem cookedPaid_descentLaw : DescentLaw cookedPaid :=
  descentLaw_of_hodgeProperty cookedPaid_hodgeProperty

theorem cookedPaid_no_unpaidClass : ¬ Nonempty (UnpaidClass cookedPaid) :=
  (hodgeProperty_iff_no_unpaidClass cookedPaid).mp cookedPaid_hodgeProperty

/-#############################################################################
  §6. TRILEMMA of the sixth boundary of the decree — all verdicts are machine-made
#############################################################################-/

/-- **D6a. CANDIDATE 1 (universal form of the sixth field).** -/
def HodgeDescentLawUniversal : Prop :=
  ∀ S : HodgeLedger, DescentLaw S

/-- **D6b. CANDIDATE 2 (existential form).** -/
def HodgeDescentLawExistential : Prop :=
  ∃ S : HodgeLedger, DescentLaw S ∧ HodgeProperty S

/-- **D6c. CANDIDATE 3 (manifestation form, Riemann mirror)** — over a
    PRESENTABLE type of witnesses: a single unpaid class
    (`UnpaidClass`), NOT a chain — the chain form degenerates into a green V2
    (`hodgeChainManifestationLaw_green` below). The same supply object
    `DeviationFlowSupply` as in riemannBoundary/YM/NS; the family is FREE
    of c — D-inertness exposed by the audits of §7. -/
def UnpaidClassManifests {S : HodgeLedger} (_c : UnpaidClass S) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def HodgeManifestationLaw : Prop :=
  ∀ (S : HodgeLedger) (c : UnpaidClass S), UnpaidClassManifests c

/-- **V1: CANDIDATE 1 GREEN-REFUTABLE** — its decree would make the quarantine
    inconsistent. Witness: cookedUnpaid (a descent step from height 1 runs
    into the quantization anchor). -/
theorem hodgeLawUniversal_refuted : ¬ HodgeDescentLawUniversal :=
  fun h => cookedUnpaid_not_descentLaw (h cookedUnpaid)

/-- **V2: CANDIDATE 2 GREEN-PROVABLE** — the decree would be vacuous.
    Witness: cookedPaid (the law is vacuous, the conjecture verbatim). -/
theorem hodgeLawExistential_green : HodgeDescentLawExistential :=
  ⟨cookedPaid, cookedPaid_descentLaw, cookedPaid_hodgeProperty⟩

/-- Chain-manifestation candidate (the YM D6c form over ladders,
    mechanically transferred to chains). -/
def ChainManifests {S : HodgeLedger} (_C : UnpaidDescentChain S) : Prop :=
  ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
    SemanticExtendedFlowLedgerCollisionResolves proj →
      DeviationFlowSupply A M0

def HodgeChainManifestationLaw : Prop :=
  ∀ (S : HodgeLedger) (C : UnpaidDescentChain S), ChainManifests C

/-- **V2′: THE CHAIN FORM IS DEGENERATE — GREEN-PROVABLE (a V2-type verdict, NOT
    V3!):** chains do not exist in any model (L3), hence the law over
    them is vacuous. The KEY structural asymmetry with YM (disclosed): there
    the ladder was conditionally habitable and its manifestation form gave
    a genuine V3; here the quantized engine is dead unconditionally — an honest
    V3 witness must be a single class (D6c). -/
theorem hodgeChainManifestationLaw_green : HodgeChainManifestationLaw :=
  fun _S C => (no_unpaidDescentChain C).elim

/-- **V3: CANDIDATE 3 IS INCOMPATIBLE WITH THE ACCEPTED BOUNDARY** (green conditional
    form, taint-free, mirror of YM/NS V3): the forged unpaid class — in
    contrast to an off-critical zero — is greenly PRESENTABLE; law + boundary ⟹
    False (the boundary gives a resolving projection (M0 = 1) → the law supplies
    `DeviationFlowSupply` → `no_deviationFlowSupply_at_resolved_scale`
    burns it). That is why the sixth field of this form would BLOW UP the quarantine. -/
theorem hodgeManifestationLaw_refutes_boundary
    (hLaw : HodgeManifestationLaw) : ¬ TheStrictLastStep00Obligation := by
  rintro ⟨A, projOf, hres⟩
  have hResolves : SemanticExtendedFlowLedgerCollisionResolves (projOf 1) :=
    strictSemanticExtended_resolves_old (hres 1)
  exact no_deviationFlowSupply_at_resolved_scale (projOf 1) hResolves
    (hLaw cookedUnpaid cookedUnpaidClass A 1 (projOf 1) hResolves)

/-- Contraposition for readability: under the accepted boundary there is NO law. -/
theorem not_hodgeManifestationLaw_of_boundary
    (hBoundary : TheStrictLastStep00Obligation) : ¬ HodgeManifestationLaw :=
  fun hLaw => hodgeManifestationLaw_refutes_boundary hLaw hBoundary

/-- **V3 characterization (unconditional — the quantifier is greenly habitable,
    cookedUnpaidClass):** the law ⟺ a global freeze of all ledgers. -/
theorem hodgeManifestationLaw_iff_no_resolution :
    HodgeManifestationLaw ↔
      ∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        ¬ SemanticExtendedFlowLedgerCollisionResolves proj := by
  constructor
  · intro hLaw A M0 proj hres
    exact no_deviationFlowSupply_at_resolved_scale proj hres
      (hLaw cookedUnpaid cookedUnpaidClass A M0 proj hres)
  · intro hFreeze S c A M0 proj hres
    exact ((hFreeze A M0 proj) hres).elim

/-#############################################################################
  §7. Origin-anchor audits (instantiation of the condemning machine)
#############################################################################-/

/-- **A1 (bundling audit, instantiation of `front_pair_iff_no_zero`):**
    Bridge∧Impossible for the family of manifestations ⟺ there are no unpaid classes. -/
theorem hodge_bundling_audit (S : HodgeLedger) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun c : UnpaidClass S => UnpaidClassManifests c) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun c : UnpaidClass S => UnpaidClassManifests c)) ↔
      ¬ Nonempty (UnpaidClass S) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_no_zero _

/-- **A1′ (sharpening via L2):** the bundle is exactly the HODGE CONJECTURE of the model
    (instantiation of `front_pair_iff_RH` with RH := HodgeProperty S). -/
theorem hodge_front_pair_iff_hodgeProperty (S : HodgeLedger) :
    (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
        (fun c : UnpaidClass S => UnpaidClassManifests c) ∧
     EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
        (fun c : UnpaidClass S => UnpaidClassManifests c)) ↔
      HodgeProperty S :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.front_pair_iff_RH
    (hodgeProperty_iff_no_unpaidClass S).symm

/-- **A2 (asymmetry with Riemann, machine-wise):** on the forged model the bundle
    is REFUTED — an unpaid class is presented. The Bridge side
    MUST NOT be decreed. -/
theorem hodge_bundle_refuted_at_cooked :
    ¬ (EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Bridge
         (fun c : UnpaidClass cookedUnpaid => UnpaidClassManifests c) ∧
       EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.Impossible
         (fun c : UnpaidClass cookedUnpaid => UnpaidClassManifests c)) :=
  fun h => (hodge_bundling_audit cookedUnpaid).mp h ⟨cookedUnpaidClass⟩

/-- **A3 (Z-free collapse, lesson of SpectralAnchorAudit):** the family
    of manifestations is FREE of the class — it collapses to a single c-independent
    "atom" question. -/
theorem hodgeLaw_freeCollapse (S : HodgeLedger) :
    EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.FreeLawCollapse
      (fun c : UnpaidClass S => UnpaidClassManifests c)
      (∀ (A M0 : ℕ) (proj : SemanticExtendedFlowLedgerProjection A M0),
        SemanticExtendedFlowLedgerCollisionResolves proj →
          DeviationFlowSupply A M0) :=
  fun _c => Iff.rfl

/-- **A4:** hence the family does not separate unpaid classes — a free
    law carries no information about the deviation (the same reason it
    is unfit for a decree field). -/
theorem hodgeLaw_cannot_separate (S : HodgeLedger) :
    ¬ EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.ZeroSeparating
        (fun c : UnpaidClass S => UnpaidClassManifests c) :=
  EuclidsPath.Riemann.ArithmeticTwoTransport.OriginAnchorAudit.no_zero_separation_under_freeCollapse
    (hodgeLaw_freeCollapse S)

end Hodge
end EuclidsPath

-- Machine-visible purity in the build log
-- (expected [propext, Classical.choice, Quot.sound]):
#print axioms EuclidsPath.Hodge.isEmpty_unpaidDescentChain
#print axioms EuclidsPath.Hodge.hodgeProperty_of_descentLaw
#print axioms EuclidsPath.Hodge.descentLaw_iff_hodgeProperty
#print axioms EuclidsPath.Hodge.hodgeLawUniversal_refuted
#print axioms EuclidsPath.Hodge.hodgeLawExistential_green
#print axioms EuclidsPath.Hodge.hodgeChainManifestationLaw_green
#print axioms EuclidsPath.Hodge.hodgeManifestationLaw_refutes_boundary
