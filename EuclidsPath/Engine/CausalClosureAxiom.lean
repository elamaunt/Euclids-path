/-
  CausalClosureAxiom — КАРАНТИННЫЙ модуль: ЕДИНСТВЕННЫЙ `axiom` всего репозитория.
  Проза: prose/24_BoundaryDecomp.md (раздел «Causal-closure как внешняя аксиома»).

  ⚠️⚠️⚠️ ВНИМАНИЕ. Этот модуль СОЗНАТЕЛЬНО объявляет аксиому
    `step00CausalClosure : TheStrictLastStep00Obligation`
  — это ОТКРЫТЫЙ ФИНАЛЬНЫЙ УЗЕЛ, принятый декретом, а НЕ доказанный факт.
  Всё, что от неё зависит (включая `twinLowersInfinite_from_step00CausalClosure :
  TwinLowers.Infinite`), — УСЛОВНО НА АКСИОМЕ и НЕ является доказательством
  гипотезы близнецов. `Step00.twin_prime_conjecture` остаётся `sorry` и НЕ
  замыкается через этот модуль.

  Карантин машинно отслеживается: узловой верификатор репортит каждую
  декларацию, заражённую нестандартной аксиомой (`AXIOM-TAINTED`). Ожидаемое
  состояние: заражены РОВНО декларации этого модуля — и никакие другие.

  Смысл кирпича (честный): зафиксировать последний Step00-принцип как ЯВНУЮ
  внешнюю аксиому, а не как скрытую теорему; и показать (уже доказано в
  ConcreteStep00Graph), что его внутреннее самозаверение строит запрещённый
  двигатель. Машинная честность: аксиома ⟺ старый узел
  (`strictLastStep00Obligation_iff_lastStep00Obligation`), и она УЖЕ утверждает
  близнецов на каждом масштабе (`causalClosureAxiom_asserts_twins_at_every_scale`)
  — принять её = принять близнецов, декрет не слабее вывода.
-/
import EuclidsPath.Engine.ConcreteStep00Graph

set_option autoImplicit false

namespace EuclidsPath
namespace ConcreteStep00Graph
namespace GeneratedFlowFormulation

/-#############################################################################
  §1. The external causal-closure principle
#############################################################################-/

/--
The Step00 causal-closure axiom, stated in the strict return-certificate form.

Unfolded, it says that there is a fixed scale `A` and, for every alleged last
twin bound `M0`, a finite semantic flow-ledger projection `ΠOf M0` such that
same-key collisions of extended generated-flow genealogies are not free
information-loss.  They must be resolved by the strict local resolver, i.e. by
an explicit return certificate or the already audited payment alternative.

This is the exact final principle previously called
`TheStrictLastStep00Obligation`.
-/
abbrev Step00CausalClosureAxiom : Prop :=
  TheStrictLastStep00Obligation

/--
The single external axiom of this patch — AND OF THE WHOLE REPOSITORY.

Reading: Step00 causal closure is accepted as an outside universe-generating
principle.  It is not derived by the internal no-engine machinery.

⚠️ Everything depending on this axiom is CONDITIONAL and machine-flagged by
the node verifier as AXIOM-TAINTED.
-/
axiom step00CausalClosure : Step00CausalClosureAxiom

/-#############################################################################
  §2. What the axiom generates (⚠️ conditional on the axiom, NOT proofs)
#############################################################################-/

/--
As an external axiom, Step00 causal closure proves infinitude of lower twin
centres.  ⚠️ AXIOM-TAINTED: this is NOT a proof of the twin-prime conjecture;
it is the reduction closed by decree.
-/
theorem twinLowersInfinite_from_step00CausalClosure :
    TwinLowers.Infinite :=
  twinLowersInfinite_of_strictLastStep00Obligation step00CausalClosure

/--
Equivalent named theorem: adding the causal-closure axiom closes the Step00
universe.  ⚠️ AXIOM-TAINTED.
-/
theorem step00CausalClosure_generates_twins :
    TwinLowers.Infinite :=
  twinLowersInfinite_from_step00CausalClosure

/-#############################################################################
  §3. Why the axiom is external, not internally self-certified
#############################################################################-/

/--
An internal self-derivation attempt of the causal-closure axiom.

This is the already audited boundary-crossing shape: the principle is available
as a proposition and is then converted back into an internal stable Step00
decision attempt.  The previous patches prove that such internalisation builds
the forbidden engine.
-/
abbrev InternalSelfDerivationOfStep00CausalClosure : Prop :=
  BoundaryCrossingSelfProof Step00CausalClosureAxiom

/--
Any internal self-derivation of Step00 causal closure builds the forbidden
concrete Euclidean engine.  (Axiom-free.)
-/
theorem internalSelfDerivation_step00CausalClosure_builds_engine
    (B : InternalSelfDerivationOfStep00CausalClosure) :
    SomeConcreteEuclideanEngine :=
  boundaryCrossingSelfProof_builds_engine B

/--
Therefore Step00 causal closure cannot be internally self-derived in the
stable no-engine Step00 architecture.  (Axiom-free.)
-/
theorem no_internalSelfDerivation_step00CausalClosure :
    ¬ InternalSelfDerivationOfStep00CausalClosure :=
  no_boundaryCrossingSelfProof

/--
If one nevertheless supplies an internal self-derivation, contradiction follows.
(Axiom-free.)
-/
theorem internalSelfDerivation_step00CausalClosure_contradiction
    (B : InternalSelfDerivationOfStep00CausalClosure) : False :=
  no_internalSelfDerivation_step00CausalClosure B

/-#############################################################################
  §4. External-only package
#############################################################################-/

/--
The causal-closure axiom as an external-only principle: it is accepted as an
outside axiom, and it cannot be self-certified internally without the forbidden
engine.
-/
abbrev Step00CausalClosureExternalOnly : Prop :=
  Step00CausalClosureAxiom ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure

/--
The external-only status of the causal-closure axiom.  ⚠️ AXIOM-TAINTED
(первый конъюнкт — сама аксиома).
-/
theorem step00CausalClosure_externalOnly :
    Step00CausalClosureExternalOnly := by
  exact ⟨step00CausalClosure, no_internalSelfDerivation_step00CausalClosure⟩

/--
The axiom both generates the twin conclusion and refuses internal
self-certification without a forbidden engine.  ⚠️ AXIOM-TAINTED.
-/
abbrev Step00CausalClosureGeneratesButDoesNotSelfCertify : Prop :=
  TwinLowers.Infinite ∧
    ¬ InternalSelfDerivationOfStep00CausalClosure

/-- Realisation of the final audit slogan.  ⚠️ AXIOM-TAINTED. -/
theorem step00CausalClosure_generatesButDoesNotSelfCertify :
    Step00CausalClosureGeneratesButDoesNotSelfCertify := by
  exact ⟨twinLowersInfinite_from_step00CausalClosure,
         no_internalSelfDerivation_step00CausalClosure⟩

/-#############################################################################
  §5. Self-proving engine contradiction, specialised to the axiom
#############################################################################-/

/--
A self-proving Step00 causal-closure engine is just an internal self-derivation
of the external causal-closure axiom.  The name records the intended audit
reading: if the axiom tries to prove itself from within the no-engine universe,
it becomes a forbidden engine construction.
-/
abbrev SelfProvingStep00CausalClosureEngine : Prop :=
  InternalSelfDerivationOfStep00CausalClosure

/-- A self-proving causal-closure engine builds a concrete Euclidean engine.
(Axiom-free.) -/
theorem selfProvingStep00CausalClosureEngine_builds_engine
    (H : SelfProvingStep00CausalClosureEngine) :
    SomeConcreteEuclideanEngine :=
  internalSelfDerivation_step00CausalClosure_builds_engine H

/-- No self-proving causal-closure engine exists.  (Axiom-free.) -/
theorem no_selfProvingStep00CausalClosureEngine :
    ¬ SelfProvingStep00CausalClosureEngine :=
  no_internalSelfDerivation_step00CausalClosure

/--
Formal version of the slogan:

  “a perpetual engine proving itself is contradiction.”

Here the perpetual engine is the internal self-proof of the external causal
closure principle; by the earlier audit it builds a forbidden concrete engine,
and forbidden engines are impossible by `lexRank` acyclicity.  (Axiom-free.)
-/
theorem selfProvingStep00CausalClosureEngine_is_contradiction
    (H : SelfProvingStep00CausalClosureEngine) : False :=
  no_selfProvingStep00CausalClosureEngine H

/-#############################################################################
  §6. Scope marker: axiomatisation, not global independence
#############################################################################-/

/--
Marker proposition recording the intended scope.

This is deliberately just `True`: the real content is in the theorems above.
It prevents the axiom patch from being read as a Gödel-style independence proof
for the ordinary twin-prime conjecture.  No external proof system, model theory,
or relative consistency theorem is asserted here.
-/
abbrev ThisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem : Prop :=
  True

theorem thisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem :
    ThisIsAnExternalStep00AxiomNotAGlobalIndependenceTheorem := by
  trivial

/-#############################################################################
  §7. Машинная честность аксиомы
#############################################################################-/

/-- **ЧЕСТНОСТЬ (машинно): аксиома УЖЕ утверждает близнецов на каждом масштабе.**
    Из аксиомы на каждом `M0` извлекается twin выше `M0` (через
    `twin_above_of_strictResolves`): декрет не слабее вывода — принять аксиому
    = принять близнецов по-масштабно. Аксиома ⟺ старый узел
    (`strictLastStep00Obligation_iff_lastStep00Obligation`). ⚠️ AXIOM-TAINTED. -/
theorem causalClosureAxiom_asserts_twins_at_every_scale :
    ∀ M0 : ℕ, ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m := by
  intro M0
  obtain ⟨A, projOf, h⟩ := step00CausalClosure
  exact twin_above_of_strictResolves (projOf M0) (h M0)

end GeneratedFlowFormulation
end ConcreteStep00Graph
end EuclidsPath
