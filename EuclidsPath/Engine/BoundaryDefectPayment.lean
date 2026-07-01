/-
  BoundaryDefectPayment — boundary-дефект ⟹ engine ИЛИ невозможная оплата.
  Источник: EuclidsPath_boundary_defect_payment_engine_patch (внешний аудит-кирпич).
  Проза: prose/24_BoundaryDecomp.md (раздел «Boundary-дефект и платёжный ledger»).

  Локализует первый материальный дефект после BoundaryExit: `¬Clean A n` разворачивается в
  конкретную арифметику `∃ q≤A prime, q ∣ 6n±1` (`SmallPrimeDefect`). Доказано: извлечение дефекта
  (`boundaryExit_has_smallPrimeDefect`) и НЕВОЗМОЖНОСТЬ no-tax-оплаты (`noTaxPaymentCertificate_impossible`
  через shifted-primorial из `PaymentLedger`). Единственный вход — дихотомия
  `BoundaryDefectCreatesCycleOrImpossiblePayment` (дефект ⟹ цикл ∨ невозможная оплата). НЕ закрывает Step00.
-/
import EuclidsPath.Engine.CleanGraph
import EuclidsPath.Engine.PaymentLedger
import EuclidsPath.Engine.LabelledFanIn

set_option autoImplicit false
set_option linter.unusedVariables false

namespace EuclidsPath

namespace BoundaryDefectPayment

open EuclidsPath.CleanGraph
open EuclidsPath.Payment
open EuclidsPath.LabelledFanIn

/-#############################################################################
  §1. The actual defect produced by a clean boundary exit
#############################################################################-/

/--
`SmallPrimeDefect A n` is the material content of `¬ Clean A n`.

It says that the state `n` has a small prime obstruction on one of the two twin
sides.  This is the first concrete defect produced by the clean/boundary split.
-/
def SmallPrimeDefect (A n : ℕ) : Prop :=
  ∃ q : ℕ,
    q.Prime ∧ q ≤ A ∧
      (q ∣ (6 * n - 1) ∨ q ∣ (6 * n + 1))

/--
A `BoundaryExit` really produces a small-prime defect.

This is the precise point where the defect appears:

  Clean A m ∧ ActiveEdge A m n ∧ ¬ Clean A n

unfolds the last conjunct to

  ∃ q prime, q ≤ A and q divides one of `6n±1`.
-/
theorem boundaryExit_has_smallPrimeDefect {A m n : ℕ}
    (hExit : BoundaryExit A m n) : SmallPrimeDefect A n := by
  classical
  rcases hExit with ⟨_hmClean, _hEdge, hnNotClean⟩
  unfold SmallPrimeDefect
  unfold Clean at hnNotClean
  push_neg at hnNotClean
  exact hnNotClean

/-#############################################################################
  §2. Certified impossible payment
#############################################################################-/

/--
A strict no-tax payment certificate.

Interpretation:
* `G` is the finite set of small primes through which the boundary wants to pass
  for free;
* `noTax` says every such prime divides the shifted charge `a - θ`;
* `product_eq` identifies `P` with the corresponding primorial/product;
* `shift_bound` and `late_bound` say the shifted charge is too small to carry
  that whole product;
* `nontrivial` excludes the degenerate zero-shift `a = θ`.

The already-proved shifted-primorial obstruction makes such a certificate
impossible.
-/
structure NoTaxPaymentCertificate (G : Finset ℕ) (a θ Z P : ℤ) : Prop where
  pairwiseCoprime : (G : Set ℕ).Pairwise Nat.Coprime
  noTax : ∀ q ∈ G, (q : ℤ) ∣ a - θ
  product_eq : P = G.prod (fun q => (q : ℤ))
  shift_bound : |a - θ| ≤ Z
  late_bound : Z < P
  nontrivial : a ≠ θ

/--
A nontrivial no-tax payment certificate is impossible.

This uses only the existing payment algebra:

  `primorial_dvd_shift`
  `late_boundary_not_free`

No Step00 arithmetic is hidden here.
-/
theorem noTaxPaymentCertificate_impossible {G : Finset ℕ} {a θ Z P : ℤ}
    (h : NoTaxPaymentCertificate G a θ Z P) : False := by
  have hdvdProd : (G.prod (fun q => (q : ℤ))) ∣ a - θ :=
    EuclidsPath.Payment.primorial_dvd_shift h.pairwiseCoprime h.noTax
  have hdvdP : P ∣ a - θ := by
    rw [h.product_eq]
    exact hdvdProd
  have heq : a = θ :=
    EuclidsPath.Payment.late_boundary_not_free hdvdP h.shift_bound h.late_bound
  exact h.nontrivial heq

/--
`ImpossiblePayment` packages the existence of a certified nontrivial no-tax
payment.  It is a proposition with an immediate contradiction theorem below.
-/
def ImpossiblePayment : Prop :=
  ∃ (G : Finset ℕ) (a θ Z P : ℤ), NoTaxPaymentCertificate G a θ Z P

/-- Any `ImpossiblePayment` is false by the shifted-primorial obstruction. -/
theorem impossiblePayment_false (h : ImpossiblePayment) : False := by
  rcases h with ⟨G, a, θ, Z, P, hcert⟩
  exact noTaxPaymentCertificate_impossible hcert

/-#############################################################################
  §3. The named real obligation: defect resolution
#############################################################################-/

variable {σ : Type*}

/--
The exact next Step00 obligation.

Every small-prime boundary defect must resolve in one of two ways:

1. it creates a genuine nonempty legal cycle in the same real-step graph;
2. it gives a certified impossible payment.

This is intentionally an input, not a theorem: proving it is the actual local
arithmetic content still missing from the Step00 graph.
-/
def BoundaryDefectCreatesCycleOrImpossiblePayment
    (A : ℕ) (RealStep : σ → σ → Prop) (Legal : σ → Prop) : Prop :=
  ∀ {n : ℕ}, SmallPrimeDefect A n →
    (∃ W : σ, Legal W ∧ NonemptyPath RealStep W W) ∨ ImpossiblePayment

/--
A boundary exit reaches the named resolution law by first extracting its
small-prime defect.
-/
theorem boundaryExit_creates_cycle_or_impossiblePayment
    {A m n : ℕ} {RealStep : σ → σ → Prop} {Legal : σ → Prop}
    (hResolve : BoundaryDefectCreatesCycleOrImpossiblePayment A RealStep Legal)
    (hExit : BoundaryExit A m n) :
    (∃ W : σ, Legal W ∧ NonemptyPath RealStep W W) ∨ ImpossiblePayment :=
  hResolve (boundaryExit_has_smallPrimeDefect hExit)

/-#############################################################################
  §4. From cycle/payment resolution to Euclidean engine
#############################################################################-/

/--
If every boundary defect either gives a legal cycle or an impossible payment,
then every boundary exit gives a Euclidean engine.

The cycle branch is consumed by `CycleBridge`; the payment branch is impossible
by §2.
-/
theorem boundaryExit_forces_engine_of_resolution
    {A m n : ℕ} {RealStep : σ → σ → Prop} {Legal : σ → Prop}
    {EuclideanEngine : Prop}
    (hBridge : CycleBridge (RealStep := RealStep) Legal EuclideanEngine)
    (hResolve : BoundaryDefectCreatesCycleOrImpossiblePayment A RealStep Legal)
    (hExit : BoundaryExit A m n) : EuclideanEngine := by
  rcases boundaryExit_creates_cycle_or_impossiblePayment hResolve hExit with hCycle | hPay
  · exact hBridge hCycle
  · exact False.elim (impossiblePayment_false hPay)

/--
Under a local height witness, the same result specializes to contradiction
(`EuclideanEngine := False`).

This is the anti-vacuum check: if a concrete Step00 instantiation provides both
  * a strict local height for every real step, and
  * the boundary-defect resolution law,
then `BoundaryExit` cannot occur.

So any proof that all fresh clean starts must boundary-exit must also explain
which hypothesis fails, or else it has produced the desired contradiction.
-/
theorem boundaryExit_impossible_under_height_of_resolution
    {A m n : ℕ} {RealStep : σ → σ → Prop} {Legal : σ → Prop}
    (height : σ → ℕ)
    (hdrop : ∀ {U V : σ}, RealStep U V → height U < height V)
    (hResolve : BoundaryDefectCreatesCycleOrImpossiblePayment A RealStep Legal)
    (hExit : BoundaryExit A m n) : False := by
  exact boundaryExit_forces_engine_of_resolution
    (A := A) (m := m) (n := n)
    (RealStep := RealStep) (Legal := Legal) (EuclideanEngine := False)
    (cycleBridge_of_height height hdrop) hResolve hExit

/-#############################################################################
  §5. Audit summary as Lean-level names
#############################################################################-/

/--
TheRealObligation is deliberately just an alias with a loud name.

To move past the current wall, instantiate this for the actual 6m±1 Step00
`RealStep` and `Legal` graph.  Until then, the proof has only shown where the
boundary defect enters the ledger, not that the ledger closes.
-/
abbrev TheRealObligation
    (A : ℕ) (RealStep : σ → σ → Prop) (Legal : σ → Prop) : Prop :=
  BoundaryDefectCreatesCycleOrImpossiblePayment A RealStep Legal

end BoundaryDefectPayment

end EuclidsPath
