/-
  PNPRankPaymentFront — ЗЕЛЁНЫЙ (аксиомо-свободный) модуль P/NP-прочтения
  автора: «NP-задача = ПОЛНАЯ ОПЛАТА всех сертификатов ранга; P = движение
  двигателя, быстро проезжающее ранг НЕ посещая все состояния» — и неравенство
  между ними КАК ТЕОРЕМА при стандартных аксиомах.

  Архитектура:
    * P-сторона: `RankFastTraversal` — всякое легальное движение ограничено
      СТАРТОВЫМ рангом (закон каждого ранжированного графа, `len_le_lexRank`);
    * NP-сторона: `FullRankCertificatePayment` — поиск решён, только когда
      КАЖДЫЙ сертификат семейства учтён инъективным конечным ключом;
    * СЕРДЦЕ (L5): ранго-быстрое конечноключевое движение не может полностью
      оплатить неограниченное семейство сертификатов — пигеонхол;
    * ДИХОТОМИЯ ОПЛАТЫ (L8/L9): LocalPSuccess ⟺ FullRankCertificatePayment на
      КАЖДОМ масштабе — обе альтернативы разрешения сожжены зелёно
      (`no_extendedFlowResolutionAlternative`), «NP = полная оплата» — теорема;
    * ЗЕЛЁНАЯ СЕПАРАЦИЯ (L10, A ≤ 4): быстрый проезд ∧ лёгкая проверка ∧
      неограниченная поставка (5-адика) ∧ ¬полная оплата ∧ несжимаемость.

  РАСКОЛ ПО МАСШТАБАМ (машинно, L14–L16): принятая причинная граница
  (`TheStrictLastStep00Obligation`, как ГИПОТЕЗА — модуль карантин НЕ импортирует)
  на своём масштабе A ≥ 5 даёт LocalPSuccess на каждом M0 — там декрет ПЛАТИТ
  все сертификаты и ограничивает поставку; сепарация живёт на A ≤ 4.
  ИНВЕРТИРОВАННАЯ АСИММЕТРИЯ против Римана (раскрыта, не подделана): для
  сепарации граница НЕ нужна — убийца зелёный; неиспользуемая hBoundary в
  essence НЕ добавлена.

  ЧЕСТНОСТЬ (машинно, обязательные аудиты):
    * ТРИЛЕММА кандидатов «третьей границы декрета» — все вердикты теоремы:
      V1 универсальная форма ОПРОВЕРЖИМА (allPFrame — декрет был бы
      противоречив); V3 decider-gated форма ОПРОВЕРЖИМА (PDecider классически
      свободен); V2 экзистенциальная форма УЖЕ ДОКАЗАНА (constantsFrame —
      декрет был бы вакуумен). Честного третьего поля НЕ СУЩЕСТВУЕТ;
      подлинно недостающее — data-anchored реальная машинная модель
      (урок SpectralAnchorAudit: Prop-невакуумность — неверный критерий).
    * ВАКУУМНОСТЬ №4 (ВСКРЫТА, A3–A5): decider-gated extraction-фронты
      СУЩЕСТВУЮЩЕГО кода (`FaithfulSelfReductionFront`,
      `CurrentExtractionFront`) классически ПУСТЫ — `PDecider` не несёт
      complexity-содержания и строится классически для любого языка, потому
      связка «extraction + несжимаемость» необитаема; их
      `gives_classicalSeparation` вакуумны. InP-gated мост
      (`Step00ToClassicalBridge`) НЕ затронут — InP абстрактен.
    * ПЛАСТИЧНОСТЬ ФРЕЙМОВ (A6/A7): `allPFrame` faithful + классы совпадают
      даром; `constantsFrame` faithful + P⊆NP + разделяет даром — абстрактный
      слой фреймов куётся в любую сторону; никакое утверждение о НАСТОЯЩИХ
      P/NP отсюда не следует и НЕ объявляется.
  Этот модуль НЕ импортирует карантин; axiom/sorry нет — верификатор обязан
  показать все декларации незаражёнными.
-/
import Mathlib
import EuclidsPath.Engine.ConcreteStep00Graph
import EuclidsPath.Engine.LocalPNPNode
import EuclidsPath.Engine.CanonicalSelfReduction

set_option autoImplicit false

namespace EuclidsPath
namespace PNPRankPayment

open EuclidsPath.ConcreteStep00Graph
open EuclidsPath.ConcreteStep00Graph.GeneratedFlowFormulation
open EuclidsPath.LocalPNP
open EuclidsPath.LocalPNP.Concrete
open EuclidsPath.ClassicalPNPBridge
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction
open EuclidsPath.ClassicalPNPBridge.PDeciderExtraction.CanonicalSelfReduction

-- НЕ открываем ConcreteStep00Graph.PvsNPAnalogy: коллизии имён
-- (PolyCertificateSuffices, VerificationEasy) с LocalPNP.

/-#############################################################################
  §1. Язык автора: оплата сертификатов и ранго-быстрый проезд
#############################################################################-/

/-- **D1. ПОЛНАЯ ОПЛАТА СЕРТИФИКАТОВ РАНГА (NP-прочтение):** поиск решён,
    только когда КАЖДЫЙ сертификат семейства учтён индивидуально —
    инъективное конечноключевое сжатие всей семьи генеалогий. -/
def FullRankCertificatePayment {G : RankedForwardGraph}
    (F : GenealogyFamily G) : Prop :=
  ∃ C : FiniteKeyCompression F, C.Injective

/-- **D2. РАНГО-БЫСТРЫЙ ПРОЕЗД (P-прочтение):** всякое легальное движение
    двигателя ограничено СТАРТОВЫМ рангом — двигатель проезжает ранг,
    не посещая все состояния. -/
def RankFastTraversal (G : RankedForwardGraph) : Prop :=
  ∀ (x y : G.State) (n : Nat), PathN G x y n → n ≤ G.lexRank x

/-- **D3. Неограниченная поставка сертификатов:** семейство генеалогий
    бесконечно. -/
def UnboundedCertificateSupply {G : RankedForwardGraph}
    (F : GenealogyFamily G) : Prop :=
  Infinite F.Index

/-#############################################################################
  §2. Зелёные свидетели: P-закон, лёгкая проверка, пигеонхол
#############################################################################-/

/-- **L1: ранго-быстрый проезд — ЗАКОН каждого ранжированного графа**
    (`PathN.len_le_lexRank`). -/
theorem rankFastTraversal_holds (G : RankedForwardGraph) : RankFastTraversal G :=
  fun _ _ _ p => p.len_le_lexRank

/-- **L2: конкретный Step00-граф проезжает ранг быстро.** -/
theorem concrete_rankFastTraversal (A M0 : ℕ) :
    RankFastTraversal (concreteGraph A M0) :=
  rankFastTraversal_holds _

/-- **L3: проверка ОДНОГО сертификата легка всегда** — verification-сторона. -/
theorem certificate_check_easy {G : RankedForwardGraph}
    (c : GenealogyCertificate G) : GenealogyCertificate.VerificationEasy c :=
  GenealogyCertificate.verificationEasy_always c

/-- **L4: неограниченная поставка ⟹ пигеонхол-принцип** — всякий конечный
    ключ коллидирует. -/
theorem collisionPrinciple_of_unboundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} (hInf : UnboundedCertificateSupply F) :
    FiniteKeyCollisionPrinciple F := by
  intro C
  haveI : Infinite F.Index := hInf
  obtain ⟨i, j, hne, hkey⟩ := Finite.exists_ne_map_eq_of_infinite C.keyOf
  exact ⟨⟨i, j, hne, hkey⟩⟩

/-- **L5 — СЕРДЦЕ НЕРАВЕНСТВА (абстрактно):** ранго-быстрое конечноключевое
    движение НЕ МОЖЕТ полностью оплатить неограниченное семейство
    сертификатов — пигеонхол. -/
theorem no_fullPayment_of_unboundedSupply {G : RankedForwardGraph}
    {F : GenealogyFamily G} (hInf : UnboundedCertificateSupply F) :
    ¬ FullRankCertificatePayment F := by
  rintro ⟨C, hInj⟩
  exact no_injective_finiteKeyCompression_of_collisionPrinciple
    (collisionPrinciple_of_unboundedSupply hInf) C hInj

/-- **L6: конкретная поставка НЕОГРАНИЧЕНА при A ≤ 4** — 5-адическая цепь,
    без единой twin-гипотезы. -/
theorem concreteSupply_unbounded_smallScale {A : ℕ} (hA : A ≤ 4) :
    UnboundedCertificateSupply (concreteFamily A 1) :=
  Infinite.of_injective (fiveAdicChainFlow hA) (fiveAdicChainFlow_injective hA)

/-- **L7: полная оплата конкретной семьи при A ≤ 4 НЕВОЗМОЖНА.** -/
theorem concrete_noFullPayment_smallScale {A : ℕ} (hA : A ≤ 4) :
    ¬ FullRankCertificatePayment (concreteFamily A 1) :=
  no_fullPayment_of_unboundedSupply (concreteSupply_unbounded_smallScale hA)

/-#############################################################################
  §3. Дихотомия оплаты: «NP = полная оплата» как теорема
#############################################################################-/

/-- **L8 (абстрактно): когда альтернатив разрешения НЕТ, локальный P-успех
    ЕСТЬ полная оплата** — конечный ключ обязан учесть каждый сертификат
    инъективно. -/
theorem localPSuccess_iff_fullPayment_of_noResolution {G : RankedForwardGraph}
    {P : Step00LocalSearchProblem G}
    (hNoRes : ∀ i j : P.family.Index, ¬ P.CollisionResolution i j) :
    LocalPSuccess P ↔ FullRankCertificatePayment P.family := by
  constructor
  · rintro ⟨S⟩
    refine ⟨S.compression, ?_⟩
    intro i j hkey
    by_contra hne
    exact hNoRes i j (S.resolves hne hkey)
  · rintro ⟨C, hInj⟩
    exact ⟨{ compression := C
             resolves := fun {i j} hne hkey => absurd (hInj hkey) hne }⟩

/-- **L9 (конкретно, КАЖДЫЙ масштаб):** в Step00-мире обе альтернативы
    разрешения (легальный цикл, невозможная оплата) сожжены зелёно
    (`no_extendedFlowResolutionAlternative`) — потому локальный P-успех ⟺
    полная оплата сертификатов. «NP-задача = полная оплата» — теорема. -/
theorem concrete_localPSuccess_iff_fullPayment (A M0 : ℕ) :
    LocalPSuccess (concreteProblem A M0) ↔
      FullRankCertificatePayment (concreteFamily A M0) :=
  localPSuccess_iff_fullPayment_of_noResolution
    (fun _ _ => no_extendedFlowResolutionAlternative A M0)

/-#############################################################################
  §4. ЗЕЛЁНАЯ СЕПАРАЦИЯ в ранговой модели
#############################################################################-/

/-- **L10 — ЗЕЛЁНАЯ СЕПАРАЦИЯ (сильнейшая безусловная форма, A ≤ 4):**
    двигатель проезжает ранг быстро; каждый сертификат проверяется легко;
    поставка сертификатов неограничена; полная оплата невозможна; потому
    ранго-быстрый искатель проваливается — локальный поиск несжимаем.
    Авторское неравенство одной теоремой, при стандартных аксиомах. -/
theorem pnp_rank_separation_smallScale {A : ℕ} (hA : A ≤ 4) :
    RankFastTraversal (concreteGraph A 1) ∧
    (∀ i : (concreteFamily A 1).Index,
      GenealogyCertificate.VerificationEasy ((concreteFamily A 1).cert i)) ∧
    UnboundedCertificateSupply (concreteFamily A 1) ∧
    ¬ FullRankCertificatePayment (concreteFamily A 1) ∧
    LocalSearchIncompressible (concreteProblem A 1) :=
  ⟨concrete_rankFastTraversal A 1,
   fun _ => GenealogyCertificate.verificationEasy_always _,
   concreteSupply_unbounded_smallScale hA,
   concrete_noFullPayment_smallScale hA,
   fun hP => concrete_noFullPayment_smallScale hA
     ((concrete_localPSuccess_iff_fullPayment A 1).mp hP)⟩

/-- **L11 (масштабно-униформно, условно):** неограниченная поставка ⟹
    несжимаемость — на ЛЮБОМ масштабе. -/
theorem localSearchIncompressible_of_unboundedSupply (A M0 : ℕ)
    (hInf : UnboundedCertificateSupply (concreteFamily A M0)) :
    LocalSearchIncompressible (concreteProblem A M0) :=
  fun hP => no_fullPayment_of_unboundedSupply hInf
    ((concrete_localPSuccess_iff_fullPayment A M0).mp hP)

/-- **L12: twin-bound ⟹ неограниченная поставка** — на любом масштабе
    (закрытая фабрика потоков). -/
theorem concreteSupply_unbounded_of_twinBound {A M0 : ℕ}
    (hTwinBound : TwinBoundAbove M0) :
    UnboundedCertificateSupply (concreteFamily A M0) := by
  obtain ⟨𝓕, h𝓕⟩ := twinBoundForcesInfiniteExtendedGeneratedFlows_closed
    (A := A) (M0 := M0) hTwinBound
  haveI := h𝓕.1.to_subtype
  exact Infinite.of_injective (Subtype.val : 𝓕 → _) Subtype.val_injective

/-- **L13 (зелёная дихотомия на каждом масштабе):** ЛИБО twin выше M0,
    ЛИБО полная оплата невозможна. -/
theorem twin_or_noFullPayment (A M0 : ℕ) :
    (∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m) ∨
    ¬ FullRankCertificatePayment (concreteFamily A M0) := by
  by_cases h : ∃ m : ℕ, M0 < m ∧ EuclidsPath.Residuals.TwinCenterZ m
  · exact Or.inl h
  · refine Or.inr (no_fullPayment_of_unboundedSupply
      (concreteSupply_unbounded_of_twinBound ?_))
    intro m hm hTwin
    exact h ⟨m, hm, hTwin⟩

/-#############################################################################
  §5. Раскол по масштабам (граница как ГИПОТЕЗА — машинно видимый)
#############################################################################-/

/-- **L14: принятая граница даёт ЛОКАЛЬНЫЙ P-УСПЕХ на своём масштабе**
    (обязательно A ≥ 5) на каждом M0 — декрет и малый масштаб живут на
    непересекающихся масштабах. -/
theorem boundary_forces_localPSuccess_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ, LocalPSuccess (concreteProblem A M0) := by
  obtain ⟨A, projOf, hres⟩ := hBoundary
  have hA : 5 ≤ A := by
    by_contra hlt
    exact no_projection_resolves_at_smallScale (by omega) (projOf 1)
      (strictSemanticExtended_resolves_old (hres 1))
  refine ⟨A, hA, fun M0 => ?_⟩
  exact ((concreteSemanticInterface A M0).localPSuccess_iff_semanticFlowLedgerCollisionResolves).mpr
    ⟨projOf M0, strictSemanticExtended_resolves_old (hres M0)⟩

/-- **L15: на декретном масштабе граница ПЛАТИТ ВСЕ СЕРТИФИКАТЫ.** -/
theorem boundary_forces_fullPayment_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      FullRankCertificatePayment (concreteFamily A M0) := by
  obtain ⟨A, hA, hLP⟩ := boundary_forces_localPSuccess_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 =>
    (concrete_localPSuccess_iff_fullPayment A M0).mp (hLP M0)⟩

/-- **L16: на декретном масштабе поставка сертификатов ОГРАНИЧЕНА** — книги
    там сводятся, потому что поставка конечноключево учётна. -/
theorem boundary_bounds_supply_at_decreed_scale
    (hBoundary : TheStrictLastStep00Obligation) :
    ∃ A : ℕ, 5 ≤ A ∧ ∀ M0 : ℕ,
      ¬ UnboundedCertificateSupply (concreteFamily A M0) := by
  obtain ⟨A, hA, hPay⟩ := boundary_forces_fullPayment_at_decreed_scale hBoundary
  exact ⟨A, hA, fun M0 hInf => no_fullPayment_of_unboundedSupply hInf (hPay M0)⟩

/-#############################################################################
  §6. Классический блок честности: PDecider свободен, фронты пусты,
      фреймы пластичны
#############################################################################-/

/-- **A1 (находка): `PDecider` классически СВОБОДЕН** — экстенсиональный
    решатель есть у каждого языка; никакого complexity-содержания в нём нет,
    вся сложность живёт в абстрактном InP. -/
noncomputable def classicalPDecider (L : ClassicalProblem) : PDecider L := by
  classical
  exact
    { run := fun x => decide (L.Accepts x)
      sound := fun x hx => of_decide_eq_true hx
      complete := fun x hx => decide_eq_true hx }

theorem pdecider_free (L : ClassicalProblem) : Nonempty (PDecider L) :=
  ⟨classicalPDecider L⟩

/-- **A2: `ConcretePAccess` свободен** — эта нога extraction-поля бессодержательна. -/
theorem concretePAccess_free (C : ClassicalComplexityFrame) :
    Nonempty (ConcretePAccess C) :=
  ⟨⟨fun L _ => ⟨classicalPDecider L⟩⟩⟩

/-- **A3 (ВАКУУМНОСТЬ №4, ядро):** над несжимаемым узлом НЕ существует
    `CanonicalResolverReconstruction` — свободный decider немедленно дал бы
    LocalPSuccess. -/
theorem isEmpty_canonicalResolverReconstruction_of_incompressible
    {N : Step00LocalNode} (hInc : N.LocalSearchIncompressible)
    (L : ClassicalProblem) (Target : LocalResolverTarget N) :
    IsEmpty (CanonicalResolverReconstruction L Target) :=
  ⟨fun R => hInc (Target.realizes (R.reconstruct (classicalPDecider L)))⟩

/-- **A4: то же для `DeciderGuidedSelfReduction`.** -/
theorem isEmpty_deciderGuidedSelfReduction_of_incompressible
    {N : Step00LocalNode} (hInc : N.LocalSearchIncompressible)
    (L : ClassicalProblem) (Target : LocalResolverTarget N) :
    IsEmpty (DeciderGuidedSelfReduction L Target) :=
  ⟨fun S => hInc (S.localSuccessOfDecider (classicalPDecider L))⟩

/-- **A5 (ВАКУУМНОСТЬ №4, раскрытие о СУЩЕСТВУЮЩЕМ фронте):**
    `FaithfulSelfReductionFront` связывает decider-gated extraction С
    несжимаемостью — классически ПУСТ для любых фрейма и узла; его
    `gives_classicalSeparation` вакуумна. -/
theorem faithfulSelfReductionFront_isEmpty
    (C : ClassicalComplexityFrame) (N : Step00LocalNode) :
    IsEmpty (FaithfulSelfReductionFront C N) :=
  ⟨fun F => F.local_incompressible
    (F.selfReduction.localSuccessOfDecider
      (classicalPDecider F.encoding.genealogyLanguage))⟩

/-- **A5b: `CurrentExtractionFront` пуст по той же причине.** -/
theorem currentExtractionFront_isEmpty
    (C : ClassicalComplexityFrame) (N : Step00LocalNode) :
    IsEmpty (CurrentExtractionFront C N) :=
  ⟨fun F => F.local_incompressible
    (F.strictEncoding.extraction.target.realizes
      (F.strictEncoding.extraction.reconstruction.reconstruct
        (classicalPDecider F.strictEncoding.encoding.genealogyLanguage)))⟩

/-- **A6 (пластичность фреймов, сторона «совпадают»):** фрейм «всё в P» —
    faithful по критерию репозитория, и классы в нём СОВПАДАЮТ даром. -/
def allPFrame : ClassicalComplexityFrame where
  InP := fun _ => True
  InNP := fun _ => True
  P_closed_under_poly_preimage := fun _ _ => trivial

theorem allPFrame_faithful : Nonempty (FaithfulPFrame allPFrame) :=
  ⟨{ concreteP := ⟨fun L _ => ⟨classicalPDecider L⟩⟩
     true_inP := trivial
     false_inP := trivial }⟩

theorem allPFrame_coincides : allPFrame.ClassesCoincide := fun _ => Iff.rfl

/-- Универсального «faithful ⟹ разделение» НЕ существует — машинно. -/
theorem no_universal_faithful_separation :
    ¬ ∀ C : ClassicalComplexityFrame,
        Nonempty (FaithfulPFrame C) → C.ClassesSeparate := by
  intro h
  rcases h allPFrame allPFrame_faithful with ⟨L, _, hNotP⟩
  exact hNotP trivial

/-- **A7 (пластичность, сторона «разделяются»):** фрейм констант — faithful,
    P ⊆ NP, и он РАЗДЕЛЯЕТ даром. -/
def constantsFrame : ClassicalComplexityFrame where
  InP := fun L => (∀ x : L.Instance, L.Accepts x) ∨ (∀ x : L.Instance, ¬ L.Accepts x)
  InNP := fun _ => True
  P_closed_under_poly_preimage := by
    intro A B R hB
    rcases hB with hAll | hNone
    · exact Or.inl (fun x => (R.preserves x).mpr (hAll (R.map x)))
    · exact Or.inr (fun x hx => hNone (R.map x) ((R.preserves x).mp hx))

theorem constantsFrame_faithful : Nonempty (FaithfulPFrame constantsFrame) :=
  ⟨{ concreteP := ⟨fun L _ => ⟨classicalPDecider L⟩⟩
     true_inP := Or.inl (fun _ => trivial)
     false_inP := Or.inr (fun _ h => h) }⟩

/-- Неконстантный язык-свидетель. -/
def boolLanguage : ClassicalProblem := ⟨Bool, fun b => b = true⟩

theorem boolLanguage_not_inP_constantsFrame :
    ¬ constantsFrame.InP boolLanguage := by
  rintro (h | h)
  · exact Bool.false_ne_true (h false)
  · exact h true rfl

theorem some_faithful_frame_separates_greenly :
    ∃ C : ClassicalComplexityFrame, Nonempty (FaithfulPFrame C) ∧
      (∀ L, C.InP L → C.InNP L) ∧ C.ClassesSeparate :=
  ⟨constantsFrame, constantsFrame_faithful, fun _ _ => trivial,
   ⟨boolLanguage, trivial, boolLanguage_not_inP_constantsFrame⟩⟩

/-- **A8: осуждение trivialFrame инстанцировано** — свободно-разделяющий
    фрейм не проходит faithfulness-гейт. -/
theorem trivialFrame_blocked :
    ¬ Nonempty (FaithfulPFrame ClassicalPNPBridge.trivialFrame) :=
  fun ⟨F⟩ => trivialFrame_not_faithful F

/-#############################################################################
  §7. ТРИЛЕММА кандидатов «третьей границы декрета» — все вердикты машинны
#############################################################################-/

/-- **D5a. КАНДИДАТ 1 (универсальная форма):** во всяком faithful-фрейме
    малый масштаб манифестирует как NP-язык, чей P-decider извлекал бы
    локальный резолвер. -/
def PnpManifestationLawUniversal : Prop :=
  ∀ C : ClassicalComplexityFrame, Nonempty (FaithfulPFrame C) →
    ∀ A : ℕ, A ≤ 4 →
      ∃ L : ClassicalProblem, C.InNP L ∧
        (C.InP L → LocalPSuccess (concreteProblem A 1))

/-- **D5b. КАНДИДАТ 2 (экзистенциальная форма):** НЕКОТОРЫЙ faithful-фрейм с
    P ⊆ NP несёт манифестацию. -/
def PnpManifestationLawExistential : Prop :=
  ∃ C : ClassicalComplexityFrame,
    Nonempty (FaithfulPFrame C) ∧ (∀ L, C.InP L → C.InNP L) ∧
    ∀ A : ℕ, A ≤ 4 →
      ∃ L : ClassicalProblem, C.InNP L ∧
        (C.InP L → LocalPSuccess (concreteProblem A 1))

/-- Конкретная резолвер-цель (инстанциация LocalResolverTarget). Резолвер —
    Type-0 обёртка локального P-успеха (`PolyCertificateSuffices` живёт в
    Type 1 и в поле `Resolver : Type` не влезает — PLift Prop-успеха честно
    сохраняет семантику: резолвер = свидетельство разрешающего ключа). -/
def concreteResolverTarget (A M0 : ℕ) :
    LocalResolverTarget (ClassicalPNPBridge.concreteNode A M0) where
  Resolver := PLift (LocalPSuccess (concreteProblem A M0))
  realizes := fun S => S.down
  finite_key_sound := fun _ => True
  finite_key_sound_proof := fun _ => trivial
  rank_bounded := fun _ => True
  rank_bounded_proof := fun _ => trivial
  collision_sound := fun _ => True
  collision_sound_proof := fun _ => trivial

/-- **D5c. КАНДИДАТ 3 (decider-gated форма):** реконструкция из голых
    решателей. -/
def PnpManifestationLawDeciderGated : Prop :=
  ∀ A : ℕ, A ≤ 4 →
    ∃ L : ClassicalProblem,
      Nonempty (CanonicalResolverReconstruction L (concreteResolverTarget A 1))

/-- **V1: КАНДИДАТ 1 ЗЕЛЁНО-ОПРОВЕРЖИМ** — его декрет сделал бы карантин
    противоречивым. Свидетель: allPFrame. -/
theorem pnpLawUniversal_refuted : ¬ PnpManifestationLawUniversal := by
  intro hLaw
  obtain ⟨L, _, hExtract⟩ := hLaw allPFrame allPFrame_faithful 4 (le_refl 4)
  exact concrete_localSearchIncompressible_smallScale (le_refl 4)
    (hExtract trivial)

/-- **V2: КАНДИДАТ 2 ЗЕЛЁНО-ДОКАЗУЕМ** — его декрет не добавил бы НИЧЕГО
    (вакуумный декрет). Свидетель: constantsFrame с пустой экстракцией. -/
theorem pnpLawExistential_green : PnpManifestationLawExistential :=
  ⟨constantsFrame, constantsFrame_faithful, fun _ _ => trivial,
   fun _ _ => ⟨boolLanguage, trivial,
     fun hP => absurd hP boolLanguage_not_inP_constantsFrame⟩⟩

/-- **V3: КАНДИДАТ 3 ЗЕЛЁНО-ОПРОВЕРЖИМ** — голые решатели классически
    существуют, извлечённый резолвер противоречит несжимаемости A ≤ 4. -/
theorem pnpLawDeciderGated_refuted : ¬ PnpManifestationLawDeciderGated := by
  intro hLaw
  obtain ⟨L, ⟨R⟩⟩ := hLaw 4 (le_refl 4)
  exact ClassicalPNPBridge.concreteNode_incompressible_smallScale (le_refl 4)
    ((concreteResolverTarget 4 1).realizes
      (R.reconstruct (classicalPDecider L)))

/-#############################################################################
  §8. Условный классический слой (мост как гипотеза) — зелёные зеркала
#############################################################################-/

/-- Достаточность в мостовой форме: любой InP-gated мост над малым узлом
    разделяет свой фрейм. -/
theorem classesSeparate_of_bridge {C : ClassicalComplexityFrame} {A : ℕ}
    (hA : A ≤ 4)
    (B : Step00ToClassicalBridge C (ClassicalPNPBridge.concreteNode A 1)) :
    C.ClassesSeparate :=
  B.classicalSeparation_of_localIncompressible
    (ClassicalPNPBridge.concreteNode_incompressible_smallScale hA)

/-- Essence-зеркало: экзистенциальный закон даёт faithful-фрейм с разделением.
    ⚠️ ЧЕСТНОСТЬ: сам закон уже зелёно доказан (V2) — потому и это следствие
    бессодержательно как «продвижение»; оно лишь фиксирует форму цепи. -/
theorem classesSeparate_of_manifestation
    (hLaw : PnpManifestationLawExistential) :
    ∃ C : ClassicalComplexityFrame,
      Nonempty (FaithfulPFrame C) ∧ C.ClassesSeparate := by
  obtain ⟨C, hFaithful, _hPNP, hMan⟩ := hLaw
  obtain ⟨L, hNP, hExtract⟩ := hMan 4 (le_refl 4)
  exact ⟨C, hFaithful, L, hNP,
    fun hP => concrete_localSearchIncompressible_smallScale (le_refl 4)
      (hExtract hP)⟩

/-- Вакуумная обратная сторона (раскрыта): разделение восстанавливает закон
    ex-falso экстракцией. -/
theorem manifestationLaw_of_separation
    (hSep : ∃ C : ClassicalComplexityFrame,
      Nonempty (FaithfulPFrame C) ∧ (∀ L, C.InP L → C.InNP L) ∧
        C.ClassesSeparate) :
    PnpManifestationLawExistential := by
  obtain ⟨C, hF, hPNP, L, hNP, hNotP⟩ := hSep
  exact ⟨C, hF, hPNP, fun _ _ => ⟨L, hNP, fun hP => absurd hP hNotP⟩⟩

/-- **Зеркало стоимости (и его коллапс):** закон ⟺ faithful-разделение —
    и, в отличие от Римана, этот iff ЗЕЛЁНЫЙ (границы не требует), а обе
    стороны УЖЕ теоремы (V2, A7): декретировать здесь нечего. -/
theorem pnpLaw_asserts_separation :
    PnpManifestationLawExistential ↔
      ∃ C : ClassicalComplexityFrame,
        Nonempty (FaithfulPFrame C) ∧ (∀ L, C.InP L → C.InNP L) ∧
          C.ClassesSeparate := by
  constructor
  · rintro ⟨C, hF, hPNP, hMan⟩
    obtain ⟨L, hNP, hExtract⟩ := hMan 4 (le_refl 4)
    exact ⟨C, hF, hPNP, L, hNP,
      fun hP => concrete_localSearchIncompressible_smallScale (le_refl 4)
        (hExtract hP)⟩
  · exact manifestationLaw_of_separation

/-- Bundling-аудит (зеркало L9 Римана): декретироваться мог бы только
    Bridge; Impossible-сторона — зелёная теорема
    `concreteNode_incompressible_smallScale`, никогда не декрет. -/
theorem pnp_bundling_audit {C : ClassicalComplexityFrame} {A : ℕ}
    (hA : A ≤ 4) :
    (Nonempty (Step00ToClassicalBridge C (ClassicalPNPBridge.concreteNode A 1)) →
      C.ClassesSeparate) ∧
    (ClassicalPNPBridge.concreteNode A 1).LocalSearchIncompressible :=
  ⟨fun ⟨B⟩ => classesSeparate_of_bridge hA B,
   ClassicalPNPBridge.concreteNode_incompressible_smallScale hA⟩

-- Машинная видимость чистоты прямо в build-логе: все ключевые декларации
-- аксиомо-свободны (ожидаемо [propext, Classical.choice, Quot.sound]).
#print axioms pnp_rank_separation_smallScale
#print axioms concrete_localPSuccess_iff_fullPayment
#print axioms boundary_forces_localPSuccess_at_decreed_scale
#print axioms pnpLawUniversal_refuted
#print axioms pnpLawExistential_green
#print axioms faithfulSelfReductionFront_isEmpty

end PNPRankPayment
end EuclidsPath
