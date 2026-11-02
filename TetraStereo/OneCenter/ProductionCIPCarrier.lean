import TetraStereo.OneCenter.DeclarativeCIPCarrierPreorder
import TetraStereo.OneCenter.ProductionRule6Certificate

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

/-!
# Production realization of descriptor-level Rule 6

The production engine has two genuine carrier families: every member of the selected two-group
reference class, and the two promoted orders in the four-way S4 path.  This module interprets both
as the independent carrier certificate.  It never asserts that the carrier rankings agree.
-/

namespace RS

/-- Embed the executable two-point result into the independent final-descriptor language. -/
def toDeclarativeDescriptor : RS → DeclarativeCIP.Descriptor
  | RS.R => .R
  | RS.S => .S

theorem toDeclarativeDescriptor_injective :
    Function.Injective toDeclarativeDescriptor := by
  intro first second h
  cases first <;> cases second <;> simp_all [toDeclarativeDescriptor]

end RS

/-! ## Two-group carrier -/

/-- A successful invocation of the executable all-reference checker, retained with all inputs
needed to replay its semantic judgment. -/
structure ProductionTwoGroupCarrierContext where
  result : ChemistryNormalizationResult
  molecule : RawMolecule
  state : RawDescriptorState
  fuel : ℕ
  center : ℕ
  parity : TetrahedralInputParity
  ligands : List ℕ
  sorted : List ℕ
  references : List ℕ
  first : Rule6TrackedRanking
  accepted : rankRule6EquivalentReferences? result molecule state fuel center parity
    ligands sorted references = some first

/-- Executable inputs before the proof-carrying result has been obtained. -/
structure ProductionTwoGroupCarrierInput where
  result : ChemistryNormalizationResult
  molecule : RawMolecule
  state : RawDescriptorState
  fuel : ℕ
  center : ℕ
  parity : TetrahedralInputParity
  ligands : List ℕ
  sorted : List ℕ
  references : List ℕ

/-- Reify a successful executable two-group check as a proof-carrying carrier context. -/
def ProductionTwoGroupCarrierInput.certify?
    (input : ProductionTwoGroupCarrierInput) : Option ProductionTwoGroupCarrierContext :=
  match hresult : rankRule6EquivalentReferences? input.result input.molecule input.state
      input.fuel input.center input.parity input.ligands input.sorted input.references with
  | none => none
  | some first => some
      { result := input.result
        molecule := input.molecule
        state := input.state
        fuel := input.fuel
        center := input.center
        parity := input.parity
        ligands := input.ligands
        sorted := input.sorted
        references := input.references
        first := first
        accepted := hresult }

def ProductionTwoGroupCarrierContext.ReferenceAdmissible
    (context : ProductionTwoGroupCarrierContext) (reference : ℕ) : Prop :=
  reference ∈ context.references

def ProductionTwoGroupCarrierContext.DescriptorJudgment
    (context : ProductionTwoGroupCarrierContext) (reference : ℕ)
    (descriptor : DeclarativeCIP.Descriptor) : Prop :=
  ∃ result : RS,
    ProductionRule6DescriptorJudgment context.result context.molecule context.state
      context.fuel context.center context.parity context.ligands context.sorted reference result ∧
    descriptor = result.toDeclarativeDescriptor

namespace ProductionTwoGroupCarrierContext

theorem referenceEnumeration_exact (context : ProductionTwoGroupCarrierContext)
    (adjacent : List (Option Ordering))
    (hreferences : context.references =
      rule6EquivalentReferencePositions context.sorted adjacent)
    (reference : ℕ) :
    context.ReferenceAdmissible reference ↔
      TwoGroupEnumeratedReferencePosition context.sorted adjacent reference := by
  simpa [ReferenceAdmissible, hreferences] using
    mem_rule6EquivalentReferencePositions_iff_enumerated context.sorted adjacent reference

theorem descriptorJudgment_functional (context : ProductionTwoGroupCarrierContext)
    (reference : ℕ) {first second : DeclarativeCIP.Descriptor}
    (hfirst : context.DescriptorJudgment reference first)
    (hsecond : context.DescriptorJudgment reference second) :
    first = second := by
  rcases hfirst with ⟨firstRS, hfirst, rfl⟩
  rcases hsecond with ⟨secondRS, hsecond, rfl⟩
  exact congrArg RS.toDeclarativeDescriptor
    (productionRule6DescriptorJudgment_functional context.result context.molecule
      context.state context.fuel context.center context.parity context.ligands context.sorted
      reference hfirst hsecond)

/-- The executable all-reference check constructs the independent common-descriptor certificate. -/
theorem descriptorCertificate (context : ProductionTwoGroupCarrierContext) :
    ∃ descriptor,
      PromotionDescriptorCertificate ReferenceAdmissible DescriptorJudgment
        context descriptor := by
  let commonRS := RawMolecule.descriptorOfParity context.parity
    (RawMolecule.permutationIsEven context.first.positions)
  have certificate := rankRule6EquivalentReferences?_sound context.result context.molecule
    context.state context.fuel context.center context.parity context.ligands context.sorted
    context.references context.first context.accepted
  refine ⟨commonRS.toDeclarativeDescriptor, ?_, ?_⟩
  · rcases certificate with ⟨_, firstReference, hhead, _, _⟩
    refine ⟨firstReference, ?_⟩
    exact List.mem_of_mem_head? (by simp [hhead])
  · intro reference hreference
    refine ⟨commonRS, certificate.reference_agrees reference hreference, rfl⟩

theorem descriptorIndependent :
    PromotionDescriptorIndependent ReferenceAdmissible DescriptorJudgment :=
  promotionDescriptorIndependent_of_certificate ReferenceAdmissible DescriptorJudgment
    (fun context reference _ _ => context.descriptorJudgment_functional reference)
    descriptorCertificate

end ProductionTwoGroupCarrierContext

/-! ## Four-way S4 carrier -/

/-- A successful invocation of the special two-promotion S4 helper. -/
structure ProductionS4CarrierContext where
  result : ChemistryNormalizationResult
  molecule : RawMolecule
  state : RawDescriptorState
  fuel : ℕ
  center : ℕ
  parity : TetrahedralInputParity
  ligands : List ℕ
  sorted : List ℕ
  agreement : Rule6FourWayAgreement
  accepted : rankRule6FourWayReferences? result molecule state fuel center parity
    ligands sorted = some agreement

structure ProductionS4CarrierInput where
  result : ChemistryNormalizationResult
  molecule : RawMolecule
  state : RawDescriptorState
  fuel : ℕ
  center : ℕ
  parity : TetrahedralInputParity
  ligands : List ℕ
  sorted : List ℕ

/-- Reify a successful executable S4 check as a proof-carrying carrier context. -/
def ProductionS4CarrierInput.certify?
    (input : ProductionS4CarrierInput) : Option ProductionS4CarrierContext :=
  match hresult : rankRule6FourWayReferences? input.result input.molecule input.state
      input.fuel input.center input.parity input.ligands input.sorted with
  | none => none
  | some agreement => some
      { result := input.result
        molecule := input.molecule
        state := input.state
        fuel := input.fuel
        center := input.center
        parity := input.parity
        ligands := input.ligands
        sorted := input.sorted
        agreement := agreement
        accepted := hresult }

/-- The parity quotient applied to either of the two S4 carrier orders. -/
def ProductionS4CarrierContext.carrierResult
    (context : ProductionS4CarrierContext) (reference : Fin 2) : RS :=
  let ranking := if reference = 0 then context.agreement.firstRanking
    else context.agreement.secondRanking
  let raw := RawMolecule.descriptorOfParity context.parity
    (RawMolecule.permutationIsEven ranking.positions)
  if context.agreement.secondRanking.unique then raw else RS.swap raw

def ProductionS4CarrierContext.ReferenceAdmissible
    (_context : ProductionS4CarrierContext) (_reference : Fin 2) : Prop := True

def ProductionS4CarrierContext.DescriptorJudgment
    (context : ProductionS4CarrierContext) (reference : Fin 2)
    (descriptor : DeclarativeCIP.Descriptor) : Prop :=
  descriptor = (context.carrierResult reference).toDeclarativeDescriptor

namespace ProductionS4CarrierContext

theorem carrierResult_eq_agreement (context : ProductionS4CarrierContext)
    (reference : Fin 2) :
    context.carrierResult reference = context.agreement.descriptor := by
  have certificate := rankRule6FourWayReferences?_sound context.result context.molecule
    context.state context.fuel context.center context.parity context.ligands context.sorted
    context.agreement context.accepted
  rcases certificate with ⟨_, hraw, _, hout⟩
  fin_cases reference
  · simp only [carrierResult, Fin.zero_eta, ↓reduceIte]
    rw [hraw]
    exact hout.symm
  · simp only [carrierResult, OfNat.ofNat]
    exact hout.symm

theorem descriptorJudgment_functional (context : ProductionS4CarrierContext)
    (reference : Fin 2) {first second : DeclarativeCIP.Descriptor}
    (hfirst : context.DescriptorJudgment reference first)
    (hsecond : context.DescriptorJudgment reference second) : first = second :=
  hfirst.trans hsecond.symm

theorem descriptorCertificate (context : ProductionS4CarrierContext) :
    ∃ descriptor,
      PromotionDescriptorCertificate ReferenceAdmissible DescriptorJudgment
        context descriptor := by
  refine ⟨context.agreement.descriptor.toDeclarativeDescriptor, ⟨0, trivial⟩, ?_⟩
  intro reference _
  exact congrArg RS.toDeclarativeDescriptor
    (context.carrierResult_eq_agreement reference).symm

theorem descriptorIndependent :
    PromotionDescriptorIndependent ReferenceAdmissible DescriptorJudgment :=
  promotionDescriptorIndependent_of_certificate ReferenceAdmissible DescriptorJudgment
    (fun context reference _ _ => context.descriptorJudgment_functional reference)
    descriptorCertificate

end ProductionS4CarrierContext

/-! ## Unified production carrier family -/

abbrev ProductionCarrierContext :=
  ProductionTwoGroupCarrierContext ⊕ ProductionS4CarrierContext

abbrev ProductionCarrierReference := ℕ ⊕ Fin 2

def ProductionCarrierReferenceAdmissible
    (context : ProductionCarrierContext) (reference : ProductionCarrierReference) : Prop :=
  match context, reference with
  | .inl context, .inl reference => context.ReferenceAdmissible reference
  | .inr context, .inr reference => context.ReferenceAdmissible reference
  | _, _ => False

def ProductionCarrierDescriptorJudgment
    (context : ProductionCarrierContext) (reference : ProductionCarrierReference)
    (descriptor : DeclarativeCIP.Descriptor) : Prop :=
  match context, reference with
  | .inl context, .inl reference => context.DescriptorJudgment reference descriptor
  | .inr context, .inr reference => context.DescriptorJudgment reference descriptor
  | _, _ => False

theorem productionCarrierDescriptorCertificate (context : ProductionCarrierContext) :
    ∃ descriptor,
      PromotionDescriptorCertificate ProductionCarrierReferenceAdmissible
        ProductionCarrierDescriptorJudgment context descriptor := by
  rcases context with twoGroup | s4
  · rcases twoGroup.descriptorCertificate with ⟨descriptor, hexists, hall⟩
    refine ⟨descriptor, ?_, ?_⟩
    · rcases hexists with ⟨reference, hreference⟩
      exact ⟨.inl reference, hreference⟩
    · intro reference hreference
      rcases reference with reference | reference
      · exact hall reference hreference
      · exact False.elim hreference
  · rcases s4.descriptorCertificate with ⟨descriptor, hexists, hall⟩
    refine ⟨descriptor, ?_, ?_⟩
    · rcases hexists with ⟨reference, hreference⟩
      exact ⟨.inr reference, hreference⟩
    · intro reference hreference
      rcases reference with reference | reference
      · exact False.elim hreference
      · exact hall reference hreference

theorem productionCarrierDescriptorJudgment_functional
    (context : ProductionCarrierContext) (reference : ProductionCarrierReference)
    {first second : DeclarativeCIP.Descriptor}
    (hfirst : ProductionCarrierDescriptorJudgment context reference first)
    (hsecond : ProductionCarrierDescriptorJudgment context reference second) :
    first = second := by
  rcases context with twoGroup | s4 <;> rcases reference with reference | reference
  · exact twoGroup.descriptorJudgment_functional reference hfirst hsecond
  · exact False.elim hfirst
  · exact False.elim hfirst
  · exact s4.descriptorJudgment_functional reference hfirst hsecond

/-- Both executable Rule-6 branches satisfy one common, descriptor-level independence theorem. -/
theorem productionCarrierDescriptorIndependent :
    PromotionDescriptorIndependent ProductionCarrierReferenceAdmissible
      ProductionCarrierDescriptorJudgment :=
  promotionDescriptorIndependent_of_certificate ProductionCarrierReferenceAdmissible
    ProductionCarrierDescriptorJudgment productionCarrierDescriptorJudgment_functional
    productionCarrierDescriptorCertificate

/-! ## Adapter to the independent carrier specification -/

universe u

/-- A declarative problem together with the successful production carrier, when Rule 6 applies.

The optional context is proof-carrying: constructing either variant requires the corresponding
executable helper to have returned successfully. -/
structure ProductionCarrierSystem (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom] where
  base : DeclarativeCIP.Problem Atom Unit
  carrier? : DeclarativeCIP.DescriptorMap Unit → Unit → Option ProductionCarrierContext

namespace ProductionCarrierSystem

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

def toCarrierProblem (system : ProductionCarrierSystem Atom Unit) :
    DeclarativeCIP.CarrierProblem Atom Unit ProductionCarrierReference where
  base := system.base
  rule6Eligible := fun descriptorMap unit =>
    ∃ context, system.carrier? descriptorMap unit = some context
  admissiblePromotionReference := fun descriptorMap unit reference =>
    ∃ context, system.carrier? descriptorMap unit = some context ∧
      ProductionCarrierReferenceAdmissible context reference
  promotionDescriptorJudgment := fun descriptorMap unit reference descriptor =>
    ∃ context, system.carrier? descriptorMap unit = some context ∧
      ProductionCarrierDescriptorJudgment context reference descriptor

theorem promotionDescriptorFunctional (system : ProductionCarrierSystem Atom Unit) :
    system.toCarrierProblem.PromotionDescriptorFunctional := by
  intro descriptorMap unit reference first second hfirst hsecond
  rcases hfirst with ⟨firstContext, hfirstContext, hfirst⟩
  rcases hsecond with ⟨secondContext, hsecondContext, hsecond⟩
  have hcontext : firstContext = secondContext :=
    Option.some.inj (hfirstContext.symm.trans hsecondContext)
  subst secondContext
  exact productionCarrierDescriptorJudgment_functional firstContext reference hfirst hsecond

/-- Every eligible production invocation supplies a common descriptor for every admissible
carrier reference in the independent specification. -/
theorem rule6DescriptorCertificate_exists (system : ProductionCarrierSystem Atom Unit)
    (descriptorMap : DeclarativeCIP.DescriptorMap Unit) (unit : Unit)
    (heligible : system.toCarrierProblem.rule6Eligible descriptorMap unit) :
    ∃ descriptor,
      system.toCarrierProblem.Rule6DescriptorCertificate descriptorMap unit descriptor := by
  rcases heligible with ⟨context, hcontext⟩
  rcases productionCarrierDescriptorCertificate context with ⟨descriptor, hexists, hall⟩
  refine ⟨descriptor, ?_, ?_⟩
  · rcases hexists with ⟨reference, hreference⟩
    exact ⟨reference, context, hcontext, hreference⟩
  · intro reference hreference
    rcases hreference with ⟨otherContext, hotherContext, hreference⟩
    have heq : otherContext = context :=
      Option.some.inj (hotherContext.symm.trans hcontext)
    subst otherContext
    exact ⟨context, hcontext, hall reference hreference⟩

theorem rule6DescriptorCertificate_unique (system : ProductionCarrierSystem Atom Unit)
    (descriptorMap : DeclarativeCIP.DescriptorMap Unit) (unit : Unit)
    {first second : DeclarativeCIP.Descriptor}
    (hfirst : system.toCarrierProblem.Rule6DescriptorCertificate descriptorMap unit first)
    (hsecond : system.toCarrierProblem.Rule6DescriptorCertificate descriptorMap unit second) :
    first = second :=
  system.toCarrierProblem.rule6DescriptorCertificate_unique
    system.promotionDescriptorFunctional descriptorMap unit hfirst hsecond

/-- The ordinary descriptor judgment observes only declared inner dependencies. -/
def OrdinaryDescriptorJudgmentLocal (system : ProductionCarrierSystem Atom Unit)
    (dependency : Unit → Unit → Prop) : Prop :=
  ∀ left right unit,
    (∀ inner, dependency inner unit → left inner = right inner) →
    ∀ descriptor,
      system.base.OrdinaryDescriptorJudgment left unit descriptor ↔
        system.base.OrdinaryDescriptorJudgment right unit descriptor

/-- Successful production carrier selection observes only declared inner dependencies. -/
def CarrierSelectionLocal (system : ProductionCarrierSystem Atom Unit)
    (dependency : Unit → Unit → Prop) : Prop :=
  ∀ left right unit,
    (∀ inner, dependency inner unit → left inner = right inner) →
    system.carrier? left unit = system.carrier? right unit

/-- Ordinary semantic locality plus locality of the proof-carrying production invocation imply
locality of the complete ordinary-or-Rule-6 carrier judgment. -/
theorem descriptorJudgmentLocal (system : ProductionCarrierSystem Atom Unit)
    (dependency : Unit → Unit → Prop)
    (ordinaryLocal : system.OrdinaryDescriptorJudgmentLocal dependency)
    (carrierLocal : system.CarrierSelectionLocal dependency) :
    system.toCarrierProblem.DescriptorJudgmentLocal dependency := by
  intro left right unit hagree descriptor
  have hcarrier := carrierLocal left right unit hagree
  constructor
  · intro h
    rcases h with hordinary | hpromotion
    · exact Or.inl ((ordinaryLocal left right unit hagree descriptor).1 hordinary)
    · exact Or.inr (by
        simpa [DeclarativeCIP.CarrierProblem.Rule6DescriptorCertificate,
          toCarrierProblem, hcarrier] using hpromotion)
  · intro h
    rcases h with hordinary | hpromotion
    · exact Or.inl ((ordinaryLocal left right unit hagree descriptor).2 hordinary)
    · exact Or.inr (by
        simpa [DeclarativeCIP.CarrierProblem.Rule6DescriptorCertificate,
          toCarrierProblem, hcarrier] using hpromotion)

end ProductionCarrierSystem

/-- Remaining, explicit semantic obligations around the production carrier.  They concern the
ordinary Rules-1a--5 descriptor path, not Rule-6 reference agreement. -/
structure CertifiedProductionCarrierSystem (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom]
    extends ProductionCarrierSystem Atom Unit where
  ordinaryDescriptorUnique : ∀ descriptorMap unit first second,
    base.OrdinaryDescriptorJudgment descriptorMap unit first →
    base.OrdinaryDescriptorJudgment descriptorMap unit second →
    first = second
  ordinaryCarrierCompatible : toProductionCarrierSystem.toCarrierProblem.OrdinaryCarrierCompatible

namespace CertifiedProductionCarrierSystem

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Assemble certified coherence from the chemically normal case in which Rule 6 is reachable only
after ordinary strict ranking has failed. -/
def ofExclusive (system : ProductionCarrierSystem Atom Unit)
    (ordinaryUnique : ∀ descriptorMap unit first second,
      system.base.OrdinaryDescriptorJudgment descriptorMap unit first →
      system.base.OrdinaryDescriptorJudgment descriptorMap unit second → first = second)
    (exclusive : system.toCarrierProblem.Rule6EligibleExcludesOrdinary) :
    CertifiedProductionCarrierSystem Atom Unit where
  toProductionCarrierSystem := system
  ordinaryDescriptorUnique := ordinaryUnique
  ordinaryCarrierCompatible :=
    system.toCarrierProblem.ordinaryCarrierCompatible_of_exclusive exclusive

/-- Assemble certified production semantics from contextual unary keys, functional orientation,
and the production fallthrough theorem excluding an ordinary strict ranking at Rule 6. -/
def ofOrdinaryModelsAndExclusive (system : ProductionCarrierSystem Atom Unit)
    (ordinaryModels : ∀ descriptorMap,
      DeclarativeCIP.OrdinaryContextualRuleKeyModel system.base descriptorMap)
    (orientationFunctional : system.base.OrientationJudgmentFunctional)
    (exclusive : system.toCarrierProblem.Rule6EligibleExcludesOrdinary) :
    CertifiedProductionCarrierSystem Atom Unit :=
  ofExclusive system
    (fun descriptorMap unit _ _ hfirst hsecond =>
      (ordinaryModels descriptorMap).ordinaryDescriptorJudgment_unique
        orientationFunctional unit hfirst hsecond)
    exclusive

theorem ordinaryPriorityIsTotalPreorder
    (system : ProductionCarrierSystem Atom Unit)
    (ordinaryModels : ∀ descriptorMap,
      DeclarativeCIP.OrdinaryContextualRuleKeyModel system.base descriptorMap)
    (descriptorMap : DeclarativeCIP.DescriptorMap Unit) :
    system.base.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  (ordinaryModels descriptorMap).ordinaryPriorityIsTotalPreorder

/-- The full ordinary-or-production-Rule-6 descriptor judgment is single-valued. -/
theorem descriptorJudgment_unique (system : CertifiedProductionCarrierSystem Atom Unit)
    (descriptorMap : DeclarativeCIP.DescriptorMap Unit) (unit : Unit)
    {first second : DeclarativeCIP.Descriptor}
    (hfirst : system.toProductionCarrierSystem.toCarrierProblem.DescriptorJudgment
      descriptorMap unit first)
    (hsecond : system.toProductionCarrierSystem.toCarrierProblem.DescriptorJudgment
      descriptorMap unit second) :
    first = second :=
  system.toProductionCarrierSystem.toCarrierProblem.descriptorJudgment_unique
    system.ordinaryDescriptorUnique
    system.toProductionCarrierSystem.promotionDescriptorFunctional
    system.ordinaryCarrierCompatible descriptorMap unit hfirst hsecond

/-- Certified ordinary/carrier coherence determines an exact optional descriptor at every unit and
under every candidate auxiliary environment. -/
theorem descriptorOutcomeExists (system : CertifiedProductionCarrierSystem Atom Unit) :
    system.toProductionCarrierSystem.toCarrierProblem.DescriptorOutcomeExists :=
  system.toProductionCarrierSystem.toCarrierProblem.descriptorOutcomeExists_of_unique
    (fun descriptorMap unit _ _ hfirst hsecond =>
      system.descriptorJudgment_unique descriptorMap unit hfirst hsecond)

/-- End-to-end mathematical assembly for a certified production carrier.  The executable Rule-6
branches discharge carrier existence and agreement internally; the remaining global hypotheses
are finite expansion and the outer-to-inner locality theorem for ordinary descriptor evidence. -/
theorem descriptorMap_existsUnique_of_wellFounded
    (system : CertifiedProductionCarrierSystem Atom Unit)
    (dependency : Unit → Unit → Prop)
    (expansions : ∀ unit ligand, ∃ graph,
      system.base.admissibleExpansion unit ligand graph)
    (wellFounded : WellFounded dependency)
    (locality : system.toProductionCarrierSystem.toCarrierProblem.DescriptorJudgmentLocal
      dependency) :
    (∃ descriptorMap,
      DeclarativeCIP.CarrierCIPSpec
        system.toProductionCarrierSystem.toCarrierProblem descriptorMap) ∧
      DeclarativeCIP.CarrierDescriptorMapUnique
        system.toProductionCarrierSystem.toCarrierProblem :=
  system.toProductionCarrierSystem.toCarrierProblem.descriptorMap_existsUnique_of_wellFounded
    dependency expansions wellFounded locality system.descriptorOutcomeExists

/-- Decomposed end-to-end theorem exposing the two concrete locality obligations separately. -/
theorem descriptorMap_existsUnique_of_localProduction
    (system : CertifiedProductionCarrierSystem Atom Unit)
    (dependency : Unit → Unit → Prop)
    (expansions : ∀ unit ligand, ∃ graph,
      system.base.admissibleExpansion unit ligand graph)
    (wellFounded : WellFounded dependency)
    (ordinaryLocal : system.toProductionCarrierSystem.OrdinaryDescriptorJudgmentLocal dependency)
    (carrierLocal : system.toProductionCarrierSystem.CarrierSelectionLocal dependency) :
    (∃ descriptorMap,
      DeclarativeCIP.CarrierCIPSpec
        system.toProductionCarrierSystem.toCarrierProblem descriptorMap) ∧
      DeclarativeCIP.CarrierDescriptorMapUnique
        system.toProductionCarrierSystem.toCarrierProblem :=
  system.descriptorMap_existsUnique_of_wellFounded dependency expansions wellFounded
    (system.toProductionCarrierSystem.descriptorJudgmentLocal
      dependency ordinaryLocal carrierLocal)

/-- Full corrected research-program boundary for the production carrier architecture.

Unlike the former global Rule-6 preorder statement, every premise has its proper level: contextual
unary keys for ordinary priority, functional geometry, Rule-6 fallthrough exclusivity, and
outer-to-inner locality.  Successful production carrier agreement itself is already proved by this
module and is not an assumption. -/
theorem program_of_contextualOrdinaryAndLocalProduction
    (system : ProductionCarrierSystem Atom Unit)
    (ordinaryModels : ∀ descriptorMap,
      DeclarativeCIP.OrdinaryContextualRuleKeyModel system.base descriptorMap)
    (orientationFunctional : system.base.OrientationJudgmentFunctional)
    (exclusive : system.toCarrierProblem.Rule6EligibleExcludesOrdinary)
    (dependency : Unit → Unit → Prop)
    (expansions : ∀ unit ligand, ∃ graph,
      system.base.admissibleExpansion unit ligand graph)
    (wellFounded : WellFounded dependency)
    (ordinaryLocal : system.OrdinaryDescriptorJudgmentLocal dependency)
    (carrierLocal : system.CarrierSelectionLocal dependency) :
    (∀ descriptorMap, system.base.OrdinaryPriorityIsTotalPreorder descriptorMap) ∧
      (∃ descriptorMap,
        DeclarativeCIP.CarrierCIPSpec system.toCarrierProblem descriptorMap) ∧
      DeclarativeCIP.CarrierDescriptorMapUnique system.toCarrierProblem := by
  let certified := ofOrdinaryModelsAndExclusive system ordinaryModels
    orientationFunctional exclusive
  refine ⟨fun descriptorMap =>
    ordinaryPriorityIsTotalPreorder system ordinaryModels descriptorMap, ?_⟩
  exact certified.descriptorMap_existsUnique_of_localProduction dependency expansions
    wellFounded ordinaryLocal carrierLocal

end CertifiedProductionCarrierSystem

end
end OneCenter
end TetraStereo
