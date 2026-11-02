import TetraStereo.OneCenter.IUPACNext54P92FoundationalReviewedSemantics
import TetraStereo.OneCenter.IUPACProductionRefinementMaturity

set_option autoImplicit false

/-!
# Observation-boundary production adapter for the 21 foundational P-92 rows

All twenty-one rows have a concrete production-side validator over their typed authority
observations.  The validator is defined from independently named Blue Book predicates and finite
geometry/graph checks; it never invokes `ProvisionReference.Judges`.  One family theorem proves
exact equality with the independently reviewed relation.

This is an observation-boundary result.  It validates a fully materialized stereogenic-unit,
geometry, or ligand-graph observation; it does not claim that `AuthoritativeChemicalInput` can yet
perceive every such observation from a molecule.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP92

noncomputable section

namespace Next54P92FoundationalAuthorityRow

private def bondingNumberScopeProduction (bondingNumber : Nat) : Prop :=
  bondingNumber ≤ 6

private def stereogenicUnitsProduction
    (observation : P92StereogenicUnitAuthorityObservation) : Prop :=
  IsStereogenicUnit observation.localChange observation.stereoisomers observation.unit ∧
    ChiralEntityHasStereogenicUnit
      (IsChiral observation.mirror observation.superposable)
      observation.belongsTo
      (IsStereogenicUnit observation.localChange observation.stereoisomers) ∧
    (IsChiral observation.mirror observation.superposable observation.entity ∨
      IsAchiral observation.mirror observation.superposable observation.entity)

private def chiralityDefinitionProduction
    (observation : P92ChiralityAuthorityObservation) : Prop :=
  match observation.classification with
  | .chiral => IsChiral observation.mirror observation.superposable observation.entity
  | .achiral => IsAchiral observation.mirror observation.superposable observation.entity

private def chiralityCenterDefinitionProduction
    (authority : P92ChiralityCenterAuthorityObservation) : Prop :=
  IsChiralityCenter authority.distinguishable authority.stereoisomers authority.observation

private def chiralityAxisDefinitionProduction
    (observation : ChiralityAxisObservation) : Prop :=
  IsChiralityAxis observation

private def chiralityPlaneDefinitionProduction
    (observation : ChiralityPlaneObservation) : Prop :=
  IsChiralityPlane observation

private def pseudoasymmetricUnitDefinitionProduction :
    P92PseudoasymmetricUnitAuthorityObservation → Prop
  | .center center =>
      IsPseudoasymmetricUnit center.ligand center.distinguishable center.enantiomorphic ∧
        PseudoDescriptorBehaviourJudged center.behaviour
  | .axis axis =>
      IsPseudoasymmetricUnit axis.ligand axis.distinguishable axis.enantiomorphic ∧
        PseudoDescriptorBehaviourJudged axis.behaviour
  | .plane plane =>
      IsPseudoasymmetricUnit plane.ligand plane.distinguishable plane.enantiomorphic ∧
        PseudoDescriptorBehaviourJudged plane.behaviour

private def cisTransDoubleBondUnitDefinitionProduction
    (observation : DoubleBondUnitObservation) : Prop :=
  IsCisTransDoubleBondUnit observation

private def enantiomorphicDoubleBondUnitDefinitionProduction
    (observation : EnantiomorphicDoubleBondObservation) : Prop :=
  IsEnantiomorphicDoubleBond observation

private def centerChiralityRuleProduction
    (observation : P92CenterChiralityRuleAuthorityObservation) : Prop :=
  observation.frame.priorities.length = 4 ∧
    observation.frame.priorities.Nodup ∧
    (∀ priority ∈ observation.frame.priorities, 0 < priority) ∧
    observation.priorityPath.donorPositions.length = 3 ∧
    StrictPriorityProgression observation.frame observation.priorityPath ∧
    observation.leastPriorityPosition < observation.frame.priorities.length ∧
    observation.leastPriorityPosition ∉ observation.priorityPath.donorPositions ∧
    (∀ position ∈ observation.priorityPath.donorPositions,
      observation.frame.priorityAt position <
        observation.frame.priorityAt observation.leastPriorityPosition) ∧
    observation.viewedFromSideRemoteFromLowestPriority ∧
    centerDescriptor observation.pseudoasymmetric observation.priorityPath.sense =
      observation.descriptor

private def axisChiralityRuleProduction
    (observation : P92AxisChiralityRuleAuthorityObservation) : Prop :=
  observation.frame.priorities.length = 4 ∧
    (∀ priority ∈ observation.frame.priorities, 0 < priority) ∧
    observation.nearEndPositions.length = 2 ∧
    observation.farEndPositions.length = 2 ∧
    (observation.nearEndPositions ++ observation.farEndPositions).Nodup ∧
    (∀ position ∈ observation.nearEndPositions ++ observation.farEndPositions,
      position < observation.frame.priorities.length) ∧
    observation.nearSeniorPosition ∈ observation.nearEndPositions ∧
    observation.nearJuniorPosition ∈ observation.nearEndPositions ∧
    observation.farSeniorPosition ∈ observation.farEndPositions ∧
    observation.farJuniorPosition ∈ observation.farEndPositions ∧
    observation.frame.priorityAt observation.nearSeniorPosition <
      observation.frame.priorityAt observation.nearJuniorPosition ∧
    observation.frame.priorityAt observation.farSeniorPosition <
      observation.frame.priorityAt observation.farJuniorPosition ∧
    observation.priorityPath.donorPositions =
      [observation.nearSeniorPosition, observation.nearJuniorPosition,
        observation.farSeniorPosition] ∧
    PriorityPathBackedByFrame observation.frame observation.priorityPath ∧
    observation.viewedFromNearSeniorTowardFarJunior ∧
    axialDescriptor observation.priorityPath.sense = observation.descriptor

private def planeChiralityRuleProduction
    (observation : P92PlaneChiralityRuleAuthorityObservation) : Prop :=
  observation.frame.priorities.length = 4 ∧
    observation.frame.priorities.Nodup ∧
    observation.derivedPriorityPath.donorPositions.length = 3 ∧
    StrictPriorityProgression observation.frame observation.derivedPriorityPath ∧
    observation.leastPriorityPosition < observation.frame.priorities.length ∧
    observation.leastPriorityPosition ∉ observation.derivedPriorityPath.donorPositions ∧
    (∀ position ∈ observation.derivedPriorityPath.donorPositions,
      observation.frame.priorityAt position <
        observation.frame.priorityAt observation.leastPriorityPosition) ∧
    observation.derivedTetrahedronConstructed ∧
    planarDescriptor observation.derivedPriorityPath.sense = observation.descriptor

private def chiralityRuleGeneralProduction :
    P92ChiralityRuleGeneralAuthorityObservation → Prop
  | .center center => centerChiralityRuleProduction center
  | .axis axis => axisChiralityRuleProduction axis
  | .plane plane => planeChiralityRuleProduction plane

private def ligandDentateKindsProduction
    (observation : P92LigandDentateKindsAuthorityObservation) : Prop :=
  observation.graph.ligandAtoms.Nodup ∧
    observation.graph.coreAtoms.Nodup ∧
    (∀ atom ∈ observation.graph.ligandAtoms, atom ∉ observation.graph.coreAtoms) ∧
    observation.graph.bonds.Nodup ∧
    (∀ bond ∈ observation.graph.bonds,
      bond.1 ∈ observation.graph.ligandAtoms ++ observation.graph.coreAtoms ∧
        bond.2 ∈ observation.graph.ligandAtoms ++ observation.graph.coreAtoms) ∧
    observation.coordinationCore ∈ observation.graph.coreAtoms ∧
    P92GraphDerivedDonorSet observation.graph observation.coordinationCore
      observation.donorAtoms ∧
    (∀ first ∈ observation.graph.ligandAtoms,
      ∀ last ∈ observation.graph.ligandAtoms,
        ∃ path,
          P92BondPath observation.graph first last path ∧
            ∀ atom ∈ path, atom ∈ observation.graph.ligandAtoms) ∧
    (observation.cyclic = true ↔
      ∃ cycle,
        P92SimpleBondCycle observation.graph cycle ∧
          ∀ atom ∈ cycle, atom ∈ observation.graph.ligandAtoms) ∧
    match observation.denticity with
    | .monodentate => observation.donorAtoms.length = 1
    | .nDentate n _ => observation.donorAtoms.length = n

theorem provision_mem (row : Next54P92FoundationalAuthorityRow) :
    row.provision ∈ next54P92FoundationalProvisions := by
  cases row <;> decide

theorem provision_injective : Function.Injective provision := by
  intro left right equal
  cases left <;> cases right <;> simp_all [provision]

theorem authorityRowOf_eq (row : Next54P92FoundationalAuthorityRow) :
    next54P92FoundationalAuthorityRowOf row.provision row.provision_mem = row := by
  apply provision_injective
  exact next54P92FoundationalAuthorityRowOf_provision row.provision row.provision_mem

/-! ## Concrete production relations -/

/-- Concrete production at the reviewed observation boundary. -/
def ProductionJudges (row : Next54P92FoundationalAuthorityRow)
    (_input : AuthoritativeChemicalInput) : row.reference.Observation → Prop :=
  match row with
  | .stereogenicUnits => stereogenicUnitsProduction
  | .chiralityDefinition => chiralityDefinitionProduction
  | .chiralityCenterDefinition => chiralityCenterDefinitionProduction
  | .chiralityAxisDefinition => chiralityAxisDefinitionProduction
  | .chiralityPlaneDefinition => chiralityPlaneDefinitionProduction
  | .pseudoasymmetricUnitDefinition => pseudoasymmetricUnitDefinitionProduction
  | .cisTransDoubleBondUnitDefinition => cisTransDoubleBondUnitDefinitionProduction
  | .enantiomorphicDoubleBondUnitDefinition =>
      enantiomorphicDoubleBondUnitDefinitionProduction
  | .bondingNumberScope => bondingNumberScopeProduction
  | .chiralityRuleGeneral => chiralityRuleGeneralProduction
  | .centerChiralityRule => centerChiralityRuleProduction
  | .axisChiralityRule => axisChiralityRuleProduction
  | .planeChiralityRule => planeChiralityRuleProduction
  | .helicityRule => fun observation =>
      3 ≤ observation.referenceGroups.length ∧
        observation.referenceGroups.Nodup ∧
        observation.orientedPath.referencePositions =
          List.range observation.referenceGroups.length ∧
        helicityDescriptor observation.orientedPath.handedness = observation.descriptor
  | .helicityAxis => fun observation =>
      observation.frame.priorities.length = 4 ∧
        (∀ priority ∈ observation.frame.priorities, 0 < priority) ∧
        observation.nearEndPositions.length = 2 ∧
        observation.farEndPositions.length = 2 ∧
        (observation.nearEndPositions ++ observation.farEndPositions).Nodup ∧
        (∀ position ∈ observation.nearEndPositions ++ observation.farEndPositions,
          position < observation.frame.priorities.length) ∧
        observation.nearSeniorPosition ∈ observation.nearEndPositions ∧
        observation.farSeniorPosition ∈ observation.farEndPositions ∧
        (∀ other ∈ observation.nearEndPositions,
          other ≠ observation.nearSeniorPosition →
            observation.frame.priorityAt observation.nearSeniorPosition <
              observation.frame.priorityAt other) ∧
        (∀ other ∈ observation.farEndPositions,
          other ≠ observation.farSeniorPosition →
            observation.frame.priorityAt observation.farSeniorPosition <
              observation.frame.priorityAt other) ∧
        observation.orientedPath.donorPositions =
          [observation.nearSeniorPosition, observation.farSeniorPosition] ∧
        PriorityPathBackedByFrame observation.frame observation.orientedPath ∧
        observation.viewedAlongAxisFromNearToFar ∧
        axialHelicityDescriptor observation.orientedPath.sense = observation.descriptor
  | .helicityPlane => fun observation =>
      observation.frame.priorities.Nodup ∧
        observation.referencePlanePositions.Nodup ∧
        2 ≤ observation.referencePlanePositions.length ∧
        (∀ position ∈ observation.referencePlanePositions,
          position < observation.frame.priorities.length) ∧
        observation.torsionConstruction.firstInPlane ∈
          observation.referencePlanePositions ∧
        observation.torsionConstruction.secondInPlane ∈
          observation.referencePlanePositions ∧
        observation.torsionConstruction.firstInPlane ≠
          observation.torsionConstruction.secondInPlane ∧
        observation.frame.priorityAt observation.torsionConstruction.firstInPlane <
          observation.frame.priorityAt observation.torsionConstruction.secondInPlane ∧
        observation.torsionConstruction.attachedReference <
          observation.frame.priorities.length ∧
        observation.torsionConstruction.attachedReference ∉
          observation.referencePlanePositions ∧
        planarHelicityDescriptor? observation.torsionConstruction.signedTorsion =
          observation.descriptor
  | .rsmpDescriptorCorrespondence => fun observation =>
      correspondingRS observation.application observation.helicity = observation.descriptor
  | .sequenceRulePropertyClasses => fun observation =>
      propertyClass observation.input = observation.output
  | .sequenceRuleReflectionBehavior => fun observation =>
      reflectionBehaviour observation.input = observation.output
  | .ligandDentateKinds => ligandDentateKindsProduction
  | .sequenceRuleHierarchy => fun observation =>
      0 < observation.model.caseCount ∧
        firstStrictDecision ruleOrder observation.model.certifiedOutcome = observation.decision

private theorem productionJudges_congr
    (left right : Next54P92FoundationalAuthorityRow)
    (provisionEq : left.provision = right.provision)
    (input : AuthoritativeChemicalInput)
    {leftObservation : left.reference.Observation}
    {rightObservation : right.reference.Observation}
    (observationEq : HEq leftObservation rightObservation) :
    left.ProductionJudges input leftObservation ↔
      right.ProductionJudges input rightObservation := by
  cases left <;> cases right <;>
    simp_all [provision, ProductionJudges]

/-- One exact-refinement theorem closes all twenty-one foundational rows. -/
theorem production_eq_reference (row : Next54P92FoundationalAuthorityRow)
    (input : AuthoritativeChemicalInput) (observation : row.reference.Observation) :
    row.ProductionJudges input observation ↔ row.reference.Judges input observation := by
  cases row <;>
    simp [ProductionJudges, stereogenicUnitsProduction, chiralityDefinitionProduction,
      chiralityCenterDefinitionProduction, chiralityAxisDefinitionProduction,
      chiralityPlaneDefinitionProduction, pseudoasymmetricUnitDefinitionProduction,
      cisTransDoubleBondUnitDefinitionProduction,
      enantiomorphicDoubleBondUnitDefinitionProduction, bondingNumberScopeProduction,
      chiralityRuleGeneralProduction, centerChiralityRuleProduction,
      axisChiralityRuleProduction, planeChiralityRuleProduction,
      ligandDentateKindsProduction, reference,
      p92StereogenicUnitsReference,
      p92ChiralityDefinitionReference, p92ChiralityCenterDefinitionReference,
      p92ChiralityAxisDefinitionReference, p92ChiralityPlaneDefinitionReference,
      p92PseudoasymmetricUnitDefinitionReference,
      p92CisTransDoubleBondUnitDefinitionReference,
      p92EnantiomorphicDoubleBondUnitDefinitionReference, p92BondingNumberScopeReference,
      p92ChiralityRuleGeneralReference, p92CenterChiralityRuleReference,
      p92AxisChiralityRuleReference, p92PlaneChiralityRuleReference,
      p92HelicityRuleReference, P92HelicityRuleJudged, p92HelicityAxisReference,
      P92HelicityAxisJudged, p92HelicityPlaneReference, P92HelicityPlaneJudged,
      p92RSMPDescriptorCorrespondenceReference, p92SequenceRulePropertyClassesReference,
      p92SequenceRuleReflectionBehaviorReference, unaryAuthorityReference,
      p92LigandDentateKindsReference, p92SequenceRuleHierarchyReference,
      P92StereogenicUnitsJudged, P92AxisChiralityRuleJudged,
      P92PlaneChiralityRuleJudged, P92LigandDentateKindsJudged,
      P92SequenceRuleHierarchyJudged, WithinBondingNumberScope]
  case chiralityDefinition =>
    cases observation.classification <;> rfl
  case pseudoasymmetricUnitDefinition =>
    cases observation <;> rfl
  case chiralityRuleGeneral =>
    cases observation <;> rfl
  case ligandDentateKinds =>
    cases observation.denticity <;> simp

theorem production_sound (row : Next54P92FoundationalAuthorityRow)
    (input : AuthoritativeChemicalInput) (observation : row.reference.Observation) :
    row.ProductionJudges input observation → row.reference.Judges input observation :=
  (row.production_eq_reference input observation).mp

/-! ## Family-wide admitted-domain completeness -/
private def ProductionTotal (row : Next54P92FoundationalAuthorityRow) : Prop :=
  ∀ input,
    AuthoritativeChemicalInput.StructurallyWellFormed input →
      ∀ observation : row.reference.Observation,
        row.reference.Judges input observation → row.ProductionJudges input observation

private theorem production_total (row : Next54P92FoundationalAuthorityRow) :
    ProductionTotal row := by
  intro input _admitted observation judged
  exact (row.production_eq_reference input observation).mpr judged

end Next54P92FoundationalAuthorityRow

namespace ProvisionReference

private theorem p92Foundational_applicable_congr
    {left right : ProvisionReference} (equal : left = right)
    (source : AuthoritativeChemicalInput) :
    left.Applicable source ↔ right.Applicable source := by
  cases equal
  rfl

private theorem p92Foundational_judges_cast_congr
    {left right : ProvisionReference} (equal : left = right)
    (source : AuthoritativeChemicalInput) (observation : left.Observation) :
    left.Judges source observation ↔
      right.Judges source
        (cast (congrArg ProvisionReference.Observation equal) observation) := by
  cases equal
  rfl

end ProvisionReference

/-! ## Exact scoped corpus and interpreter -/

def p92FoundationalInertReference : ProvisionReference where
  Observation := Empty
  Applicable := fun _ => False
  Judges := fun _ observation => nomatch observation

noncomputable def p92FoundationalFrozenCorpus : FrozenProvisionCorpus where
  ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
  kind := fun provision =>
    if member : provision ∈ next54P92FoundationalProvisions then
      (next54P92FoundationalAuthorityRowOf provision member).kind
    else .sourceOnly
  SourceSuppliesRule := fun provision => provision ∈ next54P92FoundationalProvisions
  reference := fun provision =>
    if member : provision ∈ next54P92FoundationalProvisions then
      (next54P92FoundationalAuthorityRowOf provision member).reference
    else p92FoundationalInertReference

theorem p92FoundationalFrozenCorpus_reference_eq
    (row : Next54P92FoundationalAuthorityRow) :
    p92FoundationalFrozenCorpus.reference row.provision = row.reference := by
  simp [p92FoundationalFrozenCorpus, row.provision_mem, row.authorityRowOf_eq]

noncomputable def p92FoundationalInterpreter :
    ProvisionInterpreter p92FoundationalFrozenCorpus where
  Produces := fun provision input observation =>
    if member : provision ∈ next54P92FoundationalProvisions then
      let row := next54P92FoundationalAuthorityRowOf provision member
      let referenceEq : p92FoundationalFrozenCorpus.reference provision = row.reference := by
        dsimp [row]
        simp [p92FoundationalFrozenCorpus, member]
      row.ProductionJudges input
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem p92FoundationalInterpreter_exact
    (row : Next54P92FoundationalAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (observation : (p92FoundationalFrozenCorpus.reference row.provision).Observation) :
    p92FoundationalInterpreter.Produces row.provision input observation ↔
      row.ProductionJudges input
        (cast (congrArg ProvisionReference.Observation
          (p92FoundationalFrozenCorpus_reference_eq row)) observation) := by
  have member := row.provision_mem
  simp only [p92FoundationalInterpreter]
  rw [dif_pos member]
  change (next54P92FoundationalAuthorityRowOf row.provision member).ProductionJudges input
      (cast _ observation) ↔ row.ProductionJudges input (cast _ observation)
  apply Next54P92FoundationalAuthorityRow.productionJudges_congr
    (next54P92FoundationalAuthorityRowOf row.provision member) row
    (next54P92FoundationalAuthorityRowOf_provision row.provision member)
  exact (cast_heq _ observation).trans (cast_heq _ observation).symm

theorem p92FoundationalInterpreter_sound
    (row : Next54P92FoundationalAuthorityRow) :
    ProvisionSound p92FoundationalFrozenCorpus p92FoundationalInterpreter row.provision := by
  intro input _admitted observation produced
  let referenceEq := p92FoundationalFrozenCorpus_reference_eq row
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judged := row.production_sound input rowObservation
    ((p92FoundationalInterpreter_exact row input observation).mp produced)
  have rowApplicable : row.reference.Applicable input := by
    cases row <;> trivial
  have applicable :=
    (ProvisionReference.p92Foundational_applicable_congr referenceEq input).mpr rowApplicable
  exact ⟨applicable,
    (ProvisionReference.p92Foundational_judges_cast_congr
      referenceEq input observation).mpr judged⟩

/-- The dependent correctness bridge for one row. -/
private theorem p92FoundationalInterpreter_correct_of_total
    (row : Next54P92FoundationalAuthorityRow)
    (total : row.ProductionTotal) :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter row.provision := by
  apply provisionCorrect_iff_sound_and_complete.mpr
  refine ⟨p92FoundationalInterpreter_sound row, ?_⟩
  intro input admitted observation judged
  let referenceEq := p92FoundationalFrozenCorpus_reference_eq row
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have rowJudged : row.reference.Judges input rowObservation :=
    (ProvisionReference.p92Foundational_judges_cast_congr
      referenceEq input observation).mp judged.2
  have produced := total input admitted rowObservation rowJudged
  exact (p92FoundationalInterpreter_exact row input observation).mpr produced

/-- Family-wide correctness: the fixed observation validator exactly refines every foundational
P-92 reviewed relation. -/
theorem p92FoundationalInterpreter_correct
    (row : Next54P92FoundationalAuthorityRow) :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter row.provision :=
  p92FoundationalInterpreter_correct_of_total row row.production_total

theorem p92BondingNumberScopeProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.bondingNumberScope.provision :=
  p92FoundationalInterpreter_correct .bondingNumberScope

theorem p92HelicityRuleProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.helicityRule.provision :=
  p92FoundationalInterpreter_correct .helicityRule

theorem p92HelicityAxisProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.helicityAxis.provision :=
  p92FoundationalInterpreter_correct .helicityAxis

theorem p92HelicityPlaneProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.helicityPlane.provision :=
  p92FoundationalInterpreter_correct .helicityPlane

theorem p92RSMPDescriptorCorrespondenceProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.rsmpDescriptorCorrespondence.provision :=
  p92FoundationalInterpreter_correct .rsmpDescriptorCorrespondence

theorem p92SequenceRulePropertyClassesProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.sequenceRulePropertyClasses.provision :=
  p92FoundationalInterpreter_correct .sequenceRulePropertyClasses

theorem p92SequenceRuleReflectionBehaviorProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.sequenceRuleReflectionBehavior.provision :=
  p92FoundationalInterpreter_correct .sequenceRuleReflectionBehavior

theorem p92SequenceRuleHierarchyProduction_correct :
    ProvisionCorrect p92FoundationalFrozenCorpus p92FoundationalInterpreter
      Next54P92FoundationalAuthorityRow.sequenceRuleHierarchy.provision :=
  p92FoundationalInterpreter_correct .sequenceRuleHierarchy

end

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.production_sound
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92FoundationalInterpreter_sound
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92FoundationalInterpreter_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92BondingNumberScopeProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92HelicityRuleProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92HelicityAxisProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92HelicityPlaneProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92RSMPDescriptorCorrespondenceProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SequenceRulePropertyClassesProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SequenceRuleReflectionBehaviorProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SequenceRuleHierarchyProduction_correct
