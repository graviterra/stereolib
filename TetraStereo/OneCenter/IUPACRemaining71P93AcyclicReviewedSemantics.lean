import TetraStereo.OneCenter.IUPACRemaining71ProvisionInventory
import TetraStereo.OneCenter.IUPACP93AcyclicAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed eleven-row acyclic P-93 authority family

The eleven P-93.4 acyclic provisions are exact projections of one source-bound carrier.  Physical
unit routing, descriptor applicability, nomenclature context, citation placement, cumulene parity,
and multi-unit numbering remain independent of the production descriptor pipeline.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.Acyclic

def P93AcyclicCenterAssignmentJudged
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicAuthorityAssignment policy) : Prop :=
  observation.ValidFor policy source ∧
    (observation.kind = .chiralCenter ∨
      observation.kind = .pseudoasymmetricCenter)

def P93AcyclicCenterApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation, P93AcyclicCenterAssignmentJudged policy source observation

def P93AcyclicSingleCenterApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicSingleCenterAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicMultipleDescriptorsApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicMultipleCenterDescriptorsAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicMultipleCenterDescriptorsJudged
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation :
      P93AcyclicMultipleCenterDescriptorsAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source

def P93AcyclicPrefixComponentApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicPrefixComponentAuthorityObservation policy,
    observation.ValidFor policy source ∧
      (observation.assignment.kind = .chiralCenter ∨
        observation.assignment.kind = .pseudoasymmetricCenter)

def P93AcyclicPrefixComponentCenterJudged
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicPrefixComponentAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    (observation.assignment.kind = .chiralCenter ∨
      observation.assignment.kind = .pseudoasymmetricCenter)

def P93AcyclicOrdinaryDoubleBondJudged
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicAuthorityAssignment policy) : Prop :=
  observation.ValidFor policy source ∧ observation.kind = .ordinaryDoubleBond

def P93AcyclicOrdinaryDoubleBondApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation, P93AcyclicOrdinaryDoubleBondJudged policy source observation

def P93AcyclicDoubleBondEZCisTransApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicDoubleBondAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicMultipleDoubleBondApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicMultipleDoubleBondAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicHeteroDoubleBondApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicHeteroDoubleBondAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicHeteroDoubleBondJudged
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicHeteroDoubleBondAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    HeteroDoubleBondDescriptorRecommended observation.context
      observation.assignment.descriptor

def P93AcyclicEvenCumuleneApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicEvenCumuleneAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicOddCumuleneApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicOddCumuleneAuthorityObservation policy,
    observation.ValidFor policy source

def P93AcyclicMultipleUnitsApplicable
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93AcyclicMultipleUnitsAuthorityObservation policy,
    observation.ValidFor policy source

def p93AcyclicCentersReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicAuthorityAssignment policy
  Applicable := P93AcyclicCenterApplicable policy
  Judges := P93AcyclicCenterAssignmentJudged policy

def p93SingleAcyclicCenterReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicSingleCenterAuthorityObservation policy
  Applicable := P93AcyclicSingleCenterApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93MultipleDescriptorsOneCenterReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicMultipleCenterDescriptorsAuthorityObservation policy
  Applicable := P93AcyclicMultipleDescriptorsApplicable policy
  Judges := P93AcyclicMultipleCenterDescriptorsJudged policy

def p93PrefixComponentCentersReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicPrefixComponentAuthorityObservation policy
  Applicable := P93AcyclicPrefixComponentApplicable policy
  Judges := P93AcyclicPrefixComponentCenterJudged policy

def p93OrdinaryDoubleBondsReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicAuthorityAssignment policy
  Applicable := P93AcyclicOrdinaryDoubleBondApplicable policy
  Judges := P93AcyclicOrdinaryDoubleBondJudged policy

def p93DoubleBondEZCisTransReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicDoubleBondAuthorityObservation policy
  Applicable := P93AcyclicDoubleBondEZCisTransApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93MultipleDoubleBondsReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicMultipleDoubleBondAuthorityObservation policy
  Applicable := P93AcyclicMultipleDoubleBondApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93HeteroatomDoubleBondsReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicHeteroDoubleBondAuthorityObservation policy
  Applicable := P93AcyclicHeteroDoubleBondApplicable policy
  Judges := P93AcyclicHeteroDoubleBondJudged policy

def p93EvenCumulenesReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicEvenCumuleneAuthorityObservation policy
  Applicable := P93AcyclicEvenCumuleneApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93OddCumulenesReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicOddCumuleneAuthorityObservation policy
  Applicable := P93AcyclicOddCumuleneApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93MultipleAcyclicStereogenicUnitsReference
    (policy : P93AcyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93AcyclicMultipleUnitsAuthorityObservation policy
  Applicable := P93AcyclicMultipleUnitsApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93AcyclicAuthorityRow where
  | acyclicCenters
  | singleAcyclicCenter
  | multipleDescriptorsOneCenter
  | prefixComponentCenters
  | ordinaryDoubleBonds
  | doubleBondEZCisTrans
  | multipleDoubleBonds
  | heteroatomDoubleBonds
  | evenCumulenes
  | oddCumulenes
  | multipleAcyclicStereogenicUnits
  deriving DecidableEq, Repr

namespace Remaining71P93AcyclicAuthorityRow

def all : List Remaining71P93AcyclicAuthorityRow :=
  [ .acyclicCenters
  , .singleAcyclicCenter
  , .multipleDescriptorsOneCenter
  , .prefixComponentCenters
  , .ordinaryDoubleBonds
  , .doubleBondEZCisTrans
  , .multipleDoubleBonds
  , .heteroatomDoubleBonds
  , .evenCumulenes
  , .oddCumulenes
  , .multipleAcyclicStereogenicUnits
  ]

def provision : Remaining71P93AcyclicAuthorityRow → IUPACNormativeProvision
  | .acyclicCenters => .p93AcyclicCenters
  | .singleAcyclicCenter => .p93SingleAcyclicCenter
  | .multipleDescriptorsOneCenter => .p93MultipleDescriptorsOneCenter
  | .prefixComponentCenters => .p93PrefixComponentCenters
  | .ordinaryDoubleBonds => .p93OrdinaryDoubleBonds
  | .doubleBondEZCisTrans => .p93DoubleBondEZCisTrans
  | .multipleDoubleBonds => .p93MultipleDoubleBonds
  | .heteroatomDoubleBonds => .p93HeteroatomDoubleBonds
  | .evenCumulenes => .p93EvenCumulenes
  | .oddCumulenes => .p93OddCumulenes
  | .multipleAcyclicStereogenicUnits => .p93MultipleAcyclicStereogenicUnits

def kind (_row : Remaining71P93AcyclicAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference (policy : P93AcyclicAuthorityPolicy) :
    Remaining71P93AcyclicAuthorityRow → ProvisionReference
  | .acyclicCenters => p93AcyclicCentersReference policy
  | .singleAcyclicCenter => p93SingleAcyclicCenterReference policy
  | .multipleDescriptorsOneCenter => p93MultipleDescriptorsOneCenterReference policy
  | .prefixComponentCenters => p93PrefixComponentCentersReference policy
  | .ordinaryDoubleBonds => p93OrdinaryDoubleBondsReference policy
  | .doubleBondEZCisTrans => p93DoubleBondEZCisTransReference policy
  | .multipleDoubleBonds => p93MultipleDoubleBondsReference policy
  | .heteroatomDoubleBonds => p93HeteroatomDoubleBondsReference policy
  | .evenCumulenes => p93EvenCumulenesReference policy
  | .oddCumulenes => p93OddCumulenesReference policy
  | .multipleAcyclicStereogenicUnits =>
      p93MultipleAcyclicStereogenicUnitsReference policy

def semantics (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference policy row

@[simp] theorem all_length : all.length = 11 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision = p93AcyclicSemanticsSlice := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93AcyclicAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93AcyclicAuthorityRow

theorem remaining71P93Acyclic_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93AcyclicSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93AcyclicSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93AcyclicAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93AcyclicSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93AcyclicAuthorityRow.all ∧
      row.provision = provision := by
  rw [← Remaining71P93AcyclicAuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93AcyclicAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93AcyclicSemanticsSlice) :
    Remaining71P93AcyclicAuthorityRow :=
  Classical.choose (exists_remaining71P93AcyclicAuthorityRow member)

theorem remaining71P93AcyclicAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93AcyclicSemanticsSlice) :
    (remaining71P93AcyclicAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P93AcyclicAuthorityRow member)).2

structure Remaining71P93AcyclicReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93AcyclicSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93AcyclicSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93AcyclicReviewedSemantics
    (policy : P93AcyclicAuthorityPolicy) :
    Remaining71P93AcyclicReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93AcyclicAuthorityRow.semantics policy
          (remaining71P93AcyclicAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93Acyclic_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93AcyclicAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93AcyclicAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93AcyclicAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93Acyclic_sourceAuditComplete
