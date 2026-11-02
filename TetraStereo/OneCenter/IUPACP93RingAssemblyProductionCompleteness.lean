import TetraStereo.OneCenter.IUPACRemaining71P93RingAssemblyReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for all three ring-assembly P-93 provisions

One checked assembly graph feeds three explicit all-and-only assignment validators.  Axial
geometry, center descriptors, and P-91.2.2 double-bond requirements remain distinct computed cores.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.Cyclic

def P93RingAssemblySourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly) : Prop :=
  assembly.MechanicallyValidFor source ∧ policy.AssemblyObserved source assembly

def P93RingAssemblyAxisAssignmentSourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (result : ChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (assignment : P93RingAssemblyAxisAssignment) : Prop :=
  assignment.junction ∈ assembly.junctions ∧
    policy.AxisEligible source assembly assignment.junction ∧
    P93RingAssemblyAxisFrameValid source assembly assignment.junction assignment.record ∧
    assignment.cipDescriptor = AxialDescriptor.ofSense assignment.record.sense ∧
    BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
      result spatial assignment.record assignment.cipDescriptor ∧
    assignment.preferredDescriptor = preferredRingAssemblyAxisDescriptor assignment.cipDescriptor ∧
    assignment.generalDescriptor = generalRingAssemblyAxisDescriptor assignment.cipDescriptor ∧
    PreferredRingAssemblyAxisDescriptor assignment.preferredDescriptor ∧
    policy.AxisDescriptorsObserved source assembly assignment.junction
      assignment.preferredDescriptor assignment.generalDescriptor ∧
    assignment.citation.Valid ∧
    policy.AxisCitationAuthorized source assembly assignment.junction assignment.citation

def P93RingAssemblyAxesSourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RingAssemblyAxesAuthorityObservation policy) : Prop :=
  P93RingAssemblySourceCore policy source observation.assembly ∧
    source.spatial? = some observation.spatial ∧
    observation.normalization.parsed.AuthoritativeStructureAgreement source ∧
    observation.normalization = normalizeRawMolecule observation.normalization.parsed ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment => assignment.junction).Nodup ∧
    (observation.assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      P93RingAssemblyAxisAssignmentSourceCore policy source observation.assembly
        observation.normalization observation.spatial assignment) ∧
    ∀ junction ∈ observation.assembly.junctions,
      policy.AxisEligible source observation.assembly junction →
        ∃ assignment ∈ observation.assignments, assignment.junction = junction

def P93RingAssemblyCenterAssignmentSourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (assignment : P93RingAssemblyCenterAssignment) : Prop :=
  P93RingAssemblyCenterInExactlyOneRing assembly assignment.center ∧
    (.atomCenter assignment.center : P93AuthorityPhysicalUnit).ValidFor
      policy.physicalObservation source ∧
    policy.CenterEligible source assembly assignment.center ∧
    PreferredRingAssemblyCenterDescriptor assignment.preferredDescriptor ∧
    policy.CenterCIPDescriptorAuthorized source assembly assignment.center
      assignment.preferredDescriptor ∧
    assignment.citation.Valid ∧
    policy.CenterCitationAuthorized source assembly assignment.center assignment.citation ∧
    match assignment.generalDescriptor? with
    | none => True
    | some generalDescriptor =>
        P93RingAssemblyGeneralCenterDescriptor generalDescriptor ∧
          policy.CenterGeneralDescriptorEquivalent source assembly assignment.center
            assignment.preferredDescriptor generalDescriptor

def P93RingAssemblyCentersSourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RingAssemblyCentersAuthorityObservation policy) : Prop :=
  P93RingAssemblySourceCore policy source observation.assembly ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment => assignment.center).Nodup ∧
    (observation.assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      P93RingAssemblyCenterAssignmentSourceCore policy source observation.assembly assignment) ∧
    ∀ center, policy.CenterEligible source observation.assembly center →
      ∃ assignment ∈ observation.assignments, assignment.center = center

def P93RingAssemblyDoubleBondAssignmentSourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (assignment : P93RingAssemblyDoubleBondAssignment) : Prop :=
  P93RingAssemblyBondInRing source assembly assignment.ringIndex
      assignment.first assignment.second ∧
    P93RingAssemblyDoubleBondRequired policy source assembly assignment.ringIndex
      assignment.first assignment.second ∧
    P93RingAssemblyEZDescriptor assignment.descriptor ∧
    policy.DoubleBondDescriptorAuthorized source assembly assignment.ringIndex
      assignment.first assignment.second assignment.descriptor ∧
    assignment.citation.Valid ∧
    policy.DoubleBondCitationAuthorized source assembly assignment.ringIndex
      assignment.first assignment.second assignment.citation

def P93RingAssemblyDoubleBondsSourceCore
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy) : Prop :=
  P93RingAssemblySourceCore policy source observation.assembly ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment =>
      (assignment.ringIndex, assignment.first, assignment.second)).Nodup ∧
    (observation.assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      P93RingAssemblyDoubleBondAssignmentSourceCore
        policy source observation.assembly assignment) ∧
    ∀ ringIndex first second,
      P93RingAssemblyBondInRing source observation.assembly ringIndex first second →
      P93RingAssemblyDoubleBondRequired policy source observation.assembly
        ringIndex first second →
      ∃ assignment ∈ observation.assignments,
        assignment.ringIndex = ringIndex ∧ assignment.first = first ∧ assignment.second = second

namespace Remaining71P93RingAssemblyAuthorityRow

def ProductionJudges
    (policy : P93RingAssemblyAuthorityPolicy) :
    (row : Remaining71P93RingAssemblyAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .axes, source, observation => P93RingAssemblyAxesSourceCore policy source observation
  | .centers, source, observation => P93RingAssemblyCentersSourceCore policy source observation
  | .doubleBonds, source, observation =>
      P93RingAssemblyDoubleBondsSourceCore policy source observation

theorem production_eq_reference
    (policy : P93RingAssemblyAuthorityPolicy)
    (row : Remaining71P93RingAssemblyAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row <;> rfl

theorem reference_applicable_of_judged
    (policy : P93RingAssemblyAuthorityPolicy)
    (row : Remaining71P93RingAssemblyAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row <;> exact ⟨observation, judged⟩

end Remaining71P93RingAssemblyAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93RingAssemblyAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93RingAssemblyAuthorityRow.reference_applicable_of_judged
