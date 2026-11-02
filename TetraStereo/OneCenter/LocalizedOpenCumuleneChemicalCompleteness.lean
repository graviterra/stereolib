import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3ChemicalApplicability
import TetraStereo.OneCenter.LocalizedScheduledStereochemistryExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Public open-cumulene completeness from finite chemical classification

This module replaces the remaining reachable-support field in the even- and odd-open-cumulene
readiness packages with `LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough`, and carries
that source-facing evidence through the actual four-family scheduled analyzer.
-/

/-- Non-circular dependency evidence for one perceived even open cumulene. -/
def LocalizedEvenCumuleneChemicalProductionDependencyEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)) : Prop :=
  let target := input.localizedEvenAxialRootOccurrence
    input.certified.input.molecule.atomCount axis
  input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough target view
      (localizedDescriptorBearingRule3EvaluationFuel
        input.certified.input.molecule.atomCount) ∧
    ∀ (topology : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount)
      (embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount target
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis)
        axis.1.path.tail),
      topology.initial = input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
          input.certified.input.molecule.atomCount axis →
      topology.rightward = embedding.cursors →
      topology.rightCursor ∈ embedding.cursors →
      topology.rightPartnerCursor ∈ embedding.cursors →
      topology.rightCursor.previous? = some topology.rightPartnerCursor.occurrence →
      ∃ leftFirst leftSecond rightFirst rightSecond,
        input.localizedRule3ExplicitSubstituents
            axis.1.root.terminal axis.1.root.firstAxis = [leftFirst, leftSecond] ∧
        input.localizedRule3ExplicitSubstituents
            topology.right topology.rightPartner = [rightFirst, rightSecond]

/-- Finite chemical classification supplies the former even-cumulene dependency package. -/
theorem LocalizedEvenCumuleneChemicalProductionDependencyEvidence.toProductionEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (chemical : input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view) :
    input.LocalizedEvenCumuleneProductionDependencyEvidence axis view := by
  rcases chemical with ⟨recursiveChemical, endpoints⟩
  intro topology embedding initial rightward rightPresent rightPartnerPresent incoming
  obtain ⟨leftFirst, leftSecond, rightFirst, rightSecond,
    leftCandidates, rightCandidates⟩ :=
    endpoints topology embedding initial rightward rightPresent rightPartnerPresent incoming
  exact ⟨leftFirst, leftSecond, rightFirst, rightSecond,
    leftCandidates, rightCandidates,
    recursiveChemical.reachableSupport input
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis) view⟩

/-- Independent strict axial geometry for the endpoint frames produced for one perceived even
open cumulene. -/
def LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)) : Prop :=
  ∀ (topology : input.LocalizedRule3CumulatedEndpointCursorFrame
      input.certified.input.molecule.atomCount)
    (leftCompilation rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame
      input.certified.input.molecule.atomCount),
    input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis) topology →
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (input.localizedEvenAxialRootOccurrence
          input.certified.input.molecule.atomCount axis)
        view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view (localizedEvenCumuleneAxialRule3EvaluationFuel
            input.certified.input.molecule.atomCount))
        topology.initial.left topology.initial.right topology.initial.leftCursor =
      some leftCompilation →
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (input.localizedEvenAxialRootOccurrence
          input.certified.input.molecule.atomCount axis)
        view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view (localizedEvenCumuleneAxialRule3EvaluationFuel
            input.certified.input.molecule.atomCount))
        topology.right topology.rightPartner topology.rightCursor =
      some rightCompilation →
    ∃ assignment,
      input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
        topology.initial.left topology.right
        leftCompilation.endpointFrame rightCompilation.endpointFrame assignment

/-- Complete source-facing readiness for one perceived even open cumulene under the canonical
scheduled auxiliary state. -/
def LocalizedEvenCumuleneChemicalReadyAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) : Prop :=
  let fuel := input.certified.input.molecule.atomCount
  let target := input.localizedEvenAxialRootOccurrence fuel axis
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let view := input.localizedDependencyView state target
  input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view ∧
    input.LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount axis view

/-- A chemically ready perceived even cumulene has one independently conforming public
assignment and literal global physical-unit count one. -/
theorem every_chemicallyApplicable_localizedEvenCumulene_public_exactly_once
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (ready : input.LocalizedEvenCumuleneChemicalReadyAtAtomCount axis) :
    ∃ assignment,
      LocalizedScheduledStereochemicalAssignment.evenAxial assignment ∈
          input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount ∧
        input.DeclarativeLocalizedEvenAxialSpatialAssignment
          input.certified.input.molecule.atomCount assignment ∧
        List.count (.evenAxial axis)
          ((input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount).map
              LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  let fuel := input.certified.input.molecule.atomCount
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let target := input.localizedEvenAxialRootOccurrence fuel axis
  let view := input.localizedDependencyView state target
  change input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view ∧
      input.LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount axis view at ready
  rcases ready with ⟨dependencies, spatial⟩
  obtain ⟨result, resultComputed, _resultMeaning⟩ :=
    input.exists_localizedEvenCumuleneAxialAssignment?_of_dependencyEvidence_at_atomCount
      axis view (dependencies.toProductionEvidence input axis view) spatial
  let assignment : input.LocalizedEvenAxialSpatialAssignment fuel := { axis, result }
  have assignmentComputed : input.localizedEvenAxialSpatialAssignmentAtWithState?
      fuel state axis = some assignment := by
    simp [localizedEvenAxialSpatialAssignmentAtWithState?, fuel, state, target, view,
      resultComputed, assignment]
  have familyPresent : assignment ∈ input.analyzeLocalizedEvenCumuleneAxial fuel :=
    (input.mem_analyzeLocalizedEvenCumuleneAxialWithState_iff fuel state assignment).mpr
      (by
        have retained := input.localizedEvenAxialSpatialAssignmentAtWithState?_axis
          fuel state axis assignment assignmentComputed
        simpa [analyzeLocalizedEvenCumuleneAxial, state, retained] using assignmentComputed)
  have derived : input.DeclarativeLocalizedEvenAxialSpatialAssignment fuel assignment := by
    exact input.analyzeLocalizedEvenCumuleneAxial_member_conforms fuel assignment familyPresent
  refine ⟨assignment,
    (input.evenAxial_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr familyPresent,
    derived, ?_⟩
  simpa [input.localizedEvenAxialSpatialAssignmentAtWithState?_axis
      fuel state axis assignment assignmentComputed] using
    input.evenAxial_physicalUnit_count_eq_one_of_mem fuel assignment familyPresent

/-- Non-circular dependency evidence for one perceived odd open cumulene. -/
def LocalizedOddCumuleneChemicalProductionDependencyEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (view : input.LocalizedDependencyView
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis))) : Prop :=
  let fuel := input.certified.input.molecule.atomCount
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough target view
      (localizedDescriptorBearingRule3EvaluationFuel fuel) ∧
    ∀ (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
      (embedding : input.LocalizedAxialOccurrencePathEmbedding fuel target
        (input.localizedAxialRootFirstChildOccurrence fuel axialRoot) axis.1.path.tail),
      topology.initial = input.localizedAxialRootInitialPhysicalEndpointCursorFrame
          fuel axialRoot →
      topology.rightward = embedding.cursors →
      topology.rightCursor ∈ embedding.cursors →
      topology.rightPartnerCursor ∈ embedding.cursors →
      topology.rightCursor.previous? = some topology.rightPartnerCursor.occurrence →
      ∃ leftFirst leftSecond rightFirst rightSecond,
        input.localizedRule3ExplicitSubstituents
            topology.initial.left topology.initial.right = [leftFirst, leftSecond] ∧
        input.localizedRule3ExplicitSubstituents
            topology.right topology.rightPartner = [rightFirst, rightSecond]

/-- Finite chemical classification supplies the former odd-cumulene dependency package. -/
theorem LocalizedOddCumuleneChemicalProductionDependencyEvidence.toProductionEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (view : input.LocalizedDependencyView
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis)))
    (chemical : input.LocalizedOddCumuleneChemicalProductionDependencyEvidence axis view) :
    input.LocalizedOddCumuleneProductionDependencyEvidence axis view := by
  rcases chemical with ⟨recursiveChemical, endpoints⟩
  intro topology embedding initial rightward rightPresent rightPartnerPresent incoming
  obtain ⟨leftFirst, leftSecond, rightFirst, rightSecond,
    leftCandidates, rightCandidates⟩ :=
    endpoints topology embedding initial rightward rightPresent rightPartnerPresent incoming
  exact ⟨leftFirst, leftSecond, rightFirst, rightSecond,
    leftCandidates, rightCandidates,
    recursiveChemical.reachableSupport input
      (input.localizedAxialRootOccurrence input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis)) view⟩

/-- Complete source-facing readiness for one perceived odd open cumulene under the canonical
scheduled auxiliary state. -/
def LocalizedOddCumuleneChemicalReadyAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) : Prop :=
  let fuel := input.certified.input.molecule.atomCount
  let target := input.localizedAxialRootOccurrence fuel
    (input.localizedOddCumuleneAxialRoot axis)
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let view := input.localizedDependencyView state target
  input.LocalizedOddCumuleneChemicalProductionDependencyEvidence axis view ∧
    input.LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount axis view

/-- A chemically ready perceived odd cumulene has one independently conforming public assignment
and literal global physical-unit count one. -/
theorem every_chemicallyApplicable_localizedOddCumulene_public_exactly_once
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (ready : input.LocalizedOddCumuleneChemicalReadyAtAtomCount axis) :
    ∃ assignment,
      LocalizedScheduledStereochemicalAssignment.oddCumuleneEZ assignment ∈
          input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount ∧
        input.DeclarativeLocalizedOddCumuleneEZSpatialAssignment
          input.certified.input.molecule.atomCount assignment ∧
        List.count (.oddCumuleneEZ axis)
          ((input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount).map
              LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  let fuel := input.certified.input.molecule.atomCount
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let target := input.localizedAxialRootOccurrence fuel
    (input.localizedOddCumuleneAxialRoot axis)
  let view := input.localizedDependencyView state target
  change input.LocalizedOddCumuleneChemicalProductionDependencyEvidence axis view ∧
      input.LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount axis view at ready
  rcases ready with ⟨dependencies, spatial⟩
  obtain ⟨assignment, familyPresent, retained, derived⟩ :=
    input.exists_mem_analyzeLocalizedOddCumuleneEZ_of_ready_at_atomCount axis
      ⟨dependencies.toProductionEvidence input axis view, spatial⟩
  refine ⟨assignment,
    (input.oddCumuleneEZ_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr familyPresent,
    derived, ?_⟩
  simpa [retained] using
    input.oddCumuleneEZ_physicalUnit_count_eq_one_of_mem fuel assignment familyPresent

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
