import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAnalysis
import TetraStereo.OneCenter.LocalizedAxialOccurrencePathEmbedding
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialPerceptionCompleteness
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAssignmentCompleteness

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedEvenCumuleneAxialRegression

open OneCenter

/-!
# Localized even-cumulene axial regression surface

These exact point fixtures exercise both signs of the directed axial scalar triple product.  The
remaining checks expose the topology-to-priority-to-geometry soundness chain used by the complete
localized result.
-/

private def axisStart : CartesianPoint3 := { x := 0, y := 0, z := 0 }
private def axisEnd : CartesianPoint3 := { x := 0, y := 0, z := 1 }
private def startHigh : CartesianPoint3 := { x := 1, y := 0, z := 0 }
private def clockwiseEndHigh : CartesianPoint3 := { x := 0, y := -1, z := 1 }
private def anticlockwiseEndHigh : CartesianPoint3 := { x := 0, y := 1, z := 1 }

theorem exact_clockwise_assigns_Ra :
    axialDescriptorOfSpatialReferences?
      axisStart axisEnd startHigh clockwiseEndHigh = some .Ra := by
  norm_num [axialDescriptorOfSpatialReferences?, CartesianPoint3.axialChiralityMeasure,
    CartesianPoint3.displacement, RationalVector3.cross, RationalVector3.dot,
    axisStart, axisEnd, startHigh, clockwiseEndHigh]

theorem exact_anticlockwise_assigns_Sa :
    axialDescriptorOfSpatialReferences?
      axisStart axisEnd startHigh anticlockwiseEndHigh = some .Sa := by
  norm_num [axialDescriptorOfSpatialReferences?, CartesianPoint3.axialChiralityMeasure,
    CartesianPoint3.displacement, RationalVector3.cross, RationalVector3.dot,
    axisStart, axisEnd, startHigh, anticlockwiseEndHigh]



theorem exact_clockwise_reports_preferred_M :
    (axialDescriptorOfSpatialReferences?
      axisStart axisEnd startHigh clockwiseEndHigh).map
        AxialDescriptor.toPreferredP93 = some .M := by
  rw [exact_clockwise_assigns_Ra]
  rfl

/-- The mirror coordinate fixture likewise reports preferred `P` for general `Sₐ`. -/
theorem exact_anticlockwise_reports_preferred_P :
    (axialDescriptorOfSpatialReferences?
      axisStart axisEnd startHigh anticlockwiseEndHigh).map
        AxialDescriptor.toPreferredP93 = some .P := by
  rw [exact_anticlockwise_assigns_Sa]
  rfl

#check axialDescriptorOfSpatialReferences?_eq_some_iff
#check axialDescriptor_clockwise_conformance
#check axialDescriptor_anticlockwise_conformance
#check BlueBookP93.Acyclic.preferredEvenCumuleneAxialDescriptor?_eq_some_iff
#check BlueBookP93.Acyclic.existsUnique_preferred_even_cumulene_axial_descriptor
#check AxialDescriptor.toPreferredP93_exact
#check OneCenter.CertifiedLocalizedCIPInput.localizedEvenCumuleneEndpointCursorFrame?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialEndpointPair?_eq_some_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialAssignmentOfEndpointFrames?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialAssignmentOfEndpointFrames?_eq_none_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedEvenCumuleneAxialAssignmentWith?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedEvenCumuleneAxialAssignment?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3CarrierParentOccurrence?_evenAxialFirstChild
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3PhysicalEndpointCursorFrame?_evenAxialFirstChild
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenAxialOccurrencePathEmbedding
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenAxialOccurrencePathEmbedding_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.LocalizedAxialOccurrencePathEmbedding.exists_canonicalRule3ReferenceCursor
#check OneCenter.CertifiedLocalizedCIPInput.exists_canonicalRule3ReferenceCursor_evenAxialInitialLeft
#check OneCenter.CertifiedLocalizedCIPInput.exists_walkLocalizedRule3CumulatedAxis?_evenAxial_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedRule3CumulatedEndpointCursorFrameWithEmbedding_evenAxial_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedRule3CumulatedEndpointCursorFrame_evenAxial_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenCumuleneEndpointCursorFrameWithEmbedding_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenCumuleneEndpointCursorFrame_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3ReferenceCursor?_eq_some_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedRule3CoupledTopologyResolution?_eq_ordinary_of_length_ne_four
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedDescriptorBearingRule3NodeWith?_iff_support
#check OneCenter.CertifiedLocalizedCIPInput.localizedDescriptorBearingRule3ReachableResolvedThrough_iff_support
#check OneCenter.CertifiedLocalizedCIPInput.LocalizedDescriptorBearingRule3ReachableResolvedThrough.ringClosure_supported
#check OneCenter.CertifiedLocalizedCIPInput.LocalizedDescriptorBearingRule3ReachableResolvedThrough.branched_individual_geometry
#check OneCenter.CertifiedLocalizedCIPInput.not_localizedDescriptorBearingRule3ResolvedThrough_evenAxial_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedDescriptorBearingRule3Frame?_two_at_conservativeFuel
#check OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_complete_of_canonical
#check OneCenter.CertifiedLocalizedCIPInput.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenCumuleneAxialAssignment?_evenAxial_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenCumuleneAxialAssignment?_of_dependencyEvidence_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.exists_localizedEvenCumuleneAxialAssignmentWith?_evenAxial_at_atomCount
#check OneCenter.CertifiedLocalizedCIPInput.analyzeLocalizedEvenCumuleneAxial_member_conforms
#check OneCenter.CertifiedLocalizedCIPInput.mem_analyzeLocalizedEvenCumuleneAxialPreferredP93_iff
#check OneCenter.CertifiedLocalizedCIPInput.analyzeLocalizedEvenCumuleneAxialPreferredP93_member_conforms
#check OneCenter.CertifiedLocalizedCIPInput.analyzeLocalizedScheduledTetrahedralAndEvenAxial_member_conforms

end TetraStereo.Examples.LocalizedEvenCumuleneAxialRegression
