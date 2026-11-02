import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3ChemicalApplicability
import TetraStereo.OneCenter.LocalizedScheduledStereochemistryExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Public ordinary-monocycle completeness from chemical node applicability

The earlier cursor-free theorem still named
`LocalizedDescriptorBearingRule3ReachableSupportThrough` as one field.  This module replaces that
last executable support certificate with the source-facing finite chemical classification proved
complete in `LocalizedRerootDescriptorBearingRule3ChemicalApplicability`.
-/

/-- Cursor-free ordinary-monocyclic chemical evidence with no complete node-evaluator success
premise.  The recursive field is the finite classification into structural, omission, even-axis,
ordinary/branched, required-monocycle, and odd-cumulene chemical cases. -/
def LocalizedOrdinaryMonocyclicChemicalDependencyEvidenceWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond) : Prop :=
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  0 < fuel ∧
    ∃ (axis : input.LocalizedRule3CumulatedEndpointCursorFrame fuel)
        (_ordinary : axis.doubleBondCount = 1)
        (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
        (leftFirst leftSecond rightFirst rightSecond : input.Atom),
      input.localizedRule3CumulatedEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel fuel) occurrence = some axis ∧
        input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
          axis.initial.left axis.initial.right policyResult ∧
        policyResult.policy = .requireEZ ∧
        input.localizedRule3ExplicitSubstituents bond.1.1 bond.1.2 =
          [leftFirst, leftSecond] ∧
        input.localizedRule3ExplicitSubstituents bond.1.2 bond.1.1 =
          [rightFirst, rightSecond] ∧
        input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel) ∧
        ∀ leftCompilation rightCompilation,
          input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view frameOf axis.initial.left axis.initial.right
                axis.initial.leftCursor = some leftCompilation →
          input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view frameOf axis.initial.right axis.initial.left
                axis.initial.rightCursor = some rightCompilation →
          input.LocalizedOrdinaryMonocyclicProductionSpatialEvidence
            axis policyResult leftCompilation rightCompilation

/-- The finite chemical classification supplies the former reachable-support field. -/
theorem LocalizedOrdinaryMonocyclicChemicalDependencyEvidenceWithState.toProductionEvidence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (chemical : input.LocalizedOrdinaryMonocyclicChemicalDependencyEvidenceWithState
      fuel state bond) :
    input.LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState
      fuel state bond := by
  dsimp [LocalizedOrdinaryMonocyclicChemicalDependencyEvidenceWithState] at chemical
  rcases chemical with ⟨positive, axis, ordinary, policyResult,
    leftFirst, leftSecond, rightFirst, rightSecond,
    axisComputed, policyMeaning, required, leftCandidates, rightCandidates,
    recursiveChemical, spatial⟩
  dsimp [LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState]
  exact ⟨positive, axis, ordinary, policyResult,
    leftFirst, leftSecond, rightFirst, rightSecond,
    axisComputed, policyMeaning, required, leftCandidates, rightCandidates,
    recursiveChemical.reachableSupport input
      (input.localizedAtomRootOccurrence fuel bond.1.1)
      (input.localizedDependencyView state
        (input.localizedAtomRootOccurrence fuel bond.1.1)),
    spatial⟩

/-- Non-circular end-to-end completeness for one required ordinary monocyclic bond: finite
chemical classification and independent exact geometry force one conforming public assignment,
and its physical unit occurs literally once in the complete four-family scheduled result. -/
theorem every_chemicallyApplicable_localizedOrdinaryMonocyclicEZ_public_exactly_once
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (chemical : input.LocalizedOrdinaryMonocyclicChemicalDependencyEvidenceWithState fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond) :
    ∃ assignment,
      LocalizedScheduledStereochemicalAssignment.ordinaryMonocyclicEZ assignment ∈
          input.analyzeLocalizedScheduledStereochemistry fuel ∧
        input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment fuel assignment ∧
        List.count (.ordinaryMonocyclicEZ bond)
          ((input.analyzeLocalizedScheduledStereochemistry fuel).map
            LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  exact input.every_dependencyResolved_localizedOrdinaryMonocyclicEZ_public_exactly_once
    fuel bond (chemical.toProductionEvidence input fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
