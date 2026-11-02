import TetraStereo.Examples.VS298OccurrenceLeftSourceCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter

def rightSource : RawMolecule.CanonicalBranchNode :=
  { atom := 6, parent := 5, history := [6, 5, 3, 4, 1], provenance := .realAtom }

/-- The right completeness-path occurrence resolves definitionally to its concrete incoming
frame; no evaluator or compiler-trust reduction is needed. -/
theorem rightResolvedSource : rightOccurrence.source = rightSource := by rfl

theorem rightSourceExact :
    (branchKey ligandFourSlot).sourceNodeAtAddress? rightOccurrence.node.1 = some rightSource := by
  exact rightOccurrence.source_eq.trans (congrArg some rightResolvedSource)

theorem rightProductionSourceExact :
    rightProductionOccurrence.sourceNode? = some rightSource := by
  exact rightSourceExact

end TetraStereo.Examples.VS298
