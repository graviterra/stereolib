import TetraStereo.Examples.VS298OccurrenceMembershipCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter

def leftSource : RawMolecule.CanonicalBranchNode :=
  { atom := 6, parent := 7, history := [6, 7, 3, 4, 1], provenance := .realAtom }

/-- The left completeness-path occurrence resolves definitionally to its concrete incoming
frame; no evaluator or compiler-trust reduction is needed. -/
theorem leftResolvedSource : leftOccurrence.source = leftSource := by rfl

theorem leftSourceExact :
    (branchKey ligandFourSlot).sourceNodeAtAddress? leftOccurrence.node.1 = some leftSource := by
  exact leftOccurrence.source_eq.trans (congrArg some leftResolvedSource)

theorem leftProductionSourceExact :
    leftProductionOccurrence.sourceNode? = some leftSource := by
  exact leftSourceExact

end TetraStereo.Examples.VS298
