import TetraStereo.Examples.VS298OccurrenceRightSourceCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery

theorem sameAtom : leftSource.atom = rightSource.atom := rfl
theorem sourcesNe : leftSource ≠ rightSource := by decide

theorem nodesNe : leftOccurrence.node ≠ rightOccurrence.node := by
  intro equal
  have leftAtRight :
      (branchKey ligandFourSlot).sourceNodeAtAddress? rightOccurrence.node.1 =
        some leftOccurrence.source := by
    simpa only [equal] using leftOccurrence.source_eq
  have sourcesEqual : leftOccurrence.source = rightOccurrence.source :=
    Option.some.inj (leftAtRight.symm.trans rightOccurrence.source_eq)
  exact sourcesNe (leftResolvedSource.symm.trans (sourcesEqual.trans rightResolvedSource))

theorem productionOccurrencesNe :
    leftProductionOccurrence ≠ rightProductionOccurrence := by
  intro equal
  have sourcesEqual := congrArg
    ProductionCIPOccurrenceDiscovery.Occurrence.sourceNode? equal
  rw [leftProductionSourceExact, rightProductionSourceExact] at sourcesEqual
  exact sourcesNe (Option.some.inj sourcesEqual)

/-- Compatibility names now denote the literal exhaustive occurrence identities, rather than an
ad-hoc root/address product that omitted the ligand-slot prefix. -/
abbrev OccurrenceIdentity := ProductionOccurrence

noncomputable def leftIdentity : OccurrenceIdentity := leftProductionOccurrence
noncomputable def rightIdentity : OccurrenceIdentity := rightProductionOccurrence

theorem identityRootsEqual : leftIdentity.root = rightIdentity.root := rfl

theorem identitiesNe : leftIdentity ≠ rightIdentity := productionOccurrencesNe

theorem sourceKeysNe :
    canonicalOccurrenceKey leftSource ≠ canonicalOccurrenceKey rightSource := by decide

end TetraStereo.Examples.VS298
