import TetraStereo.Examples.VS298OccurrenceAddressCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery

abbrev SelectedBranch := centerDiscovery.branch ligandFourSlot
abbrev SelectedNode := (branchKey ligandFourSlot).HierarchyNode
abbrev ResolvedOccurrence :=
  CompleteBranchDiscovery.ResolvedBranchOccurrence SelectedBranch

/-- The executable branch root, including its incoming edge from final center 1. -/
def rootOccurrence : ResolvedOccurrence :=
  CompleteBranchDiscovery.resolvedRoot SelectedBranch

/-- Select one exact production child by its canonical-child position.  The node is obtained from
`CanonicalCompleteBuild.ChildrenExact`, not by evaluating the complete hierarchy-address list. -/
noncomputable def childOccurrence (parent : ResolvedOccurrence)
    (position : Fin (molecule.canonicalChildren parent.source).length) : ResolvedOccurrence :=
  CompleteBranchDiscovery.resolvedChild SelectedBranch parent position

def firstPosition (source : RawMolecule.CanonicalBranchNode)
    (nonempty : 0 < (molecule.canonicalChildren source).length) :
    Fin (molecule.canonicalChildren source).length := ⟨0, nonempty⟩

noncomputable def levelOne : ResolvedOccurrence :=
  childOccurrence rootOccurrence
    ⟨2, by decide⟩

noncomputable def leftLevelTwo : ResolvedOccurrence :=
  childOccurrence levelOne
    ⟨1, by decide⟩

noncomputable def rightLevelTwo : ResolvedOccurrence :=
  childOccurrence levelOne
    ⟨2, by decide⟩

noncomputable def leftOccurrence : ResolvedOccurrence :=
  childOccurrence leftLevelTwo
    ⟨2, by decide⟩

noncomputable def rightOccurrence : ResolvedOccurrence :=
  childOccurrence rightLevelTwo
    ⟨2, by decide⟩

/-- The actual exhaustive occurrence carrier used by the fixed-point system. -/
abbrev ProductionOccurrence :=
  ProductionCIPOccurrenceDiscovery.Occurrence discovery

/-- Lift the selected left completeness-path node into the exhaustive root-relative carrier.
The slot prefix is part of `Occurrence.address`, so this is not the old unrooted source key. -/
noncomputable def leftProductionOccurrence : ProductionOccurrence :=
  { root := root
    node := branchNode (discovery.center root) ligandFourSlot leftOccurrence.node }

/-- Lift the selected right completeness-path node into the same exhaustive carrier. -/
noncomputable def rightProductionOccurrence : ProductionOccurrence :=
  { root := root
    node := branchNode (discovery.center root) ligandFourSlot rightOccurrence.node }

@[simp] theorem leftProductionOccurrence_root : leftProductionOccurrence.root = root := rfl

@[simp] theorem rightProductionOccurrence_root : rightProductionOccurrence.root = root := rfl

@[simp] theorem leftProductionOccurrence_address :
    leftProductionOccurrence.address = ligandFourSlot.val :: leftOccurrence.node.1 := rfl

@[simp] theorem rightProductionOccurrence_address :
    rightProductionOccurrence.address = ligandFourSlot.val :: rightOccurrence.node.1 := rfl

end TetraStereo.Examples.VS298
