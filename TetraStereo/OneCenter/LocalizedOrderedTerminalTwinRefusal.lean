import TetraStereo.OneCenter.LocalizedOrderedReferencePipeline
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Physical terminal-twin refusal in the ordered fixed point

The old refusal used a model of the production evaluator to clear leaf labels.  Here the same
local terminal-key proof consumes only leaf absence; the ordered fixed point derives that absence
from its own descriptor-centre guard.  No agreement with the old production state is required.
-/

namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal

noncomputable section

namespace CertifiedLocalizedCIPInput
variable (input : CertifiedLocalizedCIPInput) {fuel : Nat}

/-- Every actual physical leaf is unlabelled in the ordered evaluator's own fixed point. -/
theorem orderedReferenceState_eq_none_of_physical_leaf
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1) :
    input.orderedReferenceState fuel target = none := by
  rw [← input.orderedReferenceState_fixed fuel target]
  exact input.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_center_none target _
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
      target atom actual cardLe)

/-- The terminal-twin proof requires only the leaf values, independently of the rest of a state.
The terminal-key comparison argument is the one factored in the accepted ordered agreement
module; its old bare-model premise has been replaced by the exact local fact it used. -/
theorem orderedDescriptor_eq_none_of_terminalTwins_of_leafNone
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (leaves : ∀ (occurrence : input.LocalizedCIPOccurrence fuel) (atom : input.Atom),
      input.ActualPhysicalAtomAtNode occurrence.1.node atom →
      (input.moleculeGraph.neighborFinset atom).card ≤ 1 → state occurrence = none)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (leftIndex rightIndex : Fin 4)
    (leftCursor rightCursor : input.LocalizedRerootCursor fuel)
    (leftAt : frame.cursorAt leftIndex = leftCursor)
    (rightAt : frame.cursorAt rightIndex = rightCursor)
    (leftOutward : leftCursor.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) target.1)
    (rightOutward : rightCursor.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) target.1)
    (cursorDistinct : leftCursor ≠ rightCursor)
    (centerAtom leftAtom rightAtom : input.Atom)
    (leftActual : input.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom)
    (rightActual : input.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom)
    (leftParentObserved : leftCursor.occurrence.1.node.parent? = some centerAtom)
    (rightParentObserved : rightCursor.occurrence.1.node.parent? = some centerAtom)
    (leftNeighbors : input.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftSingleBond : input.moleculeGraph.bond leftAtom centerAtom = 1)
    (rightSingleBond : input.moleculeGraph.bond rightAtom centerAtom = 1)
    (leftNonduplicate : leftCursor.occurrence.1.node.isDuplicateLeaf = false)
    (rightNonduplicate : rightCursor.occurrence.1.node.isDuplicateLeaf = false)
    (zEq : input.moleculeGraph.atomZ leftAtom = input.moleculeGraph.atomZ rightAtom)
    (massEq : input.moleculeGraph.atomMass leftAtom = input.moleculeGraph.atomMass rightAtom)
    (distanceEq : leftCursor.occurrence.1.node.rule1bRootDistance =
      rightCursor.occurrence.1.node.rule1bRootDistance) :
    input.localizedOccurrenceRule45DescriptorOrdered? target
      (input.localizedDependencyView state target) = none := by
  let parentCursor : input.LocalizedRerootCursor fuel :=
    { occurrence := target, previous? := none }
  have leftIncomingFrame := cursorAt_previous_eq_target_of_frame
    input target frame frameComputed leftIndex
  rw [leftAt] at leftIncomingFrame
  have rightIncomingFrame := cursorAt_previous_eq_target_of_frame
    input target frame frameComputed rightIndex
  rw [rightAt] at rightIncomingFrame
  obtain ⟨leftSlot, leftAddress⟩ :=
    exists_address_slot_of_mem_outwardChildFrames input target.1 leftCursor.occurrence.1
      leftOutward
  obtain ⟨rightSlot, rightAddress⟩ :=
    exists_address_slot_of_mem_outwardChildFrames input target.1 rightCursor.occurrence.1
      rightOutward
  have leftAddress' : leftCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [leftSlot] := by
    simpa [parentCursor] using leftAddress
  have rightAddress' : rightCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [rightSlot] := by
    simpa [parentCursor] using rightAddress
  have leftTerminal := physicalLeaf_terminal input parentCursor leftCursor leftAtom centerAtom
    leftIncomingFrame leftSlot leftAddress' leftActual leftParentObserved leftNeighbors
    leftSingleBond leftNonduplicate
  have rightTerminal := physicalLeaf_terminal input parentCursor rightCursor rightAtom centerAtom
    rightIncomingFrame rightSlot rightAddress' rightActual rightParentObserved rightNeighbors
    rightSingleBond rightNonduplicate
  have leftCard : (input.moleculeGraph.neighborFinset leftAtom).card ≤ 1 := by
    rw [leftNeighbors]
    simp
  have rightCard : (input.moleculeGraph.neighborFinset rightAtom).card ≤ 1 := by
    rw [rightNeighbors]
    simp
  have leftLabelNone := localizedDependencyLabel_eq_none_of_state_eq_none input target
    state leftCursor (leaves leftCursor.occurrence leftAtom leftActual leftCard)
  have rightLabelNone := localizedDependencyLabel_eq_none_of_state_eq_none input target
    state rightCursor (leaves rightCursor.occurrence rightAtom rightActual rightCard)
  have leftComputed := buildCompound45?_terminal_actual input target
    (input.localizedDependencyView state target) leftCursor leftTerminal leftLabelNone
    (localizedOccurrenceRerootEvaluationFuel fuel)
  have rightComputed := buildCompound45?_terminal_actual input target
    (input.localizedDependencyView state target) rightCursor rightTerminal rightLabelNone
    (localizedOccurrenceRerootEvaluationFuel fuel)
  have labelEq := officialNodeAtomLabel_eq_of_actualPhysical_z_mass input
    leftCursor.occurrence.1.node rightCursor.occurrence.1.node leftAtom rightAtom
    leftActual rightActual zEq massEq
  have constitutionalEq :=
    TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
      input leftCursor rightCursor labelEq distanceEq
  have constitutionalEqSymm :=
    TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
      input rightCursor leftCursor labelEq.symm distanceEq.symm
  have leftBuilt : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) (localizedOccurrenceRerootEvaluationFuel fuel)
      (frame.cursorAt leftIndex) = some (terminalCompound45 input leftCursor.occurrence.1.node) := by
    rw [leftAt]; exact leftComputed
  have rightBuilt : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) (localizedOccurrenceRerootEvaluationFuel fuel)
      (frame.cursorAt rightIndex) = some (terminalCompound45 input rightCursor.occurrence.1.node) := by
    rw [rightAt]; exact rightComputed
  have leftRightTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5OrderedAt? target
        (input.localizedDependencyView state target) frame leftIndex rightIndex = some result ∧
        result.ordering = Ordering.eq := by
    refine ⟨_, input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target _ frame
      leftBuilt rightBuilt, ?_⟩
    rw [input.outcomeOrdered45_terminalCompound45, input.outcomeOrdered45_terminalCompound45]
    dsimp only [localizedOccurrenceRule45ComparisonRecord]
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    exact terminalCompound45_compare_eq input _ _ constitutionalEq
  have rightLeftTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5OrderedAt? target
        (input.localizedDependencyView state target) frame rightIndex leftIndex = some result ∧
        result.ordering = Ordering.eq := by
    refine ⟨_, input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target _ frame
      rightBuilt leftBuilt, ?_⟩
    rw [input.outcomeOrdered45_terminalCompound45, input.outcomeOrdered45_terminalCompound45]
    dsimp only [localizedOccurrenceRule45ComparisonRecord]
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    exact terminalCompound45_compare_eq input _ _ constitutionalEqSymm
  have indexDistinct : leftIndex ≠ rightIndex := by
    intro same
    apply cursorDistinct
    rw [← leftAt, ← rightAt, same]
  have safeNone : input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target
      (input.localizedDependencyView state target) frame = none :=
    safeTrackedOrderOf_eq_none_of_tie _ indexDistinct leftRightTie rightLeftTie
  exact input.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_safe_eq_none target _ frame
    frameComputed safeNone

end CertifiedLocalizedCIPInput

variable (input : LocalizedUniversalReference.Input)

/-- Terminal twin leaves force refusal in the actual ordered fixed point, at any eligible
carrier occurrence.  The actual frame and terminal slot data are constructed from the graph. -/
theorem orderedReferenceState_eq_none_of_terminalTwinLeaves
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (centerAtom leftAtom rightAtom : input.certified.Atom)
    (targetCurrent : target.1.node.current? = some centerAtom)
    (tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter centerAtom)
    (leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftNe : leftAtom ≠ rightAtom)
    (rootNeLeft : target.1.root ≠ leftAtom)
    (rootNeRight : target.1.root ≠ rightAtom)
    (zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom)
    (massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
      target = none := by
  obtain ⟨frame, frameComputed, leftIndex, rightIndex, leftCursor, rightCursor, leftAt, rightAt,
    leftOutward, rightOutward, cursorDistinct, leftActual, rightActual, leftParentObserved,
    rightParentObserved, leftSingleBond, rightSingleBond, leftNonduplicate, rightNonduplicate,
    distanceEq⟩ :=
    exists_terminalTwinSlots input singleBonded acyclic target centerAtom leftAtom rightAtom
      targetCurrent tetrahedral leftNeighbors rightNeighbors leftNe rootNeLeft rootNeRight
  rw [← input.certified.orderedReferenceState_fixed (LocalizedUniversalReference.carrierFuel input) target]
  exact input.certified.orderedDescriptor_eq_none_of_terminalTwins_of_leafNone target
    (input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input))
    (fun occurrence atom actual cardLe =>
      input.certified.orderedReferenceState_eq_none_of_physical_leaf occurrence atom actual cardLe)
    frame frameComputed leftIndex rightIndex leftCursor rightCursor leftAt rightAt leftOutward
    rightOutward cursorDistinct centerAtom leftAtom rightAtom leftActual rightActual
    leftParentObserved rightParentObserved leftNeighbors rightNeighbors leftSingleBond
    rightSingleBond leftNonduplicate rightNonduplicate zEq massEq distanceEq

/-- The independent physical terminal-twin predicate implies refusal in the ordered fixed point. -/
theorem orderedReferenceState_eq_none_of_globalTwinCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified m center) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) target = none := by
  obtain ⟨leftAtom, rightAtom, pair⟩ := twin
  have tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter center.1 :=
    input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq center
  have leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {center.1} := by
    rw [← graphEq]
    exact pair.neighbor_a
  have rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {center.1} := by
    rw [← graphEq]
    exact pair.neighbor_b
  have zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom := by
    rw [← graphEq]
    exact pair.z_eq
  have massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom := by
    rw [← graphEq]
    exact pair.mass_eq
  have rootNeLeft : target.1.root ≠ leftAtom :=
    root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral leftNeighbors
  have rootNeRight : target.1.root ≠ rightAtom :=
    root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral rightNeighbors
  exact orderedReferenceState_eq_none_of_terminalTwinLeaves
    input singleBonded acyclic target center.1 leftAtom rightAtom targetCurrent
    tetrahedral leftNeighbors rightNeighbors pair.ne rootNeLeft rootNeRight zEq massEq

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderedReferenceState_eq_none_of_physical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderedDescriptor_eq_none_of_terminalTwins_of_leafNone
assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_none_of_terminalTwinLeaves
assert_kernel_only TetraStereo.OneCenter.orderedReferenceState_eq_none_of_globalTwinCenter
