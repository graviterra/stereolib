import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
Inside an actual Rule-1a-tied original-root arm, a distinct refined-key tie cannot use the
incoming slot or a ring-duplicate outward slot. The incoming exclusion uses the existing
rootward separation theorem, independently of auxiliary-center rigidity. The outward
provenance conclusion follows from actual Rule-1b observations and unique source indices.

The root-arm calls, their Rule-1a tie, and the target's branch membership remain explicit.
This module does not infer a key tie from arbitrary evaluator refusal: disagreement between
successful local reference readings is a separate case. It makes no physical properness
claim at boundary or other centers.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedActualBoundaryObservationReadback LocalizedActualBoundaryPathRealization
open LocalizedActualOutwardRule1bEquivalence LocalizedCyclicGeneralRigidPriority

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-- The first, constitutional part of the actual compiled Rule-4a stages ties whenever
the actual refined keys tie. No marker coverage or desired comparison outcome is assumed. -/
theorem refined_tie_constitutional (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (W D : Nat) (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    OfficialRuleMajorKey.compare
      ((frames input single state target real unit targetUnit).stages left).a.key.constitutional
      ((frames input single state target real unit targetUnit).stages right).a.key.constitutional = .eq := by
  let frame := frames input single state target real unit targetUnit
  have prior := congrArg (fun key : RefinedKey => (ofLex key).1) tie
  change frame.retainedKeys unit left = frame.retainedKeys unit right at prior
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right
  rw [prior, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have constitutional := constitutional_eq_of_full_eq (frame.compounds left) (frame.compounds right) full
  have ordinaryBuilt (slot : Fin 4) : ordinaryKey? input target
      (input.molecularView (rawStateDescriptorMap input state) target)
      (frame.stages slot).a.tree.source = some (frame.compounds slot) := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.compoundBuilt slot
  have sameL := subtree_constitution_eq_ordinary (frame.stages left).a.trace target
    (input.molecularView (rawStateDescriptorMap input state) target) (frame.compounds left) (ordinaryBuilt left)
  have sameR := subtree_constitution_eq_ordinary (frame.stages right).a.trace target
    (input.molecularView (rawStateDescriptorMap input state) target) (frame.compounds right) (ordinaryBuilt right)
  exact (ruleMajor_compare_congr _ _ _ _ sameL sameR).trans constitutional

/-- Distinct outward siblings with tied actual constitutional keys are both real, with
distinct current atoms. Duplicate cases are excluded by their actual Rule-1b source indices. -/
theorem outward_tie_real (single : input.moleculeGraph.SimpleBonded)
    (pair : ActualOutwardSiblingPair input (retainedCarrierFuel input))
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (distinct : pair.left ≠ pair.right) (center : input.Atom)
    (current : pair.target.occurrence.1.node.current? = some center)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR)
    (tie : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional = .eq) :
    ∃ a b : input.Atom, a ≠ b ∧ pair.left.occurrence.1.node.current? = some a ∧
      pair.right.occurrence.1.node.current? = some b ∧
      pair.left.occurrence.1.node.provenance = .realAtom ∧
      pair.right.occurrence.1.node.provenance = .realAtom := by
  have memberL := outwardChild_node_mem input pair.target pair.left pair.leftRoot pair.leftSlot pair.leftAddress
  have memberR := outwardChild_node_mem input pair.target pair.right pair.rightRoot pair.rightSlot pair.rightAddress
  obtain ⟨a, nodeL, _, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input single _ current targetReal _).mp memberL
  obtain ⟨b, nodeR, _, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input single _ current targetReal _).mp memberR
  have different : a ≠ b := by
    intro same
    apply distinct
    apply outwardChild_eq_of_node_eq input single pair.target pair.left pair.right
      pair.leftPrevious pair.rightPrevious pair.leftRoot pair.rightRoot pair.leftSlot pair.rightSlot
      pair.leftAddress pair.rightAddress
    rw [nodeL, nodeR, same]
  have equalDistance := outwardSibling_rule1b_eq_of_tie input pair builtL builtR tie
  rw [nodeL, nodeR] at equalDistance
  have fresh : a ∉ pair.target.occurrence.1.node.history ∧ b ∉ pair.target.occurrence.1.node.history := by
    by_cases seenL : a ∈ pair.target.occurrence.1.node.history
    · obtain ⟨i, indexL, _, distanceL, boundL⟩ := extend_rule1b_of_mem seenL
      by_cases seenR : b ∈ pair.target.occurrence.1.node.history
      · obtain ⟨j, indexR, _, distanceR, _⟩ := extend_rule1b_of_mem seenR
        rw [distanceL, distanceR] at equalDistance
        rw [equalDistance] at indexL
        exact False.elim (different (Option.some.inj (indexL.symm.trans indexR)))
      · have distanceR := (extend_rule1b_of_not_mem seenR).2
        rw [distanceL, distanceR] at equalDistance
        omega
    · by_cases seenR : b ∈ pair.target.occurrence.1.node.history
      · obtain ⟨j, _, _, distanceR, boundR⟩ := extend_rule1b_of_mem seenR
        have distanceL := (extend_rule1b_of_not_mem seenL).2
        rw [distanceL, distanceR] at equalDistance
        omega
      · exact ⟨seenL, seenR⟩
  refine ⟨a, b, different, ?_, ?_, ?_, ?_⟩
  · rw [nodeL]
    rfl
  · rw [nodeR]
    rfl
  · rw [nodeL]
    exact (extend_rule1b_of_not_mem fresh.1).1
  · rw [nodeR]
    exact (extend_rule1b_of_not_mem fresh.2).1

/-- At a target inside an actually tied root arm, a distinct actual refined-key tie supplies
the real outward pair and distinct atom readbacks required by the odd ranked reconstruction.
No incoming/outward/provenance/selected-reference conclusion is presumed. -/
theorem selected_refined_tie_real_outward
    (single : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = .realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = .realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat} (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a armRead' armFuel' armCursor' = some armKey')
    (armTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = .eq)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom) (inside : input.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ []) (center : input.Atom) (current : target.1.node.current? = some center)
    (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (W D : Nat) (left right : Fin 4) (distinct : left ≠ right)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    ∃ (parentIndex : Fin 4) (pair : ActualOutwardSiblingPair input (retainedCarrierFuel input))
      (a b : input.Atom),
      IsLocalizedActualFrameParentCursor input target
        ((frames input single state target real unit targetUnit).frame.cursorAt parentIndex) ∧
      left ≠ parentIndex ∧ right ≠ parentIndex ∧
      pair.target = { occurrence := target, previous? := none } ∧
      pair.left = (frames input single state target real unit targetUnit).frame.cursorAt left ∧
      pair.right = (frames input single state target real unit targetUnit).frame.cursorAt right ∧
      a ≠ b ∧ pair.left.occurrence.1.node.current? = some a ∧
      pair.right.occurrence.1.node.current? = some b ∧
      pair.left.occurrence.1.node.provenance = .realAtom ∧
      pair.right.occurrence.1.node.provenance = .realAtom := by
  let frame := frames input single state target real unit targetUnit
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frame.frameComputed
  have constitutional := refined_tie_constitutional input single state target real unit targetUnit
    reference W D left right tie
  obtain ⟨parentIndex, parentClass, others⟩ := parentSlot_separated_of_rootArmRule1aTie input single
    rootCursor rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal'
    armRead armRead' armKey armKey' armBuilt armBuilt' armTie target real inside frame.frame computed nonroot
  have leftOut : left ≠ parentIndex := by
    intro same
    subst left
    exact (others right (Ne.symm distinct)).2 _ _ _ _ _ _ _ _
      (frame.stages parentIndex).a.built (frame.stages right).a.built constitutional
  have rightOut : right ≠ parentIndex := by
    intro same
    subst right
    exact ((others left distinct).2).symm _ _ _ _ _ _ _ _
      (frame.stages left).a.built (frame.stages parentIndex).a.built constitutional
  obtain ⟨pair, targetEq, leftEq, rightEq⟩ := outwardSiblingPair_of_frame target frame.frame computed
    (others left leftOut).1 (others right rightOut).1
  have pairDistinct : pair.left ≠ pair.right := by
    rw [leftEq, rightEq]
    exact frame_cursorAt_ne target frame.frame computed distinct
  have builtL : input.buildRuleMajorCumulativeWithRead? .rule4a
      (input.localizedDependencyLabel target (input.molecularView (rawStateDescriptorMap input state) target))
      (2 * (retainedCarrierFuel input + 1)) pair.left = some (frame.stages left).a.key := by
    rw [leftEq]
    exact (frame.stages left).a.built
  have builtR : input.buildRuleMajorCumulativeWithRead? .rule4a
      (input.localizedDependencyLabel target (input.molecularView (rawStateDescriptorMap input state) target))
      (2 * (retainedCarrierFuel input + 1)) pair.right = some (frame.stages right).a.key := by
    rw [rightEq]
    exact (frame.stages right).a.built
  obtain ⟨a, b, different, atomL, atomR, realL, realR⟩ := outward_tie_real input single pair
    (by simpa only [targetEq] using real) pairDistinct center (by simpa only [targetEq] using current)
    builtL builtR constitutional
  exact ⟨parentIndex, pair, a, b, parentClass, leftOut, rightOut, targetEq, leftEq, rightEq,
    different, atomL, atomR, realL, realR⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie.refined_tie_constitutional
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie.outward_tie_real
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie.selected_refined_tie_real_outward
