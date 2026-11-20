import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation
import TetraStereo.OneCenter.LocalizedChemicalRingSealedReferenceComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000















namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedActualBoundaryObservationReadback LocalizedActualBoundaryPathRealization
open LocalizedActualOutwardRule1bEquivalence LocalizedCyclicGeneralRigidPriority
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)

noncomputable section
open scoped Classical

section Generic

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

/-- An actual ordinary tie inside a tied root arm uses two real outward siblings. -/
theorem prior_tie_real_outward (branch : TiedRootBranch input target)
    (center : input.Atom) (current : target.1.node.current? = some center)
    (left right : Fin 4) (distinct : left ≠ right)
    (prior : rawStateKeys input single state target real unit targetUnit left =
      rawStateKeys input single state target real unit targetUnit right) :
    ∃ pair : ActualOutwardSiblingPair input (retainedCarrierFuel input),
      pair.target = { occurrence := target, previous? := none } ∧
      pair.left = (frames input single state target real unit targetUnit).frame.cursorAt left ∧
      pair.right = (frames input single state target real unit targetUnit).frame.cursorAt right ∧
      pair.left.occurrence.1.node.provenance = .realAtom ∧
      pair.right.occurrence.1.node.provenance = .realAtom := by
  let frame := frames input single state target real unit targetUnit
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frame.frameComputed
  have constitutional : OfficialRuleMajorKey.compare (frame.stages left).a.key.constitutional
      (frame.stages right).a.key.constitutional = .eq := by
    change frame.retainedKeys unit left = frame.retainedKeys unit right at prior
    have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state)
      single unit targetUnit left right
    rw [prior, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
    have equal := constitutional_eq_of_full_eq (frame.compounds left) (frame.compounds right) full
    have ordinaryBuilt (slot : Fin 4) : ordinaryKey? input target
        (input.molecularView (rawStateDescriptorMap input state) target)
        (frame.stages slot).a.tree.source = some (frame.compounds slot) := by
      rw [(frame.stages slot).a.sourceEq]
      exact frame.compoundBuilt slot
    have sameL := subtree_constitution_eq_ordinary (frame.stages left).a.trace target
      (input.molecularView (rawStateDescriptorMap input state) target) (frame.compounds left)
      (ordinaryBuilt left)
    have sameR := subtree_constitution_eq_ordinary (frame.stages right).a.trace target
      (input.molecularView (rawStateDescriptorMap input state) target) (frame.compounds right)
      (ordinaryBuilt right)
    exact (ruleMajor_compare_congr _ _ _ _ sameL sameR).trans equal
  obtain ⟨parentIndex, _, others⟩ := parentSlot_separated_of_rootArmRule1aTie input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie target real branch.inside frame.frame computed branch.nonroot
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
  obtain ⟨_, _, _, _, _, realL, realR⟩ := LocalizedChemicalRingSelectedOutwardTie.outward_tie_real
    input single pair (by simpa only [targetEq] using real) pairDistinct center
    (by simpa only [targetEq] using current) builtL builtR constitutional
  exact ⟨pair, targetEq, leftEq, rightEq, realL, realR⟩

/-- A sealed, nonadjacent inherited reference turns an actual ordinary tie of two real outward
siblings into an actual refined-key tie. The vanishing marker is derived, not assumed. -/
theorem refined_tie_of_sealed_prior_tie (reference : input.Atom) (W D : Nat) (left right : Fin 4)
    (pair : ActualOutwardSiblingPair input (retainedCarrierFuel input))
    (targetEq : pair.target = { occurrence := target, previous? := none })
    (leftEq : pair.left = (frames input single state target real unit targetUnit).frame.cursorAt left)
    (rightEq : pair.right = (frames input single state target real unit targetUnit).frame.cursorAt right)
    (realL : pair.left.occurrence.1.node.provenance = .realAtom)
    (realR : pair.right.occurrence.1.node.provenance = .realAtom)
    (a b : input.Atom) (currentL : pair.left.occurrence.1.node.current? = some a)
    (currentR : pair.right.occurrence.1.node.current? = some b)
    (differentL : a ≠ reference) (differentR : b ≠ reference)
    (sealedHistory : ∀ neighbor, input.moleculeGraph.Adj neighbor reference →
      neighbor ∈ target.1.node.history)
    (notAdjacentL : ¬ input.moleculeGraph.Adj a reference)
    (notAdjacentR : ¬ input.moleculeGraph.Adj b reference)
    (prior : rawStateKeys input single state target real unit targetUnit left =
      rawStateKeys input single state target real unit targetUnit right) :
    refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right := by
  let frame := frames input single state target real unit targetUnit
  have historyBelow (child : input.LocalizedRerootCursor (retainedCarrierFuel input))
      (member : child.occurrence.1.node ∈ input.executableOfficialCIPChildren target.1.node) :
      target.1.node.history ⊆ child.occurrence.1.node.history := by
    obtain ⟨next, copy, same⟩ := MolecularEvidenceTree.executableOfficialCIPChildren_extend
      input _ _ member
    rw [same, OfficialCIPNode.extend_history]
    exact fun _ h => List.mem_cons_of_mem _ h
  have memberL : pair.left.occurrence.1.node ∈ input.executableOfficialCIPChildren target.1.node := by
    have member := outwardChild_node_mem input pair.target pair.left pair.leftRoot pair.leftSlot
      pair.leftAddress
    rw [targetEq] at member
    exact member
  have memberR : pair.right.occurrence.1.node ∈ input.executableOfficialCIPChildren target.1.node := by
    have member := outwardChild_node_mem input pair.target pair.right pair.rightRoot pair.rightSlot
      pair.rightAddress
    rw [targetEq] at member
    exact member
  have incomingL : LocalizedRerootCursorIncomingParent input pair.left :=
    ⟨pair.target.occurrence, pair.leftPrevious, pair.leftRoot.symm,
      by rw [pair.leftAddress]; simp, by rw [pair.leftAddress]; simp⟩
  have incomingR : LocalizedRerootCursorIncomingParent input pair.right :=
    ⟨pair.target.occurrence, pair.rightPrevious, pair.rightRoot.symm,
      by rw [pair.rightAddress]; simp, by rw [pair.rightAddress]; simp⟩
  have absentL := fun descendant path =>
    LocalizedChemicalRingSealedCursorReference.cursor_reference_absent_of_not_adjacent input
      pair.left descendant incomingL reference a realL currentL differentL
      (fun neighbor adjacent => historyBelow pair.left memberL (sealedHistory neighbor adjacent))
      notAdjacentL path
  have absentR := fun descendant path =>
    LocalizedChemicalRingSealedCursorReference.cursor_reference_absent_of_not_adjacent input
      pair.right descendant incomingR reference b realR currentR differentR
      (fun neighbor adjacent => historyBelow pair.right memberR (sealedHistory neighbor adjacent))
      notAdjacentR path
  rw [leftEq] at absentL
  rw [rightEq] at absentR
  let view := rawStateView input state target
  have priorL := build?_prior input target view reference W D _ _ _
    (compiled_built input single state target real unit targetUnit reference W D left)
  have priorR := build?_prior input target view reference W D _ _ _
    (compiled_built input single state target real unit targetUnit reference W D right)
  have sparse := LocalizedChemicalRingAbsentReferenceKey.sparseCompareAt_eq_prior_of_absent input
    target view reference W D (frame.frame.cursorAt left) (frame.frame.cursorAt right)
    (slot_valid input single state target real unit targetUnit left)
    (slot_valid input single state target real unit targetUnit right)
    absentL absentR _ _ priorL priorR
  rw [LocalizedMarkedRetainedSparsePromotedKey.sparseCompareAt?_eq,
    compiled_prior input single state target real unit targetUnit reference W D left,
    compiled_prior input single state target real unit targetUnit reference W D right] at sparse
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right
  have keysEq : frame.retainedKeys unit left = frame.retainedKeys unit right := prior
  rw [keysEq, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  rw [full] at sparse
  have refined := before_eq_refined input single state target real unit targetUnit reference W D
    left right
  change compareAt? input target view reference W D (frame.frame.cursorAt left)
    (frame.frame.cursorAt right) = _ at refined
  rw [sparse] at refined
  exact (refined_compare_eq_iff _ _).mp (Option.some.inj refined).symm

end Generic

/-! ## The actual occurrence `o+` -/

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceConsensusArmSeparation
open LocalizedChemicalRingInheritedRefusalCases (referenceAt)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)

/-- **Ordinary separation at `o+`.** On the actual snapshot below `o+` for inherited reference
28, the actual Rules-1-5 keys of the two O18 attachments differ. -/
theorem arm_prior_separate (depth : Nat) (adequate : 13 ≤ depth) :
    rawStateKeys certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (inputGeometry certified) armNode 28)
        armData.target armData.real armUnit rfl slot34 ≠
      rawStateKeys certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (inputGeometry certified) armNode 28)
        armData.target armData.real armUnit rfl slot35 := by
  intro prior
  let state := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
    (inputGeometry certified) armNode 28
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨armData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  obtain ⟨pair, targetEq, leftEq, rightEq, realL, realR⟩ := prior_tie_real_outward certified
    single_bonded state armData.target armData.real armUnit rfl (Classical.choice arm_tied_branch)
    center centerCurrent slot34 slot35 slots_distinct prior
  have currentL : pair.left.occurrence.1.node.current? = some (34 : Fin 46) := by
    rw [leftEq]
    exact slot_current state slot34 34 slot_atoms.1
  have currentR : pair.right.occurrence.1.node.current? = some (35 : Fin 46) := by
    rw [rightEq]
    exact slot_current state slot35 35 slot_atoms.2
  have sealedHistory : ∀ neighbor, graph.Adj neighbor (28 : Fin 46) →
      neighbor ∈ armData.target.1.node.history := by
    rw [arm_history]
    have finite : ∀ n : Fin 46, graph.Adj n (28 : Fin 46) → n ∈ armPath.reverse := by
      intro n
      fin_cases n <;> decide +kernel
    exact finite
  apply arm_refined_separate depth adequate
  exact refined_tie_of_sealed_prior_tie certified single_bonded state armData.target armData.real
    armUnit rfl (28 : Fin 46) (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1))
    slot34 slot35 pair targetEq leftEq rightEq realL realR (34 : Fin 46) (35 : Fin 46) currentL currentR
    (by decide) (by decide) sealedHistory (by decide +kernel) (by decide +kernel) prior

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior.prior_tie_real_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior.refined_tie_of_sealed_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior.arm_prior_separate
