import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionExecution
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! A distinct actual joint-key tie below a constitutionally tied root arm produces one
history- and all-reference-fixing molecular automorphism, ranked witness paths, and exact
optional auxiliary-fact matches. Incoming and duplicate exclusions, outward readback and
runtime layout bounds are derived. The state is arbitrary and can be the actual prepared
state; the physical meaning of its labels is not presumed or concluded here. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedTieWitness

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingJointMarkerRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedActualBoundaryObservationReadback LocalizedActualBoundaryPathRealization
open LocalizedActualOutwardRule1bEquivalence LocalizedCyclicGeneralRigidPriority

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

open LocalizedChemicalRingSelectedOutwardTie (outward_tie_real)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointMarkerReconstructionExecution
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch RetainedCoherentSymmetry

/-- The first, constitutional part of the actual compiled Rule-4a stages ties whenever
the actual refined keys tie. No marker coverage or desired comparison outcome is assumed. -/
theorem joint_refined_tie_constitutional (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (references : List input.Atom) (W D : Nat) (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right) :
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

/-- The actual tied slots are real outward children; no such classification is assumed. -/
theorem joint_tie_real_outward
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
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) (distinct : left ≠ right)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right) :
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
  have constitutional := joint_refined_tie_constitutional input single state target real unit targetUnit
    references W D left right tie
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


/-- The same symmetry carries every field; in particular the fact matches are not
attached to an independently chosen isomorphism. -/
structure JointMatchedSymmetry (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (references : List input.Atom) (left right : Fin 4) (a b : input.Atom) where
  leftCurrent : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a
  rightCurrent : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b
  leftReal : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom
  rightReal : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom
  symmetry : input.detectedMultiCenterMolecule.Aut
  rank : input.Atom → Nat
  fixedHistory : ∀ atom ∈ target.1.node.history, (symmetry : Equiv.Perm input.Atom) atom = atom
  entry : (symmetry : Equiv.Perm input.Atom) a = b
  fixedReferences : ∀ reference ∈ references, (symmetry : Equiv.Perm input.Atom) reference = reference
  support : ∀ z, ¬ InComponent input.moleculeGraph target.1.node.history.reverse a z →
    ¬ InComponent input.moleculeGraph target.1.node.history.reverse b z →
    (symmetry : Equiv.Perm input.Atom) z = z
  matched : ∀ c : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph target.1.node.history.reverse a c.1 →
    ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p},
      pathTerminal p.1 p.2.nonempty = c.1 ∧
      PathLabelsAgree
        (slotTree input single state target real unit targetUnit left)
        (slotTree input single state target real unit targetUnit right)
        (rawStateReader input state target) (rawStateReader input state target)
        target.1.node.history.reverse p.1 (p.1.map (symmetry : Equiv.Perm input.Atom)) ∧
      (state.factAt? (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel =
        (state.factAt? (rawPathNode target.1.root
          (boundaryPath target (p.1.map (symmetry : Equiv.Perm input.Atom))))).map factLabel ∧
      (∀ y ∈ p.1.dropLast, rank y < rank c.1) ∧
      ∀ y, InComponent input.moleculeGraph (target.1.node.history.reverse ++ p.1.dropLast) c.1 y →
        y ≠ c.1 → rank c.1 < rank y

variable (mol : RawMolecule) (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)

include charge in
theorem joint_matched_of_tie (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (branch : TiedRootBranch input data.target) (state : OccurrenceAuxState) (references : List input.Atom)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data state references left =
      slotKeys input mol single c node data state references right) :
    ∃ a b : input.Atom, a ≠ b ∧
      Nonempty (JointMatchedSymmetry input single state data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references left right a b) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  change refinedKey input single state data.target data.real unit rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
    refinedKey input single state data.target data.real unit rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right at tie
  obtain ⟨center, current⟩ := input.localizedRerootCursor_current_exists
    (⟨data.target, none⟩ : input.LocalizedRerootCursor (retainedCarrierFuel input))
  obtain ⟨_, pair, a, b, _, _, _, targetEq, leftEq, rightEq, different,
      currentL, currentR, realL, realR⟩ := joint_tie_real_outward input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie state data.target data.real branch.inside branch.nonroot
    center current unit rfl references (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) left right distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at currentL realL
  rw [rightEq] at currentR realR
  obtain ⟨e, rank, fixed, entry, ref, support, matched⟩ := actual_outward_default_joint_tie_witness
    input single state data.target data.real unit rfl references left right a b currentL currentR
    realL realR rootL rootR pair.leftSlot pair.rightSlot addressL addressR tie charge
  exact ⟨a, b, different,
    ⟨⟨currentL, currentR, realL, realR, e, rank, fixed, entry, ref, support, matched⟩⟩⟩


end
end TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedTieWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedTieWitness.joint_refined_tie_constitutional
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedTieWitness.joint_tie_real_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedTieWitness.joint_matched_of_tie
