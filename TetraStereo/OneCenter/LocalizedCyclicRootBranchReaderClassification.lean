import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels
import TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinRefusal
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Actual dependency-reader classification on cyclic tied root branches

This module combines the current RuleMajorReference fixed point's cyclic terminal-twin refusal
with the generated-label classification for physically general-rigid centers.  The branch
front-door retains the actual root-arm membership and Rule-1a tie; the reader conclusion is
restricted to occurrences below that arm.
-/

namespace TetraStereo.OneCenter
namespace LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput
open DeclarativeCIP
noncomputable section
open scoped Classical

/-- A current generated state read at an actual real detected occurrence under one of two tied
root arms is sparse.  A physical terminal-twin center is refused by the current evaluator; in the
other case the cyclic generated-label theorem derives the uppercase label from the physical
general-rigid domain.  The arm keys and their Rule-1a tie are actual successful current builds.
-/
theorem referenceState_sparse_of_tiedRootArm_of_domain
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (rootEq : root.1 = target.1.root)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root) :
    LocalizedRule4bSparseLabel (referenceState input target) := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target frames.center).mp frames.centerComputed
  have centerNonroot : (frames.center : input.certified.detectedMultiCenterMolecule.Center) ≠
      root := by
    intro same
    apply LocalizedCyclicGeneralRigidPriority.current_ne_root_of_nonroot
      input.certified target real nonroot centerMeaning.2
    rw [← rootEq]
    exact congrArg Subtype.val same
  by_cases notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule frames.center
  · obtain ⟨_strict, ⟨priority, _order, generated⟩⟩ :=
      LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_eq_chiral_of_tiedRootArm_of_domain
        input singleBonded charge rootCursor rootAddress armCursor armCursor' armMem armMem'
        armDistinct armReal armReal' armRead armRead' armKey armKey' armBuilt armBuilt' tie
        target real unit targetUnit inside nonroot cfg root domain rootEq notTwin
    exact Or.inr ⟨(if input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
      permHandedness frames.detectedLigandPermutation * permHandedness priority = -1 then .R else .S),
      generated⟩
  · have twin : ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule frames.center :=
      Classical.not_not.mp notTwin
    have targetCurrent : target.1.node.current? = some frames.center.1 := by
      exact centerMeaning.2
    have leaves := CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinLeaves_of_globalTwinCenter
      input input.certified.detectedMultiCenterMolecule domain.graphEq frames.center target
      targetCurrent twin
    rcases leaves with ⟨centerAtom, leftLeaf, rightLeaf, current, _tetra, leftNeighbors,
      rightNeighbors, leavesDistinct, zEq, massEq, _chargeEq⟩
    have centerEq : centerAtom = frames.center.1 :=
      Option.some.inj (current.symm.trans targetCurrent)
    have leftNeighbors' : input.certified.moleculeGraph.neighborFinset leftLeaf =
        {frames.center.1} := by simpa [← centerEq] using leftNeighbors
    have rightNeighbors' : input.certified.moleculeGraph.neighborFinset rightLeaf =
        {frames.center.1} := by simpa [← centerEq] using rightNeighbors
    exact Or.inl (referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves input singleBonded
      target frames.center centerMeaning leftLeaf rightLeaf leftNeighbors' rightNeighbors'
      leavesDistinct rootTetrahedral zEq massEq)

/-- On a reached strict dependency in a tied root branch, the actual restricted dependency reader
returns the same sparse value as the generated current fixed point.  `inside` is the full
original-root path membership; `dependency` records the source-target relation used by the actual
reader's definition.
-/
theorem localizedDependencyLabel_sparse_of_tiedRootArm_of_domain
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (rootEq : root.1 = target.1.root)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorAtTarget : cursor.occurrence = target)
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence rootCursor.occurrence)
    :
    LocalizedRule4bSparseLabel
      (input.certified.localizedDependencyLabel rootCursor.occurrence
        (input.certified.localizedDependencyView (referenceState input) rootCursor.occurrence)
        cursor) := by
  rw [input.certified.localizedDependencyLabel_eq_state_of_dependency
    rootCursor.occurrence (referenceState input) cursor dependency]
  simpa [cursorAtTarget] using referenceState_sparse_of_tiedRootArm_of_domain input singleBonded charge rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
    armKey armKey' armBuilt armBuilt' tie target real unit targetUnit inside nonroot cfg root
    domain rootEq rootTetrahedral

/-- Full reached-occurrence classification. Ring duplicates are rejected by the current fixed
point, real nondetected atoms are rejected by its center gate, and real detected centers use the
physical tied-arm result above. The branch membership is retained for the exact occurrence whose
dependency reader is being classified.
-/
theorem localizedDependencyLabel_sparse_of_reachedTiedRootArm_of_domain
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (inside : input.certified.RootBranchContains armCursor.occurrence cursor.occurrence)
    (nonroot : cursor.occurrence.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (rootEq : root.1 = cursor.occurrence.1.root)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter
      cursor.occurrence.1.root)
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence rootCursor.occurrence) :
    LocalizedRule4bSparseLabel
      (input.certified.localizedDependencyLabel rootCursor.occurrence
        (input.certified.localizedDependencyView (referenceState input) rootCursor.occurrence)
        cursor) := by
  rw [input.certified.localizedDependencyLabel_eq_state_of_dependency
    rootCursor.occurrence (referenceState input) cursor dependency]
  rcases input.certified.carrierOccurrence_provenance_simple_or_ring singleBonded
      cursor.occurrence with real | duplicate
  · by_cases detected : IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit cursor.occurrence.1).atom
    · let unit : DetectedOccurrence input.certified.moleculeGraph :=
      ⟨input.certified.molecularFrameUnit cursor.occurrence.1, detected⟩
      have unitEq : input.certified.molecularFrameUnit cursor.occurrence.1 = unit.1 := rfl
      exact referenceState_sparse_of_tiedRootArm_of_domain input singleBonded charge rootCursor
        rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead
        armRead' armKey armKey' armBuilt armBuilt' tie cursor.occurrence real unit unitEq inside
        nonroot cfg root domain rootEq rootTetrahedral
    · exact Or.inl (referenceState_none_of_real_not_detected singleBonded cursor.occurrence
        real detected)
  · obtain ⟨distance, duplicate⟩ := duplicate
    exact Or.inl (referenceState_none_of_ringDuplicate cursor.occurrence duplicate)

end
end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_sparse_of_tiedRootArm_of_domain
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.localizedDependencyLabel_sparse_of_tiedRootArm_of_domain
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.localizedDependencyLabel_sparse_of_reachedTiedRootArm_of_domain
