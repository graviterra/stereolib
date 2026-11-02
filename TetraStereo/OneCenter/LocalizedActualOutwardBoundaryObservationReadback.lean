import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback
import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! # Actual outward boundary observation readback

For real outward siblings at an auxiliary target, a tie between current rule-major keys yields
equal three-column tables of the exact context-reader trees.  The trees are rooted below the
target's full root-first history.  The generic boundary path-tree construction then gives the
residual equivalence needed by the cyclic rigidity consumer, with address observations from the
same stage and reader that supplied the tie.
-/

namespace TetraStereo.OneCenter
namespace LocalizedActualOutwardBoundaryObservationReadback

open CertifiedLocalizedCIPInput
open OfficialRuleMajorKey
open RetainedCoherentSymmetry
open LocalizedCumulativeDecoratedTree
open LocalizedRetainedConstitutionalTreeReadback
open LocalizedActualBoundaryPathRealization
open LocalizedActualBoundaryObservationReadback
open LocalizedActualOutwardRule1bEquivalence
open LocalizedCyclicOutwardProvenanceSeparation

private theorem left_incoming {input : CertifiedLocalizedCIPInput}
    {fuel : Nat} (pair : ActualOutwardSiblingPair input fuel) :
    LocalizedRerootCursorIncomingParent input pair.left := by
  refine ⟨pair.target.occurrence, pair.leftPrevious, pair.leftRoot.symm, ?_, ?_⟩
  · rw [pair.leftAddress]
    simp
  · rw [pair.leftAddress]
    simp

private theorem right_incoming {input : CertifiedLocalizedCIPInput}
    {fuel : Nat} (pair : ActualOutwardSiblingPair input fuel) :
    LocalizedRerootCursorIncomingParent input pair.right := by
  refine ⟨pair.target.occurrence, pair.rightPrevious, pair.rightRoot.symm, ?_, ?_⟩
  · rw [pair.rightAddress]
    simp
  · rw [pair.rightAddress]
    simp

private theorem contextTree_generated {input : CertifiedLocalizedCIPInput}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1)}
    {stage : LocalizedCumulativeRule45Stage}
    (arm : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stage read cursor)
    (incoming : LocalizedRerootCursorIncomingParent input cursor) :
    (toOfficialSourceTree arm.tree).GeneratedBy input.executableOfficialCIPChildren := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace
  have positive : LocalizedCumulativeTreePositive arm.tree :=
    input.localizedCumulativeTreePositive_of_atomCount_le (by omega) arm.tree
  have treeIncoming := input.localizedCumulativeTreeIncoming_of_realizes read arm.tree
    realizes (by simpa [arm.sourceEq] using incoming)
  exact input.toOfficialSourceTree_generatedBy read arm.tree realizes positive treeIncoming

private theorem contextTree_shape_eq_of_tie {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (armL : input.RuleMajorContextArm carrierFuel stageL readL left)
    (armR : input.RuleMajorContextArm carrierFuel stageR readR right)
    (tie : OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional =
      Ordering.eq) : armL.tree.shape = armR.tree.shape := by
  have columns := (officialRuleMajorKey_compare_eq_iff
    armL.key.constitutional armR.key.constitutional).mp tie
  have matchL := (LocalizedRuleMajorSortTrace.fullMatch_of_trace armL.trace).tableMatch
  have matchR := (LocalizedRuleMajorSortTrace.fullMatch_of_trace armR.trace).tableMatch
  rcases matchL with ⟨h1aL, h1bL, h2L, _⟩
  rcases matchR with ⟨h1aR, h1bR, h2R, _⟩
  simp only [tables_rule1a, tables_rule1b, tables_rule2] at h1aL h1bL h2L h1aR h1bR h2R
  exact table_shape_eq_of_constitutional_tables_eq armL.tree armR.tree
    (h1aL.trans (columns.1.trans h1aR.symm))
    (h1bL.trans (columns.2.1.trans h1bR.symm))
    (h2L.trans (columns.2.2.trans h2R.symm))

/-- At any current rule-major stages and readers, a constitutional tie of two actual outward
context arms gives a residual path-tree equivalence below the target's entire source history.
The trace arms are actual successful builds, and their same-reader addressed observations are
read from those very trees. -/
theorem contextArms_residualPathTreeEquiv_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (pair : ActualOutwardSiblingPair input (input.certified.input.molecule.atomCount + 1))
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (leftReal : pair.left.occurrence.1.node.provenance = .realAtom)
    (rightReal : pair.right.occurrence.1.node.provenance = .realAtom)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (armL : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stageL readL pair.left)
    (armR : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stageR readR pair.right)
    (tie : OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional =
      Ordering.eq) :
    ∃ a b, pair.left.occurrence.1.node.current? = some a ∧
      pair.right.occurrence.1.node.current? = some b ∧
      Nonempty (ResidualPathTreeEquiv input.moleculeGraph
        pair.target.occurrence.1.node.history.reverse
        pair.target.occurrence.1.node.history.reverse a b) := by
  have leftMem := outwardChild_node_mem input pair.target pair.left pair.leftRoot
    pair.leftSlot pair.leftAddress
  have rightMem := outwardChild_node_mem input pair.target pair.right pair.rightRoot
    pair.rightSlot pair.rightAddress
  obtain ⟨t, ht⟩ := exists_current_of_mem_children input leftMem
  obtain ⟨leftAtom, leftNode, _, _⟩ := outwardChild_atom_facts input simple pair.target
    pair.left pair.leftRoot pair.leftSlot pair.leftAddress targetReal leftReal ht
  obtain ⟨rightAtom, rightNode, _, _⟩ := outwardChild_atom_facts input simple pair.target
    pair.right pair.rightRoot pair.rightSlot pair.rightAddress targetReal rightReal ht
  have leftCurrent : pair.left.occurrence.1.node.current? = some leftAtom := by
    rw [leftNode]
    rfl
  have rightCurrent : pair.right.occurrence.1.node.current? = some rightAtom := by
    rw [rightNode]
    rfl
  have leftGenerated := contextTree_generated armL (left_incoming pair)
  have rightGenerated := contextTree_generated armR (right_incoming pair)
  obtain ⟨rootedL, _, adjacentL⟩ := outwardChild_boundaryRooted input simple pair.target
    pair.left pair.leftRoot pair.leftSlot pair.leftAddress targetReal leftReal leftCurrent
    armL.tree armL.sourceEq leftGenerated
  obtain ⟨rootedR, _, adjacentR⟩ := outwardChild_boundaryRooted input simple pair.target
    pair.right pair.rightRoot pair.rightSlot pair.rightAddress targetReal rightReal rightCurrent
    armR.tree armR.sourceEq rightGenerated
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace armL.trace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace armR.trace
  have sameShape := contextTree_shape_eq_of_tie armL armR tie
  have observed := observedTreePair_of_constitutional simple rootedL rootedR rfl
    (constitutionalObservationAt_eq_of_shape_eq input armL.tree armR.tree realizesL realizesR
      sameShape)
  have targetFacts := occurrence_history_facts input pair.target.occurrence targetReal
  have parentOf : ∀ c : input.Atom,
      (∀ t, pair.target.occurrence.1.node.current? = some t → input.moleculeGraph.Adj t c) →
        ∀ z, pair.target.occurrence.1.node.history.reverse.getLast? = some z →
          input.moleculeGraph.Adj c z := by
    intro c adjacent z hz
    rw [List.getLast?_reverse, ← targetFacts.2] at hz
    exact input.moleculeGraph.adj_symm.mp (adjacent z hz)
  exact ⟨leftAtom, rightAtom, leftCurrent, rightCurrent,
    ⟨residualPathTreeEquivOfSameObservations observed charge rfl
      (parentOf leftAtom adjacentL) (parentOf rightAtom adjacentR)⟩⟩

/-- Actual sibling façade: it derives successful current-stage context arms from the emitted
outward cursors, then turns any constitutional tie of those derived keys into the residual
path-tree equivalence. -/
theorem actualOutwardSibling_residualPathTreeEquiv
    (input : CertifiedLocalizedCIPInput)
    (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (pair : ActualOutwardSiblingPair input (input.certified.input.molecule.atomCount + 1))
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (leftReal : pair.left.occurrence.1.node.provenance = .realAtom)
    (rightReal : pair.right.occurrence.1.node.provenance = .realAtom)
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel) :
    ∃ armL : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
        stageL readL pair.left,
      ∃ armR : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
        stageR readR pair.right,
      ∀ tie : OfficialRuleMajorKey.compare armL.key.constitutional
        armR.key.constitutional = Ordering.eq,
        ∃ a b, pair.left.occurrence.1.node.current? = some a ∧
          pair.right.occurrence.1.node.current? = some b ∧
          Nonempty (ResidualPathTreeEquiv input.moleculeGraph
            pair.target.occurrence.1.node.history.reverse
            pair.target.occurrence.1.node.history.reverse a b) := by
  have leftValid := input.localizedRerootCursorValid_of_incoming pair.left (left_incoming pair)
  have rightValid := input.localizedRerootCursorValid_of_incoming pair.right (right_incoming pair)
  obtain ⟨armL⟩ := input.exists_ruleMajorContextArm
    (input.certified.input.molecule.atomCount + 1) stageL readL pair.left leftValid
  obtain ⟨armR⟩ := input.exists_ruleMajorContextArm
    (input.certified.input.molecule.atomCount + 1) stageR readR pair.right rightValid
  exact ⟨armL, armR, fun tie => contextArms_residualPathTreeEquiv_of_constitutionalTie
    input simple charge pair targetReal leftReal rightReal armL armR tie⟩

end LocalizedActualOutwardBoundaryObservationReadback
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardBoundaryObservationReadback.contextArms_residualPathTreeEquiv_of_constitutionalTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardBoundaryObservationReadback.actualOutwardSibling_residualPathTreeEquiv
