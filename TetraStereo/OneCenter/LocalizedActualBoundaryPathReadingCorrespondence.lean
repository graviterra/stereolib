import TetraStereo.OneCenter.LocalizedActualOutwardBoundaryObservationReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! # Address correspondence for actual outward boundary paths

For actual outward context arms whose current constitutional keys tie, expose the specific
residual path-tree equivalence built from those arms. Every path and its image are read at one
identical ranked source-tree address in the very trees belonging to the supplied stage/readers.
-/

namespace TetraStereo.OneCenter
namespace LocalizedActualBoundaryPathReadingCorrespondence

open CertifiedLocalizedCIPInput
open OfficialRuleMajorKey
open OfficialCIPNodeProvenance
open RetainedCoherentSymmetry
open LocalizedCumulativeDecoratedTree
open LocalizedRetainedConstitutionalTreeReadback
open LocalizedActualBoundaryPathRealization
open LocalizedActualBoundaryObservationReadback
open LocalizedActualOutwardBoundaryObservationReadback
open LocalizedCyclicOutwardProvenanceSeparation
open LocalizedActualOutwardRule1bEquivalence

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

private theorem shape_eq_of_tie {input : CertifiedLocalizedCIPInput}
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

/-- Construct the actual path equivalence and expose its same-ranked-address witness. -/
theorem contextArms_equiv_with_same_address
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
    ∃ a b,
      pair.left.occurrence.1.node.current? = some a ∧
      pair.right.occurrence.1.node.current? = some b ∧
      ∃ e : ResidualPathTreeEquiv input.moleculeGraph
          pair.target.occurrence.1.node.history.reverse
          pair.target.occurrence.1.node.history.reverse a b,
        ∀ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph
            pair.target.occurrence.1.node.history.reverse a p},
          ∃ address,
            (toOfficialSourceTree armL.tree).sourceAtAddress? address =
              some (boundaryNode pair.target.occurrence.1.node.history.reverse p.1) ∧
            (toOfficialSourceTree armR.tree).sourceAtAddress? address =
              some (boundaryNode pair.target.occurrence.1.node.history.reverse (e.toEquiv p).1) := by
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
  have generatedL := contextTree_generated armL (left_incoming pair)
  have generatedR := contextTree_generated armR (right_incoming pair)
  obtain ⟨rootedL, _, adjacentL⟩ := outwardChild_boundaryRooted input simple pair.target
    pair.left pair.leftRoot pair.leftSlot pair.leftAddress targetReal leftReal leftCurrent
    armL.tree armL.sourceEq generatedL
  obtain ⟨rootedR, _, adjacentR⟩ := outwardChild_boundaryRooted input simple pair.target
    pair.right pair.rightRoot pair.rightSlot pair.rightAddress targetReal rightReal rightCurrent
    armR.tree armR.sourceEq generatedR
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace armL.trace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace armR.trace
  have sameShape := shape_eq_of_tie armL armR tie
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
  let e := residualPathTreeEquivOfSameObservations observed charge rfl
    (parentOf leftAtom adjacentL) (parentOf rightAtom adjacentR)
  refine ⟨leftAtom, rightAtom, leftCurrent, rightCurrent, e, ?_⟩
  intro p
  have corresponds := residualPathTreeEquivOfSameObservations_correspond observed charge rfl
    (parentOf leftAtom adjacentL) (parentOf rightAtom adjacentR) p
  change PathsCorrespond (toOfficialSourceTree armL.tree) (toOfficialSourceTree armR.tree)
    pair.target.occurrence.1.node.history.reverse
    pair.target.occurrence.1.node.history.reverse p.1 (e.toEquiv p).1 at corresponds
  obtain ⟨address, hleft, hright⟩ := corresponds
  exact ⟨address, hleft, hright⟩

/-- Actual-pair frontdoor: derive successful current-stage arms from emitted outward cursors,
then expose the chosen equivalence/address match for any constitutional tie at arbitrary depth. -/
theorem actualOutwardSibling_equiv_with_same_address
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
        ∃ a b,
          pair.left.occurrence.1.node.current? = some a ∧
          pair.right.occurrence.1.node.current? = some b ∧
          ∃ e : ResidualPathTreeEquiv input.moleculeGraph
              pair.target.occurrence.1.node.history.reverse
              pair.target.occurrence.1.node.history.reverse a b,
            ∀ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph
                pair.target.occurrence.1.node.history.reverse a p},
              ∃ address,
                (toOfficialSourceTree armL.tree).sourceAtAddress? address =
                  some (boundaryNode pair.target.occurrence.1.node.history.reverse p.1) ∧
                (toOfficialSourceTree armR.tree).sourceAtAddress? address =
                  some (boundaryNode pair.target.occurrence.1.node.history.reverse
                    (e.toEquiv p).1) := by
  have leftValid := input.localizedRerootCursorValid_of_incoming pair.left
    (left_incoming pair)
  have rightValid := input.localizedRerootCursorValid_of_incoming pair.right
    (right_incoming pair)
  obtain ⟨armL⟩ := input.exists_ruleMajorContextArm
    (input.certified.input.molecule.atomCount + 1) stageL readL pair.left leftValid
  obtain ⟨armR⟩ := input.exists_ruleMajorContextArm
    (input.certified.input.molecule.atomCount + 1) stageR readR pair.right rightValid
  exact ⟨armL, armR, fun tie => contextArms_equiv_with_same_address input simple charge pair
    targetReal leftReal rightReal armL armR tie⟩

end LocalizedActualBoundaryPathReadingCorrespondence
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryPathReadingCorrespondence.contextArms_equiv_with_same_address
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryPathReadingCorrespondence.actualOutwardSibling_equiv_with_same_address
