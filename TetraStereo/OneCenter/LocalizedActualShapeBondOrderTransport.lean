import TetraStereo.OneCenter.LocalizedActualRealPositionRootedBranch
import TetraStereo.OneCenter.LocalizedActualDuplicateExcessDegree
import TetraStereo.KernelOnly

set_option autoImplicit false













































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open LocalizedMultipleBondOrderReconstruction

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## The actual physical incident excess sum at a real position -/




noncomputable def actualPhysicalIncidentExcess
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) : Nat :=
  (input.moleculeGraph.neighborFinset (realPositionAtom p)).sum
    (fun u => input.moleculeGraph.bond (realPositionAtom p) u - 1)

/-- The actual incoming excess weight of a rooted real-position branch with boundary atom
`cut`: `bond (atom v) (parent atom v) - 1`, and the boundary bond excess at the root. -/
noncomputable def actualIncomingExcessAt
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (data : RootedBranch (RealPosition tree)) (cut : input.Atom) :
    RealPosition tree → Nat :=
  incomingExcess input.moleculeGraph data realPositionAtom cut

/-! ## The actual incoming coordinate and cursor validity at every real position -/







theorem realPosition_incoming_and_valid
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (startPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (startIncoming : tree.source.previous? = some startPrevious)
    (startPreviousReal : startPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (startValid : input.LocalizedRerootCursorValid tree.source)
    (p : RealPosition tree) :
    ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
      (positionNode p.1).source.previous? = some previous ∧
        previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
          input.LocalizedRerootCursorValid (positionNode p.1).source := by
  by_cases root : p.1.val = []
  · have nodeEq : positionNode p.1 = tree := positionNode_eq_tree_of_val_eq_nil root
    refine ⟨startPrevious, ?_, ?_, ?_⟩
    · rw [nodeEq]
      exact startIncoming
    · exact startPreviousReal
    · rw [nodeEq]
      exact startValid
  · obtain ⟨slot, lookup⟩ := positionParent_node_child p.1 root
    let parentNode : LocalizedCumulativeDecoratedTree input carrierFuel :=
      positionNode (positionParent p.1 root)
    have parentRealizes : LocalizedCumulativeTreeRealizes input read parentNode :=
      realizes_of_subtree realizes (positionNode_spec (positionParent p.1 root))
    have executable : E input parentNode.source (positionNode p.1).source :=
      mem_executable_of_child parentRealizes lookup
    refine ⟨parentNode.source.occurrence, ?_, ?_, ?_⟩
    · exact child_previous_of_child parentRealizes lookup
    · exact provenance_real_of_executableChild parentNode.source
        (positionNode p.1).source executable
    · exact child_valid_of_child parentRealizes lookup

/-! ## The complete actual data of the two compared trees -/

/-- All actual hypotheses of the same-shape bond-order transport, for two realized trees with
independent readers.  Every field is an actual domain condition, not a desired conclusion:

* `acyclic` and `enough` are the finite acyclic carrier conditions;
* the two realization witnesses carry independent auxiliary-label readers;
* the two root realness witnesses are actual source facts;
* `hshape` is the full comparison-visible shape equality;
* each side supplies its actual root incoming occurrence, its realness, the shared root, cursor
  validity, the boundary edge and the observed endpoint atoms.

No sum agreement, weight law or bond preservation is a field. -/
structure ActualShapeBondData
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel) where
  acyclic : input.moleculeGraph.Acyclic
  enough : input.certified.input.molecule.atomCount ≤ carrierFuel
  leftRealizes : LocalizedCumulativeTreeRealizes input readLeft left
  rightRealizes : LocalizedCumulativeTreeRealizes input readRight right
  leftRootReal : left.source.occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  rightRootReal : right.source.occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  hshape : shape left = shape right
  leftPrevious : input.LocalizedCIPOccurrence carrierFuel
  leftIncoming : left.source.previous? = some leftPrevious
  leftSameRoot : left.source.occurrence.1.root = leftPrevious.1.root
  leftValid : input.LocalizedRerootCursorValid left.source
  leftPreviousReal : leftPrevious.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  rightPrevious : input.LocalizedCIPOccurrence carrierFuel
  rightIncoming : right.source.previous? = some rightPrevious
  rightSameRoot : right.source.occurrence.1.root = rightPrevious.1.root
  rightValid : input.LocalizedRerootCursorValid right.source
  rightPreviousReal : rightPrevious.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  oAtomL : input.Atom
  pAtomL : input.Atom
  oAtomR : input.Atom
  pAtomR : input.Atom
  leftObserved : left.source.occurrence.1.node.current? = some oAtomL
  leftPreviousObserved : leftPrevious.1.node.current? = some pAtomL
  leftIncomingEdge : input.moleculeGraph.Adj pAtomL oAtomL
  rightObserved : right.source.occurrence.1.node.current? = some oAtomR
  rightPreviousObserved : rightPrevious.1.node.current? = some pAtomR
  rightIncomingEdge : input.moleculeGraph.Adj pAtomR oAtomR

section ActualShapeTransport

variable {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
  Option LocalizedAuxiliaryLabel}
variable {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
variable (D : ActualShapeBondData input carrierFuel readLeft readRight left right)


noncomputable def actualShapeBranchIso :
    RootedBranchIso (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal)
      (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal) :=
  actualRealPositionBranchIso D.acyclic D.leftRealizes D.rightRealizes D.leftRootReal
    D.rightRootReal D.hshape











theorem actualNeighborExcessSum_eq_at_mapped_position (p : RealPosition left) :
    actualPhysicalIncidentExcess p =
      actualPhysicalIncidentExcess
        (realPositionShapeEquiv D.acyclic D.leftRealizes D.rightRealizes D.leftRootReal
          D.rightRootReal D.hshape p) := by
  classical
  let q : RealPosition right :=
    realPositionShapeEquiv D.acyclic D.leftRealizes D.rightRealizes D.leftRootReal
      D.rightRootReal D.hshape p
  have leftSub : LocalizedCumulativeTreeRealizes input readLeft (positionNode p.1) :=
    realizes_of_subtree D.leftRealizes (positionNode_spec p.1)
  have rightSub : LocalizedCumulativeTreeRealizes input readRight (positionNode q.1) :=
    realizes_of_subtree D.rightRealizes (positionNode_spec q.1)
  obtain ⟨leftPreviousP, leftIncomingP, leftPreviousPReal, leftValidP⟩ :=
    realPosition_incoming_and_valid D.leftRealizes D.leftPrevious
      D.leftIncoming D.leftPreviousReal D.leftValid p
  obtain ⟨rightPreviousQ, rightIncomingQ, rightPreviousQReal, rightValidQ⟩ :=
    realPosition_incoming_and_valid D.rightRealizes D.rightPrevious
      D.rightIncoming D.rightPreviousReal D.rightValid q
  exact neighborExcessSum_eq_of_shape_eq_of_real_incoming D.acyclic D.enough
    (positionNode p.1) (positionNode q.1)
    leftSub rightSub p.2 q.2
    leftPreviousP leftIncomingP leftPreviousPReal leftValidP
    (realPositionAtom p) (realPositionAtom_spec p)
    rightPreviousQ rightIncomingQ rightPreviousQReal rightValidQ
    (realPositionAtom q) (realPositionAtom_spec q)
    (shapePositionEquiv_positionNode_shape_eq D.hshape p.1).symm

/-! ## The two canonical physical branch trees and their actual weights -/


noncomputable def actualLeftCanonicalPhysicalBranchTree :
    PhysicalBranchTree input.moleculeGraph
      (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal) :=
  canonicalPhysicalBranchTree D.acyclic D.enough D.leftRealizes D.leftPrevious
    D.leftIncoming D.leftSameRoot D.leftValid D.leftRootReal D.leftPreviousReal
    D.leftObserved D.leftPreviousObserved D.leftIncomingEdge


noncomputable def actualRightCanonicalPhysicalBranchTree :
    PhysicalBranchTree input.moleculeGraph
      (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal) :=
  canonicalPhysicalBranchTree D.acyclic D.enough D.rightRealizes D.rightPrevious
    D.rightIncoming D.rightSameRoot D.rightValid D.rightRootReal D.rightPreviousReal
    D.rightObserved D.rightPreviousObserved D.rightIncomingEdge

/-- The actual incoming excess weight on the left canonical physical branch.  Its boundary atom is
the actual previous atom `pAtomL`, exactly the `cutRoot` of
`actualLeftCanonicalPhysicalBranchTree`. -/
noncomputable def actualLeftIncomingExcess : RealPosition left → Nat :=
  actualIncomingExcessAt
    (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal) D.pAtomL

/-- The actual incoming excess weight on the right canonical physical branch. -/
noncomputable def actualRightIncomingExcess : RealPosition right → Nat :=
  actualIncomingExcessAt
    (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal) D.pAtomR




theorem actualLeftPhysicalExcessDecomposition (v : RealPosition left) :
    actualPhysicalIncidentExcess v =
      childTotal (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal).childList
        (actualLeftIncomingExcess D) v := by
  exact physical_excess_decomposition input.moleculeGraph
    (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal)
    (actualLeftCanonicalPhysicalBranchTree D) D.acyclic
    (fun a => (input.moleculeGraph.neighborFinset a).sum
      (fun u => input.moleculeGraph.bond a u - 1))
    (fun _ => rfl) v

/-- **The right childTotal equation is derived, not assumed.** -/
theorem actualRightPhysicalExcessDecomposition (v : RealPosition right) :
    actualPhysicalIncidentExcess v =
      childTotal (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal).childList
        (actualRightIncomingExcess D) v := by
  exact physical_excess_decomposition input.moleculeGraph
    (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal)
    (actualRightCanonicalPhysicalBranchTree D) D.acyclic
    (fun a => (input.moleculeGraph.neighborFinset a).sum
      (fun u => input.moleculeGraph.bond a u - 1))
    (fun _ => rfl) v





theorem actualIncomingExcess_transport (p : RealPosition left) :
    actualLeftIncomingExcess D p =
      actualRightIncomingExcess D ((actualShapeBranchIso D).toEquiv p) := by
  exact actualRealPositionBranchIso_weights_transport D.acyclic D.leftRealizes D.rightRealizes
    D.leftRootReal D.rightRootReal D.hshape
    (actualPhysicalIncidentExcess (tree := left))
    (actualPhysicalIncidentExcess (tree := right))
    (actualLeftIncomingExcess D) (actualRightIncomingExcess D)
    (fun x => by
      simpa only [actualShapeBranchIso, actualRealPositionBranchIso] using
        actualNeighborExcessSum_eq_at_mapped_position D x)
    (actualLeftPhysicalExcessDecomposition D)
    (actualRightPhysicalExcessDecomposition D) p

/-! ## Actual bond orders -/

/-- **Every internal parent/child bond order is preserved.**  Both internal bond orders equal their
reconstructed incoming excess plus one; positivity of the actual adjacency supplies
`bond = (bond - 1) + 1`, so no `SimpleBonded` hypothesis is used. -/
theorem actualInternalBondEq (p c : RealPosition left) (hpc : RealPositionChild p c) :
    input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom c) =
      input.moleculeGraph.bond
        (realPositionAtom ((actualShapeBranchIso D).toEquiv p))
        (realPositionAtom ((actualShapeBranchIso D).toEquiv c)) := by
  classical
  have hmemLeft :
      c ∈ (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal).childList p :=
    (realChildList_iff_realPositionChild p c).mpr hpc
  have hmemRight :
      (actualShapeBranchIso D).toEquiv c ∈
        (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal).childList
          ((actualShapeBranchIso D).toEquiv p) := by
    have hm : (actualShapeBranchIso D).toEquiv c ∈
        ((canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal).childList p).map
          (actualShapeBranchIso D).toEquiv :=
      List.mem_map.mpr ⟨c, hmemLeft, rfl⟩
    rwa [(actualShapeBranchIso D).map_children p] at hm
  have hleft := internal_bond_eq input.moleculeGraph
    (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal)
    (actualLeftCanonicalPhysicalBranchTree D) D.acyclic
    (fun a => (input.moleculeGraph.neighborFinset a).sum
      (fun u => input.moleculeGraph.bond a u - 1))
    (fun _ => rfl) (actualLeftIncomingExcess D)
    (actualLeftPhysicalExcessDecomposition D) hmemLeft
  have hright := internal_bond_eq input.moleculeGraph
    (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal)
    (actualRightCanonicalPhysicalBranchTree D) D.acyclic
    (fun a => (input.moleculeGraph.neighborFinset a).sum
      (fun u => input.moleculeGraph.bond a u - 1))
    (fun _ => rfl) (actualRightIncomingExcess D)
    (actualRightPhysicalExcessDecomposition D) hmemRight
  calc
    input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom c)
        = actualLeftIncomingExcess D c + 1 := hleft
    _ = actualRightIncomingExcess D ((actualShapeBranchIso D).toEquiv c) + 1 := by
          rw [actualIncomingExcess_transport D c]
    _ = input.moleculeGraph.bond
          (realPositionAtom ((actualShapeBranchIso D).toEquiv p))
          (realPositionAtom ((actualShapeBranchIso D).toEquiv c)) := hright.symm

/-- **The root attachment boundary bond order is preserved.**  The boundary edge
`previous -- root` is reconstructed from the root residual excess plus one on each side; the two
root weights correspond through `actualShapeBranchIso`, whose `map_root` identifies the roots. -/
theorem actualBoundaryBondEq :
    input.moleculeGraph.bond D.pAtomL
        (realPositionAtom
          ⟨rootPosition left, D.leftRootReal⟩) =
      input.moleculeGraph.bond D.pAtomR
        (realPositionAtom
          ⟨rootPosition right, D.rightRootReal⟩) := by
  have hleft := boundary_bond_eq input.moleculeGraph
    (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal)
    (actualLeftCanonicalPhysicalBranchTree D) D.acyclic
    (fun a => (input.moleculeGraph.neighborFinset a).sum
      (fun u => input.moleculeGraph.bond a u - 1))
    (fun _ => rfl) (actualLeftIncomingExcess D)
    (actualLeftPhysicalExcessDecomposition D)
  have hright := boundary_bond_eq input.moleculeGraph
    (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal)
    (actualRightCanonicalPhysicalBranchTree D) D.acyclic
    (fun a => (input.moleculeGraph.neighborFinset a).sum
      (fun u => input.moleculeGraph.bond a u - 1))
    (fun _ => rfl) (actualRightIncomingExcess D)
    (actualRightPhysicalExcessDecomposition D)
  calc
    input.moleculeGraph.bond D.pAtomL
        (realPositionAtom ⟨rootPosition left, D.leftRootReal⟩)
        = actualLeftIncomingExcess D
            (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal).root + 1 := hleft
    _ = actualRightIncomingExcess D
          (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal).root + 1 := by
          rw [actualIncomingExcess_transport D
              (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal).root,
            (actualShapeBranchIso D).map_root]
    _ = input.moleculeGraph.bond D.pAtomR
          (realPositionAtom ⟨rootPosition right, D.rightRootReal⟩) := hright.symm





theorem actualAdjacentBondEq (p q : RealPosition left)
    (hadj : input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q)) :
    input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom q) =
      input.moleculeGraph.bond
        (realPositionAtom ((actualShapeBranchIso D).toEquiv p))
        (realPositionAtom ((actualShapeBranchIso D).toEquiv q)) := by
  have hpc := (realPosition_adjacent_iff_realPositionChild D.acyclic D.enough
    D.leftRealizes D.leftPrevious D.leftIncoming D.leftSameRoot D.leftValid D.leftRootReal
    D.leftPreviousReal D.leftObserved D.leftPreviousObserved D.leftIncomingEdge p q).mp hadj
  rcases hpc with hchild | hparent
  · exact actualInternalBondEq D p q hchild
  · have hrev := actualInternalBondEq D q p hparent
    rw [input.moleculeGraph.bond_symm (realPositionAtom p) (realPositionAtom q),
      input.moleculeGraph.bond_symm
        (realPositionAtom ((actualShapeBranchIso D).toEquiv p))
        (realPositionAtom ((actualShapeBranchIso D).toEquiv q))]
    exact hrev

/-- **Final actual same-shape bond-order transport.**  For the same constructed
`actualRealPositionBranchIso`, and with no desired sum agreement, weight law or bond preservation
assumed as a hypothesis:

1. the actual physical incident excess sums agree at every mapped real position;
2. every actual incoming excess (parent-bond excess or boundary-bond excess) agrees at every
   mapped real position;
3. every internal parent/child bond order is equal;
4. the root attachment boundary bond order is equal. -/
theorem actualShape_bond_order_transport :
    (∀ p : RealPosition left, actualPhysicalIncidentExcess p =
      actualPhysicalIncidentExcess ((actualShapeBranchIso D).toEquiv p)) ∧
    (∀ p : RealPosition left, actualLeftIncomingExcess D p =
      actualRightIncomingExcess D ((actualShapeBranchIso D).toEquiv p)) ∧
    (∀ (p c : RealPosition left), RealPositionChild p c →
      input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom c) =
        input.moleculeGraph.bond
          (realPositionAtom ((actualShapeBranchIso D).toEquiv p))
          (realPositionAtom ((actualShapeBranchIso D).toEquiv c))) ∧
    input.moleculeGraph.bond D.pAtomL
        (realPositionAtom ⟨rootPosition left, D.leftRootReal⟩) =
      input.moleculeGraph.bond D.pAtomR
        (realPositionAtom ⟨rootPosition right, D.rightRootReal⟩) :=
  ⟨fun p => by
      simpa only [actualShapeBranchIso, actualRealPositionBranchIso] using
        actualNeighborExcessSum_eq_at_mapped_position D p,
    fun p => actualIncomingExcess_transport D p,
    fun p c h => actualInternalBondEq D p c h,
    actualBoundaryBondEq D⟩

end ActualShapeTransport

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.actualPhysicalIncidentExcess
assert_kernel_only TetraStereo.OneCenter.actualIncomingExcessAt
assert_kernel_only TetraStereo.OneCenter.realPosition_incoming_and_valid
assert_kernel_only TetraStereo.OneCenter.ActualShapeBondData
assert_kernel_only TetraStereo.OneCenter.actualShapeBranchIso
assert_kernel_only TetraStereo.OneCenter.actualNeighborExcessSum_eq_at_mapped_position
assert_kernel_only TetraStereo.OneCenter.actualLeftCanonicalPhysicalBranchTree
assert_kernel_only TetraStereo.OneCenter.actualRightCanonicalPhysicalBranchTree
assert_kernel_only TetraStereo.OneCenter.actualLeftIncomingExcess
assert_kernel_only TetraStereo.OneCenter.actualRightIncomingExcess
assert_kernel_only TetraStereo.OneCenter.actualLeftPhysicalExcessDecomposition
assert_kernel_only TetraStereo.OneCenter.actualRightPhysicalExcessDecomposition
assert_kernel_only TetraStereo.OneCenter.actualIncomingExcess_transport
assert_kernel_only TetraStereo.OneCenter.actualInternalBondEq
assert_kernel_only TetraStereo.OneCenter.actualBoundaryBondEq
assert_kernel_only TetraStereo.OneCenter.actualAdjacentBondEq
assert_kernel_only TetraStereo.OneCenter.actualShape_bond_order_transport
