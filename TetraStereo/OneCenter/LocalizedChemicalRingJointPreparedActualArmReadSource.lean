import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Every real semantic read of an actual retained root arm is a molecular-reader consult.
The source cursor, reachability, provenance and full occurrence history are reconstructed
from its actual stage tree; no reader correspondence is assumed. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmReadSource

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree
open MolecularEvidenceTree
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedRootArmLocality

noncomputable section
open scoped Classical

private theorem occurrenceUnit_ext {Atom : Type*} {a b : OccurrenceUnit Atom}
    (rootEq : a.root = b.root) (pathEq : a.path = b.path) : a = b := by
  cases a
  cases b
  simp_all

private theorem actualSubtree_at_node {input : CertifiedLocalizedCIPInput}
    {fuel : Nat} (tree : LocalizedCumulativeDecoratedTree input fuel)
    (node : (ruleMajorTreeGraph tree).Node) :
    ∃ actual, tree.decoratedSubtreeAt? node.1 = some actual := by
  obtain ⟨erased, erasedLookup⟩ :=
    (toOfficialSourceTree tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses node.1 node.2
  have mapped : (tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree = some erased := by
    rw [← toOfficialSourceTree_subtreeAt?]
    exact erasedLookup
  obtain ⟨actual, lookup, _⟩ := Option.map_eq_some_iff.mp mapped
  exact ⟨actual, lookup⟩

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (raw : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c raw)
  (state : OccurrenceAuxState) (slot : Fin 4)

theorem arm_read_source
    (node : ((rootFrame input mol single c raw data state).actualArmGraphs slot).Node)
    (steps : List input.Atom) (occ : DetectedOccurrence input.moleculeGraph)
    (real : (((rootFrame input mol single c raw data state).actualArmGraphs slot).label node).provenance =
      NodeProvenance.realAtom)
    (ancestorEq : ancestorAtoms
      ((rootFrame input mol single c raw data state).actualArmGraphs slot) node = some steps)
    (contextEq : contextOccurrence input.moleculeGraph (input.molecularFrameUnit data.target.1)
      steps = some occ) :
    ∃ cursor : input.LocalizedRerootCursor (retainedCarrierFuel input),
      Relation.ReflTransGen (E input)
        ((rootFrame input mol single c raw data state).frame.cursorAt slot) cursor ∧
      cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      input.molecularFrameUnit cursor.occurrence.1 = occ.1 := by
  let frame := rootFrame input mol single c raw data state
  let arm := (frame.stages slot).a
  let rootCursor : input.LocalizedRerootCursor (retainedCarrierFuel input) := ⟨data.target, none⟩
  obtain ⟨actual, lookup⟩ := actualSubtree_at_node arm.tree node
  have sourceChild : arm.tree.source ∈ input.executableLocalizedRerootChildren rootCursor := by
    rw [arm.sourceEq]
    exact frame.childAt slot
  have lookup' : subtreeAt? arm.tree node.1 = some actual := by
    rwa [← decoratedSubtreeAt?_eq_subtreeAt?]
  obtain ⟨walkSteps, walkEq, walkRoot, walkPath⟩ :=
    input.retainedCursorFrame_eq_ancestorWalk single rootCursor arm.tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) sourceChild node actual lookup'
  have stepsWalk : walkSteps = steps := by
    have ancestors : ancestorAtoms (frame.actualArmGraphs slot) node = some walkSteps := by
      change ancestorAtoms (ruleMajorTreeGraph arm.tree) node = some walkSteps
      simpa [retainedOccurrenceSteps_eq_ancestorAtoms] using walkEq
    exact Option.some.inj (ancestors.symm.trans ancestorEq)
  have contextUnit : occ.1 =
      ⟨(input.molecularFrameUnit data.target.1).root,
        rerootWalk (input.molecularFrameUnit data.target.1).root
          (input.molecularFrameUnit data.target.1).path steps⟩ := by
    unfold contextOccurrence at contextEq
    dsimp only at contextEq
    split at contextEq
    · exact (congrArg Subtype.val (Option.some.inj contextEq)).symm
    · simp at contextEq
  have actualUnit : input.molecularFrameUnit actual.source.occurrence.1 = occ.1 := by
    apply occurrenceUnit_ext
    · exact walkRoot.trans (congrArg OccurrenceUnit.root contextUnit).symm
    · calc
        (input.molecularFrameUnit actual.source.occurrence.1).path =
            rerootWalk (input.molecularFrameUnit data.target.1).root
              (input.molecularFrameUnit data.target.1).path walkSteps := walkPath
        _ = rerootWalk (input.molecularFrameUnit data.target.1).root
              (input.molecularFrameUnit data.target.1).path steps := by rw [stepsWalk]
        _ = occ.1.path := (congrArg OccurrenceUnit.path contextUnit).symm
  have reachable : Relation.ReflTransGen (E input) (frame.frame.cursorAt slot) actual.source := by
    rw [← arm.sourceEq]
    exact input.subtreeAt?_source_reachable
      (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) lookup'
  have erased : (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
      some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, lookup']
    rfl
  have labels := (toOfficialSourceTree arm.tree).declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree actual) node erased
  change ((toOfficialSourceTree arm.tree).declarativeLabel node).provenance =
    NodeProvenance.realAtom at real
  rw [labels, toOfficialSourceTree_source] at real
  have realSource : actual.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
    cases h : actual.source.occurrence.1.node.provenance with
    | realAtom => rfl
    | multipleBondDuplicate distance =>
        simp_all [OfficialCIPNode.toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative]
    | ringDuplicate distance =>
        simp_all [OfficialCIPNode.toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative]
    | placeholder kind distance =>
        cases kind <;>
          simp_all [OfficialCIPNode.toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative]
  exact ⟨actual.source, reachable, realSource, actualUnit⟩

theorem arm_read_consult (rootAddress : data.target.1.address = [])
    (node : ((rootFrame input mol single c raw data state).actualArmGraphs slot).Node)
    (steps : List input.Atom) (occ : DetectedOccurrence input.moleculeGraph)
    (real : (((rootFrame input mol single c raw data state).actualArmGraphs slot).label node).provenance =
      NodeProvenance.realAtom)
    (ancestorEq : ancestorAtoms
      ((rootFrame input mol single c raw data state).actualArmGraphs slot) node = some steps)
    (contextEq : contextOccurrence input.moleculeGraph (input.molecularFrameUnit data.target.1)
      steps = some occ) :
    input.ReachableArmDescriptorConsult data.target
      ((rootFrame input mol single c raw data state).frame.cursorAt slot) occ := by
  obtain ⟨cursor, reachable, provenance, unitEq⟩ :=
    arm_read_source input mol single c raw data state slot node steps occ real ancestorEq contextEq
  exact ⟨cursor, reachable,
    (input.outward_reachable_cursor data.target _ cursor
      (root_slot_outward input mol single c raw data rootAddress state slot) reachable).2.1,
    provenance, unitEq⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmReadSource

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmReadSource.arm_read_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmReadSource.arm_read_consult
