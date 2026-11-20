import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel
import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Every actual semantic root-arm read carries its exact valid residual molecular path.
The path is read from the actual boundary-rooted occurrence expansion; it is not supplied. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmResidualPath

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree
open MolecularEvidenceTree
open LocalizedActualBoundaryPathRealization
open LocalizedActualBoundaryObservationReadback
open LocalizedChemicalRingActualReferenceFixing
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedChemicalRingInheritedRefusalCases (referenceAt)
open LocalizedChemicalRingJointPreparedRootKeyRelabel (target_root)
open RetainedCoherentSymmetry (ResidualObsPath)
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

theorem arm_read_residual
    (rootAddress : data.target.1.address = []) (current : raw.atom = c.1.val)
    (node : ((rootFrame input mol single c raw data state).actualArmGraphs slot).Node)
    (steps : List input.Atom) (occ : DetectedOccurrence input.moleculeGraph)
    (real : (((rootFrame input mol single c raw data state).actualArmGraphs slot).label node).provenance =
      NodeProvenance.realAtom)
    (ancestorEq : ancestorAtoms
      ((rootFrame input mol single c raw data state).actualArmGraphs slot) node = some steps)
    (contextEq : contextOccurrence input.moleculeGraph (input.molecularFrameUnit data.target.1)
      steps = some occ) :
    occ.1.root = data.target.1.root ∧
      ResidualObsPath input.moleculeGraph [c.1]
        (referenceAt input mol c raw data slot) occ.1.path := by
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
  have rooted := (root_slot_boundary single _ data.target frame rootAddress slot _
    (slot_current input mol single c raw data state slot)).1
  have sourceLookup : (toOfficialSourceTree arm.tree).sourceAtAddress? node.1 =
      some actual.source.occurrence.1.node := by
    rw [sourceAtAddress?_toOfficialSourceTree, lookup]
    rfl
  obtain ⟨p, valid, nodeEq⟩ := exists_residualObsPath_of_real single node.1
    [data.target.1.root] (referenceAt input mol c raw data slot)
    (toOfficialSourceTree arm.tree) actual.source.occurrence.1.node rooted sourceLookup realSource
  have cursorRoot : actual.source.occurrence.1.root = data.target.1.root := by
    have last := input.carrierOccurrence_history_getLast_eq_root single actual.source.occurrence
    have h : some data.target.1.root = some actual.source.occurrence.1.root := by
      simpa [nodeEq, boundaryNode] using last
    exact (Option.some.inj h).symm
  have pathEq : occ.1.path = p := by
    rw [← actualUnit]
    simp [molecularFrameUnit, nodeEq, boundaryNode]
  refine ⟨?_, ?_⟩
  · rw [← actualUnit]
    exact cursorRoot
  · rw [pathEq]
    rw [target_root input mol c raw data rootAddress current] at valid
    exact valid

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmResidualPath

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmResidualPath.arm_read_residual
