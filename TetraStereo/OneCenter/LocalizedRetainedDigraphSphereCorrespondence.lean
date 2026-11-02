import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedRetainedContextObservationReadback
import TetraStereo.OneCenter.Rule1bRepresentedAtomObservation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Outer-digraph sphere of a retained arm node

A realized rule-major arm is rooted at a ligand.  Its digraph depth counts edges from that
ligand.  The retained Rule 1b reading of a real node is not that depth and is not a molecular
shortest-path distance.  `retainedCursorFrame_eq_ancestorWalk` rebuilds the carrier occurrence
path from the arm's ancestor atoms.  This module identifies the retained value with the official
depth of that occurrence.

The occurrence is the pair `(outer root, path)`.  `molecularFrameUnit_injective_on_simpleBonded_carrier`
already says that equal pairs are the same carrier occurrence, so a second ring path to the same
atom is a different occurrence.

A ring duplicate keeps the stored distance.  On a single-bond carrier that distance is
`duplicateRootDistance` of the duplicated atom in the parent history, and that index is the
depth of the earlier real visit on the same simple path.

Hanson 2018 clause (c), which would read every non-duplicate node as its own sphere, is not
used.  P-92.1.3.1(b) and P-92.2.2 remain the duplicate-node clauses.  No Rule 1a tie is assumed,
and the retained value is not supplied as an observation hypothesis.
-/

namespace TetraStereo.OneCenter.RetainedDigraphSphereCorrespondence

open CertifiedLocalizedCIPInput
open DeclarativeCIP
open LocalizedCumulativeDecoratedTree
open MolecularEvidenceTree
open Rule4aTableBridge
open Rule1bRepresentedAtomObservation

variable (input : CertifiedLocalizedCIPInput)

private theorem duplicateRootDistance_extend_of_mem
    {node : OfficialCIPNode input.Atom} {next atom : input.Atom}
    (present : atom ∈ node.history) :
    (node.extend next 0).duplicateRootDistance atom = node.duplicateRootDistance atom := by
  have reversePresent : atom ∈ node.history.reverse := List.mem_reverse.mpr present
  obtain ⟨index, found⟩ := firstIndexOf?_eq_some_of_mem atom reversePresent
  have appended := firstIndexOf?_append_eq_left_of_found atom node.history.reverse [next]
    ⟨index, found⟩
  simp only [OfficialCIPNode.duplicateRootDistance, OfficialCIPNode.extend_history,
    List.reverse_cons, appended, found, Option.getD]

private theorem duplicateRootDistance_extend_self
    {node : OfficialCIPNode input.Atom} {next : input.Atom}
    (fresh : next ∉ node.history) :
    (node.extend next 0).duplicateRootDistance next = (node.extend next 0).depth := by
  have absent : next ∉ node.history.reverse := by
    intro present
    exact fresh (List.mem_reverse.mp present)
  have found := firstIndexOf?_append_singleton_of_not_mem next node.history.reverse absent
  have distanceEq : (node.extend next 0).duplicateRootDistance next = node.history.length := by
    rw [OfficialCIPNode.duplicateRootDistance, OfficialCIPNode.extend_history, List.reverse_cons,
      found]
    simp [Option.getD, List.length_reverse]
  have depthEq : (node.extend next 0).depth = node.history.length := by
    rw [OfficialCIPNode.depth, OfficialCIPNode.extend_history, List.length_cons, Nat.add_sub_cancel]
  rw [distanceEq, depthEq]

/-- The earlier real visit of an atom on one simple occurrence path.  The visit is a prefix of
this path, so another history ending at the same atom is not this visit. -/
theorem simpleOccurrence_representedPrefix
    {root : input.Atom} {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    ∀ {atom : input.Atom}, atom ∈ node.history →
      ∃ (prefixNode : OfficialCIPNode input.Atom) (prefixAddress : List Nat),
        SimpleOccurrencePath input root prefixNode prefixAddress ∧
          prefixNode.current? = some atom ∧
          prefixNode.provenance = OfficialCIPNodeProvenance.realAtom ∧
          prefixNode.depth = node.duplicateRootDistance atom ∧
          prefixNode.history.reverse <+: node.history.reverse := by
  induction path with
  | root =>
      intro atom present
      have atomEq : atom = root := by
        simpa [OfficialCIPNode.root, List.mem_singleton] using present
      refine ⟨OfficialCIPNode.root root, [], SimpleOccurrencePath.root, ?_, rfl, ?_,
        List.prefix_refl _⟩
      · simp [OfficialCIPNode.root, atomEq]
      · simp [OfficialCIPNode.root, OfficialCIPNode.depth, OfficialCIPNode.duplicateRootDistance,
          atomEq]
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      intro atom present
      rw [OfficialCIPNode.extend_history] at present
      rcases List.mem_cons.mp present with rfl | parentPresent
      · refine ⟨node.extend atom 0,
          address ++ [input.executableOfficialChildCopySlot node atom 0],
          SimpleOccurrencePath.step path currentObserved adjacent notParent fresh,
          by simp [OfficialCIPNode.extend_current?],
          input.simpleOccurrencePath_provenance
            (SimpleOccurrencePath.step path currentObserved adjacent notParent fresh),
          (duplicateRootDistance_extend_self input fresh).symm, List.prefix_refl _⟩
      · obtain ⟨prefixNode, prefixAddress, prefixPath, prefixCurrent, prefixReal, prefixDepth,
          prefixHistory⟩ := ih parentPresent
        refine ⟨prefixNode, prefixAddress, prefixPath, prefixCurrent, prefixReal, ?_, ?_⟩
        · rw [prefixDepth, duplicateRootDistance_extend_of_mem input parentPresent]
        · rw [OfficialCIPNode.extend_history, List.reverse_cons]
          exact prefixHistory.trans (List.prefix_append node.history.reverse [next])

/-- Equal outer root and path are one carrier occurrence.  The same atom reached by another
ring path has a different path, hence a different occurrence. -/
theorem sameOuterPath_sameOccurrence
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (left right : input.LocalizedCIPOccurrence fuel)
    (unitEq : input.molecularFrameUnit left.1 = input.molecularFrameUnit right.1) :
    left = right :=
  input.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded left right unitEq

private theorem armLabel_eq_carrier
    {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (node : (ruleMajorTreeGraph tree).Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree node.1 = some actual) :
    (ruleMajorTreeGraph tree).label node =
      actual.source.occurrence.1.node.toDeclarativeLabel := by
  have erased : (toOfficialSourceTree tree).subtreeAt? node.1 =
      some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq node.1 tree, lookup]
    rfl
  change (toOfficialSourceTree tree).declarativeLabel node = _
  rw [(toOfficialSourceTree tree).declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree actual) node erased, toOfficialSourceTree_source]

/-- A real node of a realized arm reads the official depth of its carrier occurrence.
That depth is the length of the occurrence path from the original outer root. -/
theorem retainedRealNode_eq_outerDigraphSphere
    (singleBonded : input.moleculeGraph.SimpleBonded) {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some actual)
    (real : actual.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    retainedContextRuleValue input.moleculeGraph (ruleMajorTreeGraph tree) unit
        .rule1bDuplicateNodeProximity node =
      actual.source.occurrence.1.node.depth ∧
    (input.molecularFrameUnit actual.source.occurrence.1).root = unit.1.root ∧
    (input.molecularFrameUnit actual.source.occurrence.1).path.length =
      actual.source.occurrence.1.node.depth := by
  obtain ⟨steps, stepsEq, rootEq, pathEq⟩ :=
    input.retainedCursorFrame_eq_ancestorWalk singleBonded target tree realizes rootChild
      node actual lookup
  have targetRoot : (input.molecularFrameUnit target.occurrence.1).root = unit.1.root :=
    congrArg OccurrenceUnit.root targetUnit
  have targetPath : (input.molecularFrameUnit target.occurrence.1).path = unit.1.path :=
    congrArg OccurrenceUnit.path targetUnit
  have walkEq : (input.molecularFrameUnit actual.source.occurrence.1).path =
      rerootWalk unit.1.root unit.1.path steps := by
    rw [pathEq, targetRoot, targetPath]
  obtain ⟨atom, current⟩ := input.localizedRerootCursor_current_exists actual.source
  have label : (ruleMajorTreeGraph tree).label node = ⟨some atom, .realAtom⟩ := by
    rw [armLabel_eq_carrier input node lookup, OfficialCIPNode.toDeclarativeLabel, current, real]
    rfl
  have pathLength := input.retainedFramePathLength_eq_officialDepth singleBonded
    actual.source.occurrence
  rw [walkEq] at pathLength
  refine ⟨?_, rootEq.trans targetRoot, ?_⟩
  · rw [retainedContextRuleValue_rule1b_real input.moleculeGraph (ruleMajorTreeGraph tree) unit
      label stepsEq]
    exact pathLength
  · rw [walkEq]
    exact pathLength

/-- A ring-duplicate arm node reads the depth of the earlier real visit of its atom on this
history.  The visit is a `SimpleOccurrencePath` prefix, identified by root and history rather
than by the atom alone. -/
theorem retainedRingNode_eq_representedRealSphere
    (singleBonded : input.moleculeGraph.SimpleBonded) {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some actual)
    (ring : ∃ distance, actual.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    ∃ distance atom prefixNode prefixAddress,
      actual.source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance ∧
        retainedContextRuleValue input.moleculeGraph (ruleMajorTreeGraph tree) unit
            .rule1bDuplicateNodeProximity node = distance ∧
        SimpleOccurrencePath input actual.source.occurrence.1.root prefixNode prefixAddress ∧
        prefixNode.current? = some atom ∧
        prefixNode.provenance = OfficialCIPNodeProvenance.realAtom ∧
        prefixNode.depth = distance ∧
        actual.source.occurrence.1.node.current? = some atom ∧
        prefixNode.history.reverse <+:
          actual.source.occurrence.1.node.history.tail.reverse ∧
        actual.source.occurrence.1.root = unit.1.root := by
  obtain ⟨_steps, _stepsEq, rootEq, _pathEq⟩ :=
    input.retainedCursorFrame_eq_ancestorWalk singleBonded target tree realizes rootChild
      node actual lookup
  have outerRoot : actual.source.occurrence.1.root = unit.1.root :=
    rootEq.trans (congrArg OccurrenceUnit.root targetUnit)
  rcases ring with ⟨distance, ringProvenance⟩
  have legit := input.carrierOccurrence_legitimate singleBonded actual.source.occurrence
  revert ringProvenance legit
  generalize hnode : actual.source.occurrence.1.node = occNode
  generalize haddress : actual.source.occurrence.1.address = occAddress
  intro ringProvenance legit
  cases legit with
  | simple path =>
      clear haddress
      have realProvenance := input.simpleOccurrencePath_provenance path
      rw [realProvenance] at ringProvenance
      cases ringProvenance
  | @ring parent _address current next path _observed _adjacent _notParent visited =>
      clear haddress
      have provenanceEq := input.legitimateOccurrence_ring_provenance visited
      have distanceEq : parent.duplicateRootDistance next = distance := by
        apply OfficialCIPNodeProvenance.ringDuplicate.inj
        rw [← provenanceEq, ringProvenance]
      obtain ⟨prefixNode, prefixAddress, prefixPath, prefixCurrent, prefixReal, prefixDepth,
          prefixHistory⟩ := simpleOccurrence_representedPrefix input path visited
      have label : (ruleMajorTreeGraph tree).label node =
          ⟨some next, .ringDuplicate distance⟩ := by
        rw [armLabel_eq_carrier input node lookup, hnode, OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNode.extend_current?, OfficialCIPNode.extend_provenance,
          OfficialCIPNode.childProvenance_ring_duplicate parent next visited, distanceEq]
        rfl
      have valueEq := retainedContextRuleValue_rule1b_ring input.moleculeGraph
        (ruleMajorTreeGraph tree) unit label
      have historyPrefix : prefixNode.history.reverse <+:
          (parent.extend next 0).history.tail.reverse := by
        rw [OfficialCIPNode.extend_history]
        simpa using prefixHistory
      refine ⟨distance, next, prefixNode, prefixAddress, ringProvenance, valueEq, prefixPath,
        prefixCurrent, prefixReal, ?_, by simp [OfficialCIPNode.extend_current?], historyPrefix,
        outerRoot⟩
      rw [prefixDepth, distanceEq]
  | @multiple _parent _address current next copyIndex _path _observed adjacent bound positive =>
      clear haddress
      have oneBond := singleBonded current next adjacent
      have copyLt : copyIndex < 1 := by simpa [oneBond] using bound
      omega

assert_kernel_only simpleOccurrence_representedPrefix
assert_kernel_only sameOuterPath_sameOccurrence
assert_kernel_only retainedRealNode_eq_outerDigraphSphere
assert_kernel_only retainedRingNode_eq_representedRealSphere

end TetraStereo.OneCenter.RetainedDigraphSphereCorrespondence
