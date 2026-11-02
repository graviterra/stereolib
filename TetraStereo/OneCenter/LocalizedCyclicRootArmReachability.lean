import TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
import TetraStereo.OneCenter.LocalizedActualOrderedRootEightRuleConnection
import TetraStereo.OneCenter.LocalizedRetainedDependencyLocality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! Every node of an actual cyclic root arm is reached within the physical root branch.
The canonical ligand cursor is used only to reuse the existing structural walk theorem;
no acyclicity or descriptor assumption enters. -/

namespace TetraStereo.OneCenter.LocalizedCyclicRootArmReachability

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open LocalizedCyclicMatchedReadingPhysicalTransport LocalizedCumulativeDecoratedTree
open RootedTetrahedralBranchSymmetry
open Rule4aTableBridge
noncomputable section

private theorem occurrenceUnit_ext {Atom : Type*} {a b : OccurrenceUnit Atom}
    (root : a.root = b.root) (path : a.path = b.path) : a = b := by
  cases a
  cases b
  simp_all

variable {input : LocalizedRuleMajorReference.Input}
  {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

theorem rootTarget_eq_atomRoot
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom) :
    target = input.certified.localizedAtomRootOccurrence (carrierFuel input) frames.center.1 := by
  obtain ⟨_, history, root⟩ := rootFrame_target_facts frames rootAddress real
  apply input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
  apply occurrenceUnit_ext
  · simpa [molecularFrameUnit] using root
  · simp [molecularFrameUnit, history, localizedAtomRootOccurrence_node,
      OfficialCIPNode.root]

theorem rootSlot_eq_canonicalLigandCursor
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom) (slot : Fin 4) :
    frames.frame.cursorAt slot =
      input.certified.localizedLigandRootCursor frames.center
        (input.certified.canonicalLigandReindex frames.center
          (frames.detectedLigandPermutation slot)) := by
  obtain ⟨_, root, history⟩ :=
    rootFrame_cursor_facts singleBonded frames rootAddress real slot
  apply LocalizedRerootCursor.ext
  · apply input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
    apply occurrenceUnit_ext
    · simpa [molecularFrameUnit] using root
    · simp [molecularFrameUnit, history, localizedLigandRootCursor_node,
        localizedLigandRootNode, OfficialCIPNode.extend, OfficialCIPNode.root,
        input.certified.canonicalLigandReindex_spec]
  · rw [frames.ligandCursor_previous singleBonded, localizedLigandRootCursor_previous]
    exact congrArg some (rootTarget_eq_atomRoot singleBonded frames rootAddress real)

theorem arm_subtree_source_reachable
    (frames : ContextFrameCompilation input target unit targetUnit)
    (slot : Fin 4) {stage : LocalizedCumulativeRule45Stage}
    (arm : input.certified.RuleMajorContextArm (carrierFuel input) stage
      (contextOccurrenceRead input target) (frames.frame.cursorAt slot))
    {address : List Nat} {node : LocalizedCumulativeDecoratedTree input.certified (carrierFuel input)}
    (lookup : arm.tree.decoratedSubtreeAt? address = some node) :
    Relation.ReflTransGen (E input.certified) (frames.frame.cursorAt slot) node.source := by
  rw [← arm.sourceEq]
  apply subtreeAt?_source_reachable (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace)
  rwa [← decoratedSubtreeAt?_eq_subtreeAt?]

/-- Root membership, positive depth and root identity of every actual arm node. -/
theorem arm_subtree_branch_facts
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    (slot : Fin 4) {stage : LocalizedCumulativeRule45Stage}
    (arm : input.certified.RuleMajorContextArm (carrierFuel input) stage
      (contextOccurrenceRead input target) (frames.frame.cursorAt slot))
    {address : List Nat} {node : LocalizedCumulativeDecoratedTree input.certified (carrierFuel input)}
    (lookup : arm.tree.decoratedSubtreeAt? address = some node) :
    input.certified.RootBranchContains (frames.frame.cursorAt slot).occurrence
        node.source.occurrence ∧
      node.source.occurrence.1.address ≠ [] ∧
      frames.center.1 = node.source.occurrence.1.root ∧
      input.certified.LocalizedDepthDependency node.source.occurrence target := by
  have reachable := arm_subtree_source_reachable frames slot arm lookup
  have addressEq := (rootFramePair frames rootAddress slot slot).leftAddress
  change (frames.frame.cursorAt slot).occurrence.1.address =
    target.1.address ++ [(rootFramePair frames rootAddress slot slot).leftSlot] at addressEq
  have deeper : target.1.address.length < (frames.frame.cursorAt slot).occurrence.1.address.length := by
    simp only [addressEq, List.length_append, List.length_singleton]
    omega
  have firstOut := input.certified.outward_first_cursor target
    (frames.frame.cursorAt slot) (frames.childAt slot) deeper
  have allOut := input.certified.outward_reachable_cursor target
    (frames.frame.cursorAt slot) node.source firstOut reachable
  have addrPrefix := input.certified.address_isPrefix_of_outward_reachable target
    (frames.frame.cursorAt slot) node.source firstOut reachable
  have rootEq := (rootFrame_target_facts frames rootAddress real).2.2
  refine ⟨⟨firstOut.2.1.1.trans allOut.2.1.1.symm, addrPrefix⟩, ?_,
    rootEq.symm.trans allOut.2.1.1.symm, allOut.2.1⟩
  intro empty
  have positive := allOut.2.1.2
  simp [empty, rootAddress] at positive

/-- The current atom of a real arm node lies in the independently defined physical
deleted-root branch, including when branches overlap through a ring. -/
theorem arm_subtree_ligandBranchReaches
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    (slot : Fin 4) {stage : LocalizedCumulativeRule45Stage}
    (arm : input.certified.RuleMajorContextArm (carrierFuel input) stage
      (contextOccurrenceRead input target) (frames.frame.cursorAt slot))
    {address : List Nat} {node : LocalizedCumulativeDecoratedTree input.certified (carrierFuel input)}
    (lookup : arm.tree.decoratedSubtreeAt? address = some node)
    (nodeReal : node.source.occurrence.1.node.provenance = .realAtom)
    (atom : input.certified.Atom) (current : node.source.occurrence.1.node.current? = some atom) :
    LigandBranchReaches input.certified.detectedMultiCenterMolecule frames.center
      (frames.detectedLigandPermutation slot) atom := by
  have reachable := arm_subtree_source_reachable frames slot arm lookup
  rw [rootSlot_eq_canonicalLigandCursor singleBonded frames rootAddress real slot] at reachable
  obtain ⟨seen, seenCurrent, reached⟩ :=
    input.certified.ligandArm_realAtom_mem_ligandBranchReaches frames.center
      (input.certified.canonicalLigandReindex frames.center
        (frames.detectedLigandPermutation slot)) node.source reachable nodeReal
  have seenEq : seen = atom := Option.some.inj (seenCurrent.symm.trans current)
  subst seen
  unfold LigandBranchReaches
  rw [input.certified.canonicalLigandReindex_spec]
  exact reached

/-- A physical root-fixing symmetry fixes the actual stored root occurrence. -/
theorem rootOccurrence_fixed
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    (e : input.certified.moleculeGraph.Aut)
    {cfg : input.certified.detectedMultiCenterMolecule.Configuration} {i j : Fin 4}
    {mirror : Bool}
    (transport : input.certified.DetectedBranchTransport e cfg frames.center i j mirror) :
    input.certified.transportOccurrence singleBonded e target = target := by
  obtain ⟨_, history, root⟩ := rootFrame_target_facts frames rootAddress real
  have rootFixed := congrArg Subtype.val transport.rootFixed
  change (e : Equiv.Perm input.certified.Atom) frames.center.1 = frames.center.1 at rootFixed
  apply input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
  rw [input.certified.molecularFrameUnit_transport]
  simp [transportOccurrenceUnit, molecularFrameUnit, history, root, rootFixed]

/-- The actual source slot is carried to the actual image slot. The two slot indices
are interpreted through the compiled detected-ligand permutation. -/
theorem rootSlot_transport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    (e : input.certified.moleculeGraph.Aut)
    {cfg : input.certified.detectedMultiCenterMolecule.Configuration} {i j : Fin 4}
    {mirror : Bool}
    (transport : input.certified.DetectedBranchTransport e cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) mirror) :
    input.certified.transportCursor singleBonded e (frames.frame.cursorAt i) =
      frames.frame.cursorAt j := by
  have rootFixed := congrArg Subtype.val transport.rootFixed
  change (e : Equiv.Perm input.certified.Atom) frames.center.1 = frames.center.1 at rootFixed
  have ligandSent := input.certified.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt
    (input.certified.physicalDetectedAut e) frames.center (frames.detectedLigandPermutation i)
  rw [transport.rootFixed, transport.ligandSent] at ligandSent
  change input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation j) =
    (e : Equiv.Perm input.certified.Atom)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation i)) at ligandSent
  obtain ⟨_, rootI, historyI⟩ := rootFrame_cursor_facts singleBonded frames rootAddress real i
  obtain ⟨_, rootJ, historyJ⟩ := rootFrame_cursor_facts singleBonded frames rootAddress real j
  apply LocalizedRerootCursor.ext
  · apply input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
    rw [input.certified.transportCursor_occurrence, input.certified.molecularFrameUnit_transport]
    simp [transportOccurrenceUnit, molecularFrameUnit, historyI, historyJ, rootI, rootJ,
      rootFixed, ← ligandSent]
  · rw [input.certified.transportCursor_previous?, frames.ligandCursor_previous singleBonded,
      frames.ligandCursor_previous singleBonded, Option.map_some]
    exact congrArg some (rootOccurrence_fixed singleBonded frames rootAddress real e transport)

end
end TetraStereo.OneCenter.LocalizedCyclicRootArmReachability

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.rootTarget_eq_atomRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.arm_subtree_source_reachable
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.arm_subtree_branch_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.arm_subtree_ligandBranchReaches
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.rootOccurrence_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootArmReachability.rootSlot_transport
