import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedRuleMajorDependencyLocality
import TetraStereo.OneCenter.LocalizedPhysicalBranchKeyTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Deep sibling comparisons as frame comparisons at the actual parent

The promoted builder compares sibling cursors at every depth by their full ordinary compound
keys, always under the ORIGINAL target's dependency view. This module relates such a deep
comparison to the accepted frame-level theorem at the siblings' own actual parent cursor.

* `shape_of_reach`: a cursor reached from the target cursor `⟨t, none⟩` either arrived from a
  strictly shorter carrier coordinate, or is no deeper than `t`. After one outward step a reroot
  walk never turns inward again.
* `reader_eq_virtual`: below any reached parent `p`, the original reader equals the reader of `p`
  for the descriptor map cut at the original target's depth (`cutMap`). Every original
  dependency is also a dependency of `p` there, and the cut removes exactly the shallower reads.
* `ordinary_eq_virtual`: hence the actual compound key built under the original view equals the
  actual compound key built under the parent's view, at every fuel.
* `virtual_sibling_compare`: at every reached parent, the accepted
  `retainedMolecularCompound_throughRule5` applied in the parent's own occurrence context identifies
  the deep sibling comparison with the comparison of independent retained complete keys. The
  original target, its cutoff and the arbitrary tetrahedral map remain explicit.

The retained readback layer takes an arbitrary occurrence context (`OccurrenceUnit`), so the
parent need not be a detected centre; a three-coordinate branching nitrogen is covered. No
comparison result, label or sort outcome is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedMolecularRule5

noncomputable section

variable {input : CertifiedLocalizedCIPInput} {fuel : Nat}

/-! ## The descriptor map cut at a depth -/

/-- Descriptors are read only at occurrences strictly deeper than `bound`. -/
def cutMap (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) (bound : Nat) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  fun unit => if bound < unit.1.path.length then descriptorMap unit else none

theorem cutMap_tetrahedral (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (bound : Nat) :
    ∀ unit value, cutMap descriptorMap bound unit = some value → value.IsTetrahedral := by
  intro unit value observed
  unfold cutMap at observed
  split at observed
  · exact tetrahedralMap unit value observed
  · cases observed

/-! ## Reroot shape -/

/-- Reached from a strictly shorter carrier coordinate, with a valid cursor. -/
def Outward (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid cursor ∧
    ∃ previous : input.LocalizedCIPOccurrence fuel, cursor.previous? = some previous ∧
      previous.1.address.length < cursor.occurrence.1.address.length

/-- One executable edge: same root, incoming coordinate recorded, carrier adjacency. -/
theorem edge_facts (cursor child : input.LocalizedRerootCursor fuel) (edge : E input cursor child) :
    child.previous? = some cursor.occurrence ∧ input.LocalizedRerootCursorValid child ∧
      input.LocalizedCarrierTreeAdjacent child.occurrence.1 cursor.occurrence.1 := by
  have derived := input.executableLocalizedRerootChildren_declarative cursor
  have intended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, edge, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended cursor
    child.occurrence.1 intended
  exact ⟨derived.2 child edge,
    input.localizedRerootChild_valid cursor child _ derived edge,
    ((input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1 child.occurrence.1).mp
      neighbor).2⟩

theorem outward_child {cursor child : input.LocalizedRerootCursor fuel} (outward : Outward cursor)
    (edge : E input cursor child) :
    Outward child ∧ child.occurrence.1.address.length = cursor.occurrence.1.address.length + 1 ∧
      child.occurrence.1.root = cursor.occurrence.1.root := by
  obtain ⟨valid, previous, previousEq, shorter⟩ := outward
  obtain ⟨_, lengthEq, rootEq, childPrevious, childValid⟩ :=
    outward_edge input cursor child valid previous previousEq shorter edge
  exact ⟨⟨childValid, cursor.occurrence, childPrevious, by omega⟩, lengthEq, rootEq⟩

theorem outward_reach {start cursor : input.LocalizedRerootCursor fuel} (outward : Outward start)
    (reach : Relation.ReflTransGen (E input) start cursor) :
    Outward cursor ∧ start.occurrence.1.address.length ≤ cursor.occurrence.1.address.length ∧
      cursor.occurrence.1.root = start.occurrence.1.root := by
  induction reach with
  | refl => exact ⟨outward, le_rfl, rfl⟩
  | tail _ edge ih =>
      obtain ⟨out, le, root⟩ := ih
      obtain ⟨out', len', root'⟩ := outward_child out edge
      exact ⟨out', by omega, root'.trans root⟩

/-- Shape relative to the target occurrence `t`. -/
def Shape (t : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel) :
    Prop :=
  cursor.occurrence.1.root = t.1.root ∧
    (Outward cursor ∨ cursor.occurrence.1.address.length ≤ t.1.address.length)

theorem shape_step (t : input.LocalizedCIPOccurrence fuel)
    {cursor child : input.LocalizedRerootCursor fuel} (shape : Shape t cursor)
    (edge : E input cursor child) : Shape t child := by
  obtain ⟨root, outward | shallow⟩ := shape
  · obtain ⟨out, _, root'⟩ := outward_child outward edge
    exact ⟨root'.trans root, Or.inl out⟩
  · obtain ⟨previous, valid, adjacent⟩ := edge_facts cursor child edge
    obtain ⟨sameRoot, asParent | asOutward⟩ := adjacent
    · exact ⟨sameRoot.trans root, Or.inr (by omega)⟩
    · exact ⟨sameRoot.trans root,
        Or.inl ⟨valid, cursor.occurrence, previous, by omega⟩⟩

/-- **Reroot shape.** Every cursor reached from the target cursor is outward or not deeper. -/
theorem shape_of_reach (t : input.LocalizedCIPOccurrence fuel)
    {cursor : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ cursor) : Shape t cursor := by
  induction reach with
  | refl => exact ⟨rfl, Or.inr le_rfl⟩
  | tail _ edge ih => exact shape_step t ih edge

/-- Below a reached parent, an original dependency is a dependency of that parent. -/
theorem deeper_of_reach (t : input.LocalizedCIPOccurrence fuel)
    {parent child cursor : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ parent)
    (edge : E input parent child) (below : Relation.ReflTransGen (E input) child cursor)
    (deeper : t.1.address.length < cursor.occurrence.1.address.length) :
    parent.occurrence.1.address.length < cursor.occurrence.1.address.length := by
  obtain ⟨_, outward | shallow⟩ := shape_of_reach t reach
  · obtain ⟨childOut, childLength, _⟩ := outward_child outward edge
    obtain ⟨_, le, _⟩ := outward_reach childOut below
    omega
  · omega

theorem reach_root (t : input.LocalizedCIPOccurrence fuel) {cursor : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ cursor) :
    cursor.occurrence.1.root = t.1.root := (shape_of_reach t reach).1

/-! ## Reader agreement -/

theorem frameUnit_path_length (occurrence : input.LocalizedCIPOccurrence fuel) :
    (input.molecularFrameUnit occurrence.1).path.length = occurrence.1.address.length := by
  have history := input.carrierOccurrence_history_length_eq_address_length occurrence
  simp only [molecularFrameUnit, List.length_tail, List.length_reverse]
  omega

/-- The reader of the parent occurrence for the descriptor map cut at the target's depth. -/
def virtualReader (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (t : input.LocalizedCIPOccurrence fuel) (parent : input.LocalizedRerootCursor fuel) :
    input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel :=
  input.localizedDependencyLabel parent.occurrence
    (input.molecularView (cutMap descriptorMap t.1.address.length) parent.occurrence)

/-- **The original reader is the virtual parent reader on everything the sibling reads.** -/
theorem reader_eq_virtual (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (t : input.LocalizedCIPOccurrence fuel)
    {parent child cursor : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ parent)
    (edge : E input parent child) (below : Relation.ReflTransGen (E input) child cursor) :
    input.localizedDependencyLabel t (input.molecularView descriptorMap t) cursor =
      virtualReader descriptorMap t parent cursor := by
  have cursorReach : Relation.ReflTransGen (E input) ⟨t, none⟩ cursor :=
    (reach.tail edge).trans below
  have cursorRoot := reach_root t cursorReach
  have parentRoot := reach_root t reach
  have pathLength := frameUnit_path_length cursor.occurrence
  unfold virtualReader localizedDependencyLabel
  by_cases original : input.LocalizedDepthDependency cursor.occurrence t
  · have deeper := deeper_of_reach t reach edge below original.2
    have virtual : input.LocalizedDepthDependency cursor.occurrence parent.occurrence :=
      ⟨cursorRoot.trans parentRoot.symm, deeper⟩
    rw [dif_pos original, dif_pos virtual]
    unfold molecularView
    split
    · split
      · rename_i detected
        simp only [cutMap, pathLength, if_pos original.2]
      · rfl
    · rfl
  · rw [dif_neg original]
    split
    · unfold molecularView
      split
      · split
        · have shallow : ¬ t.1.address.length < cursor.occurrence.1.address.length :=
            fun deeper => original ⟨cursorRoot, deeper⟩
          simp [cutMap, pathLength, shallow]
        · rfl
      · rfl
    · rfl

/-- **Actual compound congruence.** The deep compound key built under the original view is the
compound key built under the virtual parent view, at every fuel. -/
theorem ordinary_eq_virtual (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (t : input.LocalizedCIPOccurrence fuel)
    {parent child : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ parent)
    (edge : E input parent child) (budget : Nat) :
    input.buildActualRuleMajorCompoundRule45KeyExec? t (input.molecularView descriptorMap t)
        budget child =
      input.buildActualRuleMajorCompoundRule45KeyExec? parent.occurrence
        (input.molecularView (cutMap descriptorMap t.1.address.length) parent.occurrence)
        budget child := by
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
  apply input.buildRuleMajorCompoundRule45KeyWith?_eq
  intro stage
  exact input.buildRuleMajorCumulativeWithRead?_eq_of_reachable stage _ _ child
    (fun cursor below => reader_eq_virtual descriptorMap t reach edge below) budget child
    Relation.ReflTransGen.refl

/-! ## Deep comparisons at a detected parent -/

variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (singleBonded : input.moleculeGraph.SimpleBonded)

/-- The parent's own occurrence context. It need not be a detected centre: the context readings
use only its root and path. -/
def parentUnit (parent : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    OccurrenceUnit input.Atom :=
  input.molecularFrameUnit parent.occurrence.1

include tetrahedralMap singleBonded in
/-- **Deep sibling comparison at every reached parent.** Two actual siblings of any reached parent
cursor compare, under the original target view, exactly as the independent retained complete
Rule-5 keys of their actual stage graphs read in the parent's own occurrence context, with the
descriptor map cut at the original target's depth. The parent may be any atom, e.g. a
three-coordinate nitrogen. -/
theorem virtual_sibling_compare (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (parent cursorL cursorR : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ parent)
    (childL : cursorL ∈ input.executableLocalizedRerootChildren parent)
    (childR : cursorR ∈ input.executableLocalizedRerootChildren parent)
    (leftStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (virtualReader descriptorMap t parent) cursorL)
    (rightStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (virtualReader descriptorMap t parent) cursorR)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.LocalizedRerootCompoundRule45Key}
    (builtL : input.buildActualRuleMajorCompoundRule45KeyExec? t (input.molecularView descriptorMap t)
      (2 * (retainedCarrierFuel input + 1)) cursorL = some left)
    (builtR : input.buildActualRuleMajorCompoundRule45KeyExec? t (input.molecularView descriptorMap t)
      (2 * (retainedCarrierFuel input + 1)) cursorR = some right) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
      compare
        (retainedCompleteLigandRule5KeyAt input.moleculeGraph
          (cutMap descriptorMap t.1.address.length) (parentUnit parent)
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (retainedCompleteLigandRule5KeyAt input.moleculeGraph
          (cutMap descriptorMap t.1.address.length) (parentUnit parent)
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  rw [ordinary_eq_virtual descriptorMap t reach childL] at builtL
  rw [ordinary_eq_virtual descriptorMap t reach childR] at builtR
  exact (retainedMolecularCompound_throughRule5 (cutMap descriptorMap t.1.address.length)
    (cutMap_tetrahedral descriptorMap tetrahedralMap _) singleBonded parent
    (parentUnit parent) rfl cursorL cursorR childL childR leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth builtL builtR).1

end

end TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.cutMap_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.edge_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.outward_reach
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.shape_of_reach
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.deeper_of_reach
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.reader_eq_virtual
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.ordinary_eq_virtual
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget.virtual_sibling_compare
