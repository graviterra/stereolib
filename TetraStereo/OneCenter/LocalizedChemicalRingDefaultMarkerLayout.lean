import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing
import TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource
import TetraStereo.OneCenter.LocalizedActualBoundaryPathRealization
import TetraStereo.OneCenter.DeclarativeCIPDepthChains
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The default marker layout covers actual source arms

The relevant width is the number of children at each parent, not the conservative
`RootedDigraph.width`, which counts all hierarchy nodes. Simple bonding bounds each
executable child list by `atomCount + 1`; actual recursion traces bound hierarchy height
by their successful fuel. These bounds concern the existing runtime layout and do not
change the marker builder.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingReaddressedSource LocalizedMarkedRetainedMolecularSelection

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- A simple-bond source node has at most one executable child for each current atom.
The option-valued readback gives the convenient runtime bound `atomCount + 1`. -/
theorem executable_children_length_le (single : input.moleculeGraph.SimpleBonded)
    (node : OfficialCIPNode input.Atom) :
    (input.executableOfficialCIPChildren node).length ≤ retainedCarrierFuel input := by
  have distinct : ((input.executableOfficialCIPChildren node).map OfficialCIPNode.current?).Nodup := by
    apply List.Nodup.map_on _ (executableOfficialCIPChildren_nodup input single node)
    intro left leftMem right rightMem same
    obtain ⟨a, rfl⟩ := exists_extend_zero_of_mem input single leftMem
    obtain ⟨b, rfl⟩ := exists_extend_zero_of_mem input single rightMem
    have atoms : a = b := by simpa only [OfficialCIPNode.extend_current?, Option.some.injEq] using same
    rw [atoms]
  simpa [retainedCarrierFuel] using distinct.length_le_card

/-- Every parent in an actually generated source tree obeys the runtime branching bound. -/
theorem source_branching_le (single : input.moleculeGraph.SimpleBonded)
    (tree : OfficialCIPSourceTree input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (node : tree.toDeclarativeDigraph.Node) :
    (tree.toDeclarativeDigraph.childList node).length ≤ retainedCarrierFuel input := by
  have lengths := (local_enumerator_law tree input.executableOfficialCIPChildren generated node).length_eq
  simp only [List.length_map] at lengths
  rw [lengths]
  exact executable_children_length_le single _

/-- Every actual successful recursive trace has no occupied address beyond its fuel. -/
theorem trace_address_length_le
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key)
    (path : List Nat) (subtree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : tree.decoratedSubtreeAt? path = some subtree) : path.length ≤ fuel := by
  induction fuel generalizing tree key path with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
          cases path with
          | nil => simp
          | cons slot rest =>
              rw [decoratedSubtreeAt?] at lookup
              simp [localizedRootTree] at lookup
  | succ fuel ih =>
      cases path with
      | nil => simp
      | cons slot rest =>
          cases trace with
          | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
              rw [decoratedSubtreeAt?] at lookup
              simp [localizedRootTree] at lookup
          | node _fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
              childKeysComputed sortedEq constitutionalDescending _sortedDescending fullMatch realizes childrenTraced =>
              have childrenEq : (localizedRootTree input cursor (read cursor) sortedTrees).children =
                  sortedTrees := by unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              cases found : sortedTrees[slot]? with
              | none => simp [childrenEq, found] at lookup
              | some child =>
                  simp [childrenEq, found] at lookup
                  have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
                  have inTrees : slot < sortedTrees.length := (List.getElem?_eq_some_iff.mp found).1
                  have lengths := List.Forall₂.length_eq paired
                  have inKeys : slot < sortedKeys.length := by omega
                  have childTrace : LocalizedRuleMajorSortTrace input stage read fuel
                      (sortedTrees[slot]'inTrees) (sortedKeys[slot]'inKeys) :=
                    List.Forall₂.get (i := slot) paired inKeys inTrees
                  have childEq : sortedTrees[slot]'inTrees = child :=
                    Option.some.inj ((List.getElem?_eq_getElem inTrees).symm.trans found)
                  have childLookup : (sortedTrees[slot]'inTrees).decoratedSubtreeAt? rest =
                      some subtree := by simpa only [childEq] using lookup
                  have bounded := ih childTrace rest childLookup
                  simpa only [List.length_cons] using Nat.succ_le_succ bounded

/-- The hierarchy height is bounded by the actual recursive build fuel, at every stage and reader. -/
theorem trace_height_le
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    (ruleMajorTreeGraph tree).height ≤ fuel := by
  apply Finset.sup_le
  intro node _
  obtain ⟨subtree, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree node
  exact trace_address_length_le trace node.1 subtree lookup

section ActualRoot

open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedCanonicalFrame
open LocalizedChemicalRingActualReferenceFixing

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

/-- Both dimensions of the unchanged default marker layout cover every actual root slot tree.
The width assertion is the true branching bound, not a bound on total hierarchy cardinality. -/
theorem actual_root_slot_bounds (rootAddress : target.1.address = []) (slot : Fin 4) :
    (∀ node, ((ruleMajorTreeGraph
      (slotTree input single state target real unit targetUnit slot)).childList node).length ≤
        retainedCarrierFuel input) ∧
    (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit slot)).height ≤
      2 * (retainedCarrierFuel input + 1) := by
  let frame := frames input single state target real unit targetUnit
  obtain ⟨atom, current⟩ := input.localizedRerootCursor_current_exists (frame.frame.cursorAt slot)
  have rooted := (root_slot_boundary single (rawStateDescriptorMap input state) target frame
    rootAddress slot atom current).1
  exact ⟨source_branching_le single _ rooted.generated, trace_height_le (frame.stages slot).a.trace⟩

/-- At the exact `marked?` runtime layout, an actual promoted-key tie constructs one molecular
automorphism fixing the center and reference and sending the left slot atom to the right.
All layout coverage is proved internally; no replacement runtime layout is used. -/
theorem actual_root_default_tie_reference_fixed_aut (rootAddress : target.1.address = [])
    (reference : input.Atom) (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
      refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right)
    (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧ π reference = reference := by
  obtain ⟨widthL, heightL⟩ := actual_root_slot_bounds input single state target real unit targetUnit
    rootAddress left
  obtain ⟨widthR, heightR⟩ := actual_root_slot_bounds input single state target real unit targetUnit
    rootAddress right
  let fallback := (frames input single state target real unit targetUnit).retainedKeys unit left
  exact actual_root_tie_reference_fixed_aut input single state target real unit targetUnit
    reference (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) fallback
    rootAddress left right widthL heightL widthR heightR tie a b currentL currentR charge

end ActualRoot

end
end TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout.executable_children_length_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout.source_branching_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout.trace_address_length_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout.trace_height_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout.actual_root_slot_bounds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout.actual_root_default_tie_reference_fixed_aut
