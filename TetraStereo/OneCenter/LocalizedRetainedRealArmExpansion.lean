/-
COORDINATION: Owner of the global actual-arm isomorphism. Do not edit
`LocalizedRetainedArmExpansion` or `LocalizedRetainedCursorCutCover`.
`previous?` stays `some` of the actual target. The cut focus is
`occurrenceCarrierNode` of the cursor and the incoming node is
`occurrenceCarrierNode` of the target.
-/
import TetraStereo.OneCenter.LocalizedRetainedCursorCutCover
import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Actual rule-major arms and the predecessor cut

The rule-major tree of an actual executable child is the predecessor cut of that
child's carrier node. The cut's incoming node is the target's carrier node, the
same outer root is kept, and `cursor.previous?` remains `some target.occurrence`.
An inward address parent and an outward address child are both reroot-children of
the focus; neither is replaced by `focus.dropLast`. A ring-duplicate child is the
one-node cut. Nodes inside a real arm may themselves be ring duplicates.

`atomCount ≤ fuel` supplies the occurrences used by the local child law. Standard
carrier fuel is `atomCount + 1`, so that bound holds there. A shorter fuel is not
claimed to realize every carrier node. No acyclicity hypothesis and no supplied
graph isomorphism are used. The isomorphism is `LocalChildCovering.toIso.symm`:
the cut is the source and `ruleMajorTreeGraph` is the target.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutArmTraversal
open DeclarativeCIP.RootedDigraph
open MolecularEvidenceTree
open LocalizedCumulativeDecoratedTree
open LocalizedRetainedCursorCutCover
open TetraStereo.OneCenter.Rule4aTableBridge

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

private abbrev focusCut {root : input.Atom} {path : List input.Atom}
    (hpath : SimpleFrom input.moleculeGraph root path)
    (inc : Nodes input.moleculeGraph root)
    (hanchor : RealCutAnchor path hpath (some inc)) :=
  realCutRetainedArm input.moleculeGraph root hpath (some inc) hanchor

private theorem ne_real_focus_of_armChild {root : input.Atom} {path : List input.Atom}
    {parent step : Nodes input.moleculeGraph root}
    (hchild : armChild path parent step) : step.1 ≠ .real path := by
  intro heq
  have hraw : rawNewParent path step.1 = some parent.1 := hchild
  rw [heq, rawNewParent_focus] at hraw
  cases hraw

private theorem cutNode_ext {root : input.Atom} {path : List input.Atom}
    (hpath : SimpleFrom input.moleculeGraph root path)
    (inc : Nodes input.moleculeGraph root)
    (hanchor : RealCutAnchor path hpath (some inc))
    {left right : (input.focusCut hpath inc hanchor).Node}
    (same : left.1.1 = right.1.1) : left = right :=
  Subtype.ext (Subtype.ext same)

private theorem valid_cast {root₁ root₂ : input.Atom} {node : CarrierNode input.Atom}
    (h : root₁ = root₂)
    (valid : CarrierNode.Valid input.moleculeGraph root₁ node) :
    CarrierNode.Valid input.moleculeGraph root₂ node := by
  subst h
  exact valid

private theorem provenance_real_of_executable_child
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    {parent child : input.LocalizedRerootCursor fuel}
    (childMem : child ∈ input.executableLocalizedRerootChildren parent) :
    parent.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded parent.occurrence with
    real | ⟨_distance, ring⟩
  · exact real
  · have nil := ringCursor_executableChildren_eq_nil input parent ring
    rw [nil] at childMem
    cases childMem

private theorem source_nodup_of_realizes {fuel : Nat}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    (tree.children.map (fun child => child.source)).Nodup := by
  obtain ⟨perm, _computed⟩ := exists_sourcePerm_executable realizes
  have execNodup : (input.executableLocalizedRerootChildren tree.source).Nodup := by
    apply List.Nodup.of_map (fun child => child.occurrence.1)
    rw [input.executableLocalizedRerootChildren_map tree.source]
    exact input.intendedLocalizedRerootChildFrames_nodup tree.source
  exact (perm.nodup_iff).mpr execNodup

private theorem hierarchyAddress_of_decorated_lookup {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel) (address : List Nat)
    (child : LocalizedCumulativeDecoratedTree input fuel)
    (lookup : subtreeAt? tree address = some child) :
    address ∈ (toOfficialSourceTree tree).hierarchyAddresses := by
  have hoff : (toOfficialSourceTree tree).subtreeAt? address =
      some (toOfficialSourceTree child) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, lookup]
    rfl
  have occ := OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some address
    (toOfficialSourceTree tree) (toOfficialSourceTree child) hoff
  exact OfficialCIPSourceTree.mem_hierarchyAddresses_of_occurrence
    (toOfficialSourceTree tree) (address, (toOfficialSourceTree child).source) occ

private theorem exists_decorated_subtree {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (node : (ruleMajorTreeGraph tree).Node) :
    ∃ sub : LocalizedCumulativeDecoratedTree input fuel,
      subtreeAt? tree node.1 = some sub ∧
        (toOfficialSourceTree tree).subtreeAt? node.1 = some (toOfficialSourceTree sub) := by
  obtain ⟨official, hlook⟩ :=
    (toOfficialSourceTree tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses node.1 node.2
  have hcomm := toOfficialSourceTree_subtreeAt?_eq node.1 tree
  have hmap : (subtreeAt? tree node.1).map toOfficialSourceTree = some official := by
    rw [← hcomm]
    exact hlook
  obtain ⟨sub, hsub, hoff⟩ := Option.map_eq_some_iff.mp hmap
  refine ⟨sub, hsub, ?_⟩
  rw [hlook, ← hoff]

private theorem child_slot_lookup {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    {parent child : (ruleMajorTreeGraph tree).Node} (slot : Nat)
    (addrEq : child.1 = parent.1 ++ [slot])
    {parentSub childSub : LocalizedCumulativeDecoratedTree input fuel}
    (parentLook : subtreeAt? tree parent.1 = some parentSub)
    (childLook : subtreeAt? tree child.1 = some childSub) :
    parentSub.children[slot]? = some childSub := by
  have happ := subtreeAt?_append_singleton parent.1 tree slot
  rw [← addrEq, childLook, parentLook] at happ
  exact happ.symm

/-- A realized subtree, reached from the arm root, is one kept cut node.
The root's excluded predecessor is the supplied incoming target. Every deeper
cursor's excluded predecessor is the source-tree parent, and its cut node is a
cut child of that parent. -/
private structure Placement (singleBonded : input.moleculeGraph.SimpleBonded)
    {root : input.Atom} {path : List input.Atom}
    (hpath : SimpleFrom input.moleculeGraph root path)
    (inc : Nodes input.moleculeGraph root)
    (hanchor : RealCutAnchor path hpath (some inc)) {fuel : Nat}
    (sub : LocalizedCumulativeDecoratedTree input fuel) where
  cutNode : (input.focusCut hpath inc hanchor).Node
  carrierEq : cutNode.1.1 = input.occurrenceCarrierNode singleBonded sub.source.occurrence
  rootEq : sub.source.occurrence.1.root = root
  prev : input.LocalizedCIPOccurrence fuel
  prevNode : Nodes input.moleculeGraph root
  prevEq : sub.source.previous? = some prev
  prevCarrier : prevNode.1 = input.occurrenceCarrierNode singleBonded prev
  prevNeighbor : sub.source.occurrence.1 ∈
    input.localizedRerootNeighborFrames (fuel := fuel) prev.1
  excluded : ExcludedPredecessor path (some inc) cutNode.1 prevNode

private theorem placed_of_lookup
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (rootCursor : input.LocalizedRerootCursor fuel)
    (focusRoot : input.Atom)
    (cursorRoot : rootCursor.occurrence.1.root = focusRoot)
    {path : List input.Atom}
    (hpath : SimpleFrom input.moleculeGraph focusRoot path)
    (inc : Nodes input.moleculeGraph focusRoot)
    (hanchor : RealCutAnchor path hpath (some inc))
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = rootCursor)
    (focusNode : input.occurrenceCarrierNode singleBonded rootCursor.occurrence = .real path)
    (targetOcc : input.LocalizedCIPOccurrence fuel)
    (previousEq : rootCursor.previous? = some targetOcc)
    (targetCarrier : inc.1 = input.occurrenceCarrierNode singleBonded targetOcc)
    (rootNeighbor : rootCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) targetOcc.1)
    (address : List Nat) {sub : LocalizedCumulativeDecoratedTree input fuel}
    (lookup : subtreeAt? tree address = some sub) :
    Nonempty (Placement input singleBonded hpath inc hanchor sub) := by
  suffices ∀ n (address : List Nat) (sub : LocalizedCumulativeDecoratedTree input fuel),
      address.length = n → subtreeAt? tree address = some sub →
        Nonempty (Placement input singleBonded hpath inc hanchor sub) by
    exact this address.length address sub rfl lookup
  intro n
  induction n with
  | zero =>
      intro address sub hlen lookup
      cases address with
      | cons _ _ =>
          simp at hlen
      | nil =>
          rw [subtreeAt?_nil] at lookup
          have subEq : sub = tree := (Option.some.inj lookup).symm
          subst subEq
          refine ⟨{
            cutNode := (input.focusCut hpath inc hanchor).root
            carrierEq := by
              rw [sourceEq]
              exact cutRoot_eq_focusCarrier input singleBonded hpath hanchor
                rootCursor.occurrence cursorRoot focusNode
            rootEq := by
              rw [sourceEq]
              exact cursorRoot
            prev := targetOcc
            prevNode := inc
            prevEq := by
              rw [sourceEq]
              exact previousEq
            prevCarrier := targetCarrier
            prevNeighbor := by
              rw [sourceEq]
              exact rootNeighbor
            excluded := Or.inl ⟨rfl, rfl⟩
          }⟩
  | succ n ih =>
      intro address sub hlen lookup
      have hne : address ≠ [] := by
        intro hempty
        simp [hempty] at hlen
      have parentLen : address.dropLast.length = n := by
        rw [List.length_dropLast, hlen]
        omega
      have split : address = address.dropLast ++ [address.getLast hne] :=
        (List.dropLast_append_getLast hne).symm
      have lookupSplit : subtreeAt? tree (address.dropLast ++ [address.getLast hne]) = some sub := by
        rw [← split]
        exact lookup
      rw [subtreeAt?_append_singleton] at lookupSplit
      obtain ⟨parentSub, parentLook, childLook⟩ := Option.bind_eq_some_iff.mp lookupSplit
      obtain ⟨parentPlacement⟩ := ih address.dropLast parentSub parentLen parentLook
      have parentRealizes := realizes_of_subtree realizes parentLook
      have childMem := mem_executable_of_child parentRealizes childLook
      have parentReal := input.provenance_real_of_executable_child singleBonded childMem
      have childPrev := input.executableLocalizedRerootChildren_previous
        parentSub.source sub.source childMem
      have frameMem : sub.source.occurrence.1 ∈
          input.intendedLocalizedRerootChildFrames parentSub.source := by
        rw [← input.executableLocalizedRerootChildren_map parentSub.source]
        exact List.mem_map.mpr ⟨sub.source, childMem, rfl⟩
      have childNeighbor : sub.source.occurrence.1 ∈
          input.localizedRerootNeighborFrames (fuel := fuel) parentSub.source.occurrence.1 :=
        input.mem_localizedRerootNeighborFrames_of_mem_intended parentSub.source
          sub.source.occurrence.1 frameMem
      have childRoot : sub.source.occurrence.1.root = parentSub.source.occurrence.1.root :=
        ((input.mem_localizedRerootNeighborFrames_iff parentSub.source.occurrence.1
          sub.source.occurrence.1).mp childNeighbor).2.1
      cases parentPlacement.rootEq
      have validChild := input.occurrenceCarrierNode_valid singleBonded sub.source.occurrence
      let step : Nodes input.moleculeGraph parentSub.source.occurrence.1.root :=
        ⟨input.occurrenceCarrierNode singleBonded sub.source.occurrence,
          valid_cast input childRoot validChild⟩
      obtain ⟨hstep, hedge⟩ :=
        (executableChild_iff_cutChild input singleBonded enough parentSub.source hpath hanchor
          parentReal parentPlacement.prev parentPlacement.prevEq parentPlacement.prevNeighbor
          parentPlacement.cutNode parentPlacement.carrierEq parentPlacement.prevNode
          parentPlacement.prevCarrier parentPlacement.excluded step).mp
          ⟨sub.source, childMem, rfl, childPrev⟩
      have hparent : armChild path parentPlacement.cutNode.1 step := hedge
      have hne := ne_real_focus_of_armChild input hparent
      exact ⟨{
        cutNode := ⟨step, hstep⟩
        carrierEq := rfl
        rootEq := childRoot
        prev := parentSub.source.occurrence
        prevNode := parentPlacement.cutNode.1
        prevEq := childPrev
        prevCarrier := parentPlacement.carrierEq
        prevNeighbor := childNeighbor
        excluded := Or.inr ⟨hne, hparent⟩
      }⟩

private theorem realArmCover
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (target cursor : input.LocalizedRerootCursor fuel)
    (arm : input.RuleMajorContextArm fuel stage read cursor)
    (previousEq : cursor.previous? = some target.occurrence)
    (rootNeighbor : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) target.occurrence.1)
    (focusRoot : input.Atom)
    (cursorRoot : cursor.occurrence.1.root = focusRoot)
    {path : List input.Atom}
    (hpath : SimpleFrom input.moleculeGraph focusRoot path)
    (inc : Nodes input.moleculeGraph focusRoot)
    (hchild : armChild path ⟨.real path, hpath⟩ inc)
    (hanchor : RealCutAnchor path hpath (some inc))
    (focusNode : input.occurrenceCarrierNode singleBonded cursor.occurrence = .real path)
    (targetCarrier : inc.1 = input.occurrenceCarrierNode singleBonded target.occurrence) :
    RetainedContextArmFaithful input.moleculeGraph focusRoot
      ⟨.real path, hpath⟩ (some inc) (CutAnchor.realChild hchild)
      (ruleMajorTreeGraph arm.tree) := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace
  let subtreeOf : (ruleMajorTreeGraph arm.tree).Node →
      LocalizedCumulativeDecoratedTree input fuel :=
    fun node => Classical.choose (input.exists_decorated_subtree arm.tree node)
  have lookupOf (node : (ruleMajorTreeGraph arm.tree).Node) :
      subtreeAt? arm.tree node.1 = some (subtreeOf node) :=
    (Classical.choose_spec (input.exists_decorated_subtree arm.tree node)).1
  have officialOf (node : (ruleMajorTreeGraph arm.tree).Node) :
      (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
        some (toOfficialSourceTree (subtreeOf node)) :=
    (Classical.choose_spec (input.exists_decorated_subtree arm.tree node)).2
  let placementOf (node : (ruleMajorTreeGraph arm.tree).Node) :
      Placement input singleBonded hpath inc hanchor (subtreeOf node) :=
    Classical.choice (input.placed_of_lookup singleBonded enough cursor focusRoot cursorRoot
      hpath inc hanchor arm.tree realizes arm.sourceEq focusNode target.occurrence previousEq
      targetCarrier rootNeighbor node.1 (lookupOf node))
  let cutOf : (ruleMajorTreeGraph arm.tree).Node → (input.focusCut hpath inc hanchor).Node :=
    fun node => (placementOf node).cutNode
  have cover : LocalChildCovering (ruleMajorTreeGraph arm.tree)
      (input.focusCut hpath inc hanchor) := {
    toFun := cutOf
    map_root := by
      have rootAddr : (ruleMajorTreeGraph arm.tree).root.1 = [] := rfl
      have rootLookup := lookupOf (ruleMajorTreeGraph arm.tree).root
      rw [rootAddr, subtreeAt?_nil] at rootLookup
      have subEq : subtreeOf (ruleMajorTreeGraph arm.tree).root = arm.tree :=
        (Option.some.inj rootLookup).symm
      have carrier := (placementOf (ruleMajorTreeGraph arm.tree).root).carrierEq
      have sourceEqSub := congrArg
        (fun tree : LocalizedCumulativeDecoratedTree input fuel => tree.source) subEq
      have occEq := congrArg
        (fun child : input.LocalizedRerootCursor fuel => child.occurrence)
        (sourceEqSub.trans arm.sourceEq)
      have sourceCarrier := congrArg (input.occurrenceCarrierNode singleBonded) occEq
      have rootCarrier := cutRoot_eq_focusCarrier input singleBonded hpath hanchor
        cursor.occurrence cursorRoot focusNode
      exact cutNode_ext input hpath inc hanchor
        ((carrier.trans sourceCarrier).trans rootCarrier.symm)
    map_label := by
      intro node
      have graphLabel := (toOfficialSourceTree arm.tree).declarativeLabel_eq_of_subtreeAt?
        (toOfficialSourceTree (subtreeOf node)) node (officialOf node)
      have sourceLabel := toOfficialSourceTree_source (subtreeOf node)
      have cutLabel := cutLabel_eq_occurrenceLabel input singleBonded hpath hanchor
        (subtreeOf node).source.occurrence (placementOf node).cutNode (placementOf node).carrierEq
      simp only [OfficialCIPSourceTree.toDeclarativeDigraph, cutOf]
      rw [graphLabel, sourceLabel]
      exact cutLabel.symm
    child_map := by
      intro parent node hedge
      obtain ⟨slot, addrEq⟩ := hedge
      have parentLook := lookupOf parent
      have childLook := lookupOf node
      have slotLook := input.child_slot_lookup arm.tree slot addrEq parentLook childLook
      have parentRealizes := realizes_of_subtree realizes parentLook
      have childMem := mem_executable_of_child parentRealizes slotLook
      have parentReal := input.provenance_real_of_executable_child singleBonded childMem
      have childPrev := input.executableLocalizedRerootChildren_previous
        (subtreeOf parent).source (subtreeOf node).source childMem
      cases (placementOf parent).rootEq
      have validChild := input.occurrenceCarrierNode_valid singleBonded
        (subtreeOf node).source.occurrence
      let step : Nodes input.moleculeGraph (subtreeOf parent).source.occurrence.1.root :=
        ⟨input.occurrenceCarrierNode singleBonded (subtreeOf node).source.occurrence,
          valid_cast input (placementOf node).rootEq validChild⟩
      obtain ⟨hstep, hedgeCut⟩ :=
        (executableChild_iff_cutChild input singleBonded enough (subtreeOf parent).source
          hpath hanchor parentReal (placementOf parent).prev (placementOf parent).prevEq
          (placementOf parent).prevNeighbor (placementOf parent).cutNode
          (placementOf parent).carrierEq (placementOf parent).prevNode
          (placementOf parent).prevCarrier (placementOf parent).excluded step).mp
          ⟨(subtreeOf node).source, childMem, rfl, childPrev⟩
      have imageEq : cutOf node = ⟨step, hstep⟩ :=
        cutNode_ext input hpath inc hanchor (placementOf node).carrierEq
      exact imageEq.symm ▸ hedgeCut
    child_surjective := by
      intro parent cutTarget hedge
      have parentLook := lookupOf parent
      cases (placementOf parent).rootEq
      have parentReal : (subtreeOf parent).source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom := by
        rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded
            (subtreeOf parent).source.occurrence with
          real | ⟨_distance, ring⟩
        · exact real
        · exfalso
          have stepCut := (cutChild_iff_cutStep hpath hanchor (placementOf parent).cutNode
            cutTarget.1).mp ⟨cutTarget.2, hedge⟩
          let packed : Nodes input.moleculeGraph
              (subtreeOf parent).source.occurrence.1.root :=
            ⟨input.occurrenceCarrierNode singleBonded (subtreeOf parent).source.occurrence,
              input.occurrenceCarrierNode_valid singleBonded
                (subtreeOf parent).source.occurrence⟩
          have packedEq : (placementOf parent).cutNode.1 = packed :=
            Subtype.ext (placementOf parent).carrierEq
          rw [packedEq] at stepCut
          exact ringCursor_no_cutStep input singleBonded (subtreeOf parent).source ring
            (path := path) (incoming := some inc) cutTarget.1 stepCut
      obtain ⟨execChild, execMem, carrierChild, _childPrev⟩ :=
        (executableChild_iff_cutChild input singleBonded enough (subtreeOf parent).source
          hpath hanchor parentReal (placementOf parent).prev (placementOf parent).prevEq
          (placementOf parent).prevNeighbor (placementOf parent).cutNode
          (placementOf parent).carrierEq (placementOf parent).prevNode
          (placementOf parent).prevCarrier (placementOf parent).excluded cutTarget.1).mpr
          ⟨cutTarget.2, hedge⟩
      have parentRealizes := realizes_of_subtree realizes parentLook
      obtain ⟨perm, _computed⟩ := exists_sourcePerm_executable parentRealizes
      have memMap : execChild ∈ ((subtreeOf parent).children.map (fun child => child.source)) :=
        perm.mem_iff.mpr execMem
      obtain ⟨childTree, childTreeMem, childSource⟩ := List.mem_map.mp memMap
      obtain ⟨slot, slotLt, slotGet⟩ := List.mem_iff_getElem.mp childTreeMem
      have decLook : subtreeAt? arm.tree (parent.1 ++ [slot]) = some childTree := by
        rw [subtreeAt?_append_singleton, parentLook, Option.bind_some,
          List.getElem?_eq_getElem slotLt, slotGet]
      have addrMem := input.hierarchyAddress_of_decorated_lookup arm.tree
        (parent.1 ++ [slot]) childTree decLook
      refine ⟨⟨parent.1 ++ [slot], addrMem⟩, ⟨slot, rfl⟩, ?_⟩
      have childLookup := lookupOf ⟨parent.1 ++ [slot], addrMem⟩
      rw [decLook] at childLookup
      have subEq : subtreeOf ⟨parent.1 ++ [slot], addrMem⟩ = childTree :=
        (Option.some.inj childLookup).symm
      have carrierGraph : cutOf ⟨parent.1 ++ [slot], addrMem⟩ |>.1.1 = cutTarget.1.1 := by
        rw [(placementOf ⟨parent.1 ++ [slot], addrMem⟩).carrierEq, subEq, childSource]
        exact carrierChild
      exact cutNode_ext input hpath inc hanchor carrierGraph
    sibling_injective := by
      intro parent node₁ node₂ hedge₁ hedge₂ same
      obtain ⟨slot₁, addr₁⟩ := hedge₁
      obtain ⟨slot₂, addr₂⟩ := hedge₂
      have parentLook := lookupOf parent
      have slotLook₁ := input.child_slot_lookup arm.tree slot₁ addr₁ parentLook (lookupOf node₁)
      have slotLook₂ := input.child_slot_lookup arm.tree slot₂ addr₂ parentLook (lookupOf node₂)
      have parentRealizes := realizes_of_subtree realizes parentLook
      have childMem₁ := mem_executable_of_child parentRealizes slotLook₁
      have childMem₂ := mem_executable_of_child parentRealizes slotLook₂
      obtain ⟨bound₁, get₁⟩ := List.getElem?_eq_some_iff.mp slotLook₁
      obtain ⟨bound₂, get₂⟩ := List.getElem?_eq_some_iff.mp slotLook₂
      have sameCarrier : input.occurrenceCarrierNode singleBonded
            (subtreeOf node₁).source.occurrence =
          input.occurrenceCarrierNode singleBonded (subtreeOf node₂).source.occurrence := by
        have nodeEq : (placementOf node₁).cutNode = (placementOf node₂).cutNode := same
        rw [← (placementOf node₁).carrierEq, ← (placementOf node₂).carrierEq, nodeEq]
      have cursorEq := executableChild_eq_of_carrierNode input singleBonded
        (subtreeOf parent).source (subtreeOf node₁).source (subtreeOf node₂).source
        childMem₁ childMem₂ sameCarrier
      have nodup := input.source_nodup_of_realizes (subtreeOf parent) parentRealizes
      have mapBound₁ : slot₁ <
          ((subtreeOf parent).children.map (fun child => child.source)).length := by
        rw [List.length_map]
        exact bound₁
      have mapBound₂ : slot₂ <
          ((subtreeOf parent).children.map (fun child => child.source)).length := by
        rw [List.length_map]
        exact bound₂
      have slotEq : slot₁ = slot₂ := by
        apply (nodup.getElem_inj_iff (hi := mapBound₁) (hj := mapBound₂)).mp
        rw [List.getElem_map, List.getElem_map, get₁, get₂, cursorEq]
      exact Subtype.ext (by rw [addr₁, addr₂, slotEq])
    target_unique_parent := fun hfirst hsecond =>
      realCut_unique_parent hpath hanchor hfirst hsecond
  }
  exact ⟨cover.toIso.symm⟩

/-- A real executable child, at either address orientation, has rule-major tree
isomorphic to the predecessor cut of its own carrier node. The incoming cut node
is the target's carrier node. `cursor.previous?` is `some target.occurrence`. -/
theorem realExecutableChild_retainedContextArmFaithful
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (arm : input.RuleMajorContextArm fuel stage read cursor) :
    cursor.previous? = some target.occurrence ∧
    ∃ (path : List input.Atom)
      (hpath : SimpleFrom input.moleculeGraph cursor.occurrence.1.root path)
      (inc : Nodes input.moleculeGraph cursor.occurrence.1.root)
      (hchild : armChild path ⟨.real path, hpath⟩ inc),
      input.occurrenceCarrierNode singleBonded cursor.occurrence = .real path ∧
        inc.1 = input.occurrenceCarrierNode singleBonded target.occurrence ∧
        RetainedContextArmFaithful input.moleculeGraph cursor.occurrence.1.root
          ⟨.real path, hpath⟩ (some inc) (CutAnchor.realChild hchild)
          (ruleMajorTreeGraph arm.tree) := by
  obtain ⟨previousEq, rootNeighbor, _adj⟩ :=
    realExecutableChild_incoming_carrierAdjacent input singleBonded target cursor childMem real
  obtain ⟨path, hpath, inc, focusNode, targetNode, hchild⟩ :=
    input.realExecutableChild_incomingArmChild singleBonded target cursor childMem real
  have hanchor : RealCutAnchor path hpath (some inc) :=
    realAnchor (CutAnchor.realChild hchild)
  have targetCarrier : inc.1 = input.occurrenceCarrierNode singleBonded target.occurrence :=
    targetNode.symm
  exact ⟨previousEq, path, hpath, inc, hchild, focusNode, targetCarrier,
    input.realArmCover singleBonded enough target cursor arm previousEq rootNeighbor
      cursor.occurrence.1.root rfl hpath inc hchild hanchor focusNode targetCarrier⟩

/-- Every actual executable child, real or ring, is faithful to the predecessor
cut named by its own carrier image and its target's carrier image. -/
theorem executableChild_retainedContextArmFaithful
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (arm : input.RuleMajorContextArm fuel stage read cursor) :
    cursor.previous? = some target.occurrence ∧
    ∃ (focus : Nodes input.moleculeGraph cursor.occurrence.1.root)
      (incoming : Nodes input.moleculeGraph cursor.occurrence.1.root)
      (anchor : CutAnchor focus (some incoming)),
      focus.1 = input.occurrenceCarrierNode singleBonded cursor.occurrence ∧
        incoming.1 = input.occurrenceCarrierNode singleBonded target.occurrence ∧
        RetainedContextArmFaithful input.moleculeGraph cursor.occurrence.1.root
          focus (some incoming) anchor (ruleMajorTreeGraph arm.tree) := by
  rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded cursor.occurrence with
    cursorReal | ⟨_distance, cursorRing⟩
  · obtain ⟨previousEq, path, hpath, inc, hchild, focusNode, targetCarrier, faithful⟩ :=
      input.realExecutableChild_retainedContextArmFaithful singleBonded enough target cursor
        childMem cursorReal arm
    refine ⟨previousEq, ⟨.real path, hpath⟩, inc, CutAnchor.realChild hchild, ?_, targetCarrier,
      faithful⟩
    exact focusNode.symm
  · obtain ⟨previousEq, path, atom, ringValid, focusNode, targetNode, faithful⟩ :=
      input.ringExecutableChild_retainedContextArmFaithful singleBonded target cursor childMem
        arm cursorRing
    refine ⟨previousEq, ⟨.ring path atom, ringValid⟩, ⟨.real path, ringValid.1⟩,
      CutAnchor.ringParent, ?_, ?_, faithful⟩
    · exact focusNode.symm
    · exact targetNode.symm

/-- Standard carrier fuel is one more than the atom count, so the coverage bound
holds there without a separate fuel hypothesis. -/
theorem executableChild_retainedContextArmFaithful_of_carrierFuel
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (target cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (arm : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stage read cursor) :
    cursor.previous? = some target.occurrence ∧
    ∃ (focus : Nodes input.moleculeGraph cursor.occurrence.1.root)
      (incoming : Nodes input.moleculeGraph cursor.occurrence.1.root)
      (anchor : CutAnchor focus (some incoming)),
      focus.1 = input.occurrenceCarrierNode singleBonded cursor.occurrence ∧
        incoming.1 = input.occurrenceCarrierNode singleBonded target.occurrence ∧
        RetainedContextArmFaithful input.moleculeGraph cursor.occurrence.1.root
          focus (some incoming) anchor (ruleMajorTreeGraph arm.tree) :=
  input.executableChild_retainedContextArmFaithful singleBonded (Nat.le_succ _)
    target cursor childMem arm

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realExecutableChild_retainedContextArmFaithful
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableChild_retainedContextArmFaithful
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableChild_retainedContextArmFaithful_of_carrierFuel
