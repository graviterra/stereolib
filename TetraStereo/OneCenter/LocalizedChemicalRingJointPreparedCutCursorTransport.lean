





















import TetraStereo.OneCenter.LocalizedRetainedRealArmExpansion
import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

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
open LocalizedMarkedRetainedSubtreeContext
open LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedRetainedSourceCutFrames
open TetraStereo.OneCenter.Rule4aTableBridge

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-! ## The molecular carrier of an actual source cursor

These four statements are the general kernel part: they mention no cut arm, no context
arm, and no realization hypothesis. -/

/-- The independent molecular carrier node of an actual tree node: read the source
cursor back at that node's address and take its carrier node. -/
def cutCursorCarrier (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (node : (ruleMajorTreeGraph tree).Node) : CarrierNode input.Atom :=
  input.occurrenceCarrierNode singleBonded (nodeSource input tree node).occurrence

/-- Every actual source cursor carries a valid molecular carrier node at its own root. -/
theorem cutCursorCarrier_valid (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (node : (ruleMajorTreeGraph tree).Node) :
    CarrierNode.Valid input.moleculeGraph (nodeSource input tree node).occurrence.1.root
      (cutCursorCarrier input singleBonded tree node) :=
  input.occurrenceCarrierNode_valid singleBonded (nodeSource input tree node).occurrence

/-- The root's molecular carrier is the actual arm root's source cursor carrier. -/
theorem cutCursorCarrier_root (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel) :
    cutCursorCarrier input singleBonded tree (ruleMajorTreeGraph tree).root =
      input.occurrenceCarrierNode singleBonded tree.source.occurrence := by
  unfold cutCursorCarrier
  rw [nodeSource_root input tree]

/-- The carrier of `parentSource` is exactly the carrier of the actual parent node.
This needs no realization hypothesis: it is the address readback of the source tree.
`parentSource` is stated in the canonical frame only at the standard retained carrier
fuel, so this bridge is stated at that fuel, which is the fuel of every actual tree
in the pipeline. -/
theorem cutCursorCarrier_parentSource (singleBonded : input.moleculeGraph.SimpleBonded)
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    {parent node : (ruleMajorTreeGraph tree).Node}
    (edge : (ruleMajorTreeGraph tree).child parent node) :
    input.occurrenceCarrierNode singleBonded (parentSource tree node).occurrence =
      cutCursorCarrier input singleBonded tree parent := by
  unfold cutCursorCarrier
  rw [parentSource_of_child tree edge]

/-! ## Private structural helpers replicated from the real-arm expansion -/

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

/-! ## Placement: each realized subtree is one kept cut node, with its cut parent -/

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
      have lookupSplit :
          subtreeAt? tree (address.dropLast ++ [address.getLast hne]) = some sub := by
        rw [← split]
        exact lookup
      rw [subtreeAt?_append_singleton] at lookupSplit
      obtain ⟨parentSub, parentLook, childLook⟩ := Option.bind_eq_some_iff.mp lookupSplit
      obtain ⟨parentPlacement⟩ := ih address.dropLast parentSub parentLen parentLook
      have parentRealizes := realizes_of_subtree realizes parentLook
      have childMem := mem_executable_of_child parentRealizes childLook
      have parentReal := input.retainedExecutableParent_realAtom singleBonded
        parentSub.source sub.source childMem
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
      have hneFocus := ne_real_focus_of_armChild input hparent
      exact ⟨{
        cutNode := ⟨step, hstep⟩
        carrierEq := rfl
        rootEq := childRoot
        prev := parentSub.source.occurrence
        prevNode := parentPlacement.cutNode.1
        prevEq := childPrev
        prevCarrier := parentPlacement.carrierEq
        prevNeighbor := childNeighbor
        excluded := Or.inr ⟨hneFocus, hparent⟩
      }⟩

/-! ## The canonical cut covering with its carrier readback

The covering is the same local child covering as in `LocalizedRetainedRealArmExpansion`,
but it also records that its node map lands on the carrier of the actual node's source
cursor. The extra field is what the bare `RetainedContextArmFaithful` witness drops. -/

private structure ArmCover (singleBonded : input.moleculeGraph.SimpleBonded)
    {fuel : Nat} {root : input.Atom} {path : List input.Atom}
    (hpath : SimpleFrom input.moleculeGraph root path)
    (inc : Nodes input.moleculeGraph root)
    (hanchor : RealCutAnchor path hpath (some inc))
    (tree : LocalizedCumulativeDecoratedTree input fuel) where
  covering : LocalChildCovering (ruleMajorTreeGraph tree) (input.focusCut hpath inc hanchor)
  carrierOf : ∀ node : (ruleMajorTreeGraph tree).Node,
    (covering.toFun node).1.1 = cutCursorCarrier input singleBonded tree node

private def cutCursorArmCover
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
    (hanchor : RealCutAnchor path hpath (some inc))
    (focusNode : input.occurrenceCarrierNode singleBonded cursor.occurrence = .real path)
    (targetCarrier : inc.1 = input.occurrenceCarrierNode singleBonded target.occurrence) :
    ArmCover input singleBonded hpath inc hanchor arm.tree := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace
  let subtreeOf : (ruleMajorTreeGraph arm.tree).Node →
      LocalizedCumulativeDecoratedTree input fuel :=
    fun node => Classical.choose (exists_local_subtree arm.tree node)
  have lookupOf (node : (ruleMajorTreeGraph arm.tree).Node) :
      subtreeAt? arm.tree node.1 = some (subtreeOf node) :=
    Classical.choose_spec (exists_local_subtree arm.tree node)
  have officialOf (node : (ruleMajorTreeGraph arm.tree).Node) :
      (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
        some (toOfficialSourceTree (subtreeOf node)) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, lookupOf node]
    rfl
  let placementOf (node : (ruleMajorTreeGraph arm.tree).Node) :
      Placement input singleBonded hpath inc hanchor (subtreeOf node) :=
    Classical.choice (input.placed_of_lookup singleBonded enough cursor focusRoot cursorRoot
      hpath inc hanchor arm.tree realizes arm.sourceEq focusNode target.occurrence previousEq
      targetCarrier rootNeighbor node.1 (lookupOf node))
  let cutOf : (ruleMajorTreeGraph arm.tree).Node → (input.focusCut hpath inc hanchor).Node :=
    fun node => (placementOf node).cutNode
  let cover : LocalChildCovering (ruleMajorTreeGraph arm.tree)
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
      have parentReal := input.retainedExecutableParent_realAtom singleBonded
        (subtreeOf parent).source (subtreeOf node).source childMem
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
      have addrMem := LocalizedMarkedRetainedSubtreeContext.address_mem_of_lookup
        arm.tree childTree (parent.1 ++ [slot]) decLook
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
  refine { covering := cover, carrierOf := ?_ }
  intro node
  show (cutOf node).1.1 = cutCursorCarrier input singleBonded arm.tree node
  rw [(placementOf node).carrierEq]
  unfold cutCursorCarrier
  rw [nodeSource_of_lookup input arm.tree (lookupOf node)]

/-! ## The actual-arm cut transport

This is the exact missing connection. The iso is the canonical local child covering,
built from the actual realization; it is not an arbitrary faithful witness. Its node
map sends each actual tree node to the cut node whose carrier is the carrier of that
node's actual source cursor, and the cut parent of that carrier is the carrier of the
actual graph parent. -/

theorem executableChild_cutCursorTransport
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
      ∃ iso : RootedDigraph.Iso (ruleMajorTreeGraph arm.tree)
          (input.focusCut hpath inc (realAnchor (CutAnchor.realChild hchild))),
        (∀ node : (ruleMajorTreeGraph arm.tree).Node,
          (iso.toEquiv node).1.1 = cutCursorCarrier input singleBonded arm.tree node) ∧
        Function.Injective (cutCursorCarrier input singleBonded arm.tree) ∧
        (cutCursorCarrier input singleBonded arm.tree (ruleMajorTreeGraph arm.tree).root =
          .real path) ∧
        (∀ (parent node : (ruleMajorTreeGraph arm.tree).Node),
          (ruleMajorTreeGraph arm.tree).child parent node →
            (input.focusCut hpath inc (realAnchor (CutAnchor.realChild hchild))).child
              (iso.toEquiv parent) (iso.toEquiv node)) ∧
        (∀ (parent node : (ruleMajorTreeGraph arm.tree).Node),
          (ruleMajorTreeGraph arm.tree).child parent node →
            rawNewParent path (cutCursorCarrier input singleBonded arm.tree node) =
              some (cutCursorCarrier input singleBonded arm.tree parent)) := by
  obtain ⟨previousEq, rootNeighbor, _adjacent⟩ :=
    realExecutableChild_incoming_carrierAdjacent input singleBonded target cursor childMem real
  obtain ⟨path, hpath, inc, focusNode, targetNode, hchild⟩ :=
    input.realExecutableChild_incomingArmChild singleBonded target cursor childMem real
  have hanchor : RealCutAnchor path hpath (some inc) :=
    realAnchor (CutAnchor.realChild hchild)
  have targetCarrier : inc.1 = input.occurrenceCarrierNode singleBonded target.occurrence :=
    targetNode.symm
  have armCover := input.cutCursorArmCover singleBonded enough target cursor arm previousEq
    rootNeighbor cursor.occurrence.1.root rfl hpath inc hanchor focusNode targetCarrier
  refine ⟨previousEq, path, hpath, inc, hchild, focusNode, targetCarrier, ?_⟩
  let iso : RootedDigraph.Iso (ruleMajorTreeGraph arm.tree)
      (input.focusCut hpath inc hanchor) :=
    { toEquiv := Equiv.ofBijective armCover.covering.toFun
        ⟨armCover.covering.toFun_injective, armCover.covering.toFun_surjective⟩
      map_root := by
        simpa [Equiv.ofBijective_apply] using armCover.covering.map_root
      map_child := by
        intro left right
        constructor
        · intro hedge
          simpa [Equiv.ofBijective_apply] using armCover.covering.child_map hedge
        · intro hedge
          have hedge' : (input.focusCut hpath inc hanchor).child
              (armCover.covering.toFun left) (armCover.covering.toFun right) := by
            simpa [Equiv.ofBijective_apply] using hedge
          exact armCover.covering.child_map_inv hedge'
      map_label := by
        intro node
        simpa [Equiv.ofBijective_apply] using armCover.covering.map_label node
      map_depth := by
        intro node
        simpa [Equiv.ofBijective_apply] using armCover.covering.map_depth node }
  have isoEq (node : (ruleMajorTreeGraph arm.tree).Node) :
      iso.toEquiv node = armCover.covering.toFun node := by
    rfl
  refine ⟨iso, ?_, ?_, ?_, ?_, ?_⟩
  · intro node
    rw [isoEq node]
    exact armCover.carrierOf node
  · intro left right same
    apply armCover.covering.toFun_injective
    apply cutNode_ext input hpath inc hanchor
    rw [armCover.carrierOf left, armCover.carrierOf right, same]
  · rw [cutCursorCarrier_root input singleBonded arm.tree, arm.sourceEq, focusNode]
  · intro parent node edge
    rw [isoEq parent, isoEq node]
    exact armCover.covering.child_map edge
  · intro parent node edge
    have hchildCut := armCover.covering.child_map edge
    rw [← armCover.carrierOf node, ← armCover.carrierOf parent]
    exact hchildCut

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cutCursorCarrier
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cutCursorCarrier_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cutCursorCarrier_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cutCursorCarrier_parentSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableChild_cutCursorTransport
