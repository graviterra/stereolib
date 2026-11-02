/-
COORDINATION: Consumer is the live owner of `LocalizedRetainedRealArmExpansion`.
Do not edit `LocalizedRetainedArmExpansion` and do not build `RootedDigraph.Iso` here.
`LocalChildCovering.toIso` is that owner's global step. This file is the local cursor law:
carrier adjacency, executable children except the stored previous occurrence, child coverage,
and sibling injectivity. Feed those to `child_map`, `child_surjective`, and
`sibling_injective`. Use the existing `realCut_unique_parent` as `target_unique_parent`.

`realExecutableChild_incomingArmChild` identifies the arm-root focus and incoming with
`occurrenceCarrierNode` of the actual cursor and its target. Both address orientations are
reroot-children. `cursor.previous?` stays `some`; it is never cleared and never replaced by
`focus.dropLast`. `atomCount ≤ fuel` is discharged at standard carrier fuel. A shorter fuel
does not realize every carrier node.
-/
import TetraStereo.OneCenter.LocalizedRetainedArmExpansion
import TetraStereo.OneCenter.DeclarativeCIPRetainedCutArmTraversal
import TetraStereo.OneCenter.DeclarativeCIPRootedGraphLocalIso
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Local cursor correspondence for a predecessor cut

An actual reroot cursor and the independent cut agree one step at a time. For a real
occurrence, undirected carrier adjacency is the zipper neighborhood
`localizedRerootNeighborFrames`, inward or outward. An executable child is exactly such a
neighbor other than the cursor's stored previous occurrence. A ring cursor is terminal.

`atomCount ≤ fuel` turns an independent carrier neighbor into an occurrence, hence into an
executable child. It does not claim that a truncated carrier contains every simple path.
-/

namespace TetraStereo.OneCenter
namespace LocalizedRetainedCursorCutCover

open DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutArmTraversal
open DeclarativeCIP.RootedDigraph
open CertifiedLocalizedCIPInput
open scoped Classical

noncomputable section

variable (input : CertifiedLocalizedCIPInput)

private theorem not_duplicate_of_real {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    cursor.occurrence.1.node.isDuplicateLeaf = false := by
  rw [OfficialCIPNode.isDuplicateLeaf, real]
  rfl

private theorem history_nonempty
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.history ≠ [] := by
  intro empty
  have last := input.carrierOccurrence_history_getLast_eq_root singleBonded occurrence
  simp [empty] at last

private theorem root_eq_of_history_cons
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    {source step : input.LocalizedCIPOccurrence fuel} {atom : input.Atom}
    (hist : step.1.node.history = atom :: source.1.node.history) :
    step.1.root = source.1.root := by
  have stepLast := input.carrierOccurrence_history_getLast_eq_root singleBonded step
  have sourceLast := input.carrierOccurrence_history_getLast_eq_root singleBonded source
  rw [hist, List.getLast?_cons] at stepLast
  simp [sourceLast] at stepLast
  exact stepLast.symm

/-- The occurrence whose history is one cons onto a real occurrence is its zipper child. -/
private theorem neighbor_of_history_cons
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    {source step : input.LocalizedCIPOccurrence fuel} {atom : input.Atom}
    (sourceReal : source.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (hist : step.1.node.history = atom :: source.1.node.history) :
    step.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) source.1 := by
  have rootEq := root_eq_of_history_cons input singleBonded hist
  have addrNe : step.1.address ≠ [] := by
    intro empty
    have derived := (input.mem_localizedOccurrences_iff fuel step.1).mp step.2
    have rootFrame := input.declarativeLocalizedOccurrence_eq_root_of_address_nil derived empty
    have nodeEq : step.1.node = OfficialCIPNode.root step.1.root := by
      simpa using congrArg LocalizedCIPOccurrenceFrame.node rootFrame
    have histRoot : step.1.node.history = [step.1.root] := by
      simp [nodeEq, OfficialCIPNode.root]
    have tailEmpty : source.1.node.history = [] :=
      (List.cons.inj (hist.symm.trans histRoot)).2
    exact history_nonempty input singleBonded source tailEmpty
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory step addrNe
  have parentHist : certificate.parent.1.node.history = source.1.node.history :=
    (List.cons.inj ((certificate.history_eq).symm.trans hist)).2
  have parentDerived :=
    (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
  have sourceDerived := (input.mem_localizedOccurrences_iff fuel source.1).mp source.2
  have sameRoot : certificate.parent.1.root = source.1.root :=
    certificate.parent_root.trans rootEq
  have parentNode : input.occurrenceCarrierNode singleBonded certificate.parent =
      .real certificate.parent.1.node.history.reverse := by
    rw [occurrenceCarrierNode, if_pos certificate.parent_provenance]
  have sourceNode : input.occurrenceCarrierNode singleBonded source =
      .real source.1.node.history.reverse := by
    rw [occurrenceCarrierNode, if_pos sourceReal]
  have sameCarrier : input.occurrenceCarrierNode singleBonded certificate.parent =
      input.occurrenceCarrierNode singleBonded source := by
    rw [parentNode, sourceNode, parentHist]
  have frameEq := input.occurrenceFrame_eq_of_carrierNode singleBonded sameRoot sameCarrier
  have parentEq : certificate.parent = source := Subtype.ext frameEq
  have addr : source.1.address = step.1.address.dropLast := by
    simpa [parentEq] using certificate.parent_address
  have len : source.1.address.length + 1 = step.1.address.length := by
    simpa [parentEq] using certificate.parent_address_length input
  exact (input.mem_localizedRerootNeighborFrames_iff source.1 step.1).mpr
    ⟨step.2, rootEq, Or.inr ⟨len, addr⟩⟩

private theorem excludedPredecessor_eq
    {root : input.Atom} {path : List input.Atom}
    (hfocus : SimpleFrom input.moleculeGraph root path)
    {incoming : Option (Nodes input.moleculeGraph root)}
    {cursor prev step : Nodes input.moleculeGraph root}
    (hprev : ExcludedPredecessor path incoming cursor prev)
    (hstep : ExcludedPredecessor path incoming cursor step) :
    prev = step := by
  rcases hprev with ⟨hroot, hin⟩ | ⟨hne, hparent⟩
  · rcases hstep with ⟨_, hin'⟩ | ⟨hne', _⟩
    · exact Option.some_inj.mp (hin.symm.trans hin')
    · exact (hne' hroot).elim
  · rcases hstep with ⟨hroot, _⟩ | ⟨_, hparent'⟩
    · exact (hne hroot).elim
    · exact realRetainedArm_unique_parent input.moleculeGraph root hfocus hparent hparent'

/-- At a real occurrence, carrier adjacency is the actual zipper neighborhood.
The two address orientations are the two directions of `CarrierNode.Child`. A ring
neighbor is the terminal closure of the real prefix, not a second real path. -/
theorem carrierAdjacent_iff_neighborFrame
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (source step : input.LocalizedCIPOccurrence fuel)
    (real : source.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    CarrierAdjacent (input.occurrenceCarrierNode singleBonded source)
        (input.occurrenceCarrierNode singleBonded step) ↔
      step.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) source.1 := by
  constructor
  · intro hadj
    have sourceNode : input.occurrenceCarrierNode singleBonded source =
        .real source.1.node.history.reverse := by
      rw [occurrenceCarrierNode, if_pos real]
    rcases hadj with hto | hfrom
    · rw [sourceNode] at hto
      rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded step with
        stepReal | ⟨_, stepRing⟩
      · have stepNode : input.occurrenceCarrierNode singleBonded step =
            .real step.1.node.history.reverse := by
          rw [occurrenceCarrierNode, if_pos stepReal]
        rw [stepNode] at hto
        obtain ⟨atom, pathEq⟩ := hto
        have hist : step.1.node.history = atom :: source.1.node.history := by
          apply congrArg List.reverse at pathEq
          simpa [List.reverse_reverse, List.reverse_append, List.reverse_cons] using pathEq
        exact neighbor_of_history_cons input singleBonded real hist
      · have notReal : step.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
          rw [stepRing]
          rintro ⟨⟩
        have stepNode : input.occurrenceCarrierNode singleBonded step =
            .ring step.1.node.history.tail.reverse
              (step.1.node.history.head (history_nonempty input singleBonded step)) := by
          rw [occurrenceCarrierNode, if_neg notReal]
        rw [stepNode] at hto
        have pathEq : step.1.node.history.tail.reverse = source.1.node.history.reverse := hto
        have histTail : step.1.node.history.tail = source.1.node.history := by
          simpa [List.reverse_reverse] using congrArg List.reverse pathEq
        have hist : step.1.node.history =
            step.1.node.history.head (history_nonempty input singleBonded step) ::
              source.1.node.history := by
          simpa [histTail] using
            (List.cons_head_tail (history_nonempty input singleBonded step)).symm
        exact neighbor_of_history_cons input singleBonded real hist
    · rw [sourceNode] at hfrom
      cases stepNodeEq : input.occurrenceCarrierNode singleBonded step with
      | ring _ _ => simp [stepNodeEq, CarrierNode.Child] at hfrom
      | real stepPath =>
          rw [stepNodeEq] at hfrom
          obtain ⟨atom, pathEq⟩ := hfrom
          have stepReal : step.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
            rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded step with
              stepReal | ⟨_, stepRing⟩
            · exact stepReal
            · have notReal : step.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
                rw [stepRing]
                rintro ⟨⟩
              have ringNode : input.occurrenceCarrierNode singleBonded step =
                  .ring step.1.node.history.tail.reverse
                    (step.1.node.history.head (history_nonempty input singleBonded step)) := by
                rw [occurrenceCarrierNode, if_neg notReal]
              rw [ringNode] at stepNodeEq
              cases stepNodeEq
          have stepNode : input.occurrenceCarrierNode singleBonded step =
              .real step.1.node.history.reverse := by
            rw [occurrenceCarrierNode, if_pos stepReal]
          have pathHist : source.1.node.history.reverse =
              step.1.node.history.reverse ++ [atom] := by
            rw [stepNode] at stepNodeEq
            injection stepNodeEq with stepPathEq
            simpa [stepPathEq] using pathEq
          have hist : source.1.node.history = atom :: step.1.node.history := by
            apply congrArg List.reverse at pathHist
            simpa [List.reverse_reverse, List.reverse_append, List.reverse_cons] using pathHist
          have childNeighbor := neighbor_of_history_cons input singleBonded stepReal hist
          exact input.mem_localizedRerootNeighborFrames_symm step source.1 childNeighbor
  · intro neighbor
    have split := (input.mem_localizedRerootNeighborFrames_iff source.1 step.1).mp neighbor
    rcases split.2 with ⟨rootEq, shorter | longer⟩
    · have sourceNe : source.1.address ≠ [] := by
        intro empty
        simp [empty] at shorter
      obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory source sourceNe
      have parentDerived :=
        (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
      have stepDerived := (input.mem_localizedOccurrences_iff fuel step.1).mp step.2
      have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
        parentDerived stepDerived (certificate.parent_root.trans rootEq.symm)
        (certificate.parent_address.trans shorter.2.symm)
      have parentEq : certificate.parent = step := Subtype.ext frameEq
      have hist : source.1.node.history =
          certificate.current :: step.1.node.history := by
        simpa [parentEq] using certificate.history_eq
      have sourceNode : input.occurrenceCarrierNode singleBonded source =
          .real (step.1.node.history.reverse ++ [certificate.current]) := by
        rw [occurrenceCarrierNode, if_pos real, hist, List.reverse_cons]
      have stepReal : step.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
        simpa [parentEq] using certificate.parent_provenance
      have stepNode : input.occurrenceCarrierNode singleBonded step =
          .real step.1.node.history.reverse := by
        rw [occurrenceCarrierNode, if_pos stepReal]
      exact Or.inr (by rw [sourceNode, stepNode]; exact ⟨certificate.current, rfl⟩)
    · have stepNe : step.1.address ≠ [] := by
        intro empty
        simp [empty] at longer
      obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory step stepNe
      have parentDerived :=
        (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
      have sourceDerived := (input.mem_localizedOccurrences_iff fuel source.1).mp source.2
      have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
        parentDerived sourceDerived (certificate.parent_root.trans rootEq)
        (certificate.parent_address.trans longer.2.symm)
      have parentEq : certificate.parent = source := Subtype.ext frameEq
      have hist : step.1.node.history =
          certificate.current :: source.1.node.history := by
        simpa [parentEq] using certificate.history_eq
      have sourceNode : input.occurrenceCarrierNode singleBonded source =
          .real source.1.node.history.reverse := by
        rw [occurrenceCarrierNode, if_pos real]
      rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded step with
        stepReal | ⟨_, stepRing⟩
      · have stepNode : input.occurrenceCarrierNode singleBonded step =
            .real (source.1.node.history.reverse ++ [certificate.current]) := by
          rw [occurrenceCarrierNode, if_pos stepReal, hist, List.reverse_cons]
        exact Or.inl (by rw [sourceNode, stepNode]; exact ⟨certificate.current, rfl⟩)
      · have notReal : step.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
          rw [stepRing]
          rintro ⟨⟩
        have stepNode : input.occurrenceCarrierNode singleBonded step =
            .ring source.1.node.history.reverse certificate.current := by
          rw [occurrenceCarrierNode, if_neg notReal]
          simp [hist]
        exact Or.inl (by rw [sourceNode, stepNode]; rfl)

/-- The arm root's stored previous occurrence is the cut incoming, inward or outward. -/
theorem realExecutableChild_incoming_carrierAdjacent
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    cursor.previous? = some target.occurrence ∧
      cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
        (fuel := fuel) target.occurrence.1 ∧
      CarrierAdjacent (input.occurrenceCarrierNode singleBonded cursor.occurrence)
        (input.occurrenceCarrierNode singleBonded target.occurrence) := by
  have previousEq := input.executableLocalizedRerootChildren_previous target cursor childMem
  have intended : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames target := by
    rw [← input.executableLocalizedRerootChildren_map target]
    exact List.mem_map.mpr ⟨cursor, childMem, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended target
    cursor.occurrence.1 intended
  obtain ⟨_path, _hpath, inc, cursorEq, targetEq, hchild⟩ :=
    input.realExecutableChild_incomingArmChild singleBonded target cursor childMem real
  refine ⟨previousEq, neighbor, ?_⟩
  rw [cursorEq, targetEq]
  exact armChild_carrierAdjacent hchild

private theorem exists_executable_of_neighbor
    {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (prev : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some prev)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (neighbor : frame ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) cursor.occurrence.1)
    (addrNe : frame.address ≠ prev.1.address) :
    ∃ child, child ∈ input.executableLocalizedRerootChildren cursor ∧
      child.occurrence.1 = frame ∧ child.previous? = some cursor.occurrence := by
  have notDup := not_duplicate_of_real input cursor real
  have hcond : cursor.occurrence.1.node.isDuplicateLeaf ≠ true := by
    rw [notDup]
    exact Bool.false_ne_true
  have hin : frame ∈ input.intendedLocalizedRerootChildFrames cursor := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg hcond, previousEq, List.mem_filter]
    exact ⟨neighbor, by simp [bne_iff_ne, addrNe]⟩
  have hmap := input.executableLocalizedRerootChildren_map cursor
  have hmem : frame ∈ (input.executableLocalizedRerootChildren cursor).map
      (fun child => child.occurrence.1) := by
    rw [hmap]
    exact hin
  obtain ⟨child, hchild, hframe⟩ := List.mem_map.mp hmem
  exact ⟨child, hchild, hframe, input.executableLocalizedRerootChildren_previous
    cursor child hchild⟩

/-- An executable child of a real cursor is a carrier neighbor other than its stored
previous occurrence. The previous may sit inward or outward; only that occurrence is removed. -/
theorem executableChild_iff_adjacent_not_previous
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (prev : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some prev)
    (prevNeighbor : cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) prev.1) :
    child ∈ input.executableLocalizedRerootChildren cursor ↔
      child.previous? = some cursor.occurrence ∧
        CarrierAdjacent (input.occurrenceCarrierNode singleBonded cursor.occurrence)
          (input.occurrenceCarrierNode singleBonded child.occurrence) ∧
        child.occurrence ≠ prev := by
  constructor
  · intro hmem
    have previousChild :=
      input.executableLocalizedRerootChildren_previous cursor child hmem
    have frameMem : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
      rw [← input.executableLocalizedRerootChildren_map cursor]
      exact List.mem_map.mpr ⟨child, hmem, rfl⟩
    have notDup := not_duplicate_of_real input cursor real
    have hcond : cursor.occurrence.1.node.isDuplicateLeaf ≠ true := by
      rw [notDup]
      exact Bool.false_ne_true
    have filtered : child.occurrence.1 ∈ input.localizedRerootNeighborFrames
          (fuel := fuel) cursor.occurrence.1 ∧
        child.occurrence.1.address ≠ prev.1.address := by
      unfold intendedLocalizedRerootChildFrames at frameMem
      rw [if_neg hcond, previousEq, List.mem_filter, bne_iff_ne] at frameMem
      exact frameMem
    refine ⟨previousChild,
      (carrierAdjacent_iff_neighborFrame input singleBonded cursor.occurrence
        child.occurrence real).mpr filtered.1, ?_⟩
    intro heq
    exact filtered.2 (by rw [heq])
  · intro ⟨previousChild, hadj, hnot⟩
    have neighbor := (carrierAdjacent_iff_neighborFrame input singleBonded cursor.occurrence
      child.occurrence real).mp hadj
    have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
      ((input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1
        child.occurrence.1).mp neighbor).2.1
    have cursorRoot : cursor.occurrence.1.root = prev.1.root :=
      ((input.mem_localizedRerootNeighborFrames_iff prev.1 cursor.occurrence.1).mp
        prevNeighbor).2.1
    have addrNe : child.occurrence.1.address ≠ prev.1.address := by
      intro addrEq
      have childDerived :=
        (input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp child.occurrence.2
      have prevDerived := (input.mem_localizedOccurrences_iff fuel prev.1).mp prev.2
      have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
        childDerived prevDerived (childRoot.trans cursorRoot) addrEq
      exact hnot (Subtype.ext frameEq)
    obtain ⟨child', hmem, hframe, hprev⟩ := exists_executable_of_neighbor input cursor real
      prev previousEq child.occurrence.1 neighbor addrNe
    have occEq : child'.occurrence = child.occurrence := Subtype.ext hframe
    have childEq : child' = child :=
      LocalizedRerootCursor.ext input occEq (hprev.trans previousChild.symm)
    simpa [childEq] using hmem

/-- Executable children with the same carrier node are the same cursor.
Equal nodes give equal readbacks, hence equal occurrence frames by
`occurrenceFrame_eq_of_carrierNode`. -/
theorem executableChild_eq_of_carrierNode
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (cursor child₁ child₂ : input.LocalizedRerootCursor fuel)
    (h₁ : child₁ ∈ input.executableLocalizedRerootChildren cursor)
    (h₂ : child₂ ∈ input.executableLocalizedRerootChildren cursor)
    (nodeEq : input.occurrenceCarrierNode singleBonded child₁.occurrence =
      input.occurrenceCarrierNode singleBonded child₂.occurrence) :
    child₁ = child₂ := by
  have frame₁ : child₁.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
    rw [← input.executableLocalizedRerootChildren_map cursor]
    exact List.mem_map.mpr ⟨child₁, h₁, rfl⟩
  have frame₂ : child₂.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
    rw [← input.executableLocalizedRerootChildren_map cursor]
    exact List.mem_map.mpr ⟨child₂, h₂, rfl⟩
  have neighbor₁ := input.mem_localizedRerootNeighborFrames_of_mem_intended cursor
    child₁.occurrence.1 frame₁
  have neighbor₂ := input.mem_localizedRerootNeighborFrames_of_mem_intended cursor
    child₂.occurrence.1 frame₂
  have root₁ : child₁.occurrence.1.root = cursor.occurrence.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1
      child₁.occurrence.1).mp neighbor₁).2.1
  have root₂ : child₂.occurrence.1.root = cursor.occurrence.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1
      child₂.occurrence.1).mp neighbor₂).2.1
  have frameEq := input.occurrenceFrame_eq_of_carrierNode singleBonded
    (root₁.trans root₂.symm) nodeEq
  have prev₁ := input.executableLocalizedRerootChildren_previous cursor child₁ h₁
  have prev₂ := input.executableLocalizedRerootChildren_previous cursor child₂ h₂
  exact LocalizedRerootCursor.ext input (Subtype.ext frameEq) (prev₁.trans prev₂.symm)

private theorem occurrence_of_carrierNode
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {root : input.Atom} (step : Nodes input.moleculeGraph root) :
    ∃ occurrence : input.LocalizedCIPOccurrence fuel,
      occurrence.1.root = root ∧
        input.occurrenceCarrierNode singleBonded occurrence = step.1 := by
  cases stepShape : step.1 with
  | real path =>
      have simple : SimpleFrom input.moleculeGraph root path := by
        simpa [stepShape] using step.2
      obtain ⟨occurrence, rootEq, reverseEq, prov⟩ :=
        input.exists_occurrence_of_simpleFrom simple enough
      refine ⟨occurrence, rootEq, ?_⟩
      rw [occurrenceCarrierNode, if_pos prov]
      simpa [reverseEq] using rfl
  | ring path atom =>
      have ringValid : CarrierNode.Valid input.moleculeGraph root (.ring path atom) := by
        simpa [stepShape] using step.2
      obtain ⟨occurrence, rootEq, historyEq, prov⟩ :=
        input.exists_occurrence_of_ring singleBonded ringValid enough
      have notReal : occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
        rw [prov]
        rintro ⟨⟩
      refine ⟨occurrence, rootEq, ?_⟩
      rw [occurrenceCarrierNode, if_neg notReal]
      simp [historyEq]

/-- An independent carrier neighbor, other than the stored previous node, is the carrier
node of some executable child. The fuel bound is `atomCount ≤ fuel`; it is not a claim that
every truncated carrier is the whole molecule. -/
theorem exists_executableChild_of_carrierNode
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (prev : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some prev)
    (prevNeighbor : cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) prev.1)
    (step : Nodes input.moleculeGraph cursor.occurrence.1.root)
    (hadj : CarrierAdjacent (input.occurrenceCarrierNode singleBonded cursor.occurrence) step.1)
    (hnot : step.1 ≠ input.occurrenceCarrierNode singleBonded prev) :
    ∃ child, child ∈ input.executableLocalizedRerootChildren cursor ∧
      input.occurrenceCarrierNode singleBonded child.occurrence = step.1 ∧
      child.previous? = some cursor.occurrence := by
  obtain ⟨occurrence, rootEq, nodeEq⟩ :=
    occurrence_of_carrierNode input singleBonded enough step
  have hadjOcc : CarrierAdjacent
      (input.occurrenceCarrierNode singleBonded cursor.occurrence)
      (input.occurrenceCarrierNode singleBonded occurrence) := by
    simpa [nodeEq] using hadj
  have neighbor := (carrierAdjacent_iff_neighborFrame input singleBonded cursor.occurrence
    occurrence real).mp hadjOcc
  have childRoot : occurrence.1.root = cursor.occurrence.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1 occurrence.1).mp
      neighbor).2.1
  have cursorRoot : cursor.occurrence.1.root = prev.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff prev.1 cursor.occurrence.1).mp
      prevNeighbor).2.1
  have notOcc : occurrence ≠ prev := by
    intro heq
    subst heq
    exact hnot nodeEq.symm
  have addrNe : occurrence.1.address ≠ prev.1.address := by
    intro addrEq
    have occDerived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
    have prevDerived := (input.mem_localizedOccurrences_iff fuel prev.1).mp prev.2
    have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
      occDerived prevDerived (childRoot.trans cursorRoot) addrEq
    exact notOcc (Subtype.ext frameEq)
  obtain ⟨child, hmem, hframe, hprev⟩ := exists_executable_of_neighbor input cursor real prev
    previousEq occurrence.1 neighbor addrNe
  have childNode : input.occurrenceCarrierNode singleBonded child.occurrence = step.1 := by
    have occEq : child.occurrence = occurrence := Subtype.ext hframe
    simpa [occEq] using nodeEq
  exact ⟨child, hmem, childNode, hprev⟩

/-- The cut root is the focus occurrence's carrier node. -/
theorem cutRoot_eq_focusCarrier
    (singleBonded : input.moleculeGraph.SimpleBonded) {root : input.Atom} {path : List input.Atom}
    (hfocus : SimpleFrom input.moleculeGraph root path)
    {incoming : Option (Nodes input.moleculeGraph root)}
    (hanchor : RealCutAnchor path hfocus incoming) {fuel : Nat}
    (focusOcc : input.LocalizedCIPOccurrence fuel)
    (rootEq : focusOcc.1.root = root)
    (focusNode : input.occurrenceCarrierNode singleBonded focusOcc = .real path) :
    (realCutRetainedArm input.moleculeGraph root hfocus incoming hanchor).root.1.1 =
      input.occurrenceCarrierNode singleBonded focusOcc := by
  cases rootEq
  simpa [realCutRetainedArm] using focusNode.symm

/-- A kept cut node read off an occurrence keeps that occurrence's declarative label,
provenance, and ring distance. -/
theorem cutLabel_eq_occurrenceLabel
    (singleBonded : input.moleculeGraph.SimpleBonded) {root : input.Atom} {path : List input.Atom}
    (hfocus : SimpleFrom input.moleculeGraph root path)
    {incoming : Option (Nodes input.moleculeGraph root)}
    (hanchor : RealCutAnchor path hfocus incoming) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (node : (realCutRetainedArm input.moleculeGraph root hfocus incoming hanchor).Node)
    (nodeEq : node.1.1 = input.occurrenceCarrierNode singleBonded occurrence) :
    (realCutRetainedArm input.moleculeGraph root hfocus incoming hanchor).label node =
      occurrence.1.node.toDeclarativeLabel := by
  have labelEq := input.occurrenceCarrierNode_label singleBonded occurrence
  simpa [realCutRetainedArm, nodeEq] using labelEq

/-- A ring cursor has no executable child. Its carrier node is terminal in the cut as well. -/
theorem ringCursor_executableChildren_eq_nil
    {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel) {distance : Nat}
    (ring : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    input.executableLocalizedRerootChildren cursor = [] := by
  have duplicate := input.isDuplicateLeaf_eq_true_of_ring_provenance
    cursor.occurrence.1.node ring
  have intended : input.intendedLocalizedRerootChildFrames cursor = [] := by
    simp [intendedLocalizedRerootChildFrames, duplicate]
  have hmap := input.executableLocalizedRerootChildren_map cursor
  rw [intended] at hmap
  exact List.map_eq_nil_iff.mp hmap

theorem ringCursor_no_cutStep
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) {distance : Nat}
    (ring : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance)
    {path : List input.Atom} {incoming : Option (Nodes input.moleculeGraph
      cursor.occurrence.1.root)}
    (step : Nodes input.moleculeGraph cursor.occurrence.1.root) :
    ¬ CutStep path incoming ⟨input.occurrenceCarrierNode singleBonded cursor.occurrence,
        input.occurrenceCarrierNode_valid singleBonded cursor.occurrence⟩ step := by
  have notReal : cursor.occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
    rw [ring]
    rintro ⟨⟩
  have nodeEq : input.occurrenceCarrierNode singleBonded cursor.occurrence =
      .ring cursor.occurrence.1.node.history.tail.reverse
        (cursor.occurrence.1.node.history.head
          (history_nonempty input singleBonded cursor.occurrence)) := by
    rw [occurrenceCarrierNode, if_neg notReal]
  have validRing : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
      (.ring cursor.occurrence.1.node.history.tail.reverse
        (cursor.occurrence.1.node.history.head
          (history_nonempty input singleBonded cursor.occurrence))) := by
    simpa [nodeEq] using input.occurrenceCarrierNode_valid singleBonded cursor.occurrence
  intro hstep
  have hnot := ring_no_cutStep (focus := path) validRing incoming step
  apply hnot
  simpa [nodeEq] using hstep

/-- Executable children of a kept real cursor are the cut children, and conversely when
`atomCount ≤ fuel`. The cursor's stored previous node is the excluded predecessor: the
incoming anchor at the focus, and the cut parent elsewhere. -/
theorem executableChild_iff_cutChild
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    {path : List input.Atom}
    (hfocus : SimpleFrom input.moleculeGraph cursor.occurrence.1.root path)
    {incoming : Option (Nodes input.moleculeGraph cursor.occurrence.1.root)}
    (hanchor : RealCutAnchor path hfocus incoming)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (prev : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some prev)
    (prevNeighbor : cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) prev.1)
    (cursorCut : (realCutRetainedArm input.moleculeGraph cursor.occurrence.1.root
      hfocus incoming hanchor).Node)
    (cursorNode : cursorCut.1.1 =
      input.occurrenceCarrierNode singleBonded cursor.occurrence)
    (prevNode : Nodes input.moleculeGraph cursor.occurrence.1.root)
    (prevCarrier : prevNode.1 = input.occurrenceCarrierNode singleBonded prev)
    (hexcl : ExcludedPredecessor path incoming cursorCut.1 prevNode)
    (step : Nodes input.moleculeGraph cursor.occurrence.1.root) :
    (∃ child, child ∈ input.executableLocalizedRerootChildren cursor ∧
        input.occurrenceCarrierNode singleBonded child.occurrence = step.1 ∧
        child.previous? = some cursor.occurrence) ↔
      (∃ hstep, (realCutRetainedArm input.moleculeGraph cursor.occurrence.1.root
        hfocus incoming hanchor).child cursorCut ⟨step, hstep⟩) := by
  constructor
  · intro ⟨child, hmem, childNode, _previousChild⟩
    have hchar := (executableChild_iff_adjacent_not_previous input singleBonded cursor child
      real prev previousEq prevNeighbor).mp hmem
    have hadj : CarrierAdjacent cursorCut.1.1 step.1 := by
      simpa [cursorNode, childNode] using hchar.2.1
    have hnot : ¬ ExcludedPredecessor path incoming cursorCut.1 step := by
      intro hexclStep
      have sameNode : step = prevNode :=
        excludedPredecessor_eq input hfocus hexclStep hexcl
      have carrierEq : input.occurrenceCarrierNode singleBonded child.occurrence =
          input.occurrenceCarrierNode singleBonded prev := by
        rw [childNode, ← prevCarrier]
        exact congrArg Subtype.val sameNode
      have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
        ((input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1
          child.occurrence.1).mp
          ((carrierAdjacent_iff_neighborFrame input singleBonded cursor.occurrence
            child.occurrence real).mp hchar.2.1)).2.1
      have prevRoot : cursor.occurrence.1.root = prev.1.root :=
        ((input.mem_localizedRerootNeighborFrames_iff prev.1 cursor.occurrence.1).mp
          prevNeighbor).2.1
      have frameEq := input.occurrenceFrame_eq_of_carrierNode singleBonded
        (childRoot.trans prevRoot) carrierEq
      exact hchar.2.2 (Subtype.ext frameEq)
    have hstepCut : CutStep path incoming cursorCut.1 step := ⟨hadj, hnot⟩
    exact (cutChild_iff_cutStep hfocus hanchor cursorCut step).mpr hstepCut
  · intro ⟨hstep, hchild⟩
    have hstepCut := (cutChild_iff_cutStep hfocus hanchor cursorCut step).mp ⟨hstep, hchild⟩
    have hadj : CarrierAdjacent
        (input.occurrenceCarrierNode singleBonded cursor.occurrence) step.1 := by
      simpa [cursorNode] using hstepCut.1
    have hnot : step.1 ≠ input.occurrenceCarrierNode singleBonded prev := by
      intro same
      have nodeEq : step = prevNode := Subtype.ext (same.trans prevCarrier.symm)
      exact hstepCut.2 (by simpa [nodeEq] using hexcl)
    exact exists_executableChild_of_carrierNode input singleBonded enough cursor real prev
      previousEq prevNeighbor step hadj hnot

private theorem localChildCovering_child_map
    {Atom : Type} {left right : RootedDigraph Atom}
    (cover : LocalChildCovering left right) {parent node}
    (hedge : left.child parent node) :
    right.child (cover.toFun parent) (cover.toFun node) :=
  cover.child_map hedge

end

end LocalizedRetainedCursorCutCover
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.carrierAdjacent_iff_neighborFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.realExecutableChild_incoming_carrierAdjacent
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.executableChild_iff_adjacent_not_previous
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.executableChild_eq_of_carrierNode
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.exists_executableChild_of_carrierNode
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.cutRoot_eq_focusCarrier
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.cutLabel_eq_occurrenceLabel
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.ringCursor_executableChildren_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.ringCursor_no_cutStep
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCursorCutCover.executableChild_iff_cutChild
