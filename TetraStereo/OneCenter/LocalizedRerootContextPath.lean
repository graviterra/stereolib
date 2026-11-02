import TetraStereo.OneCenter.LocalizedContextMolecularReader
import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedActualReferenceMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

variable (input : CertifiedLocalizedCIPInput)

private theorem molecularFrameUnit_path_eq_append_of_history_cons
    {atom : input.Atom} {frame parent : input.LocalizedCIPOccurrenceFrame}
    (historyEq : frame.node.history = atom :: parent.node.history)
    (parentLast : parent.node.history.getLast? = some parent.root) :
    frame.node.history.reverse.tail = parent.node.history.reverse.tail ++ [atom] := by
  have reverseNe : parent.node.history.reverse ≠ [] := by
    intro empty
    have historyEmpty : parent.node.history = [] := by
      simpa using congrArg List.reverse empty
    simp [historyEmpty] at parentLast
  change frame.node.history.reverse.tail = parent.node.history.reverse.tail ++ [atom]
  rw [historyEq, List.reverse_cons]
  exact List.tail_append_singleton_of_ne_nil reverseNe

private theorem incomingAtom?_append_singleton
    {root atom : input.Atom} (path : List input.Atom) :
    incomingAtom? root (path ++ [atom]) =
      some (OccurrenceUnit.atom ⟨root, path⟩) := by
  have lastEq : path.getLast? = path.reverse.head? := by
    simpa using (List.getLast?_reverse (l := path.reverse))
  cases reverseEq : path.reverse with
  | nil =>
      have pathEq : path = [] := by
        simpa using congrArg List.reverse reverseEq
      subst path
      simp [incomingAtom?, OccurrenceUnit.atom]
  | cons first rest =>
      simp [incomingAtom?, List.reverse_append, reverseEq, lastEq, OccurrenceUnit.atom]

/-- A single executable reroot step has exactly the molecular context update: it pops the last
atom when the child is the original carrier parent, and appends the atom for an outward child.
The child atom is the actual current atom of the emitted cursor; no path or reader correspondence
is assumed. -/
theorem molecularFrameUnit_executableChild_rerootStep
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (source child : input.LocalizedRerootCursor fuel)
    {next : input.Atom}
    (nextObserved : child.occurrence.1.node.current? = some next)
    (present : child ∈ input.executableLocalizedRerootChildren source) :
    (input.molecularFrameUnit child.occurrence.1).root =
        (input.molecularFrameUnit source.occurrence.1).root ∧
      (input.molecularFrameUnit child.occurrence.1).path =
        rerootStep (input.molecularFrameUnit source.occurrence.1).root
          (input.molecularFrameUnit source.occurrence.1).path next := by
  let sourceFrame := source.occurrence.1
  let childFrame := child.occurrence.1
  have sourceDerived : input.DeclarativeLocalizedOccurrence fuel sourceFrame :=
    (input.mem_localizedOccurrences_iff fuel sourceFrame).mp source.occurrence.2
  have childDerived : input.DeclarativeLocalizedOccurrence fuel childFrame :=
    (input.mem_localizedOccurrences_iff fuel childFrame).mp child.occurrence.2
  have sourceReal := input.carrierOccurrence_realPath singleBonded acyclic source.occurrence
  have childReal := input.carrierOccurrence_realPath singleBonded acyclic child.occurrence
  have childIntended : childFrame ∈ input.intendedLocalizedRerootChildFrames source := by
    rw [← input.executableLocalizedRerootChildren_map source]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have sourceNonDuplicate : sourceFrame.node.isDuplicateLeaf = false :=
    input.carrierOccurrence_not_duplicateLeaf singleBonded acyclic source.occurrence
  have childNeighbor : childFrame ∈
      input.localizedRerootNeighborFrames (fuel := fuel) sourceFrame := by
    simp [intendedLocalizedRerootChildFrames] at childIntended
    rcases childIntended with ⟨_notDuplicate, childInNeighbors⟩
    cases previousEq : source.previous? with
    | none => simpa [previousEq] using childInNeighbors
    | some previous =>
        have filtered : childFrame ∈
            (input.localizedRerootNeighborFrames (fuel := fuel) sourceFrame).filter
              (fun frame => frame.address != previous.1.address) := by
          simpa [previousEq] using childInNeighbors
        exact (List.mem_filter.mp filtered).1
  have neighborShape :=
    (input.mem_localizedRerootNeighborFrames_iff (fuel := fuel) sourceFrame childFrame).mp
      childNeighbor
  have rootEq : childFrame.root = sourceFrame.root := neighborShape.2.1
  have addressCases :
      (childFrame.address.length + 1 = sourceFrame.address.length ∧
        childFrame.address = sourceFrame.address.dropLast) ∨
      (sourceFrame.address.length + 1 = childFrame.address.length ∧
        sourceFrame.address = childFrame.address.dropLast) := by
    exact neighborShape.2.2
  constructor
  · exact rootEq
  · rcases addressCases with ⟨_lengthEq, childAddressEq⟩ | ⟨_lengthEq, sourceAddressEq⟩
    · -- Parent case: the emitted frame is the unique actual carrier frame at the source's
      -- shorter address, and the stored history removes the source's current atom.
      have sourceNonroot : sourceFrame.address ≠ [] := by
        intro empty
        rw [empty] at _lengthEq
        simp at _lengthEq
      obtain ⟨certificate⟩ :=
        input.exists_localizedParentFrameHistory source.occurrence sourceNonroot
      have certificateDerived :
          input.DeclarativeLocalizedOccurrence fuel certificate.parent.1 :=
        (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
      have frameEq : childFrame = certificate.parent.1 :=
        input.declarativeLocalizedOccurrence_functional_at_root_address childDerived
          certificateDerived (rootEq.trans certificate.parent_root.symm)
          (childAddressEq.trans certificate.parent_address.symm)
      have parentLast : certificate.parent.1.node.history.getLast? =
          some certificate.parent.1.root :=
        input.realPathNode_history_getLast
          (input.carrierOccurrence_realPath singleBonded acyclic certificate.parent)
      have sourcePathEq :
          (input.molecularFrameUnit sourceFrame).path =
            (input.molecularFrameUnit certificate.parent.1).path ++ [certificate.current] := by
        have pathEq := molecularFrameUnit_path_eq_append_of_history_cons input
          certificate.history_eq parentLast
        exact pathEq
      have childHead : childFrame.node.history.head? = some next := by
        have currentHead :=
          input.declarativeLocalizedOccurrence_node_history_head_eq_current childDerived
        rw [nextObserved] at currentHead
        exact currentHead
      have childLast : childFrame.node.history.getLast? = some childFrame.root :=
        input.realPathNode_history_getLast childReal
      have childAtom : (input.molecularFrameUnit childFrame).atom = next :=
        input.molecularFrameUnit_atom_eq_current childFrame childHead childLast
      have parentAtom : (input.molecularFrameUnit certificate.parent.1).atom = next := by
        rw [frameEq] at childAtom
        exact childAtom
      have incoming :
          incomingAtom? (input.molecularFrameUnit sourceFrame).root
            (input.molecularFrameUnit sourceFrame).path = some next := by
        rw [sourcePathEq]
        have atomEq :
            OccurrenceUnit.atom ⟨(input.molecularFrameUnit sourceFrame).root,
              (input.molecularFrameUnit certificate.parent.1).path⟩ = next := by
          change OccurrenceUnit.atom
            ⟨certificate.parent.1.root,
              (input.molecularFrameUnit certificate.parent.1).path⟩ = next at parentAtom
          simpa [OccurrenceUnit.atom, certificate.parent_root] using parentAtom
        rw [incomingAtom?_append_singleton]
        exact congrArg some atomEq
      have childPathEq :
          (input.molecularFrameUnit childFrame).path =
            (input.molecularFrameUnit certificate.parent.1).path := by
        simpa [frameEq]
      have incoming' : incomingAtom? (input.molecularFrameUnit sourceFrame).root
          ((input.molecularFrameUnit certificate.parent.1).path ++ [certificate.current]) =
            some next := by
        simpa [sourcePathEq] using incoming
      have stepEq : rerootStep (input.molecularFrameUnit sourceFrame).root
          ((input.molecularFrameUnit certificate.parent.1).path ++ [certificate.current]) next =
            (input.molecularFrameUnit certificate.parent.1).path := by
        simp [rerootStep, incoming']
      calc
        (input.molecularFrameUnit childFrame).path =
            (input.molecularFrameUnit certificate.parent.1).path := childPathEq
        _ = rerootStep (input.molecularFrameUnit sourceFrame).root
              ((input.molecularFrameUnit certificate.parent.1).path ++
                [certificate.current]) next := stepEq.symm
        _ = rerootStep (input.molecularFrameUnit sourceFrame).root
              (input.molecularFrameUnit sourceFrame).path next := by
          rw [← sourcePathEq]
    · -- Outward case: the exact official child extension prepends its new atom to history.
      have childNonempty : childFrame.address ≠ [] := by
        intro empty
        rw [empty] at _lengthEq
        simp at _lengthEq
      let slot := childFrame.address.getLast childNonempty
      have childAddressEq' : childFrame.address = sourceFrame.address ++ [slot] := by
        rw [sourceAddressEq]
        exact (List.dropLast_append_getLast (l := childFrame.address) childNonempty).symm
      obtain ⟨childNode, childAtSlot, childFrameEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child sourceDerived childDerived
          rootEq slot childAddressEq'
      have childNodeCurrent : childNode.current? = some next := by
        have h := nextObserved
        change childFrame.node.current? = some next at h
        rw [childFrameEq] at h
        exact h
      have childNodePresent : childNode ∈ input.executableOfficialCIPChildren sourceFrame.node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      unfold executableOfficialCIPChildren at childNodePresent
      rw [if_neg (by simpa [OfficialCIPNode.isDuplicateLeaf] using sourceNonDuplicate),
        List.mem_map] at childNodePresent
      rcases childNodePresent with ⟨⟨copyAtom, copyIndex⟩, copyPresent, childIdentity⟩
      have currentObserved : sourceFrame.node.current?.isSome = true := by
        exact input.declarativeLocalizedOccurrence_node_current_isSome sourceDerived
      obtain ⟨sourceCurrent, sourceCurrentObserved⟩ :=
        Option.isSome_iff_exists.mp currentObserved
      have adjacentBound := input.mem_executableOfficialChildCopies_adjacent_bound
        sourceFrame.node sourceCurrent copyAtom copyIndex sourceCurrentObserved copyPresent
      have oneBond := singleBonded sourceCurrent copyAtom adjacentBound.1
      have copyZero : copyIndex = 0 := by
        have copyBound : copyIndex < 1 := by simpa [oneBond] using adjacentBound.2
        omega
      have copyAtomEq : copyAtom = next := by
        rw [← childIdentity] at childNodeCurrent
        simp at childNodeCurrent
        exact childNodeCurrent
      have childNodeEq : childNode = sourceFrame.node.extend next 0 := by
        calc
          childNode = sourceFrame.node.extend copyAtom copyIndex := childIdentity.symm
          _ = sourceFrame.node.extend next 0 := by rw [copyAtomEq, copyZero]
      have childHistoryEq : childFrame.node.history = next :: sourceFrame.node.history := by
        rw [childFrameEq, childNodeEq, OfficialCIPNode.extend_history]
      have sourceLast : sourceFrame.node.history.getLast? = some sourceFrame.root :=
        input.realPathNode_history_getLast sourceReal
      have childPathEq :
          (input.molecularFrameUnit childFrame).path =
            (input.molecularFrameUnit sourceFrame).path ++ [next] := by
        have pathEq := molecularFrameUnit_path_eq_append_of_history_cons input
          childHistoryEq sourceLast
        exact pathEq
      have sourceParentIncoming :
          incomingAtom? (input.molecularFrameUnit sourceFrame).root
            (input.molecularFrameUnit sourceFrame).path ≠ some next := by
        by_cases sourceNonroot : sourceFrame.address = []
        · have pathLength :=
            input.molecularFrameUnit_path_length_eq_address_length source.occurrence
          have pathLengthZero : (input.molecularFrameUnit sourceFrame).path.length = 0 := by
            calc
              (input.molecularFrameUnit sourceFrame).path.length = sourceFrame.address.length :=
                pathLength
              _ = 0 := by simp [sourceNonroot]
          have sourcePathEmpty : (input.molecularFrameUnit sourceFrame).path = [] := by
            cases path : (input.molecularFrameUnit sourceFrame).path with
            | nil => rfl
            | cons head tail => simp [path] at pathLengthZero
          simp [sourcePathEmpty, incomingAtom?]
        · obtain ⟨certificate⟩ :=
            input.exists_localizedParentFrameHistory source.occurrence sourceNonroot
          have parentLast : certificate.parent.1.node.history.getLast? =
              some certificate.parent.1.root :=
            input.realPathNode_history_getLast
              (input.carrierOccurrence_realPath singleBonded acyclic certificate.parent)
          have sourcePathEq :
              (input.molecularFrameUnit sourceFrame).path =
                (input.molecularFrameUnit certificate.parent.1).path ++
                  [certificate.current] := by
            have pathEq := molecularFrameUnit_path_eq_append_of_history_cons input
              certificate.history_eq parentLast
            exact pathEq
          have parentHead : certificate.parent.1.node.history.head? =
              certificate.parent.1.node.current? :=
            input.declarativeLocalizedOccurrence_node_history_head_eq_current
              ((input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp
                certificate.parent.2)
          have parentCurrentSome := input.declarativeLocalizedOccurrence_node_current_isSome
            ((input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp
              certificate.parent.2)
          obtain ⟨parentCurrent, parentCurrentObserved⟩ :=
            Option.isSome_iff_exists.mp parentCurrentSome
          have parentHead' : certificate.parent.1.node.history.head? = some parentCurrent := by
            rw [parentCurrentObserved] at parentHead
            exact parentHead
          have parentAtom : (input.molecularFrameUnit certificate.parent.1).atom =
              parentCurrent :=
            input.molecularFrameUnit_atom_eq_current certificate.parent.1 parentHead'
              parentLast
          have incoming :
              incomingAtom? (input.molecularFrameUnit sourceFrame).root
                (input.molecularFrameUnit sourceFrame).path = some parentCurrent := by
            rw [sourcePathEq, incomingAtom?_append_singleton]
            have atomEq :
                OccurrenceUnit.atom ⟨(input.molecularFrameUnit sourceFrame).root,
                  (input.molecularFrameUnit certificate.parent.1).path⟩ = parentCurrent := by
              change OccurrenceUnit.atom
                ⟨certificate.parent.1.root,
                  (input.molecularFrameUnit certificate.parent.1).path⟩ = parentCurrent
                at parentAtom
              simpa [OccurrenceUnit.atom, certificate.parent_root] using parentAtom
            exact congrArg some atomEq
          have sourceParent : sourceFrame.node.parent? = some parentCurrent := by
            cases parentHistory : certificate.parent.1.node.history with
            | nil => simp [parentHistory] at parentLast
            | cons first rest =>
                have firstEq : first = parentCurrent := by
                  simpa [parentHistory] using parentHead'
                subst first
                have sourceHistory : sourceFrame.node.history =
                    certificate.current :: parentCurrent :: rest := by
                  calc
                    sourceFrame.node.history =
                        certificate.current :: certificate.parent.1.node.history :=
                      certificate.history_eq
                    _ = certificate.current :: parentCurrent :: rest := by
                      rw [parentHistory]
                unfold OfficialCIPNode.parent?
                rw [sourceHistory]
          have copyNotParent := input.not_parent_of_zero_mem_executableOfficialChildCopies
            sourceFrame.node copyAtom parentCurrent (by
              simpa [copyZero] using copyPresent) sourceParent
          have nextNeParent : next ≠ parentCurrent := by
            intro equal
            apply copyNotParent
            simpa [copyAtomEq] using equal
          intro equal
          rw [incoming] at equal
          exact nextNeParent (Option.some.inj equal).symm
      have stepEq : rerootStep (input.molecularFrameUnit sourceFrame).root
          (input.molecularFrameUnit sourceFrame).path next =
            (input.molecularFrameUnit sourceFrame).path ++ [next] := by
        simp [rerootStep, sourceParentIncoming]
      simpa [sourceFrame, childFrame] using childPathEq.trans stepEq.symm

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_executableChild_rerootStep
