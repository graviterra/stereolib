import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedActualReferenceMolecularEvidence
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.OneCenter.LocalizedOutwardWholeStateKeyAgreement
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Actual arm-reader locality

`LocalizedDepthDependency` is every deeper occurrence under the same outer root.
`molecularReader` consults `descriptorMap` only for a real detected occurrence, and the
cumulative builder only applies that reader along `E`, the executable children after the
incoming cut. Equal maps on that reachable set make the actual reader, and therefore
`buildLocalizedRerootCumulativeRule45KeyWithRead?`, agree. This is not a covariance theorem.

For the shipped ligand cursor (`previous?` the center root), every consulted atom lies in
`LigandBranchReaches` of the canonical detected molecule. The argument is the occurrence
history, so overlapping rings stay inside the branch. Another ligand root is a depth
dependency and is not reachable from this arm.

Consumer: the one-step descriptor transport. Do not treat depth induction as the read set.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP RootedTetrahedralBranchSymmetry

/-! ## The occurrences an arm actually indexes -/

/-- One cursor consults a detected occurrence when the actual molecular view reads it:
the cursor is a strict depth dependency of the target, its node is a real atom, and the
frame unit is the detected occurrence. Duplicate leaves fail the real-atom test and
contribute no map entry. -/
def ArmDescriptorConsult
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (unit : DetectedOccurrence input.moleculeGraph) : Prop :=
  input.LocalizedDepthDependency cursor.occurrence target ∧
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      input.molecularFrameUnit cursor.occurrence.1 = unit.1

/-- The map support of one actual arm: detected occurrences consulted by some cursor
reachable from the arm start by executable children. The incoming coordinate is already
absent from `E`. -/
def ReachableArmDescriptorConsult
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (start : input.LocalizedRerootCursor fuel)
    (unit : DetectedOccurrence input.moleculeGraph) : Prop :=
  ∃ cursor : input.LocalizedRerootCursor fuel,
    Relation.ReflTransGen (E input) start cursor ∧
      input.ArmDescriptorConsult target cursor unit

/-- Two descriptor maps that agree on the arm's consulted occurrences give the same
actual `molecularReader` value at every executable-reachable cursor. Cursors that fail
the depth, provenance, or detection test read `none` on both sides. -/
theorem molecularReader_eq_of_reachableArmDescriptorConsult
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (start : input.LocalizedRerootCursor fuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (cursor : input.LocalizedRerootCursor fuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.molecularReader map₁ target cursor =
      input.molecularReader map₂ target cursor := by
  unfold molecularReader localizedDependencyLabel
  by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
  · rw [dif_pos dependency, dif_pos dependency]
    unfold molecularView
    by_cases real : cursor.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom
    · rw [if_pos real, if_pos real]
      by_cases detected : IsDetectedCenter input.moleculeGraph
          (input.molecularFrameUnit cursor.occurrence.1).atom
      · rw [dif_pos detected, dif_pos detected]
        have consulted : input.ReachableArmDescriptorConsult target start
            ⟨input.molecularFrameUnit cursor.occurrence.1, detected⟩ :=
          ⟨cursor, reachable, dependency, real, rfl⟩
        rw [agree _ consulted]
      · rw [dif_neg detected, dif_neg detected]
    · rw [if_neg real, if_neg real]
  · rw [dif_neg dependency, dif_neg dependency]

/-- The actual cumulative builder, run on `molecularReader`, depends only on the
consulted occurrences of the arm. The equality is the full `Option` key at every fuel,
including the fail-closed `none` outcome. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_of_reachableArmDescriptorConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.molecularReader map₁ target) fuel cursor =
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.molecularReader map₂ target) fuel cursor :=
  input.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable stage
    (input.molecularReader map₁ target) (input.molecularReader map₂ target) start
    (fun cursor reachable =>
      input.molecularReader_eq_of_reachableArmDescriptorConsult target start map₁ map₂
        agree cursor reachable)

/-! ## The ligand cursor only steps outward -/

/-- The shipped ligand root is an outward cursor of the center: its recorded previous
coordinate is the center root, and its address is the single ligand slot. -/
theorem ligandRoot_outward
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    OutwardRerootCursor input
      (input.localizedAtomRootOccurrence (input.certified.input.molecule.atomCount + 1) center.1)
      (input.localizedLigandRootCursor center index) := by
  let fuel := input.certified.input.molecule.atomCount + 1
  let cursor := input.localizedLigandRootCursor center index
  let rootOcc := input.localizedAtomRootOccurrence fuel center.1
  refine And.intro ?valid (And.intro ?dependency ?incoming)
  · change cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) rootOcc.1
    rw [localizedRerootNeighborFrames, List.mem_append]
    refine Or.inr ?_
    rw [input.mem_localizedCarrierOutwardChildFrames_iff]
    refine ⟨cursor.occurrence.2, ?_, ?_, ?_⟩
    · simpa [cursor, rootOcc] using
        (localizedLigandRootCursor_root input center index).trans
          (localizedAtomRootOccurrence_root input fuel center.1).symm
    · have lengthEq :
          cursor.occurrence.1.address.length = rootOcc.1.address.length + 1 := by
        simp [cursor, rootOcc, localizedLigandRootCursor_address,
          localizedAtomRootOccurrence_address, List.length_singleton]
      exact lengthEq
    · simp [cursor, rootOcc, localizedLigandRootCursor_address,
        localizedAtomRootOccurrence_address, List.dropLast_singleton]
  · unfold LocalizedDepthDependency
    refine ⟨?_, ?_⟩
    · simpa [cursor, rootOcc] using
        (localizedLigandRootCursor_root input center index).trans
          (localizedAtomRootOccurrence_root input fuel center.1).symm
    · simp [cursor, rootOcc, localizedLigandRootCursor_address,
        localizedAtomRootOccurrence_address, List.length_singleton]
  · refine ⟨rootOcc, ?_, ?_⟩
    · simpa [cursor, rootOcc, fuel] using
        localizedLigandRootCursor_previous input center index
    · simp [cursor, rootOcc, localizedLigandRootCursor_address,
        localizedAtomRootOccurrence_address, List.length_singleton]

/-- Executable reachability from an outward cursor only extends the address. -/
theorem address_isPrefix_of_outward_reachable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (start cursor : input.LocalizedRerootCursor fuel)
    (outward : OutwardRerootCursor input target start)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    start.occurrence.1.address <+: cursor.occurrence.1.address := by
  induction reachable with
  | refl => exact ⟨[], by simp⟩
  | @tail parent child path edge ih =>
      have parentOut := input.outward_reachable_cursor target start parent outward path
      rcases parentOut with ⟨valid, _, previous, previousEq, shorter⟩
      rcases input.outward_edge parent child valid previous previousEq shorter edge with
        ⟨dropLastEq, _lengthEq, _, _, _⟩
      have childNonempty : child.occurrence.1.address ≠ [] := by
        intro empty
        have zero : child.occurrence.1.address.length = 0 := by simp [empty]
        omega
      have childAddr : child.occurrence.1.address =
          parent.occurrence.1.address ++
            [child.occurrence.1.address.getLast childNonempty] := by
        have concatEq := List.dropLast_append_getLast childNonempty
        rw [dropLastEq] at concatEq
        exact concatEq.symm
      exact ih.trans ⟨[child.occurrence.1.address.getLast childNonempty], childAddr.symm⟩

/-- Distinct canonical ligands occupy distinct executable slots. -/
theorem localizedLigandRootSlot_ne
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) {index other : Fin 4}
    (distinct : index ≠ other) :
    input.localizedLigandRootSlot center index ≠
      input.localizedLigandRootSlot center other := by
  intro sameSlot
  let children := input.executableOfficialCIPChildren (OfficialCIPNode.root center.1)
  have nodeNe : input.localizedLigandRootNode center index ≠
      input.localizedLigandRootNode center other := by
    intro nodeEq
    have currentEq := congrArg OfficialCIPNode.current? nodeEq
    simp [localizedLigandRootNode, OfficialCIPNode.extend_current?] at currentEq
    exact distinct (input.canonicalLigandAtom_injective center currentEq)
  have memIndex := input.localizedLigandRootNode_mem center index
  have memOther := input.localizedLigandRootNode_mem center other
  have gotIndex := List.getElem?_idxOf memIndex
  have gotOther := List.getElem?_idxOf memOther
  have idxEq : List.idxOf (input.localizedLigandRootNode center index) children =
      List.idxOf (input.localizedLigandRootNode center other) children := by
    simpa [localizedLigandRootSlot, children] using sameSlot
  rw [idxEq] at gotIndex
  exact nodeNe (Option.some_inj.mp (gotIndex.symm.trans gotOther))

/-- A second ligand root is a depth dependency of the center and is not an executable
descendant of the first ligand. Depth induction therefore quantifies over occurrences
this arm does not read. -/
theorem otherLigand_depthDependency_not_reachable
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) {index other : Fin 4}
    (distinct : index ≠ other) :
    let fuel := input.certified.input.molecule.atomCount + 1
    let target := input.localizedAtomRootOccurrence fuel center.1
    input.LocalizedDepthDependency
        (input.localizedLigandRootCursor center other).occurrence target ∧
      ¬ Relation.ReflTransGen (E input)
          (input.localizedLigandRootCursor center index)
          (input.localizedLigandRootCursor center other) := by
  intro fuel target
  refine ⟨?dependency, ?notReach⟩
  · constructor
    · rw [localizedLigandRootCursor_root, localizedAtomRootOccurrence_root]
    · rw [localizedLigandRootCursor_address, localizedAtomRootOccurrence_address]
      simp [List.length_singleton]
  · intro reachable
    have prefixAddr := input.address_isPrefix_of_outward_reachable target
      (input.localizedLigandRootCursor center index)
      (input.localizedLigandRootCursor center other)
      (input.ligandRoot_outward center index) reachable
    rw [localizedLigandRootCursor_address, localizedLigandRootCursor_address] at prefixAddr
    obtain ⟨tail, tailEq⟩ := prefixAddr
    cases tail with
    | nil =>
        simp at tailEq
        exact input.localizedLigandRootSlot_ne center distinct tailEq
    | cons extra rest =>
        have lengthEq := congrArg List.length tailEq
        simp at lengthEq

/-! ## One outward step appends a bonded atom -/

private theorem outwardStep_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (parentShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (edge : E input cursor child) :
    ∃ parentAtom childAtom,
      cursor.occurrence.1.node.current? = some parentAtom ∧
        child.occurrence.1.node.current? = some childAtom ∧
          child.occurrence.1.node.history = childAtom :: cursor.occurrence.1.node.history ∧
            input.moleculeGraph.Adj parentAtom childAtom ∧
              cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  classical
  rcases input.outward_edge cursor child valid previous previousEq parentShorter edge with
    ⟨dropLastEq, _lengthEq, rootEq, _, _⟩
  have childNonempty : child.occurrence.1.address ≠ [] := by
    intro empty
    have zero : child.occurrence.1.address.length = 0 := by simp [empty]
    omega
  have childAddr : child.occurrence.1.address =
      cursor.occurrence.1.address ++
        [child.occurrence.1.address.getLast childNonempty] := by
    have concatEq := List.dropLast_append_getLast childNonempty
    rw [dropLastEq] at concatEq
    exact concatEq.symm
  have cursorDerived :=
    (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
  have childDerived :=
    (input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp child.occurrence.2
  obtain ⟨official, officialAt, frameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child cursorDerived childDerived rootEq
      (child.occurrence.1.address.getLast childNonempty) childAddr
  have officialMem := List.fst_mem_of_mem_zipIdx officialAt
  obtain ⟨cert⟩ := input.exists_localizedParentFrameHistory child.occurrence childNonempty
  have parentDerived :=
    (input.mem_localizedOccurrences_iff fuel cert.parent.1).mp cert.parent.2
  have parentEq : cert.parent.1 = cursor.occurrence.1 :=
    input.declarativeLocalizedOccurrence_functional_at_root_address parentDerived cursorDerived
      (cert.parent_root.trans rootEq) (by rw [cert.parent_address, dropLastEq])
  have parentSome := input.declarativeLocalizedOccurrence_node_current_isSome cursorDerived
  obtain ⟨parentAtom, parentCurrent⟩ := Option.isSome_iff_exists.mp parentSome
  have nodeEq : child.occurrence.1.node = official :=
    congrArg LocalizedCIPOccurrenceFrame.node frameEq
  have officialCurrent : official.current? = some cert.current := by
    rw [← nodeEq]
    exact cert.current_eq
  have adjacent := input.adj_of_mem_executableOfficialCIPChildren
    cursor.occurrence.1.node official parentAtom cert.current parentCurrent officialCurrent
    officialMem
  have historyEq : child.occurrence.1.node.history =
      cert.current :: cursor.occurrence.1.node.history := by
    rw [cert.history_eq, parentEq]
  have parentReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
    simpa [parentEq] using cert.parent_active.1
  exact ⟨parentAtom, cert.current, parentCurrent, cert.current_eq, historyEq, adjacent,
    parentReal⟩

private theorem ligandReachable_center_mem_history
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (reachable : Relation.ReflTransGen (E input)
      (input.localizedLigandRootCursor center index) cursor) :
    center.1 ∈ cursor.occurrence.1.node.history := by
  let fuel := input.certified.input.molecule.atomCount + 1
  let target := input.localizedAtomRootOccurrence fuel center.1
  induction reachable with
  | refl =>
      simp [localizedLigandRootCursor_node, localizedLigandRootNode_eq_rootFromEdge,
        OfficialCIPNode.rootFromEdge, List.mem_cons, List.mem_singleton]
  | @tail parent child path edge ih =>
      have parentOut := input.outward_reachable_cursor target
        (input.localizedLigandRootCursor center index) parent
        (input.ligandRoot_outward center index) path
      rcases parentOut with ⟨valid, _, previous, previousEq, shorter⟩
      obtain ⟨_parentAtom, childAtom, _, _, historyEq, _, _⟩ :=
        input.outwardStep_facts parent child valid previous previousEq shorter edge
      rw [historyEq]
      exact List.mem_cons_of_mem childAtom ih

private theorem ligandReachable_history_getLast
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (reachable : Relation.ReflTransGen (E input)
      (input.localizedLigandRootCursor center index) cursor) :
    cursor.occurrence.1.node.history.getLast? = some center.1 := by
  let fuel := input.certified.input.molecule.atomCount + 1
  let target := input.localizedAtomRootOccurrence fuel center.1
  induction reachable with
  | refl =>
      simp [localizedLigandRootCursor_node, localizedLigandRootNode_eq_rootFromEdge,
        OfficialCIPNode.rootFromEdge]
  | @tail parent child path edge ih =>
      have parentOut := input.outward_reachable_cursor target
        (input.localizedLigandRootCursor center index) parent
        (input.ligandRoot_outward center index) path
      rcases parentOut with ⟨valid, _, previous, previousEq, shorter⟩
      obtain ⟨_parentAtom, childAtom, _, _, historyEq, _, _⟩ :=
        input.outwardStep_facts parent child valid previous previousEq shorter edge
      have parentNonempty : parent.occurrence.1.node.history ≠ [] := by
        intro empty
        simp [empty] at ih
      rw [historyEq]
      have headLast : (childAtom :: parent.occurrence.1.node.history).getLast? =
          parent.occurrence.1.node.history.getLast? := by
        cases parentHistory : parent.occurrence.1.node.history with
        | nil => exact (parentNonempty parentHistory).elim
        | cons atom rest => simp [parentHistory, List.getLast?_cons_cons]
      rw [headLast]
      exact ih

private theorem ligandReachable_real_branchWalk
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (reachable : Relation.ReflTransGen (E input)
      (input.localizedLigandRootCursor center index) cursor) :
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      ∃ atom,
        cursor.occurrence.1.node.current? = some atom ∧
          ∃ walk : input.canonicalDetectedMultiCenterMolecule.mol.underlyingSimpleGraph.Walk
              (input.canonicalDetectedMultiCenterMolecule.ligandAtomAt center index) atom,
            center.1 ∉ walk.support := by
  let fuel := input.certified.input.molecule.atomCount + 1
  let target := input.localizedAtomRootOccurrence fuel center.1
  let molecule := input.canonicalDetectedMultiCenterMolecule
  induction reachable with
  | refl =>
      intro _real
      refine ⟨input.canonicalLigandAtom center index, ?current, ?walk⟩
      · simp [localizedLigandRootCursor_node, localizedLigandRootNode,
          OfficialCIPNode.extend_current?]
      · refine ⟨SimpleGraph.Walk.nil, ?_⟩
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
        intro atomEq
        exact input.canonicalLigandAtom_ne_center center index
          (by simpa [canonicalDetectedMultiCenterMolecule_ligandAtomAt] using atomEq.symm)
  | @tail parent child path edge ih =>
      intro real
      have parentOut := input.outward_reachable_cursor target
        (input.localizedLigandRootCursor center index) parent
        (input.ligandRoot_outward center index) path
      rcases parentOut with ⟨valid, _, previous, previousEq, shorter⟩
      obtain ⟨parentAtom, childAtom, parentCurrent, childCurrent, historyEq, adjacent, parentReal⟩ :=
        input.outwardStep_facts parent child valid previous previousEq shorter edge
      obtain ⟨parentSeen, parentSeenCurrent, parentWalk, parentAvoid⟩ := ih parentReal
      have sameParent : parentSeen = parentAtom :=
        Option.some_inj.mp (parentSeenCurrent.symm.trans parentCurrent)
      subst sameParent
      have childActive :=
        input.localizedCIPOccurrence_activeSimple_of_provenance_real child.occurrence real
      have childFresh : childAtom ∉ parent.occurrence.1.node.history := by
        have nodup := childActive.2
        rw [historyEq] at nodup
        exact (List.nodup_cons.mp nodup).1
      have childNotCenter : childAtom ≠ center.1 := by
        intro childCenter
        exact childFresh (childCenter ▸
          input.ligandReachable_center_mem_history center index parent path)
      have edgeAdj : molecule.mol.underlyingSimpleGraph.Adj parentSeen childAtom := by
        simpa [canonicalDetectedMultiCenterMolecule_mol, MoleculeGraph.underlyingSimpleGraph_adj]
          using adjacent
      refine ⟨childAtom, childCurrent, parentWalk.concat edgeAdj, ?avoid⟩
      intro member
      rw [SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at member
      rcases member with parentMember | childMember
      · exact parentAvoid parentMember
      · exact childNotCenter childMember.symm

/-- A real atom reached by the shipped ligand arm lies in that ligand's deleted-center
branch. The walk is the occurrence history after the center, so the inclusion holds for
overlapping rings. It is not claimed for a rootward start. -/
theorem ligandArm_realAtom_mem_ligandBranchReaches
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (reachable : Relation.ReflTransGen (E input)
      (input.localizedLigandRootCursor center index) cursor)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    ∃ atom, cursor.occurrence.1.node.current? = some atom ∧
      LigandBranchReaches input.canonicalDetectedMultiCenterMolecule center index atom := by
  obtain ⟨atom, current, reaches⟩ :=
    input.ligandReachable_real_branchWalk center index cursor reachable real
  exact ⟨atom, current, reaches⟩

/-- Every detected occurrence actually consulted by the shipped ligand arm has its atom in
`LigandBranchReaches`. The reader target may be any occurrence; the arm start is the
ligand cursor. -/
theorem reachableArmDescriptorConsult_mem_ligandBranchReaches
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult target
      (input.localizedLigandRootCursor center index) unit) :
    LigandBranchReaches input.canonicalDetectedMultiCenterMolecule center index unit.1.atom := by
  obtain ⟨cursor, reachable, _dependency, real, frameEq⟩ := consulted
  obtain ⟨atom, current, reaches⟩ :=
    input.ligandArm_realAtom_mem_ligandBranchReaches center index cursor reachable real
  have derived :=
    (input.mem_localizedOccurrences_iff _ cursor.occurrence.1).mp cursor.occurrence.2
  have head := input.declarativeLocalizedOccurrence_node_history_head_eq_current derived
  rw [current] at head
  have rootEq : cursor.occurrence.1.root = center.1 := by
    have outward := input.outward_reachable_cursor
      (input.localizedAtomRootOccurrence (input.certified.input.molecule.atomCount + 1) center.1)
      (input.localizedLigandRootCursor center index) cursor
      (input.ligandRoot_outward center index) reachable
    have same := outward.2.1.1
    simpa [localizedAtomRootOccurrence_root] using same
  have last : cursor.occurrence.1.node.history.getLast? = some cursor.occurrence.1.root := by
    rw [rootEq]
    exact input.ligandReachable_history_getLast center index cursor reachable
  have atomEq := input.molecularFrameUnit_atom_eq_current cursor.occurrence.1 head last
  have unitAtom : unit.1.atom = atom := by
    rw [← frameEq]
    exact atomEq
  simpa [unitAtom] using reaches

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ArmDescriptorConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ReachableArmDescriptorConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_of_reachableArmDescriptorConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_of_reachableArmDescriptorConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ligandRoot_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.address_isPrefix_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootSlot_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.otherLigand_depthDependency_not_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ligandArm_realAtom_mem_ligandBranchReaches
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reachableArmDescriptorConsult_mem_ligandBranchReaches
