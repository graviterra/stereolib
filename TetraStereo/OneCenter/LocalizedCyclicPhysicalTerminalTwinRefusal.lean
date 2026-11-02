import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.OneCenter.LocalizedPhysicalTerminalTwinOutwardDomain
import TetraStereo.OneCenter.LocalizedTerminalTwinAuxiliaryRefusal
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundBuilder
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Cyclic actual terminal-twin refusal

The actual reference state is the revised rule-major fixed point.  Physical leaf labels are
derived from its own descriptor-center guard; simple-path evidence excludes a terminal leaf from
the stored parent of a real detected occurrence even when the molecule contains rings.
-/

namespace TetraStereo.OneCenter
namespace LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput
open DeclarativeCIP
noncomputable section
open scoped Classical

/-- A physical leaf occurrence is unlabelled in the current rule-major generated state. -/
theorem referenceState_none_of_actualPhysicalLeaf
    (input : Input) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input) (atom : input.certified.Atom)
    (actual : input.certified.ActualPhysicalAtomAtNode target.1.node atom)
    (leaf : (input.certified.moleculeGraph.neighborFinset atom).card ≤ 1) :
    referenceState input target = none := by
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := actual.1
  have detectedAbsent : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom := by
    intro detected
    have path := input.certified.simpleOccurrencePath_of_carrier_real singleBonded target real
    obtain ⟨current, _walk, currentObserved, head, _provenance, _isPath, _support, _parent⟩ :=
      input.certified.simpleOccurrencePath_realPathNode path
    have last := input.certified.realPathNode_history_getLast
      (input.certified.simpleOccurrencePath_realPathNode path)
    have frameAtom := input.certified.molecularFrameUnit_atom_eq_current target.1 head last
    have currentEq : current = atom := Option.some.inj (currentObserved.symm.trans actual.2)
    change (input.certified.moleculeGraph.neighborFinset
      (input.certified.molecularFrameUnit target.1).atom).card = 4 at detected
    rw [frameAtom] at detected
    rw [currentEq] at detected
    omega
  exact referenceState_none_of_real_not_detected singleBonded target real detectedAbsent

/-- In a finite simple-bonded cyclic molecule, a real occurrence whose physical current atom is
adjacent to a terminal leaf cannot have that leaf as its stored parent when the original root is
not the leaf.  This uses the actual simple path represented by the real occurrence; no
acyclicity premise is involved. -/
theorem actualParent_ne_terminalLeaf
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) {leaf center : input.Atom}
    (currentObserved : occurrence.1.node.current? = some center)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (parentObserved : occurrence.1.node.parent? = some leaf)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center})
    (rootNe : occurrence.1.root ≠ leaf) : False := by
  have path := input.simpleOccurrencePath_of_carrier_real singleBonded occurrence real
  obtain ⟨current, walk, observed, _head, _provenance, isPath, _support, penultimate⟩ :=
    input.simpleOccurrencePath_realPathNode path
  have currentEq : current = center := Option.some.inj (observed.symm.trans currentObserved)
  exact reverseWalk_not_terminalLeaf input
    walk.reverse isPath.reverse
    (by rw [SimpleGraph.Walk.snd_reverse]; exact penultimate leaf parentObserved)
    currentEq leafNeighbors rootNe

/-- A degree-one physical leaf different from the occurrence root cannot already occur anywhere
on the simple source path to its center. If it did, the path's next edge would revisit the center,
the only physical neighbor of that leaf. -/
theorem actualHistory_avoids_terminalLeaf
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) {leaf center : input.Atom}
    (currentObserved : occurrence.1.node.current? = some center)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center})
    (rootNe : occurrence.1.root ≠ leaf) : leaf ∉ occurrence.1.node.history := by
  have path := input.simpleOccurrencePath_of_carrier_real singleBonded occurrence real
  obtain ⟨_current, walk, observed, _head, _provenance, isPath, supportReverse, _parent⟩ :=
    input.simpleOccurrencePath_realPathNode path
  have currentEq : _current = center := Option.some.inj (observed.symm.trans currentObserved)
  intro leafHistory
  have leafHistory' : leaf ∈ walk.support.reverse := by
    rw [supportReverse]
    exact leafHistory
  have leafSupport : leaf ∈ walk.support := by
    exact List.mem_reverse.mp leafHistory'
  obtain ⟨index, indexGet⟩ := List.mem_iff_get.mp leafSupport
  have indexBound : index.val ≤ walk.length := by
    have hlen := walk.length_support
    have h := index.isLt
    omega
  have getLeaf : walk.getVert index.val = leaf := by
    rw [walk.getVert_eq_support_getElem indexBound]
    simpa using indexGet
  have leafNeCenter : leaf ≠ center := by
    have centerMem : center ∈ input.moleculeGraph.neighborFinset leaf := by
      rw [leafNeighbors]
      simp
    have adjacent := (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf center).mp centerMem
    exact SimpleGraph.ne_of_adj input.moleculeGraph.underlyingSimpleGraph
      ((MoleculeGraph.underlyingSimpleGraph_adj input.moleculeGraph leaf center).mpr adjacent)
  have indexNotStart : index.val ≠ 0 := by
    intro endEq
    have rootEqLeaf : occurrence.1.root = leaf := by simpa [endEq] using getLeaf
    exact rootNe rootEqLeaf
  have indexNotEnd : index.val ≠ walk.length := by
    intro endEq
    have leafEqCenter : leaf = center := by
      calc
        leaf = walk.getVert index.val := getLeaf.symm
        _ = walk.getVert walk.length := by rw [endEq]
        _ = center := by simp [currentEq]
    exact leafNeCenter leafEqCenter
  have indexLt : index.val < walk.length := by omega
  have nextAdj : input.moleculeGraph.Adj leaf (walk.getVert (index.val + 1)) := by
    have adj := walk.adj_getVert_succ indexLt
    rw [getLeaf] at adj
    exact (MoleculeGraph.underlyingSimpleGraph_adj input.moleculeGraph leaf
      (walk.getVert (index.val + 1))).mp adj
  have nextMem : walk.getVert (index.val + 1) ∈ input.moleculeGraph.neighborFinset leaf :=
    (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf _).mpr nextAdj
  rw [leafNeighbors] at nextMem
  have nextEq : walk.getVert (index.val + 1) = center := Finset.mem_singleton.mp nextMem
  have endEq : index.val + 1 = walk.length :=
    (isPath.getVert_eq_end_iff (by omega)).mp (by rw [nextEq]; simp [currentEq])
  have penultimateIdx : index.val = walk.length - 1 := by omega
  have qSnd : walk.reverse.snd = leaf := by
    rw [SimpleGraph.Walk.snd_reverse]
    simpa [SimpleGraph.Walk.penultimate, penultimateIdx] using getLeaf
  exact reverseWalk_not_terminalLeaf input walk.reverse isPath.reverse qSnd
    currentEq leafNeighbors rootNe

/-- A physical terminal neighbor of a real detected occurrence is produced as an actual outward
carrier frame, in finite simple-bonded cyclic molecules. The original root exclusion makes the
leaf different from the endpoint, and the simple-path argument excludes it as the stored parent. -/
theorem exists_actualOutwardTerminalLeafFrame
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (leaf : input.Atom)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center.1})
    (rootNe : target.1.root ≠ leaf) :
    ∃ frame slot,
      frame.address = target.1.address ++ [slot] ∧
      frame.root = target.1.root ∧ frame.node.current? = some leaf ∧
      frame.node = target.1.node.extend leaf 0 ∧
      frame ∈ input.localizedOccurrences carrierFuel ∧
      frame ∈ input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
  have adjacent : input.moleculeGraph.Adj center.1 leaf := by
    have member : center.1 ∈ input.moleculeGraph.neighborFinset leaf := by
      rw [leafNeighbors]
      simp
    exact (MoleculeGraph.adj_symm input.moleculeGraph).mp
      ((MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf center.1).mp member)
  have notParent : target.1.node.parent? ≠ some leaf := by
    intro parent
    exact actualParent_ne_terminalLeaf input singleBonded target meaning.2 meaning.1
      parent leafNeighbors rootNe
  exact input.realCenter_outwardChildFrame_of_notParent enough target meaning.2 adjacent
    notParent meaning.1

/-- The outward leaf frame is represented by a cursor in the actual fail-closed reroot child
enumeration, with its recorded predecessor set to the target occurrence. -/
theorem exists_actualOutwardTerminalLeafCursor
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (leaf : input.Atom)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center.1})
    (rootNe : target.1.root ≠ leaf) :
    ∃ child : input.LocalizedRerootCursor carrierFuel,
      child ∈ input.executableLocalizedRerootChildren
        ({ occurrence := target, previous? := none }) ∧
      child.previous? = some target ∧
      child.occurrence.1.node.current? = some leaf ∧
      child.occurrence.1.node = target.1.node.extend leaf 0 ∧
      input.ActualPhysicalAtomAtNode child.occurrence.1.node leaf ∧
      child.occurrence.1 ∈ input.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel) target.1 := by
  obtain ⟨frame, _slot, _addressEq, _rootEq, currentEq, nodeEq, _carrier, outward⟩ :=
    exists_actualOutwardTerminalLeafFrame input singleBonded enough target center meaning leaf
      leafNeighbors rootNe
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren rootCursor
  have targetNonduplicate : target.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target.1.node meaning.1
  have leafFresh := actualHistory_avoids_terminalLeaf input singleBonded target
    meaning.2 meaning.1 leafNeighbors rootNe
  have framesEq : input.intendedLocalizedRerootChildFrames rootCursor =
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
    simp [intendedLocalizedRerootChildFrames, rootCursor, targetNonduplicate]
  have frameMem : frame ∈ children.map (fun cursor => cursor.occurrence.1) := by
    have sound := input.localizedRerootChildren?_sound rootCursor children computed
    rw [sound.1, framesEq]
    exact List.mem_append_right _ outward
  obtain ⟨child, childMem, frameEq⟩ := List.mem_map.mp frameMem
  have sound := input.localizedRerootChildren?_sound rootCursor children computed
  have childrenEq : children = input.executableLocalizedRerootChildren rootCursor :=
    Option.some.inj (computed.symm.trans
      (input.localizedRerootChildren?_eq_some_executable rootCursor))
  refine ⟨child, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← childrenEq]
    simpa [rootCursor] using childMem
  · exact sound.2 child childMem
  · simpa [frameEq] using currentEq
  · simpa [frameEq] using nodeEq
  · refine ⟨?_, ?_⟩
    · rw [frameEq, nodeEq, OfficialCIPNode.extend_provenance]
      exact OfficialCIPNode.childProvenance_real target.1.node leaf leafFresh
    · simpa [frameEq] using currentEq
  · rw [frameEq]
    exact outward

/-- A physical terminal neighbor occupies a slot of the cyclic single-bond four-ligand frame, and
that slot is the very real child cursor in the actual reroot compilation. -/
theorem exists_actualTerminalLeafSlotCursor
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (ligand : Fin 4 ≃ input.moleculeGraph.Neighbor center.1)
    (ligandAt : ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
      some (ligand i).1)
    (leaf : input.Atom)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center.1})
    (rootNe : target.1.root ≠ leaf) :
    ∃ index cursor,
      frame.cursorAt index = cursor ∧
      cursor.previous? = some target ∧
      cursor.occurrence.1.node.current? = some leaf ∧
      cursor.occurrence.1.node = target.1.node.extend leaf 0 ∧
      input.ActualPhysicalAtomAtNode cursor.occurrence.1.node leaf ∧
      cursor.occurrence.1 ∈ input.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel) target.1 := by
  have centerMem : center.1 ∈ input.moleculeGraph.neighborFinset leaf := by
    rw [leafNeighbors]
    simp
  have adjCenterLeaf : input.moleculeGraph.Adj center.1 leaf :=
    (MoleculeGraph.adj_symm input.moleculeGraph).mp
      ((MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf center.1).mp centerMem)
  let neighbor : input.moleculeGraph.Neighbor center.1 := ⟨leaf, adjCenterLeaf⟩
  let index : Fin 4 := ligand.symm neighbor
  have slotCurrent : (frame.cursorAt index).occurrence.1.node.current? = some leaf := by
    dsimp [index, neighbor]
    rw [ligandAt]
    simp
  obtain ⟨child, childMem, incoming, childCurrent, childNode, childActual, childOutward⟩ :=
    exists_actualOutwardTerminalLeafCursor input singleBonded enough target center meaning
      leaf leafNeighbors rootNe
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren rootCursor
  have childrenEq : children = input.executableLocalizedRerootChildren rootCursor :=
    Option.some.inj (computed.symm.trans
      (input.localizedRerootChildren?_eq_some_executable rootCursor))
  have slotMem : frame.cursorAt index ∈ children := by
    rw [childrenEq]
    rw [← input.localizedOccurrenceFourLigandFrame_cursors_eq_executable
      target frame frameComputed]
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  have childMember : child ∈ children := by
    rw [childrenEq]
    exact childMem
  have injective := input.simpleBond_realCenter_rerootChildren_current_injective
    singleBonded target center meaning children computed
  have same : (frame.cursorAt index).occurrence.1.node.current? =
      child.occurrence.1.node.current? := slotCurrent.trans childCurrent.symm
  have cursorEq : frame.cursorAt index = child := injective
    (frame.cursorAt index) slotMem child childMember same
  exact ⟨index, child, cursorEq, incoming, childCurrent, childNode, childActual, childOutward⟩

/-- The current revised cumulative compiler emits its canonical actual terminal key when the
occurrence's child enumeration is empty and its own reader returns none. -/
theorem actualRuleMajorCumulative_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (labelNone : read cursor = none) (fuel : Nat) :
    input.buildRuleMajorCumulativeWithReadExec? stage read fuel cursor =
      some (localizedCumulativeRule45TerminalKey input stage cursor none) := by
  cases fuel with
  | zero => simp [buildRuleMajorCumulativeWithReadExec?, terminal, labelNone]
  | succ fuel => simp [buildRuleMajorCumulativeWithReadExec?, terminal, labelNone]

/-- The current reader-consistent compound compiler on a terminal actual cursor is the canonical
terminal key used by the cyclic physical-leaf comparison. -/
theorem actualRuleMajorCompound_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.executableLocalizedRerootChildren? cursor = some [])
    (labelNone : input.localizedDependencyLabel target view cursor = none)
    (fuel : Nat) :
    input.buildActualRuleMajorCompoundRule45Key? target view fuel cursor =
      some (TerminalTwinAuxiliaryRefusal.terminalCompound45 input
        cursor.occurrence.1.node) := by
  rw [← input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
  unfold buildActualRuleMajorCompoundRule45KeyExec? buildRuleMajorCompoundRule45KeyExec?
  have oldTerminal : input.localizedRerootChildren? cursor = some [] := by
    have same : input.executableLocalizedRerootChildren? cursor =
        input.localizedRerootChildren? cursor :=
      (input.executableLocalizedRerootChildren?_eq_some cursor).trans
        (input.localizedRerootChildren?_eq_some_executable cursor).symm
    rw [← same]
    exact terminal
  have rootKey : input.buildLocalizedRerootCumulativeRule45KeyExec?
      .rule4a target view fuel cursor =
      some (TerminalTwinAuxiliaryRefusal.terminalCumulativeKey input
        cursor.occurrence.1.node .rule4a) := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build
      .rule4a target view fuel cursor]
    cases fuel with
    | zero => simp [buildLocalizedRerootCumulativeRule45Key?, oldTerminal, labelNone,
        TerminalTwinAuxiliaryRefusal.terminalCumulativeKey]
    | succ fuel => simp [buildLocalizedRerootCumulativeRule45Key?, oldTerminal, labelNone,
        TerminalTwinAuxiliaryRefusal.terminalCumulativeKey]
  let terminalCompiler : input.RuleMajorCompoundStageCompiler carrierFuel :=
    fun stage c => some (TerminalTwinAuxiliaryRefusal.terminalCumulativeKey input
      c.occurrence.1.node stage)
  have stageEq : ∀ stage,
      input.ruleMajorCompoundStageCompilerExec target view
        (input.localizedDependencyLabel target view) fuel stage cursor =
        terminalCompiler stage cursor := by
    intro stage
    cases stage with
    | rule4a => exact rootKey
    | rule4b reference =>
        exact actualRuleMajorCumulative_terminal input (.rule4b reference)
          (input.localizedDependencyLabel target view) cursor terminal labelNone fuel
    | rule4cNoReference =>
        exact actualRuleMajorCumulative_terminal input .rule4cNoReference
          (input.localizedDependencyLabel target view) cursor terminal labelNone fuel
    | rule4c reference =>
        exact actualRuleMajorCumulative_terminal input (.rule4c reference)
          (input.localizedDependencyLabel target view) cursor terminal labelNone fuel
    | rule5NoRule4bReference reference =>
        exact actualRuleMajorCumulative_terminal input (.rule5NoRule4bReference reference)
          (input.localizedDependencyLabel target view) cursor terminal labelNone fuel
    | rule5 reference common =>
        exact actualRuleMajorCumulative_terminal input (.rule5 reference common)
          (input.localizedDependencyLabel target view) cursor terminal labelNone fuel
  rw [input.buildRuleMajorCompoundRule45KeyWith?_eq
    (input.ruleMajorCompoundStageCompilerExec target view
      (input.localizedDependencyLabel target view) fuel)
    terminalCompiler cursor stageEq]
  rfl

/-- The independently proved terminal Rule-1b constitutional tie for physical twins also ties the
canonical through-Rule-5 compound keys used by the current actual compiler. -/
theorem actualTerminalCompound_compare_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (firstAtom secondAtom : input.Atom)
    (firstActual : input.ActualPhysicalAtomAtNode first.occurrence.1.node firstAtom)
    (secondActual : input.ActualPhysicalAtomAtNode second.occurrence.1.node secondAtom)
    (zEq : input.moleculeGraph.atomZ firstAtom = input.moleculeGraph.atomZ secondAtom)
    (massEq : input.moleculeGraph.atomMass firstAtom = input.moleculeGraph.atomMass secondAtom)
    (distanceEq : first.occurrence.1.node.rule1bRootDistance =
      second.occurrence.1.node.rule1bRootDistance) :
    (input.compareLocalizedRerootCompoundThroughRule5
      (TerminalTwinAuxiliaryRefusal.terminalCompound45 input first.occurrence.1.node)
      (TerminalTwinAuxiliaryRefusal.terminalCompound45 input second.occurrence.1.node)).ordering =
        Ordering.eq := by
  have labelEq := TerminalTwinAuxiliaryRefusal.officialNodeAtomLabel_eq_of_actualPhysical_z_mass
    input first.occurrence.1.node second.occurrence.1.node firstAtom secondAtom
    firstActual secondActual zEq massEq
  have constitutionalEq := TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
    input first second labelEq distanceEq
  rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
  exact TerminalTwinAuxiliaryRefusal.terminalCompound45_compare_eq input
    first.occurrence.1.node second.occurrence.1.node constitutionalEq

/-- The current descriptor callback reports a successful equality comparison for two frame
slots whose actual revised builders produce the canonical terminal twin keys. -/
theorem compareRuleMajorOccurrenceAt?_terminal_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (leftIndex rightIndex : Fin 4)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftAt : frame.cursorAt leftIndex = leftCursor)
    (rightAt : frame.cursorAt rightIndex = rightCursor)
    (leftBuilt : input.buildActualRuleMajorCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) leftCursor =
        some (TerminalTwinAuxiliaryRefusal.terminalCompound45 input
          leftCursor.occurrence.1.node))
    (rightBuilt : input.buildActualRuleMajorCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) rightCursor =
        some (TerminalTwinAuxiliaryRefusal.terminalCompound45 input
          rightCursor.occurrence.1.node))
    (leftAtom rightAtom : input.Atom)
    (leftActual : input.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom)
    (rightActual : input.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom)
    (zEq : input.moleculeGraph.atomZ leftAtom = input.moleculeGraph.atomZ rightAtom)
    (massEq : input.moleculeGraph.atomMass leftAtom = input.moleculeGraph.atomMass rightAtom)
    (distanceEq : leftCursor.occurrence.1.node.rule1bRootDistance =
      rightCursor.occurrence.1.node.rule1bRootDistance) :
    ∃ result, input.compareRuleMajorOccurrenceAt? target view frame leftIndex rightIndex =
      some result ∧ result.ordering = Ordering.eq := by
  dsimp [CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceAt?]
  rw [leftAt, rightAt, leftBuilt, rightBuilt]
  refine ⟨localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5
      (TerminalTwinAuxiliaryRefusal.terminalCompound45 input leftCursor.occurrence.1.node)
      (TerminalTwinAuxiliaryRefusal.terminalCompound45 input rightCursor.occurrence.1.node)), ?_, ?_⟩
  · rfl
  · exact actualTerminalCompound_compare_eq input leftCursor rightCursor leftAtom rightAtom
      leftActual rightActual zEq massEq distanceEq

/-- Two distinct tied actual frame slots make the revised rule-major descriptor refuse at any
target for which its own center and frame computations succeed. -/
theorem ruleMajorDescriptor?_eq_none_of_actualTerminalTwinTie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (leftIndex rightIndex : Fin 4) (distinct : leftIndex ≠ rightIndex)
    (leftTie : ∃ result, input.compareRuleMajorOccurrenceAt? target view frame
      leftIndex rightIndex = some result ∧ result.ordering = Ordering.eq)
    (rightTie : ∃ result, input.compareRuleMajorOccurrenceAt? target view frame
      rightIndex leftIndex = some result ∧ result.ordering = Ordering.eq) :
    input.ruleMajorDescriptor? target view = none := by
  have sortNone := safeTrackedOrderOf_eq_none_of_tie
    (input.compareRuleMajorOccurrenceAt? target view frame) distinct leftTie rightTie
  unfold ruleMajorDescriptor? ruleMajorSpatialEvidence?
  simp [centerComputed, frameComputed, sortNone]

/-- Current generated-state refusal for two distinct physical terminal twins of any actual real
detected carrier occurrence. The cyclic single-bond frame compiler supplies the two slots; simple
path freshness makes both leaves real children, and the fixed-point reader supplies their `none`
labels. -/
theorem referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (center : input.certified.TetrahedralCenter)
    (meaning : input.certified.RealTetrahedralCenterNode target.1.node center)
    (leftLeaf rightLeaf : input.certified.Atom)
    (leftNeighbors : input.certified.moleculeGraph.neighborFinset leftLeaf = {center.1})
    (rightNeighbors : input.certified.moleculeGraph.neighborFinset rightLeaf = {center.1})
    (leavesDistinct : leftLeaf ≠ rightLeaf)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (zEq : input.certified.moleculeGraph.atomZ leftLeaf =
      input.certified.moleculeGraph.atomZ rightLeaf)
    (massEq : input.certified.moleculeGraph.atomMass leftLeaf =
      input.certified.moleculeGraph.atomMass rightLeaf) :
    referenceState input target = none := by
  let cert := input.certified
  let fuel := carrierFuel input
  have enough : cert.certified.input.molecule.atomCount ≤ fuel :=
    globalCarrierFuel_adequate input
  obtain ⟨frame, ligand, frameComputed, ligandAt⟩ :=
    cert.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded enough target center meaning
  have rootNeLeft := root_ne_terminalLeaf_of_tetrahedralRoot cert rootTetrahedral leftNeighbors
  have rootNeRight := root_ne_terminalLeaf_of_tetrahedralRoot cert rootTetrahedral rightNeighbors
  obtain ⟨leftIndex, leftCursor, leftAt, leftIncoming, leftCurrent, leftNode,
      leftActual, leftOutward⟩ := exists_actualTerminalLeafSlotCursor cert singleBonded enough
    target center meaning frame frameComputed ligand ligandAt leftLeaf leftNeighbors rootNeLeft
  obtain ⟨rightIndex, rightCursor, rightAt, rightIncoming, rightCurrent, rightNode,
      rightActual, rightOutward⟩ := exists_actualTerminalLeafSlotCursor cert singleBonded enough
    target center meaning frame frameComputed ligand ligandAt rightLeaf rightNeighbors rootNeRight
  have indicesDistinct : leftIndex ≠ rightIndex := by
    intro indexEq
    have sameCurrent : leftCursor.occurrence.1.node.current? =
        rightCursor.occurrence.1.node.current? := by
      rw [← leftAt, ← rightAt, indexEq]
    have sameLeaves : leftLeaf = rightLeaf :=
      Option.some.inj (leftCurrent.symm.trans (sameCurrent.trans rightCurrent))
    exact leavesDistinct sameLeaves
  have targetHead : target.1.node.history.head? = some center.1 :=
    (cert.declarativeLocalizedOccurrence_node_history_head_eq_current
      ((cert.mem_localizedOccurrences_iff fuel target.1).mp target.2)).trans meaning.2
  obtain ⟨tail, historyEq⟩ := List.head?_eq_some_iff.mp targetHead
  have leftParent : leftCursor.occurrence.1.node.parent? = some center.1 := by
    rw [leftNode]
    simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyEq]
  have rightParent : rightCursor.occurrence.1.node.parent? = some center.1 := by
    rw [rightNode]
    simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyEq]
  have leftNonduplicate : leftCursor.occurrence.1.node.isDuplicateLeaf = false :=
    cert.isDuplicateLeaf_eq_false_of_provenance_real leftCursor.occurrence.1.node leftActual.1
  have rightNonduplicate : rightCursor.occurrence.1.node.isDuplicateLeaf = false :=
    cert.isDuplicateLeaf_eq_false_of_provenance_real rightCursor.occurrence.1.node rightActual.1
  have leftBond : cert.moleculeGraph.bond leftLeaf center.1 = 1 :=
    singleBonded leftLeaf center.1
      ((MoleculeGraph.mem_neighborFinset cert.moleculeGraph leftLeaf center.1).mp
        (by rw [leftNeighbors]; simp))
  have rightBond : cert.moleculeGraph.bond rightLeaf center.1 = 1 :=
    singleBonded rightLeaf center.1
      ((MoleculeGraph.mem_neighborFinset cert.moleculeGraph rightLeaf center.1).mp
        (by rw [rightNeighbors]; simp))
  let parentCursor : cert.LocalizedRerootCursor fuel :=
    { occurrence := target, previous? := none }
  obtain ⟨leftSlot, leftAddress⟩ :=
    TerminalTwinAuxiliaryRefusal.exists_address_slot_of_mem_outwardChildFrames cert
      target.1 leftCursor.occurrence.1 leftOutward
  obtain ⟨rightSlot, rightAddress⟩ :=
    TerminalTwinAuxiliaryRefusal.exists_address_slot_of_mem_outwardChildFrames cert
      target.1 rightCursor.occurrence.1 rightOutward
  have leftAddress' : leftCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [leftSlot] := by
    simpa [parentCursor] using leftAddress
  have rightAddress' : rightCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [rightSlot] := by
    simpa [parentCursor] using rightAddress
  have leftTerminal := TerminalTwinAuxiliaryRefusal.physicalLeaf_terminal cert parentCursor
    leftCursor leftLeaf center.1 leftIncoming leftSlot leftAddress' leftActual leftParent
    leftNeighbors leftBond leftNonduplicate
  have rightTerminal := TerminalTwinAuxiliaryRefusal.physicalLeaf_terminal cert parentCursor
    rightCursor rightLeaf center.1 rightIncoming rightSlot rightAddress' rightActual rightParent
    rightNeighbors rightBond rightNonduplicate
  have leftCard : (cert.moleculeGraph.neighborFinset leftLeaf).card ≤ 1 := by
    rw [leftNeighbors]
    simp
  have rightCard : (cert.moleculeGraph.neighborFinset rightLeaf).card ≤ 1 := by
    rw [rightNeighbors]
    simp
  have leftStateNone := referenceState_none_of_actualPhysicalLeaf input singleBonded leftCursor.occurrence
    leftLeaf leftActual leftCard
  have rightStateNone := referenceState_none_of_actualPhysicalLeaf input singleBonded rightCursor.occurrence
    rightLeaf rightActual rightCard
  let view := cert.localizedDependencyView (referenceState input) target
  have leftLabelNone := TerminalTwinAuxiliaryRefusal.localizedDependencyLabel_eq_none_of_state_eq_none
    cert target (referenceState input) leftCursor leftStateNone
  have rightLabelNone := TerminalTwinAuxiliaryRefusal.localizedDependencyLabel_eq_none_of_state_eq_none
    cert target (referenceState input) rightCursor rightStateNone
  have leftBuilt := actualRuleMajorCompound_terminal cert target view leftCursor leftTerminal
    leftLabelNone (localizedOccurrenceRerootEvaluationFuel fuel)
  have rightBuilt := actualRuleMajorCompound_terminal cert target view rightCursor rightTerminal
    rightLabelNone (localizedOccurrenceRerootEvaluationFuel fuel)
  have leftExtendReal : (target.1.node.extend leftLeaf 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [← leftNode]
    exact leftActual.1
  have rightExtendReal : (target.1.node.extend rightLeaf 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [← rightNode]
    exact rightActual.1
  have leftProvenance : target.1.node.childProvenance leftLeaf 0 =
      OfficialCIPNodeProvenance.realAtom := by
    simpa [OfficialCIPNode.extend] using leftExtendReal
  have rightProvenance : target.1.node.childProvenance rightLeaf 0 =
      OfficialCIPNodeProvenance.realAtom := by
    simpa [OfficialCIPNode.extend] using rightExtendReal
  have leftDistance : leftCursor.occurrence.1.node.rule1bRootDistance =
      target.1.node.history.length := by
    rw [leftNode]
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth,
      OfficialCIPNode.extend_history, leftProvenance]
  have rightDistance : rightCursor.occurrence.1.node.rule1bRootDistance =
      target.1.node.history.length := by
    rw [rightNode]
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth,
      OfficialCIPNode.extend_history, rightProvenance]
  have distanceEq := leftDistance.trans rightDistance.symm
  have leftTie := compareRuleMajorOccurrenceAt?_terminal_eq cert target view frame
    leftIndex rightIndex leftCursor rightCursor leftAt rightAt leftBuilt rightBuilt
    leftLeaf rightLeaf leftActual rightActual zEq massEq distanceEq
  have rightTie := compareRuleMajorOccurrenceAt?_terminal_eq cert target view frame
    rightIndex leftIndex rightCursor leftCursor rightAt leftAt rightBuilt leftBuilt
    rightLeaf leftLeaf rightActual leftActual zEq.symm massEq.symm distanceEq.symm
  have centerComputed := (cert.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2
    meaning
  have descriptorNone := ruleMajorDescriptor?_eq_none_of_actualTerminalTwinTie cert target view
    center centerComputed frame frameComputed leftIndex rightIndex indicesDistinct leftTie rightTie
  rw [← reference_fixed input target]
  simpa [view] using descriptorNone

end
end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_none_of_actualPhysicalLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualParent_ne_terminalLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualHistory_avoids_terminalLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_actualOutwardTerminalLeafFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_actualOutwardTerminalLeafCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.exists_actualTerminalLeafSlotCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualRuleMajorCumulative_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualRuleMajorCompound_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualTerminalCompound_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.compareRuleMajorOccurrenceAt?_terminal_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptor?_eq_none_of_actualTerminalTwinTie
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves
