import TetraStereo.OneCenter.LocalizedRerootCompoundOrderedBuilder
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedActualRigidFrameCompleteness
import TetraStereo.OneCenter.LocalizedTerminalTwinAuxiliaryRefusal
import TetraStereo.OneCenter.LocalizedPhysicalTerminalTwinOutwardDomain
import TetraStereo.OneCenter.LocalizedPhysicalLeafModelNone
import TetraStereo.OneCenter.LocalizedNoDoubleWholeStateRule45Bridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000


























namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal
open AcyclicCutBranchAutomorphism

noncomputable section

namespace CertifiedLocalizedCIPInput

/-! ## Rigid frames -/

section Rigid

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)
  (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)

/-- At a constitutionally rigid real centre every pair of slots compares identically under the
ordered and the production keys. -/
theorem compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_of_rigidFrame
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame =
      input.compareLocalizedOccurrenceThroughRule5At? target view frame := by
  funext i j
  have hi := frame.compoundKeyAt_built input target view derived i
  have hj := frame.compoundKeyAt_built input target view derived j
  rw [input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target view frame hi hj,
    input.compareLocalizedOccurrenceThroughRule5At?_of_built target view frame hi hj]
  by_cases hij : i = j
  · subst hij
    rw [compareLocalizedRerootCompoundThroughRule5_self, compareLocalizedRerootCompoundThroughRule5_self]
  · have ne := constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input target view
      frame derived center centerReal rigid hacyc hsimple hcharge enough i j hij
    rw [input.compareThroughRule5_outcomeOrdered45_of_rule4a_ne _ _
      (input.compareLocalizedRerootCumulativeRule45Keys_ne_of_constitutional_ne _ _ ne)]

theorem localizedOccurrenceRule45DescriptorOrdered?_eq_of_rigidFrame
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (center : input.TetrahedralCenter)
    (centerReal : input.RealTetrahedralCenterNode target.1.node center)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph center.1)
    (hacyc : input.moleculeGraph.Acyclic)
    (hsimple : input.moleculeGraph.SimpleBonded)
    (hcharge : ConstantFormalCharge input.moleculeGraph)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    input.localizedOccurrenceRule45DescriptorOrdered? target view =
      input.localizedOccurrenceRule45Descriptor? target view := by
  apply input.localizedOccurrenceRule45DescriptorOrdered?_eq_of_compareAt_eq
  intro frame' hframe'
  cases Option.some.inj (hframe'.symm.trans frameComputed)
  exact input.compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_of_rigidFrame target view frame
    derived center centerReal rigid hacyc hsimple hcharge enough

/-! ## Frames with at most one alternative per slot -/

/-- A built through-Rule-5 key has as many Rule-5 readings as alternatives. -/
theorem rule5Readings_length_of_built {fuel : Nat} {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor = some key) :
    key.rule5Readings.length = key.prior.readings.length := by
  unfold buildLocalizedRerootCompoundRule45Key? at built
  cases hp : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor with
  | none => simp [hp] at built
  | some prior =>
      cases hr : input.buildLocalizedRerootRule5Readings? target view fuel cursor prior.readings with
      | none => simp [hp, hr] at built
      | some readings =>
          simp [hp, hr] at built
          subst built
          exact input.buildLocalizedRerootRule5Readings?_length target view fuel cursor _ hr

theorem compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_of_short
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (short : ∀ i, (frame.compoundKeyAt input target view derived i).prior.readings.length ≤ 1) :
    input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame =
      input.compareLocalizedOccurrenceThroughRule5At? target view frame := by
  funext i j
  have hi := frame.compoundKeyAt_built input target view derived i
  have hj := frame.compoundKeyAt_built input target view derived j
  rw [input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target view frame hi hj,
    input.compareLocalizedOccurrenceThroughRule5At?_of_built target view frame hi hj,
    input.outcomeOrdered45_eq_self_of_length_le_one _ (short i)
      (by rw [input.rule5Readings_length_of_built target view hi]; exact short i),
    input.outcomeOrdered45_eq_self_of_length_le_one _ (short j)
      (by rw [input.rule5Readings_length_of_built target view hj]; exact short j)]

theorem localizedOccurrenceRule45DescriptorOrdered?_eq_of_short
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (short : ∀ i, (frame.compoundKeyAt input target view derived i).prior.readings.length ≤ 1) :
    input.localizedOccurrenceRule45DescriptorOrdered? target view =
      input.localizedOccurrenceRule45Descriptor? target view := by
  apply input.localizedOccurrenceRule45DescriptorOrdered?_eq_of_compareAt_eq
  intro frame' hframe'
  cases Option.some.inj (hframe'.symm.trans frameComputed)
  exact input.compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_of_short target view frame derived
    short

end Rigid

/-! ## Terminal twins: the ordered refusal -/

section Twins

variable (input : CertifiedLocalizedCIPInput) {fuel : Nat}

theorem outcomeOrdered45_terminalCompound45 (node : OfficialCIPNode input.Atom) :
    input.outcomeOrdered45 (terminalCompound45 input node) = terminalCompound45 input node :=
  input.outcomeOrdered45_eq_self_of_length_le_one _ (le_refl 1) (le_refl 1)



theorem localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_actualPhysical_terminalTwins
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (leftIndex rightIndex : Fin 4)
    (leftCursor rightCursor : input.LocalizedRerootCursor fuel)
    (leftAt : frame.cursorAt leftIndex = leftCursor)
    (rightAt : frame.cursorAt rightIndex = rightCursor)
    (leftOutward : leftCursor.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) target.1)
    (rightOutward : rightCursor.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) target.1)
    (cursorDistinct : leftCursor ≠ rightCursor)
    (centerAtom leftAtom rightAtom : input.Atom)
    (leftActual : input.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom)
    (rightActual : input.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom)
    (leftParentObserved : leftCursor.occurrence.1.node.parent? = some centerAtom)
    (rightParentObserved : rightCursor.occurrence.1.node.parent? = some centerAtom)
    (leftNeighbors : input.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftSingleBond : input.moleculeGraph.bond leftAtom centerAtom = 1)
    (rightSingleBond : input.moleculeGraph.bond rightAtom centerAtom = 1)
    (leftNonduplicate : leftCursor.occurrence.1.node.isDuplicateLeaf = false)
    (rightNonduplicate : rightCursor.occurrence.1.node.isDuplicateLeaf = false)
    (zEq : input.moleculeGraph.atomZ leftAtom = input.moleculeGraph.atomZ rightAtom)
    (massEq : input.moleculeGraph.atomMass leftAtom = input.moleculeGraph.atomMass rightAtom)
    (distanceEq : leftCursor.occurrence.1.node.rule1bRootDistance =
      rightCursor.occurrence.1.node.rule1bRootDistance) :
    input.localizedOccurrenceRule45DescriptorOrdered? target
      (input.localizedDependencyView state target) = none := by
  let parentCursor : input.LocalizedRerootCursor fuel :=
    { occurrence := target, previous? := none }
  have leftIncomingFrame := cursorAt_previous_eq_target_of_frame
    input target frame frameComputed leftIndex
  rw [leftAt] at leftIncomingFrame
  have rightIncomingFrame := cursorAt_previous_eq_target_of_frame
    input target frame frameComputed rightIndex
  rw [rightAt] at rightIncomingFrame
  obtain ⟨leftSlot, leftAddress⟩ :=
    exists_address_slot_of_mem_outwardChildFrames input target.1 leftCursor.occurrence.1
      leftOutward
  obtain ⟨rightSlot, rightAddress⟩ :=
    exists_address_slot_of_mem_outwardChildFrames input target.1 rightCursor.occurrence.1
      rightOutward
  have leftAddress' : leftCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [leftSlot] := by
    simpa [parentCursor] using leftAddress
  have rightAddress' : rightCursor.occurrence.1.address =
      parentCursor.occurrence.1.address ++ [rightSlot] := by
    simpa [parentCursor] using rightAddress
  have leftTerminal := physicalLeaf_terminal input parentCursor leftCursor leftAtom centerAtom
    leftIncomingFrame leftSlot leftAddress' leftActual leftParentObserved leftNeighbors
    leftSingleBond leftNonduplicate
  have rightTerminal := physicalLeaf_terminal input parentCursor rightCursor rightAtom centerAtom
    rightIncomingFrame rightSlot rightAddress' rightActual rightParentObserved rightNeighbors
    rightSingleBond rightNonduplicate
  have leftCard : (input.moleculeGraph.neighborFinset leftAtom).card ≤ 1 := by
    rw [leftNeighbors]
    simp
  have rightCard : (input.moleculeGraph.neighborFinset rightAtom).card ≤ 1 := by
    rw [rightNeighbors]
    simp
  have leftLabelNone := localizedDependencyLabel_eq_none_of_physicalLeaf input target
    leftCursor leftAtom leftActual leftCard state model
  have rightLabelNone := localizedDependencyLabel_eq_none_of_physicalLeaf input target
    rightCursor rightAtom rightActual rightCard state model
  have leftComputed := buildCompound45?_terminal_actual input target
    (input.localizedDependencyView state target) leftCursor leftTerminal leftLabelNone
    (localizedOccurrenceRerootEvaluationFuel fuel)
  have rightComputed := buildCompound45?_terminal_actual input target
    (input.localizedDependencyView state target) rightCursor rightTerminal rightLabelNone
    (localizedOccurrenceRerootEvaluationFuel fuel)
  have labelEq := officialNodeAtomLabel_eq_of_actualPhysical_z_mass input
    leftCursor.occurrence.1.node rightCursor.occurrence.1.node leftAtom rightAtom
    leftActual rightActual zEq massEq
  have constitutionalEq :=
    TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
      input leftCursor rightCursor labelEq distanceEq
  have constitutionalEqSymm :=
    TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
      input rightCursor leftCursor labelEq.symm distanceEq.symm
  have leftBuilt : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) (localizedOccurrenceRerootEvaluationFuel fuel)
      (frame.cursorAt leftIndex) = some (terminalCompound45 input leftCursor.occurrence.1.node) := by
    rw [leftAt]; exact leftComputed
  have rightBuilt : input.buildLocalizedRerootCompoundRule45Key? target
      (input.localizedDependencyView state target) (localizedOccurrenceRerootEvaluationFuel fuel)
      (frame.cursorAt rightIndex) = some (terminalCompound45 input rightCursor.occurrence.1.node) := by
    rw [rightAt]; exact rightComputed
  have leftRightTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5OrderedAt? target
        (input.localizedDependencyView state target) frame leftIndex rightIndex = some result ∧
        result.ordering = Ordering.eq := by
    refine ⟨_, input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target _ frame
      leftBuilt rightBuilt, ?_⟩
    rw [input.outcomeOrdered45_terminalCompound45, input.outcomeOrdered45_terminalCompound45]
    dsimp only [localizedOccurrenceRule45ComparisonRecord]
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    exact terminalCompound45_compare_eq input _ _ constitutionalEq
  have rightLeftTie : ∃ result,
      input.compareLocalizedOccurrenceThroughRule5OrderedAt? target
        (input.localizedDependencyView state target) frame rightIndex leftIndex = some result ∧
        result.ordering = Ordering.eq := by
    refine ⟨_, input.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built target _ frame
      rightBuilt leftBuilt, ?_⟩
    rw [input.outcomeOrdered45_terminalCompound45, input.outcomeOrdered45_terminalCompound45]
    dsimp only [localizedOccurrenceRule45ComparisonRecord]
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    exact terminalCompound45_compare_eq input _ _ constitutionalEqSymm
  have indexDistinct : leftIndex ≠ rightIndex := by
    intro same
    apply cursorDistinct
    rw [← leftAt, ← rightAt, same]
  have safeNone : input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target
      (input.localizedDependencyView state target) frame = none :=
    safeTrackedOrderOf_eq_none_of_tie _ indexDistinct leftRightTie rightLeftTie
  exact input.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_safe_eq_none target _ frame
    frameComputed safeNone

end Twins

end CertifiedLocalizedCIPInput



section TwinSlots

variable (input : LocalizedUniversalReference.Input)



theorem exists_terminalTwinSlots
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (centerAtom leftAtom rightAtom : input.certified.Atom)
    (targetCurrent : target.1.node.current? = some centerAtom)
    (tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter centerAtom)
    (leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftNe : leftAtom ≠ rightAtom)
    (rootNeLeft : target.1.root ≠ leftAtom)
    (rootNeRight : target.1.root ≠ rightAtom) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
          (LocalizedUniversalReference.carrierFuel input))
      (_frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame)
      (leftIndex rightIndex : Fin 4)
      (leftCursor rightCursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      frame.cursorAt leftIndex = leftCursor ∧
      frame.cursorAt rightIndex = rightCursor ∧
      leftCursor.occurrence.1 ∈ input.certified.localizedCarrierOutwardChildFrames
        (fuel := LocalizedUniversalReference.carrierFuel input) target.1 ∧
      rightCursor.occurrence.1 ∈ input.certified.localizedCarrierOutwardChildFrames
        (fuel := LocalizedUniversalReference.carrierFuel input) target.1 ∧
      leftCursor ≠ rightCursor ∧
      input.certified.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom ∧
      input.certified.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom ∧
      leftCursor.occurrence.1.node.parent? = some centerAtom ∧
      rightCursor.occurrence.1.node.parent? = some centerAtom ∧
      input.certified.moleculeGraph.bond leftAtom centerAtom = 1 ∧
      input.certified.moleculeGraph.bond rightAtom centerAtom = 1 ∧
      leftCursor.occurrence.1.node.isDuplicateLeaf = false ∧
      rightCursor.occurrence.1.node.isDuplicateLeaf = false ∧
      leftCursor.occurrence.1.node.rule1bRootDistance =
        rightCursor.occurrence.1.node.rule1bRootDistance := by
  classical
  let cert := input.certified
  let fuel := LocalizedUniversalReference.carrierFuel input
  have enough : cert.certified.input.molecule.atomCount ≤ fuel := by
    dsimp [fuel, cert, LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
      LocalizedReference.Input.molecule]
    omega
  obtain ⟨frame, frameComputed⟩ :=
    cert.exists_localizedOccurrenceFourLigandFrame_of_tetrahedral
      singleBonded acyclic enough target targetCurrent tetrahedral
  have targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    cert.carrierOccurrence_provenance_real singleBonded acyclic target
  have adjCenterLeft : cert.moleculeGraph.Adj centerAtom leftAtom := by
    have leftMem : centerAtom ∈ cert.moleculeGraph.neighborFinset leftAtom := by
      rw [leftNeighbors]
      simp
    exact (MoleculeGraph.adj_symm cert.moleculeGraph).mp
      ((MoleculeGraph.mem_neighborFinset cert.moleculeGraph leftAtom centerAtom).mp
        leftMem)
  have adjCenterRight : cert.moleculeGraph.Adj centerAtom rightAtom := by
    have rightMem : centerAtom ∈ cert.moleculeGraph.neighborFinset rightAtom := by
      rw [rightNeighbors]
      simp
    exact (MoleculeGraph.adj_symm cert.moleculeGraph).mp
      ((MoleculeGraph.mem_neighborFinset cert.moleculeGraph rightAtom centerAtom).mp
        rightMem)
  have notParentLeft : target.1.node.parent? ≠ some leftAtom := by
    intro parentObserved
    exact cert.carrierOccurrence_parent_ne_terminalLeaf singleBonded acyclic target
      targetCurrent parentObserved leftNeighbors rootNeLeft
  have notParentRight : target.1.node.parent? ≠ some rightAtom := by
    intro parentObserved
    exact cert.carrierOccurrence_parent_ne_terminalLeaf singleBonded acyclic target
      targetCurrent parentObserved rightNeighbors rootNeRight
  obtain ⟨frameLeft, slotLeft, addrLeft, rootLeft, currentLeft, nodeLeft,
    memCarrierLeft, outwardLeft⟩ :=
    cert.carrierChildFrame_of_adjacent_notParent singleBonded acyclic enough target
      targetCurrent adjCenterLeft notParentLeft targetReal
  obtain ⟨frameRight, slotRight, addrRight, rootRight, currentRight, nodeRight,
    memCarrierRight, outwardRight⟩ :=
    cert.carrierChildFrame_of_adjacent_notParent singleBonded acyclic enough target
      targetCurrent adjCenterRight notParentRight targetReal
  let rootCursor : cert.LocalizedRerootCursor fuel :=
    { occurrence := target, previous? := none }
  have declarativeFrame :=
    cert.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  have ligandComputed : cert.localizedOccurrenceLigandFrame? target = some frame.cursors :=
    (cert.localizedOccurrenceLigandFrame?_eq_some_iff target frame.cursors).mpr
      declarativeFrame.1
  have childrenComputed : cert.localizedRerootChildren? rootCursor = some frame.cursors := by
    simpa [rootCursor, localizedOccurrenceLigandFrame?] using ligandComputed
  have rootCurrent : rootCursor.occurrence.1.node.current? = some centerAtom := by
    simpa [rootCursor] using targetCurrent
  have neighborIff :=
    cert.localizedRerootChildren?_current_iff_adjacent_root singleBonded acyclic enough
      rootCursor rfl rootCurrent frame.cursors childrenComputed
  obtain ⟨leftCursor, leftMem, leftCurrent⟩ :=
    (neighborIff leftAtom).mpr adjCenterLeft
  obtain ⟨rightCursor, rightMem, rightCurrent⟩ :=
    (neighborIff rightAtom).mpr adjCenterRight
  have leftRoot : leftCursor.occurrence.1.root = target.1.root := by
    have rootEq := cert.localizedRerootChildren_root_eq rootCursor leftCursor
      frame.cursors declarativeFrame.1 leftMem
    simpa [rootCursor] using rootEq
  have rightRoot : rightCursor.occurrence.1.root = target.1.root := by
    have rootEq := cert.localizedRerootChildren_root_eq rootCursor rightCursor
      frame.cursors declarativeFrame.1 rightMem
    simpa [rootCursor] using rootEq
  have leftOccEq : leftCursor.occurrence = ⟨frameLeft, memCarrierLeft⟩ :=
    cert.localizedCIPOccurrence_current_injective_at_fixedRoot singleBonded acyclic
      leftCursor.occurrence ⟨frameLeft, memCarrierLeft⟩
      (leftRoot.trans rootLeft.symm) (leftCurrent.trans currentLeft.symm)
  have rightOccEq : rightCursor.occurrence = ⟨frameRight, memCarrierRight⟩ :=
    cert.localizedCIPOccurrence_current_injective_at_fixedRoot singleBonded acyclic
      rightCursor.occurrence ⟨frameRight, memCarrierRight⟩
      (rightRoot.trans rootRight.symm) (rightCurrent.trans currentRight.symm)
  have leftVal : leftCursor.occurrence.1 = frameLeft := congrArg Subtype.val leftOccEq
  have rightVal : rightCursor.occurrence.1 = frameRight := congrArg Subtype.val rightOccEq
  have leftOutward : leftCursor.occurrence.1 ∈
      cert.localizedCarrierOutwardChildFrames (fuel := fuel) target.1 := by
    rw [leftVal]
    exact outwardLeft
  have rightOutward : rightCursor.occurrence.1 ∈
      cert.localizedCarrierOutwardChildFrames (fuel := fuel) target.1 := by
    rw [rightVal]
    exact outwardRight
  have leftActual : cert.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom := by
    refine ⟨?_, leftCurrent⟩
    rw [leftVal]
    exact cert.carrierOccurrence_provenance_real singleBonded acyclic
      ⟨frameLeft, memCarrierLeft⟩
  have rightActual : cert.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom := by
    refine ⟨?_, rightCurrent⟩
    rw [rightVal]
    exact cert.carrierOccurrence_provenance_real singleBonded acyclic
      ⟨frameRight, memCarrierRight⟩
  have targetHead : target.1.node.history.head? = some centerAtom :=
    (cert.declarativeLocalizedOccurrence_node_history_head_eq_current
      ((cert.mem_localizedOccurrences_iff fuel target.1).mp target.2)).trans targetCurrent
  obtain ⟨tail, historyEq⟩ := List.head?_eq_some_iff.mp targetHead
  have leftParentObserved : leftCursor.occurrence.1.node.parent? = some centerAtom := by
    rw [leftVal, nodeLeft]
    simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyEq]
  have rightParentObserved : rightCursor.occurrence.1.node.parent? = some centerAtom := by
    rw [rightVal, nodeRight]
    simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyEq]
  have leftNonduplicate : leftCursor.occurrence.1.node.isDuplicateLeaf = false :=
    cert.carrierOccurrence_not_duplicateLeaf singleBonded acyclic leftCursor.occurrence
  have rightNonduplicate : rightCursor.occurrence.1.node.isDuplicateLeaf = false :=
    cert.carrierOccurrence_not_duplicateLeaf singleBonded acyclic rightCursor.occurrence
  have leftSingleBond : cert.moleculeGraph.bond leftAtom centerAtom = 1 :=
    singleBonded leftAtom centerAtom
      ((MoleculeGraph.adj_symm cert.moleculeGraph).mp adjCenterLeft)
  have rightSingleBond : cert.moleculeGraph.bond rightAtom centerAtom = 1 :=
    singleBonded rightAtom centerAtom
      ((MoleculeGraph.adj_symm cert.moleculeGraph).mp adjCenterRight)
  have leftExtendReal : (target.1.node.extend leftAtom 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [← nodeLeft]
    exact cert.carrierOccurrence_provenance_real singleBonded acyclic
      ⟨frameLeft, memCarrierLeft⟩
  have rightExtendReal : (target.1.node.extend rightAtom 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [← nodeRight]
    exact cert.carrierOccurrence_provenance_real singleBonded acyclic
      ⟨frameRight, memCarrierRight⟩
  have leftProvenance : target.1.node.childProvenance leftAtom 0 =
      OfficialCIPNodeProvenance.realAtom := by
    simpa [OfficialCIPNode.extend] using leftExtendReal
  have rightProvenance : target.1.node.childProvenance rightAtom 0 =
      OfficialCIPNodeProvenance.realAtom := by
    simpa [OfficialCIPNode.extend] using rightExtendReal
  have leftDistance : leftCursor.occurrence.1.node.rule1bRootDistance =
      target.1.node.history.length := by
    rw [leftVal, nodeLeft]
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth,
      OfficialCIPNode.extend_history, leftProvenance]
  have rightDistance : rightCursor.occurrence.1.node.rule1bRootDistance =
      target.1.node.history.length := by
    rw [rightVal, nodeRight]
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth,
      OfficialCIPNode.extend_history, rightProvenance]
  have distanceEq : leftCursor.occurrence.1.node.rule1bRootDistance =
      rightCursor.occurrence.1.node.rule1bRootDistance :=
    leftDistance.trans rightDistance.symm
  have cursorDistinct : leftCursor ≠ rightCursor := by
    intro cursorEq
    have sameCurrent : leftCursor.occurrence.1.node.current? =
        rightCursor.occurrence.1.node.current? := by
      rw [cursorEq]
    have : leftAtom = rightAtom :=
      Option.some.inj (leftCurrent.symm.trans (sameCurrent.trans rightCurrent))
    exact leftNe this
  obtain ⟨leftFin, leftGet⟩ := List.mem_iff_get.mp leftMem
  obtain ⟨rightFin, rightGet⟩ := List.mem_iff_get.mp rightMem
  let leftIndex : Fin 4 := Fin.cast frame.length_eq leftFin
  let rightIndex : Fin 4 := Fin.cast frame.length_eq rightFin
  have leftAt : frame.cursorAt leftIndex = leftCursor := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    dsimp only [leftIndex]
    rw [show Fin.cast frame.length_eq.symm (Fin.cast frame.length_eq leftFin) = leftFin by
      exact Fin.ext rfl]
    exact leftGet
  have rightAt : frame.cursorAt rightIndex = rightCursor := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    dsimp only [rightIndex]
    rw [show Fin.cast frame.length_eq.symm (Fin.cast frame.length_eq rightFin) = rightFin by
      exact Fin.ext rfl]
    exact rightGet
  exact ⟨frame, frameComputed, leftIndex, rightIndex, leftCursor, rightCursor, leftAt, rightAt,
    leftOutward, rightOutward, cursorDistinct, leftActual, rightActual, leftParentObserved,
    rightParentObserved, leftSingleBond, rightSingleBond, leftNonduplicate, rightNonduplicate,
    distanceEq⟩

/-- The ordered bare descriptor refuses at a terminal-twin centre on the generated reference
state's view (the atom-level form of the ordered refusal). -/
theorem localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_physical_terminalTwinLeaves
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (centerAtom leftAtom rightAtom : input.certified.Atom)
    (targetCurrent : target.1.node.current? = some centerAtom)
    (tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter centerAtom)
    (leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftNe : leftAtom ≠ rightAtom)
    (rootNeLeft : target.1.root ≠ leftAtom)
    (rootNeRight : target.1.root ≠ rightAtom)
    (zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom)
    (massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom) :
    input.certified.localizedOccurrenceRule45DescriptorOrdered? target
      (input.certified.localizedDependencyView (LocalizedUniversalReference.referenceState input)
        target) = none := by
  obtain ⟨frame, frameComputed, leftIndex, rightIndex, leftCursor, rightCursor, leftAt, rightAt,
    leftOutward, rightOutward, cursorDistinct, leftActual, rightActual, leftParentObserved,
    rightParentObserved, leftSingleBond, rightSingleBond, leftNonduplicate, rightNonduplicate,
    distanceEq⟩ :=
    exists_terminalTwinSlots input singleBonded acyclic target centerAtom leftAtom rightAtom
      targetCurrent tetrahedral leftNeighbors rightNeighbors leftNe rootNeLeft rootNeRight
  exact localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_actualPhysical_terminalTwins
    input.certified target (LocalizedUniversalReference.referenceState input)
    (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords input noDouble)
    frame frameComputed leftIndex rightIndex leftCursor rightCursor leftAt rightAt leftOutward
    rightOutward cursorDistinct centerAtom leftAtom rightAtom leftActual rightActual
    leftParentObserved rightParentObserved leftNeighbors rightNeighbors leftSingleBond
    rightSingleBond leftNonduplicate rightNonduplicate zEq massEq distanceEq

end TwinSlots

/-! ## Agreement at every actual strict dependency of the final occurrence -/

section Dependency

variable (input : LocalizedUniversalReference.Input)

/-- The production bare descriptor at the generated state's view is the generated state. -/
theorem localizedOccurrenceRule45Descriptor?_referenceState
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input) :
    input.certified.localizedOccurrenceRule45Descriptor? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) =
      LocalizedUniversalReference.referenceState input target :=
  (input.certified.declarativeLocalizedOccurrenceRule45Outcome_iff _ target _).1
    (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords input noDouble
      target)

/-- **Per-dependency agreement.**  On the general rigid / terminal-twin physical domain, at every
actual strict dependency of the final occurrence of the root, the ordered and the production bare
descriptors agree on the generated reference state's view. -/
theorem orderedDescriptor_eq_descriptor_of_strictDependency
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1)
    (target : LocalizedUniversalReference.Occurrence input)
    (dependency : input.certified.LocalizedDepthDependency target
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    input.certified.localizedOccurrenceRule45DescriptorOrdered? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) =
      input.certified.localizedOccurrenceRule45Descriptor? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    dsimp [LocalizedUniversalReference.carrierFuel, LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.carrierFuel, LocalizedReference.Input.molecule]
    omega
  have finalRoot : target.1.root = topCenter.1 := by
    rw [dependency.1]
    exact AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
      (LocalizedUniversalReference.carrierFuel input) topCenter
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root := by
    rw [finalRoot]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet topCenter.1).mp topCenter.2
  rcases actualStrictDependency_classification_generalRigid input singleBonded acyclic hcharge
      noDouble cfg root domain topCenter topAt
      ({ occurrence := target, previous? := none } : input.certified.LocalizedRerootCursor _)
      dependency with
    ⟨⟨atom, current, notMem⟩, _⟩ | ⟨twinLeaves, stateNone⟩ | ⟨center, readback⟩
  · have hcenter := input.certified.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target atom current notMem
    rw [input.certified.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_center_none _ _
      hcenter, input.certified.localizedOccurrenceRule45Descriptor?_eq_none_of_center_none _ _
      hcenter]
  · obtain ⟨centerAtom, leftAtom, rightAtom, current, tetrahedral, leftNeighbors, rightNeighbors,
      leftNe, zEq, massEq, _⟩ := twinLeaves
    have rootNeLeft : target.1.root ≠ leftAtom :=
      root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral leftNeighbors
    have rootNeRight : target.1.root ≠ rightAtom :=
      root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral rightNeighbors
    rw [localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_physical_terminalTwinLeaves input
      singleBonded acyclic noDouble target centerAtom leftAtom rightAtom current tetrahedral
      leftNeighbors rightNeighbors leftNe rootNeLeft rootNeRight zEq massEq,
      localizedOccurrenceRule45Descriptor?_referenceState input noDouble target, stateNone]
  · obtain ⟨_rs, _tracked, frame, _alpha, _pointAt, current, _notTwin, calibrated, frameComputed,
      _ligandLink, _spatial, _observed, _calibration, _trackedOrder, _pseudo, _state, _sign⟩ :=
      readback
    exact input.certified.localizedOccurrenceRule45DescriptorOrdered?_eq_of_rigidFrame target _
      frame (input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed)
      frameComputed center
      ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target, current⟩
      (constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
        ⟨center.1, center.2⟩ calibrated.1)
      acyclic singleBonded hcharge enough

end Dependency

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_eq_of_rigidFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_eq_of_short
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_actualPhysical_terminalTwins
assert_kernel_only TetraStereo.OneCenter.exists_terminalTwinSlots
assert_kernel_only TetraStereo.OneCenter.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_physical_terminalTwinLeaves
assert_kernel_only TetraStereo.OneCenter.orderedDescriptor_eq_descriptor_of_strictDependency
