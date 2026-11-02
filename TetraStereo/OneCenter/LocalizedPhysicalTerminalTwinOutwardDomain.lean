import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedTerminalTwinAuxiliaryRefusal

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace CertifiedLocalizedCIPInput

/-! ## Physical parent exclusion

The central observation is that a carrier occurrence's stored parent is the penultimate
atom of a simple physical walk from the original root.  Reversing the walk puts the
stored parent at index one.  If that parent is a physical terminal leaf whose only
neighbour is the current atom, the reverse walk either ends at the leaf with the
original root, or leaves the leaf once more; the latter revisits the current atom,
contradicting simplicity.  No carrier fuel bound is involved: this is a statement about
the physical walk only.

The walk argument is factored out so that the case analysis acts on explicit walk
variables rather than on a walk whose endpoint is a projection of an occurrence. -/

theorem reverseWalk_not_terminalLeaf
    (input : CertifiedLocalizedCIPInput)
    {current root leaf center : input.Atom}
    (q : input.moleculeGraph.underlyingSimpleGraph.Walk current root)
    (qPath : q.IsPath)
    (qSnd : q.snd = leaf)
    (currentEq : current = center)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center})
    (rootNe : root ≠ leaf) : False := by
  by_cases hlen : q.length = 0
  · have hroot : q.snd = root := by
      exact SimpleGraph.Walk.getVert_of_length_le q (by omega)
    exact rootNe (hroot.symm.trans qSnd)
  · have hpos : 0 < q.length := Nat.pos_of_ne_zero hlen
    have qNonNil : ¬ q.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hpos
    have nodupSupport : (current :: q.tail.support).Nodup := by
      rw [SimpleGraph.Walk.cons_support_tail q qNonNil]
      exact qPath.support_nodup
    have currentNotTail : current ∉ q.tail.support :=
      (List.nodup_cons.mp nodupSupport).1
    by_cases htail : q.tail.length = 0
    · have hroot : q.tail.getVert 0 = root :=
        SimpleGraph.Walk.getVert_of_length_le q.tail (by omega)
      have hleaf : q.tail.getVert 0 = leaf := by
        rw [SimpleGraph.Walk.getVert_tail]
        simpa using qSnd
      exact rootNe (hroot.symm.trans hleaf)
    · have htailPos : 0 < q.tail.length := Nat.pos_of_ne_zero htail
      have tailNonNil : ¬ q.tail.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        exact htailPos
      have hleaf : q.tail.getVert 0 = leaf := by
        rw [SimpleGraph.Walk.getVert_tail]
        simpa using qSnd
      have adjLeaf : input.moleculeGraph.underlyingSimpleGraph.Adj leaf q.tail.snd := by
        have h := SimpleGraph.Walk.adj_snd (p := q.tail) tailNonNil
        simpa [hleaf, qSnd] using h
      have innerMem : q.tail.snd ∈ input.moleculeGraph.neighborFinset leaf :=
        (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf q.tail.snd).mpr
          adjLeaf
      rw [leafNeighbors] at innerMem
      have sndEq : q.tail.snd = center := Finset.mem_singleton.mp innerMem
      have currentEqSnd : current = q.tail.snd := currentEq.trans sndEq.symm
      have sndMem : q.tail.snd ∈ q.tail.support :=
        SimpleGraph.Walk.getVert_mem_support q.tail 1
      apply currentNotTail
      rw [← currentEqSnd] at sndMem
      exact sndMem

theorem carrierOccurrence_parent_ne_terminalLeaf
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    {leaf center : input.Atom}
    (currentObserved : occurrence.1.node.current? = some center)
    (parentObserved : occurrence.1.node.parent? = some leaf)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center})
    (rootNe : occurrence.1.root ≠ leaf) : False := by
  obtain ⟨current, path, observed, _head, _provenance, isPath, _supportReverse,
    penultimateObserved⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic occurrence
  have currentEq : current = center :=
    Option.some.inj (observed.symm.trans currentObserved)
  exact reverseWalk_not_terminalLeaf input path.reverse isPath.reverse
    (by
      rw [SimpleGraph.Walk.snd_reverse]
      exact penultimateObserved leaf parentObserved)
    currentEq leafNeighbors rootNe

/-! ## The original root cannot itself be one of the terminal leaves when it is nonleaf -/

/-- An atom with two distinct neighbours cannot be a terminal leaf whose full neighbour set is a
singleton. -/
theorem root_ne_terminalLeaf_of_two_neighbors
    (input : CertifiedLocalizedCIPInput)
    {root leaf center u v : input.Atom}
    (leftAdj : input.moleculeGraph.Adj root u)
    (rightAdj : input.moleculeGraph.Adj root v)
    (different : u ≠ v)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center}) :
    root ≠ leaf := by
  intro rootEqLeaf
  have leftLeaf : input.moleculeGraph.Adj leaf u := rootEqLeaf ▸ leftAdj
  have rightLeaf : input.moleculeGraph.Adj leaf v := rootEqLeaf ▸ rightAdj
  have uMem : u ∈ input.moleculeGraph.neighborFinset leaf :=
    (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf u).mpr leftLeaf
  have vMem : v ∈ input.moleculeGraph.neighborFinset leaf :=
    (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf v).mpr rightLeaf
  rw [leafNeighbors] at uMem vMem
  have uEq : u = center := Finset.mem_singleton.mp uMem
  have vEq : v = center := Finset.mem_singleton.mp vMem
  exact different (uEq.trans vEq.symm)

/-- A root with at least two physical neighbours cannot coincide with a terminal leaf. -/
theorem root_ne_terminalLeaf_of_two_le_neighborCard
    (input : CertifiedLocalizedCIPInput)
    {root leaf center : input.Atom}
    (rootCard : 2 ≤ Fintype.card (input.moleculeGraph.Neighbor root))
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center}) :
    root ≠ leaf := by
  intro rootEqLeaf
  have cardEq : Fintype.card (input.moleculeGraph.Neighbor leaf) =
      (input.moleculeGraph.neighborFinset leaf).card := by
    unfold MoleculeGraph.neighborFinset
    exact Fintype.card_subtype (fun v => input.moleculeGraph.Adj leaf v)
  have leafCard : Fintype.card (input.moleculeGraph.Neighbor leaf) = 1 := by
    rw [cardEq, leafNeighbors]
    simp
  rw [rootEqLeaf] at rootCard
  omega

/-- A tetrahedral original root is in particular not one of the terminal leaves. -/
theorem root_ne_terminalLeaf_of_tetrahedralRoot
    (input : CertifiedLocalizedCIPInput)
    {root leaf center : input.Atom}
    (rootTetrahedral : input.moleculeGraph.IsTetrahedralCenter root)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {center}) :
    root ≠ leaf := by
  refine root_ne_terminalLeaf_of_two_le_neighborCard input ?_ leafNeighbors
  unfold MoleculeGraph.IsTetrahedralCenter at rootTetrahedral
  omega

end CertifiedLocalizedCIPInput

open CertifiedLocalizedCIPInput









theorem referenceState_eq_none_of_physical_terminalTwinLeaves
    (input : LocalizedUniversalReference.Input)
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
    LocalizedUniversalReference.referenceState input target = none := by
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
  exact referenceState_reader_eq_none_of_actualPhysical_terminalTwins
    input noDouble target frame frameComputed leftIndex rightIndex leftCursor rightCursor
    leftAt rightAt leftOutward rightOutward cursorDistinct centerAtom leftAtom rightAtom
    leftActual rightActual leftParentObserved rightParentObserved leftNeighbors rightNeighbors
    leftSingleBond rightSingleBond leftNonduplicate rightNonduplicate zEq massEq distanceEq

/-- Physical nonleaf-root form: if the original root has at least two distinct physical
neighbours, the root-exclusion premise is derived rather than assumed. -/
theorem referenceState_eq_none_of_physical_terminalTwinLeaves_of_rootCard
    (input : LocalizedUniversalReference.Input)
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
    (rootCard : 2 ≤ Fintype.card (input.certified.moleculeGraph.Neighbor target.1.root))
    (zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom)
    (massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom) :
    LocalizedUniversalReference.referenceState input target = none := by
  refine referenceState_eq_none_of_physical_terminalTwinLeaves input singleBonded acyclic
    noDouble target centerAtom leftAtom rightAtom targetCurrent tetrahedral
    leftNeighbors rightNeighbors leftNe ?_ ?_ zEq massEq
  · exact CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_two_le_neighborCard
      input.certified rootCard leftNeighbors
  · exact CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_two_le_neighborCard
      input.certified rootCard rightNeighbors

/-- Tetrahedral-original-root form: the root-exclusion premise is the physical nonleaf
condition that the original root is itself a tetrahedral center. -/
theorem referenceState_eq_none_of_physical_terminalTwinLeaves_of_tetrahedralRoot
    (input : LocalizedUniversalReference.Input)
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
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom)
    (massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom) :
    LocalizedUniversalReference.referenceState input target = none := by
  refine referenceState_eq_none_of_physical_terminalTwinLeaves input singleBonded acyclic
    noDouble target centerAtom leftAtom rightAtom targetCurrent tetrahedral
    leftNeighbors rightNeighbors leftNe ?_ ?_ zEq massEq
  · exact CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_tetrahedralRoot
      input.certified rootTetrahedral leftNeighbors
  · exact CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_tetrahedralRoot
      input.certified rootTetrahedral rightNeighbors

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reverseWalk_not_terminalLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_parent_ne_terminalLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_two_neighbors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_two_le_neighborCard
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.root_ne_terminalLeaf_of_tetrahedralRoot
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_none_of_physical_terminalTwinLeaves
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_none_of_physical_terminalTwinLeaves_of_rootCard
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_none_of_physical_terminalTwinLeaves_of_tetrahedralRoot

end OneCenter
end TetraStereo
