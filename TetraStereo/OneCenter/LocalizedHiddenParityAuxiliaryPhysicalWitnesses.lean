import TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse
import TetraStereo.OneCenter.LocalizedRetainedArmExpansion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

namespace TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open scoped Classical

noncomputable section

/-- A history refusal witness directly supplies a proper retained-context branch transport.
The explicit slot witnesses preserve the actual outward-frame condition, so this is the same
construction used inside `referenceState_none_of_historyWitness`, exposed as a reusable result. -/
theorem historyWitness_to_properAuxiliaryTransport
    {input : Input} {target : Occurrence input}
    {unit : DetectedOccurrence input.certified.moleculeGraph}
    {unitEq : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit unitEq)
    (nonroot : target.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (witness : HistoryRefusalWitness input cfg target.1.node.history frames.center.1) :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : input.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ cfg a b false := by
  obtain ⟨σ, s, t, distinctST, adjS, adjT, freshS, freshT, historyFixed, sentST, law⟩ := witness
  obtain ⟨a, ligandA, outwardA⟩ := outwardSlot_of_fresh frames nonroot s adjS freshS
  obtain ⟨b, ligandB, outwardB⟩ := outwardSlot_of_fresh frames nonroot t adjT freshT
  have slotsDistinct : a ≠ b := by
    intro same
    apply distinctST
    rw [← ligandA, ← ligandB, same]
  have transport : AuxiliaryBranchTransport frames σ cfg a b false :=
    { historyFixed := historyFixed
      ligandSent := by rw [ligandA, ligandB]; exact sentST
      componentLaw := by
        intro d component
        rw [ligandA] at component
        rw [law d component]
        simp [physicalMirrorFactor] }
  exact ⟨a, b, slotsDistinct, outwardA, outwardB, σ, transport⟩

/-- Compile the actual context frame of a real detected occurrence, then turn its history witness
into a proper auxiliary transport. -/
theorem actualHistoryWitness_to_properAuxiliaryTransport
    {input : Input} {target : Occurrence input}
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom)
    (nonroot : target.1.address ≠ [])
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    {a : input.certified.Atom} {h : List input.certified.Atom}
    (history : target.1.node.history = h)
    (current : target.1.node.current? = some a)
    (witness : HistoryRefusalWitness input cfg h a) :
    let unit : DetectedOccurrence input.certified.moleculeGraph :=
      ⟨input.certified.molecularFrameUnit target.1, detected⟩
    let frames : ContextFrameCompilation input target unit rfl :=
      cyclicContextFrameCompilation input singleBonded target real unit rfl
    ∃ x y : Fin 4, x ≠ y ∧
      IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt x) ∧
      IsLocalizedActualFrameOutwardCursor input.certified target (frames.frame.cursorAt y) ∧
      ∃ σ : input.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ cfg x y false := by
  let unit : DetectedOccurrence input.certified.moleculeGraph :=
    ⟨input.certified.molecularFrameUnit target.1, detected⟩
  let frames : ContextFrameCompilation input target unit rfl :=
    cyclicContextFrameCompilation input singleBonded target real unit rfl
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target frames.center).mp frames.centerComputed
  have centerEq : frames.center.1 = a :=
    Option.some.inj (centerMeaning.2.symm.trans current)
  have actualWitness : HistoryRefusalWitness input cfg target.1.node.history frames.center.1 := by
    rw [history, centerEq]
    exact witness
  exact historyWitness_to_properAuxiliaryTransport frames nonroot cfg actualWitness

/-- Predicate for a proper transport in the cyclic frame of an actual real detected occurrence. -/
def ActualProperTransportAt (target : Occurrence decReference)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter decReference.certified.moleculeGraph
      (decReference.certified.molecularFrameUnit target.1).atom) : Prop :=
  let unit : DetectedOccurrence decReference.certified.moleculeGraph :=
    ⟨decReference.certified.molecularFrameUnit target.1, detected⟩
  let frames : ContextFrameCompilation decReference target unit rfl :=
    cyclicContextFrameCompilation decReference simple_bonded target real unit rfl
  ∃ a b : Fin 4, a ≠ b ∧
    IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
    IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
    ∃ σ : decReference.certified.moleculeGraph.Aut,
      AuxiliaryBranchTransport frames σ detectedCfg a b false

/-- A concrete strict outward carrier coordinate is an executable reroot edge. The proof uses the
shared finite carrier and address grading; it does not evaluate the reference-state reader. -/
theorem actualOutwardEdge
    (source : decReference.certified.LocalizedRerootCursor (carrierFuel decReference))
    (previous : Occurrence decReference)
    (previousEq : source.previous? = some previous)
    (shorter : previous.1.address.length < source.occurrence.1.address.length)
    (child : Occurrence decReference) (rootEq : child.1.root = source.occurrence.1.root)
    (addressEq : child.1.address = source.occurrence.1.address ++ [0] \/
      ∃ slot : Nat, child.1.address = source.occurrence.1.address ++ [slot])
    (sourceReal : source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    (⟨child, some source.occurrence⟩ :
      decReference.certified.LocalizedRerootCursor (carrierFuel decReference)) ∈
        decReference.certified.executableLocalizedRerootChildren source := by
  have childStep : ∃ slot : Nat,
      child.1.address = source.occurrence.1.address ++ [slot] := by
    rcases addressEq with h | ⟨slot, h⟩
    · exact ⟨0, h⟩
    · exact ⟨slot, h⟩
  obtain ⟨slot, addressEq⟩ := childStep
  have treeAdjacent : decReference.certified.LocalizedCarrierTreeAdjacent
      child.1 source.occurrence.1 := by
    refine ⟨rootEq, Or.inr ⟨?_, ?_⟩⟩
    · rw [addressEq]
      simp
    · rw [addressEq]
      simp
  have neighbor : child.1 ∈ decReference.certified.localizedRerootNeighborFrames
      (fuel := carrierFuel decReference) source.occurrence.1 :=
    (decReference.certified.mem_localizedRerootNeighborFrames_iff
      source.occurrence.1 child.1).mpr ⟨child.2, treeAdjacent⟩
  have previousNe : child.1.address ≠ previous.1.address := by
    intro same
    have lengths := congrArg List.length same
    rw [addressEq] at lengths
    simp at lengths
    omega
  have intended : child.1 ∈ decReference.certified.intendedLocalizedRerootChildFrames source := by
    unfold CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames
    simp only [sourceReal, OfficialCIPNode.isDuplicateLeaf,
      OfficialCIPNodeProvenance.isDuplicateLeaf_realAtom, Bool.false_eq_true, ↓reduceIte]
    rw [previousEq]
    exact List.mem_filter.mpr ⟨neighbor, by simpa using previousNe⟩
  rw [decReference.certified.executableLocalizedRerootChildren_mem_iff]
  exact ⟨rfl, intended⟩

/-! The next four adapters name the actual 21-atom hidden-parity source histories. They take an
actual compiled context frame for the occurrence, and preserve the supported outward slots in the
conclusion. The source witnesses themselves are the accepted bridge 3-cycle and far-bridge swap
certificates; no carrier or state evaluation is performed here. -/

theorem attachmentA_cycle_transport
    {target : Occurrence decReference}
    {unit : DetectedOccurrence decReference.certified.moleculeGraph}
    {unitEq : decReference.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation decReference target unit unitEq)
    (nonroot : target.1.address ≠ [])
    (history : target.1.node.history = ([6, 3, 0] : List (Fin 21)))
    (center : frames.center.1 = (6 : Fin 21)) :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  have w : HistoryRefusalWitness decReference detectedCfg target.1.node.history frames.center.1 := by
    rw [history, center]
    exact LocalizedRecursiveAuxiliaryParityDecoration.cycleWitnessA
  exact historyWitness_to_properAuxiliaryTransport frames nonroot detectedCfg w

theorem attachmentB_cycle_transport
    {target : Occurrence decReference}
    {unit : DetectedOccurrence decReference.certified.moleculeGraph}
    {unitEq : decReference.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation decReference target unit unitEq)
    (nonroot : target.1.address ≠ [])
    (history : target.1.node.history = ([15, 12, 0] : List (Fin 21)))
    (center : frames.center.1 = (15 : Fin 21)) :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  have w : HistoryRefusalWitness decReference detectedCfg target.1.node.history frames.center.1 := by
    rw [history, center]
    exact LocalizedRecursiveAuxiliaryParityDecoration.cycleWitnessB
  exact historyWitness_to_properAuxiliaryTransport frames nonroot detectedCfg w

theorem farA_swap_transport
    {target : Occurrence decReference}
    {unit : DetectedOccurrence decReference.certified.moleculeGraph}
    {unitEq : decReference.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation decReference target unit unitEq)
    (nonroot : target.1.address ≠ []) (o : Fin 21) (ho : o ∈ [8, 9, 10])
    (history : target.1.node.history = ([11, o, 6, 3, 0] : List (Fin 21)))
    (center : frames.center.1 = (11 : Fin 21)) :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  have w : HistoryRefusalWitness decReference detectedCfg target.1.node.history frames.center.1 := by
    rw [history, center]
    exact LocalizedRecursiveAuxiliaryParityDecoration.swapWitnessA o ho
  exact historyWitness_to_properAuxiliaryTransport frames nonroot detectedCfg w

theorem farB_swap_transport
    {target : Occurrence decReference}
    {unit : DetectedOccurrence decReference.certified.moleculeGraph}
    {unitEq : decReference.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation decReference target unit unitEq)
    (nonroot : target.1.address ≠ []) (o : Fin 21) (ho : o ∈ [17, 18, 19])
    (history : target.1.node.history = ([20, o, 15, 12, 0] : List (Fin 21)))
    (center : frames.center.1 = (20 : Fin 21)) :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  have w : HistoryRefusalWitness decReference detectedCfg target.1.node.history frames.center.1 := by
    rw [history, center]
    exact LocalizedRecursiveAuxiliaryParityDecoration.swapWitnessB o ho
  exact historyWitness_to_properAuxiliaryTransport frames nonroot detectedCfg w

/-! Concrete wrappers construct the actual cyclic context frames from each real detected
occurrence. The premises identify the established cage history and current atom. -/

theorem actual_attachmentA_cycle_transport
    (target : Occurrence decReference)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter decReference.certified.moleculeGraph
      (decReference.certified.molecularFrameUnit target.1).atom)
    (nonroot : target.1.address ≠ [])
    (history : target.1.node.history = ([6, 3, 0] : List (Fin 21)))
    (current : target.1.node.current? = some (6 : Fin 21)) :
    let unit : DetectedOccurrence decReference.certified.moleculeGraph :=
      ⟨decReference.certified.molecularFrameUnit target.1, detected⟩
    let frames : ContextFrameCompilation decReference target unit rfl :=
      cyclicContextFrameCompilation decReference simple_bonded target real unit rfl
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  exact actualHistoryWitness_to_properAuxiliaryTransport simple_bonded real detected nonroot
    detectedCfg history current LocalizedRecursiveAuxiliaryParityDecoration.cycleWitnessA

theorem actual_attachmentB_cycle_transport
    (target : Occurrence decReference)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter decReference.certified.moleculeGraph
      (decReference.certified.molecularFrameUnit target.1).atom)
    (nonroot : target.1.address ≠ [])
    (history : target.1.node.history = ([15, 12, 0] : List (Fin 21)))
    (current : target.1.node.current? = some (15 : Fin 21)) :
    let unit : DetectedOccurrence decReference.certified.moleculeGraph :=
      ⟨decReference.certified.molecularFrameUnit target.1, detected⟩
    let frames : ContextFrameCompilation decReference target unit rfl :=
      cyclicContextFrameCompilation decReference simple_bonded target real unit rfl
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  exact actualHistoryWitness_to_properAuxiliaryTransport simple_bonded real detected nonroot
    detectedCfg history current LocalizedRecursiveAuxiliaryParityDecoration.cycleWitnessB

theorem actual_farA_swap_transport
    (target : Occurrence decReference)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter decReference.certified.moleculeGraph
      (decReference.certified.molecularFrameUnit target.1).atom)
    (nonroot : target.1.address ≠ []) (o : Fin 21) (ho : o ∈ [8, 9, 10])
    (history : target.1.node.history = ([11, o, 6, 3, 0] : List (Fin 21)))
    (current : target.1.node.current? = some (11 : Fin 21)) :
    let unit : DetectedOccurrence decReference.certified.moleculeGraph :=
      ⟨decReference.certified.molecularFrameUnit target.1, detected⟩
    let frames : ContextFrameCompilation decReference target unit rfl :=
      cyclicContextFrameCompilation decReference simple_bonded target real unit rfl
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  exact actualHistoryWitness_to_properAuxiliaryTransport simple_bonded real detected nonroot
    detectedCfg history current (LocalizedRecursiveAuxiliaryParityDecoration.swapWitnessA o ho)

theorem actual_farB_swap_transport
    (target : Occurrence decReference)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter decReference.certified.moleculeGraph
      (decReference.certified.molecularFrameUnit target.1).atom)
    (nonroot : target.1.address ≠ []) (o : Fin 21) (ho : o ∈ [17, 18, 19])
    (history : target.1.node.history = ([20, o, 15, 12, 0] : List (Fin 21)))
    (current : target.1.node.current? = some (20 : Fin 21)) :
    let unit : DetectedOccurrence decReference.certified.moleculeGraph :=
      ⟨decReference.certified.molecularFrameUnit target.1, detected⟩
    let frames : ContextFrameCompilation decReference target unit rfl :=
      cyclicContextFrameCompilation decReference simple_bonded target real unit rfl
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decReference.certified target (frames.frame.cursorAt b) ∧
      ∃ σ : decReference.certified.moleculeGraph.Aut,
        AuxiliaryBranchTransport frames σ detectedCfg a b false := by
  exact actualHistoryWitness_to_properAuxiliaryTransport simple_bonded real detected nonroot
    detectedCfg history current (LocalizedRecursiveAuxiliaryParityDecoration.swapWitnessB o ho)

/-- The accepted successful false-lowercase endpoint keeps the global/root obstruction alongside
the local witness adapters: the local proper transports do not assert a whole-root transport. -/
abbrev successfulFalseLowercase_globalEndpoint :=
  LocalizedRecursiveAuxiliarySuccessfulObstruction.successfulFalseLowercase

/-! ## Concrete actual carrier occurrences

The following occurrences are built from finite simple graph paths using the existing carrier
coverage theorem. Their addresses use the executable child-copy-slot function, and their frame
membership is proved at standard `carrierFuel`; no reader state or evaluator result is executed. -/

def occurrenceOfSimplePath {input : CertifiedLocalizedCIPInput} {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) (fuel : Nat)
    (enough : address.length ≤ fuel) : input.LocalizedCIPOccurrence fuel :=
  ⟨{ root := root
     address := address
     node := node
     remaining := fuel + 1 - address.length },
    input.legitimateOccurrence_mem_localizedOccurrences_of_fuel
      (LegitimateOccurrence.simple path) enough⟩

def nearANode3 : OfficialCIPNode (Fin 21) :=
  (OfficialCIPNode.root (0 : Fin 21)).extend 3 0

def nearANode6 : OfficialCIPNode (Fin 21) := nearANode3.extend 6 0

def nearAAddress3 : List Nat :=
  [decReference.certified.executableOfficialChildCopySlot
    (OfficialCIPNode.root (0 : Fin 21)) (3 : Fin 21) 0]

def nearAAddress6 : List Nat :=
  nearAAddress3 ++ [decReference.certified.executableOfficialChildCopySlot nearANode3
    (6 : Fin 21) 0]

def nearAPath3 : SimpleOccurrencePath decReference.certified (0 : Fin 21)
    nearANode3 nearAAddress3 := by
  refine @SimpleOccurrencePath.step decReference.certified (0 : Fin 21)
    (OfficialCIPNode.root (0 : Fin 21)) [] (0 : Fin 21) (3 : Fin 21)
    SimpleOccurrencePath.root ?_ ?_ ?_ ?_
  · rfl
  · decide
  · simp [OfficialCIPNode.parent?, OfficialCIPNode.root]
  · simp [OfficialCIPNode.root]

def nearAPath6 : SimpleOccurrencePath decReference.certified (0 : Fin 21)
    nearANode6 nearAAddress6 := by
  refine @SimpleOccurrencePath.step decReference.certified (0 : Fin 21)
    nearANode3 nearAAddress3 (3 : Fin 21) (6 : Fin 21) nearAPath3 ?_ ?_ ?_ ?_
  · simp [nearANode3]
  · decide
  · simp [nearANode3, OfficialCIPNode.parent?, OfficialCIPNode.extend_history,
      OfficialCIPNode.root]
  · simp [nearANode3, OfficialCIPNode.extend_history, OfficialCIPNode.root]

theorem nearAAddress6_nonempty : nearAAddress6 ≠ [] := by
  simp [nearAAddress6, nearAAddress3]

def nearAOccurrence3 : Occurrence decReference := by
  have bound : nearAAddress3.length ≤ carrierFuel decReference := by
    have leg : LegitimateOccurrence decReference.certified (0 : Fin 21) nearANode3 nearAAddress3 :=
      .simple nearAPath3
    have h := decReference.certified.legitimateOccurrence_address_length_le_atomCount leg
    change nearAAddress3.length ≤ decReference.certified.certified.input.molecule.atomCount + 1
    omega
  exact occurrenceOfSimplePath nearAPath3 (carrierFuel decReference) bound

def nearAOccurrence : Occurrence decReference := by
  let leg : LegitimateOccurrence decReference.certified (0 : Fin 21) nearANode6 nearAAddress6 :=
    .simple nearAPath6
  have bound : nearAAddress6.length ≤ carrierFuel decReference := by
    have h := decReference.certified.legitimateOccurrence_address_length_le_atomCount leg
    change nearAAddress6.length ≤ decReference.certified.certified.input.molecule.atomCount + 1
    omega
  exact occurrenceOfSimplePath nearAPath6 (carrierFuel decReference) bound

theorem nearAOccurrence_root : nearAOccurrence.1.root = (0 : Fin 21) := rfl

theorem nearAOccurrence_history :
    nearAOccurrence.1.node.history = ([6, 3, 0] : List (Fin 21)) := by
  simp [nearAOccurrence, occurrenceOfSimplePath,
    nearANode6, nearANode3, OfficialCIPNode.extend_history, OfficialCIPNode.root]

theorem nearAOccurrence_real :
    nearAOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  exact decReference.certified.simpleOccurrencePath_provenance nearAPath6

theorem nearAOccurrence_nonroot : nearAOccurrence.1.address ≠ [] := by
  simpa [nearAOccurrence, occurrenceOfSimplePath] using nearAAddress6_nonempty

theorem nearAOccurrence_current :
    nearAOccurrence.1.node.current? = some (6 : Fin 21) := by
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    decReference.certified nearAOccurrence nearAOccurrence_real
  rw [facts.2, nearAOccurrence_history]
  rfl

theorem nearAOccurrence_detected : IsDetectedCenter decoratedCertified.moleculeGraph
    (decoratedCertified.molecularFrameUnit nearAOccurrence.1).atom := by
  have head : nearAOccurrence.1.node.history.head? = some (6 : Fin 21) := by
    rw [nearAOccurrence_history]
    rfl
  have last : nearAOccurrence.1.node.history.getLast? = some nearAOccurrence.1.root := by
    rw [nearAOccurrence_history, nearAOccurrence_root]
    rfl
  have unitAtom := decReference.certified.molecularFrameUnit_atom_eq_current
    nearAOccurrence.1 head last
  rw [IsDetectedCenter, unitAtom]
  apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
  apply (graph.mem_tetrahedralCenterSet _).mp
  exact (degree_four_iff 6).2 (by decide)

theorem nearAOccurrence_properTransport :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified nearAOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded nearAOccurrence
          nearAOccurrence_real
          ⟨decoratedCertified.molecularFrameUnit nearAOccurrence.1,
            nearAOccurrence_detected⟩ rfl).frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified nearAOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded nearAOccurrence
          nearAOccurrence_real
          ⟨decoratedCertified.molecularFrameUnit nearAOccurrence.1,
            nearAOccurrence_detected⟩ rfl).frame.cursorAt b) ∧
      ∃ σ : graph.Aut, AuxiliaryBranchTransport
        (cyclicContextFrameCompilation decReference simple_bonded nearAOccurrence
          nearAOccurrence_real
          ⟨decoratedCertified.molecularFrameUnit nearAOccurrence.1,
            nearAOccurrence_detected⟩ rfl) σ detectedCfg a b false := by
  exact actual_attachmentA_cycle_transport nearAOccurrence nearAOccurrence_real
    nearAOccurrence_detected nearAOccurrence_nonroot nearAOccurrence_history
    nearAOccurrence_current

theorem nearAOccurrence3_history :
    nearAOccurrence3.1.node.history = ([3, 0] : List (Fin 21)) := by
  simp [nearAOccurrence3, occurrenceOfSimplePath, nearANode3, OfficialCIPNode.extend_history,
    OfficialCIPNode.root]

theorem armAAddress : armTargetA.1.address = nearAAddress3 := by
  have unitEq : decReference.certified.molecularFrameUnit armTargetA.1 =
      decReference.certified.molecularFrameUnit nearAOccurrence3.1 := by
    change (⟨armTargetA.1.root, armTargetA.1.node.history.reverse.tail⟩ :
      OccurrenceUnit (Fin 21)) =
      ⟨nearAOccurrence3.1.root, nearAOccurrence3.1.node.history.reverse.tail⟩
    rw [armA_root, armA_history, nearAOccurrence3_history]
    rfl
  have occurrenceEq := decReference.certified.molecularFrameUnit_injective_on_simpleBonded_carrier
    simple_bonded armTargetA nearAOccurrence3 unitEq
  have addressEq := congrArg (fun occurrence : Occurrence decReference => occurrence.1.address)
    occurrenceEq
  exact addressEq.trans rfl

def nearACursor : decReference.certified.LocalizedRerootCursor (carrierFuel decReference) :=
  ⟨nearAOccurrence, some armTargetA⟩

theorem nearAReachPath : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E decReference.certified)
    (decFrames.frame.cursorAt slotA) nearACursor := by
  let source := decFrames.frame.cursorAt slotA
  have previousEq : source.previous? = some decTarget :=
    (LocalizedCyclicMatchedReadingPhysicalTransport.rootFramePair
      decFrames decAddress slotA slotA).leftPrevious
  have shorter : decTarget.1.address.length < source.occurrence.1.address.length := by
    rw [decAddress, armAAddress]
    simp [nearAAddress3]
  have childAddress : nearAOccurrence.1.address =
      source.occurrence.1.address ++
        [decReference.certified.executableOfficialChildCopySlot nearANode3 (6 : Fin 21) 0] := by
    rw [show source.occurrence = armTargetA from rfl, armAAddress]
    rfl
  have edge := actualOutwardEdge source decTarget previousEq shorter nearAOccurrence
    (by rw [nearAOccurrence_root, armA_root]) (Or.inr ⟨_, childAddress⟩)
    (by simpa [source] using armA_real)
  exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl edge

theorem nearAReach : Reach decFrames slotA nearAOccurrence :=
  ⟨nearACursor, rfl, nearAReachPath⟩

def farANode8 : OfficialCIPNode (Fin 21) := nearANode6.extend 8 0
def farANode11 : OfficialCIPNode (Fin 21) := farANode8.extend 11 0

def farAAddress8 : List Nat := nearAAddress6 ++
  [decReference.certified.executableOfficialChildCopySlot nearANode6 (8 : Fin 21) 0]
def farAAddress11 : List Nat := farAAddress8 ++
  [decReference.certified.executableOfficialChildCopySlot farANode8 (11 : Fin 21) 0]

def farAPath8 : SimpleOccurrencePath decReference.certified (0 : Fin 21)
    farANode8 farAAddress8 := by
  refine @SimpleOccurrencePath.step decReference.certified (0 : Fin 21)
    nearANode6 nearAAddress6 (6 : Fin 21) (8 : Fin 21) nearAPath6 ?_ ?_ ?_ ?_
  · simp [nearANode6]
  · decide
  · simp [nearANode6, nearANode3, OfficialCIPNode.parent?, OfficialCIPNode.extend_history,
      OfficialCIPNode.root]
  · simp [nearANode6, nearANode3, OfficialCIPNode.extend_history, OfficialCIPNode.root]

def farAOccurrence8 : Occurrence decReference := by
  let leg : LegitimateOccurrence decReference.certified (0 : Fin 21) farANode8 farAAddress8 :=
    .simple farAPath8
  have bound : farAAddress8.length ≤ carrierFuel decReference := by
    have h := decReference.certified.legitimateOccurrence_address_length_le_atomCount leg
    change farAAddress8.length ≤ decReference.certified.certified.input.molecule.atomCount + 1
    omega
  exact occurrenceOfSimplePath farAPath8 (carrierFuel decReference) bound

def farAPath11 : SimpleOccurrencePath decReference.certified (0 : Fin 21)
    farANode11 farAAddress11 := by
  refine @SimpleOccurrencePath.step decReference.certified (0 : Fin 21)
    farANode8 farAAddress8 (8 : Fin 21) (11 : Fin 21) farAPath8 ?_ ?_ ?_ ?_
  · simp [farANode8, nearANode6]
  · decide
  · simp [farANode8, nearANode6, nearANode3, OfficialCIPNode.parent?,
      OfficialCIPNode.extend_history, OfficialCIPNode.root]
  · simp [farANode8, nearANode6, nearANode3, OfficialCIPNode.extend_history,
      OfficialCIPNode.root]

theorem farAAddress11_nonempty : farAAddress11 ≠ [] := by
  simp [farAAddress11, farAAddress8, nearAAddress6, nearAAddress3]

def farAOccurrence : Occurrence decReference := by
  let leg : LegitimateOccurrence decReference.certified (0 : Fin 21) farANode11 farAAddress11 :=
    .simple farAPath11
  have bound : farAAddress11.length ≤ carrierFuel decReference := by
    have h := decReference.certified.legitimateOccurrence_address_length_le_atomCount leg
    change farAAddress11.length ≤ decReference.certified.certified.input.molecule.atomCount + 1
    omega
  exact occurrenceOfSimplePath farAPath11 (carrierFuel decReference) bound

theorem farAOccurrence_root : farAOccurrence.1.root = (0 : Fin 21) := rfl
theorem farAOccurrence_history :
    farAOccurrence.1.node.history = ([11, 8, 6, 3, 0] : List (Fin 21)) := by
  simp [farAOccurrence, occurrenceOfSimplePath, farANode11, farANode8,
    nearANode6, nearANode3, OfficialCIPNode.extend_history, OfficialCIPNode.root]
theorem farAOccurrence_real :
    farAOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  decReference.certified.simpleOccurrencePath_provenance farAPath11
theorem farAOccurrence_nonroot : farAOccurrence.1.address ≠ [] := by
  simpa [farAOccurrence, occurrenceOfSimplePath] using farAAddress11_nonempty
theorem farAOccurrence_current :
    farAOccurrence.1.node.current? = some (11 : Fin 21) := by
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    decReference.certified farAOccurrence farAOccurrence_real
  rw [facts.2, farAOccurrence_history]
  rfl

theorem farAOccurrence8_history :
    farAOccurrence8.1.node.history = ([8, 6, 3, 0] : List (Fin 21)) := by
  simp [farAOccurrence8, occurrenceOfSimplePath, farANode8, nearANode6, nearANode3,
    OfficialCIPNode.extend_history, OfficialCIPNode.root]

theorem farAOccurrence8_real :
    farAOccurrence8.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  decReference.certified.simpleOccurrencePath_provenance farAPath8

def farA8Cursor : decReference.certified.LocalizedRerootCursor (carrierFuel decReference) :=
  ⟨farAOccurrence8, some nearAOccurrence⟩

theorem farAOccurrence8_root : farAOccurrence8.1.root = (0 : Fin 21) := rfl

theorem farA8ReachPath : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E decReference.certified)
    (decFrames.frame.cursorAt slotA) farA8Cursor := by
  have shorter : armTargetA.1.address.length < nearAOccurrence.1.address.length := by
    rw [armAAddress]
    simp [nearAAddress6, nearAAddress3, nearAOccurrence, occurrenceOfSimplePath]
  have childAddress : farAOccurrence8.1.address =
      nearACursor.occurrence.1.address ++
        [decReference.certified.executableOfficialChildCopySlot nearANode6 (8 : Fin 21) 0] := by
    rfl
  have edge := actualOutwardEdge nearACursor armTargetA
    (by rfl) shorter farAOccurrence8
    (by simpa [nearACursor] using nearAOccurrence_root.symm)
    (Or.inr ⟨_, childAddress⟩) nearAOccurrence_real
  exact nearAReachPath.tail edge

theorem farA8Reach : Reach decFrames slotA farAOccurrence8 :=
  ⟨farA8Cursor, rfl, farA8ReachPath⟩

theorem farAReachPath : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E decReference.certified)
    (decFrames.frame.cursorAt slotA)
      (⟨farAOccurrence, some farAOccurrence8⟩ :
        decReference.certified.LocalizedRerootCursor (carrierFuel decReference)) := by
  have shorter : nearAOccurrence.1.address.length < farAOccurrence8.1.address.length := by
    simp [nearAOccurrence, farAOccurrence8, occurrenceOfSimplePath, nearAAddress6,
      nearAAddress3, farAAddress8]
  have childAddress : farAOccurrence.1.address = farAOccurrence8.1.address ++
      [decReference.certified.executableOfficialChildCopySlot farANode8 (11 : Fin 21) 0] := rfl
  have edge := actualOutwardEdge farA8Cursor nearAOccurrence (by rfl) shorter farAOccurrence
    (by simpa [farA8Cursor] using farAOccurrence8_root.symm) (Or.inr ⟨_, childAddress⟩)
    farAOccurrence8_real
  exact farA8ReachPath.tail edge

theorem farAReach : Reach decFrames slotA farAOccurrence :=
  ⟨⟨farAOccurrence, some farAOccurrence8⟩, rfl, farAReachPath⟩
theorem farAOccurrence_detected : IsDetectedCenter decoratedCertified.moleculeGraph
    (decoratedCertified.molecularFrameUnit farAOccurrence.1).atom := by
  have head : farAOccurrence.1.node.history.head? = some (11 : Fin 21) := by
    rw [farAOccurrence_history]
    rfl
  have last : farAOccurrence.1.node.history.getLast? = some farAOccurrence.1.root := by
    rw [farAOccurrence_history, farAOccurrence_root]
    rfl
  have unitAtom := decReference.certified.molecularFrameUnit_atom_eq_current
    farAOccurrence.1 head last
  rw [IsDetectedCenter, unitAtom]
  apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
  apply (graph.mem_tetrahedralCenterSet _).mp
  exact (degree_four_iff 11).2 (by decide)

theorem farAOccurrence_properTransport :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified farAOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded farAOccurrence
          farAOccurrence_real ⟨decoratedCertified.molecularFrameUnit farAOccurrence.1,
            farAOccurrence_detected⟩ rfl).frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified farAOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded farAOccurrence
          farAOccurrence_real ⟨decoratedCertified.molecularFrameUnit farAOccurrence.1,
            farAOccurrence_detected⟩ rfl).frame.cursorAt b) ∧
      ∃ σ : graph.Aut, AuxiliaryBranchTransport
        (cyclicContextFrameCompilation decReference simple_bonded farAOccurrence
          farAOccurrence_real ⟨decoratedCertified.molecularFrameUnit farAOccurrence.1,
            farAOccurrence_detected⟩ rfl) σ detectedCfg a b false := by
  exact actual_farA_swap_transport farAOccurrence farAOccurrence_real farAOccurrence_detected
    farAOccurrence_nonroot 8 (by decide) farAOccurrence_history farAOccurrence_current

/-! The actual arm-swap occurrence transport supplies matching B-side occurrence identities. -/

def nearBOccurrence : Occurrence decReference :=
  decReference.certified.transportOccurrence simple_bonded armSwap nearAOccurrence

theorem nearBOccurrence_history :
    nearBOccurrence.1.node.history = ([15, 12, 0] : List (Fin 21)) := by
  simp [nearBOccurrence, transportOccurrence_node, mapOfficialNode, nearAOccurrence_history]
  decide

theorem nearBOccurrence_real :
    nearBOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  simpa only [nearBOccurrence] using
    (decReference.certified.transportOccurrence_provenance simple_bonded armSwap nearAOccurrence).trans
      nearAOccurrence_real

theorem nearBOccurrence_root : nearBOccurrence.1.root = (0 : Fin 21) := by
  change (armSwap : Equiv.Perm (Fin 21)) nearAOccurrence.1.root = 0
  rw [nearAOccurrence_root]
  decide

theorem nearBOccurrence_nonroot : nearBOccurrence.1.address ≠ [] := by
  intro empty
  have lengthZero := congrArg List.length empty
  have mappedLength := decReference.certified.transportOccurrence_address_length
    simple_bonded armSwap nearAOccurrence
  have lengthEq : nearBOccurrence.1.address.length = nearAOccurrence.1.address.length := by
    simpa only [nearBOccurrence] using mappedLength
  rw [lengthEq] at lengthZero
  have sourceEmpty : nearAOccurrence.1.address = [] := List.length_eq_zero_iff.mp lengthZero
  exact nearAOccurrence_nonroot sourceEmpty

theorem nearBOccurrence_current :
    nearBOccurrence.1.node.current? = some (15 : Fin 21) := by
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    decReference.certified nearBOccurrence nearBOccurrence_real
  rw [facts.2, nearBOccurrence_history]
  rfl

theorem nearBOccurrence_detected : IsDetectedCenter decoratedCertified.moleculeGraph
    (decoratedCertified.molecularFrameUnit nearBOccurrence.1).atom := by
  have head : nearBOccurrence.1.node.history.head? = some (15 : Fin 21) := by
    rw [nearBOccurrence_history]
    rfl
  have last : nearBOccurrence.1.node.history.getLast? = some nearBOccurrence.1.root := by
    rw [nearBOccurrence_history, nearBOccurrence_root]
    rfl
  have unitAtom := decReference.certified.molecularFrameUnit_atom_eq_current
    nearBOccurrence.1 head last
  rw [IsDetectedCenter, unitAtom]
  apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
  apply (graph.mem_tetrahedralCenterSet _).mp
  exact (degree_four_iff 15).2 (by decide)

theorem nearBOccurrence_properTransport :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified nearBOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded nearBOccurrence
          nearBOccurrence_real ⟨decoratedCertified.molecularFrameUnit nearBOccurrence.1,
            nearBOccurrence_detected⟩ rfl).frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified nearBOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded nearBOccurrence
          nearBOccurrence_real ⟨decoratedCertified.molecularFrameUnit nearBOccurrence.1,
            nearBOccurrence_detected⟩ rfl).frame.cursorAt b) ∧
      ∃ σ : graph.Aut, AuxiliaryBranchTransport
        (cyclicContextFrameCompilation decReference simple_bonded nearBOccurrence
          nearBOccurrence_real ⟨decoratedCertified.molecularFrameUnit nearBOccurrence.1,
            nearBOccurrence_detected⟩ rfl) σ detectedCfg a b false := by
  exact actual_attachmentB_cycle_transport nearBOccurrence nearBOccurrence_real
    nearBOccurrence_detected nearBOccurrence_nonroot nearBOccurrence_history
    nearBOccurrence_current

def farBOccurrence : Occurrence decReference :=
  decReference.certified.transportOccurrence simple_bonded armSwap farAOccurrence

theorem farBOccurrence_history :
    farBOccurrence.1.node.history = ([20, 17, 15, 12, 0] : List (Fin 21)) := by
  simp [farBOccurrence, transportOccurrence_node, mapOfficialNode, farAOccurrence_history]
  decide

theorem farBOccurrence_real :
    farBOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  simpa only [farBOccurrence] using
    (decReference.certified.transportOccurrence_provenance simple_bonded armSwap farAOccurrence).trans
      farAOccurrence_real

theorem farBOccurrence_root : farBOccurrence.1.root = (0 : Fin 21) := by
  change (armSwap : Equiv.Perm (Fin 21)) farAOccurrence.1.root = 0
  rw [farAOccurrence_root]
  decide

theorem farBOccurrence_nonroot : farBOccurrence.1.address ≠ [] := by
  intro empty
  have lengthZero := congrArg List.length empty
  have mappedLength := decReference.certified.transportOccurrence_address_length
    simple_bonded armSwap farAOccurrence
  have lengthEq : farBOccurrence.1.address.length = farAOccurrence.1.address.length := by
    simpa only [farBOccurrence] using mappedLength
  rw [lengthEq] at lengthZero
  have sourceEmpty : farAOccurrence.1.address = [] := List.length_eq_zero_iff.mp lengthZero
  exact farAOccurrence_nonroot sourceEmpty

theorem farBOccurrence_current :
    farBOccurrence.1.node.current? = some (20 : Fin 21) := by
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    decReference.certified farBOccurrence farBOccurrence_real
  rw [facts.2, farBOccurrence_history]
  rfl

theorem farBOccurrence_detected : IsDetectedCenter decoratedCertified.moleculeGraph
    (decoratedCertified.molecularFrameUnit farBOccurrence.1).atom := by
  have head : farBOccurrence.1.node.history.head? = some (20 : Fin 21) := by
    rw [farBOccurrence_history]
    rfl
  have last : farBOccurrence.1.node.history.getLast? = some farBOccurrence.1.root := by
    rw [farBOccurrence_history, farBOccurrence_root]
    rfl
  have unitAtom := decReference.certified.molecularFrameUnit_atom_eq_current
    farBOccurrence.1 head last
  rw [IsDetectedCenter, unitAtom]
  apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
  apply (graph.mem_tetrahedralCenterSet _).mp
  exact (degree_four_iff 20).2 (by decide)

theorem farBOccurrence_properTransport :
    ∃ a b : Fin 4, a ≠ b ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified farBOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded farBOccurrence
          farBOccurrence_real ⟨decoratedCertified.molecularFrameUnit farBOccurrence.1,
            farBOccurrence_detected⟩ rfl).frame.cursorAt a) ∧
      IsLocalizedActualFrameOutwardCursor decoratedCertified farBOccurrence
        ((cyclicContextFrameCompilation decReference simple_bonded farBOccurrence
          farBOccurrence_real ⟨decoratedCertified.molecularFrameUnit farBOccurrence.1,
            farBOccurrence_detected⟩ rfl).frame.cursorAt b) ∧
      ∃ σ : graph.Aut, AuxiliaryBranchTransport
        (cyclicContextFrameCompilation decReference simple_bonded farBOccurrence
          farBOccurrence_real ⟨decoratedCertified.molecularFrameUnit farBOccurrence.1,
            farBOccurrence_detected⟩ rfl) σ detectedCfg a b false := by
  exact actual_farB_swap_transport farBOccurrence farBOccurrence_real farBOccurrence_detected
    farBOccurrence_nonroot 17 (by decide) farBOccurrence_history farBOccurrence_current

theorem armSwap_sends_A_to_B :
    decReference.certified.transportCursor simple_bonded armSwap
        (decFrames.frame.cursorAt slotA) = decFrames.frame.cursorAt slotB := by
  apply rootSlot_sent simple_bonded decFrames decAddress decReal armSwap armSwap_root
  calc
    (armSwap : Equiv.Perm (Fin 21))
        (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
          (decFrames.detectedLigandPermutation slotA)) = (armSwap : Equiv.Perm (Fin 21)) 3 := by rw [slotA_spec]
    _ = 12 := by decide
    _ = decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
        (decFrames.detectedLigandPermutation slotB) := slotB_spec.symm

theorem armSwap_sends_B_to_A :
    decReference.certified.transportCursor simple_bonded armSwap
        (decFrames.frame.cursorAt slotB) = decFrames.frame.cursorAt slotA := by
  apply rootSlot_sent simple_bonded decFrames decAddress decReal armSwap armSwap_root
  calc
    (armSwap : Equiv.Perm (Fin 21))
        (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
          (decFrames.detectedLigandPermutation slotB)) = (armSwap : Equiv.Perm (Fin 21)) 12 := by rw [slotB_spec]
    _ = 3 := by decide
    _ = decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
        (decFrames.detectedLigandPermutation slotA) := slotA_spec.symm

theorem nearBReach : Reach decFrames slotB nearBOccurrence := by
  simpa [nearBOccurrence] using
    (reach_transport simple_bonded decFrames armSwap armSwap_sends_A_to_B nearAReach)

theorem farBReach : Reach decFrames slotB farBOccurrence := by
  simpa [farBOccurrence] using
    (reach_transport simple_bonded decFrames armSwap armSwap_sends_A_to_B farAReach)

theorem nearAReferenceState_none : referenceState decReference nearAOccurrence = none := by
  apply referenceState_none_of_historyWitness simple_bonded decFrames decAddress decReal
    slots_ne armSwap armSwap_root (by
      calc
        (armSwap : Equiv.Perm (Fin 21))
            (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
              (decFrames.detectedLigandPermutation slotA)) = (armSwap : Equiv.Perm (Fin 21)) 3 := by rw [slotA_spec]
        _ = 12 := by decide
        _ = decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
            (decFrames.detectedLigandPermutation slotB) := slotB_spec.symm)
    detectedCfg domainAtFrames nearAOccurrence nearAReach nearAOccurrence_real
    nearAOccurrence_detected
  intro d current
  have dEq : d = (6 : Fin 21) := Option.some.inj
    (current.symm.trans nearAOccurrence_current)
  subst d
  rw [nearAOccurrence_history]
  exact LocalizedRecursiveAuxiliaryParityDecoration.cycleWitnessA

theorem farAReferenceState_none : referenceState decReference farAOccurrence = none := by
  apply referenceState_none_of_historyWitness simple_bonded decFrames decAddress decReal
    slots_ne armSwap armSwap_root (by
      calc
        (armSwap : Equiv.Perm (Fin 21))
            (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
              (decFrames.detectedLigandPermutation slotA)) = (armSwap : Equiv.Perm (Fin 21)) 3 := by rw [slotA_spec]
        _ = 12 := by decide
        _ = decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
            (decFrames.detectedLigandPermutation slotB) := slotB_spec.symm)
    detectedCfg domainAtFrames farAOccurrence farAReach farAOccurrence_real
    farAOccurrence_detected
  intro d current
  have dEq : d = (11 : Fin 21) := Option.some.inj
    (current.symm.trans farAOccurrence_current)
  subst d
  rw [farAOccurrence_history]
  exact LocalizedRecursiveAuxiliaryParityDecoration.swapWitnessA 8 (by decide)

theorem nearBReferenceState_none : referenceState decReference nearBOccurrence = none := by
  apply referenceState_none_of_historyWitness simple_bonded decFrames decAddress decReal
    (Ne.symm slots_ne) armSwap armSwap_root (by
      calc
        (armSwap : Equiv.Perm (Fin 21))
            (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
              (decFrames.detectedLigandPermutation slotB)) = (armSwap : Equiv.Perm (Fin 21)) 12 := by rw [slotB_spec]
        _ = 3 := by decide
        _ = decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
            (decFrames.detectedLigandPermutation slotA) := slotA_spec.symm)
    detectedCfg domainAtFrames nearBOccurrence nearBReach nearBOccurrence_real
    nearBOccurrence_detected
  intro d current
  have dEq : d = (15 : Fin 21) := Option.some.inj
    (current.symm.trans nearBOccurrence_current)
  subst d
  rw [nearBOccurrence_history]
  exact LocalizedRecursiveAuxiliaryParityDecoration.cycleWitnessB

theorem farBReferenceState_none : referenceState decReference farBOccurrence = none := by
  apply referenceState_none_of_historyWitness simple_bonded decFrames decAddress decReal
    (Ne.symm slots_ne) armSwap armSwap_root (by
      calc
        (armSwap : Equiv.Perm (Fin 21))
            (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
              (decFrames.detectedLigandPermutation slotB)) = (armSwap : Equiv.Perm (Fin 21)) 12 := by rw [slotB_spec]
        _ = 3 := by decide
        _ = decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
            (decFrames.detectedLigandPermutation slotA) := slotA_spec.symm)
    detectedCfg domainAtFrames farBOccurrence farBReach farBOccurrence_real
    farBOccurrence_detected
  intro d current
  have dEq : d = (20 : Fin 21) := Option.some.inj
    (current.symm.trans farBOccurrence_current)
  subst d
  rw [farBOccurrence_history]
  exact LocalizedRecursiveAuxiliaryParityDecoration.swapWitnessB 17 (by decide)

def nearAUnit : DetectedOccurrence graph :=
  ⟨decReference.certified.molecularFrameUnit nearAOccurrence.1, nearAOccurrence_detected⟩
def farAUnit : DetectedOccurrence graph :=
  ⟨decReference.certified.molecularFrameUnit farAOccurrence.1, farAOccurrence_detected⟩
def nearBUnit : DetectedOccurrence graph :=
  ⟨decReference.certified.molecularFrameUnit nearBOccurrence.1, nearBOccurrence_detected⟩
def farBUnit : DetectedOccurrence graph :=
  ⟨decReference.certified.molecularFrameUnit farBOccurrence.1, farBOccurrence_detected⟩

theorem nearAActualGeneratedReadback :
    actualReferenceOccurrenceOf decReference nearAUnit.1 = some nearAOccurrence ∧
      descriptorMap decReference nearAUnit = none := by
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded decReference
    simple_bonded nearAUnit.1 nearAOccurrence).2 rfl
  have read := descriptorMap_eq_of_actualState decReference simple_bonded nearAUnit
    nearAOccurrence rfl
  exact ⟨chosen, by simpa [nearAReferenceState_none] using read⟩

theorem farAActualGeneratedReadback :
    actualReferenceOccurrenceOf decReference farAUnit.1 = some farAOccurrence ∧
      descriptorMap decReference farAUnit = none := by
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded decReference
    simple_bonded farAUnit.1 farAOccurrence).2 rfl
  have read := descriptorMap_eq_of_actualState decReference simple_bonded farAUnit
    farAOccurrence rfl
  exact ⟨chosen, by simpa [farAReferenceState_none] using read⟩

theorem nearBActualGeneratedReadback :
    actualReferenceOccurrenceOf decReference nearBUnit.1 = some nearBOccurrence ∧
      descriptorMap decReference nearBUnit = none := by
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded decReference
    simple_bonded nearBUnit.1 nearBOccurrence).2 rfl
  have read := descriptorMap_eq_of_actualState decReference simple_bonded nearBUnit
    nearBOccurrence rfl
  exact ⟨chosen, by simpa [nearBReferenceState_none] using read⟩

theorem farBActualGeneratedReadback :
    actualReferenceOccurrenceOf decReference farBUnit.1 = some farBOccurrence ∧
      descriptorMap decReference farBUnit = none := by
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded decReference
    simple_bonded farBUnit.1 farBOccurrence).2 rfl
  have read := descriptorMap_eq_of_actualState decReference simple_bonded farBUnit
    farBOccurrence rfl
  exact ⟨chosen, by simpa [farBReferenceState_none] using read⟩

/-- Concrete 21-atom local proper transports coexist with the accepted successful lowercase root
result and its zero physical enantiomorphic pair count. These occurrences are reached in the root
arms, and their generated descriptor-map reads at the actual molecular units are `none`. -/
theorem concrete21_hiddenParityEndpoint :
    physicalEnantiomorphicPairCount decoratedCertified.detectedMultiCenterMolecule detectedCfg
        decRoot = 0 ∧
      (∃ descriptor : LocalizedAuxiliaryLabel,
        referenceState decReference decTarget = some descriptor ∧ descriptor.IsLowercase ∧
          (decRoot.val.val, some descriptor) ∈ analyze decReference) ∧
      ActualProperTransportAt nearAOccurrence nearAOccurrence_real nearAOccurrence_detected ∧
      ActualProperTransportAt farAOccurrence farAOccurrence_real farAOccurrence_detected ∧
      ActualProperTransportAt nearBOccurrence nearBOccurrence_real nearBOccurrence_detected ∧
      ActualProperTransportAt farBOccurrence farBOccurrence_real farBOccurrence_detected :=
  by
    obtain ⟨_, _, _, _, _, _, countZero, _, _, ⟨descriptor, returned, lowercase, report⟩⟩ :=
      successfulFalseLowercase_globalEndpoint
    exact ⟨countZero, ⟨descriptor, returned, lowercase, report⟩,
      (show ActualProperTransportAt nearAOccurrence nearAOccurrence_real nearAOccurrence_detected
        from nearAOccurrence_properTransport),
      (show ActualProperTransportAt farAOccurrence farAOccurrence_real farAOccurrence_detected
        from farAOccurrence_properTransport),
      (show ActualProperTransportAt nearBOccurrence nearBOccurrence_real nearBOccurrence_detected
        from nearBOccurrence_properTransport),
      (show ActualProperTransportAt farBOccurrence farBOccurrence_real farBOccurrence_detected
        from farBOccurrence_properTransport)⟩

/-- The actual local refusal/readback facts coexist with the accepted global false-lowercase
endpoint. The generated-map reads are at the four constructed occurrence molecular units; the
Reach proofs above identify their actual root-arm cursor paths. -/
theorem concrete21_hiddenParityLocalStateReadback :
    (physicalEnantiomorphicPairCount decoratedCertified.detectedMultiCenterMolecule detectedCfg
        decRoot = 0 ∧
      (∃ descriptor : LocalizedAuxiliaryLabel,
        referenceState decReference decTarget = some descriptor ∧ descriptor.IsLowercase ∧
          (decRoot.val.val, some descriptor) ∈ analyze decReference) ∧
      ActualProperTransportAt nearAOccurrence nearAOccurrence_real nearAOccurrence_detected ∧
      ActualProperTransportAt farAOccurrence farAOccurrence_real farAOccurrence_detected ∧
      ActualProperTransportAt nearBOccurrence nearBOccurrence_real nearBOccurrence_detected ∧
      ActualProperTransportAt farBOccurrence farBOccurrence_real farBOccurrence_detected) ∧
      referenceState decReference nearAOccurrence = none ∧
      referenceState decReference farAOccurrence = none ∧
      referenceState decReference nearBOccurrence = none ∧
      referenceState decReference farBOccurrence = none ∧
      (actualReferenceOccurrenceOf decReference nearAUnit.1 = some nearAOccurrence ∧
        descriptorMap decReference nearAUnit = none) ∧
      (actualReferenceOccurrenceOf decReference farAUnit.1 = some farAOccurrence ∧
        descriptorMap decReference farAUnit = none) ∧
      (actualReferenceOccurrenceOf decReference nearBUnit.1 = some nearBOccurrence ∧
        descriptorMap decReference nearBUnit = none) ∧
      (actualReferenceOccurrenceOf decReference farBUnit.1 = some farBOccurrence ∧
        descriptorMap decReference farBUnit = none) := by
  exact ⟨concrete21_hiddenParityEndpoint, nearAReferenceState_none, farAReferenceState_none,
    nearBReferenceState_none, farBReferenceState_none, nearAActualGeneratedReadback,
    farAActualGeneratedReadback, nearBActualGeneratedReadback, farBActualGeneratedReadback⟩

end

end TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses

assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.historyWitness_to_properAuxiliaryTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.actualHistoryWitness_to_properAuxiliaryTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.attachmentA_cycle_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.attachmentB_cycle_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farA_swap_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farB_swap_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.actual_attachmentA_cycle_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.actual_attachmentB_cycle_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.actual_farA_swap_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.actual_farB_swap_transport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.successfulFalseLowercase_globalEndpoint
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearAOccurrence_properTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farAOccurrence_properTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearBOccurrence_properTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farBOccurrence_properTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.concrete21_hiddenParityEndpoint
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.actualOutwardEdge
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.armAAddress
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearAReachPath
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farA8ReachPath
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farAReachPath
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearBReach
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farBReach
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearAReferenceState_none
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farAReferenceState_none
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearBReferenceState_none
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farBReferenceState_none
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearAActualGeneratedReadback
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farAActualGeneratedReadback
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.nearBActualGeneratedReadback
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.farBActualGeneratedReadback
assert_kernel_only
  TetraStereo.OneCenter.LocalizedHiddenParityAuxiliaryPhysicalWitnesses.concrete21_hiddenParityLocalStateReadback
