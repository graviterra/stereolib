import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality
import TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport
import TetraStereo.OneCenter.LocalizedRetainedCutDescriptorTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Structural key transport for the actual root compilation. The reader law is a
separate input here; actual generated-label covariance supplies it in the physical join.
Every graph and predecessor cut is obtained from the actual successful arm construction. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel

open CertifiedLocalizedCIPInput DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedRootArmLocality
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRootWitness (root_slot_data)
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap)

noncomputable section
open scoped Classical

private theorem cut_eq_of_carriers {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) {root root' : Atom} (rootEq : root = root')
    (focus : Nodes molecule root) (incoming : Nodes molecule root)
    (anchor : CutAnchor focus (some incoming))
    (focus' : Nodes molecule root') (incoming' : Nodes molecule root')
    (anchor' : CutAnchor focus' (some incoming'))
    (focusEq : focus.1 = focus'.1) (incomingEq : incoming.1 = incoming'.1) :
    cutRetainedArm molecule root focus (some incoming) anchor =
      cutRetainedArm molecule root' focus' (some incoming') anchor' := by
  subst root'
  have hf : focus = focus' := Subtype.ext focusEq
  have hi : incoming = incoming' := Subtype.ext incomingEq
  subst focus'
  subst incoming'
  rfl

/-- A molecular symmetry and actual reader agreement transport a fixed-window prior key.
The compilation's descriptor map only determines the concrete arm representation. -/
theorem priorKey_relabel_of_cursor_transport
    (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
    (compilationMap sourceMap imageMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame compilationMap target)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (e : input.moleculeGraph.Aut) (left right : Fin 4)
    (fixed : input.transportOccurrence single e target = target)
    (sent : input.transportCursor single e (frame.frame.cursorAt left) = frame.frame.cursorAt right)
    (reads : ReadsAgree input.moleculeGraph e imageMap sourceMap unit
      (frame.actualArmGraphs left)) (W D : Nat) :
    retainedCompleteLigandPriorKeyAt input.moleculeGraph imageMap unit
        (frame.actualArmGraphs right) W D =
      retainedCompleteLigandPriorKeyAt input.moleculeGraph sourceMap unit
        (frame.actualArmGraphs left) W D := by
  let parent : input.LocalizedRerootCursor (retainedCarrierFuel input) := ⟨target, none⟩
  obtain ⟨_prevL, focusL, incomingL, anchorL, focusEqL, incomingEqL, faithfulL⟩ :=
    input.executableChild_retainedContextArmFaithful_of_carrierFuel single parent
      (frame.frame.cursorAt left) (frame.childAt left) (frame.stages left).a
  obtain ⟨_prevR, focusR, incomingR, anchorR, focusEqR, incomingEqR, faithfulR⟩ :=
    input.executableChild_retainedContextArmFaithful_of_carrierFuel single parent
      (frame.frame.cursorAt right) (frame.childAt right) (frame.stages right).a
  let isoL := Classical.choice faithfulL
  let isoR := Classical.choice faithfulR
  have readsCut := LocalizedCyclicPhysicalStageTransport.readsAgree_of_iso e imageMap
    sourceMap unit isoL.symm reads
  have moved := cut_priorKey e focusL (some incomingL) anchorL imageMap sourceMap unit readsCut W D
  have fixedUnit : mapDetected input.moleculeGraph e unit = unit := by
    apply Subtype.ext
    have h := input.molecularFrameUnit_transport single e target
    rw [fixed, targetUnit] at h
    exact h.symm
  have occurrenceSent := congrArg (fun cursor => cursor.occurrence) sent
  change input.transportOccurrence single e (frame.frame.cursorAt left).occurrence =
    (frame.frame.cursorAt right).occurrence at occurrenceSent
  have rootSent := congrArg (fun cursor => cursor.occurrence.1.root) sent
  change (e : Equiv.Perm input.Atom) (frame.frame.cursorAt left).occurrence.1.root =
    (frame.frame.cursorAt right).occurrence.1.root at rootSent
  have imageCut : cutRetainedArm input.moleculeGraph
      ((e : Equiv.Perm input.Atom) (frame.frame.cursorAt left).occurrence.1.root)
      (imageNode e focusL) ((some incomingL).map (imageNode e))
      (cutAnchor_image e focusL (some incomingL) anchorL) =
    cutRetainedArm input.moleculeGraph (frame.frame.cursorAt right).occurrence.1.root
      focusR (some incomingR) anchorR := by
    apply cut_eq_of_carriers input.moleculeGraph rootSent
    · rw [imageNode_carrier, focusEqL, focusEqR, mapCarrier_eq_mapCarrierNode,
        input.occurrenceCarrierNode_transport, occurrenceSent]
    · rw [imageNode_carrier, incomingEqL, incomingEqR, mapCarrier_eq_mapCarrierNode,
        input.occurrenceCarrierNode_transport, fixed]
  rw [fixedUnit, imageCut] at moved
  exact (retainedCompleteLigandPriorKeyAt_iso input.moleculeGraph imageMap unit isoR W D).trans
    (moved.trans (retainedCompleteLigandPriorKeyAt_iso input.moleculeGraph sourceMap unit isoL W D).symm)


private theorem occurrenceUnit_ext {Atom : Type*} {a b : OccurrenceUnit Atom}
    (root : a.root = b.root) (path : a.path = b.path) : a = b := by
  cases a
  cases b
  simp_all

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

theorem target_root (rootAddress : data.target.1.address = [])
    (current : node.atom = c.1.val) : data.target.1.root = c.1 := by
  have equality := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
    ((input.mem_localizedOccurrences_iff _ _).mp data.target.2) rootAddress
  have nodeEq := congrArg (fun occurrence => occurrence.node) equality
  change data.target.1.node = OfficialCIPNode.root data.target.1.root at nodeEq
  have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).current
  rw [nodeEq] at sound
  exact Fin.ext ((Option.some.inj sound).trans current)

theorem target_unit (rootAddress : data.target.1.address = [])
    (current : node.atom = c.1.val) :
    input.molecularFrameUnit data.target.1 = (⟨c.1, []⟩ : OccurrenceUnit input.Atom) := by
  simp [molecularFrameUnit, root_history input mol c node data rootAddress current,
    target_root input mol c node data rootAddress current]

theorem slot_unit (state : OccurrenceAuxState) (slot : Fin 4)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val) :
    input.molecularFrameUnit ((rootFrame input mol single c node data state).frame.cursorAt slot).occurrence.1 =
      (⟨c.1, [referenceAt input mol c node data slot]⟩ : OccurrenceUnit input.Atom) := by
  obtain ⟨_, rootEq, _, _⟩ := root_slot_data input single _ data.target
    (rootFrame input mol single c node data state) rootAddress slot _
    (slot_current input mol single c node data state slot)
  apply occurrenceUnit_ext
  · exact rootEq.trans (target_root input mol c node data rootAddress current)
  · exact root_slot_path input mol single c node data rootAddress state slot

theorem rootOccurrence_fixed (rootAddress : data.target.1.address = [])
    (current : node.atom = c.1.val) (e : input.moleculeGraph.Aut)
    (fixed : (e : Equiv.Perm input.Atom) c.1 = c.1) :
    input.transportOccurrence single e data.target = data.target := by
  apply input.molecularFrameUnit_injective_on_simpleBonded_carrier single
  rw [input.molecularFrameUnit_transport, target_unit input mol c node data rootAddress current]
  simp [transportOccurrenceUnit, fixed]

theorem rootSlot_transport (state : OccurrenceAuxState)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (e : input.moleculeGraph.Aut) (left right : Fin 4)
    (fixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
    (sent : (e : Equiv.Perm input.Atom) (referenceAt input mol c node data left) =
      referenceAt input mol c node data right) :
    input.transportCursor single e ((rootFrame input mol single c node data state).frame.cursorAt left) =
      (rootFrame input mol single c node data state).frame.cursorAt right := by
  let frame := rootFrame input mol single c node data state
  have previous (slot : Fin 4) : (frame.frame.cursorAt slot).previous? = some data.target := by
    exact (input.executableChild_retainedContextArmFaithful_of_carrierFuel single
      (⟨data.target, none⟩ : input.LocalizedRerootCursor (retainedCarrierFuel input))
      (frame.frame.cursorAt slot) (frame.childAt slot) (frame.stages slot).a).1
  apply LocalizedRerootCursor.ext
  · apply input.molecularFrameUnit_injective_on_simpleBonded_carrier single
    rw [input.transportCursor_occurrence, input.molecularFrameUnit_transport,
      slot_unit input mol single c node data state left rootAddress current,
      slot_unit input mol single c node data state right rootAddress current]
    simp [transportOccurrenceUnit, fixed, sent]
  · rw [input.transportCursor_previous?, previous, previous, Option.map_some]
    exact congrArg some (rootOccurrence_fixed input mol single c node data rootAddress current e fixed)


/-- The physical reader law has only to hold at the actual real reads of one arm.
Both compared keys are the original compilation's own keys and own common window. -/
theorem rawState_priorTie_of_reflected_reads (state : OccurrenceAuxState)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (e : input.moleculeGraph.Aut) (left right : Fin 4)
    (fixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
    (sent : (e : Equiv.Perm input.Atom) (referenceAt input mol c node data left) =
      referenceAt input mol c node data right)
    (reads : ReadsAgree input.moleculeGraph e (rawStateDescriptorMap input state).reflect
      (rawStateDescriptorMap input state) (input.molecularFrameUnit data.target.1)
      ((rootFrame input mol single c node data state).actualArmGraphs left)) :
    (ofLex (rawStateKeys input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left)).1 =
    (ofLex (rawStateKeys input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right)).1 := by
  let frame := rootFrame input mol single c node data state
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  have h := priorKey_relabel_of_cursor_transport input single
    (rawStateDescriptorMap input state) (rawStateDescriptorMap input state)
    (rawStateDescriptorMap input state).reflect data.target frame unit rfl e left right
    (rootOccurrence_fixed input mol single c node data rootAddress current e fixed)
    (rootSlot_transport input mol single c node data state rootAddress current e left right fixed sent)
    reads frame.W frame.D
  rw [LocalizedRetainedDescriptorTransport.retainedCompleteLigandPriorKeyAt_reflect] at h
  exact h.symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.priorKey_relabel_of_cursor_transport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.target_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.target_unit
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.slot_unit
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.rootOccurrence_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.rootSlot_transport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel.rawState_priorTie_of_reflected_reads
