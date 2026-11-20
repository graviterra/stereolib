import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! The full current comparison matrix is invariant under a physical root symmetry.
The auxiliary state is the actual generated child state, not an empty-state surrogate.
Its relabeling law follows from prepared recursion and strict-descendant geometry agreement.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (generated keys)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingJointMarkerCovariance
open LocalizedChemicalRingJointPreparedCovariance (StateRel)
open LocalizedChemicalRingJointOperationTransportExecution (actual_preparedChildren_map)
open LocalizedChemicalRingPreparedContextFacts (preparedChildrenUnder_keys_nodup)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport (AgreeOn)
open LocalizedChemicalRingFrameReadback (atomAt_transport)
open LocalizedChemicalRingResidualReadingTransport (mapNode_eq_of_history_fixed)
open LocalizedChemicalRingLookupTransport (lookup_transport)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedChemicalRingJointPreparedPhysicalTransport
  (map_eq_self_of_pointwise strictDescendant_closed strictDescendant_child)
open LocalizedChemicalRingMovedSlotEligibility (key_fixed_of_order_action)
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedGenericMarkedRecalculation (Geometry flatMap_congr_mem)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

include agreement admissible supported in
/-- Generated-state transport preserves the entire current key, via the full comparator. -/
theorem actual_slot_key_action
    (e : input.detectedMultiCenterMolecule.Aut)
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (historyFixed : ∀ atom ∈ node.history,
      relabelOf input (e : Equiv.Perm input.Atom) atom = atom)
    (references : List input.Atom)
    (marksFixed : ∀ reference ∈ references, (e : Equiv.Perm input.Atom) reference = reference)
    (depth : Nat) (geom : Geometry)
    (childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) geom) :
    ∃ p : Equiv.Perm (Fin 4),
      (∀ i, referenceAt input mol c node data (p i) =
        (e : Equiv.Perm input.Atom) (referenceAt input mol c node data i)) ∧
      ∀ i, keys input mol single c node data depth geom references (p i) =
        keys input mol single c node data depth geom references i := by
  let graphAut : input.moleculeGraph.Aut :=
    ⟨e, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule e⟩
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have fixedTarget : input.transportOccurrence single graphAut data.target = data.target := by
    have h := lookup_transport input mol agreement admissible supported single graphAut sym
      node reached data.target data.found
    rw [fixedNode, data.found] at h
    exact (Option.some.inj h).symm
  have fixedRaw : (references.map Fin.val).map
      (relabelOf input (graphAut : Equiv.Perm input.Atom)) = references.map Fin.val := by
    apply map_eq_self_of_pointwise
    intro value member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    rw [relabelOf_val, marksFixed atom present]
  have fixedRefs : references.map (graphAut : Equiv.Perm input.Atom) = references := by
    simpa using List.map_congr_left (f := (graphAut : Equiv.Perm input.Atom))
      (g := id) (fun atom present => marksFixed atom present)
  have childrenEq : generated input mol depth
      (pullback (relabelOf input (graphAut : Equiv.Perm input.Atom)) geom) node references =
      generated input mol depth geom node references := by
    unfold generated childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member =>
      LocalizedChemicalRingJointPreparedGeometryCongruence.preparedFacts_congr
        mol (jointOperations input mol) (StrictDescendant mol node)
        (strictDescendant_closed mol node) depth _ _ childAgree [] (references.map Fin.val)
        child (strictDescendant_child mol node child member)
  let state := generated input mol depth geom node references
  have stateRel : StateRel (relabelOf input (graphAut : Equiv.Perm input.Atom)) state state := by
    have h := actual_preparedChildren_map input mol agreement admissible supported single graphAut
      sym depth geom (references.map Fin.val) node reached
    rw [fixedNode, fixedRaw] at h
    change StateRel _ state (generated input mol depth _ node references) at h
    rwa [childrenEq] at h
  have unique : (state.map (·.key)).Nodup :=
    preparedChildrenUnder_keys_nodup mol (jointOperations input mol) admissible.1.1
      (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
      admissible.1.2 depth geom [] node (references.map Fin.val)
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := rawStateFrames input single state data.target data.real unit rfl
  have meaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff data.target
    execution.center).mp execution.centerComputed
  let ft := input.actualFrameSlotTransport single graphAut (Nat.le_succ _)
    data.target execution.center meaning
  have computed : input.localizedOccurrenceFourLigandFrame? data.target = some data.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact data.frameExec
  have sourceFrame : ft.sourceFrame = data.frame :=
    Option.some.inj (ft.sourceComputed.symm.trans computed)
  have imageFrame : ft.imageFrame = data.frame := by
    have h := ft.imageComputed
    rw [fixedTarget, computed] at h
    exact (Option.some.inj h).symm
  have executionFrame : execution.frame = data.frame :=
    Option.some.inj (execution.frameComputed.symm.trans data.frameExec)
  let key := keys input mol single c node data depth geom references
  have keyMatrix (a b : Fin 4) :
      jointBefore input state data.target data.frame references (retainedCarrierFuel input)
        (2 * (retainedCarrierFuel input + 1)) a b = some (compare (key a) (key b)) := by
    have h := jointBefore_eq_refined input single state data.target data.real unit rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) a b
    change jointBefore input state data.target execution.frame references _ _ a b = _ at h
    simpa only [executionFrame] using h
  have preserved (a b : Fin 4) :
      compare (key (ft.slotPerm a)) (key (ft.slotPerm b)) = compare (key a) (key b) := by
    have h := jointBefore_transport input single graphAut sym state state stateRel unique
      data.target execution.center ft references (retainedCarrierFuel input)
      (2 * (retainedCarrierFuel input + 1)) a b
    rw [fixedTarget, sourceFrame, imageFrame, fixedRefs, keyMatrix, keyMatrix] at h
    exact Option.some.inj h
  refine ⟨ft.slotPerm, ?_, ?_⟩
  · intro i
    have h := atomAt_transport input single graphAut data.target execution.center ft i
    rw [sourceFrame, imageFrame, data.atomAt_eq, data.atomAt_eq, Option.map_some,
      relabelOf_val] at h
    exact Fin.ext (Option.some.inj h)
  · apply key_fixed_of_order_action
    intro a b lower
    apply (refined_compare_lt_iff _ _).mp
    rw [preserved]
    exact (refined_compare_lt_iff _ _).mpr lower

include agreement admissible supported in
/-- Properness off the root derives current-key invariance under the actual root slot action.
No sign restriction at the root is required. -/
theorem root_current_key_action
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (e : input.detectedMultiCenterMolecule.Aut)
    (historyFixed : ∀ atom ∈ data.target.1.node.history,
      (e : Equiv.Perm input.Atom) atom = atom)
    (references : List input.Atom)
    (marksFixed : ∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom)
    (properOff : ∀ d : input.detectedMultiCenterMolecule.Center,
      d.1 ∉ data.target.1.node.history → relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (depth : Nat) (reflected : Bool) :
    ∀ i, keys input mol single c node data depth (observedGeometry input reflected) references
        (slotAction input mol e c node data i) =
      keys input mol single c node data depth (observedGeometry input reflected) references i := by
  have rawFixed : ∀ value ∈ node.history,
      relabelOf input (e : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history] at member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    rw [relabelOf_val, historyFixed atom present]
  have centerFixed := LocalizedChemicalRingResidualThreeCycleRefusal.center_fixed
    input mol e c node reached current rawFixed
  have base := LocalizedChemicalRingResidualOrientationStep.agreeOn_strictDescendants input mol
    agreement admissible supported single cfg e calibrated [] node c.1 current.symm
    (by simp) (by simp) reached (fun d _ different => properOff d (by
      rw [LocalizedChemicalRingJointPreparedRootPhysicalTransport.root_history
        input mol c node data rootAddress current]
      simpa using different))
  have agree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
      (observedGeometry input reflected) := by
    cases reflected with
    | false => exact base
    | true => simpa only [observedGeometry, Bool.true_eq, if_true, mirror_pullback] using base.mirror
  obtain ⟨p, atoms, invariant⟩ := actual_slot_key_action input mol agreement admissible supported
    single e c node data reached rawFixed references marksFixed depth _ agree
  have same (i : Fin 4) : p i = slotAction input mol e c node data i := by
    apply data.ligandOf.injective
    apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    exact (atoms i).trans (referenceAt_action input mol e c node data centerFixed i).symm
  intro i
  rw [← same i]
  exact invariant i

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance.actual_slot_key_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance.root_current_key_action
