import TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedReadingOrbit
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual selected fallback agreement under a proper nontrivial local rotation.
All descriptor states are the prepared evaluator's own states. Descendant agreement comes
from finite residual physical signs, and selected-reading agreement from the moving orbit.
Consequently an actual refusal has a failed selected fallback in this even case. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry referenceAt)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots)
open LocalizedChemicalRingJointPreparedExecution (generated fallback step)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action)
open LocalizedChemicalRingJointSelectedReadingOrbit (selected_readings_equal)
open LocalizedChemicalRingJointPreparedPhysicalTransport (actual_fallback_eq_of_even_slot)
open LocalizedChemicalRingResidualOrientationStep (agreeOn_strictDescendants)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport (AgreeOn)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (current : node.atom = c.1.val) (e : input.detectedMultiCenterMolecule.Aut)
  (centerFixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
  (historyFixed : ∀ atom ∈ data.target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom)
  (references : List input.Atom)
  (marksFixed : ∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom)
  (B : List input.Atom) (outside : c.1 ∉ B)
  (carried : ∀ atom ∈ B, atom.val ∈ node.history)
  (proper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph B c.1 d.1 → d.1 ≠ c.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
  (even : relativeSign input.detectedMultiCenterMolecule cfg e c = 1)

include agreement admissible supported single calibrated reached current historyFixed marksFixed
  outside carried proper even in
/-- Physical residual signs derive invariance of each actual fallback under the local action. -/
theorem fallback_action (depth : Nat) (reflected : Bool) (slot : Fin 4) :
    fallback input mol c node data depth (observedGeometry input reflected) references
      (slotAction input mol e c node data slot) =
      fallback input mol c node data depth (observedGeometry input reflected) references slot := by
  let graphAut : input.moleculeGraph.Aut :=
    ⟨e, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule e⟩
  have rawFixed : ∀ value ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history] at member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    rw [relabelOf_val, historyFixed atom present]
  have fixed := LocalizedChemicalRingResidualThreeCycleRefusal.center_fixed input mol e c node
    reached current rawFixed
  have base := agreeOn_strictDescendants input mol agreement admissible supported single cfg e
    calibrated B node c.1 current.symm outside carried reached proper
  have agree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
      (observedGeometry input reflected) := by
    cases reflected with
    | false => exact base
    | true => simpa only [observedGeometry, Bool.true_eq, if_true, mirror_pullback] using base.mirror
  exact actual_fallback_eq_of_even_slot input mol agreement admissible supported single cfg
    graphAut e rfl (structuralSymmetry_of_aut input mol agreement admissible supported e)
    calibrated c node current reached data reflected agree depth references rawFixed
    (fun atom member => congrArg Fin.val (marksFixed atom member)) slot
    (slotAction input mol e c node data slot)
    ((relabelOf_val input e (referenceAt input mol c node data slot)).trans
      (congrArg Fin.val (referenceAt_action input mol e c node data fixed slot).symm)) even

include agreement admissible supported single calibrated reached current centerFixed historyFixed
  marksFixed outside carried proper even in
/-- All actual selected readings agree, without supplied state correspondence or sorting laws. -/
theorem selected_fallbacks_equal (branch : TiedRootBranch input data.target)
    (moved : ∃ atom, input.moleculeGraph.Adj c.1 atom ∧ (e : Equiv.Perm input.Atom) atom ≠ atom)
    (depth : Nat) (reflected : Bool)
    (i j : Fin 4)
    (selectedI : i ∈ selectedSlots input mol single c node data
      (generated input mol depth (observedGeometry input reflected) node references) references)
    (selectedJ : j ∈ selectedSlots input mol single c node data
      (generated input mol depth (observedGeometry input reflected) node references) references) :
    fallback input mol c node data depth (observedGeometry input reflected) references j =
      fallback input mol c node data depth (observedGeometry input reflected) references i := by
  have localEven : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 := by
    rw [← LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg e c
      (Subtype.ext centerFixed)]
    exact even
  exact selected_readings_equal input mol single c node data references branch _ e centerFixed
    historyFixed marksFixed moved localEven _
    (fallback_action input mol agreement admissible supported single cfg calibrated c node data
      reached current e historyFixed references marksFixed B outside carried proper even depth reflected)
    i j selectedI selectedJ

include agreement admissible supported single calibrated reached current centerFixed historyFixed
  marksFixed outside carried proper even in
/-- In the even correction case, actual consensus refusal gives a failed selected fallback. -/
theorem refusal_has_failed_selected (branch : TiedRootBranch input data.target)
    (moved : ∃ atom, input.moleculeGraph.Adj c.1 atom ∧ (e : Equiv.Perm input.Atom) atom ≠ atom)
    (depth : Nat) (reflected : Bool)
    (refused : step input mol node depth (observedGeometry input reflected) references = none) :
    ∃ slot ∈ selectedSlots input mol single c node data
      (generated input mol depth (observedGeometry input reflected) node references) references,
      fallback input mol c node data depth (observedGeometry input reflected) references slot = none := by
  apply LocalizedChemicalRingJointPreparedExecution.step_none_failed_of_equal_readings
    input mol agreement admissible supported single c node data depth references cfg (calibrated c)
    reflected refused
  intro i memberI j memberJ
  exact (selected_fallbacks_equal input mol agreement admissible supported single cfg calibrated
    c node data reached current e centerFixed historyFixed references marksFixed B outside carried
    proper even branch moved depth reflected i j memberI memberJ).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings.fallback_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings.selected_fallbacks_equal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings.refusal_has_failed_selected
