import TetraStereo.OneCenter.LocalizedChemicalRingJointOrientationExecution
import TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal
import TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual selected slots lie in the moving orbit of a nontrivial even symmetry fixing
history and all retained references. Reading invariance therefore makes all selected readings
equal, without an extra selected-population covariance hypothesis. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedReadingOrbit

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots)
open LocalizedChemicalRingJointOrientationExecution (selected_parent selected_fixed_context_odd)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action)
open LocalizedChemicalRingFixedParentParity (local_dichotomy)
open LocalizedChemicalRingFinalEntryCorrection (slot_fixed)
open LocalizedChemicalRingThreeCycleConsensus (readings_eq)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (references : List input.Atom)
  (branch : TiedRootBranch input data.target) (state : OccurrenceAuxState)
  (e : input.detectedMultiCenterMolecule.Aut)
  (centerFixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
  (historyFixed : ∀ atom ∈ data.target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom)
  (marksFixed : ∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom)
  (moved : ∃ atom, input.moleculeGraph.Adj c.1 atom ∧ (e : Equiv.Perm input.Atom) atom ≠ atom)
  (even : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1)

include branch centerFixed historyFixed marksFixed moved even in
/-- A selected reference cannot be fixed by this even symmetry: two fixed neighboring
atoms would make the nontrivial local action odd. -/
theorem selected_moved (slot : Fin 4)
    (selected : slot ∈ selectedSlots input mol single c node data state references) :
    input.detectedMultiCenterMolecule.ligandPermAt e c (data.ligandOf slot) ≠ data.ligandOf slot := by
  intro fixedSlot
  have fixedAtom : (e : Equiv.Perm input.Atom) (referenceAt input mol c node data slot) =
      referenceAt input mol c node data slot := by
    have transport := input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt e c
      (data.ligandOf slot)
    rw [show input.detectedMultiCenterMolecule.centerPerm e c = c from Subtype.ext centerFixed,
      fixedSlot] at transport
    exact transport.symm
  have odd := selected_fixed_context_odd input mol single c node data references branch state slot
    selected e centerFixed historyFixed (fun atom member => by
      rcases List.mem_append.mp member with prior | last
      · exact marksFixed atom prior
      · have same := List.mem_singleton.mp last
        simpa only [same] using fixedAtom) moved
  rw [even] at odd
  norm_num at odd

include branch centerFixed historyFixed marksFixed moved even in
/-- The actual selected population is contained in one orbit. Successful and failed readings
are both covered; only pointwise reading transport remains for the physical evaluator. -/
theorem selected_readings_equal {α : Type*} (reading : Fin 4 → α)
    (transport : ∀ slot, reading (slotAction input mol e c node data slot) = reading slot)
    (i j : Fin 4)
    (selectedI : i ∈ selectedSlots input mol single c node data state references)
    (selectedJ : j ∈ selectedSlots input mol single c node data state references) :
    reading j = reading i := by
  obtain ⟨parent, member, adjacent, _⟩ := selected_parent input mol single c node data references
    branch state i selectedI
  obtain ⟨parentSlot, atParent, cases⟩ := local_dichotomy input.detectedMultiCenterMolecule e c
    centerFixed parent adjacent (historyFixed parent member) moved
  have fixed : input.detectedMultiCenterMolecule.ligandPermAt e c parentSlot = parentSlot :=
    slot_fixed input.detectedMultiCenterMolecule e c parentSlot (Subtype.ext centerFixed)
      (by rw [atParent]; exact historyFixed parent member)
  rcases cases with odd | ⟨_, _, allMoved⟩
  · rw [even] at odd
    norm_num at odd
  · have outside (k : Fin 4)
        (selected : k ∈ selectedSlots input mol single c node data state references) :
        data.ligandOf k ≠ parentSlot := by
      intro same
      have notFixed := selected_moved input mol single c node data references branch state e
        centerFixed historyFixed marksFixed moved even k selected
      exact notFixed (by rw [same, fixed])
    have action : ∀ k, reading (data.ligandOf.symm
        (input.detectedMultiCenterMolecule.ligandPermAt e c k)) = reading (data.ligandOf.symm k) := by
      intro k
      simpa only [slotAction, Equiv.trans_apply, Equiv.apply_symm_apply] using
        transport (data.ligandOf.symm k)
    simpa only [Equiv.symm_apply_apply] using readings_eq
      (input.detectedMultiCenterMolecule.ligandPermAt e c) parentSlot fixed allMoved
      (fun k => reading (data.ligandOf.symm k)) action (data.ligandOf i) (data.ligandOf j)
      (outside i selectedI) (outside j selectedJ)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedReadingOrbit

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedReadingOrbit.selected_moved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedReadingOrbit.selected_readings_equal
