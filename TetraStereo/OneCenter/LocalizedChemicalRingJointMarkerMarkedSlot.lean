import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Every retained frame atom is a singleton joint-key class

The zero-level bit of the actual built joint marker distinguishes its retained atom from every
other ligand slot, at any auxiliary state. A selected fallback reference therefore cannot already
be in the inherited context. This is the fixed-reference separation needed by the odd-stabilizer
argument; it does not assume chemical correctness of the supplied state.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerMarkedSlot

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerFrameExecution
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedStateReader

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (state : OccurrenceAuxState)
  (references : List input.Atom)

/-- A key tie cannot move a frame atom named by any retained reference coordinate. -/
theorem retained_slot_singleton (marked other : Fin 4)
    (member : referenceAt input mol c node data marked ∈ references)
    (tie : slotKeys input mol single c node data state references other =
      slotKeys input mol single c node data state references marked) : other = marked := by
  obtain ⟨index, indexBound, stored⟩ := List.mem_iff_getElem.mp member
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  have markers :
      (compiled input single state data.target data.real unit rfl references
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) other).markers =
      (compiled input single state data.target data.real unit rfl references
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) marked).markers :=
    congrArg (fun key : RefinedKey => (ofLex key).2) tie
  have bit (slot : Fin 4) := buildJoint?_bit input data.target (rawStateView input state data.target)
    references (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
    (2 * (retainedCarrierFuel input + 1))
    ((frames input single state data.target data.real unit rfl).frame.cursorAt slot)
    (compiled input single state data.target data.real unit rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) slot)
    (compiled_built input single state data.target data.real unit rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) slot) index indexBound
  have bits : referenceBit input references[index]
      ((frames input single state data.target data.real unit rfl).frame.cursorAt other) =
    referenceBit input references[index]
      ((frames input single state data.target data.real unit rfl).frame.cursorAt marked) := by
    rw [← bit other, ← bit marked, markers]
  by_contra different
  have differentAtoms : referenceAt input mol c node data other ≠
      referenceAt input mol c node data marked := by
    intro same
    exact different (data.ligandOf.injective
      (input.detectedMultiCenterMolecule.ligandAtomAt_injective c same))
  rw [stored] at bits
  have current (slot : Fin 4) :
      ((frames input single state data.target data.real unit rfl).frame.cursorAt
        slot).occurrence.1.node.current? = some (referenceAt input mol c node data slot) :=
    slot_current input mol single c node data state slot
  simp only [referenceBit, current,
    Option.some.injEq, if_neg differentAtoms] at bits
  cases bits

/-- An actual eligible fallback reference is fresh relative to the inherited marks. -/
theorem selected_reference_not_retained (slot : Fin 4)
    (selected : slot ∈ selectedSlots input mol single c node data state references) :
    referenceAt input mol c node data slot ∉ references := by
  intro member
  obtain ⟨other, different, tie⟩ :=
    (LocalizedChemicalRingJointMarkerEligibility.eligible_iff_other input single state data.target
      data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) slot).mp selected
  exact different (retained_slot_singleton input mol single c node data state references slot other member tie)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerMarkedSlot

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerMarkedSlot.retained_slot_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerMarkedSlot.selected_reference_not_retained
