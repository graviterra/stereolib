import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual raw frame determines all four slot identities; none is supplied as a premise. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFrameSlots

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingProperRotationConsensus (referenceAt_injective)

noncomputable section

/-- Every actual occurrence-data frame has a unique slot for each raw atom 4,5,6,7. -/
theorem left_slots_by_raw_atom
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter) :
    ∃ q : Equiv.Perm (Fin 4),
      ∀ i, (referenceAt (certified true) mol c leftCenter data (q i)).val = 4 + i.val := by
  have atoms : data.atoms = [4, 5, 6, 7] :=
    Option.some.inj (data.rawFrame.symm.trans raw_frames.2.1)
  have range (slot : Fin 4) :
      4 ≤ (referenceAt (certified true) mol c leftCenter data slot).val ∧
      (referenceAt (certified true) mol c leftCenter data slot).val ≤ 7 := by
    have found := (data.read.atom slot).trans (data.atomAt_eq slot)
    change data.atoms[data.read.index slot]? =
      some (referenceAt (certified true) mol c leftCenter data slot).val at found
    have member := List.mem_of_getElem? found
    rw [atoms] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  let f : Fin 4 → Fin 4 := fun slot =>
    ⟨(referenceAt (certified true) mol c leftCenter data slot).val - 4,
      by have bound := range slot; omega⟩
  have injective : Function.Injective f := by
    intro a b same
    apply referenceAt_injective (certified true) mol c leftCenter data
    apply Fin.ext
    have values := congrArg Fin.val same
    change (referenceAt (certified true) mol c leftCenter data a).val - 4 =
      (referenceAt (certified true) mol c leftCenter data b).val - 4 at values
    have ra := range a
    have rb := range b
    omega
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective f
    ⟨injective, Finite.surjective_of_injective injective⟩
  refine ⟨e.symm, ?_⟩
  intro i
  have value := congrArg Fin.val (e.apply_symm_apply i)
  change (referenceAt (certified true) mol c leftCenter data (e.symm i)).val - 4 = i.val at value
  have bound := range (e.symm i)
  omega

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFrameSlots

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFrameSlots.left_slots_by_raw_atom
