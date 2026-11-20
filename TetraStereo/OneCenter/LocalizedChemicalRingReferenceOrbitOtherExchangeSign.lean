import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! An exchange of the O18 root branches fixing either O16 reference must reverse
center26. Molecular color/adjacency signatures derive the fixed neighbors; no supplied
orientation or generated-label premise is used. The sign is independent of configuration.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingTwoFixedNeighbors
open LocalizedPhysicalMarkedParityCompleteness

private theorem fix_single (e : graph.Aut) (pin atom : Fin 46)
    (fixed : e.val pin = pin) (unique : SignatureUnique graph [pin] atom) :
    e.val atom = atom := by
  apply fixed_of_signature graph e [pin] atom
  · intro a member
    have same : a = pin := List.mem_singleton.mp member
    simpa only [same] using fixed
  · exact unique

theorem fixed_other_frame (e : graph.Aut) (mark : Fin 46)
    (allowed : mark = 28 ∨ mark = 29) (fixedMark : e.val mark = mark) :
    e.val (26 : Fin 46) = (26 : Fin 46) ∧
      e.val (1 : Fin 46) = (1 : Fin 46) ∧ e.val (27 : Fin 46) = (27 : Fin 46) := by
  have fixed28 : e.val (28 : Fin 46) = (28 : Fin 46) := by
    rcases allowed with rfl | rfl
    · exact fixedMark
    · exact fix_single e 29 28 fixedMark (by unfold SignatureUnique; decide +kernel)
  have fixed29 := fix_single e 28 29 fixed28 (by unfold SignatureUnique; decide +kernel)
  have fixed32 := fix_single e 28 32 fixed28 (by unfold SignatureUnique; decide +kernel)
  have fixed33 := fix_single e 29 33 fixed29 (by unfold SignatureUnique; decide +kernel)
  have fixed27 : e.val (27 : Fin 46) = (27 : Fin 46) := by
    apply fixed_of_signature graph e [32, 33] 27
    · intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact fixed32
      · exact fixed33
    · unfold SignatureUnique
      decide +kernel
  have fixed26 := fix_single e 27 26 fixed27 (by unfold SignatureUnique; decide +kernel)
  have fixed1 := fix_single e 26 1 fixed26 (by unfold SignatureUnique; decide +kernel)
  exact ⟨fixed26, fixed1, fixed27⟩

theorem other_exchange_odd (e : physical.Aut) (mark : Fin 46)
    (allowed : mark = 28 ∨ mark = 29) (fixedMark : e.val mark = mark)
    (entry : e.val (30 : Fin 46) = (31 : Fin 46)) :
    physical.centerPerm e otherCurrent = otherCurrent ∧
      permHandedness (physical.ligandPermAt e otherCurrent) = -1 := by
  let g : graph.Aut := ⟨e.val, e.2.1⟩
  obtain ⟨fixed26, fixed1, fixed27⟩ := fixed_other_frame g mark allowed fixedMark
  have moved34 : e.val (34 : Fin 46) ≠ (34 : Fin 46) := by
    intro fixed34
    have fixed30 := fix_single g 34 30 fixed34 (by unfold SignatureUnique; decide +kernel)
    have impossible := fixed30.symm.trans entry
    exact (by decide : (30 : Fin 46) ≠ 31) impossible
  exact local_odd_of_two_fixed_neighbors physical e otherCurrent fixed26
    (1 : Fin 46) (27 : Fin 46) (by decide) (by decide +kernel) (by decide +kernel)
    fixed1 fixed27 ⟨(34 : Fin 46), by decide +kernel, moved34⟩

theorem other_exchange_negative (configuration : physical.Configuration)
    (e : physical.Aut) (mark : Fin 46)
    (allowed : mark = 28 ∨ mark = 29) (fixedMark : e.val mark = mark)
    (entry : e.val (30 : Fin 46) = (31 : Fin 46)) :
    physical.centerPerm e otherCurrent = otherCurrent ∧
      relativeSign physical configuration e otherCurrent = -1 := by
  obtain ⟨fixed, odd⟩ := other_exchange_odd e mark allowed fixedMark entry
  refine ⟨fixed, ?_⟩
  unfold relativeSign transportedSign
  rw [fixed, odd]
  have square : physical.configurationSign configuration otherCurrent *
      physical.configurationSign configuration otherCurrent = 1 :=
    permHandedness_mul_self (configuration otherCurrent)
  nlinarith

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign.fixed_other_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign.other_exchange_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign.other_exchange_negative
