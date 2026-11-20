import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-!
An explicit constitutional involution exchanges root arms 30/31 while fixing 28/29.
All indices use ReferenceOrbitInput's compact numbering. Its graph preservation is
checked on the actual certified input; no physical properness or label equality is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry

open LocalizedChemicalRingReferenceOrbitInput

private def swapFun (a : Fin 46) : Fin 46 :=
  ![0, 1, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11, 13, 12, 15, 14, 18, 19, 16, 17, 21, 20, 24, 25, 22, 23, 26, 27, 28, 29, 31, 30, 32, 33, 35, 34, 36, 37, 39, 38, 41, 40, 43, 42, 45, 44] a

def otherArmSwap : Equiv.Perm (Fin 46) where
  toFun := swapFun
  invFun := swapFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem otherArmSwap_square : otherArmSwap * otherArmSwap = 1 := by
  apply Equiv.ext
  intro a
  fin_cases a <;> rfl

theorem otherArmSwap_graph : graph.IsAutomorphism otherArmSwap := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def otherGraphAut : graph.Aut := ⟨otherArmSwap, otherArmSwap_graph⟩
def otherPhysicalAut : physical.Aut := graph.detectedMultiCenterAutOfGraphAut otherGraphAut

theorem other_physical_actions :
    otherPhysicalAut.val (0 : Fin 46) = (0 : Fin 46) ∧
    otherPhysicalAut.val (30 : Fin 46) = (31 : Fin 46) ∧
    otherPhysicalAut.val (31 : Fin 46) = (30 : Fin 46) ∧
    otherPhysicalAut.val (28 : Fin 46) = (28 : Fin 46) ∧
    otherPhysicalAut.val (29 : Fin 46) = (29 : Fin 46) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem other_root_history_fixed :
    ∀ value ∈ (canonicalCenterRoot 0).history,
      LocalizedChemicalRingPhysicalSense.relabelOf certified
        otherPhysicalAut.val value = value := by
  intro value member
  have same : value = 0 := by simpa only [canonicalCenterRoot, List.mem_singleton] using member
  subst value
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry.otherArmSwap_square
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry.otherArmSwap_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry.other_physical_actions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry.other_root_history_fixed
