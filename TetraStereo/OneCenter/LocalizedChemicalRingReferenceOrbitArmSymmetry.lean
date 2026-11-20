import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput
import Mathlib.GroupTheory.OrderOfElement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-!
The explicit order-two constitutional automorphism used to choose the two tied root arms.
In the source JSON numbering it swaps 29/30, fixes 0,31,6, and swaps 4/5. Here all
indices use ReferenceOrbitInput's compact map (old 0 -> 0; old k -> k-1 for k >= 2).
The finite checks concern the actual certified molecular graph. No physical properness,
auxiliary label equality or evaluator result is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry

open LocalizedChemicalRingReferenceOrbitInput

private def swapFun (a : Fin 46) : Fin 46 :=
  ![0, 1, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11, 13, 12, 15, 14, 18, 19, 16, 17, 21, 20, 24, 25, 22, 23, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 37, 36, 38, 39, 41, 40, 44, 45, 42, 43] a

def armSwap : Equiv.Perm (Fin 46) where
  toFun := swapFun
  invFun := swapFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem armSwap_square : armSwap * armSwap = 1 := by
  apply Equiv.ext
  intro a
  fin_cases a <;> rfl

theorem armSwap_ne_one : armSwap ≠ 1 := by
  intro same
  have impossible := congrArg (fun p : Equiv.Perm (Fin 46) => p 28) same
  change (29 : Fin 46) = 28 at impossible
  exact (by decide : (29 : Fin 46) ≠ 28) impossible

theorem armSwap_order : orderOf armSwap = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime (by simpa only [pow_two] using armSwap_square) armSwap_ne_one

theorem armSwap_graph : graph.IsAutomorphism armSwap := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def graphAut : graph.Aut := ⟨armSwap, armSwap_graph⟩
def physicalAut : physical.Aut := graph.detectedMultiCenterAutOfGraphAut graphAut

theorem atom_actions :
    armSwap 0 = 0 ∧ armSwap 28 = 29 ∧ armSwap 29 = 28 ∧
    armSwap reference = reference ∧ armSwap 2 = 2 ∧ armSwap 5 = 5 ∧
    armSwap 3 = 4 ∧ armSwap 4 = 3 := by decide +kernel

theorem physicalAut_square : physicalAut * physicalAut = 1 := by
  apply Subtype.ext
  exact armSwap_square

theorem physical_actions :
    physicalAut.val (0 : Fin 46) = (0 : Fin 46) ∧
    physicalAut.val (28 : Fin 46) = (29 : Fin 46) ∧
    physicalAut.val (29 : Fin 46) = (28 : Fin 46) ∧
    physicalAut.val reference = reference :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem raw_root_history_fixed :
    ∀ value ∈ (canonicalCenterRoot 0).history,
      LocalizedChemicalRingPhysicalSense.relabelOf certified
        physicalAut.val value = value := by
  intro value member
  have same : value = 0 := by simpa only [canonicalCenterRoot, List.mem_singleton] using member
  subst value
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.armSwap_square
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.armSwap_ne_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.armSwap_order
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.armSwap_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.atom_actions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.physicalAut_square
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.physical_actions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry.raw_root_history_fixed
