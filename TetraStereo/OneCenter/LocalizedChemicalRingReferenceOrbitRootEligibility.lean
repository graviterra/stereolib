import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
The actual empty-state root selector admits exactly its four neighboring atoms.
Two explicit graph symmetries force the two ordinary tied pairs. The converse follows
from actual occurrence-frame readback and the certified root neighbor inventory.
This is membership, not a claim about reference order or agreement of their readings.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootEligibility

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitArmSymmetry LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingMovedSlotEligibility
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedGenericMarkedRecalculation (eligibleOf)

noncomputable section

def rootEligible : List Nat :=
  eligibleOf rootData.atoms
    ((order certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData).map rootData.read.index)
    (adjacent certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData)

private theorem first_pair_eligible (a : Fin 46) (member : a = 28 ∨ a = 29) :
    a.val ∈ rootEligible := by
  apply moved_neighbor_eligible certified mol structure_agreement admissible supported single_bonded
    physicalAut rootCenter (canonicalCenterRoot 0) rootData (reached_root mol 0 (by decide))
    raw_root_history_fixed a
  · rcases member with rfl | rfl <;> decide +kernel
  · rcases member with rfl | rfl <;> decide +kernel

private theorem second_pair_eligible (a : Fin 46) (member : a = 30 ∨ a = 31) :
    a.val ∈ rootEligible := by
  apply moved_neighbor_eligible certified mol structure_agreement admissible supported single_bonded
    otherPhysicalAut rootCenter (canonicalCenterRoot 0) rootData (reached_root mol 0 (by decide))
    other_root_history_fixed a
  · rcases member with rfl | rfl <;> decide +kernel
  · rcases member with rfl | rfl <;> decide +kernel

/-- Every and only actual root neighbor is eligible; no key tie or selector premise remains. -/
theorem root_eligible_iff (value : Nat) :
    value ∈ rootEligible ↔ value ∈ ([28, 29, 30, 31] : List Nat) := by
  constructor
  · intro member
    change value ∈ eligibleOf rootData.atoms
      ((order certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData).map rootData.read.index)
      (adjacent certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData) at member
    rw [eligible_eq] at member
    obtain ⟨slot, _, same⟩ := List.mem_map.mp member
    rw [← same]
    have neighbor := physical.ligandAtomAt_adj rootCenter (rootData.ligandOf slot)
    have finite (a : Fin 46) : graph.Adj 0 a → a.val ∈ ([28, 29, 30, 31] : List Nat) := by
      fin_cases a <;> decide +kernel
    exact finite _ neighbor
  · intro member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact first_pair_eligible 28 (Or.inl rfl)
    · exact first_pair_eligible 29 (Or.inr rfl)
    · exact second_pair_eligible 30 (Or.inl rfl)
    · exact second_pair_eligible 31 (Or.inr rfl)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootEligibility

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootEligibility.root_eligible_iff
