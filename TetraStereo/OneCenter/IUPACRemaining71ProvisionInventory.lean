import TetraStereo.OneCenter.IUPACGlobalProvisionClassification
import TetraStereo.OneCenter.IUPACNext54ReviewedSemantics
import TetraStereo.OneCenter.IUPACPrimitive35ReviewedSemantics

set_option autoImplicit false

/-!
# Exact remaining descriptor-assignment work queue

The 2,452-row operation partition contains only 152 descriptor-bearing rows.  The reviewed first
35 owns 35 of them and the reviewed next-54 batch owns another 46; its eight depiction,
nomenclature, and source-scope rows are correctly outside descriptor assignment.  This module
freezes the exact remaining 71-row positive queue:

* 56 non-polyhedral P-93 configuration provisions;
* 12 P-94 conformation provisions; and
* 3 atomic-number/weight/mass authority-data provisions.

The exactness and disjointness theorems make this a complement calculation, not a curated claim.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def next54DescriptorBearingProvisions : List IUPACNormativeProvision :=
  next54SequenceRuleProvisions ++
    next54PerceptionProvisions ++
      next54SpatialDescriptorProvisions

@[simp] theorem next54DescriptorBearingProvisionCount :
    next54DescriptorBearingProvisions.length = 46 := by
  rfl

def reviewed81DescriptorBearingProvisions : List IUPACNormativeProvision :=
  primitive35Provisions ++ next54DescriptorBearingProvisions

@[simp] theorem reviewed81DescriptorBearingProvisionCount :
    reviewed81DescriptorBearingProvisions.length = 81 := by
  simp [reviewed81DescriptorBearingProvisions]

def remainingP93DescriptorProvisions : List IUPACNormativeProvision :=
  p93GeneralSemanticsSlice ++
    p93NoncarbonTetrahedraSemanticsSlice ++
      p93AcyclicSemanticsSlice ++
        p93CyclicSemanticsSlice

@[simp] theorem remainingP93DescriptorProvisionCount :
    remainingP93DescriptorProvisions.length = 56 := by
  rfl

def remaining71DescriptorBearingProvisions : List IUPACNormativeProvision :=
  remainingP93DescriptorProvisions ++
    p94SemanticsSlice ++
      descriptorAssignmentAuthorityDataProvisions

@[simp] theorem remaining71DescriptorBearingProvisionCount :
    remaining71DescriptorBearingProvisions.length = 71 := by
  rfl

set_option maxRecDepth 16384 in
theorem next54DescriptorBearingProvisions_exact :
    next54DescriptorBearingProvisions.toFinset =
      (next54Provisions.filter descriptorAssignmentBearing?).toFinset := by
  decide

set_option maxRecDepth 16384 in
theorem reviewed81DescriptorBearingProvisions_nodup :
    reviewed81DescriptorBearingProvisions.Nodup := by
  decide

set_option maxRecDepth 16384 in
theorem remaining71DescriptorBearingProvisions_nodup :
    remaining71DescriptorBearingProvisions.Nodup := by
  decide

set_option maxRecDepth 16384 in
theorem reviewed81_disjoint_remaining71 :
    List.Disjoint reviewed81DescriptorBearingProvisions
      remaining71DescriptorBearingProvisions := by
  have remainingAvoidsReviewed :
      remaining71DescriptorBearingProvisions.Forall
        (fun provision => provision ∉ reviewed81DescriptorBearingProvisions) := by
    decide
  rw [List.disjoint_left]
  intro provision reviewed remaining
  exact (List.forall_iff_forall_mem.mp remainingAvoidsReviewed provision remaining) reviewed

/- The reviewed 81 and remaining 71 recover every descriptor-assignment-bearing row exactly. -/
set_option maxRecDepth 16384 in
theorem reviewed81_union_remaining71_exact :
    (reviewed81DescriptorBearingProvisions ++
      remaining71DescriptorBearingProvisions).toFinset =
        descriptorAssignmentBearingProvisions.toFinset := by
  let combined := reviewed81DescriptorBearingProvisions ++
    remaining71DescriptorBearingProvisions
  have combinedNodup : combined.Nodup :=
    reviewed81DescriptorBearingProvisions_nodup.append
      remaining71DescriptorBearingProvisions_nodup reviewed81_disjoint_remaining71
  have combinedBearing : combined.Forall
      (fun provision => descriptorAssignmentBearing? provision = true) := by
    decide
  apply Finset.eq_of_subset_of_card_le
  · intro provision member
    have listMember : provision ∈ combined := by simpa [combined] using member
    have bearing := List.forall_iff_forall_mem.mp combinedBearing provision listMember
    have globalMember := (mem_descriptorAssignmentBearingProvisions_iff provision).2 bearing
    simpa using globalMember
  · rw [List.toFinset_card_of_nodup combinedNodup,
      List.toFinset_card_of_nodup descriptorAssignmentBearingProvisions_nodup,
      descriptorAssignmentBearingProvisionCount]
    simp [combined]

/-- Membership form of the exact positive-work partition. -/
theorem descriptorBearing_mem_reviewed81_or_remaining71
    {provision : IUPACNormativeProvision}
    (bearing : DescriptorAssignmentBearing provision) :
    provision ∈ reviewed81DescriptorBearingProvisions ∨
      provision ∈ remaining71DescriptorBearingProvisions := by
  have allBearing : provision ∈ descriptorAssignmentBearingProvisions :=
    (mem_descriptorAssignmentBearingProvisions_iff provision).2 bearing
  have finMember : provision ∈ descriptorAssignmentBearingProvisions.toFinset := by
    simpa using allBearing
  rw [← reviewed81_union_remaining71_exact] at finMember
  simpa using finMember

/-- No row in the remaining queue can be borrowed from either reviewed compiler batch. -/
theorem remaining71_not_reviewed81
    {provision : IUPACNormativeProvision}
    (remaining : provision ∈ remaining71DescriptorBearingProvisions) :
    provision ∉ reviewed81DescriptorBearingProvisions := by
  intro reviewed
  exact (List.disjoint_left.mp reviewed81_disjoint_remaining71)
    reviewed remaining

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54DescriptorBearingProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.reviewed81DescriptorBearingProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71DescriptorBearingProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54DescriptorBearingProvisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.reviewed81_disjoint_remaining71
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.reviewed81_union_remaining71_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorBearing_mem_reviewed81_or_remaining71
