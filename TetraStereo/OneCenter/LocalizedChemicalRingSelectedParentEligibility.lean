import TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Beneath a Rule-1a-tied carrier root branch, the actual incoming frame slot is absent
from the actual eligible reference population. Parent separation, full-to-constitutional
comparison and tied-run membership provide the exclusion; no reference-selection premise
is added. The claim is for the actual empty-state ordinary stage. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedRanking LocalizedChemicalRingOrderingTransport
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedCyclicGeneralRigidPriority
open LocalizedMarkedRetainedPromotedKey

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

/-- Actual eligible references are precisely slots with another equal empty-state key. -/
theorem eligible_iff_other (slot : Fin 4) :
    slot ∈ eligibleSlots input mol single c node data ↔
      ∃ other, other ≠ slot ∧ ordinaryKeys input mol single c node data other =
        ordinaryKeys input mol single c node data slot := by
  unfold eligibleSlots adjacent order
  rw [tiedEntries_mem compare completeLigandRule5Key_compare_eq_iff _ _
    ((keyOrder_perm _ _).nodup_iff.mpr (List.nodup_finRange 4)) (keyOrder_pairwise _ _)]
  constructor
  · rintro ⟨_, other, _, different, equal⟩
    exact ⟨other, different, equal⟩
  · rintro ⟨other, different, equal⟩
    exact ⟨(keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange slot), other,
      (keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange other), different, equal⟩

theorem parent_not_eligible (branch : TiedRootBranch input data.target) :
    ∃ parent : Fin 4,
      IsLocalizedActualFrameParentCursor input data.target
        ((frames input single [] data.target data.real
          ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt parent) ∧
      parent ∉ eligibleSlots input mol single c node data := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let frame := frames input single [] data.target data.real unit rfl
  have computed : input.localizedOccurrenceFourLigandFrame? data.target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? data.target]
    exact frame.frameComputed
  obtain ⟨parent, parentClass, others⟩ := parentSlot_separated_of_rootArmRule1aTie input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie data.target data.real branch.inside frame.frame computed
    branch.nonroot
  refine ⟨parent, parentClass, ?_⟩
  intro member
  obtain ⟨other, different, equal⟩ := (eligible_iff_other input mol single c node data parent).mp member
  change frame.retainedKeys unit other = frame.retainedKeys unit parent at equal
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input []) single unit rfl other parent
  rw [equal, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have constitutional := constitutional_eq_of_full_eq (frame.compounds other) (frame.compounds parent) full
  have ordinaryBuilt (slot : Fin 4) : ordinaryKey? input data.target
      (input.molecularView (rawStateDescriptorMap input []) data.target)
      (frame.stages slot).a.tree.source = some (frame.compounds slot) := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.compoundBuilt slot
  have sameL := subtree_constitution_eq_ordinary (frame.stages other).a.trace data.target
    (input.molecularView (rawStateDescriptorMap input []) data.target) (frame.compounds other) (ordinaryBuilt other)
  have sameR := subtree_constitution_eq_ordinary (frame.stages parent).a.trace data.target
    (input.molecularView (rawStateDescriptorMap input []) data.target) (frame.compounds parent) (ordinaryBuilt parent)
  have tied := (ruleMajor_compare_congr _ _ _ _ sameL sameR).trans constitutional
  exact ((others other different).2).symm _ _ _ _ _ _ _ _
    (frame.stages other).a.built (frame.stages parent).a.built tied

end
end TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility.eligible_iff_other
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility.parent_not_eligible
