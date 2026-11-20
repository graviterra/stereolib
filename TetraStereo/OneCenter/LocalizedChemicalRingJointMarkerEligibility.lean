import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking
import TetraStereo.OneCenter.LocalizedChemicalRingEligibleOrbit
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
# One eligible class for the actual joint comparison at any auxiliary state

Beneath a constitutionally tied root arm, the parent slot remains separated at every raw
auxiliary state and every accumulated reference vector. When nonempty, the eligible population
of the actual joint order forms one nonsingleton key class. The state may be the prepared generated
state; it need not be empty. Transitivity of the physical symmetry action on this class still
requires the reconstruction and orientation argument.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingJointMarkerRanking LocalizedChemicalRingOrderingTransport
open LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedCyclicGeneralRigidPriority
open LocalizedMarkedRetainedPromotedKey

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

/-- Constitutional parent separation survives every later descriptor state. -/
theorem parent_ordinary_singleton (branch : TiedRootBranch input target) :
    ∃ parent : Fin 4,
      IsLocalizedActualFrameParentCursor input target
        ((frames input single state target real unit targetUnit).frame.cursorAt parent) ∧
      ∀ other, other ≠ parent →
        rawStateKeys input single state target real unit targetUnit other ≠
          rawStateKeys input single state target real unit targetUnit parent := by
  let frame := frames input single state target real unit targetUnit
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frame.frameComputed
  obtain ⟨parent, parentClass, others⟩ := parentSlot_separated_of_rootArmRule1aTie input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie target real branch.inside frame.frame computed
    branch.nonroot
  refine ⟨parent, parentClass, ?_⟩
  intro other different equal
  change frame.retainedKeys unit other = frame.retainedKeys unit parent at equal
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit other parent
  rw [equal, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have constitutional := constitutional_eq_of_full_eq (frame.compounds other) (frame.compounds parent) full
  have ordinaryBuilt (slot : Fin 4) : ordinaryKey? input target
      (input.molecularView (rawStateDescriptorMap input state) target)
      (frame.stages slot).a.tree.source = some (frame.compounds slot) := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.compoundBuilt slot
  have sameL := subtree_constitution_eq_ordinary (frame.stages other).a.trace target
    (input.molecularView (rawStateDescriptorMap input state) target) (frame.compounds other) (ordinaryBuilt other)
  have sameR := subtree_constitution_eq_ordinary (frame.stages parent).a.trace target
    (input.molecularView (rawStateDescriptorMap input state) target) (frame.compounds parent) (ordinaryBuilt parent)
  have tied := (ruleMajor_compare_congr _ _ _ _ sameL sameR).trans constitutional
  exact ((others other different).2).symm _ _ _ _ _ _ _ _
    (frame.stages other).a.built (frame.stages parent).a.built tied

variable (references : List input.Atom) (W D : Nat)

/-- All accumulated marks refine the ordinary order, so the parent stays a singleton. -/
theorem parent_joint_singleton (branch : TiedRootBranch input target) :
    ∃ parent : Fin 4,
      IsLocalizedActualFrameParentCursor input target
        ((frames input single state target real unit targetUnit).frame.cursorAt parent) ∧
      ∀ other, other ≠ parent →
        refinedKey input single state target real unit targetUnit references W D other ≠
          refinedKey input single state target real unit targetUnit references W D parent := by
  obtain ⟨parent, isParent, separated⟩ :=
    parent_ordinary_singleton input single state target real unit targetUnit branch
  refine ⟨parent, isParent, ?_⟩
  intro other different equal
  exact separated other different (congrArg (fun key : RefinedKey => (ofLex key).1) equal)

/-- Eligible entries in the sorted actual slot partition, before mapping slots to raw atoms. -/
def eligibleSlots : List (Fin 4) :=
  let key := refinedKey input single state target real unit targetUnit references W D
  let sorted := keyOrder key (List.finRange 4)
  tiedEntries false sorted (adjacentBy (fun a b => some (compare (key a) (key b))) sorted)

/-- Membership in the actual partition is equality with a distinct partner key. -/
theorem eligible_iff_other (slot : Fin 4) :
    slot ∈ eligibleSlots input single state target real unit targetUnit references W D ↔
      ∃ other, other ≠ slot ∧
        refinedKey input single state target real unit targetUnit references W D other =
          refinedKey input single state target real unit targetUnit references W D slot := by
  unfold eligibleSlots
  rw [tiedEntries_mem compare refined_compare_eq_iff _ _
    ((keyOrder_perm _ _).nodup_iff.mpr (List.nodup_finRange 4)) (keyOrder_pairwise _ _)]
  constructor
  · rintro ⟨_, other, _, different, equal⟩
    exact ⟨other, different, equal⟩
  · rintro ⟨other, different, equal⟩
    exact ⟨(keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange slot), other,
      (keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange other), different, equal⟩

/-- All current-context eligible entries share one key, with no empty-state restriction. -/
theorem eligible_key_eq (branch : TiedRootBranch input target) (a b : Fin 4)
    (ha : a ∈ eligibleSlots input single state target real unit targetUnit references W D)
    (hb : b ∈ eligibleSlots input single state target real unit targetUnit references W D) :
    refinedKey input single state target real unit targetUnit references W D a =
      refinedKey input single state target real unit targetUnit references W D b := by
  obtain ⟨parent, _, separated⟩ :=
    parent_joint_singleton input single state target real unit targetUnit references W D branch
  exact LocalizedChemicalRingEligibleOrbit.key_eq_of_two_partners _ parent separated a b
    ((eligible_iff_other input single state target real unit targetUnit references W D a).mp ha)
    ((eligible_iff_other input single state target real unit targetUnit references W D b).mp hb)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility.parent_ordinary_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility.parent_joint_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility.eligible_iff_other
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility.eligible_key_eq
