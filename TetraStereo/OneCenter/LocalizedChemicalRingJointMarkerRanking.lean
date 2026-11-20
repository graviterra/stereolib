import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Total joint-marker comparison at actual detected frames

At a real detected occurrence of a finite single-bond input, the concrete joint comparator
is a linear-order comparison of the independent ordinary key followed by its actually computed
joint marker. Its sort therefore succeeds, returns all four slots and has consistent adjacent
comparisons. Rings, arbitrary accumulated references, and arbitrary tetrahedral auxiliary states
are admitted. The physical meaning of that generated state remains a separate obligation.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerOperations

abbrev RefinedKey := Lex (CompleteLigandRule5Key × JointMarker)

private theorem natList_compare_lt_iff (left right : List Nat) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) left right

private theorem natList_compare_eq_iff (left right : List Nat) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare (fun _ _ => compare_eq_iff_eq) left right

private theorem marker_compare_lt_iff (left right : MarkerKey) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare natList_compare_lt_iff natList_compare_eq_iff left right

private theorem marker_compare_eq_iff (left right : MarkerKey) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare natList_compare_eq_iff left right

private theorem joint_compare_lt_iff (left right : JointMarker) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare marker_compare_lt_iff marker_compare_eq_iff left right

private theorem joint_compare_eq_iff (left right : JointMarker) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare marker_compare_eq_iff left right

theorem refined_compare_lt_iff (left right : RefinedKey) :
    compare left right = .lt ↔ left < right :=
  then_eq_lt_iff_lex compare compare completeLigandRule5Key_compare_lt_iff
    completeLigandRule5Key_compare_eq_iff joint_compare_lt_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem refined_compare_eq_iff (left right : RefinedKey) :
    compare left right = .eq ↔ left = right :=
  then_eq_eq_iff_lex compare compare completeLigandRule5Key_compare_eq_iff joint_compare_eq_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

variable (input : CertifiedLocalizedCIPInput)
noncomputable section
variable (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat)

abbrev frames := rawStateFrames input single state target real unit targetUnit

/-- Proof-only names for the actual successfully computed keys. -/
def compiled (slot : Fin 4) : JointPromotedKey input :=
  Classical.choose (buildJoint?_exists input target (rawStateView input state target) references W D
    ((frames input single state target real unit targetUnit).frame.cursorAt slot)
    (LocalizedMarkedRetainedPromotedRanking.slot_valid input single state target real unit targetUnit slot))

theorem compiled_built (slot : Fin 4) :
    buildJoint? input target (rawStateView input state target) references W D
        (2 * (retainedCarrierFuel input + 1))
        ((frames input single state target real unit targetUnit).frame.cursorAt slot) =
      some (compiled input single state target real unit targetUnit references W D slot) :=
  Classical.choose_spec (buildJoint?_exists input target (rawStateView input state target) references W D
    ((frames input single state target real unit targetUnit).frame.cursorAt slot)
    (LocalizedMarkedRetainedPromotedRanking.slot_valid input single state target real unit targetUnit slot))

theorem compiled_prior (slot : Fin 4) :
    (compiled input single state target real unit targetUnit references W D slot).prior =
      (frames input single state target real unit targetUnit).compounds slot := by
  have actual := buildJoint?_prior input target (rawStateView input state target) references W D _ _ _
    (compiled_built input single state target real unit targetUnit references W D slot)
  unfold ordinaryKey? at actual
  rw [rawStateView_eq_molecularView,
    (frames input single state target real unit targetUnit).compoundBuilt slot] at actual
  exact (Option.some.inj actual).symm

/-- Independent ordinary signature followed by the actual joint marker. -/
def refinedKey (slot : Fin 4) : RefinedKey :=
  toLex (rawStateKeys input single state target real unit targetUnit slot,
    (compiled input single state target real unit targetUnit references W D slot).markers)

theorem jointBefore_eq_refined (left right : Fin 4) :
    jointBefore input state target
        (frames input single state target real unit targetUnit).frame references W D left right =
      some (compare (refinedKey input single state target real unit targetUnit references W D left)
        (refinedKey input single state target real unit targetUnit references W D right)) := by
  have joint : compareJointAt? input target (rawStateView input state target) references W D
        ((frames input single state target real unit targetUnit).frame.cursorAt left)
        ((frames input single state target real unit targetUnit).frame.cursorAt right) =
      some (compare (refinedKey input single state target real unit targetUnit references W D left)
        (refinedKey input single state target real unit targetUnit references W D right)) := by
    simp only [compareJointAt?,
      compiled_built input single state target real unit targetUnit references W D,
      Option.bind_eq_bind, Option.bind_some]
    unfold compareJointKeys
    rw [compiled_prior input single state target real unit targetUnit references W D left,
      compiled_prior input single state target real unit targetUnit references W D right,
      (frames input single state target real unit targetUnit).fullOrdering
        (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit left right]
    rfl
  rw [jointBefore, rawStateBefore_eq_keys input single state target real unit targetUnit left right]
  simp only [Option.bind_some]
  rw [joint]
  change (if compare (rawStateKeys input single state target real unit targetUnit left)
      (rawStateKeys input single state target real unit targetUnit right) = .eq
    then some ((compare (rawStateKeys input single state target real unit targetUnit left)
      (rawStateKeys input single state target real unit targetUnit right)).then _)
    else some (compare (rawStateKeys input single state target real unit targetUnit left)
      (rawStateKeys input single state target real unit targetUnit right))) = _
  change _ = some ((compare (rawStateKeys input single state target real unit targetUnit left)
    (rawStateKeys input single state target real unit targetUnit right)).then _)
  cases compare (rawStateKeys input single state target real unit targetUnit left)
    (rawStateKeys input single state target real unit targetUnit right) <;> rfl

/-- Sorting the actual comparator succeeds without a desired-order or successful-sort premise. -/
theorem joint_sort_eq :
    sortBy? (jointBefore input state target
      (frames input single state target real unit targetUnit).frame references W D)
      (List.finRange 4) =
    some (keyOrder (refinedKey input single state target real unit targetUnit references W D)
      (List.finRange 4)) := by
  have callback := funext fun left => funext fun right =>
    jointBefore_eq_refined input single state target real unit targetUnit references W D left right
  rw [callback, sortBy?_key compare refined_compare_lt_iff]

/-- The concrete partition includes every slot and all adjacent comparisons are consistent. -/
theorem joint_partition_exists :
    ∃ sorted adjacent count,
      partitionBy? (rawStateBefore input state target
        (frames input single state target real unit targetUnit).frame)
        (jointBefore input state target
          (frames input single state target real unit targetUnit).frame references W D)
        (List.finRange 4) = some (sorted, adjacent, count) ∧
      sorted.Perm (List.finRange 4) ∧
      ∀ decision ∈ adjacent, decision = some Ordering.gt ∨ decision = some Ordering.eq := by
  let key := refinedKey input single state target real unit targetUnit references W D
  let sorted := keyOrder key (List.finRange 4)
  have callback := funext fun left => funext fun right =>
    jointBefore_eq_refined input single state target real unit targetUnit references W D left right
  obtain ⟨count, hc⟩ := LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?_exists
    (rawStateBefore input state target (frames input single state target real unit targetUnit).frame)
    (jointBefore input state target (frames input single state target real unit targetUnit).frame
      references W D)
    (fun left right => ⟨_, rawStateBefore_eq_keys input single state target real unit targetUnit left right⟩)
    (fun left right => ⟨_, jointBefore_eq_refined input single state target real unit targetUnit references W D left right⟩)
    sorted
  refine ⟨sorted, adjacentBy (jointBefore input state target
      (frames input single state target real unit targetUnit).frame references W D) sorted,
    count, ?_, keyOrder_perm key _, ?_⟩
  · unfold partitionBy?
    rw [joint_sort_eq input single state target real unit targetUnit references W D]
    change (LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?
      (rawStateBefore input state target (frames input single state target real unit targetUnit).frame)
      (jointBefore input state target (frames input single state target real unit targetUnit).frame
        references W D) sorted).bind (fun n => some (sorted,
          adjacentBy (jointBefore input state target
            (frames input single state target real unit targetUnit).frame references W D) sorted,
          n)) = _
    rw [hc]
    rfl
  · rw [callback]
    exact adjacentBy_key_consistent compare refined_compare_lt_iff refined_compare_eq_iff
      key sorted (keyOrder_pairwise key _)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.refined_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.refined_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.compiled_built
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.compiled_prior
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.jointBefore_eq_refined
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.joint_sort_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking.joint_partition_exists
