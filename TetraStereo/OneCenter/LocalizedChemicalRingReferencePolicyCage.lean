import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Executed nested-promotion chronology witness on the 15-atom cage

The root selects reference 3, reaches nearA, and nearA selects reference 5. We regenerate
its child maps independently at inherited reference 3 and nested reference 5. The first
map is empty; the second gives a successful near readback. No temporary labels or map
equality assumptions are inputs. This is a local chronology witness for the accepted cage
adapter, not equivalence of the CURRENT joint evaluator with either published policy.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage

open LocalizedRecursiveAuxiliaryPhysicalCompletion
open LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedHiddenParityMarkedProbe
open LocalizedHiddenParityPromotedReadback
open LocalizedGenericMarkedRecalculationCage
open LocalizedGenericMarkedRecalculation (eligibleOf)

/-- These are actual eligible lists, with the ordinary comparator results separately pinned
by `root_ordinary` and `nearA_ordinary` in the cage simulation. -/
theorem root_reference_selected :
    3 ∈ eligibleOf [1, 2, 3, 9] [1, 2, 3, 0] [some .gt, some .eq, some .gt] := by decide

theorem nested_reference_selected :
    5 ∈ eligibleOf [0, 5, 6, 7] [1, 2, 3, 0] [some .eq, some .eq, some .gt] := by decide

/-- The selected nested site lies on the actual root traversal, and both ordinary rankings
are the actual executable comparator results, not hypothetical frames. -/
theorem executed_selection_site :
    nearA ∈ cageRaw.canonicalChildren root0 ∧
    LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] root0 =
      some ([1, 2, 3, 0], [some .gt, some .eq, some .gt]) ∧
    LocalizedGenericMarkedRecalculation.ordinary? cageRaw 16 [] nearA =
      some ([1, 2, 3, 0], [some .eq, some .eq, some .gt]) :=
  ⟨nearA_is_canonical_child_of_root0, root_ordinary, nearA_ordinary⟩

noncomputable section

variable (P : List CartesianPoint3) (len : P.length = 15)

/-- Both sides generate their own child facts by recursion from the empty state. The inherited
map uses reference 3; the promotion-regenerated map uses reference 5. -/
def childMap (depth reference : Nat) : OccurrenceAuxState :=
  LocalizedGenericMarkedRecalculation.underWith cageRaw 16 (geomOf P len) [] nearA
    (LocalizedGenericMarkedRecalculation.facts cageRaw 16 (depth + 2)) reference

theorem inherited_childMap_empty (nondeg : Nondegenerate P len) (depth : Nat) :
    childMap P len depth 3 = [] := by
  unfold childMap LocalizedGenericMarkedRecalculation.underWith
  rw [tiedChildren_nearA]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [facts_oxA 5 (by decide), facts_oxA 6 (by decide), facts_oxA 7 (by decide),
    facts_farA 5 (by decide), facts_farA 6 (by decide), facts_farA 7 (by decide),
    descriptorFarA_root P len nondeg depth 5 3 (by decide) (by simp),
    descriptorFarA_root P len nondeg depth 6 3 (by decide) (by simp),
    descriptorFarA_root P len nondeg depth 7 3 (by decide) (by simp)]
  rfl

/-- This failure is a nonunique actual tracked ranking, not a fabricated missing label. -/
theorem inherited_near_readback (nondeg : Nondegenerate P len) (depth : Nat) :
    LocalizedGenericMarkedRecalculation.markedReadback? cageRaw 16 (geomOf P len)
      (childMap P len depth 3) nearA 5 = none := by
  rw [inherited_childMap_empty P len nondeg depth, markedReadback_empty]
  unfold visitReadback? visitRankedAtoms?
  rw [nearA_frameAtoms, near_mark5_tracked_output]
  rfl

/-- Actual nested regeneration produces the far auxiliary facts and a unique near ranking. -/
theorem regenerated_near_readback (nondeg : Nondegenerate P len) (depth : Nat) :
    LocalizedGenericMarkedRecalculation.markedReadback? cageRaw 16 (geomOf P len)
      (childMap P len depth 5) nearA 5 = some (jointLetterA P len) := by
  unfold childMap
  rw [underNearA P len nondeg depth 5 (by decide), markedReadback_eq]
  exact nearRecalcA P len nondeg 5 (by decide) true

/-- The independently regenerated maps are observably different on an executed nested
promotion: frozen inherited context refuses; recalculating under the nested reference succeeds. -/
theorem executed_chronology_disagreement (nondeg : Nondegenerate P len) (depth : Nat) :
    LocalizedGenericMarkedRecalculation.markedReadback? cageRaw 16 (geomOf P len)
        (childMap P len depth 3) nearA 5 ≠
      LocalizedGenericMarkedRecalculation.markedReadback? cageRaw 16 (geomOf P len)
        (childMap P len depth 5) nearA 5 := by
  rw [inherited_near_readback P len nondeg depth, regenerated_near_readback P len nondeg depth]
  simp

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.root_reference_selected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.nested_reference_selected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.childMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.inherited_childMap_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.inherited_near_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.regenerated_near_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.executed_chronology_disagreement

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCage.executed_selection_site
