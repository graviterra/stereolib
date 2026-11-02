import TetraStereo.OneCenter.LocalizedRuleMajorActualCompoundComparison
import TetraStereo.OneCenter.LocalizedActualOrderedRootIndependentPriority
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The full independent prior key has its stated linear order. These laws identify the
native comparators used by the actual-refinement theorem with that order, rather than assuming
per-rule order laws. They apply equally to ties and to strict decisions. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open Rule4aTableBridge
open Certificate.CanonicalSphereKey (Key)
noncomputable section

private theorem readingLists_compare_lt_iff
    (left right : Lex (List (Key StereoLabel) × List (Key StereoLabel))) :
    compare left right = .lt ↔ left < right :=
  then_eq_lt_iff_lex compare compare listKey_compare_lt_iff listKey_compare_eq_iff
    listKey_compare_lt_iff (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

private theorem readingLists_compare_eq_iff
    (left right : Lex (List (Key StereoLabel) × List (Key StereoLabel))) :
    compare left right = .eq ↔ left = right :=
  then_eq_eq_iff_lex compare compare listKey_compare_eq_iff listKey_compare_eq_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completePriorSignature_compare_lt_iff (left right : CompletePriorSignature) :
    compare left right = .lt ↔ left < right :=
  then_eq_lt_iff_lex compare compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) readingLists_compare_lt_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completePriorSignature_compare_eq_iff (left right : CompletePriorSignature) :
    compare left right = .eq ↔ left = right :=
  then_eq_eq_iff_lex compare compare (fun _ _ => compare_eq_iff_eq) readingLists_compare_eq_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completeLigandPriorKey_compare_lt_iff (left right : CompleteLigandPriorKey) :
    compare left right = .lt ↔ left < right :=
  then_eq_lt_iff_lex compare compare pairKeyCompare_eq_lt_iff pairKeyCompare_eq_eq_iff
    completePriorSignature_compare_lt_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completeLigandPriorKey_compare_eq_iff (left right : CompleteLigandPriorKey) :
    compare left right = .eq ↔ left = right :=
  then_eq_eq_iff_lex compare compare pairKeyCompare_eq_eq_iff completePriorSignature_compare_eq_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completeLigandPriorKey_compare_gt_iff (left right : CompleteLigandPriorKey) :
    compare left right = .gt ↔ right < left := by
  have actual := eq_compare_of_iff (compare left right) left right
    (completeLigandPriorKey_compare_lt_iff left right)
    (completeLigandPriorKey_compare_eq_iff left right)
  rw [actual]
  exact compare_gt_iff_gt

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignature_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignature_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandPriorKey_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandPriorKey_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandPriorKey_compare_gt_iff
