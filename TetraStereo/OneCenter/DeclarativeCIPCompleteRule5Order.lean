import TetraStereo.OneCenter.DeclarativeCIPCompleteRule5Signature
import TetraStereo.OneCenter.DeclarativeCIPCompleteLigandOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent molecular priority through Rule 5 and its reference-sensitivity criterion.
The priority exhausts the complete prior key, then every ordered absolute-R reading. The
reference-sensitivity proposition compares the independently obtained R/S streams; it is not
asserted here to characterize physical enantiomorphism. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)
open Rule4aTableBridge
noncomputable section
universe u

abbrev CompleteLigandRule5Key := Lex (CompleteLigandPriorKey × List (Key StereoLabel))

def completeLigandRule5KeyAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : Nat) :
    CompleteLigandRule5Key :=
  toLex (completeLigandPriorKeyAt molecule descriptorMap unit graph W D,
    completeRule5ReadingsAt molecule descriptorMap unit graph W D .senior)

/-- A strict Rule-5 decision sensitive to swapping the common reference. This is stated only
in terms of independent molecular observations, not the runtime pseudo flag. -/
def ReferenceSensitiveRule5PairAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : RootedDigraph Atom) (W D : Nat) : Prop :=
  completeLigandPriorKeyAt molecule descriptorMap unit left W D =
      completeLigandPriorKeyAt molecule descriptorMap unit right W D ∧
    completeRule5ReadingsAt molecule descriptorMap unit left W D .senior ≠
      completeRule5ReadingsAt molecule descriptorMap unit right W D .senior ∧
    compare (completeRule5ReadingsAt molecule descriptorMap unit left W D .senior)
        (completeRule5ReadingsAt molecule descriptorMap unit right W D .senior) ≠
      compare (completeRule5ReadingsAt molecule descriptorMap unit left W D .junior)
        (completeRule5ReadingsAt molecule descriptorMap unit right W D .junior)

theorem completeLigandRule5KeyAt_eq_of_faithful
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (parent ligand : Atom)
    {left right : RootedDigraph Atom}
    (faithfulL : left.FaithfulExactExpansion molecule parent ligand)
    (faithfulR : right.FaithfulExactExpansion molecule parent ligand) (W D : Nat) :
    completeLigandRule5KeyAt molecule descriptorMap unit left W D =
      completeLigandRule5KeyAt molecule descriptorMap unit right W D := by
  unfold completeLigandRule5KeyAt
  rw [completeLigandPriorKeyAt_eq_of_faithful molecule descriptorMap unit parent ligand faithfulL faithfulR W D,
    completeRule5ReadingsAt_eq_of_faithful molecule descriptorMap unit parent ligand faithfulL faithfulR W D]

theorem completeLigandRule5Key_compare_lt_iff (left right : CompleteLigandRule5Key) :
    compare left right = .lt ↔ left < right :=
  then_eq_lt_iff_lex compare compare completeLigandPriorKey_compare_lt_iff
    completeLigandPriorKey_compare_eq_iff listKey_compare_lt_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completeLigandRule5Key_compare_eq_iff (left right : CompleteLigandRule5Key) :
    compare left right = .eq ↔ left = right :=
  then_eq_eq_iff_lex compare compare completeLigandPriorKey_compare_eq_iff listKey_compare_eq_iff
    (ofLex left).1 (ofLex right).1 (ofLex left).2 (ofLex right).2

theorem completeLigandRule5Key_compare_gt_iff (left right : CompleteLigandRule5Key) :
    compare left right = .gt ↔ right < left := by
  have actual := eq_compare_of_iff (compare left right) left right
    (completeLigandRule5Key_compare_lt_iff left right)
    (completeLigandRule5Key_compare_eq_iff left right)
  rw [actual]
  exact compare_gt_iff_gt

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandRule5KeyAt_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandRule5Key_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandRule5Key_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandRule5Key_compare_gt_iff
