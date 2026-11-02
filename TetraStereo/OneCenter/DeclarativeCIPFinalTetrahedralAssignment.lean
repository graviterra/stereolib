import TetraStereo.OneCenter.LocalizedActualOrderedRootDeclarativeDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Independent final tetrahedral assignments, including letter case

The geometric `Problem.DescriptorJudgment` determines the R/S letter.  The independent count of
distinct ligand pairs tied before Rule 5 determines its case.  This relation combines the two
without consulting an evaluator, a sorted runtime key, or a supplied final label.  It is separate
from the map of auxiliary occurrence descriptors that the chemical rule judgments read.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP

open CertifiedLocalizedCIPInput

universe u

noncomputable section
open scoped Classical

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Count each unordered pair of distinct ligand positions once, using independent rule ties. -/
def finalRule5PairCount (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit)
    (unit : Unit) : ℕ :=
  sourceEnantiomorphicPairCount fun i j =>
    i ≠ j ∧ problem.EarlierRulesTie auxiliary .rule5EnantiomorphicDescriptor unit i j

/-- The complete final tetrahedral descriptor, including independently determined letter case. -/
def FinalTetrahedralAssignment (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit)
    (unit : Unit) (label : LocalizedAuxiliaryLabel) : Prop :=
  ∃ rs : RS, problem.DescriptorJudgment auxiliary unit (rsDescriptor rs) ∧
    label = classifyTetrahedralRSPseudo rs (finalRule5PairCount problem auxiliary unit)

theorem finalRule5PairCount_eq_zero_of_noEarlierTie
    (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit) (unit : Unit)
    (noTie : ∀ i j : Fin 4, i ≠ j →
      ¬ problem.EarlierRulesTie auxiliary .rule5EnantiomorphicDescriptor unit i j) :
    finalRule5PairCount problem auxiliary unit = 0 := by
  have absent (i j : Fin 4) :
      ¬ (i ≠ j ∧ problem.EarlierRulesTie auxiliary .rule5EnantiomorphicDescriptor unit i j) :=
    fun h => noTie i j h.1 h.2
  change sourceEnantiomorphicPairCount _ = 0
  calc
    _ = sourceEnantiomorphicPairCount (fun _ _ : Fin 4 => False) :=
      sourceEnantiomorphicPairCount_congr_of_forall _ _
        (fun i j => iff_false_intro (absent i j))
    _ = 0 := by simp [sourceEnantiomorphicPairCount]

/-- Unique geometric meaning supplies a unique final classification, with no runtime premise. -/
theorem finalTetrahedralAssignment_existsUnique
    (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit) (unit : Unit)
    (rs : RS)
    (judgment : problem.DescriptorJudgment auxiliary unit (rsDescriptor rs))
    (unique : ∀ descriptor, problem.DescriptorJudgment auxiliary unit descriptor →
      descriptor = rsDescriptor rs) :
    ∃! label, FinalTetrahedralAssignment problem auxiliary unit label := by
  refine ⟨classifyTetrahedralRSPseudo rs (finalRule5PairCount problem auxiliary unit),
    ⟨rs, judgment, rfl⟩, ?_⟩
  rintro label ⟨other, hother, rfl⟩
  have heq : other = rs := rsDescriptor_injective (unique _ hother)
  rw [heq]

theorem finalTetrahedralAssignment_chiral_of_count_zero
    (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit) (unit : Unit)
    (rs : RS)
    (judgment : problem.DescriptorJudgment auxiliary unit (rsDescriptor rs))
    (count : finalRule5PairCount problem auxiliary unit = 0) :
    FinalTetrahedralAssignment problem auxiliary unit (.chiral rs) := by
  refine ⟨rs, judgment, ?_⟩
  rw [count]
  rfl

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.finalRule5PairCount_eq_zero_of_noEarlierTie
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.finalTetrahedralAssignment_existsUnique
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.finalTetrahedralAssignment_chiral_of_count_zero
