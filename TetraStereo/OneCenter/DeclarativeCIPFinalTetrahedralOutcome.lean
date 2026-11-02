import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralAssignment
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent optional tetrahedral results. A missing assignment means that no complete
declarative priority ranking with a geometric descriptor exists; it is not defined by a runtime
failure. Present assignments retain the independent letter and Rule-5 case relation. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open CertifiedLocalizedCIPInput

universe u
noncomputable section
variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

def FinalTetrahedralOutcome (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit)
    (unit : Unit) : Option LocalizedAuxiliaryLabel → Prop
  | none => ¬ ∃ descriptor, problem.DescriptorJudgment auxiliary unit descriptor
  | some label => FinalTetrahedralAssignment problem auxiliary unit label

theorem finalOutcome_iff_some_of_unique_assignment
    (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit) (unit : Unit)
    (label : LocalizedAuxiliaryLabel)
    (assigned : FinalTetrahedralAssignment problem auxiliary unit label)
    (unique : ∀ other, FinalTetrahedralAssignment problem auxiliary unit other → other = label)
    (outcome : Option LocalizedAuxiliaryLabel) :
    FinalTetrahedralOutcome problem auxiliary unit outcome ↔ outcome = some label := by
  cases outcome with
  | none =>
      constructor
      · intro absent
        obtain ⟨rs, judgment, _⟩ := assigned
        exact (absent ⟨rsDescriptor rs, judgment⟩).elim
      · intro impossible
        cases impossible
  | some other =>
      constructor
      · intro h
        exact congrArg some (unique other h)
      · intro equality
        cases Option.some.inj equality
        exact assigned

theorem finalOutcome_iff_none_of_no_judgment
    (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit) (unit : Unit)
    (absent : ¬ ∃ descriptor, problem.DescriptorJudgment auxiliary unit descriptor)
    (outcome : Option LocalizedAuxiliaryLabel) :
    FinalTetrahedralOutcome problem auxiliary unit outcome ↔ outcome = none := by
  cases outcome with
  | none => exact ⟨fun _ => rfl, fun _ => absent⟩
  | some label =>
      constructor
      · rintro ⟨rs, judgment, _⟩
        exact (absent ⟨rsDescriptor rs, judgment⟩).elim
      · intro impossible
        cases impossible

/-- Two distinct ligands with neither strict priority direction prevent every complete ranking,
independently of the orientation predicate. -/
theorem no_descriptorJudgment_of_unordered_pair
    (problem : Problem Atom Unit) (auxiliary : DescriptorMap Unit) (unit : Unit)
    (left right : Fin 4) (different : left ≠ right)
    (notLeft : ¬ problem.Higher auxiliary unit left right)
    (notRight : ¬ problem.Higher auxiliary unit right left) :
    ¬ ∃ descriptor, problem.DescriptorJudgment auxiliary unit descriptor := by
  rintro ⟨descriptor, ranking, ranked, _orientation⟩
  have distinctPositions : ranking.symm left ≠ ranking.symm right :=
    fun eq => different (ranking.symm.injective eq)
  rcases lt_or_gt_of_ne distinctPositions with before | after
  · apply notLeft
    simpa only [Equiv.apply_symm_apply] using ranked _ _ before
  · apply notRight
    simpa only [Equiv.apply_symm_apply] using ranked _ _ after

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.finalOutcome_iff_some_of_unique_assignment
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.finalOutcome_iff_none_of_no_judgment
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.no_descriptorJudgment_of_unordered_pair
