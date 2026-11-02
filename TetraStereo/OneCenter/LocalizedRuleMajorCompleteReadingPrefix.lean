import TetraStereo.OneCenter.LocalizedRuleMajorStagePrefix
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cTableBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Earlier comparison columns for the two alternative readings of one actual branch.
These facts are derived from separately executed stages, including their recursive sorts. -/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open Rule4aTableBridge Rule4cObservationBridge
noncomputable section

private theorem scalar4a_project (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    projectCumulative 0 key.descriptor = scalar4a key := by
  unfold projectCumulative scalar4a
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro entry _
  rcases entry with ⟨address, values⟩
  cases values <;> rfl

theorem ruleMajorPrefix_one_scalar4a {input : CertifiedLocalizedCIPInput}
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (equal : input.ruleMajorPrefixObservable 1 left = input.ruleMajorPrefixObservable 1 right) :
    scalar4a left = scalar4a right := by
  have h := congrArg (fun value : RuleMajorPrefixObservable input.Atom => value.columns) equal
  simpa [ruleMajorPrefixObservable, ruleMajorCumulativeColumns, scalar4a_project]
    using h

theorem ruleMajorPrefix_two_scalars {input : CertifiedLocalizedCIPInput}
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (equal : input.ruleMajorPrefixObservable 2 left = input.ruleMajorPrefixObservable 2 right) :
    scalar4a left = scalar4a right ∧ scalar4b left = scalar4b right := by
  have h := congrArg (fun value : RuleMajorPrefixObservable input.Atom => value.columns) equal
  simpa [ruleMajorPrefixObservable, ruleMajorCumulativeColumns, List.range_succ,
    scalar4a_project, scalar4b] using h

/-- The actual alternatives of one branch share their preceding columns. This does not assert
that the full trees or metadata have the same order. -/
theorem ruleMajor_sameBranch_reading_prefixes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (leftReference rightReference : RS)
    (a bL cL bR cR : input.LocalizedRerootCumulativeRule45Key)
    (builtA : input.buildRuleMajorCumulativeWithRead? .rule4a read fuel cursor = some a)
    (builtBL : input.buildRuleMajorCumulativeWithRead? (.rule4b leftReference) read fuel cursor = some bL)
    (builtCL : input.buildRuleMajorCumulativeWithRead? (.rule4c leftReference) read fuel cursor = some cL)
    (builtBR : input.buildRuleMajorCumulativeWithRead? (.rule4b rightReference) read fuel cursor = some bR)
    (builtCR : input.buildRuleMajorCumulativeWithRead? (.rule4c rightReference) read fuel cursor = some cR) :
    bL.constitutional.rule1a = bR.constitutional.rule1a ∧
      scalar4a bL = scalar4a bR ∧
      cL.constitutional.rule1a = cR.constitutional.rule1a ∧
      scalar4a cL = scalar4a cR ∧
      scalar4b bL = scalar4b cL ∧ scalar4b bR = scalar4b cR := by
  have abL := input.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix
    leftReference read fuel cursor a bL builtA builtBL
  have abR := input.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix
    rightReference read fuel cursor a bR builtA builtBR
  have bcL := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix
    leftReference read fuel cursor bL cL builtBL builtCL
  have bcR := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix
    rightReference read fuel cursor bR cR builtBR builtCR
  have b1 : bL.constitutional.rule1a = bR.constitutional.rule1a :=
    congrArg (fun value : RuleMajorPrefixObservable input.Atom => value.rule1a)
      (abL.symm.trans abR)
  have ba := ruleMajorPrefix_one_scalar4a (abL.symm.trans abR)
  have l1 : bL.constitutional.rule1a = cL.constitutional.rule1a :=
    congrArg (fun value : RuleMajorPrefixObservable input.Atom => value.rule1a) bcL
  have r1 : bR.constitutional.rule1a = cR.constitutional.rule1a :=
    congrArg (fun value : RuleMajorPrefixObservable input.Atom => value.rule1a) bcR
  have ls := ruleMajorPrefix_two_scalars bcL
  have rs := ruleMajorPrefix_two_scalars bcR
  exact ⟨b1, ba, l1.symm.trans (b1.trans r1),
    ls.1.symm.trans (ba.trans rs.1), ls.2, rs.2⟩

end
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorPrefix_one_scalar4a
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorPrefix_two_scalars
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajor_sameBranch_reading_prefixes
