import TetraStereo.OneCenter.LocalizedSpiroLambdaSupportedSpatialACAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

namespace CertifiedLocalizedCIPInput

/-!
# Whole-molecule exactness for the represented lambda-spiro A/C pipeline

The local analyzer already has an exact `eq_some` theorem against an independent source,
coordinate, IR-9, and P-93 judgment.  This module enumerates every atom once and lifts that
local result to exact whole-molecule membership, exhaustive readiness/refusal, uniqueness, and
literal count-one theorems.

The represented coordinate domain is SS-4, SPY-4, SPY-5, TBPY-5, and OC-6. This module does not
silently treat the missing coordinate-level TPR-6 route as supported.
-/

/-- A source atom is ready exactly when the independent represented lambda-spiro judgment has
an assignment at that atom. -/
def LocalizedLambdaSpiroSupportedACReady
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) : Prop :=
  ∃ assignment : input.LocalizedLambdaSpiroSupportedACAssignment,
    assignment.center = center ∧
      input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment

/-- Exhaustive semantic refusal: no assignment at the source atom satisfies the complete
represented lambda-spiro judgment. -/
def LocalizedLambdaSpiroSupportedACRefusal
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) : Prop :=
  ∀ assignment : input.LocalizedLambdaSpiroSupportedACAssignment,
    assignment.center = center →
      ¬input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment

/-- Executable success is exactly semantic readiness. -/
theorem localizedLambdaSpiroSupportedACAssignmentAt?_isSome_iff_ready
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    (input.localizedLambdaSpiroSupportedACAssignmentAt? certified center).isSome ↔
      input.LocalizedLambdaSpiroSupportedACReady certified center := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨assignment, computed⟩
    exact ⟨assignment,
      (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
        certified center assignment).mp computed⟩
  · rintro ⟨assignment, judged⟩
    exact ⟨assignment,
      (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
        certified center assignment).mpr judged⟩

/-- Executable absence is exactly exhaustive semantic refusal. -/
theorem localizedLambdaSpiroSupportedACAssignmentAt?_eq_none_iff_refusal
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    input.localizedLambdaSpiroSupportedACAssignmentAt? certified center = none ↔
      input.LocalizedLambdaSpiroSupportedACRefusal certified center := by
  exact input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_none_iff certified center

/-- Readiness and refusal are exact complements. -/
theorem localizedLambdaSpiroSupportedACReady_iff_not_refusal
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    input.LocalizedLambdaSpiroSupportedACReady certified center ↔
      ¬input.LocalizedLambdaSpiroSupportedACRefusal certified center := by
  classical
  constructor
  · rintro ⟨assignment, centerEq, judged⟩ refusal
    exact refusal assignment centerEq judged
  · intro notRefusal
    by_contra notReady
    apply notRefusal
    intro assignment centerEq judged
    exact notReady ⟨assignment, centerEq, judged⟩

/-- Every source atom lies in exactly one of the represented readiness/refusal cases. -/
theorem localizedLambdaSpiroSupportedAC_ready_or_refusal
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    input.LocalizedLambdaSpiroSupportedACReady certified center ∨
      input.LocalizedLambdaSpiroSupportedACRefusal certified center := by
  classical
  by_cases ready : input.LocalizedLambdaSpiroSupportedACReady certified center
  · exact Or.inl ready
  · exact Or.inr (by
      intro assignment centerEq judged
      exact ready ⟨assignment, centerEq, judged⟩)

/-- Whole-molecule represented lambda-spiro A/C analysis, in ascending source-atom order. -/
noncomputable def analyzeLocalizedLambdaSpiroSupportedAC
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) :
    List input.LocalizedLambdaSpiroSupportedACAssignment := by
  classical
  exact ((Finset.univ : Finset input.Atom).sort (· ≤ ·)).filterMap
    (input.localizedLambdaSpiroSupportedACAssignmentAt? certified)

/-- The whole-molecule list contains exactly the independently judged represented assignments. -/
theorem mem_analyzeLocalizedLambdaSpiroSupportedAC_iff
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment) :
    assignment ∈ input.analyzeLocalizedLambdaSpiroSupportedAC certified ↔
      input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment := by
  classical
  rw [analyzeLocalizedLambdaSpiroSupportedAC, List.mem_filterMap]
  constructor
  · rintro ⟨center, _centerPresent, computed⟩
    exact (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
      certified center assignment).mp computed |>.2
  · intro judged
    exact ⟨assignment.center, by simp,
      (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
        certified assignment.center assignment).mpr ⟨rfl, judged⟩⟩

/-- Whole-molecule assignment records are duplicate-free. -/
theorem analyzeLocalizedLambdaSpiroSupportedAC_nodup
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) :
    (input.analyzeLocalizedLambdaSpiroSupportedAC certified).Nodup := by
  classical
  unfold analyzeLocalizedLambdaSpiroSupportedAC
  apply List.Nodup.filterMap
  · intro left right assignment leftComputed rightComputed
    have leftCenter :=
      (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
        certified left assignment).mp leftComputed |>.1
    have rightCenter :=
      (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
        certified right assignment).mp rightComputed |>.1
    exact leftCenter.symm.trans rightCenter
  · exact Finset.sort_nodup _ _

/-- Mapping whole-molecule results to physical source centers is also duplicate-free. -/
theorem analyzeLocalizedLambdaSpiroSupportedAC_centers_nodup
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) :
    ((input.analyzeLocalizedLambdaSpiroSupportedAC certified).map
      LocalizedLambdaSpiroSupportedACAssignment.center).Nodup := by
  classical
  apply (input.analyzeLocalizedLambdaSpiroSupportedAC_nodup certified).map_on
  intro left leftPresent right rightPresent sameCenter
  have leftJudged :=
    (input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified left).mp leftPresent
  have rightJudged :=
    (input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified right).mp rightPresent
  exact input.localizedLambdaSpiroSupportedACAssignmentJudgment_subsingleton certified
    left.center rfl sameCenter.symm leftJudged rightJudged

/-- Every independently judged assignment occurs literally once in the public family list. -/
theorem localizedLambdaSpiroSupportedAC_judged_assignment_count_eq_one
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment)
    (judged : input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment) :
    (input.analyzeLocalizedLambdaSpiroSupportedAC certified).count assignment = 1 := by
  exact List.count_eq_one_of_mem
    (input.analyzeLocalizedLambdaSpiroSupportedAC_nodup certified)
    ((input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified assignment).mpr judged)

/-- Every successful source center occurs literally once as a physical center in the public
family list. -/
theorem localizedLambdaSpiroSupportedAC_success_center_count_eq_one
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment)
    (computed : input.localizedLambdaSpiroSupportedACAssignmentAt? certified center =
      some assignment) :
    (((input.analyzeLocalizedLambdaSpiroSupportedAC certified).map
      LocalizedLambdaSpiroSupportedACAssignment.center).count center) = 1 := by
  have retained :=
    (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
      certified center assignment).mp computed
  have present : assignment ∈ input.analyzeLocalizedLambdaSpiroSupportedAC certified :=
    (input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified assignment).mpr retained.2
  exact List.count_eq_one_of_mem
    (input.analyzeLocalizedLambdaSpiroSupportedAC_centers_nodup certified)
    (List.mem_map.mpr ⟨assignment, present, retained.1⟩)

/-- Exact whole-family P-93 soundness: every public result has a represented polyhedral A/C
judgment at exactly its perceived lambda coordination number. -/
theorem mem_analyzeLocalizedLambdaSpiroSupportedAC_sound_P93
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment)
    (present : assignment ∈ input.analyzeLocalizedLambdaSpiroSupportedAC certified) :
    SpiroPolyhedralACDescriptorJudgment assignment.carrier.coordination
      assignment.descriptor := by
  have judged :=
    (input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified assignment).mp present
  rcases judged with ⟨_agreement, sourceFrame, spatial, publicAssignment,
    _frameJudged, _candidateEq, _spatialEq, _publicJudged, _unitEq, _outcomeEq,
    descriptorJudged⟩
  exact descriptorJudged

/-- A source center is present in the public list exactly when it is semantically ready. -/
theorem center_mem_analyzeLocalizedLambdaSpiroSupportedAC_iff_ready
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    center ∈ (input.analyzeLocalizedLambdaSpiroSupportedAC certified).map
        LocalizedLambdaSpiroSupportedACAssignment.center ↔
      input.LocalizedLambdaSpiroSupportedACReady certified center := by
  constructor
  · intro centerPresent
    rcases List.mem_map.mp centerPresent with ⟨assignment, present, centerEq⟩
    exact ⟨assignment, centerEq,
      (input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified assignment).mp present⟩
  · rintro ⟨assignment, centerEq, judged⟩
    exact List.mem_map.mpr ⟨assignment,
      (input.mem_analyzeLocalizedLambdaSpiroSupportedAC_iff certified assignment).mpr judged,
      centerEq⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
