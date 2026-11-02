import TetraStereo.OneCenter.CIPAuthoritativeRule6CompletePipelineIntegration
import TetraStereo.OneCenter.CIPObservedGeometryAssignmentConformance

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

open RawMolecule
open AuthoritativeCIPRule6Scheduler

/-!
# Authoritative unannotated Rule 6 in the certified observed-geometry pipeline

This module installs the already-proved raw five-branch replacement below the existing
width-unbounded annotated-occurrence override and the observed axial/planar/helical/polyhedral
suffix.  It proves both an exact public membership theorem and independent-judgment soundness.
-/

/-- Apply the existing annotated occurrence override to the authoritative-Rule-6 normalized
analyzer.  At an unannotated center the override is definitionally unavailable, so the new
configuration-unspecified or ranking-unresolved result is retained. -/
def ChemistryNormalizationResult.analyzeWithAuthoritativeRule6Occurrences
    (result : ChemistryNormalizationResult) : List StereoAssignment :=
  (analyzeNormalizedWithAuthoritativeRule6 result).map fun assignment =>
    match assignment.unit with
    | .tetrahedral center =>
        (result.authoritativeOccurrenceAssignment? center).getD assignment
    | _ => assignment

/-- Independent meaning of the native certified result after the occurrence override. -/
def AuthoritativeRule6OccurrenceNativeAssignmentJudgment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  ∃ base,
    result.parsed.rule2MassesKnown? = true ∧
    result.expandedStereochemicalAdmissible? = true ∧
    IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6 result base ∧
    AuthoritativeOccurrenceOverrideJudgment result base assignment

/-- Exact native-list membership after authoritative Rule 6 and the annotated occurrence
override have both been installed. -/
theorem ChemistryNormalizationResult.mem_analyzeWithAuthoritativeRule6Occurrences_iff
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ result.analyzeWithAuthoritativeRule6Occurrences ↔
      AuthoritativeRule6OccurrenceNativeAssignmentJudgment result assignment := by
  rw [ChemistryNormalizationResult.analyzeWithAuthoritativeRule6Occurrences, List.mem_map]
  constructor
  · rintro ⟨base, basePresent, mapped⟩
    obtain ⟨massesKnown, admissible, judged⟩ :=
      (mem_analyzeNormalizedWithAuthoritativeRule6_iff_independently_judged
        result base).mp basePresent
    exact ⟨base, massesKnown, admissible, judged,
      (result.authoritativeOccurrenceOverride_eq_iff base assignment).mp mapped⟩
  · rintro ⟨base, massesKnown, admissible, judged, override⟩
    exact ⟨base,
      (mem_analyzeNormalizedWithAuthoritativeRule6_iff_independently_judged
        result base).mpr ⟨massesKnown, admissible, judged⟩,
      (result.authoritativeOccurrenceOverride_eq_iff base assignment).mpr override⟩

/-- Independent final meanings for the authoritative-Rule-6 native certified prefix. -/
def IndependentlyJudgedAuthorityFacingStereoAssignmentWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6 result assignment ∨
    ∃ center, AuthoritativeOccurrenceStereoAssignmentJudgment result center assignment

/-- Every native certified-prefix member has an independent assignment judgment. -/
theorem ChemistryNormalizationResult.analyzeWithAuthoritativeRule6Occurrences_member_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈ result.analyzeWithAuthoritativeRule6Occurrences) :
    IndependentlyJudgedAuthorityFacingStereoAssignmentWithAuthoritativeRule6
      result assignment := by
  obtain ⟨base, _massesKnown, _admissible, baseJudged, override⟩ :=
    (result.mem_analyzeWithAuthoritativeRule6Occurrences_iff assignment).mp present
  have retained (assignmentEq : assignment = base) :
      IndependentlyJudgedAuthorityFacingStereoAssignmentWithAuthoritativeRule6
        result assignment := by
    subst assignment
    exact Or.inl baseJudged
  cases unitEq : base.unit with
  | tetrahedral center =>
      simp [AuthoritativeOccurrenceOverrideJudgment, unitEq] at override
      rcases override with unchanged | authoritative
      · exact retained unchanged.2
      · exact Or.inr ⟨center, authoritative⟩
  | doubleBond left right =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using override)
  | axis start finish =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using override)
  | plane atoms =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using override)
  | helix path =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using override)
  | polyhedron center =>
      exact retained (by
        simpa [AuthoritativeOccurrenceOverrideJudgment, unitEq] using override)

/-- Certified-input specialization of the authoritative-Rule-6 native prefix. -/
def analyzeCertifiedNormalizedWithAuthoritativeRule6
    (certified : CertifiedChemistryNormalizationResult) : List StereoAssignment :=
  certified.result.analyzeWithAuthoritativeRule6Occurrences

/-- No member of `native` owns the same public stereogenic-unit key. -/
def ObservedAssignmentHasNoNativeOwner
    (native : List StereoAssignment) (assignment : StereoAssignment) : Prop :=
  ∀ existing ∈ native, existing.unit ≠ assignment.unit

/-- Exact conflict and precedence policy of the four raw observed-geometry branches.  The local
constructors are separately proved sound for their independent P-92/P-93 judgments. -/
def ObservedGeometryAssignmentsPolicyJudgment
    (result : ChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (native : List StereoAssignment) (assignment : StereoAssignment) : Prop :=
  result.expandedStereochemicalAdmissible? = true ∧
    ((ConflictFreeGeometryAssignmentJudgment
        (observations.axes.filterMap result.axialGeometryObservationAssignment?) assignment ∧
        ObservedAssignmentHasNoNativeOwner native assignment) ∨
      ConflictFreeGeometryAssignmentJudgment
        (observations.planes.filterMap result.planarGeometryObservationAssignment?) assignment ∨
      ConflictFreeGeometryAssignmentJudgment
        (observations.helices.filterMap result.helicalGeometryObservationAssignment?) assignment ∨
      (ConflictFreeGeometryAssignmentJudgment
          (observations.polyhedra.filterMap
            result.polyhedralGeometryObservationAssignment?) assignment ∧
        ObservedAssignmentHasNoNativeOwner native assignment))

/-- Exact membership theorem for the generic observed-geometry suffix. -/
theorem mem_observedGeometryAssignments_iff_policy
    (result : ChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (native : List StereoAssignment) (assignment : StereoAssignment) :
    assignment ∈ observedGeometryAssignments result observations native ↔
      ObservedGeometryAssignmentsPolicyJudgment
        result observations native assignment := by
  cases admissible : result.expandedStereochemicalAdmissible? <;>
    simp [observedGeometryAssignments, admissible,
      ObservedGeometryAssignmentsPolicyJudgment,
      mem_conflictFreeGeometryAssignments_iff,
      ObservedAssignmentHasNoNativeOwner, List.mem_append]

/-- A native tetrahedral result survives exactly when the observed suffix contains no polyhedral
assignment at the same center. Other native unit families are never removed by this policy. -/
def NativeAssignmentNotReplacedByObservedPolyhedron
    (observed : List StereoAssignment) (assignment : StereoAssignment) : Prop :=
  match assignment.unit with
  | .tetrahedral center =>
      ∀ observedAssignment ∈ observed,
        observedAssignment.unit ≠ .polyhedron center
  | _ => True

/-- Exact membership theorem for the native-retention filter. -/
theorem mem_retainNativeAgainstObservedGeometry_iff
    (native observed : List StereoAssignment) (assignment : StereoAssignment) :
    assignment ∈ retainNativeAgainstObservedGeometry native observed ↔
      assignment ∈ native ∧
        NativeAssignmentNotReplacedByObservedPolyhedron observed assignment := by
  unfold retainNativeAgainstObservedGeometry
  rw [List.mem_filter]
  cases unitEq : assignment.unit with
  | tetrahedral center =>
      simp [unitEq, NativeAssignmentNotReplacedByObservedPolyhedron,
        List.mem_filterMap]
      intro _nativePresent
      constructor
      · intro noCenter observedAssignment observedPresent observedUnit
        exact noCenter observedAssignment observedPresent (by simp [observedUnit])
      · intro noObservedPolyhedron observedAssignment observedPresent
        cases observedUnit : observedAssignment.unit with
        | tetrahedral other => simp [observedUnit]
        | doubleBond left right => simp [observedUnit]
        | axis start finish => simp [observedUnit]
        | plane atoms => simp [observedUnit]
        | helix path => simp [observedUnit]
        | polyhedron other =>
            simp only [observedUnit, Option.some.injEq]
            intro otherEq
            subst other
            exact noObservedPolyhedron observedAssignment observedPresent (by
              simp [observedUnit])
  | doubleBond left right => simp [NativeAssignmentNotReplacedByObservedPolyhedron, unitEq]
  | axis start finish => simp [NativeAssignmentNotReplacedByObservedPolyhedron, unitEq]
  | plane atoms => simp [NativeAssignmentNotReplacedByObservedPolyhedron, unitEq]
  | helix path => simp [NativeAssignmentNotReplacedByObservedPolyhedron, unitEq]
  | polyhedron center => simp [NativeAssignmentNotReplacedByObservedPolyhedron, unitEq]

/-- Certified native prefix plus all four observed-geometry branches, with authoritative
unannotated Rule 6 installed below the existing annotated occurrence override. -/
def analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) : List StereoAssignment :=
  let native := analyzeCertifiedNormalizedWithAuthoritativeRule6 certified
  let observed := observedGeometryAssignments certified.result observations native
  retainNativeAgainstObservedGeometry native observed ++ observed

/-- Exact public policy judgment for the joined certified graph-plus-observed pipeline. -/
def AuthoritativeRule6ObservedGeometryPublicAssignmentJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  let native := analyzeCertifiedNormalizedWithAuthoritativeRule6 certified
  let observed := observedGeometryAssignments certified.result observations native
  (AuthoritativeRule6OccurrenceNativeAssignmentJudgment certified.result assignment ∧
      NativeAssignmentNotReplacedByObservedPolyhedron observed assignment) ∨
    ObservedGeometryAssignmentsPolicyJudgment
      certified.result observations native assignment

/-- Exact final membership theorem, including native polyhedral replacement and all observed
conflict/precedence policies. -/
theorem mem_analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry_iff
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) :
    assignment ∈
        analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry
          certified observations ↔
      AuthoritativeRule6ObservedGeometryPublicAssignmentJudgment
        certified observations assignment := by
  unfold analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry
  unfold AuthoritativeRule6ObservedGeometryPublicAssignmentJudgment
  unfold analyzeCertifiedNormalizedWithAuthoritativeRule6
  rw [List.mem_append, mem_retainNativeAgainstObservedGeometry_iff,
    certified.result.mem_analyzeWithAuthoritativeRule6Occurrences_iff,
    mem_observedGeometryAssignments_iff_policy]

/-- Independent assignment meanings at the joined certified observed-geometry boundary. -/
def IndependentlyJudgedCertifiedGeometryStereoAssignmentWithAuthoritativeRule6
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedAuthorityFacingStereoAssignmentWithAuthoritativeRule6
      certified.result assignment ∨
    IndependentlyJudgedObservedGeometryAssignment certified.result observations
      (analyzeCertifiedNormalizedWithAuthoritativeRule6 certified) assignment

/-- End-to-end soundness: every descriptor or refusal exposed by the joined replacement pipeline
has an independent native or observed-geometry assignment judgment. -/
theorem analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry
        certified observations) :
    IndependentlyJudgedCertifiedGeometryStereoAssignmentWithAuthoritativeRule6
      certified observations assignment := by
  unfold analyzeCertifiedNormalizedWithAuthoritativeRule6ObservedGeometry at present
  simp only [List.mem_append] at present
  rcases present with native | observed
  · left
    have nativePresent :
        assignment ∈ analyzeCertifiedNormalizedWithAuthoritativeRule6 certified :=
      (List.mem_filter.mp native).1
    exact certified.result.analyzeWithAuthoritativeRule6Occurrences_member_judged
      assignment nativePresent
  · right
    exact observedGeometryAssignments_member_judged certified.result observations
      (analyzeCertifiedNormalizedWithAuthoritativeRule6 certified) assignment observed

end TetraStereo.OneCenter
