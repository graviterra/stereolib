import TetraStereo.OneCenter.CIPObservedGeometryAssignmentConformance
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact spatial refinement of raw axial observations

The raw geometry API must accept an orientation observation because a molecular graph has no
handedness.  When exact rational coordinates are available, however, the observation need not be
trusted: this module independently selects the CIP-senior reference at each end and checks the
P-92 axial scalar-triple-product sign before allowing the raw axial record into the joined
analyzer.  Planar, helical, and polyhedral observations retain their existing typed external
evidence boundaries.
-/

namespace BlueBookP93.GeometryIngress

/-- Independent meaning of choosing the senior member of one candidate pair from a strict
official-context branch comparison. -/
def SeniorReferenceJudgment (decision : Option Ordering)
    (first second senior : Nat) : Prop :=
  (decision = some .gt ∧ senior = first) ∨
    (decision = some .lt ∧ senior = second)

/-- Direct semantic lookup of one atom's exact rational coordinate. -/
def SpatialPointAt (spatial : SpatialConfiguration) (atom : Nat)
    (point : CartesianPoint3) : Prop :=
  spatial.positions[atom]? = some point

/-- Coordinate-backed meaning of one axial descriptor observation.  The two senior references
are selected from molecule-derived CIP decisions; the descriptor is then fixed by the independent
rational P-92 axial sign relation. -/
def RationalAxialObservationJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation) (descriptor : AxialDescriptor) : Prop :=
  let context := result.geometryPriorityState
  ∃ startHigh endHigh axisStartPoint axisEndPoint startHighPoint endHighPoint,
    SeniorReferenceJudgment
      (compareBranchesThroughOfficialContext? result context.1 context.2.2 context.2.1
        record.axisStart record.startFirst record.startSecond)
      record.startFirst record.startSecond startHigh ∧
    SeniorReferenceJudgment
      (compareBranchesThroughOfficialContext? result context.1 context.2.2 context.2.1
        record.axisEnd record.endFirst record.endSecond)
      record.endFirst record.endSecond endHigh ∧
    SpatialPointAt spatial record.axisStart axisStartPoint ∧
    SpatialPointAt spatial record.axisEnd axisEndPoint ∧
    SpatialPointAt spatial startHigh startHighPoint ∧
    SpatialPointAt spatial endHigh endHighPoint ∧
    RationalAxialSpatialDescriptor axisStartPoint axisEndPoint
      startHighPoint endHighPoint descriptor

end BlueBookP93.GeometryIngress

/-- Executable strict senior-reference selector.  Ties and unavailable comparisons are refused. -/
def seniorReferenceOfDecision? (decision : Option Ordering)
    (first second : Nat) : Option Nat :=
  match decision with
  | some .gt => some first
  | some .lt => some second
  | _ => none

theorem seniorReferenceOfDecision?_eq_some_iff
    (decision : Option Ordering) (first second senior : Nat) :
    seniorReferenceOfDecision? decision first second = some senior ↔
      BlueBookP93.GeometryIngress.SeniorReferenceJudgment
        decision first second senior := by
  cases decision with
  | none => simp [seniorReferenceOfDecision?,
      BlueBookP93.GeometryIngress.SeniorReferenceJudgment]
  | some ordering =>
      cases ordering <;>
        simp [seniorReferenceOfDecision?,
          BlueBookP93.GeometryIngress.SeniorReferenceJudgment, eq_comm]

/-- Safe exact coordinate lookup for a raw normalized atom index. -/
def SpatialConfiguration.pointAt? (spatial : SpatialConfiguration)
    (atom : Nat) : Option CartesianPoint3 :=
  spatial.positions[atom]?

theorem SpatialConfiguration.pointAt?_eq_some_iff
    (spatial : SpatialConfiguration) (atom : Nat) (point : CartesianPoint3) :
    spatial.pointAt? atom = some point ↔
      BlueBookP93.GeometryIngress.SpatialPointAt spatial atom point := by
  rfl

/-- Recompute the axial descriptor from molecule-derived senior references and exact coordinates. -/
def ChemistryNormalizationResult.axialObservationSpatialDescriptor?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation) : Option AxialDescriptor := do
  let context := result.geometryPriorityState
  let startHigh ← seniorReferenceOfDecision?
    (compareBranchesThroughOfficialContext? result context.1 context.2.2 context.2.1
      record.axisStart record.startFirst record.startSecond)
    record.startFirst record.startSecond
  let endHigh ← seniorReferenceOfDecision?
    (compareBranchesThroughOfficialContext? result context.1 context.2.2 context.2.1
      record.axisEnd record.endFirst record.endSecond)
    record.endFirst record.endSecond
  let axisStartPoint ← spatial.pointAt? record.axisStart
  let axisEndPoint ← spatial.pointAt? record.axisEnd
  let startHighPoint ← spatial.pointAt? startHigh
  let endHighPoint ← spatial.pointAt? endHigh
  axialDescriptorOfSpatialReferences?
    axisStartPoint axisEndPoint startHighPoint endHighPoint

/-- The coordinate validator is exactly the independent senior-selection and rational-sign
relation, including every refusal. -/
theorem ChemistryNormalizationResult.axialObservationSpatialDescriptor?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation) (descriptor : AxialDescriptor) :
    result.axialObservationSpatialDescriptor? spatial record = some descriptor ↔
      BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
        result spatial record descriptor := by
  constructor
  · intro computed
    unfold ChemistryNormalizationResult.axialObservationSpatialDescriptor? at computed
    generalize startEq : seniorReferenceOfDecision?
      (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
        result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
        record.axisStart record.startFirst record.startSecond)
      record.startFirst record.startSecond = startSelected at computed
    cases startSelected with
    | none => simp [startEq] at computed
    | some startHigh =>
        generalize endEq : seniorReferenceOfDecision?
          (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
            result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
            record.axisEnd record.endFirst record.endSecond)
          record.endFirst record.endSecond = endSelected at computed
        cases endSelected with
        | none => simp [startEq, endEq] at computed
        | some endHigh =>
            cases axisStartEq : spatial.pointAt? record.axisStart with
            | none => simp [startEq, endEq, axisStartEq] at computed
            | some axisStartPoint =>
                cases axisEndEq : spatial.pointAt? record.axisEnd with
                | none => simp [startEq, endEq, axisStartEq, axisEndEq] at computed
                | some axisEndPoint =>
                    cases startHighEq : spatial.pointAt? startHigh with
                    | none =>
                        simp [startEq, endEq, axisStartEq, axisEndEq, startHighEq] at computed
                    | some startHighPoint =>
                        cases endHighEq : spatial.pointAt? endHigh with
                        | none =>
                            simp [startEq, endEq, axisStartEq, axisEndEq,
                              endHighEq] at computed
                        | some endHighPoint =>
                            have geometry :=
                              (axialDescriptorOfSpatialReferences?_eq_some_iff
                                axisStartPoint axisEndPoint startHighPoint
                                endHighPoint descriptor).mp (by
                                  simpa [startEq, endEq, axisStartEq, axisEndEq,
                                    startHighEq, endHighEq] using computed)
                            exact ⟨startHigh, endHigh, axisStartPoint, axisEndPoint,
                              startHighPoint, endHighPoint,
                              (seniorReferenceOfDecision?_eq_some_iff _ _ _ _).mp startEq,
                              (seniorReferenceOfDecision?_eq_some_iff _ _ _ _).mp endEq,
                              axisStartEq, axisEndEq, startHighEq, endHighEq, geometry⟩
  · rintro ⟨startHigh, endHigh, axisStartPoint, axisEndPoint,
      startHighPoint, endHighPoint, startSenior, endSenior,
      axisStartEq, axisEndEq, startHighEq, endHighEq, geometry⟩
    have startEq := (seniorReferenceOfDecision?_eq_some_iff _ _ _ _).mpr startSenior
    have endEq := (seniorReferenceOfDecision?_eq_some_iff _ _ _ _).mpr endSenior
    have descriptorEq :=
      (axialDescriptorOfSpatialReferences?_eq_some_iff
        axisStartPoint axisEndPoint startHighPoint endHighPoint descriptor).mpr geometry
    change spatial.pointAt? record.axisStart = some axisStartPoint at axisStartEq
    change spatial.pointAt? record.axisEnd = some axisEndPoint at axisEndEq
    change spatial.pointAt? startHigh = some startHighPoint at startHighEq
    change spatial.pointAt? endHigh = some endHighPoint at endHighEq
    simp [ChemistryNormalizationResult.axialObservationSpatialDescriptor?, startEq, endEq,
      axisStartEq, axisEndEq, startHighEq, endHighEq, descriptorEq]

/-- A raw sense is admitted exactly when exact coordinates recompute the descriptor constructed
from that sense. -/
def ChemistryNormalizationResult.axialObservationSpatiallyValid?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation) : Bool :=
  result.axialObservationSpatialDescriptor? spatial record ==
    some (AxialDescriptor.ofSense record.sense)

theorem ChemistryNormalizationResult.axialObservationSpatiallyValid?_eq_true_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedAxialGeometryObservation) :
    result.axialObservationSpatiallyValid? spatial record = true ↔
      BlueBookP93.GeometryIngress.RationalAxialObservationJudgment result spatial record
        (AxialDescriptor.ofSense record.sense) := by
  rw [← result.axialObservationSpatialDescriptor?_eq_some_iff spatial record]
  simp [ChemistryNormalizationResult.axialObservationSpatiallyValid?]

/-! ## Coordinate-validated joined analyzer -/

/-- Retain exactly the raw axial records whose supplied sense agrees with the exact rational
coordinate calculation. Other geometry families keep their separately typed observation
boundaries. -/
def IndexedCIPGeometryObservations.withSpatiallyValidatedAxes
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    IndexedCIPGeometryObservations :=
  { observations with
    axes := observations.axes.filter fun record =>
      result.axialObservationSpatiallyValid? spatial record }

/-- Certified public analysis with raw axial observations first checked against exact rational
coordinates. -/
def analyzeCertifiedNormalizedWithSpatiallyValidatedAxialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithObservedGeometry certified
    (observations.withSpatiallyValidatedAxes certified.result spatial)

/-- Independent meaning of an observed assignment after exact axial-coordinate validation. -/
inductive IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations) (native : List StereoAssignment) :
    StereoAssignment → Prop
  | axial {assignment record}
      (present : record ∈ observations.axes)
      (ingress : BlueBookP93.GeometryIngress.AxialObservationAssignmentJudgment
        result record assignment)
      (spatiallyCorrect : BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
        result spatial record (AxialDescriptor.ofSense record.sense))
      (notNative : ¬ native.any fun existing => existing.unit == assignment.unit) :
      IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment
        result spatial observations native assignment
  | planar {assignment record}
      (present : record ∈ observations.planes)
      (judged : BlueBookP93.GeometryIngress.PlanarObservationAssignmentJudgment
        result record assignment) :
      IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment
        result spatial observations native assignment
  | helical {assignment record}
      (present : record ∈ observations.helices)
      (judged : BlueBookP93.GeometryIngress.HelicalObservationAssignmentJudgment
        result record assignment) :
      IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment
        result spatial observations native assignment
  | polyhedral {assignment record}
      (present : record ∈ observations.polyhedra)
      (judged : BlueBookP93.GeometryIngress.PolyhedralObservationAssignmentJudgment
        result record assignment)
      (notNative : ¬ native.any fun existing => existing.unit == assignment.unit) :
      IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment
        result spatial observations native assignment

theorem independentlyJudgedSpatiallyValidatedObservedGeometryAssignment_of_filtered
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations) (native : List StereoAssignment)
    (assignment : StereoAssignment)
    (judged : IndependentlyJudgedObservedGeometryAssignment result
      (observations.withSpatiallyValidatedAxes result spatial) native assignment) :
    IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment
      result spatial observations native assignment := by
  cases judged with
  | axial present ingress notNative =>
      change _ ∈ observations.axes.filter (fun record =>
        result.axialObservationSpatiallyValid? spatial record) at present
      rcases List.mem_filter.mp present with ⟨inOriginal, valid⟩
      exact .axial inOriginal ingress
        ((result.axialObservationSpatiallyValid?_eq_true_iff spatial _).mp valid)
        notNative
  | planar present judged =>
      exact .planar (by simpa [IndexedCIPGeometryObservations.withSpatiallyValidatedAxes]
        using present) judged
  | helical present judged =>
      exact .helical (by simpa [IndexedCIPGeometryObservations.withSpatiallyValidatedAxes]
        using present) judged
  | polyhedral present judged notNative =>
      exact .polyhedral
        (by simpa [IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using present)
        judged notNative

/-- Independent final meaning of every result from the coordinate-validated axial entry point. -/
def IndependentlyJudgedCertifiedSpatialGeometryStereoAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment ∨
    IndependentlyJudgedSpatiallyValidatedObservedGeometryAssignment certified.result spatial
      observations (analyzeCertifiedNormalized certified) assignment

/-- Every axial assignment added by this public entry point carries exact molecule-derived
senior-reference and rational P-92 sign evidence; no raw axial sense can bypass that check. -/
theorem analyzeCertifiedNormalizedWithSpatiallyValidatedAxialGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithSpatiallyValidatedAxialGeometry
        certified spatial observations) :
    IndependentlyJudgedCertifiedSpatialGeometryStereoAssignment
      certified spatial observations assignment := by
  have judged := analyzeCertifiedNormalizedWithObservedGeometry_member_judged certified
    (observations.withSpatiallyValidatedAxes certified.result spatial) assignment present
  rcases judged with native | observed
  · exact .inl native
  · exact .inr
      (independentlyJudgedSpatiallyValidatedObservedGeometryAssignment_of_filtered
        certified.result spatial observations (analyzeCertifiedNormalized certified)
        assignment observed)

end TetraStereo.OneCenter
