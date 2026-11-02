import TetraStereo.OneCenter.CIPObservedAxialSpatialConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact spatial refinement of raw helical observations

P-92.1.2.2 defines `M/P` from the handedness of an identified helix and, for an ordered bond or
axis witness, from the smaller torsion between its near and far reference groups.  This module
removes trust in the raw `StereoSense` for the represented terminal-reference subdomain.  The
ordered path and its two reference atoms remain typed applicability evidence: this theorem does
not claim to perceive every chemical helix from constitution or coordinates alone.

**Sign calibration (P-92.1.2.2.1).**  Looking along the axis from the nearer to the farther
endpoint, the path from the senior near reference to the senior far reference is `P` when it is
clockwise and `M` when it is anticlockwise.  With exact coordinates and a directed axis pointing
from the near endpoint to the far endpoint, the scalar triple product
`axis · (frontArm × backArm)` is positive exactly for the clockwise turn and negative exactly for
the anticlockwise turn.  Hence positive measure is `P` and negative measure is `M`.  This is the
same sign convention already used by the P-94 torsion sine numerator and by the existing axial
primitive's `S_a` branch; `axialChiralityMeasure` and `helicalReferenceMeasure` are the same
arithmetic expression under the aligned reference identification.
-/

namespace CartesianPoint3

/-- Exact scalar-triple-product numerator of the signed turn from the front reference to the back
reference while looking from the first path endpoint toward the last.  A positive value is the
clockwise (`P`) turn and a negative value is the anticlockwise (`M`) turn in this near-to-far
coordinate convention.  Components of either reference arm parallel to the axis cancel
automatically. -/
def helicalReferenceMeasure
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) : ℚ :=
  let axis := displacement frontEndpoint backEndpoint
  let frontArm := displacement frontEndpoint frontReference
  let backArm := displacement backEndpoint backReference
  RationalVector3.dot axis (RationalVector3.cross frontArm backArm)

/-- Reversing the named direction of an identified helix and exchanging its terminal references
does not change its handedness measure. -/
theorem helicalReferenceMeasure_swap
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalReferenceMeasure backEndpoint frontEndpoint backReference frontReference =
      helicalReferenceMeasure frontEndpoint backEndpoint frontReference backReference := by
  simp [helicalReferenceMeasure, displacement, RationalVector3.dot,
    RationalVector3.cross]
  ring

end CartesianPoint3

namespace BlueBookP93.GeometryIngress

/-- Independent meaning of selecting the two endpoints of the ordered helix witness. -/
def HelicalPathEndpoints (path : List Nat) (front back : Nat) : Prop :=
  path.head? = some front ∧ path.getLast? = some back

/-- Independent exact rational interpretation of terminal-reference helicity.  A positive
near-to-far triple product is the clockwise `P` turn and a negative value is the anticlockwise
`M` turn (P-92.1.2.2.1).  Zero is refused: it supplies no handed turn. -/
def RationalHelicalSpatialDescriptor
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3)
    (descriptor : HelicalDescriptor) : Prop :=
  match descriptor with
  | .P => 0 < CartesianPoint3.helicalReferenceMeasure
      frontEndpoint backEndpoint frontReference backReference
  | .M => CartesianPoint3.helicalReferenceMeasure
      frontEndpoint backEndpoint frontReference backReference < 0

/-- Coordinate-backed meaning of one helical orientation record. -/
def RationalHelicalObservationJudgment
    (spatial : SpatialConfiguration) (record : IndexedHelicalGeometryObservation)
    (descriptor : HelicalDescriptor) : Prop :=
  ∃ frontAtom backAtom frontPoint backPoint frontReferencePoint backReferencePoint,
    HelicalPathEndpoints record.helixPath frontAtom backAtom ∧
    SpatialPointAt spatial frontAtom frontPoint ∧
    SpatialPointAt spatial backAtom backPoint ∧
    SpatialPointAt spatial record.frontReference frontReferencePoint ∧
    SpatialPointAt spatial record.backReference backReferencePoint ∧
    RationalHelicalSpatialDescriptor frontPoint backPoint
      frontReferencePoint backReferencePoint descriptor

end BlueBookP93.GeometryIngress

/-- Extract both endpoints from a nonempty ordered path. -/
def helicalPathEndpoints? (path : List Nat) : Option (Nat × Nat) := do
  let front ← path.head?
  let back ← path.getLast?
  some (front, back)

theorem helicalPathEndpoints?_eq_some_iff
    (path : List Nat) (front back : Nat) :
    helicalPathEndpoints? path = some (front, back) ↔
      BlueBookP93.GeometryIngress.HelicalPathEndpoints path front back := by
  constructor
  · intro computed
    unfold helicalPathEndpoints? at computed
    cases frontEq : path.head? with
    | none => simp [frontEq] at computed
    | some selectedFront =>
        cases backEq : path.getLast? with
        | none => simp [frontEq, backEq] at computed
        | some selectedBack =>
            simp [frontEq, backEq] at computed
            rcases computed with ⟨rfl, rfl⟩
            exact ⟨frontEq, backEq⟩
  · rintro ⟨frontEq, backEq⟩
    simp [helicalPathEndpoints?, frontEq, backEq]

/-- Exact `P/M` calculation for an already identified ordered helix witness.  The sign is the
P-92.1.2.2.1 near-to-far calibration: positive is `P`, negative is `M`, zero is refused. -/
def helicalDescriptorOfSpatialReferences?
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    Option HelicalDescriptor :=
  let measure := CartesianPoint3.helicalReferenceMeasure
    frontEndpoint backEndpoint frontReference backReference
  if measure < 0 then some .M
  else if 0 < measure then some .P
  else none

/-- The executable sign test is equivalent to the independent rational helicity relation. -/
theorem helicalDescriptorOfSpatialReferences?_eq_some_iff
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3)
    (descriptor : HelicalDescriptor) :
    helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference = some descriptor ↔
      BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
        frontEndpoint backEndpoint frontReference backReference descriptor := by
  let measure := CartesianPoint3.helicalReferenceMeasure
    frontEndpoint backEndpoint frontReference backReference
  cases descriptor with
  | P =>
      unfold helicalDescriptorOfSpatialReferences?
        BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
      by_cases negative : measure < 0
      · have notPositive : ¬ 0 < measure := not_lt_of_ge negative.le
        simp [measure, negative, notPositive]
      · rw [if_neg negative]
        by_cases positive : 0 < measure <;> simp [measure, positive]
  | M =>
      unfold helicalDescriptorOfSpatialReferences?
        BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
      by_cases negative : measure < 0
      · simp [measure, negative]
      · rw [if_neg negative]
        by_cases positive : 0 < measure <;> simp [measure, negative, positive]

/-- Specialized `P` reading: the executable evaluator returns `P` exactly on a positive
near-to-far turn. -/
theorem helicalDescriptorOfSpatialReferences?_eq_some_P_iff
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference = some .P ↔
      0 < CartesianPoint3.helicalReferenceMeasure
        frontEndpoint backEndpoint frontReference backReference := by
  let measure := CartesianPoint3.helicalReferenceMeasure
    frontEndpoint backEndpoint frontReference backReference
  unfold helicalDescriptorOfSpatialReferences?
  by_cases negative : measure < 0
  · have notPositive : ¬ 0 < measure := not_lt_of_ge negative.le
    simp [measure, negative, notPositive]
  · rw [if_neg negative]
    by_cases positive : 0 < measure <;> simp [measure, positive]

/-- Specialized `M` reading: the executable evaluator returns `M` exactly on a negative
near-to-far turn. -/
theorem helicalDescriptorOfSpatialReferences?_eq_some_M_iff
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference = some .M ↔
      CartesianPoint3.helicalReferenceMeasure
        frontEndpoint backEndpoint frontReference backReference < 0 := by
  let measure := CartesianPoint3.helicalReferenceMeasure
    frontEndpoint backEndpoint frontReference backReference
  unfold helicalDescriptorOfSpatialReferences?
  by_cases negative : measure < 0
  · simp [measure, negative]
  · rw [if_neg negative]
    by_cases positive : 0 < measure <;> simp [measure, negative, positive]

/-- Both the independent semantics and executable descriptor are invariant under endpoint
reversal when the matching references are exchanged. -/
theorem rationalHelicalSpatialDescriptor_swap
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3)
    (descriptor : HelicalDescriptor) :
    BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
        backEndpoint frontEndpoint backReference frontReference descriptor ↔
      BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor
        frontEndpoint backEndpoint frontReference backReference descriptor := by
  cases descriptor <;>
    simp [BlueBookP93.GeometryIngress.RationalHelicalSpatialDescriptor,
      CartesianPoint3.helicalReferenceMeasure_swap]

theorem helicalDescriptorOfSpatialReferences?_swap
    (frontEndpoint backEndpoint frontReference backReference : CartesianPoint3) :
    helicalDescriptorOfSpatialReferences?
        backEndpoint frontEndpoint backReference frontReference =
      helicalDescriptorOfSpatialReferences?
        frontEndpoint backEndpoint frontReference backReference := by
  simp [helicalDescriptorOfSpatialReferences?,
    CartesianPoint3.helicalReferenceMeasure_swap]

/-- Recompute a helical descriptor from the ordered path endpoints, terminal references, and exact
rational coordinates. -/
def IndexedHelicalGeometryObservation.spatialDescriptor?
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration) :
    Option HelicalDescriptor := do
  let endpoints ← helicalPathEndpoints? record.helixPath
  let frontPoint ← spatial.pointAt? endpoints.1
  let backPoint ← spatial.pointAt? endpoints.2
  let frontReferencePoint ← spatial.pointAt? record.frontReference
  let backReferencePoint ← spatial.pointAt? record.backReference
  helicalDescriptorOfSpatialReferences?
    frontPoint backPoint frontReferencePoint backReferencePoint

/-- The coordinate evaluator is exactly the independent ordered-path and rational-torsion
judgment, including every missing-coordinate and zero-turn refusal. -/
theorem IndexedHelicalGeometryObservation.spatialDescriptor?_eq_some_iff
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration)
    (descriptor : HelicalDescriptor) :
    record.spatialDescriptor? spatial = some descriptor ↔
      BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment
        spatial record descriptor := by
  constructor
  · intro computed
    unfold IndexedHelicalGeometryObservation.spatialDescriptor? at computed
    cases endpointsEq : helicalPathEndpoints? record.helixPath with
    | none => simp [endpointsEq] at computed
    | some endpoints =>
        cases frontEq : spatial.pointAt? endpoints.1 with
        | none => simp [endpointsEq, frontEq] at computed
        | some frontPoint =>
            cases backEq : spatial.pointAt? endpoints.2 with
            | none => simp [endpointsEq, frontEq, backEq] at computed
            | some backPoint =>
                cases frontReferenceEq : spatial.pointAt? record.frontReference with
                | none =>
                    simp [endpointsEq, frontReferenceEq] at computed
                | some frontReferencePoint =>
                    cases backReferenceEq : spatial.pointAt? record.backReference with
                    | none =>
                        simp [endpointsEq, frontReferenceEq,
                          backReferenceEq] at computed
                    | some backReferencePoint =>
                        have geometry :=
                          (helicalDescriptorOfSpatialReferences?_eq_some_iff
                            frontPoint backPoint frontReferencePoint
                            backReferencePoint descriptor).mp (by
                              simpa [endpointsEq, frontEq, backEq, frontReferenceEq,
                                backReferenceEq] using computed)
                        rcases endpoints with ⟨frontAtom, backAtom⟩
                        have endpointJudgment :=
                          (helicalPathEndpoints?_eq_some_iff
                            record.helixPath frontAtom backAtom).mp endpointsEq
                        exact ⟨frontAtom, backAtom, frontPoint, backPoint,
                          frontReferencePoint, backReferencePoint, endpointJudgment,
                          frontEq, backEq, frontReferenceEq, backReferenceEq, geometry⟩
  · rintro ⟨frontAtom, backAtom, frontPoint, backPoint,
      frontReferencePoint, backReferencePoint, endpointJudgment,
      frontEq, backEq, frontReferenceEq, backReferenceEq, geometry⟩
    have endpointsEq :=
      (helicalPathEndpoints?_eq_some_iff record.helixPath frontAtom backAtom).mpr
        endpointJudgment
    have descriptorEq :=
      (helicalDescriptorOfSpatialReferences?_eq_some_iff
        frontPoint backPoint frontReferencePoint backReferencePoint descriptor).mpr geometry
    change spatial.pointAt? frontAtom = some frontPoint at frontEq
    change spatial.pointAt? backAtom = some backPoint at backEq
    change spatial.pointAt? record.frontReference = some frontReferencePoint at frontReferenceEq
    change spatial.pointAt? record.backReference = some backReferencePoint at backReferenceEq
    simp [IndexedHelicalGeometryObservation.spatialDescriptor?, endpointsEq,
      frontEq, backEq, frontReferenceEq, backReferenceEq, descriptorEq]

/-- A supplied raw helical sense is valid exactly when the coordinates reproduce its `P/M`
descriptor under the calibrated near-to-far sign convention. -/
def IndexedHelicalGeometryObservation.spatiallyValid?
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration) : Bool :=
  record.spatialDescriptor? spatial == some (HelicalDescriptor.ofSense record.sense)

theorem IndexedHelicalGeometryObservation.spatiallyValid?_eq_true_iff
    (record : IndexedHelicalGeometryObservation) (spatial : SpatialConfiguration) :
    record.spatiallyValid? spatial = true ↔
      BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment spatial record
        (HelicalDescriptor.ofSense record.sense) := by
  rw [← record.spatialDescriptor?_eq_some_iff spatial]
  simp [IndexedHelicalGeometryObservation.spatiallyValid?]

/-! ## Coordinate-validated axial and helical analyzer -/

/-- Validate both raw axial and raw helical senses against exact coordinates. -/
def IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    IndexedCIPGeometryObservations :=
  { observations.withSpatiallyValidatedAxes result spatial with
    helices := observations.helices.filter fun record => record.spatiallyValid? spatial }

def analyzeCertifiedNormalizedWithSpatiallyValidatedAxialHelicalGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithObservedGeometry certified
    (observations.withSpatiallyValidatedAxesAndHelices certified.result spatial)

/-- Independent meaning of an observation-derived result after both coordinate checks. -/
inductive IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment
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
      IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment
        result spatial observations native assignment
  | planar {assignment record}
      (present : record ∈ observations.planes)
      (judged : BlueBookP93.GeometryIngress.PlanarObservationAssignmentJudgment
        result record assignment) :
      IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment
        result spatial observations native assignment
  | helical {assignment record}
      (present : record ∈ observations.helices)
      (ingress : BlueBookP93.GeometryIngress.HelicalObservationAssignmentJudgment
        result record assignment)
      (spatiallyCorrect : BlueBookP93.GeometryIngress.RationalHelicalObservationJudgment
        spatial record (HelicalDescriptor.ofSense record.sense)) :
      IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment
        result spatial observations native assignment
  | polyhedral {assignment record}
      (present : record ∈ observations.polyhedra)
      (judged : BlueBookP93.GeometryIngress.PolyhedralObservationAssignmentJudgment
        result record assignment)
      (notNative : ¬ native.any fun existing => existing.unit == assignment.unit) :
      IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment
        result spatial observations native assignment

theorem independentlyJudgedSpatiallyValidatedAxialHelicalAssignment_of_filtered
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (observations : IndexedCIPGeometryObservations) (native : List StereoAssignment)
    (assignment : StereoAssignment)
    (judged : IndependentlyJudgedObservedGeometryAssignment result
      (observations.withSpatiallyValidatedAxesAndHelices result spatial) native assignment) :
    IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment
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
      exact .planar
        (by simpa [IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
          IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using present)
        judged
  | helical present ingress =>
      change _ ∈ observations.helices.filter (fun record =>
        record.spatiallyValid? spatial) at present
      rcases List.mem_filter.mp present with ⟨inOriginal, valid⟩
      exact .helical inOriginal ingress
        ((IndexedHelicalGeometryObservation.spatiallyValid?_eq_true_iff
          _ spatial).mp valid)
  | polyhedral present judged notNative =>
      exact .polyhedral
        (by simpa [IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
          IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using present)
        judged notNative

def IndependentlyJudgedCertifiedSpatialAxialHelicalStereoAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment ∨
    IndependentlyJudgedSpatiallyValidatedAxialHelicalAssignment certified.result spatial
      observations (analyzeCertifiedNormalized certified) assignment

/-- Every observation-derived axial or helical member of the joined public output carries the
corresponding exact rational coordinate certificate. -/
theorem analyzeCertifiedNormalizedWithSpatiallyValidatedAxialHelicalGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithSpatiallyValidatedAxialHelicalGeometry
        certified spatial observations) :
    IndependentlyJudgedCertifiedSpatialAxialHelicalStereoAssignment
      certified spatial observations assignment := by
  have judged := analyzeCertifiedNormalizedWithObservedGeometry_member_judged certified
    (observations.withSpatiallyValidatedAxesAndHelices certified.result spatial)
    assignment present
  rcases judged with native | observed
  · exact .inl native
  · exact .inr
      (independentlyJudgedSpatiallyValidatedAxialHelicalAssignment_of_filtered
        certified.result spatial observations (analyzeCertifiedNormalized certified)
        assignment observed)

end TetraStereo.OneCenter
