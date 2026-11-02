import TetraStereo.OneCenter.CIPRule3CumulatedTopologyAffineInvariance
import TetraStereo.OneCenter.CIPRule3DescriptorKeyAffineInvariance
import TetraStereo.OneCenter.CIPRule45DependencyViewAffineInvariance
import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3OccurrenceEndpointKeyFrame fuel :=
  { firstCursor := frame.firstCursor.mapSpatialPoints mapPoint
    secondCursor := frame.secondCursor.mapSpatialPoints mapPoint
    rule3Frame := frame.rule3Frame.mapSpatialPoints mapPoint
    endpointFrame := frame.endpointFrame.mapSpatialPoints mapPoint }

@[simp] theorem localizedRule3ReferenceCursorCandidates_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (children : List (input.LocalizedRerootCursor fuel))
    (reference : input.Atom) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3ReferenceCursorCandidates
        (children.map fun cursor => cursor.mapSpatialPoints mapPoint) reference =
      (input.localizedRule3ReferenceCursorCandidates children reference).map
        (fun cursor => cursor.mapSpatialPoints mapPoint) := by
  induction children with
  | nil => rfl
  | cons child children ih =>
      change List.filter _
          ((child :: children).map fun cursor => cursor.mapSpatialPoints mapPoint) =
        (List.filter _ (child :: children)).map
          (fun cursor => cursor.mapSpatialPoints mapPoint)
      change List.filter _
          (children.map fun cursor => cursor.mapSpatialPoints mapPoint) =
        (List.filter _ children).map
          (fun cursor => cursor.mapSpatialPoints mapPoint) at ih
      simp only [List.map_cons, List.filter_cons]
      have predicateEq :
          (((child.mapSpatialPoints mapPoint).occurrence.1.node.current? ==
              some reference) &&
            localizedRule3PhysicalReferenceProvenance
              (child.mapSpatialPoints mapPoint).occurrence.1.node.provenance) =
          ((child.occurrence.1.node.current? == some reference) &&
            localizedRule3PhysicalReferenceProvenance
              child.occurrence.1.node.provenance) := rfl
      rw [predicateEq]
      split <;> simp_all

@[simp] theorem localizedRule3ReferenceCursor?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3ReferenceCursor?
        (endpointCursor.mapSpatialPoints mapPoint) reference =
      (input.localizedRule3ReferenceCursor? endpointCursor reference).map
        (fun cursor => cursor.mapSpatialPoints mapPoint) := by
  unfold localizedRule3ReferenceCursor?
  rw [localizedRerootChildren?_mapSpatialPoints]
  cases childrenEq : input.localizedRerootChildren? endpointCursor with
  | none => rfl
  | some children =>
      dsimp
      rw [localizedRule3ReferenceCursorCandidates_mapSpatialPoints]
      cases candidatesEq : input.localizedRule3ReferenceCursorCandidates children reference with
      | nil => rfl
      | cons selected rest =>
          cases rest <;> rfl

theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (mappedRule3FrameOf :
      List ((input.mapSpatialPoints mapPoint).LocalizedRerootCursor carrierFuel) →
        Option (input.mapSpatialPoints mapPoint).LocalizedRule3CanonicalKeyFrame)
    (rule3FrameNatural : ∀ cursors,
      mappedRule3FrameOf (cursors.map fun cursor => cursor.mapSpatialPoints mapPoint) =
        (rule3FrameOf cursors).map
          (fun frame => frame.mapSpatialPoints mapPoint))
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    (input.mapSpatialPoints mapPoint).buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (target.mapSpatialPoints mapPoint)
        (view.mapSpatialPoints mapPoint)
        mappedRule3FrameOf endpoint partner
        (endpointCursor.mapSpatialPoints mapPoint) =
      (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor).map
          (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
  rw [localizedRule3ExplicitSubstituents_mapSpatialPoints]
  generalize candidatesEq :
    input.localizedRule3ExplicitSubstituents endpoint partner = candidates
  cases candidates with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          cases tail with
          | cons third more => rfl
          | nil =>
              simp only
              rw [localizedRule3ReferenceCursor?_mapSpatialPoints]
              cases firstCursorEq : input.localizedRule3ReferenceCursor?
                  endpointCursor first with
              | none => rfl
              | some firstCursor =>
                  dsimp
                  rw [localizedRule3ReferenceCursor?_mapSpatialPoints]
                  cases secondCursorEq : input.localizedRule3ReferenceCursor?
                      endpointCursor second with
                  | none => rfl
                  | some secondCursor =>
                      dsimp
                      have frameNatural := rule3FrameNatural [firstCursor, secondCursor]
                      simp only [List.map_cons, List.map_nil] at frameNatural
                      rw [frameNatural]
                      cases rule3FrameEq : rule3FrameOf [firstCursor, secondCursor] with
                      | none => rfl
                      | some rule3Frame =>
                          simp only [Option.map_some, Option.bind_some]
                          cases keysEq : rule3Frame.keys with
                          | nil =>
                              simp [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints,
                                keysEq]
                          | cons firstRule3 keyTail =>
                              cases keyTail with
                              | nil =>
                                  simp [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints,
                                    keysEq]
                              | cons secondRule3 keyRest =>
                                  cases keyRest with
                                  | cons thirdRule3 more =>
                                      simp [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints,
                                        keysEq]
                                  | nil =>
                                      simp only [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints,
                                        keysEq, List.map_cons, List.map_nil]
                                      rw [buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints]
                                      cases firstRule45Eq :
                                          input.buildLocalizedRerootCompoundRule45Key?
                                            target view
                                              (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                                              firstCursor with
                                      | none => simp
                                      | some firstRule45 =>
                                          simp only [Option.map_some, Option.bind_some]
                                          rw [buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints]
                                          cases secondRule45Eq :
                                              input.buildLocalizedRerootCompoundRule45Key?
                                                target view
                                                  (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                                                  secondCursor <;>
                                            simp [LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
                                              LocalizedRule3EndpointKeyFrame.mapSpatialPoints,
                                              LocalizedOccurrenceRule3Through5Key.mapSpatialPoints,
                                              LocalizedRule3CanonicalKeyFrame.mapSpatialPoints,
                                              keysEq]

/-- The extended terminal-to-terminal evaluator used for odd cumulenes has the same exact affine
naturality as the ordinary double-bond evaluator, without requiring a fictitious terminal bond. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_affine
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3ExtendedDescriptorBearingSpatialUnit?
          left right (leftFrame.mapSpatialPoints transform.applyPoint)
            (rightFrame.mapSpatialPoints transform.applyPoint) =
      (input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
        left right leftFrame rightFrame).map
          (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3ExtendedDescriptorBearingSpatialUnit?
  rw [localizedRule3EndpointPriority_mapSpatialPoints,
    localizedRule3EndpointPriority_mapSpatialPoints]
  generalize leftPriorityEq :
    input.localizedRule3EndpointPriority leftFrame = leftPriority
  generalize rightPriorityEq :
    input.localizedRule3EndpointPriority rightFrame = rightPriority
  cases leftPriority with
  | nonstereogenic =>
      simp [LocalizedRule3EndpointPriority.mapSpatialPoints,
        LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints]
  | senior leftReference =>
      cases rightPriority with
      | nonstereogenic =>
          simp [LocalizedRule3EndpointPriority.mapSpatialPoints,
            LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints]
      | senior rightReference =>
          simp only [LocalizedRule3EndpointPriority.mapSpatialPoints]
          cases leftPointEq : input.spatialPointAt? left with
          | none => simp [spatialPointAt?_mapSpatialPoints, leftPointEq]
          | some leftPoint =>
              cases rightPointEq : input.spatialPointAt? right with
              | none =>
                  simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq]
              | some rightPoint =>
                  cases leftReferencePointEq : input.spatialPointAt? leftReference with
                  | none =>
                      simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq,
                        leftReferencePointEq]
                  | some leftReferencePoint =>
                      cases rightReferencePointEq : input.spatialPointAt? rightReference with
                      | none =>
                          simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq,
                            leftReferencePointEq, rightReferencePointEq]
                      | some rightReferencePoint =>
                          simp [spatialPointAt?_mapSpatialPoints, leftPointEq, rightPointEq,
                            leftReferencePointEq, rightReferencePointEq,
                            rule3GeometryOfSpatialReferences?_affine transform
                              leftPoint rightPoint leftReferencePoint rightReferencePoint
                              determinantNonzero,
                            LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
                            LocalizedRule3EndpointPriority.mapSpatialPoints]

def LocalizedRule3OccurrenceDescriptorBearingSpatialResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3OccurrenceDescriptorBearingSpatialResult fuel :=
  { topology := result.topology.mapSpatialPoints mapPoint
    leftCompilation := result.leftCompilation.mapSpatialPoints mapPoint
    rightCompilation := result.rightCompilation.mapSpatialPoints mapPoint
    unit := result.unit.mapSpatialPoints mapPoint }

theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (transform : RationalAffineFrameTransform)
    (mappedRule3FrameOf :
      List ((input.mapSpatialPoints transform.applyPoint).LocalizedRerootCursor carrierFuel) →
        Option (input.mapSpatialPoints transform.applyPoint).LocalizedRule3CanonicalKeyFrame)
    (rule3FrameNatural : ∀ cursors,
      mappedRule3FrameOf
          (cursors.map fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
        (rule3FrameOf cursors).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint))
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
          (target.mapSpatialPoints transform.applyPoint)
          (occurrence.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint) mappedRule3FrameOf =
      (input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf).map
          (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
  rw [localizedRule3PhysicalEndpointCursorFrame?_mapSpatialPoints]
  cases topologyEq : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => rfl
  | some topology =>
      dsimp
      simp only [LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
      rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
        input target view rule3FrameOf transform.applyPoint mappedRule3FrameOf
          rule3FrameNatural]
      cases leftEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf topology.left topology.right topology.leftCursor with
      | none => rfl
      | some leftCompilation =>
          dsimp
          rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
            input target view rule3FrameOf transform.applyPoint mappedRule3FrameOf
              rule3FrameNatural]
          cases rightEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf topology.right topology.left topology.rightCursor with
          | none => rfl
          | some rightCompilation =>
              dsimp
              simp only [LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints]
              rw [localizedRule3DescriptorBearingSpatialUnit?_affine
                input topology.left topology.right leftCompilation.endpointFrame
                  rightCompilation.endpointFrame transform determinantNonzero]
              cases unitEq : input.localizedRule3DescriptorBearingSpatialUnit?
                  topology.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame <;>
                simp [LocalizedRule3OccurrenceDescriptorBearingSpatialResult.mapSpatialPoints,
                  LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
                  LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]

def LocalizedRule3OddCumuleneDescriptorBearingSpatialResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3OddCumuleneDescriptorBearingSpatialResult fuel :=
  { topology := result.topology.mapSpatialPoints mapPoint
    leftCompilation := result.leftCompilation.mapSpatialPoints mapPoint
    rightCompilation := result.rightCompilation.mapSpatialPoints mapPoint
    unit := result.unit.mapSpatialPoints mapPoint }

theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (transform : RationalAffineFrameTransform)
    (mappedRule3FrameOf :
      List ((input.mapSpatialPoints transform.applyPoint).LocalizedRerootCursor carrierFuel) →
        Option (input.mapSpatialPoints transform.applyPoint).LocalizedRule3CanonicalKeyFrame)
    (rule3FrameNatural : ∀ cursors,
      mappedRule3FrameOf
          (cursors.map fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
        (rule3FrameOf cursors).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint))
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
          (target.mapSpatialPoints transform.applyPoint)
          (occurrence.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint) mappedRule3FrameOf =
      (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf).map
          (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
  simp only [localizedRule3CumulatedTraversalFuel]
  rw [localizedRule3OddCumuleneEndpointCursorFrame?_mapSpatialPoints]
  cases topologyEq : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) occurrence with
  | none => rfl
  | some topology =>
      dsimp
      simp only [LocalizedRule3OddCumuleneEndpointCursorFrame.mapSpatialPoints,
        LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
      rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
        input target view rule3FrameOf transform.applyPoint mappedRule3FrameOf
          rule3FrameNatural]
      cases leftEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf topology.initial.left topology.initial.right
            topology.initial.leftCursor with
      | none => rfl
      | some leftCompilation =>
          dsimp
          rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
            input target view rule3FrameOf transform.applyPoint mappedRule3FrameOf
              rule3FrameNatural]
          cases rightEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf topology.right topology.rightPartner
                topology.rightCursor with
          | none => rfl
          | some rightCompilation =>
              dsimp
              simp only [LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints]
              rw [localizedRule3ExtendedDescriptorBearingSpatialUnit?_affine
                input topology.initial.left topology.right
                  leftCompilation.endpointFrame rightCompilation.endpointFrame
                    transform determinantNonzero]
              cases unitEq : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
                  topology.initial.left topology.right leftCompilation.endpointFrame
                    rightCompilation.endpointFrame <;>
                simp [LocalizedRule3OddCumuleneDescriptorBearingSpatialResult.mapSpatialPoints,
                  LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
                  LocalizedRule3OddCumuleneEndpointCursorFrame.mapSpatialPoints,
                  LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
