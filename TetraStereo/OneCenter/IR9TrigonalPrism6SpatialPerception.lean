import TetraStereo.OneCenter.IR9FourCoordinateSpatialRoles

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalPrism6SpatialPerception

open FourCoordinateSpatialRoles

/-!
# Exact coordinate perception for idealized TPR-6

The ten unordered `3+3` partitions of six donor positions are searched exhaustively.  Within a
partition, all six correspondences between the second and first triangular faces are searched.
A correspondence is accepted exactly when the second face is a nonzero translation of the first,
the translation axis is perpendicular to the first face, the central atom is the prism centroid,
and every two-site priority progression on either face has nonzero viewed determinant from the
opposite face.  Exactly one face partition and one correspondence must survive.
-/

structure Frame where
  center : CartesianPoint3
  donor0 : CartesianPoint3
  donor1 : CartesianPoint3
  donor2 : CartesianPoint3
  donor3 : CartesianPoint3
  donor4 : CartesianPoint3
  donor5 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

def donorAt (frame : Frame) : Fin 6 → CartesianPoint3
  | 0 => frame.donor0
  | 1 => frame.donor1
  | 2 => frame.donor2
  | 3 => frame.donor3
  | 4 => frame.donor4
  | 5 => frame.donor5

end Frame

structure Face where
  position0 : Fin 6
  position1 : Fin 6
  position2 : Fin 6
  deriving DecidableEq, Repr

namespace Face

def positionAt (face : Face) : Fin 3 → Fin 6
  | 0 => face.position0
  | 1 => face.position1
  | 2 => face.position2

def positions (face : Face) : List (Fin 6) :=
  [face.position0, face.position1, face.position2]

def pointAt (frame : Frame) (face : Face) (position : Fin 3) : CartesianPoint3 :=
  frame.donorAt (face.positionAt position)

def centroid (frame : Frame) (face : Face) : CartesianPoint3 :=
  { x := ((face.pointAt frame 0).x + (face.pointAt frame 1).x +
      (face.pointAt frame 2).x) / 3
    y := ((face.pointAt frame 0).y + (face.pointAt frame 1).y +
      (face.pointAt frame 2).y) / 3
    z := ((face.pointAt frame 0).z + (face.pointAt frame 1).z +
      (face.pointAt frame 2).z) / 3 }

end Face

structure FacePartition where
  first : Face
  second : Face
  deriving DecidableEq, Repr

/-- Each unordered three-plus-three partition appears once; position zero fixes which face is
listed first. -/
def facePartitions : List FacePartition :=
  [ ⟨⟨0, 1, 2⟩, ⟨3, 4, 5⟩⟩
  , ⟨⟨0, 1, 3⟩, ⟨2, 4, 5⟩⟩
  , ⟨⟨0, 1, 4⟩, ⟨2, 3, 5⟩⟩
  , ⟨⟨0, 1, 5⟩, ⟨2, 3, 4⟩⟩
  , ⟨⟨0, 2, 3⟩, ⟨1, 4, 5⟩⟩
  , ⟨⟨0, 2, 4⟩, ⟨1, 3, 5⟩⟩
  , ⟨⟨0, 2, 5⟩, ⟨1, 3, 4⟩⟩
  , ⟨⟨0, 3, 4⟩, ⟨1, 2, 5⟩⟩
  , ⟨⟨0, 3, 5⟩, ⟨1, 2, 4⟩⟩
  , ⟨⟨0, 4, 5⟩, ⟨1, 2, 3⟩⟩ ]

theorem facePartitions_nodup : facePartitions.Nodup := by decide

/-- Every possible correspondence order of one triangular face. -/
def secondFaceOrders (face : Face) : List Face :=
  [ ⟨face.position0, face.position1, face.position2⟩
  , ⟨face.position0, face.position2, face.position1⟩
  , ⟨face.position1, face.position0, face.position2⟩
  , ⟨face.position1, face.position2, face.position0⟩
  , ⟨face.position2, face.position0, face.position1⟩
  , ⟨face.position2, face.position1, face.position0⟩ ]

theorem secondFaceOrders_nodup_of_partition
    {partition : FacePartition} (member : partition ∈ facePartitions) :
    (secondFaceOrders partition.second).Nodup := by
  simp [facePartitions] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem flattenedPositions_nodup
    {partition : FacePartition} (partitionMember : partition ∈ facePartitions)
    {second : Face} (secondMember : second ∈ secondFaceOrders partition.second) :
    (partition.first.positions ++ second.positions).Nodup := by
  simp [facePartitions] at partitionMember
  rcases partitionMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [secondFaceOrders] at secondMember <;>
    rcases secondMember with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def translationVector (frame : Frame) (first second : Face) : ℚ × ℚ × ℚ :=
  ((second.pointAt frame 0).x - (first.pointAt frame 0).x,
    (second.pointAt frame 0).y - (first.pointAt frame 0).y,
    (second.pointAt frame 0).z - (first.pointAt frame 0).z)

/-- Corresponding second-face vertices are one common nonzero translation from the first face. -/
def FacesMatchByTranslation (frame : Frame) (first second : Face) : Prop :=
  let vector := translationVector frame first second
  (vector.1 ≠ 0 ∨ vector.2.1 ≠ 0 ∨ vector.2.2 ≠ 0) ∧
    ∀ position : Fin 3,
      (second.pointAt frame position).x - (first.pointAt frame position).x = vector.1 ∧
      (second.pointAt frame position).y - (first.pointAt frame position).y = vector.2.1 ∧
      (second.pointAt frame position).z - (first.pointAt frame position).z = vector.2.2

instance facesMatchByTranslationDecidable (frame : Frame) (first second : Face) :
    Decidable (FacesMatchByTranslation frame first second) := by
  unfold FacesMatchByTranslation
  infer_instance

/-- The face-translation axis is orthogonal to two independent presented edges of the first
triangle. -/
def TranslationAxisPerpendicularToFace (frame : Frame) (first second : Face) : Prop :=
  let vector := translationVector frame first second
  ((first.pointAt frame 1).x - (first.pointAt frame 0).x) * vector.1 +
      ((first.pointAt frame 1).y - (first.pointAt frame 0).y) * vector.2.1 +
      ((first.pointAt frame 1).z - (first.pointAt frame 0).z) * vector.2.2 = 0 ∧
    ((first.pointAt frame 2).x - (first.pointAt frame 0).x) * vector.1 +
      ((first.pointAt frame 2).y - (first.pointAt frame 0).y) * vector.2.1 +
      ((first.pointAt frame 2).z - (first.pointAt frame 0).z) * vector.2.2 = 0

instance translationAxisPerpendicularToFaceDecidable
    (frame : Frame) (first second : Face) :
    Decidable (TranslationAxisPerpendicularToFace frame first second) := by
  unfold TranslationAxisPerpendicularToFace
  infer_instance

/-- The central atom is the exact centroid of the six prism vertices. -/
def CenterAtPrismCentroid (frame : Frame) : Prop :=
  6 * frame.center.x = frame.donor0.x + frame.donor1.x + frame.donor2.x +
      frame.donor3.x + frame.donor4.x + frame.donor5.x ∧
  6 * frame.center.y = frame.donor0.y + frame.donor1.y + frame.donor2.y +
      frame.donor3.y + frame.donor4.y + frame.donor5.y ∧
  6 * frame.center.z = frame.donor0.z + frame.donor1.z + frame.donor2.z +
      frame.donor3.z + frame.donor4.z + frame.donor5.z

instance centerAtPrismCentroidDecidable (frame : Frame) :
    Decidable (CenterAtPrismCentroid frame) := by
  unfold CenterAtPrismCentroid
  infer_instance

/-- Physical progression on `readFace`, viewed from above `preferredFace`. -/
def progressionDeterminant
    (frame : Frame) (preferredFace readFace : Face) (first second : Fin 3) : ℚ :=
  CartesianPoint3.orientedVolume
    (readFace.pointAt frame first) (readFace.pointAt frame second)
    (preferredFace.centroid frame) frame.center

/-- Every possible strict two-site progression on either face has a determinate sign from above
the opposite face. -/
def FaceProgressionsNondegenerate (frame : Frame) (first second : Face) : Prop :=
  (∀ left right : Fin 3, left ≠ right →
      progressionDeterminant frame first second left right ≠ 0) ∧
    (∀ left right : Fin 3, left ≠ right →
      progressionDeterminant frame second first left right ≠ 0)

instance faceProgressionsNondegenerateDecidable
    (frame : Frame) (first second : Face) :
    Decidable (FaceProgressionsNondegenerate frame first second) := by
  unfold FaceProgressionsNondegenerate
  infer_instance

/-- Exact matched triangular-prism frame. -/
def IsMatchedPrismFrame (frame : Frame) (first second : Face) : Prop :=
  FacesMatchByTranslation frame first second ∧
    TranslationAxisPerpendicularToFace frame first second ∧
    CenterAtPrismCentroid frame ∧
    FaceProgressionsNondegenerate frame first second

instance isMatchedPrismFrameDecidable (frame : Frame) (first second : Face) :
    Decidable (IsMatchedPrismFrame frame first second) := by
  unfold IsMatchedPrismFrame
  infer_instance

def matchedPrismFrame? (frame : Frame) (first second : Face) : Bool :=
  decide (IsMatchedPrismFrame frame first second)

@[simp] theorem matchedPrismFrame?_eq_true_iff (frame : Frame) (first second : Face) :
    matchedPrismFrame? frame first second = true ↔
      IsMatchedPrismFrame frame first second := by
  simp [matchedPrismFrame?]

/-- Exact correspondence selection within one unordered face partition. -/
def matchingSecondFace? (frame : Frame) (partition : FacePartition) : Option Face :=
  uniqueSatisfying? (secondFaceOrders partition.second)
    (matchedPrismFrame? frame partition.first)

def MatchingJudgment
    (frame : Frame) (partition : FacePartition) (second : Face) : Prop :=
  second ∈ secondFaceOrders partition.second ∧
    IsMatchedPrismFrame frame partition.first second ∧
    ∀ other ∈ secondFaceOrders partition.second,
      IsMatchedPrismFrame frame partition.first other → other = second

theorem matchingSecondFace?_eq_some_iff
    (frame : Frame) (partition : FacePartition)
    (partitionMember : partition ∈ facePartitions) (second : Face) :
    matchingSecondFace? frame partition = some second ↔
      MatchingJudgment frame partition second := by
  rw [matchingSecondFace?, uniqueSatisfying?_eq_some_iff
    (secondFaceOrders partition.second) (matchedPrismFrame? frame partition.first)
    (secondFaceOrders_nodup_of_partition partitionMember) second]
  simp only [matchedPrismFrame?_eq_true_iff]
  rfl

def partitionCandidate? (frame : Frame) (partition : FacePartition) : Bool :=
  (matchingSecondFace? frame partition).isSome

theorem partitionCandidate?_eq_true_iff
    (frame : Frame) (partition : FacePartition)
    (partitionMember : partition ∈ facePartitions) :
    partitionCandidate? frame partition = true ↔
      ∃ second, MatchingJudgment frame partition second := by
  rw [partitionCandidate?, Option.isSome_iff_exists]
  constructor
  · rintro ⟨second, computed⟩
    exact ⟨second,
      (matchingSecondFace?_eq_some_iff frame partition partitionMember second).mp computed⟩
  · rintro ⟨second, judged⟩
    exact ⟨second,
      (matchingSecondFace?_eq_some_iff frame partition partitionMember second).mpr judged⟩

def uniqueFacePartition? (frame : Frame) : Option FacePartition :=
  uniqueSatisfying? facePartitions (partitionCandidate? frame)

def PartitionJudgment (frame : Frame) (partition : FacePartition) : Prop :=
  partition ∈ facePartitions ∧
    (∃ second, MatchingJudgment frame partition second) ∧
    ∀ other ∈ facePartitions,
      (∃ second, MatchingJudgment frame other second) → other = partition

theorem uniqueFacePartition?_eq_some_iff (frame : Frame) (partition : FacePartition) :
    uniqueFacePartition? frame = some partition ↔
      PartitionJudgment frame partition := by
  rw [uniqueFacePartition?, uniqueSatisfying?_eq_some_iff facePartitions
    (partitionCandidate? frame) facePartitions_nodup partition]
  constructor
  · rintro ⟨member, accepted, unique⟩
    have candidate := (partitionCandidate?_eq_true_iff frame partition member).mp accepted
    refine ⟨member, candidate, ?_⟩
    intro other otherMember otherCandidate
    exact unique other otherMember
      ((partitionCandidate?_eq_true_iff frame other otherMember).mpr otherCandidate)
  · rintro ⟨member, candidate, unique⟩
    refine ⟨member,
      (partitionCandidate?_eq_true_iff frame partition member).mpr candidate, ?_⟩
    intro other otherMember accepted
    exact unique other otherMember
      ((partitionCandidate?_eq_true_iff frame other otherMember).mp accepted)

/-- Two triangular faces in corresponding-vertex order. -/
structure CorrespondingFaces where
  first : Face
  second : Face
  deriving DecidableEq, Repr

def Judgment (frame : Frame) (faces : CorrespondingFaces) : Prop :=
  ∃ partition,
    PartitionJudgment frame partition ∧
    faces.first = partition.first ∧
    MatchingJudgment frame partition faces.second

def perceive? (frame : Frame) : Option CorrespondingFaces := do
  let partition ← uniqueFacePartition? frame
  let second ← matchingSecondFace? frame partition
  some { first := partition.first, second }

theorem perceive?_eq_some_iff (frame : Frame) (faces : CorrespondingFaces) :
    perceive? frame = some faces ↔ Judgment frame faces := by
  constructor
  · intro computed
    unfold perceive? at computed
    cases partitionEq : uniqueFacePartition? frame with
    | none => simp [partitionEq] at computed
    | some partition =>
        have partitionJudged := (uniqueFacePartition?_eq_some_iff frame partition).mp partitionEq
        cases secondEq : matchingSecondFace? frame partition with
        | none => simp [partitionEq, secondEq] at computed
        | some second =>
            have facesEq : faces = { first := partition.first, second := second } := by
              simpa [partitionEq, secondEq] using computed.symm
            subst faces
            exact ⟨partition, partitionJudged, rfl,
              (matchingSecondFace?_eq_some_iff
                frame partition partitionJudged.1 second).mp secondEq⟩
  · rintro ⟨partition, partitionJudged, firstEq, matching⟩
    have partitionEq : uniqueFacePartition? frame = some partition :=
      (uniqueFacePartition?_eq_some_iff frame partition).mpr partitionJudged
    have secondEq : matchingSecondFace? frame partition = some faces.second :=
      (matchingSecondFace?_eq_some_iff
        frame partition partitionJudged.1 faces.second).mpr matching
    have facesEq : ({ first := partition.first, second := faces.second } :
        CorrespondingFaces) = faces := by
      cases faces
      simp_all
    simpa [perceive?, partitionEq, secondEq] using congrArg some facesEq

theorem perceive?_eq_none_iff (frame : Frame) :
    perceive? frame = none ↔ ¬ ∃ faces, Judgment frame faces := by
  constructor
  · intro absent ⟨faces, judged⟩
    have present := (perceive?_eq_some_iff frame faces).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : perceive? frame with
    | none => rfl
    | some faces =>
        exact False.elim (noJudgment ⟨faces, (perceive?_eq_some_iff frame faces).mp computed⟩)

theorem flattenedPositions_nodup_of_judgment
    {frame : Frame} {faces : CorrespondingFaces} (judged : Judgment frame faces) :
    (faces.first.positions ++ faces.second.positions).Nodup := by
  rcases judged with ⟨partition, partitionJudged, firstEq, matching⟩
  rw [firstEq]
  exact flattenedPositions_nodup partitionJudged.1 matching.1

/-- The two perceived triangular faces exhaust all six donor positions. -/
theorem position_mem_first_or_second_of_judgment
    {frame : Frame} {faces : CorrespondingFaces} (judged : Judgment frame faces)
    (position : Fin 6) :
    position ∈ faces.first.positions ∨ position ∈ faces.second.positions := by
  have nodup := flattenedPositions_nodup_of_judgment judged
  have card :
      (faces.first.positions ++ faces.second.positions).toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup nodup]
    simp [Face.positions]
  have all :
      (faces.first.positions ++ faces.second.positions).toFinset =
        (Finset.univ : Finset (Fin 6)) :=
    Finset.eq_univ_of_card _ (by simpa using card)
  have present : position ∈ faces.first.positions ++ faces.second.positions := by
    rw [← List.mem_toFinset, all]
    simp
  simpa using present

theorem progressionDeterminant_ne_zero_of_judgment
    {frame : Frame} {faces : CorrespondingFaces} (judged : Judgment frame faces)
    {preferred read : Face}
    (faceChoice :
      (preferred = faces.first ∧ read = faces.second) ∨
      (preferred = faces.second ∧ read = faces.first))
    {first second : Fin 3} (different : first ≠ second) :
    progressionDeterminant frame preferred read first second ≠ 0 := by
  rcases judged with ⟨partition, partitionJudged, firstEq, matching⟩
  have nondegenerate := matching.2.1.2.2.2
  rcases faceChoice with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [firstEq] using nondegenerate.1 first second different
  · simpa [firstEq] using nondegenerate.2 first second different

end TetraStereo.OneCenter.RedBookIR9.TrigonalPrism6SpatialPerception
