import TetraStereo.OneCenter.IR9TrigonalBipyramid5SpatialPerception
import Mathlib.Data.List.Permutation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.HexagonalBipyramid8SpatialPerception

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles

/-!
# Exact coordinate perception for idealized HBPY-8

The finite recognizer exhausts every unordered axial pair and every order of the other six
positions.  A canonical index representative removes rotation/reversal duplicates.  Exact
geometry requires an antiparallel axial pair, a centered perpendicular equatorial plane, a strict
convex boundary traversal, and nonzero viewed progressions.  No metric distortion threshold is
invented.
-/

structure Frame where
  center : CartesianPoint3
  donor0 : CartesianPoint3
  donor1 : CartesianPoint3
  donor2 : CartesianPoint3
  donor3 : CartesianPoint3
  donor4 : CartesianPoint3
  donor5 : CartesianPoint3
  donor6 : CartesianPoint3
  donor7 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

def donorAt (frame : Frame) : Fin 8 → CartesianPoint3
  | 0 => frame.donor0
  | 1 => frame.donor1
  | 2 => frame.donor2
  | 3 => frame.donor3
  | 4 => frame.donor4
  | 5 => frame.donor5
  | 6 => frame.donor6
  | 7 => frame.donor7

end Frame

def positions8 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

@[simp] theorem mem_positions8 (position : Fin 8) : position ∈ positions8 := by
  fin_cases position <;> simp [positions8]

theorem positions8_nodup : positions8.Nodup := by decide

/-- Every unordered pair of eight donor positions, in canonical index order. -/
def axialPairs : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
    (2, 3), (2, 4), (2, 5), (2, 6), (2, 7),
    (3, 4), (3, 5), (3, 6), (3, 7),
    (4, 5), (4, 6), (4, 7),
    (5, 6), (5, 7), (6, 7)]

theorem axialPairs_nodup : axialPairs.Nodup := by decide

theorem axialPair_distinct {pair : Fin 8 × Fin 8} (member : pair ∈ axialPairs) :
    pair.1 ≠ pair.2 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def remainingPositions (pair : Fin 8 × Fin 8) : List (Fin 8) :=
  positions8.filter fun position => position != pair.1 && position != pair.2

theorem remainingPositions_nodup (pair : Fin 8 × Fin 8) :
    (remainingPositions pair).Nodup :=
  positions8_nodup.filter _

theorem remainingPositions_length
    {pair : Fin 8 × Fin 8} (member : pair ∈ axialPairs) :
    (remainingPositions pair).length = 6 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure Partition where
  axial : Fin 8 × Fin 8
  equatorialCycle : List (Fin 8)
  deriving DecidableEq, Repr

/-- Exhaustive finite axial-pair/equatorial-order search space. -/
def partitions : List Partition :=
  axialPairs.flatMap fun axial =>
    (remainingPositions axial).permutations.map fun cycle =>
      { axial, equatorialCycle := cycle }

theorem mem_partitions_iff (partition : Partition) :
    partition ∈ partitions ↔
      partition.axial ∈ axialPairs ∧
        partition.equatorialCycle ∈ (remainingPositions partition.axial).permutations := by
  unfold partitions
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨axial, axialMember, mapped⟩
    rcases List.mem_map.mp mapped with ⟨cycle, cycleMember, equality⟩
    subst partition
    exact ⟨axialMember, cycleMember⟩
  · rintro ⟨axialMember, cycleMember⟩
    exact ⟨partition.axial, axialMember,
      List.mem_map.mpr ⟨partition.equatorialCycle, cycleMember, rfl⟩⟩

theorem equatorialCycle_length_of_mem
    {partition : Partition} (member : partition ∈ partitions) :
    partition.equatorialCycle.length = 6 := by
  have parts := (mem_partitions_iff partition).mp member
  have permutation := List.mem_permutations.mp parts.2
  rw [permutation.length_eq]
  exact remainingPositions_length parts.1

theorem flattenedPositions_nodup_of_mem
    {partition : Partition} (member : partition ∈ partitions) :
    (partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).Nodup := by
  have parts := (mem_partitions_iff partition).mp member
  have pairDistinct := axialPair_distinct parts.1
  have permutation := List.mem_permutations.mp parts.2
  have cycleNodup : partition.equatorialCycle.Nodup :=
    permutation.symm.nodup (remainingPositions_nodup partition.axial)
  have firstAbsent : partition.axial.1 ∉ partition.equatorialCycle := by
    intro present
    have remainingMember : partition.axial.1 ∈ remainingPositions partition.axial :=
      permutation.mem_iff.mp present
    simp [remainingPositions, mem_positions8] at remainingMember
  have secondAbsent : partition.axial.2 ∉ partition.equatorialCycle := by
    intro present
    have remainingMember : partition.axial.2 ∈ remainingPositions partition.axial :=
      permutation.mem_iff.mp present
    simp [remainingPositions, mem_positions8] at remainingMember
  exact List.nodup_cons.mpr ⟨by simp [pairDistinct, firstAbsent],
    List.nodup_cons.mpr ⟨secondAbsent, cycleNodup⟩⟩

theorem flattenedPositions_length_of_mem
    {partition : Partition} (member : partition ∈ partitions) :
    (partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).length = 8 := by
  simp [equatorialCycle_length_of_mem member]

theorem partitions_nodup : partitions.Nodup := by
  unfold partitions
  rw [List.nodup_flatMap]
  constructor
  · intro axial _member
    apply (List.nodup_permutations _ (remainingPositions_nodup axial)).map
    intro left right equal
    exact congrArg Partition.equatorialCycle equal
  · have pairsNodup := axialPairs_nodup
    rw [List.nodup_iff_pairwise_ne] at pairsNodup
    apply pairsNodup.imp
    intro left right different
    rw [Function.onFun, List.disjoint_left]
    intro candidate leftMember rightMember
    rcases List.mem_map.mp leftMember with ⟨leftCycle, _leftCycleMember, rfl⟩
    rcases List.mem_map.mp rightMember with ⟨rightCycle, _rightCycleMember, equal⟩
    exact different (congrArg Partition.axial equal).symm

/-- Indexed access to the six-position cycle.  The default is unreachable for members of
`partitions`, whose cycle length is proved to be six. -/
def cycleAt (cycle : List (Fin 8)) (position : Fin 6) : Fin 8 :=
  (cycle[position.val]?).getD 0

def next6 : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 0

/-- The index-normal form selecting one representative of the six rotations and two traversal
directions of a physical hexagonal boundary. -/
def CanonicalCycle (cycle : List (Fin 8)) : Prop :=
  (∀ position : Fin 6, (cycleAt cycle 0).val ≤ (cycleAt cycle position).val) ∧
    (cycleAt cycle 1).val < (cycleAt cycle 5).val

instance canonicalCycleDecidable (cycle : List (Fin 8)) : Decidable (CanonicalCycle cycle) := by
  unfold CanonicalCycle
  infer_instance

/-- Exact center-antiparallel relation for the axial reference pair. -/
def IsCenterAntiparallelPair (frame : Frame) (first second : Fin 8) : Prop :=
  first ≠ second ∧
  ((frame.donorAt first).y - frame.center.y) *
        ((frame.donorAt second).z - frame.center.z) -
      ((frame.donorAt first).z - frame.center.z) *
        ((frame.donorAt second).y - frame.center.y) = 0 ∧
  ((frame.donorAt first).z - frame.center.z) *
        ((frame.donorAt second).x - frame.center.x) -
      ((frame.donorAt first).x - frame.center.x) *
        ((frame.donorAt second).z - frame.center.z) = 0 ∧
  ((frame.donorAt first).x - frame.center.x) *
        ((frame.donorAt second).y - frame.center.y) -
      ((frame.donorAt first).y - frame.center.y) *
        ((frame.donorAt second).x - frame.center.x) = 0 ∧
  ((frame.donorAt first).x - frame.center.x) *
        ((frame.donorAt second).x - frame.center.x) +
      ((frame.donorAt first).y - frame.center.y) *
        ((frame.donorAt second).y - frame.center.y) +
      ((frame.donorAt first).z - frame.center.z) *
        ((frame.donorAt second).z - frame.center.z) < 0

instance isCenterAntiparallelPairDecidable
    (frame : Frame) (first second : Fin 8) :
    Decidable (IsCenterAntiparallelPair frame first second) := by
  unfold IsCenterAntiparallelPair
  infer_instance

def equatorialPoint (frame : Frame) (partition : Partition) (position : Fin 6) :
    CartesianPoint3 :=
  frame.donorAt (cycleAt partition.equatorialCycle position)

/-- Every equatorial radius is perpendicular to the axial reference line. -/
def EquatorialPlanePerpendicular (frame : Frame) (partition : Partition) : Prop :=
  ∀ position : Fin 6,
    ((equatorialPoint frame partition position).x - frame.center.x) *
          ((frame.donorAt partition.axial.1).x - frame.center.x) +
        ((equatorialPoint frame partition position).y - frame.center.y) *
          ((frame.donorAt partition.axial.1).y - frame.center.y) +
        ((equatorialPoint frame partition position).z - frame.center.z) *
          ((frame.donorAt partition.axial.1).z - frame.center.z) = 0

instance equatorialPlanePerpendicularDecidable (frame : Frame) (partition : Partition) :
    Decidable (EquatorialPlanePerpendicular frame partition) := by
  unfold EquatorialPlanePerpendicular
  infer_instance

/-- The center is the exact centroid of the six equatorial donors. -/
def CenterAtEquatorialCentroid (frame : Frame) (partition : Partition) : Prop :=
  (equatorialPoint frame partition 0).x + (equatorialPoint frame partition 1).x +
      (equatorialPoint frame partition 2).x + (equatorialPoint frame partition 3).x +
      (equatorialPoint frame partition 4).x + (equatorialPoint frame partition 5).x =
        6 * frame.center.x ∧
  (equatorialPoint frame partition 0).y + (equatorialPoint frame partition 1).y +
      (equatorialPoint frame partition 2).y + (equatorialPoint frame partition 3).y +
      (equatorialPoint frame partition 4).y + (equatorialPoint frame partition 5).y =
        6 * frame.center.y ∧
  (equatorialPoint frame partition 0).z + (equatorialPoint frame partition 1).z +
      (equatorialPoint frame partition 2).z + (equatorialPoint frame partition 3).z +
      (equatorialPoint frame partition 4).z + (equatorialPoint frame partition 5).z =
        6 * frame.center.z

instance centerAtEquatorialCentroidDecidable (frame : Frame) (partition : Partition) :
    Decidable (CenterAtEquatorialCentroid frame partition) := by
  unfold CenterAtEquatorialCentroid
  infer_instance

/-- Side-of-directed-edge determinant in the projected equatorial plane. -/
def edgeSideVolume (frame : Frame) (partition : Partition)
    (edge other : Fin 6) : ℚ :=
  CartesianPoint3.orientedVolume
    (equatorialPoint frame partition edge)
    (equatorialPoint frame partition (next6 edge))
    (frame.donorAt partition.axial.1)
    (equatorialPoint frame partition other)

/-- Strict convexity of the stated perimeter.  Requiring every non-edge vertex to lie strictly on
the same side of every directed edge rejects self-intersecting star-polygon traversals. -/
def StrictConvexEquatorialCycle (frame : Frame) (partition : Partition) : Prop :=
  (∀ edge other : Fin 6, other ≠ edge → other ≠ next6 edge →
      0 < edgeSideVolume frame partition edge other) ∨
    (∀ edge other : Fin 6, other ≠ edge → other ≠ next6 edge →
      edgeSideVolume frame partition edge other < 0)

instance strictConvexEquatorialCycleDecidable (frame : Frame) (partition : Partition) :
    Decidable (StrictConvexEquatorialCycle frame partition) := by
  unfold StrictConvexEquatorialCycle
  infer_instance

/-- Viewed determinant for two equatorial sites from one axial endpoint. -/
def progressionDeterminant (frame : Frame) (partition : Partition)
    (viewpoint : Fin 8) (first second : Fin 6) : ℚ :=
  CartesianPoint3.orientedVolume
    (equatorialPoint frame partition first)
    (equatorialPoint frame partition second)
    (frame.donorAt viewpoint) frame.center

def EquatorialProgressionsNondegenerate (frame : Frame) (partition : Partition) : Prop :=
  ∀ viewpoint, viewpoint = partition.axial.1 ∨ viewpoint = partition.axial.2 →
    ∀ first second : Fin 6, first ≠ second →
      progressionDeterminant frame partition viewpoint first second ≠ 0

instance equatorialProgressionsNondegenerateDecidable (frame : Frame) (partition : Partition) :
    Decidable (EquatorialProgressionsNondegenerate frame partition) := by
  unfold EquatorialProgressionsNondegenerate
  infer_instance

/-- Independent exact idealized HBPY-8 partition judgment. -/
def IsHexagonalBipyramidPartition (frame : Frame) (partition : Partition) : Prop :=
  partition ∈ partitions ∧
    CanonicalCycle partition.equatorialCycle ∧
    IsCenterAntiparallelPair frame partition.axial.1 partition.axial.2 ∧
    EquatorialPlanePerpendicular frame partition ∧
    CenterAtEquatorialCentroid frame partition ∧
    StrictConvexEquatorialCycle frame partition ∧
    EquatorialProgressionsNondegenerate frame partition

instance isHexagonalBipyramidPartitionDecidable (frame : Frame) (partition : Partition) :
    Decidable (IsHexagonalBipyramidPartition frame partition) := by
  unfold IsHexagonalBipyramidPartition
  infer_instance

def partitionCandidate? (frame : Frame) (partition : Partition) : Bool :=
  decide (IsHexagonalBipyramidPartition frame partition)

@[simp] theorem partitionCandidate?_eq_true_iff (frame : Frame) (partition : Partition) :
    partitionCandidate? frame partition = true ↔
      IsHexagonalBipyramidPartition frame partition := by
  simp [partitionCandidate?]

def Judgment (frame : Frame) (partition : Partition) : Prop :=
  partition ∈ partitions ∧
    IsHexagonalBipyramidPartition frame partition ∧
    ∀ other ∈ partitions,
      IsHexagonalBipyramidPartition frame other → other = partition

def perceive? (frame : Frame) : Option Partition :=
  uniqueSatisfying? partitions (partitionCandidate? frame)

theorem perceive?_eq_some_iff (frame : Frame) (partition : Partition) :
    perceive? frame = some partition ↔ Judgment frame partition := by
  rw [perceive?, uniqueSatisfying?_eq_some_iff partitions
    (partitionCandidate? frame) partitions_nodup partition]
  simp only [partitionCandidate?_eq_true_iff]
  rfl

theorem perceive?_eq_none_iff (frame : Frame) :
    perceive? frame = none ↔ ¬ ∃ partition, Judgment frame partition := by
  constructor
  · intro absent ⟨partition, judged⟩
    have present := (perceive?_eq_some_iff frame partition).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : perceive? frame with
    | none => rfl
    | some partition =>
        exact False.elim (noJudgment ⟨partition,
          (perceive?_eq_some_iff frame partition).mp computed⟩)

theorem progressionDeterminant_ne_zero_of_judgment
    {frame : Frame} {partition : Partition}
    (judged : Judgment frame partition)
    {viewpoint : Fin 8}
    (viewpointAxial : viewpoint = partition.axial.1 ∨ viewpoint = partition.axial.2)
    {first second : Fin 6} (different : first ≠ second) :
    progressionDeterminant frame partition viewpoint first second ≠ 0 :=
  judged.2.1.2.2.2.2.2.2 viewpoint viewpointAxial first second different

end TetraStereo.OneCenter.RedBookIR9.HexagonalBipyramid8SpatialPerception
