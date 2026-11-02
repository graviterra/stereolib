import TetraStereo.OneCenter.IR9TrigonalBipyramid5SpatialPerception
import Mathlib.Data.List.Permutation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.HeptagonalBipyramid9SpatialPerception

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles

/-!
# Exact coordinate perception for idealized HBPY-9

The finite recognizer exhausts every unordered axial pair and every order of the other seven
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
  donor8 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

def donorAt (frame : Frame) : Fin 9 → CartesianPoint3
  | 0 => frame.donor0
  | 1 => frame.donor1
  | 2 => frame.donor2
  | 3 => frame.donor3
  | 4 => frame.donor4
  | 5 => frame.donor5
  | 6 => frame.donor6
  | 7 => frame.donor7
  | 8 => frame.donor8

end Frame

def positions9 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

@[simp] theorem mem_positions9 (position : Fin 9) : position ∈ positions9 := by
  fin_cases position <;> simp [positions9]

theorem positions9_nodup : positions9.Nodup := by decide

/-- Every unordered pair of nine donor positions, in canonical index order. -/
def axialPairs : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8),
    (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8),
    (3, 4), (3, 5), (3, 6), (3, 7), (3, 8),
    (4, 5), (4, 6), (4, 7), (4, 8),
    (5, 6), (5, 7), (5, 8),
    (6, 7), (6, 8), (7, 8)]

theorem axialPairs_nodup : axialPairs.Nodup := by decide

/-- The explicit list contains exactly the increasing representatives of all unordered pairs. -/
theorem mem_axialPairs_iff (pair : Fin 9 × Fin 9) :
    pair ∈ axialPairs ↔ pair.1.val < pair.2.val := by
  rcases pair with ⟨first, second⟩
  fin_cases first <;> fin_cases second <;> decide

/-- Hence every pair of distinct sites occurs exactly once, in one of its two orientations. -/
theorem unordered_axialPair_covered (first second : Fin 9) :
    first ≠ second ↔
      (first, second) ∈ axialPairs ∨ (second, first) ∈ axialPairs := by
  fin_cases first <;> fin_cases second <;> decide

theorem axialPairs_length : axialPairs.length = 36 := by decide

theorem axialPair_distinct {pair : Fin 9 × Fin 9} (member : pair ∈ axialPairs) :
    pair.1 ≠ pair.2 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide

def remainingPositions (pair : Fin 9 × Fin 9) : List (Fin 9) :=
  positions9.filter fun position => position != pair.1 && position != pair.2

theorem remainingPositions_nodup (pair : Fin 9 × Fin 9) :
    (remainingPositions pair).Nodup :=
  positions9_nodup.filter _

theorem remainingPositions_length
    {pair : Fin 9 × Fin 9} (member : pair ∈ axialPairs) :
    (remainingPositions pair).length = 7 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide

structure Partition where
  axial : Fin 9 × Fin 9
  equatorialCycle : List (Fin 9)
  deriving DecidableEq, Repr

/-- Exhaustive finite axial-pair/equatorial-order search space. -/
def partitions : List Partition :=
  axialPairs.flatMap fun axial =>
    (remainingPositions axial).permutations.map fun cycle =>
      { axial, equatorialCycle := cycle }

/-- The raw search contains `36 × 7! = 181440` axial-pair/cycle candidates. -/
theorem partitions_length : partitions.length = 181440 := by
  unfold partitions
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_permutations]
  have mapped :
      axialPairs.map (fun pair => (remainingPositions pair).length.factorial) =
        axialPairs.map (fun _pair => Nat.factorial 7) := by
    apply List.map_congr_left
    intro pair member
    rw [remainingPositions_length member]
  rw [mapped]
  norm_num [axialPairs, Nat.factorial]

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
    partition.equatorialCycle.length = 7 := by
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
    simp [remainingPositions, mem_positions9] at remainingMember
  have secondAbsent : partition.axial.2 ∉ partition.equatorialCycle := by
    intro present
    have remainingMember : partition.axial.2 ∈ remainingPositions partition.axial :=
      permutation.mem_iff.mp present
    simp [remainingPositions, mem_positions9] at remainingMember
  exact List.nodup_cons.mpr ⟨by simp [pairDistinct, firstAbsent],
    List.nodup_cons.mpr ⟨secondAbsent, cycleNodup⟩⟩

theorem flattenedPositions_length_of_mem
    {partition : Partition} (member : partition ∈ partitions) :
    (partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).length = 9 := by
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

/-- Indexed access to the seven-position cycle.  The default is unreachable for members of
`partitions`, whose cycle length is proved to be seven. -/
def cycleAt (cycle : List (Fin 9)) (position : Fin 7) : Fin 9 :=
  (cycle[position.val]?).getD 0

def next7 : Fin 7 → Fin 7
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 0

/-- The index-normal form selecting one representative of the seven rotations and two traversal
directions of a physical heptagonal boundary. -/
def CanonicalCycle (cycle : List (Fin 9)) : Prop :=
  (∀ position : Fin 7, (cycleAt cycle 0).val ≤ (cycleAt cycle position).val) ∧
    (cycleAt cycle 1).val < (cycleAt cycle 6).val

instance canonicalCycleDecidable (cycle : List (Fin 9)) : Decidable (CanonicalCycle cycle) := by
  unfold CanonicalCycle
  infer_instance

/-- Exact center-antiparallel relation for the axial reference pair. -/
def IsCenterAntiparallelPair (frame : Frame) (first second : Fin 9) : Prop :=
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
    (frame : Frame) (first second : Fin 9) :
    Decidable (IsCenterAntiparallelPair frame first second) := by
  unfold IsCenterAntiparallelPair
  infer_instance

def equatorialPoint (frame : Frame) (partition : Partition) (position : Fin 7) :
    CartesianPoint3 :=
  frame.donorAt (cycleAt partition.equatorialCycle position)

/-- Every equatorial radius is perpendicular to the axial reference line. -/
def EquatorialPlanePerpendicular (frame : Frame) (partition : Partition) : Prop :=
  ∀ position : Fin 7,
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

/-- The center is the exact centroid of the seven equatorial donors. -/
def CenterAtEquatorialCentroid (frame : Frame) (partition : Partition) : Prop :=
  (equatorialPoint frame partition 0).x + (equatorialPoint frame partition 1).x +
      (equatorialPoint frame partition 2).x + (equatorialPoint frame partition 3).x +
      (equatorialPoint frame partition 4).x + (equatorialPoint frame partition 5).x +
      (equatorialPoint frame partition 6).x = 7 * frame.center.x ∧
  (equatorialPoint frame partition 0).y + (equatorialPoint frame partition 1).y +
      (equatorialPoint frame partition 2).y + (equatorialPoint frame partition 3).y +
      (equatorialPoint frame partition 4).y + (equatorialPoint frame partition 5).y +
      (equatorialPoint frame partition 6).y = 7 * frame.center.y ∧
  (equatorialPoint frame partition 0).z + (equatorialPoint frame partition 1).z +
      (equatorialPoint frame partition 2).z + (equatorialPoint frame partition 3).z +
      (equatorialPoint frame partition 4).z + (equatorialPoint frame partition 5).z +
      (equatorialPoint frame partition 6).z = 7 * frame.center.z

instance centerAtEquatorialCentroidDecidable (frame : Frame) (partition : Partition) :
    Decidable (CenterAtEquatorialCentroid frame partition) := by
  unfold CenterAtEquatorialCentroid
  infer_instance

/-- Side-of-directed-edge determinant in the projected equatorial plane. -/
def edgeSideVolume (frame : Frame) (partition : Partition)
    (edge other : Fin 7) : ℚ :=
  CartesianPoint3.orientedVolume
    (equatorialPoint frame partition edge)
    (equatorialPoint frame partition (next7 edge))
    (frame.donorAt partition.axial.1)
    (equatorialPoint frame partition other)

/-- Strict convexity of the stated perimeter.  Requiring every non-edge vertex to lie strictly on
the same side of every directed edge rejects self-intersecting star-polygon traversals. -/
def StrictConvexEquatorialCycle (frame : Frame) (partition : Partition) : Prop :=
  (∀ edge other : Fin 7, other ≠ edge → other ≠ next7 edge →
      0 < edgeSideVolume frame partition edge other) ∨
    (∀ edge other : Fin 7, other ≠ edge → other ≠ next7 edge →
      edgeSideVolume frame partition edge other < 0)

instance strictConvexEquatorialCycleDecidable (frame : Frame) (partition : Partition) :
    Decidable (StrictConvexEquatorialCycle frame partition) := by
  unfold StrictConvexEquatorialCycle
  infer_instance

/-- Viewed determinant for two equatorial sites from one axial endpoint. -/
def progressionDeterminant (frame : Frame) (partition : Partition)
    (viewpoint : Fin 9) (first second : Fin 7) : ℚ :=
  CartesianPoint3.orientedVolume
    (equatorialPoint frame partition first)
    (equatorialPoint frame partition second)
    (frame.donorAt viewpoint) frame.center

def EquatorialProgressionsNondegenerate (frame : Frame) (partition : Partition) : Prop :=
  ∀ viewpoint, viewpoint = partition.axial.1 ∨ viewpoint = partition.axial.2 →
    ∀ first second : Fin 7, first ≠ second →
      progressionDeterminant frame partition viewpoint first second ≠ 0

instance equatorialProgressionsNondegenerateDecidable (frame : Frame) (partition : Partition) :
    Decidable (EquatorialProgressionsNondegenerate frame partition) := by
  unfold EquatorialProgressionsNondegenerate
  infer_instance

/-- Independent exact idealized HBPY-9 partition judgment. -/
def IsHeptagonalBipyramidPartition (frame : Frame) (partition : Partition) : Prop :=
  partition ∈ partitions ∧
    CanonicalCycle partition.equatorialCycle ∧
    IsCenterAntiparallelPair frame partition.axial.1 partition.axial.2 ∧
    EquatorialPlanePerpendicular frame partition ∧
    CenterAtEquatorialCentroid frame partition ∧
    StrictConvexEquatorialCycle frame partition ∧
    EquatorialProgressionsNondegenerate frame partition

instance isHeptagonalBipyramidPartitionDecidable (frame : Frame) (partition : Partition) :
    Decidable (IsHeptagonalBipyramidPartition frame partition) := by
  unfold IsHeptagonalBipyramidPartition
  infer_instance

def partitionCandidate? (frame : Frame) (partition : Partition) : Bool :=
  decide (IsHeptagonalBipyramidPartition frame partition)

@[simp] theorem partitionCandidate?_eq_true_iff (frame : Frame) (partition : Partition) :
    partitionCandidate? frame partition = true ↔
      IsHeptagonalBipyramidPartition frame partition := by
  simp [partitionCandidate?]

def Judgment (frame : Frame) (partition : Partition) : Prop :=
  partition ∈ partitions ∧
    IsHeptagonalBipyramidPartition frame partition ∧
    ∀ other ∈ partitions,
      IsHeptagonalBipyramidPartition frame other → other = partition

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
    {viewpoint : Fin 9}
    (viewpointAxial : viewpoint = partition.axial.1 ∨ viewpoint = partition.axial.2)
    {first second : Fin 7} (different : first ≠ second) :
    progressionDeterminant frame partition viewpoint first second ≠ 0 :=
  judged.2.1.2.2.2.2.2.2 viewpoint viewpointAxial first second different

end TetraStereo.OneCenter.RedBookIR9.HeptagonalBipyramid9SpatialPerception
