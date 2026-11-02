import TetraStereo.OneCenter.IR9SquarePyramid5SpatialPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.OctahedronSpatialPerception

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles
open SquarePyramid5SpatialOrientation
open SquarePyramid5SpatialPerception

/-! # Exact coordinate perception for idealized OC-6

An exact octahedral frame consists of one center and six unordered donor coordinates.  Opposite
donors are detected by exact central symmetry.  Removing either end of any such reference axis
must leave a nondegenerate four-donor plane, and the center must lie on the positive ray from the
viewed axial donor toward that plane's centroid.  This is the exact affine domain needed by the
Red Book OC-6 cyclic comparison; no distortion tolerance is introduced.
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

def positions : List (Fin 6) := [0, 1, 2, 3, 4, 5]

@[simp] theorem mem_positions (position : Fin 6) : position ∈ positions := by
  fin_cases position <;> simp [positions]

theorem positions_nodup : positions.Nodup := by decide

/-- The four original positions outside an ordered axial pair. -/
def remainingPositions (axial trans : Fin 6) : List (Fin 6) :=
  positions.filter fun position => position != axial && position != trans

theorem remainingPositions_length
    (axial trans : Fin 6) (distinct : axial ≠ trans) :
    (remainingPositions axial trans).length = 4 := by
  fin_cases axial <;> fin_cases trans <;>
    simp [remainingPositions, positions] at distinct ⊢

/-- Original six-position index of a normalized perpendicular-plane position.  The default branch
is unreachable whenever the two axial positions are distinct. -/
def remainingOriginalPosition (axial trans : Fin 6) (position : Fin 4) : Fin 6 :=
  ((remainingPositions axial trans)[position.val]?).getD 0

theorem remainingOriginalPosition_ne_axial
    (axial trans : Fin 6) (distinct : axial ≠ trans) (position : Fin 4) :
    remainingOriginalPosition axial trans position ≠ axial := by
  fin_cases axial <;> fin_cases trans <;> fin_cases position <;>
    simp [remainingOriginalPosition, remainingPositions, positions] at distinct ⊢

theorem remainingOriginalPosition_ne_trans
    (axial trans : Fin 6) (distinct : axial ≠ trans) (position : Fin 4) :
    remainingOriginalPosition axial trans position ≠ trans := by
  fin_cases axial <;> fin_cases trans <;> fin_cases position <;>
    simp [remainingOriginalPosition, remainingPositions, positions] at distinct ⊢

theorem remainingOriginalPosition_injective :
    ∀ axial trans : Fin 6, axial ≠ trans →
      Function.Injective (remainingOriginalPosition axial trans) := by
  decide

namespace Frame

/-- Present the four donors outside an axial pair as the basal plane of the already certified
four-cycle viewpoint model. -/
def normalizePlane (frame : Frame) (axial trans : Fin 6) :
    SquarePyramid5SpatialOrientation.Frame :=
  { center := frame.center
    apex := frame.donorAt axial
    base0 := frame.donorAt (remainingOriginalPosition axial trans 0)
    base1 := frame.donorAt (remainingOriginalPosition axial trans 1)
    base2 := frame.donorAt (remainingOriginalPosition axial trans 2)
    base3 := frame.donorAt (remainingOriginalPosition axial trans 3) }

@[simp] theorem normalizePlane_apex (frame : Frame) (axial trans : Fin 6) :
    (frame.normalizePlane axial trans).apex = frame.donorAt axial := rfl

@[simp] theorem normalizePlane_baseAt
    (frame : Frame) (axial trans : Fin 6) (position : Fin 4) :
    (frame.normalizePlane axial trans).baseAt position =
      frame.donorAt (remainingOriginalPosition axial trans position) := by
  fin_cases position <;> rfl

end Frame

/-- Exact central opposition of two OC-6 donor sites. -/
def IsOppositePair (frame : Frame) (first second : Fin 6) : Prop :=
  first ≠ second ∧
    (frame.donorAt first).x + (frame.donorAt second).x = 2 * frame.center.x ∧
    (frame.donorAt first).y + (frame.donorAt second).y = 2 * frame.center.y ∧
    (frame.donorAt first).z + (frame.donorAt second).z = 2 * frame.center.z

instance isOppositePairDecidable
    (frame : Frame) (first second : Fin 6) : Decidable (IsOppositePair frame first second) := by
  unfold IsOppositePair
  infer_instance

def isOppositePair? (frame : Frame) (first second : Fin 6) : Bool :=
  decide (IsOppositePair frame first second)

@[simp] theorem isOppositePair?_eq_true_iff
    (frame : Frame) (first second : Fin 6) :
    isOppositePair? frame first second = true ↔ IsOppositePair frame first second := by
  simp [isOppositePair?]

theorem isOppositePair_symmetric
    {frame : Frame} {first second : Fin 6}
    (opposite : IsOppositePair frame first second) :
    IsOppositePair frame second first := by
  rcases opposite with ⟨distinct, x, y, z⟩
  refine ⟨distinct.symm, ?_, ?_, ?_⟩ <;> linarith

def oppositePosition? (frame : Frame) (position : Fin 6) : Option (Fin 6) :=
  uniqueSatisfying? positions (isOppositePair? frame position)

theorem oppositePosition?_eq_some_iff
    (frame : Frame) (position opposite : Fin 6) :
    oppositePosition? frame position = some opposite ↔
      IsOppositePair frame position opposite ∧
        ∀ other, IsOppositePair frame position other → other = opposite := by
  rw [oppositePosition?, uniqueSatisfying?_eq_some_iff positions
    (isOppositePair? frame position) positions_nodup]
  simp [mem_positions]

/-- Exact geometric meaning of choosing one end of an octahedral reference axis. -/
def IsAxialPartition (frame : Frame) (axial trans : Fin 6) : Prop :=
  IsOppositePair frame axial trans ∧
    (∀ other, IsOppositePair frame axial other → other = trans) ∧
    (frame.normalizePlane axial trans).baseFrame.DonorsCoplanarCenterDisplaced ∧
    SquarePyramid5SpatialPerception.AxisTowardCenterNondegenerate
      (frame.normalizePlane axial trans) ∧
    ∀ position : Fin 4,
      ∃ opposite,
        FourCoordinateSpatialRoles.IsOppositePair
          (frame.normalizePlane axial trans).baseFrame position opposite ∧
        ∀ other,
          FourCoordinateSpatialRoles.IsOppositePair
            (frame.normalizePlane axial trans).baseFrame position other →
          other = opposite

/-- Executable exact-axis check.  Each Boolean component has an independently proved declarative
meaning; in particular, the positive-axis test does not search over rational scale witnesses. -/
def axialPartition? (frame : Frame) (axial trans : Fin 6) : Bool :=
  oppositePosition? frame axial == some trans &&
    ((FourCoordinateSpatialPerception.observe?
        (frame.normalizePlane axial trans).baseFrame ==
          some .donorsCoplanarCenterDisplaced) &&
      (SquarePyramid5SpatialPerception.axisTowardCenter?
          (frame.normalizePlane axial trans) &&
        FourCoordinateSpatialRoles.positions.all fun position =>
          (FourCoordinateSpatialRoles.oppositePosition?
            (frame.normalizePlane axial trans).baseFrame position).isSome))

theorem axialPartition?_eq_true_iff
    (frame : Frame) (axial trans : Fin 6) :
    axialPartition? frame axial trans = true ↔ IsAxialPartition frame axial trans := by
  simp only [axialPartition?, Bool.and_eq_true, beq_iff_eq,
    oppositePosition?_eq_some_iff,
    FourCoordinateSpatialPerception.observe?_eq_some_iff,
    FourCoordinateSpatialPerception.judgment_donorsCoplanarCenterDisplaced_iff,
    SquarePyramid5SpatialPerception.axisTowardCenter?_eq_true_iff,
    List.all_eq_true]
  constructor
  · rintro ⟨⟨opposite, unique⟩, displaced, axis, every⟩
    refine ⟨opposite, unique, displaced, axis, ?_⟩
    intro position
    have present := every position (FourCoordinateSpatialRoles.mem_positions position)
    obtain ⟨planeOpposite, computed⟩ := Option.isSome_iff_exists.mp present
    exact ⟨planeOpposite,
      (FourCoordinateSpatialRoles.oppositePosition?_eq_some_iff
        (frame.normalizePlane axial trans).baseFrame position planeOpposite).mp computed⟩
  · rintro ⟨opposite, unique, displaced, axis, every⟩
    refine ⟨⟨opposite, unique⟩, displaced, axis, ?_⟩
    intro position _
    obtain ⟨planeOpposite, planeOppositePair, planeUnique⟩ := every position
    apply Option.isSome_iff_exists.mpr
    exact ⟨planeOpposite,
      (FourCoordinateSpatialRoles.oppositePosition?_eq_some_iff
        (frame.normalizePlane axial trans).baseFrame position planeOpposite).mpr
          ⟨planeOppositePair, planeUnique⟩⟩

/-- Every donor can serve as the viewed end of one unique exact octahedral axis. -/
def IsExactOctahedron (frame : Frame) : Prop :=
  ∀ axial, ∃ trans, IsAxialPartition frame axial trans

def recognize? (frame : Frame) : Bool :=
  positions.all fun axial =>
    match oppositePosition? frame axial with
    | some partner => axialPartition? frame axial partner
    | none => false

theorem recognize?_eq_true_iff (frame : Frame) :
    recognize? frame = true ↔ IsExactOctahedron frame := by
  rw [recognize?, List.all_eq_true]
  constructor
  · intro checked axial
    have accepted := checked axial (mem_positions axial)
    cases computed : oppositePosition? frame axial with
    | none => simp [computed] at accepted
    | some partner =>
        refine ⟨partner, ?_⟩
        apply (axialPartition?_eq_true_iff frame axial partner).mp
        simpa only [computed] using accepted
  · intro exact axial _
    obtain ⟨trans, partition⟩ := exact axial
    have computed : oppositePosition? frame axial = some trans :=
      (oppositePosition?_eq_some_iff frame axial trans).mpr
        ⟨partition.1, partition.2.1⟩
    rw [computed]
    exact (axialPartition?_eq_true_iff frame axial trans).mpr partition

-- Keep the explicit opposite-pair witness in this public theorem's interface.
set_option linter.unusedVariables false in
/-- The partition selected by the executable unique-opposite search carries all exact-octahedral
plane and axis facts. -/
theorem axialPartition_of_opposite
    (frame : Frame) (axial trans : Fin 6)
    (exact : IsExactOctahedron frame)
    (opposite : IsOppositePair frame axial trans)
    (unique : ∀ other, IsOppositePair frame axial other → other = trans) :
    IsAxialPartition frame axial trans := by
  obtain ⟨expected, partition⟩ := exact axial
  have expectedEq : expected = trans := unique expected partition.1
  simpa [expectedEq] using partition

end TetraStereo.OneCenter.RedBookIR9.OctahedronSpatialPerception
