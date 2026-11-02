import TetraStereo.OneCenter.CIPIR9FourCoordinateSpatialRoleIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SeeSawSpatialOrientation

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles

/-!
# Exact physical A/C progression for idealized SS-4 frames

The IUPAC see-saw reference direction is the senior member of the largest-angle pair.  On the
exact idealized domain, the largest-angle pair is the unique center-antiparallel donor pair.  The
remaining pair is read from its senior member to its junior member while looking from the senior
axial donor toward the center.

For an observer on that outward viewing ray, the exact scalar triple product
`(remainingSenior - center) × (remainingJunior - center) · (viewpoint - center)` is positive for
counterclockwise progression and negative for clockwise progression.  A zero determinant, a CIP
tie, or absent/non-unique exact axial geometry is refused.
-/

/-- Strictly order two positions by their molecule-derived polyhedral priorities. -/
def strictOrderPair?
    (placement : Fin 4 → PolyhedralPriorityNumber) (pair : Fin 4 × Fin 4) :
    Option (Fin 4 × Fin 4) :=
  if (placement pair.1).outranks (placement pair.2) then
    some pair
  else if (placement pair.2).outranks (placement pair.1) then
    some (pair.2, pair.1)
  else
    none

/-- Declarative strict ordering of the same unordered pair. -/
def IsStrictOrder
    (placement : Fin 4 → PolyhedralPriorityNumber) (pair ordered : Fin 4 × Fin 4) : Prop :=
  (ordered = pair ∧ (placement pair.1).outranks (placement pair.2) = true) ∨
    (ordered = (pair.2, pair.1) ∧
      (placement pair.2).outranks (placement pair.1) = true)

theorem outranks_asymmetric
    {left right : PolyhedralPriorityNumber}
    (forward : left.outranks right = true) : right.outranks left = false := by
  simp [PolyhedralPriorityNumber.outranks] at forward ⊢
  omega

theorem strictOrderPair?_eq_some_iff
    (placement : Fin 4 → PolyhedralPriorityNumber) (pair ordered : Fin 4 × Fin 4) :
    strictOrderPair? placement pair = some ordered ↔ IsStrictOrder placement pair ordered := by
  unfold strictOrderPair? IsStrictOrder
  by_cases forward : (placement pair.1).outranks (placement pair.2) = true
  · have reverse := outranks_asymmetric forward
    simp [forward, reverse, eq_comm]
  · have forwardFalse : (placement pair.1).outranks (placement pair.2) = false := by
      exact Bool.eq_false_of_not_eq_true forward
    by_cases reverse : (placement pair.2).outranks (placement pair.1) = true
    · simp [forwardFalse, reverse, eq_comm]
    · have reverseFalse : (placement pair.2).outranks (placement pair.1) = false := by
        exact Bool.eq_false_of_not_eq_true reverse
      simp [forwardFalse, reverseFalse]

/-- The other two donor positions for each canonical unordered pair. -/
def complementaryPair? (pair : Fin 4 × Fin 4) : Option (Fin 4 × Fin 4) :=
  if pair = (0, 1) then some (2, 3)
  else if pair = (0, 2) then some (1, 3)
  else if pair = (0, 3) then some (1, 2)
  else if pair = (1, 2) then some (0, 3)
  else if pair = (1, 3) then some (0, 2)
  else if pair = (2, 3) then some (0, 1)
  else none

theorem complementaryPair?_exists_of_mem_unorderedPairs
    {pair : Fin 4 × Fin 4} (member : pair ∈ unorderedPairs) :
    ∃ remaining, complementaryPair? pair = some remaining := by
  simp [unorderedPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [complementaryPair?]

/-- The exact right-handed scalar triple product for the source-prescribed view and progression. -/
def progressionDeterminant
    (frame : FourCoordinateSpatialPerception.Frame)
    (viewpoint remainingSenior remainingJunior : Fin 4) : ℚ :=
  CartesianPoint3.orientedVolume
    (frame.donorAt remainingSenior)
    (frame.donorAt remainingJunior)
    (frame.donorAt viewpoint)
    frame.center

@[simp] theorem donorAt_map
    (frame : FourCoordinateSpatialPerception.Frame)
    (transform : FourCoordinateSpatialPerception.FrameTransform) (position : Fin 4) :
    (frame.map transform).donorAt position = transform.applyPoint (frame.donorAt position) := by
  fin_cases position <;> rfl

/-- The progression determinant has the expected affine determinant scaling law.  Therefore its
sign is preserved by every orientation-preserving exact affine coordinate change and reversed by
every orientation-reversing one. -/
@[simp] theorem progressionDeterminant_map
    (frame : FourCoordinateSpatialPerception.Frame)
    (transform : FourCoordinateSpatialPerception.FrameTransform)
    (viewpoint remainingSenior remainingJunior : Fin 4) :
    progressionDeterminant (frame.map transform) viewpoint remainingSenior remainingJunior =
      transform.determinant *
        progressionDeterminant frame viewpoint remainingSenior remainingJunior := by
  unfold progressionDeterminant
  rw [donorAt_map, donorAt_map, donorAt_map]
  change CartesianPoint3.orientedVolume
      (transform.applyPoint (frame.donorAt remainingSenior))
      (transform.applyPoint (frame.donorAt remainingJunior))
      (transform.applyPoint (frame.donorAt viewpoint))
      (transform.applyPoint frame.center) = _
  exact FourCoordinateSpatialPerception.FrameTransform.orientedVolume_applyPoint _ _ _ _ _

theorem progressionDeterminant_eq_scalarTriple
    (frame : FourCoordinateSpatialPerception.Frame)
    (viewpoint remainingSenior remainingJunior : Fin 4) :
    progressionDeterminant frame viewpoint remainingSenior remainingJunior =
      let ux := (frame.donorAt remainingSenior).x - frame.center.x
      let uy := (frame.donorAt remainingSenior).y - frame.center.y
      let uz := (frame.donorAt remainingSenior).z - frame.center.z
      let vx := (frame.donorAt remainingJunior).x - frame.center.x
      let vy := (frame.donorAt remainingJunior).y - frame.center.y
      let vz := (frame.donorAt remainingJunior).z - frame.center.z
      let wx := (frame.donorAt viewpoint).x - frame.center.x
      let wy := (frame.donorAt viewpoint).y - frame.center.y
      let wz := (frame.donorAt viewpoint).z - frame.center.z
      (uy * vz - uz * vy) * wx +
        (uz * vx - ux * vz) * wy +
        (ux * vy - uy * vx) * wz := by
  simp [progressionDeterminant, CartesianPoint3.orientedVolume]
  ring

/-- Exact sign-to-sense conversion in the senior-axial viewing convention. -/
def senseOfDeterminant? (determinant : ℚ) : Option PolyhedralRotationSense :=
  if 0 < determinant then some .counterclockwise
  else if determinant < 0 then some .clockwise
  else none

theorem senseOfDeterminant?_eq_some_iff
    (determinant : ℚ) (sense : PolyhedralRotationSense) :
    senseOfDeterminant? determinant = some sense ↔
      (sense = .counterclockwise ∧ 0 < determinant) ∨
      (sense = .clockwise ∧ determinant < 0) := by
  by_cases positive : 0 < determinant
  · cases sense <;> simp [senseOfDeterminant?, positive, eq_comm]
    all_goals linarith
  · by_cases negative : determinant < 0
    · cases sense <;> simp [senseOfDeterminant?, positive, negative, eq_comm]
    · cases sense <;> simp [senseOfDeterminant?, positive, negative, eq_comm]

theorem senseOfDeterminant?_positive_scale
    (scale determinant : ℚ) (positiveScale : 0 < scale) :
    senseOfDeterminant? (scale * determinant) = senseOfDeterminant? determinant := by
  unfold senseOfDeterminant?
  by_cases positive : 0 < determinant
  · have scaledPositive : 0 < scale * determinant := mul_pos positiveScale positive
    simp [positive, scaledPositive]
  · by_cases negative : determinant < 0
    · have scaledNegative : scale * determinant < 0 := mul_neg_of_pos_of_neg positiveScale negative
      have scaledNotPositive : ¬ 0 < scale * determinant := not_lt_of_ge (le_of_lt scaledNegative)
      simp [positive, negative, scaledNegative, scaledNotPositive]
    · have zero : determinant = 0 := le_antisymm (le_of_not_gt positive) (le_of_not_gt negative)
      simp [zero]

theorem progressionSense_map_of_positiveDeterminant
    (frame : FourCoordinateSpatialPerception.Frame)
    (transform : FourCoordinateSpatialPerception.FrameTransform)
    (viewpoint remainingSenior remainingJunior : Fin 4)
    (positiveTransform : 0 < transform.determinant) :
    senseOfDeterminant?
        (progressionDeterminant (frame.map transform)
          viewpoint remainingSenior remainingJunior) =
      senseOfDeterminant?
        (progressionDeterminant frame viewpoint remainingSenior remainingJunior) := by
  rw [progressionDeterminant_map]
  exact senseOfDeterminant?_positive_scale _ _ positiveTransform

/-- Fully coordinate- and priority-derived see-saw rotation sense. -/
def rotationSense?
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber) : Option PolyhedralRotationSense := do
  let axialPair ← uniqueCenterAntiparallelPair? frame
  let axialOrder ← strictOrderPair? placement axialPair
  let remainingPair ← complementaryPair? axialPair
  let remainingOrder ← strictOrderPair? placement remainingPair
  senseOfDeterminant?
    (progressionDeterminant frame axialOrder.1 remainingOrder.1 remainingOrder.2)

/-- Declarative physical reading of the exact see-saw reference frame. -/
def Judgment
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) : Prop :=
  ∃ axialPair axialOrder remainingPair remainingOrder,
    axialPair ∈ unorderedPairs ∧
    IsCenterAntiparallelPair frame axialPair.1 axialPair.2 ∧
    (∀ other ∈ unorderedPairs,
      IsCenterAntiparallelPair frame other.1 other.2 → other = axialPair) ∧
    IsStrictOrder placement axialPair axialOrder ∧
    complementaryPair? axialPair = some remainingPair ∧
    IsStrictOrder placement remainingPair remainingOrder ∧
    ((sense = .counterclockwise ∧
        0 < progressionDeterminant frame axialOrder.1 remainingOrder.1 remainingOrder.2) ∨
      (sense = .clockwise ∧
        progressionDeterminant frame axialOrder.1 remainingOrder.1 remainingOrder.2 < 0))

theorem rotationSense?_eq_some_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) :
    rotationSense? frame placement = some sense ↔ Judgment frame placement sense := by
  constructor
  · intro computed
    cases axialEq : uniqueCenterAntiparallelPair? frame with
    | none => simp [rotationSense?, axialEq] at computed
    | some axialPair =>
        cases axialOrderEq : strictOrderPair? placement axialPair with
        | none => simp [rotationSense?, axialEq, axialOrderEq] at computed
        | some axialOrder =>
            cases remainingEq : complementaryPair? axialPair with
            | none => simp [rotationSense?, axialEq, axialOrderEq, remainingEq] at computed
            | some remainingPair =>
                cases remainingOrderEq : strictOrderPair? placement remainingPair with
                | none =>
                    simp [rotationSense?, axialEq, axialOrderEq, remainingEq,
                      remainingOrderEq] at computed
                | some remainingOrder =>
                    have axialFacts :=
                      (uniqueCenterAntiparallelPair?_eq_some_iff frame axialPair).mp axialEq
                    have axialOrdered :=
                      (strictOrderPair?_eq_some_iff placement axialPair axialOrder).mp axialOrderEq
                    have remainingOrdered :=
                      (strictOrderPair?_eq_some_iff placement remainingPair remainingOrder).mp
                        remainingOrderEq
                    have sign :
                        (sense = .counterclockwise ∧
                            0 < progressionDeterminant frame axialOrder.1
                              remainingOrder.1 remainingOrder.2) ∨
                          (sense = .clockwise ∧
                            progressionDeterminant frame axialOrder.1
                              remainingOrder.1 remainingOrder.2 < 0) := by
                      apply (senseOfDeterminant?_eq_some_iff _ sense).mp
                      simpa [rotationSense?, axialEq, axialOrderEq, remainingEq,
                        remainingOrderEq] using computed
                    exact ⟨axialPair, axialOrder, remainingPair, remainingOrder,
                      axialFacts.1, axialFacts.2.1, axialFacts.2.2, axialOrdered,
                      remainingEq, remainingOrdered, sign⟩
  · rintro ⟨axialPair, axialOrder, remainingPair, remainingOrder,
      pairMember, antiparallel, unique, axialOrdered, remainingEq,
      remainingOrdered, sign⟩
    have axialEq : uniqueCenterAntiparallelPair? frame = some axialPair :=
      (uniqueCenterAntiparallelPair?_eq_some_iff frame axialPair).mpr
        ⟨pairMember, antiparallel, unique⟩
    have axialOrderEq : strictOrderPair? placement axialPair = some axialOrder :=
      (strictOrderPair?_eq_some_iff placement axialPair axialOrder).mpr axialOrdered
    have remainingOrderEq : strictOrderPair? placement remainingPair = some remainingOrder :=
      (strictOrderPair?_eq_some_iff placement remainingPair remainingOrder).mpr remainingOrdered
    have signEq :
        senseOfDeterminant?
            (progressionDeterminant frame axialOrder.1 remainingOrder.1 remainingOrder.2) =
          some sense :=
      (senseOfDeterminant?_eq_some_iff _ sense).mpr sign
    simp [rotationSense?, axialEq, axialOrderEq, remainingEq, remainingOrderEq, signEq]

theorem rotationSense?_eq_none_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber) :
    rotationSense? frame placement = none ↔
      ¬ ∃ sense, Judgment frame placement sense := by
  constructor
  · intro none ⟨sense, judgment⟩
    have some := (rotationSense?_eq_some_iff frame placement sense).mpr judgment
    rw [none] at some
    contradiction
  · intro noJudgment
    cases computed : rotationSense? frame placement with
    | none => rfl
    | some sense =>
        exfalso
        exact noJudgment ⟨sense,
          (rotationSense?_eq_some_iff frame placement sense).mp computed⟩

end TetraStereo.OneCenter.RedBookIR9.SeeSawSpatialOrientation
