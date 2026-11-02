import TetraStereo.OneCenter.IR9SeeSawSpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquarePyramid4SpatialOrientation

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles
open SeeSawSpatialOrientation

/-!
# Exact physical A/C progression for SPY-4

Red Book IR-9.3.4.6 directs the viewer along the formal C4 axis with the central atom nearer than
the four ligands.  Starting at the highest-priority donor in the perpendicular donor plane, the
clockwise and anticlockwise priority sequences are compared and the direction lower at the first
point of difference supplies C or A.

For four distinct priorities, both readings start at the same senior donor and first differ at its
two adjacent donors.  Thus the source comparison is exactly strict CIP ordering of that adjacent
pair.  The physical direction is then the sign of an exact scalar triple product with the vector
from the donor-plane centroid toward the displaced center/viewer.
-/

/-- The two positions outside a distinct input pair, independent of the pair's presentation order. -/
def remainingPair? (first second : Fin 4) : Option (Fin 4 × Fin 4) :=
  if (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) then some (2, 3)
  else if (first = 0 ∧ second = 2) ∨ (first = 2 ∧ second = 0) then some (1, 3)
  else if (first = 0 ∧ second = 3) ∨ (first = 3 ∧ second = 0) then some (1, 2)
  else if (first = 1 ∧ second = 2) ∨ (first = 2 ∧ second = 1) then some (0, 3)
  else if (first = 1 ∧ second = 3) ∨ (first = 3 ∧ second = 1) then some (0, 2)
  else if (first = 2 ∧ second = 3) ∨ (first = 3 ∧ second = 2) then some (0, 1)
  else none

theorem remainingPair?_exists_of_ne
    (first second : Fin 4) (distinct : first ≠ second) :
    ∃ remaining, remainingPair? first second = some remaining := by
  fin_cases first <;> fin_cases second <;>
    simp [remainingPair?] at distinct ⊢

/-- Exact centroid of the four donor positions. -/
def donorCentroid (frame : FourCoordinateSpatialPerception.Frame) : CartesianPoint3 :=
  { x := donorCoordinateSum frame (fun point => point.x) / 4
    y := donorCoordinateSum frame (fun point => point.y) / 4
    z := donorCoordinateSum frame (fun point => point.z) / 4 }

@[simp] theorem donorCentroid_reorder
    (frame : FourCoordinateSpatialPerception.Frame)
    (permutation : Equiv.Perm (Fin 4)) :
    donorCentroid (frame.reorder permutation) = donorCentroid frame := by
  simp [donorCentroid]

/-- Viewed progression from the global senior donor toward the senior adjacent donor, with the
displaced center on the observer's side of the donor plane. -/
def progressionDeterminant
    (frame : FourCoordinateSpatialPerception.Frame)
    (senior adjacentSenior : Fin 4) : ℚ :=
  CartesianPoint3.orientedVolume
    (frame.donorAt senior) (frame.donorAt adjacentSenior)
    frame.center (donorCentroid frame)

theorem progressionDeterminant_eq_scalarTriple
    (frame : FourCoordinateSpatialPerception.Frame)
    (senior adjacentSenior : Fin 4) :
    progressionDeterminant frame senior adjacentSenior =
      let origin := donorCentroid frame
      let ux := (frame.donorAt senior).x - origin.x
      let uy := (frame.donorAt senior).y - origin.y
      let uz := (frame.donorAt senior).z - origin.z
      let vx := (frame.donorAt adjacentSenior).x - origin.x
      let vy := (frame.donorAt adjacentSenior).y - origin.y
      let vz := (frame.donorAt adjacentSenior).z - origin.z
      let wx := frame.center.x - origin.x
      let wy := frame.center.y - origin.y
      let wz := frame.center.z - origin.z
      (uy * vz - uz * vy) * wx +
        (uz * vx - ux * vz) * wy +
        (ux * vy - uy * vx) * wz := by
  simp [progressionDeterminant, CartesianPoint3.orientedVolume]
  ring

/-- Centroid of four explicitly ordered points. -/
def centroid4 (a b c d : CartesianPoint3) : CartesianPoint3 :=
  { x := (a.x + b.x + c.x + d.x) / 4
    y := (a.y + b.y + c.y + d.y) / 4
    z := (a.z + b.z + c.z + d.z) / 4 }

/-- Algebraic core: in a parallelogram `a+b=c+d`, zero viewed volume from `a` toward adjacent
`c` forces every center-containing four-point minor to vanish. -/
theorem parallelogram_replacementVolumes_zero
    (a b c d center : CartesianPoint3)
    (sumX : a.x + b.x = c.x + d.x)
    (sumY : a.y + b.y = c.y + d.y)
    (sumZ : a.z + b.z = c.z + d.z)
    (progressionZero : CartesianPoint3.orientedVolume a c center (centroid4 a b c d) = 0) :
    CartesianPoint3.orientedVolume center b c d = 0 ∧
      CartesianPoint3.orientedVolume a center c d = 0 ∧
      CartesianPoint3.orientedVolume a b center d = 0 ∧
      CartesianPoint3.orientedVolume a b c center = 0 := by
  have dx : d.x = a.x + b.x - c.x := by linarith
  have dy : d.y = a.y + b.y - c.y := by linarith
  have dz : d.z = a.z + b.z - c.z := by linarith
  have firstIdentity : CartesianPoint3.orientedVolume center b c d =
      -2 * CartesianPoint3.orientedVolume a c center (centroid4 a b c d) := by
    simp [centroid4, CartesianPoint3.orientedVolume, dx, dy, dz]
    ring
  have secondIdentity : CartesianPoint3.orientedVolume a center c d =
      -2 * CartesianPoint3.orientedVolume a c center (centroid4 a b c d) := by
    simp [centroid4, CartesianPoint3.orientedVolume, dx, dy, dz]
    ring
  have thirdIdentity : CartesianPoint3.orientedVolume a b center d =
      2 * CartesianPoint3.orientedVolume a c center (centroid4 a b c d) := by
    simp [centroid4, CartesianPoint3.orientedVolume, dx, dy, dz]
    ring
  have fourthIdentity : CartesianPoint3.orientedVolume a b c center =
      2 * CartesianPoint3.orientedVolume a c center (centroid4 a b c d) := by
    simp [centroid4, CartesianPoint3.orientedVolume, dx, dy, dz]
    ring
  simp [progressionZero] at firstIdentity secondIdentity thirdIdentity fourthIdentity
  exact ⟨firstIdentity, secondIdentity, thirdIdentity, fourthIdentity⟩

/-- Two sites present the same unordered pair. -/
def IsPairOrder (pair : Fin 4 × Fin 4) (first second : Fin 4) : Prop :=
  (first = pair.1 ∧ second = pair.2) ∨ (first = pair.2 ∧ second = pair.1)

theorem isStrictOrder_isPairOrder
    (placement : Fin 4 → PolyhedralPriorityNumber) (pair ordered : Fin 4 × Fin 4)
    (strict : IsStrictOrder placement pair ordered) :
    IsPairOrder pair ordered.1 ordered.2 := by
  rcases strict with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [IsPairOrder]

theorem centroid4_eq_donorCentroid_of_remainingPair
    (frame : FourCoordinateSpatialPerception.Frame)
    (senior trans : Fin 4) (remaining : Fin 4 × Fin 4) (first second : Fin 4)
    (remainingEq : remainingPair? senior trans = some remaining)
    (order : IsPairOrder remaining first second) :
    centroid4 (frame.donorAt senior) (frame.donorAt trans)
        (frame.donorAt first) (frame.donorAt second) = donorCentroid frame := by
  rcases order with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    fin_cases senior <;> fin_cases trans <;>
      simp [remainingPair?] at remainingEq
  all_goals subst remaining
  all_goals
    simp [centroid4, donorCentroid, donorCoordinateSum, Fin.sum_univ_four,
      FourCoordinateSpatialPerception.Frame.donorAt]
    <;> try ring_nf
  all_goals simp

theorem opposite_coordinateSums_of_remainingPair
    (frame : FourCoordinateSpatialPerception.Frame)
    (senior trans : Fin 4) (remaining : Fin 4 × Fin 4) (first second : Fin 4)
    (opposite : IsOppositePair frame senior trans)
    (remainingEq : remainingPair? senior trans = some remaining)
    (order : IsPairOrder remaining first second) :
    (frame.donorAt senior).x + (frame.donorAt trans).x =
        (frame.donorAt first).x + (frame.donorAt second).x ∧
      (frame.donorAt senior).y + (frame.donorAt trans).y =
        (frame.donorAt first).y + (frame.donorAt second).y ∧
      (frame.donorAt senior).z + (frame.donorAt trans).z =
        (frame.donorAt first).z + (frame.donorAt second).z := by
  rcases opposite with ⟨_, oppositeX, oppositeY, oppositeZ⟩
  rcases order with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    fin_cases senior <;> fin_cases trans <;>
      simp [remainingPair?] at remainingEq
  all_goals subst remaining
  all_goals
    simp [FourCoordinateSpatialPerception.Frame.donorAt] at oppositeX oppositeY oppositeZ ⊢
    constructor
    · linarith
    constructor <;> linarith

/-- Present the four donor positions in the order used by the replacement-volume hypotheses. -/
private def donorOrder
    (senior trans first second : Fin 4) : Fin 4 → Fin 4
  | 0 => senior
  | 1 => trans
  | 2 => first
  | 3 => second

private theorem donorOrder_injective_of_remainingPair
    (senior trans : Fin 4) (remaining : Fin 4 × Fin 4) (first second : Fin 4)
    (remainingEq : remainingPair? senior trans = some remaining)
    (order : IsPairOrder remaining first second) :
    Function.Injective (donorOrder senior trans first second) := by
  rcases order with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    fin_cases senior <;> fin_cases trans <;>
      simp [remainingPair?] at remainingEq
  all_goals subst remaining
  all_goals
    intro left right
    fin_cases left <;> fin_cases right <;> simp [donorOrder]

/-- Vanishing of all four center-containing replacement volumes. -/
private def CenterVolumesZero (frame : FourCoordinateSpatialPerception.Frame) : Prop :=
  ∀ position, frame.centerVolumeAt position = 0

private theorem centerVolumesZero_reorder_swap_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (first second : Fin 4) (distinct : first ≠ second) :
    CenterVolumesZero (frame.reorder (Equiv.swap first second)) ↔
      CenterVolumesZero frame := by
  constructor
  · intro reorderedZero position
    have zero := reorderedZero (Equiv.swap first second position)
    rw [FourCoordinateSpatialPerception.Frame.centerVolumeAt_reorder_swap
      frame first second _ distinct] at zero
    simpa using zero
  · intro originalZero position
    rw [FourCoordinateSpatialPerception.Frame.centerVolumeAt_reorder_swap
      frame first second position distinct]
    simpa using originalZero (Equiv.swap first second position)

/-- Vanishing of all replacement volumes is invariant under an arbitrary donor permutation.
This packages the determinant sign changes, which are irrelevant to an equation with zero. -/
private theorem centerVolumesZero_reorder_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (permutation : Equiv.Perm (Fin 4)) :
    CenterVolumesZero (frame.reorder permutation) ↔ CenterVolumesZero frame := by
  induction permutation using Equiv.Perm.swap_induction_on' with
  | one => simp [CenterVolumesZero]
  | mul_swap permutation first second distinct inductionHypothesis =>
      rw [← FourCoordinateSpatialPerception.Frame.reorder_reorder,
        centerVolumesZero_reorder_swap_iff _ first second distinct,
        inductionHypothesis]

theorem centerVolumes_zero_of_remainingPair
    (frame : FourCoordinateSpatialPerception.Frame)
    (senior trans : Fin 4) (remaining : Fin 4 × Fin 4) (first second : Fin 4)
    (remainingEq : remainingPair? senior trans = some remaining)
    (order : IsPairOrder remaining first second)
    (zeroA : CartesianPoint3.orientedVolume frame.center
      (frame.donorAt trans) (frame.donorAt first) (frame.donorAt second) = 0)
    (zeroB : CartesianPoint3.orientedVolume (frame.donorAt senior)
      frame.center (frame.donorAt first) (frame.donorAt second) = 0)
    (zeroC : CartesianPoint3.orientedVolume (frame.donorAt senior)
      (frame.donorAt trans) frame.center (frame.donorAt second) = 0)
    (zeroD : CartesianPoint3.orientedVolume (frame.donorAt senior)
      (frame.donorAt trans) (frame.donorAt first) frame.center = 0) :
    frame.centerVolume0 = 0 ∧ frame.centerVolume1 = 0 ∧
      frame.centerVolume2 = 0 ∧ frame.centerVolume3 = 0 := by
  have orderInjective : Function.Injective (donorOrder senior trans first second) :=
    donorOrder_injective_of_remainingPair senior trans remaining first second remainingEq order
  have orderBijective : Function.Bijective (donorOrder senior trans first second) :=
    ⟨orderInjective, Finite.surjective_of_injective orderInjective⟩
  let permutation : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective (donorOrder senior trans first second) orderBijective
  have reorderedZero : CenterVolumesZero (frame.reorder permutation) := by
    intro position
    fin_cases position
    · simpa [permutation, donorOrder,
        FourCoordinateSpatialPerception.Frame.centerVolumeAt,
        FourCoordinateSpatialPerception.Frame.centerVolume0,
        FourCoordinateSpatialPerception.Frame.reorder] using zeroA
    · simpa [permutation, donorOrder,
        FourCoordinateSpatialPerception.Frame.centerVolumeAt,
        FourCoordinateSpatialPerception.Frame.centerVolume1,
        FourCoordinateSpatialPerception.Frame.reorder] using zeroB
    · simpa [permutation, donorOrder,
        FourCoordinateSpatialPerception.Frame.centerVolumeAt,
        FourCoordinateSpatialPerception.Frame.centerVolume2,
        FourCoordinateSpatialPerception.Frame.reorder] using zeroC
    · simpa [permutation, donorOrder,
        FourCoordinateSpatialPerception.Frame.centerVolumeAt,
        FourCoordinateSpatialPerception.Frame.centerVolume3,
        FourCoordinateSpatialPerception.Frame.reorder] using zeroD
  have originalZero : CenterVolumesZero frame :=
    (centerVolumesZero_reorder_iff frame permutation).mp reorderedZero
  exact ⟨originalZero 0, originalZero 1, originalZero 2, originalZero 3⟩

/-- On the exact displaced-parallelogram domain, the source-selected senior-to-adjacent viewed
progression is necessarily nondegenerate. -/
theorem progressionDeterminant_ne_zero
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (displaced : frame.DonorsCoplanarCenterDisplaced)
    (opposite : IsOppositePair frame senior trans)
    (remainingEq : remainingPair? senior trans = some remaining)
    (adjacentOrdered : IsStrictOrder placement remaining adjacentOrder) :
    progressionDeterminant frame senior adjacentOrder.1 ≠ 0 := by
  intro progressionZero
  have order := isStrictOrder_isPairOrder placement remaining adjacentOrder adjacentOrdered
  have centroidEq := centroid4_eq_donorCentroid_of_remainingPair frame senior trans remaining
    adjacentOrder.1 adjacentOrder.2 remainingEq order
  obtain ⟨sumX, sumY, sumZ⟩ := opposite_coordinateSums_of_remainingPair
    frame senior trans remaining adjacentOrder.1 adjacentOrder.2 opposite remainingEq order
  have genericZero : CartesianPoint3.orientedVolume
      (frame.donorAt senior) (frame.donorAt adjacentOrder.1) frame.center
        (centroid4 (frame.donorAt senior) (frame.donorAt trans)
          (frame.donorAt adjacentOrder.1) (frame.donorAt adjacentOrder.2)) = 0 := by
    rw [centroidEq]
    exact progressionZero
  obtain ⟨zeroA, zeroB, zeroC, zeroD⟩ := parallelogram_replacementVolumes_zero
    (frame.donorAt senior) (frame.donorAt trans)
    (frame.donorAt adjacentOrder.1) (frame.donorAt adjacentOrder.2)
    frame.center sumX sumY sumZ genericZero
  obtain ⟨center0, center1, center2, center3⟩ := centerVolumes_zero_of_remainingPair
    frame senior trans remaining adjacentOrder.1 adjacentOrder.2 remainingEq order
    zeroA zeroB zeroC zeroD
  exact displaced.2 ⟨displaced.1, center0, center1, center2, center3⟩

/-- A positive determinant is counterclockwise/A from the prescribed viewer; a negative one is
clockwise/C. -/
def senseOfDeterminant? (determinant : ℚ) : Option PolyhedralRotationSense :=
  SeeSawSpatialOrientation.senseOfDeterminant? determinant

theorem senseOfDeterminant?_eq_some_iff
    (determinant : ℚ) (sense : PolyhedralRotationSense) :
    senseOfDeterminant? determinant = some sense ↔
      (sense = .counterclockwise ∧ 0 < determinant) ∨
      (sense = .clockwise ∧ determinant < 0) :=
  SeeSawSpatialOrientation.senseOfDeterminant?_eq_some_iff determinant sense

/-- The source's full clockwise/anticlockwise comparison first differs at the two adjacent sites. -/
theorem seniorAdjacent_firstDifference
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (ordered : IsStrictOrder placement remaining adjacentOrder) :
    BlueBookP93.comparePrioritySequence
        [BlueBookP93.priorityOfProduction (placement senior),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.1),
          BlueBookP93.priorityOfProduction (placement trans),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.2)]
        [BlueBookP93.priorityOfProduction (placement senior),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.2),
          BlueBookP93.priorityOfProduction (placement trans),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.1)] = .gt := by
  rcases ordered with ⟨orderedEq, priority⟩ | ⟨orderedEq, priority⟩
  · subst adjacentOrder
    have seniorTo :
        (BlueBookP93.priorityOfProduction (placement remaining.1)).seniorTo
            (BlueBookP93.priorityOfProduction (placement remaining.2)) = true := by
      simpa using priority
    have adjacentDecision :
        BlueBookP93.priorityDecision
            (BlueBookP93.priorityOfProduction (placement remaining.1))
            (BlueBookP93.priorityOfProduction (placement remaining.2)) = .gt := by
      simp [BlueBookP93.priorityDecision, seniorTo]
    have selfDecision (entry : BlueBookP93.PriorityNumber) :
        BlueBookP93.priorityDecision entry entry = .eq := by
      simp [BlueBookP93.priorityDecision, BlueBookP93.PriorityNumber.seniorTo]
    simp only [BlueBookP93.comparePrioritySequence]
    rw [selfDecision, adjacentDecision]
  · subst adjacentOrder
    have seniorTo :
        (BlueBookP93.priorityOfProduction (placement remaining.2)).seniorTo
            (BlueBookP93.priorityOfProduction (placement remaining.1)) = true := by
      simpa using priority
    have adjacentDecision :
        BlueBookP93.priorityDecision
            (BlueBookP93.priorityOfProduction (placement remaining.2))
            (BlueBookP93.priorityOfProduction (placement remaining.1)) = .gt := by
      simp [BlueBookP93.priorityDecision, seniorTo]
    have selfDecision (entry : BlueBookP93.PriorityNumber) :
        BlueBookP93.priorityDecision entry entry = .eq := by
      simp [BlueBookP93.priorityDecision, BlueBookP93.PriorityNumber.seniorTo]
    simp only [BlueBookP93.comparePrioritySequence]
    rw [selfDecision, adjacentDecision]

/-- Fully coordinate- and priority-derived SPY-4 rotation sense. -/
def rotationSense?
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber) : Option PolyhedralRotationSense := do
  let senior ← strictSeniorPosition? placement
  let trans ← oppositePosition? frame senior
  let remaining ← remainingPair? senior trans
  let adjacentOrder ← strictOrderPair? placement remaining
  senseOfDeterminant? (progressionDeterminant frame senior adjacentOrder.1)

/-- Declarative Red Book IR-9.3.4.6 reading of an exact SPY-4 frame. -/
def Judgment
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) : Prop :=
  ∃ senior trans remaining adjacentOrder,
    IsStrictSenior placement senior ∧
    IsOppositePair frame senior trans ∧
    (∀ other, IsOppositePair frame senior other → other = trans) ∧
    remainingPair? senior trans = some remaining ∧
    IsStrictOrder placement remaining adjacentOrder ∧
    ((sense = .counterclockwise ∧
        0 < progressionDeterminant frame senior adjacentOrder.1) ∨
      (sense = .clockwise ∧
        progressionDeterminant frame senior adjacentOrder.1 < 0))

theorem rotationSense?_eq_some_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) :
    rotationSense? frame placement = some sense ↔ Judgment frame placement sense := by
  constructor
  · intro computed
    cases seniorEq : strictSeniorPosition? placement with
    | none => simp [rotationSense?, seniorEq] at computed
    | some senior =>
        cases transEq : oppositePosition? frame senior with
        | none => simp [rotationSense?, seniorEq, transEq] at computed
        | some trans =>
            cases remainingEq : remainingPair? senior trans with
            | none => simp [rotationSense?, seniorEq, transEq, remainingEq] at computed
            | some remaining =>
                cases adjacentEq : strictOrderPair? placement remaining with
                | none =>
                    simp [rotationSense?, seniorEq, transEq, remainingEq, adjacentEq] at computed
                | some adjacentOrder =>
                    have seniority := (strictSeniorPosition?_eq_some_iff placement senior).mp seniorEq
                    have transFacts := (oppositePosition?_eq_some_iff frame senior trans).mp transEq
                    have adjacentOrdered :=
                      (strictOrderPair?_eq_some_iff placement remaining adjacentOrder).mp adjacentEq
                    have sign :
                        (sense = .counterclockwise ∧
                            0 < progressionDeterminant frame senior adjacentOrder.1) ∨
                          (sense = .clockwise ∧
                            progressionDeterminant frame senior adjacentOrder.1 < 0) := by
                      apply (senseOfDeterminant?_eq_some_iff _ sense).mp
                      simpa [rotationSense?, seniorEq, transEq, remainingEq, adjacentEq]
                        using computed
                    exact ⟨senior, trans, remaining, adjacentOrder, seniority,
                      transFacts.1, transFacts.2, remainingEq, adjacentOrdered, sign⟩
  · rintro ⟨senior, trans, remaining, adjacentOrder, seniority,
      opposite, unique, remainingEq, adjacentOrdered, sign⟩
    have seniorEq : strictSeniorPosition? placement = some senior :=
      (strictSeniorPosition?_eq_some_iff placement senior).mpr seniority
    have transEq : oppositePosition? frame senior = some trans :=
      (oppositePosition?_eq_some_iff frame senior trans).mpr ⟨opposite, unique⟩
    have adjacentEq : strictOrderPair? placement remaining = some adjacentOrder :=
      (strictOrderPair?_eq_some_iff placement remaining adjacentOrder).mpr adjacentOrdered
    have signEq : senseOfDeterminant?
        (progressionDeterminant frame senior adjacentOrder.1) = some sense :=
      (senseOfDeterminant?_eq_some_iff _ sense).mpr sign
    simp [rotationSense?, seniorEq, transEq, remainingEq, adjacentEq, signEq]

/-- Exact SPY-4 geometry and strict priority decisions cannot reach the indeterminate determinant
branch: the physical Red Book reading necessarily exists and is either clockwise/C or
counterclockwise/A. -/
theorem rotationSense?_exists_of_exactGeometry
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (displaced : frame.DonorsCoplanarCenterDisplaced)
    (seniority : IsStrictSenior placement senior)
    (opposite : IsOppositePair frame senior trans)
    (unique : ∀ other, IsOppositePair frame senior other → other = trans)
    (remainingEq : remainingPair? senior trans = some remaining)
    (adjacentOrdered : IsStrictOrder placement remaining adjacentOrder) :
    ∃ sense,
      rotationSense? frame placement = some sense ∧
        Judgment frame placement sense := by
  have determinantNonzero :
      progressionDeterminant frame senior adjacentOrder.1 ≠ 0 :=
    progressionDeterminant_ne_zero frame placement senior trans remaining adjacentOrder
      displaced opposite remainingEq adjacentOrdered
  rcases lt_trichotomy
      (progressionDeterminant frame senior adjacentOrder.1) 0 with
    clockwise | zero | counterclockwise
  · let sense : PolyhedralRotationSense := .clockwise
    have judgment : Judgment frame placement sense :=
      ⟨senior, trans, remaining, adjacentOrder, seniority, opposite, unique,
        remainingEq, adjacentOrdered, Or.inr ⟨rfl, clockwise⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame placement sense).mpr judgment, judgment⟩
  · exact (determinantNonzero zero).elim
  · let sense : PolyhedralRotationSense := .counterclockwise
    have judgment : Judgment frame placement sense :=
      ⟨senior, trans, remaining, adjacentOrder, seniority, opposite, unique,
        remainingEq, adjacentOrdered, Or.inl ⟨rfl, counterclockwise⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame placement sense).mpr judgment, judgment⟩

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
    | none => simp
    | some sense =>
        exfalso
        exact noJudgment ⟨sense,
          (rotationSense?_eq_some_iff frame placement sense).mp computed⟩

end TetraStereo.OneCenter.RedBookIR9.SquarePyramid4SpatialOrientation
