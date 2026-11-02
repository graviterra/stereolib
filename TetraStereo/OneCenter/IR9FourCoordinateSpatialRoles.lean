import TetraStereo.OneCenter.IR9FourCoordinateSpatialPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.FourCoordinateSpatialRoles

open FourCoordinateSpatialPerception
open scoped BigOperators

/-!
# Exact distinguished-site roles for idealized four-coordinate frames

The geometry classifier establishes SP-4/SPY-4/T-4/SS-4 without trusting a qualitative label.
This module derives the next exact idealized subdomain: opposite sites, the unique strict CIP-senior
site, and the unique opposite (largest-angle) pair.  Distorted structures without exact opposite
sites are refused instead of being assigned an unstated tolerance.
-/

/-- Return a value only when exactly one candidate satisfies a decidable predicate. -/
def uniqueSatisfying? {α : Type*} (candidates : List α) (predicate : α → Bool) : Option α :=
  match candidates.filter predicate with
  | [candidate] => some candidate
  | _ => none

theorem uniqueSatisfying?_eq_some_iff
    {α : Type*} [DecidableEq α] (candidates : List α) (predicate : α → Bool)
    (nodup : candidates.Nodup) (candidate : α) :
    uniqueSatisfying? candidates predicate = some candidate ↔
      candidate ∈ candidates ∧ predicate candidate = true ∧
        ∀ other ∈ candidates, predicate other = true → other = candidate := by
  generalize acceptedEq : candidates.filter predicate = accepted
  have acceptedNodup : accepted.Nodup := by
    rw [← acceptedEq]
    exact nodup.filter _
  constructor
  · intro computed
    unfold uniqueSatisfying? at computed
    rw [acceptedEq] at computed
    cases accepted with
    | nil => simp at computed
    | cons head tail =>
        cases tail with
        | nil =>
            simp at computed
            subst head
            have member : candidate ∈ candidates.filter predicate := by
              rw [acceptedEq]
              simp
            have filtered := List.mem_filter.mp member
            refine ⟨filtered.1, filtered.2, ?_⟩
            intro other otherMem acceptedOther
            have inAccepted : other ∈ candidates.filter predicate := by
              exact List.mem_filter.mpr ⟨otherMem, acceptedOther⟩
            rw [acceptedEq] at inAccepted
            simpa using inAccepted
        | cons second rest => simp at computed
  · rintro ⟨candidateMem, candidateAccepted, unique⟩
    have candidateInAccepted : candidate ∈ accepted := by
      rw [← acceptedEq]
      exact List.mem_filter.mpr ⟨candidateMem, candidateAccepted⟩
    have everyAcceptedEq : ∀ other ∈ accepted, other = candidate := by
      intro other otherMem
      have filtered := List.mem_filter.mp (show other ∈ candidates.filter predicate by
        rw [acceptedEq]
        exact otherMem)
      exact unique other filtered.1 filtered.2
    cases accepted with
    | nil => simp at candidateInAccepted
    | cons head tail =>
        have headEq : head = candidate := everyAcceptedEq head (by simp)
        subst head
        have candidateNotTail : candidate ∉ tail := by
          exact (List.nodup_cons.mp acceptedNodup).1
        have tailNil : tail = [] := by
          by_contra notNil
          obtain ⟨other, otherMem⟩ := List.exists_mem_of_ne_nil tail notNil
          have otherEq : other = candidate := everyAcceptedEq other (by simp [otherMem])
          exact candidateNotTail (otherEq ▸ otherMem)
        subst tail
        unfold uniqueSatisfying?
        rw [acceptedEq]

def positions : List (Fin 4) := [0, 1, 2, 3]

theorem positions_nodup : positions.Nodup := by decide

@[simp] theorem mem_positions (position : Fin 4) : position ∈ positions := by
  fin_cases position <;> simp [positions]

/-- Sum one coordinate over the four donor sites. -/
def donorCoordinateSum (frame : FourCoordinateSpatialPerception.Frame)
    (coordinate : CartesianPoint3 → ℚ) : ℚ :=
  ∑ position : Fin 4, coordinate (frame.donorAt position)

@[simp] theorem donorCoordinateSum_reorder
    (frame : FourCoordinateSpatialPerception.Frame)
    (permutation : Equiv.Perm (Fin 4)) (coordinate : CartesianPoint3 → ℚ) :
    donorCoordinateSum (frame.reorder permutation) coordinate =
      donorCoordinateSum frame coordinate := by
  unfold donorCoordinateSum
  simpa only [FourCoordinateSpatialPerception.Frame.donorAt_reorder] using
    (Fintype.sum_equiv permutation
      (fun position => coordinate (frame.donorAt (permutation position)))
      (fun position => coordinate (frame.donorAt position)) (fun _ => rfl))

theorem donorCoordinateSum_x
    (frame : FourCoordinateSpatialPerception.Frame) :
    donorCoordinateSum frame (fun point => point.x) =
      frame.donor0.x + frame.donor1.x + frame.donor2.x + frame.donor3.x := by
  simp [donorCoordinateSum, Fin.sum_univ_four,
    FourCoordinateSpatialPerception.Frame.donorAt]

theorem donorCoordinateSum_y
    (frame : FourCoordinateSpatialPerception.Frame) :
    donorCoordinateSum frame (fun point => point.y) =
      frame.donor0.y + frame.donor1.y + frame.donor2.y + frame.donor3.y := by
  simp [donorCoordinateSum, Fin.sum_univ_four,
    FourCoordinateSpatialPerception.Frame.donorAt]

theorem donorCoordinateSum_z
    (frame : FourCoordinateSpatialPerception.Frame) :
    donorCoordinateSum frame (fun point => point.z) =
      frame.donor0.z + frame.donor1.z + frame.donor2.z + frame.donor3.z := by
  simp [donorCoordinateSum, Fin.sum_univ_four,
    FourCoordinateSpatialPerception.Frame.donorAt]

/-- Two donor sites are opposite vertices of the same idealized four-site parallelogram exactly
when their coordinate sum is half the total donor sum. -/
def IsOppositePair
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) : Prop :=
  first ≠ second ∧
  2 * (frame.donorAt first).x + 2 * (frame.donorAt second).x =
      frame.donor0.x + frame.donor1.x + frame.donor2.x + frame.donor3.x ∧
  2 * (frame.donorAt first).y + 2 * (frame.donorAt second).y =
      frame.donor0.y + frame.donor1.y + frame.donor2.y + frame.donor3.y ∧
  2 * (frame.donorAt first).z + 2 * (frame.donorAt second).z =
      frame.donor0.z + frame.donor1.z + frame.donor2.z + frame.donor3.z

theorem isOppositePair_iff_coordinateSums
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) :
    IsOppositePair frame first second ↔
      first ≠ second ∧
      2 * (frame.donorAt first).x + 2 * (frame.donorAt second).x =
          donorCoordinateSum frame (fun point => point.x) ∧
      2 * (frame.donorAt first).y + 2 * (frame.donorAt second).y =
          donorCoordinateSum frame (fun point => point.y) ∧
      2 * (frame.donorAt first).z + 2 * (frame.donorAt second).z =
          donorCoordinateSum frame (fun point => point.z) := by
  simp only [IsOppositePair, donorCoordinateSum_x, donorCoordinateSum_y,
    donorCoordinateSum_z]

/-- Square-base opposition is covariant under any simultaneous relabeling of donor sites. -/
theorem isOppositePair_reorder_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (permutation : Equiv.Perm (Fin 4)) (first second : Fin 4) :
    IsOppositePair (frame.reorder permutation) first second ↔
      IsOppositePair frame (permutation first) (permutation second) := by
  rw [isOppositePair_iff_coordinateSums, isOppositePair_iff_coordinateSums]
  simp [FourCoordinateSpatialPerception.Frame.donorAt_reorder]

def isOppositePair?
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) : Bool :=
  first != second &&
    (2 * (frame.donorAt first).x + 2 * (frame.donorAt second).x ==
      frame.donor0.x + frame.donor1.x + frame.donor2.x + frame.donor3.x) &&
    (2 * (frame.donorAt first).y + 2 * (frame.donorAt second).y ==
      frame.donor0.y + frame.donor1.y + frame.donor2.y + frame.donor3.y) &&
    (2 * (frame.donorAt first).z + 2 * (frame.donorAt second).z ==
      frame.donor0.z + frame.donor1.z + frame.donor2.z + frame.donor3.z)

@[simp] theorem isOppositePair?_eq_true_iff
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) :
    isOppositePair? frame first second = true ↔ IsOppositePair frame first second := by
  simp [isOppositePair?, IsOppositePair, and_assoc]

theorem isOppositePair_symmetric
    {frame : FourCoordinateSpatialPerception.Frame} {first second : Fin 4}
    (opposite : IsOppositePair frame first second) :
    IsOppositePair frame second first := by
  rcases opposite with ⟨distinct, x, y, z⟩
  refine ⟨distinct.symm, ?_, ?_, ?_⟩ <;> linarith

/-- Unique opposite site for one distinguished donor. -/
def oppositePosition?
    (frame : FourCoordinateSpatialPerception.Frame) (position : Fin 4) : Option (Fin 4) :=
  uniqueSatisfying? positions (isOppositePair? frame position)

theorem oppositePosition?_eq_some_iff
    (frame : FourCoordinateSpatialPerception.Frame) (position opposite : Fin 4) :
    oppositePosition? frame position = some opposite ↔
      IsOppositePair frame position opposite ∧
        ∀ other, IsOppositePair frame position other → other = opposite := by
  rw [oppositePosition?, uniqueSatisfying?_eq_some_iff positions
    (isOppositePair? frame position) positions_nodup]
  simp [mem_positions]

/-- Strict CIP-senior site.  Ties intentionally produce no senior site. -/
def IsStrictSenior (placement : Fin 4 → PolyhedralPriorityNumber) (senior : Fin 4) : Prop :=
  ∀ other, other ≠ senior → (placement senior).outranks (placement other) = true

/-- Reindex a priority placement along the same donor permutation used for its coordinate frame. -/
def reorderPlacement (placement : Fin 4 → PolyhedralPriorityNumber)
    (permutation : Equiv.Perm (Fin 4)) : Fin 4 → PolyhedralPriorityNumber :=
  placement ∘ permutation

theorem isStrictSenior_reorderPlacement_iff
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (permutation : Equiv.Perm (Fin 4)) (senior : Fin 4) :
    IsStrictSenior (reorderPlacement placement permutation) senior ↔
      IsStrictSenior placement (permutation senior) := by
  constructor
  · intro seniority other distinct
    have preimageDistinct : permutation.symm other ≠ senior := by
      intro equal
      apply distinct
      simpa using congrArg permutation equal
    simpa [reorderPlacement] using seniority (permutation.symm other) preimageDistinct
  · intro seniority other distinct
    have imageDistinct : permutation other ≠ permutation senior :=
      fun equal => distinct (permutation.injective equal)
    exact seniority (permutation other) imageDistinct

def isStrictSenior? (placement : Fin 4 → PolyhedralPriorityNumber) (senior : Fin 4) : Bool :=
  positions.all fun other => other == senior || (placement senior).outranks (placement other)

theorem isStrictSenior?_eq_true_iff
    (placement : Fin 4 → PolyhedralPriorityNumber) (senior : Fin 4) :
    isStrictSenior? placement senior = true ↔ IsStrictSenior placement senior := by
  simp only [isStrictSenior?, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro checked other distinct
    rcases checked other (mem_positions other) with same | outranks
    · exact (distinct same).elim
    · exact outranks
  · intro seniority other _
    by_cases same : other = senior
    · exact Or.inl same
    · exact Or.inr (seniority other same)

def strictSeniorPosition? (placement : Fin 4 → PolyhedralPriorityNumber) : Option (Fin 4) :=
  uniqueSatisfying? positions (isStrictSenior? placement)

theorem strictSeniorPosition?_eq_some_iff
    (placement : Fin 4 → PolyhedralPriorityNumber) (senior : Fin 4) :
    strictSeniorPosition? placement = some senior ↔ IsStrictSenior placement senior := by
  rw [strictSeniorPosition?, uniqueSatisfying?_eq_some_iff positions
    (isStrictSenior? placement) positions_nodup]
  simp only [mem_positions, true_and, isStrictSenior?_eq_true_iff]
  constructor
  · exact fun result => result.1
  · intro seniority
    refine ⟨seniority, ?_⟩
    intro other _ otherSeniority
    by_contra different
    have seniorOverOther := seniority other different
    have otherOverSenior := otherSeniority senior (Ne.symm different)
    simp [PolyhedralPriorityNumber.outranks] at seniorOverOther otherOverSenior
    omega

/-- Derive the position trans to the unique strict senior donor. -/
def transToStrictSeniorPosition?
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber) : Option (Fin 4) := do
  let senior ← strictSeniorPosition? placement
  oppositePosition? frame senior

theorem transToStrictSeniorPosition?_eq_some_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber) (trans : Fin 4) :
    transToStrictSeniorPosition? frame placement = some trans ↔
      ∃ senior, IsStrictSenior placement senior ∧
        IsOppositePair frame senior trans ∧
        ∀ other, IsOppositePair frame senior other → other = trans := by
  constructor
  · intro computed
    cases seniorEq : strictSeniorPosition? placement with
    | none => simp [transToStrictSeniorPosition?, seniorEq] at computed
    | some senior =>
        have seniority := (strictSeniorPosition?_eq_some_iff placement senior).mp seniorEq
        have oppositeComputed : oppositePosition? frame senior = some trans := by
          simpa [transToStrictSeniorPosition?, seniorEq] using computed
        exact ⟨senior, seniority,
          (oppositePosition?_eq_some_iff frame senior trans).mp oppositeComputed⟩
  · rintro ⟨senior, seniority, opposite, unique⟩
    have seniorComputed : strictSeniorPosition? placement = some senior :=
      (strictSeniorPosition?_eq_some_iff placement senior).mpr seniority
    have oppositeComputed : oppositePosition? frame senior = some trans :=
      (oppositePosition?_eq_some_iff frame senior trans).mpr ⟨opposite, unique⟩
    simp [transToStrictSeniorPosition?, seniorComputed, oppositeComputed]

/-- Coordinate characterization of two nonzero vectors lying on opposite rays. -/
theorem antiparallelCoordinates_iff
    (ux uy uz vx vy vz : ℚ) :
    (uy * vz - uz * vy = 0 ∧
      uz * vx - ux * vz = 0 ∧
      ux * vy - uy * vx = 0 ∧
      ux * vx + uy * vy + uz * vz < 0) ↔
    ∃ scale : ℚ, 0 < scale ∧ (ux ≠ 0 ∨ uy ≠ 0 ∨ uz ≠ 0) ∧
      vx = -scale * ux ∧ vy = -scale * uy ∧ vz = -scale * uz := by
  constructor
  · rintro ⟨crossX, crossY, crossZ, dotNegative⟩
    have firstNonzero : ux ≠ 0 ∨ uy ≠ 0 ∨ uz ≠ 0 := by
      by_contra allZero
      push_neg at allZero
      rcases allZero with ⟨rfl, rfl, rfl⟩
      norm_num at dotNegative
    rcases firstNonzero with uxNonzero | uyOrUz
    · let scale : ℚ := -(vx / ux)
      have vxEq : vx = -scale * ux := by
        dsimp [scale]
        field_simp
      have vyEq : vy = -scale * uy := by
        dsimp [scale]
        field_simp
        nlinarith
      have vzEq : vz = -scale * uz := by
        dsimp [scale]
        field_simp
        nlinarith
      have normPositive : 0 < ux ^ 2 + uy ^ 2 + uz ^ 2 := by
        nlinarith [sq_pos_of_ne_zero uxNonzero, sq_nonneg uy, sq_nonneg uz]
      have scalePositive : 0 < scale := by
        rw [vxEq, vyEq, vzEq] at dotNegative
        dsimp [scale] at dotNegative ⊢
        nlinarith
      exact ⟨scale, scalePositive, Or.inl uxNonzero, vxEq, vyEq, vzEq⟩
    · rcases uyOrUz with uyNonzero | uzNonzero
      · let scale : ℚ := -(vy / uy)
        have vxEq : vx = -scale * ux := by
          dsimp [scale]
          field_simp
          nlinarith
        have vyEq : vy = -scale * uy := by
          dsimp [scale]
          field_simp
        have vzEq : vz = -scale * uz := by
          dsimp [scale]
          field_simp
          nlinarith
        have normPositive : 0 < ux ^ 2 + uy ^ 2 + uz ^ 2 := by
          nlinarith [sq_nonneg ux, sq_pos_of_ne_zero uyNonzero, sq_nonneg uz]
        have scalePositive : 0 < scale := by
          rw [vxEq, vyEq, vzEq] at dotNegative
          dsimp [scale] at dotNegative ⊢
          nlinarith
        exact ⟨scale, scalePositive, Or.inr (Or.inl uyNonzero), vxEq, vyEq, vzEq⟩
      · let scale : ℚ := -(vz / uz)
        have vxEq : vx = -scale * ux := by
          dsimp [scale]
          field_simp
          nlinarith
        have vyEq : vy = -scale * uy := by
          dsimp [scale]
          field_simp
          nlinarith
        have vzEq : vz = -scale * uz := by
          dsimp [scale]
          field_simp
        have normPositive : 0 < ux ^ 2 + uy ^ 2 + uz ^ 2 := by
          nlinarith [sq_nonneg ux, sq_nonneg uy, sq_pos_of_ne_zero uzNonzero]
        have scalePositive : 0 < scale := by
          rw [vxEq, vyEq, vzEq] at dotNegative
          dsimp [scale] at dotNegative ⊢
          nlinarith
        exact ⟨scale, scalePositive, Or.inr (Or.inr uzNonzero), vxEq, vyEq, vzEq⟩
  · rintro ⟨scale, scalePositive, firstNonzero, rfl, rfl, rfl⟩
    refine ⟨by ring, by ring, by ring, ?_⟩
    rcases firstNonzero with uxNonzero | uyNonzero | uzNonzero
    · nlinarith [sq_pos_of_ne_zero uxNonzero, sq_nonneg uy, sq_nonneg uz]
    · nlinarith [sq_nonneg ux, sq_pos_of_ne_zero uyNonzero, sq_nonneg uz]
    · nlinarith [sq_nonneg ux, sq_nonneg uy, sq_pos_of_ne_zero uzNonzero]

/-- Two donor vectors are exactly antiparallel at the coordination center.  The three cross-product
coordinates enforce collinearity, while the negative dot product chooses the 180-degree rather
than the same-ray orientation.  This is the idealized SS-4 axial-pair relation; unlike the square-
base relation above, it does not require the complementary donors to have the same midpoint. -/
def IsCenterAntiparallelPair
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) : Prop :=
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

theorem isCenterAntiparallelPair_iff_exists_positive_scale
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) :
    IsCenterAntiparallelPair frame first second ↔
      first ≠ second ∧
      ∃ scale : ℚ, 0 < scale ∧
        ((frame.donorAt first).x - frame.center.x ≠ 0 ∨
          (frame.donorAt first).y - frame.center.y ≠ 0 ∨
          (frame.donorAt first).z - frame.center.z ≠ 0) ∧
        (frame.donorAt second).x - frame.center.x =
          -scale * ((frame.donorAt first).x - frame.center.x) ∧
        (frame.donorAt second).y - frame.center.y =
          -scale * ((frame.donorAt first).y - frame.center.y) ∧
        (frame.donorAt second).z - frame.center.z =
          -scale * ((frame.donorAt first).z - frame.center.z) := by
  unfold IsCenterAntiparallelPair
  rw [and_congr_right_iff]
  intro _
  exact antiparallelCoordinates_iff
    ((frame.donorAt first).x - frame.center.x)
    ((frame.donorAt first).y - frame.center.y)
    ((frame.donorAt first).z - frame.center.z)
    ((frame.donorAt second).x - frame.center.x)
    ((frame.donorAt second).y - frame.center.y)
    ((frame.donorAt second).z - frame.center.z)

/-- Center-antiparallel opposition is covariant under the same donor relabeling. -/
theorem isCenterAntiparallelPair_reorder_iff
    (frame : FourCoordinateSpatialPerception.Frame)
    (permutation : Equiv.Perm (Fin 4)) (first second : Fin 4) :
    IsCenterAntiparallelPair (frame.reorder permutation) first second ↔
      IsCenterAntiparallelPair frame (permutation first) (permutation second) := by
  have centerEq : (frame.reorder permutation).center = frame.center := rfl
  simp only [IsCenterAntiparallelPair,
    FourCoordinateSpatialPerception.Frame.donorAt_reorder, centerEq]
  simp

def isCenterAntiparallelPair?
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) : Bool :=
  first != second &&
    (((frame.donorAt first).y - frame.center.y) *
          ((frame.donorAt second).z - frame.center.z) -
        ((frame.donorAt first).z - frame.center.z) *
          ((frame.donorAt second).y - frame.center.y) == 0) &&
    (((frame.donorAt first).z - frame.center.z) *
          ((frame.donorAt second).x - frame.center.x) -
        ((frame.donorAt first).x - frame.center.x) *
          ((frame.donorAt second).z - frame.center.z) == 0) &&
    (((frame.donorAt first).x - frame.center.x) *
          ((frame.donorAt second).y - frame.center.y) -
        ((frame.donorAt first).y - frame.center.y) *
          ((frame.donorAt second).x - frame.center.x) == 0) &&
    decide
      (((frame.donorAt first).x - frame.center.x) *
            ((frame.donorAt second).x - frame.center.x) +
          ((frame.donorAt first).y - frame.center.y) *
            ((frame.donorAt second).y - frame.center.y) +
          ((frame.donorAt first).z - frame.center.z) *
            ((frame.donorAt second).z - frame.center.z) < 0)

@[simp] theorem isCenterAntiparallelPair?_eq_true_iff
    (frame : FourCoordinateSpatialPerception.Frame) (first second : Fin 4) :
    isCenterAntiparallelPair? frame first second = true ↔
      IsCenterAntiparallelPair frame first second := by
  simp [isCenterAntiparallelPair?, IsCenterAntiparallelPair, and_assoc]

theorem isCenterAntiparallelPair_symmetric
    {frame : FourCoordinateSpatialPerception.Frame} {first second : Fin 4}
    (opposite : IsCenterAntiparallelPair frame first second) :
    IsCenterAntiparallelPair frame second first := by
  rcases opposite with ⟨distinct, crossX, crossY, crossZ, dot⟩
  refine ⟨distinct.symm, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Six unordered donor pairs. -/
def unorderedPairs : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

theorem unorderedPairs_nodup : unorderedPairs.Nodup := by decide

/-- The unique exact center-antiparallel pair, i.e. the idealized see-saw 180-degree pair. -/
def uniqueCenterAntiparallelPair?
    (frame : FourCoordinateSpatialPerception.Frame) : Option (Fin 4 × Fin 4) :=
  uniqueSatisfying? unorderedPairs fun pair =>
    isCenterAntiparallelPair? frame pair.1 pair.2

theorem uniqueCenterAntiparallelPair?_eq_some_iff
    (frame : FourCoordinateSpatialPerception.Frame) (pair : Fin 4 × Fin 4) :
    uniqueCenterAntiparallelPair? frame = some pair ↔
      pair ∈ unorderedPairs ∧ IsCenterAntiparallelPair frame pair.1 pair.2 ∧
        ∀ other ∈ unorderedPairs,
          IsCenterAntiparallelPair frame other.1 other.2 → other = pair := by
  rw [uniqueCenterAntiparallelPair?,
    uniqueSatisfying?_eq_some_iff unorderedPairs _ unorderedPairs_nodup]
  simp only [isCenterAntiparallelPair?_eq_true_iff]

end TetraStereo.OneCenter.RedBookIR9.FourCoordinateSpatialRoles
