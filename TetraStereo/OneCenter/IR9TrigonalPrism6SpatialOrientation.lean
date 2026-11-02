import TetraStereo.OneCenter.IR9TrigonalPrism6SpatialPerception
import TetraStereo.OneCenter.IR9TrigonalBipyramid5SpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalPrism6SpatialOrientation

open FourCoordinateSpatialRoles
open TrigonalPrism6SpatialPerception

abbrev Frame := TrigonalPrism6SpatialPerception.Frame

/-!
# Exact physical A/C progression for idealized TPR-6

On the absolute-distinct priority domain, the triangular face containing the unique global-senior
donor is the preferred face.  The opposite face is read from its own strict senior donor through
its second-senior donor while viewing from above the preferred face.  This is the IR-9.3.4.9
construction specialized to the priority domain already required by the public polyhedral route.
-/

def positions6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

@[simp] theorem mem_positions6 (position : Fin 6) : position ∈ positions6 := by
  fin_cases position <;> simp [positions6]

theorem positions6_nodup : positions6.Nodup := by decide

def IsStrictSenior6
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) : Prop :=
  ∀ other, other ≠ senior →
    (placement senior).outranks (placement other) = true

def isStrictSenior6?
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) : Bool :=
  positions6.all fun other =>
    other == senior || (placement senior).outranks (placement other)

theorem isStrictSenior6?_eq_true_iff
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) :
    isStrictSenior6? placement senior = true ↔ IsStrictSenior6 placement senior := by
  simp only [isStrictSenior6?, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro checked other different
    rcases checked other (mem_positions6 other) with same | outranks
    · exact (different same).elim
    · exact outranks
  · intro seniority other _
    by_cases same : other = senior
    · exact Or.inl same
    · exact Or.inr (seniority other same)

def strictSeniorPosition6?
    (placement : Fin 6 → PolyhedralPriorityNumber) : Option (Fin 6) :=
  uniqueSatisfying? positions6 (isStrictSenior6? placement)

theorem strictSeniorPosition6?_eq_some_iff
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) :
    strictSeniorPosition6? placement = some senior ↔ IsStrictSenior6 placement senior := by
  rw [strictSeniorPosition6?, uniqueSatisfying?_eq_some_iff positions6
    (isStrictSenior6? placement) positions6_nodup senior]
  simp only [mem_positions6, true_and, isStrictSenior6?_eq_true_iff]
  constructor
  · exact fun result => result.1
  · intro seniority
    refine ⟨seniority, ?_⟩
    intro other _ otherSeniority
    by_contra different
    have seniorOverOther := seniority other different
    have otherOverSenior := otherSeniority senior (Ne.symm different)
    rw [RedBookIR9.SeeSawSpatialOrientation.outranks_asymmetric seniorOverOther]
      at otherOverSenior
    contradiction

structure PreferredFaces where
  preferred : Face
  read : Face
  deriving DecidableEq, Repr

/-- Select the preferred triangular face from the unique global-senior donor. -/
def choosePreferredFaces?
    (faces : CorrespondingFaces) (placement : Fin 6 → PolyhedralPriorityNumber) :
    Option PreferredFaces := do
  let senior ← strictSeniorPosition6? placement
  if senior ∈ faces.first.positions then
    some { preferred := faces.first, read := faces.second }
  else if senior ∈ faces.second.positions then
    some { preferred := faces.second, read := faces.first }
  else none

def PreferredFacesJudgment
    (faces : CorrespondingFaces) (placement : Fin 6 → PolyhedralPriorityNumber)
    (choice : PreferredFaces) : Prop :=
  ∃ senior,
    IsStrictSenior6 placement senior ∧
    ((senior ∈ faces.first.positions ∧
        choice = { preferred := faces.first, read := faces.second }) ∨
      (senior ∈ faces.second.positions ∧
        senior ∉ faces.first.positions ∧
        choice = { preferred := faces.second, read := faces.first }))

theorem choosePreferredFaces?_eq_some_iff
    (faces : CorrespondingFaces) (placement : Fin 6 → PolyhedralPriorityNumber)
    (choice : PreferredFaces) :
    choosePreferredFaces? faces placement = some choice ↔
      PreferredFacesJudgment faces placement choice := by
  constructor
  · intro computed
    unfold choosePreferredFaces? at computed
    cases seniorEq : strictSeniorPosition6? placement with
    | none => simp [seniorEq] at computed
    | some senior =>
        have seniority := (strictSeniorPosition6?_eq_some_iff placement senior).mp seniorEq
        by_cases firstMember : senior ∈ faces.first.positions
        · have choiceEq : choice = { preferred := faces.first, read := faces.second } := by
            simpa [seniorEq, firstMember] using computed.symm
          exact ⟨senior, seniority, Or.inl ⟨firstMember, choiceEq⟩⟩
        · by_cases secondMember : senior ∈ faces.second.positions
          · have choiceEq : choice = { preferred := faces.second, read := faces.first } := by
              simpa [seniorEq, firstMember, secondMember] using computed.symm
            exact ⟨senior, seniority, Or.inr ⟨secondMember, firstMember, choiceEq⟩⟩
          · simp [seniorEq, firstMember, secondMember] at computed
  · rintro ⟨senior, seniority, first | second⟩
    · have seniorEq : strictSeniorPosition6? placement = some senior :=
        (strictSeniorPosition6?_eq_some_iff placement senior).mpr seniority
      rcases first with ⟨member, rfl⟩
      simp [choosePreferredFaces?, seniorEq, member]
    · have seniorEq : strictSeniorPosition6? placement = some senior :=
        (strictSeniorPosition6?_eq_some_iff placement senior).mpr seniority
      rcases second with ⟨secondMember, firstAbsent, rfl⟩
      simp [choosePreferredFaces?, seniorEq, firstAbsent, secondMember]

theorem preferredFaces_are_original_faces
    {faces : CorrespondingFaces} {placement : Fin 6 → PolyhedralPriorityNumber}
    {choice : PreferredFaces}
    (judged : PreferredFacesJudgment faces placement choice) :
    (choice.preferred = faces.first ∧ choice.read = faces.second) ∨
      (choice.preferred = faces.second ∧ choice.read = faces.first) := by
  rcases judged with ⟨senior, seniority, first | second⟩
  · rcases first with ⟨member, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
  · rcases second with ⟨secondMember, firstAbsent, rfl⟩
    exact Or.inr ⟨rfl, rfl⟩

/-- Perceived exhaustive faces make preferred-face selection total once a strict global senior
exists. -/
theorem choosePreferredFaces?_exists_of_perception
    (frame : Frame) (faces : CorrespondingFaces)
    (perceived : TrigonalPrism6SpatialPerception.Judgment frame faces)
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6)
    (seniority : IsStrictSenior6 placement senior) :
    ∃ choice, choosePreferredFaces? faces placement = some choice ∧
      PreferredFacesJudgment faces placement choice := by
  have seniorEq : strictSeniorPosition6? placement = some senior :=
    (strictSeniorPosition6?_eq_some_iff placement senior).mpr seniority
  rcases TrigonalPrism6SpatialPerception.position_mem_first_or_second_of_judgment
      perceived senior with firstMember | secondMember
  · let choice : PreferredFaces := { preferred := faces.first, read := faces.second }
    have computed : choosePreferredFaces? faces placement = some choice := by
      simp [choosePreferredFaces?, seniorEq, firstMember, choice]
    exact ⟨choice, computed,
      (choosePreferredFaces?_eq_some_iff faces placement choice).mp computed⟩
  · by_cases firstMember : senior ∈ faces.first.positions
    · let choice : PreferredFaces := { preferred := faces.first, read := faces.second }
      have computed : choosePreferredFaces? faces placement = some choice := by
        simp [choosePreferredFaces?, seniorEq, firstMember, choice]
      exact ⟨choice, computed,
        (choosePreferredFaces?_eq_some_iff faces placement choice).mp computed⟩
    · let choice : PreferredFaces := { preferred := faces.second, read := faces.first }
      have computed : choosePreferredFaces? faces placement = some choice := by
        simp [choosePreferredFaces?, seniorEq, firstMember, secondMember, choice]
      exact ⟨choice, computed,
        (choosePreferredFaces?_eq_some_iff faces placement choice).mp computed⟩

def facePlacement
    (placement : Fin 6 → PolyhedralPriorityNumber) (face : Face) :
    Fin 3 → PolyhedralPriorityNumber :=
  fun position => placement (face.positionAt position)

def senseOfDeterminant? (determinant : ℚ) : Option PolyhedralRotationSense :=
  RedBookIR9.SeeSawSpatialOrientation.senseOfDeterminant? determinant

theorem senseOfDeterminant?_eq_some_iff
    (determinant : ℚ) (sense : PolyhedralRotationSense) :
    senseOfDeterminant? determinant = some sense ↔
      (sense = .counterclockwise ∧ 0 < determinant) ∨
      (sense = .clockwise ∧ determinant < 0) :=
  RedBookIR9.SeeSawSpatialOrientation.senseOfDeterminant?_eq_some_iff determinant sense

/-- Fully priority- and coordinate-derived IR-9.3.4.9 sense. -/
def rotationSense?
    (frame : Frame) (faces : CorrespondingFaces)
    (placement : Fin 6 → PolyhedralPriorityNumber) : Option PolyhedralRotationSense := do
  let choice ← choosePreferredFaces? faces placement
  let readPlacement := facePlacement placement choice.read
  let senior ← TrigonalBipyramid5SpatialOrientation.strictSeniorPosition3? readPlacement
  let remaining ← TrigonalBipyramid5SpatialOrientation.remainingPair3? senior
  let remainingOrder ←
    TrigonalBipyramid5SpatialOrientation.strictOrderEquatorialPair?
      readPlacement remaining
  senseOfDeterminant?
    (TrigonalPrism6SpatialPerception.progressionDeterminant
      frame choice.preferred choice.read senior remainingOrder.1)

def Judgment
    (frame : Frame) (faces : CorrespondingFaces)
    (placement : Fin 6 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) : Prop :=
  ∃ choice senior remaining remainingOrder,
    PreferredFacesJudgment faces placement choice ∧
    TrigonalBipyramid5SpatialOrientation.IsStrictSenior3
      (facePlacement placement choice.read) senior ∧
    TrigonalBipyramid5SpatialOrientation.remainingPair3? senior = some remaining ∧
    TrigonalBipyramid5SpatialOrientation.IsStrictEquatorialOrder
      (facePlacement placement choice.read) remaining remainingOrder ∧
    ((sense = .counterclockwise ∧
        0 < TrigonalPrism6SpatialPerception.progressionDeterminant
          frame choice.preferred choice.read senior remainingOrder.1) ∨
      (sense = .clockwise ∧
        TrigonalPrism6SpatialPerception.progressionDeterminant
          frame choice.preferred choice.read senior remainingOrder.1 < 0))

theorem rotationSense?_eq_some_iff
    (frame : Frame) (faces : CorrespondingFaces)
    (placement : Fin 6 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) :
    rotationSense? frame faces placement = some sense ↔
      Judgment frame faces placement sense := by
  constructor
  · intro computed
    unfold rotationSense? at computed
    cases choiceEq : choosePreferredFaces? faces placement with
    | none => simp [choiceEq] at computed
    | some choice =>
        let readPlacement := facePlacement placement choice.read
        cases seniorEq :
            TrigonalBipyramid5SpatialOrientation.strictSeniorPosition3? readPlacement with
        | none => simp [choiceEq, readPlacement, seniorEq] at computed
        | some senior =>
            cases remainingEq :
                TrigonalBipyramid5SpatialOrientation.remainingPair3? senior with
            | none => simp [choiceEq, readPlacement, seniorEq, remainingEq] at computed
            | some remaining =>
                cases orderEq :
                    TrigonalBipyramid5SpatialOrientation.strictOrderEquatorialPair?
                      readPlacement remaining with
                | none =>
                    simp [choiceEq, readPlacement, seniorEq, remainingEq, orderEq] at computed
                | some remainingOrder =>
                    have sign := (senseOfDeterminant?_eq_some_iff _ sense).mp
                      (show senseOfDeterminant?
                          (TrigonalPrism6SpatialPerception.progressionDeterminant
                            frame choice.preferred choice.read senior remainingOrder.1) =
                            some sense by
                        simpa [choiceEq, readPlacement, seniorEq, remainingEq, orderEq]
                          using computed)
                    exact ⟨choice, senior, remaining, remainingOrder,
                      (choosePreferredFaces?_eq_some_iff faces placement choice).mp choiceEq,
                      (TrigonalBipyramid5SpatialOrientation.strictSeniorPosition3?_eq_some_iff
                        readPlacement senior).mp seniorEq,
                      remainingEq,
                      (TrigonalBipyramid5SpatialOrientation.strictOrderEquatorialPair?_eq_some_iff
                          readPlacement remaining remainingOrder).mp orderEq,
                      sign⟩
  · rintro ⟨choice, senior, remaining, remainingOrder, preferred,
      seniority, remainingEq, ordered, sign⟩
    let readPlacement := facePlacement placement choice.read
    have choiceEq : choosePreferredFaces? faces placement = some choice :=
      (choosePreferredFaces?_eq_some_iff faces placement choice).mpr preferred
    have seniorEq :
        TrigonalBipyramid5SpatialOrientation.strictSeniorPosition3? readPlacement =
          some senior :=
      (TrigonalBipyramid5SpatialOrientation.strictSeniorPosition3?_eq_some_iff
        readPlacement senior).mpr seniority
    have orderEq :
        TrigonalBipyramid5SpatialOrientation.strictOrderEquatorialPair?
            readPlacement remaining = some remainingOrder :=
      (TrigonalBipyramid5SpatialOrientation.strictOrderEquatorialPair?_eq_some_iff
        readPlacement remaining remainingOrder).mpr ordered
    have signEq : senseOfDeterminant?
        (TrigonalPrism6SpatialPerception.progressionDeterminant
          frame choice.preferred choice.read senior remainingOrder.1) = some sense :=
      (senseOfDeterminant?_eq_some_iff _ sense).mpr sign
    simp [rotationSense?, choiceEq, readPlacement, seniorEq, remainingEq, orderEq, signEq]

theorem progression_ne_zero_of_exactGeometry
    (frame : Frame) (faces : CorrespondingFaces)
    (placement : Fin 6 → PolyhedralPriorityNumber)
    (perceived : TrigonalPrism6SpatialPerception.Judgment frame faces)
    (choice : PreferredFaces) (senior : Fin 3)
    (remaining remainingOrder : Fin 3 × Fin 3)
    (preferred : PreferredFacesJudgment faces placement choice)
    (remainingEq :
      TrigonalBipyramid5SpatialOrientation.remainingPair3? senior = some remaining)
    (ordered : TrigonalBipyramid5SpatialOrientation.IsStrictEquatorialOrder
      (facePlacement placement choice.read) remaining remainingOrder) :
    TrigonalPrism6SpatialPerception.progressionDeterminant
      frame choice.preferred choice.read senior remainingOrder.1 ≠ 0 := by
  apply TrigonalPrism6SpatialPerception.progressionDeterminant_ne_zero_of_judgment perceived
    (preferredFaces_are_original_faces preferred)
  exact TrigonalBipyramid5SpatialOrientation.equatorialOrder_first_ne_senior
    remainingEq ordered

theorem rotationSense?_exists_of_exactGeometry
    (frame : Frame) (faces : CorrespondingFaces)
    (placement : Fin 6 → PolyhedralPriorityNumber)
    (perceived : TrigonalPrism6SpatialPerception.Judgment frame faces)
    (choice : PreferredFaces) (senior : Fin 3)
    (remaining remainingOrder : Fin 3 × Fin 3)
    (preferred : PreferredFacesJudgment faces placement choice)
    (seniority : TrigonalBipyramid5SpatialOrientation.IsStrictSenior3
      (facePlacement placement choice.read) senior)
    (remainingEq :
      TrigonalBipyramid5SpatialOrientation.remainingPair3? senior = some remaining)
    (ordered : TrigonalBipyramid5SpatialOrientation.IsStrictEquatorialOrder
      (facePlacement placement choice.read) remaining remainingOrder) :
    ∃ sense, rotationSense? frame faces placement = some sense ∧
      Judgment frame faces placement sense := by
  have determinantNonzero := progression_ne_zero_of_exactGeometry frame faces placement
    perceived choice senior remaining remainingOrder preferred remainingEq ordered
  let determinant := TrigonalPrism6SpatialPerception.progressionDeterminant
    frame choice.preferred choice.read senior remainingOrder.1
  rcases lt_trichotomy determinant 0 with negative | zero | positive
  · let sense : PolyhedralRotationSense := .clockwise
    have judged : Judgment frame faces placement sense :=
      ⟨choice, senior, remaining, remainingOrder, preferred, seniority, remainingEq, ordered,
        Or.inr ⟨rfl, negative⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame faces placement sense).mpr judged, judged⟩
  · exact (determinantNonzero zero).elim
  · let sense : PolyhedralRotationSense := .counterclockwise
    have judged : Judgment frame faces placement sense :=
      ⟨choice, senior, remaining, remainingOrder, preferred, seniority, remainingEq, ordered,
        Or.inl ⟨rfl, positive⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame faces placement sense).mpr judged, judged⟩

theorem rotationSense?_eq_none_iff
    (frame : Frame) (faces : CorrespondingFaces)
    (placement : Fin 6 → PolyhedralPriorityNumber) :
    rotationSense? frame faces placement = none ↔
      ¬ ∃ sense, Judgment frame faces placement sense := by
  constructor
  · intro absent ⟨sense, judged⟩
    have present := (rotationSense?_eq_some_iff frame faces placement sense).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : rotationSense? frame faces placement with
    | none => rfl
    | some sense =>
        exact False.elim (noJudgment ⟨sense,
          (rotationSense?_eq_some_iff frame faces placement sense).mp computed⟩)

end TetraStereo.OneCenter.RedBookIR9.TrigonalPrism6SpatialOrientation
