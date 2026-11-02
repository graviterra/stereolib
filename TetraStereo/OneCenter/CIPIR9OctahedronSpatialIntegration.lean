import TetraStereo.OneCenter.IR9OctahedronSpatialPerception
import TetraStereo.OneCenter.CIPIR9SquarePyramidOctahedronIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.FourCoordinateSpatialRoles
open RedBookIR9.SeeSawSpatialOrientation
open RedBookIR9.SquarePyramid5SpatialOrientation
open RedBookIR9.OctahedronSpatialPerception

/-! # Public molecule/coordinate integration for exact OC-6 -/

def sixPriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) : Fin 6 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4
  | 5 => priority5

def sixPriorityPlacement? (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 6 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5] =>
      some (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5)
  | _ => none

@[simp] theorem sixPriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) :
    sixPriorityPlacement? [priority0, priority1, priority2, priority3, priority4, priority5] =
      some (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5) := rfl

@[simp] theorem sixPriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) (position : Fin 6) :
    [priority0, priority1, priority2, priority3, priority4, priority5][position.val]? =
      some (sixPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 position) := by
  fin_cases position <;> rfl

def octahedronPlanePlacement
    (placement : Fin 6 → PolyhedralPriorityNumber) (axial trans : Fin 6) :
    Fin 4 → PolyhedralPriorityNumber :=
  fun position => placement (remainingOriginalPosition axial trans position)

/-- Unique strict global priority-1 site on the absolute-distinct OC-6 domain. -/
def IsStrictSenior6
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) : Prop :=
  ∀ other, other ≠ senior → (placement senior).outranks (placement other) = true

def isStrictSenior6?
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) : Bool :=
  OctahedronSpatialPerception.positions.all fun other =>
    other == senior || (placement senior).outranks (placement other)

theorem isStrictSenior6?_eq_true_iff
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) :
    isStrictSenior6? placement senior = true ↔ IsStrictSenior6 placement senior := by
  simp only [isStrictSenior6?, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro checked other distinct
    rcases checked other (OctahedronSpatialPerception.mem_positions other) with same | outranks
    · exact (distinct same).elim
    · exact outranks
  · intro seniority other _
    by_cases same : other = senior
    · exact Or.inl same
    · exact Or.inr (seniority other same)

def strictSeniorPosition6?
    (placement : Fin 6 → PolyhedralPriorityNumber) : Option (Fin 6) :=
  uniqueSatisfying? OctahedronSpatialPerception.positions (isStrictSenior6? placement)

theorem strictSeniorPosition6?_eq_some_iff
    (placement : Fin 6 → PolyhedralPriorityNumber) (senior : Fin 6) :
    strictSeniorPosition6? placement = some senior ↔ IsStrictSenior6 placement senior := by
  rw [strictSeniorPosition6?, uniqueSatisfying?_eq_some_iff
    OctahedronSpatialPerception.positions (isStrictSenior6? placement)
    OctahedronSpatialPerception.positions_nodup]
  simp only [OctahedronSpatialPerception.mem_positions, true_and,
    isStrictSenior6?_eq_true_iff]
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

theorem octahedron_trans_planePosition_distinct
    (axial trans : Fin 6) (position : Fin 4)
    (distinct : axial ≠ trans) :
    [trans.val, (remainingOriginalPosition axial trans position).val].eraseDups.length = 2 := by
  have positionNeTrans := remainingOriginalPosition_ne_trans axial trans distinct position
  have valuesNe : trans.val ≠ (remainingOriginalPosition axial trans position).val := by
    intro same
    exact positionNeTrans (Fin.ext same.symm)
  have reverseValuesNe : (remainingOriginalPosition axial trans position).val ≠ trans.val :=
    Ne.symm valuesNe
  simp [List.eraseDups_cons, reverseValuesNe]

structure IndexedOctahedronSpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

def SpatialConfiguration.octahedronFrame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option OctahedronSpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3, donor4, donor5] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      let donorPoint4 ← spatial.positions[donor4]?
      let donorPoint5 ← spatial.positions[donor5]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4
          donor5 := donorPoint5 }
  | _ => none

namespace IndexedOctahedronSpatialObservation

def withDerivedData
    (record : IndexedOctahedronSpatialObservation)
    (axial trans : Fin 6) (planeTrans : Fin 4) (sense : PolyhedralRotationSense) :
    IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .octahedron
    recognition := .higherCoordinationNearestIdealized .octahedron
    ligands := record.ligands
    configurationPositions := .octahedron trans.val
      (remainingOriginalPosition axial trans planeTrans).val
    absoluteOrientation := .octahedronAC (BlueBookP93.rotationOfProduction sense) }

/-- Derive exact OC-6 geometry, both source index roles, and the physical A/C sense. -/
def derivedRecord?
    (record : IndexedOctahedronSpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.octahedronFrame? record.center record.ligands
  if !OctahedronSpatialPerception.recognize? frame then none else
    let priorities ← result.molecularPolyhedralPriorityNumbers?
      record.center .octahedron record.ligands
    let placement ← sixPriorityPlacement? priorities
    let axial ← strictSeniorPosition6? placement
    let trans ← OctahedronSpatialPerception.oppositePosition? frame axial
    let normalized := frame.normalizePlane axial trans
    let planePlacement := octahedronPlanePlacement placement axial trans
    let planeSenior ← strictSeniorPosition? planePlacement
    let planeTrans ← oppositePosition? normalized.baseFrame planeSenior
    let sense ← SquarePyramid5SpatialOrientation.rotationSense? normalized planePlacement
    some (record.withDerivedData axial trans planeTrans sense)

end IndexedOctahedronSpatialObservation

def OctahedronDerivedRecordJudgment
    (record : IndexedOctahedronSpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame priorities placement axial trans planeSenior planeTrans sense,
    spatial.octahedronFrame? record.center record.ligands = some frame ∧
    OctahedronSpatialPerception.IsExactOctahedron frame ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .octahedron record.ligands = some priorities ∧
    sixPriorityPlacement? priorities = some placement ∧
    IsStrictSenior6 placement axial ∧
    OctahedronSpatialPerception.IsAxialPartition frame axial trans ∧
    IsStrictSenior (octahedronPlanePlacement placement axial trans) planeSenior ∧
    IsOppositePair (frame.normalizePlane axial trans).baseFrame planeSenior planeTrans ∧
    (∀ other,
      IsOppositePair (frame.normalizePlane axial trans).baseFrame planeSenior other →
        other = planeTrans) ∧
    SquarePyramid5SpatialOrientation.Judgment
      (frame.normalizePlane axial trans)
      (octahedronPlanePlacement placement axial trans) sense ∧
    derived = record.withDerivedData axial trans planeTrans sense

theorem IndexedOctahedronSpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedOctahedronSpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      OctahedronDerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedOctahedronSpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.octahedronFrame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases recognizedEq : OctahedronSpatialPerception.recognize? frame with
        | false => simp [frameEq, recognizedEq] at computed
        | true =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .octahedron record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : sixPriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    cases axialEq : strictSeniorPosition6? placement with
                    | none =>
                        simp [frameEq, priorityEq, placementEq, axialEq] at computed
                    | some axial =>
                        cases transEq : OctahedronSpatialPerception.oppositePosition? frame axial with
                        | none =>
                            simp [frameEq, recognizedEq, priorityEq, placementEq,
                              axialEq, transEq] at computed
                        | some trans =>
                            let normalized := frame.normalizePlane axial trans
                            let planePlacement := octahedronPlanePlacement placement axial trans
                            cases planeSeniorEq : strictSeniorPosition? planePlacement with
                            | none =>
                                simp [frameEq, recognizedEq, priorityEq, placementEq, axialEq,
                                  transEq, planePlacement, planeSeniorEq] at computed
                            | some planeSenior =>
                                cases planeTransEq : oppositePosition?
                                    normalized.baseFrame planeSenior with
                                | none =>
                                    simp [frameEq, recognizedEq, priorityEq, placementEq, axialEq,
                                      transEq, normalized, planePlacement, planeSeniorEq,
                                      planeTransEq] at computed
                                | some planeTrans =>
                                    cases senseEq : SquarePyramid5SpatialOrientation.rotationSense?
                                        normalized planePlacement with
                                    | none =>
                                        simp [frameEq, recognizedEq, priorityEq, placementEq,
                                          axialEq, transEq, normalized, planePlacement,
                                          planeSeniorEq, senseEq] at computed
                                    | some sense =>
                                        have exactGeometry :=
                                          (OctahedronSpatialPerception.recognize?_eq_true_iff
                                            frame).mp recognizedEq
                                        have axialSeniority :=
                                          (strictSeniorPosition6?_eq_some_iff placement axial).mp axialEq
                                        have transFacts :=
                                          (OctahedronSpatialPerception.oppositePosition?_eq_some_iff
                                            frame axial trans).mp transEq
                                        have partition :=
                                          OctahedronSpatialPerception.axialPartition_of_opposite
                                            frame axial trans exactGeometry transFacts.1 transFacts.2
                                        have planeSeniority :=
                                          (strictSeniorPosition?_eq_some_iff
                                            planePlacement planeSenior).mp planeSeniorEq
                                        have planeTransFacts :=
                                          (oppositePosition?_eq_some_iff
                                            normalized.baseFrame planeSenior planeTrans).mp planeTransEq
                                        have orientation :=
                                          (SquarePyramid5SpatialOrientation.rotationSense?_eq_some_iff
                                            normalized planePlacement sense).mp senseEq
                                        have derivedEq :
                                            derived = record.withDerivedData
                                              axial trans planeTrans sense := by
                                          simpa [frameEq, recognizedEq, priorityEq, placementEq,
                                            axialEq, transEq, normalized, planePlacement,
                                            planeSeniorEq, planeTransEq, senseEq] using computed.symm
                                        exact ⟨frame, priorities, placement, axial, trans, planeSenior,
                                          planeTrans, sense, frameEq, exactGeometry, priorityEq,
                                          placementEq, axialSeniority, partition, planeSeniority,
                                          planeTransFacts.1, planeTransFacts.2, orientation, derivedEq⟩
  · rintro ⟨frame, priorities, placement, axial, trans, planeSenior, planeTrans, sense,
      frameEq, exactGeometry, priorityEq, placementEq, axialSeniority, partition,
      planeSeniority, planeOpposite, planeUnique, orientation, rfl⟩
    let normalized := frame.normalizePlane axial trans
    let planePlacement := octahedronPlanePlacement placement axial trans
    have recognizedEq : OctahedronSpatialPerception.recognize? frame = true :=
      (OctahedronSpatialPerception.recognize?_eq_true_iff frame).mpr exactGeometry
    have axialEq : strictSeniorPosition6? placement = some axial :=
      (strictSeniorPosition6?_eq_some_iff placement axial).mpr axialSeniority
    have transEq : OctahedronSpatialPerception.oppositePosition? frame axial = some trans :=
      (OctahedronSpatialPerception.oppositePosition?_eq_some_iff frame axial trans).mpr
        ⟨partition.1, partition.2.1⟩
    have planeSeniorEq : strictSeniorPosition? planePlacement = some planeSenior :=
      (strictSeniorPosition?_eq_some_iff planePlacement planeSenior).mpr planeSeniority
    have planeTransEq : oppositePosition? normalized.baseFrame planeSenior = some planeTrans :=
      (oppositePosition?_eq_some_iff normalized.baseFrame planeSenior planeTrans).mpr
        ⟨planeOpposite, planeUnique⟩
    have senseEq : SquarePyramid5SpatialOrientation.rotationSense?
        normalized planePlacement = some sense :=
      (SquarePyramid5SpatialOrientation.rotationSense?_eq_some_iff
        normalized planePlacement sense).mpr orientation
    simp [IndexedOctahedronSpatialObservation.derivedRecord?, frameEq, recognizedEq,
      priorityEq, placementEq, axialEq, transEq, normalized, planePlacement,
      planeSeniorEq, planeTransEq, senseEq]

def ChemistryNormalizationResult.octahedronSpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedOctahedronSpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

theorem ChemistryNormalizationResult.octahedronSpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedOctahedronSpatialObservation) :
    result.octahedronSpatialAssignment? spatial record = none ↔
      record.derivedRecord? result spatial = none ∨
        ∃ derived, record.derivedRecord? result spatial = some derived ∧
          result.polyhedralGeometryObservationAssignment? derived = none := by
  unfold ChemistryNormalizationResult.octahedronSpatialAssignment?
  cases derivedEq : record.derivedRecord? result spatial with
  | none => simp
  | some derived =>
      cases producedEq : result.polyhedralGeometryObservationAssignment? derived <;>
        simp [producedEq]

/-- Exact public OC-6 assignment from independently stated exact geometry and derived source roles. -/
theorem ChemistryNormalizationResult.octahedronSpatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : OctahedronSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (axial trans : Fin 6) (planeSenior planeTrans : Fin 4)
    (sense : PolyhedralRotationSense)
    (frameEq : spatial.octahedronFrame? center ligands = some frame)
    (exactGeometry : OctahedronSpatialPerception.IsExactOctahedron frame)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .octahedron ligands =
      some [priority0, priority1, priority2, priority3, priority4, priority5])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5].eraseDups.length = 6)
    (axialSeniority : IsStrictSenior6
      (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5) axial)
    (partition : OctahedronSpatialPerception.IsAxialPartition frame axial trans)
    (planeSeniority : IsStrictSenior
      (octahedronPlanePlacement
        (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5)
        axial trans) planeSenior)
    (planeOpposite : IsOppositePair
      (frame.normalizePlane axial trans).baseFrame planeSenior planeTrans)
    (planeUnique : ∀ other,
      IsOppositePair (frame.normalizePlane axial trans).baseFrame planeSenior other →
        other = planeTrans)
    (orientation : SquarePyramid5SpatialOrientation.Judgment
      (frame.normalizePlane axial trans)
      (octahedronPlanePlacement
        (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5)
        axial trans) sense) :
    result.octahedronSpatialAssignment? spatial { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .octahedron
              configurationIndex :=
                [[sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5
                    trans,
                  sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5
                    (remainingOriginalPosition axial trans planeTrans)]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5
  let normalized := frame.normalizePlane axial trans
  let planePlacement := octahedronPlanePlacement placement axial trans
  have recognizedEq : OctahedronSpatialPerception.recognize? frame = true :=
    (OctahedronSpatialPerception.recognize?_eq_true_iff frame).mpr exactGeometry
  have axialEq : strictSeniorPosition6? placement = some axial :=
    (strictSeniorPosition6?_eq_some_iff placement axial).mpr axialSeniority
  have transEq : OctahedronSpatialPerception.oppositePosition? frame axial = some trans :=
    (OctahedronSpatialPerception.oppositePosition?_eq_some_iff frame axial trans).mpr
      ⟨partition.1, partition.2.1⟩
  have planeSeniorEq : strictSeniorPosition? planePlacement = some planeSenior :=
    (strictSeniorPosition?_eq_some_iff planePlacement planeSenior).mpr planeSeniority
  have planeTransEq : oppositePosition? normalized.baseFrame planeSenior = some planeTrans :=
    (oppositePosition?_eq_some_iff normalized.baseFrame planeSenior planeTrans).mpr
      ⟨planeOpposite, planeUnique⟩
  have senseEq : SquarePyramid5SpatialOrientation.rotationSense?
      normalized planePlacement = some sense :=
    (SquarePyramid5SpatialOrientation.rotationSense?_eq_some_iff
      normalized planePlacement sense).mpr orientation
  have derivedEq :
      IndexedOctahedronSpatialObservation.derivedRecord?
          ({ center := center, ligands := ligands }) result spatial =
        some (IndexedOctahedronSpatialObservation.withDerivedData
          ({ center := center, ligands := ligands }) axial trans planeTrans sense) := by
    simp [IndexedOctahedronSpatialObservation.derivedRecord?, frameEq, recognizedEq,
      priorityEq, sixPriorityPlacement?_explicit, placement, normalized, planePlacement,
      axialEq, transEq, planeSeniorEq, planeTransEq, senseEq]
  have positionsDistinct := octahedron_trans_planePosition_distinct
    axial trans planeTrans partition.1.1
  have lookups :
      [trans.val, (remainingOriginalPosition axial trans planeTrans).val].mapM
          (fun position =>
            [priority0, priority1, priority2, priority3, priority4, priority5][position]?) =
        some [placement trans, placement (remainingOriginalPosition axial trans planeTrans)] := by
    have first := sixPriorityPlacement_lookup
      priority0 priority1 priority2 priority3 priority4 priority5 trans
    have second := sixPriorityPlacement_lookup
      priority0 priority1 priority2 priority3 priority4 priority5
        (remainingOriginalPosition axial trans planeTrans)
    simp
    constructor
    · fin_cases trans <;> rfl
    · generalize remainingOriginalPosition axial trans planeTrans = mapped
      fin_cases mapped <;> rfl
  have downstream := octahedronGeometryObservationAssignment_exact result center ligands sense
    [priority0, priority1, priority2, priority3, priority4, priority5]
    trans.val (remainingOriginalPosition axial trans planeTrans).val
    (placement trans) (placement (remainingOriginalPosition axial trans planeTrans))
    priorityEq prioritiesDistinct positionsDistinct lookups
  simpa [ChemistryNormalizationResult.octahedronSpatialAssignment?, derivedEq,
    IndexedOctahedronSpatialObservation.withDerivedData, placement] using downstream

/-- Completeness on the exact OC-6 domain: the physical plane comparison cannot be degenerate. -/
theorem ChemistryNormalizationResult.octahedronSpatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : OctahedronSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (axial trans : Fin 6) (planeSenior planeTrans : Fin 4)
    (remaining adjacentOrder : Fin 4 × Fin 4)
    (frameEq : spatial.octahedronFrame? center ligands = some frame)
    (exactGeometry : OctahedronSpatialPerception.IsExactOctahedron frame)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .octahedron ligands =
      some [priority0, priority1, priority2, priority3, priority4, priority5])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5].eraseDups.length = 6)
    (axialSeniority : IsStrictSenior6
      (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5) axial)
    (partition : OctahedronSpatialPerception.IsAxialPartition frame axial trans)
    (planeSeniority : IsStrictSenior
      (octahedronPlanePlacement
        (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5)
        axial trans) planeSenior)
    (planeOpposite : IsOppositePair
      (frame.normalizePlane axial trans).baseFrame planeSenior planeTrans)
    (planeUnique : ∀ other,
      IsOppositePair (frame.normalizePlane axial trans).baseFrame planeSenior other →
        other = planeTrans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair?
      planeSenior planeTrans = some remaining)
    (adjacentOrdered : IsStrictOrder
      (octahedronPlanePlacement
        (sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5)
        axial trans) remaining adjacentOrder) :
    ∃ sense,
      result.octahedronSpatialAssignment? spatial { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .octahedron
                configurationIndex :=
                  [[sixPriorityPlacement priority0 priority1 priority2 priority3 priority4
                      priority5 trans,
                    sixPriorityPlacement priority0 priority1 priority2 priority3 priority4
                      priority5 (remainingOriginalPosition axial trans planeTrans)]]
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := sixPriorityPlacement priority0 priority1 priority2 priority3 priority4 priority5
  let normalized := frame.normalizePlane axial trans
  let planePlacement := octahedronPlanePlacement placement axial trans
  obtain ⟨sense, _, orientation⟩ :=
    SquarePyramid5SpatialOrientation.rotationSense?_exists_of_exactGeometry
      normalized planePlacement planeSenior planeTrans remaining adjacentOrder
      partition.2.2.1 partition.2.2.2.1.1 planeSeniority planeOpposite planeUnique
      remainingEq adjacentOrdered
  refine ⟨sense, ?_⟩
  exact result.octahedronSpatial_exact spatial center ligands frame
    priority0 priority1 priority2 priority3 priority4 priority5 axial trans planeSenior planeTrans
    sense frameEq exactGeometry priorityEq prioritiesDistinct axialSeniority partition
    planeSeniority planeOpposite planeUnique orientation

end TetraStereo.OneCenter
