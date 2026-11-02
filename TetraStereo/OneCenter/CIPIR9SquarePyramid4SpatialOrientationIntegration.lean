import TetraStereo.OneCenter.IR9SquarePyramid4SpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.FourCoordinateSpatialPerception
open RedBookIR9.FourCoordinateSpatialRoles
open RedBookIR9.SeeSawSpatialOrientation
open RedBookIR9.SquarePyramid4SpatialOrientation

/-! # Molecule-to-SPY-4 descriptor with physical A/C derivation -/

/-- SPY-4 input with no qualitative geometry, distinguished-position, or A/C observation. -/
structure IndexedSquarePyramid4SpatialObservation where
  center : ℕ
  ligands : List ℕ
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

namespace IndexedSquarePyramid4SpatialObservation

def withDerivedOrientation
    (record : IndexedSquarePyramid4SpatialObservation) (sense : PolyhedralRotationSense) :
    IndexedFourCoordinateSpatialRoleObservation :=
  { center := record.center
    geometry := .squarePyramid4
    ligands := record.ligands
    absoluteOrientation := .squarePyramid4AC (BlueBookP93.rotationOfProduction sense)
    priming := record.priming }

/-- Derive the complete typed record, refusing every non-SPY-4 or indeterminate case. -/
def derivedRecord?
    (record : IndexedSquarePyramid4SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedFourCoordinateSpatialRoleObservation := do
  let frame ← spatial.fourCoordinateFrame? record.center record.ligands
  match FourCoordinateSpatialPerception.observe? frame with
  | some .donorsCoplanarCenterDisplaced =>
      let priorities ← result.molecularPolyhedralPriorityNumbers?
        record.center .squarePyramid4 record.ligands
      let placement ← fourPriorityPlacement? priorities
      let sense ← SquarePyramid4SpatialOrientation.rotationSense? frame placement
      some (record.withDerivedOrientation sense)
  | _ => none

end IndexedSquarePyramid4SpatialObservation

/-- Public molecule/coordinate-to-SPY-4 assignment with no caller-supplied A/C sense. -/
def ChemistryNormalizationResult.squarePyramid4SpatialOrientationAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedSquarePyramid4SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.fourCoordinateSpatialRoleAssignment? spatial derived

theorem IndexedSquarePyramid4SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedSquarePyramid4SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedFourCoordinateSpatialRoleObservation) :
    record.derivedRecord? result spatial = some derived ↔
      ∃ frame priorities placement sense,
        spatial.fourCoordinateFrame? record.center record.ligands = some frame ∧
        FourCoordinateSpatialPerception.Judgment frame .donorsCoplanarCenterDisplaced ∧
        result.molecularPolyhedralPriorityNumbers?
          record.center .squarePyramid4 record.ligands = some priorities ∧
        fourPriorityPlacement? priorities = some placement ∧
        SquarePyramid4SpatialOrientation.Judgment frame placement sense ∧
        derived = record.withDerivedOrientation sense := by
  constructor
  · intro computed
    unfold IndexedSquarePyramid4SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.fourCoordinateFrame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases observationEq : FourCoordinateSpatialPerception.observe? frame with
        | none => simp [frameEq, observationEq] at computed
        | some observation =>
            cases observation with
            | allFiveCoplanar => simp [frameEq, observationEq] at computed
            | donorsCoplanarCenterDisplaced =>
                cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                    record.center .squarePyramid4 record.ligands with
                | none => simp [frameEq, observationEq, priorityEq] at computed
                | some priorities =>
                    cases placementEq : fourPriorityPlacement? priorities with
                    | none => simp [frameEq, observationEq, priorityEq, placementEq] at computed
                    | some placement =>
                        cases senseEq :
                            SquarePyramid4SpatialOrientation.rotationSense? frame placement with
                        | none =>
                            simp [frameEq, observationEq, priorityEq, placementEq, senseEq]
                              at computed
                        | some sense =>
                            have derivedEq : derived = record.withDerivedOrientation sense := by
                              simpa [frameEq, observationEq, priorityEq, placementEq, senseEq]
                                using computed.symm
                            exact ⟨frame, priorities, placement, sense, rfl,
                              (FourCoordinateSpatialPerception.observe?_eq_some_iff frame _).mp
                                observationEq,
                              rfl, placementEq,
                              (SquarePyramid4SpatialOrientation.rotationSense?_eq_some_iff
                                frame placement sense).mp senseEq,
                              derivedEq⟩
            | donorsNoncoplanarCenterInsideDonorPolyhedron =>
                simp [frameEq, observationEq] at computed
            | donorsNoncoplanarCenterOutsideDonorPolyhedron =>
                simp [frameEq, observationEq] at computed
  · rintro ⟨frame, priorities, placement, sense, frameEq, displaced,
      priorityEq, placementEq, orientation, rfl⟩
    have observationEq : FourCoordinateSpatialPerception.observe? frame =
        some .donorsCoplanarCenterDisplaced :=
      (FourCoordinateSpatialPerception.observe?_eq_some_iff frame _).mpr displaced
    have senseEq : SquarePyramid4SpatialOrientation.rotationSense? frame placement = some sense :=
      (SquarePyramid4SpatialOrientation.rotationSense?_eq_some_iff
        frame placement sense).mpr orientation
    simp [IndexedSquarePyramid4SpatialObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, placementEq, senseEq]

theorem ChemistryNormalizationResult.squarePyramid4SpatialOrientationAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedSquarePyramid4SpatialObservation) :
    result.squarePyramid4SpatialOrientationAssignment? spatial record = none ↔
      record.derivedRecord? result spatial = none ∨
        ∃ derived, record.derivedRecord? result spatial = some derived ∧
          result.fourCoordinateSpatialRoleAssignment? spatial derived = none := by
  unfold ChemistryNormalizationResult.squarePyramid4SpatialOrientationAssignment?
  cases derivedEq : record.derivedRecord? result spatial with
  | none => simp
  | some derived =>
      cases producedEq : result.fourCoordinateSpatialRoleAssignment? spatial derived <;>
        simp [producedEq]

/-- Exact final SPY-4 descriptor after geometry, role, priority, cyclic comparison, and physical
orientation have all been derived. -/
theorem ChemistryNormalizationResult.squarePyramid4SpatialOrientation_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (sense : PolyhedralRotationSense)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (displaced : frame.DonorsCoplanarCenterDisplaced)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .squarePyramid4 ligands =
      some [priority0, priority1, priority2, priority3])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3].eraseDups.length = 4)
    (seniority : IsStrictSenior
      (fourPriorityPlacement priority0 priority1 priority2 priority3) senior)
    (opposite : IsOppositePair frame senior trans)
    (unique : ∀ other, IsOppositePair frame senior other → other = trans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans =
      some remaining)
    (adjacentOrdered : IsStrictOrder
      (fourPriorityPlacement priority0 priority1 priority2 priority3) remaining adjacentOrder)
    (progression :
      (sense = .counterclockwise ∧
          0 < SquarePyramid4SpatialOrientation.progressionDeterminant
            frame senior adjacentOrder.1) ∨
        (sense = .clockwise ∧
          SquarePyramid4SpatialOrientation.progressionDeterminant
            frame senior adjacentOrder.1 < 0)) :
    result.squarePyramid4SpatialOrientationAssignment? spatial
        { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePyramid4
              configurationIndex :=
                [[fourPriorityPlacement priority0 priority1 priority2 priority3 trans]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := fourPriorityPlacement priority0 priority1 priority2 priority3
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsCoplanarCenterDisplaced :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame _).mpr
      (.donorsCoplanarCenterDisplaced displaced)
  have orientation : SquarePyramid4SpatialOrientation.Judgment frame placement sense :=
    ⟨senior, trans, remaining, adjacentOrder, seniority, opposite, unique,
      remainingEq, adjacentOrdered, progression⟩
  have senseEq : SquarePyramid4SpatialOrientation.rotationSense? frame placement = some sense :=
    (SquarePyramid4SpatialOrientation.rotationSense?_eq_some_iff
      frame placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } :
          IndexedSquarePyramid4SpatialObservation).derivedRecord? result spatial =
        some
          ({ center := center
             geometry := PolyhedralGeometry.squarePyramid4
             ligands := ligands
             absoluteOrientation := RedBookIR9.AbsoluteOrientationObservation.squarePyramid4AC
               (BlueBookP93.rotationOfProduction sense) } :
            IndexedFourCoordinateSpatialRoleObservation) := by
    simp [IndexedSquarePyramid4SpatialObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, fourPriorityPlacement?_explicit, placement, senseEq,
      IndexedSquarePyramid4SpatialObservation.withDerivedOrientation]
  have downstream := result.fourCoordinateSpatialRole_squarePyramid4_exact spatial center ligands
    frame sense priority0 priority1 priority2 priority3 senior trans frameEq displaced priorityEq
    prioritiesDistinct seniority opposite unique
  simpa [ChemistryNormalizationResult.squarePyramid4SpatialOrientationAssignment?, derivedEq]
    using downstream

/-- Completeness on the exact SPY-4 domain: once molecule-derived priorities are distinct and the
formal square-pyramidal role data are exact, the public pipeline cannot refuse for a zero physical
progression.  It emits one of the two Red Book absolute descriptors, with the emitted symbol fixed
by the coordinate-derived clockwise/anticlockwise sense. -/
theorem ChemistryNormalizationResult.squarePyramid4SpatialOrientation_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (displaced : frame.DonorsCoplanarCenterDisplaced)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .squarePyramid4 ligands =
      some [priority0, priority1, priority2, priority3])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3].eraseDups.length = 4)
    (seniority : IsStrictSenior
      (fourPriorityPlacement priority0 priority1 priority2 priority3) senior)
    (opposite : IsOppositePair frame senior trans)
    (unique : ∀ other, IsOppositePair frame senior other → other = trans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans =
      some remaining)
    (adjacentOrdered : IsStrictOrder
      (fourPriorityPlacement priority0 priority1 priority2 priority3) remaining adjacentOrder) :
    ∃ sense,
      result.squarePyramid4SpatialOrientationAssignment? spatial
          { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .squarePyramid4
                configurationIndex :=
                  [[fourPriorityPlacement priority0 priority1 priority2 priority3 trans]]
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := fourPriorityPlacement priority0 priority1 priority2 priority3
  have determinantNonzero :
      SquarePyramid4SpatialOrientation.progressionDeterminant
          frame senior adjacentOrder.1 ≠ 0 :=
    SquarePyramid4SpatialOrientation.progressionDeterminant_ne_zero
      frame placement senior trans remaining adjacentOrder displaced opposite remainingEq
        adjacentOrdered
  rcases lt_trichotomy
      (SquarePyramid4SpatialOrientation.progressionDeterminant
        frame senior adjacentOrder.1) 0 with
    clockwise | zero | counterclockwise
  · refine ⟨.clockwise, ?_⟩
    exact result.squarePyramid4SpatialOrientation_exact spatial center ligands frame
      priority0 priority1 priority2 priority3 senior trans remaining adjacentOrder .clockwise
      frameEq displaced priorityEq prioritiesDistinct seniority opposite unique remainingEq
      adjacentOrdered (Or.inr ⟨rfl, clockwise⟩)
  · exact (determinantNonzero zero).elim
  · refine ⟨.counterclockwise, ?_⟩
    exact result.squarePyramid4SpatialOrientation_exact spatial center ligands frame
      priority0 priority1 priority2 priority3 senior trans remaining adjacentOrder
      .counterclockwise frameEq displaced priorityEq prioritiesDistinct seniority opposite unique
      remainingEq adjacentOrdered (Or.inl ⟨rfl, counterclockwise⟩)

end TetraStereo.OneCenter
