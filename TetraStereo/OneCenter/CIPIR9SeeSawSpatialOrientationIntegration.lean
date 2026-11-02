import TetraStereo.OneCenter.IR9SeeSawSpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.FourCoordinateSpatialPerception
open RedBookIR9.FourCoordinateSpatialRoles
open RedBookIR9.SeeSawSpatialOrientation

/-!
# Molecule-to-SS-4 descriptor with physical A/C derivation

This public route takes only the center, the four ligands, molecular normalization evidence, and
exact coordinates.  It derives the SS-4 family, the unique axial pair, both CIP orderings, and the
A/C progression.  In particular, no rotation sense or absolute descriptor is supplied by the
caller.
-/

/-- See-saw input with no qualitative geometry, distinguished-position, or A/C observation. -/
structure IndexedSeeSawSpatialObservation where
  center : ℕ
  ligands : List ℕ
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

namespace IndexedSeeSawSpatialObservation

/-- Insert only the orientation that was derived from coordinates and molecular CIP priorities. -/
def withDerivedOrientation
    (record : IndexedSeeSawSpatialObservation) (sense : PolyhedralRotationSense) :
    IndexedFourCoordinateSpatialRoleObservation :=
  { center := record.center
    geometry := .seeSaw
    ligands := record.ligands
    absoluteOrientation := .seeSawAC (BlueBookP93.rotationOfProduction sense)
    priming := record.priming }

/-- Derive the complete typed record, refusing every non-SS-4 or physically indeterminate case. -/
def derivedRecord?
    (record : IndexedSeeSawSpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedFourCoordinateSpatialRoleObservation := do
  let frame ← spatial.fourCoordinateFrame? record.center record.ligands
  match FourCoordinateSpatialPerception.observe? frame with
  | some .donorsNoncoplanarCenterOutsideDonorPolyhedron =>
      let priorities ← result.molecularPolyhedralPriorityNumbers?
        record.center .seeSaw record.ligands
      let placement ← fourPriorityPlacement? priorities
      let sense ← SeeSawSpatialOrientation.rotationSense? frame placement
      some (record.withDerivedOrientation sense)
  | _ => none

end IndexedSeeSawSpatialObservation

/-- Public molecule/coordinate-to-SS-4 assignment with no caller-supplied A/C sense. -/
def ChemistryNormalizationResult.seeSawSpatialOrientationAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedSeeSawSpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.fourCoordinateSpatialRoleAssignment? spatial derived

/-- Exact success boundary for derivation of the internal, orientation-bearing record. -/
theorem IndexedSeeSawSpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedSeeSawSpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedFourCoordinateSpatialRoleObservation) :
    record.derivedRecord? result spatial = some derived ↔
      ∃ frame priorities placement sense,
        spatial.fourCoordinateFrame? record.center record.ligands = some frame ∧
        FourCoordinateSpatialPerception.Judgment frame
          .donorsNoncoplanarCenterOutsideDonorPolyhedron ∧
        result.molecularPolyhedralPriorityNumbers?
          record.center .seeSaw record.ligands = some priorities ∧
        fourPriorityPlacement? priorities = some placement ∧
        SeeSawSpatialOrientation.Judgment frame placement sense ∧
        derived = record.withDerivedOrientation sense := by
  constructor
  · intro computed
    unfold IndexedSeeSawSpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.fourCoordinateFrame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases observationEq : FourCoordinateSpatialPerception.observe? frame with
        | none => simp [frameEq, observationEq] at computed
        | some observation =>
            cases observation with
            | allFiveCoplanar => simp [frameEq, observationEq] at computed
            | donorsCoplanarCenterDisplaced => simp [frameEq, observationEq] at computed
            | donorsNoncoplanarCenterInsideDonorPolyhedron =>
                simp [frameEq, observationEq] at computed
            | donorsNoncoplanarCenterOutsideDonorPolyhedron =>
                cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                    record.center .seeSaw record.ligands with
                | none => simp [frameEq, observationEq, priorityEq] at computed
                | some priorities =>
                    cases placementEq : fourPriorityPlacement? priorities with
                    | none => simp [frameEq, observationEq, priorityEq, placementEq] at computed
                    | some placement =>
                        cases senseEq :
                            SeeSawSpatialOrientation.rotationSense? frame placement with
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
                              (SeeSawSpatialOrientation.rotationSense?_eq_some_iff
                                frame placement sense).mp senseEq,
                              derivedEq⟩
  · rintro ⟨frame, priorities, placement, sense, frameEq, outside,
      priorityEq, placementEq, orientation, rfl⟩
    have observationEq : FourCoordinateSpatialPerception.observe? frame =
        some .donorsNoncoplanarCenterOutsideDonorPolyhedron :=
      (FourCoordinateSpatialPerception.observe?_eq_some_iff frame _).mpr outside
    have senseEq : SeeSawSpatialOrientation.rotationSense? frame placement = some sense :=
      (SeeSawSpatialOrientation.rotationSense?_eq_some_iff frame placement sense).mpr orientation
    simp [IndexedSeeSawSpatialObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, placementEq, senseEq]

/-- Exact refusal for the public route: either physical derivation fails or the already-certified
molecule-to-polyhedral descriptor constructor refuses the derived record. -/
theorem ChemistryNormalizationResult.seeSawSpatialOrientationAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedSeeSawSpatialObservation) :
    result.seeSawSpatialOrientationAssignment? spatial record = none ↔
      record.derivedRecord? result spatial = none ∨
        ∃ derived, record.derivedRecord? result spatial = some derived ∧
          result.fourCoordinateSpatialRoleAssignment? spatial derived = none := by
  unfold ChemistryNormalizationResult.seeSawSpatialOrientationAssignment?
  cases derivedEq : record.derivedRecord? result spatial with
  | none => simp
  | some derived =>
      cases producedEq : result.fourCoordinateSpatialRoleAssignment? spatial derived <;>
        simp [producedEq]

/-- Exact final descriptor after all SS-4 geometry, role, priority, and orientation choices have
been derived rather than asserted. -/
theorem ChemistryNormalizationResult.seeSawSpatialOrientation_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (axialPair axialOrder remainingPair remainingOrder : Fin 4 × Fin 4)
    (sense : PolyhedralRotationSense)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (outside : frame.CenterStrictlyOutside)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .seeSaw ligands =
      some [priority0, priority1, priority2, priority3])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3].eraseDups.length = 4)
    (pairMember : axialPair ∈ unorderedPairs)
    (antiparallel : IsCenterAntiparallelPair frame axialPair.1 axialPair.2)
    (unique : ∀ other ∈ unorderedPairs,
      IsCenterAntiparallelPair frame other.1 other.2 → other = axialPair)
    (axialOrdered : IsStrictOrder
      (fourPriorityPlacement priority0 priority1 priority2 priority3) axialPair axialOrder)
    (remainingEq : complementaryPair? axialPair = some remainingPair)
    (remainingOrdered : IsStrictOrder
      (fourPriorityPlacement priority0 priority1 priority2 priority3) remainingPair remainingOrder)
    (progression :
      (sense = .counterclockwise ∧
          0 < progressionDeterminant frame axialOrder.1
            remainingOrder.1 remainingOrder.2) ∨
        (sense = .clockwise ∧
          progressionDeterminant frame axialOrder.1
            remainingOrder.1 remainingOrder.2 < 0)) :
    result.seeSawSpatialOrientationAssignment? spatial
        { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .seeSaw
              configurationIndex :=
                [seeSawConfigurationIndex
                  (fourPriorityPlacement priority0 priority1 priority2 priority3 axialPair.1)
                  (fourPriorityPlacement priority0 priority1 priority2 priority3 axialPair.2)]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := fourPriorityPlacement priority0 priority1 priority2 priority3
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsNoncoplanarCenterOutsideDonorPolyhedron :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame _).mpr
      (.donorsNoncoplanarCenterOutside outside)
  have orientation : SeeSawSpatialOrientation.Judgment frame placement sense :=
    ⟨axialPair, axialOrder, remainingPair, remainingOrder, pairMember, antiparallel,
      unique, axialOrdered, remainingEq, remainingOrdered, progression⟩
  have senseEq : SeeSawSpatialOrientation.rotationSense? frame placement = some sense :=
    (SeeSawSpatialOrientation.rotationSense?_eq_some_iff frame placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } : IndexedSeeSawSpatialObservation).derivedRecord?
          result spatial =
        some
          ({ center := center
             geometry := PolyhedralGeometry.seeSaw
             ligands := ligands
             absoluteOrientation := RedBookIR9.AbsoluteOrientationObservation.seeSawAC
               (BlueBookP93.rotationOfProduction sense) } :
            IndexedFourCoordinateSpatialRoleObservation) := by
    simp [IndexedSeeSawSpatialObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, fourPriorityPlacement?_explicit, placement, senseEq,
      IndexedSeeSawSpatialObservation.withDerivedOrientation]
  have downstream := result.fourCoordinateSpatialRole_seeSaw_exact spatial center ligands frame
    sense priority0 priority1 priority2 priority3 axialPair frameEq outside priorityEq
    prioritiesDistinct pairMember antiparallel unique
  simpa [ChemistryNormalizationResult.seeSawSpatialOrientationAssignment?, derivedEq]
    using downstream

end TetraStereo.OneCenter
