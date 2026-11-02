import TetraStereo.OneCenter.IR9FourCoordinateSpatialRoles
import TetraStereo.OneCenter.CIPIR9FourCoordinateSpatialIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.FourCoordinateSpatialPerception
open RedBookIR9.FourCoordinateSpatialRoles

/-!
# Molecule-backed exact four-coordinate role integration

This layer removes the caller-supplied configuration-position observation from the exact
four-coordinate ingress.  Molecular CIP priorities determine a unique strict senior donor;
coordinates determine its square-base opposite site for SP-4/SPY-4, or the unique center-
antiparallel (180-degree) pair for SS-4.
T-4 has no distinguished configuration position.  Priority ties, a non-four-entry priority list,
and absent/non-unique exact opposite relations are refused.
-/

/-- The position-indexed view of four priorities. -/
def fourPriorityPlacement
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber) :
    Fin 4 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3

/-- Accept exactly four priorities, preserving ligand-list order. -/
def fourPriorityPlacement? (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 4 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3] =>
      some (fourPriorityPlacement priority0 priority1 priority2 priority3)
  | _ => none

@[simp] theorem fourPriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber) :
    fourPriorityPlacement? [priority0, priority1, priority2, priority3] =
      some (fourPriorityPlacement priority0 priority1 priority2 priority3) := by
  rfl

@[simp] theorem fourPriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (position : Fin 4) :
    [priority0, priority1, priority2, priority3][position.val]? =
      some (fourPriorityPlacement priority0 priority1 priority2 priority3 position) := by
  fin_cases position <;> rfl

/-- Derive exactly the configuration positions needed by each perceived four-coordinate family. -/
def fourCoordinateConfigurationPositions?
    (frame : FourCoordinateSpatialPerception.Frame)
    (observation : RedBookIR9.FourCoordinateObservation)
    (placement : Fin 4 → PolyhedralPriorityNumber) :
    Option RedBookIR9.ConfigurationPositionObservation :=
  match observation with
  | .allFiveCoplanar =>
      (transToStrictSeniorPosition? frame placement).map
        (fun position => .squarePlanar position.val)
  | .donorsCoplanarCenterDisplaced =>
      (transToStrictSeniorPosition? frame placement).map
        (fun position => .squarePyramid4 position.val)
  | .donorsNoncoplanarCenterInsideDonorPolyhedron =>
      some .noDistinguishedPositions
  | .donorsNoncoplanarCenterOutsideDonorPolyhedron =>
      (uniqueCenterAntiparallelPair? frame).map
        (fun pair => .seeSaw pair.1.val pair.2.val)

/-- Public input with neither a qualitative geometry-recognition answer nor distinguished sites. -/
structure IndexedFourCoordinateSpatialRoleObservation where
  center : ℕ
  geometry : PolyhedralGeometry
  ligands : List ℕ
  absoluteOrientation : RedBookIR9.AbsoluteOrientationObservation
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

namespace IndexedFourCoordinateSpatialRoleObservation

/-- The ordinary spatial record after its positions have been derived. -/
def withDerivedPositions
    (record : IndexedFourCoordinateSpatialRoleObservation)
    (positions : RedBookIR9.ConfigurationPositionObservation) :
    IndexedFourCoordinateSpatialGeometryObservation :=
  { center := record.center
    geometry := record.geometry
    ligands := record.ligands
    configurationPositions := positions
    absoluteOrientation := record.absoluteOrientation
    priming := record.priming }

/-- Collect coordinates, perceive the geometry, compute molecular CIP priorities, and derive the
distinguished configuration positions. -/
def derivedRecord?
    (record : IndexedFourCoordinateSpatialRoleObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedFourCoordinateSpatialGeometryObservation := do
  let frame ← spatial.fourCoordinateFrame? record.center record.ligands
  let observation ← FourCoordinateSpatialPerception.observe? frame
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center record.geometry record.ligands
  let placement ← fourPriorityPlacement? priorities
  let positions ← fourCoordinateConfigurationPositions? frame observation placement
  some (record.withDerivedPositions positions)

end IndexedFourCoordinateSpatialRoleObservation

/-- Public molecule-to-descriptor construction with coordinate-derived recognition and roles. -/
def ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialRoleObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.fourCoordinateSpatialGeometryAssignment? spatial derived

/-- Exact success characterization for the role-derived public route. -/
theorem ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialRoleObservation)
    (assignment : StereoAssignment) :
    result.fourCoordinateSpatialRoleAssignment? spatial record = some assignment ↔
      ∃ frame observation priorities placement positions,
        spatial.fourCoordinateFrame? record.center record.ligands = some frame ∧
        FourCoordinateSpatialPerception.Judgment frame observation ∧
        result.molecularPolyhedralPriorityNumbers?
            record.center record.geometry record.ligands = some priorities ∧
        fourPriorityPlacement? priorities = some placement ∧
        fourCoordinateConfigurationPositions? frame observation placement = some positions ∧
        result.fourCoordinateSpatialGeometryAssignment? spatial
            (record.withDerivedPositions positions) = some assignment := by
  constructor
  · intro produced
    unfold ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment? at produced
    unfold IndexedFourCoordinateSpatialRoleObservation.derivedRecord? at produced
    cases frameEq : spatial.fourCoordinateFrame? record.center record.ligands with
    | none => simp [frameEq] at produced
    | some frame =>
        cases observationEq : FourCoordinateSpatialPerception.observe? frame with
        | none => simp [frameEq, observationEq] at produced
        | some observation =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center record.geometry record.ligands with
            | none => simp [frameEq, priorityEq] at produced
            | some priorities =>
                cases placementEq : fourPriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at produced
                | some placement =>
                    cases positionsEq :
                        fourCoordinateConfigurationPositions? frame observation placement with
                    | none =>
                        simp [frameEq, observationEq, priorityEq, placementEq, positionsEq] at produced
                    | some positions =>
                        refine ⟨frame, observation, priorities, placement, positions,
                          rfl,
                          (FourCoordinateSpatialPerception.observe?_eq_some_iff
                            frame observation).mp observationEq,
                          rfl, placementEq, positionsEq, ?_⟩
                        simpa [frameEq, observationEq, priorityEq, placementEq, positionsEq]
                          using produced
  · rintro ⟨frame, observation, priorities, placement, positions,
      frameEq, judgment, priorityEq, placementEq, positionsEq, produced⟩
    have observationEq : FourCoordinateSpatialPerception.observe? frame = some observation :=
      (FourCoordinateSpatialPerception.observe?_eq_some_iff frame observation).mpr judgment
    simp [ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?,
      IndexedFourCoordinateSpatialRoleObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, placementEq, positionsEq, produced]

/-- Exact refusal is the complement of the fully derived-record route. -/
theorem ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedFourCoordinateSpatialRoleObservation) :
    result.fourCoordinateSpatialRoleAssignment? spatial record = none ↔
      record.derivedRecord? result spatial = none ∨
        ∃ derived, record.derivedRecord? result spatial = some derived ∧
          result.fourCoordinateSpatialGeometryAssignment? spatial derived = none := by
  unfold ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?
  cases derivedEq : record.derivedRecord? result spatial with
  | none => simp
  | some derived =>
      cases producedEq : result.fourCoordinateSpatialGeometryAssignment? spatial derived <;>
        simp [producedEq]

/-! ## Exact final assignments after derived role selection -/

theorem finPairPositionValues_eraseDups_length
    (first second : Fin 4) (distinct : first ≠ second) :
    [first.val, second.val].eraseDups.length = 2 := by
  fin_cases first <;> fin_cases second <;>
    simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop] at distinct ⊢

theorem fourPriorityPlacement_pair_lookups
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (first second : Fin 4) :
    [first.val, second.val].mapM
        (fun position => [priority0, priority1, priority2, priority3][position]?) =
      some
        [fourPriorityPlacement priority0 priority1 priority2 priority3 first,
          fourPriorityPlacement priority0 priority1 priority2 priority3 second] := by
  rw [List.mapM_cons, fourPriorityPlacement_lookup, List.mapM_cons,
    fourPriorityPlacement_lookup]
  rfl

theorem ChemistryNormalizationResult.fourCoordinateSpatialRole_squarePlanar_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (senior trans : Fin 4)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (coplanar : frame.AllFiveCoplanar)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .squarePlanar ligands =
      some [priority0, priority1, priority2, priority3])
    (seniority : IsStrictSenior
      (fourPriorityPlacement priority0 priority1 priority2 priority3) senior)
    (opposite : IsOppositePair frame senior trans)
    (unique : ∀ other, IsOppositePair frame senior other → other = trans) :
    result.fourCoordinateSpatialRoleAssignment? spatial
        { center := center
          geometry := .squarePlanar
          ligands := ligands
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePlanar
              configurationIndex :=
                [[fourPriorityPlacement priority0 priority1 priority2 priority3 trans]]
              absolute? := none } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .allFiveCoplanar :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame .allFiveCoplanar).mpr
      (.allFiveCoplanar coplanar)
  have transEq : transToStrictSeniorPosition? frame
      (fourPriorityPlacement priority0 priority1 priority2 priority3) = some trans :=
    (transToStrictSeniorPosition?_eq_some_iff frame
      (fourPriorityPlacement priority0 priority1 priority2 priority3) trans).mpr
        ⟨senior, seniority, opposite, unique⟩
  have derivedEq :
      ({ center := center
         geometry := PolyhedralGeometry.squarePlanar
         ligands := ligands
         absoluteOrientation := RedBookIR9.AbsoluteOrientationObservation.none } :
        IndexedFourCoordinateSpatialRoleObservation).derivedRecord? result spatial =
      some
        { center := center
          geometry := .squarePlanar
          ligands := ligands
          configurationPositions := .squarePlanar trans.val
          absoluteOrientation := .none } := by
    simp [IndexedFourCoordinateSpatialRoleObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, fourCoordinateConfigurationPositions?, transEq,
      IndexedFourCoordinateSpatialRoleObservation.withDerivedPositions]
  have downstream := result.fourCoordinateSpatial_squarePlanar_exact spatial center ligands frame
    [priority0, priority1, priority2, priority3] trans.val
    (fourPriorityPlacement priority0 priority1 priority2 priority3 trans)
    frameEq coplanar priorityEq
    (fourPriorityPlacement_lookup priority0 priority1 priority2 priority3 trans)
  simpa [ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?, derivedEq]
    using downstream

theorem ChemistryNormalizationResult.fourCoordinateSpatialRole_squarePyramid4_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame) (sense : PolyhedralRotationSense)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (senior trans : Fin 4)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (displaced : frame.DonorsCoplanarCenterDisplaced)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .squarePyramid4 ligands =
      some [priority0, priority1, priority2, priority3])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3].eraseDups.length = 4)
    (seniority : IsStrictSenior
      (fourPriorityPlacement priority0 priority1 priority2 priority3) senior)
    (opposite : IsOppositePair frame senior trans)
    (unique : ∀ other, IsOppositePair frame senior other → other = trans) :
    result.fourCoordinateSpatialRoleAssignment? spatial
        { center := center
          geometry := .squarePyramid4
          ligands := ligands
          absoluteOrientation := .squarePyramid4AC
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePyramid4
              configurationIndex :=
                [[fourPriorityPlacement priority0 priority1 priority2 priority3 trans]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsCoplanarCenterDisplaced :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame
      .donorsCoplanarCenterDisplaced).mpr (.donorsCoplanarCenterDisplaced displaced)
  have transEq : transToStrictSeniorPosition? frame
      (fourPriorityPlacement priority0 priority1 priority2 priority3) = some trans :=
    (transToStrictSeniorPosition?_eq_some_iff frame
      (fourPriorityPlacement priority0 priority1 priority2 priority3) trans).mpr
        ⟨senior, seniority, opposite, unique⟩
  have derivedEq :
      ({ center := center
         geometry := PolyhedralGeometry.squarePyramid4
         ligands := ligands
         absoluteOrientation :=
           RedBookIR9.AbsoluteOrientationObservation.squarePyramid4AC
             (BlueBookP93.rotationOfProduction sense) } :
        IndexedFourCoordinateSpatialRoleObservation).derivedRecord? result spatial =
      some
        { center := center
          geometry := .squarePyramid4
          ligands := ligands
          configurationPositions := .squarePyramid4 trans.val
          absoluteOrientation := .squarePyramid4AC
            (BlueBookP93.rotationOfProduction sense) } := by
    simp [IndexedFourCoordinateSpatialRoleObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, fourCoordinateConfigurationPositions?, transEq,
      IndexedFourCoordinateSpatialRoleObservation.withDerivedPositions]
  have downstream := result.fourCoordinateSpatial_squarePyramid4_exact spatial center ligands
    frame sense [priority0, priority1, priority2, priority3] trans.val
    (fourPriorityPlacement priority0 priority1 priority2 priority3 trans)
    frameEq displaced priorityEq prioritiesDistinct
    (fourPriorityPlacement_lookup priority0 priority1 priority2 priority3 trans)
  simpa [ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?, derivedEq]
    using downstream

theorem ChemistryNormalizationResult.fourCoordinateSpatialRole_tetrahedron_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (inside : frame.CenterStrictlyInside)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .tetrahedron ligands =
      some [priority0, priority1, priority2, priority3]) :
    result.fourCoordinateSpatialRoleAssignment? spatial
        { center := center
          geometry := .tetrahedron
          ligands := ligands
          absoluteOrientation := .none } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .tetrahedron
              configurationIndex := []
              absolute? := none } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsNoncoplanarCenterInsideDonorPolyhedron :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame
      .donorsNoncoplanarCenterInsideDonorPolyhedron).mpr
        (.donorsNoncoplanarCenterInside
          (FourCoordinateSpatialPerception.Frame.centerStrictlyInside_donorVolume_ne inside)
          inside)
  have derivedEq :
      ({ center := center
         geometry := PolyhedralGeometry.tetrahedron
         ligands := ligands
         absoluteOrientation := RedBookIR9.AbsoluteOrientationObservation.none } :
        IndexedFourCoordinateSpatialRoleObservation).derivedRecord? result spatial =
      some
        { center := center
          geometry := .tetrahedron
          ligands := ligands
          configurationPositions := .noDistinguishedPositions
          absoluteOrientation := .none } := by
    simp [IndexedFourCoordinateSpatialRoleObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, fourCoordinateConfigurationPositions?,
      IndexedFourCoordinateSpatialRoleObservation.withDerivedPositions]
  have downstream := result.fourCoordinateSpatial_tetrahedron_exact spatial center ligands frame
    [priority0, priority1, priority2, priority3] frameEq inside priorityEq
  simpa [ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?, derivedEq]
    using downstream

theorem ChemistryNormalizationResult.fourCoordinateSpatialRole_seeSaw_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat)
    (frame : FourCoordinateSpatialPerception.Frame) (sense : PolyhedralRotationSense)
    (priority0 priority1 priority2 priority3 : PolyhedralPriorityNumber)
    (pair : Fin 4 × Fin 4)
    (frameEq : spatial.fourCoordinateFrame? center ligands = some frame)
    (outside : frame.CenterStrictlyOutside)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .seeSaw ligands =
      some [priority0, priority1, priority2, priority3])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3].eraseDups.length = 4)
    (pairMember : pair ∈ unorderedPairs)
    (opposite : IsCenterAntiparallelPair frame pair.1 pair.2)
    (unique : ∀ other ∈ unorderedPairs,
      IsCenterAntiparallelPair frame other.1 other.2 → other = pair) :
    result.fourCoordinateSpatialRoleAssignment? spatial
        { center := center
          geometry := .seeSaw
          ligands := ligands
          absoluteOrientation := .seeSawAC (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .seeSaw
              configurationIndex :=
                [seeSawConfigurationIndex
                  (fourPriorityPlacement priority0 priority1 priority2 priority3 pair.1)
                  (fourPriorityPlacement priority0 priority1 priority2 priority3 pair.2)]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have observationEq : FourCoordinateSpatialPerception.observe? frame =
      some .donorsNoncoplanarCenterOutsideDonorPolyhedron :=
    (FourCoordinateSpatialPerception.observe?_eq_some_iff frame
      .donorsNoncoplanarCenterOutsideDonorPolyhedron).mpr
        (.donorsNoncoplanarCenterOutside outside)
  have pairEq : uniqueCenterAntiparallelPair? frame = some pair :=
    (uniqueCenterAntiparallelPair?_eq_some_iff frame pair).mpr
      ⟨pairMember, opposite, unique⟩
  have derivedEq :
      ({ center := center
         geometry := PolyhedralGeometry.seeSaw
         ligands := ligands
         absoluteOrientation := RedBookIR9.AbsoluteOrientationObservation.seeSawAC
           (BlueBookP93.rotationOfProduction sense) } :
        IndexedFourCoordinateSpatialRoleObservation).derivedRecord? result spatial =
      some
        { center := center
          geometry := .seeSaw
          ligands := ligands
          configurationPositions := .seeSaw pair.1.val pair.2.val
          absoluteOrientation := .seeSawAC (BlueBookP93.rotationOfProduction sense) } := by
    simp [IndexedFourCoordinateSpatialRoleObservation.derivedRecord?, frameEq, observationEq,
      priorityEq, fourCoordinateConfigurationPositions?, pairEq,
      IndexedFourCoordinateSpatialRoleObservation.withDerivedPositions]
  have positionsDistinct :=
    finPairPositionValues_eraseDups_length pair.1 pair.2 opposite.1
  have lookups := fourPriorityPlacement_pair_lookups
    priority0 priority1 priority2 priority3 pair.1 pair.2
  have downstream := result.fourCoordinateSpatial_seeSaw_exact spatial center ligands frame sense
    [priority0, priority1, priority2, priority3] pair.1.val pair.2.val
    (fourPriorityPlacement priority0 priority1 priority2 priority3 pair.1)
    (fourPriorityPlacement priority0 priority1 priority2 priority3 pair.2)
    frameEq outside priorityEq prioritiesDistinct positionsDistinct lookups
  simpa [ChemistryNormalizationResult.fourCoordinateSpatialRoleAssignment?, derivedEq]
    using downstream

end TetraStereo.OneCenter
