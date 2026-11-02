import TetraStereo.OneCenter.P94CoordinateRingWitnessDiscovery
import TetraStereo.OneCenter.P94ExecutableRingApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.PracticalCrownSelection

open CoordinateRing

/-!
# Practical executable general-crown selection

This detector does not assume that the one-step ring rotation is a spatial isometry.  It
enumerates complete finite molecular permutations, retains exactly those that preserve atom and
bond constitution, induce a cyclic-adjacency-preserving action on the selected ring, and preserve
the complete exact distance matrix, then requires those retained actions to act transitively.
This admits multi-generator crowns such as the rational cube-vertex example, where no order-eight
Euclidean rotation is needed.
-/

private def zeroPoint : CartesianPoint3 := { x := 0, y := 0, z := 0 }

def parityPoints (points : List CartesianPoint3) (evenParity : Bool) :
    List CartesianPoint3 :=
  points.zipIdx.filterMap fun indexed =>
    if decide (Even indexed.2) == evenParity then some indexed.1 else none

def alternatingNormalCandidates (points : List CartesianPoint3) : List RationalVector3 :=
  ((candidatePlanes (parityPoints points true)).map ExactPlane.normal ++
    (candidatePlanes (parityPoints points false)).map ExactPlane.normal).eraseDups

def normalAlternates? (points : List CartesianPoint3) (normal : RationalVector3) : Bool :=
  match points[0]?, points[1]? with
  | some evenPoint, some oddPoint =>
      let evenLevel := pointProjection normal evenPoint
      let oddLevel := pointProjection normal oddPoint
      decide (0 < RationalVector3.dot normal normal) &&
        decide (evenLevel ≠ oddLevel) &&
        points.zipIdx.all fun indexed =>
          if decide (Even indexed.2) then
            decide (pointProjection normal indexed.1 = evenLevel)
          else
            decide (pointProjection normal indexed.1 = oddLevel)
  | _, _ => false

def PracticalAlternatingParallelPlanes (points : List CartesianPoint3) : Prop :=
  points.Nodup ∧
    ∃ normal ∈ alternatingNormalCandidates points, normalAlternates? points normal = true

def practicalAlternatingParallelPlanes? (points : List CartesianPoint3) : Bool :=
  decide points.Nodup &&
    (alternatingNormalCandidates points).any (normalAlternates? points)

@[simp] theorem practicalAlternatingParallelPlanes?_eq_true_iff
    (points : List CartesianPoint3) :
    practicalAlternatingParallelPlanes? points = true ↔
      PracticalAlternatingParallelPlanes points := by
  simp [practicalAlternatingParallelPlanes?, PracticalAlternatingParallelPlanes]

def cyclicActionCandidates (count : Nat) : List (List Nat) :=
  if count = 0 then [] else
    ((List.range count).map fun offset =>
      (List.range count).map fun index => (index + offset) % count) ++
    ((List.range count).map fun offset =>
      (List.range count).map fun index => (offset + count - index) % count)

def ringActionSeed (unit : P94ConformationUnit) (action : List Nat) :
    List (Nat × Nat) :=
  unit.atoms.zip (action.map fun targetIndex => unit.atoms.getD targetIndex 0)

def ringActionConstitutionallyAccepted? (molecule : RawMolecule)
    (unit : P94ConformationUnit) (action : List Nat) : Bool :=
  let vertices := List.range molecule.atomCount
  let seed := ringActionSeed unit action
  let seedValid := seed.all fun pair =>
    molecule.sameConstitutionAtom pair.1 pair.2 &&
      molecule.constitutionMappingConsistent molecule.localizedMancudeEdges
        (seed.erase pair) pair.1 pair.2
  let remaining := vertices.filter fun atom => !(seed.map Prod.fst).contains atom
  decide (action.Perm (List.range unit.atoms.length)) && seedValid &&
    molecule.searchConstitutionAutomorphismExact molecule.localizedMancudeEdges
      vertices remaining seed

def cyclicallyAdjacentIndex? (count left right : Nat) : Bool :=
  count != 0 && (((left + 1) % count == right) || ((right + 1) % count == left))

def preservesCyclicAdjacency? (count : Nat) (action : List Nat) : Bool :=
  decide (action.Perm (List.range count)) &&
    (List.range count).all fun left =>
      (List.range count).all fun right =>
        decide (cyclicallyAdjacentIndex? count left right =
          cyclicallyAdjacentIndex? count (action.getD left 0) (action.getD right 0))

def preservesCrownMetric? (points : List CartesianPoint3) (action : List Nat) : Bool :=
  decide (action.Perm (List.range points.length)) &&
    (List.range points.length).all fun left =>
      (List.range points.length).all fun right =>
        decide (crownSquaredDistance (points.getD left zeroPoint) (points.getD right zeroPoint) =
          crownSquaredDistance
            (points.getD (action.getD left 0) zeroPoint)
            (points.getD (action.getD right 0) zeroPoint))

def acceptedCrownActions (molecule : RawMolecule) (unit : P94ConformationUnit)
    (points : List CartesianPoint3) : List (List Nat) :=
  ((cyclicActionCandidates unit.atoms.length).filter fun action =>
    preservesCyclicAdjacency? unit.atoms.length action &&
      preservesCrownMetric? points action &&
      ringActionConstitutionallyAccepted? molecule unit action).eraseDups

def PracticalGeneralCrownSymmetry (molecule : RawMolecule)
    (unit : P94ConformationUnit) (points : List CartesianPoint3) : Prop :=
  let actions := acceptedCrownActions molecule unit points
  actions ≠ [] ∧
    (List.range unit.atoms.length).all (fun source =>
      (List.range unit.atoms.length).all fun target =>
        actions.any fun action => action.getD source 0 == target) = true

def practicalGeneralCrownSymmetry? (molecule : RawMolecule)
    (unit : P94ConformationUnit) (points : List CartesianPoint3) : Bool :=
  let actions := acceptedCrownActions molecule unit points
  !actions.isEmpty &&
    (List.range unit.atoms.length).all (fun source =>
      (List.range unit.atoms.length).all fun target =>
        actions.any fun action => action.getD source 0 == target)

@[simp] theorem practicalGeneralCrownSymmetry?_eq_true_iff
    (molecule : RawMolecule) (unit : P94ConformationUnit)
    (points : List CartesianPoint3) :
    practicalGeneralCrownSymmetry? molecule unit points = true ↔
      PracticalGeneralCrownSymmetry molecule unit points := by
  simp [practicalGeneralCrownSymmetry?, PracticalGeneralCrownSymmetry]

def crownCarrier? (molecule : RawMolecule) (unit : P94ConformationUnit) : Bool :=
  decide (unit.kind = .crownRing) && unit.ringValidFor? molecule &&
    unit.saturatedCyclic? molecule

@[simp] theorem crownCarrier?_eq_true_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) :
    crownCarrier? molecule unit = true ↔
      unit.kind = .crownRing ∧ unit.ValidFor molecule ∧
        unit.SaturatedCyclic molecule := by
  by_cases kind : unit.kind = .crownRing
  · simp [crownCarrier?, kind, P94ConformationUnit.SupportedCoordinateRingKind]
  · simp [crownCarrier?, kind]

structure SelectedCrown where
  points : List CartesianPoint3
  sides : List PlaneSide
  deriving DecidableEq, Repr

def PracticalCrownSelectionJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedCrown) : Prop :=
  unit.kind = .crownRing ∧ unit.ValidFor molecule ∧
    unit.SaturatedCyclic molecule ∧
    ∃ points,
      SpatialPointsAt spatial unit.atoms points ∧
      PracticalAlternatingParallelPlanes points ∧
      PracticalGeneralCrownSymmetry molecule unit points ∧
      output = { points := points, sides := canonicalCrownSides points }

def automaticCrownSelection? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) : Option SelectedCrown :=
  if crownCarrier? molecule unit then do
    let points ← spatialPointsAt? spatial unit.atoms
    if practicalAlternatingParallelPlanes? points &&
        practicalGeneralCrownSymmetry? molecule unit points then
      some { points := points, sides := canonicalCrownSides points }
    else none
  else none

theorem automaticCrownSelection?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (output : SelectedCrown) :
    automaticCrownSelection? molecule spatial unit = some output ↔
      PracticalCrownSelectionJudgment molecule spatial unit output := by
  by_cases carrier : crownCarrier? molecule unit = true
  · have carrierMeaning := (crownCarrier?_eq_true_iff molecule unit).mp carrier
    cases pointsComputed : spatialPointsAt? spatial unit.atoms with
    | none =>
        constructor
        · simp [automaticCrownSelection?, carrier, pointsComputed]
        · rintro ⟨_, _, _, points, pointsJudged, _⟩
          have someComputed := (spatialPointsAt?_eq_some_iff spatial unit.atoms points).mpr
            pointsJudged
          rw [pointsComputed] at someComputed
          contradiction
    | some points =>
        by_cases alternating : practicalAlternatingParallelPlanes? points = true
        · by_cases symmetry : practicalGeneralCrownSymmetry? molecule unit points = true
          · constructor
            · intro computed
              have outputEqual : SelectedCrown.mk points (canonicalCrownSides points) = output := by
                simpa [automaticCrownSelection?, carrier, pointsComputed,
                  alternating, symmetry] using computed
              exact ⟨carrierMeaning.1, carrierMeaning.2.1, carrierMeaning.2.2,
                points, (spatialPointsAt?_eq_some_iff spatial unit.atoms points).mp pointsComputed,
                (practicalAlternatingParallelPlanes?_eq_true_iff points).mp alternating,
                (practicalGeneralCrownSymmetry?_eq_true_iff molecule unit points).mp symmetry,
                outputEqual.symm⟩
            · rintro ⟨_, _, _, otherPoints, otherPointsJudged, _, _, rfl⟩
              have otherComputed := (spatialPointsAt?_eq_some_iff
                spatial unit.atoms otherPoints).mpr otherPointsJudged
              rw [pointsComputed] at otherComputed
              have equal : points = otherPoints := Option.some.inj otherComputed
              subst otherPoints
              simp [automaticCrownSelection?, carrier, pointsComputed, alternating, symmetry]
          · have symmetryFalse := Bool.eq_false_of_not_eq_true symmetry
            constructor
            · simp [automaticCrownSelection?, carrier, pointsComputed,
                alternating, symmetryFalse]
            · rintro ⟨_, _, _, otherPoints, otherPointsJudged, _, otherSymmetry, _⟩
              have otherComputed := (spatialPointsAt?_eq_some_iff
                spatial unit.atoms otherPoints).mpr otherPointsJudged
              rw [pointsComputed] at otherComputed
              have equal : points = otherPoints := Option.some.inj otherComputed
              subst otherPoints
              exact False.elim (symmetry
                ((practicalGeneralCrownSymmetry?_eq_true_iff molecule unit points).mpr
                  otherSymmetry))
        · have alternatingFalse := Bool.eq_false_of_not_eq_true alternating
          constructor
          · simp [automaticCrownSelection?, carrier, pointsComputed, alternatingFalse]
          · rintro ⟨_, _, _, otherPoints, otherPointsJudged, otherAlternating, _⟩
            have otherComputed := (spatialPointsAt?_eq_some_iff
              spatial unit.atoms otherPoints).mpr otherPointsJudged
            rw [pointsComputed] at otherComputed
            have equal : points = otherPoints := Option.some.inj otherComputed
            subst otherPoints
            exact False.elim (alternating
              ((practicalAlternatingParallelPlanes?_eq_true_iff points).mpr otherAlternating))
  · have carrierFalse := Bool.eq_false_of_not_eq_true carrier
    constructor
    · simp [automaticCrownSelection?, carrierFalse]
    · rintro ⟨kind, valid, saturated, _⟩
      exact False.elim (carrier ((crownCarrier?_eq_true_iff molecule unit).mpr
        ⟨kind, valid, saturated⟩))

theorem automaticCrownSelection?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    automaticCrownSelection? molecule spatial unit = none ↔
      ¬∃ output, PracticalCrownSelectionJudgment molecule spatial unit output := by
  constructor
  · intro computed ⟨output, judged⟩
    have someComputed := (automaticCrownSelection?_eq_some_iff
      molecule spatial unit output).mpr judged
    rw [computed] at someComputed
    contradiction
  · intro absent
    cases computed : automaticCrownSelection? molecule spatial unit with
    | none => rfl
    | some output =>
        exact False.elim (absent ⟨output,
          (automaticCrownSelection?_eq_some_iff molecule spatial unit output).mp computed⟩)

def SelectedCrown.toEvidence (molecule : RawMolecule) (unit : P94ConformationUnit)
    (selected : SelectedCrown) : P94ConformationEvidence Unit Unit :=
  .ringPlane
    { unit := unit
      sides := selected.sides
      saturatedCyclic := unit.SaturatedCyclic molecule
      symmetricallyEquivalent := PracticalGeneralCrownSymmetry molecule unit selected.points }

theorem crownSelectionJudgment_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (selected : SelectedCrown)
    (judged : PracticalCrownSelectionJudgment molecule spatial unit selected) :
    IndependentP94ConformationAssignment molecule [selected.toEvidence molecule unit]
      { unit := unit, descriptor := .crown } := by
  rcases judged with ⟨kind, valid, saturated, points, pointsJudged,
    alternating, symmetry, rfl⟩
  refine ⟨(SelectedCrown.toEvidence molecule unit
      (SelectedCrown.mk points (canonicalCrownSides points)) :
      P94ConformationEvidence Unit Unit), by simp, rfl, valid, ?_, ?_⟩
  · simpa [SelectedCrown.toEvidence, P94ConformationEvidence.MolecularRolesValid,
      kind] using saturated
  · refine ⟨kind, ?_, saturated, ?_⟩
    · simpa using pointsJudged.length_eq
    · have crownValid := valid
      unfold P94ConformationUnit.ValidFor at crownValid
      rw [kind] at crownValid
      refine ⟨?_, ?_, canonicalCrownSides_alternating points, symmetry⟩
      · simpa [canonicalCrownSides, pointsJudged.length_eq] using crownValid.2.2.2.1
      · simpa [canonicalCrownSides, pointsJudged.length_eq] using crownValid.2.2.2.2.1

def automaticCrownAssignment? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option P94ConformationAssignment :=
  (automaticCrownSelection? molecule spatial unit).map fun _ =>
    { unit := unit, descriptor := .crown }

theorem automaticCrownAssignment?_some_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment)
    (computed : automaticCrownAssignment? molecule spatial unit = some assignment) :
    ∃ evidence : P94ConformationEvidence Unit Unit,
      IndependentP94ConformationAssignment molecule [evidence] assignment := by
  cases selectedComputed : automaticCrownSelection? molecule spatial unit with
  | none => simp [automaticCrownAssignment?, selectedComputed] at computed
  | some selected =>
      have assignmentEqual :
          ({ unit := unit, descriptor := .crown } : P94ConformationAssignment) = assignment := by
        simpa [automaticCrownAssignment?, selectedComputed] using computed
      refine ⟨selected.toEvidence molecule unit, ?_⟩
      rw [← assignmentEqual]
      exact crownSelectionJudgment_independent molecule spatial unit selected
        ((automaticCrownSelection?_eq_some_iff molecule spatial unit selected).mp
          selectedComputed)

end BlueBookP94.PracticalCrownSelection

end TetraStereo.OneCenter
