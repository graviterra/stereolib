import TetraStereo.OneCenter.P94MolecularAtomInOutObservationScheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularLonePairInOutObservationScheduler

open CoordinateTwistInOut
open P94MolecularRequestScheduler
open P94MolecularBicyclicFramework
open P94MolecularLonePair
open P94MolecularBridgeheadAxisInterior
open P94MolecularAtomInOutObservationScheduler

/-!
# Exhaustive supplied lone-pair observations for P-94.3.2.6

Nuclear coordinates do not determine a lone pair's virtual 3D position.  The honest finite input
is therefore a list pairing each supplied spatial configuration with a virtual-point ledger.  Once
that evidence is supplied, no observation template selection remains: every compatible theta
framework and both oriented bridgehead axes can be enumerated, and the opposite endpoint supplies
the inward reference coordinate.

This module also appends those observations to the automatically generated physical-atom ledger
and schedules every ordered pair.  A coverage theorem proves that every accepted observation
represented by either finite ledger occurs.  The result validates and schedules virtual geometry;
it does not infer electron-pair positions from nuclear coordinates.
-/

structure LonePairGeometryState where
  spatial : SpatialConfiguration
  virtualPoints : CoordinateTorsion.VirtualTorsionPointLedger
  deriving DecidableEq, Repr

def lonePairObservation (framework : ThetaFramework) (state : LonePairGeometryState)
    (bridgehead : ℕ) (interior : CartesianPoint3) :
    CoordinateInOutObservation ThetaFramework :=
  { framework := framework
    spatial := state.spatial
    virtualPoints := state.virtualPoints
    bridgehead := bridgehead
    directedParticipant := .lonePair bridgehead
    interior := interior }

/-- At one oriented theta axis, a supplied virtual-geometry state determines exactly one canonical
lone-pair observation whenever the opposite endpoint has a nuclear coordinate. -/
def lonePairObservationsForAxis (framework : ThetaFramework) (state : LonePairGeometryState)
    (axis : ℕ × ℕ) : List (CoordinateInOutObservation ThetaFramework) :=
  match state.spatial.positions[axis.2]? with
  | none => []
  | some interior => [lonePairObservation framework state axis.1 interior]

theorem mem_lonePairObservationsForAxis_iff (framework : ThetaFramework)
    (state : LonePairGeometryState) (axis : ℕ × ℕ)
    (observation : CoordinateInOutObservation ThetaFramework) :
    observation ∈ lonePairObservationsForAxis framework state axis ↔
      ∃ interior,
        CoordinateRing.SpatialPointAt state.spatial axis.2 interior ∧
          lonePairObservation framework state axis.1 interior = observation := by
  unfold lonePairObservationsForAxis
  cases coordinate : state.spatial.positions[axis.2]? with
  | none =>
      simp [CoordinateRing.SpatialPointAt, coordinate]
  | some interior =>
      simp [CoordinateRing.SpatialPointAt, coordinate, eq_comm]

noncomputable def scheduledLonePairInOutObservations (molecule : RawMolecule)
    (unit : P94ConformationUnit) (states : List LonePairGeometryState) :
    List (CoordinateInOutObservation ThetaFramework) :=
  (thetaFrameworksForUnit molecule unit).toList.flatMap fun framework =>
    states.flatMap fun state =>
      (bridgeheadAxes framework).flatMap fun axis =>
        lonePairObservationsForAxis framework state axis

theorem mem_scheduledLonePairInOutObservations_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (states : List LonePairGeometryState)
    (observation : CoordinateInOutObservation ThetaFramework) :
    observation ∈ scheduledLonePairInOutObservations molecule unit states ↔
      ∃ framework, framework.ValidFor molecule unit ∧
        ∃ state ∈ states,
          ∃ axis : ℕ × ℕ,
            OppositeBridgehead framework axis.1 axis.2 ∧
              ∃ interior,
                CoordinateRing.SpatialPointAt state.spatial axis.2 interior ∧
                  lonePairObservation framework state axis.1 interior = observation := by
  simp only [scheduledLonePairInOutObservations, List.mem_flatMap, Finset.mem_toList,
    mem_thetaFrameworksForUnit_iff, mem_bridgeheadAxes_iff,
    mem_lonePairObservationsForAxis_iff]

/-- Every accepted lone-pair observation whose exact spatial/virtual ledger pair was supplied is
generated at its graph-derived framework and oriented bridgehead axis. -/
theorem acceptedLonePairObservation_mem_scheduled
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (unit : P94ConformationUnit) (states : List LonePairGeometryState)
    (observation : CoordinateInOutObservation ThetaFramework) (center : ℕ)
    (direction : BridgeheadDirection)
    (lonePairParticipant : observation.directedParticipant = .lonePair center)
    (statePresent :
      ({ spatial := observation.spatial, virtualPoints := observation.virtualPoints } :
        LonePairGeometryState) ∈ states)
    (judged : CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule unit observation direction) :
    observation ∈ scheduledLonePairInOutObservations molecule unit states := by
  have axisFacts := coordinateDirectionJudgment_uses_oppositeBridgeheadAxis
    molecule ledger unit observation direction judged
  rcases axisFacts with
    ⟨_virtualValid, frameworkValid, _actualBridgehead,
      other, _bridgeheadPoint, _participantPoint,
      opposite, otherAt, _bridgeheadAt, _participantAt, _sign⟩
  have chemical := judged.2.2.1
  rw [lonePairParticipant] at chemical
  rcases chemical with
    ⟨_bridgeheadInUnit, _bridgeheadCertified, _bridgeheadBounded,
      centerIdentity, _certifiedLonePair⟩
  subst center
  let state : LonePairGeometryState :=
    { spatial := observation.spatial, virtualPoints := observation.virtualPoints }
  have stateIn : state ∈ states := by
    exact statePresent
  have observationIdentity :
      lonePairObservation observation.framework state
        observation.bridgehead observation.interior = observation := by
    cases observation
    simp_all [state, lonePairObservation]
  apply (mem_scheduledLonePairInOutObservations_iff
    molecule unit states observation).mpr
  exact ⟨observation.framework, frameworkValid,
    state, stateIn, (observation.bridgehead, other), opposite,
    observation.interior, otherAt, observationIdentity⟩

/-! ## Combined atom and lone-pair coverage -/

def ObservationCoveredByFiniteLedgers
    (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState)
    (observation : CoordinateInOutObservation ThetaFramework) : Prop :=
  (∃ atom,
      observation.directedParticipant = .atom atom ∧
      observation.virtualPoints = [] ∧
      observation.spatial ∈ atomSpatialStates) ∨
    (∃ center,
      observation.directedParticipant = .lonePair center ∧
      ({ spatial := observation.spatial, virtualPoints := observation.virtualPoints } :
        LonePairGeometryState) ∈ lonePairStates)

noncomputable def scheduledCompleteInOutObservations (molecule : RawMolecule)
    (unit : P94ConformationUnit) (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState) :
    List (CoordinateInOutObservation ThetaFramework) :=
  scheduledAtomInOutObservations molecule unit atomSpatialStates ++
    scheduledLonePairInOutObservations molecule unit lonePairStates

theorem mem_scheduledCompleteInOutObservations_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState)
    (observation : CoordinateInOutObservation ThetaFramework) :
    observation ∈ scheduledCompleteInOutObservations molecule unit
        atomSpatialStates lonePairStates ↔
      observation ∈ scheduledAtomInOutObservations molecule unit atomSpatialStates ∨
        observation ∈ scheduledLonePairInOutObservations molecule unit lonePairStates := by
  simp [scheduledCompleteInOutObservations]

/-- Participant coverage by either finite ledger is enough to guarantee scheduling of every
accepted observation.  Duplicate-atom phantoms are absent because P-94.3.2.6 admits only an
exocyclic atom or a lone pair. -/
theorem acceptedCoveredObservation_mem_scheduled
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (unit : P94ConformationUnit) (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState)
    (observation : CoordinateInOutObservation ThetaFramework)
    (direction : BridgeheadDirection)
    (covered : ObservationCoveredByFiniteLedgers
      atomSpatialStates lonePairStates observation)
    (judged : CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule unit observation direction) :
    observation ∈ scheduledCompleteInOutObservations molecule unit
      atomSpatialStates lonePairStates := by
  apply (mem_scheduledCompleteInOutObservations_iff
    molecule unit atomSpatialStates lonePairStates observation).mpr
  rcases covered with atomCovered | lonePairCovered
  · rcases atomCovered with ⟨atom, participant, canonical, spatialPresent⟩
    exact Or.inl (acceptedCanonicalAtomObservation_mem_scheduled
      molecule ledger unit atomSpatialStates observation atom direction
      canonical participant spatialPresent judged)
  · rcases lonePairCovered with ⟨center, participant, statePresent⟩
    exact Or.inr (acceptedLonePairObservation_mem_scheduled
      molecule ledger unit lonePairStates observation center direction
      participant statePresent judged)

noncomputable def scheduledCompleteInOutLedger (molecule : RawMolecule)
    (unit : P94ConformationUnit) (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState) : CoordinateInOutLedger ThetaFramework :=
  { unit := unit
    observations := scheduledCompleteInOutObservations molecule unit
      atomSpatialStates lonePairStates }

noncomputable def scheduledCompleteInOutInputs (molecule : RawMolecule)
    (unit : P94ConformationUnit) (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState) :
    List (CoordinateInOutInput ThetaFramework) :=
  scheduledCoordinateInOutInputs
    (scheduledCompleteInOutLedger molecule unit atomSpatialStates lonePairStates)

theorem mem_scheduledCompleteInOutInputs_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState)
    (input : CoordinateInOutInput ThetaFramework) :
    input ∈ scheduledCompleteInOutInputs molecule unit atomSpatialStates lonePairStates ↔
      ∃ first ∈ scheduledCompleteInOutObservations molecule unit
          atomSpatialStates lonePairStates,
        ∃ second ∈ scheduledCompleteInOutObservations molecule unit
            atomSpatialStates lonePairStates,
          ({ unit := unit, first := first, second := second } :
            CoordinateInOutInput ThetaFramework) = input := by
  exact mem_scheduledCoordinateInOutInputs_iff
    (scheduledCompleteInOutLedger molecule unit atomSpatialStates lonePairStates) input

end BlueBookP94.P94MolecularLonePairInOutObservationScheduler
end TetraStereo.OneCenter
