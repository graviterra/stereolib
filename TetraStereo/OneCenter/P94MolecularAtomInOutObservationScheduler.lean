import TetraStereo.OneCenter.P94MolecularBridgeheadAxisInterior

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularAtomInOutObservationScheduler

open CoordinateTwistInOut
open P94MolecularRequestScheduler
open P94MolecularBicyclicFramework
open P94MolecularLonePair
open P94MolecularBridgeheadAxisInterior

/-!
# Exhaustive molecular atom observations for P-94.3.2.6

For an ordinary exocyclic atom, every field of a canonical in/out observation is already finite
data: a graph-derived theta framework, one of its two bridgehead orientations, one supplied exact
spatial configuration, and one bounded raw atom.  The opposite theta endpoint supplies the axis
reference coordinate, and atom participants need no virtual-point entry.

This module enumerates that entire product and then applies the existing all-ordered-pairs
scheduler.  Chemically irrelevant combinations are harmless finite requests and are refused by
the independent judgment.  Conversely, every accepted canonical atom observation over a supplied
spatial state is proved to occur.  Lone-pair observations remain separate because their virtual
3D points are genuine electronic geometry evidence rather than nuclear coordinates.
-/

/-! ## The two oriented bridgehead axes -/

def bridgeheadAxes (framework : ThetaFramework) : List (ℕ × ℕ) :=
  [(framework.firstBridgehead, framework.secondBridgehead),
    (framework.secondBridgehead, framework.firstBridgehead)]

theorem mem_bridgeheadAxes_iff (framework : ThetaFramework) (axis : ℕ × ℕ) :
    axis ∈ bridgeheadAxes framework ↔
      OppositeBridgehead framework axis.1 axis.2 := by
  rcases axis with ⟨bridgehead, other⟩
  simp [bridgeheadAxes, OppositeBridgehead, Prod.ext_iff]

/-! ## Every bounded atom at one axis and spatial state -/

def atomObservation (framework : ThetaFramework) (spatial : SpatialConfiguration)
    (bridgehead atom : ℕ) (interior : CartesianPoint3) :
    CoordinateInOutObservation ThetaFramework :=
  { framework := framework
    spatial := spatial
    virtualPoints := []
    bridgehead := bridgehead
    directedParticipant := .atom atom
    interior := interior }

/-- If the opposite endpoint has a coordinate, enumerate every bounded atom as a canonical
physical-participant observation at this oriented bridgehead axis. -/
def atomObservationsForAxis (molecule : RawMolecule) (framework : ThetaFramework)
    (spatial : SpatialConfiguration) (axis : ℕ × ℕ) :
    List (CoordinateInOutObservation ThetaFramework) :=
  match spatial.positions[axis.2]? with
  | none => []
  | some interior =>
      (List.range molecule.atomCount).map fun atom =>
        atomObservation framework spatial axis.1 atom interior

theorem mem_atomObservationsForAxis_iff (molecule : RawMolecule)
    (framework : ThetaFramework) (spatial : SpatialConfiguration) (axis : ℕ × ℕ)
    (observation : CoordinateInOutObservation ThetaFramework) :
    observation ∈ atomObservationsForAxis molecule framework spatial axis ↔
      ∃ atom, atom < molecule.atomCount ∧
        ∃ interior,
          CoordinateRing.SpatialPointAt spatial axis.2 interior ∧
            atomObservation framework spatial axis.1 atom interior = observation := by
  unfold atomObservationsForAxis
  cases coordinate : spatial.positions[axis.2]? with
  | none =>
      simp [CoordinateRing.SpatialPointAt, coordinate]
  | some interior =>
      simp [CoordinateRing.SpatialPointAt, coordinate]

/-! ## Every framework, state, axis, and atom -/

noncomputable def scheduledAtomInOutObservations (molecule : RawMolecule)
    (unit : P94ConformationUnit) (spatialStates : List SpatialConfiguration) :
    List (CoordinateInOutObservation ThetaFramework) :=
  (thetaFrameworksForUnit molecule unit).toList.flatMap fun framework =>
    spatialStates.flatMap fun spatial =>
      (bridgeheadAxes framework).flatMap fun axis =>
        atomObservationsForAxis molecule framework spatial axis

theorem mem_scheduledAtomInOutObservations_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (spatialStates : List SpatialConfiguration)
    (observation : CoordinateInOutObservation ThetaFramework) :
    observation ∈ scheduledAtomInOutObservations molecule unit spatialStates ↔
      ∃ framework, framework.ValidFor molecule unit ∧
        ∃ spatial ∈ spatialStates,
          ∃ axis : ℕ × ℕ,
            OppositeBridgehead framework axis.1 axis.2 ∧
              ∃ atom, atom < molecule.atomCount ∧
                ∃ interior,
                  CoordinateRing.SpatialPointAt spatial axis.2 interior ∧
                    atomObservation framework spatial axis.1 atom interior = observation := by
  simp only [scheduledAtomInOutObservations, List.mem_flatMap, Finset.mem_toList,
    mem_thetaFrameworksForUnit_iff, mem_bridgeheadAxes_iff,
    mem_atomObservationsForAxis_iff]

/-- Accepted atom observations use no virtual point.  Therefore every accepted canonical
observation whose spatial state is in the supplied finite ledger is one of the generated
observations; no caller-selected framework, bridgehead, participant atom, or interior point is
needed. -/
theorem acceptedCanonicalAtomObservation_mem_scheduled
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (unit : P94ConformationUnit) (spatialStates : List SpatialConfiguration)
    (observation : CoordinateInOutObservation ThetaFramework) (atom : ℕ)
    (direction : BridgeheadDirection)
    (canonicalVirtualPoints : observation.virtualPoints = [])
    (atomParticipant : observation.directedParticipant = .atom atom)
    (spatialPresent : observation.spatial ∈ spatialStates)
    (judged : CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule unit observation direction) :
    observation ∈ scheduledAtomInOutObservations molecule unit spatialStates := by
  have axisFacts := coordinateDirectionJudgment_uses_oppositeBridgeheadAxis
    molecule ledger unit observation direction judged
  rcases axisFacts with
    ⟨_virtualValid, frameworkValid, _actualBridgehead,
      other, _bridgeheadPoint, _participantPoint,
      opposite, otherAt, _bridgeheadAt, _participantAt, _sign⟩
  have chemical := judged.2.2.1
  rw [atomParticipant] at chemical
  rcases chemical with
    ⟨_bridgeheadInUnit, _bridgeheadCertified, _bridgeheadBounded, atomBounded,
      _atomOutsideUnit, _atomOutsideFramework, _bonded⟩
  have observationIdentity :
      atomObservation observation.framework observation.spatial
        observation.bridgehead atom observation.interior = observation := by
    cases observation
    simp_all [atomObservation]
  apply (mem_scheduledAtomInOutObservations_iff
    molecule unit spatialStates observation).mpr
  exact ⟨observation.framework, frameworkValid,
    observation.spatial, spatialPresent,
    (observation.bridgehead, other), opposite,
    atom, atomBounded, observation.interior, otherAt, observationIdentity⟩

/-! ## Every ordered pair of generated observations -/

noncomputable def scheduledAtomInOutLedger (molecule : RawMolecule)
    (unit : P94ConformationUnit) (spatialStates : List SpatialConfiguration) :
    CoordinateInOutLedger ThetaFramework :=
  { unit := unit
    observations := scheduledAtomInOutObservations molecule unit spatialStates }

noncomputable def scheduledAtomInOutInputs (molecule : RawMolecule)
    (unit : P94ConformationUnit) (spatialStates : List SpatialConfiguration) :
    List (CoordinateInOutInput ThetaFramework) :=
  scheduledCoordinateInOutInputs
    (scheduledAtomInOutLedger molecule unit spatialStates)

theorem mem_scheduledAtomInOutInputs_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (spatialStates : List SpatialConfiguration)
    (input : CoordinateInOutInput ThetaFramework) :
    input ∈ scheduledAtomInOutInputs molecule unit spatialStates ↔
      ∃ first ∈ scheduledAtomInOutObservations molecule unit spatialStates,
        ∃ second ∈ scheduledAtomInOutObservations molecule unit spatialStates,
          ({ unit := unit, first := first, second := second } :
            CoordinateInOutInput ThetaFramework) = input := by
  exact mem_scheduledCoordinateInOutInputs_iff
    (scheduledAtomInOutLedger molecule unit spatialStates) input

end BlueBookP94.P94MolecularAtomInOutObservationScheduler
end TetraStereo.OneCenter
