import TetraStereo.OneCenter.P94MolecularTwistInOutRequestScheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularDirectRotationEvidence

open P94MolecularRingCycleScheduler
open P94MolecularRequestScheduler

/-!
# Molecule-bound evidence for direct formally-single-bond rotation

P-94 defines conformational interconversion through rotations about formally single bonds, but two
static coordinate snapshots do not determine which bond was physically rotated.  This module
therefore retains an explicit finite assertion ledger while making its chemical obligations exact.

Every admitted state edge names a raw bond record in the same molecule.  That record must be a
normalized saturated single-bond spelling (`single`, `up`, or `down`) and an edge of the same valid
six-membered conformation carrier.  Both endpoint states are finite-ledger members with complete
molecule-sized coordinates and distinct configurations.  The resulting relation can be placed in
the existing exhaustive twist scheduler, and every scheduled use recovers these facts.
-/

structure MolecularDirectRotationAssertion (State : Type*) where
  first : State
  second : State
  bond : RawBond
  deriving DecidableEq

structure MolecularDirectRotationLedger (State : Type*) where
  unit : P94ConformationUnit
  states : List State
  spatialAt : State → SpatialConfiguration
  assertions : List (MolecularDirectRotationAssertion State)

def MolecularDirectRotationAssertion.ValidFor {State : Type*} [DecidableEq State]
    (assertion : MolecularDirectRotationAssertion State)
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) : Prop :=
  ledger.unit.kind = .sixMemberedRing ∧
    ledger.unit.ValidFor molecule ∧
    assertion.first ∈ ledger.states ∧
    assertion.second ∈ ledger.states ∧
    assertion.first ≠ assertion.second ∧
    ledger.spatialAt assertion.first ≠ ledger.spatialAt assertion.second ∧
    assertion.bond ∈ molecule.bonds ∧
    P94ConformationUnit.SaturatedSingleBondKind assertion.bond.kind ∧
    IsNamedCycleEdge ledger.unit.atoms assertion.bond.source assertion.bond.target ∧
    (ledger.spatialAt assertion.first).positions.length = molecule.atomCount ∧
    (ledger.spatialAt assertion.second).positions.length = molecule.atomCount

theorem molecularDirectRotationAssertion_validFor_iff
    {State : Type*} [DecidableEq State]
    (assertion : MolecularDirectRotationAssertion State)
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    assertion.ValidFor molecule ledger ↔
      ledger.unit.kind = .sixMemberedRing ∧
        ledger.unit.ValidFor molecule ∧
        assertion.first ∈ ledger.states ∧
        assertion.second ∈ ledger.states ∧
        assertion.first ≠ assertion.second ∧
        ledger.spatialAt assertion.first ≠ ledger.spatialAt assertion.second ∧
        assertion.bond ∈ molecule.bonds ∧
        P94ConformationUnit.SaturatedSingleBondKind assertion.bond.kind ∧
        IsNamedCycleEdge ledger.unit.atoms assertion.bond.source assertion.bond.target ∧
        (ledger.spatialAt assertion.first).positions.length = molecule.atomCount ∧
        (ledger.spatialAt assertion.second).positions.length = molecule.atomCount :=
  Iff.rfl

/-- Oriented authority relation.  The independent P-94 path layer takes its unoriented closure via
`DirectRotationStep`, so a finite ledger may choose either orientation for each physical edge. -/
def RotationAboutMolecularSingleBond {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State) : Prop :=
  ∃ assertion ∈ ledger.assertions,
    assertion.first = first ∧ assertion.second = second ∧ assertion.ValidFor molecule ledger

theorem rotationAboutMolecularSingleBond_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State) :
    RotationAboutMolecularSingleBond molecule ledger first second ↔
      ∃ assertion ∈ ledger.assertions,
        assertion.first = first ∧ assertion.second = second ∧
          assertion.ValidFor molecule ledger :=
  Iff.rfl

/-- Facts recovered from one admitted oriented state edge. -/
def MolecularSingleBondRotationSound {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State) : Prop :=
  ∃ bond,
    bond ∈ molecule.bonds ∧
      P94ConformationUnit.SaturatedSingleBondKind bond.kind ∧
      IsNamedCycleEdge ledger.unit.atoms bond.source bond.target ∧
      ledger.unit.kind = .sixMemberedRing ∧
      ledger.unit.ValidFor molecule ∧
      first ∈ ledger.states ∧ second ∈ ledger.states ∧
      first ≠ second ∧ ledger.spatialAt first ≠ ledger.spatialAt second ∧
      (ledger.spatialAt first).positions.length = molecule.atomCount ∧
      (ledger.spatialAt second).positions.length = molecule.atomCount

theorem rotationAboutMolecularSingleBond_sound
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State)
    (rotation : RotationAboutMolecularSingleBond molecule ledger first second) :
    MolecularSingleBondRotationSound molecule ledger first second := by
  rcases rotation with ⟨assertion, _assertionPresent, firstEq, secondEq, valid⟩
  subst first
  subst second
  rcases valid with
    ⟨kind, unitValid, firstPresent, secondPresent, stateDistinct, spatialDistinct,
      bondPresent, saturated, namedEdge, firstComplete, secondComplete⟩
  exact ⟨assertion.bond, bondPresent, saturated, namedEdge, kind, unitValid,
    firstPresent, secondPresent, stateDistinct, spatialDistinct, firstComplete, secondComplete⟩

private theorem molecularSingleBondRotationSound_symmetric
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    Symmetric (MolecularSingleBondRotationSound molecule ledger) := by
  intro first second sound
  rcases sound with
    ⟨bond, bondPresent, saturated, namedEdge, kind, unitValid,
      firstPresent, secondPresent, stateDistinct, spatialDistinct,
      firstComplete, secondComplete⟩
  exact ⟨bond, bondPresent, saturated, namedEdge, kind, unitValid,
    secondPresent, firstPresent, stateDistinct.symm, spatialDistinct.symm,
    secondComplete, firstComplete⟩

theorem directRotationStep_aboutMolecularSingleBond_sound
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State)
    (step : DirectRotationStep
      (RotationAboutMolecularSingleBond molecule ledger) first second) :
    MolecularSingleBondRotationSound molecule ledger first second := by
  rcases step with forward | reverse
  · exact rotationAboutMolecularSingleBond_sound molecule ledger first second forward
  · exact molecularSingleBondRotationSound_symmetric molecule ledger
      (rotationAboutMolecularSingleBond_sound molecule ledger second first reverse)

/-! ## Composition with exhaustive finite twist scheduling -/

def auditedCoordinateTwistLedger {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    CoordinateTwistLedger State :=
  { unit := ledger.unit
    states := ledger.states
    spatialAt := ledger.spatialAt
    independentSingleBondRotation := RotationAboutMolecularSingleBond molecule ledger }

theorem scheduledAuditedCoordinateTwistInput_rotation_sound
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (input : CoordinateTwistInOut.CoordinateTwistInput State)
    (inputPresent : input ∈ scheduledCoordinateTwistInputs
      (auditedCoordinateTwistLedger molecule ledger))
    (first second : State)
    (rotation : input.independentSingleBondRotation first second) :
    MolecularSingleBondRotationSound molecule ledger first second := by
  rcases (mem_scheduledCoordinateTwistInputs_iff
    (auditedCoordinateTwistLedger molecule ledger) input).mp inputPresent with
    ⟨candidate, _candidatePresent, inputEq⟩
  subst input
  change RotationAboutMolecularSingleBond molecule ledger first second at rotation
  exact rotationAboutMolecularSingleBond_sound molecule ledger first second rotation

end BlueBookP94.P94MolecularDirectRotationEvidence
end TetraStereo.OneCenter
