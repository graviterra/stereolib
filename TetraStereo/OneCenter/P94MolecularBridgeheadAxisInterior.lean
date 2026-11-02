import TetraStereo.OneCenter.P94MolecularBridgeSufficiency

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularBridgeheadAxisInterior

open CoordinateTwistInOut
open P94MolecularBicyclicFramework
open P94MolecularLonePair
open P94MolecularBridgeSufficiency

/-!
# Source-backed bridgehead-axis interior evidence for P-94.3.2.6

The Blue Book defines in/out isomerism at a *bridgehead* exocyclic bond or lone pair, not at an
arbitrary atom of a bicyclic framework.  Its two P-94.3.2.6 figures depict the inward direction at
one bridgehead as the direction across the cage toward the other bridgehead.  For the represented
theta core, this gives an exact reference that requires no nominated free-space “interior point”:
the observation's stored reference point must be the coordinate of the opposite theta endpoint.

This module intentionally makes only that theta-core claim.  It does not invent a centroid or a
convex-hull rule for arbitrary fused/polycyclic frameworks, for which the cited provision supplies
no such construction.
-/

/-! ## Exact endpoint and opposite-endpoint semantics -/

theorem thetaFramework_isBridgehead_iff (framework : ThetaFramework) (atom : ℕ) :
    framework.IsBridgehead atom ↔
      atom = framework.firstBridgehead ∨ atom = framework.secondBridgehead :=
  Iff.rfl

/-- `other` is the endpoint across the theta cage from `bridgehead`. -/
def OppositeBridgehead (framework : ThetaFramework) (bridgehead other : ℕ) : Prop :=
  (bridgehead = framework.firstBridgehead ∧ other = framework.secondBridgehead) ∨
    (bridgehead = framework.secondBridgehead ∧ other = framework.firstBridgehead)

theorem oppositeBridgehead_iff (framework : ThetaFramework) (bridgehead other : ℕ) :
    OppositeBridgehead framework bridgehead other ↔
      (bridgehead = framework.firstBridgehead ∧ other = framework.secondBridgehead) ∨
        (bridgehead = framework.secondBridgehead ∧ other = framework.firstBridgehead) :=
  Iff.rfl

/-- Valid theta endpoints are ordered, hence the opposite bridgehead is genuinely distinct. -/
theorem oppositeBridgehead_ne (molecule : RawMolecule) (framework : ThetaFramework)
    (bridgehead other : ℕ) (valid : framework.Valid molecule)
    (opposite : OppositeBridgehead framework bridgehead other) :
    bridgehead ≠ other := by
  rcases opposite with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Nat.ne_of_lt valid.1
  · exact (Nat.ne_of_lt valid.1).symm

/-- Exact theta-core interior reference: the framework is molecularly valid, and the supplied
reference point is the coordinate of the endpoint opposite the observed bridgehead. -/
def BridgeheadAxisInteriorWitness (molecule : RawMolecule) (unit : P94ConformationUnit)
    (framework : ThetaFramework) (bridgehead : ℕ) (spatial : SpatialConfiguration)
    (interior : CartesianPoint3) : Prop :=
  framework.ValidFor molecule unit ∧
    ∃ other,
      OppositeBridgehead framework bridgehead other ∧
        CoordinateRing.SpatialPointAt spatial other interior

theorem bridgeheadAxisInteriorWitness_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (bridgehead : ℕ)
    (spatial : SpatialConfiguration) (interior : CartesianPoint3) :
    BridgeheadAxisInteriorWitness molecule unit framework bridgehead spatial interior ↔
      framework.ValidFor molecule unit ∧
        ∃ other,
          OppositeBridgehead framework bridgehead other ∧
            CoordinateRing.SpatialPointAt spatial other interior :=
  Iff.rfl

/-! ## Complete graph/electronic/axis adapter -/

/-- All single-direction premises except the source-operational bridge capability.  Topology,
actual bridgehead identity, complete-framework membership, and the axis reference are derived;
only the molecule-linked electronic ledger remains as explicit input. -/
def graphElectronicAxisBasePremises (molecule : RawMolecule)
    (ledger : CertifiedLonePairLedger molecule) :
    InOutPremisesWithoutBridge ThetaFramework :=
  { BicyclicFramework := fun candidate unit framework => framework.ValidFor candidate unit
    InteriorWitness := BridgeheadAxisInteriorWitness
    AtomInFramework := fun _candidate _unit framework atom => framework.ContainsAtom atom
    BridgeheadInFramework := fun candidate unit framework atom =>
      framework.ValidFor candidate unit ∧ framework.IsBridgehead atom
    LonePairAt := fun candidate atom =>
      candidate = molecule ∧ ledger.HasLonePairAt atom }

/-- Complete represented P-94.3.2.6 premise adapter.  Bridge sufficiency is still exactly the
existence of validated inward and outward observations at one site. -/
def graphElectronicAxisBridgePremises (molecule : RawMolecule)
    (ledger : CertifiedLonePairLedger molecule) :
    IndependentInOutPremises ThetaFramework :=
  bridgeDerivedPremises (graphElectronicAxisBasePremises molecule ledger)

theorem graphElectronicAxisBridgePremises_bicyclicFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (candidate : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework) :
    (graphElectronicAxisBridgePremises molecule ledger).BicyclicFramework
        candidate unit framework ↔
      framework.ValidFor candidate unit :=
  Iff.rfl

theorem graphElectronicAxisBridgePremises_bridgeheadInFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (candidate : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework)
    (atom : ℕ) :
    (graphElectronicAxisBridgePremises molecule ledger).BridgeheadInFramework
        candidate unit framework atom ↔
      framework.ValidFor candidate unit ∧ framework.IsBridgehead atom :=
  Iff.rfl

theorem graphElectronicAxisBridgePremises_interiorWitness_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (candidate : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework)
    (bridgehead : ℕ) (spatial : SpatialConfiguration) (interior : CartesianPoint3) :
    (graphElectronicAxisBridgePremises molecule ledger).InteriorWitness
        candidate unit framework bridgehead spatial interior ↔
      framework.ValidFor candidate unit ∧
        ∃ other,
          OppositeBridgehead framework bridgehead other ∧
            CoordinateRing.SpatialPointAt spatial other interior :=
  Iff.rfl

theorem graphElectronicAxisBridgePremises_atomInFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (candidate : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework)
    (atom : ℕ) :
    (graphElectronicAxisBridgePremises molecule ledger).AtomInFramework
        candidate unit framework atom ↔
      ∃ path ∈ framework.bridges, atom ∈ path :=
  Iff.rfl

theorem graphElectronicAxisBridgePremises_lonePairAt_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (candidate : RawMolecule) (atom : ℕ) :
    (graphElectronicAxisBridgePremises molecule ledger).LonePairAt candidate atom ↔
      candidate = molecule ∧ ledger.HasLonePairAt atom :=
  Iff.rfl

/-- Every accepted single-observation direction uses an actual theta endpoint and the coordinate
of its opposite endpoint as the alignment reference.  The final conjunct preserves the exact
strict dot-product sign used to emit `inward` or `outward`. -/
theorem coordinateDirectionJudgment_uses_oppositeBridgeheadAxis
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation ThetaFramework)
    (direction : BridgeheadDirection)
    (judged : CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises molecule ledger)
      molecule unit observation direction) :
    observation.virtualPoints.Valid ∧
      observation.framework.ValidFor molecule unit ∧
      observation.framework.IsBridgehead observation.bridgehead ∧
      ∃ other bridgeheadPoint participantPoint,
        OppositeBridgehead observation.framework observation.bridgehead other ∧
        CoordinateRing.SpatialPointAt observation.spatial other observation.interior ∧
        CoordinateRing.SpatialPointAt observation.spatial observation.bridgehead bridgeheadPoint ∧
        CoordinateTorsion.ParticipantPointAt observation.spatial observation.virtualPoints
          observation.directedParticipant participantPoint ∧
        let alignment := RationalVector3.dot
          (CartesianPoint3.displacement bridgeheadPoint participantPoint)
          (CartesianPoint3.displacement bridgeheadPoint observation.interior)
        match direction with
        | .inward => 0 < alignment
        | .outward => alignment < 0 := by
  rcases judged with
    ⟨ledgerValid, interiorWitness, participantValid,
      bridgeheadPoint, participantPoint, bridgeheadAt, participantAt, sign⟩
  rcases interiorWitness with ⟨frameworkValid, other, opposite, otherAt⟩
  have actualBridgehead := inOutParticipantChemicallyValid_bridgeheadInFramework
    (graphElectronicAxisBridgePremises molecule ledger) molecule unit observation.framework
    observation.bridgehead observation.directedParticipant participantValid
  have endpoint : observation.framework.IsBridgehead observation.bridgehead :=
    ((graphElectronicAxisBridgePremises_bridgeheadInFramework_iff
      molecule ledger molecule unit observation.framework observation.bridgehead).mp
        actualBridgehead).2
  cases direction <;>
    exact ⟨ledgerValid, frameworkValid, endpoint, other, bridgeheadPoint, participantPoint,
      opposite, otherAt, bridgeheadAt, participantAt, sign⟩

end BlueBookP94.P94MolecularBridgeheadAxisInterior
end TetraStereo.OneCenter
